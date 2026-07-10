import { execFile } from "node:child_process";
import * as crypto from "node:crypto";
import { copyFile, mkdtemp, rm } from "node:fs/promises";
import * as http from "node:http";
import type { AddressInfo } from "node:net";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { URL } from "node:url";
import type { ExtensionAPI, ExtensionContext } from "@earendil-works/pi-coding-agent";

type DiffLineKind = "context" | "add" | "delete" | "meta";
type DiffFileStatus = "modified" | "added" | "deleted" | "renamed" | "binary" | "unknown";

type DiffLine = {
	kind: DiffLineKind;
	content: string;
	oldLine?: number;
	newLine?: number;
};

type DiffHunk = {
	header: string;
	oldStart: number;
	oldCount: number;
	newStart: number;
	newCount: number;
	lines: DiffLine[];
};

type DiffFile = {
	oldPath: string;
	newPath: string;
	status: DiffFileStatus;
	isBinary: boolean;
	hunks: DiffHunk[];
};

type DiffMode = "active-turn" | "branch" | "uncommitted" | "last-turn";

type DiffModeOption = {
	id: DiffMode;
	label: string;
	description: string;
	available: boolean;
};

type DiffCapture = {
	gitRoot: string;
	branchName: string;
	diffText: string;
	files: DiffFile[];
	truncated: boolean;
	modeLabel: string;
	modeDescription: string;
	baseRef?: string;
	additions: number;
	deletions: number;
};

type LastTurnSnapshot = {
	beforeTree: string;
	afterTree: string;
};

type TurnActivityFile = {
	path: string;
	status: DiffFileStatus;
	additions: number;
	deletions: number;
};

type TurnActivity = {
	running: boolean;
	filesChanged: number;
	additions: number;
	deletions: number;
	files: TurnActivityFile[];
	updatedAt: number;
};

type ReviewCommentStatus = "pending" | "sent" | "resolved";
type ReviewCommentSide = "old" | "new" | "context" | "mixed";

type ReviewComment = {
	id: string;
	reviewId: string;
	createdAt: number;
	filePath: string;
	side: ReviewCommentSide;
	oldLine?: number;
	newLine?: number;
	oldEndLine?: number;
	newEndLine?: number;
	hunkHeader: string;
	lineContent: string;
	body: string;
	status: ReviewCommentStatus;
};

type Review = {
	id: string;
	token: string;
	createdAt: number;
	updatedAt: number;
	diffVersion: number;
	cwd: string;
	gitRoot: string;
	branchName: string;
	mode: DiffMode;
	modeLabel: string;
	modeDescription: string;
	baseRef?: string;
	additions: number;
	deletions: number;
	diffText: string;
	files: DiffFile[];
	comments: ReviewComment[];
};

type ServerState = {
	server: http.Server;
	baseUrl: string;
};

const WIDGET_KEY = "review-diff";
const MAX_DIFF_BYTES = 4 * 1024 * 1024;

let serverState: ServerState | undefined;
const reviews = new Map<string, Review>();
const activeTurnTrees = new Map<string, string>();
const lastTurnSnapshots = new Map<string, LastTurnSnapshot>();
const turnActivities = new Map<string, TurnActivity>();
const activityClients = new Map<string, Set<http.ServerResponse>>();
const activityRefreshTimers = new Map<string, ReturnType<typeof setTimeout>>();
let pendingComments: ReviewComment[] = [];
let lastCtx: ExtensionContext | undefined;

function randomId(prefix: string): string {
	return `${prefix}_${crypto.randomBytes(12).toString("base64url")}`;
}

function jsonResponse(res: http.ServerResponse, status: number, value: unknown): void {
	const body = JSON.stringify(value);
	res.writeHead(status, {
		"content-type": "application/json; charset=utf-8",
		"content-length": Buffer.byteLength(body),
		"cache-control": "no-store",
	});
	res.end(body);
}

function textResponse(res: http.ServerResponse, status: number, body: string, contentType = "text/plain; charset=utf-8"): void {
	res.writeHead(status, {
		"content-type": contentType,
		"content-length": Buffer.byteLength(body),
		"cache-control": "no-store",
	});
	res.end(body);
}

async function readRequestJson(req: http.IncomingMessage): Promise<unknown> {
	const chunks: Buffer[] = [];
	let total = 0;
	for await (const chunk of req) {
		const buffer = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
		total += buffer.length;
		if (total > 256 * 1024) throw new Error("Request body too large");
		chunks.push(buffer);
	}
	const raw = Buffer.concat(chunks).toString("utf8");
	return raw ? JSON.parse(raw) : {};
}

function requireReviewAuth(req: http.IncomingMessage, review: Review): boolean {
	return req.headers.authorization === `Bearer ${review.token}`;
}

function parseHunkHeader(header: string): Pick<DiffHunk, "oldStart" | "oldCount" | "newStart" | "newCount"> | null {
	const match = header.match(/^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/);
	if (!match) return null;
	return {
		oldStart: Number(match[1]),
		oldCount: match[2] ? Number(match[2]) : 1,
		newStart: Number(match[3]),
		newCount: match[4] ? Number(match[4]) : 1,
	};
}

function pathFromDiffMarker(line: string): string {
	const value = line.slice(4).trim();
	if (value === "/dev/null") return value;
	return value.replace(/^[ab]\//, "");
}

function inferStatus(file: DiffFile): DiffFileStatus {
	if (file.isBinary) return "binary";
	if (file.oldPath === "/dev/null") return "added";
	if (file.newPath === "/dev/null") return "deleted";
	if (file.oldPath && file.newPath && file.oldPath !== file.newPath) return "renamed";
	return "modified";
}

function parseUnifiedDiff(diffText: string): DiffFile[] {
	const files: DiffFile[] = [];
	let currentFile: DiffFile | undefined;
	let currentHunk: DiffHunk | undefined;
	let oldLine = 0;
	let newLine = 0;

	const diffLines = diffText.endsWith("\n") ? diffText.slice(0, -1).split("\n") : diffText.split("\n");
	for (const line of diffLines) {
		if (line.startsWith("diff --git ")) {
			if (currentFile) currentFile.status = inferStatus(currentFile);
			currentHunk = undefined;
			oldLine = 0;
			newLine = 0;

			const match = line.match(/^diff --git a\/(.*) b\/(.*)$/);
			currentFile = {
				oldPath: match?.[1] ?? "",
				newPath: match?.[2] ?? "",
				status: "unknown",
				isBinary: false,
				hunks: [],
			};
			files.push(currentFile);
			continue;
		}

		if (!currentFile) continue;

		if (line.startsWith("old mode ") || line.startsWith("new mode ") || line.startsWith("index ")) continue;
		if (line.startsWith("similarity index ")) continue;
		if (line.startsWith("rename from ")) {
			currentFile.oldPath = line.slice("rename from ".length).trim();
			continue;
		}
		if (line.startsWith("rename to ")) {
			currentFile.newPath = line.slice("rename to ".length).trim();
			continue;
		}
		if (line.startsWith("Binary files ") || line.startsWith("GIT binary patch")) {
			currentFile.isBinary = true;
			currentHunk = undefined;
			continue;
		}
		if (line.startsWith("--- ")) {
			currentFile.oldPath = pathFromDiffMarker(line);
			continue;
		}
		if (line.startsWith("+++ ")) {
			currentFile.newPath = pathFromDiffMarker(line);
			continue;
		}
		if (line.startsWith("@@ ")) {
			const parsed = parseHunkHeader(line);
			if (!parsed) continue;
			currentHunk = {
				header: line,
				...parsed,
				lines: [],
			};
			currentFile.hunks.push(currentHunk);
			oldLine = parsed.oldStart;
			newLine = parsed.newStart;
			continue;
		}
		if (!currentHunk) continue;

		if (line.startsWith("+")) {
			currentHunk.lines.push({ kind: "add", content: line.slice(1), newLine });
			newLine += 1;
		} else if (line.startsWith("-")) {
			currentHunk.lines.push({ kind: "delete", content: line.slice(1), oldLine });
			oldLine += 1;
		} else if (line.startsWith("\\")) {
			currentHunk.lines.push({ kind: "meta", content: line });
		} else {
			const content = line.startsWith(" ") ? line.slice(1) : line;
			currentHunk.lines.push({ kind: "context", content, oldLine, newLine });
			oldLine += 1;
			newLine += 1;
		}
	}

	if (currentFile) currentFile.status = inferStatus(currentFile);
	return files;
}

async function getGitRoot(pi: ExtensionAPI, cwd: string): Promise<string> {
	const result = await pi.exec("git", ["rev-parse", "--show-toplevel"], { cwd, timeout: 5000 });
	if (result.code !== 0) throw new Error("Not inside a git repository");
	return result.stdout.trim() || cwd;
}

async function getBranchName(pi: ExtensionAPI, gitRoot: string): Promise<string> {
	const symbolic = await pi.exec("git", ["symbolic-ref", "--quiet", "--short", "HEAD"], { cwd: gitRoot, timeout: 5000 });
	if (symbolic.code === 0 && symbolic.stdout.trim()) return symbolic.stdout.trim();
	const detached = await pi.exec("git", ["rev-parse", "--short", "HEAD"], { cwd: gitRoot, timeout: 5000 });
	return detached.code === 0 && detached.stdout.trim() ? `detached@${detached.stdout.trim()}` : "worktree";
}

function runGitWithIndex(gitRoot: string, indexPath: string, args: string[]): Promise<string> {
	return new Promise((resolve, reject) => {
		execFile(
			"git",
			args,
			{
				cwd: gitRoot,
				env: { ...process.env, GIT_INDEX_FILE: indexPath },
				maxBuffer: MAX_DIFF_BYTES * 2,
			},
			(error, stdout, stderr) => {
				if (error) {
					reject(new Error(stderr.trim() || stdout.trim() || error.message));
					return;
				}
				resolve(stdout.trim());
			},
		);
	});
}

function runGitCapture(gitRoot: string, args: string[]): Promise<string> {
	return new Promise((resolve, reject) => {
		execFile("git", args, { cwd: gitRoot, maxBuffer: MAX_DIFF_BYTES * 2 }, (error, stdout, stderr) => {
			if (error) {
				reject(new Error(stderr.trim() || stdout.trim() || error.message));
				return;
			}
			resolve(stdout.trim());
		});
	});
}

// Seed a temp index from the repo's real index so Git keeps its cached stat
// data (plus the untracked and fsmonitor caches). Without this, `git add -A`
// re-hashes every file in the worktree, which is multi-second on large repos.
async function seedIndexFromRepo(gitRoot: string, indexPath: string): Promise<boolean> {
	try {
		const gitDir = await runGitCapture(gitRoot, ["rev-parse", "--absolute-git-dir"]);
		if (!gitDir) return false;
		await copyFile(join(gitDir, "index"), indexPath);
		return true;
	} catch {
		return false;
	}
}

async function captureWorktreeTree(gitRoot: string): Promise<string> {
	const tempDir = await mkdtemp(join(tmpdir(), "pi-review-diff-"));
	const indexPath = join(tempDir, "index");
	try {
		if (await seedIndexFromRepo(gitRoot, indexPath)) {
			try {
				await runGitWithIndex(gitRoot, indexPath, ["add", "-A", "--", "."]);
				return await runGitWithIndex(gitRoot, indexPath, ["write-tree"]);
			} catch {
				// Seeded index was unusable (e.g. a split-index edge case).
				// Fall through and rebuild a fresh index below.
			}
		}
		try {
			await runGitWithIndex(gitRoot, indexPath, ["read-tree", "HEAD"]);
		} catch {
			await runGitWithIndex(gitRoot, indexPath, ["read-tree", "--empty"]);
		}
		await runGitWithIndex(gitRoot, indexPath, ["add", "-A", "--", "."]);
		return await runGitWithIndex(gitRoot, indexPath, ["write-tree"]);
	} finally {
		await rm(tempDir, { recursive: true, force: true });
	}
}

async function resolveMainBase(pi: ExtensionAPI, gitRoot: string): Promise<{ baseRef: string; mergeBase: string }> {
	const candidates = ["main", "origin/main", "upstream/main"];
	for (const remote of ["origin", "upstream"]) {
		const symbolic = await pi.exec("git", ["symbolic-ref", "--quiet", "--short", `refs/remotes/${remote}/HEAD`], { cwd: gitRoot, timeout: 5000 });
		const defaultRef = symbolic.stdout.trim();
		if (symbolic.code === 0 && defaultRef && !candidates.includes(defaultRef)) candidates.push(defaultRef);
	}
	candidates.push("master", "origin/master", "upstream/master");
	for (const baseRef of candidates) {
		const exists = await pi.exec("git", ["rev-parse", "--verify", "--quiet", `${baseRef}^{commit}`], { cwd: gitRoot, timeout: 5000 });
		if (exists.code !== 0) continue;
		const mergeBase = await pi.exec("git", ["merge-base", "HEAD", baseRef], { cwd: gitRoot, timeout: 5000 });
		if (mergeBase.code === 0 && mergeBase.stdout.trim()) return { baseRef, mergeBase: mergeBase.stdout.trim() };
	}
	throw new Error("Could not find main (or a main/master remote) to compare this branch against");
}

async function diffTrees(pi: ExtensionAPI, gitRoot: string, before: string, after: string): Promise<string> {
	const result = await pi.exec(
		"git",
		["-c", "core.quotepath=false", "diff", "--no-ext-diff", "--no-color", "--find-renames", "--submodule=short", before, after],
		{ cwd: gitRoot, timeout: 30000 },
	);
	if (result.code !== 0) throw new Error(result.stderr.trim() || result.stdout.trim() || "git diff failed");
	return result.stdout;
}

function diffStats(files: DiffFile[]): { additions: number; deletions: number } {
	let additions = 0;
	let deletions = 0;
	for (const file of files) {
		for (const hunk of file.hunks) {
			for (const line of hunk.lines) {
				if (line.kind === "add") additions += 1;
				if (line.kind === "delete") deletions += 1;
			}
		}
	}
	return { additions, deletions };
}

function activityFiles(files: DiffFile[]): TurnActivityFile[] {
	return files.map((file) => {
		const path = file.newPath === "/dev/null" ? file.oldPath : file.newPath;
		return { path, status: file.status, ...diffStats([file]) };
	});
}

function idleTurnActivity(): TurnActivity {
	return { running: false, filesChanged: 0, additions: 0, deletions: 0, files: [], updatedAt: Date.now() };
}

function broadcastTurnActivity(gitRoot: string): void {
	const activity = turnActivities.get(gitRoot) ?? idleTurnActivity();
	const payload = `data: ${JSON.stringify(activity)}\n\n`;
	for (const review of reviews.values()) {
		if (review.gitRoot !== gitRoot) continue;
		for (const client of activityClients.get(review.id) ?? []) {
			if (!client.destroyed && !client.writableEnded) client.write(payload);
		}
	}
}

function setTurnActivity(gitRoot: string, activity: TurnActivity): void {
	turnActivities.set(gitRoot, activity);
	broadcastTurnActivity(gitRoot);
}

async function refreshTurnActivity(pi: ExtensionAPI, gitRoot: string, beforeTree: string): Promise<void> {
	try {
		const afterTree = await captureWorktreeTree(gitRoot);
		if (activeTurnTrees.get(gitRoot) !== beforeTree) return;
		const diffText = await diffTrees(pi, gitRoot, beforeTree, afterTree);
		const files = parseUnifiedDiff(diffText);
		const stats = diffStats(files);
		for (const review of reviews.values()) {
			if (review.gitRoot !== gitRoot || review.mode !== "active-turn") continue;
			applyCapture(review, {
				gitRoot,
				branchName: review.branchName,
				diffText,
				files,
				truncated: false,
				modeLabel: "Active turn",
				modeDescription: "Changes in the current Pi turn",
				...stats,
			});
		}
		setTurnActivity(gitRoot, {
			running: true,
			filesChanged: files.length,
			...stats,
			files: activityFiles(files),
			updatedAt: Date.now(),
		});
	} catch {
		// Live activity is best-effort and must not interrupt the agent run.
	}
}

function scheduleTurnActivityRefresh(pi: ExtensionAPI, gitRoot: string): void {
	const existing = activityRefreshTimers.get(gitRoot);
	if (existing) clearTimeout(existing);
	const timer = setTimeout(() => {
		activityRefreshTimers.delete(gitRoot);
		const beforeTree = activeTurnTrees.get(gitRoot);
		if (beforeTree) void refreshTurnActivity(pi, gitRoot, beforeTree);
	}, 250);
	activityRefreshTimers.set(gitRoot, timer);
}

function diffModeOptions(gitRoot: string, baseRef?: string): DiffModeOption[] {
	const activity = turnActivities.get(gitRoot);
	return [
		...(activity?.running ? [{ id: "active-turn" as const, label: "Active turn", description: "Changes in the current Pi turn", available: true }] : []),
		{ id: "branch", label: "Branch", description: `Everything changed since ${baseRef ?? "main"}`, available: true },
		{ id: "uncommitted", label: "Uncommitted", description: "Working tree compared with HEAD", available: true },
		{
			id: "last-turn",
			label: "Last turn",
			description: lastTurnSnapshots.has(gitRoot) ? "Changes made by the latest Pi turn" : "Available after Pi completes a turn",
			available: lastTurnSnapshots.has(gitRoot),
		},
	];
}

async function captureDiff(pi: ExtensionAPI, cwd: string, mode: DiffMode): Promise<DiffCapture> {
	const gitRoot = await getGitRoot(pi, cwd);
	const branchName = await getBranchName(pi, gitRoot);
	let before: string;
	let after: string;
	let baseRef: string | undefined;
	let modeLabel: string;
	let modeDescription: string;

	if (mode === "active-turn") {
		const activeTree = activeTurnTrees.get(gitRoot);
		if (!activeTree || !turnActivities.get(gitRoot)?.running) throw new Error("No Pi turn is currently running");
		before = activeTree;
		after = await captureWorktreeTree(gitRoot);
		modeLabel = "Active turn";
		modeDescription = "Changes in the current Pi turn";
	} else if (mode === "last-turn") {
		const snapshot = lastTurnSnapshots.get(gitRoot);
		if (!snapshot) throw new Error("Last turn is not available yet. Complete a Pi turn, then try again.");
		before = snapshot.beforeTree;
		after = snapshot.afterTree;
		modeLabel = "Last turn";
		modeDescription = "Changes made by the latest Pi turn";
	} else {
		after = await captureWorktreeTree(gitRoot);
		if (mode === "branch") {
			const base = await resolveMainBase(pi, gitRoot);
			before = base.mergeBase;
			baseRef = base.baseRef;
			modeLabel = "Branch";
			modeDescription = `Compared with ${baseRef}`;
		} else {
			const head = await pi.exec("git", ["rev-parse", "HEAD^{tree}"], { cwd: gitRoot, timeout: 5000 });
			if (head.code !== 0) throw new Error(head.stderr.trim() || "Could not resolve HEAD");
			before = head.stdout.trim();
			modeLabel = "Uncommitted";
			modeDescription = "Working tree compared with HEAD";
		}
	}

	let diffText = await diffTrees(pi, gitRoot, before, after);
	let truncated = false;
	if (Buffer.byteLength(diffText, "utf8") > MAX_DIFF_BYTES) {
		truncated = true;
		diffText = diffText.slice(0, MAX_DIFF_BYTES) + "\n\n[review-diff: diff truncated]\n";
	}
	const files = parseUnifiedDiff(diffText);
	return { gitRoot, branchName, diffText, files, truncated, modeLabel, modeDescription, baseRef, ...diffStats(files) };
}

function formatRange(start: number | undefined, end: number | undefined): string | undefined {
	if (start === undefined) return undefined;
	if (end === undefined || end === start) return String(start);
	return `${start}-${end}`;
}

function commentLocation(comment: ReviewComment): string {
	const oldRange = formatRange(comment.oldLine, comment.oldEndLine);
	const newRange = formatRange(comment.newLine, comment.newEndLine);
	if (comment.side === "mixed" && oldRange && newRange) return `old ${oldRange}, new ${newRange}`;
	return newRange ?? oldRange ?? "?";
}

function shortComment(comment: ReviewComment): string {
	const text = comment.body.replace(/\s+/g, " ").trim();
	return `${comment.filePath}:${commentLocation(comment)} — ${text.length > 80 ? `${text.slice(0, 77)}…` : text}`;
}

function updateWidget(ctx = lastCtx): void {
	if (!ctx?.hasUI) return;
	const allPending = pendingComments.filter((comment) => comment.status === "pending");

	if (allPending.length === 0) {
		ctx.ui.setWidget(WIDGET_KEY, undefined);
		ctx.ui.setStatus(WIDGET_KEY, undefined);
		return;
	}

	ctx.ui.setWidget(
		WIDGET_KEY,
		allPending.slice(-5).map((comment, index) => `${index + 1}. ${shortComment(comment)}`),
	);
	ctx.ui.setStatus(WIDGET_KEY, `${allPending.length} review comment${allPending.length === 1 ? "" : "s"}`);
}

function commentPayload(comment: ReviewComment, index: number): string {
	return [
		`${index + 1}. ${comment.filePath}:${commentLocation(comment)} (${comment.side})`,
		`Hunk: ${comment.hunkHeader}`,
		`Line${comment.lineContent.includes("\n") ? "s" : ""}: ${comment.lineContent}`,
		`Comment: ${comment.body.trim()}`,
	].join("\n");
}

function buildCommentsPrompt(comments: ReviewComment[]): string {
	return [
		"<review-diff-comments>",
		"The following comments were added in the local diff review UI. Treat them as user review feedback.",
		"",
		...comments.map(commentPayload),
		"</review-diff-comments>",
	].join("\n");
}

function validateCommentInput(value: unknown): Omit<ReviewComment, "id" | "reviewId" | "createdAt" | "status"> {
	if (!value || typeof value !== "object") throw new Error("Expected JSON object");
	const input = value as Record<string, unknown>;
	const body = typeof input.body === "string" ? input.body.trim() : "";
	const filePath = typeof input.filePath === "string" ? input.filePath : "";
	const side = input.side === "old" || input.side === "new" || input.side === "context" || input.side === "mixed" ? input.side : undefined;
	if (!body) throw new Error("Comment body is required");
	if (!filePath) throw new Error("filePath is required");
	if (!side) throw new Error("side is required");
	return {
		filePath,
		side,
		oldLine: typeof input.oldLine === "number" ? input.oldLine : undefined,
		newLine: typeof input.newLine === "number" ? input.newLine : undefined,
		oldEndLine: typeof input.oldEndLine === "number" ? input.oldEndLine : undefined,
		newEndLine: typeof input.newEndLine === "number" ? input.newEndLine : undefined,
		hunkHeader: typeof input.hunkHeader === "string" ? input.hunkHeader : "",
		lineContent: typeof input.lineContent === "string" ? input.lineContent : "",
		body,
	};
}

function applyCapture(review: Review, capture: DiffCapture): void {
	review.gitRoot = capture.gitRoot;
	review.branchName = capture.branchName;
	review.diffText = capture.diffText;
	review.files = capture.files;
	review.modeLabel = capture.modeLabel;
	review.modeDescription = capture.modeDescription;
	if (capture.baseRef) review.baseRef = capture.baseRef;
	review.additions = capture.additions;
	review.deletions = capture.deletions;
	review.updatedAt = Date.now();
	review.diffVersion += 1;
}

function reviewResponse(review: Review): Record<string, unknown> {
	return {
		id: review.id,
		createdAt: review.createdAt,
		updatedAt: review.updatedAt,
		diffVersion: review.diffVersion,
		cwd: review.cwd,
		gitRoot: review.gitRoot,
		branchName: review.branchName,
		mode: review.mode,
		modeLabel: review.modeLabel,
		modeDescription: review.modeDescription,
		baseRef: review.baseRef,
		additions: review.additions,
		deletions: review.deletions,
		modes: diffModeOptions(review.gitRoot, review.baseRef),
		files: review.files,
		comments: review.comments,
	};
}

async function refreshReview(pi: ExtensionAPI, review: Review): Promise<void> {
	applyCapture(review, await captureDiff(pi, review.cwd, review.mode));
}

async function refreshAllReviews(pi: ExtensionAPI): Promise<void> {
	const targets = [...reviews.values()];
	if (targets.length === 0) return;
	await Promise.allSettled(targets.map((review) => refreshReview(pi, review)));
	updateWidget();
}

function createRequestHandler(pi: ExtensionAPI): http.RequestListener {
	return async (req, res) => {
		try {
			const parsedUrl = new URL(req.url ?? "/", "http://127.0.0.1");
			const path = parsedUrl.pathname;

			if (req.method === "GET" && path.match(/^\/review\/[^/]+$/)) {
				textResponse(res, 200, REVIEW_PAGE_HTML, "text/html; charset=utf-8");
				return;
			}

			const apiReviewMatch = path.match(/^\/api\/reviews\/([^/]+)(?:\/(activity|comments|version|mode)(?:\/([^/]+))?)?$/);
			if (!apiReviewMatch) {
				textResponse(res, 404, "Not found");
				return;
			}

			const reviewId = apiReviewMatch[1]!;
			const suffix = apiReviewMatch[2];
			const commentId = apiReviewMatch[3];
			const review = reviews.get(reviewId);
			if (!review) {
				jsonResponse(res, 404, { error: "Unknown review" });
				return;
			}
			if (!requireReviewAuth(req, review)) {
				jsonResponse(res, 401, { error: "Unauthorized" });
				return;
			}

			if (req.method === "GET" && !suffix) {
				if (parsedUrl.searchParams.get("refresh") === "1") await refreshReview(pi, review);
				jsonResponse(res, 200, reviewResponse(review));
				return;
			}

			if (req.method === "GET" && suffix === "version") {
				jsonResponse(res, 200, { updatedAt: review.updatedAt, diffVersion: review.diffVersion, mode: review.mode });
				return;
			}

			if (req.method === "GET" && suffix === "activity") {
				res.writeHead(200, {
					"content-type": "text/event-stream; charset=utf-8",
					"cache-control": "no-cache, no-store",
					connection: "keep-alive",
					"x-accel-buffering": "no",
				});
				res.write(`data: ${JSON.stringify(turnActivities.get(review.gitRoot) ?? idleTurnActivity())}\n\n`);
				const clients = activityClients.get(review.id) ?? new Set<http.ServerResponse>();
				clients.add(res);
				activityClients.set(review.id, clients);
				req.on("close", () => {
					clients.delete(res);
					if (clients.size === 0) activityClients.delete(review.id);
				});
				return;
			}

			if (req.method === "POST" && suffix === "mode") {
				const input = await readRequestJson(req);
				const mode = input && typeof input === "object" ? (input as Record<string, unknown>).mode : undefined;
				if (mode !== "active-turn" && mode !== "branch" && mode !== "uncommitted" && mode !== "last-turn") {
					jsonResponse(res, 400, { error: "Unknown diff mode" });
					return;
				}
				if (mode === "active-turn" && (!activeTurnTrees.has(review.gitRoot) || !turnActivities.get(review.gitRoot)?.running)) {
					jsonResponse(res, 409, { error: "No Pi turn is currently running" });
					return;
				}
				if (mode === "last-turn" && !lastTurnSnapshots.has(review.gitRoot)) {
					jsonResponse(res, 409, { error: "Last turn is not available yet. Complete a Pi turn, then try again." });
					return;
				}
				const capture = await captureDiff(pi, review.cwd, mode);
				review.mode = mode;
				applyCapture(review, capture);
				jsonResponse(res, 200, reviewResponse(review));
				return;
			}

			if (req.method === "GET" && suffix === "comments") {
				jsonResponse(res, 200, { comments: review.comments });
				return;
			}

			if (req.method === "POST" && suffix === "comments" && !commentId) {
				const input = validateCommentInput(await readRequestJson(req));
				const comment: ReviewComment = {
					id: randomId("cmt"),
					reviewId,
					createdAt: Date.now(),
					status: "pending",
					...input,
				};
				review.comments.push(comment);
				pendingComments.push(comment);
				updateWidget();
				jsonResponse(res, 201, { comment });
				return;
			}

			if (req.method === "DELETE" && suffix === "comments" && !commentId) {
				const removedIds = new Set(review.comments.filter((comment) => comment.status === "pending").map((comment) => comment.id));
				review.comments = review.comments.filter((comment) => !removedIds.has(comment.id));
				pendingComments = pendingComments.filter((comment) => !removedIds.has(comment.id));
				updateWidget();
				jsonResponse(res, 200, { removed: removedIds.size, comments: review.comments });
				return;
			}

			if (req.method === "DELETE" && suffix === "comments" && commentId) {
				const comment = review.comments.find((candidate) => candidate.id === commentId);
				if (!comment) {
					jsonResponse(res, 404, { error: "Unknown comment" });
					return;
				}
				if (comment.status !== "pending") {
					jsonResponse(res, 409, { error: "Only pending comments can be removed" });
					return;
				}
				review.comments = review.comments.filter((candidate) => candidate.id !== commentId);
				pendingComments = pendingComments.filter((candidate) => candidate.id !== commentId);
				updateWidget();
				jsonResponse(res, 200, { removed: 1, comments: review.comments });
				return;
			}

			jsonResponse(res, 405, { error: "Method not allowed" });
		} catch (error) {
			jsonResponse(res, 500, { error: error instanceof Error ? error.message : String(error) });
		}
	};
}

async function ensureServer(pi: ExtensionAPI): Promise<ServerState> {
	if (serverState) return serverState;
	const server = http.createServer(createRequestHandler(pi));
	await new Promise<void>((resolve, reject) => {
		const onError = (error: Error) => {
			server.off("listening", onListening);
			reject(error);
		};
		const onListening = () => {
			server.off("error", onError);
			resolve();
		};
		server.once("error", onError);
		server.once("listening", onListening);
		server.listen({ host: "127.0.0.1", port: 0, exclusive: true });
	});
	const address = server.address() as AddressInfo;
	serverState = { server, baseUrl: `http://127.0.0.1:${address.port}` };
	return serverState;
}

async function openUrl(pi: ExtensionAPI, url: string): Promise<void> {
	if (process.env.CMUX_WORKSPACE_ID) {
		const cmux = await pi.exec("cmux", ["browser", "open", url], { timeout: 5000 });
		if (cmux.code === 0) return;
	}
	if (process.platform === "darwin") {
		await pi.exec("open", [url], { timeout: 5000 });
		return;
	}
	if (process.platform === "win32") {
		await pi.exec("cmd", ["/c", "start", "", url], { timeout: 5000 });
		return;
	}
	await pi.exec("xdg-open", [url], { timeout: 5000 });
}

async function createReview(pi: ExtensionAPI, ctx: ExtensionContext): Promise<{ review: Review; url: string; truncated: boolean }> {
	const server = await ensureServer(pi);
	const mode: DiffMode = "branch";
	const capture = await captureDiff(pi, ctx.cwd, mode);
	const review: Review = {
		id: randomId("rvw"),
		token: crypto.randomBytes(32).toString("base64url"),
		createdAt: Date.now(),
		updatedAt: Date.now(),
		diffVersion: 1,
		cwd: ctx.cwd,
		gitRoot: capture.gitRoot,
		branchName: capture.branchName,
		mode,
		modeLabel: capture.modeLabel,
		modeDescription: capture.modeDescription,
		baseRef: capture.baseRef,
		additions: capture.additions,
		deletions: capture.deletions,
		diffText: capture.diffText,
		files: capture.files,
		comments: [],
	};
	reviews.set(review.id, review);
	return { review, url: `${server.baseUrl}/review/${review.id}#token=${review.token}`, truncated: capture.truncated };
}

const REVIEW_PAGE_HTML = String.raw`<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>Review changes · Pi</title>
<style>
:root { color-scheme:dark; --bg:#0d0e10; --panel:#131416; --line:#1b1d20; --text:#e8e9eb; --muted:#8a8f98; --accent:#8b7cff; --add-bg:#10251b; --add-fg:#56c991; --del-bg:#2a171a; --del-fg:#f06d7a; --border:#292b30; --comment:#1a1c20; --select:#242038; --syntax-keyword:#c7a0ff; --syntax-string:#d9b477; --syntax-comment:#6f7682; --syntax-number:#e89b70; --syntax-type:#69c7c2; --syntax-function:#7db7ff; --syntax-attribute:#d8a0df; --syntax-tag:#7db7ff; --syntax-property:#8fc7ff; --syntax-selector:#d7ba7d; --syntax-operator:#a9adb5; }
* { box-sizing:border-box; }
html { background:var(--bg); }
body { margin:0; min-height:100vh; background:var(--bg); color:var(--text); font:13px/1.5 Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }
body[data-scheme="light"] { --syntax-keyword:#6f42c1; --syntax-string:#8a6116; --syntax-comment:#6a737d; --syntax-number:#a04400; --syntax-type:#087f8c; --syntax-function:#0757a6; --syntax-attribute:#8b3f8f; --syntax-tag:#0757a6; --syntax-property:#005cc5; --syntax-selector:#735c0f; --syntax-operator:#586069; }
body.is-dragging-comment { cursor:ns-resize; user-select:none; }
button, select, textarea { font:inherit; }
button:focus-visible, select:focus-visible, textarea:focus-visible { outline:2px solid color-mix(in srgb, var(--accent) 72%, white); outline-offset:2px; }
header { position:sticky; top:0; z-index:10; min-height:68px; padding:12px 18px; background:var(--bg); border-bottom:1px solid var(--border); transform:translateZ(0); backface-visibility:hidden; }
.topbar { display:flex; align-items:center; min-width:0; max-width:1800px; margin:0 auto; }
.review-controls { display:flex; align-items:center; justify-content:flex-start; gap:8px; width:100%; min-width:0; }
.scope-control { position:relative; }
.scope-trigger, .file-menu-button, .collapse-toggle { display:flex; align-items:center; gap:8px; height:34px; color:var(--text); background:var(--panel); border:1px solid var(--border); border-radius:8px; padding:0 11px; font-weight:550; cursor:pointer; box-shadow:0 1px 2px rgba(0,0,0,.18); }
.scope-trigger:hover, .file-menu-button:hover, .collapse-toggle:hover { background:var(--comment); border-color:color-mix(in srgb, var(--border) 65%, var(--muted)); }
.collapse-toggle[hidden] { display:none; }
.file-menu-button svg, .collapse-toggle svg { display:block; flex:0 0 auto; }
.collapse-toggle { padding:0; width:34px; justify-content:center; }
#file-count { font:600 12px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; color:color-mix(in srgb, var(--text) 84%, var(--muted)); }
.file-menu-button { margin-left:auto; }
.chevron-down { color:var(--muted); font-size:10px; transition:transform .15s ease; }
.scope-trigger[aria-expanded="true"] .chevron-down { transform:rotate(180deg); }
.diff-stats { display:flex; align-items:center; gap:7px; min-width:74px; padding:0 4px; font:600 12px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.branch-comparison { display:flex; align-items:center; gap:7px; min-width:0; max-width:min(38vw, 480px); color:var(--muted); font:500 11.5px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.branch-current { min-width:0; overflow:hidden; color:color-mix(in srgb, var(--text) 88%, var(--muted)); text-overflow:ellipsis; white-space:nowrap; }
.comparison-arrow { flex:0 0 auto; color:color-mix(in srgb, var(--muted) 72%, transparent); }
.comparison-target { flex:0 0 auto; color:var(--muted); }
.additions { color:var(--add-fg); }
.deletions { color:var(--del-fg); }
.theme-select { width:34px; height:34px; color:transparent; background:var(--panel); border:1px solid var(--border); border-radius:8px; padding:0; cursor:pointer; }
.theme-select option { color:var(--text); background:var(--panel); }
.theme-wrap { position:relative; width:34px; height:34px; }
.theme-wrap::after { content:"◐"; position:absolute; inset:0; display:grid; place-items:center; color:var(--muted); pointer-events:none; font-size:14px; }
.mode-popover, .file-popover { position:fixed; z-index:20; background:color-mix(in srgb, var(--panel) 96%, black); border:1px solid var(--border); border-radius:12px; box-shadow:0 18px 60px rgba(0,0,0,.55), 0 1px 0 rgba(255,255,255,.04) inset; padding:6px; }
.mode-popover { position:fixed; top:auto; left:auto; right:auto; width:min(290px, calc(100vw - 24px)); }
.file-popover { top:60px; right:18px; width:min(468px, calc(100vw - 36px)); max-height:min(74vh, 660px); overflow:auto; }
.mode-popover[hidden], .file-popover[hidden] { display:none; }
.mode-option { display:grid; grid-template-columns:22px 1fr; width:100%; gap:4px 8px; padding:9px 10px; color:var(--text); text-align:left; background:transparent; border:0; border-radius:8px; cursor:pointer; }
.mode-option:hover:not(:disabled) { background:var(--comment); }
.mode-option:disabled { opacity:.45; cursor:not-allowed; }
.mode-check { grid-row:1 / span 3; color:var(--accent); font-size:14px; padding-top:1px; }
.mode-option.is-live .mode-check { animation:live-dot 1.4s ease-in-out infinite; }
.mode-label { font-weight:600; }
.mode-description { color:var(--muted); font-size:11.5px; font-weight:400; }
.mode-files { overflow:hidden; color:color-mix(in srgb, var(--muted) 72%, transparent); font:10.5px/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; text-overflow:ellipsis; white-space:nowrap; }
@keyframes live-dot { 0%, 100% { opacity:.45; } 50% { opacity:1; } }
.file-link { display:flex; align-items:center; gap:8px; color:var(--text); text-decoration:none; padding:8px 9px; border-radius:7px; overflow:hidden; }
.file-link:hover { background:var(--comment); }
.file-link.is-active { background:color-mix(in srgb, var(--accent) 13%, var(--comment)); }
.file-link.is-active::before { content:""; width:5px; height:5px; flex:0 0 auto; background:var(--accent); border-radius:999px; box-shadow:0 0 0 3px color-mix(in srgb, var(--accent) 12%, transparent); }
.file-link-path { display:flex; align-items:baseline; flex:1 1 auto; min-width:0; overflow:hidden; }
.path-dir { flex:0 1 auto; min-width:0; overflow:hidden; white-space:nowrap; text-overflow:ellipsis; direction:rtl; color:var(--muted); font-weight:400; }
.path-name { flex:0 0 auto; white-space:nowrap; color:var(--text); }
.file-link .count { margin-left:auto; color:var(--accent); font-size:11px; }
.status { margin:6px 4px 2px; padding-top:8px; color:var(--muted); border-top:1px solid var(--border); font-size:11.5px; }
.file-filter-wrap { position:sticky; top:0; z-index:3; display:flex; align-items:center; gap:7px; margin:-6px -6px 6px; padding:9px 10px; background:color-mix(in srgb, var(--panel) 97%, black); border-bottom:1px solid var(--border); border-radius:12px 12px 0 0; }
.file-filter-icon { flex:0 0 auto; color:var(--muted); }
#file-filter { flex:1 1 auto; min-width:0; height:30px; color:var(--text); background:var(--bg); border:1px solid var(--border); border-radius:7px; padding:0 9px; }
#file-filter::placeholder { color:var(--muted); }
.file-tree { display:flex; flex-direction:column; gap:1px; }
.tree-children { margin-left:9px; padding-left:7px; border-left:1px solid color-mix(in srgb, var(--border) 85%, transparent); }
.tree-row { display:flex; align-items:center; gap:7px; width:100%; padding:4px 8px; border-radius:7px; overflow:hidden; }
.tree-dir-row { color:var(--text); background:transparent; border:0; text-align:left; cursor:pointer; font-weight:600; }
.tree-dir-row:hover { background:var(--comment); }
.tree-chevron { position:relative; width:12px; height:12px; flex:0 0 12px; color:var(--muted); }
.tree-chevron::before { content:""; position:absolute; left:2px; top:2px; width:5px; height:5px; border-right:1.5px solid currentColor; border-bottom:1.5px solid currentColor; transform:rotate(45deg); transition:transform .15s ease; }
.tree-dir-row.is-collapsed .tree-chevron::before { transform:rotate(-45deg); }
.tree-dir-label { display:flex; align-items:center; gap:4px; flex:1 1 auto; min-width:0; overflow:hidden; }
.tree-dir-label .seg { min-width:0; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; color:color-mix(in srgb, var(--text) 80%, var(--muted)); }
.tree-dir-label .seg:last-child { color:var(--text); }
.seg-sep { flex:0 0 auto; color:var(--muted); opacity:.55; }
.tree-dir-dot { flex:0 0 auto; width:6px; height:6px; border-radius:999px; background:color-mix(in srgb, var(--accent) 50%, transparent); }
.tree-file-row { gap:8px; }
.tree-file-row.is-active { background:color-mix(in srgb, var(--accent) 14%, var(--comment)); box-shadow:inset 2px 0 0 var(--accent); }
.tree-file-row.is-active::before { content:none; }
.tree-file-icon { flex:0 0 auto; color:var(--muted); }
.tree-file-name { display:flex; align-items:baseline; flex:1 1 auto; min-width:0; overflow:hidden; font:12px/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.fn-stem { overflow:hidden; text-overflow:ellipsis; white-space:nowrap; color:var(--text); }
.fn-ext { flex:0 0 auto; white-space:nowrap; color:var(--muted); }
.tree-hits { flex:0 0 auto; padding:0 6px; color:var(--accent); background:color-mix(in srgb, var(--accent) 15%, transparent); border-radius:999px; font:600 10.5px/16px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.tree-badge { flex:0 0 auto; display:grid; place-items:center; min-width:18px; height:18px; padding:0 4px; color:var(--muted); border:1px solid var(--border); border-radius:5px; font:700 11px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.tree-badge.is-mod { font-size:9px; }
.tree-badge.is-add { color:var(--add-fg); border-color:color-mix(in srgb, var(--add-fg) 45%, var(--border)); }
.tree-badge.is-del { color:var(--del-fg); border-color:color-mix(in srgb, var(--del-fg) 45%, var(--border)); }
.tree-badge.is-mod, .tree-badge.is-ren { color:var(--accent); border-color:color-mix(in srgb, var(--accent) 45%, var(--border)); }
.tree-empty { padding:18px 10px; color:var(--muted); text-align:center; }
main { max-width:1800px; margin:0 auto; padding:16px 18px 40px; overflow:visible; }
.file { margin-bottom:12px; overflow:visible; background:var(--panel); border:1px solid var(--border); border-radius:10px; scroll-margin-top:80px; box-shadow:0 1px 2px rgba(0,0,0,.12); content-visibility:auto; contain-intrinsic-size:auto 600px; }
button.file-header { all:unset; box-sizing:border-box; position:sticky; top:68px; z-index:6; display:flex; align-items:center; gap:9px; width:100%; min-height:43px; padding:10px 13px; background:var(--panel); background-clip:padding-box; border-bottom:1px solid var(--border); border-radius:9px 9px 0 0; cursor:pointer; box-shadow:0 1px 0 var(--border); transform:translateZ(0); backface-visibility:hidden; }
button.file-header:hover { background:var(--comment); }
.file.is-collapsed button.file-header { border-bottom-color:transparent; border-radius:9px; box-shadow:none; }
.file-chevron { display:grid; place-items:center; width:16px; height:18px; flex:0 0 16px; color:var(--muted); }
.file-chevron::before { content:""; width:6px; height:6px; border-right:1.5px solid currentColor; border-bottom:1.5px solid currentColor; transform:rotate(45deg) translate(-1px, -1px); transform-origin:center; transition:transform .16s ease; }
.file.is-collapsed .file-chevron::before { transform:rotate(-45deg) translate(-1px, -1px); }
.file-title { display:flex; align-items:baseline; flex:0 1 auto; min-width:0; overflow:hidden; font-family:ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size:12px; font-weight:550; }
.file-status { flex:0 0 auto; padding:1px 6px; color:var(--muted); background:var(--comment); border:1px solid var(--border); border-radius:999px; font-size:10px; text-transform:capitalize; }
.file-change-stats { display:flex; gap:7px; margin-left:auto; font:600 11px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.file-comment-count { color:var(--accent); font-size:11px; font-weight:550; }
.file-body { display:grid; grid-template-rows:1fr; min-width:0; overflow:clip; border-radius:0 0 9px 9px; opacity:1; transition:grid-template-rows .2s ease, opacity .14s ease; }
.file-body-inner { min-height:0; overflow-x:auto; overflow-y:hidden; background:var(--bg); }
@keyframes flash-file { 0% { box-shadow:inset 0 0 0 2px var(--accent); background:color-mix(in srgb, var(--accent) 16%, var(--panel)); } 100% { box-shadow:inset 0 0 0 2px transparent; background:var(--panel); } }
.file.flash-target { animation:flash-file 1.15s ease-out; }
::highlight(review-search) { background-color:color-mix(in srgb, var(--accent) 55%, transparent); color:var(--text); }
.file.is-collapsed .file-body { grid-template-rows:0fr; opacity:0; }
.hunk-header { padding:6px 13px; color:color-mix(in srgb, var(--accent) 70%, var(--text)); background:color-mix(in srgb, var(--panel) 85%, var(--accent)); border-top:1px solid var(--border); border-bottom:1px solid var(--border); font:11.5px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.hunk-header:first-child { border-top:0; }
table.diff { width:max-content; min-width:100%; border-collapse:collapse; font:12px/20px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
td { height:20px; vertical-align:top; }
td.num { position:relative; width:50px; padding:0 8px; color:color-mix(in srgb, var(--muted) 78%, transparent); text-align:right; user-select:none; border-right:1px solid color-mix(in srgb, var(--border) 72%, transparent); }
td.num.comment-target { cursor:ns-resize; }
td.code { padding:0 18px 0 0; white-space:pre; color:color-mix(in srgb, var(--text) 90%, var(--muted)); }
.code-marker { display:inline-block; width:1.35em; color:var(--muted); text-align:center; user-select:none; }
.syntax-keyword { color:var(--syntax-keyword); }
.syntax-string { color:var(--syntax-string); }
.syntax-comment { color:var(--syntax-comment); font-style:italic; }
.syntax-number { color:var(--syntax-number); }
.syntax-type { color:var(--syntax-type); }
.syntax-function { color:var(--syntax-function); }
.syntax-attribute { color:var(--syntax-attribute); }
.syntax-tag { color:var(--syntax-tag); }
.syntax-property { color:var(--syntax-property); }
.syntax-selector { color:var(--syntax-selector); }
.syntax-operator { color:var(--syntax-operator); }
tr.line { background:var(--bg); }
tr.line:hover { background:var(--comment); }
tr.add { background:var(--add-bg); }
tr.add td.code, tr.add .code-marker { color:var(--add-fg); }
tr.delete { background:var(--del-bg); }
tr.delete td.code, tr.delete .code-marker { color:var(--del-fg); }
tr.meta-line { color:var(--muted); }
tr.line.range-anchor td.num { color:var(--accent); }
tr.line.range-selected td { background:color-mix(in srgb, var(--accent) 17%, var(--bg)) !important; }
tr.line.range-selected td.code { color:var(--text); }
tr.line.range-selected .code-marker { color:var(--accent); }
tr.line.commented-range td { background:color-mix(in srgb, var(--accent) 10%, var(--bg)) !important; }
tr.line.commented-range .code-marker { color:var(--accent); }
.comment-row td { height:auto; padding:10px 12px; background:color-mix(in srgb, var(--comment) 92%, var(--accent)); border-top:1px solid var(--border); border-bottom:1px solid var(--border); }
.comment-row td.comment-cell { width:max(120px, calc(var(--diff-viewport-width, 100vw) - var(--comment-left-offset, 128px) - 28px)); max-width:max(120px, calc(var(--diff-viewport-width, 100vw) - var(--comment-left-offset, 128px) - 28px)); overflow:hidden; }
.comment { width:min(900px, max(120px, calc(var(--diff-viewport-width, 100vw) - var(--comment-left-offset, 128px) - 28px))); max-width:100%; margin:3px 0; padding:10px 11px; overflow-wrap:anywhere; white-space:pre-wrap; background:var(--panel); border:1px solid var(--border); border-radius:8px; }
.comment-header { display:flex; align-items:center; justify-content:space-between; gap:12px; margin-bottom:5px; }
.comment-meta, .range-help { color:var(--muted); font-size:11.5px; white-space:normal; }
.range-help { margin-bottom:8px; }
.comment-form { display:flex; flex-direction:column; gap:8px; width:min(900px, max(120px, calc(var(--diff-viewport-width, 100vw) - var(--comment-left-offset, 128px) - 28px))); max-width:100%; min-width:0; }
.comment-actions { display:flex; flex-wrap:wrap; gap:7px; justify-content:flex-end; max-width:100%; }
textarea { display:block; width:100%; min-width:0; min-height:92px; resize:vertical; color:var(--text); background:var(--bg); border:1px solid var(--border); border-radius:8px; padding:9px 10px; }
textarea::placeholder { color:var(--muted); }
button { color:white; background:var(--accent); border:0; border-radius:7px; padding:7px 10px; font-weight:600; cursor:pointer; }
button.secondary { color:var(--text); background:var(--comment); border:1px solid var(--border); }
button.remove-comment { color:var(--muted); background:transparent; padding:2px 6px; font-size:11px; font-weight:500; }
button.remove-comment:hover { color:var(--del-fg); background:var(--del-bg); }
.sidebar-actions { margin-top:8px; }
.sidebar-actions button { width:100%; color:var(--del-fg); background:var(--del-bg); }
button.line-plus { all:unset; box-sizing:border-box; display:inline-grid; place-items:center; position:absolute; right:4px; top:50%; z-index:1; width:18px; height:18px; color:white; background:var(--accent); border-radius:5px; font:700 13px/18px ui-sans-serif, system-ui; cursor:ns-resize; opacity:0; transform:translateY(-50%) scale(.92); box-shadow:0 2px 5px rgba(0,0,0,.35); transition:opacity .08s ease, transform .08s ease; }
tr.line:hover td.comment-target .line-number-text, td.comment-target:has(button.line-plus:focus-visible) .line-number-text { opacity:0; }
tr.line:hover button.line-plus, button.line-plus:focus-visible { opacity:1; transform:translateY(-50%) scale(1); }
button.line-plus:active { transform:translateY(-50%) scale(.94); }
body.is-dragging-comment button.line-plus { pointer-events:none; }
.activity-pill { position:fixed; left:50%; bottom:20px; z-index:40; display:flex; align-items:center; gap:10px; min-height:40px; max-width:calc(100vw - 24px); padding:8px 12px; color:var(--text); background:color-mix(in srgb, var(--panel) 94%, black); border:1px solid color-mix(in srgb, var(--accent) 35%, var(--border)); border-radius:999px; box-shadow:0 14px 44px rgba(0,0,0,.45), 0 1px 0 rgba(255,255,255,.05) inset; transform:translateX(-50%) translateZ(0); backface-visibility:hidden; cursor:pointer; }
.activity-pill:hover { background:color-mix(in srgb, var(--panel) 88%, var(--accent)); border-color:color-mix(in srgb, var(--accent) 58%, var(--border)); }
.activity-pill[hidden] { display:none; }
.activity-dot { width:8px; height:8px; flex:0 0 auto; background:var(--accent); border-radius:999px; box-shadow:0 0 0 0 color-mix(in srgb, var(--accent) 35%, transparent); animation:activity-pulse 1.4s ease-out infinite; }
.activity-label { font-size:12px; font-weight:650; white-space:nowrap; }
.activity-summary { min-width:0; overflow:hidden; color:var(--muted); font-size:11.5px; text-overflow:ellipsis; white-space:nowrap; }
.activity-stats { display:flex; gap:7px; flex:0 0 auto; padding-left:2px; font:600 11.5px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
@keyframes activity-pulse { 0% { box-shadow:0 0 0 0 color-mix(in srgb, var(--accent) 38%, transparent); } 70%, 100% { box-shadow:0 0 0 7px transparent; } }
.empty, .error { display:grid; place-items:center; min-height:220px; padding:32px; color:var(--muted); text-align:center; background:var(--panel); border:1px dashed var(--border); border-radius:10px; }
.error { color:var(--del-fg); }
@media (max-width:760px) { header { padding:10px 12px; } .branch-comparison { max-width:34vw; } .file-menu-button { margin-left:auto; } main { padding:12px; } .theme-wrap { display:none; } }
@media (prefers-reduced-motion:reduce) { .file-body, .file-chevron::before, .chevron-down { transition:none; } .activity-dot, .mode-option.is-live .mode-check, .file.flash-target { animation:none; } }
</style>
</head>
<body>
<header>
  <div class="topbar">
    <div class="review-controls">
      <div class="scope-control">
        <button class="scope-trigger" id="scope-trigger" data-action="toggle-mode-list" aria-expanded="false">
          <span id="mode-label">Branch</span><span class="chevron-down">▼</span>
        </button>
        <div class="mode-popover" id="mode-popover" hidden></div>
      </div>
      <div class="diff-stats" aria-label="Diff statistics"><span class="additions" id="additions">+0</span><span class="deletions" id="deletions">−0</span></div>
      <div class="branch-comparison" id="branch-comparison"></div>
      <button class="file-menu-button" id="file-menu-button" data-action="toggle-file-list" title="Files" aria-label="Files">
        <svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M21 12h-8"/><path d="M21 6H8"/><path d="M21 18h-8"/><path d="M3 6v4c0 1.1 .9 2 2 2h3"/><path d="M3 10v6c0 1.1 .9 2 2 2h3"/></svg>
        <span id="file-count">0</span>
      </button>
      <button class="collapse-toggle" id="collapse-toggle" data-action="toggle-collapse-all" title="Collapse all files" aria-label="Collapse all files">
        <svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m7 20 5-5 5 5"/><path d="m7 4 5 5 5-5"/></svg>
      </button>
      <div class="theme-wrap"><select class="theme-select" id="theme-select" aria-label="Theme"></select></div>
    </div>
  </div>
</header>
<div class="file-popover" id="file-popover" hidden>
  <div class="file-filter-wrap">
    <svg class="file-filter-icon" width="14" height="14" viewBox="0 0 16 16" aria-hidden="true"><path d="M7 1a6 6 0 0 1 4.74 9.67l3.29 3.3a.75.75 0 0 1-1.06 1.06l-3.3-3.29A6 6 0 1 1 7 1zm0 1.5a4.5 4.5 0 1 0 0 9 4.5 4.5 0 0 0 0-9z" fill="currentColor"/></svg>
    <input id="file-filter" type="search" autocomplete="off" spellcheck="false" placeholder="Filter files &amp; contents…" aria-label="Filter files and contents" />
  </div>
  <div id="file-list" class="file-tree"></div>
  <div class="status" id="status"></div>
</div>
<main id="content"></main>
<button class="activity-pill" id="activity-pill" type="button" data-action="select-mode" data-mode="active-turn" aria-live="polite" title="View changes in the active turn" hidden>
  <span class="activity-dot"></span>
  <span class="activity-label">Pi is working</span>
  <span class="activity-summary" id="activity-summary">Watching this turn…</span>
  <span class="activity-stats"><span class="additions" id="activity-additions">+0</span><span class="deletions" id="activity-deletions">−0</span></span>
</button>
<script>
const reviewId = location.pathname.split('/').pop();
const hash = new URLSearchParams(location.hash.slice(1));
let token = hash.get('token') || sessionStorage.getItem('pi-review-token-' + reviewId);
if (token) {
  sessionStorage.setItem('pi-review-token-' + reviewId, token);
  history.replaceState(null, '', location.pathname);
}
const headers = () => ({ 'Authorization': 'Bearer ' + token, 'Content-Type': 'application/json' });
const THEMES = [
  { id:'linear-dark', label:'Linear Dark', scheme:'dark', colors:{ bg:'#0d0e10', panel:'#131416', text:'#e8e9eb', muted:'#8a8f98', accent:'#8b7cff', addBg:'#10251b', addFg:'#56c991', delBg:'#2a171a', delFg:'#f06d7a', border:'#292b30', comment:'#1a1c20' } },
  { id:'light-modern', label:'Light Modern', scheme:'light', colors:{ bg:'#ffffff', panel:'#f3f3f3', text:'#1f2328', muted:'#6e7781', accent:'#0969da', addBg:'#dafbe1', addFg:'#116329', delBg:'#ffebe9', delFg:'#cf222e', border:'#d0d7de', comment:'#f6f8fa' } },
  { id:'dark-plus', label:'Dark+', scheme:'dark', colors:{ bg:'#1e1e1e', panel:'#252526', text:'#d4d4d4', muted:'#858585', accent:'#3794ff', addBg:'#122b1b', addFg:'#89d185', delBg:'#331b1b', delFg:'#f48771', border:'#3c3c3c', comment:'#22272e' } },
  { id:'light-plus', label:'Light+', scheme:'light', colors:{ bg:'#ffffff', panel:'#f3f3f3', text:'#24292f', muted:'#6a737d', accent:'#0366d6', addBg:'#e6ffed', addFg:'#22863a', delBg:'#ffeef0', delFg:'#cb2431', border:'#d1d5da', comment:'#f6f8fa' } },
  { id:'visual-studio-dark', label:'Visual Studio Dark', scheme:'dark', colors:{ bg:'#1e1e1e', panel:'#2d2d30', text:'#cccccc', muted:'#969696', accent:'#007acc', addBg:'#12301d', addFg:'#6a9955', delBg:'#3a1f1f', delFg:'#ce9178', border:'#3f3f46', comment:'#252526' } },
  { id:'visual-studio-light', label:'Visual Studio Light', scheme:'light', colors:{ bg:'#ffffff', panel:'#eeeeee', text:'#000000', muted:'#666666', accent:'#007acc', addBg:'#eaffea', addFg:'#008000', delBg:'#ffdddd', delFg:'#a31515', border:'#dddddd', comment:'#f5f5f5' } },
  { id:'quiet-light', label:'Quiet Light', scheme:'light', colors:{ bg:'#f5f5f5', panel:'#ececec', text:'#333333', muted:'#777777', accent:'#4d8fd6', addBg:'#e2f7e2', addFg:'#448c27', delBg:'#ffe2e2', delFg:'#aa3731', border:'#cfcfcf', comment:'#eeeeee' } },
  { id:'solarized-light', label:'Solarized Light', scheme:'light', colors:{ bg:'#fdf6e3', panel:'#eee8d5', text:'#657b83', muted:'#93a1a1', accent:'#268bd2', addBg:'#e4efd0', addFg:'#859900', delBg:'#f4d6cf', delFg:'#dc322f', border:'#d8cfb6', comment:'#eee8d5' } },
  { id:'solarized-dark', label:'Solarized Dark', scheme:'dark', colors:{ bg:'#002b36', panel:'#073642', text:'#839496', muted:'#586e75', accent:'#268bd2', addBg:'#063f35', addFg:'#859900', delBg:'#4b2023', delFg:'#dc322f', border:'#16424d', comment:'#073642' } },
  { id:'monokai', label:'Monokai', scheme:'dark', colors:{ bg:'#272822', panel:'#1e1f1c', text:'#f8f8f2', muted:'#90908a', accent:'#66d9ef', addBg:'#2f3d20', addFg:'#a6e22e', delBg:'#4a1f2a', delFg:'#f92672', border:'#3e3d32', comment:'#2f3029' } },
  { id:'monokai-dimmed', label:'Monokai Dimmed', scheme:'dark', colors:{ bg:'#1f1f1f', panel:'#252526', text:'#c5c8c6', muted:'#888888', accent:'#66d9ef', addBg:'#28351f', addFg:'#a6e22e', delBg:'#3a2028', delFg:'#f92672', border:'#3a3a3a', comment:'#2b2b2b' } },
  { id:'abyss', label:'Abyss', scheme:'dark', colors:{ bg:'#000c18', panel:'#07111f', text:'#d9e6f2', muted:'#6688aa', accent:'#66ccff', addBg:'#062319', addFg:'#22aa66', delBg:'#271320', delFg:'#ff6677', border:'#12324d', comment:'#081a2b' } },
  { id:'kimbie-dark', label:'Kimbie Dark', scheme:'dark', colors:{ bg:'#221a0f', panel:'#2b2115', text:'#d3af86', muted:'#8a7a63', accent:'#dc3958', addBg:'#2d2b17', addFg:'#889b4a', delBg:'#3a1b17', delFg:'#dc3958', border:'#51412c', comment:'#2b2115' } },
  { id:'red', label:'Red', scheme:'dark', colors:{ bg:'#390000', panel:'#2a0000', text:'#f8d7da', muted:'#d98a8a', accent:'#ff6666', addBg:'#17351f', addFg:'#7ee787', delBg:'#4f1111', delFg:'#ff9b9b', border:'#662222', comment:'#451010' } },
  { id:'tomorrow-night-blue', label:'Tomorrow Night Blue', scheme:'dark', colors:{ bg:'#002451', panel:'#001f46', text:'#ffffff', muted:'#7285b7', accent:'#ffc58f', addBg:'#123b3b', addFg:'#d1f1a9', delBg:'#45233c', delFg:'#ff9da4', border:'#00346e', comment:'#002b60' } },
  { id:'default-high-contrast', label:'Default High Contrast', scheme:'dark', colors:{ bg:'#000000', panel:'#000000', text:'#ffffff', muted:'#c0c0c0', accent:'#ffff00', addBg:'#003000', addFg:'#00ff00', delBg:'#3a0000', delFg:'#ff8080', border:'#6fc3df', comment:'#101010' } },
  { id:'default-high-contrast-light', label:'Default High Contrast Light', scheme:'light', colors:{ bg:'#ffffff', panel:'#ffffff', text:'#000000', muted:'#333333', accent:'#0f4a85', addBg:'#dfffe0', addFg:'#006b00', delBg:'#ffe0e0', delFg:'#a00000', border:'#0f4a85', comment:'#f2f2f2' } },
  { id:'dark-2026', label:'Dark 2026', scheme:'dark', colors:{ bg:'#181818', panel:'#202020', text:'#d7d7d7', muted:'#8f8f8f', accent:'#4daafc', addBg:'#10281a', addFg:'#79c991', delBg:'#30191c', delFg:'#ff8f8f', border:'#353535', comment:'#242424' } },
  { id:'light-2026', label:'Light 2026', scheme:'light', colors:{ bg:'#ffffff', panel:'#f7f7f7', text:'#1f1f1f', muted:'#666666', accent:'#005fb8', addBg:'#e4f6e7', addFg:'#187a36', delBg:'#fde7e9', delFg:'#c42b1c', border:'#d6d6d6', comment:'#f5f5f5' } },
];
function applyTheme(themeId) {
  const theme = THEMES.find(candidate => candidate.id === themeId) || THEMES[0];
  document.body.dataset.theme = theme.id;
  document.body.dataset.scheme = theme.scheme;
  document.body.style.colorScheme = theme.scheme;
  for (const [key, value] of Object.entries(theme.colors)) {
    document.body.style.setProperty('--' + key.replace(/[A-Z]/g, letter => '-' + letter.toLowerCase()), value);
  }
  localStorage.setItem('pi-review-diff-theme', theme.id);
  const select = document.getElementById('theme-select');
  if (select) select.value = theme.id;
}
function initTheme() {
  const select = document.getElementById('theme-select');
  if (!select) return;
  select.innerHTML = THEMES.map(theme => '<option value="' + theme.id + '">' + theme.label + '</option>').join('');
  select.addEventListener('change', () => applyTheme(select.value));
  applyTheme(localStorage.getItem('pi-review-diff-theme') || 'linear-dark');
}
initTheme();
let review;
let turnActivity = { running:false, filesChanged:0, additions:0, deletions:0, files:[] };
let activeReviewRefreshRunning = false;
let activeReviewRefreshQueued = false;
let dragState = null;
let activeFilePath = null;
let activeFileTimer = null;
let diffResizeObserver = null;
let fileBodyObserver = null;
const collapsedFiles = new Set();
const collapsedTreeDirs = new Set();
const ICON_COLLAPSE_ALL = '<svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m7 20 5-5 5 5"/><path d="m7 4 5 5 5-5"/></svg>';
const ICON_EXPAND_ALL = '<svg viewBox="0 0 24 24" width="15" height="15" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m7 15 5 5 5-5"/><path d="m7 9 5-5 5 5"/></svg>';
function valueOrEmpty(value) { return value === undefined || value === null ? '' : String(value); }
function keyFor(filePath, hunkHeader, line) { return filePath + '|' + hunkHeader + '|' + valueOrEmpty(line.oldLine) + '|' + valueOrEmpty(line.newLine); }
function escapeHtml(s) { return String(s ?? '').replace(/[&<>"']/g, ch => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[ch])); }
function pathLabelHtml(path) {
  const clean = String(path ?? '');
  const slash = clean.lastIndexOf('/');
  const name = slash < 0 ? clean : clean.slice(slash + 1);
  const dir = slash < 0 ? '' : clean.slice(0, slash + 1);
  const dirHtml = dir ? '<span class="path-dir"><bdi>' + escapeHtml(dir) + '</bdi></span>' : '';
  return dirHtml + '<span class="path-name">' + escapeHtml(name) + '</span>';
}
function syntaxSpan(kind, value) { return '<span class="syntax-' + kind + '">' + escapeHtml(value) + '</span>'; }
function isIdentifierStart(char) { return Boolean(char && /[A-Za-z_$]/.test(char)); }
function isIdentifierPart(char) { return Boolean(char && /[A-Za-z0-9_$]/.test(char)); }
function nextNonSpace(line, index) { while (index < line.length && /\s/.test(line[index])) index += 1; return line[index]; }
function highlightCLike(line, keywords) {
  let html = '';
  let index = 0;
  while (index < line.length) {
    const char = line[index];
    const pair = line.slice(index, index + 2);
    if (pair === '//' || pair === '/*') {
      const end = pair === '/*' ? line.indexOf('*/', index + 2) : -1;
      const stop = end >= 0 ? end + 2 : line.length;
      html += syntaxSpan('comment', line.slice(index, stop));
      index = stop;
      continue;
    }
    if (char === '"' || char === "'" || char.charCodeAt(0) === 96) {
      const quote = char;
      let stop = index + 1;
      while (stop < line.length) {
        if (line[stop] === '\\') { stop += 2; continue; }
        if (line[stop] === quote) { stop += 1; break; }
        stop += 1;
      }
      html += syntaxSpan('string', line.slice(index, stop));
      index = stop;
      continue;
    }
    if (/\d/.test(char) && (index === 0 || !isIdentifierPart(line[index - 1]))) {
      const match = line.slice(index).match(/^(?:0[xX][\da-fA-F]+|0[bB][01]+|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)/);
      const value = match ? match[0] : char;
      html += syntaxSpan('number', value);
      index += value.length;
      continue;
    }
    if ((char === '@' || char === '#') && isIdentifierStart(line[index + 1])) {
      let stop = index + 2;
      while (isIdentifierPart(line[stop])) stop += 1;
      html += syntaxSpan('attribute', line.slice(index, stop));
      index = stop;
      continue;
    }
    if (isIdentifierStart(char)) {
      let stop = index + 1;
      while (isIdentifierPart(line[stop])) stop += 1;
      const value = line.slice(index, stop);
      let kind = '';
      if (keywords.has(value)) kind = 'keyword';
      else if (/^[A-Z]/.test(value)) kind = 'type';
      else if (nextNonSpace(line, stop) === '(') kind = 'function';
      html += kind ? syntaxSpan(kind, value) : escapeHtml(value);
      index = stop;
      continue;
    }
    if ('=+-*/%!?&|^~<>:.'.includes(char)) html += syntaxSpan('operator', char);
    else html += escapeHtml(char);
    index += 1;
  }
  return html;
}
function highlightHtmlTag(tag) {
  let html = '';
  let index = 0;
  let sawTagName = false;
  while (index < tag.length) {
    const char = tag[index];
    if ('<>/='.includes(char)) {
      html += syntaxSpan('operator', char);
      index += 1;
      continue;
    }
    if (char === '"' || char === "'") {
      let stop = index + 1;
      while (stop < tag.length) {
        if (tag[stop] === '\\') { stop += 2; continue; }
        if (tag[stop] === char) { stop += 1; break; }
        stop += 1;
      }
      html += syntaxSpan('string', tag.slice(index, stop));
      index = stop;
      continue;
    }
    if (/[A-Za-z!:_-]/.test(char)) {
      let stop = index + 1;
      while (stop < tag.length && /[A-Za-z0-9:_.-]/.test(tag[stop])) stop += 1;
      const value = tag.slice(index, stop);
      html += syntaxSpan(sawTagName ? 'attribute' : 'tag', value);
      sawTagName = true;
      index = stop;
      continue;
    }
    html += escapeHtml(char);
    index += 1;
  }
  return html;
}
function highlightHtml(line) {
  let html = '';
  let index = 0;
  while (index < line.length) {
    if (line.startsWith('<!--', index)) {
      const end = line.indexOf('-->', index + 4);
      const stop = end >= 0 ? end + 3 : line.length;
      html += syntaxSpan('comment', line.slice(index, stop));
      index = stop;
      continue;
    }
    if (line[index] === '<') {
      const end = line.indexOf('>', index + 1);
      const stop = end >= 0 ? end + 1 : line.length;
      html += highlightHtmlTag(line.slice(index, stop));
      index = stop;
      continue;
    }
    const nextTag = line.indexOf('<', index);
    const stop = nextTag >= 0 ? nextTag : line.length;
    html += escapeHtml(line.slice(index, stop));
    index = stop;
  }
  return html;
}
function highlightCss(line) {
  let html = '';
  let index = 0;
  const firstBrace = line.indexOf('{');
  while (index < line.length) {
    const char = line[index];
    if (line.slice(index, index + 2) === '/*') {
      const end = line.indexOf('*/', index + 2);
      const stop = end >= 0 ? end + 2 : line.length;
      html += syntaxSpan('comment', line.slice(index, stop));
      index = stop;
      continue;
    }
    if (char === '"' || char === "'") {
      let stop = index + 1;
      while (stop < line.length) {
        if (line[stop] === '\\') { stop += 2; continue; }
        if (line[stop] === char) { stop += 1; break; }
        stop += 1;
      }
      html += syntaxSpan('string', line.slice(index, stop));
      index = stop;
      continue;
    }
    const color = line.slice(index).match(/^#[\da-fA-F]{3,8}\b/);
    if (color) {
      html += syntaxSpan('number', color[0]);
      index += color[0].length;
      continue;
    }
    const number = line.slice(index).match(/^\d+(?:\.\d+)?(?:%|[A-Za-z]+)?/);
    if (number) {
      html += syntaxSpan('number', number[0]);
      index += number[0].length;
      continue;
    }
    if (/[A-Za-z_@!.-]/.test(char)) {
      let stop = index + 1;
      while (stop < line.length && /[A-Za-z0-9_@!.-]/.test(line[stop])) stop += 1;
      const value = line.slice(index, stop);
      const next = nextNonSpace(line, stop);
      const kind = value[0] === '@' || value === '!important' ? 'keyword' : next === ':' ? 'property' : (firstBrace < 0 || index < firstBrace) ? 'selector' : '';
      html += kind ? syntaxSpan(kind, value) : escapeHtml(value);
      index = stop;
      continue;
    }
    if ('{}:;>,+~='.includes(char)) html += syntaxSpan('operator', char);
    else html += escapeHtml(char);
    index += 1;
  }
  return html;
}
const SYNTAX_LANGUAGES = [
  { id:'swift', extensions:['swift'], keywords:new Set('actor any associatedtype as async await break case catch class continue convenience default defer deinit do dynamic else enum extension fallthrough false fileprivate final for func get guard if import in indirect init inout internal is isolated lazy let mutating nil nonisolated open operator override private protocol public repeat required rethrows return self some static struct subscript super switch throws true try typealias var weak where while willSet didSet'.split(' ')) },
  { id:'kotlin', extensions:['kt','kts'], keywords:new Set('as break by catch class companion const constructor continue crossinline data delegate do dynamic else enum expect external false field file final finally for fun get if import in infix init inline inner interface internal is lateinit noinline null object open operator out override package private protected public reified return sealed set suspend super tailrec this throw true try typealias typeof val var vararg when where while'.split(' ')) },
  { id:'typescript', extensions:['ts','tsx','mts','cts'], keywords:new Set('abstract any as assert asserts async await bigint boolean break case catch class const constructor continue debugger declare default delete do else enum export extends false finally for from function get if implements import in infer instanceof interface is keyof let module namespace never new null number object of override private protected public readonly require return satisfies set static string super switch symbol this throw true try type typeof undefined unique unknown using var void while with yield'.split(' ')) },
  { id:'javascript', extensions:['js','jsx','mjs','cjs'], keywords:new Set('as async await break case catch class const continue debugger default delete do else export extends false finally for from function get if import in instanceof let new null of return set static super switch this throw true try typeof undefined var void while with yield'.split(' ')) },
  { id:'html', extensions:['html','htm'], highlight:highlightHtml },
  { id:'css', extensions:['css'], highlight:highlightCss },
];
const SYNTAX_BY_EXTENSION = new Map();
for (const language of SYNTAX_LANGUAGES) for (const extension of language.extensions) SYNTAX_BY_EXTENSION.set(extension, language);
function highlightCodeLine(filePath, line) {
  const cleanPath = String(filePath || '').split(/[?#]/)[0];
  const extension = cleanPath.includes('.') ? cleanPath.split('.').pop().toLowerCase() : '';
  const language = SYNTAX_BY_EXTENSION.get(extension);
  const source = String(line ?? '');
  if (!language) return escapeHtml(source);
  return language.highlight ? language.highlight(source) : highlightCLike(source, language.keywords);
}
async function api(path, opts = {}) {
  if (!token) throw new Error('Missing review token');
  const res = await fetch(path, { ...opts, headers: { ...headers(), ...(opts.headers || {}) } });
  const body = await res.json().catch(() => ({}));
  if (!res.ok) throw new Error(body.error || res.statusText);
  return body;
}
async function refreshActiveTurnReview() {
  if (!review || review.mode !== 'active-turn') return;
  if (activeReviewRefreshRunning) {
    activeReviewRefreshQueued = true;
    return;
  }
  activeReviewRefreshRunning = true;
  try {
    await loadReview();
  } catch (_error) {
    // The next activity event or version poll will retry.
  } finally {
    activeReviewRefreshRunning = false;
    if (activeReviewRefreshQueued) {
      activeReviewRefreshQueued = false;
      void refreshActiveTurnReview();
    }
  }
}
function renderTurnActivity(activity) {
  turnActivity = { running:false, filesChanged:0, additions:0, deletions:0, files:[], ...(activity || {}) };
  const pill = document.getElementById('activity-pill');
  if (!turnActivity.running) {
    pill.hidden = true;
    if (review?.mode === 'active-turn') void refreshActiveTurnReview();
    else if (review) renderModeMenu();
    return;
  }
  const filesChanged = Number(turnActivity.filesChanged || 0);
  document.getElementById('activity-summary').textContent = filesChanged ? filesChanged + ' file' + (filesChanged === 1 ? '' : 's') + ' changed' : 'Watching this turn…';
  document.getElementById('activity-additions').textContent = '+' + Number(turnActivity.additions || 0);
  document.getElementById('activity-deletions').textContent = '−' + Number(turnActivity.deletions || 0);
  pill.hidden = false;
  if (review) renderModeMenu();
  if (review?.mode === 'active-turn') void refreshActiveTurnReview();
}
async function connectActivityStream() {
  while (true) {
    try {
      const response = await fetch('/api/reviews/' + reviewId + '/activity', { headers:headers() });
      if (!response.ok || !response.body) throw new Error('Activity stream unavailable');
      const reader = response.body.getReader();
      const decoder = new TextDecoder();
      let buffer = '';
      while (true) {
        const result = await reader.read();
        if (result.done) throw new Error('Activity stream ended');
        buffer += decoder.decode(result.value, { stream:true });
        const frames = buffer.split('\n\n');
        buffer = frames.pop() || '';
        for (const frame of frames) {
          const data = frame.split('\n').filter(line => line.startsWith('data:')).map(line => line.slice(5).trim()).join('\n');
          if (data) renderTurnActivity(JSON.parse(data));
        }
      }
    } catch (_error) {
      renderTurnActivity({ running:false });
      await new Promise(resolve => setTimeout(resolve, 1000));
    }
  }
}
function lineSide(line) {
  if (line.kind === 'delete') return 'old';
  if (line.kind === 'add') return 'new';
  return 'context';
}
function lineMarker(line) {
  if (line.kind === 'add') return '+';
  if (line.kind === 'delete') return '-';
  if (line.kind === 'meta') return '\\';
  return ' ';
}
function rangeText(start, end) {
  if (start === undefined || start === null) return '';
  if (end === undefined || end === null || end === start) return String(start);
  return String(start) + '-' + String(end);
}
function commentLocation(comment) {
  const oldRange = rangeText(comment.oldLine, comment.oldEndLine);
  const newRange = rangeText(comment.newLine, comment.newEndLine);
  if (comment.side === 'mixed' && oldRange && newRange) return 'old ' + oldRange + ', new ' + newRange;
  return newRange || oldRange || '?';
}
function numberInRange(value, start, end) {
  return typeof value === 'number' && value > 0 && typeof start === 'number' && start > 0 && value >= start && value <= (typeof end === 'number' ? end : start);
}
function lineMatchesComment(comment, line) {
  const matchesOld = numberInRange(line.oldLine, comment.oldLine, comment.oldEndLine);
  const matchesNew = numberInRange(line.newLine, comment.newLine, comment.newEndLine);
  if (comment.side === 'old') return matchesOld;
  if (comment.side === 'new') return matchesNew;
  if (comment.side === 'context') return matchesNew || matchesOld;
  return matchesOld || matchesNew;
}
function isMultiLineComment(comment) {
  return (typeof comment.oldLine === 'number' && typeof comment.oldEndLine === 'number' && comment.oldEndLine !== comment.oldLine) ||
    (typeof comment.newLine === 'number' && typeof comment.newEndLine === 'number' && comment.newEndLine !== comment.newLine) ||
    String(comment.lineContent || '').includes('\n');
}
function selectedIndicesForComment(comment, hunk) {
  const indices = [];
  hunk.lines.forEach((line, index) => {
    if (line.kind !== 'meta' && lineMatchesComment(comment, line)) indices.push(index);
  });
  return indices;
}
function commentsForAnchor(filePath, hunk, lineIndex) {
  return pendingComments().filter(comment => {
    if (comment.filePath !== filePath || comment.hunkHeader !== hunk.header) return false;
    const indices = selectedIndicesForComment(comment, hunk);
    return indices.length > 0 && indices[indices.length - 1] === lineIndex;
  });
}
function hasMultiLineCommentOnLine(filePath, hunk, line) {
  return pendingComments().some(comment =>
    comment.filePath === filePath &&
    comment.hunkHeader === hunk.header &&
    isMultiLineComment(comment) &&
    lineMatchesComment(comment, line)
  );
}
function pendingComments() { return (review.comments || []).filter(c => c.status === 'pending'); }
function statsForFile(file) {
  let additions = 0;
  let deletions = 0;
  for (const hunk of file.hunks) {
    for (const line of hunk.lines) {
      if (line.kind === 'add') additions += 1;
      if (line.kind === 'delete') deletions += 1;
    }
  }
  return { additions, deletions };
}
function renderModeMenu() {
  const popover = document.getElementById('mode-popover');
  const modes = (review.modes || []).filter(mode => mode.id !== 'active-turn');
  if (turnActivity.running || review.mode === 'active-turn') {
    const count = Number(turnActivity.filesChanged || 0);
    modes.unshift({
      id:'active-turn',
      label:'Active turn',
      description:count ? count + ' file' + (count === 1 ? '' : 's') + ' changing · +' + Number(turnActivity.additions || 0) + ' −' + Number(turnActivity.deletions || 0) : 'Watching the current Pi turn',
      available:Boolean(turnActivity.running),
      files:(turnActivity.files || []).map(file => file.path),
    });
  }
  popover.innerHTML = modes.map(mode => {
    const selected = mode.id === review.mode;
    const isLive = mode.id === 'active-turn' && turnActivity.running;
    const fileSummary = mode.files?.length ? '<span class="mode-files">' + escapeHtml(mode.files.slice(0, 4).join(' · ') + (mode.files.length > 4 ? ' · +' + (mode.files.length - 4) : '')) + '</span>' : '';
    return '<button class="mode-option' + (isLive ? ' is-live' : '') + '" data-action="select-mode" data-mode="' + escapeHtml(mode.id) + '"' + (mode.available ? '' : ' disabled') + '>' +
      '<span class="mode-check">' + (selected ? '✓' : isLive ? '●' : '') + '</span>' +
      '<span class="mode-label">' + escapeHtml(mode.label) + '</span>' +
      '<span class="mode-description">' + escapeHtml(mode.description) + '</span>' + fileSummary +
    '</button>';
  }).join('');
  document.getElementById('mode-label').textContent = review.modeLabel || 'Changes';
}
function collapsePathFor(file) { return file.newPath === '/dev/null' ? file.oldPath : file.newPath; }
function allFilesCollapsed() {
  const files = review?.files || [];
  return files.length > 0 && files.every(file => collapsedFiles.has(collapsePathFor(file)));
}
function updateCollapseToggle() {
  const btn = document.getElementById('collapse-toggle');
  if (!btn) return;
  btn.hidden = !(review?.files?.length);
  const allCollapsed = allFilesCollapsed();
  btn.innerHTML = allCollapsed ? ICON_EXPAND_ALL : ICON_COLLAPSE_ALL;
  const label = allCollapsed ? 'Expand all files' : 'Collapse all files';
  btn.title = label;
  btn.setAttribute('aria-label', label);
}
function setAllFilesCollapsed(collapsed) {
  const files = review?.files || [];
  if (!files.length) return;
  for (const file of files) {
    const path = collapsePathFor(file);
    if (collapsed) collapsedFiles.add(path); else collapsedFiles.delete(path);
  }
  document.querySelectorAll('.file').forEach(section => {
    const header = section.querySelector('.file-header');
    section.classList.toggle('is-collapsed', collapsed);
    if (header) header.setAttribute('aria-expanded', collapsed ? 'false' : 'true');
  });
  clearOpenForms();
  if (!collapsed) { observeFileBodies(); renderVisibleFileBodies(); }
  else if (fileBodyObserver) fileBodyObserver.disconnect();
  updateCollapseToggle();
}
function fuzzyMatch(query, text) {
  const q = String(query).toLowerCase();
  const t = String(text).toLowerCase();
  if (!q) return true;
  if (t.includes(q)) return true;
  let qi = 0;
  for (let ti = 0; ti < t.length && qi < q.length; ti++) if (t[ti] === q[qi]) qi++;
  return qi === q.length;
}
function contentMatchCount(file, query) {
  const q = String(query).toLowerCase();
  if (!q) return 0;
  let count = 0;
  for (const hunk of file.hunks || []) for (const line of hunk.lines || []) {
    if (line.content && String(line.content).toLowerCase().includes(q)) count++;
  }
  return count;
}
function fileMatchesFilter(file, query) {
  if (!query) return true;
  const path = collapsePathFor(file);
  const name = path.split('/').pop();
  if (path.toLowerCase().includes(query.toLowerCase())) return true;
  if (fuzzyMatch(query, name)) return true;
  return contentMatchCount(file, query) > 0;
}
function buildFileTree(files) {
  const root = { name:'', path:'', dirs:new Map(), files:[] };
  for (const file of files) {
    const index = review.files.indexOf(file);
    const path = collapsePathFor(file);
    const parts = path.split('/');
    const name = parts.pop();
    let node = root;
    let acc = '';
    for (const part of parts) {
      acc = acc ? acc + '/' + part : part;
      if (!node.dirs.has(part)) node.dirs.set(part, { name:part, path:acc, dirs:new Map(), files:[] });
      node = node.dirs.get(part);
    }
    node.files.push({ file, index, name, path });
  }
  return root;
}
function compressDir(node) {
  const segments = [node.name];
  let current = node;
  while (current.files.length === 0 && current.dirs.size === 1) {
    const only = current.dirs.values().next().value;
    segments.push(only.name);
    current = only;
  }
  return { segments, node:current };
}
function fileIconHtml() {
  return '<svg class="tree-file-icon" width="12" height="14" viewBox="0 0 12 14" aria-hidden="true"><path d="M2 0h5l5 5v8a1 1 0 0 1-1 1H2a1 1 0 0 1-1-1V1a1 1 0 0 1 1-1z" fill="currentColor" opacity=".5"/></svg>';
}
function statusBadgeHtml(status) {
  const map = { added:['+','is-add'], deleted:['−','is-del'], modified:['•','is-mod'], renamed:['→','is-ren'], binary:['◆','is-mod'], unknown:['•','is-mod'] };
  const entry = map[status] || map.unknown;
  return '<span class="tree-badge ' + entry[1] + '" title="' + escapeHtml(status) + '">' + entry[0] + '</span>';
}
function fileNameLabel(name) {
  const dot = name.lastIndexOf('.');
  if (dot <= 0) return '<span class="fn-stem">' + escapeHtml(name) + '</span>';
  return '<span class="fn-stem">' + escapeHtml(name.slice(0, dot)) + '</span><span class="fn-ext">' + escapeHtml(name.slice(dot)) + '</span>';
}
function renderTreeNode(node, query) {
  let html = '';
  const dirs = Array.from(node.dirs.values()).sort((a, b) => a.name.localeCompare(b.name));
  for (const dir of dirs) {
    const compressed = compressDir(dir);
    const dirPath = compressed.node.path;
    const collapsed = !query && collapsedTreeDirs.has(dirPath);
    const label = compressed.segments.map(seg => '<span class="seg">' + escapeHtml(seg) + '</span>').join('<span class="seg-sep">/</span>');
    html += '<div class="tree-dir">' +
      '<button class="tree-row tree-dir-row' + (collapsed ? ' is-collapsed' : '') + '" data-action="toggle-tree-dir" data-dir-path="' + escapeHtml(dirPath) + '">' +
        '<span class="tree-chevron" aria-hidden="true"></span>' +
        '<span class="tree-dir-label">' + label + '</span>' +
        '<span class="tree-dir-dot"></span>' +
      '</button>' +
      (collapsed ? '' : '<div class="tree-children">' + renderTreeNode(compressed.node, query) + '</div>') +
    '</div>';
  }
  const files = node.files.slice().sort((a, b) => a.name.localeCompare(b.name));
  for (const entry of files) {
    const status = entry.file.isBinary ? 'binary' : entry.file.status;
    const pending = pendingComments().filter(c => c.filePath === entry.path).length;
    const hits = query ? contentMatchCount(entry.file, query) : 0;
    html += '<a class="file-link tree-row tree-file-row' + (entry.path === activeFilePath ? ' is-active' : '') + '" href="#file-' + entry.index + '" data-file-path="' + escapeHtml(entry.path) + '">' +
      fileIconHtml() +
      '<span class="tree-file-name">' + fileNameLabel(entry.name) + '</span>' +
      (pending ? '<span class="count">' + pending + '</span>' : '') +
      (hits ? '<span class="tree-hits" title="' + hits + ' content match' + (hits === 1 ? '' : 'es') + '">' + hits + '</span>' : '') +
      statusBadgeHtml(status) +
    '</a>';
  }
  return html;
}
function renderFileTree() {
  const el = document.getElementById('file-list');
  if (!el || !review) return;
  const input = document.getElementById('file-filter');
  const query = (input && input.value ? input.value : '').trim();
  let files = review.files;
  if (query) files = files.filter(file => fileMatchesFilter(file, query));
  if (!files.length) {
    el.innerHTML = '<div class="tree-empty">' + (query ? 'No files match “' + escapeHtml(query) + '”' : 'No changes') + '</div>';
    return;
  }
  el.innerHTML = renderTreeNode(buildFileTree(files), query);
}
function renderSidebar() {
  const pending = pendingComments();
  renderFileTree();
  const countEl = document.getElementById('file-count');
  if (countEl) countEl.textContent = review.files.length;
  updateCollapseToggle();
  document.getElementById('status').innerHTML = pending.length + ' pending comment' + (pending.length === 1 ? '' : 's') +
    (pending.length ? '<div class="sidebar-actions"><button data-action="clear-pending-comments">Remove all pending comments</button></div>' : '');
}
function updateActiveFile() {
  const sections = Array.from(document.querySelectorAll('.file'));
  if (!sections.length) return;
  const viewportTop = (document.querySelector('header')?.getBoundingClientRect().bottom || 0) + 1;
  const containingSection = sections.find(section => {
    const rect = section.getBoundingClientRect();
    return rect.top <= viewportTop && rect.bottom > viewportTop;
  });
  const nextSection = sections.find(section => section.getBoundingClientRect().top > viewportTop);
  const activeSection = containingSection || nextSection || sections[sections.length - 1];
  const nextPath = activeSection.querySelector('.file-header')?.dataset?.filePath || null;
  if (nextPath === activeFilePath) return;
  activeFilePath = nextPath;
  document.querySelectorAll('.file-link').forEach(link => link.classList.toggle('is-active', link.dataset.filePath === activeFilePath));
}
function queueActiveFileUpdate() {
  if (activeFileTimer !== null) clearTimeout(activeFileTimer);
  activeFileTimer = setTimeout(() => {
    activeFileTimer = null;
    updateActiveFile();
  }, 100);
}
function scrollActiveFileLinkIntoView() {
  const popover = document.getElementById('file-popover');
  const link = popover?.querySelector('.file-link.is-active');
  if (!popover || !link) return;
  const popoverRect = popover.getBoundingClientRect();
  const linkRect = link.getBoundingClientRect();
  if (linkRect.top < popoverRect.top + 6) popover.scrollTop -= popoverRect.top + 6 - linkRect.top;
  if (linkRect.bottom > popoverRect.bottom - 6) popover.scrollTop += linkRect.bottom - popoverRect.bottom + 6;
}
function renderCommentsFor(comments) {
  return comments.map(c => '<div class="comment" data-comment-id="' + escapeHtml(c.id) + '"><div class="comment-header"><div class="comment-meta">' + escapeHtml(commentLocation(c) + ' · ' + c.side) + '</div>' +
    (c.status === 'pending' ? '<button class="remove-comment" data-action="remove-comment" data-comment-id="' + escapeHtml(c.id) + '">Remove</button>' : '') +
    '</div>' + escapeHtml(c.body) + '</div>').join('');
}
function payloadLocation(payload) {
  const oldRange = rangeText(payload.oldLine, payload.oldEndLine);
  const newRange = rangeText(payload.newLine, payload.newEndLine);
  if (payload.side === 'mixed' && oldRange && newRange) return 'old ' + oldRange + ', new ' + newRange;
  return newRange || oldRange || '?';
}
function renderCommentForm(payload) {
  const lineCount = payload.lineContent ? payload.lineContent.split('\n').length : 1;
  return '<div class="range-help">Commenting on ' + lineCount + ' line' + (lineCount === 1 ? '' : 's') + ' at ' + escapeHtml(payloadLocation(payload)) + '</div>' +
    '<div class="comment-form">' +
    '<textarea placeholder="Add review comment…"></textarea>' +
    '<div class="comment-actions"><button data-action="save-comment">Comment</button>' +
    '<button class="secondary" data-action="cancel-comment">Cancel</button></div>' +
    '</div>';
}
function hunkShowsOldNumbers(hunk) { return hunk.lines.some(line => typeof line.oldLine === 'number' && line.oldLine > 0); }
function hunkShowsNewNumbers(hunk) { return hunk.lines.some(line => typeof line.newLine === 'number' && line.newLine > 0); }
function commentRowHtml(hunk, content, extraClass = '') {
  const prefix = [];
  if (hunkShowsOldNumbers(hunk)) prefix.push('<td></td>');
  if (hunkShowsNewNumbers(hunk)) prefix.push('<td></td>');
  const leftOffset = (prefix.length * 50) + 28;
  return '<tr class="comment-row' + (extraClass ? ' ' + extraClass : '') + '">' + prefix.join('') + '<td class="comment-cell" style="--comment-left-offset:' + leftOffset + 'px">' + content + '</td></tr>';
}
function observeDiffViewportWidths() {
  diffResizeObserver?.disconnect();
  const viewports = Array.from(document.querySelectorAll('.file-body-inner'));
  const sync = viewport => viewport.style.setProperty('--diff-viewport-width', viewport.clientWidth + 'px');
  viewports.forEach(sync);
  if (typeof ResizeObserver === 'undefined') return;
  diffResizeObserver = new ResizeObserver(entries => entries.forEach(entry => sync(entry.target)));
  viewports.forEach(viewport => diffResizeObserver.observe(viewport));
}
function buildFileBodyHtml(file) {
  const filePath = file.newPath === '/dev/null' ? file.oldPath : file.newPath;
  if (file.isBinary) return '<div class="empty">Binary file diff cannot be annotated.</div>';
  return file.hunks.map((hunk, hunkIndex) => {
    const showOldNumbers = hunkShowsOldNumbers(hunk);
    const showNewNumbers = hunkShowsNewNumbers(hunk);
    const rows = hunk.lines.map((line, lineIndex) => {
      const key = keyFor(filePath, hunk.header, line);
      const baseCls = line.kind === 'add' ? 'add' : line.kind === 'delete' ? 'delete' : line.kind === 'meta' ? 'meta-line' : 'context';
      const cls = baseCls + (hasMultiLineCommentOnLine(filePath, hunk, line) ? ' commented-range' : '');
      const marker = lineMarker(line);
      const oldNum = line.oldLine || '';
      const newNum = line.newLine || '';
      const anchoredComments = commentsForAnchor(filePath, hunk, lineIndex);
      const comments = renderCommentsFor(anchoredComments);
      const plus = line.kind === 'meta' || review.mode === 'active-turn' ? '' : '<button class="line-plus" data-action="start-comment" aria-label="Add comment" title="Add comment. Drag to select multiple lines">+</button>';
      const plusOnOld = showOldNumbers && (!showNewNumbers || line.kind === 'delete' || (line.kind === 'context' && !newNum));
      const oldNumClass = 'num' + (plus && plusOnOld ? ' comment-target' : '');
      const newNumClass = 'num' + (plus && !plusOnOld ? ' comment-target' : '');
      const oldCell = showOldNumbers ? '<td class="' + oldNumClass + '"><span class="line-number-text">' + oldNum + '</span>' + (plusOnOld ? plus : '') + '</td>' : '';
      const newCell = showNewNumbers ? '<td class="' + newNumClass + '"><span class="line-number-text">' + newNum + '</span>' + (!plusOnOld ? plus : '') + '</td>' : '';
      const codeMarker = marker === ' ' ? '&nbsp;' : escapeHtml(marker);
      return '<tr class="line ' + cls + '" data-file-path="' + escapeHtml(filePath) + '" data-hunk="' + escapeHtml(hunk.header) + '" data-hunk-index="' + hunkIndex + '" data-line-index="' + lineIndex + '" data-key="' + escapeHtml(key) + '">' +
        oldCell + newCell + '<td class="code"><span class="code-marker">' + codeMarker + '</span>' + highlightCodeLine(filePath, line.content) + '</td></tr>' +
        (comments ? commentRowHtml(hunk, comments) : '');
    }).join('');
    return '<div class="hunk-header">' + escapeHtml(hunk.header) + '</div><table class="diff"><tbody>' + rows + '</tbody></table>';
  }).join('');
}
function ensureFileBody(section) {
  if (!section) return;
  const inner = section.querySelector('.file-body-inner');
  if (!inner || inner.dataset.rendered === '1') return;
  const fileIndex = Number(section.dataset.fileIndex);
  const file = review.files[fileIndex];
  if (!file) return;
  inner.innerHTML = buildFileBodyHtml(file);
  inner.dataset.rendered = '1';
  inner.style.setProperty('--diff-viewport-width', inner.clientWidth + 'px');
  highlightSearchInBody(inner);
  if (fileBodyObserver) fileBodyObserver.unobserve(section);
}
function observeFileBodies() {
  if (fileBodyObserver) { fileBodyObserver.disconnect(); fileBodyObserver = null; }
  const sections = Array.from(document.querySelectorAll('.file'));
  if (typeof IntersectionObserver === 'undefined') { sections.forEach(ensureFileBody); return; }
  fileBodyObserver = new IntersectionObserver(entries => {
    for (const entry of entries) {
      if (entry.isIntersecting && !entry.target.classList.contains('is-collapsed')) ensureFileBody(entry.target);
    }
  }, { rootMargin: '1200px 0px' });
  for (const section of sections) if (!section.classList.contains('is-collapsed')) fileBodyObserver.observe(section);
}
function renderVisibleFileBodies() {
  const vh = window.innerHeight || 800;
  for (const section of document.querySelectorAll('.file')) {
    if (section.classList.contains('is-collapsed')) continue;
    const rect = section.getBoundingClientRect();
    if (rect.top <= vh + 600 && rect.bottom >= -600) ensureFileBody(section);
  }
}
function revealFile(section) {
  if (!section) return;
  const header = section.querySelector('.file-header');
  const filePath = header && header.dataset ? header.dataset.filePath : null;
  if (filePath && collapsedFiles.has(filePath)) {
    collapsedFiles.delete(filePath);
    section.classList.remove('is-collapsed');
    if (header) header.setAttribute('aria-expanded', 'true');
    updateCollapseToggle();
  }
  ensureFileBody(section);
  section.scrollIntoView({ block:'start' });
  section.classList.remove('flash-target');
  void section.offsetWidth;
  section.classList.add('flash-target');
  clearTimeout(section._flashTimer);
  section._flashTimer = setTimeout(() => section.classList.remove('flash-target'), 1300);
}
function searchQuery() {
  const input = document.getElementById('file-filter');
  return (input && input.value ? input.value : '').trim();
}
function collectSearchRanges(root, q, out) {
  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
    acceptNode(node) {
      const parent = node.parentElement;
      if (!parent || !parent.closest('td.code')) return NodeFilter.FILTER_REJECT;
      return node.nodeValue && node.nodeValue.toLowerCase().includes(q) ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT;
    }
  });
  let node;
  while ((node = walker.nextNode())) {
    const lower = node.nodeValue.toLowerCase();
    let idx = 0;
    while ((idx = lower.indexOf(q, idx)) !== -1) {
      const range = document.createRange();
      range.setStart(node, idx);
      range.setEnd(node, idx + q.length);
      out.push(range);
      idx += q.length;
    }
  }
}
function searchHighlightSupported() {
  return typeof CSS !== 'undefined' && CSS.highlights && typeof Highlight !== 'undefined';
}
function refreshSearchHighlights() {
  if (!searchHighlightSupported()) return;
  CSS.highlights.delete('review-search');
  const q = searchQuery().toLowerCase();
  if (q.length < 2) return;
  const content = document.getElementById('content');
  if (!content) return;
  const ranges = [];
  collectSearchRanges(content, q, ranges);
  if (ranges.length) CSS.highlights.set('review-search', new Highlight(...ranges));
}
function highlightSearchInBody(inner) {
  if (!searchHighlightSupported()) return;
  const q = searchQuery().toLowerCase();
  if (q.length < 2) return;
  let highlight = CSS.highlights.get('review-search');
  if (!highlight) { highlight = new Highlight(); CSS.highlights.set('review-search', highlight); }
  const ranges = [];
  collectSearchRanges(inner, q, ranges);
  for (const range of ranges) highlight.add(range);
}
function render() {
  renderModeMenu();
  renderSidebar();
  document.getElementById('additions').textContent = '+' + (review.additions || 0);
  document.getElementById('deletions').textContent = '−' + (review.deletions || 0);
  const comparisonTarget = review.mode === 'branch' ? (review.baseRef || 'main') : review.mode === 'uncommitted' ? 'HEAD' : 'turn start';
  const comparison = document.getElementById('branch-comparison');
  comparison.innerHTML = '<span class="branch-current">' + escapeHtml(review.branchName || 'worktree') + '</span><span class="comparison-arrow">→</span><span class="comparison-target">' + escapeHtml(comparisonTarget) + '</span>';
  comparison.title = (review.branchName || 'worktree') + ' compared with ' + comparisonTarget;
  comparison.setAttribute('aria-label', comparison.title);
  const content = document.getElementById('content');
  if (!review.files.length) {
    diffResizeObserver?.disconnect();
    content.innerHTML = '<div class="empty">No changes in ' + escapeHtml((review.modeLabel || 'this view').toLowerCase()) + '.</div>';
    return;
  }
  content.innerHTML = review.files.map((file, fileIndex) => {
    const filePath = file.newPath === '/dev/null' ? file.oldPath : file.newPath;
    const pendingForFile = pendingComments().filter(c => c.filePath === filePath).length;
    const collapsed = collapsedFiles.has(filePath);
    const stats = statsForFile(file);
    let estRows = 0;
    for (const hunk of file.hunks) estRows += hunk.lines.length;
    const estHeight = collapsed ? 44 : 44 + (file.isBinary ? 40 : file.hunks.length * 30 + estRows * 20);
    const fileHeader = '<button class="file-header" data-action="toggle-file" data-file-path="' + escapeHtml(filePath) + '" aria-expanded="' + (!collapsed) + '">' +
      '<span class="file-chevron" aria-hidden="true"></span><span class="file-title">' + pathLabelHtml(filePath) + '</span>' +
      '<span class="file-status">' + escapeHtml(file.isBinary ? 'binary' : file.status) + '</span>' +
      (pendingForFile ? '<span class="file-comment-count">' + pendingForFile + ' pending</span>' : '') +
      '<span class="file-change-stats"><span class="additions">+' + stats.additions + '</span><span class="deletions">−' + stats.deletions + '</span></span></button>';
    const sectionClass = 'file' + (collapsed ? ' is-collapsed' : '');
    return '<section class="' + sectionClass + '" id="file-' + fileIndex + '" data-file-index="' + fileIndex + '" style="contain-intrinsic-size:auto ' + estHeight + 'px">' + fileHeader + '<div class="file-body"><div class="file-body-inner" data-file-index="' + fileIndex + '"></div></div></section>';
  }).join('');
  observeFileBodies();
  renderVisibleFileBodies();
  refreshSearchHighlights();
  observeDiffViewportWidths();
  queueActiveFileUpdate();
}
function findHunk(filePath, hunkHeader) {
  for (const file of review.files) {
    const path = file.newPath === '/dev/null' ? file.oldPath : file.newPath;
    if (path !== filePath) continue;
    for (const hunk of file.hunks) {
      if (hunk.header === hunkHeader) return hunk;
    }
  }
}
function buildPayloadForRange(filePath, hunk, startIndex, endIndex) {
  const start = Math.min(startIndex, endIndex);
  const end = Math.max(startIndex, endIndex);
  const selected = hunk.lines.slice(start, end + 1).filter(line => line.kind !== 'meta');
  if (!selected.length) return null;
  const sides = Array.from(new Set(selected.map(lineSide)));
  const side = sides.length === 1 ? sides[0] : 'mixed';
  const oldNumbers = selected.map(line => line.oldLine).filter(value => typeof value === 'number');
  const newNumbers = selected.map(line => line.newLine).filter(value => typeof value === 'number');
  const payload = {
    filePath,
    side,
    hunkHeader: hunk.header,
    lineContent: selected.map(line => lineMarker(line) + line.content).join('\n')
  };
  if (oldNumbers.length) {
    payload.oldLine = Math.min(...oldNumbers);
    payload.oldEndLine = Math.max(...oldNumbers);
  }
  if (newNumbers.length) {
    payload.newLine = Math.min(...newNumbers);
    payload.newEndLine = Math.max(...newNumbers);
  }
  return payload;
}
function clearOpenForms() {
  document.querySelectorAll('tr.comment-row.form-row').forEach(row => row.remove());
  document.querySelectorAll('tr.line.range-selected, tr.line.range-anchor').forEach(row => row.classList.remove('range-selected', 'range-anchor'));
}
function rowsForRange(filePath, hunkHeader, startIndex, endIndex) {
  const start = Math.min(startIndex, endIndex);
  const end = Math.max(startIndex, endIndex);
  return Array.from(document.querySelectorAll('tr.line')).filter(row =>
    row.dataset.filePath === filePath && row.dataset.hunk === hunkHeader && Number(row.dataset.lineIndex) >= start && Number(row.dataset.lineIndex) <= end && !row.classList.contains('meta-line')
  );
}
function updateDragSelection() {
  if (!dragState) return;
  document.querySelectorAll('tr.line.range-selected, tr.line.range-anchor').forEach(row => row.classList.remove('range-selected', 'range-anchor'));
  const rows = rowsForRange(dragState.filePath, dragState.hunkHeader, dragState.startIndex, dragState.currentIndex);
  rows.forEach(selectedRow => selectedRow.classList.add('range-selected'));
  const anchorRow = rows.find(selectedRow => Number(selectedRow.dataset.lineIndex) === dragState.startIndex);
  if (anchorRow) anchorRow.classList.add('range-anchor');
}
function openFormForRange(row, filePath, hunk, startIndex, endIndex) {
  const payload = buildPayloadForRange(filePath, hunk, startIndex, endIndex);
  if (!payload) return;
  clearOpenForms();
  const rows = rowsForRange(filePath, hunk.header, startIndex, endIndex);
  rows.forEach(selectedRow => selectedRow.classList.add('range-selected'));
  const anchorRow = rows.find(selectedRow => Number(selectedRow.dataset.lineIndex) === startIndex);
  if (anchorRow) anchorRow.classList.add('range-anchor');
  const insertionRow = rows[rows.length - 1] || row;
  const wrapper = document.createElement('tbody');
  wrapper.innerHTML = commentRowHtml(hunk, renderCommentForm(payload), 'form-row');
  const tr = wrapper.firstElementChild;
  tr.querySelector('.comment-form').dataset.payload = JSON.stringify(payload);
  insertionRow.after(tr);
  tr.querySelector('textarea').focus();
}
function startCommentDrag(row, event) {
  if (!row || row.classList.contains('meta-line')) return;
  const filePath = row.dataset.filePath;
  const hunkHeader = row.dataset.hunk;
  const lineIndex = Number(row.dataset.lineIndex);
  const hunk = findHunk(filePath, hunkHeader);
  if (!hunk || !Number.isFinite(lineIndex)) return;
  clearOpenForms();
  dragState = { filePath, hunkHeader, hunk, startIndex: lineIndex, currentIndex: lineIndex, row };
  document.body.classList.add('is-dragging-comment');
  updateDragSelection();
  event.preventDefault();
  event.stopPropagation();
}
function updateCommentDrag(row) {
  if (!dragState || !row || row.classList.contains('meta-line')) return;
  if (row.dataset.filePath !== dragState.filePath || row.dataset.hunk !== dragState.hunkHeader) return;
  const lineIndex = Number(row.dataset.lineIndex);
  if (!Number.isFinite(lineIndex) || lineIndex === dragState.currentIndex) return;
  dragState.currentIndex = lineIndex;
  updateDragSelection();
}
function finishCommentDrag() {
  if (!dragState) return;
  const state = dragState;
  dragState = null;
  document.body.classList.remove('is-dragging-comment');
  openFormForRange(state.row, state.filePath, state.hunk, state.startIndex, state.currentIndex);
}
document.addEventListener('mousedown', (event) => {
  const button = event.target.closest('button.line-plus');
  if (!button) return;
  startCommentDrag(button.closest('tr.line'), event);
});
document.addEventListener('mouseover', (event) => {
  if (!dragState) return;
  updateCommentDrag(event.target.closest('tr.line'));
});
document.addEventListener('mouseup', () => finishCommentDrag());
function setFilePopoverOpen(open) {
  const popover = document.getElementById('file-popover');
  const button = document.getElementById('file-menu-button');
  if (!popover || !button) return;
  popover.hidden = !open;
  button.setAttribute('aria-expanded', open ? 'true' : 'false');
  if (open) {
    setModePopoverOpen(false);
    updateActiveFile();
    requestAnimationFrame(scrollActiveFileLinkIntoView);
    const filter = document.getElementById('file-filter');
    if (filter) requestAnimationFrame(() => filter.focus({ preventScroll:true }));
  }
}
function toggleFilePopover() {
  const popover = document.getElementById('file-popover');
  setFilePopoverOpen(Boolean(popover?.hidden));
}
function positionModePopover() {
  const popover = document.getElementById('mode-popover');
  const button = document.getElementById('scope-trigger');
  if (!popover || !button || popover.hidden) return;
  const triggerRect = button.getBoundingClientRect();
  const gutter = 12;
  const width = Math.min(290, window.innerWidth - gutter * 2);
  const left = Math.max(gutter, Math.min(triggerRect.left, window.innerWidth - width - gutter));
  popover.style.width = width + 'px';
  popover.style.left = left + 'px';
  popover.style.right = 'auto';
  popover.style.top = triggerRect.bottom + 8 + 'px';
}
function setModePopoverOpen(open) {
  const popover = document.getElementById('mode-popover');
  const button = document.getElementById('scope-trigger');
  if (!popover || !button) return;
  popover.hidden = !open;
  button.setAttribute('aria-expanded', open ? 'true' : 'false');
  if (open) {
    setFilePopoverOpen(false);
    positionModePopover();
  }
}
function toggleModePopover() {
  const popover = document.getElementById('mode-popover');
  setModePopoverOpen(Boolean(popover?.hidden));
}

document.addEventListener('keydown', (event) => {
  if (event.key === 'Escape') {
    const filter = document.getElementById('file-filter');
    if (filter && document.activeElement === filter && filter.value) {
      filter.value = '';
      renderFileTree();
      refreshSearchHighlights();
      return;
    }
    dragState = null;
    document.body.classList.remove('is-dragging-comment');
    clearOpenForms();
    setFilePopoverOpen(false);
    setModePopoverOpen(false);
  }
});
(function initFileFilter() {
  const filter = document.getElementById('file-filter');
  if (!filter) return;
  let timer = null;
  filter.addEventListener('input', () => {
    if (timer) clearTimeout(timer);
    timer = setTimeout(() => { timer = null; renderFileTree(); refreshSearchHighlights(); }, 120);
  });
})();
async function loadReview({ refresh = false } = {}) {
  review = await api('/api/reviews/' + reviewId + (refresh ? '?refresh=1' : ''));
  render();
}
async function refreshComments() {
  if (!review) return;
  try {
    const result = await api('/api/reviews/' + reviewId + '/comments');
    const before = JSON.stringify((review.comments || []).map(c => [c.id, c.status, c.body]));
    const after = JSON.stringify((result.comments || []).map(c => [c.id, c.status, c.body]));
    if (before !== after) {
      review.comments = result.comments;
      render();
    }
  } catch (_error) {}
}
async function refreshDiffIfChanged() {
  if (!review) return;
  try {
    const version = await api('/api/reviews/' + reviewId + '/version');
    if (version.diffVersion !== review.diffVersion) {
      await loadReview();
    }
  } catch (_error) {}
}
async function refreshPageState() {
  await Promise.all([refreshComments(), refreshDiffIfChanged()]);
}
window.addEventListener('focus', () => { refreshPageState(); });
window.addEventListener('scroll', queueActiveFileUpdate, { passive:true });
window.addEventListener('resize', () => { queueActiveFileUpdate(); positionModePopover(); });
document.addEventListener('visibilitychange', () => { if (!document.hidden) refreshPageState(); });
setInterval(refreshPageState, 1500);

document.addEventListener('click', async (event) => {
  const popover = document.getElementById('file-popover');
  const menuButton = document.getElementById('file-menu-button');
  const modePopover = document.getElementById('mode-popover');
  const scopeTrigger = document.getElementById('scope-trigger');
  if (popover && menuButton && !popover.hidden && !popover.contains(event.target) && !menuButton.contains(event.target)) setFilePopoverOpen(false);
  if (modePopover && scopeTrigger && !modePopover.hidden && !modePopover.contains(event.target) && !scopeTrigger.contains(event.target)) setModePopoverOpen(false);
  const fileLink = event.target.closest('.file-link');
  if (fileLink) {
    event.preventDefault();
    activeFilePath = fileLink.dataset.filePath || activeFilePath;
    setFilePopoverOpen(false);
    const target = document.querySelector(fileLink.getAttribute('href'));
    revealFile(target);
    return;
  }
  const actionTarget = event.target.closest('[data-action]');
  const action = actionTarget?.dataset?.action;
  if (action === 'toggle-file-list') {
    toggleFilePopover();
    return;
  }
  if (action === 'toggle-mode-list') {
    toggleModePopover();
    return;
  }
  if (action === 'toggle-collapse-all') {
    setAllFilesCollapsed(!allFilesCollapsed());
    return;
  }
  if (action === 'toggle-tree-dir') {
    const dirPath = actionTarget.dataset.dirPath;
    if (dirPath) {
      if (collapsedTreeDirs.has(dirPath)) collapsedTreeDirs.delete(dirPath); else collapsedTreeDirs.add(dirPath);
      renderFileTree();
    }
    return;
  }
  if (action === 'select-mode') {
    const mode = actionTarget.dataset.mode;
    if (!mode || mode === review.mode) { setModePopoverOpen(false); return; }
    const trigger = document.getElementById('scope-trigger');
    trigger.disabled = true;
    try {
      review = await api('/api/reviews/' + reviewId + '/mode', { method:'POST', body:JSON.stringify({ mode }) });
      clearOpenForms();
      setModePopoverOpen(false);
      render();
    } catch (e) {
      alert(e.message);
    } finally {
      trigger.disabled = false;
    }
    return;
  }
  if (action === 'toggle-file') {
    const button = actionTarget.closest('button.file-header');
    const filePath = button?.dataset?.filePath;
    const section = button?.closest('.file');
    if (filePath && section) {
      clearOpenForms();
      const shouldCollapse = !collapsedFiles.has(filePath);
      if (shouldCollapse) collapsedFiles.add(filePath);
      else collapsedFiles.delete(filePath);
      section.classList.toggle('is-collapsed', shouldCollapse);
      button.setAttribute('aria-expanded', shouldCollapse ? 'false' : 'true');
      if (!shouldCollapse) ensureFileBody(section);
      updateCollapseToggle();
    }
    return;
  }
  if (action === 'start-comment') {
    event.preventDefault();
    return;
  }
  if (action === 'cancel-comment') { dragState = null; render(); return; }
  if (action === 'remove-comment') {
    const commentId = actionTarget.dataset.commentId;
    if (!commentId) return;
    try {
      const result = await api('/api/reviews/' + reviewId + '/comments/' + encodeURIComponent(commentId), { method:'DELETE' });
      review.comments = result.comments;
      render();
    } catch (e) { alert(e.message); }
    return;
  }
  if (action === 'clear-pending-comments') {
    try {
      const result = await api('/api/reviews/' + reviewId + '/comments', { method:'DELETE' });
      review.comments = result.comments;
      render();
    } catch (e) { alert(e.message); }
    return;
  }
  if (action === 'save-comment') {
    const form = event.target.closest('.comment-form');
    const body = form.querySelector('textarea').value.trim();
    if (!body) return;
    const data = JSON.parse(form.dataset.payload);
    try {
      const result = await api('/api/reviews/' + reviewId + '/comments', { method:'POST', body: JSON.stringify({ ...data, body }) });
      review.comments.push(result.comment);
      render();
    } catch (e) { alert(e.message); }
  }
});
(async function init() {
  try {
    await loadReview({ refresh: true });
    void connectActivityStream();
  } catch (e) {
    document.getElementById('content').innerHTML = '<div class="error">' + escapeHtml(e.message) + '</div>';
  }
})();
</script>
</body>
</html>`;

export default function reviewDiffExtension(pi: ExtensionAPI) {
	pi.on("session_start", (_event, ctx) => {
		lastCtx = ctx;
		updateWidget(ctx);
	});

	pi.on("session_shutdown", (_event, ctx) => {
		if (ctx.hasUI) {
			ctx.ui.setWidget(WIDGET_KEY, undefined);
			ctx.ui.setStatus(WIDGET_KEY, undefined);
		}
		for (const timer of activityRefreshTimers.values()) clearTimeout(timer);
		activityRefreshTimers.clear();
		for (const clients of activityClients.values()) {
			for (const client of clients) client.end();
		}
		activityClients.clear();
		serverState?.server.close();
		serverState = undefined;
		lastCtx = undefined;
	});

	pi.on("agent_start", async (_event, ctx) => {
		lastCtx = ctx;
		updateWidget(ctx);
		let gitRoot: string | undefined;
		try {
			gitRoot = await getGitRoot(pi, ctx.cwd);
			const existingTimer = activityRefreshTimers.get(gitRoot);
			if (existingTimer) clearTimeout(existingTimer);
			activityRefreshTimers.delete(gitRoot);
			activeTurnTrees.delete(gitRoot);
			activeTurnTrees.set(gitRoot, await captureWorktreeTree(gitRoot));
			setTurnActivity(gitRoot, { running: true, filesChanged: 0, additions: 0, deletions: 0, files: [], updatedAt: Date.now() });
		} catch {
			if (gitRoot) {
				activeTurnTrees.delete(gitRoot);
				setTurnActivity(gitRoot, idleTurnActivity());
			}
		}
	});

	pi.on("tool_execution_end", async (event, ctx) => {
		lastCtx = ctx;
		if (event.isError || !["bash", "edit", "write"].includes(event.toolName)) return;
		try {
			const gitRoot = await getGitRoot(pi, ctx.cwd);
			if (activeTurnTrees.has(gitRoot)) scheduleTurnActivityRefresh(pi, gitRoot);
		} catch {
			// Live activity is best-effort.
		}
	});

	pi.on("agent_end", async (_event, ctx) => {
		lastCtx = ctx;
		let gitRoot: string | undefined;
		try {
			gitRoot = await getGitRoot(pi, ctx.cwd);
			const timer = activityRefreshTimers.get(gitRoot);
			if (timer) clearTimeout(timer);
			activityRefreshTimers.delete(gitRoot);
			const beforeTree = activeTurnTrees.get(gitRoot);
			if (beforeTree) {
				const afterTree = await captureWorktreeTree(gitRoot);
				lastTurnSnapshots.set(gitRoot, { beforeTree, afterTree });
				for (const review of reviews.values()) {
					if (review.gitRoot === gitRoot && review.mode === "active-turn") review.mode = "last-turn";
				}
			}
		} catch {
			// Diff refresh below handles repository errors per review.
		} finally {
			if (gitRoot) activeTurnTrees.delete(gitRoot);
		}
		for (const review of reviews.values()) {
			for (const comment of review.comments) {
				if (comment.status === "sent") comment.status = "resolved";
			}
		}
		updateWidget(ctx);
		await refreshAllReviews(pi);
		if (gitRoot) {
			setTurnActivity(gitRoot, { ...(turnActivities.get(gitRoot) ?? idleTurnActivity()), running: false, updatedAt: Date.now() });
		}
	});

	pi.on("input", (event, ctx) => {
		lastCtx = ctx;
		if (event.source === "extension") return { action: "continue" as const };
		const text = event.text.trimStart();
		if (!text || text.startsWith("/") || text.startsWith("!")) return { action: "continue" as const };
		const toInject = pendingComments.filter((comment) => comment.status === "pending");
		if (toInject.length === 0) return { action: "continue" as const };

		for (const comment of toInject) comment.status = "sent";
		pendingComments = pendingComments.filter((comment) => comment.status === "pending");
		updateWidget(ctx);

		return {
			action: "transform" as const,
			text: `${event.text}\n\n${buildCommentsPrompt(toInject)}`,
			images: event.images,
		};
	});

	pi.registerCommand("review-diff", {
		description: "Open a local annotated review page for the current git diff",
		handler: async (_args, ctx) => {
			lastCtx = ctx;
			try {
				const { review, url, truncated } = await createReview(pi, ctx);
				updateWidget(ctx);
				await openUrl(pi, url);
				ctx.ui.notify(`Opened diff review ${review.id}${truncated ? " (diff truncated)" : ""}`, truncated ? "warning" : "info");
			} catch (error) {
				ctx.ui.notify(error instanceof Error ? error.message : String(error), "error");
			}
		},
	});

}
