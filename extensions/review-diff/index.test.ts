import assert from "node:assert/strict";
import test from "node:test";
import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { resolveBranchBase } from "./index.ts";

type ExecResult = {
	stdout: string;
	stderr: string;
	code: number;
	killed: boolean;
};

type ExecCall = { command: string; args: string[] };

function result(stdout = "", code = 0, stderr = ""): ExecResult {
	return { stdout, stderr, code, killed: false };
}

function fakePi(handler: (call: ExecCall) => ExecResult | Promise<ExecResult>): { pi: ExtensionAPI; calls: ExecCall[] } {
	const calls: ExecCall[] = [];
	return {
		calls,
		pi: {
			exec: async (command: string, args: string[]) => {
				const call = { command, args };
				calls.push(call);
				return handler(call);
			},
		} as unknown as ExtensionAPI,
	};
}

function commandIs(call: ExecCall, command: string, ...args: string[]): boolean {
	return call.command === command && call.args.join("\0") === args.join("\0");
}

test("uses the current pull request base for a stacked branch", async () => {
	const baseOid = "b".repeat(40);
	const mergeBase = "a".repeat(40);
	const { pi, calls } = fakePi((call) => {
		if (commandIs(call, "gh", "pr", "view", "--json", "headRefName,baseRefName,baseRefOid")) {
			return result(JSON.stringify({ headRefName: "feature/child", baseRefName: "feature/parent", baseRefOid: baseOid }));
		}
		if (commandIs(call, "git", "rev-parse", "--verify", "--quiet", `${baseOid}^{commit}`)) return result(baseOid);
		if (commandIs(call, "git", "remote")) return result("origin\nupstream\n");
		if (commandIs(call, "git", "merge-base", "HEAD", baseOid)) return result(mergeBase);
		throw new Error(`Unexpected command: ${call.command} ${call.args.join(" ")}`);
	});

	const base = await resolveBranchBase(pi, "/repo", "feature/child");

	assert.deepEqual(base, {
		baseRef: "feature/parent",
		mergeBase,
		source: "pr",
	});
	assert.equal(calls.some((call) => call.command === "git" && call.args[0] === "fetch"), false);
});

test("fetches a missing pull request base object from the matching remote", async () => {
	const baseOid = "c".repeat(40);
	const mergeBase = "d".repeat(40);
	let objectFetched = false;
	const { pi, calls } = fakePi((call) => {
		if (call.command === "gh" && call.args[0] === "pr") {
			return result(JSON.stringify({ headRefName: "feature/child", baseRefName: "feature/parent", baseRefOid: baseOid }));
		}
		if (commandIs(call, "git", "rev-parse", "--verify", "--quiet", `${baseOid}^{commit}`)) {
			return objectFetched ? result(baseOid) : result("", 1);
		}
		if (commandIs(call, "git", "remote")) return result("origin\nupstream\n");
		if (call.command === "gh" && call.args[0] === "repo") return result("shopify/shop-client\n");
		if (commandIs(call, "git", "remote", "get-url", "origin")) return result("git@github.com:someone/shop-client.git\n");
		if (commandIs(call, "git", "remote", "get-url", "upstream")) return result("https://github.com/Shopify/shop-client.git\n");
		if (commandIs(call, "git", "fetch", "--quiet", "--no-tags", "upstream", "refs/heads/feature/parent")) {
			objectFetched = true;
			return result();
		}
		if (commandIs(call, "git", "merge-base", "HEAD", baseOid)) return result(mergeBase);
		throw new Error(`Unexpected command: ${call.command} ${call.args.join(" ")}`);
	});

	const base = await resolveBranchBase(pi, "/repo", "feature/child");

	assert.equal(base.baseRef, "feature/parent");
	assert.equal(base.source, "pr");
	assert.equal(calls.filter((call) => call.command === "git" && call.args[0] === "fetch").length, 1);
});

test("refreshes remote main before using a stale local main", async () => {
	const remoteMain = "e".repeat(40);
	const mergeBase = "f".repeat(40);
	const { pi } = fakePi((call) => {
		if (call.command === "gh") return result("", 1, "no pull request");
		if (commandIs(call, "git", "remote")) return result("origin\n");
		if (commandIs(call, "git", "symbolic-ref", "--quiet", "--short", "refs/remotes/origin/HEAD")) return result("origin/main\n");
		if (commandIs(call, "git", "fetch", "--quiet", "--no-tags", "origin", "+refs/heads/main:refs/remotes/origin/main")) return result();
		if (commandIs(call, "git", "rev-parse", "--verify", "--quiet", "origin/main^{commit}")) return result(remoteMain);
		if (commandIs(call, "git", "merge-base", "HEAD", remoteMain)) return result(mergeBase);
		throw new Error(`Unexpected command: ${call.command} ${call.args.join(" ")}`);
	});

	const base = await resolveBranchBase(pi, "/repo", "feature/work");

	assert.equal(base.baseRef, "origin/main");
	assert.equal(base.source, "main");
});

test("uses existing remote main and labels it offline when refresh fails", async () => {
	const remoteMain = "1".repeat(40);
	const localMain = "2".repeat(40);
	const mergeBase = "3".repeat(40);
	const { pi } = fakePi((call) => {
		if (call.command === "gh") return result("", 1, "offline");
		if (commandIs(call, "git", "remote")) return result("origin\n");
		if (commandIs(call, "git", "symbolic-ref", "--quiet", "--short", "refs/remotes/origin/HEAD")) return result("origin/main\n");
		if (call.command === "git" && call.args[0] === "fetch") return result("", 1, "offline");
		if (commandIs(call, "git", "rev-parse", "--verify", "--quiet", "origin/main^{commit}")) return result(remoteMain);
		if (commandIs(call, "git", "rev-parse", "--verify", "--quiet", "main^{commit}")) return result(localMain);
		if (commandIs(call, "git", "merge-base", "HEAD", remoteMain)) return result(mergeBase);
		throw new Error(`Unexpected command: ${call.command} ${call.args.join(" ")}`);
	});

	const base = await resolveBranchBase(pi, "/repo", "feature/work");

	assert.equal(base.baseRef, "origin/main");
	assert.equal(base.source, "offline");
});

test("supports local master only when there is no remote default branch", async () => {
	const master = "4".repeat(40);
	const mergeBase = "5".repeat(40);
	const { pi } = fakePi((call) => {
		if (call.command === "gh") return result("", 1, "no pull request");
		if (commandIs(call, "git", "remote")) return result();
		if (commandIs(call, "git", "rev-parse", "--verify", "--quiet", "main^{commit}")) return result("", 1);
		if (commandIs(call, "git", "rev-parse", "--verify", "--quiet", "master^{commit}")) return result(master);
		if (commandIs(call, "git", "merge-base", "HEAD", master)) return result(mergeBase);
		throw new Error(`Unexpected command: ${call.command} ${call.args.join(" ")}`);
	});

	const base = await resolveBranchBase(pi, "/repo", "feature/work");

	assert.equal(base.baseRef, "master");
	assert.equal(base.source, "offline");
});
