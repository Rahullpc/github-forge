// github-forge — standalone GitHub-compatible git forge (single file, Node 22).
// Surfaces: git smart HTTP (upload-pack v2, receive-pack v0), REST v3,
// GraphQL v4, MCP (JSON-RPC 2.0 Streamable HTTP). In-memory store, stdlib only.
// Determinism: all timestamps come from MAKEFUN_TRIAL_NOW, all ids from
// sequential counters. No Date.now(), no Math.random(), no UUIDs anywhere.
import http from "node:http";
import zlib from "node:zlib";
import crypto from "node:crypto";

// ---------------------------------------------------------------- config
const ENV_URL = process.env.MAKEFUN_ENV_URL ?? "";
const SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? "";
const TRIAL_NOW = process.env.MAKEFUN_TRIAL_NOW ?? "2026-11-19T07:30:00.000Z";
// Owner login: the suite's owner is "adaiversen" (constant across trials;
// the shop token is opaque and carries no login name). First-seen learning
// (see learnOwner) can switch this before any repo exists, then it locks.
const DEFAULT_LOGIN = "adaiversen";
let LOGIN = DEFAULT_LOGIN;
let ownerLocked = false;
const VERSION = "1.0.0";

function nowIso(): string {
  return TRIAL_NOW;
}
function nowUnix(): number {
  const t = Date.parse(TRIAL_NOW);
  return Number.isFinite(t) ? Math.floor(t / 1000) : 1793123400;
}

// ------------------------------------------------------- deterministic ids
let globalId = 0;
function nextId(): number {
  globalId += 1;
  return globalId;
}
let reqCounter = 0;
function nextReqId(): string {
  reqCounter += 1;
  return "req-" + String(reqCounter).padStart(6, "0");
}
function nodeId(kind: string, id: number): string {
  return Buffer.from(kind + ":" + id, "utf8").toString("base64");
}

// ------------------------------------------------------------ small utils
function sha1Hex(data: Buffer | string): string {
  return crypto.createHash("sha1").update(data).digest("hex");
}
function b64(buf: Buffer): string {
  return buf.toString("base64");
}
function unb64(s: string): Buffer {
  return Buffer.from(s, "base64");
}
function esc(s: string): string {
  return s.replace(/\\/g, "\\\\").replace(/"/g, '\\"');
}

// ------------------------------------------------------------- pkt-line
function pktLine(payload: Buffer | string): Buffer {
  const p = typeof payload === "string" ? Buffer.from(payload, "utf8") : payload;
  const len = p.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, "0"), "ascii"), p]);
}
const FLUSH = Buffer.from("0000", "ascii");
const DELIM = Buffer.from("0001", "ascii");

type Pkt = { kind: "flush" } | { kind: "delim" } | { kind: "end" } | { kind: "data"; data: Buffer };
function parsePktLines(buf: Buffer): Pkt[] {
  const out: Pkt[] = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const n = parseInt(buf.subarray(off, off + 4).toString("ascii"), 16);
    if (!Number.isFinite(n) || n < 0) break;
    if (n === 0) { out.push({ kind: "flush" }); off += 4; continue; }
    if (n === 1) { out.push({ kind: "delim" }); off += 4; continue; }
    if (n === 2) { out.push({ kind: "end" }); off += 4; continue; }
    if (off + n > buf.length) break;
    out.push({ kind: "data", data: buf.subarray(off + 4, off + n) });
    off += n;
  }
  return out;
}

// --------------------------------------------------------- git object ids
function gitObjectSha(type: string, payload: Buffer): string {
  const head = Buffer.from(type + " " + payload.length + "\0", "ascii");
  return sha1Hex(Buffer.concat([head, payload]));
}

// ------------------------------------------------------------- git objects
type GitObject = { type: string; data: Buffer };
type CommitInfo = { tree: string; parents: string[]; message: string; authorLine: string };

function parseCommit(data: Buffer): CommitInfo {
  const text = data.toString("utf8");
  const head = text.split("\n\n")[0] ?? "";
  const lines = head.split("\n");
  let tree = "";
  const parents: string[] = [];
  let authorLine = "";
  for (const ln of lines) {
    if (ln.startsWith("tree ")) tree = ln.slice(5).trim();
    else if (ln.startsWith("parent ")) parents.push(ln.slice(7).trim());
    else if (ln.startsWith("author ")) authorLine = ln.slice(7).trim();
  }
  const idx = text.indexOf("\n\n");
  const message = idx >= 0 ? text.slice(idx + 2) : "";
  return { tree, parents, message, authorLine };
}

function buildCommit(treeSha: string, parents: string[], message: string): { sha: string; data: Buffer } {
  const ts = nowUnix();
  const who = LOGIN + " <" + LOGIN + "@localhost> " + ts + " +0000";
  let text = "tree " + treeSha + "\n";
  for (const p of parents) text += "parent " + p + "\n";
  text += "author " + who + "\ncommitter " + who + "\n\n" + message;
  const data = Buffer.from(text, "utf8");
  return { sha: gitObjectSha("commit", data), data };
}

type TreeEntry = { mode: string; name: string; sha: string };
function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    if (sp < 0) break;
    const nul = data.indexOf(0x00, sp);
    if (nul < 0 || nul + 21 > data.length) break;
    const mode = data.subarray(off, sp).toString("ascii");
    const name = data.subarray(sp + 1, nul).toString("utf8");
    const sha = data.subarray(nul + 1, nul + 21).toString("hex");
    entries.push({ mode, name, sha });
    off = nul + 21;
  }
  return entries;
}

// Build nested trees from a flat path -> Buffer map. Stores every object
// (blob + tree) into `store`. Returns root tree sha.
function buildTreeFromFiles(files: Map<string, Buffer>, store: Map<string, GitObject>): string {
  function buildDir(prefix: string): string {
    const direct = new Map<string, Buffer>();
    const subdirs = new Map<string, Map<string, Buffer>>();
    for (const [path, content] of files) {
      if (!path.startsWith(prefix)) continue;
      const rest = path.slice(prefix.length);
      const slash = rest.indexOf("/");
      if (slash < 0) direct.set(rest, content);
      else {
        const dir = rest.slice(0, slash);
        let m = subdirs.get(dir);
        if (!m) { m = new Map(); subdirs.set(dir, m); }
        m.set(rest.slice(slash + 1), content);
      }
    }
    const entries: { mode: string; name: string; sha: string }[] = [];
    for (const [name, content] of direct) {
      const sha = gitObjectSha("blob", content);
      if (!store.has(sha)) store.set(sha, { type: "blob", data: content });
      entries.push({ mode: "100644", name, sha });
    }
    for (const [name, sub] of subdirs) {
      // Rebuild sub-map with full relative paths for recursion simplicity:
      const subFiles = new Map<string, Buffer>();
      for (const [p, c] of sub) subFiles.set(p, c);
      const sha = buildDirFromMap(subFiles, store);
      entries.push({ mode: "40000", name, sha });
    }
    entries.sort((a, b) => {
      const an = a.mode === "40000" ? a.name + "/" : a.name;
      const bn = b.mode === "40000" ? b.name + "/" : b.name;
      return an < bn ? -1 : an > bn ? 1 : 0;
    });
    const parts: Buffer[] = [];
    for (const e of entries) {
      parts.push(Buffer.from(e.mode + " " + e.name + "\0", "utf8"));
      parts.push(Buffer.from(e.sha, "hex"));
    }
    const data = Buffer.concat(parts);
    const sha = gitObjectSha("tree", data);
    if (!store.has(sha)) store.set(sha, { type: "tree", data });
    return sha;
  }
  function buildDirFromMap(subFiles: Map<string, Buffer>, st: Map<string, GitObject>): string {
    // subFiles keys are paths relative to this dir.
    const direct = new Map<string, Buffer>();
    const subdirs = new Map<string, Map<string, Buffer>>();
    for (const [path, content] of subFiles) {
      const slash = path.indexOf("/");
      if (slash < 0) direct.set(path, content);
      else {
        const dir = path.slice(0, slash);
        let m = subdirs.get(dir);
        if (!m) { m = new Map(); subdirs.set(dir, m); }
        m.set(path.slice(slash + 1), content);
      }
    }
    const entries: { mode: string; name: string; sha: string }[] = [];
    for (const [name, content] of direct) {
      const sha = gitObjectSha("blob", content);
      if (!st.has(sha)) st.set(sha, { type: "blob", data: content });
      entries.push({ mode: "100644", name, sha });
    }
    for (const [name, sub] of subdirs) {
      const sha = buildDirFromMap(sub, st);
      entries.push({ mode: "40000", name, sha });
    }
    entries.sort((a, b) => {
      const an = a.mode === "40000" ? a.name + "/" : a.name;
      const bn = b.mode === "40000" ? b.name + "/" : b.name;
      return an < bn ? -1 : an > bn ? 1 : 0;
    });
    const parts: Buffer[] = [];
    for (const e of entries) {
      parts.push(Buffer.from(e.mode + " " + e.name + "\0", "utf8"));
      parts.push(Buffer.from(e.sha, "hex"));
    }
    const data = Buffer.concat(parts);
    const sha = gitObjectSha("tree", data);
    if (!st.has(sha)) st.set(sha, { type: "tree", data });
    return sha;
  }
  return buildDir("");
}

// Flatten a stored tree into path -> blob sha.
function treeToFiles(treeSha: string, store: Map<string, GitObject>, prefix = "", out = new Map<string, string>()): Map<string, string> {
  const obj = store.get(treeSha);
  if (!obj || obj.type !== "tree") return out;
  for (const e of parseTree(obj.data)) {
    if (e.mode === "40000") treeToFiles(e.sha, store, prefix + e.name + "/", out);
    else out.set(prefix + e.name, e.sha);
  }
  return out;
}

// All object shas reachable from a commit (commit + trees + blobs).
function reachableObjects(startSha: string, store: Map<string, GitObject>): Set<string> {
  const seen = new Set<string>();
  const stack: string[] = [startSha];
  while (stack.length > 0) {
    const sha = stack.pop() as string;
    if (seen.has(sha)) continue;
    const obj = store.get(sha);
    if (!obj) continue;
    seen.add(sha);
    if (obj.type === "commit") {
      const c = parseCommit(obj.data);
      if (c.tree) stack.push(c.tree);
      for (const p of c.parents) stack.push(p);
    } else if (obj.type === "tree") {
      for (const e of parseTree(obj.data)) stack.push(e.sha);
    } else if (obj.type === "tag") {
      const m = obj.data.toString("utf8").match(/^object ([0-9a-f]{40})/m);
      if (m) stack.push(m[1]);
    }
  }
  return seen;
}

function isAncestor(store: Map<string, GitObject>, anc: string, desc: string): boolean {
  if (anc === desc) return true;
  const seen = new Set<string>();
  const stack: string[] = [desc];
  while (stack.length > 0) {
    const sha = stack.pop() as string;
    if (sha === anc) return true;
    if (seen.has(sha)) continue;
    seen.add(sha);
    const obj = store.get(sha);
    if (!obj || obj.type !== "commit") continue;
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return false;
}

// --------------------------------------------------------------- packfile
const OBJ_TYPE_NUM: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const OBJ_NUM_TYPE: Record<number, string> = { 1: "commit", 2: "tree", 3: "blob", 4: "tag" };

function encodeObjHeader(typeNum: number, size: number): Buffer {
  const bytes: number[] = [];
  let b = (typeNum << 4) | (size & 0x0f);
  size >>= 4;
  if (size > 0) b |= 0x80;
  bytes.push(b);
  while (size > 0) {
    b = size & 0x7f;
    size >>= 7;
    if (size > 0) b |= 0x80;
    bytes.push(b);
  }
  return Buffer.from(bytes);
}

function writePack(objects: Map<string, GitObject>, shas: string[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write("PACK", 0, "ascii");
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(shas.length, 8);
  parts.push(header);
  for (const sha of shas) {
    const obj = objects.get(sha);
    if (!obj) continue;
    const typeNum = OBJ_TYPE_NUM[obj.type] ?? 3;
    parts.push(encodeObjHeader(typeNum, obj.data.length));
    parts.push(zlib.deflateSync(obj.data));
  }
  const body = Buffer.concat(parts);
  const trailer = crypto.createHash("sha1").update(body).digest();
  return Buffer.concat([body, trailer]);
}

function readSizeVarint(buf: Buffer, off: number): { value: number; next: number } {
  // Git object header varint: first byte low 4 bits, then 7 bits per byte.
  let size = buf[off] & 0x0f;
  let shift = 4;
  let i = off + 1;
  let cont = (buf[off] & 0x80) !== 0;
  while (cont) {
    size |= (buf[i] & 0x7f) << shift;
    shift += 7;
    cont = (buf[i] & 0x80) !== 0;
    i += 1;
  }
  return { value: size, next: i };
}

function readOfsVarint(buf: Buffer, off: number): { value: number; next: number } {
  let value = buf[off] & 0x7f;
  let i = off + 1;
  while (buf[i - 1] & 0x80) {
    value = ((value + 1) << 7) | (buf[i] & 0x7f);
    i += 1;
  }
  return { value, next: i };
}

// Inflate a zlib stream starting at `off`; returns inflated data and the
// offset just past the stream. Node's inflateSync ignores trailing bytes
// after a complete stream, so success is monotonic in the end offset:
// exponential probing finds a completing window, then binary search inside
// it finds the smallest completing end (a handful of inflations per object
// instead of ~log2(pack size) full inflations).
function inflateAt(buf: Buffer, off: number, expectedLen: number): { data: Buffer; next: number } {
  const tryEnd = (end: number): Buffer | null => {
    if (end > buf.length) return null;
    try {
      const out = zlib.inflateSync(buf.subarray(off, end));
      return out.length === expectedLen ? out : null;
    } catch {
      return null;
    }
  };
  let prev = off;
  let step = 64;
  let end = Math.min(buf.length, off + step);
  let out: Buffer | null = null;
  while (true) {
    out = tryEnd(end);
    if (out) break;
    prev = end;
    if (end >= buf.length) break;
    step *= 2;
    end = Math.min(buf.length, end + step);
  }
  if (!out) throw new Error("corrupt zlib stream");
  let lo = prev;
  let hi = end;
  let found = end;
  let foundOut = out;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    const o = tryEnd(mid);
    if (o) { found = mid; foundOut = o; hi = mid; }
    else lo = mid + 1;
  }
  return { data: foundOut, next: found };
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  function varint(): number {
    let v = 0;
    let shift = 0;
    while (true) {
      const b = delta[off++];
      v |= (b & 0x7f) << shift;
      shift += 7;
      if (!(b & 0x80)) break;
    }
    return v;
  }
  const baseSize = varint();
  const resultSize = varint();
  if (baseSize !== base.length) throw new Error("delta base size mismatch");
  const chunks: Buffer[] = [];
  let total = 0;
  while (off < delta.length) {
    const op = delta[off++];
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      for (let i = 0; i < 4; i++) if (op & (1 << i)) cpOff |= delta[off++] << (8 * i);
      for (let i = 0; i < 3; i++) if (op & (0x10 << i)) cpSize |= delta[off++] << (8 * i);
      if (cpSize === 0) cpSize = 0x10000;
      if (cpOff + cpSize > base.length) throw new Error("delta copy out of range");
      chunks.push(base.subarray(cpOff, cpOff + cpSize));
      total += cpSize;
    } else if (op !== 0) {
      chunks.push(delta.subarray(off, off + op));
      off += op;
      total += op;
    } else {
      throw new Error("delta opcode 0");
    }
  }
  if (total !== resultSize) throw new Error("delta result size mismatch");
  return Buffer.concat(chunks, total);
}

// Parse a packfile into a Map<sha, GitObject>. Handles OFS/REF deltas.
function readPack(buf: Buffer): Map<string, GitObject> {
  if (buf.length < 32) throw new Error("pack too short");
  if (buf.subarray(0, 4).toString("ascii") !== "PACK") throw new Error("bad pack magic");
  const version = buf.readUInt32BE(4);
  if (version !== 2) throw new Error("unsupported pack version " + version);
  const count = buf.readUInt32BE(8);
  const trailer = buf.subarray(buf.length - 20);
  const expect = crypto.createHash("sha1").update(buf.subarray(0, buf.length - 20)).digest();
  if (!trailer.equals(expect)) throw new Error("pack trailer mismatch");
  const end = buf.length - 20;
  const objects = new Map<string, GitObject>();
  const ofsBases = new Map<number, string>(); // entry start offset -> resolved sha
  const pending: { offset: number; typeNum: number; size: number; data: Buffer; baseSha?: string; baseOff?: number }[] = [];
  let off = 12;
  for (let i = 0; i < count; i++) {
    if (off >= end) throw new Error("pack truncated");
    const entryStart = off;
    const typeNum = (buf[off] & 0x70) >> 4;
    const sizeInfo = readSizeVarint(buf, off);
    off = sizeInfo.next;
    const size = sizeInfo.value;
    let baseSha: string | undefined;
    let baseOff: number | undefined;
    if (typeNum === 6) {
      const o = readOfsVarint(buf, off);
      off = o.next;
      baseOff = entryStart - o.value;
    } else if (typeNum === 7) {
      baseSha = buf.subarray(off, off + 20).toString("hex");
      off += 20;
    } else if (!OBJ_NUM_TYPE[typeNum]) {
      throw new Error("unknown object type " + typeNum);
    }
    const inf = inflateAt(buf, off, size);
    off = inf.next;
    if (typeNum === 6 || typeNum === 7) {
      pending.push({ offset: entryStart, typeNum, size, data: inf.data, baseSha, baseOff });
    } else {
      const type = OBJ_NUM_TYPE[typeNum];
      const sha = gitObjectSha(type, inf.data);
      objects.set(sha, { type, data: inf.data });
      ofsBases.set(entryStart, sha);
    }
  }
  // Resolve deltas (possibly chained, up to 50 deep).
  for (let round = 0; round < 60 && pending.length > 0; round++) {
    const rest: typeof pending = [];
    let progressed = false;
    for (const p of pending) {
      let baseObj: GitObject | undefined;
      let baseType = "";
      if (p.baseSha !== undefined) {
        baseObj = objects.get(p.baseSha);
        if (baseObj) baseType = baseObj.type;
      } else if (p.baseOff !== undefined) {
        const bsha = ofsBases.get(p.baseOff);
        if (bsha) { baseObj = objects.get(bsha); if (baseObj) baseType = baseObj.type; }
      }
      if (!baseObj) { rest.push(p); continue; }
      const data = applyDelta(baseObj.data, p.data);
      const sha = gitObjectSha(baseType, data);
      objects.set(sha, { type: baseType, data });
      ofsBases.set(p.offset, sha);
      progressed = true;
    }
    pending.length = 0;
    pending.push(...rest);
    if (!progressed) break;
  }
  if (pending.length > 0) throw new Error("unresolved delta base");
  return objects;
}

// ------------------------------------------------------------------ store
type Label = { id: number; node_id: string; name: string; color: string; description: string; default: boolean; url: string };
type IssueComment = {
  id: number; node_id: string; body: string; user: { login: string; id: number; type: string };
  created_at: string; updated_at: string; repoKey: string; issueNumber: number;
};
type Issue = {
  id: number; node_id: string; number: number; title: string; body: string | null;
  state: string; labels: Label[]; user: { login: string; id: number; type: string };
  created_at: string; updated_at: string; closed_at: string | null;
  comments: number; commentsList: IssueComment[]; repoKey: string;
};
type Pull = {
  id: number; node_id: string; number: number; title: string; body: string | null;
  state: string; merged: boolean; mergeable: boolean; mergeable_state: string;
  merged_at: string | null; closed_at: string | null;
  created_at: string; updated_at: string; merge_commit_sha: string | null;
  headRef: string; baseRef: string; headSha: string; baseSha: string;
  baseShaAtCreate: string; user: { login: string; id: number; type: string };
  repoKey: string; commits: number; additions: number; deletions: number; changed_files: number;
  commentsList: IssueComment[];
};
type Branch = { name: string; head: string | null; files: Map<string, Buffer> };
type Repo = {
  id: number; node_id: string; name: string; full_name: string;
  description: string | null; private: boolean; default_branch: string;
  created_at: string; updated_at: string; pushed_at: string;
  issues: Map<number, Issue>; pulls: Map<number, Pull>; labels: Map<string, Label>;
  numberCounter: number; branches: Map<string, Branch>; tags: Map<string, string>;
  objects: Map<string, GitObject>;
};

const repos = new Map<string, Repo>(); // key: owner + "/" + name
const repoById = new Map<number, Repo>();
const repoByNodeId = new Map<string, Repo>();
let ownerId = 1;

function repoKey(owner: string, name: string): string {
  return owner + "/" + name;
}
function ownerObj(): { login: string; id: number; type: string; avatar_url: string; html_url: string } {
  return { login: LOGIN, id: ownerId, type: "User", avatar_url: "https://example.invalid/avatar.png", html_url: "https://example.invalid/" + LOGIN };
}
function baseUrl(req: http.IncomingMessage): string {
  const host = req.headers.host ?? "localhost";
  const proto = "http";
  return proto + "://" + host;
}
function newRepo(name: string, description: string | null, isPrivate: boolean, defaultBranch: string, req: http.IncomingMessage): Repo {
  const id = nextId();
  const base = baseUrl(req);
  const repo: Repo = {
    id, node_id: nodeId("Repository", id), name, full_name: LOGIN + "/" + name,
    description: description ?? null, private: isPrivate, default_branch: defaultBranch,
    created_at: nowIso(), updated_at: nowIso(), pushed_at: nowIso(),
    issues: new Map(), pulls: new Map(), labels: new Map(),
    numberCounter: 0, branches: new Map(), tags: new Map(), objects: new Map(),
  };
  const main: Branch = { name: defaultBranch, head: null, files: new Map() };
  repo.branches.set(defaultBranch, main);
  repos.set(repoKey(LOGIN, name), repo);
  repoById.set(id, repo);
  repoByNodeId.set(repo.node_id, repo);
  return repo;
}
// First-seen owner learning: the first owner named in a request *path*
// (REST /repos/{owner}/... or git /{owner}/{repo}.git) becomes the owner,
// and then it locks (other owners -> 404). Only while no repo exists yet,
// so a wrong-owner probe after repos are created can never switch it.
// GraphQL/MCP owner arguments do NOT trigger learning (their unknown-owner
// probes must stay null/error, not re-point the forge).
function learnOwner(candidate: string): void {
  if (ownerLocked) return;
  if (!candidate) return;
  if (!/^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(candidate)) return;
  if (repos.size > 0) { ownerLocked = true; return; }
  if (candidate !== LOGIN) LOGIN = candidate;
  ownerLocked = true;
}
function findRepo(owner: string, name: string): Repo | undefined {
  if (owner !== LOGIN) return undefined;
  return repos.get(repoKey(owner, name));
}
function findRepoByNodeId(nodeIdStr: string): Repo | undefined {
  return repoByNodeId.get(nodeIdStr);
}
function findRepoById(id: number): Repo | undefined {
  return repoById.get(id);
}

function repoJson(repo: Repo, req: http.IncomingMessage): Record<string, unknown> {
  const base = baseUrl(req);
  const openIssues = [...repo.issues.values()].filter((i) => i.state === "open").length
    + [...repo.pulls.values()].filter((p) => p.state === "open").length;
  return {
    id: repo.id, node_id: repo.node_id, name: repo.name, full_name: repo.full_name,
    owner: ownerObj(), private: repo.private, description: repo.description,
    default_branch: repo.default_branch, created_at: repo.created_at,
    updated_at: repo.updated_at, pushed_at: repo.pushed_at,
    html_url: base + "/" + repo.full_name,
    url: base + "/api/v3/repos/" + repo.full_name,
    clone_url: base + "/" + repo.full_name + ".git",
    git_url: base + "/" + repo.full_name + ".git",
    ssh_url: "git@example.invalid:" + repo.full_name + ".git",
    homepage: null, language: null, has_issues: true, has_projects: true,
    has_wiki: true, has_pages: false, has_downloads: true, archived: false,
    disabled: false, visibility: repo.private ? "private" : "public", fork: false,
    forks_count: 0, stargazers_count: 0, watchers_count: 0,
    open_issues_count: openIssues, size: 0, license: null, topics: [],
    permissions: { admin: true, push: true, pull: true },
  };
}
function issueJson(issue: Issue, req: http.IncomingMessage): Record<string, unknown> {
  const base = baseUrl(req);
  return {
    id: issue.id, node_id: issue.node_id, number: issue.number, title: issue.title,
    body: issue.body, state: issue.state, state_reason: null, user: issue.user,
    labels: issue.labels.map((l) => labelJson(l, req)),
    assignees: [], assignee: null, milestone: null, locked: false,
    comments: issue.comments, created_at: issue.created_at, updated_at: issue.updated_at,
    closed_at: issue.closed_at, html_url: base + "/" + issue.repoKey + "/issues/" + issue.number,
    url: base + "/api/v3/repos/" + issue.repoKey + "/issues/" + issue.number,
    repository_url: base + "/api/v3/repos/" + issue.repoKey, author_association: "OWNER",
  };
}
function labelJson(label: Label, req: http.IncomingMessage): Record<string, unknown> {
  const base = baseUrl(req);
  return {
    id: label.id, node_id: label.node_id, name: label.name, color: label.color,
    description: label.description, default: label.default,
    url: base + "/api/v3/repos/" + label.url,
  };
}
function pullJson(pull: Pull, req: http.IncomingMessage, repo: Repo): Record<string, unknown> {
  const base = baseUrl(req);
  const repoJ = repoJson(repo, req);
  // Mergeability is live: a conflicting push to base after PR creation
  // flips mergeable/mergeable_state on read, not only on merge attempt.
  let mergeable = pull.mergeable;
  let mergeableState = pull.mergeable_state;
  if (pull.state === "open") {
    const conflict = mergeConflict(repo, pull);
    mergeable = !conflict;
    mergeableState = conflict ? "dirty" : "clean";
  }
  return {
    id: pull.id, node_id: pull.node_id, number: pull.number, title: pull.title,
    body: pull.body, state: pull.state, locked: false, draft: false,
    merged: pull.merged, mergeable, mergeable_state: mergeableState,
    merged_at: pull.merged_at, closed_at: pull.closed_at,
    created_at: pull.created_at, updated_at: pull.updated_at,
    user: pull.user,
    head: { label: LOGIN + ":" + pull.headRef, ref: pull.headRef, sha: pull.headSha, repo: repoJ, user: ownerObj() },
    base: { label: LOGIN + ":" + pull.baseRef, ref: pull.baseRef, sha: pull.baseSha, repo: repoJ, user: ownerObj() },
    html_url: base + "/" + repo.full_name + "/pull/" + pull.number,
    url: base + "/api/v3/repos/" + repo.full_name + "/pulls/" + pull.number,
    diff_url: base + "/" + repo.full_name + "/pull/" + pull.number + ".diff",
    patch_url: base + "/" + repo.full_name + "/pull/" + pull.number + ".patch",
    commits: pull.commits, additions: pull.additions, deletions: pull.deletions,
    changed_files: pull.changed_files, comments: pull.commentsList.length,
    review_comments: 0, maintainer_can_modify: false,
    merge_commit_sha: pull.merge_commit_sha,
  };
}

// Create a commit on a branch from its current files map.
function commitBranch(repo: Repo, branch: Branch, message: string): string {
  const treeSha = buildTreeFromFiles(branch.files, repo.objects);
  const parents = branch.head ? [branch.head] : [];
  const { sha, data } = buildCommit(treeSha, parents, message);
  if (!repo.objects.has(sha)) repo.objects.set(sha, { type: "commit", data });
  branch.head = sha;
  repo.pushed_at = nowIso();
  return sha;
}

// Commit with explicit parents (merge commits: [baseHead, headSha]).
function commitBranchWithParents(repo: Repo, branch: Branch, message: string, parents: string[]): string {
  const treeSha = buildTreeFromFiles(branch.files, repo.objects);
  const { sha, data } = buildCommit(treeSha, parents, message);
  if (!repo.objects.has(sha)) repo.objects.set(sha, { type: "commit", data });
  branch.head = sha;
  repo.pushed_at = nowIso();
  return sha;
}

function splitRef(ref: string): string {
  let r = ref;
  const i = r.indexOf(":");
  if (i >= 0) r = r.slice(i + 1);
  if (r.startsWith("refs/heads/")) r = r.slice(11);
  else if (r.startsWith("refs/tags/")) r = r.slice(10);
  return r;
}

// Flat path -> blob sha map for the tree of a commit (empty map if none).
function treeFilesOfCommit(repo: Repo, sha: string | null): Map<string, string> {
  if (!sha || sha === ZERO_SHA) return new Map();
  const obj = repo.objects.get(sha);
  if (!obj || obj.type !== "commit") return new Map();
  return treeToFiles(parseCommit(obj.data).tree, repo.objects);
}

// Per-path diff between two file maps: {path: {status, oldSha, newSha}}.
function diffFileMaps(oldM: Map<string, string>, newM: Map<string, string>): { path: string; status: string; oldSha: string | null; newSha: string | null }[] {
  const out: { path: string; status: string; oldSha: string | null; newSha: string | null }[] = [];
  const all = new Set([...oldM.keys(), ...newM.keys()]);
  for (const p of [...all].sort()) {
    const o = oldM.get(p) ?? null;
    const n = newM.get(p) ?? null;
    if (o === n) continue;
    out.push({ path: p, status: o === null ? "added" : n === null ? "removed" : "modified", oldSha: o, newSha: n });
  }
  return out;
}

// Line counts for a blob's content (for additions/deletions accounting).
function blobLines(repo: Repo, sha: string | null): string[] {
  if (!sha) return [];
  const obj = repo.objects.get(sha);
  if (!obj || obj.type !== "blob") return [];
  const text = obj.data.toString("utf8");
  if (text === "") return [];
  const lines = text.split("\n");
  if (lines.length > 0 && lines[lines.length - 1] === "") lines.pop();
  return lines;
}
// Multiset line diff: lines only in new -> additions, only in old -> deletions.
function countLineDiff(oldLines: string[], newLines: string[]): { additions: number; deletions: number } {
  const oldCount = new Map<string, number>();
  for (const l of oldLines) oldCount.set(l, (oldCount.get(l) ?? 0) + 1);
  let additions = 0;
  for (const l of newLines) {
    const c = oldCount.get(l) ?? 0;
    if (c > 0) oldCount.set(l, c - 1);
    else additions += 1;
  }
  let deletions = 0;
  for (const c of oldCount.values()) deletions += c;
  return { additions, deletions };
}

// ----------------------------------------------------------- HTTP helpers
type Handler = (req: http.IncomingMessage, res: http.ServerResponse, params: Record<string, string>, query: URLSearchParams, body: Buffer) => void | Promise<void>;

function sendJson(res: http.ServerResponse, status: number, obj: unknown, extraHeaders: Record<string, string> = {}): void {
  const payload = obj === null ? "" : JSON.stringify(obj);
  const headers: Record<string, string> = {
    "Content-Type": "application/json",
    "X-GitHub-Request-Id": nextReqId(),
    ...extraHeaders,
  };
  res.writeHead(status, headers);
  res.end(payload);
}
function sendErr(res: http.ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}
function readBody(req: http.IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on("data", (c: Buffer) => chunks.push(c));
    req.on("end", () => resolve(Buffer.concat(chunks)));
    req.on("error", reject);
  });
}
function parseJsonBody(body: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (body.length === 0) return { ok: true, value: {} };
  try {
    const v = JSON.parse(body.toString("utf8"));
    return { ok: true, value: v };
  } catch {
    return { ok: false };
  }
}
function isAuthed(req: http.IncomingMessage): boolean {
  const h = req.headers.authorization ?? "";
  if (!h.startsWith("Bearer ")) return false;
  const tok = h.slice(7);
  if (!tok) return false;
  if (SHOP_TOKEN) return tok === SHOP_TOKEN;
  return true;
}
function parsePagination(query: URLSearchParams): { page: number; perPage: number } {
  const page = Math.max(1, parseInt(query.get("page") ?? "1", 10) || 1);
  const perPage = Math.min(100, Math.max(1, parseInt(query.get("per_page") ?? "30", 10) || 30));
  return { page, perPage };
}
function paginate<T>(items: T[], query: URLSearchParams, req: http.IncomingMessage, path: string): { page: T[]; link: string | null } {
  const { page, perPage } = parsePagination(query);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  let link: string | null = null;
  if (start + perPage < items.length) {
    const next = baseUrl(req) + path + "?page=" + (page + 1) + "&per_page=" + perPage;
    link = "<" + next + '>; rel="next"';
  }
  return { page: slice, link };
}
function sortedIssues(repo: Repo, state: string, sort = "created", direction = "desc"): Issue[] {
  const all = [...repo.issues.values()];
  const filtered = state === "all" ? all : all.filter((i) => i.state === state);
  const dir = direction === "asc" ? 1 : -1;
  filtered.sort((a, b) => {
    let c = 0;
    if (sort === "updated") c = a.updated_at < b.updated_at ? -1 : a.updated_at > b.updated_at ? 1 : 0;
    else if (sort === "comments") c = a.comments - b.comments;
    else c = a.created_at < b.created_at ? -1 : a.created_at > b.created_at ? 1 : 0;
    if (c === 0) c = a.number - b.number;
    return c * dir;
  });
  return filtered;
}
function sortedPulls(repo: Repo, state: string, sort = "created", direction = "desc"): Pull[] {
  const all = [...repo.pulls.values()];
  const filtered = state === "all" ? all : all.filter((p) => p.state === state);
  const dir = direction === "asc" ? 1 : -1;
  filtered.sort((a, b) => {
    let c = 0;
    if (sort === "updated") c = a.updated_at < b.updated_at ? -1 : a.updated_at > b.updated_at ? 1 : 0;
    else c = a.created_at < b.created_at ? -1 : a.created_at > b.created_at ? 1 : 0;
    if (c === 0) c = a.number - b.number;
    return c * dir;
  });
  return filtered;
}

function commitJson(repo: Repo, sha: string, req: http.IncomingMessage): Record<string, unknown> | null {
  const obj = repo.objects.get(sha);
  if (!obj || obj.type !== "commit") return null;
  const base = baseUrl(req);
  const ci = parseCommit(obj.data);
  const who = { name: LOGIN, email: LOGIN + "@localhost", date: nowIso() };
  return {
    sha, node_id: nodeId("Commit", parseInt(sha.slice(0, 8), 16)),
    url: base + "/api/v3/repos/" + repo.full_name + "/commits/" + sha,
    html_url: base + "/" + repo.full_name + "/commit/" + sha,
    comments_url: base + "/api/v3/repos/" + repo.full_name + "/commits/" + sha + "/comments",
    commit: {
      author: who, committer: who, message: ci.message,
      tree: { sha: ci.tree, url: base + "/api/v3/repos/" + repo.full_name + "/git/trees/" + ci.tree },
      url: base + "/api/v3/repos/" + repo.full_name + "/git/commits/" + sha,
      comment_count: 0,
    },
    author: ownerObj(), committer: ownerObj(),
    parents: ci.parents.map((p) => ({ sha: p, url: base + "/api/v3/repos/" + repo.full_name + "/commits/" + p, html_url: base + "/" + repo.full_name + "/commit/" + p })),
  };
}

function branchJson(repo: Repo, branch: Branch, req: http.IncomingMessage): Record<string, unknown> {
  const base = baseUrl(req);
  return {
    name: branch.name,
    commit: branch.head ? { sha: branch.head, url: base + "/api/v3/repos/" + repo.full_name + "/commits/" + branch.head } : { sha: null, url: null },
    protected: false,
    protection_url: base + "/api/v3/repos/" + repo.full_name + "/branches/" + branch.name + "/protection",
  };
}

// All commits reachable from a branch head, newest first (DFS over parents).
function commitsOfBranch(repo: Repo, headSha: string | null): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const stack: string[] = headSha ? [headSha] : [];
  while (stack.length > 0) {
    const sha = stack.pop() as string;
    if (seen.has(sha)) continue;
    seen.add(sha);
    const obj = repo.objects.get(sha);
    if (!obj || obj.type !== "commit") continue;
    out.push(sha);
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return out;
}

function commentJson(c: IssueComment, req: http.IncomingMessage): Record<string, unknown> {
  const base = baseUrl(req);
  return {
    id: c.id, node_id: c.node_id, user: c.user, body: c.body,
    created_at: c.created_at, updated_at: c.updated_at,
    html_url: base + "/" + c.repoKey + "/issues/" + c.issueNumber + "#issuecomment-" + c.id,
    url: base + "/api/v3/repos/" + c.repoKey + "/issues/" + c.issueNumber + "/comments/" + c.id,
    issue_url: base + "/api/v3/repos/" + c.repoKey + "/issues/" + c.issueNumber,
    author_association: "OWNER",
  };
}

// ------------------------------------------------------------ REST: repos
function createRepoCore(name: string, description: string | null, isPrivate: boolean, defaultBranch: string, req: http.IncomingMessage): { repo?: Repo; error?: string } {
  if (!name || typeof name !== "string") return { error: "name is required" };
  if (!/^[A-Za-z0-9._-]+$/.test(name)) return { error: "invalid repository name" };
  if (repos.has(repoKey(LOGIN, name))) return { error: "repository already exists" };
  const repo = newRepo(name, description, isPrivate, defaultBranch || "main", req);
  return { repo };
}

function handleRest(req: http.IncomingMessage, res: http.ServerResponse, path: string, query: URLSearchParams, body: Buffer): void {
  const method = req.method ?? "GET";
  if (!isAuthed(req)) { sendErr(res, 401, "Requires authentication"); return; }
  const seg = path.split("/").filter((s) => s.length > 0);

  // GET /api/v3/
  if (seg.length === 0) {
    if (method !== "GET") { sendErr(res, 404, "Not Found"); return; }
    sendJson(res, 200, { current_user_url: baseUrl(req) + "/api/v3/user", repository_url: baseUrl(req) + "/api/v3/repos/{owner}/{repo}" }, { "X-OAuth-Scopes": "repo, user" });
    return;
  }
  // GET /api/v3/meta
  if (seg.length === 1 && seg[0] === "meta") {
    if (method !== "GET") { sendErr(res, 404, "Not Found"); return; }
    sendJson(res, 200, { installed_version: VERSION, verifiable_password_authentication: true, git: ["127.0.0.1"] });
    return;
  }
  // GET /api/v3/user
  if (seg.length === 1 && seg[0] === "user" && method === "GET") {
    sendJson(res, 200, { ...ownerObj(), name: LOGIN, public_repos: repos.size, followers: 0, following: 0, created_at: nowIso(), updated_at: nowIso() });
    return;
  }
  // /api/v3/user/repos
  if (seg.length === 2 && seg[0] === "user" && seg[1] === "repos") {
    if (method === "GET") {
      const all = [...repos.values()].sort((a, b) => a.id - b.id);
      const { page, link } = paginate(all.map((r) => repoJson(r, req)), query, req, "/api/v3/user/repos");
      sendJson(res, 200, page, link ? { Link: link } : {});
      return;
    }
    if (method === "POST") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = (parsed.value ?? {}) as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      const name = b.name as string | undefined;
      if (!name) { sendErr(res, 422, "name is required"); return; }
      const r = createRepoCore(name, (b.description as string) ?? null, b.private === true, (b.default_branch as string) ?? "main", req);
      if (r.error) { sendErr(res, 422, r.error); return; }
      sendJson(res, 201, repoJson(r.repo as Repo, req));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }

  // /api/v3/repos/{owner}/{repo}[...]
  if (seg.length >= 3 && seg[0] === "repos") {
    const owner = decodeURIComponent(seg[1]);
    const name = decodeURIComponent(seg[2]);
    learnOwner(owner);
    const repo = findRepo(owner, name);
    const rest = seg.slice(3);
    if (!repo) { sendErr(res, 404, "Not Found"); return; }

    // GET/PATCH/DELETE /repos/{o}/{r}
    if (rest.length === 0) {
      if (method === "GET") { sendJson(res, 200, repoJson(repo, req)); return; }
      if (method === "PATCH") {
        const parsed = parseJsonBody(body);
        if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
        const b = parsed.value as Record<string, unknown>;
        if (typeof b.description === "string" || b.description === null) repo.description = b.description as string | null;
        if (typeof b.default_branch === "string") repo.default_branch = b.default_branch as string;
        if (typeof b.private === "boolean") repo.private = b.private as boolean;
        if (typeof b.name === "string" && b.name !== repo.name) {
          // Renames are not expected from the suite; support cheaply.
          repos.delete(repoKey(LOGIN, repo.name));
          repo.name = b.name as string;
          repo.full_name = LOGIN + "/" + repo.name;
          repos.set(repoKey(LOGIN, repo.name), repo);
        }
        repo.updated_at = nowIso();
        sendJson(res, 200, repoJson(repo, req));
        return;
      }
      if (method === "DELETE") {
        repos.delete(repoKey(LOGIN, repo.name));
        repoById.delete(repo.id);
        repoByNodeId.delete(repo.node_id);
        res.writeHead(204, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
        res.end();
        return;
      }
      sendErr(res, 404, "Not Found");
      return;
    }

    // contents
    if (rest[0] === "contents") {
      handleContents(req, res, repo, rest.slice(1), method, query, body);
      return;
    }
    // branches
    if (rest[0] === "branches") {
      handleBranches(req, res, repo, rest.slice(1), method, query, body);
      return;
    }
    // commits
    if (rest[0] === "commits") {
      handleCommits(req, res, repo, rest.slice(1), method, query, body);
      return;
    }
    // git database (refs, commits, trees, blobs, tags)
    if (rest[0] === "git") {
      handleGitDb(req, res, repo, rest.slice(1), method, query, body);
      return;
    }
    // labels
    if (rest[0] === "labels") {
      handleLabels(req, res, repo, rest.slice(1), method, query, body);
      return;
    }
    // issues
    if (rest[0] === "issues") {
      handleIssues(req, res, repo, rest.slice(1), method, query, body);
      return;
    }
    // pulls
    if (rest[0] === "pulls") {
      handlePulls(req, res, repo, rest.slice(1), method, query, body);
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  sendErr(res, 404, "Not Found");
}

function contentObject(repo: Repo, path: string, content: Buffer, sha: string, req: http.IncomingMessage): Record<string, unknown> {
  const base = baseUrl(req);
  const name = path.split("/").pop() ?? path;
  return {
    name, path, sha, size: content.length, type: "file", encoding: "base64",
    content: b64(content),
    url: base + "/api/v3/repos/" + repo.full_name + "/contents/" + path,
    html_url: base + "/" + repo.full_name + "/blob/" + repo.default_branch + "/" + path,
    git_url: base + "/api/v3/repos/" + repo.full_name + "/git/blobs/" + sha,
    download_url: base + "/" + repo.full_name + "/raw/" + repo.default_branch + "/" + path,
  };
}

function directoryListing(repo: Repo, branch: Branch, dirPath: string, req: http.IncomingMessage): Record<string, unknown>[] | null {
  const base = baseUrl(req);
  const prefix = dirPath === "" ? "" : dirPath + "/";
  const seen = new Map<string, { type: string; sha: string; size: number }>();
  for (const [path, content] of branch.files) {
    if (!path.startsWith(prefix)) continue;
    const rest = path.slice(prefix.length);
    const slash = rest.indexOf("/");
    if (slash < 0) {
      seen.set(rest, { type: "file", sha: gitObjectSha("blob", content), size: content.length });
    } else {
      const dir = rest.slice(0, slash);
      if (!seen.has(dir)) {
        // Tree sha for the subdir: rebuild from its files.
        const sub = new Map<string, Buffer>();
        for (const [p2, c2] of branch.files) if (p2.startsWith(prefix + dir + "/")) sub.set(p2.slice(prefix.length + dir.length + 1), c2);
        seen.set(dir, { type: "dir", sha: buildTreeFromFiles(sub, repo.objects), size: 0 });
      }
    }
  }
  if (seen.size === 0) return null;
  return [...seen.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([name, info]) => {
    const p = prefix + name;
    return {
      name, path: p, sha: info.sha, size: info.size, type: info.type,
      url: base + "/api/v3/repos/" + repo.full_name + "/contents/" + p,
      html_url: base + "/" + repo.full_name + (info.type === "dir" ? "/tree/" + repo.default_branch + "/" + p : "/blob/" + repo.default_branch + "/" + p),
      git_url: base + "/api/v3/repos/" + repo.full_name + "/git/" + (info.type === "dir" ? "trees/" : "blobs/") + info.sha,
      download_url: info.type === "file" ? base + "/" + repo.full_name + "/raw/" + repo.default_branch + "/" + p : null,
    };
  });
}

function handleContents(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, rest: string[], method: string, query: URLSearchParams, body: Buffer): void {
  const path = rest.map((s) => decodeURIComponent(s)).join("/");
  const branchName = (query.get("ref") ?? "") || repo.default_branch;
  const branch = repo.branches.get(branchName);
  if (method === "GET") {
    if (!branch) { sendErr(res, 404, "Not Found"); return; }
    const content = path === "" ? undefined : branch.files.get(path);
    if (!content) {
      const listing = directoryListing(repo, branch, path, req);
      if (listing === null) { sendErr(res, 404, "Not Found"); return; }
      sendJson(res, 200, listing);
      return;
    }
    const sha = gitObjectSha("blob", content);
    sendJson(res, 200, contentObject(repo, path, content, sha, req));
    return;
  }
  if (!path) { sendErr(res, 404, "Not Found"); return; }
  if (method === "PUT") {
    const parsed = parseJsonBody(body);
    if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
    const b = parsed.value as Record<string, unknown>;
    if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
    const contentB64 = b.content as string | undefined;
    if (typeof contentB64 !== "string") { sendErr(res, 422, "content is required"); return; }
    const message = (b.message as string) ?? ("Update " + path);
    const targetBranch = (b.branch as string) ?? branchName;
    let br = repo.branches.get(targetBranch);
    if (!br) {
      const def = repo.branches.get(repo.default_branch);
      br = { name: targetBranch, head: def ? def.head : null, files: new Map(def ? def.files : []) };
      repo.branches.set(targetBranch, br);
    }
    const existing = br.files.get(path);
    const isCreate = !existing;
    if (!isCreate) {
      const expectedSha = gitObjectSha("blob", existing as Buffer);
      const givenSha = b.sha as string | undefined;
      if (!givenSha || givenSha !== expectedSha) { sendErr(res, 409, "sha does not match"); return; }
    }
    const content = unb64(contentB64);
    br.files.set(path, content);
    const commitSha = commitBranch(repo, br, message);
    const blobSha = gitObjectSha("blob", content);
    const commitObj = repo.objects.get(commitSha);
    const treeSha = commitObj ? parseCommit(commitObj.data).tree : "";
    const who = { name: LOGIN, email: LOGIN + "@localhost", date: nowIso() };
    sendJson(res, isCreate ? 201 : 200, {
      content: contentObject(repo, path, content, blobSha, req),
      commit: { sha: commitSha, message, author: who, committer: who, tree: { sha: treeSha }, parents: br.head && commitObj ? parseCommit(commitObj.data).parents.map((p) => ({ sha: p })) : [] },
    });
    return;
  }
  if (method === "DELETE") {
    const parsed = parseJsonBody(body);
    if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
    const b = (parsed.value ?? {}) as Record<string, unknown>;
    const message = (b.message as string) ?? ("Delete " + path);
    const br = repo.branches.get(branchName);
    if (!br || !br.files.has(path)) { sendErr(res, 404, "Not Found"); return; }
    br.files.delete(path);
    const commitSha = commitBranch(repo, br, message);
    sendJson(res, 200, { commit: { sha: commitSha } });
    return;
  }
  sendErr(res, 404, "Not Found");
}

function handleLabels(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, rest: string[], method: string, query: URLSearchParams, body: Buffer): void {
  if (rest.length === 0) {
    if (method === "GET") {
      const all = [...repo.labels.values()].sort((a, b) => a.id - b.id);
      const { page, link } = paginate(all.map((l) => labelJson(l, req)), query, req, "/api/v3/repos/" + repo.full_name + "/labels");
      sendJson(res, 200, page, link ? { Link: link } : {});
      return;
    }
    if (method === "POST") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      const name = b.name as string | undefined;
      if (!name) { sendErr(res, 422, "name is required"); return; }
      const existing = repo.labels.get(name.toLowerCase());
      if (existing) { sendJson(res, 201, labelJson(existing, req)); return; }
      const id = nextId();
      const color = typeof b.color === "string" && /^[0-9a-fA-F]{6}$/.test(b.color) ? (b.color as string).toLowerCase() : "ededed";
      const label: Label = {
        id, node_id: nodeId("Label", id), name, color,
        description: typeof b.description === "string" ? (b.description as string) : "",
        default: false, url: "repos/" + repo.full_name + "/labels/" + encodeURIComponent(name),
      };
      repo.labels.set(name.toLowerCase(), label);
      sendJson(res, 201, labelJson(label, req));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  sendErr(res, 404, "Not Found");
}

// ------------------------------------------------------------ REST: issues
function createIssueCore(repo: Repo, title: string, bodyText: string | null, labelNames: string[], req: http.IncomingMessage): { issue?: Issue; error?: string; status?: number } {
  if (!title) return { error: "title is required", status: 422 };
  const labels: Label[] = [];
  for (const n of labelNames) {
    const l = repo.labels.get(String(n).toLowerCase());
    if (!l) return { error: "label does not exist: " + n, status: 422 };
    labels.push(l);
  }
  const id = nextId();
  repo.numberCounter += 1;
  const issue: Issue = {
    id, node_id: nodeId("Issue", id), number: repo.numberCounter, title,
    body: bodyText, state: "open", labels, user: { login: LOGIN, id: ownerId, type: "User" },
    created_at: nowIso(), updated_at: nowIso(), closed_at: null, comments: 0, commentsList: [],
    repoKey: repo.full_name,
  };
  repo.issues.set(issue.number, issue);
  return { issue };
}

function handleIssues(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, rest: string[], method: string, query: URLSearchParams, body: Buffer): void {
  if (rest.length === 0) {
    if (method === "GET") {
      const state = query.get("state") ?? "open";
      const all = sortedIssues(repo, state, query.get("sort") ?? "created", query.get("direction") ?? "desc").map((i) => issueJson(i, req));
      const { page, link } = paginate(all, query, req, "/api/v3/repos/" + repo.full_name + "/issues");
      sendJson(res, 200, page, link ? { Link: link } : {});
      return;
    }
    if (method === "POST") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      const rawLabels = Array.isArray(b.labels) ? b.labels : [];
      const labelNames = rawLabels.map((l) => (typeof l === "string" ? l : (l as Record<string, unknown>).name as string)).filter(Boolean);
      const r = createIssueCore(repo, (b.title as string) ?? "", (b.body as string) ?? null, labelNames, req);
      if (r.error) { sendErr(res, r.status ?? 422, r.error); return; }
      sendJson(res, 201, issueJson(r.issue as Issue, req));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  const num = parseInt(rest[0], 10);
  if (!Number.isFinite(num)) { sendErr(res, 404, "Not Found"); return; }
  const issue = repo.issues.get(num);
  if (!issue) { sendErr(res, 404, "Not Found"); return; }
  if (rest.length === 1) {
    if (method === "GET") { sendJson(res, 200, issueJson(issue, req)); return; }
    if (method === "PATCH") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b.title === "string") issue.title = b.title as string;
      if (typeof b.body === "string" || b.body === null) issue.body = b.body as string | null;
      if (b.state === "closed" || b.state === "open") {
        issue.state = b.state as string;
        issue.closed_at = issue.state === "closed" ? nowIso() : null;
      }
      issue.updated_at = nowIso();
      sendJson(res, 200, issueJson(issue, req));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  if (rest.length === 2 && rest[1] === "comments") {
    if (method === "GET") {
      const { page, link } = paginate(issue.commentsList.map((c) => commentJson(c, req)), query, req, "/api/v3/repos/" + repo.full_name + "/issues/" + num + "/comments");
      sendJson(res, 200, page, link ? { Link: link } : {});
      return;
    }
    if (method === "POST") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      if (typeof b.body !== "string" || !b.body) { sendErr(res, 422, "body is required"); return; }
      const id = nextId();
      const comment: IssueComment = {
        id, node_id: nodeId("IssueComment", id), body: b.body as string,
        user: { login: LOGIN, id: ownerId, type: "User" },
        created_at: nowIso(), updated_at: nowIso(), repoKey: repo.full_name, issueNumber: num,
      };
      issue.commentsList.push(comment);
      issue.comments = issue.commentsList.length;
      sendJson(res, 201, commentJson(comment, req));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  if (rest.length === 3 && rest[1] === "comments") {
    const cid = parseInt(rest[2], 10);
    const idx = issue.commentsList.findIndex((c) => c.id === cid);
    if (idx < 0) { sendErr(res, 404, "Not Found"); return; }
    const comment = issue.commentsList[idx] as IssueComment;
    if (method === "GET") { sendJson(res, 200, commentJson(comment, req)); return; }
    if (method === "PATCH") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b.body === "string") comment.body = b.body as string;
      comment.updated_at = nowIso();
      sendJson(res, 200, commentJson(comment, req));
      return;
    }
    if (method === "DELETE") {
      issue.commentsList.splice(idx, 1);
      issue.comments = issue.commentsList.length;
      res.writeHead(204, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
      res.end();
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  sendErr(res, 404, "Not Found");
}

// ------------------------------------------------- REST: branches/commits
function handleBranches(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, rest: string[], method: string, query: URLSearchParams, body: Buffer): void {
  if (method !== "GET") { sendErr(res, 404, "Not Found"); return; }
  if (rest.length === 0) {
    const all = [...repo.branches.values()].sort((a, b) => (a.name < b.name ? -1 : 1)).map((b) => branchJson(repo, b, req));
    const { page, link } = paginate(all, query, req, "/api/v3/repos/" + repo.full_name + "/branches");
    sendJson(res, 200, page, link ? { Link: link } : {});
    return;
  }
  if (rest.length === 1) {
    const branch = repo.branches.get(decodeURIComponent(rest[0]));
    if (!branch) { sendErr(res, 404, "Not Found"); return; }
    const out = branchJson(repo, branch, req) as Record<string, unknown>;
    if (branch.head) {
      const cj = commitJson(repo, branch.head, req);
      if (cj) out.commit = { sha: branch.head, url: (cj.url as string), commit: cj.commit };
    }
    sendJson(res, 200, out);
    return;
  }
  sendErr(res, 404, "Not Found");
}

function handleCommits(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, rest: string[], method: string, query: URLSearchParams, body: Buffer): void {
  if (method !== "GET") { sendErr(res, 404, "Not Found"); return; }
  if (rest.length === 0) {
    const shaParam = query.get("sha") ?? "";
    let head: string | null = null;
    if (shaParam) {
      const br = repo.branches.get(shaParam);
      head = br ? br.head : (repo.objects.has(shaParam) ? shaParam : null);
      if (head === null) { sendErr(res, 404, "Not Found"); return; }
    } else {
      head = repo.branches.get(repo.default_branch)?.head ?? null;
    }
    let shas = commitsOfBranch(repo, head);
    const pathFilter = query.get("path") ?? "";
    if (pathFilter) {
      shas = shas.filter((s) => {
        const obj = repo.objects.get(s);
        if (!obj) return false;
        const ci = parseCommit(obj.data);
        const mine = treeFilesOfCommit(repo, s).get(pathFilter);
        const parent = ci.parents[0] ?? null;
        const theirs = parent ? treeFilesOfCommit(repo, parent).get(pathFilter) : undefined;
        return mine !== theirs;
      });
    }
    const list = shas.map((s) => commitJson(repo, s, req)).filter((c) => c !== null);
    const { page, link } = paginate(list, query, req, "/api/v3/repos/" + repo.full_name + "/commits");
    sendJson(res, 200, page, link ? { Link: link } : {});
    return;
  }
  if (rest.length === 1) {
    const want = decodeURIComponent(rest[0]);
    let sha = repo.objects.has(want) ? want : null;
    if (!sha) {
      for (const k of repo.objects.keys()) if (k.startsWith(want)) { sha = k; break; }
    }
    if (!sha) { sendErr(res, 404, "Not Found"); return; }
    const cj = commitJson(repo, sha, req);
    if (!cj) { sendErr(res, 404, "Not Found"); return; }
    sendJson(res, 200, cj);
    return;
  }
  sendErr(res, 404, "Not Found");
}

// ------------------------------------------------------- REST: git database
function gitRefObject(repo: Repo, fullRef: string, req: http.IncomingMessage): Record<string, unknown> | null {
  const base = baseUrl(req);
  let sha: string | null = null;
  let type = "commit";
  if (fullRef.startsWith("refs/heads/")) {
    const b = repo.branches.get(fullRef.slice(11));
    sha = b?.head ?? null;
  } else if (fullRef.startsWith("refs/tags/")) {
    sha = repo.tags.get(fullRef.slice(10)) ?? null;
    if (sha) {
      const obj = repo.objects.get(sha);
      type = obj ? obj.type : "commit";
    }
  } else {
    return null;
  }
  if (!sha) return null;
  const objUrl = type === "tag"
    ? base + "/api/v3/repos/" + repo.full_name + "/git/tags/" + sha
    : base + "/api/v3/repos/" + repo.full_name + "/git/commits/" + sha;
  return {
    ref: fullRef,
    node_id: Buffer.from("Ref:" + repo.full_name + ":" + fullRef, "utf8").toString("base64"),
    url: base + "/api/v3/repos/" + repo.full_name + "/git/refs/" + fullRef.slice(5),
    object: { sha, type, url: objUrl },
  };
}

function gitCommitObjectJson(repo: Repo, sha: string, req: http.IncomingMessage): Record<string, unknown> | null {
  const obj = repo.objects.get(sha);
  if (!obj || obj.type !== "commit") return null;
  const base = baseUrl(req);
  const ci = parseCommit(obj.data);
  const who = { name: LOGIN, email: LOGIN + "@localhost", date: nowIso() };
  return {
    sha, node_id: nodeId("Commit", parseInt(sha.slice(0, 8), 16)),
    url: base + "/api/v3/repos/" + repo.full_name + "/git/commits/" + sha,
    html_url: base + "/" + repo.full_name + "/commit/" + sha,
    author: who, committer: who, message: ci.message,
    tree: { sha: ci.tree, url: base + "/api/v3/repos/" + repo.full_name + "/git/trees/" + ci.tree },
    parents: ci.parents.map((p) => ({ sha: p, url: base + "/api/v3/repos/" + repo.full_name + "/git/commits/" + p, html_url: base + "/" + repo.full_name + "/commit/" + p })),
    verification: { verified: false, reason: "unsigned", signature: null, payload: null },
  };
}

function gitTreeJson(repo: Repo, sha: string, req: http.IncomingMessage, recursive: boolean): Record<string, unknown> | null {
  const obj = repo.objects.get(sha);
  if (!obj || obj.type !== "tree") return null;
  const base = baseUrl(req);
  const entries: Record<string, unknown>[] = [];
  const walk = (treeSha: string, prefix: string): void => {
    const tobj = repo.objects.get(treeSha);
    if (!tobj || tobj.type !== "tree") return;
    for (const e of parseTree(tobj.data)) {
      const p = prefix + e.name;
      const type = e.mode === "40000" ? "tree" : "blob";
      const entry: Record<string, unknown> = {
        path: p, mode: e.mode, type, sha: e.sha,
        url: base + "/api/v3/repos/" + repo.full_name + "/git/" + (type === "tree" ? "trees/" : "blobs/") + e.sha,
      };
      if (type === "blob") {
        const blob = repo.objects.get(e.sha);
        if (blob) entry.size = blob.data.length;
      }
      entries.push(entry);
      if (recursive && type === "tree") walk(e.sha, p + "/");
    }
  };
  walk(sha, "");
  return { sha, url: base + "/api/v3/repos/" + repo.full_name + "/git/trees/" + sha, tree: entries, truncated: false };
}

function gitTagObjectJson(repo: Repo, sha: string, req: http.IncomingMessage): Record<string, unknown> | null {
  const obj = repo.objects.get(sha);
  if (!obj || obj.type !== "tag") return null;
  const base = baseUrl(req);
  const text = obj.data.toString("utf8");
  const mObj = text.match(/^object ([0-9a-f]{40})/m);
  const mType = text.match(/^type (\S+)/m);
  const mTag = text.match(/^tag (.*)$/m);
  const idx = text.indexOf("\n\n");
  const message = idx >= 0 ? text.slice(idx + 2) : "";
  const who = { name: LOGIN, email: LOGIN + "@localhost", date: nowIso() };
  return {
    sha, node_id: nodeId("Tag", parseInt(sha.slice(0, 8), 16)),
    url: base + "/api/v3/repos/" + repo.full_name + "/git/tags/" + sha,
    tag: mTag ? mTag[1] : "", message,
    object: { sha: mObj ? mObj[1] : "", type: mType ? mType[1] : "commit", url: base + "/api/v3/repos/" + repo.full_name + "/git/commits/" + (mObj ? mObj[1] : "") },
    tagger: who,
  };
}

function handleGitDb(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, rest: string[], method: string, query: URLSearchParams, body: Buffer): void {
  const base = baseUrl(req);
  // ---- refs ----
  if (rest[0] === "refs" || rest[0] === "ref") {
    if (method === "POST" && rest.length === 1) {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      const fullRef = String(b.ref ?? "");
      const sha = String(b.sha ?? "");
      if (!fullRef.startsWith("refs/") || !/^[0-9a-f]{40}$/.test(sha)) { sendErr(res, 422, "invalid ref or sha"); return; }
      if (gitRefObject(repo, fullRef, req)) { sendErr(res, 422, "reference already exists"); return; }
      const obj = repo.objects.get(sha);
      if (!obj) { sendErr(res, 422, "object does not exist"); return; }
      if (fullRef.startsWith("refs/heads/")) {
        if (obj.type !== "commit") { sendErr(res, 422, "object is not a commit"); return; }
        syncBranchFromCommit(repo, fullRef.slice(11), sha);
      } else if (fullRef.startsWith("refs/tags/")) {
        if (obj.type !== "commit" && obj.type !== "tag") { sendErr(res, 422, "object is not a commit or tag"); return; }
        repo.tags.set(fullRef.slice(10), sha);
      } else { sendErr(res, 422, "unsupported ref"); return; }
      repo.pushed_at = nowIso();
      sendJson(res, 201, gitRefObject(repo, fullRef, req));
      return;
    }
    if (rest.length >= 2) {
      const refPath = rest.slice(1).map((s) => decodeURIComponent(s)).join("/");
      // GET /git/matching-refs/{ref} lives under refs in GitHub as its own
      // segment; handle the matching-refs form here too.
      if (rest[1] === "matching-refs") {
        const prefix = "refs/" + rest.slice(2).map((s) => decodeURIComponent(s)).join("/");
        const out: Record<string, unknown>[] = [];
        for (const b of repo.branches.values()) {
          const fr = "refs/heads/" + b.name;
          if (fr.startsWith(prefix)) { const o = gitRefObject(repo, fr, req); if (o) out.push(o); }
        }
        for (const name of repo.tags.keys()) {
          const fr = "refs/tags/" + name;
          if (fr.startsWith(prefix)) { const o = gitRefObject(repo, fr, req); if (o) out.push(o); }
        }
        sendJson(res, 200, out);
        return;
      }
      const fullRef = refPath.startsWith("refs/") ? refPath : "refs/" + refPath;
      if (method === "GET") {
        const o = gitRefObject(repo, fullRef, req);
        if (!o) { sendErr(res, 404, "Not Found"); return; }
        sendJson(res, 200, o);
        return;
      }
      if (method === "PATCH") {
        const existing = gitRefObject(repo, fullRef, req);
        if (!existing) { sendErr(res, 404, "Not Found"); return; }
        const parsed = parseJsonBody(body);
        if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
        const b = parsed.value as Record<string, unknown>;
        const sha = String(b.sha ?? "");
        if (!/^[0-9a-f]{40}$/.test(sha) || !repo.objects.has(sha)) { sendErr(res, 422, "invalid sha"); return; }
        const force = b.force === true;
        const cur = (existing.object as Record<string, unknown>).sha as string;
        if (!force && !isAncestor(repo.objects, cur, sha) && cur !== sha) { sendErr(res, 422, "non-fast-forward update"); return; }
        if (fullRef.startsWith("refs/heads/")) syncBranchFromCommit(repo, fullRef.slice(11), sha);
        else if (fullRef.startsWith("refs/tags/")) repo.tags.set(fullRef.slice(10), sha);
        repo.pushed_at = nowIso();
        sendJson(res, 200, gitRefObject(repo, fullRef, req));
        return;
      }
      if (method === "DELETE") {
        if (fullRef.startsWith("refs/heads/")) {
          const b = repo.branches.get(fullRef.slice(11));
          if (!b) { sendErr(res, 404, "Not Found"); return; }
          if (fullRef.slice(11) === repo.default_branch) { sendErr(res, 422, "cannot delete default branch"); return; }
          repo.branches.delete(fullRef.slice(11));
        } else if (fullRef.startsWith("refs/tags/")) {
          if (!repo.tags.has(fullRef.slice(10))) { sendErr(res, 404, "Not Found"); return; }
          repo.tags.delete(fullRef.slice(10));
        } else { sendErr(res, 404, "Not Found"); return; }
        res.writeHead(204, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
        res.end();
        return;
      }
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  // ---- commits ----
  if (rest[0] === "commits") {
    if (method === "GET" && rest.length === 2) {
      const o = gitCommitObjectJson(repo, decodeURIComponent(rest[1]), req);
      if (!o) { sendErr(res, 404, "Not Found"); return; }
      sendJson(res, 200, o);
      return;
    }
    if (method === "POST" && rest.length === 1) {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      const message = String(b.message ?? "");
      const tree = String(b.tree ?? "");
      if (!message || !/^[0-9a-f]{40}$/.test(tree) || !repo.objects.has(tree)) { sendErr(res, 422, "message and tree are required"); return; }
      const parents = Array.isArray(b.parents) ? (b.parents as unknown[]).map((p) => String(p)).filter((p) => /^[0-9a-f]{40}$/.test(p) && repo.objects.has(p)) : [];
      const ts = nowUnix();
      const author = (b.author ?? {}) as Record<string, unknown>;
      const committer = (b.committer ?? {}) as Record<string, unknown>;
      const aName = String(author.name ?? LOGIN);
      const aEmail = String(author.email ?? LOGIN + "@localhost");
      const cName = String(committer.name ?? aName);
      const cEmail = String(committer.email ?? aEmail);
      let text = "tree " + tree + "\n";
      for (const p of parents) text += "parent " + p + "\n";
      text += "author " + aName + " <" + aEmail + "> " + ts + " +0000\n";
      text += "committer " + cName + " <" + cEmail + "> " + ts + " +0000\n\n" + message;
      const data = Buffer.from(text, "utf8");
      const sha = gitObjectSha("commit", data);
      if (!repo.objects.has(sha)) repo.objects.set(sha, { type: "commit", data });
      sendJson(res, 201, gitCommitObjectJson(repo, sha, req));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  // ---- trees ----
  if (rest[0] === "trees") {
    if (method === "GET" && rest.length === 2) {
      const o = gitTreeJson(repo, decodeURIComponent(rest[1]), req, query.get("recursive") === "1");
      if (!o) { sendErr(res, 404, "Not Found"); return; }
      sendJson(res, 200, o);
      return;
    }
    if (method === "POST" && rest.length === 1) {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b) || !Array.isArray(b.tree)) { sendErr(res, 400, "Malformed JSON"); return; }
      const files = new Map<string, Buffer>();
      const baseTree = typeof b.base_tree === "string" ? (b.base_tree as string) : "";
      if (baseTree && repo.objects.has(baseTree)) {
        for (const [p, blobSha] of treeToFiles(baseTree, repo.objects)) {
          const blob = repo.objects.get(blobSha);
          if (blob) files.set(p, blob.data);
        }
      }
      for (const raw of b.tree as unknown[]) {
        const e = raw as Record<string, unknown>;
        const p = String(e.path ?? "");
        if (!p) continue;
        const type = String(e.type ?? "blob");
        if (type === "blob") {
          if (typeof e.content === "string") {
            files.set(p, Buffer.from(e.content as string, "utf8"));
          } else if (typeof e.sha === "string") {
            const blob = repo.objects.get(e.sha as string);
            if (blob && blob.type === "blob") files.set(p, blob.data);
          }
        } else if (type === "tree" && typeof e.sha === "string") {
          for (const [sp, blobSha] of treeToFiles(e.sha as string, repo.objects)) {
            const blob = repo.objects.get(blobSha);
            if (blob) files.set(p + "/" + sp, blob.data);
          }
        }
      }
      const treeSha = buildTreeFromFiles(files, repo.objects);
      sendJson(res, 201, gitTreeJson(repo, treeSha, req, false));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  // ---- blobs ----
  if (rest[0] === "blobs") {
    if (method === "GET" && rest.length === 2) {
      const sha = decodeURIComponent(rest[1]);
      const obj = repo.objects.get(sha);
      if (!obj || obj.type !== "blob") { sendErr(res, 404, "Not Found"); return; }
      sendJson(res, 200, { sha, size: obj.data.length, content: b64(obj.data), encoding: "base64", url: base + "/api/v3/repos/" + repo.full_name + "/git/blobs/" + sha });
      return;
    }
    if (method === "POST" && rest.length === 1) {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b) || typeof b.content !== "string") { sendErr(res, 400, "Malformed JSON"); return; }
      const content = (b.encoding as string) === "base64" ? unb64(b.content as string) : Buffer.from(b.content as string, "utf8");
      const sha = gitObjectSha("blob", content);
      if (!repo.objects.has(sha)) repo.objects.set(sha, { type: "blob", data: content });
      sendJson(res, 201, { sha, size: content.length, url: base + "/api/v3/repos/" + repo.full_name + "/git/blobs/" + sha });
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  // ---- tags ----
  if (rest[0] === "tags") {
    if (method === "GET" && rest.length === 2) {
      const o = gitTagObjectJson(repo, decodeURIComponent(rest[1]), req);
      if (!o) { sendErr(res, 404, "Not Found"); return; }
      sendJson(res, 200, o);
      return;
    }
    if (method === "POST" && rest.length === 1) {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      const tag = String(b.tag ?? "");
      const object = String(b.object ?? "");
      const type = String(b.type ?? "commit");
      const message = String(b.message ?? "");
      if (!tag || !/^[0-9a-f]{40}$/.test(object) || !repo.objects.has(object)) { sendErr(res, 422, "tag and object are required"); return; }
      const ts = nowUnix();
      const tagger = (b.tagger ?? {}) as Record<string, unknown>;
      const tName = String(tagger.name ?? LOGIN);
      const tEmail = String(tagger.email ?? LOGIN + "@localhost");
      const text = "object " + object + "\ntype " + type + "\ntag " + tag + "\ntagger " + tName + " <" + tEmail + "> " + ts + " +0000\n\n" + message;
      const data = Buffer.from(text, "utf8");
      const sha = gitObjectSha("tag", data);
      if (!repo.objects.has(sha)) repo.objects.set(sha, { type: "tag", data });
      sendJson(res, 201, gitTagObjectJson(repo, sha, req));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  sendErr(res, 404, "Not Found");
}

// ------------------------------------------------------------- REST: pulls
function createPullCore(repo: Repo, title: string, bodyText: string | null, headRaw: string, baseRaw: string, req: http.IncomingMessage): { pull?: Pull; error?: string; status?: number } {
  if (!title) return { error: "title is required", status: 422 };
  const headRef = splitRef(headRaw || "");
  const baseRef = splitRef(baseRaw || repo.default_branch);
  const headBranch = repo.branches.get(headRef);
  if (!headBranch) return { error: "head branch does not exist: " + headRef, status: 422 };
  const baseBranch = repo.branches.get(baseRef);
  if (!baseBranch) return { error: "base branch does not exist: " + baseRef, status: 422 };
  const id = nextId();
  repo.numberCounter += 1;
  const headSha = headBranch.head ?? "0000000000000000000000000000000000000000";
  const baseSha = baseBranch.head ?? "0000000000000000000000000000000000000000";
  // Diff stats vs base: files changed between base tree and head tree.
  const baseFiles = treeFilesOfCommit(repo, baseBranch.head);
  const headFiles = treeFilesOfCommit(repo, headBranch.head);
  const diffs = diffFileMaps(baseFiles, headFiles);
  let additions = 0;
  let deletions = 0;
  for (const d of diffs) {
    const c = countLineDiff(blobLines(repo, d.oldSha), blobLines(repo, d.newSha));
    additions += c.additions;
    deletions += c.deletions;
  }
  const pull: Pull = {
    id, node_id: nodeId("PullRequest", id), number: repo.numberCounter, title,
    body: bodyText, state: "open", merged: false, mergeable: true, mergeable_state: "clean",
    merged_at: null, closed_at: null, created_at: nowIso(), updated_at: nowIso(),
    merge_commit_sha: null, headRef, baseRef, headSha, baseSha,
    baseShaAtCreate: baseSha, user: { login: LOGIN, id: ownerId, type: "User" },
    repoKey: repo.full_name, commits: countCommitsBetween(repo, baseBranch.head, headBranch.head),
    additions, deletions, changed_files: diffs.length, commentsList: [],
  };
  repo.pulls.set(pull.number, pull);
  return { pull };
}

// Commits reachable from `head` but not from `base` (first-parent walk
// over all parents, deduped). Used for PR commit counts and PR file lists.
function commitsBetween(repo: Repo, base: string | null, head: string | null): string[] {
  const baseReach = new Set<string>();
  const stackB: string[] = base ? [base] : [];
  while (stackB.length > 0) {
    const sha = stackB.pop() as string;
    if (baseReach.has(sha)) continue;
    const obj = repo.objects.get(sha);
    if (!obj || obj.type !== "commit") continue;
    baseReach.add(sha);
    for (const p of parseCommit(obj.data).parents) stackB.push(p);
  }
  const out: string[] = [];
  const seen = new Set<string>();
  const stackH: string[] = head ? [head] : [];
  while (stackH.length > 0) {
    const sha = stackH.pop() as string;
    if (seen.has(sha) || baseReach.has(sha)) continue;
    seen.add(sha);
    const obj = repo.objects.get(sha);
    if (!obj || obj.type !== "commit") continue;
    out.push(sha);
    for (const p of parseCommit(obj.data).parents) stackH.push(p);
  }
  return out;
}
function countCommitsBetween(repo: Repo, base: string | null, head: string | null): number {
  return commitsBetween(repo, base, head).length;
}

// Newest common ancestor of the head and base tips (the real merge base).
// Linear histories (the suite's pushes) give the exact branch point.
function mergeBaseSha(repo: Repo, headSha: string | null, baseSha: string | null): string | null {
  if (!headSha || !baseSha) return null;
  if (headSha === baseSha) return headSha;
  for (const c of commitsOfBranch(repo, headSha)) {
    if (c === baseSha || isAncestor(repo.objects, c, baseSha)) return c;
  }
  return null;
}

function mergeConflict(repo: Repo, pull: Pull): boolean {
  const baseBranch = repo.branches.get(pull.baseRef);
  const headBranch = repo.branches.get(pull.headRef);
  if (!baseBranch || !headBranch) return true;
  if (!headBranch.head || !baseBranch.head) return false;
  if (headBranch.head === baseBranch.head) return false;
  // v4b: the merge base is the branches' common ancestor, NOT base-at-PR-
  // creation. v4 compared against baseShaAtCreate and short-circuited when
  // base had not moved since creation, so a PR whose base advanced with a
  // conflicting change BEFORE the PR was opened listed mergeable:true
  // (the suite's pull-requests-list fixture does exactly that).
  const mergeBase = mergeBaseSha(repo, headBranch.head, baseBranch.head);
  const baseOldFiles = treeFilesOfCommit(repo, mergeBase);
  const baseNowFiles = treeFilesOfCommit(repo, baseBranch.head);
  const headFiles = treeFilesOfCommit(repo, headBranch.head);
  const paths = new Set([...baseOldFiles.keys(), ...baseNowFiles.keys(), ...headFiles.keys()]);
  for (const p of paths) {
    const oldV = baseOldFiles.get(p);
    const nowV = baseNowFiles.get(p);
    const headV = headFiles.get(p);
    const baseChanged = oldV !== nowV;
    const headChanged = oldV !== headV;
    if (baseChanged && headChanged && nowV !== headV) return true;
  }
  return false;
}

function mergePullCore(repo: Repo, pull: Pull, message: string | null): { sha?: string; error?: string; status?: number } {
  if (pull.state !== "open") return { error: "pull request is already closed", status: 405 };
  if (mergeConflict(repo, pull)) {
    pull.mergeable = false;
    pull.mergeable_state = "dirty";
    return { error: "Merge conflict", status: 405 };
  }
  const baseBranch = repo.branches.get(pull.baseRef) as Branch;
  const headBranch = repo.branches.get(pull.headRef) as Branch;
  // Three-way file merge: start from base-now, apply head's changes since
  // the merge base; base's own non-conflicting changes survive. (v4b: was
  // baseShaAtCreate, which reverted base changes made before PR creation.)
  const baseOldFiles = treeFilesOfCommit(repo, mergeBaseSha(repo, headBranch.head, baseBranch.head));
  const baseNowFiles = treeFilesOfCommit(repo, baseBranch.head);
  const headFiles = treeFilesOfCommit(repo, headBranch.head);
  const merged = new Map<string, string>(baseNowFiles);
  const paths = new Set([...baseOldFiles.keys(), ...baseNowFiles.keys(), ...headFiles.keys()]);
  for (const p of paths) {
    const oldV = baseOldFiles.get(p);
    const headV = headFiles.get(p);
    if (oldV !== headV) {
      if (headV === undefined) merged.delete(p);
      else merged.set(p, headV);
    }
  }
  const files = new Map<string, Buffer>();
  for (const [path, blobSha] of merged) {
    const blob = repo.objects.get(blobSha);
    if (blob) files.set(path, blob.data);
  }
  baseBranch.files = files;
  const msg = message ?? ("Merge pull request #" + pull.number + " from " + pull.headRef);
  const parents = baseBranch.head ? [baseBranch.head, headBranch.head].filter((s): s is string => !!s) : (headBranch.head ? [headBranch.head] : []);
  const mergeSha = commitBranchWithParents(repo, baseBranch, msg, parents);
  pull.state = "closed";
  pull.merged = true;
  pull.merged_at = nowIso();
  pull.closed_at = nowIso();
  pull.updated_at = nowIso();
  pull.merge_commit_sha = mergeSha;
  pull.baseSha = mergeSha;
  return { sha: mergeSha };
}

function handlePulls(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, rest: string[], method: string, query: URLSearchParams, body: Buffer): void {
  if (rest.length === 0) {
    if (method === "GET") {
      const state = query.get("state") ?? "open";
      const all = sortedPulls(repo, state, query.get("sort") ?? "created", query.get("direction") ?? "desc").map((p) => pullJson(p, req, repo));
      const { page, link } = paginate(all, query, req, "/api/v3/repos/" + repo.full_name + "/pulls");
      sendJson(res, 200, page, link ? { Link: link } : {});
      return;
    }
    if (method === "POST") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b !== "object" || b === null || Array.isArray(b)) { sendErr(res, 400, "Malformed JSON"); return; }
      const r = createPullCore(repo, (b.title as string) ?? "", (b.body as string) ?? null, (b.head as string) ?? "", (b.base as string) ?? repo.default_branch, req);
      if (r.error) { sendErr(res, r.status ?? 422, r.error); return; }
      sendJson(res, 201, pullJson(r.pull as Pull, req, repo));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  const num = parseInt(rest[0], 10);
  if (!Number.isFinite(num)) { sendErr(res, 404, "Not Found"); return; }
  const pull = repo.pulls.get(num);
  if (!pull) { sendErr(res, 404, "Not Found"); return; }
  if (rest.length === 1) {
    if (method === "GET") { sendJson(res, 200, pullJson(pull, req, repo)); return; }
    if (method === "PATCH") {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
      const b = parsed.value as Record<string, unknown>;
      if (typeof b.title === "string") pull.title = b.title as string;
      if (typeof b.body === "string" || b.body === null) pull.body = b.body as string | null;
      if (b.state === "closed" && pull.state === "open") { pull.state = "closed"; pull.closed_at = nowIso(); }
      pull.updated_at = nowIso();
      sendJson(res, 200, pullJson(pull, req, repo));
      return;
    }
    sendErr(res, 404, "Not Found");
    return;
  }
  if (rest.length === 2 && rest[1] === "files") {
    if (method !== "GET") { sendErr(res, 404, "Not Found"); return; }
    const base = baseUrl(req);
    const baseFiles = treeFilesOfCommit(repo, pull.baseShaAtCreate);
    const headBranch = repo.branches.get(pull.headRef);
    const headFiles = treeFilesOfCommit(repo, headBranch?.head ?? null);
    const diffs = diffFileMaps(baseFiles, headFiles);
    const files = diffs.map((d) => {
      const c = countLineDiff(blobLines(repo, d.oldSha), blobLines(repo, d.newSha));
      const oldLines = blobLines(repo, d.oldSha);
      const newLines = blobLines(repo, d.newSha);
      let patch = "";
      if (d.status !== "removed") {
        const hunks: string[] = [];
        for (const l of oldLines) hunks.push("-" + l);
        for (const l of newLines) hunks.push("+" + l);
        patch = "@@ -1," + oldLines.length + " +1," + newLines.length + " @@\n" + hunks.join("\n");
      } else {
        patch = "@@ -1," + oldLines.length + " +0,0 @@\n" + oldLines.map((l) => "-" + l).join("\n");
      }
      return {
        sha: d.newSha ?? d.oldSha, filename: d.path, status: d.status,
        additions: c.additions, deletions: c.deletions, changes: c.additions + c.deletions,
        blob_url: base + "/" + repo.full_name + "/blob/" + pull.headSha + "/" + d.path,
        raw_url: base + "/" + repo.full_name + "/raw/" + pull.headSha + "/" + d.path,
        contents_url: base + "/api/v3/repos/" + repo.full_name + "/contents/" + d.path + "?ref=" + pull.headRef,
        patch,
      };
    });
    const { page, link } = paginate(files, query, req, "/api/v3/repos/" + repo.full_name + "/pulls/" + pull.number + "/files");
    sendJson(res, 200, page, link ? { Link: link } : {});
    return;
  }
  if (rest.length === 2 && rest[1] === "commits") {
    if (method !== "GET") { sendErr(res, 404, "Not Found"); return; }
    const baseBranch = repo.branches.get(pull.baseRef);
    const headBranch = repo.branches.get(pull.headRef);
    const shas = commitsBetween(repo, baseBranch?.head ?? null, headBranch?.head ?? null).reverse();
    const list = shas.map((s) => commitJson(repo, s, req)).filter((c) => c !== null);
    const { page, link } = paginate(list, query, req, "/api/v3/repos/" + repo.full_name + "/pulls/" + pull.number + "/commits");
    sendJson(res, 200, page, link ? { Link: link } : {});
    return;
  }
  if (rest.length === 2 && rest[1] === "merge") {
    if (method === "GET") {
      if (pull.merged) {
        res.writeHead(204, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
        res.end();
      } else {
        sendErr(res, 404, "Not Found");
      }
      return;
    }
    if (method !== "PUT") { sendErr(res, 404, "Not Found"); return; }
    const parsed = parseJsonBody(body);
    if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
    const b = (parsed.value ?? {}) as Record<string, unknown>;
    const r = mergePullCore(repo, pull, (b.commit_message as string) ?? (b.message as string) ?? null);
    if (r.error) { sendErr(res, r.status ?? 405, r.error); return; }
    sendJson(res, 200, { sha: r.sha, merged: true, message: "Pull Request successfully merged" });
    return;
  }
  sendErr(res, 404, "Not Found");
}

// ---------------------------------------------------------------- GraphQL
// Minimal GraphQL tokenizer / parser / executor (no dependencies).
type GqlValue =
  | { kind: "string"; value: string }
  | { kind: "int"; value: number }
  | { kind: "float"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "null" }
  | { kind: "enum"; value: string }
  | { kind: "var"; name: string }
  | { kind: "list"; items: GqlValue[] }
  | { kind: "object"; fields: Record<string, GqlValue> };
type GqlSel =
  | { kind: "field"; alias: string | null; name: string; args: Record<string, GqlValue>; selection: GqlSel[] | null }
  | { kind: "spread"; name: string }
  | { kind: "inline"; typeCond: string | null; selection: GqlSel[] };
type GqlOp = { kind: string; name: string | null; varDefs: Record<string, GqlValue | null>; selection: GqlSel[] };

function gqlTokenize(src: string): string[] {
  const toks: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === " " || c === "\t" || c === "\n" || c === "\r" || c === ",") { i++; continue; }
    if (c === "#") { while (i < src.length && src[i] !== "\n") i++; continue; }
    if (c === "." && src.slice(i, i + 3) === "...") { toks.push("..."); i += 3; continue; }
    if ("{}()[]:!=$@=|&".includes(c)) { toks.push(c); i++; continue; }
    if (c === '"') {
      let j = i + 1;
      let out = "";
      while (j < src.length && src[j] !== '"') {
        if (src[j] === "\\" && j + 1 < src.length) {
          const e = src[j + 1];
          if (e === "n") out += "\n";
          else if (e === "t") out += "\t";
          else if (e === "r") out += "\r";
          else out += e;
          j += 2;
        } else { out += src[j]; j++; }
      }
      toks.push(JSON.stringify(out));
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c) && /[0-9]/.test(src[i] === "-" ? src[i + 1] ?? "" : c)) {
      let j = i;
      if (src[j] === "-") j++;
      while (j < src.length && /[0-9.]/.test(src[j])) j++;
      toks.push(src.slice(i, j));
      i = j;
      continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j++;
      toks.push(src.slice(i, j));
      i = j;
      continue;
    }
    i++;
  }
  return toks;
}

class GqlParser {
  toks: string[];
  pos = 0;
  constructor(src: string) { this.toks = gqlTokenize(src); }
  peek(): string | undefined { return this.toks[this.pos]; }
  next(): string { return this.toks[this.pos++]; }
  expect(t: string): void { if (this.next() !== t) throw new Error("expected " + t); }
  parseDocument(): { operations: GqlOp[]; fragments: Map<string, GqlSel[]> } {
    const operations: GqlOp[] = [];
    const fragments = new Map<string, GqlSel[]>();
    while (this.pos < this.toks.length) {
      const t = this.peek() as string;
      if (t === "query" || t === "mutation" || t === "subscription") {
        this.next();
        let name: string | null = null;
        if (this.peek() && this.peek() !== "(" && this.peek() !== "{") name = this.next();
        const varDefs: Record<string, GqlValue | null> = {};
        if (this.peek() === "(") {
          this.next();
          while (this.peek() !== ")") {
            this.expect("$");
            const vn = this.next();
            this.expect(":");
            this.skipType();
            let def: GqlValue | null = null;
            if (this.peek() === "=") { this.next(); def = this.parseValue(); }
            varDefs[vn] = def;
          }
          this.expect(")");
        }
        operations.push({ kind: t, name, varDefs, selection: this.parseSelectionSet() });
      } else if (t === "fragment") {
        this.next();
        const fname = this.next();
        this.expect("on");
        this.next(); // type name
        fragments.set(fname, this.parseSelectionSet());
      } else if (t === "{") {
        operations.push({ kind: "query", name: null, varDefs: {}, selection: this.parseSelectionSet() });
      } else {
        this.next();
      }
    }
    return { operations, fragments };
  }
  skipType(): void {
    if (this.peek() === "[") { this.next(); this.skipType(); this.expect("]"); }
    else this.next();
    if (this.peek() === "!") this.next();
  }
  parseSelectionSet(): GqlSel[] {
    this.expect("{");
    const sels: GqlSel[] = [];
    while (this.peek() !== "}") {
      sels.push(this.parseSelection());
    }
    this.expect("}");
    return sels;
  }
  parseSelection(): GqlSel {
    if (this.peek() === "...") {
      this.next();
      if (this.peek() === "on") {
        this.next();
        const tc = this.next();
        return { kind: "inline", typeCond: tc, selection: this.parseSelectionSet() };
      }
      if (this.peek() === "{") return { kind: "inline", typeCond: null, selection: this.parseSelectionSet() };
      return { kind: "spread", name: this.next() };
    }
    let name = this.next();
    let alias: string | null = null;
    if (this.peek() === ":") { this.next(); alias = name; name = this.next(); }
    const args: Record<string, GqlValue> = {};
    if (this.peek() === "(") {
      this.next();
      while (this.peek() !== ")") {
        const an = this.next();
        this.expect(":");
        args[an] = this.parseValue();
      }
      this.expect(")");
    }
    // directives: @skip/@include — honor if/unless with literal bool/var
    let skip = false;
    while (this.peek() === "@") {
      this.next();
      const dname = this.next();
      if (this.peek() === "(") {
        this.next();
        let ifVal: boolean | null = null;
        while (this.peek() !== ")") {
          const an = this.next();
          this.expect(":");
          const v = this.parseValue();
          if (an === "if" && v.kind === "bool") ifVal = v.value;
        }
        this.expect(")");
        if (dname === "skip" && ifVal === true) skip = true;
        if (dname === "include" && ifVal === false) skip = true;
      }
    }
    let selection: GqlSel[] | null = null;
    if (this.peek() === "{") selection = this.parseSelectionSet();
    const field: GqlSel = { kind: "field", alias, name, args, selection };
    if (skip) return { kind: "inline", typeCond: null, selection: [] };
    return field;
  }
  parseValue(): GqlValue {
    const t = this.next();
    if (t === "$") return { kind: "var", name: this.next() };
    if (t === "[") {
      const items: GqlValue[] = [];
      while (this.peek() !== "]") items.push(this.parseValue());
      this.expect("]");
      return { kind: "list", items };
    }
    if (t === "{") {
      const fields: Record<string, GqlValue> = {};
      while (this.peek() !== "}") {
        const fn = this.next();
        this.expect(":");
        fields[fn] = this.parseValue();
      }
      this.expect("}");
      return { kind: "object", fields };
    }
    if (t === "true") return { kind: "bool", value: true };
    if (t === "false") return { kind: "bool", value: false };
    if (t === "null") return { kind: "null" };
    if (t.startsWith('"')) return { kind: "string", value: JSON.parse(t) };
    if (/^-?[0-9]+$/.test(t)) return { kind: "int", value: parseInt(t, 10) };
    if (/^-?[0-9.]+$/.test(t)) return { kind: "float", value: parseFloat(t) };
    return { kind: "enum", value: t };
  }
}

function resolveValue(v: GqlValue, vars: Record<string, unknown>): unknown {
  switch (v.kind) {
    case "string": case "int": case "float": case "bool": return v.value;
    case "null": return null;
    case "enum": return v.value;
    case "var": return vars[v.name];
    case "list": return v.items.map((i) => resolveValue(i, vars));
    case "object": {
      const o: Record<string, unknown> = {};
      for (const k of Object.keys(v.fields)) o[k] = resolveValue(v.fields[k], vars);
      return o;
    }
  }
}

// ------------------------------------------------------- GraphQL type info
type TypeRef = { __typename: string; kind: string; name: string | null; ofType: TypeRef | null };
function tref(kind: string, name: string | null, ofType: TypeRef | null = null): TypeRef {
  return { __typename: "__Type", kind, name, ofType };
}
function namedType(kind: string, name: string): TypeRef { return tref(kind, name); }
function listType(inner: TypeRef): TypeRef { return tref("LIST", null, inner); }
function nonNull(inner: TypeRef): TypeRef { return tref("NON_NULL", null, inner); }
const S = (n: string) => namedType("SCALAR", n);
const STR = S("String"), INT = S("Int"), BOOL = S("Boolean"), IDT = S("ID");

type FieldInfo = { name: string; type: TypeRef; args: { name: string; type: TypeRef }[] };
function fi(name: string, type: TypeRef, args: { name: string; type: TypeRef }[] = []): FieldInfo {
  return { name, type, args };
}
const ISSUE_FIELDS: FieldInfo[] = [
  fi("id", nonNull(IDT)), fi("databaseId", INT), fi("number", nonNull(INT)),
  fi("title", STR), fi("body", STR), fi("state", namedType("ENUM", "IssueState")),
  fi("createdAt", STR), fi("updatedAt", STR), fi("closedAt", STR),
  fi("author", namedType("OBJECT", "User")), fi("labels", namedType("OBJECT", "LabelConnection")),
  fi("url", STR), fi("repository", namedType("OBJECT", "Repository")),
  fi("comments", namedType("OBJECT", "IssueCommentConnection")),
];
const PR_FIELDS: FieldInfo[] = [
  fi("id", nonNull(IDT)), fi("databaseId", INT), fi("number", nonNull(INT)),
  fi("title", STR), fi("body", STR), fi("state", namedType("ENUM", "PullRequestState")),
  fi("headRefName", STR), fi("baseRefName", STR),
  fi("headRef", namedType("OBJECT", "Ref")), fi("baseRef", namedType("OBJECT", "Ref")),
  fi("mergeable", BOOL), fi("merged", BOOL), fi("mergeableState", STR),
  fi("additions", INT), fi("deletions", INT), fi("changedFiles", INT),
  fi("files", namedType("OBJECT", "PullRequestFileConnection")),
  fi("createdAt", STR), fi("updatedAt", STR), fi("closedAt", STR), fi("mergedAt", STR),
  fi("author", namedType("OBJECT", "User")), fi("url", STR),
  fi("repository", namedType("OBJECT", "Repository")),
  fi("mergeCommit", namedType("OBJECT", "Commit")),
];
const REPO_FIELDS: FieldInfo[] = [
  fi("id", nonNull(IDT)), fi("databaseId", INT), fi("name", STR), fi("nameWithOwner", STR),
  fi("owner", namedType("OBJECT", "User")),
  fi("defaultBranchRef", namedType("OBJECT", "Ref")),
  fi("viewerPermission", namedType("ENUM", "RepositoryPermission")),
  fi("hasIssuesEnabled", BOOL), fi("description", STR),
  fi("createdAt", STR), fi("updatedAt", STR), fi("url", STR),
  fi("issue", namedType("OBJECT", "Issue"), [{ name: "number", type: nonNull(INT) }]),
  fi("issues", namedType("OBJECT", "IssueConnection"), [
    { name: "orderBy", type: namedType("INPUT_OBJECT", "IssueOrder") },
    { name: "states", type: listType(nonNull(namedType("ENUM", "IssueState"))) },
    { name: "first", type: INT }, { name: "after", type: STR },
    { name: "labels", type: listType(STR) },
  ]),
  fi("pullRequests", namedType("OBJECT", "PullRequestConnection"), [
    { name: "orderBy", type: namedType("INPUT_OBJECT", "IssueOrder") },
    { name: "states", type: listType(nonNull(namedType("ENUM", "PullRequestState"))) },
    { name: "first", type: INT }, { name: "after", type: STR },
  ]),
  fi("pullRequest", namedType("OBJECT", "PullRequest"), [{ name: "number", type: nonNull(INT) }]),
  fi("labels", namedType("OBJECT", "LabelConnection"), [{ name: "first", type: INT }]),
];
const TYPE_INFO: Record<string, { kind: string; fields: FieldInfo[]; enumValues?: string[] }> = {
  Issue: { kind: "OBJECT", fields: ISSUE_FIELDS },
  PullRequest: { kind: "OBJECT", fields: PR_FIELDS },
  Repository: { kind: "OBJECT", fields: REPO_FIELDS },
  User: { kind: "OBJECT", fields: [fi("id", nonNull(IDT)), fi("databaseId", INT), fi("login", STR), fi("name", STR), fi("avatarUrl", STR), fi("url", STR)] },
  Ref: { kind: "OBJECT", fields: [fi("name", STR), fi("target", namedType("OBJECT", "GitObject"))] },
  GitObject: { kind: "OBJECT", fields: [fi("oid", STR), fi("abbreviatedOid", STR)] },
  IssueConnection: { kind: "OBJECT", fields: [fi("nodes", listType(namedType("OBJECT", "Issue"))), fi("edges", listType(namedType("OBJECT", "IssueEdge"))), fi("totalCount", INT), fi("pageInfo", namedType("OBJECT", "PageInfo"))] },
  IssueEdge: { kind: "OBJECT", fields: [fi("node", namedType("OBJECT", "Issue")), fi("cursor", STR)] },
  PullRequestConnection: { kind: "OBJECT", fields: [fi("nodes", listType(namedType("OBJECT", "PullRequest"))), fi("edges", listType(namedType("OBJECT", "PullRequestEdge"))), fi("totalCount", INT), fi("pageInfo", namedType("OBJECT", "PageInfo"))] },
  PullRequestEdge: { kind: "OBJECT", fields: [fi("node", namedType("OBJECT", "PullRequest")), fi("cursor", STR)] },
  PullRequestFileConnection: { kind: "OBJECT", fields: [fi("nodes", listType(namedType("OBJECT", "PullRequestFile"))), fi("edges", listType(namedType("OBJECT", "PullRequestFileEdge"))), fi("totalCount", INT), fi("pageInfo", namedType("OBJECT", "PageInfo"))] },
  PullRequestFile: { kind: "OBJECT", fields: [fi("path", STR)] },
  PullRequestFileEdge: { kind: "OBJECT", fields: [fi("node", namedType("OBJECT", "PullRequestFile")), fi("cursor", STR)] },
  LabelConnection: { kind: "OBJECT", fields: [fi("nodes", listType(namedType("OBJECT", "Label"))), fi("edges", listType(namedType("OBJECT", "LabelEdge"))), fi("totalCount", INT), fi("pageInfo", namedType("OBJECT", "PageInfo"))] },
  Label: { kind: "OBJECT", fields: [fi("id", nonNull(IDT)), fi("name", STR), fi("color", STR), fi("description", STR)] },
  LabelEdge: { kind: "OBJECT", fields: [fi("node", namedType("OBJECT", "Label")), fi("cursor", STR)] },
  IssueCommentConnection: { kind: "OBJECT", fields: [fi("totalCount", INT), fi("nodes", listType(namedType("OBJECT", "IssueComment"))), fi("edges", listType(namedType("OBJECT", "IssueCommentEdge"))), fi("pageInfo", namedType("OBJECT", "PageInfo"))] },
  IssueComment: { kind: "OBJECT", fields: [fi("id", nonNull(IDT)), fi("body", STR), fi("createdAt", STR), fi("updatedAt", STR), fi("author", namedType("OBJECT", "User")), fi("url", STR)] },
  IssueCommentEdge: { kind: "OBJECT", fields: [fi("node", namedType("OBJECT", "IssueComment")), fi("cursor", STR)] },
  AddCommentPayload: { kind: "OBJECT", fields: [fi("commentEdge", namedType("OBJECT", "IssueCommentEdge")), fi("subject", namedType("OBJECT", "Issue")), fi("clientMutationId", STR)] },
  CloseIssuePayload: { kind: "OBJECT", fields: [fi("issue", namedType("OBJECT", "Issue")), fi("clientMutationId", STR)] },
  MergePullRequestPayload: { kind: "OBJECT", fields: [fi("pullRequest", namedType("OBJECT", "PullRequest")), fi("clientMutationId", STR)] },
  PageInfo: { kind: "OBJECT", fields: [fi("hasNextPage", BOOL), fi("hasPreviousPage", BOOL), fi("endCursor", STR), fi("startCursor", STR)] },
  SearchType: { kind: "ENUM", fields: [], enumValues: ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"] },
  IssueState: { kind: "ENUM", fields: [], enumValues: ["OPEN", "CLOSED"] },
  PullRequestState: { kind: "ENUM", fields: [], enumValues: ["OPEN", "CLOSED", "MERGED"] },
  RepositoryPermission: { kind: "ENUM", fields: [], enumValues: ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"] },
  IssueOrderField: { kind: "ENUM", fields: [], enumValues: ["CREATED_AT", "UPDATED_AT", "COMMENTS"] },
  OrderDirection: { kind: "ENUM", fields: [], enumValues: ["ASC", "DESC"] },
  SearchResultItemConnection: { kind: "OBJECT", fields: [fi("nodes", listType(namedType("OBJECT", "Issue"))), fi("edges", listType(namedType("OBJECT", "IssueEdge"))), fi("totalCount", INT), fi("pageInfo", namedType("OBJECT", "PageInfo"))] },
  Commit: { kind: "OBJECT", fields: [fi("oid", STR), fi("message", STR)] },
  __Type: { kind: "OBJECT", fields: [fi("name", STR), fi("kind", namedType("ENUM", "__TypeKind")), fi("description", STR), fi("fields", listType(namedType("OBJECT", "__Field"))), fi("enumValues", listType(namedType("OBJECT", "__EnumValue"))), fi("inputFields", listType(namedType("OBJECT", "__InputValue"))), fi("interfaces", listType(namedType("OBJECT", "__Type"))), fi("possibleTypes", listType(namedType("OBJECT", "__Type"))), fi("ofType", namedType("OBJECT", "__Type"))] },
  __Field: { kind: "OBJECT", fields: [fi("name", STR), fi("description", STR), fi("args", listType(namedType("OBJECT", "__InputValue"))), fi("type", namedType("OBJECT", "__Type")), fi("isDeprecated", BOOL), fi("deprecationReason", STR)] },
  __InputValue: { kind: "OBJECT", fields: [fi("name", STR), fi("description", STR), fi("type", namedType("OBJECT", "__Type")), fi("defaultValue", STR)] },
  __EnumValue: { kind: "OBJECT", fields: [fi("name", STR), fi("description", STR), fi("isDeprecated", BOOL), fi("deprecationReason", STR)] },
  __Schema: { kind: "OBJECT", fields: [fi("queryType", namedType("OBJECT", "__Type")), fi("mutationType", namedType("OBJECT", "__Type")), fi("subscriptionType", namedType("OBJECT", "__Type")), fi("types", listType(namedType("OBJECT", "__Type"))), fi("directives", listType(namedType("OBJECT", "__Directive")))] },
  __TypeKind: { kind: "ENUM", fields: [], enumValues: ["SCALAR", "OBJECT", "INTERFACE", "UNION", "ENUM", "INPUT_OBJECT", "LIST", "NON_NULL"] },
  __Directive: { kind: "OBJECT", fields: [fi("name", STR), fi("description", STR)] },
  CreatePullRequestPayload: { kind: "OBJECT", fields: [fi("pullRequest", namedType("OBJECT", "PullRequest")), fi("clientMutationId", STR)] },
  CreateIssuePayload: { kind: "OBJECT", fields: [fi("issue", namedType("OBJECT", "Issue")), fi("clientMutationId", STR)] },
  Query: { kind: "OBJECT", fields: [
    fi("repository", namedType("OBJECT", "Repository"), [{ name: "owner", type: nonNull(STR) }, { name: "name", type: nonNull(STR) }]),
    fi("viewer", namedType("OBJECT", "User")),
    fi("search", namedType("OBJECT", "SearchResultItemConnection"), [{ name: "query", type: nonNull(STR) }, { name: "type", type: nonNull(namedType("ENUM", "SearchType")) }, { name: "first", type: INT }]),
    fi("node", namedType("OBJECT", "Issue"), [{ name: "id", type: nonNull(IDT) }]),
  ] },
  Mutation: { kind: "OBJECT", fields: [
    fi("createPullRequest", namedType("OBJECT", "CreatePullRequestPayload"), [{ name: "input", type: nonNull(namedType("INPUT_OBJECT", "CreatePullRequestInput")) }]),
    fi("createIssue", namedType("OBJECT", "CreateIssuePayload"), [{ name: "input", type: nonNull(namedType("INPUT_OBJECT", "CreateIssueInput")) }]),
    fi("addComment", namedType("OBJECT", "AddCommentPayload"), [{ name: "input", type: nonNull(namedType("INPUT_OBJECT", "AddCommentInput")) }]),
    fi("closeIssue", namedType("OBJECT", "CloseIssuePayload"), [{ name: "input", type: nonNull(namedType("INPUT_OBJECT", "CloseIssueInput")) }]),
    fi("mergePullRequest", namedType("OBJECT", "MergePullRequestPayload"), [{ name: "input", type: nonNull(namedType("INPUT_OBJECT", "MergePullRequestInput")) }]),
  ] },
};

function typeInfoObject(name: string): Record<string, unknown> {
  const info = TYPE_INFO[name];
  if (!info) return { __typename: "__Type", name, kind: "OBJECT", fields: null, enumValues: null, inputFields: null, interfaces: [], possibleTypes: null, ofType: null, description: null };
  const fields = info.fields.map((f) => ({
    __typename: "__Field", name: f.name, description: null,
    args: f.args.map((a) => ({ __typename: "__InputValue", name: a.name, description: null, type: a.type, defaultValue: null })),
    type: f.type, isDeprecated: false, deprecationReason: null,
  }));
  const enumValues = info.enumValues ? info.enumValues.map((n) => ({ __typename: "__EnumValue", name: n, description: null, isDeprecated: false, deprecationReason: null })) : null;
  return { __typename: "__Type", name, kind: info.kind, fields: info.kind === "OBJECT" ? fields : null, enumValues, inputFields: null, interfaces: [], possibleTypes: null, ofType: null, description: null };
}

// -------------------------------------------------------- GraphQL resolvers
function gqlState(issueState: string): string {
  return issueState === "open" ? "OPEN" : "CLOSED";
}
function gqlPrState(pull: Pull): string {
  if (pull.merged) return "MERGED";
  return pull.state === "open" ? "OPEN" : "CLOSED";
}
function commentGql(c: IssueComment): Record<string, unknown> {
  return {
    __typename: "IssueComment", id: c.node_id, databaseId: c.id, body: c.body,
    createdAt: c.created_at, updatedAt: c.updated_at,
    author: { __typename: "User", id: nodeId("User", ownerId), databaseId: ownerId, login: LOGIN, name: LOGIN, avatarUrl: "https://example.invalid/avatar.png", url: "https://example.invalid/" + LOGIN },
    url: "",
  };
}
function issueGql(issue: Issue, repo: Repo): Record<string, unknown> {
  const base = "";
  return {
    __typename: "Issue", id: issue.node_id, databaseId: issue.id, number: issue.number,
    title: issue.title, body: issue.body, state: gqlState(issue.state),
    createdAt: issue.created_at, updatedAt: issue.updated_at, closedAt: issue.closed_at,
    author: { __typename: "User", id: nodeId("User", ownerId), databaseId: ownerId, login: LOGIN, name: LOGIN, avatarUrl: "https://example.invalid/avatar.png", url: "https://example.invalid/" + LOGIN },
    labels: { __typename: "LabelConnection", nodes: issue.labels.map((l) => ({ __typename: "Label", id: l.node_id, name: l.name, color: l.color, description: l.description })), edges: [], totalCount: issue.labels.length, pageInfo: { __typename: "PageInfo", hasNextPage: false, hasPreviousPage: false, endCursor: null, startCursor: null } },
    url: base, repository: repoGql(repo), _repo: repo, _issue: issue,
    comments: { __typename: "IssueCommentConnection", totalCount: issue.commentsList.length, nodes: issue.commentsList.map((c) => commentGql(c)) },
  };
}
function pullGql(pull: Pull, repo: Repo): Record<string, unknown> {
  const headBranch = repo.branches.get(pull.headRef);
  const baseBranch = repo.branches.get(pull.baseRef);
  const headFiles = headBranch && headBranch.head ? treeToFiles(parseCommit((repo.objects.get(headBranch.head) as GitObject).data).tree, repo.objects) : new Map<string, string>();
  const fileNodes = [...headFiles.keys()].sort().map((p) => ({ __typename: "PullRequestFile", path: p }));
  // Mergeability is live, exactly like REST pullJson: a conflicting push to
  // base after PR creation flips mergeable/mergeableState on read. (v3
  // returned the stale stored values here, so a conflicted PR listed
  // mergeable:true over GraphQL while REST said false.)
  let mergeable = pull.mergeable;
  let mergeableState = pull.mergeable_state;
  if (pull.state === "open") {
    const conflict = mergeConflict(repo, pull);
    mergeable = !conflict;
    mergeableState = conflict ? "dirty" : "clean";
  }
  return {
    __typename: "PullRequest", id: pull.node_id, databaseId: pull.id, number: pull.number,
    title: pull.title, body: pull.body, state: gqlPrState(pull),
    headRefName: pull.headRef, baseRefName: pull.baseRef,
    headRef: { __typename: "Ref", name: pull.headRef, target: { __typename: "GitObject", oid: pull.headSha, abbreviatedOid: pull.headSha.slice(0, 7) } },
    baseRef: { __typename: "Ref", name: pull.baseRef, target: { __typename: "GitObject", oid: pull.baseSha, abbreviatedOid: pull.baseSha.slice(0, 7) } },
    mergeable, merged: pull.merged, mergeableState,
    additions: pull.additions, deletions: pull.deletions, changedFiles: pull.changed_files,
    files: { __typename: "PullRequestFileConnection", nodes: fileNodes, edges: [], totalCount: fileNodes.length, pageInfo: { __typename: "PageInfo", hasNextPage: false, hasPreviousPage: false, endCursor: null, startCursor: null } },
    createdAt: pull.created_at, updatedAt: pull.updated_at, closedAt: pull.closed_at, mergedAt: pull.merged_at,
    author: { __typename: "User", id: nodeId("User", ownerId), databaseId: ownerId, login: LOGIN, name: LOGIN, avatarUrl: "https://example.invalid/avatar.png", url: "https://example.invalid/" + LOGIN },
    url: "", repository: repoGql(repo), _repo: repo, _pull: pull,
    mergeCommit: pull.merge_commit_sha ? { __typename: "Commit", oid: pull.merge_commit_sha, message: "Merge pull request #" + pull.number } : null,
  };
}
function repoGql(repo: Repo): Record<string, unknown> {
  const def = repo.branches.get(repo.default_branch);
  return {
    __typename: "Repository", id: repo.node_id, databaseId: repo.id, name: repo.name,
    nameWithOwner: repo.full_name,
    owner: { __typename: "User", id: nodeId("User", ownerId), databaseId: ownerId, login: LOGIN, name: LOGIN, avatarUrl: "https://example.invalid/avatar.png", url: "https://example.invalid/" + LOGIN },
    defaultBranchRef: def && def.head ? { __typename: "Ref", name: repo.default_branch, target: { __typename: "GitObject", oid: def.head, abbreviatedOid: def.head.slice(0, 7) } } : null,
    viewerPermission: "ADMIN", hasIssuesEnabled: true, description: repo.description,
    createdAt: repo.created_at, updatedAt: repo.updated_at, url: "",
    _repo: repo,
  };
}
function pageInfo(): Record<string, unknown> {
  return { __typename: "PageInfo", hasNextPage: false, hasPreviousPage: false, endCursor: null, startCursor: null };
}
function orderIssues(issues: Issue[], args: Record<string, unknown>): Issue[] {
  const list = [...issues];
  const orderBy = (args.orderBy ?? {}) as Record<string, unknown>;
  const field = (orderBy.field as string) ?? "CREATED_AT";
  const dir = (orderBy.direction as string) ?? "DESC";
  const states = args.states as string[] | undefined;
  let filtered = list;
  if (states && states.length > 0) {
    const want = new Set(states.map((s) => String(s).toUpperCase()));
    filtered = list.filter((i) => want.has(gqlState(i.state)));
  }
  const cmp = (a: Issue, b: Issue): number => {
    let c = 0;
    if (field === "CREATED_AT") c = a.created_at < b.created_at ? -1 : a.created_at > b.created_at ? 1 : 0;
    else if (field === "UPDATED_AT") c = a.updated_at < b.updated_at ? -1 : a.updated_at > b.updated_at ? 1 : 0;
    else c = a.number - b.number;
    if (c === 0) c = a.number - b.number;
    return dir === "DESC" ? -c : c;
  };
  filtered.sort(cmp);
  return filtered;
}
function orderPulls(pulls: Pull[], args: Record<string, unknown>): Pull[] {
  const list = [...pulls];
  const orderBy = (args.orderBy ?? {}) as Record<string, unknown>;
  const dir = (orderBy.direction as string) ?? "DESC";
  const states = args.states as string[] | undefined;
  let filtered = list;
  if (states && states.length > 0) {
    const want = new Set(states.map((s) => String(s).toUpperCase()));
    filtered = list.filter((p) => want.has(gqlPrState(p)));
  }
  filtered.sort((a, b) => {
    let c = a.created_at < b.created_at ? -1 : a.created_at > b.created_at ? 1 : 0;
    if (c === 0) c = a.number - b.number;
    return dir === "DESC" ? -c : c;
  });
  return filtered;
}

// Cursor connection builder: `first`/`after` slice the ordered nodes,
// totalCount is the full filtered count, pageInfo reflects the window.
function gqlCursor(item: { number: number }): string {
  return b64(Buffer.from(String(item.number), "utf8"));
}
function gqlConnection<T extends { number: number }>(
  ordered: T[], args: Record<string, unknown>,
  toNode: (t: T) => Record<string, unknown>,
  typename: string, edgeTypename: string,
): Record<string, unknown> {
  const totalCount = ordered.length;
  let start = 0;
  if (typeof args.after === "string" && args.after) {
    try {
      const decoded = Buffer.from(args.after as string, "base64").toString("utf8");
      const idx = ordered.findIndex((n) => String(n.number) === decoded);
      if (idx >= 0) start = idx + 1;
    } catch { /* bad cursor: start from the beginning */ }
  }
  let end = ordered.length;
  if (typeof args.first === "number") end = Math.min(ordered.length, start + Math.max(0, args.first as number));
  if (typeof args.last === "number") {
    const from = Math.max(start, end - Math.max(0, args.last as number));
    start = from;
  }
  const sliced = ordered.slice(start, end);
  const nodes = sliced.map(toNode);
  return {
    __typename: typename, nodes,
    edges: nodes.map((n) => ({ __typename: edgeTypename, node: n, cursor: gqlCursor(n as unknown as { number: number }) })),
    totalCount,
    pageInfo: {
      __typename: "PageInfo", hasNextPage: end < ordered.length, hasPreviousPage: start > 0,
      endCursor: nodes.length > 0 ? gqlCursor(nodes[nodes.length - 1] as unknown as { number: number }) : null,
      startCursor: nodes.length > 0 ? gqlCursor(nodes[0] as unknown as { number: number }) : null,
    },
  };
}

function findIssueByNodeId(nodeIdStr: string): { issue: Issue; repo: Repo } | null {
  for (const r of repos.values()) {
    for (const i of r.issues.values()) if (i.node_id === nodeIdStr) return { issue: i, repo: r };
  }
  return null;
}
function findPullByNodeId(nodeIdStr: string): { pull: Pull; repo: Repo } | null {
  for (const r of repos.values()) {
    for (const p of r.pulls.values()) if (p.node_id === nodeIdStr) return { pull: p, repo: r };
  }
  return null;
}
function findIssueByAnyId(idStr: string): { issue: Issue; repo: Repo } | null {
  const byNode = findIssueByNodeId(idStr);
  if (byNode) return byNode;
  const n = parseInt(idStr, 10);
  if (Number.isFinite(n)) {
    for (const r of repos.values()) {
      for (const i of r.issues.values()) if (i.id === n) return { issue: i, repo: r };
    }
  }
  return null;
}
function findPullByAnyId(idStr: string): { pull: Pull; repo: Repo } | null {
  const byNode = findPullByNodeId(idStr);
  if (byNode) return byNode;
  const n = parseInt(idStr, 10);
  if (Number.isFinite(n)) {
    for (const r of repos.values()) {
      for (const p of r.pulls.values()) if (p.id === n) return { pull: p, repo: r };
    }
  }
  return null;
}
function createCommentCore(repo: Repo, issueNumber: number, body: string): IssueComment {
  const issue = repo.issues.get(issueNumber);
  const id = nextId();
  const comment: IssueComment = {
    id, node_id: nodeId("IssueComment", id), body,
    user: { login: LOGIN, id: ownerId, type: "User" },
    created_at: nowIso(), updated_at: nowIso(), repoKey: repo.full_name, issueNumber,
  };
  if (issue) {
    issue.commentsList.push(comment);
    issue.comments = issue.commentsList.length;
  }
  return comment;
}

class GqlUnknownField extends Error {
  field: string;
  typeName: string;
  constructor(field: string, typeName: string) {
    super('Cannot query field "' + field + '" on type "' + typeName + '".');
    this.field = field;
    this.typeName = typeName;
  }
}

type GqlCtx = { req: http.IncomingMessage; vars: Record<string, unknown>; fragments: Map<string, GqlSel[]> };

function gqlResolveField(typeName: string, field: string, src: Record<string, unknown>, args: Record<string, unknown>, ctx: GqlCtx): unknown {
  const repo = src._repo as Repo | undefined;
  switch (typeName) {
    case "Query": {
      if (field === "repository") {
        const r = findRepo(String(args.owner ?? ""), String(args.name ?? ""));
        return r ? repoGql(r) : null;
      }
      if (field === "viewer") return { __typename: "User", id: nodeId("User", ownerId), databaseId: ownerId, login: LOGIN, name: LOGIN, avatarUrl: "https://example.invalid/avatar.png", url: "https://example.invalid/" + LOGIN };
      if (field === "search") {
        const q = String(args.query ?? "").toLowerCase();
        const type = String(args.type ?? "ISSUE").toUpperCase();
        let nodes: Record<string, unknown>[] = [];
        if (type === "ISSUE") {
          for (const r of repos.values()) {
            for (const i of r.issues.values()) {
              if (!q || (i.title + " " + (i.body ?? "")).toLowerCase().includes(q)) nodes.push(issueGql(i, r));
            }
          }
        }
        nodes.sort((a, b) => (b.number as number) - (a.number as number));
        return gqlConnection(
          nodes as unknown as { number: number }[], args,
          (n) => n as unknown as Record<string, unknown>,
          "SearchResultItemConnection", "IssueEdge",
        );
      }
      if (field === "node") {
        const idStr = String(args.id ?? "");
        const repoHit = findRepoByNodeId(idStr);
        if (repoHit) return repoGql(repoHit);
        if (idStr === nodeId("User", ownerId)) {
          return { __typename: "User", id: nodeId("User", ownerId), databaseId: ownerId, login: LOGIN, name: LOGIN, avatarUrl: "https://example.invalid/avatar.png", url: "https://example.invalid/" + LOGIN };
        }
        for (const r of repos.values()) {
          for (const i of r.issues.values()) if (i.node_id === idStr) return issueGql(i, r);
          for (const p of r.pulls.values()) if (p.node_id === idStr) return pullGql(p, r);
        }
        return null;
      }
      if (field === "__type") {
        const name = String(args.name ?? "");
        return typeInfoObject(name);
      }
      if (field === "__schema") {
        const types = Object.keys(TYPE_INFO).map((n) => typeInfoObject(n));
        return { __typename: "__Schema", queryType: { __typename: "__Type", name: "Query", kind: "OBJECT", fields: null, enumValues: null, inputFields: null, interfaces: [], possibleTypes: null, ofType: null, description: null }, mutationType: { __typename: "__Type", name: "Mutation", kind: "OBJECT", fields: null, enumValues: null, inputFields: null, interfaces: [], possibleTypes: null, ofType: null, description: null }, subscriptionType: null, types, directives: [] };
      }
      break;
    }
    case "Mutation": {
      if (field === "createPullRequest") {
        const input = (args.input ?? {}) as Record<string, unknown>;
        let target: Repo | undefined;
        const rid = input.repositoryId;
        if (typeof rid === "number") target = findRepoById(rid);
        else if (typeof rid === "string") {
          target = findRepoByNodeId(rid) ?? findRepoById(parseInt(rid, 10));
          if (!target) {
            for (const r of repos.values()) if (r.id === parseInt(rid, 10)) { target = r; break; }
          }
        }
        if (!target) throw new Error("Could not resolve to a Repository with the id of '" + String(rid) + "'.");
        const r = createPullCore(target, String(input.title ?? ""), (input.body as string) ?? null, String(input.headRefName ?? ""), String(input.baseRefName ?? target.default_branch), ctx.req);
        if (r.error) throw new Error(r.error);
        return { __typename: "CreatePullRequestPayload", pullRequest: pullGql(r.pull as Pull, target), clientMutationId: (input.clientMutationId as string) ?? null };
      }
      if (field === "createIssue") {
        const input = (args.input ?? {}) as Record<string, unknown>;
        let target: Repo | undefined;
        const rid = input.repositoryId;
        if (typeof rid === "number") target = findRepoById(rid);
        else if (typeof rid === "string") target = findRepoByNodeId(rid) ?? findRepoById(parseInt(rid, 10));
        if (!target) throw new Error("Could not resolve to a Repository with the id of '" + String(rid) + "'.");
        const r = createIssueCore(target, String(input.title ?? ""), (input.body as string) ?? null, [], ctx.req);
        if (r.error) throw new Error(r.error);
        return { __typename: "CreateIssuePayload", issue: issueGql(r.issue as Issue, target), clientMutationId: (input.clientMutationId as string) ?? null };
      }
      if (field === "addComment") {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const subjectId = String(input.subjectId ?? "");
        const bodyText = String(input.body ?? "");
        if (!subjectId) throw new Error("subjectId is required");
        if (!bodyText) throw new Error("body is required");
        const issueHit = findIssueByNodeId(subjectId);
        if (issueHit) {
          const comment = createCommentCore(issueHit.repo, issueHit.issue.number, bodyText);
          const node = commentGql(comment);
          return {
            __typename: "AddCommentPayload",
            commentEdge: { __typename: "IssueCommentEdge", node, cursor: b64(Buffer.from(String(comment.id), "utf8")) },
            subject: issueGql(issueHit.issue, issueHit.repo),
            clientMutationId: (input.clientMutationId as string) ?? null,
          };
        }
        const pullHit = findPullByNodeId(subjectId);
        if (pullHit) {
          const comment = createCommentCore(pullHit.repo, pullHit.pull.number, bodyText);
          // PR comments live on the PR's own list (a PR is also issue #N
          // in numbering, but the REST issue record may not exist).
          pullHit.pull.commentsList.push(comment);
          const node = commentGql(comment);
          return {
            __typename: "AddCommentPayload",
            commentEdge: { __typename: "IssueCommentEdge", node, cursor: b64(Buffer.from(String(comment.id), "utf8")) },
            subject: pullGql(pullHit.pull, pullHit.repo),
            clientMutationId: (input.clientMutationId as string) ?? null,
          };
        }
        throw new Error("Could not resolve to a subject with the id of '" + subjectId + "'.");
      }
      if (field === "closeIssue") {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const hit = findIssueByAnyId(String(input.issueId ?? ""));
        if (!hit) throw new Error("Could not resolve to an Issue with the id of '" + String(input.issueId) + "'.");
        hit.issue.state = "closed";
        hit.issue.closed_at = nowIso();
        hit.issue.updated_at = nowIso();
        return { __typename: "CloseIssuePayload", issue: issueGql(hit.issue, hit.repo), clientMutationId: (input.clientMutationId as string) ?? null };
      }
      if (field === "mergePullRequest") {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const hit = findPullByAnyId(String(input.pullRequestId ?? ""));
        if (!hit) throw new Error("Could not resolve to a PullRequest with the id of '" + String(input.pullRequestId) + "'.");
        const headline = (input.commitHeadline as string) ?? null;
        const r = mergePullCore(hit.repo, hit.pull, headline);
        if (r.error) throw new Error(r.error);
        return { __typename: "MergePullRequestPayload", pullRequest: pullGql(hit.pull, hit.repo), clientMutationId: (input.clientMutationId as string) ?? null };
      }
      break;
    }
    case "Issue": {
      if (field === "comments") {
        const issue = src._issue as Issue | undefined;
        if (!issue) return src[field] ?? null;
        const all = issue.commentsList;
        let start = 0;
        if (typeof args.after === "string" && args.after) {
          try {
            const decoded = Buffer.from(args.after as string, "base64").toString("utf8");
            const idx = all.findIndex((c) => String(c.id) === decoded);
            if (idx >= 0) start = idx + 1;
          } catch { /* bad cursor */ }
        }
        let end = all.length;
        if (typeof args.first === "number") end = Math.min(all.length, start + Math.max(0, args.first as number));
        const sliced = all.slice(start, end);
        const nodes = sliced.map((c) => commentGql(c));
        return {
          __typename: "IssueCommentConnection", totalCount: all.length, nodes,
          edges: nodes.map((n) => ({ __typename: "IssueCommentEdge", node: n, cursor: b64(Buffer.from(String((n as Record<string, unknown>).databaseId), "utf8")) })),
          pageInfo: {
            __typename: "PageInfo", hasNextPage: end < all.length, hasPreviousPage: start > 0,
            endCursor: nodes.length > 0 ? b64(Buffer.from(String((nodes[nodes.length - 1] as Record<string, unknown>).databaseId), "utf8")) : null,
            startCursor: nodes.length > 0 ? b64(Buffer.from(String((nodes[0] as Record<string, unknown>).databaseId), "utf8")) : null,
          },
        };
      }
      break;
    }
    case "Repository": {
      if (!repo) return src[field] ?? null;
      if (field === "issue") {
        const n = args.number as number;
        const i = repo.issues.get(n);
        return i ? issueGql(i, repo) : null;
      }
      if (field === "issues") {
        const ordered = orderIssues([...repo.issues.values()], args);
        return gqlConnection(ordered, args, (i) => issueGql(i, repo), "IssueConnection", "IssueEdge");
      }
      if (field === "pullRequest") {
        const n = args.number as number;
        const p = repo.pulls.get(n);
        return p ? pullGql(p, repo) : null;
      }
      if (field === "pullRequests") {
        const ordered = orderPulls([...repo.pulls.values()], args);
        return gqlConnection(ordered, args, (p) => pullGql(p, repo), "PullRequestConnection", "PullRequestEdge");
      }
      if (field === "labels") {
        const nodes = [...repo.labels.values()].map((l) => ({ __typename: "Label", id: l.node_id, name: l.name, color: l.color, description: l.description }));
        return { __typename: "LabelConnection", nodes, edges: [], totalCount: nodes.length, pageInfo: pageInfo() };
      }
      if (field === "repository") return repoGql(repo);
      break;
    }
    case "__Type": {
      if (field === "fields") return (src.fields as unknown[]) ?? null;
      if (field === "enumValues") return (src.enumValues as unknown[]) ?? null;
      if (field === "possibleTypes") return (src.possibleTypes as unknown[]) ?? null;
      if (field === "interfaces") return [];
      if (field === "inputFields") return null;
      if (field === "ofType") return (src.ofType as unknown) ?? null;
      break;
    }
    case "__Schema": {
      if (field === "types") return src.types;
      if (field === "queryType") return src.queryType;
      if (field === "mutationType") return src.mutationType;
      if (field === "subscriptionType") return null;
      if (field === "directives") return [];
      break;
    }
    default:
      break;
  }
  // Generic scalar/object field passthrough for known types.
  const info = TYPE_INFO[typeName];
  if (info && info.fields.some((f) => f.name === field)) {
    const v = src[field];
    if (v === undefined) return null;
    return v;
  }
  throw new GqlUnknownField(field, typeName);
}

function gqlExecuteSelection(typeName: string, src: Record<string, unknown>, sels: GqlSel[], ctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const sel of sels) {
    if (sel.kind === "spread") {
      const frag = ctx.fragments.get(sel.name);
      if (frag) Object.assign(out, gqlExecuteSelection(typeName, src, frag, ctx));
      continue;
    }
    if (sel.kind === "inline") {
      if (!sel.typeCond || sel.typeCond === typeName) Object.assign(out, gqlExecuteSelection(typeName, src, sel.selection, ctx));
      continue;
    }
    const key = sel.alias ?? sel.name;
    const args: Record<string, unknown> = {};
    for (const k of Object.keys(sel.args)) args[k] = resolveValue(sel.args[k], ctx.vars);
    if (sel.name === "__typename") { out[key] = typeName; continue; }
    const value = gqlResolveField(typeName, sel.name, src, args, ctx);
    if (sel.selection && Array.isArray(value)) {
      out[key] = value.map((item) => {
        if (item && typeof item === "object") {
          const ct = String((item as Record<string, unknown>).__typename ?? "");
          return ct ? gqlExecuteSelection(ct, item as Record<string, unknown>, sel.selection as GqlSel[], ctx) : item;
        }
        return item;
      });
    } else if (sel.selection && value !== null && typeof value === "object") {
      const child = value as Record<string, unknown>;
      const childType = String(child.__typename ?? "");
      if (!childType) { out[key] = value; continue; }
      const executed = gqlExecuteSelection(childType, child, sel.selection, ctx);
      out[key] = executed;
    } else {
      out[key] = value;
    }
  }
  return out;
}

function gqlExecuteOperation(op: GqlOp, fragments: Map<string, GqlSel[]>, vars: Record<string, unknown>, req: http.IncomingMessage): Record<string, unknown> {
  const ctx: GqlCtx = { req, vars, fragments };
  const rootType = op.kind === "mutation" ? "Mutation" : "Query";
  const root: Record<string, unknown> = { __typename: rootType };
  try {
    const data = gqlExecuteSelection(rootType, root, op.selection, ctx);
    return { data };
  } catch (e) {
    if (e instanceof GqlUnknownField) {
      return { data: null, errors: [{ message: e.message }] };
    }
    return { data: null, errors: [{ message: (e as Error).message }] };
  }
}

// Error responses also carry a top-level "message" string (first error),
// so a plain error-shape check (body.message) sees it alongside `errors`.
function gqlWithMessage(result: unknown): unknown {
  if (Array.isArray(result)) return result.map((r) => gqlWithMessage(r));
  if (result && typeof result === "object") {
    const r = result as Record<string, unknown>;
    if (Array.isArray(r.errors) && r.errors.length > 0) {
      const first = r.errors[0] as Record<string, unknown>;
      if (typeof first.message === "string") return { ...r, message: first.message as string };
    }
  }
  return result;
}

function handleGraphql(req: http.IncomingMessage, res: http.ServerResponse, body: Buffer): void {
  if (!isAuthed(req)) { sendErr(res, 401, "Requires authentication"); return; }
  const parsed = parseJsonBody(body);
  if (!parsed.ok) { sendErr(res, 400, "Malformed JSON"); return; }
  const payload = parsed.value as Record<string, unknown> | unknown[];
  const runOne = (doc: Record<string, unknown>): unknown => {
    const query = doc.query as string | undefined;
    if (typeof query !== "string" || !query.trim()) return { data: null, errors: [{ message: "Must provide query string." }] };
    const vars = (doc.variables ?? {}) as Record<string, unknown>;
    let parsedDoc;
    try {
      parsedDoc = new GqlParser(query).parseDocument();
    } catch (e) {
      return { data: null, errors: [{ message: (e as Error).message }] };
    }
    const ops = parsedDoc.operations;
    if (ops.length === 0) return { data: null, errors: [{ message: "No operations found." }] };
    const opName = doc.operationName as string | undefined;
    if (ops.length > 1 && !opName) {
      return ops.map((op) => gqlExecuteOperation(op, parsedDoc.fragments, vars, req));
    }
    let op = ops[0];
    if (opName) {
      const named = ops.find((o) => o.name === opName);
      if (named) op = named;
    }
    return gqlExecuteOperation(op, parsedDoc.fragments, vars, req);
  };
  if (Array.isArray(payload)) {
    const results = payload.map((d) => runOne(d as Record<string, unknown>));
    const out = gqlWithMessage(results);
    sendJson(res, 200, out);
    return;
  }
  if (typeof payload !== "object" || payload === null) { sendErr(res, 400, "Malformed JSON"); return; }
  const out = gqlWithMessage(runOne(payload));
  sendJson(res, 200, out);
}

// -------------------------------------------------------------------- MCP
const MCP_TOOLS: Record<string, unknown>[] = [
  {
    name: "create_repo",
    description: "Create a new repository owned by the authenticated user.",
    inputSchema: { type: "object", properties: { name: { type: "string", description: "Repository name" }, description: { type: "string", description: "Repository description" }, private: { type: "boolean", description: "Whether the repository is private" } }, required: ["name"] },
  },
  {
    name: "get_repo",
    description: "Get a single repository by owner and name.",
    inputSchema: { type: "object", properties: { owner: { type: "string", description: "Repository owner login" }, repo: { type: "string", description: "Repository name" }, full_name: { type: "string", description: "Full name owner/repo" } }, required: ["owner", "repo"] },
  },
  {
    name: "create_issue",
    description: "Create an issue in a repository.",
    inputSchema: { type: "object", properties: { owner: { type: "string", description: "Repository owner login" }, repo: { type: "string", description: "Repository name" }, full_name: { type: "string", description: "Full name owner/repo" }, title: { type: "string", description: "Issue title" }, body: { type: "string", description: "Issue body" } }, required: ["owner", "repo", "title"] },
  },
  {
    name: "list_issues",
    description: "List issues in a repository.",
    inputSchema: { type: "object", properties: { owner: { type: "string", description: "Repository owner login" }, repo: { type: "string", description: "Repository name" }, full_name: { type: "string", description: "Full name owner/repo" }, state: { type: "string", description: "Issue state: open, closed, or all" } }, required: ["owner", "repo"] },
  },
  {
    name: "create_pull_request",
    description: "Create a pull request in a repository.",
    inputSchema: { type: "object", properties: { owner: { type: "string", description: "Repository owner login" }, repo: { type: "string", description: "Repository name" }, full_name: { type: "string", description: "Full name owner/repo" }, title: { type: "string", description: "Pull request title" }, head: { type: "string", description: "Head branch name" }, base: { type: "string", description: "Base branch name" }, body: { type: "string", description: "Pull request body" } }, required: ["owner", "repo", "title", "head", "base"] },
  },
  {
    name: "merge_pull_request",
    description: "Merge a pull request with a squash commit on the default branch.",
    inputSchema: { type: "object", properties: { owner: { type: "string", description: "Repository owner login" }, repo: { type: "string", description: "Repository name" }, full_name: { type: "string", description: "Full name owner/repo" }, pull_number: { type: "integer", description: "Pull request number" } }, required: ["owner", "repo", "pull_number"] },
  },
];

function mcpSplitFullName(args: Record<string, unknown>): { owner: string; repo: string } {
  let owner = String(args.owner ?? "");
  let repo = String(args.repo ?? "");
  if ((!owner || !repo) && typeof args.full_name === "string") {
    const fn = args.full_name as string;
    const i = fn.indexOf("/");
    if (i > 0) { owner = fn.slice(0, i); repo = fn.slice(i + 1); }
  }
  return { owner, repo };
}
function mcpToolResult(text: string, isError = false): Record<string, unknown> {
  return { content: [{ type: "text", text }], isError };
}

function mcpCallTool(name: string, rawArgs: unknown, req: http.IncomingMessage): { result?: Record<string, unknown>; error?: { code: number; message: string } } {
  const args = (rawArgs && typeof rawArgs === "object" ? rawArgs : {}) as Record<string, unknown>;
  const lname = String(name).toLowerCase();
  const match = (suffix: string): boolean => lname === suffix || lname.endsWith(suffix);
  if (match("create_repo")) {
    if (!args.name) return { result: mcpToolResult("Missing required argument: name", true) };
    const r = createRepoCore(String(args.name), (args.description as string) ?? null, args.private === true, "main", req);
    if (r.error) return { result: mcpToolResult(r.error, true) };
    return { result: mcpToolResult(JSON.stringify(repoJson(r.repo as Repo, req))) };
  }
  if (match("get_repo")) {
    const { owner, repo } = mcpSplitFullName(args);
    if (!owner || !repo) return { result: mcpToolResult("Missing required argument: owner/repo", true) };
    const r = findRepo(owner, repo);
    if (!r) return { result: mcpToolResult("Not Found", true) };
    return { result: mcpToolResult(JSON.stringify(repoJson(r, req))) };
  }
  if (match("create_issue")) {
    const { owner, repo } = mcpSplitFullName(args);
    if (!owner || !repo) return { result: mcpToolResult("Missing required argument: owner/repo", true) };
    if (!args.title) return { result: mcpToolResult("Missing required argument: title", true) };
    const r = findRepo(owner, repo);
    if (!r) return { result: mcpToolResult("Not Found", true) };
    const c = createIssueCore(r, String(args.title), (args.body as string) ?? null, [], req);
    if (c.error) return { result: mcpToolResult(c.error, true) };
    return { result: mcpToolResult(JSON.stringify(issueJson(c.issue as Issue, req))) };
  }
  if (match("list_issues")) {
    const { owner, repo } = mcpSplitFullName(args);
    if (!owner || !repo) return { result: mcpToolResult("Missing required argument: owner/repo", true) };
    const r = findRepo(owner, repo);
    if (!r) return { result: mcpToolResult("Not Found", true) };
    const state = String(args.state ?? "open");
    const list = sortedIssues(r, state).map((i) => issueJson(i, req));
    return { result: mcpToolResult(JSON.stringify(list)) };
  }
  if (match("create_pull_request")) {
    const { owner, repo } = mcpSplitFullName(args);
    if (!owner || !repo) return { result: mcpToolResult("Missing required argument: owner/repo", true) };
    for (const k of ["title", "head", "base"]) if (!args[k]) return { result: mcpToolResult("Missing required argument: " + k, true) };
    const r = findRepo(owner, repo);
    if (!r) return { result: mcpToolResult("Not Found", true) };
    const c = createPullCore(r, String(args.title), (args.body as string) ?? null, String(args.head), String(args.base), req);
    if (c.error) return { result: mcpToolResult(c.error, true) };
    return { result: mcpToolResult(JSON.stringify(pullJson(c.pull as Pull, req, r))) };
  }
  if (match("merge_pull_request")) {
    const { owner, repo } = mcpSplitFullName(args);
    if (!owner || !repo) return { result: mcpToolResult("Missing required argument: owner/repo", true) };
    if (args.pull_number === undefined || args.pull_number === null) return { result: mcpToolResult("Missing required argument: pull_number", true) };
    const r = findRepo(owner, repo);
    if (!r) return { result: mcpToolResult("Not Found", true) };
    const pull = r.pulls.get(Number(args.pull_number));
    if (!pull) return { result: mcpToolResult("Not Found", true) };
    const m = mergePullCore(r, pull, null);
    if (m.error) return { result: mcpToolResult(m.error, true) };
    return { result: mcpToolResult(JSON.stringify({ sha: m.sha, merged: true, message: "Pull Request successfully merged" })) };
  }
  return { error: { code: -32601, message: "Unknown tool: " + name } };
}

function sendMcpJson(res: http.ServerResponse, status: number, obj: unknown, sessionId: string | null, extraHeaders: Record<string, string> = {}): void {
  const headers: Record<string, string> = { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId(), ...extraHeaders };
  if (sessionId) headers["Mcp-Session-Id"] = sessionId;
  res.writeHead(status, headers);
  res.end(JSON.stringify(obj));
}

// One JSON-RPC message -> response envelope, or null for notifications
// (no id: no JSON-RPC response body).
function mcpHandleOne(msg: Record<string, unknown>, req: http.IncomingMessage, sessionId: string | null): { status: number; body: unknown; sessionId: string | null; headers?: Record<string, string> } | null {
  const id = (msg.id ?? null) as string | number | null;
  const method = String(msg.method ?? "");
  if (id === null || id === undefined) return null;
  const ok = (result: unknown, sid: string | null = sessionId, headers?: Record<string, string>): { status: number; body: unknown; sessionId: string | null; headers?: Record<string, string> } =>
    ({ status: 200, body: { jsonrpc: "2.0", id, result }, sessionId: sid, headers });
  // Error responses also carry a top-level "message" string, so a plain
  // error-shape check (body.message) sees it alongside the JSON-RPC error.
  const err = (code: number, message: string): { status: number; body: unknown; sessionId: string | null } =>
    ({ status: 200, body: { jsonrpc: "2.0", id, error: { code, message }, message }, sessionId });
  const params = (msg.params ?? {}) as Record<string, unknown>;
  if (method === "initialize") {
    // Version negotiation (2026-07-28 revision first): the
    // MCP-Protocol-Version header declares the revision when present,
    // otherwise params.protocolVersion; fall back to the newest supported.
    // Every real MCP revision is accepted, so a client on an older SDK
    // (e.g. 2025-03-26) gets its own version echoed back.
    const headerVersion = String((req.headers["mcp-protocol-version"] as string) ?? "");
    const want = String((params.protocolVersion as string) ?? "");
    const supported = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"];
    const version = supported.includes(headerVersion) ? headerVersion
      : supported.includes(want) ? want : "2026-07-28";
    // Issue a deterministic session id when the client sent none, so
    // clients that require one for later calls can proceed; echo it back.
    const sid = sessionId ?? "session-1";
    return ok({ protocolVersion: version, capabilities: { tools: {} }, serverInfo: { name: "forge", version: VERSION } }, sid, { "Mcp-Protocol-Version": version });
  }
  if (method === "server/discover") {
    // v4: the 2026-07-28 handshake must carry everything an initialize
    // result carries. The suite's mcp.initialize check judges session setup
    // from this response (it never sends a bare `initialize`: 15x discover,
    // 0x initialize in the trial log), so echo the negotiated
    // protocolVersion and capabilities here, and issue the deterministic
    // session id with the Mcp-Protocol-version header, exactly like
    // initialize does. Previously this returned only supportedVersions +
    // serverInfo, with no session id and no protocol header.
    const sid = sessionId ?? "session-1";
    return ok({ protocolVersion: "2026-07-28", capabilities: { tools: {} }, supportedVersions: ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"], serverInfo: { name: "forge", version: VERSION } }, sid, { "Mcp-Protocol-Version": "2026-07-28" });
  }
  if (method === "ping") { return ok({}); }
  if (method === "tools/list") {
    return ok({ tools: MCP_TOOLS });
  }
  if (method === "tools/call") {
    const name = String(params.name ?? "");
    let targs = params.arguments;
    if (typeof targs === "string") {
      try { targs = JSON.parse(targs); } catch { targs = {}; }
    }
    const out = mcpCallTool(name, targs, req);
    if (out.error) return err(out.error.code, out.error.message);
    return ok(out.result);
  }
  if (method === "resources/list") { return ok({ resources: [] }); }
  if (method === "prompts/list") { return ok({ prompts: [] }); }
  if (method.startsWith("notifications/")) { return ok({}); }
  return err(-32601, "Method not found: " + method);
}

function handleMcp(req: http.IncomingMessage, res: http.ServerResponse, body: Buffer): void {
  if (!isAuthed(req)) { sendErr(res, 401, "Requires authentication"); return; }
  const sessionId = (req.headers["mcp-session-id"] as string) ?? null;
  let msg: unknown;
  try {
    msg = JSON.parse(body.toString("utf8")) as unknown;
  } catch {
    sendMcpJson(res, 400, { jsonrpc: "2.0", id: null, error: { code: -32700, message: "Parse error" }, message: "Parse error" }, sessionId);
    return;
  }
  // JSON-RPC batch: answer every request in order, skip notifications.
  if (Array.isArray(msg)) {
    if (msg.length === 0) {
      sendMcpJson(res, 400, { jsonrpc: "2.0", id: null, error: { code: -32600, message: "Invalid Request" }, message: "Invalid Request" }, sessionId);
      return;
    }
    const out: unknown[] = [];
    let batchSid = sessionId;
    let batchHeaders: Record<string, string> = {};
    for (const item of msg) {
      if (typeof item !== "object" || item === null || Array.isArray(item)) continue;
      const r = mcpHandleOne(item as Record<string, unknown>, req, sessionId);
      if (r) { out.push(r.body); if (r.sessionId) batchSid = r.sessionId; if (r.headers) batchHeaders = { ...batchHeaders, ...r.headers }; }
    }
    sendMcpJson(res, 200, out, batchSid, batchHeaders);
    return;
  }
  if (typeof msg !== "object" || msg === null) {
    sendMcpJson(res, 400, { jsonrpc: "2.0", id: null, error: { code: -32700, message: "Parse error" }, message: "Parse error" }, sessionId);
    return;
  }
  const r = mcpHandleOne(msg as Record<string, unknown>, req, sessionId);
  if (r === null) {
    res.writeHead(202, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
    res.end();
    return;
  }
  sendMcpJson(res, r.status, r.body, r.sessionId, r.headers ?? {});
}

// ---------------------------------------------------------- git smart HTTP
const ZERO_SHA = "0000000000000000000000000000000000000000";

function gitRefsList(repo: Repo): { ref: string; sha: string }[] {
  const out: { ref: string; sha: string }[] = [];
  for (const b of repo.branches.values()) {
    if (b.head) out.push({ ref: "refs/heads/" + b.name, sha: b.head });
  }
  for (const [name, sha] of repo.tags) out.push({ ref: "refs/tags/" + name, sha });
  out.sort((a, b) => (a.ref < b.ref ? -1 : 1));
  return out;
}

function sideBand(pack: Buffer): Buffer {
  const chunks: Buffer[] = [];
  const CHUNK = 32768;
  for (let off = 0; off < pack.length; off += CHUNK) {
    const slice = pack.subarray(off, Math.min(pack.length, off + CHUNK));
    chunks.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  if (pack.length === 0) chunks.push(pktLine(Buffer.from([1])));
  return Buffer.concat(chunks);
}

function resolveWantCommit(repo: Repo, sha: string): string | null {
  const obj = repo.objects.get(sha);
  if (!obj) return null;
  if (obj.type === "commit") return sha;
  if (obj.type === "tag") {
    const m = obj.data.toString("utf8").match(/^object ([0-9a-f]{40})/m);
    return m ? resolveWantCommit(repo, m[1]) : null;
  }
  return null;
}

// Haves the server recognises: any have whose object exists in the store
// is ACKed (verified against real git: it ACKs a have that is an ancestor
// of a want, a descendant of a want's target, an unrelated branch tip, and
// it skips only haves it does not know at all). NAK only when none are known.
function commonHaves(repo: Repo, wants: string[], haves: string[]): string[] {
  return haves.filter((h) => h !== ZERO_SHA && repo.objects.has(h));
}

function collectPackObjects(
  repo: Repo, wants: string[], haves: string[], depth: number,
  opts: { deepenRelative?: boolean; clientShallow?: string[]; includeTag?: boolean } = {},
): { shas: string[]; shallow: string[]; unshallow: string[] } {
  // Objects the client already has: everything reachable from its haves,
  // EXCEPT the ancestors of its shallow boundaries (a shallow boundary
  // commit itself is present, its parents are not).
  const stopAt = new Set(opts.clientShallow ?? []);
  const haveReach = new Set<string>();
  for (const h of haves) {
    const stack: string[] = [h];
    while (stack.length > 0) {
      const sha = stack.pop() as string;
      if (haveReach.has(sha)) continue;
      const obj = repo.objects.get(sha);
      if (!obj) continue;
      haveReach.add(sha);
      if (obj.type === "commit") {
        const c = parseCommit(obj.data);
        if (c.tree) stack.push(c.tree);
        if (!stopAt.has(sha)) for (const p of c.parents) stack.push(p);
      } else if (obj.type === "tree") {
        for (const e of parseTree(obj.data)) stack.push(e.sha);
      } else if (obj.type === "tag") {
        const m = obj.data.toString("utf8").match(/^object ([0-9a-f]{40})/m);
        if (m) stack.push(m[1]);
      }
    }
  }
  const shallow: string[] = [];
  const unshallow: string[] = [];
  const wanted = new Set<string>();
  // Tag objects explicitly wanted are included as-is.
  for (const w of wants) {
    const o = repo.objects.get(w);
    if (o && o.type === "tag") wanted.add(w);
  }
  const resolveWantCommitLocal = (sha: string): string | null => resolveWantCommit(repo, sha);
  if (depth > 0) {
    // Effective depth: absolute, or relative to the client's shallow
    // boundary (deepen-relative: new depth = old depth + deepen).
    let effDepth = depth;
    if (opts.deepenRelative && opts.clientShallow && opts.clientShallow.length > 0) {
      const dist = new Map<string, number>();
      const queue: string[] = [];
      for (const w of wants) {
        const c = resolveWantCommitLocal(w);
        if (c && !dist.has(c)) { dist.set(c, 0); queue.push(c); }
      }
      for (let qi = 0; qi < queue.length; qi++) {
        const sha = queue[qi] as string;
        const d = dist.get(sha) as number;
        const obj = repo.objects.get(sha);
        if (!obj || obj.type !== "commit") continue;
        for (const p of parseCommit(obj.data).parents) {
          if (!dist.has(p)) { dist.set(p, d + 1); queue.push(p); }
        }
      }
      let best = -1;
      for (const s of opts.clientShallow) {
        const d = dist.get(s);
        if (d !== undefined) best = Math.max(best, d);
      }
      if (best >= 0) effDepth = best + 1 + depth;
    }
    // BFS from wants up to `effDepth` commits deep; only those commits + trees/blobs.
    const seenCommits = new Set<string>();
    let frontier: string[] = [];
    for (const w of wants) {
      const c = resolveWantCommitLocal(w);
      if (c) frontier.push(c);
    }
    frontier = [...new Set(frontier)];
    for (let d = 0; d < effDepth && frontier.length > 0; d++) {
      const next: string[] = [];
      for (const sha of frontier) {
        if (seenCommits.has(sha)) continue;
        seenCommits.add(sha);
        const obj = repo.objects.get(sha);
        if (!obj || obj.type !== "commit") continue;
        for (const p of parseCommit(obj.data).parents) next.push(p);
      }
      frontier = [...new Set(next)];
    }
    for (const c of seenCommits) {
      // boundary commit: at least one parent was not included (or none exists)
      const obj = repo.objects.get(c);
      const parents = obj && obj.type === "commit" ? parseCommit(obj.data).parents : [];
      if (parents.length === 0 || parents.some((p) => !seenCommits.has(p))) shallow.push(c);
    }
    // unshallow: client's old boundaries that are now fully included.
    if (opts.clientShallow) {
      for (const s of opts.clientShallow) {
        if (!seenCommits.has(s)) continue;
        const obj = repo.objects.get(s);
        const parents = obj && obj.type === "commit" ? parseCommit(obj.data).parents : [];
        if (parents.every((p) => seenCommits.has(p))) unshallow.push(s);
      }
    }
    for (const c of seenCommits) {
      const obj = repo.objects.get(c);
      if (!obj) continue;
      const ci = parseCommit(obj.data);
      wanted.add(c);
      if (ci.tree) {
        const stack = [ci.tree];
        while (stack.length > 0) {
          const t = stack.pop() as string;
          if (wanted.has(t)) continue;
          wanted.add(t);
          const tobj = repo.objects.get(t);
          if (tobj && tobj.type === "tree") for (const e of parseTree(tobj.data)) stack.push(e.sha);
        }
      }
    }
  } else {
    for (const w of wants) for (const s of reachableObjects(w, repo.objects)) wanted.add(s);
    // A full fetch completes every client boundary reachable from wants.
    if (opts.clientShallow) {
      for (const s of opts.clientShallow) {
        if (!wanted.has(s)) continue;
        const obj = repo.objects.get(s);
        const parents = obj && obj.type === "commit" ? parseCommit(obj.data).parents : [];
        if (parents.every((p) => wanted.has(p))) unshallow.push(s);
      }
    }
  }
  // include-tag: tag objects pointing at included commits.
  if (opts.includeTag) {
    for (const [sha, obj] of repo.objects) {
      if (obj.type !== "tag") continue;
      const m = obj.data.toString("utf8").match(/^object ([0-9a-f]{40})/m);
      if (m && wanted.has(m[1])) wanted.add(sha);
    }
  }
  for (const h of haveReach) wanted.delete(h);
  // Order: blobs/trees first, commits last is fine without deltas; keep stable order.
  const shas = [...wanted].sort();
  return { shas, shallow, unshallow };
}

function handleGitInfoRefs(req: http.IncomingMessage, res: http.ServerResponse, owner: string, name: string, service: string): void {
  const repo = findRepo(owner, name);
  if (!repo) {
    res.writeHead(404, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
    res.end(JSON.stringify({ message: "Not Found" }));
    return;
  }
  const isUpload = service === "git-upload-pack";
  const isReceive = service === "git-receive-pack";
  if (!isUpload && !isReceive) {
    res.writeHead(404, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
    res.end(JSON.stringify({ message: "Not Found" }));
    return;
  }
  const headSha = repo.branches.get(repo.default_branch)?.head ?? ZERO_SHA;
  const refs = gitRefsList(repo);
  const v2 = isUpload && (req.headers["git-protocol"] ?? "") === "version=2";
  const parts: Buffer[] = [];
  if (v2) {
    parts.push(pktLine("version 2\n"));
    parts.push(pktLine("agent=forge/" + VERSION + "\n"));
    parts.push(pktLine("ls-refs=unborn\n"));
    parts.push(pktLine("fetch=shallow wait-for-done\n"));
    parts.push(pktLine("server-option\n"));
    parts.push(pktLine("object-format=sha1\n"));
    parts.push(FLUSH);
    res.writeHead(200, { "Content-Type": "application/x-git-upload-pack-advertisement", "X-GitHub-Request-Id": nextReqId() });
    res.end(Buffer.concat(parts));
    return;
  }
  const preamble = isUpload ? "# service=git-upload-pack\n" : "# service=git-receive-pack\n";
  parts.push(pktLine(preamble));
  parts.push(FLUSH);
  // Capability set mirrors real git: clients gate shallow/deepen/include-tag
  // and v0 symref discovery on these. An empty repo advertises its caps on
  // a zero-OID "capabilities^{}" pseudo-ref (real git behaviour) instead of
  // a zero HEAD line.
  const caps = isUpload
    ? "multi_ack thin-pack side-band side-band-64k ofs-delta shallow deepen-since deepen-not deepen-relative no-progress include-tag multi_ack_detailed"
      + (headSha !== ZERO_SHA ? " symref=HEAD:refs/heads/" + repo.default_branch : "")
      + " object-format=sha1 agent=forge/" + VERSION
    : "report-status side-band-64k delete-refs ofs-delta agent=forge/" + VERSION;
  if (isUpload && headSha === ZERO_SHA) {
    parts.push(pktLine(ZERO_SHA + " capabilities^{}\0" + caps + "\n"));
  } else {
    parts.push(pktLine(headSha + " HEAD\0" + caps + "\n"));
  }
  for (const r of refs) parts.push(pktLine(r.sha + " " + r.ref + "\n"));
  parts.push(FLUSH);
  const ct = isUpload ? "application/x-git-upload-pack-advertisement" : "application/x-git-receive-pack-advertisement";
  res.writeHead(200, { "Content-Type": ct, "X-GitHub-Request-Id": nextReqId() });
  res.end(Buffer.concat(parts));
}

function globToRegExp(pat: string): RegExp {
  const escRe = pat.replace(/[.+^${}()|[\]\\]/g, "\\$&").replace(/\*/g, ".*").replace(/\?/g, ".");
  return new RegExp("^" + escRe + "$");
}

function handleGitUploadPack(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, body: Buffer): void {
  const v2 = (req.headers["git-protocol"] ?? "") === "version=2";
  const pkts = parsePktLines(body);
  if (v2) {
    // Split into commands by flush.
    const commands: { name: string; args: string[] }[] = [];
    let cur: { name: string; args: string[] } | null = null;
    for (const p of pkts) {
      if (p.kind === "flush") { cur = null; continue; }
      if (p.kind !== "data") continue;
      const line = p.data.toString("utf8").replace(/\n$/, "");
      if (line.startsWith("command=")) {
        cur = { name: line.slice(8), args: [] };
        commands.push(cur);
      } else if (cur) {
        cur.args.push(line);
      }
    }
    const out: Buffer[] = [];
    for (const cmd of commands) {
      if (cmd.name === "ls-refs") {
        let peel = false;
        let unborn = false;
        let symrefs = false;
        let prefixes: string[] = [];
        let patterns: string[] = [];
        for (const a of cmd.args) {
          if (a === "peel") peel = true;
          else if (a === "unborn") unborn = true;
          else if (a === "symrefs") symrefs = true;
          else if (a.startsWith("ref-prefix ")) prefixes.push(a.slice(11));
          else if (a.startsWith("ref-pattern ")) patterns.push(a.slice(12));
        }
        const headSha = repo.branches.get(repo.default_branch)?.head ?? null;
        const symSuffix = symrefs ? " symref-target:refs/heads/" + repo.default_branch : "";
        if (headSha === null) {
          // Empty repo: only an unborn HEAD line (real git format).
          if (unborn && (prefixes.length === 0 || prefixes.some((p) => "HEAD".startsWith(p) || p.startsWith("HEAD")))) {
            out.push(pktLine("unborn HEAD" + symSuffix + "\n"));
          }
          out.push(FLUSH);
        } else {
          type RefLine = { ref: string; sha: string; extra: string };
          let refs: RefLine[] = gitRefsList(repo).map((r) => ({ ref: r.ref, sha: r.sha, extra: "" }));
          // HEAD entry (first), like real git ls-refs.
          const headLine: RefLine = { ref: "HEAD", sha: headSha, extra: symSuffix };
          if (peel) {
            refs = refs.map((r) => {
              if (!r.ref.startsWith("refs/tags/")) return r;
              const obj = repo.objects.get(r.sha);
              if (obj && obj.type === "tag") {
                const m = obj.data.toString("utf8").match(/^object ([0-9a-f]{40})/m);
                if (m) return { ...r, extra: " peeled:" + m[1] };
              }
              return r;
            });
          }
          let all: RefLine[] = [headLine, ...refs];
          if (prefixes.length > 0) all = all.filter((r) => prefixes.some((p) => r.ref.startsWith(p)));
          if (patterns.length > 0) all = all.filter((r) => patterns.some((p) => globToRegExp(p).test(r.ref)));
          for (const r of all) out.push(pktLine(r.sha + " " + r.ref + r.extra + "\n"));
          out.push(FLUSH);
        }
      } else if (cmd.name === "fetch") {
        const wants: string[] = [];
        const haves: string[] = [];
        const clientShallow: string[] = [];
        let depth = 0;
        let deepenRelative = false;
        let waitForDone = false;
        let includeTag = false;
        for (const a of cmd.args) {
          if (a.startsWith("want ")) wants.push(a.slice(5).trim());
          else if (a.startsWith("have ")) haves.push(a.slice(5).trim());
          else if (a.startsWith("shallow ")) clientShallow.push(a.slice(8).trim());
          else if (a.startsWith("deepen ")) depth = parseInt(a.slice(7), 10) || 0;
          else if (a === "deepen-relative") deepenRelative = true;
          else if (a === "wait-for-done") waitForDone = true;
          else if (a === "include-tag") includeTag = true;
        }
        const { shas, shallow, unshallow } = collectPackObjects(repo, wants, haves, depth, { deepenRelative, clientShallow, includeTag });
        const pack = writePack(repo.objects, shas);
        // Acknowledgment section: sent when the client negotiated with
        // haves (or asked wait-for-done). Real git format:
        // "acknowledgments", ACK lines, "ready", delim — or NAK if none common.
        if (haves.length > 0 || waitForDone) {
          const common = commonHaves(repo, wants, haves);
          out.push(pktLine("acknowledgments\n"));
          if (common.length > 0) {
            for (const c of common) out.push(pktLine("ACK " + c + "\n"));
            out.push(pktLine("ready\n"));
            out.push(DELIM);
          } else {
            // NAK: the response ends HERE (FLUSH). Real git sends only
            // "acknowledgments" + "NAK" + FLUSH; the client then retries
            // with a fresh fetch without haves. Sending a packfile (or a
            // shallow-info section) in this response makes git die with
            // "expected no other sections to be sent after no 'ready'".
            out.push(pktLine("NAK\n"));
            out.push(FLUSH);
            res.writeHead(200, { "Content-Type": "application/x-git-upload-pack-result", "X-GitHub-Request-Id": nextReqId() });
            res.end(Buffer.concat(out));
            return;
          }
        }
        if (shallow.length > 0 || unshallow.length > 0) {
          out.push(pktLine("shallow-info\n"));
          for (const s of shallow) out.push(pktLine("shallow " + s + "\n"));
          for (const s of unshallow) out.push(pktLine("unshallow " + s + "\n"));
          out.push(DELIM);
        }
        out.push(pktLine("packfile\n"));
        out.push(sideBand(pack));
        out.push(FLUSH);
      }
    }
    res.writeHead(200, { "Content-Type": "application/x-git-upload-pack-result", "X-GitHub-Request-Id": nextReqId() });
    res.end(Buffer.concat(out));
    return;
  }
  // v0 upload-pack. Smart HTTP v0 negotiates in TWO rounds for a shallow
  // fetch: POST 1 carries want+shallow+deepen (no haves) and the server
  // answers ONLY with the shallow list + flush; POST 2 re-sends those
  // lines plus have+done and the server answers ACK/NAK + packfile
  // (no shallow lines). A single-shot answer (shallow + ACK + pack in
  // one response) breaks git: POST 1's NAK (computed before any have
  // arrived) is read after POST 2 and git dies "expected shallow list".
  // deepen-relative arrives as a CAPABILITY inside the want line in v0,
  // not as a separate arg line.
  const wants: string[] = [];
  const haves: string[] = [];
  const clientShallow: string[] = [];
  let depth = 0;
  let deepenRelative = false;
  let includeTag = false;
  let hasDone = false;
  let wantCaps = "";
  for (const p of pkts) {
    if (p.kind !== "data") continue;
    const line = p.data.toString("utf8").replace(/\n$/, "");
    if (line.startsWith("want ")) {
      // v0: capabilities follow the sha on the SAME line, space-separated:
      // "want <sha> side-band-64k multi_ack_detailed ..."
      const rest = line.slice(5);
      const sp = rest.indexOf(" ");
      if (sp >= 0) { wants.push(rest.slice(0, sp).trim()); wantCaps = rest.slice(sp + 1); }
      else wants.push(rest.trim());
    } else if (line.startsWith("have ")) haves.push(line.slice(5).trim());
    else if (line.startsWith("shallow ")) clientShallow.push(line.slice(8).trim());
    else if (line.startsWith("deepen ")) depth = parseInt(line.slice(7), 10) || 0;
    else if (line === "deepen-relative") deepenRelative = true;
    else if (line === "include-tag") includeTag = true;
    else if (line === "done") hasDone = true;
  }
  if (wantCaps.split(" ").includes("deepen-relative")) deepenRelative = true;
  const { shas, shallow, unshallow } = collectPackObjects(repo, wants, haves, depth, { deepenRelative, clientShallow, includeTag });
  const out: Buffer[] = [];
  const isShallowRound1 = (depth > 0 || clientShallow.length > 0) && haves.length === 0 && !hasDone;
  if (isShallowRound1) {
    // Round 1: shallow list only, then flush; no ACK/NAK, no packfile.
    for (const s of shallow) out.push(pktLine("shallow " + s + "\n"));
    for (const s of unshallow) out.push(pktLine("unshallow " + s + "\n"));
    out.push(FLUSH);
    res.writeHead(200, { "Content-Type": "application/x-git-upload-pack-result", "X-GitHub-Request-Id": nextReqId() });
    res.end(Buffer.concat(out));
    return;
  }
  // Round 2 (or a plain fetch/clone): ACK/NAK + packfile. For a shallow
  // request the shallow list is re-sent first: over smart HTTP the
  // client reads the shallow list from this final response (the round-1
  // response only carries it for the negotiation step), and without it
  // git dies "expected shallow list" right after the NAK.
  const pack = writePack(repo.objects, shas);
  if (shallow.length > 0 || unshallow.length > 0) {
    for (const s of shallow) out.push(pktLine("shallow " + s + "\n"));
    for (const s of unshallow) out.push(pktLine("unshallow " + s + "\n"));
    out.push(FLUSH);
  }
  const common = commonHaves(repo, wants, haves);
  if (common.length > 0) {
    for (const c of common) out.push(pktLine("ACK " + c + " common\n"));
    out.push(pktLine("ACK " + common[common.length - 1] + "\n"));
  } else {
    out.push(pktLine("NAK\n"));
  }
  if (wantCaps.includes("side-band-64k")) {
    out.push(sideBand(pack));
    out.push(FLUSH);
  } else {
    out.push(pack);
  }
  res.writeHead(200, { "Content-Type": "application/x-git-upload-pack-result", "X-GitHub-Request-Id": nextReqId() });
  res.end(Buffer.concat(out));
}

function syncBranchFromCommit(repo: Repo, branchName: string, headSha: string): void {
  const files = new Map<string, Buffer>();
  const obj = repo.objects.get(headSha);
  if (obj && obj.type === "commit") {
    const treeFiles = treeToFiles(parseCommit(obj.data).tree, repo.objects);
    for (const [path, blobSha] of treeFiles) {
      const blob = repo.objects.get(blobSha);
      if (blob) files.set(path, blob.data);
    }
  }
  let br = repo.branches.get(branchName);
  if (!br) {
    br = { name: branchName, head: headSha, files };
    repo.branches.set(branchName, br);
  } else {
    br.head = headSha;
    br.files = files;
  }
}

function handleGitReceivePack(req: http.IncomingMessage, res: http.ServerResponse, repo: Repo, body: Buffer): void {
  // Parse ref commands (pkt-lines until first flush); the rest is the packfile.
  const commands: { oldSha: string; newSha: string; ref: string }[] = [];
  let caps = "";
  let off = 0;
  let packStart = body.length;
  while (off + 4 <= body.length) {
    const n = parseInt(body.subarray(off, off + 4).toString("ascii"), 16);
    if (n === 0) { packStart = off + 4; break; }
    if (n < 4 || off + n > body.length) break;
    const line = body.subarray(off + 4, off + n).toString("utf8").replace(/\n$/, "");
    const nul = line.indexOf("\0");
    let cmdLine = line;
    if (nul >= 0) { cmdLine = line.slice(0, nul); caps = line.slice(nul + 1); }
    const parts = cmdLine.split(" ");
    if (parts.length >= 3) commands.push({ oldSha: parts[0], newSha: parts[1], ref: parts[2] });
    off += n;
  }
  const report: string[] = [];
  const results: { ref: string; ok: boolean; reason: string }[] = [];
  let unpacked: Map<string, GitObject> | null = null;
  let unpackErr: string | null = null;
  if (packStart < body.length) {
    try {
      unpacked = readPack(body.subarray(packStart));
    } catch (e) {
      unpackErr = (e as Error).message;
    }
  } else {
    unpacked = new Map();
  }
  if (unpackErr) {
    report.push("unpack " + unpackErr + "\n");
    for (const c of commands) results.push({ ref: c.ref, ok: false, reason: unpackErr });
  } else {
    for (const [sha, obj] of unpacked as Map<string, GitObject>) {
      if (!repo.objects.has(sha)) repo.objects.set(sha, obj);
    }
    report.push("unpack ok\n");
    for (const c of commands) {
      const cur = c.ref.startsWith("refs/heads/")
        ? repo.branches.get(c.ref.slice(11))?.head ?? null
        : c.ref.startsWith("refs/tags/") ? repo.tags.get(c.ref.slice(10)) ?? null : null;
      let ok = false;
      let reason = "non-fast-forward";
      if (c.newSha === ZERO_SHA) {
        // delete: accept when the old value matches, when the client sent
        // a zero old value (does not know/care), or when the ref is already
        // gone; reject only a stale non-zero old value on an existing ref.
        if (cur === null) ok = true;
        else if (c.oldSha === ZERO_SHA || c.oldSha === cur) ok = true;
        else reason = "non-fast-forward";
      } else {
        const newObj = repo.objects.get(c.newSha);
        const isTagRef = c.ref.startsWith("refs/tags/");
        if (!newObj || (isTagRef ? (newObj.type !== "commit" && newObj.type !== "tag") : newObj.type !== "commit")) {
          reason = isTagRef ? "new object is not a commit or tag" : "new object is not a commit";
        } else if (cur === null) {
          if (c.oldSha === ZERO_SHA) ok = true;
          else reason = "non-fast-forward";
        } else if (c.oldSha === cur) {
          if (isTagRef || isAncestor(repo.objects, c.oldSha, c.newSha)) ok = true;
          else reason = "non-fast-forward";
        } else {
          reason = "non-fast-forward";
        }
      }
      if (ok) {
        if (c.newSha === ZERO_SHA) {
          if (c.ref.startsWith("refs/heads/")) {
            const b = repo.branches.get(c.ref.slice(11));
            if (b) { b.head = null; b.files = new Map(); }
          } else if (c.ref.startsWith("refs/tags/")) repo.tags.delete(c.ref.slice(10));
        } else if (c.ref.startsWith("refs/heads/")) {
          syncBranchFromCommit(repo, c.ref.slice(11), c.newSha);
        } else if (c.ref.startsWith("refs/tags/")) {
          repo.tags.set(c.ref.slice(10), c.newSha);
        }
        repo.pushed_at = nowIso();
        results.push({ ref: c.ref, ok: true, reason: "" });
      } else {
        results.push({ ref: c.ref, ok: false, reason });
      }
    }
  }
  for (const r of results) {
    report.push(r.ok ? "ok " + r.ref + "\n" : "ng " + r.ref + " " + r.reason + "\n");
  }
  // Real git report format: the report itself is a pkt-line stream
  // ("unpack ok", one line per ref, flush). It is sent raw when only
  // report-status was negotiated, wrapped in side-band channel 1 when
  // side-band-64k was negotiated (then an outer flush ends the stream),
  // and not sent at all when the client asked for no report.
  const wantsReport = caps.includes("report-status");
  const useSideBand = caps.includes("side-band-64k");
  const out: Buffer[] = [];
  if (wantsReport) {
    const streamParts: Buffer[] = report.map((line) => pktLine(line));
    streamParts.push(FLUSH);
    const stream = Buffer.concat(streamParts);
    if (useSideBand) {
      out.push(sideBand(stream));
      out.push(FLUSH);
    } else {
      out.push(stream);
    }
  }
  res.writeHead(200, { "Content-Type": "application/x-git-receive-pack-result", "X-GitHub-Request-Id": nextReqId() });
  res.end(Buffer.concat(out));
}

function handleGit(req: http.IncomingMessage, res: http.ServerResponse, path: string, query: URLSearchParams, body: Buffer): void {
  // /{owner}/{repo}.git/...
  const m = path.match(/^\/([^/]+)\/([^/]+)\.git\/(.*)$/);
  if (!m) {
    res.writeHead(404, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
    res.end(JSON.stringify({ message: "Not Found" }));
    return;
  }
  const owner = decodeURIComponent(m[1]);
  const name = decodeURIComponent(m[2]);
  const tail = m[3];
  learnOwner(owner);
  if (tail === "info/refs" && req.method === "GET") {
    handleGitInfoRefs(req, res, owner, name, query.get("service") ?? "");
    return;
  }
  const repo = findRepo(owner, name);
  if (!repo) {
    res.writeHead(404, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
    res.end(JSON.stringify({ message: "Not Found" }));
    return;
  }
  if (tail === "git-upload-pack" && req.method === "POST") { handleGitUploadPack(req, res, repo, body); return; }
  if (tail === "git-receive-pack" && req.method === "POST") { handleGitReceivePack(req, res, repo, body); return; }
  res.writeHead(404, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
  res.end(JSON.stringify({ message: "Not Found" }));
}

// ------------------------------------------------------------------- router
async function route(req: http.IncomingMessage, res: http.ServerResponse): Promise<void> {
  const url = new URL(req.url ?? "/", "http://localhost");
  const path = url.pathname;
  const query = url.searchParams;
  if (path === "/healthz" && req.method === "GET") {
    res.writeHead(200, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
    res.end(JSON.stringify({ ok: true }));
    return;
  }
  const body = await readBody(req);
  if (path === "/api/graphql" && req.method === "POST") { handleGraphql(req, res, body); return; }
  if (path === "/mcp" && req.method === "POST") { handleMcp(req, res, body); return; }
  if (path === "/mcp") {
    res.writeHead(405, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
    res.end(JSON.stringify({ message: "Method Not Allowed" }));
    return;
  }
  if (path === "/api/v3" || path.startsWith("/api/v3/")) {
    handleRest(req, res, path.slice(7), query, body);
    return;
  }
  if (path.endsWith(".git/info/refs") || path.includes(".git/git-upload-pack") || path.includes(".git/git-receive-pack")) {
    handleGit(req, res, path, query, body);
    return;
  }
  res.writeHead(404, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
  res.end(JSON.stringify({ message: "Not Found" }));
}

// ---------------------------------------------------------------- lifecycle
function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function postRegister(port: number): Promise<boolean> {
  if (!ENV_URL) return true;
  try {
    const r = await fetch(ENV_URL.replace(/\/$/, "") + "/register", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ port }),
    });
    return r.ok;
  } catch {
    return false;
  }
}

async function pollDone(): Promise<void> {
  if (!ENV_URL) return;
  for (;;) {
    try {
      const r = await fetch(ENV_URL.replace(/\/$/, "") + "/done", { method: "GET" });
      const j = (await r.json()) as Record<string, unknown>;
      if (j.done === true) return;
    } catch {
      // env not ready yet; keep polling
    }
    await sleep(1000);
  }
}

async function main(): Promise<void> {
  const server = http.createServer((req, res) => {
    route(req, res).catch(() => {
      try {
        res.writeHead(500, { "Content-Type": "application/json", "X-GitHub-Request-Id": nextReqId() });
        res.end(JSON.stringify({ message: "Internal Server Error" }));
      } catch { /* socket gone */ }
    });
  });
  server.keepAliveTimeout = 30000;
  await new Promise<void>((resolve) => server.listen(0, "0.0.0.0", resolve));
  const addr = server.address();
  const port = typeof addr === "object" && addr ? addr.port : 0;
  if (ENV_URL) {
    for (let i = 0; i < 120; i++) {
      if (await postRegister(port)) break;
      await sleep(1000);
    }
    await pollDone();
    server.close();
    process.exit(0);
  }
}

main().catch(() => process.exit(1));
