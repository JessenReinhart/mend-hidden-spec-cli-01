	import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join, relative, sep } from 'node:path';
import { runTrial } from './runner.ts';

const FORMATS = new Set(['auto', 'unified', 'search-replace', 'v4a', 'json']);

function out(line: string): void {
	process.stdout.write(line + '\n');
}

function usage(): never {
	out('error: usage');
	process.exit(2);
}

function fatal(line: string): never {
	out(line);
	process.exit(2);
}

interface ParsedArgs {
	format: 'auto' | 'unified' | 'search-replace' | 'v4a' | 'json';
	check: boolean;
	strict: boolean;
	patch: string | null;
}

function parseArgs(argv: string[]): ParsedArgs {
	let format: ParsedArgs['format'] | null = null;
	let check = false;
	let strict = false;
	let patch: string | null = null;
	let optsDone = false;
	for (let i = 0; i < argv.length; i++) {
		const a = argv[i];
		if (!optsDone && a === '--') {
			optsDone = true;
			continue;
		}
		if (!optsDone && a.startsWith('-') && a !== '-') {
			if (a === '--check') {
				if (check) usage();
				check = true;
				continue;
			}
			if (a === '--strict') {
				if (strict) usage();
				strict = true;
				continue;
			}
			if (a.startsWith('--format=')) {
				if (format !== null) usage();
				const v = a.slice('--format='.length);
				if (!FORMATS.has(v)) usage();
				format = v as ParsedArgs['format'];
				continue;
			}
			usage();
		}
		if (patch !== null) usage();
		patch = a;
	}
	return { format: format ?? 'auto', check, strict, patch };
}

function readPatch(patch: string | null): string {
	if (patch === null || patch === '-') {
		try {
			return readFileSync(0, 'utf8');
		} catch {
			fatal('error: no-patch');
		}
	}
	try {
		return readFileSync(patch, 'utf8');
	} catch {
		fatal('error: no-patch');
	}
}

// ---------------------------------------------------------------------------
// Tree model
// ---------------------------------------------------------------------------

/** Read every regular file under dir into a path -> text map (paths use '/'). */
function readTree(dir: string): Map<string, string> {
	const m = new Map<string, string>();
	const walk = (d: string): void => {
		for (const name of readdirSync(d)) {
			const p = join(d, name);
			const st = statSync(p);
			if (st.isDirectory()) walk(p);
			else if (st.isFile()) m.set(relative(dir, p).split(sep).join('/'), readFileSync(p, 'utf8'));
		}
	};
	walk(dir);
	return m;
}

class EditFail {
	code: string;
	path: string;
	constructor(code: string, path: string) {
		this.code = code;
		this.path = path;
	}
}

/** Parse-level failure: 1-based patch line. */
class ParseFail {
	line: number;
	constructor(line: number) {
		this.line = line;
	}
}

type Edit = (ap: Applier) => void;

interface Move {
	old: string;
	neww: string;
}

class Applier {
	orig: Map<string, string>;
	/** path -> string (new content) | null (deleted); absent = unchanged from orig. */
	state = new Map<string, string | null>();
	moves: Move[] = [];

	constructor(orig: Map<string, string>) {
		this.orig = orig;
	}

	get(path: string): string | undefined {
		if (this.state.has(path)) {
			const v = this.state.get(path);
			return v === null || v === undefined ? undefined : v;
		}
		return this.orig.get(path);
	}

	exists(path: string): boolean {
		return this.get(path) !== undefined;
	}

	set(path: string, content: string): void {
		this.state.set(path, content);
	}

	del(path: string): void {
		this.state.set(path, null);
	}

	recordMove(oldp: string, newp: string): void {
		this.moves.push({ old: oldp, new: newp });
	}
}

// ---------------------------------------------------------------------------
// Path safety (section 3)
// ---------------------------------------------------------------------------

function isSafe(p: string): boolean {
	if (p === '' || p.startsWith('/')) return false;
	if (p.includes('\\')) return false;
	for (const seg of p.split('/')) {
		if (seg === '' || seg === '.' || seg === '..') return false;
	}
	return true;
}

// ---------------------------------------------------------------------------
// Line model (section 3)
// ---------------------------------------------------------------------------

interface Lines {
	lines: string[];
	eol: string;
	endsBreak: boolean;
}

function splitLines(text: string): Lines {
	let eol = '\n';
	const firstLf = text.indexOf('\n');
	if (firstLf > 0 && text[firstLf - 1] === '\r') eol = '\r\n';
	const raw = text.split(eol);
	let endsBreak = false;
	if (text.length > 0 && text.endsWith(eol)) {
		endsBreak = true;
		raw.pop();
	}
	return { lines: raw, eol, endsBreak };
}

function joinLines(lines: string[], eol: string, endsBreak: boolean): string {
	if (lines.length === 0) return '';
	let s = lines.join(eol);
	if (endsBreak) s += eol;
	return s;
}

/** Split a patch's text into patch lines (section 3). */
function patchLines(text: string): string[] {
	const raw = text.split('\n');
	if (text.endsWith('\n')) raw.pop();
	return raw.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

// ---------------------------------------------------------------------------
// Matching (section 5)
// ---------------------------------------------------------------------------

function normLine(line: string, tier: number): string {
	if (tier === 0) return line;
	if (tier === 1) return line.replace(/[ \t]+$/, '');
	return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

function lineMatchesAt(fileLines: string[], pos: number, o: string[], tier: number): boolean {
	if (pos < 0 || pos + o.length > fileLines.length) return false;
	for (let k = 0; k < o.length; k++) {
		if (normLine(fileLines[pos + k], tier) !== normLine(o[k], tier)) return false;
	}
	return true;
}

/** All 0-based start positions where o occurs in fileLines at given tier. */
function occurrences(fileLines: string[], o: string[], tier: number): number[] {
	const res: number[] = [];
	if (o.length === 0) return res;
	for (let i = 0; i + o.length <= fileLines.length; i++) {
		if (lineMatchesAt(fileLines, i, o, tier)) res.push(i);
	}
	return res;
}

/** Find o at the first tier that has any occurrence. */
function findTier(
	fileLines: string[],
	o: string[],
	strict: boolean,
): { tier: number; occ: number[] } | null {
	const tiers = strict ? [0] : [0, 1, 2];
	for (const tier of tiers) {
		const occ = occurrences(fileLines, o, tier);
		if (occ.length > 0) return { tier, occ };
	}
	return null;
}

// ---------------------------------------------------------------------------
// Section 6: unified diffs
// ---------------------------------------------------------------------------

interface Hunk {
	a: number; // old start (1-based from header)
	body: string[]; // raw body lines (prefix char + rest), before trailing-empty trim
	// computed:
	o: string[];
	n: string[];
	// noEolFinal: a '\' line follows the last context/'+' body line
	noEolFinal: boolean;
}

interface USection {
	oldPath: string | null; // null if /dev/null or unset
	newPath: string | null;
	create: boolean;
	deleting: boolean;
	hunks: Hunk[];
	// the path used for change/move operations:
}

function stripPrefix(p: string): string {
	let r = p.trim();
	if (r.startsWith('a/') || r.startsWith('b/')) r = r.slice(2);
	return r;
}

function headerPath(rest: string): string {
	const tab = rest.indexOf('\t');
	const p = (tab >= 0 ? rest.slice(0, tab) : rest).trim();
	if (p === '/dev/null') return p;
	return stripPrefix(p);
}

function isDiffGit(line: string): boolean {
	return line.startsWith('diff --git ');
}
function isMinus(line: string): boolean {
	return line.startsWith('--- ');
}
function isPlus(line: string): boolean {
	return line.startsWith('+++ ');
}

function isSectionStart(pl: string[], i: number): boolean {
	if (isDiffGit(pl[i])) return true;
	if (isMinus(pl[i]) && i + 1 < pl.length && isPlus(pl[i + 1])) return true;
	return false;
}

type BodyItem = { t: 'ctx' | 'old' | 'new'; s: string };

interface Hunk {
	a: number;
	items: BodyItem[];
	o: string[];
	n: string[];
	noEolFinal: boolean;
	add: string[];
	addNoEol: boolean;
}

function parseHunkHeader(line: string): { a: number } | null {
	const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
	if (!m) return null;
	return { a: parseInt(m[1], 10) };
}

function isHunkBodyLine(line: string): boolean {
	return line === '' || line[0] === ' ' || line[0] === '-' || line[0] === '+' || line[0] === '\\';
}

function parseHunk(pl: string[], i: number): { hunk: Hunk; next: number } {
	const hdr = parseHunkHeader(pl[i]);
	if (!hdr) throw new ParseFail(i + 1);
	i++;
	const body: string[] = [];
	while (i < pl.length) {
		const bl = pl[i];
		if (isDiffGit(bl)) break;
		if (isMinus(bl) && i + 1 < pl.length && isPlus(pl[i + 1])) break;
		if (!isHunkBodyLine(bl)) break;
		// "diff --git" starts with 'd', not a body kind; but " " or "-" prefix lines are body even if they look like headers.
		// The section-boundary check above handles ---/+++ pair and diff --git. Keep going for normal body lines.
		body.push(bl);
		i++;
	}
	// trim trailing empty context lines at end of body (not part of it) - spec says "empty lines at the end of a body are not part of it"
	while (body.length > 0 && body[body.length - 1] === '') body.pop();

	const items: BodyItem[] = [];
	const o: string[] = [];
	const nlines: string[] = [];
	const add: string[] = [];
	let lastKeptBodyIdx = -1;
	let lastAddIdx = -1;
	for (let k = 0; k < body.length; k++) {
		const line = body[k];
		if (line === '') {
			items.push({ t: 'ctx', s: '' });
			o.push('');
			nlines.push('');
			lastKeptBodyIdx = k;
		} else if (line[0] === ' ') {
			const t = line.slice(1);
			items.push({ t: 'ctx', s: t });
			o.push(t);
			nlines.push(t);
			lastKeptBodyIdx = k;
		} else if (line[0] === '-') {
			items.push({ t: 'old', s: line.slice(1) });
			o.push(line.slice(1));
		} else if (line[0] === '+') {
			const t = line.slice(1);
			items.push({ t: 'new', s: t });
			nlines.push(t);
			add.push(t);
			lastKeptBodyIdx = k;
			lastAddIdx = k;
		}
	}
	let noEolFinal = false;
	if (lastKeptBodyIdx >= 0 && lastKeptBodyIdx + 1 < body.length && body[lastKeptBodyIdx + 1].startsWith('\\')) {
		noEolFinal = true;
	}
	let addNoEol = false;
	if (lastAddIdx >= 0 && lastAddIdx + 1 < body.length && body[lastAddIdx + 1].startsWith('\\')) {
		addNoEol = true;
	}
	return { hunk: { a: hdr.a, items, o, n: nlines, noEolFinal, add, addNoEol }, next: i };
}

function parseUnified(pl: string[], strict: boolean): Edit[] {
	const edits: Edit[] = [];
	let i = 0;
	const n = pl.length;
	while (i < n) {
		if (!isSectionStart(pl, i)) { i++; continue; }

		let gitOld: string | null = null;
		let gitNew: string | null = null;
		if (isDiffGit(pl[i])) {
			const m = /^diff --git a\/(.+?) b\/(.+)$/.exec(pl[i]);
			if (!m) throw new ParseFail(i + 1);
			gitOld = m[1];
			gitNew = m[2];
			i++;
		}

		let oldPath: string | null = null;
		let newPath: string | null = null;
		let create = false;
		let deleting = false;
		let sawMinusPlus = false;

		// header lines until first hunk or next section
		while (i < n) {
			const line = pl[i];
			if (line.startsWith('@@')) break;
			if (isDiffGit(line)) break;
			// ---/+++ pair that is NOT this section's header pair we already consumed?
			if (isMinus(line) && i + 1 < n && isPlus(pl[i + 1])) {
				if (sawMinusPlus) break; // another section
				sawMinusPlus = true;
				oldPath = headerPath(line.slice(4));
				newPath = headerPath(pl[i + 1].slice(4));
				i += 2;
				continue;
			}
			if (isMinus(line)) {
				// --- not followed by +++ inside header
				i++;
				throw new ParseFail(i + 1); // the line after it
			}
			if (line.startsWith('new file mode')) { create = true; i++; continue; }
			if (line.startsWith('deleted file mode')) { deleting = true; i++; continue; }
			if (line.startsWith('rename from ')) { oldPath = line.slice('rename from '.length).trim(); i++; continue; }
			if (line.startsWith('rename to ')) { newPath = line.slice('rename to '.length).trim(); i++; continue; }
			// ignored: index, old mode, new mode, similarity, dissimilarity, Index:, +++, anything else
			i++;
		}

		// resolve paths
		let op: string | null = oldPath;
		let np: string | null = newPath;
		if (op === '/dev/null') op = null;
		if (np === '/dev/null') np = null;
		if (op === null && np === null) { op = gitOld; np = gitNew; }
		else { if (op === null) op = gitOld; if (np === null) np = gitNew; }
		if (create) { op = null; if (np === null) np = gitNew; }
		if (deleting) { np = null; if (op === null) op = gitOld; }

		const hunks: Hunk[] = [];
		while (i < n) {
			if (!pl[i].startsWith('@@')) break;
			const parsed = parseHunk(pl, i);
			hunks.push(parsed.hunk);
			i = parsed.next;
		}

		edits.push(makeUnifiedEdit(op, np, create, deleting, hunks, strict));
	}
	return edits;
}

function renderNewLines(h: Hunk, matched: string[], tier: number): string[] {
	const fileFirst = matched.length > 0 ? matched[0] : '';
	const f = /^[ \t]*/.exec(fileFirst)![0];
	const p = /^[ \t]*/.exec(h.o[0] ?? '')![0];
	const res: string[] = [];
	let m = 0;
	for (const it of h.items) {
		if (it.t === 'ctx') { res.push(matched[m]); m++; }
		else if (it.t === 'old') { m++; }
		else {
			if (tier === 2 && it.s !== '' && it.s.trim() !== '' && p.length > 0 && it.s.startsWith(p)) {
				res.push(f + it.s.slice(p.length));
			} else {
				res.push(it.s);
			}
		}
	}
	return res;
}

function applyHunks(lines: string[], endsBreak: boolean, hunks: Hunk[], strict: boolean): { lines: string[]; endsBreak: boolean } {
	let cur = lines.slice();
	let curEnd = endsBreak;
	let d = 0;
	for (const h of hunks) {
		if (h.o.length > 0) {
			const found = findTier(cur, h.o, strict);
			if (!found) throw new EditFail('no-match', '');
			const target = h.a - 1 + d;
			let best = found.occ[0];
			let bestDist = Math.abs(best - target);
			for (let k = 1; k < found.occ.length; k++) {
				const pos = found.occ[k];
				const dist = Math.abs(pos - target);
				if (dist < bestDist) { bestDist = dist; best = pos; }
			}
			const pos = best;
			const matched = cur.slice(pos, pos + h.o.length);
			const repl = renderNewLines(h, matched, found.tier);
			cur.splice(pos, h.o.length, ...repl);
			d += h.n.length - h.o.length;
			if (pos + repl.length === cur.length) curEnd = !h.noEolFinal;
			// if matched not at end, file's final break stays as it was (curEnd unchanged)
		} else {
			let at = h.a + d;
			if (at > cur.length) at = cur.length;
			const repl = h.n.slice();
			cur.splice(at, 0, ...repl);
			d += h.n.length;
			if (at + repl.length === cur.length) curEnd = !h.noEolFinal;
		}
	}
	return { lines: cur, endsBreak: curEnd };
}

function makeUnifiedEdit(
	oldPath: string | null,
	newPath: string | null,
	create: boolean,
	deleting: boolean,
	hunks: Hunk[],
	strict: boolean,
): Edit {
	return (ap) => {
		if (oldPath !== null && !isSafe(oldPath)) throw new EditFail('unsafe', oldPath);
		if (newPath !== null && !isSafe(newPath)) throw new EditFail('unsafe', newPath);

		if (create) {
			const np = newPath as string;
			if (ap.exists(np)) throw new EditFail('exists', np);
			// created file: + lines of all hunks in order, LF breaks, ends with line break unless '' follows last + line
			const plus: string[] = [];
			let noEolFinal = false;
			for (const h of hunks) {
				for (const l of h.add) plus.push(l);
				noEolFinal = h.addNoEol;
			}
			ap.set(np, joinLines(plus, '\n', !noEolFinal));
			return;
		}

		if (deleting) {
			const op = oldPath as string;
			if (!ap.exists(op)) throw new EditFail('missing', op);
			ap.del(op);
			return;
		}

		const op = oldPath as string;
		const np = newPath;
		if (np !== null && np !== op) {
			if (!ap.exists(op)) throw new EditFail('missing', op);
			if (ap.exists(np)) throw new EditFail('exists', np);
			const text = ap.get(op) as string;
			const L = splitLines(text);
			let res: { lines: string[]; endsBreak: boolean };
			try { res = applyHunks(L.lines, L.endsBreak, hunks, strict); }
			catch (e) { if (e instanceof EditFail) throw new EditFail(e.code, op); throw e; }
			ap.set(np, joinLines(res.lines, L.eol, res.endsBreak));
			ap.del(op);
			ap.recordMove(op, np);
			return;
		}

		if (!ap.exists(op)) throw new EditFail('missing', op);
		const text = ap.get(op) as string;
		const L = splitLines(text);
		let res: { lines: string[]; endsBreak: boolean };
		try { res = applyHunks(L.lines, L.endsBreak, hunks, strict); }
		catch (e) { if (e instanceof EditFail) throw new EditFail(e.code, op); throw e; }
		ap.set(op, joinLines(res.lines, L.eol, res.endsBreak));
	};
}

// ---------------------------------------------------------------------------
// Detection (section 4)
// ---------------------------------------------------------------------------

function detectFormat(text: string): ParsedArgs['format'] | null {
	const pl = patchLines(text);
	const isBlank = (s: string): boolean => s.trim() === '';
	let firstNonBlank = -1;
	for (let i = 0; i < pl.length; i++) {
		if (!isBlank(pl[i])) {
			firstNonBlank = i;
			break;
		}
	}
	if (firstNonBlank >= 0 && pl[firstNonBlank].trim() === '*** Begin Patch') return 'v4a';
	if (firstNonBlank >= 0) {
		const c = pl[firstNonBlank].trimStart()[0];
		if (c === '[' || c === '{') return 'json';
	}
	for (const line of pl) {
		if (line.replace(/[ \t]+$/, '') === '<<<<<<< SEARCH') return 'search-replace';
	}
	for (let i = 0; i < pl.length; i++) {
		if (pl[i].startsWith('diff --git ')) return 'unified';
		if (pl[i].startsWith('--- ') && i + 1 < pl.length && pl[i + 1].startsWith('+++ ')) return 'unified';
	}
	return null;
}

// ---------------------------------------------------------------------------
// Other format parsers (placeholders until implemented)
// ---------------------------------------------------------------------------

function rtrim(line: string): string {
	return line.replace(/[ \t]+$/, '');
}

function reindentNewLines(n: string[], o: string[], matched: string[], tier: number): string[] {
	if (tier !== 2) return n.slice();
	const fileFirst = matched.length > 0 ? matched[0] : '';
	const f = /^[ \t]*/.exec(fileFirst)![0];
	const p = /^[ \t]*/.exec(o[0] ?? '')![0];
	return n.map((nl) => {
		if (nl !== '' && nl.trim() !== '' && p.length > 0 && nl.startsWith(p)) return f + nl.slice(p.length);
		return nl;
	});
}

function parseSearchReplace(pl: string[], strict: boolean): Edit[] {
	const edits: Edit[] = [];
	let i = 0;
	let prevEnd = 0; // index after previous block's REPLACE
	let prevPath: string | null = null;
	while (i < pl.length) {
		if (rtrim(pl[i]) !== '<<<<<<< SEARCH') { i++; continue; }
		const searchIdx = i;
		// find path: nearest non-blank non-fence line before searchIdx, after prevEnd
		let path: string | null = null;
		for (let k = searchIdx - 1; k >= prevEnd; k--) {
			const t = pl[k].trim();
			if (t === '') continue;
			if (t.startsWith('```')) continue;
			path = t;
			break;
		}
		if (path === null) {
			if (prevPath === null) throw new ParseFail(searchIdx + 1);
			path = prevPath;
		}
		// find ======= after searchIdx
		let eqIdx = -1;
		for (let k = searchIdx + 1; k < pl.length; k++) {
			if (rtrim(pl[k]) === '=======') { eqIdx = k; break; }
		}
		if (eqIdx < 0) throw new ParseFail(searchIdx + 1);
		let repIdx = -1;
		for (let k = eqIdx + 1; k < pl.length; k++) {
			if (rtrim(pl[k]) === '>>>>>>> REPLACE') { repIdx = k; break; }
		}
		if (repIdx < 0) throw new ParseFail(searchIdx + 1);
		const oldLines = pl.slice(searchIdx + 1, eqIdx);
		const newLines = pl.slice(eqIdx + 1, repIdx);
		const p = path;
		prevPath = path;
		prevEnd = repIdx + 1;
		i = repIdx + 1;
		edits.push((ap) => {
			if (!isSafe(p)) throw new EditFail('unsafe', p);
			if (oldLines.length === 0) {
				if (ap.exists(p)) throw new EditFail('exists', p);
				ap.set(p, joinLines(newLines, '\n', newLines.length > 0));
				return;
			}
			if (!ap.exists(p)) throw new EditFail('missing', p);
			const text = ap.get(p) as string;
			const L = splitLines(text);
			const found = findTier(L.lines, oldLines, strict);
			if (!found) throw new EditFail('no-match', p);
			if (found.occ.length !== 1) throw new EditFail('ambiguous', p);
			const pos = found.occ[0];
			const matched = L.lines.slice(pos, pos + oldLines.length);
			const repl = reindentNewLines(newLines, oldLines, matched, found.tier);
			const next = L.lines.slice();
			next.splice(pos, oldLines.length, ...repl);
			ap.set(p, joinLines(next, L.eol, L.endsBreak));
		});
	}
	return edits;
}

interface V4aChunk {
	anchor: string | null; // null = no anchor
	items: BodyItem[];
	o: string[];
	n: string[];
	eof: boolean;
}

function parseV4a(pl: string[], strict: boolean): Edit[] {
	// find Begin Patch / End Patch
	let begin = -1;
	let end = -1;
	for (let i = 0; i < pl.length; i++) { if (pl[i].trim() === '*** Begin Patch') { begin = i; break; } }
	if (begin < 0) {
		// error: parse <that line> or parse 1 when none
		let firstNonBlank = -1;
		for (let i = 0; i < pl.length; i++) { if (pl[i].trim() !== '') { firstNonBlank = i; break; } }
		throw new ParseFail(firstNonBlank >= 0 ? firstNonBlank + 1 : 1);
	}
	for (let i = pl.length - 1; i >= 0; i--) { if (pl[i].trim() === '*** End Patch') { end = i; break; } }
	if (end < 0 || end <= begin) throw new ParseFail(pl.length + 1);

	const edits: Edit[] = [];
	let i = begin + 1;
	while (i < end) {
		const line = pl[i];
		if (line.trim() === '') { i++; continue; }
		if (line.startsWith('*** Add File: ')) {
			const path = line.slice('*** Add File: '.length).trim();
			i++;
			const lines: string[] = [];
			while (i < end) {
				const l = pl[i];
				if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ') || l.trim() === '*** End Patch') break;
				if (l === '') { lines.push(''); i++; continue; }
				if (l[0] === '+') { lines.push(l.slice(1)); i++; continue; }
				// blank line between sections ignored? but we are inside section; "Blank lines at the end of a section (before the next section or *** End Patch) are not part of it"
				// A line that's not + and not section start and not end patch: parse error
				throw new ParseFail(i + 1);
			}
			// trim trailing blank lines at end of section
			while (lines.length > 0 && lines[lines.length - 1] === '') lines.pop();
			edits.push((ap) => {
				if (!isSafe(path)) throw new EditFail('unsafe', path);
				if (ap.exists(path)) throw new EditFail('exists', path);
				ap.set(path, joinLines(lines, '\n', true));
			});
			continue;
		}
		if (line.startsWith('*** Delete File: ')) {
			const path = line.slice('*** Delete File: '.length).trim();
			i++;
			// delete section has no lines; consume only blank lines before next section/end
			while (i < end && pl[i].trim() === '') i++;
			edits.push((ap) => {
				if (!isSafe(path)) throw new EditFail('unsafe', path);
				if (!ap.exists(path)) throw new EditFail('missing', path);
				ap.del(path);
			});
			continue;
		}
		if (line.startsWith('*** Update File: ')) {
			const path = line.slice('*** Update File: '.length).trim();
			const updateLine = i + 1;
			i++;
			let moveTo: string | null = null;
			if (i < end && pl[i].startsWith('*** Move to: ')) {
				moveTo = pl[i].slice('*** Move to: '.length).trim();
				i++;
			}
			// parse chunks until next section or end
			const chunks: V4aChunk[] = [];
			while (i < end) {
				const l = pl[i];
				if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ') || l.trim() === '*** End Patch') break;
				if (l.trim() === '') { i++; continue; } // blank between chunks/sections end handled
				if (l.startsWith('@@') || l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+' || l.trim() === '*** End of File') {
					// chunk
					let anchor: string | null = null;
					if (l.startsWith('@@')) {
						const a = l.slice(2).trim();
						anchor = a === '' ? null : a;
						i++;
					}
					const items: BodyItem[] = [];
					const o: string[] = [];
					const nlines: string[] = [];
					let eof = false;
					while (i < end) {
						const bl = pl[i];
						if (bl.startsWith('*** Add File: ') || bl.startsWith('*** Delete File: ') || bl.startsWith('*** Update File: ') || bl.trim() === '*** End Patch') break;
						if (bl.startsWith('@@')) break; // next chunk
						if (bl.trim() === '*** End of File') { eof = true; i++; break; }
						if (bl === '') { items.push({ t: 'ctx', s: '' }); o.push(''); nlines.push(''); i++; continue; }
						const c = bl[0];
						if (c === ' ') { const t = bl.slice(1); items.push({ t: 'ctx', s: t }); o.push(t); nlines.push(t); i++; continue; }
						if (c === '-') { const t = bl.slice(1); items.push({ t: 'old', s: t }); o.push(t); i++; continue; }
						if (c === '+') { const t = bl.slice(1); items.push({ t: 'new', s: t }); nlines.push(t); i++; continue; }
						if (bl.trim() === '') { i++; continue; }
						throw new ParseFail(i + 1);
					}
					// trim trailing blank context lines (not part of section)
					while (items.length > 0 && items[items.length - 1].t === 'ctx' && items[items.length - 1].s === '') {
						items.pop();
						o.pop();
						nlines.pop();
					}
					chunks.push({ anchor, items, o, n: nlines, eof });
					continue;
				}
				throw new ParseFail(i + 1);
			}
			if (chunks.length === 0 && moveTo === null) throw new ParseFail(updateLine);
			edits.push((ap) => {
				if (!isSafe(path)) throw new EditFail('unsafe', path);
				if (moveTo !== null && !isSafe(moveTo)) throw new EditFail('unsafe', moveTo);
				if (!ap.exists(path)) throw new EditFail('missing', path);
				if (moveTo !== null && ap.exists(moveTo)) throw new EditFail('exists', moveTo);
				const text = ap.get(path) as string;
				const L = splitLines(text);
				let cur = L.lines.slice();
				let cursor = 0;
				for (const ch of chunks) {
					if (ch.anchor !== null) {
						// find first line at or after cursor equal to anchor at first tier where one is
						let foundAnchor = -1;
						const tiers = strict ? [0] : [0, 1, 2];
						outer: for (const tier of tiers) {
							for (let p = cursor; p < cur.length; p++) {
								if (normLine(cur[p], tier) === normLine(ch.anchor, tier)) { foundAnchor = p; break outer; }
							}
						}
						if (foundAnchor < 0) throw new EditFail('no-match', path);
						cursor = foundAnchor + 1;
					}
					if (ch.o.length === 0) {
						const at = ch.eof ? cur.length : cursor;
						cur.splice(at, 0, ...ch.n);
						cursor = at + ch.n.length;
						continue;
					}
					const found = findTierInRange(cur, ch.o, strict, cursor, ch.eof);
					if (found === null) throw new EditFail('no-match', path);
					const pos = found.pos;
					const matched = cur.slice(pos, pos + ch.o.length);
					const repl = renderChunkLines(ch, matched, found.tier);
					cur.splice(pos, ch.o.length, ...repl);
					cursor = pos + repl.length;
				}
				const outText = joinLines(cur, L.eol, L.endsBreak);
				if (moveTo !== null) {
					ap.set(moveTo, outText);
					ap.del(path);
					ap.recordMove(path, moveTo);
				} else {
					ap.set(path, outText);
				}
			});
			continue;
		}
		throw new ParseFail(i + 1);
	}
	return edits;
}

function renderChunkLines(ch: V4aChunk, matched: string[], tier: number): string[] {
	const fileFirst = matched.length > 0 ? matched[0] : '';
	const f = /^[ \t]*/.exec(fileFirst)![0];
	const firstOld = ch.items.find((it) => it.t === 'old');
	const p = /^[ \t]*/.exec(firstOld ? firstOld.s : (ch.o[0] ?? ''))![0];
	const res: string[] = [];
	let m = 0;
	for (const it of ch.items) {
		if (it.t === 'ctx') { res.push(matched[m]); m++; }
		else if (it.t === 'old') { m++; }
		else if (!ch.eof && tier === 2 && it.s !== '' && it.s.trim() !== '') {
			if (p.length > 0 && it.s.startsWith(p)) res.push(f + it.s.slice(p.length));
			else if (p.length === 0) res.push(f + it.s);
			else res.push(it.s);
		} else {
			res.push(it.s);
		}
	}
	return res;
}

function findTierInRange(
	fileLines: string[],
	o: string[],
	strict: boolean,
	from: number,
	eof: boolean,
): { tier: number; pos: number } | null {
	const tiers = strict ? [0] : [0, 1, 2];
	for (const tier of tiers) {
		for (let p = from; p + o.length <= fileLines.length; p++) {
			if (eof && p + o.length !== fileLines.length) continue;
			let ok = true;
			for (let k = 0; k < o.length; k++) {
				if (normLine(fileLines[p + k], tier) !== normLine(o[k], tier)) { ok = false; break; }
			}
			if (ok) return { tier, pos: p };
		}
	}
	return null;
}

function splitNewStr(s: string): string[] {
	const raw = s.split('\n');
	if (s.endsWith('\n')) raw.pop();
	return raw.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function normalizeJsonStrForFile(text: string, eol: string): string {
	if (eol === '\r\n') return text.replace(/\r\n/g, '\n');
	return text;
}
function denormalizeForFile(text: string, eol: string): string {
	if (eol === '\r\n') return text.replace(/\n/g, '\r\n');
	return text;
}

function isEditObject(v: unknown): v is Record<string, unknown> {
	return !!v && typeof v === 'object' && !Array.isArray(v);
}

function parseJsonEditObj(obj: Record<string, unknown>, lineNo: number): Edit {
	const cmd = obj.command;
	const path = obj.path;
	if (typeof cmd !== 'string' || typeof path !== 'string') throw new ParseFail(lineNo);
	if (cmd === 'create') {
		if (typeof obj.file_text !== 'string') throw new ParseFail(lineNo);
		const fileText = obj.file_text as string;
		return (ap) => {
			if (!isSafe(path)) throw new EditFail('unsafe', path);
			if (ap.exists(path)) throw new EditFail('exists', path);
			ap.set(path, fileText);
		};
	}
	if (cmd === 'str_replace') {
		if (typeof obj.old_str !== 'string') throw new ParseFail(lineNo);
		const oldStr = obj.old_str as string;
		if (oldStr === '') throw new ParseFail(lineNo);
		const newStrRaw = obj.new_str;
		if (newStrRaw !== undefined && typeof newStrRaw !== 'string') throw new ParseFail(lineNo);
		const newStr = newStrRaw === undefined ? '' : (newStrRaw as string);
		return (ap) => {
			if (!isSafe(path)) throw new EditFail('unsafe', path);
			if (!ap.exists(path)) throw new EditFail('missing', path);
			const orig = ap.get(path) as string;
			const L = splitLines(orig);
			const hay = normalizeJsonStrForFile(orig, L.eol);
			const needle = normalizeJsonStrForFile(oldStr, L.eol);
			const repl = normalizeJsonStrForFile(newStr, L.eol);
			let first = -1;
			let count = 0;
			let pos = 0;
			while (true) {
				const idx = hay.indexOf(needle, pos);
				if (idx < 0) break;
				if (count === 0) first = idx;
				count++;
				pos = idx + 1; // allow overlaps count? spec says "occurs in the text exactly once (positions may overlap)"
			}
			if (count === 0) throw new EditFail('no-match', path);
			if (count !== 1) throw new EditFail('ambiguous', path);
			const outText = hay.slice(0, first) + repl + hay.slice(first + needle.length);
			ap.set(path, denormalizeForFile(outText, L.eol));
		};
	}
	if (cmd === 'insert') {
		const il = obj.insert_line;
		if (typeof il !== 'number' || !Number.isInteger(il)) throw new ParseFail(lineNo);
		const newStrRaw = obj.new_str;
		if (typeof newStrRaw !== 'string') throw new ParseFail(lineNo);
		const newStr = newStrRaw as string;
		return (ap) => {
			if (!isSafe(path)) throw new EditFail('unsafe', path);
			if (!ap.exists(path)) throw new EditFail('missing', path);
			const orig = ap.get(path) as string;
			const L = splitLines(orig);
			if (il < 0 || il > L.lines.length) throw new EditFail('no-match', path);
			const ins = splitNewStr(newStr);
			const next = L.lines.slice();
			next.splice(il, 0, ...ins);
			ap.set(path, joinLines(next, L.eol, L.endsBreak));
		};
	}
	throw new ParseFail(lineNo);
}

function parseJson(text: string, pl: string[], _strict: boolean): Edit[] {
	// array form: one JSON array of edit objects. Any fault is parse error at line where array starts.
	// JSON Lines: one edit object a line, blank lines ignored. A line that does not hold one valid edit object is parse <that line>.
	// Detect: first non-blank line trimmed starts with '[' => array, else object lines.
	let firstNonBlank = -1;
	for (let i = 0; i < pl.length; i++) { if (pl[i].trim() !== '') { firstNonBlank = i; break; } }
	if (firstNonBlank < 0) throw new ParseFail(1);
	const startLine = pl[firstNonBlank].trimStart()[0];
	if (startLine === '[') {
		const arrLineNo = firstNonBlank + 1;
		let parsed: unknown;
		try { parsed = JSON.parse(text); } catch { throw new ParseFail(arrLineNo); }
		if (!Array.isArray(parsed)) throw new ParseFail(arrLineNo);
		const edits: Edit[] = [];
		for (const item of parsed) {
			if (!isEditObject(item)) throw new ParseFail(arrLineNo);
			edits.push(parseJsonEditObj(item, arrLineNo));
		}
		return edits;
	}
	// JSON Lines form
	const edits: Edit[] = [];
	for (let i = 0; i < pl.length; i++) {
		const line = pl[i];
		if (line.trim() === '') continue;
		let obj: unknown;
		try { obj = JSON.parse(line); } catch { throw new ParseFail(i + 1); }
		if (!isEditObject(obj)) throw new ParseFail(i + 1);
		edits.push(parseJsonEditObj(obj, i + 1));
	}
	return edits;
}

function parseByFormat(format: string, text: string, pl: string[], strict: boolean): Edit[] {
	switch (format) {
		case 'unified':
			return parseUnified(pl, strict);
		case 'search-replace':
			return parseSearchReplace(pl, strict);
		case 'v4a':
			return parseV4a(pl, strict);
		case 'json':
			return parseJson(text, pl, strict);
		default:
			throw new ParseFail(1);
	}
}

// ---------------------------------------------------------------------------
// Output (section 2)
// ---------------------------------------------------------------------------

function finalContent(ap: Applier, path: string): string | null {
	if (ap.state.has(path)) {
		const v = ap.state.get(path);
		return v === null || v === undefined ? null : v;
	}
	return ap.orig.has(path) ? (ap.orig.get(path) as string) : null;
}

function emitResult(ap: Applier): void {
	const paths = new Set<string>();
	for (const p of ap.orig.keys()) paths.add(p);
	for (const p of ap.state.keys()) paths.add(p);

	type Change = { kind: 'A' | 'D' | 'M' | 'R'; path: string; sortKey: string };
	const changes: Change[] = [];
	const movedOld = new Set<string>();
	const movedNew = new Set<string>();
	const moveByNew = new Map<string, string>();
	for (const m of ap.moves) {
		movedOld.add(m.old);
		movedNew.add(m.new);
		moveByNew.set(m.new, m.old);
	}

	for (const p of paths) {
		const before = ap.orig.has(p) ? (ap.orig.get(p) as string) : null;
		const after = finalContent(ap, p);
		if (before === null && after === null) continue;
		if (before === null && after !== null) {
			if (movedNew.has(p)) {
				changes.push({ kind: 'R', path: p, sortKey: p });
			} else {
				changes.push({ kind: 'A', path: p, sortKey: p });
			}
		} else if (before !== null && after === null) {
			if (movedOld.has(p)) {
				// represented by R; skip standalone D
			} else {
				changes.push({ kind: 'D', path: p, sortKey: p });
			}
		} else if (before !== null && after !== null && before !== after) {
			changes.push({ kind: 'M', path: p, sortKey: p });
		}
	}

	changes.sort((x, y) => (x.sortKey < y.sortKey ? -1 : x.sortKey > y.sortKey ? 1 : 0));
	let count = 0;
	for (const c of changes) {
		count++;
		if (c.kind === 'R') {
			const oldp = moveByNew.get(c.path) as string;
			out(`R ${oldp} -> ${c.path}`);
		} else if (c.kind === 'A') {
			out(`A ${c.path}`);
		} else if (c.kind === 'D') {
			out(`D ${c.path}`);
		} else {
			out(`M ${c.path}`);
		}
	}
	out(count === 1 ? 'ok: 1 file' : `ok: ${count} files`);
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

async function main(): Promise<void> {
	const envUrl = process.env.MAKEFUN_ENV_URL;
	if (envUrl) {
		await runTrial(envUrl);
		return;
	}
	const args = parseArgs(process.argv.slice(2));
	const text = readPatch(args.patch);
	const pl = patchLines(text);

	let format = args.format;
	if (format === 'auto') {
		const d = detectFormat(text);
		if (d === null) fatal('error: format');
		format = d;
	}

	let edits: Edit[];
	try {
		edits = parseByFormat(format, text, pl, args.strict);
	} catch (e) {
		if (e instanceof ParseFail) fatal(`error: parse ${e.line}`);
		throw e;
	}
	if (edits.length === 0) fatal('error: parse 1');

	const ap = new Applier(readTree('.'));
	const failures: EditFail[] = [];
	for (const edit of edits) {
		try {
			edit(ap);
		} catch (e) {
			if (e instanceof EditFail) failures.push(e);
			else throw e;
		}
	}

	if (failures.length > 0) {
		for (const f of failures) out(`error: ${f.code} ${f.path}`);
		out(`failed: ${failures.length} of ${edits.length} edits`);
		process.exit(1);
	}

	if (args.check) {
		// no writes; but still print the result as if written
		emitResult(ap);
		return;
	}
	// write changed files
	const { writeFileSync, mkdirSync } = await import('node:fs');
	const { dirname } = await import('node:path');
	const paths = new Set<string>();
	for (const p of ap.state.keys()) paths.add(p);
	for (const p of paths) {
		const after = finalContent(ap, p);
		const before = ap.orig.has(p) ? ap.orig.get(p) : undefined;
		if (after === null) {
			// delete
			try {
				(await import('node:fs')).rmSync(p);
			} catch {
				/* ignore */
			}
			continue;
		}
		if (after === before) continue;
		const dir = dirname(p);
		if (dir && dir !== '.') mkdirSync(dir, { recursive: true });
		writeFileSync(p, after);
	}
	emitResult(ap);
}

main().catch((e) => {
	process.stderr.write(String(e?.stack ?? e) + '\n');
	process.exit(2);
});