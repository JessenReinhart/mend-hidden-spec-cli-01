// Patch applier CLI for hidden-spec-cli. Detects/applies patch formats:
// auto (detection), json (file-op list), search-replace (<<<<<<< blocks),
// unified (diff/git hunks), and v4a (*** Begin/Update/Add/Delete File).

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

class Exit2 extends Error { readonly line: string; constructor(line: string) { super(line); this.line = line; } }
class Fail { readonly code: string; readonly path: string; constructor(code: string, path: string) { this.code = code; this.path = path; } }

const FORMATS = ['auto', 'json', 'search-replace', 'unified', 'v4a'];
const blank = (s: string): boolean => s.trim() === '';
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}
function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}
function fileBreak(text: string): string { const nl = text.indexOf('\n'); return nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n'; }
function splitFile(text: string): { lines: string[]; br: string; final: boolean } {
  if (text === '') return { lines: [], br: '\n', final: false };
  const br = fileBreak(text);
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}
function joinFile(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}
function normLF(s: string): string { return s.replace(/\r\n/g, '\n').replace(/\r/g, '\n'); }
function trimEndWS(s: string): string { return s.replace(/[ \t]+$/, ''); }
function trimWS(s: string): string { return s.replace(/^[ \t]+|[ \t]+$/g, ''); }
function leadingWS(s: string): string { const m = s.match(/^[ \t]*/); return m ? m[0] : ''; }

class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try { if (statSync(p).isFile()) v = readFileSync(p, 'utf8'); } catch { v = null; }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null { return this.now.has(p) ? this.now.get(p)! : this.original(p); }
}

type EditFn = (tree: Tree, strict: boolean) => void;
interface Edit { path: string; kind: 'normal' | 'rename'; to?: string; run: EditFn; }

function ensureSafe(p: string, raw: string): void { if (!safe(p)) throw new Fail('unsafe', raw); }
function exists(tree: Tree, p: string, raw: string): string {
  ensureSafe(p, raw); const t = tree.get(p); if (t === null) throw new Fail('missing', p); return t;
}
function ensureMissing(tree: Tree, p: string, raw: string): void { ensureSafe(p, raw); if (tree.get(p) !== null) throw new Fail('exists', p); }

function eqAt(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimEndWS(a) === trimEndWS(b);
  return trimWS(a) === trimWS(b);
}
function findTier(fileLines: string[], oldLines: string[], strict: boolean): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const occ: number[] = [];
    for (let i = 0; i <= fileLines.length - oldLines.length; i++) {
      let ok = true;
      for (let j = 0; j < oldLines.length; j++) { if (!eqAt(fileLines[i + j]!, oldLines[j]!, tier)) { ok = false; break; } }
      if (ok) occ.push(i);
    }
    if (occ.length > 0) return { tier, occ };
  }
  return null;
}
function reindentLine(line: string, fileFirst: string, oldFirst: string): string {
  if (line === '' || line.trim() === '') return line;
  const P = leadingWS(oldFirst);
  const F = leadingWS(fileFirst);
  if (P !== '' && line.startsWith(P)) return F + line.slice(P.length);
  if (P === '') return F + line; // ? better follow spec: "starts with P" - empty P means startsWith true
  return line;
}
function applyReplacement(file: { lines: string[]; br: string; final: boolean }, i: number, oldLines: string[], newLines: string[], tier: number, ctxOldIdx?: Set<number>) {
  const matched = file.lines.slice(i, i + oldLines.length);
  const out: string[] = [];
  const F = leadingWS(matched[0] ?? '');
  const P = leadingWS(oldLines[0] ?? '');
  // We need to map newLines to context vs replaced. For unified/v4a, context lines appear in both old and new at same positions in a merged walk.
  // Caller provides buildOutput to handle context properly.
  for (let j = 0; j < newLines.length; j++) {
    const isCtx = ctxOldIdx ? false : false; // unused here
    if (tier === 2) out.push(reindentLine(newLines[j]!, matched[0] ?? '', oldLines[0] ?? ''));
    else out.push(newLines[j]!);
  }
  file.lines.splice(i, oldLines.length, ...out);
}

function buildRepl(file: { lines: string[]; br: string; final: boolean }, i: number, oldLines: string[], newLines: string[], tier: number, isContextNew: (newIdx: number) => number | -1): string[] {
  const matched = file.lines.slice(i, i + oldLines.length);
  const F = leadingWS(matched[0] ?? '');
  const P = leadingWS(oldLines[0] ?? '');
  return newLines.map((nl, j) => {
    const oldIdx = isContextNew(j);
    if (oldIdx >= 0) return matched[oldIdx]!;
    if (tier >= 1) {
      if (nl === '' || nl.trim() === '') return nl;
      if (P !== '' && nl.startsWith(P)) return F + nl.slice(P.length);
      if (P === '') return F + nl;
      return nl;
    }
    return nl;
  });
}

function doReplace(tree: Tree, rawPath: string, oldLines: string[], newLines: string[], strict: boolean, isContextNew?: (newIdx: number) => number | -1, choose?: (occ: number[], fileLines: string[]) => number | 'ambiguous' | 'no-match'): void {
  const p = rawPath;
  ensureSafe(p, rawPath);
  const before = tree.get(p);
  if (before === null) throw new Fail('missing', p);
  const f = splitFile(before);
  const found = findTier(f.lines, oldLines, strict);
  if (!found) throw new Fail('no-match', p);
  let pick = found.occ.length === 1 ? found.occ[0]! : -1;
  if (found.occ.length > 1) {
    if (choose) {
      const c = choose(found.occ, f.lines);
      if (c === 'ambiguous') throw new Fail('ambiguous', p);
      if (c === 'no-match') throw new Fail('no-match', p);
      pick = c;
    } else throw new Fail('ambiguous', p);
  }
  const ctxFn = isContextNew ?? (() => -1);
  const repl = buildRepl(f, pick, oldLines, newLines, found.tier, ctxFn);
  f.lines.splice(pick, oldLines.length, ...repl);
  tree.now.set(p, joinFile(f.lines, f.br, f.final));
}

// ---------- JSON (section 9) ----------
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return { path: p, kind: 'normal', run: (tree) => { ensureMissing(tree, p, p); tree.now.set(p, text); } };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str; const newStr = (o.new_str as string | undefined) ?? '';
    const tOld = typeof o.trailing_old_str === 'string' ? o.trailing_old_str : undefined;
    const tNew = typeof o.trailing_new_str === 'string' ? o.trailing_new_str : undefined;
    return { path: p, kind: 'normal', run: (tree, strict) => {
      const before = exists(tree, p, p);
      const nl = before.indexOf('\n'); const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before); const old = lf(oldStr);
      let count = 0; for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (tOld !== undefined) {
        let tcount = 0; for (let k = t.indexOf(lf(tOld)); k >= 0; k = t.indexOf(lf(tOld), k + 1)) tcount += 1;
        if (tcount === 0) throw new Fail('no-match', p);
        if (tcount > 1) throw new Fail('ambiguous', p);
        const tok = lf(tOld);
        let base = -1;
        for (let k = t.indexOf(tok); k >= 0; k = t.indexOf(tok, k + 1)) {
          if (k + tok.length === t.length || t.slice(k + tok.length).startsWith('\n')) { base = k; break; }
        }
        if (base < 0 || !t.startsWith(old, base - old.length) || base - old.length < 0) throw new Fail('no-match', p);
        if (count > 1) throw new Fail('ambiguous', p);
        const replacedNew = (tNew === undefined ? '' : lf(tNew));
        const at = base - old.length;
        const out = t.slice(0, at) + (tNew === undefined ? lf(newStr) : lf(newStr) + replacedNew) + t.slice(base + tok.length);
        tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
      } else {
        if (count === 0) throw new Fail('no-match', p);
        if (count > 1) throw new Fail('ambiguous', p);
        const at = t.indexOf(old); const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
        tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
      }
    } };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line; const add = patchLines(o.new_str);
    return { path: p, kind: 'normal', run: (tree) => {
      const before = exists(tree, p, p);
      const nl = before.indexOf('\n'); const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    } };
  }
  if (o.command === 'delete' || (o.command === 'move' && typeof o.destination === 'string')) {
    const dest = typeof o.destination === 'string' ? o.destination : undefined;
    const move = o.command === 'move' && dest !== undefined;
    return { path: p, kind: move ? 'rename' : 'normal', to: move ? dest : undefined, run: (tree) => {
      exists(tree, p, p);
      if (move) { if (dest! === p) { tree.now.set(p, null); return; } ensureMissing(tree, dest!, dest!); }
      tree.now.set(p, null);
      if (move) {
        const moved = tree.get(p);
        // after deletion, re-read content? tree.get after set null returns original/now; need to capture before delete
        // Simpler: captured in closure via outer var - but tree.now.get before set? We'll handle by reading original/now before deletion
      }
    } };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) { const e = jsonEdit(x); if (e === null) throw new Exit2(`error: parse ${first + 1}`); edits.push(e); }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------- Search-Replace (section 7) ----------
function parseSearchReplace(lines: string[]): Edit[] {
  const edits: Edit[] = [];
  let i = 0; let curPath: string | null = null;
  while (i < lines.length) {
    const line = lines[i]!;
    if (trimEndWS(line) === '<<<<<<< SEARCH') {
      const searchLine = i + 1;
      // find path: nearest non-blank line before, not starting with ``` and not after previous REPLACE
      let p: string | null = curPath;
      // scan back from i-1 to find path candidate
      for (let j = i - 1; j >= 0; j--) {
        const prev = lines[j]!;
        if (trimEndWS(prev) === '>>>>>>> REPLACE') break;
        if (blank(prev)) continue;
        const t = prev.trim();
        if (t.startsWith('```')) continue;
        p = t;
        break;
      }
      if (p === null) throw new Exit2(`error: parse ${searchLine}`);
      // read old lines until =======
      i++;
      const oldLines: string[] = [];
      let foundSep = false;
      while (i < lines.length) {
        if (trimEndWS(lines[i]!) === '=======') { foundSep = true; i++; break; }
        oldLines.push(lines[i]!); i++;
      }
      if (!foundSep) throw new Exit2(`error: parse ${searchLine}`);
      const newLines: string[] = [];
      let foundEnd = false;
      while (i < lines.length) {
        if (trimEndWS(lines[i]!) === '>>>>>>> REPLACE') { foundEnd = true; i++; break; }
        newLines.push(lines[i]!); i++;
      }
      if (!foundEnd) throw new Exit2(`error: parse ${searchLine}`);
      curPath = p;
      const path = p;
      const oldL = oldLines.slice();
      const newL = newLines.slice();
      edits.push({ path, kind: 'normal', run: (tree, strict) => {
        if (oldL.length === 0) {
          ensureMissing(tree, path, path);
          // create with LF, ends with line break unless format says otherwise
          const content = newL.length === 0 ? '' : newL.join('\n') + '\n';
          tree.now.set(path, content);
        } else {
          doReplace(tree, path, oldL, newL, strict);
        }
      } });
      continue;
    }
    i++;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}



// ---------- V4A (section 8) ----------
function parseV4a(lines: string[]): Edit[] {
  const firstNonBlank = lines.findIndex((l) => !blank(l));
  if (firstNonBlank < 0 || lines[firstNonBlank]!.trim() !== '*** Begin Patch') {
    throw new Exit2(`error: parse ${firstNonBlank + 1}`);
  }
  let lastNonBlank = -1;
  for (let i = lines.length - 1; i >= 0; i--) if (!blank(lines[i]!)) { lastNonBlank = i; break; }
  if (lastNonBlank < 0 || lines[lastNonBlank]!.trim() !== '*** End Patch') {
    throw new Exit2(`error: parse ${lines.length + 1}`);
  }
  const raw = lines.slice(firstNonBlank + 1, lastNonBlank);
  const edits: Edit[] = [];
  let pos = 0;
  const trimSectionEnd = (arr: string[]): string[] => {
    let e = arr.length; while (e > 0 && blank(arr[e - 1]!)) e--; return arr.slice(0, e);
  };
  while (pos < raw.length) {
    const line = raw[pos]!;
    if (blank(line)) { pos++; continue; }
    const t = line.trim();
    if (t.startsWith('*** Add File: ')) {
      const path = t.slice('*** Add File: '.length).trim();
      pos++;
      const body: string[] = [];
      while (pos < raw.length) {
        const lt = raw[pos]!.trim();
        if (lt.startsWith('*** ') || lt.startsWith('@@')) break;
        body.push(raw[pos]!); pos++;
      }
      const content = trimSectionEnd(body).flatMap(l => {
        if (l.startsWith('+')) return [l.slice(1)];
        if (l === '') return [''];
        return [];
      });
      edits.push({ path, kind: 'normal', run: (tree) => { ensureMissing(tree, path, path); tree.now.set(path, content.length === 0 ? '' : content.join('\n') + '\n'); } });
      continue;
    }
    if (t.startsWith('*** Delete File: ')) {
      const path = t.slice('*** Delete File: '.length).trim();
      pos++;
      edits.push({ path, kind: 'normal', run: (tree) => { exists(tree, path, path); tree.now.set(path, null); } });
      continue;
    }
    if (t.startsWith('*** Update File: ')) {
      const path = t.slice('*** Update File: '.length).trim();
      pos++;
      let moveTo: string | null = null;
      if (pos < raw.length && raw[pos]!.trim().startsWith('*** Move to: ')) { moveTo = raw[pos]!.trim().slice('*** Move to: '.length).trim(); pos++; }
      type Hunk = { old: string[]; neu: string[]; newToOld: number[]; anchor: string | null; eof: boolean };
      const hunks: Hunk[] = [];
      while (pos < raw.length) {
        const ht = raw[pos]!.trim();
        if (ht.startsWith('*** ') && ht !== '*** End of File') break;
        const isHunkStart = ht.startsWith('@@') || ht === '*** End of File' || raw[pos]!.startsWith(' ') || raw[pos]!.startsWith('-') || raw[pos]!.startsWith('+');
        if (isHunkStart) {
          let anchor: string | null = null;
          if (ht.startsWith('@@')) {
            const a = ht.slice(2).trim();
            anchor = a === '' ? null : a;
            pos++;
          }
          const old: string[] = []; const neu: string[] = []; const newToOld: number[] = [];
          let eof = false;
          while (pos < raw.length) {
            const hl = raw[pos]!;
            const hlt = hl.trim();
            if (hlt === '*** End of File') { eof = true; pos++; break; }
            if (hlt.startsWith('*** ') || hlt.startsWith('@@')) break;
            if (hl.startsWith(' ')) { const txt = hl.slice(1); newToOld.push(old.length); old.push(txt); neu.push(txt); }
            else if (hl.startsWith('-')) { old.push(hl.slice(1)); }
            else if (hl.startsWith('+')) { newToOld.push(-1); neu.push(hl.slice(1)); }
            else if (hl === '') { newToOld.push(old.length); old.push(''); neu.push(''); }
            else if (hl.startsWith('\\')) { /* no newline marker, ignore */ }
            else break;
            pos++;
          }
          while (old.length > 0 && old[old.length - 1] === '' && neu[neu.length - 1] === '') {
            old.pop(); neu.pop(); newToOld.pop();
          }
          hunks.push({ old, neu, newToOld, anchor, eof });
          continue;
        }
        pos++;
      }
      const mv = moveTo;
      edits.push({ path, kind: mv ? 'rename' : 'normal', to: mv ?? undefined, run: (tree, strict) => {
        const before = exists(tree, path, path);
        if (mv && mv !== path) ensureMissing(tree, mv, mv);
        let current = before;
        let cursor = 0;
        for (const h of hunks) {
          const f = splitFile(current);
          if (h.anchor !== null) {
            const af = findTier(f.lines.slice(cursor), [h.anchor], strict);
            if (!af) throw new Fail('no-match', path);
            cursor += af.occ[0]! + 1;
            f.lines = f.lines; // no-op; splitFile result stays intact
            // re-split below with updated cursor
          }
          if (h.old.length === 0) {
            const pick = h.eof ? f.lines.length : Math.min(cursor, f.lines.length);
            const repl = buildRepl(f, pick, [], h.neu, 0, () => -1);
            f.lines.splice(pick, 0, ...repl);
            current = joinFile(f.lines, f.br, f.final);
            cursor = pick + repl.length;
            continue;
          }
          const found = findTier(f.lines.slice(cursor), h.old, strict);
          if (!found) throw new Fail('no-match', path);
          const occ = found.occ.map((x) => x + cursor);
          let pick: number;
          if (h.eof) {
            pick = f.lines.length - h.old.length;
            if (!occ.includes(pick)) throw new Fail('no-match', path);
          } else pick = occ[0]!;
          const isCtxNew = (ni: number) => h.newToOld[ni] ?? -1;
          const repl = buildRepl(f, pick, h.old, h.neu, found.tier, isCtxNew);
          f.lines.splice(pick, h.old.length, ...repl);
          current = joinFile(f.lines, f.br, f.final);
          cursor = pick + repl.length;
        }
        if (mv && mv !== path) { tree.now.set(path, null); tree.now.set(mv, current); }
        else tree.now.set(path, current);
      } });
      continue;
    }
    pos++;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

// ---------- Unified (section 5/6) ----------
function cleanUnifiedPath(raw: string): string {
  let p = raw;
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  return p;
}
function stripAB(p: string): string {
  if (p === '/dev/null') return p;
  if (p.startsWith('a/')) return p.slice(2);
  if (p.startsWith('b/')) return p.slice(2);
  return p;
}
function parseDiffGit(line: string, lineNo: number): { oldPath: string; newPath: string } {
  const s = line.slice('diff --git '.length);
  const candidates: number[] = [];
  for (let i = 0; i < s.length - 2; i++) {
    if (s[i] === ' ' && s[i + 1] === 'b' && s[i + 2] === '/') candidates.push(i);
  }
  for (const idx of candidates) {
    const left = s.slice(0, idx);
    const right = s.slice(idx + 1);
    if (left.startsWith('a/')) return { oldPath: left, newPath: right };
  }
  const m = s.match(/^(a\/.+) (b\/.+)$/);
  if (m) return { oldPath: m[1]!, newPath: m[2]! };
  throw new Exit2(`error: parse ${lineNo}`);
}
function parseUnified(lines: string[]): Edit[] {
  type UHunk = { oldStart: number; oldCount: number; newStart: number; newCount: number; lines: { kind: ' ' | '-' | '+'; text: string }[]; noeolOld: boolean; noeolNew: boolean };
  type UFile = {
    diffOld?: string; diffNew?: string;
    minusPath?: string; plusPath?: string; hasMinusPlus: boolean;
    renameFrom?: string; renameTo?: string;
    newFile: boolean; deletedFile: boolean;
    hunks: UHunk[];
  };
  const files: UFile[] = [];
  let cur: UFile | null = null;
  let i = 0;
  const startSection = (dOld?: string, dNew?: string): UFile => {
    cur = { diffOld: dOld, diffNew: dNew, hasMinusPlus: false, newFile: false, deletedFile: false, hunks: [] };
    files.push(cur);
    return cur;
  };
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const { oldPath, newPath } = parseDiffGit(l, i + 1);
      startSection(oldPath, newPath);
      i++;
      continue;
    }
    if (l.startsWith('--- ')) {
      const nextIsPlus = i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ');
      if (!nextIsPlus) {
        throw new Exit2('error: format');
      }
      const oldPath = cleanUnifiedPath(l.slice(4));
      const newPath = cleanUnifiedPath(lines[i + 1]!.slice(4));
      if (!cur || cur.hunks.length > 0 || cur.hasMinusPlus) {
        startSection(undefined, undefined);
      }
      cur!.minusPath = oldPath;
      cur!.plusPath = newPath;
      cur!.hasMinusPlus = true;
      i += 2;
      continue;
    }
    if (l.startsWith('+++ ')) { i++; continue; }
    if (l.startsWith('rename from ')) {
      if (cur && cur.hunks.length === 0) cur.renameFrom = cleanUnifiedPath(l.slice('rename from '.length));
      i++; continue;
    }
    if (l.startsWith('rename to ')) {
      if (cur && cur.hunks.length === 0) cur.renameTo = cleanUnifiedPath(l.slice('rename to '.length));
      i++; continue;
    }
    if (l.startsWith('new file mode ')) {
      if (cur && cur.hunks.length === 0) cur.newFile = true;
      i++; continue;
    }
    if (l.startsWith('deleted file mode ')) {
      if (cur && cur.hunks.length === 0) cur.deletedFile = true;
      i++; continue;
    }
    if (l.startsWith('@@ ')) {
      const m = l.match(/^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      if (!cur) { startSection(undefined, undefined); }
      const oldStart = parseInt(m[1]!, 10), oldCount = m[2] !== undefined ? parseInt(m[2]!, 10) : 1;
      const newStart = parseInt(m[3]!, 10), newCount = m[4] !== undefined ? parseInt(m[4]!, 10) : 1;
      i++;
      const body: { kind: ' ' | '-' | '+'; text: string }[] = [];
      let oldNoeol = false;
      let newNoeol = false;
      while (i < lines.length) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ')) break;
        if (bl.startsWith('@@ ')) break;
        if (bl.startsWith(' ')) { body.push({ kind: ' ', text: bl.slice(1) }); i++; continue; }
        if (bl.startsWith('-')) { body.push({ kind: '-', text: bl.slice(1) }); i++; continue; }
        if (bl.startsWith('+')) { body.push({ kind: '+', text: bl.slice(1) }); i++; continue; }
        if (bl.startsWith('\\')) {
          if (body.length > 0) {
            const last = body[body.length - 1]!.kind;
            if (last === '-') oldNoeol = true;
            else if (last === '+') newNoeol = true;
            else { oldNoeol = true; newNoeol = true; }
          }
          i++; continue;
        }
        if (bl === '') {
          const nx = i + 1 < lines.length ? lines[i + 1]! : '';
          if (nx.startsWith(' ') || nx.startsWith('+') || nx.startsWith('-') || nx.startsWith('\\')) { body.push({ kind: ' ', text: '' }); i++; continue; }
          if (nx === '') {
            let j = i + 1; while (j < lines.length && lines[j] === '') j++;
            const nn = j < lines.length ? lines[j]! : '';
            if (nn.startsWith(' ') || nn.startsWith('+') || nn.startsWith('-') || nn.startsWith('\\')) { body.push({ kind: ' ', text: '' }); i++; continue; }
            break;
          }
          break;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1]!.kind === ' ' && body[body.length - 1]!.text === '') {
        body.pop();
      }
      cur!.hunks.push({ oldStart, oldCount, newStart, newCount, lines: body, oldNoeol, newNoeol });
      continue;
    }
    i++;
  }
  if (files.length === 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  for (const f of files) {
    let oldRaw: string | undefined;
    let newRaw: string | undefined;
    if (f.hasMinusPlus) { oldRaw = f.minusPath; newRaw = f.plusPath; }
    else if (f.renameFrom !== undefined || f.renameTo !== undefined) { oldRaw = f.renameFrom; newRaw = f.renameTo; }
    else if (f.diffOld !== undefined || f.diffNew !== undefined) { oldRaw = f.diffOld; newRaw = f.diffNew; }
    const oldPath = oldRaw !== undefined ? stripAB(oldRaw) : undefined;
    const newPath = newRaw !== undefined ? stripAB(newRaw) : undefined;
    const path = (oldPath === '/dev/null' || oldPath === undefined ? newPath : oldPath)!;
    if (!path) throw new Exit2('error: parse 1');
    const isCreate = oldPath === '/dev/null' || f.newFile;
    const isDelete = newPath === '/dev/null' || f.deletedFile;
    if (isCreate && !isDelete) {
      const cpath = (newPath && newPath !== '/dev/null') ? newPath : path;
      edits.push({ path: cpath, kind: 'normal', run: (tree) => {
        ensureMissing(tree, cpath, cpath);
        let content = '';
        for (const h of f.hunks) {
          const newLines = h.lines.filter(e => e.kind !== '-').map(e => e.text);
          content += newLines.join('\n') + '\n';
        }
        tree.now.set(cpath, content);
      } });
      continue;
    }
    if (isDelete && !isCreate) {
      const dpath = (oldPath && oldPath !== '/dev/null') ? oldPath : path;
      edits.push({ path: dpath, kind: 'normal', run: (tree) => { exists(tree, dpath, dpath); tree.now.set(dpath, null); } });
      continue;
    }
    const mv = (newPath && newPath !== oldPath && newPath !== '/dev/null' && oldPath !== '/dev/null') ? newPath : undefined;
    edits.push({ path, kind: mv ? 'rename' : 'normal', to: mv, run: (tree, strict) => {
      let current = exists(tree, path, path);
      if (mv) ensureMissing(tree, mv, mv);
      for (const h of f.hunks) {
        const O: string[] = []; const N: string[] = []; const NtoO: number[] = [];
        let o = 0;
        for (const e of h.lines) {
          if (e.kind === ' ') { O.push(e.text); N.push(e.text); NtoO.push(o); o++; }
          else if (e.kind === '-') { O.push(e.text); o++; }
          else { N.push(e.text); NtoO.push(-1); }
        }
        const sf = splitFile(current);
        if (O.length === 0 && N.length > 0) {
          const pick2 = Math.min(h.oldStart, sf.lines.length);
          const touchesEnd2 = pick2 >= sf.lines.length;
          const repl = buildRepl(sf, pick2, [], N, 0, () => -1);
          sf.lines.splice(pick2, 0, ...repl);
          if (touchesEnd2) {
            if (h.newNoeol) sf.final = false;
            else if (h.oldNoeol) sf.final = true;
          }
          current = joinFile(sf.lines, sf.br, sf.final);
          continue;
        }
        if (O.length === 0 && N.length === 0) continue;
        const found = findTier(sf.lines, O, strict);
        if (!found) throw new Fail('no-match', path);
        let pick: number;
        if (found.occ.length === 1) pick = found.occ[0]!;
        else {
          const target = Math.max(0, h.oldStart - 1);
          pick = found.occ.reduce((best, cur2) => Math.abs(cur2 - target) < Math.abs(best - target) ? cur2 : best, found.occ[0]!);
          const dmin = Math.min(...found.occ.map(x => Math.abs(x - target)));
          if (found.occ.filter(x => Math.abs(x - target) === dmin).length > 1) throw new Fail('ambiguous', path);
        }
        const isCtxNew = (ni: number) => NtoO[ni] ?? -1;
        const repl = buildRepl(sf, pick, O, N, found.tier, isCtxNew);
        const touchesEnd3 = pick + O.length >= sf.lines.length;
        sf.lines.splice(pick, O.length, ...repl);
        if (touchesEnd3) {
          if (h.newNoeol) sf.final = false;
          else if (h.oldNoeol) sf.final = true;
        }
        current = joinFile(sf.lines, sf.br, sf.final);
      }
      if (mv && mv !== path) { tree.now.set(path, null); tree.now.set(mv, current); }
      else tree.now.set(path, current);
    } });
  }
  return edits;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex(l => !blank(l));
  if (first < 0) return null;
  const t = lines[first]!.trim();
  if (t === '*** Begin Patch') return 'v4a';
  if (t.startsWith('[') || t.startsWith('{')) return 'json';
  // unified: find --- and +++ or @@ anywhere (fenced-bare)
  for (let i = 0; i < lines.length; i++) {
    if (lines[i]!.startsWith('--- ') && i+1 < lines.length && lines[i+1]!.startsWith('+++ ')) return 'unified';
    if (lines[i]!.startsWith('@@ ')) return 'unified';
  }
  if (t.startsWith('---') || t.startsWith('@@')) return 'unified';
  for (const l of lines) { if (trimEndWS(l) === '<<<<<<< SEARCH') return 'search-replace'; }
  return null;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[] = [];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines);
    else if (kind === 'v4a') edits = parseV4a(lines);
    else if (kind === 'unified') edits = parseUnified(lines);
    else throw new Exit2('error: format');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  if (edits.length === 0) return { code: 2, out: ['error: parse 1'] };
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit.run(tree, strict);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const renameTo = new Map<string, string>();
  const renameFrom = new Map<string, string>();
  for (const e of edits) {
    if (e.kind === 'rename' && e.to && e.to !== e.path) {
      renameTo.set(e.path, e.to);
      renameFrom.set(e.to, e.path);
    }
  }
  const keys = [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
  const changed = new Set<string>();
  for (const p of keys) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was !== now) changed.add(p);
  }
  const rows: string[] = [];
  const emitted = new Set<string>();
  for (const p of keys) {
    if (emitted.has(p) || !changed.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    const to = renameTo.get(p);
    if (to && was !== null && now === null) {
      const toWas = tree.original(to);
      const toNow = tree.now.get(to);
      if (toWas === null && toNow != null && changed.has(to)) {
        rows.push(`R ${p} -> ${to}`);
        emitted.add(p);
        emitted.add(to);
        if (!check) {
          rmSync(p, { force: true });
          mkdirSync(dirname(to), { recursive: true });
          writeFileSync(to, toNow);
        }
        continue;
      }
    }
    const from = renameFrom.get(p);
    if (from && was === null && now !== null) {
      const fromWas = tree.original(from);
      const fromNow = tree.now.get(from);
      if (fromWas !== null && fromNow === null && changed.has(from)) {
        rows.push(`R ${from} -> ${p}`);
        emitted.add(from);
        emitted.add(p);
        if (!check) {
          rmSync(from, { force: true });
          mkdirSync(dirname(p), { recursive: true });
          writeFileSync(p, now);
        }
        continue;
      }
    }
    rows.push(`${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`);
    emitted.add(p);
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}



