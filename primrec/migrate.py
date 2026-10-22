#!/usr/bin/env python3
"""migrate.py -- rewrite the DIRECT recursive calls of a .seg file into
recursive results (PRIMREC.md): in the branch  c xs  of a split at
position p of f, a call  f a0 .. a(p-1) x a(p+1) ..  whose arguments before
p are f's own (its parameters, or the constructor of an earlier split,
rebuilt) and whose argument p is a recursive field x of that branch becomes
ih-x a(p+1) .. , and the branch gets  | ih-..  for all its recursive fields.
For a function field g, the argument (g e ..) becomes (ih-g e ..).

Only calls of exactly that shape are rewritten.  Everything else is left
as it is and listed (MANUAL): the checker then rejects it by scope.

usage: migrate.py FILE NAME...      (rewrites FILE in place, prints a report)
"""
import re, sys

SYMS = ["->", "\\/", "<=", ":=", ".1", ".2", "(", ")", "{", "}", "[", "]", ";", ",",
        ":", "=", "\\", "|", "*", "#", "@", "<", ">", "+"]

# the data types of core: constructor -> (arity, {field: binders}) for the
# recursive fields (Base.Nat, Trees.Tree, V.M)
RECS = {"suc": (1, {0: 0}), "node": (2, {0: 0, 1: 0}), "sup": (2, {1: 1})}
CLOSE = {")": "(", "}": "{", "]": "["}

def lex(src):
    toks = []   # (kind, text, start, end)
    i, n = 0, len(src)
    isid = lambda ch: ch.isalnum() or ch in "_'"
    while i < n:
        c = src[i]
        if c.isspace():
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src.startswith("{-", i):
            depth, j = 0, i + 2
            while j < n:
                if src.startswith("-}", j):
                    if depth == 0: j += 2; break
                    depth -= 1; j += 2
                elif src.startswith("{-", j): depth += 1; j += 2
                else: j += 1
            i = j; continue
        if c == "." and i + 1 < n and (src[i+1].isalpha() or src[i+1] == "_"):
            j = i + 1
            while True:
                while j < n and isid(src[j]): j += 1
                if j + 1 < n and src[j] == "-" and isid(src[j+1]): j += 1; continue
                break
            toks.append(("proj", src[i:j], i, j)); i = j; continue
        if c.isalpha() or c == "_":
            j = i
            while True:
                while j < n and isid(src[j]): j += 1
                if j + 1 < n and src[j] == "-" and isid(src[j+1]): j += 1; continue
                break
            toks.append(("id", src[i:j], i, j)); i = j; continue
        for s in SYMS:
            if src.startswith(s, i):
                toks.append(("sym", s, i, i + len(s))); i += len(s); break
        else:
            raise SystemExit("unexpected character %r at %d" % (c, i))
    return toks

def match_close(toks, i):
    """index of the bracket closing toks[i]"""
    stack = []
    for j in range(i, len(toks)):
        k, t = toks[j][0], toks[j][1]
        if k == "sym" and t in "({[":
            stack.append(t)
        elif k == "sym" and t in ")}]":
            stack.pop()
            if not stack: return j
    raise SystemExit("unbalanced at token %d" % i)

def scan_to(toks, i, stops):
    """first index >= i at depth 0 whose token is in stops (or a closer)"""
    j = 0; d = 0
    j = i
    while j < len(toks):
        k, t = toks[j][0], toks[j][1]
        if d == 0 and k == "sym" and t in stops: return j
        if k == "sym" and t in "({[": d += 1
        elif k == "sym" and t in ")}]":
            if d == 0: return j
            d -= 1
        j += 1
    return j

KW_END = {"where", "in"}

def atom_end(toks, i):
    """end (exclusive) of an argument atom starting at i, or None"""
    k, t = toks[i][0], toks[i][1]
    if k == "id" and t not in KW_END | {"split", "let", "U", "Id", "refl", "idJ", "new"}:
        j = i + 1
    elif k == "sym" and t in "({":
        j = match_close(toks, i) + 1
    else:
        return None
    while j < len(toks) and (toks[j][0] == "proj" or (toks[j][0] == "sym" and toks[j][1] in (".1", ".2", "["))):
        j = match_close(toks, j) + 1 if toks[j][1] == "[" else j + 1
    return j

def text(src, toks, a, b):
    return src[toks[a][2]:toks[b-1][3]] if b > a else ""

def norm(s):
    s = re.sub(r"\s+", " ", s.strip())
    while s.startswith("(") and s.endswith(")"):
        inner = s[1:-1]
        depth = 0; ok = True
        for ch in inner:
            if ch == "(": depth += 1
            elif ch == ")":
                depth -= 1
                if depth < 0: ok = False; break
        if not ok or depth != 0: break
        s = inner.strip()
    return s

class Def:
    pass

def find_defs(src, toks, name):
    """the definitions of name: at a unit start (after ; { or the start)"""
    out = []
    for i, tk in enumerate(toks):
        if tk[0] == "id" and tk[1] == name and (i == 0 or (toks[i-1][0] == "sym" and toks[i-1][1] in (";", "{"))):
            # a definition: params then : ... = body ;
            colon = scan_to(toks, i + 1, (":", "=", ";"))
            if colon >= len(toks) or toks[colon][1] != ":": continue
            eq = scan_to(toks, colon + 1, ("=", ";"))
            if eq >= len(toks) or toks[eq][1] != "=": continue
            end = scan_to(toks, eq + 1, (";",))
            d = Def(); d.name = name; d.i = i; d.colon = colon; d.eq = eq; d.end = end
            out.append(d)
    return out

def header_params(toks, d):
    """visible parameter names of the header, and whether hidden ones exist"""
    names, hidden = [], False
    j = d.i + 1
    while j < d.colon:
        t = toks[j][1]
        if t in "({":
            c = match_close(toks, j)
            col = scan_to(toks, j + 1, (":",))
            ns = [toks[q][1] for q in range(j + 1, col) if toks[q][0] == "id"]
            if t == "{": hidden = True
            else: names += ns
            j = c + 1
        else:
            j += 1
    return names, hidden

def type_hidden(toks, d):
    """a hidden binder in the type's leading telescope"""
    j = d.colon + 1
    while j < d.eq:
        if toks[j][0] == "sym" and toks[j][1] == "{": return True
        if toks[j][0] == "sym" and toks[j][1] in "([":
            j = match_close(toks, j) + 1; continue
        j += 1
    return False

def walk(src, toks, a, b, path, splits, d):
    """the canonical spine of the body toks[a:b]: lambdas and splits"""
    j = a
    while j < b and toks[j][0] == "sym" and toks[j][1] == "\\":
        arrow = scan_to(toks, j + 1, ("->",))
        path = path + [toks[q][1] for q in range(j + 1, arrow) if toks[q][0] == "id"]
        j = arrow + 1
    if j < b and toks[j][1] == "split" and toks[j+1][1] == "{":
        close = match_close(toks, j + 1)
        p = len(path)
        q = j + 2
        while q < close:
            c = toks[q][1]
            arrow = scan_to(toks, q + 1, ("->", "|"))
            xs = [toks[r][1] for r in range(q + 1, arrow) if toks[r][0] == "id"]
            has_bar = toks[arrow][1] == "|"
            if has_bar:
                arrow = scan_to(toks, arrow + 1, ("->",))
            bend = scan_to(toks, arrow + 1, (";",))
            rebuilt = c if not xs else "(" + c + " " + " ".join(xs) + ")"
            br = {"c": c, "xs": xs, "p": p, "path": path, "a": arrow + 1, "b": bend,
                  "xs_end": arrow if not has_bar else None, "bar": has_bar, "uses": set()}
            splits.append(br)
            walk(src, toks, arrow + 1, bend, path + [rebuilt], splits, d)
            q = bend + 1
        return

def migrate(src, names):
    report = []
    for name in names:
        toks = lex(src)
        edits = []      # (start, end, replacement)
        for d in find_defs(src, toks, name):
            params, hid = header_params(toks, d)
            if hid or type_hidden(toks, d):
                report.append("MANUAL %s: hidden binders" % name); continue
            splits = []
            walk(src, toks, d.eq + 1, d.end, params, splits, d)
            calls = [i for i in range(d.eq + 1, d.end) if toks[i][0] == "id" and toks[i][1] == name]
            for ci in calls:
                # the visible arguments
                args = []; j = ci + 1; explicit_hidden = False
                while j < d.end:
                    e = atom_end(toks, j)
                    if e is None: break
                    if toks[j][1] == "{": explicit_hidden = True
                    args.append((j, e)); j = e
                done = False
                # the enclosing branches, innermost first
                encl = [br for br in splits if br["a"] <= ci < br["b"]]
                encl.sort(key=lambda br: br["a"], reverse=True)
                for br in encl:
                    if explicit_hidden: break
                    rec = RECS.get(br["c"])
                    if not rec or rec[0] != len(br["xs"]): continue
                    p = br["p"]
                    if len(args) <= p: continue
                    if any(norm(text(src, toks, *args[k])) != norm(br["path"][k]) for k in range(p)):
                        continue
                    a0, a1 = args[p]
                    arg = text(src, toks, a0, a1)
                    fo = {br["xs"][k]: k for k, nb in rec[1].items() if nb == 0}
                    fn = {br["xs"][k]: k for k, nb in rec[1].items() if nb > 0}
                    if toks[a0][0] == "id" and a1 == a0 + 1 and arg in fo:
                        rep = "ih-" + arg
                    elif toks[a0][1] == "(" and toks[a0+1][0] == "id" and toks[a0+1][1] in fn:
                        rep = "(ih-" + src[toks[a0+1][2]:toks[a1-1][3]]
                    else:
                        continue
                    edits.append((toks[ci][2], toks[a1-1][3], rep))
                    br["uses"].add(1)
                    done = True
                    break
                if not done:
                    line = src.count("\n", 0, toks[ci][2]) + 1
                    report.append("MANUAL %s: line %d: %s" % (name, line,
                                  re.sub(r"\s+", " ", src[toks[ci][2]:toks[min(ci+8, d.end-1)][3]])[:90]))
            for br in splits:
                if br["uses"] and not br["bar"]:
                    rec = RECS[br["c"]]
                    ihs = " ".join("ih-" + br["xs"][k] for k in sorted(rec[1]))
                    pos = toks[br["a"] - 1][2]       # the arrow
                    edits.append((pos, pos, "| " + ihs + " "))
        for s, e, r in sorted(edits, key=lambda x: x[0], reverse=True):
            src = src[:s] + r + src[e:]
        report.append("rewrote %s: %d edits" % (name, len(edits)))
    return src, report

if __name__ == "__main__":
    f = sys.argv[1]
    src = open(f).read()
    out, rep = migrate(src, sys.argv[2:])
    open(f, "w").write(out)
    print("\n".join(rep))
