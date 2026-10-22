#!/usr/bin/env python3
"""reorder.py FILE MOVED BEFORE -- move the definition MOVED (its whole
lines, with the comment lines just above it) to just before the definition
BEFORE, the nearest pair with BEFORE first (the same block).  Sequential
scope (PRIMREC.md 1): a definition must come after those it uses."""
import sys
sys.path.insert(0, __import__("os").path.dirname(__file__))
from migrate import lex, find_defs

f, moved, before = sys.argv[1:4]
src = open(f).read()
toks = lex(src)
ms, bs = find_defs(src, toks, moved), find_defs(src, toks, before)
pairs = [(b, m) for b in bs for m in ms if toks[b.i][2] < toks[m.i][2]]
if not pairs:
    raise SystemExit("no %s after %s in %s" % (moved, before, f))
b, m = min(pairs, key=lambda p: toks[p[1].i][2] - toks[p[0].i][2])

def line_start(pos):
    return src.rfind("\n", 0, pos) + 1

def with_comments(pos):
    """the start of the line, including the comment lines just above"""
    s0 = line_start(pos)
    while s0 > 0:
        prev = line_start(s0 - 1)
        if src[prev:s0 - 1].strip().startswith("--"):
            s0 = prev
        else:
            break
    return s0

ms0 = with_comments(toks[m.i][2])
me = src.find("\n", toks[m.end][3]) + 1 if m.end < len(toks) else len(src)
if src[toks[m.end][3]:me].strip():       # more on the line (a block closer): stop at ;
    me = toks[m.end][3]
if me < len(src) and src[me] == "\n":     # a blank line after it goes with it
    me += 1
block = src[ms0:me] if src[ms0:me].endswith("\n\n") else src[ms0:me] + "\n"
bs0 = with_comments(toks[b.i][2])
out = src[:bs0] + block + src[bs0:ms0] + src[me:]
open(f, "w").write(out)
print("moved %s before %s in %s" % (moved, before, f))
