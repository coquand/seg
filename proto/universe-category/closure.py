#!/usr/bin/env python3
# closure.py DIR M1 M2 ... : the changed modules and every module that
# mentions one of them, transitively (a module name as a word outside
# comments).  All / IvBase / Classical splice files and are not followed.
import sys, os, re, glob
d=sys.argv[1]; seeds=set(sys.argv[2:])
text={}
for f in glob.glob(os.path.join(d,'*.seg')):
    n=os.path.basename(f)[:-4]
    if n in ('All',): continue
    t=open(f).read()
    text[n]='\n'.join(l.split('--',1)[0] for l in t.split('\n'))
S=set(m for m in seeds if m in text); frontier=set(S)
while frontier:
    pat=re.compile(r'(?<![\w\'-])('+'|'.join(map(re.escape,sorted(frontier)))+r')(?![\w\'-])')
    new=set()
    for n,t in text.items():
        if n in S or n in ('IvBase','Classical'): continue
        if pat.search(t): new.add(n)
    S|=new; frontier=new
print(' '.join(sorted(S)))
