import re, glob, os, sys
os.chdir('/Users/coquand/CANONICITY/seg/model')
pats=['GExt*.seg','GUaOp*.seg','GUaGlue*.seg','GYonEq*.seg','GElC.seg','GTransfer*.seg','GCompU*.seg',
      'GEqLaws*.seg','GEqExt.seg','GEquivSub*.seg','GUnivEq.seg','GCofIns.seg','GFibMove.seg','PElYon*.seg','PUaOp.seg','PCompU.seg',
      'DGlueCl*.seg','DTaut*.seg','DClFull.seg','DUaOp.seg','DFibU.seg']
files=sorted(set(f for p in pats for f in glob.glob(p)))
T=[r'subst \(PTy\[',r'\btrE\b',r'trE-',r'TyEqPw',r'\btyEq\b',r'\belSub\b',r'elFibSub',r'ElCong',r'elCong',r'elYon',r'\.Psi\b',r'PsiB',r'PhiF',r'\bmvP\b',
   r'\bcomb\b',r'\bcomb3\b',r'sndSet',r'pairBack',r'\btri\b',r'triExt',r'\btrSub\b',r'fibEq',r'extOb-B',r'tyFull',r'\bQA\b',r'\bQB\b',
   r'subst-sym',r'subst W0\.V',r'substPw',r'substEIo',r'\bcV\b',r'trId',r'GXD\.ext\b',r'ext-inv',r'substIx',r'substF\b',r'coeT\b',r'pr-coe']
N=[r'ExtSub',r'\beqNat\b',r'natDat',r'OutNat',r'\bFS\b',r'FS-ins',r'\bGQ\b',r'fullS',r'\bPQ\b',r'nt-nat',r'ntEq',r'mapP-restr',r'act-o\b',r'actC\b',
   r'uAct-o',r'clSub-o',r'clSub-id',r'eqDSub',r'eqD-o',r'restrictP-o',r'fam-eq',r'pre-comp',r'insc-',r'GensIns',r'InsC']
start=re.compile(r"^(\s{0,6})(?!module\b|open\b|opaque\b|transparent\b|level\b|constraint\b|import\b|--)([A-Za-z][\w'\-]*)\s*(\(|:|\{)")
tot={'T':[0,0],'N':[0,0],'O':[0,0]}
rows=[]
for f in files:
    L=open(f).read().split('\n')
    units=[];cur=None
    for ln in L:
        m=start.match(ln)
        if m and not ln.strip().startswith('--'):
            if cur: units.append(cur)
            cur=[m.group(2),[ln]]
        elif cur is not None:
            if ln.startswith('module') or ln.strip().startswith('module '):
                units.append(cur); cur=None
            else: cur[1].append(ln)
    if cur: units.append(cur)
    c={'T':[0,0],'N':[0,0],'O':[0,0]}
    for name,ls in units:
        body='\n'.join(l for l in ls if not l.strip().startswith('--'))
        if not body.strip(): continue
        n=len([l for l in ls if l.strip()])
        cat='T' if any(re.search(p,body) for p in T) else ('N' if any(re.search(p,body) for p in N) else 'O')
        c[cat][0]+=1; c[cat][1]+=n
    for k in c: tot[k][0]+=c[k][0]; tot[k][1]+=c[k][1]
    rows.append((f,c))
for f,c in rows:
    s=sum(v[1] for v in c.values()) or 1
    print(f"{f:22s} T {c['T'][0]:3d}d {c['T'][1]:5d}l ({100*c['T'][1]//s:2d}%)  N {c['N'][0]:3d}d {c['N'][1]:5d}l ({100*c['N'][1]//s:2d}%)  O {c['O'][0]:3d}d {c['O'][1]:5d}l")
S=sum(v[1] for v in tot.values())
print(f"TOTAL files {len(files)}: T {tot['T'][0]} decls {tot['T'][1]} lines ({100*tot['T'][1]//S}%), N {tot['N'][0]} decls {tot['N'][1]} lines ({100*tot['N'][1]//S}%), O {tot['O'][0]} decls {tot['O'][1]} lines ({100*tot['O'][1]//S}%)")
