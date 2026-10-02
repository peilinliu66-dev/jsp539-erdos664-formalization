#!/usr/bin/env python3
"""Finite sanity checks only. This does not run Lean or establish the theorem."""
from itertools import combinations
from fractions import Fraction
from math import comb, exp
import hashlib, json, pathlib, random, re, zipfile
ROOT=pathlib.Path(__file__).resolve().parents[1]
rng=random.Random(539664)
counts={}
def check(name,p):
    assert p,name
    counts[name]=counts.get(name,0)+1

def plane(q):
    pts=[(x,y) for x in range(q) for y in range(q)]
    ls=[frozenset((a,y) for y in range(q)) for a in range(q)]
    ls += [frozenset((x,(m*x+b)%q) for x in range(q)) for m in range(q) for b in range(q)]
    return pts,ls

for q in [2,3,5,7,11]:
    pts,ls=plane(q)
    check('line_count',len(set(ls))==q*(q+1))
    check('line_sizes',all(len(l)==q for l in ls))
    for x in pts: check('point_degree',sum(x in l for l in ls)==q+1)
    for x,y in combinations(pts,2): check('pair_coverage',sum(x in l and y in l for l in ls)==1)
    for l,m in combinations(ls,2): check('line_intersections',len(l&m)<=1)
    # All tiny retention sets, plus reproducible samples at larger orders.
    if q<=3:
        retained=[{p for i,p in enumerate(pts) if mask>>i&1} for mask in range(1<<len(pts))]
    else:
        retained=[set(pts)]+[{p for p in pts if rng.random()<0.8} for _ in range(100)]
    for R in retained:
        ts=[frozenset(l&R) for l in ls]
        if all(len(t)>=2 for t in ts):
            check('trace_injectivity',len(set(ts))==len(ls))
            for x,y in combinations(sorted(R),2):
                check('retained_exact_pairs',sum(x in t and y in t for t in ts)==1)
    for k in [2,3,4]:
        for _ in range(40):
            C=set(rng.sample(pts,rng.randrange(min(len(pts),2*k*q)+1)))
            traces=[l&C for l in ls]
            short=[t for t in traces if len(t)<4*k]
            check('short_line_count',q*q<=2*len(short))
            if all(traces):
                chosen=[];used=set()
                for t in short:
                    if not (used&t):chosen.append(t);used|=t
                check('disjoint_packing_rate',q<=16*k*len(chosen))
                check('packing_short_size',all(0<len(t)<=4*k for t in chosen))
            # Exercise chunk edge/codegree inequalities only in their actual range.
            if len(pts)>2*k*q:
                X=set(rng.sample(pts,rng.randrange(2*k*q+1,len(pts)+1)))
                g=len(X)//(2*q)
                chunks=[]
                for l in ls:
                    v=sorted(l&X)
                    chunks += [frozenset(v[i:i+g]) for i in range(0,len(v)-g+1,g)]
                edges={frozenset(e) for c in chunks for e in combinations(sorted(c),k)}
                check('chunk_distinct',len(set(chunks))==len(chunks))
                check('chunk_edge_lower',len(edges)>=q*q*comb(g,k))
                for p in X:
                    check('chunk_degree_one',sum(p in e for e in edges)<=(q+1)*comb(g-1,k-1))
                for t in range(2,k+1):
                    for S in [rng.sample(sorted(X),t) for _ in range(min(10,comb(len(X),t)))]:
                        SS=set(S)
                        check('chunk_higher_degree',sum(SS<=e for e in edges)<=comb(g-t,k-t))

for g in range(41):
    for k in range(g+1):
        for t in range(k+1):
            check('binomial_scaled',comb(g-t,k-t)*g**t <= k**t*comb(g,k))
for n in range(101):
    prob=Fraction(sum(comb(n,j) for j in range(2*n//5+1)),2**n)
    check('line_tail',float(prob)<=exp(-n/200)+1e-15)
    pgf=sum((Fraction(comb(n,j),2**n)*Fraction(10,11)**j for j in range(n+1)),Fraction())
    check('exact_pgf',pgf==Fraction(21,22)**n)

files=list(ROOT.rglob('*.lean'))
missing=[];banned=[];graph={}
for p in files:
    c=p.read_text()
    c=re.sub(r'/\-.*?\-/','',c,flags=re.S)
    c=re.sub(r'--[^\n]*','',c)
    bad=re.findall(r'\b(?:sorry|admit|axiom|native_decide|sorryAx|unsafe|implemented_by)\b',c)
    if bad:banned.append({'file':str(p.relative_to(ROOT)),'tokens':bad})
    imps=re.findall(r'^import\s+(\S+)',c,re.M)
    mod='.'.join(p.relative_to(ROOT).with_suffix('').parts)
    graph[mod]=[m for m in imps if not m.startswith('Mathlib') and m != 'Lake']
    for m in graph[mod]:
        if not (ROOT/(m.replace('.','/')+'.lean')).is_file():missing.append(m)
active=set();done=set()
def visit(m):
    assert m not in active,('cycle',m)
    if m in done:return
    active.add(m)
    for x in graph.get(m,[]):visit(x)
    active.remove(m);done.add(m)
for m in graph:visit(m)
check('no_missing_local_imports',not missing)
check('no_forbidden_source_tokens',not banned)
result={'status':'FINITE_SANITY_AND_STATIC_SOURCE_ONLY','compiled':False,'kernel_verified':False,
        'seed':539664,'counts':counts,'total_assertions':sum(counts.values()),
        'lean_files_including_lakefile_and_verify':len(files),'lean_lines':sum(len(p.read_text().splitlines()) for p in files),
        'missing_local_imports':missing,'forbidden_tokens':banned,'local_import_cycles':False}
pathlib.Path(__file__).with_name('finite-mathematics-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
