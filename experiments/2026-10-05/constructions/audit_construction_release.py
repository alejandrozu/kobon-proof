from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[3]
a=(R/'Kobon/AllN.lean').read_text()
s=a[a.index('def enhancement'):a.index('theorem enhancement_sound')]
finite={int(n):int(v) for n,v in re.findall(r'\|\s*(\d+)\s*=>\s*(\d+)',s)}
def G(n):return 0 if n<3 else (1 if n==3 else n*(n-3)//3+1+n%2)
def candidate(n,base):
    t=0
    while base*2**t+1<=n:
        q=base*2**t
        T=(q*q-4)//3 if base==10 else (q*q-1)//3
        if n==q+1:return T
        if n==q+2:return T+q//2
        t+=1
    return 0
def previous(n):return max(G(n),finite.get(n,0),*(candidate(n,b) for b in [10,32,48]))
rows=[]
for t in range(10):
    q=60*2**t
    for parity,n,T in [('odd',q+1,1200*4**t-10),('even',q+2,1200*4**t+30*2**t-12)]:
        old=previous(n)
        rows.append(dict(t=t,parity=parity,n=n,prior_certified=old,new_family=T,retained_max=max(old,T),gain=T-old,simple_upper_gap=9 if parity=='odd' else 11))
base=R/'research/openmath-seven-hour-2026-10-05/constructions'
(base/'family61-envelope-comparison.json').write_text(json.dumps(dict(scope='Exact executable values of RecursiveEnvelope plus the closed33/49 families; does not assert worldwide numerical priority',source='Kobon/AllN.lean, Universal.lean, RecursiveEnvelope.lean',rows=rows),indent=2)+'\n')
print(json.dumps(rows[:8],indent=2))
active=['OpenMathConstructionBoolean','OpenMathConstructionRescale','OpenMathConstructionLineEquality','OpenMathConstructionLineBEq','OpenMathConstructionSeed33Data','OpenMathConstructionSeed33Simple','OpenMathConstructionSeed33Checks','OpenMathConstructionSeed33','OpenMathConstructionSeed33Normalized','OpenMathConstructionSeed33Visible','OpenMathConstructionForgeFamily','OpenMathBoundaryNormals','OpenMathBoundarySectors','OpenMathBoundaryChart','OpenMathBoundarySectorGeometry','OpenMathBoundarySignedSamples','OpenMathConstructionSeed61IntegerFastRaw','OpenMathConstructionSeed61Data','OpenMathConstructionSeed61IntegerFastData','OpenMathConstructionSeed61IntegerFastSimple','OpenMathConstructionSeed61IntegerFastTriangles','OpenMathConstructionSeed61Simple','OpenMathConstructionSeed61Triangles','OpenMathConstructionSeed61Checks','OpenMathConstructionSeed61','OpenMathConstructionSeed61Normalized','OpenMathConstructionSeed61Visible','OpenMathConstructionFamily61','OpenMathAxisCapCone','OpenMathConstructionPareto61IntegerFastRaw','OpenMathConstructionPareto61Data','OpenMathConstructionPareto61IntegerFastData','OpenMathConstructionPareto61IntegerFastSimple','OpenMathConstructionPareto61IntegerFastTriangles','OpenMathConstructionPareto61Simple','OpenMathConstructionPareto61Triangles','OpenMathConstructionPareto61Checks','OpenMathConstructionPareto61','OpenMathConstructionPareto61Normalized','OpenMathConstructionPareto61Visible','OpenMathConstructionParetoFamily61','OpenMathConstructionEnvelope','OpenMathParametricDual','OpenMathConstructionSeed37IntegerFastRaw','OpenMathConstructionSeed37Data','OpenMathConstructionSeed37IntegerFastData','OpenMathConstructionSeed37IntegerFastSimple','OpenMathConstructionSeed37IntegerFastTriangles','OpenMathConstructionSeed37Simple','OpenMathConstructionSeed37Triangles','OpenMathConstructionSeed37Checks','OpenMathConstructionSeed37','OpenMathConstructionSeed37Normalized','OpenMathConstructionFamily37']
files=[]
for name in active:
    p=R/'Kobon'/f'{name}.lean';o=R/'.lake/build/lib/lean/Kobon'/f'{name}.olean'
    assert p.exists() and o.exists(),name
    files.append(dict(path=str(p.relative_to(R)).replace('\\','/'),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),status='Compiled PASS'))
roots=['OpenMathConstructionSeed61.directions_bool._native.native_decide.ax_1','OpenMathConstructionSeed61.distinguished_subset_bool._native.native_decide.ax_1','OpenMathConstructionSeed61.ordered_bool._native.native_decide.ax_1','OpenMathConstructionSeed61Fast.int_simple_bool._native.native_decide.ax_1','OpenMathConstructionSeed61Fast.int_triangles_bool._native.native_decide.ax_1']
audit=dict(author='Alejandro Zarzuelo Urdiales',geometric_scope='Actual simple real straight-line arrangements; lower bounds remain valid for unrestricted Kobon arrangements, upper-window optimality claims are scoped to simple arrangements',n=61,T=1190,visible_pairs=28,axis_caps=59,epsilon_interval='0<epsilon<=1/100000000',parameter_grid='actual tan(k*pi/60), k=1..29; final parameter epsilon',integer_grid_denominator='100000000000000000000',seed_credit='Rohith Poola point61:1190, pinned f462d8e18aea2a458376c523c9b6c2980237071f; independent reciprocal-slope refit supplies the compatible uniform seed',iteration_credit='Bartholdi, Blanc, Loisel; existing genuine BBL geometry in this repository',novelty_scope='Lean-certified compatible uniform seed and infinite q60 orbit; finite1190 count is not claimed new; wider numerical priority remains subject to source review',odd_native_roots=roots,even_native_roots=roots+['OpenMathConstructionSeed61.admissible_bool._native.native_decide.ax_1','OpenMathConstructionSeed61.visible_bool._native.native_decide.ax_1'],other_axioms=['propext','Classical.choice','Quot.sound'],unpromoted_drafts=['OpenMathConstructionSparse.lean','OpenMathConstructionSeed61IntegerRaw.lean','OpenMathConstructionSeed61IntegerData.lean','OpenMathConstructionSeed61IntegerSimple.lean'],active_compiled_modules=files)
(base/'construction-proof-provenance.json').write_text(json.dumps(audit,indent=2)+'\n')

pareto_roots=['OpenMathConstructionPareto61.'+name+'._native.native_decide.ax_1' for name in ['directions_bool','distinguished_subset_bool','ordered_bool','admissible_bool','visible_bool']]+['OpenMathConstructionPareto61Fast.'+name+'._native.native_decide.ax_1' for name in ['int_simple_bool','int_triangles_bool']]
audit['pareto_improvement']=dict(status='Full Lean PASS',visible_pairs=29,normal=['1','-8000441397/4000000000'],central_height_coefficient='20000000000/8777037',right_slope='10000000000/29500000091',source='contestant61-pareto-sparse-uniform-box.json',epsilon_interval='0<epsilon<=1/100000000',even_formula='1200*4^t+30*2^t-11 at n=60*2^t+2',native_roots=pareto_roots,simple_upper_gap=10,prior_even_family_gain=1,scope='New stronger compatible uniform boundary resource and infinite even lower family; not a new finite record at61 or62')
(base/'construction-proof-provenance.json').write_text(json.dumps(audit,indent=2)+'\n')
pareto_rows=[]
for t in range(10):
 q=60*2**t;n=q+2;old=1200*4**t+30*2**t-12;new=old+1;prior=max(previous(n),old)
 pareto_rows.append(dict(t=t,n=n,baseline=G(n),prior_family=old,prior_retained=prior,new_family=new,new_retained=max(prior,new),gain_over_prior_retained=max(prior,new)-prior,baseline_gain=new-G(n),simple_upper_gap=10))
(base/'family61-pareto-envelope-comparison.json').write_text(json.dumps(dict(scope='Exact comparison against RecursiveEnvelope plus the33/49 and first61 family; worldwide numerical priority is not asserted',even_formula='1200*4^t+30*2^t-11',rows=pareto_rows),indent=2)+'\n')
print(json.dumps(pareto_rows[:4],indent=2))

seed37_roots=['OpenMathConstructionSeed37.'+name+'._native.native_decide.ax_1' for name in ['directions_bool','distinguished_subset_bool','ordered_bool']]+['OpenMathConstructionSeed37Fast.'+name+'._native.native_decide.ax_1' for name in ['int_simple_bool','int_triangles_bool']]
audit['known_orbit37']=dict(status='Full Lean PASS',source='contestant37-uniform-box.json',seed_T=431,axis_caps=35,epsilon_interval='0<epsilon<=1/100000000',odd_formula='432*4^t-1 at n=36*2^t+1',even_formula='432*4^t-1+18*2^t at n=36*2^t+2',scope='Known q18 numerical orbit credited to Parpalak-Utkin/Blanc; compatible fixed-slope source refit plus generic deficit-two successor verified here',simple_optimality=True,native_roots_both_parities=seed37_roots,tangent_bounds='BBLTangent36Bounds, standard axioms only')
audit['all_n_envelope']=dict(module='Kobon/OpenMathConstructionEnvelope.lean',status='Full Lean PASS',formula='max RecursiveEnvelope(n), finite maxima of matching33/49/37/61 dyadic candidates',pointwise_retains_prior=True,quadratic_quality='n^2 <=3*(bound(n)+n)',interpretation='Certified portfolio lower formula for every natural order; neither a full-gain arbitrary successor rule nor a new leading asymptotic constant')
(base/'construction-proof-provenance.json').write_text(json.dumps(audit,indent=2)+'\n')
known37=[]
for t in range(8):
 q=36*2**t
 for parity,n,T in [('odd',q+1,432*4**t-1),('even',q+2,432*4**t-1+18*2**t)]:
  prior=previous(n)
  known37.append(dict(t=t,parity=parity,n=n,prior_certified=prior,new_family=T,retained_max=max(prior,T),gain=max(prior,T)-prior,baseline_gain=T-G(n),simple_upper_gap=0))
(base/'family37-envelope-comparison.json').write_text(json.dumps(dict(scope='Known numerical q18 orbit, now fully verified as an additional portfolio branch; unrestricted even finite witnesses may be stronger',rows=known37),indent=2)+'\n')
print(json.dumps(known37[:6],indent=2))
