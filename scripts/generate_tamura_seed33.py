"""Generate a true tangent-grid 33-line parametric seed, with Lean box checks.

The 33:341 / 34:357 counts are classical. This supplies a formally checkable
whole-epsilon seed for the geometric iteration project, not numerical novelty.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json,re,sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import primitive,arrangement

def rat(v):
    v=F(v)
    return str(v.numerator) if v.denominator==1 else f'({v.numerator}/{v.denominator})'
def vector(vs):return '!['+','.join(map(rat,vs))+']'
def triples(ts):return '['+','.join('⟨'+','.join(map(str,t))+'⟩' for t in ts)+']'

def main():
    source=ROOT/'experiments/2026-09-21/hybrid-family/tamura-family/n033.json'
    raw=json.loads(source.read_text());old=[tuple(map(F,x)) for x in raw['lines_frac']]
    bd=json.loads((ROOT/'research/six-hour-2026-09-21/hybrid-family/dyadic-tangent-bounds.json').read_text())['32']
    lo=[F(bd[str(k)][0]) for k in range(1,16)]+[F(0)]
    hi=[F(bd[str(k)][1]) for k in range(1,16)]+[F(1,100000)]
    mid=[(l+h)/2 for l,h in zip(lo,hi)];mid[-1]=hi[-1]
    forms=[(F(0),)*16];slopes=[F(0)];labels=[None]
    for a,b,c in old[1:]:
        m=-a/b;scale=10**80;m=F(round(m*scale),scale)
        x=c/a;sgn=1 if x>0 else -1
        j=min(range(16),key=lambda k:abs(abs(x)-mid[k]))
        assert abs(abs(x)-mid[j])<F(1,10**40) or j==15
        form=tuple(m*sgn if k==j else F(0) for k in range(16))
        forms.append(form);slopes.append(m);labels.append((j,sgn))
    lines=[(slopes[i],F(-1),forms[i]) for i in range(33)]
    concrete=[primitive((a,b,sum(c*x for c,x in zip(form,mid)))) for a,b,form in lines]
    ar=arrangement(concrete);tris=sorted(ar['triangles'])
    assert len(tris)==341 and len(ar['points'])==528
    distinguished=[t for t in tris if 0 in t];assert len(distinguished)==31
    def det(i,j):return slopes[j]-slopes[i]
    @lru_cache(None)
    def ev(r,i,j):
        a,b=slopes[i],slopes[j];c=slopes[r]
        return tuple(c*(-forms[i][k]+forms[j][k])-(a*forms[j][k]-b*forms[i][k])-det(i,j)*forms[r][k] for k in range(16))
    @lru_cache(None)
    def lower(f):return sum(c*(lo[k] if c>=0 else hi[k]) for k,c in enumerate(f))
    @lru_cache(None)
    def upper(f):return sum(c*(hi[k] if c>=0 else lo[k]) for k,c in enumerate(f))
    @lru_cache(None)
    def oriented(r,i,j):return tuple(det(i,j)*v for v in ev(r,i,j))
    for i,j,k in combinations(range(33),3):
        f=ev(k,i,j)
        assert lower(f)>0 or upper(f)<0 or (all(f[t]==0 for t in range(15)) and f[15]),('simple',i,j,k)
    print('All rational simplicity boxes verified.',flush=True)
    for i,j,k in tris:
        for r in range(33):
            fs=[oriented(r,a,b) for a,b in ((i,j),(i,k),(j,k))]
            assert all(lower(f)>=0 for f in fs) or all(upper(f)<=0 for f in fs),('triangle',i,j,k,r)
    print('All 341 rational triangle boxes verified.',flush=True)
    visible=[]
    for i,j in combinations(range(33),2):
        good=True
        for r in range(33):
            f=oriented(r,i,j)
            di=det(r,i)*(-10+13*slopes[i]);dj=det(r,j)*(-10+13*slopes[j])
            if not ((lower(f)>=0 and di>=0 and dj>=0) or (upper(f)<=0 and di<=0 and dj<=0)):
                good=False;break
        if good:visible.append((i,j,33))
    assert len(visible)==16,visible
    assert (0,32,33) in visible
    print('All 16 visible-pair rational boxes verified.',flush=True)
    # Reuse the fully proved generic seed theorem structure; replace every
    # data definition and all size-dependent conclusions explicitly.
    template=(ROOT/'Kobon/BBLSeed21.lean').read_text(encoding='utf-8')
    prefix=template[:template.index('def lo')]
    prefix=prefix.replace('Kobon.BBLTangentBounds','Kobon.TamuraTangentBounds').replace('Kobon.BBLSeed21','Kobon.TamuraSeed33').replace('21-line','33-line').replace('pi/20','pi/32')
    body=prefix+f'def lo : Form 16 := {vector(lo)}\ndef hi : Form 16 := {vector(hi)}\n\n'
    body+='def lines : Array (ParamLine 16) := #[\n  '+',\n  '.join('⟨'+rat(a)+','+rat(b)+','+vector(c)+'⟩' for a,b,c in lines)+']\n\n'
    body+='def lineAt (i : Nat) : ParamLine 16 := lines[i]!\n\n'
    body+='def triangles : List Triple := '+triples(tris)+'\n\n'
    body+='def distinguished : List Triple := '+triples(distinguished)+'\n\n'
    body+='def visible : List Triple := '+triples(visible)+'\n\n'
    body+='def rightSlope : ℚ := '+rat(slopes[-1])+'\n\n'
    rest=template[template.index('theorem directions'):]
    # Replace the parameter declaration/proof wholesale, before changing sizes.
    p0=rest.index('noncomputable def parameters');p1=rest.index('theorem no_parallel')
    params='noncomputable def parameters (epsilon : ℝ) : Fin 16 → ℝ :=\n  !['+','.join(f'tan ({k}*π/32)' for k in range(1,16))+',epsilon]\n\n'
    params+='noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=\n  toLine (lineAt i) (parameters epsilon)\n\n'
    params+='theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :\n    InBox lo hi (parameters epsilon) := by\n  intro i\n  fin_cases i\n'
    for k in range(1,16):params+=f'  · convert TamuraTangentBounds.tan_32_{k}_bounds using 1 <;> norm_num [lo,hi,parameters]\n'
    params+='  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu\n\n'
    before=rest[:p0];after=rest[p1:]
    def resize(s):
        # Numeric replacement only in inherited theorem text, never coordinates.
        mp={'21':'33','22':'34','132':'341','142':'357','19':'31','20':'32','9':'15'}
        s=re.sub(r'\b(21|22|132|142|19|20|9)\b',lambda m:mp[m.group()],s)
        s=s.replace('visible.length=10','visible.length=16')
        return s.replace('Kobon.BBLSeed21','Kobon.TamuraSeed33')
    body+=resize(before)+params+resize(after)
    body=body.replace('theorem ordered : Increasing 33 triangles := by decide +kernel',
        'theorem ordered : Increasing 33 triangles := by native_decide')
    draft=ROOT/'research/six-hour-2026-09-21/drafts/TamuraSeed33.lean'
    draft.parent.mkdir(parents=True,exist_ok=True)
    draft.write_text(body,encoding='utf-8',newline='\n')
    report=dict(n=33,triangles=341,distinguished=31,visible_pairs=16,epsilon_interval='0 < epsilon <= 1/100000',
        tangent_grid='Actual tan(k*pi/32); rational bounds proved separately in Lean',
        numerical_priority='Classical Tamura/BBL family, not new numerical values',
        slopes=[str(m) for m in slopes],intercept_labels=labels,
        status='Generator rational checks passed; Lean build must independently check the generated theorem')
    (ROOT/'research/six-hour-2026-09-21/hybrid-family/tamura-seed33-generation.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Wrote unverified draft research/six-hour-2026-09-21/drafts/TamuraSeed33.lean',flush=True)

if __name__=='__main__':main()
