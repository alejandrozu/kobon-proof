"""Generate and exactly count a finite rational member of the derived family.

The underlying eight-line seed and doubling formula are due to
Parpalak--Utkin and Bartholdi--Blanc--Loisel, respectively. The additional
line is y = 10^(-6)*x + H, beyond every existing vertex.

Dependency for proposing coefficients: mpmath. Verification: standard library.
Usage: python generate.py 3 certificates/n051.json [precision_digits]
"""
import json
import sys
from pathlib import Path
from mpmath import mp
from exact_geometry import F, primitive, arrangement

def construct(t, digits=100):
    if t < 0:
        raise ValueError('t must be nonnegative')
    mp.dps = digits
    q = 6*2**t
    root3 = F(str(mp.sqrt(3)))
    epsilon = F(1,4*q)
    eta = 3*root3*q**6
    delta = 2*q**6
    intercepts = [-root3,-1/root3,1/root3,root3,-epsilon,epsilon]
    # Enforce Q=L1 cap L3 cap L5 exactly, including after rational rounding.
    qx = (2*eta/root3-root3)/(1+2*eta)
    qy = -(qx+root3)/2
    slopes = [-F(1,2),-eta,eta,F(2,5),qy/(qx+epsilon),
              4*root3/(root3+9*epsilon)]
    n = 6
    for _ in range(t):
        minimum = min(abs(x) for x in slopes)
        new_intercepts = [F(str(mp.tan(-mp.pi/2+(mp.mpf(j)-mp.mpf('0.5'))*mp.pi/n)))
                          for j in range(1,n+1)]
        # sin(2 beta) = 2 tan(beta)/(1+tan(beta)^2).
        new_slopes = [-minimum/F(n**10)*(2*b/(1+b*b)+1/(n**6*b))
                      for b in new_intercepts]
        intercepts += new_intercepts
        slopes += new_slopes
        n *= 2
    lines = [(0,1,0)]+[primitive((m,-1,m*a)) for m,a in zip(slopes,intercepts)]
    lines.append((1,-1,delta))
    core = arrangement(lines)
    core_count = len(core['triangles'])
    expected_core = q*q//3+q//2
    if core_count != expected_core:
        raise RuntimeError(f'Rational approximation failed core check: {core_count} != {expected_core}; increase precision')
    sigma = F(1,10**6)
    height = 1+max(F(p[1],p[2])-sigma*F(p[0],p[2]) for p in core['points'])
    lines.append(primitive((-sigma,1,height)))
    count = len(arrangement(lines)['triangles'])
    expected = q*q//3+q+1
    if count != expected:
        raise RuntimeError(f'Extension count {count} != {expected}')
    return dict(n=len(lines),triangle_count=count,t=t,
                underlying_construction='Parpalak-Utkin even draft; BBL doubling',
                extension='y = x/1000000 + H, H = 1 + max_vertex(y-x/1000000)',
                declared_parallel_pairs=[],
                lines_frac=[[str(x) for x in line] for line in lines])

if __name__ == '__main__':
    t = int(sys.argv[1])
    path = Path(sys.argv[2])
    data = construct(t,int(sys.argv[3]) if len(sys.argv)>3 else 100)
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,indent=2)+'\n')
    print(f'Wrote {path}: {data["n"]} lines, {data["triangle_count"]} triangles')
