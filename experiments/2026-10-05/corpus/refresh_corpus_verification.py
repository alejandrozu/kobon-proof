"""Hash the corpus branch's completed Lean builds and exact external artifacts.

This manifest records evidence, not another trusted mathematical oracle. Each
external JSON retains its own hypotheses and trust boundary; numerical grid-fit
reports are listed separately from exact geometric computations.
"""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'research/openmath-seven-hour-2026-10-05/corpus'

def file_record(p):return dict(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(p.read_bytes()).hexdigest())

def main():
    builds=[]
    names_logs=[
      ('BBLTangent60Bounds','tangent60/build.log'),
      ('BBLRationalTangentBounds','tangent60/generic-build.log'),
      ('BBLTangent36Bounds','tangent36/build-v2.log'),
      ('OpenMathConstructionBooleanMemo','tangent60/memo-build.log'),
      ('OpenMathBoundarySampleExistence','sample-existence-build.log'),
      ('OpenMathBoundaryRootOrder','root-order-build.log'),
      ('OpenMathBoundaryDoubleCounting','double-counting-build-v2.log'),
      ('OpenMathBoundaryIntegerAveraging','integer-averaging-build-v2.log'),
      ('OpenMathIntegerSparseBoxes','integer-sparse-build.log'),
      ('OpenMathFourLineResolution','four-line-resolution-build-v4.log'),
      ('OpenMathSixLineResolution','six-line-resolution-build-v4.log'),
      ('OpenMathTranslationGerms','translation-germs-build-v2.log'),
      ('OpenMathTranslationCounting','translation-counting-build.log'),
      ('OpenMathTranslationRetention','translation-retention-build-v2.log'),
      ('OpenMathTripleBirth','triple-birth-build-v3.log'),
      ('OpenMathIsolatedTripleResolution','isolated-triple-resolution-build.log'),
      ('UpperOpenMathAntipodalAdjacency','antipodal-adjacency-build-v5.log'),
      ('UpperOpenMathAntipodalBalancedAdjacency','antipodal-balanced-build-v4.log'),
      ('UpperOpenMathAntipodalFullNeighborPair','antipodal-full-neighbor-pair-build-v4.log'),
      ('UpperOpenMathAntipodalConeIncidence','antipodal-cone-incidence-build-v3.log'),
      ('UpperOpenMathFullCoreSides','full-core-sides-build-v2.log'),
      ('UpperOpenMathOneCapThreeCore','one-cap-three-core-build.log'),
      ('UpperOpenMathOneCapThreeCoreDegree','one-cap-three-core-degree-build-v2.log'),
      ('UpperOpenMathAntipodalCenterUniqueness','antipodal-center-uniqueness-build-v2.log'),
      ('UpperOpenMathAntipodalSameNeighbors','antipodal-same-neighbors-build-v3.log'),
      ('UpperOpenMathCevianCrossing','cevian-crossing-build-v3.log'),
      ('UpperOpenMathQuadThreeBoundary','quad-three-boundary-build-v2.log'),
      ('UpperOpenMathAntipodalThreeNeighbors','antipodal-three-neighbors-build.log'),
      ('UpperOpenMathNonfullAntipodalRecipients','nonfull-antipodal-recipients-build-v2.log'),
      ('UpperOpenMathDoubleRecipientCurvature','double-recipient-curvature-build.log'),
      ('UpperOpenMathAnyChartMatching','any-chart-matching-build.log'),
      ('UpperOpenMathClosedDoubleRecipientCurvature','closed-double-recipient-build.log'),
      ('UpperOpenMathN13ExtractionHelpers','n13-extraction-helpers-build.log'),
      ('UpperOpenMathN13OrdinaryMiddle','n13-ordinary-middle-build.log'),
      ('UpperOpenMathN13OrdinaryActual','n13-ordinary-actual-build.log'),
      ('UpperOpenMathN12Recipient','n12-recipient-build.log'),
      ('UpperOpenMathN13ActualChart','coordinated-builds/n13-actual-chart.log'),
      ('UpperOpenMathN13ActualNoDouble','coordinated-builds/n13-actual-no-double.log'),
      ('UpperOpenMathN13Degree','coordinated-builds/n13-degree.log'),
      ('UpperOpenMathN13Curvature','coordinated-builds/n13-curvature.log'),
      ('UpperOpenMathN12Curvature','coordinated-builds/n12-curvature.log'),
      ('UpperOpenMathClosedN12Curvature','coordinated-builds/closed-n12-curvature.log'),
    ]
    for name,logrel in names_logs:
        p=ROOT/f'Kobon/{name}.lean';log=BASE/logrel;source=p.read_text(encoding='utf-8');text=log.read_text(encoding='utf-8')
        assert not re.search(r'\b(sorry|admit|axiom)\b',source.replace('#print axioms',''))
        assert 'sorryAx' not in text and ': error:' not in text and ': error(' not in text
        assert '[propext' in text and 'Lean.ofReduceBool' not in text
        builds.append(dict(source=str(p.relative_to(ROOT)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),log=str(log.relative_to(ROOT)),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),completed=True,trust='standard logical axioms only; selected declarations printed in log',theorem_declarations=len(re.findall(r'^theorem ',source,re.M))))
    exact=[]
    for p in sorted(BASE.rglob('*.json')):
        if p.name in ['VERIFICATION.json','bounds.json'] or 'fp-projective-charts' in p.parts:continue
        exact.append(file_record(p))
    numeric=[]
    for rel in ['optimal31-bbl-axes/report.json','optimal31-projective-charts/report.json','forge31-leading-fit/report.json','contestant-general-axes/report.json','contestant-finite-epsilon/report.json','dual-mutation53/report.json']:
        p=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search'/rel
        if p.exists():numeric.append(file_record(p))
    for p in sorted((BASE/'fp-projective-charts').glob('*.json')):numeric.append(file_record(p))
    result=dict(recorded_at=datetime.now(timezone.utc).isoformat(),lean_builds=builds,total_theorem_declarations=sum(b['theorem_declarations'] for b in builds),external_exact_artifact_hashes=exact,numerical_search_diagnostics=numeric,scope='Completed branch builds and artifact identities; consult each artifact for exact scope. Numerical searches do not prove infeasibility, and no concrete lower-bound family is inferred from them.')
    (BASE/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(builds=len(builds),theorems=result['total_theorem_declarations'],external_artifacts=len(exact),numerical_reports=len(numeric))))

if __name__=='__main__':main()
