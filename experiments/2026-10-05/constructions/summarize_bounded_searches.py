from pathlib import Path
import json
R=Path.cwd();b=R/'research/openmath-seven-hour-2026-10-05/constructions';records=[]
for d in sorted(b.iterdir()):
 if not d.is_dir() or not (d.name.startswith('facet-reduced') or d.name.startswith('capcone-')):continue
 p=d/'search.json'
 if not p.exists():continue
 j=json.loads(p.read_text());rec={k:j[k] for k in ['best','best_combined','tested','accepted','visited','rays','events','failures','elapsed'] if k in j};rec.update(directory=d.name,scope='Bounded numerical proposals; crossed facets may repeat and are not unique cells')
 f=d/'final.json'
 if f.exists():rec['termination']=json.loads(f.read_text()).get('event','finished')
 else:rec['termination']='Stopped or pilot; final recorded checkpoint retained'
 records.append(rec)
report=dict(scope='Bounded saturated-axis searches. Floating discrepancies were rejected. No global ceiling is inferred.',verified_outcome='1190 triangles and29 visible pairs, exact whole actualtan60 box and completed Lean infinite even family',higher_proposals='No completed1191 or1190/30 certificate',runs=records,parametric_screens=dict(first_order_cases=16,second_order_cases=16,positive=0,interpretation='Numerical diagnostics only'),dual_cell=dict(n=41,axis=0,weights=11,epsilon_threshold=0.014015551084678267,exact_fraction_verified=True,generic_lean_separation='OpenMathParametricDual.no_budget compiled standard axioms',concrete_lean_replay='Pending, not promoted',scope='This exported normalized cell only'))
(b/'bounded-search-summary.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(runs=len(records),crossed_facet_events=sum(r.get('events',0) for r in records)),indent=2))
