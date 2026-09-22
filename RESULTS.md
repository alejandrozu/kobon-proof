# Verified result index

The strongest proved all-order function is `Universal.bound`: the maximum of
`G(n)=floor(n(n-3)/3)+1+(n mod 2)` for `n>=4` and the finite envelope below.
Use zero below three and one at three. The generic construction uses only
standard logical axioms; finite coordinate checks use native evaluation.

The table records the strongest **saved coordinate witnesses**, not an
exhaustive global record table or a list of original discoveries. Maiorana,
Parpalak–Utkin and earlier researchers retain attribution for their inputs.
The linked source certificates and evidence snapshots preserve provenance.
The OEIS column records the explicit table as observed on 20 September 2026;
an omitted entry is not evidence of novelty.

The corresponding aliases are `Results.best_classical_NNN` and
`Results.best_simple_NNN`. Historical `Results.classical_NNN` and
`Results.simple_NNN` still verify the earlier materialized 3–60 table, while
`Results.earlier_NNN` retains every inequality in the original inventory.
Consult [FORMALIZATION.md](FORMALIZATION.md), the
[cumulative review](research/six-hour-2026-09-21/RESEARCH_REVIEW.md), and
[build results](verification/lean-summary.json) for scope and verification.

| n | Saved simple bound | Saved classical bound | Explicit OEIS lower | Strongest classical coordinate witness |
|---:|---:|---:|---:|---|
| 3 | 1 | 1 | 1 | [coordinates](research/finite-table/classical-003.json) · [Lean](Kobon/Certificates/N003T00001H05c82de6.lean) |
| 4 | 2 | 2 | 2 | [coordinates](research/finite-table/classical-004.json) · [Lean](Kobon/Certificates/N004T00002H0e541bd5.lean) |
| 5 | 5 | 5 | 5 | [coordinates](research/finite-table/classical-005.json) · [Lean](Kobon/Certificates/N005T00005H948a0bdf.lean) |
| 6 | 7 | 7 | 7 | [coordinates](research/finite-table/classical-006.json) · [Lean](Kobon/Certificates/N006T00007H6ea9ebaa.lean) |
| 7 | 11 | 11 | 11 | [coordinates](research/finite-table/classical-007.json) · [Lean](Kobon/Certificates/N007T00011He6b9a626.lean) |
| 8 | 14 | 15 | 15 | [coordinates](research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-008.json) · [Lean](Kobon/Certificates/N008T00015Ha1380810.lean) |
| 9 | 21 | 21 | 21 | [coordinates](research/finite-table/classical-009.json) · [Lean](Kobon/Certificates/N009T00021H6ebbed82.lean) |
| 10 | 25 | 25 | 25 | [coordinates](research/finite-table/classical-010.json) · [Lean](Kobon/Certificates/N010T00025Hb767c427.lean) |
| 11 | 32 | 32 | 32 | [coordinates](research/finite-table/classical-011.json) · [Lean](Kobon/Certificates/N011T00032Hb955e7c9.lean) |
| 12 | 37 | 38 | 38 | [coordinates](research/finite-table/classical-012.json) · [Lean](Kobon/Certificates/N012T00038H38f69f38.lean) |
| 13 | 47 | 47 | 47 | [coordinates](research/finite-table/classical-013.json) · [Lean](Kobon/Certificates/N013T00047Hddec1f78.lean) |
| 14 | 53 | 54 | 54 | [coordinates](research/six-hour-2026-09-21/general-bounds/maiorana14/certificate-01.json) · [Lean](Kobon/Certificates/N014T00054Hd47aea63.lean) |
| 15 | 65 | 65 | 65 | [coordinates](research/finite-table/classical-015.json) · [Lean](Kobon/Certificates/N015T00065H4d3bf3b4.lean) |
| 16 | 72 | 72 | 72 | [coordinates](research/finite-table/classical-016.json) · [Lean](Kobon/Certificates/N016T00072H391cf79a.lean) |
| 17 | 85 | 85 | 85 | [coordinates](research/finite-table/classical-017.json) · [Lean](Kobon/Certificates/N017T00085H7cf3c061.lean) |
| 18 | 93 | 93 | 93 | [coordinates](research/finite-table/classical-018.json) · [Lean](Kobon/Certificates/N018T00093Hedb6246a.lean) |
| 19 | 107 | 107 | 107 | [coordinates](research/finite-table/classical-019.json) · [Lean](Kobon/Certificates/N019T00107Ha2f32bdb.lean) |
| 20 | 116 | 117 | 117 | [coordinates](research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-020.json) · [Lean](Kobon/Certificates/N020T00117H382171ac.lean) |
| 21 | 133 | 133 | 133 | [coordinates](research/finite-table/classical-021.json) · [Lean](Kobon/Certificates/N021T00133H36bae754.lean) |
| 22 | 143 | 143 | 143 | [coordinates](research/finite-table/classical-022.json) · [Lean](Kobon/Certificates/N022T00143H54396c64.lean) |
| 23 | 161 | 161 | 161 | [coordinates](research/finite-table/classical-023.json) · [Lean](Kobon/Certificates/N023T00161H969ad7d3.lean) |
| 24 | 172 | 172 | 172 | [coordinates](research/finite-table/classical-024.json) · [Lean](Kobon/Certificates/N024T00172He63e906b.lean) |
| 25 | 191 | 191 | 191 | [coordinates](research/finite-table/classical-025.json) · [Lean](Kobon/Certificates/N025T00191Hb568bffb.lean) |
| 26 | 203 | 204 | 204 | [coordinates](research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-026.json) · [Lean](Kobon/Certificates/N026T00204Hf71379c4.lean) |
| 27 | 225 | 225 | 225 | [coordinates](research/finite-table/classical-027.json) · [Lean](Kobon/Certificates/N027T00225H7d6ae9a0.lean) |
| 28 | 238 | 238 | 238 | [coordinates](research/finite-table/classical-028.json) · [Lean](Kobon/Certificates/N028T00238H56ef2acb.lean) |
| 29 | 261 | 261 | 261 | [coordinates](research/finite-table/classical-029.json) · [Lean](Kobon/Certificates/N029T00261Hd4805c25.lean) |
| 30 | 275 | 275 | 275 | [coordinates](research/finite-table/classical-030.json) · [Lean](Kobon/Certificates/N030T00275Hdcfe649a.lean) |
| 31 | 299 | 299 | 299 | [coordinates](research/finite-table/classical-031.json) · [Lean](Kobon/Certificates/N031T00299H70f23b94.lean) |
| 32 | 314 | 315 | 315 | [coordinates](research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-032.json) · [Lean](Kobon/Certificates/N032T00315H5914f2bb.lean) |
| 33 | 341 | 341 | 341 | [coordinates](research/finite-table/classical-033.json) · [Lean](Kobon/Certificates/N033T00341H95f3b770.lean) |
| 34 | 357 | 357 | 357 | [coordinates](research/finite-table/classical-034.json) · [Lean](Kobon/Certificates/N034T00357Hfbde0a76.lean) |
| 35 | 385 | 385 | 385 | [coordinates](research/finite-table/classical-035.json) · [Lean](Kobon/Certificates/N035T00385H9ee99af6.lean) |
| 36 | 402 | 402 | 402 | [coordinates](research/finite-table/classical-036.json) · [Lean](Kobon/Certificates/N036T00402H3fc01b7d.lean) |
| 37 | 431 | 431 | 431 | [coordinates](research/finite-table/classical-037.json) · [Lean](Kobon/Certificates/N037T00431H11f0bde7.lean) |
| 38 | 449 | 450 | 450 | [coordinates](research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-038.json) · [Lean](Kobon/Certificates/N038T00450H8ba2bdb1.lean) |
| 39 | 470 | 470 | — | [coordinates](research/six-hour-2026-09-21/certificates/n039.json) · [Lean](Kobon/Certificates/N039T00470H30caa6f7.lean) |
| 40 | 494 | 494 | — | [coordinates](research/finite-table/classical-040.json) · [Lean](Kobon/Certificates/N040T00494H785374ca.lean) |
| 41 | 533 | 533 | 533 | [coordinates](research/finite-table/classical-041.json) · [Lean](Kobon/Certificates/N041T00533H01e2ef66.lean) |
| 42 | 553 | 553 | 553 | [coordinates](research/finite-table/classical-042.json) · [Lean](Kobon/Certificates/N042T00553H2bdc9d67.lean) |
| 43 | 587 | 587 | 587 | [coordinates](research/finite-table/classical-043.json) · [Lean](Kobon/Certificates/N043T00587H861d8be2.lean) |
| 44 | 608 | 608 | — | [coordinates](research/finite-table/classical-044.json) · [Lean](Kobon/Certificates/N044T00608Hb5277675.lean) |
| 45 | 645 | 645 | 645 | [coordinates](research/finite-table/classical-045.json) · [Lean](Kobon/Certificates/N045T00645H3dc6e882.lean) |
| 46 | 667 | 667 | 667 | [coordinates](research/finite-table/classical-046.json) · [Lean](Kobon/Certificates/N046T00667H32b8ca2f.lean) |
| 47 | 691 | 691 | — | [coordinates](research/six-hour-2026-09-21/certificates/n047.json) · [Lean](Kobon/Certificates/N047T00691Hfac44af1.lean) |
| 48 | 721 | 721 | — | [coordinates](research/six-hour-2026-09-21/certificates/n048.json) · [Lean](Kobon/Certificates/N048T00721H2fb5ef0d.lean) |
| 49 | 767 | 767 | 767 | [coordinates](research/finite-table/classical-049.json) · [Lean](Kobon/Certificates/N049T00767H957e6f15.lean) |
| 50 | 791 | 792 | 792 | [coordinates](research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-050.json) · [Lean](Kobon/Certificates/N050T00792H3d40cb58.lean) |
| 51 | 818 | 818 | — | [coordinates](research/six-hour-2026-09-21/certificates/n051.json) · [Lean](Kobon/Certificates/N051T00818Hc18e1baf.lean) |
| 52 | 850 | 850 | — | [coordinates](research/finite-table/classical-052.json) · [Lean](Kobon/Certificates/N052T00850H4b0d823a.lean) |
| 53 | 885 | 885 | — | [coordinates](research/six-hour-2026-09-21/certificates/n053.json) · [Lean](Kobon/Certificates/N053T00885H6bc5b14d.lean) |
| 54 | 919 | 919 | — | [coordinates](research/six-hour-2026-09-21/certificates/n054.json) · [Lean](Kobon/Certificates/N054T00919Ha254c1b4.lean) |
| 55 | 955 | 955 | — | [coordinates](research/six-hour-2026-09-21/certificates/n055.json) · [Lean](Kobon/Certificates/N055T00955H202625a3.lean) |
| 56 | 990 | 990 | — | [coordinates](research/finite-table/classical-056.json) · [Lean](Kobon/Certificates/N056T00990Hde8a415c.lean) |
| 57 | 1045 | 1045 | — | [coordinates](research/finite-table/classical-057.json) · [Lean](Kobon/Certificates/N057T01045H9a1d337c.lean) |
| 58 | 1073 | 1073 | — | [coordinates](research/finite-table/classical-058.json) · [Lean](Kobon/Certificates/N058T01073Hd988db55.lean) |
| 59 | 1103 | 1103 | — | [coordinates](research/six-hour-2026-09-21/certificates/n059.json) · [Lean](Kobon/Certificates/N059T01103Hba482375.lean) |
| 60 | 1141 | 1141 | — | [coordinates](research/six-hour-2026-09-21/certificates/n060.json) · [Lean](Kobon/Certificates/N060T01141H9bc5096c.lean) |
| 65 | 1365 | 1365 | — | [coordinates](research/six-hour-2026-09-21/certificates/n065.json) · [Lean](Kobon/Certificates/N065T01365Hb1dcbeb4.lean) |
| 66 | 1397 | 1397 | — | [coordinates](research/six-hour-2026-09-21/certificates/n066.json) · [Lean](Kobon/Certificates/N066T01397H327ecbb9.lean) |
| 81 | 2132 | 2132 | — | [coordinates](research/kobon-hybrid/certificates/n081.json) · [Lean](Kobon/Certificates/N081T02132H7bc6b303.lean) |
| 82 | 2172 | 2172 | — | [coordinates](research/kobon-hybrid/certificates/n082.json) · [Lean](Kobon/Certificates/N082T02172Hd75c9101.lean) |
| 99 | 3170 | 3170 | — | [coordinates](research/six-hour-2026-09-21/certificates/n099.json) · [Lean](Kobon/Certificates/N099T03170Hea507e2d.lean) |
| 129 | 5461 | 5461 | — | [coordinates](research/six-hour-2026-09-21/certificates/n129.json) · [Lean](Kobon/Certificates/N129T05461H6dae0012.lean) |
| 130 | 5525 | 5525 | — | [coordinates](research/six-hour-2026-09-21/certificates/n130.json) · [Lean](Kobon/Certificates/N130T05525He0559b54.lean) |
| 161 | 8532 | 8532 | — | [coordinates](research/kobon-hybrid/certificates/n161.json) · [Lean](Kobon/Certificates/N161T08532H230691d5.lean) |
| 162 | 8612 | 8612 | — | [coordinates](research/kobon-hybrid/certificates/n162.json) · [Lean](Kobon/Certificates/N162T08612H1512e696.lean) |
| 195 | 12482 | 12482 | — | [coordinates](research/six-hour-2026-09-21/certificates/n195.json) · [Lean](Kobon/Certificates/N195T12482H5413dd7b.lean) |

The three earlier OEIS-attributed Zarzuelo values 28:238, 30:275 and 34:357
remain independently certified. Some newer values in this catalog reproduce
published nonsimple constructions; this improves the repository's coverage
without making them our numerical discoveries. Current upper bounds and
priority claims require the separate source and hypothesis audit.
