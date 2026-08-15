# Conditioning validation

## Scope and provenance

The supplementary five case reproduction and corpus survey pin PowerIO 0.7.3 at commit
`f0b79d78`. The
survey covers 66 canonical PGLib
v23.07 cases, both supplied PGLib variants for each case, and 12 cases from
ACTIVSg, PERFORM, RTS-GMLC, CATS, UIUC, Hawaii, and the Australian corpus.
Case data is read from `/path/to/datasets`; result files store relative paths
and SHA-256 hashes rather than machine specific paths.

The structural graph is the largest connected component of the active branch
topology after self loops and parallel copies are removed. The output records
the original bus and branch counts, component count, and excluded buses. This
reduction matches the finite graph invariants in the formal model, but it does not
by itself validate the positive susceptance or bounded weight ratio
assumptions.

## Five case reproduction

The hardened runner reproduces every published structural value:

| Case | Buses | Separator `s` | Treewidth upper bound `U` | Drawing crossings |
|---|---:|---:|---:|---:|
| Texas7k | 6,717 | 26 | 46 | 5,416 |
| PEGASE13k | 13,659 | 15 | 34 | 31,511 |
| Midwest24k | 23,643 | 51 | 82 | 17,734 |
| GOC30k | 30,000 | 33 | 67 | 17,584 |
| EPIGRIDS78k | 78,478 | 57 | 108 | 108,940 |

All five graphs are nonplanar. Each stored drawing passes
`1152 * (n + crossings) <= n^2`, each separator has `beta >= 1/4` and
`s^2 <= 8n`, and each validated tree decomposition has
`4 * (U + 1) <= n`. EPIGRIDS78k has seven components; the result excludes six
isolated buses and reports that choice.

The positive edge weight assumption fails for two table cases under the
direct series model `b_e = 1/x_e`: PEGASE13k has 16 active negative reactances
and Midwest24k has 279. Texas7k, GOC30k, and EPIGRIDS78k have none. The table
therefore certifies the three structural conditions on all five cases, not
all hypotheses needed to apply the positive weighted Laplacian theorem to the
unmodified case data.

## Corpus results

`experiments/results/corpus-survey.json` and its validator report:

- 78 primary cases completed with no case failure.
- All 66 canonical PGLib cases and all 132 `api` and `sad` files parsed. Every
  PGLib variant had the same retained buses and simple edge set as its
  canonical case.
- Nine graphs are planar.
- The deterministic METIS certificate meets the stated separator threshold
  in 73 cases. The five failed certificates are RTE 1888, RTE 1951, RTE 2848,
  RTE 2868, and `case3375wp`; a failed heuristic certificate does not prove
  that no qualifying separator exists.
- The validated AMD tree decomposition meets the stated finite treewidth
  threshold in 76 cases. Only the 3-bus and 5-bus cases fail the numerical
  threshold, both with `U = 2`.
- A drawing certificate was attempted for all 51 cases with at least 1,152
  retained buses. Forty-four pass. Each of the seven stopped failures exceeded
  its crossing allowance by one, which proves only that the tested drawing
  fails. ACTIVSg2000 is the sole large case with complete bus coordinates and
  uses its AUX geography; its geographic drawing fails the threshold. PWD
  display files were parsed for seven case groups but do not expose a complete
  bus coordinate join through PowerIO.
- The direct positive series model is usable without modification in 56
  cases. Twenty-two cases contain at least one active nonpositive or nonfinite
  reactance and are excluded from weighted and spectral conclusions.
- The Proposition 3 survey computes spectra for 45 cases with residuals below
  `1e-7`; 11 cases exceed its 8,000 bus limit and 22 fail the weight model.
  Every computed condition estimate exceeds both independently calculated
  theorem lower bounds. The largest estimate is `3.393767e6`; the median ratio
  of the estimate to the exact cut lower bound is `21.75`. These are cross
  sectional results, not a fitted growth law.

Within the 66 canonical PGLib cases, 61 separator certificates and 64 treewidth certificates meet
the stated thresholds. Nine are exactly planar, while 39 of the 45 cases requiring a drawing test
meet the near planar threshold. The direct positive susceptance model is usable in 46 cases, and
all 46 of those cases also pass the separator certificate. The recorded operating point diagnostic
passes in 35 of the 36 PGLib cases for which it is computed. These results measure applicability;
they do not replace the theorem premises or prove a growth law.

## Cross format findings

Topology hashes use original bus identifiers and exact simple edge sets.
Nineteen non-PGLib comparisons produced eight discrepancies:

- ACTIVSg200 AUX has edge `64--82` that is absent from both RAW and MATPOWER.
- ACTIVSg500 AUX has edges `143--247` and `247--401` that are absent from both
  RAW and MATPOWER.
- The Midwest24k RAW parser rejects a shunt referring to unknown bus `141192`;
  its AUX and MATPOWER topologies match.
- Texas7k-2030 RAW and MATPOWER retain bus `61`, while AUX excludes it from
  the largest component and uses bus `62` for three corresponding edges.
- The CATS archive file is a different vintage: it has 8,848 buses versus
  8,870 in the primary file and is not a format equivalent.

These differences make the case filename and hash part of any reproducible
claim. Substituting a different format or archived file can change the graph.

## Trust checks

The experiment does not trust solver status alone:

- Source hashes, graph counts, and expected certificate values are regression
  checked before a core result is accepted.
- PowerIO's imported version must match the checked out tagged commit and the
  source tree must have no tracked changes.
- Planarity uses NetworkX's exact combinatorial decision.
- A separator is checked for disjoint cover, balance, and absence of every
  `A--B` edge. The edge cut is recomputed from membership because METIS can
  return an overflowed negative objective on valid partitions.
- Every tree decomposition is checked for vertex coverage, edge coverage, and
  running intersection.
- Crossing candidates come from outward rounded float bounding boxes, but
  every segment relation is decided with exact integer orientation tests.
- The sparse spectrum shifts the known constant nullspace, uses fixed seeded
  generic starts, and checks the null, `lambda2`, and largest eigenpair
  residuals. A regression test compares dense and sparse implementations; it
  prevents a symmetric start from being orthogonal to the requested path
  eigenvector while returning a small residual for a different eigenpair.
- `validate_survey.py` recomputes every reported verdict and checks that the
  spectral estimates dominate the two theorem bounds.

The unit suite contains 73 tests. It covers malformed separator partitions,
METIS objective overflow, tree decomposition failures, degenerate segment
relations, coordinates beyond exact float integer range, graph normalization,
reactance signs, parallel branch aggregation, topology hashes, geographic
coverage, PGLib discovery, nullspace removal, table byte reproduction,
effective conditioning, repeated eigenvalues, disconnected matrices,
headroom extraction, relabeling, uniform scaling, restricted singular vector
reconstruction, and hard pair support.

## Reproduction

From the repository root:

```sh
experiments/run.sh /path/to/powerio-v0.7.3 /path/to/datasets publication
experiments/.venv/bin/python experiments/validate_survey.py \
  experiments/results/corpus-survey.json \
  --publication \
  --core-input experiments/results.json \
  --summary-output experiments/results/corpus-summary.json \
  --table-output experiments/results/corpus-summary.tex \
  --compressed-output experiments/results/corpus-survey.json.gz \
  --sha256-output experiments/results/corpus-survey.json.gz.sha256 \
  --check-derived
experiments/.venv/bin/python -m pytest -q experiments/tests
```

Publication mode writes all retained outputs transactionally after validation. The final command
also checks that the readable summary, TeX table, deterministic gzip, and SHA-256 file are exact
derivatives of the retained survey JSON.

## Next experiments

1. Specify the exact DCPF matrix extraction for transformers, taps, phase
   shifters, and series compensated negative reactances. Cross check it against
   a second power flow implementation before making weighted claims on the 22
   excluded cases.
2. Compute grounded matrix condition estimates for every plausible slack bus
   and compare them with the original letter's trace correction and Poincare
   separation claim.
3. Add interval certified eigenvalue bounds for selected cases so the
   numerical comparison does not depend only on residual based estimates.
4. Run several separator algorithms and seeds, then report success rates and
   the best verified certificate. The current failures are algorithm failures,
   not graph lower bounds.
5. Detect induced transfer corridors explicitly and compare the corridor
   bound with the exact cut bound and spectral estimate.
6. Build controlled graph families by scaling a fixed construction. That
   tests asymptotic exponents more directly than a regression across unrelated
   cases.
7. Join PWD substations and AUX bus to substation assignments when available,
   then test geographic drawings without substituting a force directed layout.
8. Formalize the vertex cost form of Lipton--Tarjan used after planarization so
   balance is certified on original buses rather than crossing vertices.

## Proposition 3 operating point results

The schema version 2 survey extracts each base injection as generation minus
load and balances its recorded residual at the lowest numbered recorded
reference bus. It analyzes the full Laplacian on the balanced subspace. The
grounded slack choice is not used to define the primary condition.

Among 78 primary cases, 44 base injections pass
`kappa_eff(0.01) / kappa >= 1/2` and one fails. Three of 45 computed generator
subspaces and 13 of 22 computed generator plus load subspaces pass
`kappa_S / kappa >= 1/2`. All 45 computed operating points have a nonzero
local bus or active branch observable witness. A nonzero witness supports a
precision scaled theorem; it does not give a uniform constant precision
corollary.

All 132 PGLib API/SAD variants receive separate injection and headroom
analysis. Seventy-two use a computed canonical topology spectrum: 71 base
injections, 6 generator subspaces, and 22 generator plus load subspaces pass.
The remaining 60 are indeterminate because their canonical topology fails the
positive weight model or exceeds the spectral size limit.

Grounded condition numbers are a separate sensitivity diagnostic. The survey
computes the recorded reference bus grounding in 27 primary cases and marks 18
computed balanced cases indeterminate under a 2,500-bus grounded size limit.
The grounded to balanced condition ratio ranges from `1.18` to `10.5`; it is
not used in the base or admissible subspace pass criteria.

`pass` and `fail` below refer to the factor one half thresholds. `indet` means
the case exceeded a declared numerical size limit. `--` means the positive
weight model does not apply or no spectral analysis was available. The local
gap is divided by the observable operator norm.

| Case | n | Positive weights | Base RHS | G ratio | G+L ratio | Best local gap |
|---|---:|:---:|:---:|---:|---:|---:|
| `pglib_opf_case10000_goc` | 10,000 | yes | -- | -- | -- | -- |
| `pglib_opf_case10192_epigrids` | 10,189 | yes | -- | -- | -- | -- |
| `pglib_opf_case10480_goc` | 10,480 | yes | -- | -- | -- | -- |
| `pglib_opf_case118_ieee` | 118 | yes | pass | 0.0506 (fail) | 0.485 (fail) | 0.0442 |
| `pglib_opf_case1354_pegase` | 1,354 | yes | pass | 0.161 (fail) | indet | 0.0347 |
| `pglib_opf_case13659_pegase` | 13,659 | no | -- | -- | -- | -- |
| `pglib_opf_case14_ieee` | 14 | yes | pass | 0.0332 (fail) | 0.965 (pass) | 1.68 |
| `pglib_opf_case162_ieee_dtc` | 162 | yes | pass | 0.00725 (fail) | 0.142 (fail) | 0.119 |
| `pglib_opf_case179_goc` | 179 | yes | pass | 0.00346 (fail) | 0.0673 (fail) | 0.201 |
| `pglib_opf_case1803_snem` | 1,803 | no | -- | -- | -- | -- |
| `pglib_opf_case1888_rte` | 1,888 | no | -- | -- | -- | -- |
| `pglib_opf_case19402_goc` | 19,402 | yes | -- | -- | -- | -- |
| `pglib_opf_case1951_rte` | 1,951 | no | -- | -- | -- | -- |
| `pglib_opf_case197_snem` | 197 | yes | pass | 0.0176 (fail) | 0.0893 (fail) | 0.0453 |
| `pglib_opf_case2000_goc` | 2,000 | yes | pass | 0.0156 (fail) | indet | 0.049 |
| `pglib_opf_case200_activ` | 200 | yes | pass | 0.02 (fail) | 0.425 (fail) | 0.0344 |
| `pglib_opf_case20758_epigrids` | 20,758 | yes | -- | -- | -- | -- |
| `pglib_opf_case2312_goc` | 2,312 | yes | pass | 0.103 (fail) | indet | 0.024 |
| `pglib_opf_case2383wp_k` | 2,383 | yes | pass | 0.351 (fail) | indet | 0.0142 |
| `pglib_opf_case240_pserc` | 240 | no | -- | -- | -- | -- |
| `pglib_opf_case24464_goc` | 24,464 | yes | -- | -- | -- | -- |
| `pglib_opf_case24_ieee_rts` | 24 | yes | pass | 0.623 (pass) | 0.918 (pass) | 0.383 |
| `pglib_opf_case2736sp_k` | 2,736 | yes | pass | 0.1 (fail) | indet | 0.013 |
| `pglib_opf_case2737sop_k` | 2,737 | yes | pass | 0.0792 (fail) | indet | 0.0149 |
| `pglib_opf_case2742_goc` | 2,742 | yes | pass | 0.0526 (fail) | indet | 0.0126 |
| `pglib_opf_case2746wop_k` | 2,746 | yes | pass | 0.0337 (fail) | indet | 0.0698 |
| `pglib_opf_case2746wp_k` | 2,746 | yes | pass | 0.0392 (fail) | indet | 0.0636 |
| `pglib_opf_case2848_rte` | 2,848 | no | -- | -- | -- | -- |
| `pglib_opf_case2853_sdet` | 2,853 | no | -- | -- | -- | -- |
| `pglib_opf_case2868_rte` | 2,868 | no | -- | -- | -- | -- |
| `pglib_opf_case2869_pegase` | 2,869 | yes | pass | 0.135 (fail) | indet | 0.0458 |
| `pglib_opf_case30000_goc` | 30,000 | yes | -- | -- | -- | -- |
| `pglib_opf_case300_ieee` | 300 | no | -- | -- | -- | -- |
| `pglib_opf_case3012wp_k` | 3,012 | no | -- | -- | -- | -- |
| `pglib_opf_case3022_goc` | 3,022 | yes | pass | 0.0653 (fail) | indet | 0.0176 |
| `pglib_opf_case30_as` | 30 | yes | pass | 0.112 (fail) | 0.578 (pass) | 0.445 |
| `pglib_opf_case30_ieee` | 30 | yes | pass | 0.0069 (fail) | 0.573 (pass) | 1.6 |
| `pglib_opf_case3120sp_k` | 3,120 | no | -- | -- | -- | -- |
| `pglib_opf_case3375wp_k` | 3,374 | no | -- | -- | -- | -- |
| `pglib_opf_case3970_goc` | 3,970 | yes | pass | 0.186 (fail) | indet | 0.0108 |
| `pglib_opf_case39_epri` | 39 | yes | pass | 0.0271 (fail) | 0.469 (fail) | 0.433 |
| `pglib_opf_case3_lmbd` | 3 | yes | pass | 0.806 (pass) | 1 (pass) | 1.99 |
| `pglib_opf_case4020_goc` | 4,020 | yes | pass | 0.0687 (fail) | indet | 0.00533 |
| `pglib_opf_case4601_goc` | 4,601 | yes | pass | 0.175 (fail) | indet | 0.00738 |
| `pglib_opf_case4619_goc` | 4,619 | yes | pass | 0.0159 (fail) | indet | 0.0284 |
| `pglib_opf_case4661_sdet` | 4,661 | no | -- | -- | -- | -- |
| `pglib_opf_case4837_goc` | 4,837 | yes | pass | 0.0141 (fail) | indet | 0.0152 |
| `pglib_opf_case4917_goc` | 4,917 | yes | pass | 0.084 (fail) | indet | 0.0236 |
| `pglib_opf_case500_goc` | 500 | yes | fail | 0.29 (fail) | 0.875 (pass) | 0.334 |
| `pglib_opf_case5658_epigrids` | 5,658 | yes | pass | 0.0438 (fail) | indet | 0.00317 |
| `pglib_opf_case57_ieee` | 57 | yes | pass | 0.00731 (fail) | 0.561 (pass) | 0.379 |
| `pglib_opf_case588_sdet` | 588 | no | -- | -- | -- | -- |
| `pglib_opf_case5_pjm` | 5 | yes | pass | 0.81 (pass) | 1 (pass) | 0.782 |
| `pglib_opf_case60_c` | 60 | no | -- | -- | -- | -- |
| `pglib_opf_case6468_rte` | 6,468 | no | -- | -- | -- | -- |
| `pglib_opf_case6470_rte` | 6,470 | no | -- | -- | -- | -- |
| `pglib_opf_case6495_rte` | 6,495 | no | -- | -- | -- | -- |
| `pglib_opf_case6515_rte` | 6,515 | no | -- | -- | -- | -- |
| `pglib_opf_case7336_epigrids` | 7,336 | yes | pass | 0.17 (fail) | indet | 0.0056 |
| `pglib_opf_case73_ieee_rts` | 73 | yes | pass | 0.382 (fail) | 0.665 (pass) | 0.0916 |
| `pglib_opf_case78484_epigrids` | 78,478 | yes | -- | -- | -- | -- |
| `pglib_opf_case793_goc` | 793 | yes | pass | 0.279 (fail) | 0.691 (pass) | 0.0167 |
| `pglib_opf_case8387_pegase` | 8,387 | yes | -- | -- | -- | -- |
| `pglib_opf_case89_pegase` | 89 | yes | pass | 0.0554 (fail) | 0.605 (pass) | 0.246 |
| `pglib_opf_case9241_pegase` | 9,241 | no | -- | -- | -- | -- |
| `pglib_opf_case9591_goc` | 9,591 | yes | -- | -- | -- | -- |
| `activsg200` | 200 | yes | pass | 0.00187 (fail) | 0.307 (fail) | 0.317 |
| `activsg500` | 500 | yes | pass | 0.000388 (fail) | 0.141 (fail) | 0.0355 |
| `activsg2000` | 2,000 | yes | pass | 0.0536 (fail) | indet | 0.0237 |
| `hawaii40` | 37 | yes | pass | 0.151 (fail) | 0.968 (pass) | 0.21 |
| `midwest24k_geo` | 23,643 | no | -- | -- | -- | -- |
| `texas7k_2021` | 6,717 | yes | pass | 0.00226 (fail) | indet | 0.0156 |
| `texas7k_2022` | 6,717 | yes | pass | 0.000731 (fail) | indet | 0.0189 |
| `texas7k_2030` | 7,131 | yes | pass | 0.00108 (fail) | indet | 0.0167 |
| `rts_gmlc` | 73 | yes | pass | 0.162 (fail) | 0.64 (pass) | 0.135 |
| `cats` | 8,870 | yes | -- | -- | -- | -- |
| `uiuc150` | 150 | yes | pass | 0.0399 (fail) | 0.424 (fail) | 0.0887 |
| `australian14gen` | 59 | no | -- | -- | -- | -- |
