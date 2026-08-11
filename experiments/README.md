# Structural condition experiments

The runner parses each power system case with PowerIO, reduces the in service
branch topology to its largest connected simple graph, and emits independently
validated structural certificates.

The `core` mode reproduces the five structural rows. Pass the PowerIO 0.7.3
checkout at the commit pinned in `publication.toml`:

```sh
experiments/run.sh /path/to/powerio-v0.7.3 /path/to/datasets core
```

The script builds a [PowerIO](https://github.com/eigenergy/powerio) 0.7.3 wheel
from the supplied source tree, installs it in the locked experiment
environment, and writes `results.json` and `conditions_table.tex`. It does not
copy or modify any case data.

Every mode requires Python 3.13.14, uv 0.12.3, Julia 1.12.6, and Graphviz
15.1.0. Put the matching `sfdp` first on `PATH`; `run.sh` rejects a different
Graphviz version before parsing case data. Python packages and source inputs
are pinned in `uv.lock` and `publication.toml`.

## Certificate semantics

- `Planar` is the exact planarity decision for the underlying simple graph.
- `Near planar` is checked only when a deterministic straight line drawing has
  a fully verified crossing count `c_hat` satisfying
  `1152 * (n + c_hat) <= n^2`. Failure to find such a drawing is unavailable
  evidence, not a proof that no qualifying drawing exists.
- `Separator` is a PyMetis bisection converted into an `(s,beta)` vertex
  separation and checked edge by edge. The table requires `beta >= 1/4` and
  `s^2 <= 8n`.
- `Treewidth` is an AMD Cholesky completion converted into a tree decomposition.
  The Python validator checks vertex and edge coverage and running intersection.
  Its width `U` is a certified upper bound, and the table requires
  `4 * (U + 1) <= n`.

Parallel branches and self loops do not alter these graph invariants and are
collapsed. Original active branch counts remain in `results.json`. For a
disconnected case, the connected theorem is applied to the largest component;
excluded buses are reported explicitly.

Texas7k and Midwest24k are from the [Texas A&M ARPA-E PERFORM
collection](https://electricgrids.engr.tamu.edu/texas-am-perform-cases/).
PEGASE13k, GOC30k, and EPIGRIDS78k are the v23.07
[PGLib-OPF](https://github.com/power-grid-lib/pglib-opf) files named in
`cases.toml`. The manifest fixes the exact local filenames, and the output
records their SHA-256 hashes.

## Corpus survey

The `survey` mode writes `results/corpus-survey.json`:

```sh
experiments/run.sh /path/to/powerio-v0.7.3 /path/to/datasets survey
```

It analyzes all 66 canonical PGLib v23.07 cases and parses both `api` and
`sad` variants for topology comparison. `survey_cases.toml` adds ACTIVSg,
PERFORM, RTS-GMLC, CATS, UIUC, Hawaii, and Australian cases. When available,
the runner uses bus coordinates read from `.aux`, parses `.pwd` display files,
and compares `.raw` and MATPOWER topology. A failed comparison is recorded;
it is not silently treated as an equivalent case.

For positive series reactances, the survey builds the weighted Laplacian with
aggregated simple edge weights `b_e = 1/x_e`. It records the exact cut lower
bound and the separator counting lower bound. Sparse eigenvalue checks shift
the known constant nullspace before solving for `lambda2`, use a deterministic
start, and report residuals. Cases containing nonpositive or nonfinite
reactances remain in the structural survey but are marked unusable for this
weight model.

Near planarity results use four explicit statuses: `certificate-found`,
`threshold-exceeded`, `inapplicable-size`, and `unavailable`. Completed tests
retain their integer drawing coordinates and coordinate hash. An unavailable
test records its failure reason and is rejected by the publication gate for a
case with at least 1,152 retained buses.

## Publication run

The `publication` mode runs the five core cases and the full 78 case survey
with treewidth, near planarity, all 132 PGLib variants, and the fixed spectral
cutoff enabled:

```sh
experiments/run.sh /path/to/powerio-v0.7.3 /path/to/datasets publication
```

It writes a readable survey JSON, a deterministic gzip encoding, the gzip
SHA-256, a readable count summary, and a generated TeX count table. It then
regenerates those derived files in check mode and compares their bytes. The
outputs are moved into `experiments/results` only after the complete package
passes validation, so an interrupted run does not replace retained results.
The readable 50 MB JSON is a local regeneration product and is ignored by Git.
The repository retains the deterministic gzip, its checksum, and the two
summaries. The publication validator rejects disabled analyses, missing or
duplicate cases, null required results, absolute paths, timing and timestamp
fields, dirty PowerIO source, dependency version drift, Graphviz drift,
provenance hash drift, and unexpected denominators.

To validate the retained compressed artifact without rerunning the corpus:

```sh
artifact_json=$(mktemp)
trap 'rm -f "$artifact_json"' EXIT
(cd experiments/results && sha256sum --check corpus-survey.json.gz.sha256)
gzip --decompress --stdout experiments/results/corpus-survey.json.gz \
  > "$artifact_json"
experiments/.venv/bin/python experiments/validate_survey.py \
  "$artifact_json" \
  --publication \
  --core-input experiments/results.json \
  --summary-output experiments/results/corpus-summary.json \
  --table-output experiments/results/corpus-summary.tex \
  --compressed-output experiments/results/corpus-survey.json.gz \
  --sha256-output experiments/results/corpus-survey.json.gz.sha256 \
  --check-derived
```

The retained compressed survey is not promoted by changing metadata. A run
with disabled analyses or nondeterministic fields remains a smoke artifact and
must be replaced by a complete run.

Run the unit suite independently with:

```sh
experiments/.venv/bin/python -m pytest -q experiments/tests
```
