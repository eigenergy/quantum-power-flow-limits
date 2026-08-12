# Structural condition experiments

The runner parses the five power system cases used in `main_letter_v5.tex`
with PowerIO, reduces each in service branch topology to its largest connected
simple graph, and emits independently checked structural certificates.

Pass the PowerIO 0.7.3 checkout at the commit pinned in `publication.toml`:

```sh
experiments/run.sh /path/to/powerio-v0.7.3 /path/to/datasets core
```

The script builds a PowerIO wheel from the supplied source tree, installs it in
the locked experiment environment, and writes `results.json` and
`conditions_table.tex`. It does not copy or modify case data.

Every run requires Python 3.13.14, uv 0.12.3, Julia 1.12.6, and Graphviz
15.1.0. Put the matching `sfdp` first on `PATH`; `run.sh` rejects a different
Graphviz version before parsing case data. Python packages and source inputs
are pinned in `uv.lock` and `publication.toml`.

## Certificate semantics

- `Planar` is the exact planarity decision for the underlying simple graph.
- `Near planar` is checked only when a deterministic straight line drawing has
  a fully verified count `c_hat` of proper pairwise crossing events, with no
  self or triple crossing, satisfying
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

## Publication regeneration

The publication mode checks the pinned environment and input hashes before it
runs. It writes into a temporary directory and replaces the retained outputs
only after both files have been produced:

```sh
experiments/run.sh /path/to/powerio-v0.7.3 /path/to/datasets publication
```

Validate the retained policy and provenance without rerunning the cases:

```sh
experiments/.venv/bin/python experiments/publication_policy.py --check-files
```

Run the unit suite independently with:

```sh
experiments/.venv/bin/python -m pytest -q experiments/tests
```
