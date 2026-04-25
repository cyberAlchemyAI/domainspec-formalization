# The One Rule

> **Every directory whose name does not start with `_` is a Node. Every Node has the same shape. No exceptions.**

That is the entire fractal invariant. The validator (`_meta/validate.py`) enforces it. If the rule cannot be stated in one sentence and enforced by one script, it is not a fractal — it is convention dressed up as one.

## Node anatomy

A Node is a directory containing exactly:

- `README.md` — REQUIRED. YAML frontmatter (per `ontology.md` schema) plus human-readable content.
- `children/` — REQUIRED. May be empty (empty = leaf Node).
- Optional attachments — any other files (e.g. `proof.lean`, `diagram.png`, `data.csv`).

Forbidden inside a Node directory:

- Subdirectories other than `children/` or `_*` (no ad-hoc categorization).
- More than one `README.md` (no `README-old.md`, no `NOTES.md` masquerading as a second README).

## Sanctuaries (`_`-prefixed directories)

Directories prefixed with `_` are explicitly outside the fractal. They are escape valves with their own internal organization:

- `_residue/` — ideas not yet rigorous enough to be Nodes (maturity funnel)
- `_explorer/` — visualization tooling
- `_meta/` — repository governance

The underscore is the visible signal that the Strict Regime does not apply inside.

## GitHub-mandated exceptions

Three files at the repository root exist because GitHub features depend on their location:

- `README.md` — the root Node's README, doubling as the GitHub project intro
- `LICENSE` — required for license detection
- `CITATION.cff` — required for the "Cite this repository" button

These are the only non-Node files allowed at the root. The validator hardcodes this exception. We document the exception here rather than hide it.

## Metrics

The repository's health is measured by:

| Metric | Definition | Healthy signal |
|---|---|---|
| Residue ratio | `count(Nodes) / count(_residue items)` | Grows over time |
| Promotion velocity | items moved residue → Node per month | > 0 |
| Mortality rate | items moved capture → archive vs capture → Node | < 50% |
| Status distribution | % per status across all Nodes | Visible % conjectural; > 0 refuted |
| Orphan count | Nodes with zero incoming edges | Trends to 0 |
| Max depth | deepest path in the fractal | Stable; sudden growth = candidate Node split |
| Dead refs | edges pointing to non-existent ids | Always 0 (validator enforces) |
| Edge type distribution | % of edges per type | All seven types in use; no type > 50% |
| Proof debt | `count(kind=theorem AND status=conjectural)` | Trends down; never zero (zero = nothing being attempted) |
| Refutation count | `count(status=refuted)` | > 0. Zero is suspicious — means nothing is being honestly tested. |

These are not vanity metrics. Each is a falsifiable claim about whether the framework is alive.
