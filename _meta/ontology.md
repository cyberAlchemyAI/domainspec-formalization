---
id: ontology
ontology_version: 0.1.0
status: conjectural
created: 2026-04-25
updated: 2026-04-25
node_kinds:
  theorem:    {description: "A formally provable claim"}
  claim:      {description: "A stated assertion, not yet formally proved"}
  conjecture: {description: "A claim believed true but unproved"}
  question:   {description: "An open problem"}
  axiom:      {description: "Taken without proof, by choice"}
  definition: {description: "A precise stipulation of meaning"}
  example:    {description: "An instance of another node"}
  meta:       {description: "About the framework itself"}
statuses:
  draft:       {description: "Work in progress, not yet a public claim"}
  conjectural: {description: "Stated, believed, unproved. Default."}
  proved:      {description: "Formally proved. Requires proof attachment."}
  refuted:     {description: "Disproved. Kept for honesty, never deleted."}
  accepted:    {description: "For axioms only. Taken without proof, by choice."}
  deprecated:  {description: "Superseded by another Node via supersedes edge."}
edge_types:
  depends_on:   {sources: [theorem, claim, conjecture, question], targets: [theorem, claim, axiom, definition], description: "Source uses target as a premise."}
  refines:      {sources: ["*"], targets: ["*"], description: "Source is a more precise version of target."}
  contradicts:  {sources: [claim, theorem], targets: [claim, theorem, conjecture], description: "Source explicitly challenges target."}
  instantiates: {sources: [example, meta], targets: [theorem, claim, definition, conjecture], description: "Source is an instance of target."}
  proves:       {sources: [theorem], targets: [conjecture, claim], description: "Source is a proof of target."}
  conjectures:  {sources: [conjecture], targets: [claim, theorem], description: "Source proposes target as conjectural."}
  supersedes:   {sources: ["*"], targets: ["*"], description: "Source replaces target. Target must move to status: deprecated."}
---

# Ontology v0.1

The schema for what may exist in this repository. **Itself conjectural** — the version history of this file (`ontology-history.md`) is evidence for or against the meta-conjecture that the proposed vocabulary is sufficient.

The canonical schema lives in this file's frontmatter above. The validator parses the frontmatter directly. The prose below is documentation, not source of truth.

## Node kinds (8)

- `theorem` — a formally provable claim. May attach a proof file when status is `proved`.
- `claim` — a stated assertion, not yet formally proved.
- `conjecture` — a claim believed true but unproved.
- `question` — an open problem.
- `axiom` — taken without proof, by choice. Status is `accepted`.
- `definition` — a precise stipulation of meaning.
- `example` — an instance of another node.
- `meta` — about the framework itself.

**Not included, deliberately:** `philosophical`. Same trap as `relates_to` — it would absorb claims that should be decomposed into precise atoms. Philosophical content is a *tree* of definitions, claims, conjectures, and questions, not a single fuzzy kind.

## Statuses (6)

Default for any new Node: `conjectural`.

- `draft` — work in progress, not a public claim yet.
- `conjectural` — stated, believed, unproved.
- `proved` — formally proved. Requires a proof attachment.
- `refuted` — disproved. Kept for honesty, never deleted.
- `accepted` — for `kind: axiom` only.
- `deprecated` — superseded; target of a `supersedes` edge from another Node.

**Not included, deliberately:** `stable`. In a repository where everything is conjectural, "stable" is a category error. Removed.

## Edge types (7)

- `depends_on` — source uses target as a premise.
- `refines` — source is a more precise version of target.
- `contradicts` — source explicitly challenges target.
- `instantiates` — source is an instance of target.
- `proves` — source is a proof of target.
- `conjectures` — source proposes target as conjectural.
- `supersedes` — source replaces target. Target must move to `status: deprecated`.

**Not included, deliberately:** `relates_to`. This is the junk drawer that destroys ontologies. The moment it exists, every author who hasn't yet decomposed their thinking reaches for it instead of picking the precise type. If two Nodes feel related but no precise edge type fits, the relationship is not yet rigorous — it belongs in `_residue/`, not as an edge.

Edges are declared on the **source** Node only. The inverse graph is computed by the explorer, never authored.

Edges support an optional `note` (free text). No other edge metadata. No `confidence`, no `weight`. Adding numeric properties later requires a major ontology version bump.

## Frontmatter schema

Every Node `README.md` must begin with:

```yaml
---
id: stable-slug-never-changes
title: Human-readable title
kind: <one of node_kinds>
status: <one of statuses>
authors: [Boscaro, Rondelli]
created: YYYY-MM-DD
updated: YYYY-MM-DD
edges:
  - type: <one of edge_types>
    target: <existing node id>
    note: <optional free text>
---
```

## Versioning

The ontology is versioned (semver). Breaking changes (removing a kind, removing an edge type, narrowing source/target rules) require:

1. Bump `ontology_version`.
2. Append an entry to `ontology-history.md` with the rationale.
3. Migrate all affected Nodes in the same commit.

The validator refuses to run if any Node references a kind, status, or edge type not in the current ontology.
