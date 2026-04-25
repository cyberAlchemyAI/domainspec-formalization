# Ontology History

Every revision to `_meta/ontology.md` is recorded here. The history is itself evidence for or against the meta-conjecture: each entry represents a relationship the previous ontology could not express.

A growing history means the vocabulary was insufficient. A stable history means the vocabulary holds.

---

## v0.1.0 — 2026-04-25

Initial ontology.

- 8 node kinds: theorem, claim, conjecture, question, axiom, definition, example, meta
- 6 statuses: draft, conjectural, proved, refuted, accepted, deprecated
- 7 edge types: depends_on, refines, contradicts, instantiates, proves, conjectures, supersedes

**Deliberately excluded:**

- `philosophical` kind — would absorb decomposable claims.
- `stable` status — category error in a conjectural framework.
- `relates_to` edge type — junk drawer that destroys typed graphs.
- `confidence` / `weight` edge metadata — premature numericization.

These exclusions are themselves conjectures. If reality forces one of them in, the history will record why.
