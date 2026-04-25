# Contributing

This repository is an experiment, not a software project. Contributions follow the One Rule.

## The One Rule

> Every directory whose name does not start with `_` is a Node. Every Node has the same shape. No exceptions.

See `_meta/RULE.md` for the full statement and `_meta/ontology.md` for the schema.

## Before you commit

Run the validator:

```bash
python _meta/validate.py
```

If it fails, the commit is wrong. Fix it.

## Adding a new Node

1. Decide where it goes. A new top-level concept goes in `children/`. A refinement of an existing concept goes in *that concept's* `children/`.
2. Create the directory: `children/.../my-new-node/`.
3. Create `README.md` with valid frontmatter (start with `status: conjectural` unless you have specific reason otherwise).
4. Create empty `children/`.
5. Run the validator.
6. Commit.

## Adding an idea that isn't ready to be a Node

Drop it in `_residue/capture/` with a date prefix. No structure required. Promote when it earns it.

## Modifying the ontology

The ontology itself is conjectural. Modifying it requires:

1. Bumping `ontology_version` in `_meta/ontology.md` (semver: major for breaking, minor for additive, patch for fixes).
2. Appending a record to `_meta/ontology-history.md` with the rationale — *what relationship the previous ontology could not express*.
3. Migrating all affected Nodes in the same commit.

If you find yourself wanting to add a `relates_to` edge type, stop. That edge type is the junk drawer that destroys ontologies. Either pick from the existing seven, or the relationship belongs in `_residue/`.

## Refuting a claim

If a claim turns out to be wrong, do not delete it. Change its `status` to `refuted` and add a short note explaining why. The repository's honesty is measured by what it has been willing to mark `refuted`.
