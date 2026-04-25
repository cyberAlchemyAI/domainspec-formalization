---
id: root
title: DomainSpec Theorem
kind: meta
status: conjectural
authors: [Boscaro, Rondelli]
created: 2026-04-25
updated: 2026-04-25
edges:
  - type: instantiates
    target: zero-residue-of-fractals
    note: "This repository is the existence-proof attempt for this conjecture."
---

# DomainSpec Theorem

This repository is an experiment.

It is structured as a fractal of Atomic Nodes because we conjecture that fractal structures exhibit zero residue under the Strict Regime. **We do not yet have a proof.** The repository is the existence-proof attempt: if the structure survives at scale, that is evidence for the conjecture; if it breaks down, that is data against it. Every claim in this repo, including this organizing principle, has status `conjectural` until formally proved.

## Authors

Victor Boscaro & Vladimir Rondelli.

## Status

- License: pending
- Citation: pending
- Visibility: private (will flip public once license + citation are finalized; that commit is the prior-art timestamp anchor)

## How to read this repository

The fractal begins at [`children/`](./children/). Every directory inside is a Node. Every Node has the same shape:

- `README.md` — frontmatter (machine-readable metadata) plus the human-readable claim
- `children/` — sub-Nodes (may be empty)
- Optional attachments (proofs, diagrams, data)

The single rule that governs the entire repository:

> **Every directory whose name does not start with `_` is a Node. Every Node has the same shape. No exceptions.**

See [`_meta/RULE.md`](./_meta/RULE.md) for the full statement, [`_meta/ontology.md`](./_meta/ontology.md) for the schema of allowed node kinds and edge types, and [`_meta/validate.py`](./_meta/validate.py) for the enforcement script.

## Sanctuaries (directories outside the fractal)

Directories prefixed with `_` are not Nodes. They are explicit escape valves:

- [`_residue/`](./_residue/) — the maturity funnel for ideas not yet rigorous enough to be Nodes
- [`_explorer/`](./_explorer/) — the visualization (the canonical reading interface; the file browser is the substrate, this is the lens)
- [`_meta/`](./_meta/) — repository governance: the rule, the ontology, the validator, contributing guide

## What "conjectural" means here

Everything in this repository has status `conjectural` by default. Some claims may be elevated to `proved` by attaching a formal proof; some may be marked `refuted` and kept for honesty; some may be `deprecated` and superseded by other Nodes. **Nothing is "stable"** — that word does not appear in the status taxonomy. The framework's honesty is measured by what it has been willing to mark `refuted`.

## The meta-conjecture

The first Node in this repository is the conjecture this repository tests:

[`children/zero-residue-of-fractals/`](./children/zero-residue-of-fractals/)

The repository points at the conjecture it embodies. The fractal closes on itself.
