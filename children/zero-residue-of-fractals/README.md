---
id: zero-residue-of-fractals
title: Fractal structures exhibit zero residue under the Strict Regime
kind: conjecture
status: conjectural
authors: [Boscaro, Rondelli]
created: 2026-04-25
updated: 2026-04-25
edges: []
---

# Fractal structures exhibit zero residue under the Strict Regime

## Statement

A knowledge structure organized as a strict fractal — where every component shares an identical anatomy and recurses at every scale — produces no residue. That is: any concept expressible within the framework has exactly one valid location in the structure, and any location in the structure expects exactly one kind of concept. Structural ambiguity is eliminated by construction.

## Status

`conjectural`. No formal proof exists.

## Why this conjecture matters to this repository

This repository is the existence-proof attempt. It is itself organized as a strict fractal of Atomic Nodes. If the structure can absorb the accumulated DomainSpec material without breaking down — without authors reaching for ad-hoc folders, without ideas getting stuck in `_residue/`, without the validator failing — that is evidence in favor of the conjecture. If the structure breaks down at depth N, or if some category of idea cannot be expressed without violating the One Rule, that is data against it.

## What would refute this conjecture

Concrete failure modes that, if observed and documented, would falsify the conjecture and move this Node to `status: refuted`:

1. A legitimate concept emerges that cannot be expressed as a Node without violating the One Rule.
2. The promotion rate from `_residue/` to `children/` trends to zero — meaning ideas accumulate but cannot be made rigorous within the structure.
3. The ontology requires a `relates_to` edge type — meaning the typed graph has collapsed into an untyped one.
4. Path depth grows unbounded with no natural stopping point — meaning the recursion has no terminating condition.

Any of these, observed and documented, is sufficient.

## Open questions

These questions, when made into Nodes themselves, will live as children of this conjecture:

- Is there a formal proof in category theory or topos theory connecting fractal self-similarity to zero residue?
- Is "residue" itself a well-defined formal concept in the DomainSpec framework, or is it currently a metaphor that needs formalization?
- How is residue measured? The metrics in `_meta/RULE.md` are operational proxies; what is the underlying invariant they approximate?
- Is the Strict Regime a property of the structure, of the validator, or of the authors who keep choosing to honor it?

## Self-reference

The root Node of this repository (`/README.md`) declares an `instantiates` edge pointing here. The repository points at the conjecture it embodies. The fractal closes on itself. Whether that closure is virtuous (an existence proof) or vicious (a circular argument) is itself an open question.
