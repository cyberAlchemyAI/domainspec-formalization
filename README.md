---
id: root
title: DomainSpec Theorem
kind: meta
status: conjectural
authors: [Boscaro, Rondelli]
created: 2026-04-25
updated: 2026-05-07
edges: []
---

# DomainSpec Theorem

Every translation leaves something behind. We're trying to find out when it doesn't.

## The itch

We started somewhere else — a system-design framework about how software explains itself, from domain down to code. When code is implemented from domain knowledge, information can leak. Two different domain entities can be merged into one. A business rule can be missed. A nuance the practitioners carry in their heads can fail to survive the trip into a schema. The compilation step — domain to code — is one of the places this happens, and it's the one we wanted to look at closely.

Every translation has [residue](GLOSSARY.md#residue) — what the target representation cannot hold. A simulation never recovers the world it models. A category collapses the variation inside its labels. A teacher passes on less than they know. A compiler keeps the type system honest and lets the data drift, or the other way around.

A [fractal](GLOSSARY.md#fractal-functor) is the exception. The translation from whole to part recovers the whole exactly. Residue zero. That is why fractals feel uncanny — they are the one case where nothing leaks.

So: *which translations are fractal?* That question turned into math, and the math turned into Lean.

## What we want from you

We are not mathematicians. We are engineers with an itch for abstract thought, some rigor, and maybe a well-calibrated intuition. We want to know whether what's here is solid math or prose dressed up in math words.

Tell us we're wrong. Or tell us we're not.

## What's here

- **The story** — [docs/domainspec-two-layer-framework.md](./docs/domainspec-two-layer-framework.md) is the long version: why translation leaks at two independent levels (the contract and the data), and what's still open.
- **Where it came from** — [docs/meta-layers-reference.md](./docs/meta-layers-reference.md) is the system-design framework that started this.
- **The proofs** — [lean-formalization/](./lean-formalization/) holds the Lean 4 formalization. The headline files are `Fractal.lean` (the core definition), `FractalOP.lean` (a four-level hierarchy from weakest to strongest), and the two refutations: `M2Counter.lean` and `M6Counter.lean`. Status of each open conjecture lives in the framework doc, not here.
- **A picture** — [visualization/fractals.html](./visualization/fractals.html). Because some of this is easier to see than to read.

## Building the Lean files

```bash
cd lean-formalization/files
lake build
```

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

## Authors

Victor Boscaro & Vladimir Rondelli — fifteen years of conversations about simulations, fractals, categorizations, and knowledge transfer, finally given a shape we could check.

## License

Code under [Apache 2.0](./LICENSE). Prose under [CC BY 4.0](./LICENSE-PROSE).
