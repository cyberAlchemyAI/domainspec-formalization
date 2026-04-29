---
id: root
title: DomainSpec Theorem
kind: meta
status: conjectural
authors: [Boscaro, Rondelli]
created: 2026-04-25
updated: 2026-04-29
edges: []
---

# DomainSpec Theorem

A formal mathematical framework for understanding information preservation in compilation and translation.

## Origin

We started by building a system framework to help understand how systems explain themselves — a 7-layer model from domain through code to governance. The key insight: the **compilation step** from domain formalization (L1) to code (L2) is where information leaks.

Every translation has [residue](GLOSSARY.md#residue): what cannot be fully expressed in the target representation. *What if some translations have zero [residue](GLOSSARY.md#residue)?*

That question led to a formal mathematical model. A functor $\Delta : L_1 \to L_2$ is called **[fractal](GLOSSARY.md#fractal-functor)** if the compilation preserves all information — at both the [schema level](GLOSSARY.md#compilation-and-contract) (types) and the [instance level](GLOSSARY.md#compilation-and-contract) (data). This repository contains the framework and proofs about fractals.

## Goal

Validate if what we have here is solid math or just prose with math words. We are not mathematicians, just engineers with an itch for abstract thought, rigor and maybe a well calibrated intuiton. We want your help to prove if we are wrong or not. If not, then we have a proposal 

## What's here

**Core publication:**
- **[Fractal.lean](./lean-formalization/Fractal.lean)** — A four-level hierarchy of [fractal functors](GLOSSARY.md#fractal-functor): `LanFaithful` ([instance-level](GLOSSARY.md#compilation-and-contract) mono; equivalent to `Lan_F` faithful), `InstanceFractal` ([instance-level](GLOSSARY.md#compilation-and-contract) iso), `SchemaFractal` (unit of an explicit adjunction `F ⊣ G` is a natural iso; existence of that adjunction is the [M2](GLOSSARY.md#3--internal-milestone-labels) conjecture), and `Fractal` (both layers). ~15 theorems establish that identity and fully-faithful functors satisfy all four levels, and that categorical equivalences yield full fractals.
- **[M6Counter.lean](./lean-formalization/M6Counter.lean)** — Formal refutation of [M6](GLOSSARY.md#3--internal-milestone-labels) (strong): proof that schema-side discipline (injectivity + faithfulness on $\Delta$) does **not** propagate to [instance-side](GLOSSARY.md#compilation-and-contract) fidelity. The four-object counterexample, fully formalized in Lean 4. No `sorry`s.
- **[DomainSpec.lean](./lean-formalization/DomainSpec.lean)** — The full Lean 4 formalization: the two-layer [residue](GLOSSARY.md#residue) framework and open conjectures ([M2](GLOSSARY.md#3--internal-milestone-labels), [M6'](GLOSSARY.md#3--internal-milestone-labels), [M6-restricted](GLOSSARY.md#3--internal-milestone-labels)).

**Mathematical framework:**
- **[docs/domainspec-two-layer-framework.md](./docs/domainspec-two-layer-framework.md)** — The two-layer [residue](GLOSSARY.md#residue) formalization. Why [schema-level](GLOSSARY.md#compilation-and-contract) and [instance-level](GLOSSARY.md#compilation-and-contract) translation leaks exist independently, and what conjectures remain open.

**Background & context:**
- **[docs/meta-layers-reference.md](./docs/meta-layers-reference.md)** — The system-design framework that motivated this work. How the 7-layer model connects to the mathematical questions.

## Building

```bash
cd lean-formalization
lake build
```

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

## Authors

Victor Boscaro & Vladimir Rondelli

## License

Code under [Apache 2.0](./LICENSE). Prose under [CC BY 4.0](./LICENSE-PROSE).
