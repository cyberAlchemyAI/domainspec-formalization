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

Validate if what we have here is solid math or just prose with math words. We are not mathematicians, just engineers with an itch for abstract thought, rigor and maybe a well calibrated intuition. We want your help to prove if we are wrong or not.

If the framework is sound, these are the open problems that remain:

- **[M2](GLOSSARY.md#3--internal-milestone-labels)** — Does a right adjoint to $\Delta$ exist at the schema level? Equivalently, is $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ representable for every $b$? This is the condition under which schema [residue](GLOSSARY.md#residue) is even well-defined.
- **[M6'](GLOSSARY.md#3--internal-milestone-labels)** — Does faithfulness of $\Delta$ force the instance-level unit $\eta^{\mathrm{ins}}_I$ to be pointwise monic for every $I$? (The strong form, M6, is already refuted — see `M6Counter.lean`.)
- **[M6-restricted](GLOSSARY.md#3--internal-milestone-labels)** — Does injectivity + faithfulness force an iso on a reflective subcategory of $\mathbf{Set}^{\mathcal{L}_1}$?

## What's here

**Core publication:**
- **[Fractal.lean](./lean-formalization/Fractal.lean)** — The core definition of a [fractal functor](GLOSSARY.md#fractal-functor): `F` is fractal if the unit of the canonical adjunction `Lan_F ⊣ F*` (between `C ⥤ Type v` and `D ⥤ Type v`) is componentwise monic. Three implications: `fractal_iff_lan_faithful` (fractal ↔ `Lan_F` faithful), `fractal_id` (the identity functor is fractal), and `fractal_of_fullyFaithful` (every fully-faithful functor is fractal).
- **[FractalOP.lean](./lean-formalization/FractalOP.lean)** — A four-level hierarchy of fractal notions, from weakest to strongest: `LanFaithful` (unit componentwise monic, equivalent to `Lan_F` faithful), `InstanceFractal` (unit componentwise iso — no spurious Skolem witnesses), `SchemaFractal` (unit of an explicit adjunction `F ⊣ G` is a natural iso), and `Fractal` (both schema and instance layers iso). The hierarchy makes the [M2 conjecture](GLOSSARY.md#3--internal-milestone-labels) precise: the schema-level adjunction is an explicit argument rather than a typeclass, so its existence is never silently assumed.
- **[M6Counter.lean](./lean-formalization/M6Counter.lean)** — Formal refutation of [M6](GLOSSARY.md#3--internal-milestone-labels) (strong): proof that schema-side discipline (injectivity + faithfulness on $\Delta$) does **not** propagate to [instance-side](GLOSSARY.md#compilation-and-contract) fidelity. The four-object counterexample, fully formalized in Lean 4. No `sorry`s.
- **[DomainSpec.lean](./lean-formalization/DomainSpec.lean)** — The full Lean 4 formalization: the two-layer [residue](GLOSSARY.md#residue) framework and open conjectures ([M2](GLOSSARY.md#3--internal-milestone-labels), [M6'](GLOSSARY.md#3--internal-milestone-labels), [M6-restricted](GLOSSARY.md#3--internal-milestone-labels)).

**Mathematical framework:**
- **[docs/domainspec-two-layer-framework.md](./docs/domainspec-two-layer-framework.md)** — The two-layer [residue](GLOSSARY.md#residue) formalization. Why [schema-level](GLOSSARY.md#compilation-and-contract) and [instance-level](GLOSSARY.md#compilation-and-contract) translation leaks exist independently, and what conjectures remain open.

**Background & context:**
- **[docs/meta-layers-reference.md](./docs/meta-layers-reference.md)** — The system-design framework that motivated this work. How the 7-layer model connects to the mathematical questions.

**Fractal visualization:**
- **[visualization/fractals.html](./visualization/fractals.html)** — A cool visualization.

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
