---
tags: [lean4, formalization, framework, reference, category-theory, domainspec]
node_type: reference
status: current
nature: technical, reference
version: 1.0.0
last_updated: 2026-04-29
---

# From Math to Code: Reading the Lean Files

This document describes what lives in `Fractal.lean` and `DomainSpec.lean`. It assumes you've read the mathematical framework in [domainspec-two-layer-framework.md](./domainspec-two-layer-framework.md) but may not be familiar with Lean syntax. The goal is to map concepts to code and show the landscape you're entering.

---

## Overview

Two files, two purposes:

**`Fractal.lean`** — The proven kernel. Defines what a [fractal functor](../GLOSSARY.md#fractal-functor) is, gives an equivalent characterization (via faithfulness of the left Kan extension), and discharges two cases: the identity is [fractal](../GLOSSARY.md#fractal-functor), and every fully faithful functor is [fractal](../GLOSSARY.md#fractal-functor). Every claim discharged. No sorries.

**`DomainSpec.lean`** — The research landscape. The full two-layer [residue](../GLOSSARY.md#residue) framework formalized in Lean: all the definitions, assumptions, the free adjunctions that exist, and the conjectures still open. It shows where the results in `Fractal.lean` live, and what remains to be proved.

---

## `Fractal.lean` — The Proven Results

A [fractal functor](../GLOSSARY.md#fractal-functor) is defined simply: a functor $F : C \to D$ where the canonical adjunction $\mathrm{Lan}_F \dashv F^*$ between presheaf categories has a unit that is **componentwise monic** — no information loss in the round-trip.

### The definition

```
def Fractal (F : C ⥤ D) : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    Mono (((F.lanAdjunction (Type v)).unit.app X).app c)
```

This says: for every presheaf `X` and every object `c`, the unit of the left Kan extension is monic at that point. Monomorphism means no data collapses; what you push forward and pull back is preserved.

### The characterization and two cases

**Characterization — `fractal_iff_lan_faithful`**
A functor is [fractal](../GLOSSARY.md#fractal-functor) iff the left Kan extension functor itself is faithful. Two views of the same property.

**Identity case — `fractal_id`**
The identity functor is [fractal](../GLOSSARY.md#fractal-functor). Immediate: the identity's Kan extension is fully faithful (its unit is iso), so the unit is certainly monic.

**Fully faithful case — `fractal_of_fullyFaithful`**
Every fully faithful functor is [fractal](../GLOSSARY.md#fractal-functor). If `F` preserves all information at the morphism level (faithful) and reflects it back (full), then the data-level round-trip is lossless.

All three are discharged in full — no gaps, no `sorry`s. They are reference results: if your compiler is fully faithful, information preservation at the [instance level](../GLOSSARY.md#compilation-and-contract) is guaranteed.

---

## `DomainSpec.lean` — The Full Framework

This file formalizes the setting in which [fractals](../GLOSSARY.md#fractal-functor) make sense: the two-layer compilation model, the [schema-level](../GLOSSARY.md#compilation-and-contract) and [instance-level](../GLOSSARY.md#compilation-and-contract) adjunctions, and the conjectures linking them.

### Section 1: The carriers

**[Meta-types](../GLOSSARY.md#carrier-vocabulary):**
```
inductive MetaType | entity | operation | constraint | relationship
```
The four fundamental categories that classify objects in a domain ontology.

**Time track ([M4](../GLOSSARY.md#3--internal-milestone-labels)):**
```
variable {T : Type*} [SemilatticeSup T] [Category T]
variable (L1 L2 : T ⥤ Cat)
```
Compilation is temporally indexed: at each moment `t` in a join-semilattice of times, we have two categories — `L1.obj t` (the domain schema at time `t`) and `L2.obj t` (the code schema at time `t`).

**Typing:**
```
variable (τ : (t : T) → (L1.obj t) ⥤ Discrete MetaType)
```
At each time, objects in the domain are typed: each object `X` in `L1.obj t` receives a [meta-type](../GLOSSARY.md#carrier-vocabulary) (entity, operation, constraint, or relationship).

**The [edge law](../GLOSSARY.md#carrier-vocabulary):**
```
axiom EdgeLaw : MetaType → MetaType → Prop
```
Not every [meta-type](../GLOSSARY.md#carrier-vocabulary) can relate to every other. The [edge law](../GLOSSARY.md#carrier-vocabulary) is a decidable relation that governs valid morphisms.

### Section 2: Compilation at the schema level (M1, M3)

**The base compiler:**
```
variable (Δ_base : (t : T) → K ⥤ (L2.obj t))
variable (Δ : (t : T) → (L1.obj t) ⥤ (L2.obj t))
variable (α : (t : T) → Δ_base t ⟶ I t ⋙ Δ t)
variable [∀ t, (Δ t).IsLeftKanExtension (α t)]
```

The compiler `Δ` at each time is the **left Kan extension** of a base compiler `Δ_base` through a dense subcategory `K`. This formalization captures: compilation is the unique cocontinuous extension of a base functor.

**Injectivity and faithfulness ([M3](../GLOSSARY.md#3--internal-milestone-labels)):**
```
class IsInjectiveOnObjects (F : C ⥤ D) : Prop where
  inj_obj : ∀ X Y : C, F.obj X = F.obj Y → X = Y

variable [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]
```

We assume the compiler is injective on objects (distinct domain concepts map to distinct artifact types) and faithful (distinct domain morphisms map to distinct artifact morphisms). These are [M3](../GLOSSARY.md#3--internal-milestone-labels)'s assumptions.

**Compilation determinism — `T0'_C1`:**
```
theorem T0'_C1 (t : T) (g g' : L1.obj t) (h : g = g') :
    (Δ t).obj g = (Δ t).obj g'
```
If two objects are equal, their images under `Δ` are equal. A tautology, but formalized: compilation is deterministic. From functoriality.

### Section 3: Instance-level adjunctions (M5)

At the [instance level](../GLOSSARY.md#compilation-and-contract), we work with presheaves:
```
abbrev L1Instances (t : T) := (L1.obj t) ⥤ Type
abbrev L2Instances (t : T) := (L2.obj t) ⥤ Type
```

An instance category `L1Instances t` is the category of copresheaves on the domain — a mapping from domain objects to sets of concrete data.

**The precomposition functor:**
```
def Δ_pullback (t : T) : L2Instances L2 t ⥤ L1Instances L1 t :=
  (whiskeringLeft _ _ _).obj (Δ t)
```
Given compiled data (an `L2` instance), pull it back to the domain by precomposing with `Δ`.

**The Kan extensions ([M5](../GLOSSARY.md#3--internal-milestone-labels)):**
```
noncomputable def Δ_sigma (t : T) : L1Instances L1 t ⥤ L2Instances L2 t
noncomputable def Δ_pi (t : T) : L1Instances L1 t ⥤ L2Instances L2 t

noncomputable def InstanceLeftAdjunction (t : T) :
    Δ_sigma L1 L2 Δ t ⊣ Δ_pullback L1 L2 Δ t
noncomputable def InstanceRightAdjunction (t : T) :
    Δ_pullback L1 L2 Δ t ⊣ Δ_pi L1 L2 Δ t
```

These are the two [instance-level](../GLOSSARY.md#compilation-and-contract) adjunctions:
- $\Sigma_\Delta$ (left Kan extension): pushes domain data forward to artifacts; fills missing fields with [Skolem nulls](../GLOSSARY.md#migration-vocabulary).
- $\Delta^*$ (precomposition): [pull-back](../GLOSSARY.md#migration-vocabulary).
- $\Pi_\Delta$ (right Kan extension): pulls back conservatively; joins all valid completions.

Mathematically, the existence of these adjunctions is **free** — it follows from presheaf category structure (left and right Kan extensions exist for every functor into a complete and cocomplete category, and `Type` is both). In *this* file, however, all four definitions above are stubbed with `sorry`. The Mathlib infrastructure for pointwise Kan extensions exists; wiring it through has not been done yet. [M5](../GLOSSARY.md#3--internal-milestone-labels) is a theorem we expect to discharge, not a conjecture — but it is currently an open obligation in `DomainSpec.lean`.

### Section 4: Conjectures (M2, M6)

**[M2](../GLOSSARY.md#3--internal-milestone-labels) — Schema-Level Adjunction Conjecture:**
```
def SchemaAdjunctionConjecture (t : T) : Prop :=
  ∀ (b : (L2.obj t)),
    Functor.IsRepresentable ((Δ t).op ⋙ yoneda.obj b)

def SchemaResidueZero (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) : Prop :=
  IsIso (SchemaAdjunction L1 L2 Δ t h).unit
```

At the [schema level](../GLOSSARY.md#compilation-and-contract), does a right adjoint `G : L2 → L1` exist? The conjecture says: for every artifact type `b`, the contravariant Hom-functor `Hom(Δ(-), b)` is representable. If true, then `G` exists pointwise, and schema round-trips recover exactly — the [schema residue](../GLOSSARY.md#residue) is zero.

Open. Proving this would make the schema [compilation contract](../GLOSSARY.md#compilation-and-contract) fully faithful.

**[M6](../GLOSSARY.md#3--internal-milestone-labels) — [Two-Layer Coherence](../GLOSSARY.md#two-layer-framing) Conjectures:**
```
def TwoLayerCoherence (t : T) : Prop :=
  IsInjectiveOnObjects (Δ t) → Functor.Faithful (Δ t) →
  IsIso (InstanceLeftAdjunction L1 L2 Δ t).unit

def TwoLayerCoherence_strong (t : T) : Prop :=
  Functor.FullyFaithful (Δ t) → IsIso (InstanceLeftAdjunction L1 L2 Δ t).unit
```

Does [schema-level](../GLOSSARY.md#compilation-and-contract) discipline guarantee [instance-level](../GLOSSARY.md#compilation-and-contract) fidelity?

- **`TwoLayerCoherence` (weak):** If the compiler is injective and faithful, is the [instance-level](../GLOSSARY.md#compilation-and-contract) unit iso? Open.
- **`TwoLayerCoherence_strong`:** If the compiler is fully faithful, is the [instance-level](../GLOSSARY.md#compilation-and-contract) unit iso? **Refuted.** A four-object counterexample exists: even full faithfulness doesn't prevent [Skolem-null witnesses](../GLOSSARY.md#migration-vocabulary) from corrupting the round-trip.

---

## How They Connect

```
┌─ Fractal.lean ─────────────────────────────────────────┐
│ • Definition of "fractal"                              │
│ • Characterization + two cases (identity, fully FF)    │
│   (all discharged)                                      │
└─────────────────────────────────────────────────────────┘
        ↑
        └─ illustrates the ideal case of
           DomainSpec.lean

┌─ DomainSpec.lean ──────────────────────────────────────┐
│ • Framework: two layers, two adjunctions               │
│ • M5: instance-level adjunctions, free in theory,      │
│   currently `sorry` in this file                       │
│ • M2 (Conjecture): schema-level adjunction             │
│ • M6 (Conjecture + Refutation): schema doesn't imply   │
│   instance fidelity; strong form is false              │
└─────────────────────────────────────────────────────────┘
```

The three results in `Fractal.lean` are the *positive answer*: under the right conditions (fully faithful), information is preserved perfectly at the [instance level](../GLOSSARY.md#compilation-and-contract). `DomainSpec.lean` is the *research question*: when do those conditions hold in a two-layer compilation model, and what can we prove about the gaps when they don't?

---

## How to Read Them

**If you want to understand [fractals](../GLOSSARY.md#fractal-functor):**
- Start with the definition at the top of `Fractal.lean`
- Read the three results in order: they build intuition (identity → fully faithful → general case)
- All proofs are complete; follow them if Lean syntax permits

**If you want to understand the framework:**
- Read `DomainSpec.lean` in sections
  1. Carriers ([meta-types](../GLOSSARY.md#carrier-vocabulary), time track, typing, [edge law](../GLOSSARY.md#carrier-vocabulary)) — the setup
  2. [Schema-level](../GLOSSARY.md#compilation-and-contract) (Δ, injectivity, faithfulness) — the compiler
  3. [Instance-level](../GLOSSARY.md#compilation-and-contract) (presheaves, Kan extensions) — the adjunctions
  4. Conjectures ([M2](../GLOSSARY.md#3--internal-milestone-labels), [M6](../GLOSSARY.md#3--internal-milestone-labels)) — what's open
- Skip proofs that look immediate (like `T0'_C1`); focus on the definitions

**If you want to connect math to code:**
- Check the correspondence table at the end of this document (below)

---

## Correspondence: Math ↔ Code

| Mathematical Concept | DomainSpec.lean | Fractal.lean |
|---|---|---|
| Functor $\Delta : L_1 \to L_2$ | `Δ t : (L1.obj t) ⥤ (L2.obj t)` | `F : C ⥤ D` |
| Presheaf category $\mathrm{Set}^{L_1}$ | `L1Instances t` | `C ⥤ Type v` |
| Left Kan extension $\mathrm{Lan}_\Delta$ | `Δ_sigma t` | `F.lan` |
| Pullback $\Delta^*$ | `Δ_pullback t` | `F.whisker` |
| Right Kan extension $\mathrm{Ran}_\Delta$ | `Δ_pi t` | (not used in Fractal) |
| Adjunction unit $\eta$ | `InstanceLeftAdjunction.unit` | `(F.lanAdjunction).unit` |
| Unit is monic/iso | `IsIso (.unit)` | `Mono (.unit.app ...)` |
| Fully faithful functor | `Functor.FullyFaithful (Δ t)` | `F.FullyFaithful` |
| Instance residue | `∃ I, ¬IsIso (InstanceLeftAdjunction.unit)` | (counterexample in proof of `fractal_of_fullyFaithful`) |

---

## Status Summary

| Result | File | Status | Role |
|---|---|---|---|
| Fractal definition | Fractal.lean | Defined | Core concept |
| Fractal ↔ faithful | Fractal.lean | **Proved** | Equivalence characterization |
| Identity is fractal | Fractal.lean | **Proved** | Base case |
| FullyFaithful → fractal | Fractal.lean | **Proved** | Sufficient condition |
| Schema adjunction (M2) | DomainSpec.lean | **Conjectural** | Open question |
| Instance adjunctions (M5) | DomainSpec.lean | **Free in theory, `sorry` in file** | Mathlib wiring not yet done |
| Weak coherence (M6) | DomainSpec.lean | **Conjectural** | Open question |
| Strong coherence (M6_strong) | DomainSpec.lean | **Refuted** | Counterexample exists |

---

## Navigating the Proof Obligations

Uncommented theorems and definitions in `DomainSpec.lean` marked with `sorry` are open proof obligations. They include:

- `G_adjoint` and `SchemaAdjunction` — assuming [M2](../GLOSSARY.md#3--internal-milestone-labels) holds, this is the [schema-level](../GLOSSARY.md#compilation-and-contract) right adjoint
- `Δ_sigma` and `Δ_pi` — the left and right Kan extensions; defined as `sorry` because their pointwise definitions require Mathlib infrastructure for pointwise Kan extensions (available but verbose)

Commented theorems (like `T0'_C2` and `T0'_C3`) are documented sketches of what would need to be filled in. The comments explain why they're open:
- `T0'_C2` needs a typing functor on `L2` or coherence (A3 in the framework)
- `T0'_C3` needs measure theory and a concrete definition of `N_plus` (the neighbor bound)

These gaps are not bugs. They are honest marks of where the formalization meets the research frontier.
