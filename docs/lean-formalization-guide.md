---
tags: [lean4, formalization, framework, reference, category-theory, domainspec]
node_type: reference
status: current
nature: technical, reference
version: 1.0.0
last_updated: 2026-04-29
---

# From Math to Code: Reading the Lean Files

This document describes what lives in `CoreflectiveHierarchy.lean` and `DomainSpec.lean`. It assumes you've read the mathematical framework in [domainspec-two-layer-framework.md](./domainspec-two-layer-framework.md) but may not be familiar with Lean syntax. The goal is to map concepts to code and show the landscape you're entering.

---

## Overview

Eight files, organized by purpose:

**`CoreflectiveHierarchy.lean`** — The unit-side kernel. Defines a [coreflective functor](../GLOSSARY.md#coreflective-functor) and splits it into four graduated levels — `LanFaithful` (componentwise mono unit, the weakest; equivalent to `Lan_F` faithful), `InstanceCoreflective` (componentwise iso unit), `SchemaCoreflective`, and `IsCoreflective` (both layers) — so that the [M2 conjecture](../GLOSSARY.md#3--internal-milestone-labels) is captured precisely. Gives the equivalent characterization (faithfulness of the left Kan extension) and discharges the base cases (identity, fully faithful); every claim discharged, no sorries. The schema-level definition takes an explicit adjunction argument rather than a typeclass, preventing typeclass inference from silently assuming the conjecture. (This file absorbs the earlier standalone `Fractal.lean`, now its weakest level `LanFaithful`.)

**`S3Coreflective.lean`** — Two parallel unit-iso conditions. Defines `S2UnitCoreflective F` (unit of `Lan_F ⊣ F*` is iso — the left-Kan adjunction) and `S3UnitCoreflective F` (unit of `F* ⊣ Ran_F` is iso — the right-Kan adjunction). Both are instance-layer properties; they are independent of each other. Proves that every fully faithful functor is S2 unit-coreflective.

**`S2VsS3Counter.lean`** — Left-Kan vs right-Kan unit-iso independence. Exhibits a single functor `F : Discrete (Fin 1) ⥤ Discrete (Fin 2)` that satisfies `S2UnitCoreflective` (because `F` is fully faithful) but fails `S3UnitCoreflective` (the unit at an object outside the image of `F` collapses `Bool` to `PUnit`). The headline: `s2_and_s3_decoupled`. Note: this is *not* the schema-vs-instance independence result (that is proved via M6 Strong refutation in `M6Counter.lean`); it is the finer claim that, within the instance layer, the left-Kan and right-Kan unit conditions are themselves independent.

**`ReflectiveHierarchy.lean`** — Counit-side duals. Defines the counit analogues `InstanceReflective` (counit componentwise iso), `SchemaReflective`, and `IsReflective`. There is no mono-only level on the counit side: the Mathlib criterion is naturally stated at the iso level. Dual to `CoreflectiveHierarchy.lean` but independent: a functor can satisfy the unit-side conditions without satisfying the counit-side ones.

**`CounitCounter.lean`** — Unit/counit decoupling. Constructs a functor `Finc` that is `InstanceCoreflective` (unit componentwise iso) but fails `InstanceReflective` (counit not iso). Proves `InstanceCoreflective Finc ∧ ¬ InstanceReflective Finc`.

**`DomainSpec.lean`** — The research landscape. The full two-layer [residue](../GLOSSARY.md#residue) framework formalized in Lean: all the definitions, assumptions, the free adjunctions that exist, and the conjectures still open. It shows where the results in `CoreflectiveHierarchy.lean` and `ReflectiveHierarchy.lean` live, and what remains to be proved.

**`M6Counter.lean`** — The four-object counterexample. Constructs the concrete setup (`L1 = Discrete (Fin 2)`, `L2 = {a, b, f : a → b}`, Δ the inclusion) used to refute the strong form of the [M6 coherence conjecture](../GLOSSARY.md#3--internal-milestone-labels): even when Δ is fully faithful, the [instance-level](../GLOSSARY.md#compilation-and-contract) unit fails to be iso. The carriers, the category structure, and the Kan-extension instance live here.

**`M2Counter.lean`** — The refutation of unrestricted [M2](../GLOSSARY.md#3--internal-milestone-labels). Reuses the four-object setup from `M6Counter.lean` and shows that the unrestricted Schema-Adjunction Conjecture is false: the presheaf `(Δ.op ⋙ yoneda.obj b)` is not representable, so no schema-level right adjoint exists in general. The conjecture survives only in restricted form.

---

## `CoreflectiveHierarchy.lean` — Base Results (`LanFaithful`)

The weakest level, `LanFaithful`, is defined simply: a functor $F : C \to D$ where the canonical adjunction $\mathrm{Lan}_F \dashv F^*$ between presheaf categories has a unit that is **componentwise monic** — no information loss in the round-trip.

### The definition

```
def LanFaithful (F : C ⥤ D) : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    Mono (((F.lanAdjunction (Type v)).unit.app X).app c)
```

This says: for every presheaf `X` and every object `c`, the unit of the left Kan extension is monic at that point. Monomorphism means no data collapses; what you push forward and pull back is preserved.

### The characterization and two cases

**Characterization — `lanFaithful_iff_lan_faithful`**
A functor is Lan-faithful iff the left Kan extension functor itself is faithful. Two views of the same property.

**Identity case — `lanFaithful_id`**
The identity functor is Lan-faithful. Immediate: the identity's Kan extension is fully faithful (its unit is iso), so the unit is certainly monic.

**Fully faithful case — `lanFaithful_of_fullyFaithful`**
Every fully faithful functor is Lan-faithful. If `F` preserves all information at the morphism level (faithful) and reflects it back (full), then the data-level round-trip is lossless.

All three are discharged in full — no gaps, no `sorry`s. They are reference results: if your compiler is fully faithful, information preservation at the [instance level](../GLOSSARY.md#compilation-and-contract) is guaranteed.

---

## `CoreflectiveHierarchy.lean` — The Four-Level Hierarchy

Where `LanFaithful` is a single notion (componentwise mono unit), the hierarchy pulls the idea apart into four graduated levels that reflect the actual structure of the [M2 conjecture](../GLOSSARY.md#3--internal-milestone-labels).

### Level 1 — `LanFaithful`

```
def LanFaithful (F : C ⥤ D) : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    Mono (((F.lanAdjunction (Type v)).unit.app X).app c)
```

This is exactly the old standalone `Fractal` definition, renamed `LanFaithful`. The unit of `Lan_F ⊣ F*` is componentwise monic — no information loss — which is equivalent to `Lan_F` being faithful. Weakest level.

### Level 2 — `InstanceCoreflective`

```
def InstanceCoreflective (F : C ⥤ D) : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    IsIso (((F.lanAdjunction (Type v)).unit.app X).app c)
```

The unit is componentwise an isomorphism — not just monic, but also epi. No spurious Skolem witnesses: what you push forward and pull back is identical, not just injected. Strictly stronger than `LanFaithful`. Every fully faithful functor satisfies this.

### Level 3 — `SchemaCoreflective`

```
def SchemaCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G) : Prop :=
  IsIso adj.unit
```

The unit of an explicit adjunction `F ⊣ G` at the schema level is a natural isomorphism. The adjunction `adj` is an **explicit argument**, not a typeclass. This is intentional: at the schema level, whether a right adjoint to `F` even exists is the content of the [M2 conjecture](../GLOSSARY.md#3--internal-milestone-labels). Making it explicit means you must supply a proof of existence; you cannot accidentally discharge the conjecture via typeclass inference.

### Level 4 — `IsCoreflective`

```
def IsCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  SchemaCoreflective F adj ∧ InstanceCoreflective F
```

Both layers iso. This is the definition that matches the prose: [residue](../GLOSSARY.md#residue) zero at the schema level and at the instance level simultaneously. An equivalence of categories is a coreflective; every fully faithful functor with an explicit right adjoint is a coreflective.

### What the hierarchy buys

The split lets you state partial results cleanly. You can prove `InstanceCoreflective F` from Mathlib adjunction theory without needing to resolve [M2](../GLOSSARY.md#3--internal-milestone-labels). You can prove `SchemaCoreflective F adj` if someone hands you an adjunction. Only `IsCoreflective F adj` requires both — and that is exactly where [M2](../GLOSSARY.md#3--internal-milestone-labels) sits.

---

## `DomainSpec.lean` — The Full Framework

This file formalizes the setting in which [coreflectives](../GLOSSARY.md#coreflective-functor) make sense: the two-layer compilation model, the [schema-level](../GLOSSARY.md#compilation-and-contract) and [instance-level](../GLOSSARY.md#compilation-and-contract) adjunctions, and the conjectures linking them.

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
- **`TwoLayerCoherence_strong`:** If the compiler is fully faithful, is the [instance-level](../GLOSSARY.md#compilation-and-contract) unit iso? **Refuted.** A four-object counterexample exists: even full faithfulness doesn't prevent [Skolem-null witnesses](../GLOSSARY.md#migration-vocabulary) from corrupting the round-trip. The witness lives in `M6Counter.lean`.

---

## `M6Counter.lean` and `M2Counter.lean` — The Counterexamples

Two of the conjectures in `DomainSpec.lean` are not just open — they are **false in their unrestricted form**, and these two files supply the witnesses. Both rest on a single shared setup.

### The shared four-object setup

```
L1 := Discrete (Fin 2)            -- two isolated objects a₁, b₁
L2Obj := {a, b}  with one non-identity arrow  f : a → b
Δ : L1 ⥤ L2Obj                    -- a ↦ a, b ↦ b (the inclusion)
```

`Δ` is faithful and injective on objects (in fact it is the inclusion of a discrete subcategory). The only structural difference between `L1` and `L2` is the single arrow `f`, which `L1` lacks. That single missing arrow is enough to break both conjectures.

The setup is defined in `M6Counter.lean`; `M2Counter.lean` imports it.

### `M6Counter.lean` — refutes M6 strong

The strong form of [M6](../GLOSSARY.md#3--internal-milestone-labels) (`TwoLayerCoherence_strong` in `DomainSpec.lean`) claims: if Δ is fully faithful, then the unit of the [instance-level](../GLOSSARY.md#compilation-and-contract) left adjunction is iso. `M6Counter.lean` exhibits a presheaf on `L1` whose unit fails to be iso under the four-object Δ — even though Δ is faithful and discrete-injective. The [Skolem witnesses](../GLOSSARY.md#migration-vocabulary) introduced when extending across the missing arrow `f` cannot be undone by pull-back.

### `M2Counter.lean` — refutes unrestricted M2

The headline theorem:

```
theorem M2_unrestricted_false :
    ¬ (∀ {C₁ C₂ : Type} [SmallCategory C₁] [SmallCategory C₂]
         (F : C₁ ⥤ C₂) (b : C₂),
         Functor.IsRepresentable (F.op ⋙ yoneda.obj b))
```

The presheaf `P_b := Δ.op ⋙ yoneda.obj L2Obj.b` is nontrivial at *both* `a₁` and `b₁` (its values are `Hom(a, b) ≃ Unit` and `Hom(b, b) ≃ Unit`). But `L1` is discrete — there are no cross hom-sets — so no single object of `L1` can represent `P_b`. The case-split on the candidate representing object lands in `no_hom_b₁_a₁` or `no_hom_a₁_b₁`, both impossible.

This means the [M2 conjecture](../GLOSSARY.md#3--internal-milestone-labels) as stated in full generality is false. M2 survives only when Δ is restricted (e.g., to fully faithful functors, or to functors satisfying additional density conditions); identifying the right restriction is now the open question, not whether the unrestricted form holds.

---

## How They Connect

```
┌─ LanFaithful — base notion ─────────────────────────────┐
│ • Single definition (componentwise mono unit)           │
│ • Characterization + two cases (identity, fully FF)    │
│   (all discharged)                                      │
└─────────────────────────────────────────────────────────┘
        ↓ refined into
┌─ CoreflectiveHierarchy.lean ───────────────────────────────────────┐
│ • Four-level hierarchy: LanFaithful → InstanceCoreflective  │
│   → SchemaCoreflective → IsCoreflective                            │
│ • SchemaCoreflective takes explicit adj (M2 is not assumed) │
│ • All four levels discharged for identity, equivalence,│
│   and fully faithful functors                          │
└─────────────────────────────────────────────────────────┘
        ↑
        └─ both illustrate the ideal case of
           DomainSpec.lean

┌─ S3Coreflective.lean ───────────────────────────────────────┐
│ • S2UnitCoreflective: unit of Lan_F ⊣ F* is iso            │
│ • S3UnitCoreflective: unit of F* ⊣ Ran_F is iso            │
│ • Fully faithful → S2 (proved)                         │
└─────────────────────────────────────────────────────────┘
        ↓ decoupling proved by
┌─ S2VsS3Counter.lean ───────────────────────────────────┐
│ • Witness: F = Discrete(Fin 1) ⥤ Discrete(Fin 2)      │
│ • S2UnitCoreflective F holds (F fully faithful)             │
│ • S3UnitCoreflective F fails (unit collapses Bool → PUnit   │
│   at object outside image of F)                        │
│ • s2_and_s3_decoupled: the two conditions are          │
│   independent — the "two symmetries" in the title      │
└─────────────────────────────────────────────────────────┘

┌─ ReflectiveHierarchy.lean ───────────────────────────────────────┐
│ • Counit duals: InstanceReflective, SchemaReflective,   │
│   IsReflective (no mono-only level)                     │
│ • Orthogonal to unit-side hierarchy                    │
└─────────────────────────────────────────────────────────┘
        ↓ decoupling proved by
┌─ CounitCounter.lean ───────────────────────────────────┐
│ • Finc is InstanceCoreflective but ¬InstanceReflective       │
│ • Unit-iso and counit-iso are independent              │
└─────────────────────────────────────────────────────────┘

┌─ DomainSpec.lean ──────────────────────────────────────┐
│ • Framework: two layers, two adjunctions               │
│ • M5: instance-level adjunctions, free in theory,      │
│   currently `sorry` in this file                       │
│ • M2 (Conjecture): schema-level adjunction             │
│ • M6 (Conjecture + Refutation): schema doesn't imply   │
│   instance fidelity; strong form is false              │
└─────────────────────────────────────────────────────────┘
        ↑ refuted in unrestricted form by
┌─ M6Counter.lean ───────────────────────────────────────┐
│ • Four-object setup (L1 discrete, L2 with one arrow f) │
│ • Witnesses M6_strong false: fully faithful Δ does     │
│   not force the instance-level unit to be iso          │
└─────────────────────────────────────────────────────────┘
┌─ M2Counter.lean ───────────────────────────────────────┐
│ • Imports M6Counter's four-object setup                │
│ • theorem M2_unrestricted_false: no schema-level right │
│   adjoint exists in general                            │
└─────────────────────────────────────────────────────────┘
```

The results in `CoreflectiveHierarchy.lean` are the *positive answer*: under the right conditions (fully faithful), information is preserved perfectly at both layers. `DomainSpec.lean` is the *research question*: when do those conditions hold in a two-layer compilation model, and what can we prove about the gaps when they don't?

---

## How to Read Them

**If you want to understand [coreflectives](../GLOSSARY.md#coreflective-functor):**
- Start with the definition at the top of `CoreflectiveHierarchy.lean`
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

| Mathematical Concept | DomainSpec.lean | CoreflectiveHierarchy.lean |
|---|---|---|
| Functor $\Delta : L_1 \to L_2$ | `Δ t : (L1.obj t) ⥤ (L2.obj t)` | `F : C ⥤ D` |
| Presheaf category $\mathrm{Set}^{L_1}$ | `L1Instances t` | `C ⥤ Type v` |
| Left Kan extension $\mathrm{Lan}_\Delta$ | `Δ_sigma t` | `F.lan` |
| Pullback $\Delta^*$ | `Δ_pullback t` | `F.whisker` |
| Right Kan extension $\mathrm{Ran}_\Delta$ | `Δ_pi t` | (not used in CoreflectiveHierarchy) |
| Adjunction unit $\eta$ | `InstanceLeftAdjunction.unit` | `(F.lanAdjunction).unit` |
| Unit is monic/iso | `IsIso (.unit)` | `Mono (.unit.app ...)` |
| Fully faithful functor | `Functor.FullyFaithful (Δ t)` | `F.FullyFaithful` |
| Instance residue | `∃ I, ¬IsIso (InstanceLeftAdjunction.unit)` | (counterexample in proof of `lanFaithful_of_fullyFaithful`) |

---

## Status Summary

| Result | File | Status | Role |
|---|---|---|---|
| LanFaithful definition (mono) | CoreflectiveHierarchy.lean | Defined | Core concept |
| Coreflective ↔ faithful | CoreflectiveHierarchy.lean | **Proved** | Equivalence characterization |
| Identity is coreflective | CoreflectiveHierarchy.lean | **Proved** | Base case |
| FullyFaithful → coreflective | CoreflectiveHierarchy.lean | **Proved** | Sufficient condition |
| Four-level hierarchy | CoreflectiveHierarchy.lean | Defined | Refines M2 boundary |
| LanFaithful / InstanceCoreflective / SchemaCoreflective / IsCoreflective | CoreflectiveHierarchy.lean | **Proved** (identity, equiv, fully FF) | Graduated cases |
| Schema adjunction (M2), unrestricted | DomainSpec.lean | **Refuted** in M2Counter.lean | Open only in restricted form |
| Instance adjunctions (M5) | DomainSpec.lean | **Free in theory, `sorry` in file** | Mathlib wiring not yet done |
| Weak coherence (M6) | DomainSpec.lean | **Conjectural** | Open question |
| Strong coherence (M6_strong) | DomainSpec.lean | **Refuted** in M6Counter.lean | Four-object counterexample |
| Four-object setup | M6Counter.lean | Defined | Shared base for M6Counter and M2Counter |
| `M2_unrestricted_false` | M2Counter.lean | **Proved** | Refutation of unrestricted M2 |
| S2UnitCoreflective definition | S3Coreflective.lean | Defined | Left-Kan unit-iso condition |
| S3UnitCoreflective definition | S3Coreflective.lean | Defined | Right-Kan unit-iso condition |
| Fully faithful → S2UnitCoreflective | S3Coreflective.lean | **Proved** | `s2UnitCoreflective_of_fullyFaithful` |
| S2 and S3 are decoupled | S2VsS3Counter.lean | **Proved** (no `sorry`) | `s2_and_s3_decoupled` — the "two independent symmetries" |
| Reflective hierarchy (3 levels) | ReflectiveHierarchy.lean | Defined | Counit-side duals of CoreflectiveHierarchy |
| InstanceCoreflective ∧ ¬InstanceReflective | CounitCounter.lean | **Proved** | Unit/counit independence |

---

## Navigating the Proof Obligations

Uncommented theorems and definitions in `DomainSpec.lean` marked with `sorry` are open proof obligations. They include:

- `G_adjoint` and `SchemaAdjunction` — assuming [M2](../GLOSSARY.md#3--internal-milestone-labels) holds, this is the [schema-level](../GLOSSARY.md#compilation-and-contract) right adjoint
- `Δ_sigma` and `Δ_pi` — the left and right Kan extensions; defined as `sorry` because their pointwise definitions require Mathlib infrastructure for pointwise Kan extensions (available but verbose)

Commented theorems (like `T0'_C2` and `T0'_C3`) are documented sketches of what would need to be filled in. The comments explain why they're open:
- `T0'_C2` needs a typing functor on `L2` or coherence (A3 in the framework)
- `T0'_C3` needs measure theory and a concrete definition of `N_plus` (the neighbor bound)

These gaps are not bugs. They are honest marks of where the formalization meets the research frontier.
