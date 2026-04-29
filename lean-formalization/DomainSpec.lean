/-
  DomainSpec — v4 two-layer residue, Lean 4 signatures.
  Extracted from theorem/theorem-presentations/v4-two-layer-residue.md (§4.3, §4.4).

  Targets current Mathlib (deploy-2026-04-28+). Two namespace migrations vs the
  presentation source:

    * `Mathlib.CategoryTheory.Limits.KanExtension` was removed; Kan-extension
      material now lives under `Mathlib.CategoryTheory.Functor.KanExtension.*`.
    * `Mathlib.CategoryTheory.Types` was split into `Types.Basic`, `Types.Limits`,
      `Types.Colimits`, etc. — the aggregate name no longer ships an `.olean`.

  Open proof obligations from the presentation source are preserved as `sorry`s.
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Fintype.Basic

open CategoryTheory Functor

-- A1: meta-types
-- (`Fintype` deriving requires `Mathlib.Tactic.DeriveFintype`; nothing in this
-- file uses `Fintype MetaType` yet, so we drop it from the `deriving` clause.)
inductive MetaType | entity | operation | constraint | relationship
  deriving DecidableEq

axiom EdgeLaw : MetaType → MetaType → Prop
-- The original `instance : DecidableRel EdgeLaw := by exact inferInstance` is
-- circular: `EdgeLaw` is opaque, nothing to derive. If decidability is needed
-- downstream, fall back to classical:
--   open Classical in instance : DecidableRel EdgeLaw := fun _ _ => propDecidable _
-- For the conjecture block below it isn't used, so we drop it.

-- A_time (M4): T is a join-semilattice viewed as a thin category
variable {T : Type*} [SemilatticeSup T] [Category T]

-- The temporally-indexed L1 and L2 (schema level)
variable (L1 L2 : T ⥤ Cat)

-- A1 typing functor at each time
variable (τ : (t : T) → (L1.obj t) ⥤ Discrete MetaType)

-- A_Kan (M1): a dense subcategory K and a base compiler at each time
variable {K : Type*} [Category K]
variable (I : (t : T) → K ⥤ (L1.obj t))
variable (Δ_base : (t : T) → K ⥤ (L2.obj t))

-- The compiler is the Left Kan Extension at each time (schema level).
-- The typeclass needs the unit `α t : Δ_base t ⟶ I t ⋙ Δ t` explicitly.
variable (Δ : (t : T) → (L1.obj t) ⥤ (L2.obj t))
variable (α : (t : T) → Δ_base t ⟶ I t ⋙ Δ t)
variable [∀ t, (Δ t).IsLeftKanExtension (α t)]

-- A_inj (M3): injectivity on objects + faithfulness
class IsInjectiveOnObjects {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : Prop where
  inj_obj : ∀ X Y : C, F.obj X = F.obj Y → X = Y

variable [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]

-- M4 schema-level naturality.
-- The clean statement is `(L1.map h) ⋙ (Δ t₂) = (Δ t₁) ⋙ (L2.map h)`, but
-- `L1.map h : L1.obj t₁ ⟶ L1.obj t₂` is a morphism in `Cat`, not directly a
-- `⥤`-composable functor — Lean needs an explicit ascription. Since this
-- variable isn't used downstream in the file, dropped to keep elaboration clean.

-- ============================================================
-- Instance categories: presheaves
-- ============================================================

abbrev L1Instances (t : T) := (L1.obj t) ⥤ Type
abbrev L2Instances (t : T) := (L2.obj t) ⥤ Type

-- ============================================================
-- M5 — Free instance-level data migration triple (Σ_Δ ⊣ Δ* ⊣ Π_Δ)
-- ============================================================

-- Pullback (precomposition) — survives the rename unchanged.
def Δ_pullback (t : T) : L2Instances L2 t ⥤ L1Instances L1 t :=
  (whiskeringLeft _ _ _).obj (Δ t)

-- Σ_Δ and Π_Δ used to be `Lan (Δ t)` / `Ran (Δ t)` from
-- `Mathlib.CategoryTheory.Limits.KanExtension`. In current Mathlib they go
-- through `Functor.lan` / `Functor.ran` under the `Functor.KanExtension.Pointwise`
-- namespace, plus `HasPointwiseLeftKanExtension` typeclass arguments.
-- Stubbed as `sorry` definitions so the conjecture block in §4.4 typechecks.
--
-- The bodies do `have := Δ t` purely to reference the section variable `Δ` —
-- without that, Lean's auto-inclusion elides `Δ` (because the stated type
-- doesn't depend on it and the body is `sorry`), and then downstream calls like
-- `Δ_sigma L1 L2 Δ t` mis-read `Δ` as the `t : T` argument.
noncomputable def Δ_sigma (t : T) : L1Instances L1 t ⥤ L2Instances L2 t := by
  have _ := Δ t
  exact sorry

noncomputable def Δ_pi (t : T) : L1Instances L1 t ⥤ L2Instances L2 t := by
  have _ := Δ t
  exact sorry

noncomputable def InstanceLeftAdjunction (t : T) :
    Δ_sigma L1 L2 Δ t ⊣ Δ_pullback L1 L2 Δ t := sorry

noncomputable def InstanceRightAdjunction (t : T) :
    Δ_pullback L1 L2 Δ t ⊣ Δ_pi L1 L2 Δ t := sorry

-- ============================================================
-- T0' — Compilation Confluence (per time slice, schema level)
-- ============================================================

-- C1: determinism from functoriality (no sorry).
-- `T0'_C1` only depends on `Δ` and `L1`; the lint flags the other section
-- variables (`SemilatticeSup T`, the injectivity/faithfulness assumptions on
-- `Δ`) as unused. `omit ... in` keeps them out of the theorem's signature.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)] in
theorem T0'_C1 (t : T) (g g' : L1.obj t) (h : g = g') :
    (Δ t).obj g = (Δ t).obj g' :=
  congrArg (Δ t).obj h

-- C2: image validity — mediated by τ. The v4 source kept this commented as a
-- sketch only, and the reason is real: τ types `L1` objects, but to assert
-- `EdgeLaw` *on the image* we'd need a typing functor τ' on `L2` (or A3-typing-
-- coherence to transport types across Δ). Without that, the natural restatement
-- is at the L1 level — `EdgeLaw ((τ t).obj X).as ((τ t).obj Y).as` — which is
-- what the project's agent notes (theorem-counterargument.md, agent-c) record.
-- Left as a doc stub to keep the file honest about the open obligation.
-- theorem T0'_C2 (t : T) {X Y : L1.obj t} (_f : X ⟶ Y) :
--     EdgeLaw ((τ t).obj X).as ((τ t).obj Y).as := sorry

-- C3: per-step entropy bound (from A4). Needs Mathlib.MeasureTheory + a
-- concrete `N_plus` definition not present at this scope; left as a doc stub.
-- theorem T0'_C3 (t : T) (v : L1.obj t) (P : Measure (L1.obj t))
--     (h_a4 : P.support ⊆ N_plus v) :
--     measureEntropy P ≤ Real.log (N_plus v).toFinset.card := sorry

-- ============================================================
-- M1 — Cocontinuity is a theorem at the schema level
-- ============================================================

-- Modern Mathlib name lives in `Functor.KanExtension.Pointwise`:
--   `Functor.preservesColimitsOfShape_of_isPointwiseLeftKanExtension`.
-- The legacy `Functor.IsLeftKanExtension.preservesColimits` no longer resolves.

-- ============================================================
-- T1', T5' — Substitution into a parametric General Schema
-- ============================================================

-- Parametric GS — the v1/v4 promissory note. Open proof obligation.
-- theorem GeneralSchema (G : T ⥤ Cat) (Artifacts : T ⥤ Cat)
--   (Δ_G : ∀ t, (G.obj t) ⥤ (Artifacts.obj t))
--   [hyp : ...] : (T0'_C1 ∧ T0'_C2 ∧ T0'_C3 instantiated for G, Δ_G) := sorry

-- ============================================================
-- §4.4 — Conjectures
-- ============================================================

-- M2 — Schema-level Adjunction Conjecture (Representability)
-- Note: the v4 source wrote `coyoneda.obj (Opposite.op b)`, but that produces a
-- functor `L2 ⥤ Type` and `(Δ t).op` lands in `(L2)ᵒᵖ` — composition is type-
-- wrong. The presheaf P_b(a) = Hom_{L2}(Δ a, b) is `(Δ t).op ⋙ yoneda.obj b`.
-- The current-Mathlib name for the representability predicate is
-- `Functor.IsRepresentable` (a `Prop` typeclass); the v4 source's
-- `Functor.Representable` no longer resolves.
def SchemaAdjunctionConjecture (t : T) : Prop :=
  ∀ (b : (L2.obj t)),
    Functor.IsRepresentable ((Δ t).op ⋙ yoneda.obj b)

noncomputable def G_adjoint
    (t : T) (_h : SchemaAdjunctionConjecture L1 L2 Δ t) :
    (L2.obj t) ⥤ (L1.obj t) :=
  -- pointwise: G(b) is the representing object of P_b
  sorry

noncomputable def SchemaAdjunction
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) :
    (Δ t) ⊣ G_adjoint L1 L2 Δ t h :=
  sorry

-- Schema residue: the schema-level unit's failure to be iso.
def SchemaResidueZero (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) : Prop :=
  IsIso (SchemaAdjunction L1 L2 Δ t h).unit

-- M5-derived: Instance Residue (free; no conjecture)
def InstanceResidueZero (t : T) : Prop :=
  IsIso (InstanceLeftAdjunction L1 L2 Δ t).unit

-- M6 — Two-Layer Coherence Conjecture
def TwoLayerCoherence (t : T) : Prop :=
  IsInjectiveOnObjects (Δ t) → Functor.Faithful (Δ t) →
  IsIso (InstanceLeftAdjunction L1 L2 Δ t).unit

-- A weaker form: require Δ fully faithful.
def TwoLayerCoherence_strong (t : T) : Prop :=
  Functor.FullyFaithful (Δ t) → IsIso (InstanceLeftAdjunction L1 L2 Δ t).unit
