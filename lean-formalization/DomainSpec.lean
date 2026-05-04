/-
  DomainSpec — v4 two-layer residue, Lean 4 signatures.
  Extracted from theorem/theorem-presentations/v4-two-layer-residue.md (§4.3, §4.4).

  Targets current Mathlib (deploy-2026-04-28+). Two namespace migrations vs the
  presentation source:

    * `Mathlib.CategoryTheory.Limits.KanExtension` was removed; Kan-extension
      material now lives under `Mathlib.CategoryTheory.Functor.KanExtension.*`.
    * `Mathlib.CategoryTheory.Types` was split into `Types.Basic`, `Types.Limits`,
      `Types.Colimits`, etc. — the aggregate name no longer ships an `.olean`.

  All proofs in this file are complete: T0'_C1 (determinism), T0'_C2 (image
  validity, L1-level via reflexivity of `EdgeLaw`), T0'_C3 (per-step entropy
  bound via the discrete Gibbs inequality), the M5 instance triple
  `Σ_Δ ⊣ Δ* ⊣ Π_Δ`, conditional discharge of M2 from costructured-arrow
  terminals, and the parametric `GeneralSchema` substitution theorem.
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

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

-- M5 instance-level Kan extension typeclasses (target = Type 0).
variable [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
variable [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F]

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

-- Σ_Δ and Π_Δ are the left/right Kan extension functors `Functor.lan`/`Functor.ran`
-- between presheaf categories, available from
-- `Mathlib.CategoryTheory.Functor.KanExtension.Adjunction`. The triple
-- `Σ_Δ ⊣ Δ* ⊣ Π_Δ` is then `lanAdjunction (Type 0)` and `ranAdjunction (Type 0)`.
noncomputable def Δ_sigma (t : T) : L1Instances L1 t ⥤ L2Instances L2 t :=
  (Δ t).lan

noncomputable def Δ_pi (t : T) : L1Instances L1 t ⥤ L2Instances L2 t :=
  (Δ t).ran

noncomputable def InstanceLeftAdjunction (t : T) :
    Δ_sigma L1 L2 Δ t ⊣ Δ_pullback L1 L2 Δ t :=
  (Δ t).lanAdjunction (Type 0)

noncomputable def InstanceRightAdjunction (t : T) :
    Δ_pullback L1 L2 Δ t ⊣ Δ_pi L1 L2 Δ t :=
  (Δ t).ranAdjunction (Type 0)

-- ============================================================
-- T0' — Compilation Confluence (per time slice, schema level)
-- ============================================================

-- C1: determinism from functoriality (no sorry).
-- `T0'_C1` only depends on `Δ` and `L1`; the lint flags the other section
-- variables (`SemilatticeSup T`, the injectivity/faithfulness assumptions on
-- `Δ`) as unused. `omit ... in` keeps them out of the theorem's signature.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem T0'_C1 (t : T) (g g' : L1.obj t) (h : g = g') :
    (Δ t).obj g = (Δ t).obj g' :=
  congrArg (Δ t).obj h

-- C2: image validity at the L1 level. With `EdgeLaw` reflexive, a morphism
-- `f : X ⟶ Y` in `L1.obj t` lifts to `(τ t).map f : (τ t).obj X ⟶ (τ t).obj Y`
-- in `Discrete MetaType`, where `Discrete.eq_of_hom` collapses the morphism to
-- the equality `((τ t).obj X).as = ((τ t).obj Y).as`. The conclusion is then
-- `EdgeLaw a a` for the common type `a`, discharged by `Std.Refl.refl`.
--
-- The L2-side variant (`EdgeLaw` on the image through `Δ`) requires a typing
-- functor `τ' : L2.obj t ⥤ Discrete MetaType` plus an A3-style coherence
-- `τ' t = Δ t ⋙ τ t` — a structural addition deferred for now.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem T0'_C2 [Std.Refl EdgeLaw]
    (t : T) {X Y : L1.obj t} (f : X ⟶ Y) :
    EdgeLaw ((τ t).obj X).as ((τ t).obj Y).as := by
  have h : ((τ t).obj X).as = ((τ t).obj Y).as :=
    Discrete.eq_of_hom ((τ t).map f)
  rw [← h]
  exact Std.Refl.refl _

-- C3: per-step entropy bound (from A4). Discrete reformulation: a probability
-- mass function `p` supported in the finite 1-neighborhood `N_plus t v ⊆ L1.obj t`
-- has Shannon entropy at most `log |N_plus t v|`. The Mathlib `measureEntropy`
-- the v4 source referenced doesn't exist in current Mathlib; we work with a
-- discrete `Finset`-based entropy, which is the natural fit since `N_plus` is
-- finite by construction.

/-- Discrete Shannon entropy of `p : α → ℝ` summed over a finite set `S`. -/
noncomputable def discreteEntropy {α : Type*} (p : α → ℝ) (S : Finset α) : ℝ :=
  ∑ x ∈ S, Real.negMulLog (p x)

/-- **Maximum-entropy bound.** A nonnegative function `p : α → ℝ` with total
mass `1` over a finite set `S` has discrete entropy at most `Real.log |S|`.
The proof goes via `Real.self_sub_one_le_mul_log` applied pointwise to
`p x * |S|`, then summing and dividing by `|S|`. This is the discrete Gibbs
inequality with the uniform reference distribution. -/
theorem discreteEntropy_le_log_card {α : Type*} {p : α → ℝ} {S : Finset α}
    (hp_nn : ∀ x ∈ S, 0 ≤ p x) (hp_sum : ∑ x ∈ S, p x = 1) :
    discreteEntropy p S ≤ Real.log S.card := by
  -- `S` must be nonempty: otherwise `∑ = 0 ≠ 1`.
  have hS_ne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · simp at hp_sum
    · exact hne
  set n : ℝ := (S.card : ℝ) with hn_def
  have hn_pos : 0 < n := by
    rw [hn_def]; exact_mod_cast Finset.card_pos.mpr hS_ne
  -- Pointwise: `p x * n - 1 ≤ (p x * n) * log (p x * n)`.
  have key : ∀ x ∈ S, p x * n - 1 ≤ (p x * n) * Real.log (p x * n) := fun x hx =>
    Real.self_sub_one_le_mul_log (mul_nonneg (hp_nn x hx) hn_pos.le)
  have sum_ineq : ∑ x ∈ S, (p x * n - 1) ≤ ∑ x ∈ S, (p x * n) * Real.log (p x * n) :=
    Finset.sum_le_sum key
  -- LHS sum simplifies to 0: `n * ∑ p x - card = n - n = 0`.
  have lhs_zero : ∑ x ∈ S, (p x * n - 1) = 0 := by
    have h1 : ∑ x ∈ S, p x * n = n := by
      rw [show (∑ x ∈ S, p x * n) = (∑ x ∈ S, p x) * n from (Finset.sum_mul ..).symm,
          hp_sum, one_mul]
    rw [Finset.sum_sub_distrib, h1, Finset.sum_const, Nat.smul_one_eq_cast, hn_def]
    ring
  -- Pointwise rewrite of RHS: split `log (p x * n)` via `log_mul` (handling `p x = 0`).
  have rhs_pointwise : ∀ x ∈ S, (p x * n) * Real.log (p x * n)
      = n * (p x * Real.log (p x)) + p x * (n * Real.log n) := by
    intros x hx
    rcases eq_or_lt_of_le (hp_nn x hx) with hpx_eq | hpx_pos
    · rw [← hpx_eq]; simp
    · rw [Real.log_mul hpx_pos.ne' hn_pos.ne']; ring
  have rhs_eq : ∑ x ∈ S, (p x * n) * Real.log (p x * n)
      = n * (∑ x ∈ S, p x * Real.log (p x)) + n * Real.log n := by
    rw [Finset.sum_congr rfl rhs_pointwise]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp_sum, one_mul]
  rw [lhs_zero, rhs_eq] at sum_ineq
  -- Goal becomes: `-(∑ p x * log p x) ≤ log n`. Convert entropy to negation.
  unfold discreteEntropy
  have entropy_neg : ∑ x ∈ S, Real.negMulLog (p x) = -(∑ x ∈ S, p x * Real.log (p x)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Real.negMulLog]; ring
  rw [entropy_neg]
  -- From `0 ≤ n * (∑ p log p) + n * log n` and `n > 0`, deduce
  -- `0 ≤ (∑ p log p) + log n`, hence `-(∑ p log p) ≤ log n`.
  have h_factored : 0 ≤ n * ((∑ x ∈ S, p x * Real.log (p x)) + Real.log n) := by
    have : n * ((∑ x ∈ S, p x * Real.log (p x)) + Real.log n)
         = n * (∑ x ∈ S, p x * Real.log (p x)) + n * Real.log n := by ring
    linarith [this, sum_ineq]
  have h_div : 0 ≤ (∑ x ∈ S, p x * Real.log (p x)) + Real.log n :=
    (mul_nonneg_iff_of_pos_left hn_pos).mp h_factored
  linarith

-- The 1-neighborhood `N_plus t v ⊆ L1.obj t` is taken as a section parameter:
-- different concrete instantiations (in-edges, out-edges, full 1-ball) all yield
-- the same entropy bound, so the theorem is parametric in this choice.
section EntropyBound
variable (N_plus : (t : T) → L1.obj t → Finset (L1.obj t))

-- **T0'_C3 (per-step entropy bound).** A probability mass function `p`
-- supported in the finite 1-neighborhood `N_plus t v` has discrete entropy at
-- most `log |N_plus t v|`.
omit [SemilatticeSup T] in
theorem T0'_C3 (t : T) (v : L1.obj t) (p : L1.obj t → ℝ)
    (hp_nn : ∀ x ∈ N_plus t v, 0 ≤ p x)
    (hp_sum : ∑ x ∈ N_plus t v, p x = 1) :
    discreteEntropy p (N_plus t v) ≤ Real.log (N_plus t v).card :=
  discreteEntropy_le_log_card hp_nn hp_sum

end EntropyBound

-- ============================================================
-- M1 — Cocontinuity is a theorem at the schema level
-- ============================================================

-- Modern Mathlib name lives in `Functor.KanExtension.Pointwise`:
--   `Functor.preservesColimitsOfShape_of_isPointwiseLeftKanExtension`.
-- The legacy `Functor.IsLeftKanExtension.preservesColimits` no longer resolves.

-- ============================================================
-- T1', T5' — Substitution into a parametric General Schema
-- ============================================================

-- Parametric General Schema — substitution of any choice of
-- `(G, Artifacts, τ_G, Δ_G, N_plus_G)` into the C1/C2/C3 legs of T0'. The proofs
-- transfer verbatim because nothing in C1/C2/C3 depends on the specific names
-- `L1/L2/τ/Δ/N_plus`; the file's main section just happened to use those.
omit [SemilatticeSup T] in
theorem GeneralSchema
    (G Artifacts : T ⥤ Cat)
    (τ_G : (t : T) → (G.obj t) ⥤ Discrete MetaType)
    (Δ_G : (t : T) → (G.obj t) ⥤ (Artifacts.obj t))
    (N_plus_G : (t : T) → G.obj t → Finset (G.obj t))
    [Std.Refl EdgeLaw] :
    -- C1: determinism of compilation per time slice.
    (∀ (t : T) (g g' : G.obj t), g = g' → (Δ_G t).obj g = (Δ_G t).obj g') ∧
    -- C2: image validity (L1-level), via the typing functor `τ_G`.
    (∀ (t : T) {X Y : G.obj t}, (X ⟶ Y) →
        EdgeLaw ((τ_G t).obj X).as ((τ_G t).obj Y).as) ∧
    -- C3: per-step entropy bound on the 1-neighborhood `N_plus_G t v`.
    (∀ (t : T) (_ : G.obj t) (p : G.obj t → ℝ) (v : G.obj t),
        (∀ x ∈ N_plus_G t v, 0 ≤ p x) →
        (∑ x ∈ N_plus_G t v, p x = 1) →
        discreteEntropy p (N_plus_G t v) ≤ Real.log (N_plus_G t v).card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t g g' h
    exact congrArg (Δ_G t).obj h
  · intro t X Y f
    have h : ((τ_G t).obj X).as = ((τ_G t).obj Y).as :=
      Discrete.eq_of_hom ((τ_G t).map f)
    rw [← h]; exact Std.Refl.refl _
  · intro _t _ p _ hp_nn hp_sum
    exact discreteEntropy_le_log_card hp_nn hp_sum

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

-- §4.4.1 — Conditional discharge of M2 from costructured-arrow terminals.
--
-- The unrestricted M2 conjecture is *false* in general (see `M2Counter.lean`:
-- the four-object setup `L1 = Disc {a,b}`, `L2 = {a,b, f:a→b}`, `Δ` the
-- inclusion is a counterexample). However, M2 *does* follow from the standard
-- existence-of-right-adjoint criterion: if for every `b : L2.obj t` the
-- costructured-arrow category `CostructuredArrow (Δ t) b` has a terminal
-- object, then `Δ t` admits a right adjoint and hence each
-- `(Δ t).op ⋙ yoneda.obj b` is representable.
--
-- Mathlib's `adjunctionOfCostructuredArrowTerminals` (in
-- `Mathlib.CategoryTheory.Adjunction.Comma`) supplies the adjunction; we
-- read off representability from its hom-equivalence.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem SchemaAdjunctionConjecture_of_hasTerminal_costructuredArrow
    (t : T)
    [∀ b : L2.obj t, Limits.HasTerminal (CostructuredArrow (Δ t) b)] :
    SchemaAdjunctionConjecture L1 L2 Δ t := by
  -- Build the adjunction `Δ t ⊣ G` from the terminal-object hypothesis.
  let adj : (Δ t) ⊣ rightAdjointOfCostructuredArrowTerminals (Δ t) :=
    adjunctionOfCostructuredArrowTerminals (Δ t)
  -- For each `b`, exhibit a `RepresentableBy` witness with representing object
  -- `G.obj b`. The natural bijection is `(adj.homEquiv X b).symm`, whose
  -- naturality on the left is `homEquiv_naturality_left_symm`.
  intro b
  refine RepresentableBy.isRepresentable
    (Y := (rightAdjointOfCostructuredArrowTerminals (Δ t)).obj b)
    { homEquiv := fun {X} => (adj.homEquiv X b).symm
      homEquiv_comp := ?_ }
  intro X X' f g
  -- `(Δ t).op ⋙ yoneda.obj b` sends `f.op : op X' ⟶ op X` to
  -- precomposition with `(Δ t).map f`, which is exactly the left-naturality
  -- of the symmetric hom-equivalence.
  exact adj.homEquiv_naturality_left_symm f g

-- Construction of the right adjoint and the adjunction is mechanical given the
-- representability hypothesis: each `(Δ t).op ⋙ yoneda.obj b` has a representing
-- object `G(b)` and a natural hom-equiv. This pattern follows the Mathlib proof
-- of `isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top` (PartialAdjoint.lean).
noncomputable def G_adjoint
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) :
    (L2.obj t) ⥤ (L1.obj t) :=
  haveI : ∀ b, IsRepresentable ((Δ t).op ⋙ yoneda.obj b) := h
  Adjunction.rightAdjointOfEquiv
    (F := Δ t)
    (G_obj := fun b => ((Δ t).op ⋙ yoneda.obj b).reprX)
    (e := fun _ Y => ((Δ t).op ⋙ yoneda.obj Y).representableBy.homEquiv.symm)
    (fun _ _ _ _ _ => (RepresentableBy.comp_homEquiv_symm ..).symm)

noncomputable def SchemaAdjunction
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) :
    (Δ t) ⊣ G_adjoint L1 L2 Δ t h := by
  haveI : ∀ b, IsRepresentable ((Δ t).op ⋙ yoneda.obj b) := h
  exact Adjunction.adjunctionOfEquivRight
    (F := Δ t)
    (G_obj := fun b => ((Δ t).op ⋙ yoneda.obj b).reprX)
    (e := fun _ Y => ((Δ t).op ⋙ yoneda.obj Y).representableBy.homEquiv.symm)
    (fun _ _ _ _ _ => (RepresentableBy.comp_homEquiv_symm ..).symm)

-- Schema residue: the schema-level unit's failure to be iso.
def SchemaResidueZero (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) : Prop :=
  IsIso (SchemaAdjunction L1 L2 Δ t h).unit

-- **Conditional M2 (residue zero from fullness).** Given the
-- representability conjecture `SchemaAdjunctionConjecture` at time `t` and
-- fully-faithfulness of `Δ t`, the schema-level adjunction's unit is an
-- isomorphism — i.e. `SchemaResidueZero` holds. This sidesteps the existence
-- question for the right adjoint (which is the content of the conjecture
-- itself) and only uses Mathlib's `Adjunction.unit_isIso_of_L_fully_faithful`:
-- a fully faithful left adjoint has iso unit.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem SchemaResidueZero_of_fullyFaithful
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t)
    (hΔ : (Δ t).FullyFaithful) :
    SchemaResidueZero L1 L2 Δ t h := by
  unfold SchemaResidueZero
  haveI : (Δ t).Full := hΔ.full
  haveI : (Δ t).Faithful := hΔ.faithful
  exact inferInstance

-- **Schema residue zero forces full faithfulness.** Once the schema adjunction
-- exists, an isomorphism unit characterizes fully faithful left adjoints.
noncomputable def fullyFaithfulOfSchemaResidueZero
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t)
    (hz : SchemaResidueZero L1 L2 Δ t h) :
    (Δ t).FullyFaithful := by
  let adj := SchemaAdjunction L1 L2 Δ t h
  haveI : IsIso adj.unit := by
    simpa [SchemaResidueZero] using hz
  exact adj.fullyFaithfulLOfIsIsoUnit

@[reducible] noncomputable def fullOfSchemaResidueZero
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t)
    (hz : SchemaResidueZero L1 L2 Δ t h) :
    Full (Δ t) :=
  (fullyFaithfulOfSchemaResidueZero L1 L2 Δ t h hz).full

-- In the ambient DomainSpec regime faithfulness is already assumed globally,
-- so fullness is the missing half of full faithfulness.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem SchemaResidueZero_of_full
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t)
    [Full (Δ t)] :
    SchemaResidueZero L1 L2 Δ t h := by
  unfold SchemaResidueZero
  infer_instance

-- **Characterization, propositionally packaged.** Since `Full` and
-- `FullyFaithful` are structures rather than `Prop`s, we expose the converse
-- via `Nonempty`.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem SchemaResidueZero_iff_nonempty_full
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) :
    SchemaResidueZero L1 L2 Δ t h ↔ Nonempty (Full (Δ t)) := by
  constructor
  · intro hz
    exact ⟨fullOfSchemaResidueZero L1 L2 Δ t h hz⟩
  · rintro ⟨hfull⟩
    letI : Full (Δ t) := hfull
    exact SchemaResidueZero_of_full L1 L2 Δ t h

omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem SchemaResidueZero_iff_full
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t) :
    SchemaResidueZero L1 L2 Δ t h ↔ Nonempty (Full (Δ t)) := by
  constructor
  · intro hz
    exact ⟨fullOfSchemaResidueZero L1 L2 Δ t h hz⟩
  · rintro ⟨_⟩
    exact SchemaResidueZero_of_full L1 L2 Δ t h

omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasLeftKanExtension (Δ t) F]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem not_SchemaResidueZero_of_not_full
    (t : T) (h : SchemaAdjunctionConjecture L1 L2 Δ t)
    (hnf : ¬ Full (Δ t)) :
    ¬ SchemaResidueZero L1 L2 Δ t h := by
  intro hz
  exact hnf (fullOfSchemaResidueZero L1 L2 Δ t h hz)

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

-- The fully-faithful case of two-layer coherence is already available once
-- pointwise left Kan extensions are in scope; this is the strongest instance-
-- side result currently packaged in `DomainSpec.lean`.
omit [SemilatticeSup T] [∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]
  [∀ t, ∀ (F : (L1.obj t) ⥤ Type), HasRightKanExtension (Δ t) F] in
theorem TwoLayerCoherence_strong_of_pointwise
    (t : T)
    [∀ X : (L1.obj t) ⥤ Type, (Δ t).HasPointwiseLeftKanExtension X] :
    TwoLayerCoherence_strong L1 L2 Δ t := by
  intro hΔ
  haveI : (Δ t).Full := hΔ.full
  haveI : (Δ t).Faithful := hΔ.faithful
  change IsIso (((Δ t).lanAdjunction (Type 0)).unit)
  infer_instance
