import Mathlib
import S3Fractal

/-!
# S2 vs S3: a concrete decoupling

We exhibit a single functor `F : Discrete (Fin 1) ⥤ Discrete (Fin 2)`
that:

* satisfies `S2UnitFractal F` (the unit of `Lan_F ⊣ F*` is iso), because
  `F` is fully faithful;
* fails `S3UnitFractal F` (the unit of `F* ⊣ Ran_F` is **not** iso),
  because the unit at the constantly-`Bool` presheaf, evaluated at the
  object `⟨1⟩ ∈ Discrete (Fin 2)` not in the image of `F`, is a map
  `Bool → (limit of an empty diagram in Type) ≃ PUnit`, which collapses
  `true ≠ false` and therefore is not even injective.

This refutes the claim of an unrestricted coupling between the S2 and
S3 unit-iso conditions.
-/

open CategoryTheory Functor Limits

set_option maxHeartbeats 800000

namespace S2VsS3

/-! ## Domain & codomain: discrete categories of size 1 and 2 -/

abbrev C₁ := Discrete (Fin 1)
abbrev D₂ := Discrete (Fin 2)

abbrev c₀ : C₁ := ⟨0⟩
abbrev d₀ : D₂ := ⟨0⟩
abbrev d₁ : D₂ := ⟨1⟩

/-- The functor `F : Discrete (Fin 1) ⥤ Discrete (Fin 2)` sending
`⟨0⟩ ↦ ⟨0⟩`. -/
def F : C₁ ⥤ D₂ := Discrete.functor (fun (_ : Fin 1) => d₀)

@[simp] lemma F_obj (c : C₁) : F.obj c = d₀ := rfl

/-! ## `F` is fully faithful (only identity morphisms in either category). -/

/-- `F` is faithful: all hom-sets in a `Discrete` category are subsingletons. -/
instance : F.Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

/-- `F` is full: a morphism in `Discrete (Fin 2)` between objects `F.obj X` and
`F.obj Y` necessarily has `X.as = Y.as` because `F.obj X = F.obj Y = d₀`, but we
need to lift it back to a morphism in `C₁`.  The structure of `C₁` has unique
identity morphisms on `c₀`, so we just produce the identity. -/
instance : F.Full where
  map_surjective {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    have hxy : X = Y := by
      fin_cases X
      fin_cases Y
      rfl
    subst hxy
    exact ⟨𝟙 _, Subsingleton.elim _ _⟩

/-- Package up full+faithful. -/
noncomputable def F_fullyFaithful : F.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful F

/-! ## Pointwise Kan extensions exist (both sides). -/

instance (X : C₁ ⥤ Type) : F.HasPointwiseLeftKanExtension X := fun _ => inferInstance
instance (Y : C₁ ⥤ Type) : F.HasPointwiseRightKanExtension Y := fun _ => inferInstance

/-! ## S2 succeeds: F is fully faithful. -/

theorem s2_unit_iso : S2UnitFractal.{0} F :=
  s2UnitFractal_of_fullyFaithful F F_fullyFaithful

/-! ## S3 fails: explicit `Y` with collapsing unit at `d₁`. -/

/-- The constantly-`Bool` presheaf on `D₂`. -/
def Ybool : D₂ ⥤ Type := (Functor.const D₂).obj Bool

@[simp] lemma Ybool_obj (X : D₂) : Ybool.obj X = Bool := rfl

/-! ### The structured-arrow category `StructuredArrow d₁ F` is empty. -/

/-- A structured arrow `(right : C₁, hom : d₁ ⟶ F.obj right)` cannot exist:
`F.obj right = d₀` and `d₁ ⟶ d₀` is empty in `Discrete (Fin 2)`. -/
instance structuredArrow_d1_F_empty : IsEmpty (StructuredArrow d₁ F) := by
  refine ⟨fun s => ?_⟩
  -- The hom field forces `d₁.as = (F.obj s.right).as`.
  have h : d₁ ⟶ F.obj s.right := s.hom
  have heq : (d₁ : D₂).as = (F.obj s.right).as := Discrete.eq_of_hom h
  -- `F.obj s.right = d₀`, so its `as` is `0`.  But `d₁.as = 1 ≠ 0`.
  have hF : F.obj s.right = d₀ := rfl
  rw [hF] at heq
  exact absurd heq (by decide)

/-! ### The Ran at `d₁` is a Subsingleton (limit over an empty cat). -/

theorem ran_at_d1_subsingleton :
    Subsingleton ((F.ran.obj (F ⋙ Ybool)).obj d₁) := by
  -- Iso to a limit over the (empty) structured-arrow category.
  let iso : (F.ran.obj (F ⋙ Ybool)).obj d₁ ≅
      limit (StructuredArrow.proj d₁ F ⋙ (F ⋙ Ybool)) :=
    F.ranObjObjIsoLimit (F ⋙ Ybool) d₁
  -- The limit is over an empty diagram, hence terminal, hence subsingleton.
  haveI : IsEmpty (StructuredArrow d₁ F) := inferInstance
  let cn : Cone (StructuredArrow.proj d₁ F ⋙ (F ⋙ Ybool)) :=
    limit.cone _
  have htlim :
      IsTerminal (limit (StructuredArrow.proj d₁ F ⋙ (F ⋙ Ybool))) :=
    (isLimitEquivIsTerminalOfIsEmpty (C := Type) cn) (limit.isLimit _)
  -- Terminal in Type ⇒ Unique ⇒ Subsingleton.
  have hu : Unique (limit (StructuredArrow.proj d₁ F ⋙ (F ⋙ Ybool))) :=
    Types.isTerminalEquivUnique _ htlim
  haveI : Subsingleton (limit (StructuredArrow.proj d₁ F ⋙ (F ⋙ Ybool))) :=
    hu.instSubsingleton
  exact iso.toEquiv.subsingleton

/-! ### Two distinct elements of `Bool`. -/

lemma true_ne_false_bool : (true : Bool) ≠ (false : Bool) := by decide

/-! ## Main theorem: S3 unit-fractality fails for `F`. -/

theorem s3_unit_not_iso : ¬ S3UnitFractal.{0} F := by
  intro h
  -- Register `h` as a typeclass instance so Mathlib's auto-instances fire.
  haveI hh : IsIso (F.ranAdjunction (Type 0)).unit := h
  -- Each component (at a presheaf, and at an object) is iso.
  have h₁ : IsIso ((F.ranAdjunction (Type 0)).unit.app Ybool) :=
    NatIso.isIso_app_of_isIso _ Ybool
  haveI := h₁
  have h₂ : IsIso (((F.ranAdjunction (Type 0)).unit.app Ybool).app d₁) :=
    NatIso.isIso_app_of_isIso _ d₁
  -- In `Type`, iso ⇔ bijective on the underlying function.
  have hbij : Function.Bijective
      (((F.ranAdjunction (Type 0)).unit.app Ybool).app d₁) :=
    (CategoryTheory.isIso_iff_bijective _).mp h₂
  -- The target is a subsingleton.
  have hsubT : Subsingleton ((F.ran.obj (F ⋙ Ybool)).obj d₁) :=
    ran_at_d1_subsingleton
  -- The function maps into `(F.ran.obj (F ⋙ Ybool)).obj d₁` (definitionally).
  -- Injective into a subsingleton ⇒ source is subsingleton.
  have hsubS : Subsingleton (Ybool.obj d₁) := by
    refine ⟨fun a b => ?_⟩
    apply hbij.injective
    exact @Subsingleton.elim _ hsubT _ _
  -- But `Ybool.obj d₁ = Bool`, where `true ≠ false`.
  have : (true : Ybool.obj d₁) = (false : Ybool.obj d₁) :=
    hsubS.elim _ _
  exact true_ne_false_bool this

/-! ## Headline corollary: S2 and S3 unit-fractality are decoupled. -/

theorem s2_and_s3_decoupled :
    S2UnitFractal.{0} F ∧ ¬ S3UnitFractal.{0} F :=
  ⟨s2_unit_iso, s3_unit_not_iso⟩

end S2VsS3
