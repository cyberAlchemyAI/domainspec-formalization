import Mathlib

open CategoryTheory Functor

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-- A functor `F : C ⥤ D` admitting `Type v`-valued (pointwise) left Kan
extensions is **fractal** if the unit of the canonical adjunction
`Lan_F ⊣ F*` between `(C ⥤ Type v)` and `(D ⥤ Type v)` is componentwise
monic. -/
def Fractal (F : C ⥤ D) [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    Mono (((F.lanAdjunction (Type v)).unit.app X).app c)

/-- Equivalent reformulation: `Lan_F : (C ⥤ Type v) ⥤ (D ⥤ Type v)` is faithful. -/
theorem fractal_iff_lan_faithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] :
    Fractal F ↔ Functor.Faithful
      (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)) := by
  constructor
  · intro hF
    haveI : ∀ X, Mono ((F.lanAdjunction (Type v)).unit.app X) := by
      intro X
      haveI : ∀ Y, Mono (((F.lanAdjunction (Type v)).unit.app X).app Y) := hF X
      exact NatTrans.mono_of_mono_app _
    exact (F.lanAdjunction (Type v)).faithful_L_of_mono_unit_app
  · intro _ X c
    -- Faithful left adjoint ⇒ unit components are mono (Mathlib instance)
    haveI : Mono ((F.lanAdjunction (Type v)).unit.app X) := inferInstance
    infer_instance

/-- The identity functor is fractal. `𝟭 C` is fully faithful, so the unit of
its `lanAdjunction` is iso, hence componentwise mono. -/
theorem fractal_id [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    Fractal (𝟭 C) := by
  intro X c
  -- Mathlib's `[Full L] [Faithful L]` instance gives unit-iso, then componentwise.
  haveI : IsIso ((((𝟭 C).lanAdjunction (Type v)).unit.app X).app c) :=
    NatIso.isIso_app_of_isIso _ c
  infer_instance

/-- Every fully faithful functor is fractal. -/
theorem fractal_of_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    Fractal F := by
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  intro X c
  haveI : IsIso (((F.lanAdjunction (Type v)).unit.app X).app c) :=
    NatIso.isIso_app_of_isIso _ c
  infer_instance