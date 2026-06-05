import Mathlib

/-!
# S2 / S3 unit-fractality and their decoupling

This file defines two parallel "unit-is-iso" properties for a functor
`F : C ⥤ D`, corresponding to the two canonical adjunctions on the
presheaf categories:

* **S2** (left Kan extension): `Lan_F ⊣ F*` from `(C ⥤ Type v)` to
  `(D ⥤ Type v)`.  Its unit `Z → F* (Lan_F Z)` is an iso when, e.g., `F`
  is fully faithful.
* **S3** (right Kan extension): `F* ⊣ Ran_F` from `(D ⥤ Type v)` to
  `(C ⥤ Type v)`.  Its unit `Y → Ran_F (F* Y)` is an iso under a
  *different* condition (`F*` fully faithful, equivalently `F`
  essentially surjective in appropriate strong senses).

The S2 and S3 unit-iso conditions are therefore **not coupled**: it is
possible for one to hold while the other fails.  The witness lives in
`S2VsS3Counter.lean`.
-/

open CategoryTheory Functor

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## S2 unit-fractality: unit of `Lan_F ⊣ F*` is iso. -/

/-- A functor `F : C ⥤ D` (admitting pointwise left Kan extensions to
`Type v`) is **S2 unit-fractal** with respect to the canonical adjunction
`F.lanAdjunction (Type v) : F.lan ⊣ (whiskeringLeft _ _ _).obj F` if the
unit of that adjunction is a natural isomorphism. -/
def S2UnitFractal (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  IsIso (F.lanAdjunction (Type v)).unit

/-! ## S3 unit-fractality: unit of `F* ⊣ Ran_F` is iso. -/

/-- A functor `F : C ⥤ D` (admitting pointwise right Kan extensions to
`Type v`) is **S3 unit-fractal** with respect to the canonical
adjunction `F.ranAdjunction (Type v) : (whiskeringLeft _ _ _).obj F ⊣ F.ran`
if the unit of that adjunction is a natural isomorphism. -/
def S3UnitFractal (F : C ⥤ D)
    [∀ Y : C ⥤ Type v, F.HasPointwiseRightKanExtension Y] : Prop :=
  IsIso (F.ranAdjunction (Type v)).unit

/-! ## Trivial sanity: a fully faithful functor satisfies S2. -/

/-- A fully faithful `F` is S2 unit-fractal: the unit of `Lan_F ⊣ F*` is
an iso whenever `F` is fully faithful. -/
theorem s2UnitFractal_of_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    S2UnitFractal.{v} F := by
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  -- Mathlib instance: fully faithful left adjoint ⇒ unit is iso.
  show IsIso (F.lanAdjunction (Type v)).unit
  infer_instance
