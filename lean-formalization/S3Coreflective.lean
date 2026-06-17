import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# S2 / S3 unit-coreflectivity and their decoupling

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

## Naming

See `NAMING.md` for the project-to-Mathlib translation. `S2UnitCoreflective F`
is the whole-nat-trans form of `InstanceCoreflective F`; both are equivalent
to `F.lan` being fully faithful (lemma below). `S3UnitCoreflective F` has no
clean classical translation and is kept structural.
-/

open CategoryTheory Functor

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## S2 unit-coreflectivity: unit of `Lan_F ⊣ F*` is iso. -/

/-- A functor `F : C ⥤ D` (admitting pointwise left Kan extensions to
`Type v`) is **S2 unit-coreflective** with respect to the canonical adjunction
`F.lanAdjunction (Type v) : F.lan ⊣ (whiskeringLeft _ _ _).obj F` if the
unit of that adjunction is a natural isomorphism. -/
def S2UnitCoreflective (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  IsIso (F.lanAdjunction (Type v)).unit

/-! ## S3 unit-coreflectivity: unit of `F* ⊣ Ran_F` is iso. -/

/-- A functor `F : C ⥤ D` (admitting pointwise right Kan extensions to
`Type v`) is **S3 unit-coreflective** with respect to the canonical
adjunction `F.ranAdjunction (Type v) : (whiskeringLeft _ _ _).obj F ⊣ F.ran`
if the unit of that adjunction is a natural isomorphism. -/
-- Note: unlike S2, there is no clean classical "F-side" name for
-- `S3UnitCoreflective F` in current Mathlib. See `NAMING.md`. The
-- `S2VsS3Counter.lean` file shows S2 and S3 are independent.
def S3UnitCoreflective (F : C ⥤ D)
    [∀ Y : C ⥤ Type v, F.HasPointwiseRightKanExtension Y] : Prop :=
  IsIso (F.ranAdjunction (Type v)).unit

/-! ## Trivial sanity: a fully faithful functor satisfies S2. -/

/-- A fully faithful `F` is S2 unit-coreflective: the unit of `Lan_F ⊣ F*` is
an iso whenever `F` is fully faithful. -/
theorem s2UnitCoreflective_of_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    S2UnitCoreflective.{v} F := by
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  -- Mathlib instance: fully faithful left adjoint ⇒ unit is iso.
  show IsIso (F.lanAdjunction (Type v)).unit
  infer_instance

/-- `S2UnitCoreflective F` is equivalent to `F.lan` being fully faithful (in the
`Type v`-valued presheaf setting). This is the whole-nat-trans form of the
classical "unit of `Lan_F ⊣ F*` iso ⇔ left adjoint fully faithful." -/
noncomputable def fullyFaithful_lan_of_s2UnitCoreflective (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : S2UnitCoreflective.{v} F) :
    (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)).FullyFaithful := by
  haveI : IsIso (F.lanAdjunction (Type v)).unit := h
  exact Adjunction.fullyFaithfulLOfIsIsoUnit (F.lanAdjunction (Type v))
