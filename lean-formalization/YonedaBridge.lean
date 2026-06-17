/-
Copyright (c) 2026 Victor Boscaro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Boscaro
-/

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Yoneda

/-!
# The Yoneda bridge for left Kan extensions

For a functor `F : C ⥤ D` admitting pointwise left Kan extensions of every
presheaf `C ⥤ Type v`, the functor `F` is fully faithful if and only if its
left Kan extension functor `F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)` is fully
faithful.

The `(→)` direction follows from
`Adjunction.fullyFaithfulLOfIsIsoUnit` once the unit of `F.lanAdjunction`
is shown componentwise iso. The `(←)` direction transports full faithfulness
back along the canonical iso `F.lan.obj (coyoneda.obj (op c)) ≅
coyoneda.obj (op (F.obj c))`: the corepresentable `coyoneda.obj (op (F.obj c))`
is itself a left Kan extension of `coyoneda.obj (op c)` along `F`, and the
unit of `F.lanAdjunction` at a corepresentable presheaf recovers `F.map`.

## Main definitions

- `coyonedaUnit F c` : the natural transformation
  `coyoneda.obj (op c) ⟶ F ⋙ coyoneda.obj (op (F.obj c))` exhibiting
  `coyoneda.obj (op (F.obj c))` as a left Kan extension along `F`.
- `lanObjCoyonedaIso F c` : the iso
  `F.lan.obj (coyoneda.obj (op c)) ≅ coyoneda.obj (op (F.obj c))`.

## Main results

- `coyoneda_isLeftKanExtension` : `coyoneda.obj (op (F.obj c))` is the left
  Kan extension of `coyoneda.obj (op c)` along `F`, witnessed by
  `coyonedaUnit F c`. Covariant analogue of the yoneda instance in
  `Mathlib.CategoryTheory.Limits.Presheaf`.
- `Functor.fullyFaithfulEquivLanFullyFaithful` : `F.FullyFaithful ≃
  F.lan.FullyFaithful`.

## Tags

Yoneda, coyoneda, left Kan extension, fully faithful, adjunction
-/

open CategoryTheory Functor Opposite

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## Helper: coyoneda.obj (op (F.obj c)) is a left Kan extension -/

variable (F : C ⥤ D)

/-- The natural unit map `coyoneda.obj (op c) ⟶ F ⋙ coyoneda.obj (op (F.obj c))`,
sending `f : c ⟶ x` to `F.map f : F.obj c ⟶ F.obj x`.

This is the covariant analogue of `Functor.yonedaMap` from `Mathlib.CategoryTheory.Yoneda`. -/
def coyonedaUnit (c : C) : coyoneda.obj (op c) ⟶ F ⋙ coyoneda.obj (op (F.obj c)) where
  app _ := TypeCat.ofHom fun f => F.map f

/-- Computing `coyonedaUnit F c` at an object `c'`: it is the `TypeCat` hom
sending `f : c ⟶ c'` to `F.map f`. -/
@[simp]
lemma coyonedaUnit_app (c c' : C) :
    (coyonedaUnit F c).app c' = TypeCat.ofHom (fun f => F.map f) := rfl

variable {F}

set_option backward.isDefEq.respectTransparency false in
/-- The `Unique` instance for lifts from `LeftExtension.mk _ (coyonedaUnit F c)`.

This is the covariant analogue of the `Unique` instance in `Mathlib.CategoryTheory.Limits.Presheaf`
for the yoneda case (lines 393–409), using `coyonedaEquiv` in place of `yonedaEquiv`. -/
instance (c : C) (Y : F.LeftExtension (coyoneda.obj (op c))) :
    Unique (Functor.LeftExtension.mk _ (coyonedaUnit F c) ⟶ Y) where
  default := StructuredArrow.homMk
      (coyonedaEquiv.symm (coyonedaEquiv (F := F ⋙ Y.right) Y.hom)) (by
        ext Z f
        convert (Y.hom.naturality_apply f _).symm
        simp)
  uniq φ := by
    ext1
    apply coyonedaEquiv.injective
    simp [← StructuredArrow.w φ, coyonedaEquiv, coyonedaUnit]

set_option backward.isDefEq.respectTransparency false in
/-- The functor `coyoneda.obj (op (F.obj c))` is the left Kan extension of
`coyoneda.obj (op c)` along `F`, witnessed by `coyonedaUnit F c`.

This is the covariant analogue of the yoneda instance in `Mathlib.CategoryTheory.Limits.Presheaf`
(line 408). The proof follows immediately from the `Unique` instance above. -/
instance coyoneda_isLeftKanExtension {c : C} :
    (coyoneda.obj (op (F.obj c))).IsLeftKanExtension (coyonedaUnit F c) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

/-- The canonical isomorphism `F.lan.obj (coyoneda.obj (op c)) ≅ coyoneda.obj (op (F.obj c))`.

This is the **Yoneda bridge** for covariant presheaves: the left Kan extension of a
corepresentable functor is again corepresentable.

**Proof**: By `Functor.leftKanExtensionUnique`, any two left Kan extensions of the same
functor along the same base functor are canonically isomorphic.  We have:
- `F.lan.obj (coyoneda.obj (op c))` is a left Kan extension with unit
  `F.lanUnit.app (coyoneda.obj (op c))` (by definition of `F.lan`).
- `coyoneda.obj (op (F.obj c))` is a left Kan extension with unit
  `coyonedaUnit F c` (by `coyoneda_isLeftKanExtension`).
So they are iso by `Functor.leftKanExtensionUnique`. -/
noncomputable def lanObjCoyonedaIso
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] (c : C) :
    F.lan.obj (coyoneda.obj (op c)) ≅ coyoneda.obj (op (F.obj c)) :=
  @Functor.leftKanExtensionUnique C (Type v) D _ _ _
    (F.lan.obj (coyoneda.obj (op c)))
    F
    (coyoneda.obj (op c))
    (F.lanUnit.app (coyoneda.obj (op c)))
    (by dsimp [Functor.lan, Functor.lanUnit]; infer_instance)
    (coyoneda.obj (op (F.obj c)))
    (coyonedaUnit F c)
    (coyoneda_isLeftKanExtension (F := F) (c := c))

/-! ## Main theorem -/

/-- **Yoneda bridge theorem**: A functor `F : C ⥤ D` is fully faithful if and only if
the left Kan extension functor `F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)` is fully faithful.

### (→) direction

`F.FullyFaithful → F.lan.FullyFaithful`:

Full faithfulness of `F` implies `[F.Full]` and `[F.Faithful]`, which by
`Adjunction.lean` (section `Full L` `Faithful L`) makes each
`(lanUnit.app G).app X` an isomorphism.  Hence `lanUnit.app G` and
`lanUnit` itself are isos, so `F.lan` is fully faithful by
`Adjunction.fullyFaithfulLOfIsIsoUnit`.

### (←) direction

`F.lan.FullyFaithful → F.FullyFaithful`:

Given `hlan : F.lan.FullyFaithful`:

1. Since `F.lan.FullyFaithful`, we have `F.lan.Full` and `F.lan.Faithful`.
2. By `Adjunction.unit_isIso_of_L_fully_faithful`, the unit `η` of `lanAdjunction`
   is a natural isomorphism.
3. By `descOfIsLeftKanExtension_fac`, the key equation holds:
   `F.lanUnit.app X ≫ whiskerLeft F (lanObjCoyonedaIso F c).hom = coyonedaUnit F c`
   so `bridge.hom.app (F.obj c') (η_c.hom.app c' f) = F.map f`.
4. The preimage of `g : F.obj c ⟶ F.obj c'` is `η_c.inv.app c' (bridge.inv.app (F.obj c') g)`.
5. The two iso-cancellation identities close `map_preimage` and `preimage_map`. -/
noncomputable def Functor.fullyFaithfulEquivLanFullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] :
    F.FullyFaithful ≃ (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)).FullyFaithful where
  toFun hF := by
    -- (→): F fully faithful → F.lan fully faithful
    haveI : F.Full := hF.full
    haveI : F.Faithful := hF.faithful
    haveI hlanUnit_app_app : ∀ (X : C ⥤ Type v) (c : C),
        IsIso ((F.lanUnit.app X).app c) := fun X c => inferInstance
    haveI hlanUnit_app : ∀ X : C ⥤ Type v, IsIso (F.lanUnit.app X) := fun X => by
      haveI : ∀ c, IsIso ((F.lanUnit.app X).app c) := hlanUnit_app_app X
      exact NatIso.isIso_of_isIso_app _
    haveI hlanUnit : IsIso (F.lanUnit (H := Type v)) := NatIso.isIso_of_isIso_app _
    haveI : IsIso (F.lanAdjunction (Type v)).unit := by
      rw [Functor.lanAdjunction_unit]; exact hlanUnit
    exact Adjunction.fullyFaithfulLOfIsIsoUnit (F.lanAdjunction (Type v))
  invFun hlan := by
    -- (←): F.lan fully faithful → F fully faithful
    haveI hFlanFull : (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)).Full := hlan.full
    haveI hFlanFaithful : (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)).Faithful := hlan.faithful
    haveI hunit_iso : IsIso (F.lanAdjunction (Type v)).unit := inferInstance
    haveI hlanUnit_iso : IsIso (F.lanUnit (H := Type v)) := by
      rw [← Functor.lanAdjunction_unit]; exact hunit_iso
    exact {
      preimage := fun {c c'} g =>
          (asIso (F.lanUnit.app (coyoneda.obj (op c)))).inv.app c'
            ((lanObjCoyonedaIso c).inv.app (F.obj c') g)
      map_preimage := fun {c c'} g => by
        have key : ∀ h : c ⟶ c',
            (lanObjCoyonedaIso c).hom.app (F.obj c')
              ((F.lanUnit.app (coyoneda.obj (op c))).app c' h) = F.map h := fun h => by
          simp only [lanObjCoyonedaIso, Functor.leftKanExtensionUnique,
            Functor.leftKanExtensionUniqueOfIso, Iso.refl_hom]
          exact congrFun (congrArg TypeCat.Fun.toFun (congrArg TypeCat.Hom.hom'
            ((F.lan.obj (coyoneda.obj (op c))).descOfIsLeftKanExtension_fac_app
              (F.lanUnit.app (coyoneda.obj (op c)))
              (coyoneda.obj (op (F.obj c)))
              (coyonedaUnit F c) c'))) h
        rw [← key]
        simp only [asIso_inv, NatIso.isIso_inv_app]
        rw [IsIso.inv_hom_id_apply ((F.lanUnit.app (coyoneda.obj (op c))).app c')]
        rw [← comp_apply ((lanObjCoyonedaIso (F := F) c).inv.app (F.obj c'))
              ((lanObjCoyonedaIso (F := F) c).hom.app (F.obj c'))]
        simp [← NatTrans.comp_app, Iso.inv_hom_id]
      preimage_map := fun {c c'} f => by
        have key : (lanObjCoyonedaIso c).hom.app (F.obj c')
            ((F.lanUnit.app (coyoneda.obj (op c))).app c' f) = F.map f := by
          simp only [lanObjCoyonedaIso, Functor.leftKanExtensionUnique,
            Functor.leftKanExtensionUniqueOfIso, Iso.refl_hom]
          exact congrFun (congrArg TypeCat.Fun.toFun (congrArg TypeCat.Hom.hom'
            ((F.lan.obj (coyoneda.obj (op c))).descOfIsLeftKanExtension_fac_app
              (F.lanUnit.app (coyoneda.obj (op c)))
              (coyoneda.obj (op (F.obj c)))
              (coyonedaUnit F c) c'))) f
        rw [← key]
        simp only [asIso_inv, NatIso.isIso_inv_app]
        have step1 : (ConcreteCategory.hom ((lanObjCoyonedaIso (F := F) c).inv.app (F.obj c')))
            ((ConcreteCategory.hom ((lanObjCoyonedaIso (F := F) c).hom.app (F.obj c')))
              ((ConcreteCategory.hom ((F.lanUnit.app (coyoneda.obj (op c))).app c')) f))
            = (ConcreteCategory.hom ((F.lanUnit.app (coyoneda.obj (op c))).app c')) f := by
          rw [← comp_apply ((lanObjCoyonedaIso (F := F) c).hom.app (F.obj c'))
                ((lanObjCoyonedaIso (F := F) c).inv.app (F.obj c'))]
          simp [← NatTrans.comp_app, Iso.hom_inv_id]
        rw [step1]
        exact IsIso.hom_inv_id_apply ((F.lanUnit.app (coyoneda.obj (op c))).app c') f
    }
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `F : C ⥤ D` is fully faithful, then its pointwise left Kan extension along
the Yoneda embedding `F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)` is fully faithful.

This is the `(→)` direction of `Functor.fullyFaithfulEquivLanFullyFaithful`,
exposed as a standalone lemma for convenience. -/
noncomputable def Functor.fullyFaithfulLanOfFullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (hF : F.FullyFaithful) :
    (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)).FullyFaithful :=
  Functor.fullyFaithfulEquivLanFullyFaithful F hF