import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Whiskering

import ReflectiveHierarchy

/-!
# M6-Restricted — Unit-iso Characterization under `InstanceReflective`

This file mechanizes the **M6-restricted** theorem of the DomainSpec project:

> Under `[InstanceReflective F]`, the unit `η_X` of the adjunction `Lan_F ⊣ F*`
> at a presheaf `X : C ⥤ Type v` is an isomorphism **if and only if** `X` lies
> in the essential image of the precomposition functor
> `F* = (whiskeringLeft C D (Type v)).obj F`.

## Role in the hierarchy

`M6-restricted` bridges the counit-side and unit-side parts of the coreflective
hierarchy from `CoreflectiveHierarchy.lean` and `ReflectiveHierarchy.lean`.  The `InstanceReflective`
hypothesis says the right adjoint `F*` is fully faithful; the conclusion
characterizes the reflective subcategory `essImage(F*) ⊆ Psh(C)` as precisely
the locus where the unit is an isomorphism.

Concretely:
- **(←)** If `X ≅ F*(Y)` for some `Y : D ⥤ Type v`, then the unit
  `η_{X}` is iso because the Mathlib lemma
  `Adjunction.isIso_unit_app_iff_mem_essImage` reduces it to essential image
  membership when the right adjoint is fully faithful.
- **(→)** If `η_X` is iso then `X ≅ F*(Lan_F X)` via the unit itself, so
  `X` lies in the essential image with witness `Lan_F X = F.lan.obj X`.

## Type-correction note

The research notes write the essential image as
`((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj F.op).essImage`.
This is **incorrect** as a type: `F : C ⥤ D`, not `Cᵒᵖ ⥤ Dᵒᵖ`, and
the adjunction `F.lanAdjunction (Type v)` lives between `C ⥤ Type v` and
`D ⥤ Type v` (not presheaves on the opposites).  The correct precomposition
functor is `(whiskeringLeft C D (Type v)).obj F`, which is already the one
used throughout `ReflectiveHierarchy.lean`.

`F.essImage` in Mathlib is `ObjectProperty D = D → Prop`, i.e., a predicate
applied by function application `F.essImage X`, not by `∈`.

## References

- `ReflectiveHierarchy.lean` — `InstanceReflective`, `fullyFaithful_pullback_of_instanceReflective`.
- `CoreflectiveHierarchy.lean` — the unit-side hierarchy this theorem connects to.
- Mathlib: `CategoryTheory.Adjunction.FullyFaithful`,
  specifically `Adjunction.isIso_unit_app_iff_mem_essImage`.
- Mathlib: `CategoryTheory.EssentialImage` — `Functor.essImage`.
- DomainSpec project, `NAMING.md` §M6-restricted.
-/

open CategoryTheory Functor Adjunction

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## The M6-restricted statement -/

/-- **M6-restricted** (backward direction): if `X` lies in the essential image
of the precomposition functor `F*`, then the unit `η_X` is an isomorphism.

Under `[InstanceReflective F]`, the functor `F* = (whiskeringLeft C D (Type v)).obj F`
is fully faithful (by `fullyFaithful_pullback_of_instanceReflective`).  The
Mathlib lemma `Adjunction.isIso_unit_app_iff_mem_essImage` then reduces `IsIso
η_X` to essential image membership, so the hypothesis `hX` is exactly what is
needed.

**Proof outline:** `InstanceReflective F` → `F*` fully faithful → `[F*.Full]
[F*.Faithful]` → apply `(isIso_unit_app_iff_mem_essImage (F.lanAdjunction _)).mpr hX`. -/
theorem m6_restricted_backward (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (hCof : InstanceReflective F)
    (X : C ⥤ Type v)
    (hX : ((whiskeringLeft C D (Type v)).obj F).essImage X) :
    IsIso ((F.lanAdjunction (Type v)).unit.app X) := by
  -- `InstanceReflective F` gives full faithfulness of the right adjoint `F*`.
  have hFF : ((whiskeringLeft C D (Type v)).obj F).FullyFaithful :=
    fullyFaithful_pullback_of_instanceReflective F hCof
  haveI : ((whiskeringLeft C D (Type v)).obj F).Full := hFF.full
  haveI : ((whiskeringLeft C D (Type v)).obj F).Faithful := hFF.faithful
  -- Now apply the Mathlib characterization.
  exact (isIso_unit_app_iff_mem_essImage (F.lanAdjunction (Type v))).mpr hX

/-- **M6-restricted** (forward direction): if the unit `η_X` is an isomorphism,
then `X` lies in the essential image of `F*`.

This direction does **not** require `InstanceReflective F`; it holds for any
adjunction.  The Mathlib lemma `mem_essImage_of_unit_isIso` directly gives
`R.essImage X` (where `R = (whiskeringLeft C D (Type v)).obj F`) from the
hypothesis `[IsIso (h.unit.app X)]`.

**Proof outline:** `[IsIso η_X]` → apply
`Adjunction.mem_essImage_of_unit_isIso`. -/
theorem m6_restricted_forward (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (X : C ⥤ Type v)
    (hη : IsIso ((F.lanAdjunction (Type v)).unit.app X)) :
    ((whiskeringLeft C D (Type v)).obj F).essImage X := by
  -- The Mathlib lemma works with a typeclass `[IsIso (h.unit.app A)]`.
  haveI : IsIso ((F.lanAdjunction (Type v)).unit.app X) := hη
  exact mem_essImage_of_unit_isIso (F.lanAdjunction (Type v)) X

/-- **M6-restricted** (main biconditional): under `[InstanceReflective F]`, the
unit `η_X` of the adjunction `Lan_F ⊣ F*` at `X : C ⥤ Type v` is an
isomorphism if and only if `X` lies in the essential image of `F*`.

The essential image of `F* = (whiskeringLeft C D (Type v)).obj F` is the full
subcategory of `C ⥤ Type v` consisting of those presheaves `X` for which there
exists `Y : D ⥤ Type v` with `F ⋙ Y ≅ X`.  Concretely `F*.essImage X` unfolds
to `∃ Y : D ⥤ Type v, Nonempty (F.obj · ⋅ Y ≅ X)`.

The `InstanceReflective F` hypothesis is used only in the *backward* (←)
direction to ensure `F*` is fully faithful, which is the hypothesis needed by
`Adjunction.isIso_unit_app_iff_mem_essImage`.  The forward direction (→) is
unconditional.

**Type note.** The research notes write the essential image using
`whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)` and `F.op`; this is a typo — the
adjunction `F.lanAdjunction (Type v)` is between `C ⥤ Type v` and
`D ⥤ Type v`, not presheaf categories on the opposites. -/
theorem m6_restricted (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (hCof : InstanceReflective F)
    (X : C ⥤ Type v) :
    IsIso ((F.lanAdjunction (Type v)).unit.app X) ↔
    ((whiskeringLeft C D (Type v)).obj F).essImage X :=
  ⟨m6_restricted_forward F X,
   m6_restricted_backward F hCof X⟩
