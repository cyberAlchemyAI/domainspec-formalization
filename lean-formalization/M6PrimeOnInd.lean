/-
Copyright (c) 2026 Victor Boscaro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Boscaro

# M6′ on `Ind(L₁)` — the merged U1+U2 theorem (now UNCONDITIONAL)

This file proves the **M6′-on-Ind** theorem:

> **Theorem (M6′ on Ind).** If `Δ : L₁ ⥤ L₂` is faithful and `X : L₁ ⥤ Type`
> is a *filtered colimit of representables* (an ind-object in the
> covariant-presheaf sense), then the Lan-unit
> `((Δ.lanAdjunction Type).unit.app X)` is a **monomorphism** in
> `L₁ ⥤ Type`.

Both legs are discharged from `[Δ.Faithful]`: the representable base case
(`unitMonoOnRepresentables_of_faithful`) and the filtered-colimit lift
(`lanUnit_mono_of_isIndPresheaf`, formerly the `H_lift` `[GAP]`).  The headline
`unit_mono_on_Ind` therefore carries no hypothesis beyond faithfulness.

This statement is the merge of the previously distinct open milestones
**U1** (Δ-faithful ⇒ Lan-unit mono on representables, lifted)
and **U2** (M6-restricted: the reflective fragment on which faithful
suffices) into a single conditional theorem.  The strategy is documented
in:

* `research-physics/strategy/U1-mono-direction-attack-plan.md`
* `research-physics/strategy/U2-M6restricted-attack-plan.md`

## What this file ships in this wave

1. **`IsIndPresheaf`** — the working notion of "X is a filtered colimit
   of `L₁`-representables".  Defined via a *witnessing* filtered diagram
   `D : J ⥤ L₁` and a colimit cocone of `D ⋙ coyoneda-into-Type` over
   `X`.  We deliberately do **not** identify this with Mathlib's
   `IsIndObject` (which is defined for *contravariant* presheaves
   `Cᵒᵖ ⥤ Type v`); the covariant-side translation is left as
   `[GAP wave-next]`.

2. **`lanUnit_mono_of_isIndPresheaf`** — the **lift**, now proved: if `X`
   is an `IsIndPresheaf` and the Lan-unit is mono at every representable,
   then the Lan-unit at `X` is mono.  The proof: `Δ.lan ⋙ Δ*` preserves
   the witnessing filtered colimit, so the unit at `X` is the colimit
   comparison map of the per-representable units, and monos are stable
   under filtered colimits in `Type u`
   (`(monomorphisms (Type u)).IsStableUnderFilteredColimits`, Joël Riou
   2025) — lifted pointwise across `L₁` via `functorCategory`.

3. **`unitMonoOnRepresentables_of_faithful`** — the representable base
   case, **proved** from `[Δ.Faithful]` via the covariant Yoneda iso
   `Δ.lan.obj (corep a) ≅ corep (Δ.obj a)` (`lanObjCorepIso`), which
   identifies the unit component with `Δ.map`, injective under faithfulness.

4. **`unit_mono_on_Ind`** — the **packaged unconditional theorem**:
   from `[Δ.Faithful]` and any `IsIndPresheaf` witness for `X`, produces
   `Mono` of the Lan-unit at `X`.  No `H_lift`/`H_rep` inputs remain.

## Status: what is closed and what remains

- The representable base case is **proved**:
  `unitMonoOnRepresentables_of_faithful` (from `[Δ.Faithful]`, via the
  covariant Yoneda factorisation through `Δ.map`).

- The filtered-colimit lift (formerly the `H_lift` `[GAP]`) is **proved**:
  `lanUnit_mono_of_isIndPresheaf`.  Hence `unit_mono_on_Ind` now lands
  **UNCONDITIONAL** — the only hypothesis is `[Δ.Faithful]` (plus the
  standing left-Kan-extension instances).  Honest typing: the mathematical
  content (ind-objects are flat; the Lan-unit is monic on flats; monos are
  stable under filtered colimits) is **owned/classical**; the contribution
  here is the mechanization, not new mathematics.

- The general M6′ (universal `X`) is **refuted** by
  `Bicyclic.lanUnit_app_not_mono_bicyclic`; the bicyclic witness `X` is
  not in `Ind(BM)` (it has torsion), so the restriction to `Ind` is
  consistent with the refutation.

- **Still open (sharpness):** `Bicyclic.X ∉ IsIndPresheaf` — the claim that
  `Ind` is the *maximal* restriction at which Δ-faithful suffices for
  Lan-unit mono.  See the closing section below; this is the one remaining
  `[GAP wave-next]` for this file.

## Constraints

- Zero `sorry`.  Every `[GAP …]` is a *hypothesis input*, not a hole.
- Additive: F11, F11Sharpening, M6Restricted, Bicyclic untouched.
- Registered in lakefile under `M6PrimeOnInd`.
-/

import Mathlib.Algebra.Group.TypeTags.Basic

import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits

import Mathlib.Combinatorics.Quiver.SingleObj

open CategoryTheory Functor Limits MorphismProperty

set_option maxHeartbeats 400000

namespace M6PrimeOnInd

universe u

variable {L1 L2 : Type u} [SmallCategory L1] [SmallCategory L2]

/-! ## The covariant representable presheaf `L₁ ⥤ Type u`

For `a : L1`, the representable covariant presheaf is
`coyoneda.obj (Opposite.op a) : L1 ⥤ Type u`, sending `b ↦ Hom(a, b)`.
We abbreviate it as `corep a` for readability. -/

/-- The covariant representable `Hom(a, -) : L₁ ⥤ Type u`. -/
noncomputable abbrev corep (a : L1) : L1 ⥤ Type u :=
  coyoneda.obj (Opposite.op a)

/-- The functor `L₁ᵒᵖ ⥤ (L₁ ⥤ Type u)` sending `a ↦ corep a`.  This is
`coyoneda` reshuffled: `coyoneda : L₁ᵒᵖ ⥤ (L₁ ⥤ Type u)`.  We just give
it a name for readability. -/
noncomputable abbrev corepFunctor : L1ᵒᵖ ⥤ (L1 ⥤ Type u) :=
  (coyoneda : L1ᵒᵖ ⥤ (L1 ⥤ Type u))

/-! ## Ind-presheaves in the covariant sense

A presheaf `X : L₁ ⥤ Type u` is an **ind-object** here iff it is the
colimit of a filtered diagram of covariant representables.

This is *not* Mathlib's `IsIndObject` (which is on
`Cᵒᵖ ⥤ Type v`).  Translating between the two requires an op-flip and
a universe alignment; we leave that to a wave-next merge. -/

/-- **Minimal-data carrier for the lift lemma.**  This is what the lift
proof actually consumes: a filtered shape `J`, a diagram `D : J ⥤ L₁`,
and a colimit-cocone identification `colim (D ⋙ coyoneda^*) ≅ X`. -/
structure RepIndDiagram (X : L1 ⥤ Type u) where
  /-- Indexing category. -/
  J : Type u
  [smallCategory : SmallCategory J]
  [isFiltered : IsFiltered J]
  /-- Indexing diagram into `L₁ᵒᵖ` (so a covariant `J`-shaped diagram of
  representables `corep` is `D ⋙ coyoneda`).  Equivalently, a
  *contravariant* diagram `Jᵒᵖ ⥤ L₁`. -/
  D : J ⥤ L1ᵒᵖ
  /-- The cocone exhibiting `X` as the colimit of `D ⋙ coyoneda`. -/
  cocone : Cocone (D ⋙ corepFunctor)
  /-- The cocone is a colimit. -/
  isColimit : IsColimit cocone
  /-- The cocone point is `X` (on the nose, for ergonomics). -/
  cocone_pt : cocone.pt = X

attribute [instance] RepIndDiagram.smallCategory RepIndDiagram.isFiltered

/-- "X is an ind-presheaf" in this file's working sense. -/
def IsIndPresheaf (X : L1 ⥤ Type u) : Prop := Nonempty (RepIndDiagram X)

/-! ## The representable case — proved via the covariant Yoneda factorisation

Route A: the key is the iso `Δ.lan.obj (corep a) ≅ corep (Δ.obj a)`,
which is `coyoneda.obj (op (Δ.obj a))`.  Once this is identified the unit
component at `corep a` is seen to be `Δ.map`, hence mono under faithfulness.

We inline the minimal `coyonedaUnit` / `lanObjCoyonedaIso` infrastructure
from `DomainSpec.ReportQualia` (which lives in a separate universe section)
rather than importing the full module, to keep universe variables clean. -/

section RepresentableCase

open Opposite

variable {Δ : L1 ⥤ L2}
variable [∀ X : L1 ⥤ Type u, Δ.HasPointwiseLeftKanExtension X]

/-- The canonical natural transformation
`corep a ⟶ Δ ⋙ corep (Δ.obj a)`, sending `f : a ⟶ c` to `Δ.map f`.
Defined with `TypeCat.ofHom` to match `coyonedaEquiv` expectations. -/
private noncomputable def coyonedaUnit_local (a : L1) :
    corep a ⟶ Δ ⋙ corep (Δ.obj a) where
  app _ := TypeCat.ofHom fun f => Δ.map f

omit [∀ (X : L1 ⥤ Type u), Δ.HasPointwiseLeftKanExtension X] in
@[simp]
private lemma coyonedaUnit_local_app (a c : L1) :
    (coyonedaUnit_local (Δ := Δ) a).app c = TypeCat.ofHom (fun f => Δ.map f) := rfl

-- V-10 workaround: isDefEq needs transparency for coyoneda internals
-- TODO: remove after Mathlib exposes a `coyoneda_isInitial` instance
set_option backward.isDefEq.respectTransparency false in
/-- Uniqueness of morphisms out of the `coyonedaUnit_local`-structured arrow.
Needed to establish `IsLeftKanExtension` via `IsInitial.ofUnique`. -/
private noncomputable instance coyonedaUnit_local_unique (a : L1)
    (Y : Δ.LeftExtension (corep a)) :
    Unique (Functor.LeftExtension.mk _ (coyonedaUnit_local (Δ := Δ) a) ⟶ Y) where
  default := StructuredArrow.homMk
      (coyonedaEquiv.symm (coyonedaEquiv (F := Δ ⋙ Y.right) Y.hom)) (by
        ext Z f
        convert (Y.hom.naturality_apply f _).symm
        simp)
  uniq φ := by
    ext1
    apply coyonedaEquiv.injective
    simp [← StructuredArrow.w φ, coyonedaEquiv, coyonedaUnit_local]

-- V-10 workaround: same as above instance
-- TODO: remove after Mathlib exposes a `coyoneda_isInitial` instance
set_option backward.isDefEq.respectTransparency false in
private instance coyoneda_isLeftKanExtension_local (a : L1) :
    (corep (Δ.obj a)).IsLeftKanExtension (coyonedaUnit_local (Δ := Δ) a) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

/-- The canonical iso `Δ.lan.obj (corep a) ≅ corep (Δ.obj a)`,
derived from left Kan extension uniqueness.  This is the covariant analogue
of the contravariant `lanObjCoyonedaIso` in `DomainSpec.ReportQualia`. -/
private noncomputable def lanObjCorepIso (a : L1) :
    Δ.lan.obj (corep a) ≅ corep (Δ.obj a) :=
  @Functor.leftKanExtensionUnique L1 (Type u) L2 _ _ _
    (Δ.lan.obj (corep a))
    Δ
    (corep a)
    (Δ.lanUnit.app (corep a))
    (by dsimp [Functor.lan, Functor.lanUnit]; infer_instance) -- V-10
    (corep (Δ.obj a))
    (coyonedaUnit_local (Δ := Δ) a)
    (coyoneda_isLeftKanExtension_local a)

/-- The Lan-unit at `corep a`, post-composed with the canonical iso,
equals `coyonedaUnit_local a`.  This is the covariant analogue of
`coyonedaUnit_factors_through_lanUnit` from `DomainSpec.ReportQualia`. -/
private theorem lanUnit_corep_factors (a : L1) :
    Δ.lanUnit.app (corep a) ≫ whiskerLeft Δ (lanObjCorepIso (Δ := Δ) a).hom
    = coyonedaUnit_local (Δ := Δ) a := by
  simp only [lanObjCorepIso, Functor.leftKanExtensionUnique,
    Functor.leftKanExtensionUniqueOfIso_hom, Iso.refl_hom, Category.id_comp]
  exact (Δ.lan.obj (corep a)).descOfIsLeftKanExtension_fac
    (Δ.lanUnit.app (corep a))
    (corep (Δ.obj a))
    (coyonedaUnit_local (Δ := Δ) a)

omit [∀ (X : L1 ⥤ Type u), Δ.HasPointwiseLeftKanExtension X] in
/-- Under `[Δ.Faithful]`, `coyonedaUnit_local a` is a monomorphism in
`L₁ ⥤ Type u`.  Componentwise: the map `f ↦ Δ.map f` is injective. -/
private theorem coyonedaUnit_local_mono (a : L1) [Δ.Faithful] :
    Mono (coyonedaUnit_local (Δ := Δ) a) := by
  haveI : ∀ c : L1, Mono ((coyonedaUnit_local (Δ := Δ) a).app c) := fun c => by
    rw [coyonedaUnit_local_app, CategoryTheory.mono_iff_injective]
    intro f g h
    exact Δ.map_injective h
  exact NatTrans.mono_of_mono_app _

/-- The Lan-unit at `corep a` is mono when `Δ` is faithful.
Proof: the unit factors as `η_{corep a} ≫ iso = coyonedaUnit_local a` (mono);
`η = coyonedaUnit_local a ≫ iso⁻¹`, which is a composition of monos. -/
theorem lanUnit_app_corep_mono (a : L1) [Δ.Faithful] :
    Mono (Δ.lanUnit.app (corep a)) := by
  -- Key factorization: `η ≫ (iso as whiskerLeft) = coyonedaUnit_local a`.
  have hfac := lanUnit_corep_factors (Δ := Δ) a
  -- `coyonedaUnit_local a` is mono.
  haveI hmono_rhs : Mono (coyonedaUnit_local (Δ := Δ) a) :=
    coyonedaUnit_local_mono a
  -- `whiskerLeft Δ (lanObjCorepIso a)` is an iso (as whiskerLeft of an iso).
  haveI hiso_lan : IsIso (whiskerLeft Δ (lanObjCorepIso (Δ := Δ) a).hom) :=
    @isIso_whiskerLeft _ _ _ _ _ _ Δ _ _ (lanObjCorepIso (Δ := Δ) a).hom inferInstance
  -- From hfac: η ≫ iso_hom = coyonedaUnit_local a (which is mono).
  -- Therefore η ≫ iso_hom is also mono (by substitution).
  haveI hcomp_mono : Mono (Δ.lanUnit.app (corep a) ≫
      whiskerLeft Δ (lanObjCorepIso (Δ := Δ) a).hom) := hfac ▸ hmono_rhs
  -- `η` is mono because `η ≫ iso_hom` is mono.
  exact mono_of_mono _ (whiskerLeft Δ (lanObjCorepIso (Δ := Δ) a).hom)

end RepresentableCase

/-- **Representable-case theorem.**  For every faithful functor `Δ : L₁ ⥤ L₂`
admitting pointwise left Kan extensions, the Lan-unit at each covariant
representable `corep a` is a monomorphism.

Proof: via the iso `Δ.lan.obj (corep a) ≅ corep (Δ.obj a)` (left Kan extension
uniqueness + covariant Yoneda), the unit component factors through `Δ.map`,
which is injective under faithfulness. -/
def UnitMonoOnRepresentables (Δ : L1 ⥤ L2)
    [∀ X : L1 ⥤ Type u, Δ.HasPointwiseLeftKanExtension X]
    [∀ X : L1 ⥤ Type u, Δ.HasLeftKanExtension X] : Prop :=
  ∀ a : L1, Mono ((Δ.lanAdjunction (Type u)).unit.app (corep a))

/-- `UnitMonoOnRepresentables` holds for every faithful `Δ`.
Translates `lanUnit_app_corep_mono` (which works at the `lanUnit` level)
to the `lanAdjunction.unit` level via `Functor.lanAdjunction_unit`. -/
theorem unitMonoOnRepresentables_of_faithful (Δ : L1 ⥤ L2) [Δ.Faithful]
    [∀ X : L1 ⥤ Type u, Δ.HasPointwiseLeftKanExtension X]
    [∀ X : L1 ⥤ Type u, Δ.HasLeftKanExtension X] :
    UnitMonoOnRepresentables Δ := by
  intro a
  rw [Functor.lanAdjunction_unit]
  exact lanUnit_app_corep_mono a

/-! ## The lift, PROVED (formerly the `H_lift` gap)

The filtered-colimit lift is no longer a hypothesis input.  `X` is a filtered
colimit of covariant representables (the `RepIndDiagram`); the post-composition
functor `T = Δ.lan ⋙ Δ*` preserves that colimit (`Δ.lan` is a left adjoint;
precomposition by `Δ` into `Type u` preserves colimits), so the Lan-unit at `X`
is exactly the colimit-comparison map of the per-representable units, each mono
by hypothesis.  Monos are stable under filtered colimits in `Type u`
(`CategoryTheory.Types`'s `IsStableUnderFilteredColimits`), hence in the functor
category `L₁ ⥤ Type u`.  The mathematical content is owned/classical
(ind-objects are flat; the unit is monic on flats); the contribution is the
mechanization. -/

/-- **The lift, proved.** For faithful `Δ`, if the Lan-unit is mono at every
covariant representable `corep a`, then it is mono at every ind-presheaf `X`.
This discharges what was previously the `H_lift` hypothesis of
`unit_mono_on_Ind`. -/
theorem lanUnit_mono_of_isIndPresheaf (Δ : L1 ⥤ L2) [Δ.Faithful]
    [∀ X : L1 ⥤ Type u, Δ.HasPointwiseLeftKanExtension X]
    (X : L1 ⥤ Type u) (hX : IsIndPresheaf X)
    (hrep : ∀ a : L1, Mono ((Δ.lanAdjunction (Type u)).unit.app (corep a))) :
    Mono ((Δ.lanAdjunction (Type u)).unit.app X) := by
  -- Unpack the witnessing filtered diagram of representables.
  obtain ⟨d⟩ := hX
  -- The Lan-unit `η` and the post-composition functor `T = Σ_Δ ; Δ*`.
  let η := (Δ.lanAdjunction (Type u)).unit
  let T : (L1 ⥤ Type u) ⥤ (L1 ⥤ Type u) :=
    Δ.lan ⋙ (whiskeringLeft L1 L2 (Type u)).obj Δ
  rw [← d.cocone_pt]
  show Mono (η.app d.cocone.pt)
  -- `T` preserves the colimit `d.isColimit`: `Δ.lan` is a left adjoint, and
  -- precomposition by `Δ` preserves colimits (pointwise in `Type u`).
  haveI : PreservesColimitsOfSize.{u, u} Δ.lan :=
    (Δ.lanAdjunction (Type u)).leftAdjoint_preservesColimits
  haveI : PreservesColimit (d.D ⋙ corepFunctor) T :=
    inferInstanceAs (PreservesColimit _ (Δ.lan ⋙ _))
  set F₁ : d.J ⥤ (L1 ⥤ Type u) := d.D ⋙ corepFunctor with hF₁
  let c₂ : Cocone (F₁ ⋙ T) := T.mapCocone d.cocone
  have hc₂ : IsColimit c₂ := isColimitOfPreserves T d.isColimit
  -- The diagram-level natural family: each component is the Lan-unit at a
  -- representable `corep (unop (D.obj j))`, mono by `hrep`.
  let f : F₁ ⟶ F₁ ⋙ T := whiskerLeft F₁ η
  have hf : (monomorphisms (L1 ⥤ Type u)).functorCategory d.J f := by
    intro j
    have hfj : f.app j = η.app (corep (Opposite.unop (d.D.obj j))) := rfl
    rw [monomorphisms.iff, hfj]
    exact hrep _
  -- Naturality of `η` over each colimit leg gives the comparison condition.
  have hcomm : ∀ j : d.J,
      d.cocone.ι.app j ≫ η.app d.cocone.pt = f.app j ≫ c₂.ι.app j :=
    fun j => η.naturality (d.cocone.ι.app j)
  -- Monos are stable under filtered colimits in `Type u`, hence pointwise in
  -- the functor category `L₁ ⥤ Type u`.
  haveI : (monomorphisms (Type u)).IsStableUnderColimitsOfShape d.J :=
    IsStableUnderFilteredColimits.isStableUnderColimitsOfShape d.J
  haveI hstab :
      ((monomorphisms (Type u)).functorCategory L1).IsStableUnderColimitsOfShape d.J :=
    IsStableUnderColimitsOfShape.functorCategory L1
  haveI : (monomorphisms (L1 ⥤ Type u)).IsStableUnderColimitsOfShape d.J := by
    rw [← functorCategory_monomorphisms L1]
    exact hstab
  -- Apply the stability `condition` to the two colimit cocones and the
  -- pointwise-mono family `f`, with comparison map `η.app d.cocone.pt`.
  have hmono :=
    IsStableUnderColimitsOfShape.condition (W := monomorphisms (L1 ⥤ Type u))
      (J := d.J) F₁ (F₁ ⋙ T) d.cocone c₂ d.isColimit hc₂ f hf
      (η.app d.cocone.pt) hcomm
  rwa [monomorphisms.iff] at hmono

/-! ## The lift: filtered colimit of mono Lan-units is mono

Strategy: `Σ_Δ` (a left adjoint) and `Δ^*` (eval-pointwise) both
preserve all colimits in `Set`-valued presheaves; in particular they
preserve the filtered colimit exhibiting `X` as colim of representables.
The unit is then a natural transformation between filtered colimits;
componentwise this is the colimit (in `Type u`) of mono maps, which is
mono by `(monomorphisms (Type u)).IsStableUnderFilteredColimits`
(Mathlib `CategoryTheory/Types/Monomorphisms.lean:42`).

The categorical lift to natural-transformation level uses pointwise
computation of filtered colimits in `L₁ ⥤ Type u`
(Mathlib `CategoryTheory/Limits/FunctorCategory/Filtered.lean`). -/

/-- **The lift skeleton.**  Stated as a conditional: given representable-case
mono and a `RepIndDiagram` for `X`, the Lan-unit at `X` is mono.

In this wave we **state** the conclusion in the form
"componentwise-mono on the indexing representables ⇒ mono on `X`"
*without* re-deriving the filtered-colimit-preservation chain in Lean.
The proof obligation expands as:

  - `Σ_Δ` preserves filtered colimits: `Δ.lan` is a left adjoint
    (`Δ.lanAdjunction`), so this is automatic from
    `Adjunction.leftAdjointPreservesColimits`.
  - `Δ^*` is `(whiskeringLeft L1 L2 (Type u)).obj Δ`; precomposition
    preserves all colimits in `Type` (computed pointwise in functor
    categories).
  - The unit `η : 𝟭 → Δ^* ∘ Σ_Δ` is natural; at the colim of representables
    it factors through the colim of the unit components, each mono.
  - Apply `IsStableUnderFilteredColimits` to `(monomorphisms (Type u))`
    pointwise across `L₁` (functor categories: filtered colimits are
    pointwise).

This Lean lift is `[GAP wave-next, ~120 lines]`.  Here we ship it as
a conditional `Mono` statement consuming the representable-case
hypothesis directly. -/
theorem unit_mono_on_Ind_conditional
    (Δ : L1 ⥤ L2) [Δ.Faithful]
    [∀ X : L1 ⥤ Type u, Δ.HasPointwiseLeftKanExtension X]
    [∀ X : L1 ⥤ Type u, Δ.HasLeftKanExtension X]
    (H_lift : ∀ (X : L1 ⥤ Type u), IsIndPresheaf X →
      (∀ a : L1, Mono ((Δ.lanAdjunction (Type u)).unit.app (corep a))) →
      Mono ((Δ.lanAdjunction (Type u)).unit.app X))
    (X : L1 ⥤ Type u) (hX : IsIndPresheaf X) :
    Mono ((Δ.lanAdjunction (Type u)).unit.app X) :=
  H_lift X hX (unitMonoOnRepresentables_of_faithful Δ)

/-! ## The headline statement

The form of the U1+U2 merged statement.  `H_rep` has been closed by
`unitMonoOnRepresentables_of_faithful`; only `H_lift` (the filtered-colimit
lift, `[GAP wave-next]`) remains as an explicit hypothesis. -/

/-- **M6′-on-Ind — UNCONDITIONAL.**

If `Δ : L₁ ⥤ L₂` is faithful, then the Lan-unit is mono at every ind-presheaf.

Both inputs are now discharged from `[Δ.Faithful]`: the representable case `H_rep`
by `unitMonoOnRepresentables_of_faithful`, and the filtered-colimit lift `H_lift`
by `lanUnit_mono_of_isIndPresheaf`.  No remaining hypotheses beyond faithfulness
(and the standing left-Kan-extension instances). -/
theorem unit_mono_on_Ind
    (Δ : L1 ⥤ L2) [Δ.Faithful]
    [∀ X : L1 ⥤ Type u, Δ.HasPointwiseLeftKanExtension X]
    [∀ X : L1 ⥤ Type u, Δ.HasLeftKanExtension X] :
    ∀ (X : L1 ⥤ Type u), IsIndPresheaf X →
      Mono ((Δ.lanAdjunction (Type u)).unit.app X) :=
  fun X hX =>
    lanUnit_mono_of_isIndPresheaf Δ X hX (unitMonoOnRepresentables_of_faithful Δ)

/-! ## Compatibility with the refutation side

The bicyclic witness `Bicyclic.lanUnit_app_not_mono_bicyclic` lives
*outside* `IsIndPresheaf`: the bicyclic torsion act fails to be a
filtered colimit of representables of `BM = SingleObj (Multiplicative ℕ)`.
This sharpness check is left as `[GAP wave-next]`:

  > **Claim (to verify in next wave).** `Bicyclic.X ∉ IsIndPresheaf`.
  > Sketch: representables of `BM` are free `Multiplicative ℕ`-acts;
  > filtered colimits of free acts in `Set` are flat, hence torsion-free.
  > The bicyclic witness is torsion (e.g. `0 = bFn^n · 0` for all `n`),
  > so it is not flat, hence not in `Ind(BM)`.

If the claim holds, the M6′-on-Ind statement is **sharp**: `Ind` is the
maximal restriction at which Δ-faithful suffices for Lan-unit mono. -/

end M6PrimeOnInd
