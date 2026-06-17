import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering

/-!
# Reflective Functors — Counit-Side Dual of the Coreflective Hierarchy

This file mirrors `CoreflectiveHierarchy.lean` on the counit side of the canonical
adjunction `Lan_F ⊣ F*` between `(C ⥤ Type v)` and `(D ⥤ Type v)`.

While the unit-side hierarchy in `CoreflectiveHierarchy.lean` measures defects of the form
"information lost when transporting up via `F`," the counit-side hierarchy
measures defects of the form "extra image structure beyond the essential image
of `F`."  Concretely, the unit `Z ⟶ F* (Lan_F Z)` is an iso iff `F` is fully
faithful, while the counit `Lan_F (F* Y) ⟶ Y` is an iso iff `F*` is fully
faithful (a different, strictly stronger condition on `F`).

## The three levels

| Name | Layer | Strength |
|---|---|---|
| `InstanceReflective F` | instance | counit componentwise iso |
| `SchemaReflective F adj` | schema | counit of `adj : F ⊣ G` is an iso |
| `IsReflective F adj` | both | `SchemaReflective ∧ InstanceReflective` |

There is no `LanFaithful`-style "mono only" level on the counit side: the
classical Mathlib criterion (`fullyFaithfulROfIsIsoCounit`) is naturally stated
at the iso level.

## References

- `CoreflectiveHierarchy.lean` — the unit-side hierarchy this file mirrors.
- Mathlib: `CategoryTheory.Adjunction.FullyFaithful` for the
  `IsIso counit ↔ R fully faithful` correspondence.

## Naming

See `NAMING.md` for the translation table. `InstanceReflective F` is
`((whiskeringLeft _ _ _).obj F).FullyFaithful` (the precomposition
functor `F*` is fully faithful); `SchemaReflective F adj` is `IsIso
adj.counit` (equivalently the right adjoint `G` is fully faithful).
-/

open CategoryTheory Functor

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## Level 1 — `InstanceReflective`: instance-level iso -/

/-- A functor `F : C ⥤ D` is an **instance reflective** if the counit of the
canonical adjunction `Lan_F ⊣ F*` is componentwise an isomorphism.

Dual to `InstanceCoreflective`: while the latter measures "no information lost when
extending a `C`-presheaf to `D` and restricting back," this one measures "no
extra structure when restricting a `D`-presheaf to `C` and extending back." -/
def InstanceReflective (F : C ⥤ D) [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  ∀ (Y : D ⥤ Type v) (d : D),
    IsIso (((F.lanAdjunction (Type v)).counit.app Y).app d)

/-- The identity functor is an instance reflective: its `lanAdjunction` counit
is iso by Mathlib's `[Full L] [Faithful L]` instance. -/
theorem instanceReflective_id [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    InstanceReflective (𝟭 C) := by
  intro Y d
  haveI : IsIso (((𝟭 C).lanAdjunction (Type v)).counit.app Y) :=
    NatIso.isIso_app_of_isIso _ Y
  exact NatIso.isIso_app_of_isIso _ d

/-- A functor `F` whose precomposition functor `F*` is fully faithful yields
an instance reflective: by Mathlib's `counit_isIso_of_R_fully_faithful`, the
counit of `F.lanAdjunction _` is iso, hence componentwise iso. -/
theorem instanceReflective_of_pullback_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    [((whiskeringLeft C D (Type v)).obj F).Full]
    [((whiskeringLeft C D (Type v)).obj F).Faithful] :
    InstanceReflective F := by
  intro Y d
  haveI : IsIso ((F.lanAdjunction (Type v)).counit.app Y) :=
    NatIso.isIso_app_of_isIso _ Y
  exact NatIso.isIso_app_of_isIso _ d

/-- `InstanceReflective F` is equivalent to the precomposition functor
`F* = (whiskeringLeft C D (Type v)).obj F` being fully faithful. Forward:
componentwise iso of the counit implies whole-nat-trans iso, hence
`F*` is fully faithful by `Adjunction.fullyFaithfulROfIsIsoCounit`.
Backward: this is exactly `instanceReflective_of_pullback_fullyFaithful`. -/
noncomputable def fullyFaithful_pullback_of_instanceReflective (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : InstanceReflective F) :
    ((whiskeringLeft C D (Type v)).obj F).FullyFaithful := by
  haveI : ∀ Y, IsIso ((F.lanAdjunction (Type v)).counit.app Y) := fun Y => by
    haveI : ∀ d, IsIso (((F.lanAdjunction (Type v)).counit.app Y).app d) := h Y
    exact NatIso.isIso_of_isIso_app _
  haveI : IsIso (F.lanAdjunction (Type v)).counit := NatIso.isIso_of_isIso_app _
  exact Adjunction.fullyFaithfulROfIsIsoCounit (F.lanAdjunction (Type v))

/-- An equivalence of categories yields an instance reflective: precomposition
with an equivalence is itself an equivalence (Mathlib instance), hence fully
faithful, so the counit of `e.functor.lanAdjunction _` is iso. -/
theorem instanceReflective_of_equivalence (e : C ≌ D)
    [∀ X : C ⥤ Type v, e.functor.HasPointwiseLeftKanExtension X] :
    InstanceReflective e.functor := by
  haveI : IsEquivalence ((whiskeringLeft C D (Type v)).obj e.functor) := inferInstance
  exact instanceReflective_of_pullback_fullyFaithful e.functor

/-! ## Level 2 — `SchemaReflective`: schema-level iso -/

/-- A functor `F : C ⥤ D` with an explicit right adjoint `G` and adjunction
`adj : F ⊣ G` is a **schema reflective** if the counit `adj.counit : F ⋙ G ⟶ 𝟭 D`
is a natural isomorphism.

Dual to `SchemaCoreflective` from `CoreflectiveHierarchy.lean`. -/
def SchemaReflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G) : Prop :=
  IsIso adj.counit

/-- An equivalence of categories yields a schema reflective: the counit of the
adjunction `e.toAdjunction : e.functor ⊣ e.inverse` is a natural isomorphism. -/
theorem schemaReflective_of_equivalence (e : C ≌ D) :
    SchemaReflective e.functor e.toAdjunction := by
  simp [SchemaReflective]
  exact inferInstance

/-- The identity functor is a schema reflective, witnessed by `Adjunction.id`. -/
theorem schemaReflective_id :
    SchemaReflective (𝟭 C) (Adjunction.id (C := C)) := by
  unfold SchemaReflective
  exact inferInstance

/-- If the *right* adjoint `G` of `F ⊣ G` is fully faithful, then `F` is a
schema reflective: a fully faithful right adjoint forces the counit to be an
iso (Mathlib's `[Full G] [Faithful G]` instance for `counit`). -/
theorem schemaReflective_of_R_fullyFaithful {G : D ⥤ C} (F : C ⥤ D)
    (adj : F ⊣ G) (h : G.FullyFaithful) :
    SchemaReflective F adj := by
  simp [SchemaReflective]
  haveI : G.Full := h.full
  haveI : G.Faithful := h.faithful
  exact inferInstance

/-! ## Level 3 — `IsReflective`: both layers iso -/

/-- A functor `F : C ⥤ D` is a **reflective** if it is both a schema reflective
and an instance reflective.  Dual to `IsCoreflective` from `CoreflectiveHierarchy.lean`. -/
def IsReflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  SchemaReflective F adj ∧ InstanceReflective F

/-- Project the schema-reflective component. -/
theorem IsReflective.schemaReflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : IsReflective F adj) : SchemaReflective F adj :=
  h.1

/-- Project the instance-reflective component. -/
theorem IsReflective.instanceReflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : IsReflective F adj) : InstanceReflective F :=
  h.2

/-- The identity functor is a reflective. -/
theorem isReflective_id
    [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    IsReflective (𝟭 C) (Adjunction.id (C := C)) :=
  ⟨schemaReflective_id, instanceReflective_id⟩

/-- An equivalence of categories yields a reflective functor.  Dual to
`isCoreflective_of_equivalence` in `CoreflectiveHierarchy.lean`. -/
theorem isReflective_of_equivalence (e : C ≌ D)
    [∀ X : C ⥤ Type v, e.functor.HasPointwiseLeftKanExtension X] :
    IsReflective e.functor e.toAdjunction :=
  ⟨schemaReflective_of_equivalence e,
   instanceReflective_of_equivalence e⟩
