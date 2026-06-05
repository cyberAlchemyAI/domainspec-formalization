import Mathlib

/-!
# Cofractal Functors — Counit-Side Dual of the Fractal Hierarchy

This file mirrors `FractalOP.lean` on the counit side of the canonical
adjunction `Lan_F ⊣ F*` between `(C ⥤ Type v)` and `(D ⥤ Type v)`.

While the unit-side hierarchy in `FractalOP.lean` measures defects of the form
"information lost when transporting up via `F`," the counit-side hierarchy
measures defects of the form "extra image structure beyond the essential image
of `F`."  Concretely, the unit `Z ⟶ F* (Lan_F Z)` is an iso iff `F` is fully
faithful, while the counit `Lan_F (F* Y) ⟶ Y` is an iso iff `F*` is fully
faithful (a different, strictly stronger condition on `F`).

## The three levels

| Name | Layer | Strength |
|---|---|---|
| `InstanceCofractal F` | instance | counit componentwise iso |
| `SchemaCofractal F adj` | schema | counit of `adj : F ⊣ G` is an iso |
| `Cofractal F adj` | both | `SchemaCofractal ∧ InstanceCofractal` |

There is no `LanFaithful`-style "mono only" level on the counit side: the
classical Mathlib criterion (`fullyFaithfulROfIsIsoCounit`) is naturally stated
at the iso level.

## References

- `FractalOP.lean` — the unit-side hierarchy this file mirrors.
- Mathlib: `CategoryTheory.Adjunction.FullyFaithful` for the
  `IsIso counit ↔ R fully faithful` correspondence.
-/

open CategoryTheory Functor

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## Level 1 — `InstanceCofractal`: instance-level iso -/

/-- A functor `F : C ⥤ D` is an **instance cofractal** if the counit of the
canonical adjunction `Lan_F ⊣ F*` is componentwise an isomorphism.

Dual to `InstanceFractal`: while the latter measures "no information lost when
extending a `C`-presheaf to `D` and restricting back," this one measures "no
extra structure when restricting a `D`-presheaf to `C` and extending back." -/
def InstanceCofractal (F : C ⥤ D) [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  ∀ (Y : D ⥤ Type v) (d : D),
    IsIso (((F.lanAdjunction (Type v)).counit.app Y).app d)

/-- The identity functor is an instance cofractal: its `lanAdjunction` counit
is iso by Mathlib's `[Full L] [Faithful L]` instance. -/
theorem instanceCofractal_id [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    InstanceCofractal (𝟭 C) := by
  intro Y d
  haveI : IsIso (((𝟭 C).lanAdjunction (Type v)).counit.app Y) :=
    NatIso.isIso_app_of_isIso _ Y
  exact NatIso.isIso_app_of_isIso _ d

/-- A functor `F` whose precomposition functor `F*` is fully faithful yields
an instance cofractal: by Mathlib's `counit_isIso_of_R_fully_faithful`, the
counit of `F.lanAdjunction _` is iso, hence componentwise iso. -/
theorem instanceCofractal_of_pullback_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    [((whiskeringLeft C D (Type v)).obj F).Full]
    [((whiskeringLeft C D (Type v)).obj F).Faithful] :
    InstanceCofractal F := by
  intro Y d
  haveI : IsIso ((F.lanAdjunction (Type v)).counit.app Y) :=
    NatIso.isIso_app_of_isIso _ Y
  exact NatIso.isIso_app_of_isIso _ d

/-- An equivalence of categories yields an instance cofractal: precomposition
with an equivalence is itself an equivalence (Mathlib instance), hence fully
faithful, so the counit of `e.functor.lanAdjunction _` is iso. -/
theorem instanceCofractal_of_equivalence (e : C ≌ D)
    [∀ X : C ⥤ Type v, e.functor.HasPointwiseLeftKanExtension X] :
    InstanceCofractal e.functor := by
  haveI : IsEquivalence ((whiskeringLeft C D (Type v)).obj e.functor) := inferInstance
  exact instanceCofractal_of_pullback_fullyFaithful e.functor

/-! ## Level 2 — `SchemaCofractal`: schema-level iso -/

/-- A functor `F : C ⥤ D` with an explicit right adjoint `G` and adjunction
`adj : F ⊣ G` is a **schema cofractal** if the counit `adj.counit : F ⋙ G ⟶ 𝟭 D`
is a natural isomorphism.

Dual to `SchemaFractal` from `FractalOP.lean`. -/
def SchemaCofractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G) : Prop :=
  IsIso adj.counit

/-- An equivalence of categories yields a schema cofractal: the counit of the
adjunction `e.toAdjunction : e.functor ⊣ e.inverse` is a natural isomorphism. -/
theorem schemaCofractal_of_equivalence (e : C ≌ D) :
    SchemaCofractal e.functor e.toAdjunction := by
  simp [SchemaCofractal]
  exact inferInstance

/-- The identity functor is a schema cofractal, witnessed by `Adjunction.id`. -/
theorem schemaCofractal_id :
    SchemaCofractal (𝟭 C) (Adjunction.id (C := C)) := by
  unfold SchemaCofractal
  exact inferInstance

/-- If the *right* adjoint `G` of `F ⊣ G` is fully faithful, then `F` is a
schema cofractal: a fully faithful right adjoint forces the counit to be an
iso (Mathlib's `[Full G] [Faithful G]` instance for `counit`). -/
theorem schemaCofractal_of_R_fullyFaithful {G : D ⥤ C} (F : C ⥤ D)
    (adj : F ⊣ G) (h : G.FullyFaithful) :
    SchemaCofractal F adj := by
  simp [SchemaCofractal]
  haveI : G.Full := h.full
  haveI : G.Faithful := h.faithful
  exact inferInstance

/-! ## Level 3 — `Cofractal`: both layers iso -/

/-- A functor `F : C ⥤ D` is a **cofractal** if it is both a schema cofractal
and an instance cofractal.  Dual to `Fractal` from `FractalOP.lean`. -/
def Cofractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  SchemaCofractal F adj ∧ InstanceCofractal F

/-- Project the schema-cofractal component. -/
theorem Cofractal.schemaCofractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : Cofractal F adj) : SchemaCofractal F adj :=
  h.1

/-- Project the instance-cofractal component. -/
theorem Cofractal.instanceCofractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : Cofractal F adj) : InstanceCofractal F :=
  h.2

/-- The identity functor is a cofractal. -/
theorem cofractal_id
    [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    Cofractal (𝟭 C) (Adjunction.id (C := C)) :=
  ⟨schemaCofractal_id, instanceCofractal_id⟩

/-- An equivalence of categories yields a cofractal functor.  Dual to
`fractal_of_equivalence` in `FractalOP.lean`. -/
theorem cofractal_of_equivalence (e : C ≌ D)
    [∀ X : C ⥤ Type v, e.functor.HasPointwiseLeftKanExtension X] :
    Cofractal e.functor e.toAdjunction :=
  ⟨schemaCofractal_of_equivalence e,
   instanceCofractal_of_equivalence e⟩
