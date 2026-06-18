import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Whiskering

/-!
# Coreflective Functors — A Four-Level Hierarchy

This file defines four graduated notions of "coreflective functor," arranged from
weakest to strongest.  The split is motivated by the **M2 conjecture** of the
DomainSpec project: while the instance-level iso property can be established
from standard Mathlib adjunction theory, the *schema-level* iso property (i.e.
the unit of an adjunction `F ⊣ G` being a natural isomorphism) is conjectural
at the level of database schemas and requires an explicit adjunction argument.

## The four levels

| Name | Layer | Strength | Notes |
|---|---|---|---|
| `LanFaithful F` | instance | unit componentwise mono | the weakest level; `Lan_F` faithful |
| `InstanceCoreflective F` | instance | unit componentwise **iso** | no collapse, no spurious Skolem witnesses |
| `SchemaCoreflective F adj` | schema | unit of `adj : F ⊣ G` is an **iso** | explicit adjunction; existence is the M2 conjecture |
| `IsCoreflective F adj` | both | `SchemaCoreflective ∧ InstanceCoreflective` | matches the prose definition: residue zero on both layers |

The reason `SchemaCoreflective` and `IsCoreflective` take an explicit adjunction argument
(rather than a typeclass) is that, at the schema level, it is currently
*unknown* whether a right adjoint to `F` exists in general.  Making the
adjunction explicit means we do not accidentally `sorry`-in its existence via
typeclass inference.

## References

- DomainSpec project, `docs/` directory, M2 conjecture.
- Mathlib: `CategoryTheory.Adjunction`, `CategoryTheory.Functor.KanExtension`.

## Naming

See `NAMING.md` for the translation between this file's "coreflective"
vocabulary and standard Mathlib terms. In short:
`LanFaithful F` is `F.lan.Faithful`; `InstanceCoreflective F` is `F.FullyFaithful`
(presheaf-`Type v` witness); `SchemaCoreflective F adj` is `IsIso adj.unit`
(equivalently `F.FullyFaithful` via `adj`). The names persist because
they label *taxonomy slots* in the coreflective/reflective/Lan/Ran hierarchy,
not new mathematical concepts.
-/

open CategoryTheory Functor

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## Level 1 — `LanFaithful`: instance-level mono -/

/-- A functor `F : C ⥤ D` is **Lan-faithful** if the unit of the canonical
adjunction `Lan_F ⊣ F*` between `(C ⥤ Type v)` and `(D ⥤ Type v)` is
componentwise monic.

This is the weakest coreflective-like property.  It is equivalent to `Lan_F` being
a faithful functor, and is a necessary (but not sufficient) condition for the
full `IsCoreflective` property.

This was previously the standalone `Fractal` definition in the v0 file (now
removed); it is the weakest level of the hierarchy, kept here as `LanFaithful`. -/
def LanFaithful (F : C ⥤ D) [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    Mono (((F.lanAdjunction (Type v)).unit.app X).app c)

/-- Equivalent reformulation: `Lan_F : (C ⥤ Type v) ⥤ (D ⥤ Type v)` is faithful. -/
theorem lanFaithful_iff_lan_faithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] :
    LanFaithful F ↔ Functor.Faithful
      (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)) := by
  constructor
  · intro hF
    haveI : ∀ X, Mono ((F.lanAdjunction (Type v)).unit.app X) := by
      intro X
      haveI : ∀ Y, Mono (((F.lanAdjunction (Type v)).unit.app X).app Y) := hF X
      exact NatTrans.mono_of_mono_app _
    exact (F.lanAdjunction (Type v)).faithful_L_of_mono_unit_app
  · intro _ X c
    haveI : Mono ((F.lanAdjunction (Type v)).unit.app X) := inferInstance
    infer_instance

/-- The identity functor is Lan-faithful.  `𝟭 C` is fully faithful, so the
unit of its `lanAdjunction` is an iso, hence componentwise mono. -/
theorem lanFaithful_id [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    LanFaithful (𝟭 C) := by
  intro X c
  haveI : IsIso ((((𝟭 C).lanAdjunction (Type v)).unit.app X).app c) :=
    NatIso.isIso_app_of_isIso _ c
  infer_instance

/-- Every fully faithful functor is Lan-faithful. -/
theorem lanFaithful_of_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    LanFaithful F := by
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  intro X c
  haveI : IsIso (((F.lanAdjunction (Type v)).unit.app X).app c) :=
    NatIso.isIso_app_of_isIso _ c
  infer_instance

/-! ## Level 2 — `InstanceCoreflective`: instance-level iso -/

/-- A functor `F : C ⥤ D` is an **instance coreflective** if the unit of the
canonical adjunction `Lan_F ⊣ F*` is componentwise an isomorphism.

This is strictly stronger than `LanFaithful`: it says not only that no
information is lost (mono) but also that no spurious Skolem witnesses are
introduced (epi / split-epi component). -/
def InstanceCoreflective (F : C ⥤ D) [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    IsIso (((F.lanAdjunction (Type v)).unit.app X).app c)

/-- Every instance coreflective functor is Lan-faithful. -/
theorem lanFaithful_of_instanceCoreflective (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : InstanceCoreflective F) : LanFaithful F := by
  intro X c
  haveI := h X c
  infer_instance

/-- The identity functor is an instance coreflective. -/
theorem instanceCoreflective_id [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    InstanceCoreflective (𝟭 C) := by
  intro X c
  exact NatIso.isIso_app_of_isIso _ c

/-- Every fully faithful functor is an instance coreflective. -/
theorem instanceCoreflective_of_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    InstanceCoreflective F := by
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  intro X c
  exact NatIso.isIso_app_of_isIso _ c

/-- `InstanceCoreflective F` implies `F.lan` is fully faithful. The unit of
`F.lanAdjunction _` is the natural transformation whose components are
the maps in the definition of `InstanceCoreflective`; componentwise iso
implies whole-nat-trans iso (by `NatIso.isIso_of_isIso_app`), which
yields `F.lan.FullyFaithful` via `Adjunction.fullyFaithfulLOfIsIsoUnit`.

This is the precise Mathlib-level statement of "`InstanceCoreflective F` is
equivalent to fully faithfulness." The canonical equivalence between
`F.FullyFaithful` and `F.lan.FullyFaithful` is proved separately in
`YonedaBridge.lean` (`Functor.fullyFaithfulEquivLanFullyFaithful`); the form
below is the direct unit-side reformulation. -/
noncomputable def fullyFaithful_lan_of_instanceCoreflective (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : InstanceCoreflective F) :
    (F.lan : (C ⥤ Type v) ⥤ (D ⥤ Type v)).FullyFaithful := by
  haveI : ∀ X, IsIso ((F.lanAdjunction (Type v)).unit.app X) := fun X => by
    haveI : ∀ c, IsIso (((F.lanAdjunction (Type v)).unit.app X).app c) := h X
    exact NatIso.isIso_of_isIso_app _
  haveI : IsIso (F.lanAdjunction (Type v)).unit := NatIso.isIso_of_isIso_app _
  exact Adjunction.fullyFaithfulLOfIsIsoUnit (F.lanAdjunction (Type v))

/-! ## Level 3 — `SchemaCoreflective`: schema-level iso -/

/-- A functor `F : C ⥤ D` with an explicit right adjoint `G` and adjunction
`adj : F ⊣ G` is a **schema coreflective** if the unit `adj.unit : 𝟭 C ⟶ F ⋙ G`
is a natural isomorphism.

The adjunction is an *explicit argument* (not a typeclass) because its
existence at the schema level is the content of the **M2 conjecture** in the
DomainSpec project.  Making it explicit prevents typeclass inference from
silently assuming the conjecture. -/
def SchemaCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G) : Prop :=
  IsIso adj.unit

/-- An equivalence of categories yields a schema coreflective: the unit of the
adjunction `e.toAdjunction : e.functor ⊣ e.inverse` is a natural isomorphism.
For an equivalence the unit is iso by construction. -/
theorem schemaCoreflective_of_equivalence (e : C ≌ D) :
    SchemaCoreflective e.functor e.toAdjunction := by
  simp [SchemaCoreflective]
  exact inferInstance

/-- The identity functor is a schema coreflective, witnessed by `Adjunction.id`. -/
theorem schemaCoreflective_id :
    SchemaCoreflective (𝟭 C) (Adjunction.id (C := C)) := by
  unfold SchemaCoreflective
  exact inferInstance

/-- A fully faithful functor `F` with a right adjoint `G` is a schema coreflective:
`[Full F] [Faithful F]` implies the unit of `F ⊣ G` is an iso. -/
theorem schemaCoreflective_of_fullyFaithful {G : D ⥤ C} (F : C ⥤ D)
    (adj : F ⊣ G) (h : F.FullyFaithful) :
    SchemaCoreflective F adj := by
  simp [SchemaCoreflective]
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  exact inferInstance

/-! ## Level 4 — `IsCoreflective`: both layers iso -/

/-- A functor `F : C ⥤ D` is a **coreflective** (in the full sense) if it is both a
schema coreflective and an instance coreflective.

This is the definition that matches the prose: "residue zero on both the schema
layer and the instance layer."

`adj` is explicit for the same reason as in `SchemaCoreflective`: the existence of a
schema-level right adjoint is conjectural (M2 conjecture). -/
def IsCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  SchemaCoreflective F adj ∧ InstanceCoreflective F

/-- Project the schema-coreflective component. -/
theorem IsCoreflective.schemaCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : IsCoreflective F adj) : SchemaCoreflective F adj :=
  h.1

/-- Project the instance-coreflective component. -/
theorem IsCoreflective.instanceCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : IsCoreflective F adj) : InstanceCoreflective F :=
  h.2

/-- The identity functor is a coreflective. -/
theorem isCoreflective_id
    [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    IsCoreflective (𝟭 C) (Adjunction.id (C := C)) :=
  ⟨schemaCoreflective_id, instanceCoreflective_id⟩

/-- An equivalence of categories yields a coreflective functor. -/
theorem isCoreflective_of_equivalence (e : C ≌ D)
    [∀ X : C ⥤ Type v, e.functor.HasPointwiseLeftKanExtension X] :
    IsCoreflective e.functor e.toAdjunction :=
  ⟨schemaCoreflective_of_equivalence e,
   instanceCoreflective_of_fullyFaithful e.functor e.fullyFaithfulFunctor⟩

/-- Every fully faithful functor (equipped with an explicit right adjoint) is a
coreflective. -/
theorem isCoreflective_of_fullyFaithful {G : D ⥤ C} (F : C ⥤ D)
    (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    IsCoreflective F adj :=
  ⟨schemaCoreflective_of_fullyFaithful F adj h,
   instanceCoreflective_of_fullyFaithful F h⟩
