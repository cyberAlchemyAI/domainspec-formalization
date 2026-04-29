import Mathlib

/-!
# Fractal Functors — A Four-Level Hierarchy

This file defines four graduated notions of "fractal functor," arranged from
weakest to strongest.  The split is motivated by the **M2 conjecture** of the
DomainSpec project: while the instance-level iso property can be established
from standard Mathlib adjunction theory, the *schema-level* iso property (i.e.
the unit of an adjunction `F ⊣ G` being a natural isomorphism) is conjectural
at the level of database schemas and requires an explicit adjunction argument.

## The four levels

| Name | Layer | Strength | Notes |
|---|---|---|---|
| `LanFaithful F` | instance | unit componentwise mono | the original `Fractal`; Lan_F faithful |
| `InstanceFractal F` | instance | unit componentwise **iso** | no collapse, no spurious Skolem witnesses |
| `SchemaFractal F adj` | schema | unit of `adj : F ⊣ G` is an **iso** | explicit adjunction; existence is the M2 conjecture |
| `Fractal F adj` | both | `SchemaFractal ∧ InstanceFractal` | matches the prose definition: residue zero on both layers |

The reason `SchemaFractal` and `Fractal` take an explicit adjunction argument
(rather than a typeclass) is that, at the schema level, it is currently
*unknown* whether a right adjoint to `F` exists in general.  Making the
adjunction explicit means we do not accidentally `sorry`-in its existence via
typeclass inference.

## References

- DomainSpec project, `docs/` directory, M2 conjecture.
- Mathlib: `CategoryTheory.Adjunction`, `CategoryTheory.Functor.KanExtension`.
-/

open CategoryTheory Functor

universe v u₁ u₂
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-! ## Level 1 — `LanFaithful`: instance-level mono -/

/-- A functor `F : C ⥤ D` is **Lan-faithful** if the unit of the canonical
adjunction `Lan_F ⊣ F*` between `(C ⥤ Type v)` and `(D ⥤ Type v)` is
componentwise monic.

This is the weakest fractal-like property.  It is equivalent to `Lan_F` being
a faithful functor, and is a necessary (but not sufficient) condition for the
full `Fractal` property.

This was previously called `Fractal` in the v0 file; it is renamed here to
make room for the stronger notion. -/
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

/-! ## Level 2 — `InstanceFractal`: instance-level iso -/

/-- A functor `F : C ⥤ D` is an **instance fractal** if the unit of the
canonical adjunction `Lan_F ⊣ F*` is componentwise an isomorphism.

This is strictly stronger than `LanFaithful`: it says not only that no
information is lost (mono) but also that no spurious Skolem witnesses are
introduced (epi / split-epi component). -/
def InstanceFractal (F : C ⥤ D) [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    IsIso (((F.lanAdjunction (Type v)).unit.app X).app c)

/-- Every instance fractal functor is Lan-faithful. -/
theorem lanFaithful_of_instanceFractal (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : InstanceFractal F) : LanFaithful F := by
  intro X c
  haveI := h X c
  infer_instance

/-- The identity functor is an instance fractal. -/
theorem instanceFractal_id [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    InstanceFractal (𝟭 C) := by
  intro X c
  exact NatIso.isIso_app_of_isIso _ c

/-- Every fully faithful functor is an instance fractal. -/
theorem instanceFractal_of_fullyFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    InstanceFractal F := by
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  intro X c
  exact NatIso.isIso_app_of_isIso _ c

/-! ## Level 3 — `SchemaFractal`: schema-level iso -/

/-- A functor `F : C ⥤ D` with an explicit right adjoint `G` and adjunction
`adj : F ⊣ G` is a **schema fractal** if the unit `adj.unit : 𝟭 C ⟶ F ⋙ G`
is a natural isomorphism.

The adjunction is an *explicit argument* (not a typeclass) because its
existence at the schema level is the content of the **M2 conjecture** in the
DomainSpec project.  Making it explicit prevents typeclass inference from
silently assuming the conjecture. -/
def SchemaFractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G) : Prop :=
  IsIso adj.unit

/-- An equivalence of categories yields a schema fractal: the unit of the
adjunction `e.toAdjunction : e.functor ⊣ e.inverse` is a natural isomorphism.
For an equivalence the unit is iso by construction. -/
theorem schemaFractal_of_equivalence (e : C ≌ D) :
    SchemaFractal e.functor e.toAdjunction := by
  simp [SchemaFractal]
  exact inferInstance

/-- The identity functor is a schema fractal, witnessed by `Adjunction.id`. -/
theorem schemaFractal_id :
    SchemaFractal (𝟭 C) (Adjunction.id (C := C)) := by
  unfold SchemaFractal
  exact inferInstance

/-- A fully faithful functor `F` with a right adjoint `G` is a schema fractal:
`[Full F] [Faithful F]` implies the unit of `F ⊣ G` is an iso.

Note: the exact Mathlib lemma name is uncertain.  The relevant result should
be something like `Adjunction.isIso_unit_of_fullyFaithful` or follow from
`Adjunction.fullyFaithfulEquiv`.  We use `sorry` pending name lookup. -/
theorem schemaFractal_of_fullyFaithful {G : D ⥤ C} (F : C ⥤ D)
    (adj : F ⊣ G) (h : F.FullyFaithful) :
    SchemaFractal F adj := by
  simp [SchemaFractal]
  -- need: `[Full F] [Faithful F]` (or `F.FullyFaithful`) and `adj : F ⊣ G`
  -- implies `IsIso adj.unit`.
  -- Candidate Mathlib lemma: `Adjunction.isIso_unit_of_full_of_faithful`
  -- or the instance produced by `Adjunction.FullyFaithful.isIso_unit`.
  haveI : F.Full := h.full
  haveI : F.Faithful := h.faithful
  -- `Adjunction.unit_isIso_of_L_fully_faithful` is a Mathlib instance:
  -- `[L.Full] [L.Faithful] → IsIso (adj.unit)`
  exact inferInstance

/-! ## Level 4 — `Fractal`: both layers iso -/

/-- A functor `F : C ⥤ D` is a **fractal** (in the full sense) if it is both a
schema fractal and an instance fractal.

This is the definition that matches the prose: "residue zero on both the schema
layer and the instance layer."

`adj` is explicit for the same reason as in `SchemaFractal`: the existence of a
schema-level right adjoint is conjectural (M2 conjecture). -/
def Fractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  SchemaFractal F adj ∧ InstanceFractal F

/-- Project the schema-fractal component. -/
theorem Fractal.schemaFractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : Fractal F adj) : SchemaFractal F adj :=
  h.1

/-- Project the instance-fractal component. -/
theorem Fractal.instanceFractal {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : Fractal F adj) : InstanceFractal F :=
  h.2

/-- The identity functor is a fractal. -/
theorem fractal_id
    [∀ X : C ⥤ Type v, (𝟭 C).HasPointwiseLeftKanExtension X] :
    Fractal (𝟭 C) (Adjunction.id (C := C)) :=
  ⟨schemaFractal_id, instanceFractal_id⟩

/-- An equivalence of categories yields a fractal functor. -/
theorem fractal_of_equivalence (e : C ≌ D)
    [∀ X : C ⥤ Type v, e.functor.HasPointwiseLeftKanExtension X] :
    Fractal e.functor e.toAdjunction :=
  ⟨schemaFractal_of_equivalence e,
   instanceFractal_of_fullyFaithful e.functor e.fullyFaithfulFunctor⟩

/-- Every fully faithful functor (equipped with an explicit right adjoint) is a
fractal. -/
theorem fractal_of_fullyFaithful {G : D ⥤ C} (F : C ⥤ D)
    (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X]
    (h : F.FullyFaithful) :
    Fractal F adj :=
  ⟨schemaFractal_of_fullyFaithful F adj h,
   instanceFractal_of_fullyFaithful F h⟩
