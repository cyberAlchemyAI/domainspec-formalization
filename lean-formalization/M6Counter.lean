import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

open CategoryTheory Functor Limits

set_option maxHeartbeats 400000

universe u v

/-! ## L2: two objects with one non-identity arrow (universe-polymorphic) -/

inductive L2Obj : Type u | a | b
  deriving DecidableEq

namespace L2Obj

def Hom : L2Obj.{u} → L2Obj.{u} → Type u
  | a, a => PUnit
  | a, b => PUnit
  | b, a => PEmpty
  | b, b => PUnit

def id' : (X : L2Obj.{u}) → Hom X X
  | .a => PUnit.unit
  | .b => PUnit.unit

def comp' : {X Y Z : L2Obj.{u}} → Hom X Y → Hom Y Z → Hom X Z
  | .a, .a, .a, _, _ => PUnit.unit
  | .a, .a, .b, _, _ => PUnit.unit
  | .a, .b, .a, _, h => h.elim
  | .a, .b, .b, _, _ => PUnit.unit
  | .b, .a, _, h, _ => h.elim
  | .b, .b, .a, _, h => h.elim
  | .b, .b, .b, _, _ => PUnit.unit

instance : SmallCategory L2Obj.{u} where
  Hom := Hom
  id := id'
  comp := comp'
  id_comp {X Y} f := by cases X <;> cases Y <;> first | rfl | exact f.elim
  comp_id {X Y} f := by cases X <;> cases Y <;> first | rfl | exact f.elim
  assoc {W X Y Z} f g h := by
    cases W <;> cases X <;> cases Y <;> cases Z <;>
      first | rfl | exact f.elim | exact g.elim | exact h.elim

end L2Obj

/-! ## L1 = Discrete (ULift (Fin 2)) -/

abbrev L1 := Discrete (ULift.{u} (Fin 2))
abbrev a₁ : L1.{u} := ⟨ULift.up 0⟩
abbrev b₁ : L1.{u} := ⟨ULift.up 1⟩

def ΔObj : ULift.{u} (Fin 2) → L2Obj.{u}
  | ⟨0⟩ => .a
  | ⟨1⟩ => .b

def Δ : L1.{u} ⥤ L2Obj.{u} := Discrete.functor ΔObj

@[simp] lemma Δ_obj_a₁ : Δ.{u}.obj a₁ = L2Obj.a := rfl
@[simp] lemma Δ_obj_b₁ : Δ.{u}.obj b₁ = L2Obj.b := rfl

lemma Δ_obj_injective : Function.Injective Δ.{u}.obj := by
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ h
  congr 2
  fin_cases i <;> fin_cases j <;>
    first | rfl | (simp [Δ, Discrete.functor, ΔObj] at h)

instance : Δ.{u}.Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

/-! ## I = const PUnit -/

abbrev I : L1.{u} ⥤ Type v := (Functor.const L1.{u}).obj PUnit.{v+1}

/-! ## Smallness witnesses so colimits in `Type v` over the comma exist. -/

instance : Small.{v} L1.{u} := by
  refine ⟨⟨ULift.{v} (Fin 2),
    ⟨fun ⟨⟨n⟩⟩ => ULift.up n, fun ⟨n⟩ => ⟨⟨n⟩⟩, ?_, ?_⟩⟩⟩
  · rintro ⟨⟨_⟩⟩; rfl
  · rintro ⟨_⟩; rfl

instance L2Obj.hom_subsingleton (X Y : L2Obj.{u}) : Subsingleton (X ⟶ Y) := by
  cases X <;> cases Y <;> first
    | (change Subsingleton PUnit.{u+1}; infer_instance)
    | (change Subsingleton PEmpty.{u+1}; infer_instance)

instance : LocallySmall.{v} L2Obj.{u} where
  hom_small _ _ := inferInstance

/-! ## Pointwise Kan extension exists for every X. -/

instance (X : L1.{u} ⥤ Type v) : (Δ.{u}).HasPointwiseLeftKanExtension X :=
  fun _ => inferInstance

/-! ## The conjecture (universe-polymorphic statement) -/

def M6Strong.{u', v'} : Prop :=
  ∀ {C₁ C₂ : Type u'} [SmallCategory C₁] [SmallCategory C₂]
    (F : C₁ ⥤ C₂) [∀ X : C₁ ⥤ Type v', F.HasPointwiseLeftKanExtension X],
    Function.Injective F.obj → F.Faithful →
      ∀ (X : C₁ ⥤ Type v') (c : C₁),
        IsIso (((F.lanAdjunction (Type v')).unit.app X).app c)

/-! ## Separator: cocone with apex `ULift Bool` distinguishing `left = a₁`. -/

namespace M6CounterAux

def objA : CostructuredArrow Δ.{u} L2Obj.b :=
  CostructuredArrow.mk (Y := a₁) (show L2Obj.a ⟶ L2Obj.b from PUnit.unit)

def objB : CostructuredArrow Δ.{u} L2Obj.b :=
  CostructuredArrow.mk (Y := b₁) (𝟙 L2Obj.b)

lemma left_eq_of_hom {X Y : CostructuredArrow Δ.{u} L2Obj.b} (φ : X ⟶ Y) :
    X.left = Y.left := by
  have h := Discrete.eq_of_hom φ.left
  rcases X with ⟨⟨i⟩, _, _⟩
  rcases Y with ⟨⟨j⟩, _, _⟩
  simp at h
  subst h
  rfl

def sepCocone : Cocone (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) where
  pt := ULift.{v} Bool
  ι :=
    { app := fun X => TypeCat.ofHom (fun _ => ULift.up (decide (X.left = a₁)))
      naturality := by
        intro X Y φ
        have hxy : X.left = Y.left := left_eq_of_hom φ
        ext _
        simp [hxy] }

end M6CounterAux

open M6CounterAux

/-! ## Main theorem (universe-polymorphic) -/

theorem m6_strong_refuted_poly : ¬ M6Strong.{u, v} := by
  intro hM6
  haveI hiso : IsIso (((Δ.{u}.lanAdjunction (Type v)).unit.app I.{u, v}).app b₁) :=
    hM6 Δ.{u} Δ_obj_injective inferInstance I.{u, v} b₁
  have hunit_eq : ((Δ.{u}.lanAdjunction (Type v)).unit.app I.{u, v}).app b₁
                = (Δ.{u}.lanUnit.app I.{u, v}).app b₁ := by
    rw [lanAdjunction_unit]
  rw [hunit_eq] at hiso
  have hbij : Function.Bijective ((Δ.{u}.lanUnit.app I.{u, v}).app b₁) :=
    (CategoryTheory.isIso_iff_bijective _).mp hiso
  let isoCol : (Δ.{u}.lan.obj I.{u, v}).obj L2Obj.b ≅
      colimit (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) :=
    Δ.{u}.leftKanExtensionObjIsoColimit I.{u, v} L2Obj.b
  let d : colimit (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) ⟶ ULift.{v} Bool :=
    colimit.desc _ sepCocone
  set yA := colimit.ι (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) objA PUnit.unit
    with hyA
  set yB := colimit.ι (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) objB PUnit.unit
    with hyB
  have hA : d yA = ULift.up true := by
    have heq : colimit.ι (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) objA ≫ d
             = sepCocone.ι.app objA := colimit.ι_desc sepCocone objA
    show (colimit.ι (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) objA ≫ d) PUnit.unit
       = ULift.up true
    rw [heq]; rfl
  have hB : d yB = ULift.up false := by
    have heq : colimit.ι (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) objB ≫ d
             = sepCocone.ι.app objB := colimit.ι_desc sepCocone objB
    show (colimit.ι (CostructuredArrow.proj Δ.{u} L2Obj.b ⋙ I.{u, v}) objB ≫ d) PUnit.unit
       = ULift.up false
    rw [heq]; rfl
  have hne : yA ≠ yB := by
    intro hEq
    have hh : d yA = d yB := congrArg _ hEq
    rw [hA, hB] at hh
    exact Bool.noConfusion (ULift.up.inj hh)
  set xA : (Δ.{u}.lan.obj I.{u, v}).obj L2Obj.b := isoCol.inv yA with hxA
  set xB : (Δ.{u}.lan.obj I.{u, v}).obj L2Obj.b := isoCol.inv yB with hxB
  have e1 : isoCol.hom xA = yA := Iso.inv_hom_id_apply isoCol _
  have e2 : isoCol.hom xB = yB := Iso.inv_hom_id_apply isoCol _
  have hxneq : xA ≠ xB := by
    intro hEq
    apply hne
    rw [← e1, ← e2, hEq]
  -- Bijective from `I.obj b₁ = PUnit` forces all elements equal.
  have hone : ∀ x y : (Δ.{u}.lan.obj I.{u, v}).obj L2Obj.b, x = y := by
    intro x y
    obtain ⟨ux, hux⟩ := hbij.surjective x
    obtain ⟨uy, huy⟩ := hbij.surjective y
    cases ux; cases uy
    rw [← hux, ← huy]
  exact hxneq (hone xA xB)

/-! ## Original Type-0 corollary -/

theorem m6_strong_refuted : ¬ M6Strong.{0, 0} := m6_strong_refuted_poly.{0, 0}
