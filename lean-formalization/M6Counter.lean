import Mathlib

open CategoryTheory Functor Limits

set_option maxHeartbeats 400000

/-! ## L2: two objects with one non-identity arrow -/

inductive L2Obj | a | b
  deriving DecidableEq

namespace L2Obj

def Hom : L2Obj → L2Obj → Type
  | a, a => Unit
  | a, b => Unit
  | b, a => PEmpty
  | b, b => Unit

def id' : (X : L2Obj) → Hom X X
  | .a => ()
  | .b => ()

def comp' : {X Y Z : L2Obj} → Hom X Y → Hom Y Z → Hom X Z
  | .a, .a, .a, _, _ => ()
  | .a, .a, .b, _, _ => ()
  | .a, .b, .a, _, h => h.elim
  | .a, .b, .b, _, _ => ()
  | .b, .a, _, h, _ => h.elim
  | .b, .b, .a, _, h => h.elim
  | .b, .b, .b, _, _ => ()

instance : SmallCategory L2Obj where
  Hom := Hom
  id := id'
  comp := comp'
  id_comp {X Y} f := by cases X <;> cases Y <;> first | rfl | exact f.elim
  comp_id {X Y} f := by cases X <;> cases Y <;> first | rfl | exact f.elim
  assoc {W X Y Z} f g h := by
    cases W <;> cases X <;> cases Y <;> cases Z <;>
      first | rfl | exact f.elim | exact g.elim | exact h.elim

end L2Obj

/-! ## L1 = Discrete (Fin 2) -/

abbrev L1 := Discrete (Fin 2)
abbrev a₁ : L1 := ⟨0⟩
abbrev b₁ : L1 := ⟨1⟩

def ΔObj : Fin 2 → L2Obj
  | 0 => .a
  | 1 => .b

def Δ : L1 ⥤ L2Obj := Discrete.functor ΔObj

@[simp] lemma Δ_obj_a₁ : Δ.obj a₁ = L2Obj.a := rfl
@[simp] lemma Δ_obj_b₁ : Δ.obj b₁ = L2Obj.b := rfl

lemma Δ_obj_injective : Function.Injective Δ.obj := by
  rintro ⟨i⟩ ⟨j⟩ h
  congr 1
  fin_cases i <;> fin_cases j <;>
    first | rfl | (simp [Δ, Discrete.functor, ΔObj] at h)

instance : Δ.Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

/-! ## I = const Unit -/

abbrev I : L1 ⥤ Type := (Functor.const L1).obj Unit

/-! ## Pointwise Kan extension exists for every X. -/

instance (X : L1 ⥤ Type) : Δ.HasPointwiseLeftKanExtension X := fun _ => inferInstance

/-! ## The conjecture -/

def M6Strong : Prop :=
  ∀ {C₁ C₂ : Type} [SmallCategory C₁] [SmallCategory C₂]
    (F : C₁ ⥤ C₂) [∀ X : C₁ ⥤ Type, F.HasPointwiseLeftKanExtension X],
    Function.Injective F.obj → F.Faithful →
      ∀ (X : C₁ ⥤ Type) (c : C₁),
        IsIso (((F.lanAdjunction (Type 0)).unit.app X).app c)

/-! ## Separator: build a cocone over `CostructuredArrow.proj Δ L2Obj.b ⋙ I`
that distinguishes the two objects of the comma category. -/

namespace M6CounterAux

/-- The two canonical objects of `CostructuredArrow Δ L2Obj.b`. -/
def objA : CostructuredArrow Δ L2Obj.b :=
  CostructuredArrow.mk (Y := a₁) (show L2Obj.a ⟶ L2Obj.b from ())

def objB : CostructuredArrow Δ L2Obj.b :=
  CostructuredArrow.mk (Y := b₁) (𝟙 L2Obj.b)

/-- A morphism in `CostructuredArrow Δ L2Obj.b` between two objects forces their
`.left` components to be equal (the only morphisms in `Discrete (Fin 2)` are identities). -/
lemma left_eq_of_hom {X Y : CostructuredArrow Δ L2Obj.b} (φ : X ⟶ Y) : X.left = Y.left := by
  have h := Discrete.eq_of_hom φ.left
  rcases X with ⟨⟨i⟩, _, _⟩
  rcases Y with ⟨⟨j⟩, _, _⟩
  simp at h
  subst h
  rfl

/-- Separator: cocone with apex `Bool` distinguishing objects whose left is `a₁`. -/
def sepCocone : Cocone (CostructuredArrow.proj Δ L2Obj.b ⋙ I) where
  pt := Bool
  ι :=
    { app := fun X => TypeCat.ofHom (fun _ => decide (X.left = a₁))
      naturality := by
        intro X Y φ
        have hxy : X.left = Y.left := left_eq_of_hom φ
        ext _
        simp [hxy] }

end M6CounterAux

open M6CounterAux

/-! ## Main theorem -/

theorem m6_strong_refuted : ¬ M6Strong := by
  intro hM6
  haveI hiso : IsIso (((Δ.lanAdjunction (Type 0)).unit.app I).app b₁) :=
    hM6 Δ Δ_obj_injective inferInstance I b₁
  have hunit_eq : ((Δ.lanAdjunction (Type 0)).unit.app I).app b₁
                = (Δ.lanUnit.app I).app b₁ := by
    rw [lanAdjunction_unit]
  rw [hunit_eq] at hiso
  -- `IsIso` of a Type-morphism iff bijective on the underlying function.
  have hbij : Function.Bijective ((Δ.lanUnit.app I).app b₁) :=
    (CategoryTheory.isIso_iff_bijective _).mp hiso
  -- Iso to a colimit at L2Obj.b.
  let isoCol : (Δ.lan.obj I).obj L2Obj.b ≅
      colimit (CostructuredArrow.proj Δ L2Obj.b ⋙ I) :=
    Δ.leftKanExtensionObjIsoColimit I L2Obj.b
  -- Separator descends through colimit.desc.
  let d : colimit (CostructuredArrow.proj Δ L2Obj.b ⋙ I) ⟶ Bool :=
    colimit.desc _ sepCocone
  -- Distinct elements in the colimit, distinguished by `d`.
  set yA := colimit.ι (CostructuredArrow.proj Δ L2Obj.b ⋙ I) objA () with hyA
  set yB := colimit.ι (CostructuredArrow.proj Δ L2Obj.b ⋙ I) objB () with hyB
  have hA : d yA = true := by
    have heq : colimit.ι (CostructuredArrow.proj Δ L2Obj.b ⋙ I) objA ≫ d
             = sepCocone.ι.app objA := colimit.ι_desc sepCocone objA
    show (colimit.ι (CostructuredArrow.proj Δ L2Obj.b ⋙ I) objA ≫ d) () = true
    rw [heq]; rfl
  have hB : d yB = false := by
    have heq : colimit.ι (CostructuredArrow.proj Δ L2Obj.b ⋙ I) objB ≫ d
             = sepCocone.ι.app objB := colimit.ι_desc sepCocone objB
    show (colimit.ι (CostructuredArrow.proj Δ L2Obj.b ⋙ I) objB ≫ d) () = false
    rw [heq]; rfl
  have hne : yA ≠ yB := by
    intro hEq
    have hh : d yA = d yB := congrArg _ hEq
    rw [hA, hB] at hh
    exact Bool.noConfusion hh
  -- Pull through isoCol.inv to get distinct elements in (Δ.lan.obj I).obj L2Obj.b.
  set xA : (Δ.lan.obj I).obj L2Obj.b := isoCol.inv yA with hxA
  set xB : (Δ.lan.obj I).obj L2Obj.b := isoCol.inv yB with hxB
  have e1 : isoCol.hom xA = yA := Iso.inv_hom_id_apply isoCol _
  have e2 : isoCol.hom xB = yB := Iso.inv_hom_id_apply isoCol _
  have hxneq : xA ≠ xB := by
    intro hEq
    apply hne
    rw [← e1, ← e2, hEq]
  -- Bijective from `I.obj b₁ = Unit` forces all elements equal.
  have hone : ∀ x y : (Δ.lan.obj I).obj L2Obj.b, x = y := by
    intro x y
    obtain ⟨ux, hux⟩ := hbij.surjective x
    obtain ⟨uy, huy⟩ := hbij.surjective y
    cases ux; cases uy
    rw [← hux, ← huy]
  exact hxneq (hone xA xB)
