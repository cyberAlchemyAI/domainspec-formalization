/-
  M2Counter — refutation of the unrestricted Schema-Adjunction (M2)
  Conjecture.

  We reuse the four-object setup from `M6Counter.lean`:
    L1 = Discrete (Fin 2), L2 = {a, b, f : a → b}, Δ the inclusion.
  The presheaf P_b = (Δ.op ⋙ yoneda.obj L2Obj.b) on L1 has values
    P_b(a₁) = (L2Obj.a ⟶ L2Obj.b) ≃ Unit (the morphism `f`),
    P_b(b₁) = (L2Obj.b ⟶ L2Obj.b) ≃ Unit (the identity),
  but no object G ∈ {a₁, b₁} of L1 can represent it: the discrete
  L1 has empty cross hom-sets, while P_b is nontrivial at *both*
  L1-objects. Hence the unrestricted M2 conjecture is false.
-/

import M6Counter

open CategoryTheory Functor

-- §A.1 — Hom-set inhabitants in L2Obj, witnessing the nontriviality of P_b.

/-- The unique element of `Hom_{L2Obj}(L2Obj.b, L2Obj.b)`, i.e. `id_b`. -/
def L2_idb : (L2Obj.b ⟶ L2Obj.b) := 𝟙 L2Obj.b

/-- The unique non-identity arrow `L2Obj.a ⟶ L2Obj.b`. -/
def L2_f : (L2Obj.a ⟶ L2Obj.b) := (() : Unit)

-- §A.2 — Cross hom-sets in `L1 = Discrete (Fin 2)` are empty.

/-- There is no morphism `b₁ ⟶ a₁` in `Discrete (Fin 2)`. -/
lemma no_hom_b₁_a₁ : (b₁ ⟶ a₁) → False := by
  intro h
  have heq : (1 : Fin 2) = (0 : Fin 2) := Discrete.eq_of_hom h
  exact absurd heq (by decide)

/-- There is no morphism `a₁ ⟶ b₁` in `Discrete (Fin 2)`. -/
lemma no_hom_a₁_b₁ : (a₁ ⟶ b₁) → False := by
  intro h
  have heq : (0 : Fin 2) = (1 : Fin 2) := Discrete.eq_of_hom h
  exact absurd heq (by decide)

-- §A.3 — Presheaf abbreviation and pointwise unfolding.

/-- The presheaf `P_b(X) = Hom_{L2}(Δ X, L2Obj.b)` on `L1`. -/
abbrev P_b : L1ᵒᵖ ⥤ Type := Δ.op ⋙ yoneda.obj L2Obj.b

@[simp] lemma P_b_obj_a₁ : P_b.obj (Opposite.op a₁) = (L2Obj.a ⟶ L2Obj.b) := rfl
@[simp] lemma P_b_obj_b₁ : P_b.obj (Opposite.op b₁) = (L2Obj.b ⟶ L2Obj.b) := rfl

-- §A.4 — Refutation of the unrestricted M2 conjecture.

/-- **Unrestricted M2 is false.** There is no general guarantee that the
    presheaf `(Δ.op ⋙ yoneda.obj b)` is representable: at the four-object
    counterexample, `b = L2Obj.b` already breaks it. -/
theorem M2_unrestricted_false :
    ¬ (∀ {C₁ C₂ : Type} [SmallCategory C₁] [SmallCategory C₂]
         (F : C₁ ⥤ C₂) (b : C₂),
         Functor.IsRepresentable (F.op ⋙ yoneda.obj b)) := by
  intro hM2
  -- Specialize at the M6 counterexample.
  have hRepr : Functor.IsRepresentable (Δ.op ⋙ yoneda.obj L2Obj.b) :=
    hM2 Δ L2Obj.b
  -- Extract a representing object G : L1 and a `RepresentableBy` witness.
  obtain ⟨G, ⟨e⟩⟩ := hRepr.has_representation
  -- Case-split on G : Discrete (Fin 2).
  rcases G with ⟨i⟩
  fin_cases i
  · -- G = a₁: pull `id_b` back through `e.homEquiv` at X = b₁
    --         to get a morphism `b₁ ⟶ a₁`, which is impossible.
    have h : b₁ ⟶ ⟨0⟩ := e.homEquiv.symm L2_idb
    exact no_hom_b₁_a₁ h
  · -- G = b₁: pull `f : a → b` back through `e.homEquiv` at X = a₁
    --         to get a morphism `a₁ ⟶ b₁`, which is impossible.
    have h : a₁ ⟶ ⟨1⟩ := e.homEquiv.symm L2_f
    exact no_hom_a₁_b₁ h
