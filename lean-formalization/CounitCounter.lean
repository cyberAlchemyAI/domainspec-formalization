import ReflectiveHierarchy
import CoreflectiveHierarchy

/-!
# CounitCounter — Independence of Unit-Side and Counit-Side Defects

We exhibit a small concrete functor `F : Discrete (Fin 1) ⥤ Discrete (Fin 2)`
(the inclusion sending the unique object to `⟨0⟩`) for which:

* the **unit** of `F.lanAdjunction (Type 0)` is componentwise iso, so `F`
  satisfies the unit-side `InstanceCoreflective` property from `CoreflectiveHierarchy.lean`;
* the **counit** of `F.lanAdjunction (Type 0)` is *not* iso, so `F` does *not*
  satisfy the counit-side `InstanceReflective` property from `ReflectiveHierarchy.lean`.

The argument:

* `F` is fully faithful (between discrete categories the inclusion of a
  sub-set of objects is fully faithful), so `instanceCoreflective_of_fullyFaithful`
  gives the unit-side claim.
* If `InstanceReflective F` held, then the full counit nat-trans of
  `F.lanAdjunction _` would be iso, hence by Mathlib's
  `Adjunction.fullyFaithfulROfIsIsoCounit` the precomposition functor
  `F* = (whiskeringLeft _ _ _).obj F` would be faithful.  We refute this
  directly by exhibiting two distinct natural transformations
  `α, β : const Bool ⟶ const Bool` (on `Discrete (Fin 2)`) whose restrictions
  along `F` coincide.

This proves the two defects are genuinely independent, not just notationally
dual.

## Naming

See `NAMING.md`. The main result also appears as
`lan_fullyFaithful_not_imply_pullback_faithful` in standard Mathlib
vocabulary: `Finc.lan` is fully faithful while `Finc*` is not even
faithful.
-/

open CategoryTheory Functor

/-! ## The concrete `F : Discrete (Fin 1) ⥤ Discrete (Fin 2)` -/

/-- Inclusion of `Discrete (Fin 1)` into `Discrete (Fin 2)` at index `0`. -/
def Finc : Discrete (Fin 1) ⥤ Discrete (Fin 2) :=
  Discrete.functor (fun _ => ⟨0, by decide⟩)

@[simp] lemma Finc_obj (x : Discrete (Fin 1)) : Finc.obj x = ⟨0, by decide⟩ := by
  rcases x with ⟨i⟩
  rfl

/-- Every object of `Discrete (Fin 1)` is `⟨0⟩`. -/
lemma fin1_eq_zero (i : Fin 1) : i = ⟨0, by decide⟩ := by
  apply Fin.ext
  have : i.val < 1 := i.isLt
  omega

/-- `Finc` is fully faithful: between discrete categories, the only morphisms
are identities, so injectivity on objects (here vacuous on the singleton
source) plus thin homs gives fully faithfulness. -/
def Finc_fullyFaithful : Finc.FullyFaithful where
  preimage {X Y} _ := by
    rcases X with ⟨i⟩; rcases Y with ⟨j⟩
    have hi := fin1_eq_zero i
    have hj := fin1_eq_zero j
    subst hi; subst hj
    exact 𝟙 _

/-- `Finc` admits pointwise left Kan extensions for every `X`: the source is
finite, so colimits indexed by costructured-arrow categories exist in `Type`. -/
instance (X : Discrete (Fin 1) ⥤ Type) : Finc.HasPointwiseLeftKanExtension X :=
  fun _ => inferInstance

/-! ## Unit side: `Finc` is an instance coreflective. -/

theorem Finc_instanceCoreflective : InstanceCoreflective Finc :=
  instanceCoreflective_of_fullyFaithful Finc Finc_fullyFaithful

/-! ## Counit side: two natural transformations distinguishing `Finc*` faithfulness. -/

/-- The constant `Discrete (Fin 2) ⥤ Type` functor at `Bool`. -/
abbrev Gconst : Discrete (Fin 2) ⥤ Type := (Functor.const _).obj Bool

/-- The identity natural transformation on `Gconst`. -/
def αTriv : Gconst ⟶ Gconst := 𝟙 _

/-- A function `Bool → Bool` indexed by `Fin 2`: identity at `0`, negation at `1`. -/
def flipAt (i : Fin 2) : Bool → Bool :=
  if i.val = 0 then (fun b => b) else (fun b => !b)

@[simp] lemma flipAt_zero (h : (0 : ℕ) < 2) : flipAt ⟨0, h⟩ = fun b => b := by
  simp [flipAt]

@[simp] lemma flipAt_one (h : (1 : ℕ) < 2) : flipAt ⟨1, h⟩ = fun b => !b := by
  simp [flipAt]

/-- The natural transformation on `Gconst` that is identity at `⟨0⟩` and
boolean-negation at `⟨1⟩`.  Naturality is automatic since `Discrete (Fin 2)`
has only identity morphisms. -/
def αFlip : Gconst ⟶ Gconst where
  app := fun ⟨i⟩ => TypeCat.ofHom (flipAt i)
  naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    have hij : i = j := Discrete.eq_of_hom f
    subst hij
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst hf
    simp

/-- `αTriv ≠ αFlip`: they differ on the second object `⟨1⟩`. -/
lemma αTriv_ne_αFlip : αTriv ≠ αFlip := by
  intro h
  -- Apply both sides at object `⟨1⟩` and then evaluate at `true`.
  have happ : αTriv.app ⟨1, by decide⟩ = αFlip.app ⟨1, by decide⟩ :=
    congrArg (fun η => η.app ⟨1, by decide⟩) h
  have hfun :
      (αTriv.app ⟨1, by decide⟩).hom true = (αFlip.app ⟨1, by decide⟩).hom true := by
    rw [happ]
  -- LHS reduces to `true`; RHS reduces to `false` by `flipAt_one`.
  have hL : (αTriv.app ⟨1, by decide⟩).hom true = true := rfl
  have hR : (αFlip.app ⟨1, by decide⟩).hom true = false := by
    show (TypeCat.ofHom (flipAt ⟨1, by decide⟩)).hom true = false
    show flipAt ⟨1, by decide⟩ true = false
    unfold flipAt
    simp
  rw [hL, hR] at hfun
  exact Bool.noConfusion hfun

/-- `whiskerLeft Finc αTriv = whiskerLeft Finc αFlip`: both restrictions are
the identity natural transformation on `Finc ⋙ Gconst`, since the only object
of `Discrete (Fin 1)` lands at `⟨0⟩` where `αFlip` is the identity. -/
lemma whiskerLeft_αTriv_eq_αFlip :
    (whiskerLeft Finc αTriv : Finc ⋙ Gconst ⟶ Finc ⋙ Gconst) =
      whiskerLeft Finc αFlip := by
  ext x b
  rcases x with ⟨i⟩
  have hi := fin1_eq_zero i
  subst hi
  -- LHS: identity at ⟨0⟩ applied to b → b. RHS: flipAt ⟨0⟩ applied to b → b.
  show b = (αFlip.app (Finc.obj ⟨⟨0, by decide⟩⟩)).hom b
  show b = (TypeCat.ofHom (flipAt ⟨0, by decide⟩)).hom b
  show b = flipAt ⟨0, by decide⟩ b
  unfold flipAt
  simp

/-- Distinct natural transformations witness that `(whiskeringLeft _ _ _).obj Finc`
is **not faithful**. -/
theorem whiskeringLeft_Finc_not_faithful :
    ¬ Functor.Faithful ((whiskeringLeft (Discrete (Fin 1)) (Discrete (Fin 2)) Type).obj Finc) := by
  intro hF
  apply αTriv_ne_αFlip
  apply hF.map_injective (X := Gconst) (Y := Gconst)
  exact whiskerLeft_αTriv_eq_αFlip

/-! ## Main independence theorem. -/

/-- **Independence of the unit-side and counit-side defects.**

There exists a functor (namely `Finc`) which is an `InstanceCoreflective` (unit
side iso) but *not* an `InstanceReflective` (counit side iso).  Hence the two
coreflective hierarchies are genuinely independent. -/
theorem instanceReflective_independent_of_instanceCoreflective :
    InstanceCoreflective Finc ∧ ¬ InstanceReflective Finc := by
  refine ⟨Finc_instanceCoreflective, ?_⟩
  intro hCof
  -- Lift componentwise iso of the counit to iso of the whole nat trans.
  haveI : ∀ Y, IsIso ((Finc.lanAdjunction (Type 0)).counit.app Y) := fun Y => by
    haveI : ∀ d, IsIso (((Finc.lanAdjunction (Type 0)).counit.app Y).app d) := hCof Y
    exact NatIso.isIso_of_isIso_app _
  haveI : IsIso (Finc.lanAdjunction (Type 0)).counit :=
    NatIso.isIso_of_isIso_app _
  -- Hence the right adjoint is fully faithful — in particular faithful.
  have hFF : ((whiskeringLeft _ _ (Type 0)).obj Finc).FullyFaithful :=
    Adjunction.fullyFaithfulROfIsIsoCounit (Finc.lanAdjunction (Type 0))
  exact whiskeringLeft_Finc_not_faithful hFF.faithful

/-- **Standard-language restatement** of
`instanceReflective_independent_of_instanceCoreflective`. The functor `Finc` exhibits
the asymmetry: its left Kan extension `Finc.lan` is fully faithful, but its
precomposition functor `Finc* = (whiskeringLeft _ _ _).obj Finc` is not
faithful (hence not fully faithful). In the language of `NAMING.md`: unit-side
fully-faithfulness does not imply counit-side fully-faithfulness. -/
theorem lan_fullyFaithful_not_imply_pullback_faithful :
    Nonempty ((Finc.lan : (Discrete (Fin 1) ⥤ Type) ⥤ (Discrete (Fin 2) ⥤ Type)).FullyFaithful) ∧
      ¬ Functor.Faithful ((whiskeringLeft (Discrete (Fin 1)) (Discrete (Fin 2)) Type).obj Finc) := by
  refine ⟨⟨fullyFaithful_lan_of_instanceCoreflective Finc Finc_instanceCoreflective⟩,
          whiskeringLeft_Finc_not_faithful⟩
