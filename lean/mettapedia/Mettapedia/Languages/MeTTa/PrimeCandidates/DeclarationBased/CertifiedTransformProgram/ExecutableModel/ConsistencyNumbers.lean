import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencyModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Functions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Pairs
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Comparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Telescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Coherence

/-!
# The numbers and the sets in the consistency model

In the consistency model of the executable package the numbers relate the terms
with one numeral, and the sets, a rigid type, relate every two terms. The
constants of the numbers and the sets are valid terms of their declared types:

* the numbers and the sets are types of the lowest universe;
* `zero` and `suc` build numerals;
* addition computes in the model, by recursion on its second argument, the
  numeral of the sum;
* `Power` and the iterated power set return sets, which are all related;
* the recursor relates its instances at related motives, values at zero and
  steps, and numbers with one numeral. By induction on the numeral: at zero it
  computes to its value at zero, and at a successor to the step applied to the
  recursive call. A motive gives the types at numbers with one numeral one
  denotation.

The recursor's type is dependent; its validity and the validity of its parts
are hypotheses of its theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative.Consistency
open TelescopeAbstraction (subst_empty)
open SetProfile (zeroNative sucNative)
open Package (numRecName U0 numT numRecType numRecApp numRecTelescope)

namespace CodeModel

/-- Every universe of the tower is a universe of the model. -/
private theorem sort_isUniverse (v : Nat → Nat) (u : LevelExpr Nat) :
    (model v).rules.isUniverse (.sort u) :=
  LevelTower.IsUniverse.sort u

/-- The numbers relate, at every level and world, the terms with one numeral. -/
private theorem interp_num (v : Nat → Nat) (l : Nat) {n : Nat} (ξ : World (model v).reading n) :
    InterpAt (model v) l ξ numT
      (fun t t' => ∃ k, NumVal (model v).toSetting t k ∧ NumVal (model v).toSetting t' k) :=
  Interp.num .refl

/-- The sets, a rigid type, relate every two terms, at every level and world. -/
private theorem interp_set (v : Nat → Nat) (l : Nat) {n : Nat} (ξ : World (model v).reading n) :
    InterpAt (model v) l ξ setT (fun _ _ => True) :=
  Interp.rigid (args := []) .refl
    ((modelRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_set)
    (by decide : setN ≠ propN) (by decide : setN ≠ holdsN)

/-- A closed term is a valid term of a closed type interpreted at every world by
one relation, when that relation relates the term to itself. -/
private theorem valid_of_interp (v : Nat → Nat) {c T : Tower.Tm 0} {l : Nat}
    {D : ∀ {m : Nat}, World (model v).reading m → Rel Tower.Head m}
    (interp : ∀ {m : Nat} (ξ : World (model v).reading m), InterpAt (model v) l ξ (liftClosed T) (D ξ))
    (rel : ∀ {m : Nat} (ξ : World (model v).reading m), D ξ (liftClosed c) (liftClosed c)) :
    ValidTm (model v) .nil c T := by
  refine ⟨fun {_ ξ _ _} _ => ?_, fun {_ ξ _ _} _ {_} den => ?_⟩
  · rw [subst_empty, subst_empty]
    exact ⟨D ξ, ⟨l, interp ξ⟩, ⟨l, interp ξ⟩⟩
  · rw [subst_empty] at den
    rw [subst_empty, subst_empty, Den.deterministic (model_laws v) den ⟨l, interp ξ⟩]
    exact rel ξ

/-! ## Addition computes -/

/-- Reducing the second argument of an addition. -/
theorem add_scrutinee (v : Nat → Nat) {n : Nat} (x : Tower.Tm n) {y y' : Tower.Tm n}
    (red : WhRed (model v).rules (model v).roles y y') :
    WhRed (model v).rules (model v).roles (.app (.app (.const addN) x) y)
      (.app (.app (.const addN) x) y') :=
  WhRed.scrutinee (before := [x]) (after := []) modelRoles_add rfl red

/-- `add x zero = x` in the model. -/
theorem add_zero_step (v : Nat → Nat) {n : Nat} (x : Tower.Tm n) :
    WhStep (model v).rules (model v).roles (.app (.app (.const addN) x) (.const zeroN)) x := by
  have rule : equations.family
      (.app (.app (.const addN) (.var 0)) (.const zeroN) : Tower.Tm 1) (.var 0) :=
    equation_listed 0 (by decide) rfl
  exact .root (model_step_of_rules (equation_sound rule fun _ => x))

/-- `add x (suc a) = suc (add x a)` in the model. -/
theorem add_suc_step (v : Nat → Nat) {n : Nat} (x a : Tower.Tm n) :
    WhStep (model v).rules (model v).roles (.app (.app (.const addN) x) (.app (.const sucN) a))
      (.app (.const sucN) (.app (.app (.const addN) x) a)) := by
  have rule : equations.family
      (.app (.app (.const addN) (.var 1)) (.app (.const sucN) (.var 0)) : Tower.Tm 2)
      (.app (.const sucN) (.app (.app (.const addN) (.var 1)) (.var 0))) :=
    equation_listed 1 (by decide) rfl
  exact .root (model_step_of_rules (equation_sound rule (consSub a fun _ => x)))

/-- The sum of two numbers with numerals has, in the model, the numeral of the
sum. -/
theorem numVal_add (v : Nat → Nat) {n : Nat} {x y : Tower.Tm n} {i j : Nat}
    (left : NumVal (model v).toSetting x i) (right : NumVal (model v).toSetting y j) :
    NumVal (model v).toSetting (.app (.app (.const addN) x) y) (i + j) := by
  induction right with
  | zero red =>
      exact left.expand (Relation.ReflTransGen.tail (add_scrutinee v x red) (add_zero_step v x))
  | suc red _ ih =>
      exact .suc (Relation.ReflTransGen.tail (add_scrutinee v x red) (add_suc_step v x _)) ih

/-! ## The numbers, the sets and their constants -/

/-- The numbers are a type of the lowest universe. -/
theorem valid_num (v : Nat → Nat) : ValidTm (model v) .nil (.const numN) U0 := by
  refine ⟨ValidTy.sort (sort_isUniverse v _), fun {_ ξ _ _} _ {_} den => ?_⟩
  rw [Den.sort_inv (model_laws v) (sort_isUniverse v _) den]
  intro _ ξ' _ _
  exact ⟨_, interp_num v _ ξ', interp_num v _ ξ'⟩

/-- The sets are a type of the lowest universe. -/
theorem valid_set (v : Nat → Nat) : ValidTm (model v) .nil (.const setN) U0 := by
  refine ⟨ValidTy.sort (sort_isUniverse v _), fun {_ ξ _ _} _ {_} den => ?_⟩
  rw [Den.sort_inv (model_laws v) (sort_isUniverse v _) den]
  intro _ ξ' _ _
  exact ⟨_, interp_set v _ ξ', interp_set v _ ξ'⟩

/-- `zero` is the numeral `0`. -/
theorem valid_zero (v : Nat → Nat) : ValidTm (model v) .nil (.const zeroN) numT :=
  valid_of_interp v (interp_num v 0) fun _ => ⟨0, .zero .refl, .zero .refl⟩

/-- `suc` sends a number to the next numeral. -/
theorem valid_suc (v : Nat → Nat) : ValidTm (model v) .nil (.const sucN) (.pi numT numT) :=
  valid_of_interp v (interp_arrow (dom := numT) (cod := numT) (interp_num v 0) (interp_num v 0))
    fun _ => by
      intro _ _ _ _ _ _ _ related
      obtain ⟨k, left, right⟩ := related
      exact ⟨k + 1, .suc .refl left, .suc .refl right⟩

/-- `Power` returns a set. -/
theorem valid_power (v : Nat → Nat) : ValidTm (model v) .nil (.const powerN) powerType :=
  valid_of_interp v (interp_arrow (dom := setT) (cod := setT) (interp_set v 0) (interp_set v 0))
    fun _ => by
      intro _ _ _ _ _ _ _ _
      trivial

/-- Addition sends numbers with numerals to the numeral of their sum. -/
theorem valid_add (v : Nat → Nat) : ValidTm (model v) .nil (.const addN) addType :=
  valid_of_interp v (interp_arrow (dom := numT) (cod := .pi numT numT) (interp_num v 0)
      (interp_arrow (dom := numT) (cod := numT) (interp_num v 0) (interp_num v 0)))
    fun _ => by
      intro _ _ _ _ _ _ _ left _ _ ρ _ _ _ _ right
      obtain ⟨i, x, x'⟩ := left
      obtain ⟨j, y, y'⟩ := right
      exact ⟨i + j, numVal_add v (x.rename ρ) y, numVal_add v (x'.rename ρ) y'⟩

/-- The iterated power set returns a set. -/
theorem valid_pow (v : Nat → Nat) : ValidTm (model v) .nil (.const powN) powType :=
  valid_of_interp v (interp_arrow (dom := numT) (cod := .pi setT setT) (interp_num v 0)
      (interp_arrow (dom := setT) (cod := setT) (interp_set v 0) (interp_set v 0)))
    fun _ => by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      trivial

/-! ## The recursor -/

/-- Reducing the number of an application of the recursor. -/
theorem numRec_scrutinee (v : Nat → Nat) {n : Nat} (P z s : Tower.Tm n) {t t' : Tower.Tm n}
    (red : WhRed (model v).rules (model v).roles t t') :
    WhRed (model v).rules (model v).roles (numRecApp P z s t) (numRecApp P z s t') :=
  WhRed.scrutinee (before := [P, z, s]) (after := []) modelRoles_numRec rfl red

/-- The recursor at zero returns its value at zero. -/
theorem numRec_zero_step (v : Nat → Nat) {n : Nat} (P z s : Tower.Tm n) :
    WhStep (model v).rules (model v).roles (numRecApp P z s zeroNative) z := by
  have rule : equations.family
      (numRecApp (.var 2) (.var 1) (.var 0) zeroNative : Tower.Tm 3) (.var 1) :=
    equation_listed 5 (by decide) rfl
  exact .root (model_step_of_rules (equation_sound rule (consSub s (consSub z fun _ => P))))

/-- The recursor at a successor applies the step to the recursive call. -/
theorem numRec_suc_step (v : Nat → Nat) {n : Nat} (P z s a : Tower.Tm n) :
    WhStep (model v).rules (model v).roles (numRecApp P z s (sucNative a))
      (.app (.app s a) (numRecApp P z s a)) := by
  have rule : equations.family
      (numRecApp (.var 3) (.var 2) (.var 1) (sucNative (.var 0)) : Tower.Tm 4)
      (.app (.app (.var 1) (.var 0)) (numRecApp (.var 3) (.var 2) (.var 1) (.var 0))) :=
    equation_listed 6 (by decide) rfl
  exact .root (model_step_of_rules
    (equation_sound rule (consSub a (consSub s (consSub z fun _ => P)))))

/-- The recursor at a motive, a value at zero and a step, applied to numbers with
one numeral, gives terms related at the motive at the first number. -/
theorem numRec_related (v : Nat → Nat) {m : Nat} {ξ : World (model v).reading m} {P P' z z' s s' : Tower.Tm m}
    (motive : ∀ {a b : Tower.Tm m} {k : Nat}, NumVal (model v).toSetting a k →
      NumVal (model v).toSetting b k →
        ∃ R, Den (model v) ξ (.app P a) R ∧ Den (model v) ξ (.app P b) R)
    (atZero : ∀ {R : Rel Tower.Head m}, Den (model v) ξ (.app P zeroNative) R → R z z')
    (atSuc : ∀ {a b h h' : Tower.Tm m} {k : Nat}, NumVal (model v).toSetting a k →
      NumVal (model v).toSetting b k → (∀ {R : Rel Tower.Head m}, Den (model v) ξ (.app P a) R → R h h') →
        ∀ {R : Rel Tower.Head m}, Den (model v) ξ (.app P (sucNative a)) R →
          R (.app (.app s a) h) (.app (.app s' b) h'))
    (k : Nat) :
    ∀ {t t' : Tower.Tm m}, NumVal (model v).toSetting t k → NumVal (model v).toSetting t' k →
      ∀ {R : Rel Tower.Head m}, Den (model v) ξ (.app P t) R →
        R (numRecApp P z s t) (numRecApp P' z' s' t') := by
  have laws := model_laws v
  induction k with
  | zero =>
      intro t t' ht ht' R den
      cases ht with
      | zero red =>
          cases ht' with
          | zero red' =>
              obtain ⟨R₀, denT, denZ⟩ := motive (b := zeroNative) (.zero red) (.zero .refl)
              rw [Den.deterministic laws den denT]
              exact Den.expandLeft denT
                (Relation.ReflTransGen.tail (numRec_scrutinee v P z s red)
                  (numRec_zero_step v P z s))
                (Den.expandRight denT
                  (Relation.ReflTransGen.tail (numRec_scrutinee v P' z' s' red')
                    (numRec_zero_step v P' z' s'))
                  (atZero denZ))
  | succ k ih =>
      intro t t' ht ht' R den
      cases ht with
      | @suc _ a _ red ha =>
          cases ht' with
          | @suc _ a' _ red' ha' =>
              obtain ⟨R₁, denT, denS⟩ := motive (b := sucNative a) (.suc red ha) (.suc .refl ha)
              rw [Den.deterministic laws den denT]
              exact Den.expandLeft denT
                (Relation.ReflTransGen.tail (numRec_scrutinee v P z s red)
                  (numRec_suc_step v P z s a))
                (Den.expandRight denT
                  (Relation.ReflTransGen.tail (numRec_scrutinee v P' z' s' red')
                    (numRec_suc_step v P' z' s' a'))
                  (atSuc ha ha' (ih ha ha') denS))

/-- The type of the step at a number `a`: `P a → P (suc a)`. -/
private theorem inst0_stepType {n : Nat} (P a : Tower.Tm n) :
    Presentation.inst0 a (.pi (.app (Presentation.rename wk P) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1)))) =
      .pi (.app P a) (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) := by
  show Tm.pi (.app (Presentation.inst0 a (Presentation.rename wk P)) a)
      (.app (Presentation.subst (liftSub (subst0 a))
          (Presentation.rename wk (Presentation.rename wk P)))
        (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, subst_liftSub_wk]
  show Tm.pi (.app P a) (.app (Presentation.rename wk
      (Presentation.inst0 a (Presentation.rename wk P))) (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk]

/-- The motive at the successor of a number, over one more variable,
instantiated at a value. -/
private theorem inst0_sucApp {n : Nat} (P a h : Tower.Tm n) :
    Presentation.inst0 h (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) =
      .app P (sucNative a) := by
  show Tm.app (Presentation.inst0 h (Presentation.rename wk P))
      (sucNative (Presentation.inst0 h (Presentation.rename wk a))) = _
  simp only [inst0_rename_wk]

/-- A motive related to another at `num → U0` sends numbers with one numeral to
types with one denotation. -/
private theorem numRec_motive (v : Nat → Nat) {m : Nat} {ξ : World (model v).reading m} {RP : Rel Tower.Head m}
    (den : Den (model v) ξ (.pi numT U0) RP) {P P' : Tower.Tm m} (related : RP P P')
    {a b : Tower.Tm m} {k : Nat} (left : NumVal (model v).toSetting a k)
    (right : NumVal (model v).toSetting b k) :
    ∃ R, Den (model v) ξ (.app P a) R ∧ Den (model v) ξ (.app P' b) R := by
  obtain ⟨RU, denU, types⟩ := Den.pi_app_exists (model_laws v) den related fun denA => by
    rw [Den.num_inv (model_laws v) denA]
    exact ⟨k, left, right⟩
  rw [Den.sort_inv (model_laws v) (sort_isUniverse v _) denU] at types
  obtain ⟨R, first, second⟩ := universeAt.den types
  exact ⟨R, ⟨_, first⟩, ⟨_, second⟩⟩

/-- A step related to another at `Π v:num. P v → P (suc v)` sends numbers with
one numeral and values related at the motive to values related at the motive at
the successor. -/
private theorem numRec_step (v : Nat → Nat) {m : Nat} {ξ : World (model v).reading m} {P s s' : Tower.Tm m}
    {RS : Rel Tower.Head m}
    (den : Den (model v) ξ (.pi numT (.pi (.app (Presentation.rename wk P) (.var 0))
      (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1))))) RS)
    (related : RS s s') {a b h h' : Tower.Tm m} {k : Nat}
    (left : NumVal (model v).toSetting a k) (right : NumVal (model v).toSetting b k)
    (values : ∀ {R : Rel Tower.Head m}, Den (model v) ξ (.app P a) R → R h h')
    {R : Rel Tower.Head m} (denSuc : Den (model v) ξ (.app P (sucNative a)) R) :
    R (.app (.app s a) h) (.app (.app s' b) h') := by
  obtain ⟨R₁, den₁, related₁⟩ := Den.pi_app_exists (model_laws v) den related fun denA => by
    rw [Den.num_inv (model_laws v) denA]
    exact ⟨k, left, right⟩
  rw [inst0_stepType] at den₁
  obtain ⟨R₂, den₂, related₂⟩ := Den.pi_app_exists (model_laws v) den₁ related₁ values
  rw [inst0_sucApp] at den₂
  rw [Den.deterministic (model_laws v) denSuc den₂]
  exact related₂

/-- The recursor of the numbers is a valid term of its declared type. -/
theorem valid_numRec (v : Nat → Nat) (validType : ValidTy (model v) .nil numRecType)
    (partsType : Structured (model v) .nil numRecType) :
    ValidTm (model v) .nil (.const numRecName) numRecType := by
  obtain ⟨_, validResult, _⟩ := ValidTy.close_parts (.snoc numRecTelescope numT)
    (C := .app (.var 3) (.var 0)) validType partsType
  refine ValidTm.close (model_laws v) (.snoc numRecTelescope numT) (C := .app (.var 3) (.var 0))
    (f := .const numRecName) validType partsType
    ⟨validResult, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨⟨⟨⟨-, RP, denP, relP⟩, RZ, denZ, relZ⟩, RS, denS, relS⟩, RT, denT, relT⟩ := e
  change Den (model v) ξ (.pi numT U0) RP at denP
  change RP (σ 3) (σ' 3) at relP
  change Den (model v) ξ (.app (σ 3) zeroNative) RZ at denZ
  change RZ (σ 2) (σ' 2) at relZ
  change Den (model v) ξ (.pi numT (.pi (.app (Presentation.rename wk (σ 3)) (.var 0))
    (.app (Presentation.rename wk (Presentation.rename wk (σ 3))) (sucNative (.var 1))))) RS
    at denS
  change RS (σ 1) (σ' 1) at relS
  change Den (model v) ξ (.const (model v).num) RT at denT
  change RT (σ 0) (σ' 0) at relT
  change Den (model v) ξ (.app (σ 3) (σ 0)) R at den
  show R (numRecApp (σ 3) (σ 2) (σ 1) (σ 0)) (numRecApp (σ' 3) (σ' 2) (σ' 1) (σ' 0))
  rw [Den.num_inv (model_laws v) denT] at relT
  obtain ⟨k, number, number'⟩ := relT
  exact numRec_related v
    (numRec_motive v denP (Den.refl_left (model_laws v) denP relP))
    (fun denZ' => by
      rw [Den.deterministic (model_laws v) denZ' denZ]
      exact relZ)
    (numRec_step v denS relS) k number number' den

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
