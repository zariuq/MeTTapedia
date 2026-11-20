import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Recursion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerArithmetic

/-!
# The type on the step and the type in the knowledge agree

The knowledge hosts the normalization model's tower with the natural numbers, its recursor, and
addition by structural recursion on the second argument (`TowerArithmeticModel`). A content of the
step reads as a closed term of the model (`toModel`): `zeroE` as the constructor `zero`, `succE x`
as `succ` applied to the reading of `x`.

**Closed canonical terms of the model's numbers** (`ClosedCanonicalNum`): closed terms typed at `num`
in the empty context that are constructor forms of `num` all the way down, by the model's declared
constructor list (`CtorForm`). They are exactly the model's numerals (`ctorForm_iff`), each is typed
(`numTm_typed`) and a weak-head normal form of the model (`ctorForm_whnf`), and two of them are equal
in the model exactly when they are the same numeral (`numTm_equal`, from the model's injectivity and
discrimination of constructors).

**Membership agrees, by the reading's construction** (`generated_iff_closedCanonical`,
`closedCanonical_has_row`): a row of the number region is generated exactly when its content reads
as a closed canonical term of the model's numbers, and each such term is the reading of exactly one
generated row. The reading `toModel` is defined on numerals only (`toModel_eq_some`), so the backward
direction does not use the conditions on the term. The agreement against a total reading of every
content, junk included, is `Translation.generated_iff_translate`.

**Values agree** (`add_numerals`, `answer_agrees`): the model's addition of two numerals is equal, at
`num` in the empty context, to the numeral of the sum; so for a request on two generated rows, every
final state of the step's addition holds an answer whose reading is a closed canonical number, the
one the model's addition of the readings equals, and no other closed canonical number is. The two
computations recurse on different arguments; only their values are compared.

**What the framework does not state, and this module does not use**: that every closed term typed at
`num` is equal to a closed canonical one (canonicity). The model gives weak-head normal forms and,
through its logical relation, normal forms that are constructor forms or neutral; that no closed
neutral is typed at `num` in the empty context is not stated there. The agreement above needs only
the canonical terms and the computation of the recursive definition on them; `Canonicity` proves the
missing fact for this package and extends the agreement to every closed term of `num`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open WhenTypesApply.ThatsAll
open NamesOnTheStep NamesOnTheStep.IssuingControls
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality Normalization
open TowerNumbersModel (num zero succ ctors u mem_zero mem_succ)
open TowerArithmeticModel (add)

namespace Agreement

/-! ## Reading contents as closed terms of the model -/

/-- The model's numeral of a natural number. -/
def numTm : ℕ → Tm Tower.Head 0
  | 0 => .const zero
  | k + 1 => .app (.const succ) (numTm k)

/-- **Reading a content as a closed term of the model.** -/
def toModel : Expr → Option (Tm Tower.Head 0)
  | .sym 100 => some (.const zero)
  | .app (.sym 101) x => (toModel x).map (.app (.const succ))
  | _ => none

theorem toModel_numeral (k : ℕ) : toModel (numeral k) = some (numTm k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (toModel (numeral k)).map (.app (.const succ)) = some (numTm (k + 1))
      rw [ih]
      rfl

/-- What reads as a term is a numeral, read as the model's numeral. -/
theorem toModel_eq_some {e : Expr} {t : Tm Tower.Head 0} (read : toModel e = some t) :
    ∃ k, e = numeral k ∧ t = numTm k := by
  induction e generalizing t with
  | sym k =>
      by_cases same : k = 100
      · subst same
        simp only [toModel, Option.some.injEq] at read
        exact ⟨0, rfl, read.symm⟩
      · simp [toModel, same] at read
  | app f a _ iha =>
      cases f with
      | sym k =>
          by_cases same : k = 101
          · subst same
            simp only [toModel, Option.map_eq_some_iff] at read
            obtain ⟨t', inner, rfl⟩ := read
            obtain ⟨k, rfl, rfl⟩ := iha inner
            exact ⟨k + 1, rfl, rfl⟩
          · simp [toModel, same] at read
      | app _ _ => simp [toModel] at read
      | name _ => simp [toModel] at read
      | code _ => simp [toModel] at read
  | name n => simp [toModel] at read
  | code e _ => simp [toModel] at read

/-! ## Closed canonical terms of the model's numbers -/

/-- **Constructor forms of `num` all the way down**, by the model's declared constructor list. -/
inductive CtorForm : Tm Tower.Head 0 → Prop
  | ctor {k : DeclName} {fields : List (Normalization.Field Tower.Head)}
      {args : List (Tm Tower.Head 0)} :
      (k, fields) ∈ ctors → args.length = fields.length → (∀ a ∈ args, CtorForm a) →
      CtorForm (appSpine (.const k) args)

theorem numTm_injective : ∀ {j k : ℕ}, numTm j = numTm k → j = k
  | 0, 0, _ => rfl
  | 0, _ + 1, same => by cases same
  | _ + 1, 0, same => by cases same
  | j + 1, k + 1, same => by
      simp only [numTm, Tm.app.injEq, true_and] at same
      exact congrArg (· + 1) (numTm_injective same)

theorem numTm_ctorForm : ∀ k : ℕ, CtorForm (numTm k)
  | 0 => CtorForm.ctor (args := []) mem_zero rfl fun _ member => absurd member List.not_mem_nil
  | k + 1 => CtorForm.ctor (args := [numTm k]) mem_succ rfl fun a member => by
      rw [List.mem_singleton.mp member]
      exact numTm_ctorForm k

/-- **The constructor forms of `num` are the model's numerals.** -/
theorem ctorForm_iff {t : Tm Tower.Head 0} : CtorForm t ↔ ∃ k, t = numTm k := by
  constructor
  · intro form
    induction form with
    | @ctor k fields args mem length _ ih =>
        simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
        rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have empty : args = [] := List.eq_nil_of_length_eq_zero length
          subst empty
          exact ⟨0, rfl⟩
        · match args, length, ih with
          | [a], _, ih =>
              obtain ⟨j, rfl⟩ := ih a (List.mem_singleton_self _)
              exact ⟨j + 1, rfl⟩
  · rintro ⟨k, rfl⟩
    exact numTm_ctorForm k

variable (lv : LevelExpr Nat)

/-- **A closed canonical term of the model's numbers**: typed at `num` in the empty context, and a
constructor form all the way down. -/
def ClosedCanonicalNum (t : Tm Tower.Head 0) : Prop :=
  Typed (TowerArithmeticModel.rules lv) .nil t (.const num) ∧ CtorForm t

theorem num_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed (TowerArithmeticModel.rules lv) Γ (.const num) (.head u) :=
  TowerNumbersModel.num_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort
    (TowerArithmeticModel.declaredNum lv)

theorem zero_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed (TowerArithmeticModel.rules lv) Γ (.const zero) (.const num) :=
  .const (TowerArithmeticModel.declaredZero lv) (num_typed lv) (.sort _)

theorem succ_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed (TowerArithmeticModel.rules lv) Γ (.const succ) (.pi (.const num) (.const num)) :=
  .const (TowerArithmeticModel.declaredSucc lv)
    (.piForm (num_typed lv) (.sort _) (num_typed lv) (.sort _) (.sorts _ _)) (.sort _)

theorem add_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed (TowerArithmeticModel.rules lv) Γ (.const add)
      (.pi (.const num) (.pi (.const num) (.const num))) :=
  .const (TowerArithmeticModel.declaredAdd lv)
    (.piForm (num_typed lv) (.sort _)
      (.piForm (num_typed lv) (.sort _) (num_typed lv) (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _))
    (.sort _)

/-- Every numeral of the model is typed at `num` in the empty context. -/
theorem numTm_typed : ∀ k : ℕ, Typed (TowerArithmeticModel.rules lv) .nil (numTm k) (.const num)
  | 0 => zero_typed lv
  | k + 1 => .appElim (succ_typed lv) (numTm_typed k)

theorem closedCanonical_iff {t : Tm Tower.Head 0} : ClosedCanonicalNum lv t ↔ ∃ k, t = numTm k := by
  constructor
  · exact fun canonical => ctorForm_iff.mp canonical.2
  · rintro ⟨k, rfl⟩
    exact ⟨numTm_typed lv k, numTm_ctorForm k⟩

/-- **Closed canonical terms are weak-head normal forms of the model.** -/
theorem ctorForm_whnf {t : Tm Tower.Head 0} (form : CtorForm t) :
    Whnf (TowerArithmeticModel.rules lv) TowerArithmeticModel.roles t := by
  cases form with
  | ctor mem _ _ =>
      exact canonical_whnf (TowerArithmeticModel.shape lv)
        (ctorSpine_canonical (S := TowerArithmeticModel.setting lv fun _ => 0)
          (TowerArithmeticModel.setting_roles_num lv _) mem _)

/-- **Two numerals of the model are equal at `num` exactly when they are the same numeral.** -/
theorem numTm_equal : ∀ {m n : ℕ},
    Equal (TowerArithmeticModel.rules lv) .nil (numTm m) (numTm n) (.const num) → m = n
  | 0, 0, _ => rfl
  | 0, n + 1, equal =>
      absurd equal (Equal.ctor_discrimination (S := TowerArithmeticModel.setting lv fun _ => 0)
        (TowerArithmeticModel.laws lv _) (TowerArithmeticModel.constants lv _) CtxFormed.nil
        (TowerArithmeticModel.setting_roles_num lv _) mem_zero mem_succ TowerNumbersModel.zero_ne_succ
        (as := []) (bs := [numTm n]))
  | m + 1, 0, equal =>
      absurd equal (Equal.ctor_discrimination (S := TowerArithmeticModel.setting lv fun _ => 0)
        (TowerArithmeticModel.laws lv _) (TowerArithmeticModel.constants lv _) CtxFormed.nil
        (TowerArithmeticModel.setting_roles_num lv _) mem_succ mem_zero
        TowerNumbersModel.zero_ne_succ.symm (as := [numTm m]) (bs := []))
  | m + 1, n + 1, equal => by
      obtain ⟨_, _, fieldsEqual⟩ := Equal.ctor_injective
        (S := TowerArithmeticModel.setting lv fun _ => 0) (TowerArithmeticModel.laws lv _)
        (TowerArithmeticModel.constants lv _) CtxFormed.nil
        (TowerArithmeticModel.setting_roles_num lv _) mem_succ mem_succ (as := [numTm m])
        (bs := [numTm n]) equal
      cases fieldsEqual with
      | cons head _ => exact congrArg (· + 1) (numTm_equal head)

/-! ## Membership agrees -/

/-- **A row of the number region is generated exactly when its content reads as a closed canonical
term of the model's numbers.** This holds by the reading's construction: `toModel` reads numerals
only (`toModel_eq_some`). Against the total reading, see `Translation.generated_iff_translate`. -/
theorem generated_iff_closedCanonical (e : Expr) :
    Generated natRules ∅ (natRow e) ↔ ∃ t, toModel e = some t ∧ ClosedCanonicalNum lv t := by
  constructor
  · intro generated
    obtain ⟨k, same⟩ := Numbers.natRules_generated_iff.mp generated
    rw [natRow_injective same]
    exact ⟨numTm k, toModel_numeral k, (closedCanonical_iff lv).mpr ⟨k, rfl⟩⟩
  · rintro ⟨t, read, -⟩
    obtain ⟨k, rfl, rfl⟩ := toModel_eq_some read
    exact Numbers.numeral_generated k

/-- **Each closed canonical term of the model's numbers is the reading of exactly one generated
row.** -/
theorem closedCanonical_has_row {t : Tm Tower.Head 0} (canonical : ClosedCanonicalNum lv t) :
    ∃! e, Generated natRules ∅ (natRow e) ∧ toModel e = some t := by
  obtain ⟨k, rfl⟩ := (closedCanonical_iff lv).mp canonical
  refine ⟨numeral k, ⟨Numbers.numeral_generated k, toModel_numeral k⟩, ?_⟩
  rintro e ⟨-, read⟩
  obtain ⟨j, rfl, same⟩ := toModel_eq_some read
  rw [numTm_injective same]

/-! ## Values agree -/

/-- The model's addition applied to two closed terms. -/
def addTm (a b : Tm Tower.Head 0) : Tm Tower.Head 0 := .app (.app (.const add) a) b

/-- The first equation of the model's addition, at `zero`. -/
theorem add_zero_step {n : Nat} (a : Tm Tower.Head n) :
    (TowerArithmeticModel.rules lv).computation.step (.app (.app (.const add) a) (.const zero)) a :=
  .inr ⟨zero, [], consSub (.const zero) (consSub a fun i => Fin.elim0 i), [], mem_zero, rfl, rfl,
    rfl⟩

theorem addTm_typed {a b : Tm Tower.Head 0}
    (ta : Typed (TowerArithmeticModel.rules lv) .nil a (.const num))
    (tb : Typed (TowerArithmeticModel.rules lv) .nil b (.const num)) :
    Typed (TowerArithmeticModel.rules lv) .nil (addTm a b) (.const num) :=
  .appElim (.appElim (add_typed lv) ta) tb

/-- **The model's addition of two numerals equals the numeral of the sum**, at `num` in the empty
context. -/
theorem add_numerals (a : ℕ) : ∀ b : ℕ,
    Equal (TowerArithmeticModel.rules lv) .nil (addTm (numTm a) (numTm b)) (numTm (a + b)) (.const num)
  | 0 => .root (add_zero_step lv (numTm a))
      (addTm_typed lv (numTm_typed lv a) (numTm_typed lv 0)) (numTm_typed lv a)
  | b + 1 => by
      have typedSum := addTm_typed lv (numTm_typed lv a) (numTm_typed lv b)
      have computed : Equal (TowerArithmeticModel.rules lv) .nil (addTm (numTm a) (numTm (b + 1)))
          (.app (.const succ) (addTm (numTm a) (numTm b))) (.const num) :=
        .root (TowerArithmeticModel.add_succ_step lv _ _)
          (addTm_typed lv (numTm_typed lv a) (numTm_typed lv (b + 1)))
          (.appElim (succ_typed lv) typedSum)
      have congruent : Equal (TowerArithmeticModel.rules lv) .nil
          (.app (.const succ) (addTm (numTm a) (numTm b))) (.app (.const succ) (numTm (a + b)))
          (.const num) :=
        .appCong (.refl (succ_typed lv)) (add_numerals a b)
      exact .trans computed congruent

/-- **The model's addition has exactly one closed canonical value on two numerals.** -/
theorem add_value_unique (a b : ℕ) {t : Tm Tower.Head 0} (canonical : ClosedCanonicalNum lv t)
    (equal : Equal (TowerArithmeticModel.rules lv) .nil (addTm (numTm a) (numTm b)) t (.const num)) :
    t = numTm (a + b) := by
  obtain ⟨k, rfl⟩ := (closedCanonical_iff lv).mp canonical
  rw [numTm_equal lv (.trans (.symm equal) (add_numerals lv a b))]

/-- **The step's addition computes the model's addition**: for a request on two generated rows, the
readings of the arguments exist, and every final state reached holds an answer whose reading is a
closed canonical number of the model, equal there to the model's addition of the readings, and the
only closed canonical number that is. -/
theorem answer_agrees {x y : Expr} (gx : Generated natRules ∅ (natRow x))
    (gy : Generated natRules ∅ (natRow y)) {C : Conf} (request : Recursion.Request x y C) :
    ∃ tx ty, toModel x = some tx ∧ toModel y = some ty ∧
      ∀ C', Relation.ReflTransGen Recursion.addStep C C' → (∀ C'', ¬ Recursion.addStep C' C'') →
        ∃ v t, outE v ∈ contents C' ∧ toModel v = some t ∧ ClosedCanonicalNum lv t ∧
          Equal (TowerArithmeticModel.rules lv) .nil (addTm tx ty) t (.const num) ∧
          ∀ t', ClosedCanonicalNum lv t' →
            Equal (TowerArithmeticModel.rules lv) .nil (addTm tx ty) t' (.const num) → t' = t := by
  obtain ⟨a, b, rfl, rfl, -, final, -⟩ := Recursion.addition_on_generated gx gy request
  refine ⟨numTm a, numTm b, toModel_numeral a, toModel_numeral b, fun C' run stops => ?_⟩
  obtain ⟨o, only, out⟩ := final C' run stops
  refine ⟨numeral (a + b), numTm (a + b), ⟨o, only.1, out⟩, toModel_numeral (a + b),
    (closedCanonical_iff lv).mpr ⟨a + b, rfl⟩, add_numerals lv a b, fun t' canonical equal => ?_⟩
  exact add_value_unique lv a b canonical equal

end Agreement

#print axioms Agreement.toModel_eq_some
#print axioms Agreement.ctorForm_iff
#print axioms Agreement.numTm_typed
#print axioms Agreement.ctorForm_whnf
#print axioms Agreement.numTm_equal
#print axioms Agreement.generated_iff_closedCanonical
#print axioms Agreement.closedCanonical_has_row
#print axioms Agreement.add_numerals
#print axioms Agreement.add_value_unique
#print axioms Agreement.answer_agrees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
