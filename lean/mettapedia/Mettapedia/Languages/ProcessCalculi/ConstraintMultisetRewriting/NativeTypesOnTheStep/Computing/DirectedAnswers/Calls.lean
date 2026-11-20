import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Data
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.ExtensionRuns

/-!
# Ground calls of a checked function, at data types: exactly one answer

A definition by rows whose verdict is a function is interpreted in the vectors package, without new
rules, by its compiled term, certified at the declared type (`Definitions.qualify_function`). The
theorems of this module are about that **compiled interpretation**: the compiled term applied, in the
unextended package, to closed arguments. The definition as a declared constant whose rows are rules of
an extended package is the subject of `DirectedAnswers.Rows`, which carries these theorems over to it.

* **A ground call of a closed checked function, at arguments typed along its telescope, whose declared
  result type at those arguments is a data type, has exactly one answer; it is a value, of that type,
  and typed-equal to the call** (`ground_call_answer`). The condition is on the call
  (`DataType (subst σ d.result)`) and not on the function: the declared result type of append is open,
  and the theorem applies to its calls at a data type of elements. When the declared result type is the
  numbers the answer is a numeral (`ground_call_numeral`). The arguments need not be normal. Strong
  normalization is not assumed; the proof is `data_answer`, by the normalization model of the package.
* **Addition by rows**: every call `add a b` at closed numbers has exactly one answer, a numeral
  (`add_answer`); for instance `add (add 1 1) 1` answers `3` (`add_nested`). On these calls an answer of
  the full reduction is exactly an answer (`add_answers_coincide`), so the answer that
  `Definitions.add_exactly_one` provides at a numeral and a normal number is that numeral
  (`add_exactly_one_numeral`).
* **Append on it**: every call at a data type of elements, closed lengths and vectors typed along the
  telescope has exactly one answer, a value of type `vec A (add n m)` (`appendR_answer`); the answers of
  `Definitions.appendR_exactly_one` are these (`appendR_answers_coincide`). The written-out call
  `append num 1 1 [2] [3]` answers `[2, 3]` (`appendR_ground`).
* **Map**, with a function argument and a vector result: every call whose target element type is a data
  type has exactly one answer, a value of type `vec B n`, whatever the function argument
  (`map_answer`); for instance `map num num (add 1) 1 [2]` (`map_instance`).
* **A result at a pair type**: every call of `dup` at a closed number has exactly one answer, a value
  of `num × num` (`dup_answer`).

**In an extended package.** The package extended by a development that passes the declaration-time
check is a constructor presentation (`DeclarationCheck.checkedConstructors`), so there two answers of
one term are equal, for every term (`dev_directed_unique`). The call `append num 1 1 [2] [3]` of the
declared constant answers `[2, 3]` there (`extension_ground`, by running the rules). That every such
call answers, with the answer of the compiled call, is `DirectedAnswers.Rows`.

**Controls.**
* **The data-type hypothesis of `ground_call_answer`, and it alone, fails** (`small_control`): `small 1`
  is a ground call of the closed checked function `small : Π (n : num). U₀`, at an argument typed along
  its telescope. Its declared result type `U₀` is no data type (`head_not_dataType`), its only answer is
  `num → num`, and no answer of it is a value. The condition follows the computation of the type: the
  call `small zero`, as a type, is a data type, and `small 1` is not (`small_zero_dataType`,
  `small_one_not_dataType`).
* **A partial application** (`add_one_control`): `add 1`, typed at `num → num`, answers `λ m. succ m`,
  which is no value. It is not a full call of addition (the telescope has two entries), so it is no
  control for `ground_call_answer`; it shows an answer at a function type.
* `Heads.u0_controls` is about the universe `U₀` itself, which is no call of a checked function: there
  the answer is a head, and the directed normal forms convertible with it are not unique on the nose.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TelescopeAbstraction (applyClosed)
open TowerVectorsModel (U0 numC zeroC succC ttC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three single twoThree)
open Definitions (Checked call_typed nat nat_typed spine addDef addTerm addExport appendRDef appendRTerm
  add_verdict add_compiles appendR_checked qualify_closed)
open Vectors.Checker (Definition)

/-! ## The ground-call theorem -/

/-- **A ground call of a closed checked function**, at arguments typed along its telescope, **whose
declared result type at those arguments is a data type, has exactly one answer: a value of that type**,
typed-equal to the call. The call is the compiled term applied in the unextended package. The
data-type hypothesis is on this call; it cannot be dropped (`small_control`). -/
theorem ground_call_answer {d : Definition} {c : Tower.Tm 0} (checked : Checked d 0 c)
    {σ : Sub Tower.Head d.arity 0} (args : SubstMor pkg d.telescope .nil σ)
    (data : DataType (subst σ d.result)) :
    ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed d.telescope σ c) v ∧
      Typed pkg .nil v (subst σ d.result) ∧ Equal pkg .nil (applyClosed d.telescope σ c) v (subst σ d.result) ∧
      ∀ w, DirectedAnswer pkg (applyClosed d.telescope σ c) w → w = v :=
  data_answer data (call_typed checked args)

/-- **When the declared result type is the numbers, the answer is a numeral**, and exactly one. The
hypothesis is the syntactic equality `d.result = numC`; a call whose declared result type only computes
to the numbers is covered by `ground_call_answer`. -/
theorem ground_call_numeral {d : Definition} {c : Tower.Tm 0} (checked : Checked d 0 c)
    (result : d.result = numC) {σ : Sub Tower.Head d.arity 0} (args : SubstMor pkg d.telescope .nil σ) :
    ∃ k, DirectedAnswer pkg (applyClosed d.telescope σ c) (nat k) ∧
      Equal pkg .nil (applyClosed d.telescope σ c) (nat k) numC ∧
      ∀ w, DirectedAnswer pkg (applyClosed d.telescope σ c) w ↔ w = nat k := by
  have typed := call_typed checked args
  rw [result] at typed
  obtain ⟨k, answer, equal, unique, -⟩ := num_answer typed
  exact ⟨k, answer, equal, unique⟩

/-! ## Addition by rows -/

/-- The checked addition is the compiled term `addTerm`. -/
theorem add_checked : Checked addDef 0 addTerm := by
  obtain ⟨c, checked⟩ := qualify_closed add_verdict
  obtain rfl : c = addTerm := Option.some.inj (checked.compiled.symm.trans add_compiles)
  exact checked

/-- The arguments of `add a b`. -/
def addArgs (a b : Tower.Tm 0) : Sub Tower.Head 2 0 := fun x => if x.val = 0 then b else a

theorem addArgs_typed {a b : Tower.Tm 0} (ta : Typed pkg .nil a numC) (tb : Typed pkg .nil b numC) :
    SubstMor pkg addDef.telescope .nil (addArgs a b) := by
  intro x
  match x with
  | ⟨0, _⟩ => exact tb
  | ⟨1, _⟩ => exact ta

theorem add_call (a b : Tower.Tm 0) : applyClosed addDef.telescope (addArgs a b) addTerm = spine addTerm [a, b] :=
  rfl

/-- **Every call of addition by rows at closed numbers has exactly one answer, a numeral.** -/
theorem add_answer {a b : Tower.Tm 0} (ta : Typed pkg .nil a numC) (tb : Typed pkg .nil b numC) :
    ∃ k, DirectedAnswer pkg (spine addTerm [a, b]) (nat k) ∧
      ∀ w, DirectedAnswer pkg (spine addTerm [a, b]) w ↔ w = nat k := by
  obtain ⟨k, answer, -, unique⟩ := ground_call_numeral add_checked rfl (addArgs_typed ta tb)
  exact ⟨k, answer, unique⟩

/-- **On the calls of addition the two notions coincide**: an answer of the full reduction is exactly an
answer. -/
theorem add_answers_coincide {a b : Tower.Tm 0} (ta : Typed pkg .nil a numC) (tb : Typed pkg .nil b numC)
    (v : Tower.Tm 0) : Answer pkg (spine addTerm [a, b]) v ↔ DirectedAnswer pkg (spine addTerm [a, b]) v := by
  obtain ⟨k, -, unique⟩ := add_answer ta tb
  rw [answer_iff_headFree (Vectors.vectorConstructors level1) (heads_reflexive level1)]
  constructor
  · exact fun both => both.1
  · intro answer
    refine ⟨answer, ?_⟩
    rw [(unique v).mp answer]
    exact (nat_value k).headFree

/-- **The answer of `Definitions.add_exactly_one` is a numeral**, the answer of `add_answer`. -/
theorem add_exactly_one_numeral (N : Nat) {m : Tower.Tm 0} (typed : Typed pkg .nil m numC)
    (normal : ConstructorSystem.Normal pkg m) :
    ∃ k, Answer pkg (spine addTerm [nat N, m]) (nat k) ∧ DirectedAnswer pkg (spine addTerm [nat N, m]) (nat k) := by
  obtain ⟨k, -, unique⟩ := add_answer (nat_typed N) typed
  obtain ⟨v, answer, -, -⟩ := Definitions.add_exactly_one N typed normal
  have directed := (add_answers_coincide (nat_typed N) typed v).mp answer
  have same := (unique v).mp directed
  subst same
  exact ⟨k, answer, directed⟩

/-- **A nested call at arguments that are not normal**: `add (add 1 1) 1` answers `3`. -/
theorem add_nested :
    DirectedAnswer pkg (spine addTerm [spine addTerm [one, one], one]) three := by
  have ran : Vectors.vecNormalize level1 60 (spine addTerm [spine addTerm [one, one], one]) = some three := by
    decide +kernel
  have value : Value (three : Tower.Tm 0) := .succ (.succ (.succ .zero))
  exact directedAnswer_of_answer (Vectors.vectorConstructors level1)
    ⟨Vectors.vecNormalize_sound level1 ran, value.normal⟩ value.headFree

/-! ## Append on the addition by rows -/

/-- **The exported addition is typed** at `num → num → num`, certified by the tree's checker. -/
theorem addExport_typed : Typed pkg .nil addExport (.pi numC (.pi numC numC)) :=
  Definitions.typed?_sound (fuel := 30) (by decide +kernel)

/-- The declared type of a call of append. -/
theorem appendR_result (σ : Sub Tower.Head 5 0) :
    subst σ appendRDef.result = vecC (σ 4) (spine addExport [σ 3, σ 2]) := by
  show subst σ (vecC (.var 4) (spine (liftClosed addExport) [.var 3, .var 2])) = _
  simp only [Presentation.subst, Definitions.subst_spine, List.map, subst_liftClosed,
    TelescopeAbstraction.liftClosed_zero]

/-- **The result type of a call of append over a data type of elements is a data type.** -/
theorem appendR_result_data {σ : Sub Tower.Head 5 0} (args : SubstMor pkg appendRDef.telescope .nil σ)
    (dataA : DataType (σ 4)) : DataType (subst σ appendRDef.result) := by
  have typedA : Typed pkg .nil (σ 4) U0 := args (4 : Fin 5)
  have typedN : Typed pkg .nil (σ 3) numC := args (3 : Fin 5)
  have typedM : Typed pkg .nil (σ 2) numC := args (2 : Fin 5)
  have length : Typed pkg .nil (spine addExport [σ 3, σ 2]) numC :=
    .appElim (.appElim addExport_typed typedN) typedM
  rw [appendR_result]
  exact vec_dataType typedA dataA length

/-- **Every call of append on the addition by rows**, at a data type of elements and arguments typed
along its telescope, **has exactly one answer, a value of type `vec A (add n m)`.** -/
theorem appendR_answer {σ : Sub Tower.Head 5 0} (args : SubstMor pkg appendRDef.telescope .nil σ)
    (dataA : DataType (σ 4)) :
    ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed appendRDef.telescope σ appendRTerm) v ∧
      Typed pkg .nil v (subst σ appendRDef.result) ∧
      ∀ w, DirectedAnswer pkg (applyClosed appendRDef.telescope σ appendRTerm) w → w = v := by
  obtain ⟨v, value, answer, typed, -, unique⟩ :=
    ground_call_answer appendR_checked args (appendR_result_data args dataA)
  exact ⟨v, value, answer, typed, unique⟩

/-- **On the calls of append the two notions coincide**, so the answers of
`Definitions.appendR_exactly_one` are the values of `appendR_answer`. -/
theorem appendR_answers_coincide {σ : Sub Tower.Head 5 0} (args : SubstMor pkg appendRDef.telescope .nil σ)
    (dataA : DataType (σ 4)) (v : Tower.Tm 0) :
    Answer pkg (applyClosed appendRDef.telescope σ appendRTerm) v ↔
      DirectedAnswer pkg (applyClosed appendRDef.telescope σ appendRTerm) v := by
  obtain ⟨w, value, -, -, unique⟩ := appendR_answer args dataA
  rw [answer_iff_headFree (Vectors.vectorConstructors level1) (heads_reflexive level1)]
  constructor
  · exact fun both => both.1
  · intro answer
    refine ⟨answer, ?_⟩
    rw [unique v answer]
    exact value.headFree

/-- **`append num 1 1 [2] [3]` answers `[2, 3]`**, its only answer: the compiled call in the package. -/
theorem appendR_ground :
    DirectedAnswer pkg (spine appendRTerm [numC, one, one, single two, single three]) twoThree ∧
      ∀ w, DirectedAnswer pkg (spine appendRTerm [numC, one, one, single two, single three]) w → w = twoThree := by
  have value : Value (twoThree : Tower.Tm 0) :=
    .pair (.succ (.succ .zero)) (.pair (.succ (.succ (.succ .zero))) .tt)
  have answer : DirectedAnswer pkg (spine appendRTerm [numC, one, one, single two, single three]) twoThree :=
    directedAnswer_of_answer (Vectors.vectorConstructors level1)
      ⟨Vectors.vecNormalize_sound level1 Definitions.ground_answers.2.1, value.normal⟩ value.headFree
  exact ⟨answer, fun w other => DirectedAnswer.unique (Vectors.vectorConstructors level1) other answer⟩

/-- The arguments of `append num 1 1 [2] [3]`, newest first. -/
def groundSub : Sub Tower.Head 5 0 := fun x =>
  match x with
  | ⟨0, _⟩ => single three
  | ⟨1, _⟩ => single two
  | ⟨2, _⟩ => one
  | ⟨3, _⟩ => one
  | ⟨_ + 4, _⟩ => numC

/-- **The arguments are typed along the telescope**, so the general theorem applies to the written-out
call. -/
theorem groundSub_typed : SubstMor pkg appendRDef.telescope .nil groundSub := by
  have single_typed : ∀ k : Nat, Typed pkg .nil (single (nat k)) (vecC numC one) := fun k =>
    D.cons_typed D.num_typed D.zero_typed (nat_typed k) (D.nil_typed D.num_typed)
  intro x
  match x with
  | ⟨0, _⟩ => exact single_typed 3
  | ⟨1, _⟩ => exact single_typed 2
  | ⟨2, _⟩ => exact nat_typed 1
  | ⟨3, _⟩ => exact nat_typed 1
  | ⟨4, _⟩ => exact D.num_typed

/-- **The general theorem at the written-out call**: its one answer is `[2, 3]`. -/
theorem appendR_ground_general :
    applyClosed appendRDef.telescope groundSub appendRTerm =
        spine appendRTerm [numC, one, one, single two, single three] ∧
      ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed appendRDef.telescope groundSub appendRTerm) v ∧
        v = twoThree := by
  obtain ⟨v, value, answer, -, -⟩ := appendR_answer groundSub_typed .num
  exact ⟨rfl, v, value, answer, appendR_ground.2 v answer⟩

open Definitions (devPackage addAppendDev addAppendRows appendName) in
/-- **In the package extended by the two definitions as rows, the declared constant's call answers
`[2, 3]` too**, its only answer there: the extension is a constructor presentation, and its answer of the
full reduction (`Definitions.append_answer`) has no head. -/
theorem extension_ground :
    DirectedAnswer (devPackage addAppendDev addAppendRows)
        (spine (.const appendName) [numC, one, one, single two, single three] : Tower.Tm 0) twoThree ∧
      ∀ w, DirectedAnswer (devPackage addAppendDev addAppendRows)
        (spine (.const appendName) [numC, one, one, single two, single three] : Tower.Tm 0) w → w = twoThree := by
  have found : Definitions.devRules addAppendDev = some addAppendRows := Definitions.addAppend_rules
  obtain ⟨rows', found', -, -, table⟩ := Definitions.devCheck_parts Definitions.addAppend_devCheck
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  have equations := DeclarationCheck.checkedConstructors (Definitions.devBase addAppendDev)
    (by intro n l r impossible; exact impossible) LevelTower.headEq_symmetric table
  have value : Value (twoThree : Tower.Tm 0) :=
    .pair (.succ (.succ .zero)) (.pair (.succ (.succ (.succ .zero))) .tt)
  have answer := directedAnswer_of_answer equations Definitions.append_answer.1 value.headFree
  exact ⟨answer, fun w other => DirectedAnswer.unique equations other answer⟩

/-- **In the package extended by a development that passes the declaration-time check, two answers of
one term are equal**, for every term of every arity: the extension is a constructor presentation. -/
theorem dev_directed_unique {dev : Definitions.Development} (ok : Definitions.devCheck dev = true)
    {rows : AlgebraicSchema.SchemaTable Tower.Head} (found : Definitions.devRules dev = some rows)
    {n : Nat} {t v w : Tower.Tm n}
    (first : DirectedAnswer (Definitions.devPackage dev rows) t v)
    (second : DirectedAnswer (Definitions.devPackage dev rows) t w) : v = w := by
  obtain ⟨rows', found', -, -, table⟩ := Definitions.devCheck_parts ok
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  exact DirectedAnswer.unique (DeclarationCheck.checkedConstructors (Definitions.devBase dev)
    (by intro n l r impossible; exact impossible) LevelTower.headEq_symmetric table) first second

/-! ## Map: a function argument and a vector result -/

/-- **Every call of the compiled `map`**, at arguments typed along its telescope, **whose target element
type is a data type, has exactly one answer, a value of type `vec B n`**, whatever its function
argument. -/
theorem map_answer {σ : Sub Tower.Head 5 0} (args : SubstMor pkg Definitions.mapDef.telescope .nil σ)
    (dataB : DataType (σ 3)) :
    ∃ c : Tower.Tm 0, Checked Definitions.mapDef 0 c ∧
      ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed Definitions.mapDef.telescope σ c) v ∧
        Typed pkg .nil v (vecC (σ 3) (σ 1)) ∧
        ∀ w, DirectedAnswer pkg (applyClosed Definitions.mapDef.telescope σ c) w → w = v := by
  obtain ⟨c, checked⟩ := Definitions.map_checked
  have typedB : Typed pkg .nil (σ 3) U0 := args (3 : Fin 5)
  have typedN : Typed pkg .nil (σ 1) numC := args (1 : Fin 5)
  have data : DataType (subst σ Definitions.mapDef.result) := vec_dataType typedB dataB typedN
  obtain ⟨v, value, answer, typed, -, unique⟩ := ground_call_answer checked args data
  exact ⟨c, checked, v, value, answer, typed, unique⟩

/-- The partial application `add 1` is typed at `num → num`. -/
theorem addOne_typed : Typed pkg .nil (spine addTerm [one]) (.pi numC numC) :=
  .appElim add_checked.guarantee.1 (nat_typed 1)

/-- The arguments of `map num num (add 1) 1 [2]`, newest first. -/
def mapSub : Sub Tower.Head 5 0 := fun x =>
  match x with
  | ⟨0, _⟩ => single two
  | ⟨1, _⟩ => one
  | ⟨2, _⟩ => spine addTerm [one]
  | ⟨_ + 3, _⟩ => numC

theorem mapSub_typed : SubstMor pkg Definitions.mapDef.telescope .nil mapSub := by
  intro x
  match x with
  | ⟨0, _⟩ => exact D.cons_typed D.num_typed D.zero_typed (nat_typed 2) (D.nil_typed D.num_typed)
  | ⟨1, _⟩ => exact nat_typed 1
  | ⟨2, _⟩ => exact addOne_typed
  | ⟨3, _⟩ => exact D.num_typed
  | ⟨4, _⟩ => exact D.num_typed

/-- **`map num num (add 1) 1 [2]` has exactly one answer, a value**: the hypotheses of `map_answer` at
a written-out call, with a function argument that is not normal. -/
theorem map_instance :
    ∃ c : Tower.Tm 0, Checked Definitions.mapDef 0 c ∧
      ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed Definitions.mapDef.telescope mapSub c) v ∧
        ∀ w, DirectedAnswer pkg (applyClosed Definitions.mapDef.telescope mapSub c) w → w = v := by
  obtain ⟨c, checked, v, value, answer, -, unique⟩ := map_answer mapSub_typed .num
  exact ⟨c, checked, v, value, answer, unique⟩

/-- **Every call of the compiled `dup` at a closed number has exactly one answer, a value of the pair
type** `num × num`. -/
theorem dup_answer {a : Tower.Tm 0} (ta : Typed pkg .nil a numC) :
    ∃ c : Tower.Tm 0, Checked Definitions.dupDef 0 c ∧
      ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed Definitions.dupDef.telescope (fun _ => a) c) v ∧
        Typed pkg .nil v (.sigma numC numC) ∧
        ∀ w, DirectedAnswer pkg (applyClosed Definitions.dupDef.telescope (fun _ => a) c) w → w = v := by
  obtain ⟨c, checked⟩ := qualify_closed Definitions.dup_verdict
  have args : SubstMor pkg Definitions.dupDef.telescope .nil (fun _ => a) := by
    intro x
    match x with
    | ⟨0, _⟩ => exact ta
  obtain ⟨v, value, answer, typed, -, unique⟩ := ground_call_answer checked args (DataType.sigma .num .num)
  exact ⟨c, checked, v, value, answer, typed, unique⟩

/-! ## Controls -/

/-- The compiled `small`: `λ n. num-rec (λ _. U0) num (λ k ih. num → ih) n`. -/
def smallTerm : Tower.Tm 0 :=
  .lam (Vectors.numRecAt (.lam U0) numC (.lam (.lam (.pi numC (.var 1)))) (.var 0))

theorem small_compiles : Definitions.compile 0 Definitions.smallDef = some smallTerm := by
  decide +kernel

/-- `small : Π (n : num). U0` is a closed checked function. -/
theorem small_checked : Checked Definitions.smallDef 0 smallTerm := by
  obtain ⟨c, checked⟩ := qualify_closed Definitions.small_verdict
  obtain rfl : c = smallTerm := Option.some.inj (checked.compiled.symm.trans small_compiles)
  exact checked

/-- The argument of `small a`. -/
def smallArgs (a : Tower.Tm 0) : Sub Tower.Head 1 0 := fun _ => a

theorem smallArgs_typed {a : Tower.Tm 0} (ta : Typed pkg .nil a numC) :
    SubstMor pkg Definitions.smallDef.telescope .nil (smallArgs a) := by
  intro x
  match x with
  | ⟨0, _⟩ => exact ta

/-- The full ground call `small a` of the compiled function. -/
abbrev smallCall (a : Tower.Tm 0) : Tower.Tm 0 :=
  applyClosed Definitions.smallDef.telescope (smallArgs a) smallTerm

theorem smallCall_typed {a : Tower.Tm 0} (ta : Typed pkg .nil a numC) : Typed pkg .nil (smallCall a) U0 :=
  call_typed small_checked (smallArgs_typed ta)

theorem numPi_normal : ConstructorSystem.Normal pkg (.pi numC numC : Tower.Tm 0) := by
  intro target step
  cases step with
  | root h => exact (Vectors.vectorConstructors level1).no_root_of_spineHead h rfl
  | congPiDom inner => exact Vectors.const_normal level1 (by decide) inner
  | congPiCod inner => exact Vectors.const_normal level1 (by decide) inner

theorem small_zero_answer : DirectedAnswer pkg (smallCall zeroC) numC := by
  have ran : Vectors.vecNormalize level1 30 (smallCall zeroC) = some numC := by decide +kernel
  exact directedAnswer_of_answer (Vectors.vectorConstructors level1)
    ⟨Vectors.vecNormalize_sound level1 ran, Vectors.const_normal level1 (by decide)⟩ trivial

theorem small_one_answer : DirectedAnswer pkg (smallCall one) (.pi numC numC) := by
  have ran : Vectors.vecNormalize level1 30 (smallCall one) = some (.pi numC numC) := by decide +kernel
  exact directedAnswer_of_answer (Vectors.vectorConstructors level1)
    ⟨Vectors.vecNormalize_sound level1 ran, numPi_normal⟩ ⟨trivial, trivial⟩

/-- A typed closed type with an answer is typed-equal to its answer. -/
theorem typeEq_of_answer {T V : Tower.Tm 0} (typing : Typed pkg .nil T U0) (answer : DirectedAnswer pkg T V) :
    TypeEq pkg .nil T V :=
  ⟨_, LevelTower.IsUniverse.sort _, (typed_of_qualified (Vectors.vq level1) .nil typing answer).2⟩

/-- **`small zero`, a type computed by the recursor into the universe, is a data type**: it computes to
the numbers. -/
theorem small_zero_dataType : DataType (smallCall zeroC) :=
  .conv (typeEq_of_answer (smallCall_typed D.zero_typed) small_zero_answer) .num

/-- **`small 1`, which computes to `num → num`, is not a data type.** -/
theorem small_one_not_dataType : ¬ DataType (smallCall one) := fun data =>
  pi_not_dataType (.conv (typeEq_of_answer (smallCall_typed (nat_typed 1)) small_one_answer).symm data)

/-- **The data-type hypothesis of `ground_call_answer` cannot be dropped**, and this control fails no
other hypothesis: `small 1` is a ground call of the closed checked function `small` (`small_checked`), at
an argument typed along its telescope; its declared result type at the argument, `U₀`, is no data type;
its only answer is `num → num`; and no answer of it is a value. -/
theorem small_control :
    SubstMor pkg Definitions.smallDef.telescope .nil (smallArgs one) ∧
      ¬ DataType (subst (smallArgs one) Definitions.smallDef.result) ∧
      (∀ w, DirectedAnswer pkg (smallCall one) w ↔ w = .pi numC numC) ∧
      ¬ ∃ v, Value v ∧ DirectedAnswer pkg (smallCall one) v := by
  refine ⟨smallArgs_typed (nat_typed 1), head_not_dataType _, fun w => ⟨fun answer =>
    DirectedAnswer.unique (Vectors.vectorConstructors level1) answer small_one_answer, ?_⟩, ?_⟩
  · rintro rfl
    exact small_one_answer
  · rintro ⟨v, value, answer⟩
    have same := DirectedAnswer.unique (Vectors.vectorConstructors level1) answer small_one_answer
    subst same
    cases value

/-- **A partial application, at a function type**: `add 1`, typed at `num → num`, answers
`λ m. succ m`, which is no value. The term is not a full call of addition, whose telescope has two
entries, so this is no control for `ground_call_answer`; that control is `small_control`. -/
theorem add_one_control :
    Typed pkg .nil (spine addTerm [one]) (.pi numC numC) ∧
      DirectedAnswer pkg (spine addTerm [one]) (.lam (succC (.var 0))) ∧
      ¬ Value (.lam (succC (.var 0)) : Tower.Tm 0) := by
  have ran : Vectors.vecNormalize level1 30 (spine addTerm [one]) = some (.lam (succC (.var 0))) := by
    decide +kernel
  have bodyNormal : ConstructorSystem.Normal pkg (succC (.var 0) : Tower.Tm 1) :=
    Vectors.succ_normal level1 ((Vectors.vectorConstructors level1).normal_var 0)
  have normal : ConstructorSystem.Normal pkg (.lam (succC (.var 0)) : Tower.Tm 0) := by
    intro target step
    cases step with
    | root h => exact (Vectors.vectorConstructors level1).no_root_of_spineHead h rfl
    | congLam inner => exact bodyNormal inner
  refine ⟨addOne_typed,
    directedAnswer_of_answer (Vectors.vectorConstructors level1)
      ⟨Vectors.vecNormalize_sound level1 ran, normal⟩ ⟨trivial, trivial⟩, nofun⟩

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms ground_call_answer
#print axioms ground_call_numeral
#print axioms add_checked
#print axioms add_answer
#print axioms add_answers_coincide
#print axioms add_exactly_one_numeral
#print axioms add_nested
#print axioms addExport_typed
#print axioms appendR_result
#print axioms appendR_result_data
#print axioms appendR_answer
#print axioms appendR_answers_coincide
#print axioms appendR_ground
#print axioms groundSub_typed
#print axioms appendR_ground_general
#print axioms extension_ground
#print axioms dev_directed_unique
#print axioms map_answer
#print axioms mapSub_typed
#print axioms map_instance
#print axioms dup_answer
#print axioms small_checked
#print axioms small_zero_dataType
#print axioms small_one_not_dataType
#print axioms small_control
#print axioms add_one_control
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
