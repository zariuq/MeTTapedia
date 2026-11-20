import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Calls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Agreement

/-!
# The rows' own reduction reaches the answer of the compiled call

A definition by rows, declared as a constant of an extended package, runs by its rows. Its compiled term
runs in the package without new rules, and there a ground call at a data type has exactly one answer, a
value (`ground_call_answer`). This module carries that answer over to the declared constant.

* **The transfer** (`answer_of_conv`). In the package extended by a development that passes the
  declaration-time check, a closed term that is convertible, in the extension, with a term of the
  package whose answer is a value has that value as its one answer. The extension is confluent and the
  value is a normal form of it, so no termination argument for the extension is needed: the answer
  exists because the package's term has it.
* **Calls of a recursive constant** (`recursive_call_answer`). For a constant defined by recursion on its
  call index whose rules, read at its compiled term, join, and whose recursive calls are saturated
  (`Definitions.Recursive`): every ground call, at arguments convertible in the extension with closed
  terms of the package that have a closed number at the call index, has exactly one answer in the
  extension, the answer of the compiled call at those terms. The arguments of the call may themselves
  contain the declared constants: a call whose answer is known is convertible with it, so the theorem
  applies to nested calls (`add_rows_nested`).
* **For a checked definition** (`rows_reach`). For a definition whose verdict is a closed function
  (`Definitions.Checked d 0 c`), in the class `RowsReach` (a recursion on a call index of the numbers,
  number or length of a vector, with saturated recursive calls, read at `c`): every ground call of its
  declared constant in the extended package, at arguments convertible there with closed terms typed
  along the telescope, whose declared result type at those terms is a data type, has exactly one answer,
  the one answer of the compiled call in the unextended package, a value of the declared type.
* **Instances**: addition by rows, at every two arguments (`add_rows_answer`, `add_rows_reach`); append
  over it, at every call typed along its telescope with a data type of elements (`append_rows_answer`,
  `append_rows_reach`); `map`, whatever its function argument (`map_rows_answer`).
* **A definition without a call index** (`plain_call_answer`): one row, no recursion; the same
  conclusion, with no numeral asked for. Instance: `dup`, whose answers are pairs (`dup_rows_answer`).
* **Soundness for every term** (`value_of_reading`, instance `add_value_of_reading`). With every rule of
  the development read at the compiled terms and joining, and no condition on the shape of the rows:
  whenever the rows take a closed term to a value, that value is the answer of the reading. Nothing is
  asked of the term, no typing and no data type: a closed term of the package convertible with a value
  answers it (`pkg_answer_of_conv`), by Church–Rosser. The rows reach no value that the compiled reading
  does not answer.
* **Control** (`reading_control`): the condition that the row at `succ k` reads at the term cannot be
  dropped from `Definitions.Recursive`. Read as `λ n m. m`, addition by rows meets every other condition,
  and its call `add 1 0` is not convertible with the same call of that term.

**What is assumed of a development**: the declaration-time check, which already makes every value a
normal form of the extension (`Value.normal_dev`) and keeps `zero`, `succ` and `tt` out of the
development's names (`Definitions.dev_names_ne_constructors`); and, per constant, the kernel-evaluated
conditions of `Definitions.Recursive`. **What is not proved**: that every definition whose verdict is a
closed function meets the conditions of the class. Not every one does: a row may pass its recursive call
on without the later arguments, and then the conditions fail while the ground calls that were run still
agree (`DirectedAnswers.Unsaturated`); for such a definition the existence of an answer by the rows is
open, and soundness holds. Strong normalization of the extension is neither needed nor given.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema (SchemaTable)
open ConstantExpansion (expand Bodies)
open TelescopeAbstraction (applyClosed)
open TowerVectorsModel (U0 numC zeroC succC ttC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three)
open Definitions (Development devCheck devRules devPackage OldTerm Recursive genericCall allVars idx
  withIndex withIndex_idx reading Checked nat nat_typed spine addDef addTerm addName appendName appendRDef
  appendRTerm appendR_checked addAppendDev addAppendRows addAppend_devCheck addAppend_rules mapDef mapName
  mapDev mapRows map_devCheck map_rules)

/-! ## Values in an extension -/

/-- **A value is a normal form of every checked extension.** A rule of the extension starts at a defined
constant applied to its arity of arguments, at least one. So a constant alone takes no step, whatever
its name; `succ` applied to a value takes none because `succ` is not defined there, as it occurs in the
package's rows; and a pair is no spine. -/
theorem Value.normal_dev {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {v : Tower.Tm 0} (value : Value v) :
    ConstructorSystem.Normal (devPackage dev rows) v := by
  have bare : ∀ (c : DeclName) {target : Tower.Tm 0},
      ¬ (devPackage dev rows).computation.step (.const c) target := by
    intro c target step
    obtain ⟨name, head, positive, -⟩ := Definitions.dev_root_spine ok found step
    have computed : ConstructorSystem.spineHead (.const c : Tower.Tm 0) = some (c, 0) := rfl
    rw [computed] at head
    simp only [Option.some.injEq, Prod.mk.injEq] at head
    obtain ⟨rfl, arity⟩ := head
    omega
  induction value with
  | zero => exact ConstructorSystem.Normal.const _ (bare _)
  | tt => exact ConstructorSystem.Normal.const _ (bare _)
  | @succ t _ ih =>
      intro target step
      cases step with
      | root h =>
          obtain ⟨name, head, -, defined⟩ := Definitions.dev_root_spine ok found h
          have computed : ConstructorSystem.spineHead (succC t : Tower.Tm 0) =
              some (TowerNumbersModel.succ, 1) := rfl
          rw [computed] at head
          simp only [Option.some.injEq, Prod.mk.injEq] at head
          obtain ⟨rfl, -⟩ := head
          rw [Definitions.succ_not_defined ok] at defined
          cases defined
      | congAppFun inner =>
          cases inner with
          | root h => exact bare _ h
      | congAppArg inner => exact ih inner
  | @pair a b _ _ iha ihb =>
      intro target step
      cases step with
      | root h => exact (Definitions.devConstructors ok found).no_root_of_spineHead h rfl
      | congPairFst inner => exact iha inner
      | congPairSnd inner => exact ihb inner

/-- A value is read as itself by bodies that leave the constructors of values. -/
theorem Value.expand_eq {bodies : Bodies Tower.Head}
    (zeroOld : bodies TowerNumbersModel.zero = .const TowerNumbersModel.zero)
    (succOld : bodies TowerNumbersModel.succ = .const TowerNumbersModel.succ)
    (ttOld : bodies TowerVectorsModel.tt = .const TowerVectorsModel.tt) {v : Tower.Tm 0} (value : Value v) :
    expand bodies v = v := by
  induction value with
  | zero =>
      show liftClosed (bodies TowerNumbersModel.zero) = zeroC
      rw [zeroOld]
      rfl
  | @succ t _ ih =>
      show Tm.app (liftClosed (bodies TowerNumbersModel.succ)) (expand bodies t) = succC t
      rw [succOld, ih]
      rfl
  | tt =>
      show liftClosed (bodies TowerVectorsModel.tt) = ttC
      rw [ttOld]
      rfl
  | @pair a b _ _ iha ihb =>
      show Tm.pair (expand bodies a) (expand bodies b) = .pair a b
      rw [iha, ihb]

/-! ## The transfer -/

/-- **In a checked extension, a closed term convertible with a term of the package that answers a value
has that value as its one answer.** The extension is a constructor presentation, so the conversion has a
common reduct, and the value is a normal form of the extension without heads. -/
theorem answer_of_conv {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {t u v : Tower.Tm 0}
    (conversion : Conv (devPackage dev rows).headEq t u (devPackage dev rows).computation)
    (value : Value v) (answer : DirectedAnswer pkg u v) :
    DirectedAnswer (devPackage dev rows) t v ∧ ∀ w, DirectedAnswer (devPackage dev rows) t w → w = v := by
  have toValue : Conv (devPackage dev rows).headEq t v (devPackage dev rows).computation :=
    .trans _ _ _ conversion (Definitions.conv_dev dev rows answer.conv)
  obtain ⟨s, reached, related⟩ := directedAnswer_of_conv (Definitions.devConstructors ok found) toValue
    (directedNormal_of_normal (value.normal_dev ok found))
  have same : s = v := related.eq_of_headFree value.headFree
  subst same
  exact ⟨reached, fun w other => DirectedAnswer.unique (Definitions.devConstructors ok found) other reached⟩

/-- **In a checked extension, every closed term convertible there with a term of the package typed at a
data type has exactly one answer: a value, the one answer of that term in the package.** The calls of
the declared constants below are instances, the conversion being their agreement with the compiled
calls. -/
theorem data_answer_dev {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {t u D : Tower.Tm 0}
    (conversion : Conv (devPackage dev rows).headEq t u (devPackage dev rows).computation)
    (data : DataType D) (typing : Typed pkg .nil u D) :
    ∃ v, Value v ∧ Typed pkg .nil v D ∧ DirectedAnswer pkg u v ∧
      DirectedAnswer (devPackage dev rows) t v ∧ ∀ w, DirectedAnswer (devPackage dev rows) t w → w = v := by
  obtain ⟨v, value, answer, typed, -, -⟩ := data_answer data typing
  obtain ⟨reached, unique⟩ := answer_of_conv ok found conversion value answer
  exact ⟨v, value, typed, answer, reached, unique⟩

/-- The reading of a call at closed arguments: the body applied to them. -/
theorem closed_call (bodies : Bodies Tower.Head) (name : DeclName) (q j : Nat)
    (τ : Sub Tower.Head (q + 1 + j) 0) :
    subst τ (expand bodies (genericCall name q j)) = spine (bodies name) ((allVars q j).map (subst τ)) := by
  rw [Definitions.expand_genericCall, Definitions.subst_spine, subst_liftClosed,
    TelescopeAbstraction.liftClosed_zero]

/-- The reading of one constant reads it as its term. -/
theorem reading_self (name : DeclName) (c : Tower.Tm 0) : reading [(name, c)] name = c := by
  simp [reading]

/-- **Every ground call of a recursive constant has exactly one answer in the extension, the answer of
the compiled call.** The arguments `σ` of the call are convertible, in the extension, with closed terms
`τ` of the package; the one at the call index is a closed number; the compiled call at `τ` answers the
value `v`. Then the call of the declared constant at `σ` answers `v`, and nothing else. -/
theorem recursive_call_answer {dev : Development} {rows : SchemaTable Tower.Head} {bodies : Bodies Tower.Head} {name : DeclName}
    {q j : Nat} {r0 : Tower.Tm (q + j)} {r1 : Tower.Tm (q + 1 + j)}
    (recursive : Recursive rows bodies name q j r0 r1) (ok : devCheck dev = true)
    (found : devRules dev = some rows) {σ τ : Sub Tower.Head (q + 1 + j) 0}
    (same : ∀ x, Conv (devPackage dev rows).headEq (σ x) (τ x) (devPackage dev rows).computation)
    (index : Typed pkg .nil (τ (idx q j)) numC) {v : Tower.Tm 0} (value : Value v)
    (answer : DirectedAnswer pkg (subst τ (expand bodies (genericCall name q j))) v) :
    DirectedAnswer (devPackage dev rows) (subst σ (genericCall name q j)) v ∧
      ∀ w, DirectedAnswer (devPackage dev rows) (subst σ (genericCall name q j)) w → w = v := by
  obtain ⟨N, numeral, -⟩ := num_answer index
  have toNumeral : ∀ x, Conv (devPackage dev rows).headEq (τ x) (withIndex τ (nat N) x)
      (devPackage dev rows).computation := by
    intro x
    by_cases h : x = idx q j
    · subst h
      rw [withIndex_idx]
      exact Definitions.conv_dev dev rows numeral.conv
    · have unchanged : withIndex τ (nat N) x = τ x := by simp [withIndex, h]
      rw [unchanged]
      exact .refl _
  have agreement := recursive.agrees (dev := dev) N (withIndex τ (nat N)) (withIndex_idx τ (nat N))
  refine answer_of_conv ok found ?_ value answer
  exact .trans _ _ _ (Conv.substitutePointwise same _)
    (.trans _ _ _ (Conv.substitutePointwise toNumeral _)
      (.trans _ _ _ agreement (.symm _ _ (Conv.substitutePointwise toNumeral _))))

/-! ## For a checked definition -/

/-- A call in telescope order is the function applied to the arguments, oldest first. -/
theorem applyClosed_spine : ∀ {n : Nat} (Γ : Ctx Tower.Head n) (τ : Sub Tower.Head n 0) (g : Tower.Tm 0),
    applyClosed Γ τ g = spine g (List.ofFn fun i : Fin n => τ i.rev)
  | _, .nil, _, _ => rfl
  | n + 1, .snoc Γ A, τ, g => by
      show Tm.app (applyClosed Γ (fun i => τ i.succ) g) (τ 0) = _
      rw [applyClosed_spine Γ (fun i => τ i.succ) g, List.ofFn_succ', List.concat_eq_append,
        Definitions.spine_append]
      simp only [Fin.rev_castSucc, Fin.rev_last]

theorem allVars_map_subst {q j : Nat} (τ : Sub Tower.Head (q + 1 + j) 0) :
    (allVars q j).map (subst τ) = List.ofFn fun i : Fin (q + 1 + j) => τ i.rev := by
  rw [allVars, List.map_ofFn]
  rfl

/-- **The class of definitions for which the rows' own reduction is proved to reach the compiled call's
answer.** The definition has `j` parameters before a call index and `q` after; at every argument list
typed along the telescope the argument at the call index is a closed number (so when the declared type
of the call index is the numbers, as written or after conversion); and its rows, as rules of the constant
`name` in the table, are a recursion on that index read at the compiled term `c`
(`Definitions.Recursive`: two rules, at `zero` and at `succ k`; both read at `c` join; the row at `zero`
does not mention the constant; every recursive call in the row at `succ k` is saturated, on `k`). The
conditions on the rows are decided by kernel evaluation, definition by definition. -/
structure RowsReach (d : Vectors.Checker.Definition) (c : Tower.Tm 0) (name : DeclName)
    (rows : SchemaTable Tower.Head) (q j : Nat) : Prop where
  arity : d.arity = q + 1 + j
  index : ∀ (h : q < d.arity) (τ : Sub Tower.Head d.arity 0), SubstMor pkg d.telescope .nil τ →
    Typed pkg .nil (τ ⟨q, h⟩) numC
  recursive : ∃ (r0 : Tower.Tm (q + j)) (r1 : Tower.Tm (q + 1 + j)),
    Recursive rows (reading [(name, c)]) name q j r0 r1

/-- **The rows' own reduction reaches the answer of the compiled call.** For a development that passes
the declaration-time check; a definition `d` with a closed function verdict (`Checked d 0 c`) in the
class `RowsReach`; and a ground call of its declared constant `name` in the extended package, at
arguments `σ` convertible there with closed terms `τ` of the package typed along the telescope (`σ = τ`
when the arguments are such terms themselves), whose declared result type at `τ` is a data type: the
rows' directed reduction has exactly one answer, and it is the one answer of the compiled call in the
unextended package, a value of the declared type. -/
theorem rows_reach {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {d : Vectors.Checker.Definition}
    {c : Tower.Tm 0} {name : DeclName} {q j : Nat} (checked : Checked d 0 c)
    (reach : RowsReach d c name rows q j) {σ τ : Sub Tower.Head d.arity 0}
    (args : SubstMor pkg d.telescope .nil τ)
    (same : ∀ x, Conv (devPackage dev rows).headEq (σ x) (τ x) (devPackage dev rows).computation)
    (data : DataType (subst τ d.result)) :
    ∃ v, Value v ∧ Typed pkg .nil v (subst τ d.result) ∧
      DirectedAnswer pkg (applyClosed d.telescope τ c) v ∧
      DirectedAnswer (devPackage dev rows) (applyClosed d.telescope σ (.const name)) v ∧
      (∀ w, DirectedAnswer pkg (applyClosed d.telescope τ c) w → w = v) ∧
      ∀ w, DirectedAnswer (devPackage dev rows) (applyClosed d.telescope σ (.const name)) w → w = v := by
  obtain ⟨v, value, compiled, typed, -, uniqueCompiled⟩ := ground_call_answer checked args data
  refine ⟨v, value, typed, compiled, ?_, uniqueCompiled, ?_⟩ <;>
  · obtain ⟨arity, index, r0, r1, recursive⟩ := reach
    obtain ⟨dname, n, telescope, result, drows⟩ := d
    have arity' : n = q + 1 + j := arity
    subst arity'
    have indexTyped : Typed pkg .nil (τ (idx q j)) numC := index (by omega) τ args
    have callCompiled : subst τ (expand (reading [(name, c)]) (genericCall name q j)) =
        applyClosed telescope τ c := by
      rw [closed_call, reading_self, allVars_map_subst, applyClosed_spine]
    have callRows : subst σ (genericCall name q j) = applyClosed telescope σ (.const name) := by
      rw [genericCall, Definitions.subst_spine, allVars_map_subst, applyClosed_spine]
      rfl
    have read : DirectedAnswer pkg (subst τ (expand (reading [(name, c)]) (genericCall name q j))) v := by
      rw [callCompiled]
      exact compiled
    have result' := recursive_call_answer recursive ok found same indexTyped value read
    rw [callRows] at result'
    first | exact result'.1 | exact result'.2

/-! ## Addition by rows -/

/-- The package extended by addition by rows and append over it. -/
abbrev addAppendExt : Rules Tower.Head := devPackage addAppendDev addAppendRows

/-- **Every call of the declared constant of addition has exactly one answer in the extension, the
numeral that the compiled addition answers.** The arguments `a`, `b` are closed terms of the extension
convertible there with closed numbers `a'`, `b'` of the package; when they are such numbers themselves,
take `a' = a` and `b' = b`. -/
theorem add_rows_answer {a b a' b' : Tower.Tm 0} (ta : Typed pkg .nil a' numC) (tb : Typed pkg .nil b' numC)
    (ha : Conv addAppendExt.headEq a a' addAppendExt.computation)
    (hb : Conv addAppendExt.headEq b b' addAppendExt.computation) :
    ∃ k, DirectedAnswer pkg (spine addTerm [a', b']) (nat k) ∧
      DirectedAnswer addAppendExt (spine (.const addName) [a, b]) (nat k) ∧
      ∀ w, DirectedAnswer addAppendExt (spine (.const addName) [a, b]) w → w = nat k := by
  obtain ⟨k, compiled, -⟩ := add_answer ta tb
  have call : subst (addArgs a' b') (expand (reading [(addName, addTerm)]) (genericCall addName 1 0)) =
      spine addTerm [a', b'] :=
    (closed_call (reading [(addName, addTerm)]) addName 1 0 (addArgs a' b')).trans
      (by rw [reading_self]; rfl)
  have read : DirectedAnswer pkg
      (subst (addArgs a' b') (expand (reading [(addName, addTerm)]) (genericCall addName 1 0))) (nat k) := by
    rw [call]
    exact compiled
  have same : ∀ x, Conv addAppendExt.headEq (addArgs a b x) (addArgs a' b' x) addAppendExt.computation := by
    intro x
    match x with
    | ⟨0, _⟩ => exact hb
    | ⟨1, _⟩ => exact ha
  have result := recursive_call_answer Definitions.add_recursive (dev := addAppendDev) addAppend_devCheck
    addAppend_rules same (show Typed pkg .nil (addArgs a' b' (idx 1 0)) numC from ta)
    (nat_value k) read
  exact ⟨k, compiled, result.1, result.2⟩

/-- **At closed numbers of the package**, the declared constant's call and the compiled call have one
and the same answer, the only one of each. -/
theorem add_rows_agree {a b : Tower.Tm 0} (ta : Typed pkg .nil a numC) (tb : Typed pkg .nil b numC) :
    ∃ k, DirectedAnswer pkg (spine addTerm [a, b]) (nat k) ∧
      DirectedAnswer addAppendExt (spine (.const addName) [a, b]) (nat k) ∧
      (∀ w, DirectedAnswer pkg (spine addTerm [a, b]) w → w = nat k) ∧
      ∀ w, DirectedAnswer addAppendExt (spine (.const addName) [a, b]) w → w = nat k := by
  obtain ⟨k, compiled, rows, unique⟩ := add_rows_answer ta tb (.refl _) (.refl _)
  exact ⟨k, compiled, rows, fun w other =>
    DirectedAnswer.unique (Vectors.vectorConstructors level1) other compiled, unique⟩

/-- **A nested call, with the declared constant in an argument**: `add (add 1 1) 1`, all three by the
rows, answers `3`, its only answer. The inner call is convertible with its answer `2`, a closed number
of the package. -/
theorem add_rows_nested :
    DirectedAnswer addAppendExt
        (spine (.const addName) [spine (.const addName) [one, one], one] : Tower.Tm 0) three ∧
      ∀ w, DirectedAnswer addAppendExt
        (spine (.const addName) [spine (.const addName) [one, one], one] : Tower.Tm 0) w → w = three := by
  obtain ⟨k, compiledInner, inner, -⟩ := add_rows_answer (nat_typed 1) (nat_typed 1) (.refl _) (.refl _)
  obtain ⟨k', compiledOuter, outer, unique⟩ := add_rows_answer (a := spine (.const addName) [one, one])
    (b := one) (nat_typed k) (nat_typed 1) inner.conv (.refl _)
  have value : Vectors.vecNormalize level1 60 (spine addTerm [spine addTerm [one, one], one]) = some three := by
    decide +kernel
  -- the compiled calls compute the numerals
  have innerIs : (nat k : Tower.Tm 0) = two := by
    have ran : Vectors.vecNormalize level1 40 (spine addTerm [one, one]) = some two := by decide +kernel
    have answer : DirectedAnswer pkg (spine addTerm [one, one]) two :=
      directedAnswer_of_answer (Vectors.vectorConstructors level1)
        ⟨Vectors.vecNormalize_sound level1 ran, (nat_value 2).normal⟩ (nat_value 2).headFree
    exact DirectedAnswer.unique (Vectors.vectorConstructors level1) compiledInner answer
  have outerIs : (nat k' : Tower.Tm 0) = three := by
    have ran : Vectors.vecNormalize level1 40 (spine addTerm [two, one]) = some three :=
      Definitions.ground_answers.1
    have answer : DirectedAnswer pkg (spine addTerm [two, one]) three :=
      directedAnswer_of_answer (Vectors.vectorConstructors level1)
        ⟨Vectors.vecNormalize_sound level1 ran, (nat_value 3).normal⟩ (nat_value 3).headFree
    rw [innerIs] at compiledOuter
    exact DirectedAnswer.unique (Vectors.vectorConstructors level1) compiledOuter answer
  rw [outerIs] at outer unique
  exact ⟨outer, unique⟩

/-! ## Append over addition by rows -/

/-- **Every call of the declared constant of append has exactly one answer in the extension, the value
that the compiled append answers**: at arguments `σ` convertible in the extension with closed terms `τ`
of the package typed along append's telescope, with a data type of elements. -/
theorem append_rows_answer {σ τ : Sub Tower.Head 5 0} (args : SubstMor pkg appendRDef.telescope .nil τ)
    (dataA : DataType (τ 4))
    (same : ∀ x, Conv addAppendExt.headEq (σ x) (τ x) addAppendExt.computation) :
    ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed appendRDef.telescope τ appendRTerm) v ∧
      DirectedAnswer addAppendExt (applyClosed appendRDef.telescope σ (.const appendName)) v ∧
      ∀ w, DirectedAnswer addAppendExt (applyClosed appendRDef.telescope σ (.const appendName)) w → w = v := by
  obtain ⟨v, value, compiled, -, -⟩ := appendR_answer args dataA
  have call : subst τ (expand (reading [(appendName, appendRTerm)]) (genericCall appendName 3 1)) =
      applyClosed appendRDef.telescope τ appendRTerm :=
    (closed_call (reading [(appendName, appendRTerm)]) appendName 3 1 τ).trans
      (by rw [reading_self]; rfl)
  have read : DirectedAnswer pkg
      (subst τ (expand (reading [(appendName, appendRTerm)]) (genericCall appendName 3 1))) v := by
    rw [call]
    exact compiled
  have result := recursive_call_answer Definitions.append_recursive (dev := addAppendDev)
    addAppend_devCheck addAppend_rules same
    (show Typed pkg .nil (τ (idx 3 1)) numC from args (3 : Fin 5)) value read
  exact ⟨v, value, compiled, result.1, result.2⟩

/-- **The written-out call**: in the extension, `append num 1 1 [2] [3]` of the declared constant has
one answer, and it is the answer of the compiled call. -/
theorem append_rows_ground :
    ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed appendRDef.telescope groundSub appendRTerm) v ∧
      DirectedAnswer addAppendExt (applyClosed appendRDef.telescope groundSub (.const appendName)) v ∧
      ∀ w, DirectedAnswer addAppendExt (applyClosed appendRDef.telescope groundSub (.const appendName)) w →
        w = v :=
  append_rows_answer groundSub_typed .num fun _ => .refl _

/-! ## Map -/

/-- The package extended by map by rows. -/
abbrev mapExt : Rules Tower.Head := devPackage mapDev mapRows

/-- **Every call of the declared constant of map has exactly one answer in the extension, the value
that the compiled map answers**: at arguments convertible in the extension with closed terms of the
package typed along map's telescope, with a data type of target elements, whatever the function
argument. -/
theorem map_rows_answer {σ τ : Sub Tower.Head 5 0} (args : SubstMor pkg mapDef.telescope .nil τ)
    (dataB : DataType (τ 3)) (same : ∀ x, Conv mapExt.headEq (σ x) (τ x) mapExt.computation) :
    ∃ c : Tower.Tm 0, Checked mapDef 0 c ∧
      ∃ v, Value v ∧ DirectedAnswer pkg (applyClosed mapDef.telescope τ c) v ∧
        DirectedAnswer mapExt (applyClosed mapDef.telescope σ (.const mapName)) v ∧
        ∀ w, DirectedAnswer mapExt (applyClosed mapDef.telescope σ (.const mapName)) w → w = v := by
  obtain ⟨c, checked, recursive⟩ := Definitions.map_recursive
  have typedB : Typed pkg .nil (τ 3) U0 := args (3 : Fin 5)
  have typedN : Typed pkg .nil (τ 1) numC := args (1 : Fin 5)
  have data : DataType (subst τ mapDef.result) := vec_dataType typedB dataB typedN
  obtain ⟨v, value, compiled, -, -, -⟩ := ground_call_answer checked args data
  have call : subst τ (expand (reading [(mapName, c)]) (genericCall mapName 1 3)) =
      applyClosed mapDef.telescope τ c :=
    (closed_call (reading [(mapName, c)]) mapName 1 3 τ).trans (by rw [reading_self]; rfl)
  have read : DirectedAnswer pkg
      (subst τ (expand (reading [(mapName, c)]) (genericCall mapName 1 3))) v := by
    rw [call]
    exact compiled
  have result := recursive_call_answer recursive (dev := mapDev) map_devCheck map_rules same
    (show Typed pkg .nil (τ (idx 1 3)) numC from typedN) value read
  exact ⟨c, checked, v, value, compiled, result.1, result.2⟩

/-! ## A definition without a call index -/

/-- **Every ground call of a constant defined by one row without a call index has exactly one answer in
the extension, the answer of the compiled call**: at arguments convertible in the extension with closed
terms at which the compiled call answers a value. -/
theorem plain_call_answer {dev : Development} {rows : SchemaTable Tower.Head} {bodies : Bodies Tower.Head}
    {name : DeclName} {a : Nat} {r : Tower.Tm a} (plain : Definitions.Plain rows bodies name a r)
    (ok : devCheck dev = true) (found : devRules dev = some rows) {σ τ : Sub Tower.Head a 0}
    (same : ∀ x, Conv (devPackage dev rows).headEq (σ x) (τ x) (devPackage dev rows).computation)
    {v : Tower.Tm 0} (value : Value v)
    (answer : DirectedAnswer pkg (subst τ (expand bodies (Definitions.plainCall name a))) v) :
    DirectedAnswer (devPackage dev rows) (subst σ (Definitions.plainCall name a)) v ∧
      ∀ w, DirectedAnswer (devPackage dev rows) (subst σ (Definitions.plainCall name a)) w → w = v := by
  refine answer_of_conv ok found ?_ value answer
  exact .trans _ _ _ (Conv.substitutePointwise same _) (plain.agrees (dev := dev) τ)

/-- The package extended by `dup` by rows. -/
abbrev dupExt : Rules Tower.Head := devPackage Definitions.dupDev Definitions.dupRows

/-- **Every call of the declared constant of `dup` has exactly one answer in the extension, the value
of the pair type that the compiled `dup` answers.** -/
theorem dup_rows_answer {a a' : Tower.Tm 0} (ta : Typed pkg .nil a' numC)
    (ha : Conv dupExt.headEq a a' dupExt.computation) :
    ∃ c : Tower.Tm 0, Checked Definitions.dupDef 0 c ∧
      ∃ v, Value v ∧ DirectedAnswer pkg (.app c a') v ∧
        DirectedAnswer dupExt (.app (.const Definitions.dupName) a) v ∧
        ∀ w, DirectedAnswer dupExt (.app (.const Definitions.dupName) a) w → w = v := by
  obtain ⟨c, checked, plain⟩ := Definitions.dup_plain
  have args : SubstMor pkg Definitions.dupDef.telescope .nil (fun _ => a') := by
    intro x
    match x with
    | ⟨0, _⟩ => exact ta
  obtain ⟨v, value, compiled, -, -, -⟩ := ground_call_answer checked args (DataType.sigma .num .num)
  have call : subst (fun _ => a') (expand (reading [(Definitions.dupName, c)])
      (Definitions.plainCall Definitions.dupName 1)) = .app c a' := by
    show Tm.app (subst (fun _ => a') (liftClosed (reading [(Definitions.dupName, c)] Definitions.dupName))) a' = _
    rw [reading_self, subst_liftClosed, TelescopeAbstraction.liftClosed_zero]
  have read : DirectedAnswer pkg (subst (fun _ => a') (expand (reading [(Definitions.dupName, c)])
      (Definitions.plainCall Definitions.dupName 1))) v := by
    rw [call]
    exact compiled
  have result := plain_call_answer plain (dev := Definitions.dupDev) Definitions.dup_devCheck
    Definitions.dup_rules (σ := fun _ => a) (τ := fun _ => a') (fun _ => ha) value read
  exact ⟨c, checked, v, value, compiled, result.1, result.2⟩

/-! ## The three definitions, through the theorem for checked definitions -/

/-- Addition by rows is in the class: one later parameter, no earlier one. -/
theorem add_rowsReach : RowsReach addDef addTerm addName addAppendRows 1 0 :=
  ⟨rfl, fun _ _ args => args _, _, _, Definitions.add_recursive⟩

/-- Append over it is in the class: one earlier parameter, three later ones. Its rows are those of the
checked definition `appendRDef`, whose declared type is written with the compiled addition. -/
theorem append_rowsReach : RowsReach appendRDef appendRTerm appendName addAppendRows 3 1 :=
  ⟨rfl, fun _ _ args => args _, _, _, Definitions.append_recursive⟩

/-- Map is in the class: three earlier parameters, one later one. -/
theorem map_rowsReach : ∃ c : Tower.Tm 0, Checked mapDef 0 c ∧ RowsReach mapDef c mapName mapRows 1 3 := by
  obtain ⟨c, checked, recursive⟩ := Definitions.map_recursive
  exact ⟨c, checked, rfl, fun _ _ args => args _, _, _, recursive⟩

/-- **Addition, by the theorem for checked definitions**: every ground call of the declared constant,
at arguments convertible in the extension with closed numbers of the package, has exactly one answer,
the one answer of the compiled call. -/
theorem add_rows_reach {σ τ : Sub Tower.Head 2 0} (args : SubstMor pkg addDef.telescope .nil τ)
    (same : ∀ x, Conv addAppendExt.headEq (σ x) (τ x) addAppendExt.computation) :
    ∃ v, Value v ∧ Typed pkg .nil v numC ∧
      DirectedAnswer pkg (applyClosed addDef.telescope τ addTerm) v ∧
      DirectedAnswer addAppendExt (applyClosed addDef.telescope σ (.const addName)) v ∧
      (∀ w, DirectedAnswer pkg (applyClosed addDef.telescope τ addTerm) w → w = v) ∧
      ∀ w, DirectedAnswer addAppendExt (applyClosed addDef.telescope σ (.const addName)) w → w = v :=
  rows_reach addAppend_devCheck addAppend_rules add_checked add_rowsReach args same .num

/-- **Append, by the theorem for checked definitions**: every ground call of the declared constant, at
arguments convertible in the extension with closed terms of the package typed along the telescope, with
a data type of elements, has exactly one answer, the one answer of the compiled call, a value of type
`vec A (add n m)`. -/
theorem append_rows_reach {σ τ : Sub Tower.Head 5 0} (args : SubstMor pkg appendRDef.telescope .nil τ)
    (dataA : DataType (τ 4))
    (same : ∀ x, Conv addAppendExt.headEq (σ x) (τ x) addAppendExt.computation) :
    ∃ v, Value v ∧ Typed pkg .nil v (subst τ appendRDef.result) ∧
      DirectedAnswer pkg (applyClosed appendRDef.telescope τ appendRTerm) v ∧
      DirectedAnswer addAppendExt (applyClosed appendRDef.telescope σ (.const appendName)) v ∧
      (∀ w, DirectedAnswer pkg (applyClosed appendRDef.telescope τ appendRTerm) w → w = v) ∧
      ∀ w, DirectedAnswer addAppendExt (applyClosed appendRDef.telescope σ (.const appendName)) w → w = v :=
  rows_reach addAppend_devCheck addAppend_rules appendR_checked append_rowsReach args same
    (appendR_result_data args dataA)

/-! ## Control: the rows must read at the term -/

/-- `λ n m. m`: a term that meets addition's row at `zero` and not its row at `succ k`. -/
def secondArgument : Tower.Tm 0 := .lam (.lam (.var 0))

/-- **The reading of the row at `succ k` cannot be dropped.** Read as `λ n m. m`, addition by rows
meets every condition of `Definitions.Recursive` but that one: its two rules are in the table, the row
at `zero` reads, the recursive call is saturated; the row at `succ k` does not read, at any budget; and
agreement fails, for `add 1 0` by rows and `(λ n m. m) 1 0` are not convertible in the extended package:
the first answers `1` and the second `0`. -/
theorem reading_control :
    ((⟨1 + 0, (subst (Definitions.atZero 1 0) (genericCall addName 1 0), .var 0)⟩ :
        Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ addAppendRows) ∧
      ((⟨1 + 1 + 0, (subst (Definitions.atSucc 1 0) (genericCall addName 1 0),
          succC (spine (.const addName) [.var 1, .var 0]))⟩ :
        Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ addAppendRows) ∧
      (∃ fuel, Definitions.joins fuel
        (expand (reading [(addName, secondArgument)]) (subst (Definitions.atZero 1 0) (genericCall addName 1 0)))
        (expand (reading [(addName, secondArgument)]) (.var 0 : Tower.Tm (1 + 0))) = true) ∧
      (∃ fuel, Definitions.saturated? addName 1 0 fuel (idx 1 0)
        (succC (spine (.const addName) [.var 1, .var 0]) : Tower.Tm (1 + 1 + 0)) = true) ∧
      (¬ ∃ fuel, Definitions.joins fuel
        (expand (reading [(addName, secondArgument)]) (subst (Definitions.atSucc 1 0) (genericCall addName 1 0)))
        (expand (reading [(addName, secondArgument)])
          (succC (spine (.const addName) [.var 1, .var 0]) : Tower.Tm (1 + 1 + 0))) = true) ∧
      ¬ Conv addAppendExt.headEq (spine (.const addName) [one, zeroC] : Tower.Tm 0)
        (spine secondArgument [one, zeroC]) addAppendExt.computation := by
  have zeroNormal : ConstructorSystem.Normal pkg (zeroC : Tower.Tm 0) :=
    Vectors.const_normal level1 (by decide)
  have oneNormal : ConstructorSystem.Normal pkg (one : Tower.Tm 0) := Vectors.succ_normal level1 zeroNormal
  refine ⟨by decide +kernel, by decide +kernel, ⟨30, by decide +kernel⟩, ⟨8, by decide +kernel⟩, ?_, ?_⟩
  · rintro ⟨fuel, ok⟩
    have instance_ := Conv.substitute (addArgs zeroC zeroC) (Definitions.joins_conv ok)
    have left : Vectors.vecNormalize level1 20 (subst (addArgs zeroC zeroC)
        (expand (reading [(addName, secondArgument)])
          (subst (Definitions.atSucc 1 0) (genericCall addName 1 0)))) = some zeroC := by decide +kernel
    have right : Vectors.vecNormalize level1 20 (subst (addArgs zeroC zeroC)
        (expand (reading [(addName, secondArgument)])
          (succC (spine (.const addName) [.var 1, .var 0]) : Tower.Tm (1 + 1 + 0)))) = some one := by
      decide +kernel
    have conversion : Conv pkg.headEq (zeroC : Tower.Tm 0) one pkg.computation :=
      .trans _ _ _ (.symm _ _ (conv_of_stepStar (Vectors.vecNormalize_sound level1 left)))
        (.trans _ _ _ instance_ (conv_of_stepStar (Vectors.vecNormalize_sound level1 right)))
    have same := Vectors.vectors_eq_of_normal level1 zeroNormal oneNormal conversion
    cases same
  · intro conversion
    have rows : Definitions.devNormalize addAppendDev addAppendRows 30
        (spine (.const addName) [one, zeroC] : Tower.Tm 0) = some one := by decide +kernel
    have term : Vectors.vecNormalize level1 20 (spine secondArgument [one, zeroC]) = some zeroC := by
      decide +kernel
    have toOne : Conv addAppendExt.headEq (spine (.const addName) [one, zeroC] : Tower.Tm 0) one
        addAppendExt.computation := conv_of_stepStar (Definitions.devNormalize_sound rows)
    have toZero : Conv addAppendExt.headEq (spine secondArgument [one, zeroC] : Tower.Tm 0) zeroC
        addAppendExt.computation :=
      Definitions.conv_dev _ _ (conv_of_stepStar (Vectors.vecNormalize_sound level1 term))
    have same := (Definitions.devConstructors addAppend_devCheck addAppend_rules).eq_of_normal
      (Value.normal_dev addAppend_devCheck addAppend_rules (.succ .zero))
      (Value.normal_dev addAppend_devCheck addAppend_rules .zero)
      (.trans _ _ _ (.symm _ _ toOne) (.trans _ _ _ conversion toZero))
    cases same

/-! ## Soundness of the reading, for every term -/

/-- **A closed term of the package convertible with a value answers it**, typed or not: the package is
a constructor system, so the value is reached by a directed reduction. -/
theorem pkg_answer_of_conv {u v : Tower.Tm 0} (conversion : Conv pkg.headEq u v pkg.computation)
    (value : Value v) : DirectedAnswer pkg u v := by
  obtain ⟨s, answer, related⟩ :=
    directedAnswer_of_conv (Vectors.vectorConstructors level1) conversion value.directedNormal
  have same : s = v := related.eq_of_headFree value.headFree
  subst same
  exact answer

/-- **The rows reach no value that the compiled reading does not answer.** For a checked development
whose rules, read at the bodies, all join (no condition on the shape of the rows), and every closed term
`t` of the extension: when the rows' reduction takes `t` to a value, that value is the answer of the
reading of `t` in the package. Nothing is asked of `t`. A value is read as itself, because the names of a
checked development are not `zero`, `succ` or `tt`. -/
theorem value_of_reading {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {bodies : Bodies Tower.Head}
    (others : ∀ d, (∀ e ∈ dev, e.1 ≠ d) → bodies d = .const d) {fuel : Nat}
    (read : Definitions.rulesRead fuel bodies rows = true) {t v : Tower.Tm 0} (value : Value v)
    (steps : StrongNormalization.ReducesStar (devPackage dev rows) t v) :
    DirectedAnswer pkg (expand bodies t) v := by
  have conversion := Definitions.conv_reading ok found others read
    (conv_of_stepStar (stepStar_of_reducesStar steps))
  have names := Definitions.dev_names_ne_constructors ok
  have fixed : expand bodies v = v :=
    value.expand_eq (others _ names.1) (others _ names.2.1) (others _ names.2.2)
  rw [fixed] at conversion
  exact pkg_answer_of_conv conversion value

/-- **Instance**, for addition and append by rows read at their compiled terms: the rows take `add 1 0`
to `1`, so its reading, the compiled addition at `1` and `0`, answers `1`. -/
theorem add_value_of_reading :
    StrongNormalization.ReducesStar addAppendExt (spine (.const addName) [one, zeroC] : Tower.Tm 0) one ∧
      DirectedAnswer pkg
        (expand Definitions.addAppendReading (spine (.const addName) [one, zeroC] : Tower.Tm 0)) one := by
  have rows : Definitions.devNormalize addAppendDev addAppendRows 30
      (spine (.const addName) [one, zeroC] : Tower.Tm 0) = some one := by decide +kernel
  have value : Value (one : Tower.Tm 0) := .succ .zero
  have answer : DirectedAnswer addAppendExt (spine (.const addName) [one, zeroC] : Tower.Tm 0) one :=
    directedAnswer_of_answer (Definitions.devConstructors addAppend_devCheck addAppend_rules)
      ⟨Definitions.devNormalize_sound rows, value.normal_dev addAppend_devCheck addAppend_rules⟩
      value.headFree
  exact ⟨answer.1, value_of_reading addAppend_devCheck addAppend_rules Definitions.addAppend_others
    Definitions.addAppend_read value answer.1⟩

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
open NativeTypesOnTheStep.Computing.Definitions
#print axioms Value.normal_dev
#print axioms answer_of_conv
#print axioms data_answer_dev
#print axioms recursive_call_answer
#print axioms applyClosed_spine
#print axioms rows_reach
#print axioms add_rowsReach
#print axioms append_rowsReach
#print axioms map_rowsReach
#print axioms add_rows_reach
#print axioms append_rows_reach
#print axioms add_rows_answer
#print axioms add_rows_agree
#print axioms add_rows_nested
#print axioms append_rows_answer
#print axioms append_rows_ground
#print axioms map_rows_answer
#print axioms plain_call_answer
#print axioms dup_rows_answer
#print axioms reading_control
#print axioms pkg_answer_of_conv
#print axioms value_of_reading
#print axioms add_value_of_reading
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
