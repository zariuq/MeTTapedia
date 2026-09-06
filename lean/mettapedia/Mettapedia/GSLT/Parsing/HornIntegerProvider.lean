import Mettapedia.GSLT.Parsing.HornEquationContextual
import Mettapedia.GSLT.LanguageDef.ArithmeticExtension

/-!
# Integer-provider expressions on the existing ground source carrier

This module interprets a restricted expression fragment of authored equation
residuals: exact integers and addition, integer comparisons, restricted quoted
structural equality, quoted answers,
the source encoding of empty answers, and conditional answer selection.
Independent inductive judgments specify each interpretation.

`none` means unsupported syntax or an ill-typed expression in this fragment;
`some []` means supported execution with no answers. Equation occurrence
authentication precedes interpretation and uses the existing source matcher.
These theorems do not assert full PeTTa evaluation or native C correspondence.
The normalization below models only the two Boolean spelling aliases in atoms
and application heads. It is not a SWI reader or a string/quotation codec.
Source-to-PeTTa quoting and physical integer representations still require
their own realization theorems.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornIntegerProvider

open HornCertificate HornEquationInstantiation HornEquationContextual

mutual
  /-- No uppercase Boolean aliases occur, including at application heads. -/
  inductive AliasFree : GroundTerm → Prop where
    | atom {name : String} (canonical : name ≠ "True" ∧ name ≠ "False") :
        AliasFree (.atom name)
    | integer (value : Int) : AliasFree (.integer value)
    | app {name : String} {arguments : GroundTerms}
        (canonical : name ≠ "True" ∧ name ≠ "False")
        (children : AliasesFree arguments) : AliasFree (.app name arguments)

  inductive AliasesFree : GroundTerms → Prop where
    | nil : AliasesFree .nil
    | cons {head : GroundTerm} {tail : GroundTerms}
        (first : AliasFree head) (rest : AliasesFree tail) :
        AliasesFree (.cons head tail)
end

mutual
  def checkAliasFree : GroundTerm → Bool
    | .atom name => name != "True" && name != "False"
    | .integer _ => true
    | .app name arguments =>
        (name != "True" && name != "False") && checkAliasesFree arguments

  def checkAliasesFree : GroundTerms → Bool
    | .nil => true
    | .cons head tail => checkAliasFree head && checkAliasesFree tail
end

mutual
  theorem checkAliasFree_sound (term : GroundTerm)
      (checked : checkAliasFree term = true) : AliasFree term := by
    cases term with
    | atom name => exact .atom (by simpa [checkAliasFree] using checked)
    | integer value => exact .integer value
    | app name arguments =>
      have parts : (name ≠ "True" ∧ name ≠ "False") ∧
          checkAliasesFree arguments = true := by
        simpa [checkAliasFree] using checked
      exact .app parts.1 (checkAliasesFree_sound arguments parts.2)

  theorem checkAliasesFree_sound (terms : GroundTerms)
      (checked : checkAliasesFree terms = true) : AliasesFree terms := by
    cases terms with
    | nil => exact .nil
    | cons head tail =>
      have parts : checkAliasFree head = true ∧ checkAliasesFree tail = true := by
        simpa [checkAliasesFree] using checked
      exact .cons (checkAliasFree_sound head parts.1)
        (checkAliasesFree_sound tail parts.2)
end

mutual
  theorem checkAliasFree_complete {term : GroundTerm}
      (canonical : AliasFree term) : checkAliasFree term = true := by
    cases canonical with
    | atom named => simp [checkAliasFree, named.1, named.2]
    | integer => rfl
    | app named children =>
      simp [checkAliasFree, named.1, named.2, checkAliasesFree_complete children]

  theorem checkAliasesFree_complete {terms : GroundTerms}
      (canonical : AliasesFree terms) : checkAliasesFree terms = true := by
    cases canonical with
    | nil => rfl
    | cons first rest =>
      simp [checkAliasesFree, checkAliasFree_complete first, checkAliasesFree_complete rest]
end

theorem checkAliasFree_iff (term : GroundTerm) :
    checkAliasFree term = true ↔ AliasFree term :=
  ⟨checkAliasFree_sound term, checkAliasFree_complete⟩

theorem checkAliasesFree_iff (terms : GroundTerms) :
    checkAliasesFree terms = true ↔ AliasesFree terms :=
  ⟨checkAliasesFree_sound terms, checkAliasesFree_complete⟩

/-- This spelling normalization makes no claim about the rest of a host reader. -/
def normalizeAliasName (name : String) : String :=
  if name = "True" then "true" else if name = "False" then "false" else name

theorem normalizeAliasName_canonical (name : String) :
    normalizeAliasName name ≠ "True" ∧ normalizeAliasName name ≠ "False" := by
  simp only [normalizeAliasName]
  split
  · decide
  · split
    · decide
    · exact ⟨by assumption, by assumption⟩

theorem normalizeAliasName_fixed {name : String}
    (canonical : name ≠ "True" ∧ name ≠ "False") :
    normalizeAliasName name = name := by
  simp [normalizeAliasName, canonical.1, canonical.2]

mutual
  def normalizeAliases : GroundTerm → GroundTerm
    | .atom name => .atom (normalizeAliasName name)
    | .integer value => .integer value
    | .app name arguments => .app (normalizeAliasName name) (normalizeAliasesList arguments)

  def normalizeAliasesList : GroundTerms → GroundTerms
    | .nil => .nil
    | .cons head tail => .cons (normalizeAliases head) (normalizeAliasesList tail)
end

mutual
  theorem normalizeAliases_aliasFree (term : GroundTerm) :
      AliasFree (normalizeAliases term) := by
    cases term with
    | atom name => exact .atom (normalizeAliasName_canonical name)
    | integer value => exact .integer value
    | app name arguments =>
      exact .app (normalizeAliasName_canonical name) (normalizeAliasesList_aliasFree arguments)

  theorem normalizeAliasesList_aliasFree (terms : GroundTerms) :
      AliasesFree (normalizeAliasesList terms) := by
    cases terms with
    | nil => exact .nil
    | cons head tail =>
      exact .cons (normalizeAliases_aliasFree head) (normalizeAliasesList_aliasFree tail)
end

mutual
  theorem normalizeAliases_fixed {term : GroundTerm} (canonical : AliasFree term) :
      normalizeAliases term = term := by
    cases canonical with
    | atom named => simp [normalizeAliases, normalizeAliasName_fixed named]
    | integer => rfl
    | app named children =>
      simp [normalizeAliases, normalizeAliasName_fixed named, normalizeAliasesList_fixed children]

  theorem normalizeAliasesList_fixed {terms : GroundTerms} (canonical : AliasesFree terms) :
      normalizeAliasesList terms = terms := by
    cases canonical with
    | nil => rfl
    | cons first rest =>
      simp [normalizeAliasesList, normalizeAliases_fixed first, normalizeAliasesList_fixed rest]
end

theorem normalizeAliases_fixed_iff (term : GroundTerm) :
    normalizeAliases term = term ↔ AliasFree term := by
  constructor
  · intro fixed
    exact fixed ▸ normalizeAliases_aliasFree term
  · exact normalizeAliases_fixed

theorem normalizeAliases_idempotent (term : GroundTerm) :
    normalizeAliases (normalizeAliases term) = normalizeAliases term :=
  normalizeAliases_fixed (normalizeAliases_aliasFree term)

theorem normalizeAliases_eq_iff {left right : GroundTerm}
    (leftCanonical : AliasFree left) (rightCanonical : AliasFree right) :
    normalizeAliases left = normalizeAliases right ↔ left = right := by
  rw [normalizeAliases_fixed leftCanonical, normalizeAliases_fixed rightCanonical]

theorem normalizeAliases_injective_on_aliasFree {left right : GroundTerm}
    (leftCanonical : AliasFree left) (rightCanonical : AliasFree right)
    (equal : normalizeAliases left = normalizeAliases right) : left = right :=
  (normalizeAliases_eq_iff leftCanonical rightCanonical).mp equal

def evalInteger? : GroundTerm → Option Int
  | .integer value => some value
  | .app "+" (.cons left (.cons right .nil)) => do
      let first ← evalInteger? left
      let second ← evalInteger? right
      pure (first + second)
  | _ => none
termination_by term => sizeOf term

inductive IntegerEval : GroundTerm → Int → Prop where
  | integer (value : Int) : IntegerEval (.integer value) value
  | add {left right : GroundTerm} {first second : Int}
      (leftEval : IntegerEval left first) (rightEval : IntegerEval right second) :
      IntegerEval (.app "+" (.cons left (.cons right .nil))) (first + second)

theorem evalInteger?_sound (term : GroundTerm) (value : Int)
    (evaluated : evalInteger? term = some value) : IntegerEval term value := by
  unfold evalInteger? at evaluated
  split at evaluated
  · cases evaluated
    exact .integer _
  · rename_i left right
    cases firstEval : evalInteger? left with
    | none => simp [firstEval] at evaluated
    | some first =>
      cases secondEval : evalInteger? right with
      | none => simp [firstEval, secondEval] at evaluated
      | some second =>
        have equal : first + second = value := by
          simpa [firstEval, secondEval] using evaluated
        subst value
        exact .add (evalInteger?_sound left first firstEval)
          (evalInteger?_sound right second secondEval)
  · simp at evaluated
termination_by sizeOf term

theorem evalInteger?_complete {term : GroundTerm} {value : Int}
    (evaluated : IntegerEval term value) : evalInteger? term = some value := by
  induction evaluated with
  | integer value => simp [evalInteger?]
  | add _ _ first second => simp [evalInteger?, first, second]

theorem evalInteger?_iff (term : GroundTerm) (value : Int) :
    evalInteger? term = some value ↔ IntegerEval term value :=
  ⟨evalInteger?_sound term value, evalInteger?_complete⟩

def evalBoolean? : GroundTerm → Option Bool
  | .app "<" (.cons left (.cons right .nil)) => do
      let first ← evalInteger? left
      let second ← evalInteger? right
      pure (decide (first < second))
  | .app ">=" (.cons left (.cons right .nil)) => do
      let first ← evalInteger? left
      let second ← evalInteger? right
      pure (decide (first ≥ second))
  | .app "==" (.cons (.app "quote" (.cons left .nil))
      (.cons (.app "quote" (.cons right .nil)) .nil)) =>
      if checkAliasFree left && checkAliasFree right then some (decide (left = right))
      else none
  | _ => none

inductive BooleanEval : GroundTerm → Bool → Prop where
  | less {left right : GroundTerm} {first second : Int}
      (leftEval : IntegerEval left first) (rightEval : IntegerEval right second) :
      BooleanEval (.app "<" (.cons left (.cons right .nil))) (decide (first < second))
  | notLess {left right : GroundTerm} {first second : Int}
      (leftEval : IntegerEval left first) (rightEval : IntegerEval right second) :
      BooleanEval (.app ">=" (.cons left (.cons right .nil))) (decide (first ≥ second))
  | quotedEqual {left right : GroundTerm}
      (leftCanonical : AliasFree left) (rightCanonical : AliasFree right) :
      BooleanEval (.app "==" (.cons (.app "quote" (.cons left .nil))
        (.cons (.app "quote" (.cons right .nil)) .nil))) (decide (left = right))

theorem evalBoolean?_sound (term : GroundTerm) (value : Bool)
    (evaluated : evalBoolean? term = some value) : BooleanEval term value := by
  unfold evalBoolean? at evaluated
  split at evaluated
  · rename_i left right
    cases firstEval : evalInteger? left with
    | none => simp [firstEval] at evaluated
    | some first =>
      cases secondEval : evalInteger? right with
      | none => simp [firstEval, secondEval] at evaluated
      | some second =>
        have equal : decide (first < second) = value := by
          simpa [firstEval, secondEval] using evaluated
        subst value
        exact .less (evalInteger?_sound left first firstEval)
          (evalInteger?_sound right second secondEval)
  · rename_i left right
    cases firstEval : evalInteger? left with
    | none => simp [firstEval] at evaluated
    | some first =>
      cases secondEval : evalInteger? right with
      | none => simp [firstEval, secondEval] at evaluated
      | some second =>
        have equal : decide (first ≥ second) = value := by
          simpa [firstEval, secondEval] using evaluated
        subst value
        exact .notLess (evalInteger?_sound left first firstEval)
          (evalInteger?_sound right second secondEval)
  · rename_i left right
    split at evaluated
    · rename_i canonical
      have checked : checkAliasFree left = true ∧ checkAliasFree right = true := by
        simpa using canonical
      have equal : decide (left = right) = value := Option.some.inj evaluated
      subst value
      exact .quotedEqual (checkAliasFree_sound left checked.1)
        (checkAliasFree_sound right checked.2)
    · simp at evaluated
  · simp at evaluated

theorem evalBoolean?_complete {term : GroundTerm} {value : Bool}
    (evaluated : BooleanEval term value) : evalBoolean? term = some value := by
  cases evaluated with
  | less first second =>
    simp [evalBoolean?, evalInteger?_complete first, evalInteger?_complete second]
  | notLess first second =>
    simp [evalBoolean?, evalInteger?_complete first, evalInteger?_complete second]
  | quotedEqual first second =>
    simp [evalBoolean?, checkAliasFree_complete first, checkAliasFree_complete second]

theorem evalBoolean?_iff (term : GroundTerm) (value : Bool) :
    evalBoolean? term = some value ↔ BooleanEval term value :=
  ⟨evalBoolean?_sound term value, evalBoolean?_complete⟩

theorem evalBoolean?_quotedEqual {left right : GroundTerm}
    (leftCanonical : AliasFree left) (rightCanonical : AliasFree right) :
    evalBoolean? (.app "==" (.cons (.app "quote" (.cons left .nil))
      (.cons (.app "quote" (.cons right .nil)) .nil))) = some (decide (left = right)) :=
  evalBoolean?_complete (.quotedEqual leftCanonical rightCanonical)

theorem evalBoolean?_quotedEqual_refused {left right : GroundTerm}
    (noncanonical : ¬ AliasFree left ∨ ¬ AliasFree right) :
    evalBoolean? (.app "==" (.cons (.app "quote" (.cons left .nil))
      (.cons (.app "quote" (.cons right .nil)) .nil))) = none := by
  have blocked : ¬ (checkAliasFree left = true ∧ checkAliasFree right = true) := by
    simpa only [checkAliasFree_iff] using not_and_or.mpr noncanonical
  simpa only [evalBoolean?, Bool.and_eq_true] using if_neg blocked

def evalAnswers? : GroundTerm → Option (List GroundTerm)
  | .app "quote" (.cons value .nil) => some [value]
  | .app "metta-nullary" (.cons (.atom "empty") .nil) => some []
  | .app "if" (.cons guard (.cons thenBranch (.cons elseBranch .nil))) => do
      let condition ← evalBoolean? guard
      if condition then evalAnswers? thenBranch else evalAnswers? elseBranch
  | _ => none
termination_by term => sizeOf term

inductive AnswersEval : GroundTerm → List GroundTerm → Prop where
  | quote (value : GroundTerm) :
      AnswersEval (.app "quote" (.cons value .nil)) [value]
  | empty : AnswersEval (.app "metta-nullary" (.cons (.atom "empty") .nil)) []
  | ifTrue {guard thenBranch elseBranch : GroundTerm} {answers : List GroundTerm}
      (condition : BooleanEval guard true) (selected : AnswersEval thenBranch answers) :
      AnswersEval (.app "if" (.cons guard (.cons thenBranch (.cons elseBranch .nil)))) answers
  | ifFalse {guard thenBranch elseBranch : GroundTerm} {answers : List GroundTerm}
      (condition : BooleanEval guard false) (selected : AnswersEval elseBranch answers) :
      AnswersEval (.app "if" (.cons guard (.cons thenBranch (.cons elseBranch .nil)))) answers

theorem evalAnswers?_sound (term : GroundTerm) (answers : List GroundTerm)
    (evaluated : evalAnswers? term = some answers) : AnswersEval term answers := by
  unfold evalAnswers? at evaluated
  split at evaluated
  · cases evaluated
    exact .quote _
  · cases evaluated
    exact .empty
  · rename_i guard thenBranch elseBranch
    cases condition : evalBoolean? guard with
    | none => simp [condition] at evaluated
    | some value =>
      cases value with
      | false =>
        exact .ifFalse (evalBoolean?_sound guard false condition)
          (evalAnswers?_sound elseBranch answers (by simpa [condition] using evaluated))
      | true =>
        exact .ifTrue (evalBoolean?_sound guard true condition)
          (evalAnswers?_sound thenBranch answers (by simpa [condition] using evaluated))
  · simp at evaluated
termination_by sizeOf term

theorem evalAnswers?_complete {term : GroundTerm} {answers : List GroundTerm}
    (evaluated : AnswersEval term answers) : evalAnswers? term = some answers := by
  induction evaluated with
  | quote value => simp [evalAnswers?]
  | empty => simp [evalAnswers?]
  | ifTrue condition _ selected =>
    simp [evalAnswers?, evalBoolean?_complete condition, selected]
  | ifFalse condition _ selected =>
    simp [evalAnswers?, evalBoolean?_complete condition, selected]

theorem evalAnswers?_iff (term : GroundTerm) (answers : List GroundTerm) :
    evalAnswers? term = some answers ↔ AnswersEval term answers :=
  ⟨evalAnswers?_sound term answers, evalAnswers?_complete⟩

theorem AnswersEval.deterministic {term : GroundTerm} {first second : List GroundTerm}
    (left : AnswersEval term first) (right : AnswersEval term second) : first = second :=
  Option.some.inj ((evalAnswers?_complete left).symm.trans (evalAnswers?_complete right))

def runAt? (program : Program) (occurrence : Nat) (call : GroundTerm) :
    Option (List GroundTerm) := do
  let (residual, _) ← instantiateEquationAt? program occurrence call
  evalAnswers? residual

private theorem runAt?_eq (program : Program) (occurrence : Nat) (call : GroundTerm) :
    runAt? program occurrence call =
      (rewriteAt? program occurrence [] call).bind evalAnswers? := by
  cases produced : instantiateEquationAt? program occurrence call <;>
    simp [runAt?, rewriteAt?, produced]

theorem runAt?_of_step {program : Program} {occurrence : Nat}
    (safe : OccurrenceRangeSafe program occurrence)
    {call residual : GroundTerm} {answers : List GroundTerm}
    (step : StepAt program occurrence [] call residual)
    (evaluated : evalAnswers? residual = some answers) :
    runAt? program occurrence call = some answers := by
  rw [runAt?_eq, rewriteAt?_complete_at safe step]
  exact evaluated

theorem runAt?_iff {program : Program} {occurrence : Nat}
    (safe : OccurrenceRangeSafe program occurrence)
    (call : GroundTerm) (answers : List GroundTerm) :
    runAt? program occurrence call = some answers ↔
      ∃ residual, StepAt program occurrence [] call residual ∧ AnswersEval residual answers := by
  constructor
  · intro produced
    rw [runAt?_eq] at produced
    cases residual : rewriteAt? program occurrence [] call with
    | none => simp [residual] at produced
    | some term =>
      exact ⟨term, rewriteAt?_sound program occurrence [] call term residual,
        evalAnswers?_sound term answers (by simpa [residual] using produced)⟩
  · rintro ⟨residual, step, evaluated⟩
    exact runAt?_of_step safe step (evalAnswers?_complete evaluated)

theorem addition_agrees_with_exact_core (first second : Int) :
    Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger.coreSem
      .add first second = .val (first + second) := rfl

theorem integer_addition_refines_exact_core {left right : GroundTerm} {first second : Int}
    (leftEval : IntegerEval left first) (rightEval : IntegerEval right second) :
    evalInteger? (.app "+" (.cons left (.cons right .nil))) = some (first + second) ∧
      Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger.coreSem
        .add first second = .val (first + second) :=
  ⟨evalInteger?_complete (.add leftEval rightEval), addition_agrees_with_exact_core first second⟩

theorem quotation_does_not_evaluate (value : GroundTerm) :
    evalAnswers? (.app "quote" (.cons value .nil)) = some [value] := by
  simp [evalAnswers?]

theorem unsupported_unselected_branch_is_not_evaluated :
    evalAnswers? (.app "if" (.cons
      (.app "<" (.cons (.integer 0) (.cons (.integer 1) .nil)))
      (.cons (.app "quote" (.cons (.atom "answer") .nil))
      (.cons (.app "unknown" .nil) .nil)))) = some [.atom "answer"] := by
  simp [evalAnswers?, evalBoolean?, evalInteger?]

theorem supported_empty_is_not_unsupported :
    evalAnswers? (.app "metta-nullary" (.cons (.atom "empty") .nil)) = some [] ∧
      evalAnswers? (.app "unknown" .nil) = none := by simp [evalAnswers?]

theorem unsupported_selected_branch_is_not_empty :
    evalAnswers? (.app "if" (.cons
      (.app ">=" (.cons (.integer 0) (.cons (.integer 1) .nil)))
      (.cons (.app "metta-nullary" (.cons (.atom "empty") .nil))
      (.cons (.app "unknown" .nil) .nil)))) = none := by
  simp [evalAnswers?, evalBoolean?, evalInteger?]

theorem bare_empty_is_not_empty_execution :
    evalAnswers? (.atom "empty") = none := by simp [evalAnswers?]

theorem boolean_type_mismatch_is_not_false :
    evalBoolean? (.app "<" (.cons (.atom "0") (.cons (.integer 1) .nil))) = none := by
  simp [evalBoolean?, evalInteger?]

theorem unquoted_equality_is_outside_fragment :
    evalBoolean? (.app "==" (.cons (.integer 1) (.cons (.integer 1) .nil))) = none := by decide

theorem boolean_alias_normalization_collision :
    (.atom "True" : GroundTerm) ≠ .atom "true" ∧
      normalizeAliases (.atom "True") = normalizeAliases (.atom "true") := by decide

theorem boolean_alias_is_not_aliasFree :
    ¬ AliasFree (.atom "True") ∧ ¬ AliasFree (.app "False" .nil) := by
  constructor <;> intro canonical <;>
    have checked := checkAliasFree_complete canonical <;> contradiction

theorem quoted_integer_pair_equal :
    evalBoolean? (.app "=="
      (.cons (.app "quote" (.cons (.app "pair"
        (.cons (.integer 1) (.cons (.integer 2) .nil))) .nil))
      (.cons (.app "quote" (.cons (.app "pair"
        (.cons (.integer 1) (.cons (.integer 2) .nil))) .nil)) .nil))) = some true := by decide

theorem quoted_integer_pair_different :
    evalBoolean? (.app "=="
      (.cons (.app "quote" (.cons (.app "pair"
        (.cons (.integer 1) (.cons (.integer 2) .nil))) .nil))
      (.cons (.app "quote" (.cons (.app "pair"
        (.cons (.integer 1) (.cons (.integer 3) .nil))) .nil)) .nil))) = some false := by decide

theorem undecoded_alias_is_unsupported_not_empty :
    evalAnswers? (.app "if" (.cons
      (.app "==" (.cons (.app "quote" (.cons (.atom "True") .nil))
        (.cons (.app "quote" (.cons (.atom "true") .nil)) .nil)))
      (.cons (.app "metta-nullary" (.cons (.atom "empty") .nil))
      (.cons (.app "quote" (.cons (.atom "different") .nil)) .nil)))) = none := by
  simp [evalAnswers?, evalBoolean?, checkAliasFree]

#print axioms checkAliasFree_iff
#print axioms normalizeAliases_eq_iff
#print axioms evalInteger?_iff
#print axioms evalBoolean?_iff
#print axioms evalAnswers?_iff
#print axioms runAt?_iff

end Mettapedia.GSLT.Parsing.HornIntegerProvider
