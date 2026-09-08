import Mettapedia.GSLT.LanguageDef.RelationalOutputPatternCompilation

/-!
# Discharging an admitted output constraint once

A receipt is constructed only from a successful execution of the existing
LP unifier on an actual projected output shape. Later logical writes are
substitution composition, not replacement of earlier assignments. The original
equation then remains satisfied, and an independently executed repeated check
has a concrete sufficient fuel bound and produces no elimination updates.

Source routes retain the original occurrence-hole numbering. They traverse
transparent sequence/binding bodies and structural constructor fields; calls,
conditionals and sealed bodies are barriers. Expected descendants are selected
from the admitted parent expected value under the current composed environment.

These are annotated-source and logical-substitution laws. They do not establish
a C token's plan/activation identity, mutable-store ownership, lifetime,
rollback validity, source-role classification or correspondence of effectful
evaluation with this finite supplied-continuation model.

Source-variable identities and occurrence-hole ranges must belong to the same
logical activation throughout reuse. A caller wishing to model different
activations can include their generation in `Var`; merely reusing a printed
source name or projecting a new hole range does not preserve the receipt.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OutputConstraintDischargeCompilation

open Mettapedia.Logic.LP
open UnificationEliminationTraceCompilation
open RelationalHeadSkeletonCompilation
open RelationalOutputPatternCompilation
open CompiledAnswerEffectProgram (Program)

section ReflexiveTrace

variable {signature : LPSignature}

def diagonal (terms : List (Term signature)) : List (Equation signature) :=
  terms.map fun term => (term, term)

def workSize (terms : List (Term signature)) : Nat := (terms.map Term.size).sum

@[simp] theorem workSize_cons (term : Term signature) (rest : List (Term signature)) :
    workSize (term :: rest) = term.size + workSize rest := rfl

@[simp] theorem workSize_append (left right : List (Term signature)) :
    workSize (left ++ right) = workSize left + workSize right := by
  simp [workSize, List.sum_append]

theorem workSize_children {arity : Nat} (children : Fin arity → Term signature) :
    workSize ((List.finRange arity).map children) = ∑ index, (children index).size := by
  simpa [workSize, List.map_map, Function.comp_def]
    using (Fin.sum_univ_def (fun index => (children index).size)).symm

variable [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]

/-- An ordinary unification traversal actually deletes/decomposes all the
reflexive equations. The bound counts their finite nodes plus the terminal
empty-work check, so this is not arbitrary same-fuel equivalence. -/
theorem runTrace_diagonal (fuel : Nat) (terms : List (Term signature))
    (enough : workSize terms < fuel) :
    runTrace fuel (diagonal terms) = ⟨[], .success⟩ := by
  induction fuel generalizing terms with
  | zero => omega
  | succ fuel inductionHypothesis =>
      cases terms with
      | nil => rfl
      | cons term rest =>
          cases term with
          | var name =>
              simp only [diagonal, List.map_cons, runTrace]
              apply inductionHypothesis
              simp only [workSize_cons, Term.size] at enough
              omega
          | const name =>
              simp only [diagonal, List.map_cons, runTrace]
              apply inductionHypothesis
              simp only [workSize_cons, Term.size] at enough
              omega
          | app name children =>
              simp only [diagonal, List.map_cons, runTrace]
              have work : finPairsToList children children ++ diagonal rest =
                  diagonal (((List.finRange (signature.functionArity name)).map children) ++ rest) := by
                simp [finPairsToList, diagonal, List.map_map, Function.comp_def]
              change runTrace fuel (finPairsToList children children ++ diagonal rest) = _
              rw [work]
              apply inductionHypothesis
              rw [workSize_append, workSize_children]
              simp only [workSize_cons, Term.size] at enough
              omega

theorem runTrace_reflexive (term : Term signature) :
    runTrace (term.size + 1) [(term, term)] = ⟨[], .success⟩ := by
  apply runTrace_diagonal (terms := [term])
  simp [workSize]

end ReflexiveTrace

variable {Var Call : Type}

/-- The source, occurrence-hole offset and original expected term index the
receipt. Its evidence is an actual successful finite unification execution,
not an assumed equation between two semantic interpretations. -/
structure Receipt [DecidableEq Var]
    (start : Nat) (source : Expr Var Call) (expected : LogicalTerm Var) where
  fuel : Nat
  environment : Subst (headSignature Var)
  accepted : observe (runTrace fuel [(encode (project start source).skeleton, expected)]) =
    some environment

def discharge? [DecidableEq Var] (fuel start : Nat)
    (source : Expr Var Call) (expected : LogicalTerm Var) :
    Option (Receipt start source expected) :=
  match accepted : observe (runTrace fuel [(encode (project start source).skeleton, expected)]) with
  | none => none
  | some environment => some ⟨fuel, environment, accepted⟩

theorem Receipt.equation [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) :
    receipt.environment.applyTerm (encode (project start source).skeleton) =
      receipt.environment.applyTerm expected := by
  have successful := receipt.accepted
  rw [observe_runTrace_exact] at successful
  exact unifyFuel_sound receipt.fuel _ receipt.environment successful
    (encode (project start source).skeleton, expected) (by simp)

theorem Receipt.persists [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) (later : Subst (headSignature Var)) :
    (later ∘ₛ receipt.environment).applyTerm (encode (project start source).skeleton) =
      (later ∘ₛ receipt.environment).applyTerm expected := by
  simp only [Subst.applyTerm_comp]
  exact congrArg later.applyTerm receipt.equation

theorem Receipt.source_equation_persists [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) (later : Subst (headSignature Var)) :
    (later ∘ₛ receipt.environment).applyTerm
        (interpretOutput logicalAlgebra sourceVariable occurrenceHole start source) =
      (later ∘ₛ receipt.environment).applyTerm expected := by
  simp only [Subst.applyTerm_comp]
  exact congrArg later.applyTerm
    (successful_output_gate_reconstructs receipt.fuel start source expected
      receipt.environment receipt.accepted)

theorem Receipt.moreGeneral_persists [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) (current : Subst (headSignature Var))
    (extension : receipt.environment.moreGeneral current) :
    current.applyTerm (encode (project start source).skeleton) = current.applyTerm expected := by
  obtain ⟨later, factor⟩ := extension
  have same : current = later ∘ₛ receipt.environment := funext factor
  rw [same]
  exact receipt.persists later

/-- Rechecking the same frozen projection at a later environment invokes the
ordinary reference unifier on both currently interpreted operands. The
returned substitution would be composed into that environment. -/
def checkThen [DecidableEq Var] {Event Answer : Type}
    (left right : LogicalTerm Var) (current : Subst (headSignature Var))
    (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer) :
    StopReason × Execution Event Answer :=
  let trace := runTrace (right.size + 1) [(left, right)]
  match trace.stop with
  | .success =>
      (.success, execute (eventsThen prior (body (traceSubst trace.updates ∘ₛ current))))
  | reason => (reason, ⟨[], []⟩)

theorem checkThen_reflexive [DecidableEq Var] {Event Answer : Type}
    (term : LogicalTerm Var) (current : Subst (headSignature Var))
    (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer) :
    checkThen term term current prior body =
      (.success, execute (eventsThen prior (body current))) := by
  simp only [checkThen, runTrace_reflexive, traceSubst, Subst.comp_id_left]

/-- The repeated gate can be removed without dropping, moving or duplicating
the supplied effect program. Its event trace and every answer occurrence are
preserved, and no new logical binding is made by the skipped gate. -/
theorem Receipt.single_discharge [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) (later : Subst (headSignature Var))
    {Event Answer : Type} (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer) :
    checkThen
      ((later ∘ₛ receipt.environment).applyTerm (encode (project start source).skeleton))
      ((later ∘ₛ receipt.environment).applyTerm expected)
      (later ∘ₛ receipt.environment) prior body =
        (.success, execute (eventsThen prior (body (later ∘ₛ receipt.environment)))) := by
  rw [receipt.persists later]
  exact checkThen_reflexive _ _ prior body

/-! ## Source-directed descent with the original occurrence coordinates -/

inductive Step where
  | body
  | field (index : Nat)
  deriving DecidableEq, Repr

abbrev Focus (Var Call : Type) := Nat × Expr Var Call

def field? (start : Nat) : Exprs Var Call → Nat → Option (Focus Var Call)
  | .nil, _ => none
  | .cons first _, 0 => some (start, first)
  | .cons first rest, index + 1 => field? (project start first).next rest index

def sourceAt? (start : Nat) (source : Expr Var Call) : List Step → Option (Focus Var Call)
  | [] => some (start, source)
  | .body :: rest =>
      match source with
      | .sequence _ body | .letBody _ _ body => sourceAt? start body rest
      | _ => none
  | .field index :: rest =>
      match source with
      | .node _ fields =>
          match field? start fields index with
          | none => none
          | some (childStart, child) => sourceAt? childStart child rest
      | _ => none

def fieldPath : List Step → List Nat
  | [] => []
  | .body :: rest => fieldPath rest
  | .field index :: rest => index :: fieldPath rest

def termChild? (index : Nat) : LogicalTerm Var → Option (LogicalTerm Var)
  | .app name children =>
      if available : index < (headSignature Var).functionArity name then
        some (children ⟨index, available⟩)
      else none
  | _ => none

def termAt? : List Nat → LogicalTerm Var → Option (LogicalTerm Var)
  | [], term => some term
  | index :: rest, term =>
      match termChild? index term with
      | none => none
      | some child => termAt? rest child

theorem termChild?_node (name : String) (fields : List (LogicalTerm Var)) (index : Nat) :
    termChild? index (nodeTerm name fields) = fields[index]? := by
  by_cases available : index < fields.length <;> simp [termChild?, nodeTerm, available]

/-- Successful structural child selection commutes with later substitution.
The converse is false for a currently unbound parent variable. -/
theorem termChild?_apply (environment : Subst (headSignature Var))
    (index : Nat) (parent child : LogicalTerm Var)
    (selected : termChild? index parent = some child) :
    termChild? index (environment.applyTerm parent) = some (environment.applyTerm child) := by
  cases parent with
  | var name | const name => simp [termChild?] at selected
  | app name children =>
      by_cases available : index < (headSignature Var).functionArity name
      · simp only [termChild?, dif_pos available, Option.some.injEq] at selected
        subst child
        simp [Subst.applyTerm, termChild?, available]
      · simp only [termChild?, dif_neg available, reduceCtorEq] at selected

theorem termAt?_apply (environment : Subst (headSignature Var))
    (path : List Nat) (parent child : LogicalTerm Var)
    (selected : termAt? path parent = some child) :
    termAt? path (environment.applyTerm parent) = some (environment.applyTerm child) := by
  induction path generalizing parent child with
  | nil =>
      simp only [termAt?, Option.some.injEq] at selected
      subst child
      rfl
  | cons index rest inductionHypothesis =>
      simp only [termAt?] at selected
      cases first : termChild? index parent with
      | none => simp [first] at selected
      | some middle =>
          rw [first] at selected
          simp only [termAt?, termChild?_apply environment index parent middle first]
          exact inductionHypothesis middle child selected

def projectedFields (start : Nat) (fields : Exprs Var Call) : List (LogicalTerm Var) :=
  fillFields logicalAlgebra sourceVariable occurrenceHole (projectFields start fields).skeleton

theorem field?_exact (start : Nat) (fields : Exprs Var Call) (index : Nat)
    (childStart : Nat) (child : Expr Var Call)
    (selected : field? start fields index = some (childStart, child)) :
    (projectedFields start fields)[index]? = some (encode (project childStart child).skeleton) := by
  induction index generalizing start fields childStart child with
  | zero =>
      cases fields with
      | nil => simp [field?] at selected
      | cons first rest =>
          simp only [field?, Option.some.injEq, Prod.mk.injEq] at selected
          rcases selected with ⟨rfl, rfl⟩
          rfl
  | succ index inductionHypothesis =>
      cases fields with
      | nil => simp [field?] at selected
      | cons first rest =>
          exact inductionHypothesis (project start first).next rest childStart child selected

/-- A returned route identifies a real subterm of the actual compiled shape.
Opaque payloads have no descendant route and contribute only their own hole. -/
theorem sourceAt?_compilation (start : Nat) (source : Expr Var Call) (route : List Step)
    (childStart : Nat) (child : Expr Var Call)
    (selected : sourceAt? start source route = some (childStart, child)) :
    termAt? (fieldPath route) (encode (project start source).skeleton) =
      some (encode (project childStart child).skeleton) := by
  induction route generalizing start source childStart child with
  | nil =>
      simp only [sourceAt?, Option.some.injEq, Prod.mk.injEq] at selected
      rcases selected with ⟨rfl, rfl⟩
      rfl
  | cons step rest inductionHypothesis =>
      cases step with
      | body =>
          cases source with
          | sequence prior body => exact inductionHypothesis start body childStart child selected
          | letBody pattern producer body => exact inductionHypothesis start body childStart child selected
          | «variable» name | atom name | call payload | node name fields
            | conditional condition yes no | sealed names body => simp [sourceAt?] at selected
      | field index =>
          cases source with
          | «variable» name | atom name | call payload | sequence prior body
            | letBody pattern producer body | conditional condition yes no | sealed names body =>
              simp [sourceAt?] at selected
          | node name fields =>
              simp only [sourceAt?] at selected
              cases first : field? start fields index with
              | none => simp [first] at selected
              | some focus =>
                  rcases focus with ⟨middleStart, middle⟩
                  rw [first] at selected
                  have childTerm := field?_exact start fields index middleStart middle first
                  change termAt? (index :: fieldPath rest)
                    (nodeTerm name (projectedFields start fields)) = _
                  simp only [termAt?, termChild?_node, childTerm]
                  exact inductionHypothesis middleStart middle childStart child selected

/-- Selection is against the current parent expected value. It therefore
works when the expected parent was originally an unbound caller variable. -/
theorem Receipt.descendant [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) (later : Subst (headSignature Var))
    (route : List Step) (childStart : Nat) (child : Expr Var Call)
    (selected : sourceAt? start source route = some (childStart, child)) :
    termAt? (fieldPath route) ((later ∘ₛ receipt.environment).applyTerm expected) =
      some ((later ∘ₛ receipt.environment).applyTerm (encode (project childStart child).skeleton)) := by
  have path := termAt?_apply (later ∘ₛ receipt.environment) (fieldPath route)
    (encode (project start source).skeleton) (encode (project childStart child).skeleton)
    (sourceAt?_compilation start source route childStart child selected)
  rw [receipt.persists later] at path
  exact path

def inherit? [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) (later : Subst (headSignature Var))
    (route : List Step) : Option (Focus Var Call × LogicalTerm Var) :=
  match sourceAt? start source route with
  | none => none
  | some focus =>
      match termAt? (fieldPath route) ((later ∘ₛ receipt.environment).applyTerm expected) with
      | none => none
      | some target => some (focus, target)

/-- Inheritance uses independently selected source and expected descendants.
It does not assign the desired expected value by definition. -/
theorem Receipt.inherited_single_discharge [DecidableEq Var] {start : Nat}
    {source : Expr Var Call} {expected : LogicalTerm Var}
    (receipt : Receipt start source expected) (later : Subst (headSignature Var))
    (route : List Step) (childStart : Nat) (child : Expr Var Call) (target : LogicalTerm Var)
    (inherited : inherit? receipt later route = some ((childStart, child), target))
    {Event Answer : Type} (prior : List Event)
    (body : Subst (headSignature Var) → Program (Emit Event) Answer) :
    checkThen
      ((later ∘ₛ receipt.environment).applyTerm (encode (project childStart child).skeleton))
      target (later ∘ₛ receipt.environment) prior body =
        (.success, execute (eventsThen prior (body (later ∘ₛ receipt.environment)))) := by
  unfold inherit? at inherited
  cases selected : sourceAt? start source route with
  | none => simp [selected] at inherited
  | some focus =>
      rcases focus with ⟨selectedStart, selectedSource⟩
      rw [selected, receipt.descendant later route selectedStart selectedSource selected] at inherited
      simp only [Option.some.injEq, Prod.mk.injEq] at inherited
      rcases inherited with ⟨⟨rfl, rfl⟩, rfl⟩
      exact checkThen_reflexive _ _ prior body

namespace Canaries

private abbrev Source := Expr String String
private abbrev Environment := Subst (headSignature String)

private def pair (left right : Source) : Source :=
  .node "pair" (.cons left (.cons right .nil))

private def xSource : Source := .variable "x"
private def kept : LogicalTerm String := .const "kept"
private def other : LogicalTerm String := .const "other"
private def identity : Environment := Subst.id _

private def fromStop (fuel start : Nat) (source : Source) (expected : LogicalTerm String)
    (success : (runTrace fuel [(encode (project start source).skeleton, expected)]).stop = .success) :
    Receipt start source expected :=
  ⟨fuel, traceSubst (runTrace fuel [(encode (project start source).skeleton, expected)]).updates,
    by simp only [observe, success]⟩

private def xReceipt : Receipt 0 xSource kept := fromStop 4 0 xSource kept (by decide)
private def later : Environment := Subst.single (.inr 6) other

theorem actual_success_mints_a_receipt : (discharge? 4 0 xSource kept).isSome = true := by decide

theorem exhausted_or_conflicting_gates_mint_no_receipt :
    (discharge? 0 0 xSource kept).isNone = true ∧
      (discharge? 4 0 (.atom "other" : Source) kept).isNone = true := by decide

theorem composing_a_later_write_keeps_the_original_constraint :
    (later ∘ₛ xReceipt.environment).applyTerm (sourceVariable "x") = kept := by rfl

private def duplicateBody (_ : Environment) : Program (Emit String) String :=
  .perform (.event "body") fun _ => .choice (.pure "answer") (.pure "answer")

theorem repeated_gate_preserves_events_and_duplicate_answers :
    checkThen
      ((later ∘ₛ xReceipt.environment).applyTerm (encode (project 0 xSource).skeleton))
      ((later ∘ₛ xReceipt.environment).applyTerm kept)
      (later ∘ₛ xReceipt.environment) ["prefix"] duplicateBody =
        (.success, ⟨["prefix", "body"], ["answer", "answer"]⟩) := by
  rw [xReceipt.single_discharge]
  rfl

private def shared : Source := pair (.variable "x") (.variable "x")
private def sharedExpected : LogicalTerm String :=
  nodeTerm "pair" [callerVariable 6, callerVariable 6]
private def sharedReceipt : Receipt 0 shared sharedExpected :=
  fromStop 10 0 shared sharedExpected (by decide)

theorem a_shared_source_variable_retains_correlation_after_extension :
    (later ∘ₛ sharedReceipt.environment).applyTerm (sourceVariable "x") = other ∧
      (later ∘ₛ sharedReceipt.environment).applyTerm (callerVariable 6) = other := by
  constructor <;> rfl

theorem conflicting_repeated_fields_are_rejected_before_any_receipt :
    (discharge? 10 0 shared (nodeTerm "pair" [kept, other])).isNone = true := by decide

private def nested : Source :=
  pair (.call "same")
    (.sequence (.call "effectful-prefix")
      (.letBody (.variable "bound") (.call "producer")
        (.node "box" (.cons (.call "same") (.cons (.variable "x") .nil)))))

private def nestedRoute : List Step := [.field 1, .body, .body, .field 0]
private def openExpected : LogicalTerm String := callerVariable 9
private def nestedReceipt : Receipt 4 nested openExpected :=
  fromStop 4 4 nested openExpected (by decide)
private def bindSecondHole : Environment := Subst.single (.inl (.inr 5)) kept

theorem transparent_bodies_and_constructor_fields_preserve_hole_offsets :
    sourceAt? 4 nested [.field 0] = some (4, .call "same") ∧
      sourceAt? 4 nested nestedRoute = some (5, .call "same") := by decide

private def selectedConstant? : Option (Focus String String × LogicalTerm String) → Option (Nat × String)
  | some ((start, _), .const name) => some (start, name)
  | _ => none

theorem descendant_selection_uses_the_current_initially_open_expected_value :
    termAt? (fieldPath nestedRoute) openExpected = none ∧
      selectedConstant? (inherit? nestedReceipt bindSecondHole nestedRoute) = some (5, "kept") := by
  constructor
  · rfl
  · decide

theorem inherited_child_recheck_adds_no_binding :
    (runTrace 2
      [((bindSecondHole ∘ₛ nestedReceipt.environment).applyTerm
          (encode (project 5 (.call "same" : Source)).skeleton), kept)]).updates.length = 0 ∧
      (runTrace 2
        [((bindSecondHole ∘ₛ nestedReceipt.environment).applyTerm
            (encode (project 5 (.call "same" : Source)).skeleton), kept)]).stop = .success := by decide

theorem a_nonexistent_constructor_position_declines :
    (inherit? nestedReceipt identity [.field 2]).isNone = true := by decide

theorem call_if_and_sealed_payloads_are_not_descendant_routes :
    sourceAt? 0 (.call "callee" : Source) [.body] = none ∧
      sourceAt? 0 (.conditional (.call "condition") (.atom "kept") (.atom "other") : Source)
        [.body] = none ∧
      sourceAt? 0 (.sealed [] (.atom "kept") : Source) [.body] = none := by decide

private def opaqueSource : Source := .conditional (.call "condition") (.atom "other") (.atom "kept")
private def opaqueReceipt : Receipt 0 opaqueSource kept := fromStop 4 0 opaqueSource kept (by decide)

/-- This finite supplied continuation selects a branch and independently
checks that branch's projected static output before returning an answer. -/
private def selectedBranch (_ : Environment) : Program (Emit String) String :=
  .perform (.event "condition") fun _ =>
    if (runTrace 4 [(encode (project 1 (.atom "other" : Source)).skeleton, kept)]).stop = .success then
      .pure "answer"
    else .zero

private def wronglySkipBranch (_ : Environment) : Program (Emit String) String :=
  .perform (.event "condition") fun _ => .pure "answer"

theorem opaque_acceptance_does_not_discharge_the_selected_branch :
    (runOutputPhase 4 0 opaqueSource kept ["input-prefix"] selectedBranch) =
      (.success, ⟨["input-prefix", "condition"], []⟩) ∧
    (runOutputPhase 4 0 opaqueSource kept ["input-prefix"] wronglySkipBranch) =
      (.success, ⟨["input-prefix", "condition"], ["answer"]⟩) := by decide

theorem opaque_receipt_cannot_be_inherited_into_a_branch :
    (inherit? opaqueReceipt identity [.body]).isNone = true := by decide

theorem an_unrelated_expected_term_needs_a_new_gate :
    checkThen (xReceipt.environment.applyTerm (sourceVariable "x")) other
      xReceipt.environment ["prefix"] duplicateBody =
        (.constructorConflict, ⟨[], []⟩) := by decide

theorem changing_the_projected_source_requires_a_new_gate :
    (discharge? 4 0 (.atom "kept" : Source) kept).isSome = true ∧
      (discharge? 4 0 (.atom "other" : Source) kept).isNone = true := by decide

private def callSource : Source := .call "callee"
private def callReceipt : Receipt 0 callSource kept := fromStop 4 0 callSource kept (by decide)

theorem fresh_holes_are_not_the_previously_discharged_occurrences :
    (runTrace 4
      [(callReceipt.environment.applyTerm (encode (project 0 callSource).skeleton), kept)]).updates.length = 0 ∧
    (runTrace 4
      [(callReceipt.environment.applyTerm (encode (project 1 callSource).skeleton), kept)]).updates.length = 1 := by
  decide

private def overwriteX : Environment := Subst.single (.inl (.inl "x")) other

theorem replacing_instead_of_extending_the_environment_invalidates_the_receipt :
    (runTrace 4 [(overwriteX.applyTerm (sourceVariable "x"), overwriteX.applyTerm kept)]).stop =
      .constructorConflict ∧
    (runTrace 4
      [((overwriteX ∘ₛ xReceipt.environment).applyTerm (sourceVariable "x"),
        (overwriteX ∘ₛ xReceipt.environment).applyTerm kept)]).stop = .success := by decide

theorem rollback_to_the_entrance_environment_requires_a_new_discharge :
    (runTrace 4 [(identity.applyTerm (sourceVariable "x"), kept)]).updates.length = 1 := by decide

private def scopedSource : Expr (Nat × String) String := .variable (3, "x")
private def scopedExpected : LogicalTerm (Nat × String) := .const "kept"
private def scopedTrace := runTrace 4 [(encode (project 0 scopedSource).skeleton, scopedExpected)]
private def scopedReceipt : Receipt 0 scopedSource scopedExpected :=
  ⟨4, traceSubst scopedTrace.updates,
    by
      change observe scopedTrace = some (traceSubst scopedTrace.updates)
      simp only [observe, show scopedTrace.stop = .success by decide]⟩

theorem another_activation_with_the_same_spelling_requires_a_new_discharge :
    (runTrace 4
      [(scopedReceipt.environment.applyTerm (sourceVariable (4, "x")), scopedExpected)]).updates.length = 1 :=
  by decide

theorem too_little_recheck_fuel_is_not_logical_failure :
    (runTrace 1 [(kept, kept)]).stop = .fuelExhausted ∧
      (runTrace 2 [(kept, kept)]).stop = .success := by decide

end Canaries

#print axioms runTrace_diagonal
#print axioms Receipt.equation
#print axioms Receipt.persists
#print axioms Receipt.single_discharge
#print axioms sourceAt?_compilation
#print axioms Receipt.descendant
#print axioms Receipt.inherited_single_discharge
#print axioms Canaries.opaque_acceptance_does_not_discharge_the_selected_branch

end Mettapedia.GSLT.LanguageDef.OutputConstraintDischargeCompilation
