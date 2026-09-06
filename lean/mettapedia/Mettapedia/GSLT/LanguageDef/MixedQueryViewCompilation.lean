import Mettapedia.Languages.MeTTa.TermView
import Mathlib.Data.List.OfFn

/-!
# Mixed query children at the structural matching boundary

A query root may combine computed values with source/environment children.
Rigid structure is inspected through the existing term-layer coalgebra. A
conservative route forces the residual system at the first capture. A fully
resumed route submits only the current equation to one existing unifier step,
composes the checked binding into retained environments, and resumes borrowed
traversal. Both preserve the complete reference elimination trace, including
aliases, occurs failures, speculative updates, and exact fuel.

These routes preserve the reference equation order and make no evaluation-
scheduling transformation. Computed children are supplied results;
evaluation, mutable storage, and source-lifetime checks remain separate
implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MixedQueryViewCompilation

open CompiledPlanOpenActivationViewCompilation
open DelayedSourceBindingCompilation
open TermObservationCoalgebra
open UnificationEliminationTraceCompilation
open Mettapedia.Languages.MeTTa.TermViewCompilation
open Mettapedia.Logic.LP

universe uOwner uRevision uValue uNext

variable {Owner : Type uOwner} {Revision : Type uRevision}

def openTermsOfList : List OpenTerm -> OpenTerms
  | [] => .nil
  | head :: tail => .cons head (openTermsOfList tail)

@[simp] theorem openTermsToList_ofList (values : List OpenTerm) :
    openTermsToList (openTermsOfList values) = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [openTermsOfList, openTermsToList, inductionHypothesis]

/-- A root overlay retains each child's own representation. A
computed child is not replaced by the original arithmetic source syntax. -/
structure MixedQuery (Owner : Type uOwner) (Revision : Type uRevision) where
  head : List UInt8
  children : List (BindingValue Owner Revision)

def MixedQuery.force (query : MixedQuery Owner Revision) : OpenTerm :=
  .application query.head
    (openTermsOfList (query.children.map BindingValue.denote))

/-- Only the mixed root is new. Its descendants are the already established
eager/source-view carrier. -/
inductive Value (Owner : Type uOwner) (Revision : Type uRevision) where
  | binding (value : BindingValue Owner Revision)
  | query (query : MixedQuery Owner Revision)

def Value.force : Value Owner Revision -> OpenTerm
  | .binding value => value.denote
  | .query overlay => overlay.force

def Value.out : Value Owner Revision -> TermLayer (Value Owner Revision)
  | .binding value => (outBinding value).map .binding
  | .query overlay =>
      .application overlay.head (overlay.children.map .binding)

/-- The independent mixed-root observer is a coalgebra morphism to complete
term forcing, even when its children use different representations. -/
theorem Value.out_exact (value : Value Owner Revision) :
    (Value.out value).map Value.force = outOpen value.force := by
  cases value with
  | binding value =>
      simpa [Value.out, TermLayer.map_comp, Function.comp_def, Value.force]
        using outBinding_exact value
  | query overlay =>
      simp [Value.out, Value.force, MixedQuery.force, outOpen,
        TermLayer.map, List.map_map, Function.comp_def]

abbrev UnifierTerm := Mettapedia.Logic.LP.Term openSignature
abbrev UnifierEquation := UnifierTerm × UnifierTerm

def encodeWork {Child : Type uValue} (force : Child -> OpenTerm)
    (work : List (Child × Child)) : List UnifierEquation :=
  work.map fun pair =>
    (encodeOpenTerm (force pair.1), encodeOpenTerm (force pair.2))

@[simp] theorem encodeWork_cons {Child : Type uValue}
    (force : Child -> OpenTerm) (left right : Child)
    (rest : List (Child × Child)) :
    encodeWork force ((left, right) :: rest) =
      (encodeOpenTerm (force left), encodeOpenTerm (force right)) ::
        encodeWork force rest := rfl

@[simp] theorem encodeWork_append {Child : Type uValue}
    (force : Child -> OpenTerm) (left right : List (Child × Child)) :
    encodeWork force (left ++ right) =
      encodeWork force left ++ encodeWork force right := by
  simp [encodeWork]

theorem encodeWork_zipWith {Child : Type uValue}
    (force : Child -> OpenTerm) (left right : List Child) :
    encodeWork force (List.zipWith Prod.mk left right) =
      List.zipWith Prod.mk
        (left.map (encodeOpenTerm ∘ force))
        (right.map (encodeOpenTerm ∘ force)) := by
  induction left generalizing right with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons other others =>
          change _ :: encodeWork force (List.zipWith Prod.mk tail others) =
            _ :: List.zipWith Prod.mk _ _
          rw [inductionHypothesis]
          rfl

theorem encodeOpenTerms_eq_map (values : OpenTerms) :
    encodeOpenTerms values = (openTermsToList values).map encodeOpenTerm := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp [encodeOpenTerms, openTermsToList, encodeOpenTerms_eq_map tail]

private def encodeApplication (head : List UInt8)
    (children : List UnifierTerm) : UnifierTerm :=
  .app { head, arity := children.length } children.get

private def encodeLayer : TermLayer OpenTerm -> UnifierTerm
  | .symbol name => .const (.symbol name)
  | .variable name => .var name
  | .string value => .const (.string value)
  | .integer value => .const (.integer value)
  | .application head children =>
      encodeApplication head (children.map encodeOpenTerm)

private theorem encodeLayer_outOpen (value : OpenTerm) :
    encodeLayer (outOpen value) = encodeOpenTerm value := by
  cases value with
  | symbol name => rfl
  | «variable» name => rfl
  | string value => rfl
  | integer value => rfl
  | application head children =>
      simp only [encodeLayer, outOpen, encodeOpenTerm,
        encodeApplication]
      rw [encodeOpenTerms_eq_map]

private theorem transportArguments
    (left right : OpenFunctionSymbol) (same : left = right)
    (arguments : Fin right.arity -> UnifierTerm) (index : Fin left.arity) :
    (same ▸ arguments) index =
      arguments (Fin.cast (congrArg OpenFunctionSymbol.arity same) index) := by
  cases same
  rfl

private theorem finPairsToList_get (left right : List UnifierTerm)
    (sameLength : left.length = right.length) :
    finPairsToList left.get (fun index => right.get (Fin.cast sameLength index)) =
      List.zipWith Prod.mk left right := by
  apply List.ext_getElem
  · simp [finPairsToList, sameLength]
  · intro index firstBound secondBound
    simp [finPairsToList]

private theorem runTrace_application
    (fuel : Nat) (head : List UInt8)
    (left right : List UnifierTerm) (rest : List UnifierEquation)
    (sameLength : left.length = right.length) :
    runTrace (fuel + 1)
        ((encodeApplication head left, encodeApplication head right) :: rest) =
      runTrace fuel (List.zipWith Prod.mk left right ++ rest) := by
  simp only [encodeApplication, runTrace]
  have sameHead : (OpenFunctionSymbol.mk head left.length) =
      OpenFunctionSymbol.mk head right.length := by
    rw [sameLength]
  rw [dif_pos sameHead]
  congr 1
  congr 1
  convert finPairsToList_get left right sameLength using 1
  congr 1
  funext index
  exact transportArguments _ _ sameHead right.get index

/-- Delete equal rigid leaves or expose matching rigid children. A variable,
capture, or mismatch is delegated to the existing unifier. -/
def rigidStep? {Child : Type uValue}
    (left right : TermLayer Child) (rest : List (Child × Child)) :
    Option (List (Child × Child)) :=
  match left, right with
  | .symbol first, .symbol second => if first = second then some rest else none
  | .string first, .string second => if first = second then some rest else none
  | .integer first, .integer second => if first = second then some rest else none
  | _, _ => decomposeLayers? left right rest

theorem rigidStep?_natural {Child : Type uValue} {Next : Type uNext}
    (function : Child -> Next) (left right : TermLayer Child)
    (rest : List (Child × Child)) :
    (rigidStep? left right rest).map (mapEquations function) =
      rigidStep? (left.map function) (right.map function)
        (mapEquations function rest) := by
  cases left <;> cases right <;>
    simp only [rigidStep?, TermLayer.map, decomposeLayers?, List.length_map,
      Option.map_none]
  all_goals split <;> simp_all [mapEquations_zipWith]

private theorem runTrace_rigidLayer
    (fuel : Nat) (left right : TermLayer OpenTerm)
    (rest next : List (OpenTerm × OpenTerm))
    (accepted : rigidStep? left right rest = some next) :
    runTrace (fuel + 1)
        ((encodeLayer left, encodeLayer right) :: encodeWork id rest) =
      runTrace fuel (encodeWork id next) := by
  cases left <;> cases right <;>
    simp only [rigidStep?, decomposeLayers?] at accepted
  all_goals try contradiction
  case symbol.symbol first second =>
    split at accepted <;> simp_all [encodeLayer, runTrace]
  case string.string first second =>
    split at accepted <;> simp_all [encodeLayer, runTrace]
  case integer.integer first second =>
    split at accepted <;> simp_all [encodeLayer, runTrace]
  case application.application leftHead leftChildren rightHead rightChildren =>
    split at accepted
    next equalities =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at equalities
      rcases equalities with ⟨sameHead, sameLength⟩
      subst rightHead
      cases accepted
      simp only [encodeLayer, encodeWork_append, encodeWork_zipWith]
      exact runTrace_application fuel leftHead _ _ _
        (by simpa using sameLength)
    next => contradiction

private theorem encodeWork_map {Child : Type uValue}
    (force : Child -> OpenTerm) (work : List (Child × Child)) :
    encodeWork id (mapEquations force work) = encodeWork force work := by
  simp [encodeWork, mapEquations, mapEquation, List.map_map, Function.comp_def]

/-- A rigid observation performs exactly one reference unifier step. This
includes the fuel cost and preserves all remaining equations in order. -/
theorem runTrace_rigidStep {Child : Type uValue}
    (out : Child -> TermLayer Child) (force : Child -> OpenTerm)
    (commutes : ∀ value, (out value).map force = outOpen (force value))
    (fuel : Nat) (left right : Child) (rest next : List (Child × Child))
    (accepted : rigidStep? (out left) (out right) rest = some next) :
    runTrace (fuel + 1) (encodeWork force ((left, right) :: rest)) =
      runTrace fuel (encodeWork force next) := by
  have lifted := rigidStep?_natural force (out left) (out right) rest
  rw [accepted, Option.map_some, commutes, commutes] at lifted
  have exactStep := runTrace_rigidLayer fuel (outOpen (force left))
    (outOpen (force right)) (mapEquations force rest)
    (mapEquations force next) lifted.symm
  simpa only [encodeLayer_outOpen, encodeWork_map, encodeWork_cons] using exactStep

/-- Execute rigid observations directly on the representation. The first
capture boundary forces the complete residual system once and transfers it to
the existing unifier, retaining shared substitution and failure authority. -/
def runDirect {Child : Type uValue}
    (out : Child -> TermLayer Child) (force : Child -> OpenTerm) :
    Nat -> List (Child × Child) -> EliminationTrace openSignature
  | 0, _ => ⟨[], .fuelExhausted⟩
  | _ + 1, [] => ⟨[], .success⟩
  | fuel + 1, (left, right) :: rest =>
      match rigidStep? (out left) (out right) rest with
      | some next => runDirect out force fuel next
      | none => runTrace (fuel + 1) (encodeWork force ((left, right) :: rest))

/-- The independently executed representation-level rigid prefix, followed
by capture forcing, has the exact complete reference elimination trace. -/
theorem runDirect_exact {Child : Type uValue}
    (out : Child -> TermLayer Child) (force : Child -> OpenTerm)
    (commutes : ∀ value, (out value).map force = outOpen (force value))
    (fuel : Nat) (work : List (Child × Child)) :
    runDirect out force fuel work = runTrace fuel (encodeWork force work) := by
  induction fuel generalizing work with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases work with
      | nil => rfl
      | cons pair rest =>
          rcases pair with ⟨left, right⟩
          simp only [runDirect]
          cases accepted : rigidStep? (out left) (out right) rest with
          | none => rfl
          | some next =>
              simp only
              rw [inductionHypothesis]
              exact (runTrace_rigidStep out force commutes fuel
                left right rest next accepted).symm

def runMixed (fuel : Nat) (work : List (Value Owner Revision × Value Owner Revision)) :
    EliminationTrace openSignature :=
  runDirect Value.out Value.force fuel work

theorem runMixed_exact (fuel : Nat)
    (work : List (Value Owner Revision × Value Owner Revision)) :
    runMixed fuel work = runTrace fuel (encodeWork Value.force work) :=
  runDirect_exact Value.out Value.force Value.out_exact fuel work

/-- Success exposes the same complete substitution as materialize-then-unify;
occurs failure, mismatch, and fuel exhaustion publish no substitution. -/
theorem observe_runMixed_exact (fuel : Nat)
    (work : List (Value Owner Revision × Value Owner Revision)) :
    observe (runMixed fuel work) = unifyFuel fuel (encodeWork Value.force work) := by
  rw [runMixed_exact]
  exact observe_runTrace_exact (signature := openSignature) fuel _

/-- The LP substitution associated to the existing open substitution carrier.
Unmapped variables remain generation-qualified identities. -/
def encodeSubstitution (substitution : OpenSubstitution) : Subst openSignature :=
  fun name => encodeOpenTerm
    ((substitution name).getD (.variable name))

mutual

theorem encode_substituteOpen (substitution : OpenSubstitution) (value : OpenTerm) :
    (encodeSubstitution substitution).applyTerm (encodeOpenTerm value) =
      encodeOpenTerm (substituteOpen substitution value) := by
  cases value with
  | symbol name => rfl
  | «variable» name => rfl
  | string value => rfl
  | integer value => rfl
  | application head children =>
      have childrenEqual := encode_substituteOpenTerms substitution children
      have lengths : (encodeOpenTerms children).length =
          (encodeOpenTerms (substituteOpenTerms substitution children)).length := by
        simpa using congrArg List.length childrenEqual
      simp only [encodeOpenTerm, substituteOpen, Subst.applyTerm]
      congr 1
      · exact congrArg (OpenFunctionSymbol.mk head) lengths
      apply (Fin.heq_fun_iff lengths).2
      intro index
      have pointwise := List.get_of_eq childrenEqual
        (⟨index.val, by simp⟩ :
          Fin ((encodeOpenTerms children).map
            (encodeSubstitution substitution).applyTerm).length)
      simpa using pointwise

theorem encode_substituteOpenTerms (substitution : OpenSubstitution)
    (values : OpenTerms) :
    (encodeOpenTerms values).map (encodeSubstitution substitution).applyTerm =
      encodeOpenTerms (substituteOpenTerms substitution values) := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp only [encodeOpenTerms, substituteOpenTerms, List.map_cons]
      rw [encode_substituteOpen, encode_substituteOpenTerms]

end

theorem substituteOpenTerms_ofList (substitution : OpenSubstitution)
    (values : List OpenTerm) :
    substituteOpenTerms substitution (openTermsOfList values) =
      openTermsOfList (values.map (substituteOpen substitution)) := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [openTermsOfList, substituteOpenTerms, inductionHypothesis]

/-- Retain source trees across a logical binding update. Composition reaches
aliases stored in the old environment; it is not a frozen-slot test. -/
def extendBinding (substitution : OpenSubstitution) :
    BindingValue Owner Revision -> BindingValue Owner Revision
  | .eager value => .eager (substituteOpen substitution value)
  | .delayed view => .delayed (extendSourceView view substitution)

theorem extendBinding_denote (substitution : OpenSubstitution)
    (value : BindingValue Owner Revision) :
    (extendBinding substitution value).denote =
      substituteOpen substitution value.denote := by
  cases value with
  | eager value => rfl
  | delayed view => exact extendSourceView_force_exact view substitution

def Value.extend (substitution : OpenSubstitution) :
    Value Owner Revision -> Value Owner Revision
  | .binding value => .binding (extendBinding substitution value)
  | .query overlay => .query
      { overlay with children := overlay.children.map (extendBinding substitution) }

theorem Value.extend_force (substitution : OpenSubstitution)
    (value : Value Owner Revision) :
    (value.extend substitution).force = substituteOpen substitution value.force := by
  cases value with
  | binding value => exact extendBinding_denote substitution value
  | query overlay =>
      simp [Value.extend, Value.force, MixedQuery.force, substituteOpen,
        substituteOpenTerms_ofList, List.map_map, Function.comp_def,
        extendBinding_denote]

/-- Every equation sees the same logical substitution, while each delayed
child retains its own source origin, generation, and composed environment. -/
theorem encodeWork_extend (substitution : OpenSubstitution)
    (work : List (Value Owner Revision × Value Owner Revision)) :
    encodeWork Value.force (mapEquations (Value.extend substitution) work) =
      (encodeSubstitution substitution).applyEqs (encodeWork Value.force work) := by
  induction work with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
      rcases pair with ⟨left, right⟩
      simp only [mapEquations_cons, encodeWork_cons, Value.extend_force,
        Subst.applyEqs, List.map_cons]
      rw [← encode_substituteOpen, ← encode_substituteOpen]
      exact congrArg (_ :: ·) inductionHypothesis

/-- After an independently supplied logical elimination, rigid traversal can
resume on composed source environments with exactly the LP residual system.
This is a semantic update law; a mutable physical store must refine it. -/
theorem runMixed_after_substitution (substitution : OpenSubstitution)
    (fuel : Nat) (work : List (Value Owner Revision × Value Owner Revision)) :
    runMixed fuel (mapEquations (Value.extend substitution) work) =
      runTrace fuel
        ((encodeSubstitution substitution).applyEqs (encodeWork Value.force work)) := by
  rw [runMixed_exact, encodeWork_extend]

def singleOpenSubstitution (name : LogicVariable) (value : OpenTerm) :
    OpenSubstitution :=
  fun other => if other = name then some value else none

theorem encode_singleOpenSubstitution (name : LogicVariable) (value : OpenTerm) :
    encodeSubstitution (singleOpenSubstitution name value) =
      Subst.single name (encodeOpenTerm value) := by
  funext other
  by_cases same : other = name <;>
    simp [encodeSubstitution, singleOpenSubstitution, Subst.single, same,
      encodeOpenTerm]

/-- Resume after a checked left-variable elimination. Any later failure
retains the exact speculative trace and therefore the same rollback demand. -/
theorem resume_after_left_capture (name : LogicVariable) (captured : OpenTerm)
    (acyclic : (encodeOpenTerm captured).occursIn name = false)
    (fuel : Nat) (rest : List (Value Owner Revision × Value Owner Revision)) :
    (runMixed fuel
      (mapEquations (Value.extend (singleOpenSubstitution name captured)) rest)).record
        (name, encodeOpenTerm captured) =
      runTrace (fuel + 1)
        ((.var name, encodeOpenTerm captured) :: encodeWork Value.force rest) := by
  rw [runMixed_after_substitution, encode_singleOpenSubstitution]
  cases captured with
  | symbol value => simp [encodeOpenTerm, runTrace, Term.occursIn]
  | «variable» other =>
      have different : name ≠ other := by
        intro same
        subst other
        simp [encodeOpenTerm, Term.occursIn] at acyclic
      simp [encodeOpenTerm, runTrace, different]
  | string value => simp [encodeOpenTerm, runTrace, Term.occursIn]
  | integer value => simp [encodeOpenTerm, runTrace, Term.occursIn]
  | application head children =>
      simp only [encodeOpenTerm] at acyclic
      simp only [encodeOpenTerm, runTrace, acyclic, Bool.false_eq_true, ↓reduceIte]

/-- The stored-pattern variable can capture a computed scalar or a forced
rigid source tree, after which composed view traversal can resume. The rigid
root premise preserves the reference unifier's variable orientation. -/
theorem resume_after_right_capture (name : LogicVariable) (captured : OpenTerm)
    (rigidRoot : ∀ other, captured ≠ .variable other)
    (acyclic : (encodeOpenTerm captured).occursIn name = false)
    (fuel : Nat) (rest : List (Value Owner Revision × Value Owner Revision)) :
    (runMixed fuel
      (mapEquations (Value.extend (singleOpenSubstitution name captured)) rest)).record
        (name, encodeOpenTerm captured) =
      runTrace (fuel + 1)
        ((encodeOpenTerm captured, .var name) :: encodeWork Value.force rest) := by
  rw [runMixed_after_substitution, encode_singleOpenSubstitution]
  cases captured with
  | symbol value => simp [encodeOpenTerm, runTrace, Term.occursIn]
  | «variable» other => exact False.elim (rigidRoot other rfl)
  | string value => simp [encodeOpenTerm, runTrace, Term.occursIn]
  | integer value => simp [encodeOpenTerm, runTrace, Term.occursIn]
  | application head children =>
      simp only [encodeOpenTerm] at acyclic
      simp only [encodeOpenTerm, runTrace, acyclic, Bool.false_eq_true, ↓reduceIte]

/-! ## Resuming the worklist after every checked front equation -/

/-- Recover the finite open-term carrier from a binding returned by the
existing unifier. This changes representation, not the binding decision. -/
def decodeUnifierTerm : UnifierTerm -> OpenTerm
  | .var name => .variable name
  | .const (.symbol name) => .symbol name
  | .const (.string value) => .string value
  | .const (.integer value) => .integer value
  | .app function arguments =>
      .application function.head
        (openTermsOfList (List.ofFn fun index => decodeUnifierTerm (arguments index)))

private theorem encodeApplication_ofFn (function : OpenFunctionSymbol)
    (arguments : Fin function.arity -> UnifierTerm) :
    encodeApplication function.head (List.ofFn arguments) = .app function arguments := by
  simp only [encodeApplication]
  congr 1
  · cases function
    simp
  · have lengthEq : (List.ofFn arguments).length = function.arity := by simp
    apply (Fin.heq_fun_iff lengthEq).2
    intro index
    simp

/-- Every finite checked binding is represented without loss, including all
generation-qualified variables and every application argument. -/
theorem encode_decodeUnifierTerm (value : UnifierTerm) :
    encodeOpenTerm (decodeUnifierTerm value) = value := by
  induction value with
  | var name => rfl
  | const constant => cases constant <;> rfl
  | app function arguments inductionHypothesis =>
      change encodeApplication function.head
        (encodeOpenTerms (openTermsOfList
          (List.ofFn fun index => decodeUnifierTerm (arguments index)))) = _
      rw [encodeOpenTerms_eq_map, openTermsToList_ofList, List.map_ofFn]
      simp only [Function.comp_def, inductionHypothesis]
      exact encodeApplication_ofFn function arguments

/-- Replay the checked front equation's logical writes into retained views.
Each update is composed into all equations before traversal resumes. -/
def extendCheckedUpdates (updates : List (BindingUpdate openSignature))
    (work : List (Value Owner Revision × Value Owner Revision)) :
    List (Value Owner Revision × Value Owner Revision) :=
  match updates with
  | [] => work
  | (name, value) :: rest =>
      extendCheckedUpdates rest
        (mapEquations
          (Value.extend (singleOpenSubstitution name (decodeUnifierTerm value))) work)

theorem encodeWork_extendCheckedUpdates (updates : List (BindingUpdate openSignature))
    (work : List (Value Owner Revision × Value Owner Revision)) :
    encodeWork Value.force (extendCheckedUpdates updates work) =
      (traceSubst updates).applyEqs (encodeWork Value.force work) := by
  induction updates generalizing work with
  | nil =>
      simp [extendCheckedUpdates, traceSubst, Subst.applyEqs, Subst.applyTerm_id]
  | cons update updates inductionHypothesis =>
      rcases update with ⟨name, value⟩
      simp only [extendCheckedUpdates, inductionHypothesis, encodeWork_extend,
        encode_singleOpenSubstitution, encode_decodeUnifierTerm, traceSubst]
      simp [Subst.applyEqs, List.map_map, Function.comp_def, Subst.applyTerm_comp]

/-- The checker consumes precisely one front equation. A nonterminal trace
passes its checked updates into the independent representation-level loop.
Its local fuel marker records the end of this single step, not global fuel
exhaustion. -/
def continueCheckedFront
    (resume : List (Value Owner Revision × Value Owner Revision) ->
      EliminationTrace openSignature)
    (front : EliminationTrace openSignature)
    (rest : List (Value Owner Revision × Value Owner Revision)) :
    EliminationTrace openSignature :=
  match front.stop with
  | .occursCheck | .constructorConflict => front
  | .fuelExhausted | .success =>
      let continuation := resume (extendCheckedUpdates front.updates rest)
      { updates := front.updates ++ continuation.updates, stop := continuation.stop }

/-- Fully resumed logical matching. Rigid constructors remain borrowed;
capture checks force only the current pair. The remaining source views are
updated by composition and inspected by this loop, including after failures
become possible through correlations with earlier captures. -/
def runResumed : Nat ->
    List (Value Owner Revision × Value Owner Revision) -> EliminationTrace openSignature
  | 0, _ => ⟨[], .fuelExhausted⟩
  | _ + 1, [] => ⟨[], .success⟩
  | fuel + 1, (left, right) :: rest =>
      match rigidStep? left.out right.out rest with
      | some next => runResumed fuel next
      | none =>
          continueCheckedFront (runResumed fuel)
            (runTrace 1 [(encodeOpenTerm left.force, encodeOpenTerm right.force)]) rest

private theorem continueCheckedFront_reference
    (fuel : Nat) (left right : OpenTerm)
    (rest : List (Value Owner Revision × Value Owner Revision))
    (declined : rigidStep? (outOpen left) (outOpen right)
      (mapEquations Value.force rest) = none) :
    continueCheckedFront (fun work => runTrace fuel (encodeWork Value.force work))
        (runTrace 1 [(encodeOpenTerm left, encodeOpenTerm right)]) rest =
      runTrace (fuel + 1)
        ((encodeOpenTerm left, encodeOpenTerm right) :: encodeWork Value.force rest) := by
  cases left <;> cases right <;>
    simp only [outOpen, rigidStep?, decomposeLayers?] at declined
  all_goals
    simp only [encodeOpenTerm, runTrace, Term.occursIn]
  all_goals try split_ifs
  all_goals simp_all [continueCheckedFront, extendCheckedUpdates,
    encodeWork_extend, encode_singleOpenSubstitution, encode_decodeUnifierTerm,
    EliminationTrace.record, encodeOpenTerms_eq_map]
  rename_i leftHead leftChildren rightHead rightChildren sameFunction
  exact False.elim (declined (congrArg OpenFunctionSymbol.head sameFunction)
    (by simpa only [encodeOpenTerms_eq_map, List.length_map]
      using congrArg OpenFunctionSymbol.arity sameFunction))

/-- The fully resumed representation-level loop has exactly the complete
reference trace with identical fuel. This includes correlations across every
capture and speculative updates preceding any later failure. -/
theorem runResumed_exact (fuel : Nat)
    (work : List (Value Owner Revision × Value Owner Revision)) :
    runResumed fuel work = runTrace fuel (encodeWork Value.force work) := by
  induction fuel generalizing work with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases work with
      | nil => rfl
      | cons pair rest =>
          rcases pair with ⟨left, right⟩
          simp only [runResumed]
          cases accepted : rigidStep? left.out right.out rest with
          | some next =>
              simp only
              rw [inductionHypothesis]
              exact (runTrace_rigidStep Value.out Value.force Value.out_exact
                fuel left right rest next accepted).symm
          | none =>
              simp only
              rw [show (runResumed fuel :
                  List (Value Owner Revision × Value Owner Revision) ->
                    EliminationTrace openSignature) =
                  (fun rest => runTrace fuel (encodeWork Value.force rest))
                from funext inductionHypothesis]
              apply continueCheckedFront_reference
              have lifted := rigidStep?_natural Value.force left.out right.out rest
              rw [accepted, Option.map_none, Value.out_exact, Value.out_exact] at lifted
              exact lifted.symm

/-- The resumed matcher publishes precisely the reference finite-term
substitution on success and no partial substitution on any failure. -/
theorem observe_runResumed_exact (fuel : Nat)
    (work : List (Value Owner Revision × Value Owner Revision)) :
    observe (runResumed fuel work) =
      unifyFuel fuel (encodeWork Value.force work) := by
  rw [runResumed_exact]
  exact observe_runTrace_exact (signature := openSignature) fuel _

namespace Canaries

private def emptyEnvironment : OpenEnvironment := fun _ => none

private def boundEnvironment : OpenEnvironment :=
  fun slot => if slot = 0 then some (.integer 9) else none

private def sourceView (generation : UInt32) (environment : OpenEnvironment)
    (source : CompiledPlanAdmission.Term) : SourceView Nat Nat :=
  { owner := 1, revision := 5, generation, environment, source }

private def mixedComputed : Value Nat Nat :=
  .query { head := [10], children :=
    [.eager (.integer 2),
     .delayed (sourceView 10 boundEnvironment
       (.application [20] (.cons (.variable 0) .nil)))] }

private def computedRule : Value Nat Nat :=
  .binding (.eager (.application [10]
    (.cons (.integer 2)
      (.cons (.application [20]
        (.cons (.variable { generation := 20, slot := 0 }) .nil)) .nil))))

/-- Computed and borrowed children coexist. Nested variable capture receives
the value from the borrowed child's own environment. -/
theorem computed_and_borrowed_capture :
    runMixed 8 [(mixedComputed, computedRule)] =
      { updates := [({ generation := 20, slot := 0 }, .const (.integer 9))],
        stop := .success } := by
  rfl

private def unevaluatedArithmetic : Value Nat Nat :=
  .query { head := [10], children :=
    [.delayed (sourceView 10 boundEnvironment
       (.application [43] (.cons (.integer 1) (.cons (.integer 1) .nil)))),
     .delayed (sourceView 10 boundEnvironment
       (.application [20] (.cons (.variable 0) .nil)))] }

/-- Reusing the original arithmetic syntax instead of its computed child
changes matching, even though the other borrowed child is unchanged. -/
theorem original_arithmetic_is_not_the_computed_child :
    (runMixed 8 [(unevaluatedArithmetic, computedRule)]).stop =
      .constructorConflict := by
  rfl

private def openX : Value Nat Nat :=
  .binding (.delayed (sourceView 10 emptyEnvironment (.variable 0)))

private def openY : Value Nat Nat :=
  .binding (.delayed (sourceView 20 emptyEnvironment (.variable 0)))

private def boxX : Value Nat Nat :=
  .binding (.delayed (sourceView 10 emptyEnvironment
    (.application [20] (.cons (.variable 0) .nil))))

private def crossChildQuery : Value Nat Nat :=
  .query { head := [10], children :=
    [.delayed (sourceView 10 emptyEnvironment (.variable 0)),
     .delayed (sourceView 10 emptyEnvironment
       (.application [20] (.cons (.variable 0) .nil)))] }

private def repeatedRule : Value Nat Nat :=
  .binding (.delayed (sourceView 20 emptyEnvironment
    (.application [10] (.cons (.variable 0) (.cons (.variable 0) .nil)))))

/-- The first child aliases two variables. The second then fails the occurs
check under that same substitution; no successful partial answer is exposed. -/
theorem cross_child_alias_occurs_failure :
    runMixed 8 [(crossChildQuery, repeatedRule)] =
      { updates := [({ generation := 10, slot := 0 },
          .var { generation := 20, slot := 0 })],
        stop := .occursCheck } := by
  rfl

/-- Independent child unifiers give a false positive for the joint system. -/
theorem independent_children_lose_alias_constraint :
    (observe (runMixed 2 [(openX, openY)])).isSome = true ∧
    (observe (runMixed 2 [(boxX, openY)])).isSome = true ∧
    observe (runMixed 8 [(crossChildQuery, repeatedRule)]) = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- A variable can capture a tree containing another generation's same slot,
but cannot capture the tree containing itself. -/
theorem generations_are_logical_identity :
    (runMixed 2 [(boxX, openY)]).stop = .success ∧
    (runMixed 2 [(boxX, openX)]).stop = .occursCheck := by
  exact ⟨rfl, rfl⟩

private def capturedAlias : BindingValue Nat Nat :=
  .delayed (sourceView 10
    (fun slot => if slot = 0 then
      some (.variable { generation := 30, slot := 4 }) else none)
    (.variable 0))

/-- Extending an already occupied environment slot follows its outer alias.
Keeping the old environment would incorrectly expose that unresolved alias. -/
theorem environment_composition_reaches_old_alias :
    outBinding (extendBinding
      (singleOpenSubstitution { generation := 30, slot := 4 } (.integer 9))
      capturedAlias) = .integer 9 ∧
    outBinding capturedAlias = .variable { generation := 30, slot := 4 } := by
  exact ⟨rfl, rfl⟩

/-- Resuming borrowed traversal after an alias write retains the cross-child
occurs failure; the failed continuation cannot publish its first binding. -/
theorem resumed_alias_preserves_occurs_failure :
    (runMixed 6
      (mapEquations (Value.extend
        (singleOpenSubstitution { generation := 10, slot := 0 }
          (.variable { generation := 20, slot := 0 }))) [(boxX, openY)])).stop =
        .occursCheck := by
  rfl

/-- The first scalar-to-variable capture can be followed by resumed borrowed
traversal, with the same complete trace as the ordinary remaining equations. -/
theorem resume_after_computed_capture :
    (runMixed 6
      (mapEquations (Value.extend
        (singleOpenSubstitution { generation := 20, slot := 0 } (.integer 2)))
        [(boxX, .binding (.delayed (sourceView 20 emptyEnvironment
          (.application [20] (.cons (.variable 0) .nil)))))] )).record
          (signature := openSignature)
          ({ generation := 20, slot := 0 }, .const (.integer 2)) =
      runTrace (signature := openSignature) 7
        ((.const (.integer 2), .var { generation := 20, slot := 0 }) ::
          encodeWork Value.force
            [(boxX, .binding (.delayed (sourceView 20 emptyEnvironment
              (.application [20] (.cons (.variable 0) .nil)))))]) := by
  exact resume_after_right_capture _ (.integer 2) (by intro other; simp) rfl 6 _

private def pinnedRegistry : SnapshotRegistry Nat Nat where
  retains owner revision _ := owner = 1 ∧ revision = 5

/-- Origin/revision are physical retention evidence, not fresh logical
variables. A stale origin can have the same denotation and still be rejected. -/
theorem physical_origin_is_not_logical_generation :
    let current := sourceView 10 emptyEnvironment (.variable 0)
    let stale := { current with owner := 2, revision := 4 }
    current.force = stale.force ∧
      pinnedRegistry.Admitted current ∧ ¬ pinnedRegistry.Admitted stale := by
  simp [sourceView, SourceView.force, pinnedRegistry, SnapshotRegistry.Admitted]

private def twoCaptureRule : Value Nat Nat :=
  .binding (.delayed (sourceView 20 emptyEnvironment
    (.application [10] (.cons (.variable 0)
      (.cons (.application [20] (.cons (.variable 1) .nil)) .nil)))))

/-- A scalar capture is followed by borrowed constructor decomposition and
then a second capture. Both bindings are returned by the resumed loop. -/
theorem fully_resumed_two_captures :
    runResumed 5 [(mixedComputed, twoCaptureRule)] =
      { updates :=
          [({ generation := 20, slot := 0 }, .const (.integer 2)),
           ({ generation := 20, slot := 1 }, .const (.integer 9))],
        stop := .success } := by
  rfl

/-- The same two captures with one fewer fuel unit retain both speculative
updates but cannot publish a successful substitution. -/
theorem fully_resumed_fuel_boundary :
    (runResumed 4 [(mixedComputed, twoCaptureRule)]).updates.length = 2 ∧
    (runResumed 4 [(mixedComputed, twoCaptureRule)]).stop = .fuelExhausted ∧
    observe (runResumed 4 [(mixedComputed, twoCaptureRule)]) = none := by
  exact ⟨rfl, rfl, rfl⟩

private def twoCaptureOccursQuery : Value Nat Nat :=
  .query { head := [10], children :=
    [.eager (.integer 2),
     .delayed (sourceView 10 emptyEnvironment
       (.application [21] (.cons (.variable 0) .nil))),
     .delayed (sourceView 10 emptyEnvironment
       (.application [20] (.cons (.variable 0) .nil)))] }

private def twoCaptureOccursRule : Value Nat Nat :=
  .binding (.delayed (sourceView 20 emptyEnvironment
    (.application [10] (.cons (.variable 0)
      (.cons (.application [21] (.cons (.variable 1) .nil))
        (.cons (.variable 1) .nil))))))

/-- Two checked captures, with rigid traversal between them, can establish
an alias that makes the later source tree fail the occurs check. -/
theorem fully_resumed_occurs_after_two_captures :
    runResumed 9 [(twoCaptureOccursQuery, twoCaptureOccursRule)] =
      { updates :=
          [({ generation := 20, slot := 0 }, .const (.integer 2)),
           ({ generation := 10, slot := 0 },
             .var { generation := 20, slot := 1 })],
        stop := .occursCheck } := by
  rfl

/-- Later occurs failure hides the complete speculative prefix. -/
theorem fully_resumed_failed_captures_are_not_published :
    observe (runResumed 9 [(twoCaptureOccursQuery, twoCaptureOccursRule)]) = none := by
  rfl

end Canaries

#print axioms Value.out_exact
#print axioms runTrace_rigidStep
#print axioms runDirect_exact
#print axioms runMixed_exact
#print axioms observe_runMixed_exact
#print axioms encode_substituteOpen
#print axioms Value.extend_force
#print axioms runMixed_after_substitution
#print axioms resume_after_left_capture
#print axioms resume_after_right_capture
#print axioms Canaries.computed_and_borrowed_capture
#print axioms Canaries.cross_child_alias_occurs_failure
#print axioms Canaries.independent_children_lose_alias_constraint
#print axioms Canaries.environment_composition_reaches_old_alias
#print axioms Canaries.resumed_alias_preserves_occurs_failure
#print axioms encode_decodeUnifierTerm
#print axioms encodeWork_extendCheckedUpdates
#print axioms runResumed_exact
#print axioms observe_runResumed_exact
#print axioms Canaries.fully_resumed_two_captures
#print axioms Canaries.fully_resumed_fuel_boundary
#print axioms Canaries.fully_resumed_occurs_after_two_captures
#print axioms Canaries.fully_resumed_failed_captures_are_not_published

end Mettapedia.GSLT.LanguageDef.MixedQueryViewCompilation
