import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

/-!
# Matched-only prepared HE return regions

An equation-backed region may decline when no equation matched. That decline
is not an empty language answer: HE returns the stuck call in that case.
This module connects the distinction directly to `evalAtom`. A successful
region's return analysis needs only equation-return paths; its caller must
retain the canonical path for a decline. All answers retain their order,
multiplicity and binding records.

The boundary is the existing closed, single-applicability HE call theorem.
It does not identify first-success selection with all-candidate evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPreparedReturn

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Return each actual equation reply under the head's range, then perform
HE's batch selection of successes over errors. -/
def finish (space : Space) (dispatch : GroundedDispatch) (call range : Atom)
    (fuel : Nat) (live : List Atom) (replies : ResultSet) : ResultSet :=
  HEReturns.keep (replies.flatMap fun reply =>
    ordinaryCallReturn call reply.1 reply.2 fun value bindings =>
      evalAtom space dispatch value (callReturnType range) bindings (fuel + 1) live)

/-- `none` means deoptimization. `some []` is an accepted execution with no
answers. The decision is made from query occurrences, not from body answers. -/
def attempt (space : Space) (dispatch : GroundedDispatch) (call range : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) : Option ResultSet :=
  let replies := rawQueryResults space call (callReturnType range) bindings (fuel + 1) live
  if replies.isEmpty then none else some (finish space dispatch call range fuel live replies)

theorem attempt_none_iff (space : Space) (dispatch : GroundedDispatch) (call range : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    attempt space dispatch call range bindings fuel live = none ↔
      rawQueryResults space call (callReturnType range) bindings (fuel + 1) live = [] := by
  dsimp only [attempt]
  split <;> simp_all

theorem attempt_of_matched {space : Space} {dispatch : GroundedDispatch} {call range : Atom}
    {bindings : Bindings} {fuel : Nat} {live : List Atom}
    (matched : rawQueryResults space call (callReturnType range) bindings (fuel + 1) live ≠ []) :
    attempt space dispatch call range bindings fuel live =
      some (finish space dispatch call range fuel live
        (rawQueryResults space call (callReturnType range) bindings (fuel + 1) live)) := by
  simp [attempt, List.isEmpty_eq_false_iff.mpr matched]

/-- An unmatched, already checked HE call has one canonical stuck answer. -/
theorem unmatched_call {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom}
    (unmatched : rawQueryResults space (.expression (.symbol head :: args)) (callReturnType range)
      bindings (fuel + 1) live = []) :
    evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 4) live = [(.expression (.symbol head :: args), bindings)] := by
  have invocation := invoke_refused notExecutable notInstruction
    (HEReturns.isErrorAtom_call notError args) unmatched none
  rw [HEReturns.evalAtom_expression (HEReturns.isEmptyOrError_call notError args)
    notAtom notExpression,
    interpretExpression_typed (copies := 0) declared ground notEmpty checked returns
      bindings enough arguments invocation]
  simp only [List.replicate_succ, List.replicate_zero, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  apply HEReturns.keep_clean
  intro result member
  simp only [List.mem_singleton] at member
  subst member
  exact HEReturns.isErrorAtom_call notError args

/-- Successful matched-only execution plus canonical decline is the actual
HE typed call. No equation-body semantic equality is assumed. -/
theorem attempt_canonical {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (returns : accepts expected range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom}
    (plain : ∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args))
        (callReturnType range) bindings (fuel + 1) live,
      ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    (attempt space dispatch (.expression (.symbol head :: args)) range bindings fuel live).getD
      (evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings
        (fuel + 4) live) =
      evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings
        (fuel + 4) live := by
  by_cases unmatched : rawQueryResults space (.expression (.symbol head :: args))
      (callReturnType range) bindings (fuel + 1) live = []
  · simp [attempt, unmatched]
  · rw [attempt_of_matched unmatched, Option.getD_some]
    exact (HEReturns.typed_call_once declared ground notEmpty notError notExecutable
      notInstruction checked returns notAtom notExpression bindings enough arguments
      rfl unmatched plain).symm

theorem mem_keep {results : ResultSet} {result : ResultPair}
    (member : result ∈ HEReturns.keep results) : result ∈ results := by
  unfold HEReturns.keep at member
  split at member <;> exact List.mem_of_mem_filter member

/-- Successful regions inherit their return assertion solely from the
matched equation-return paths. There is no unmatched-call obligation here. -/
theorem successful_return_property {space : Space} {dispatch : GroundedDispatch}
    {call range : Atom} {bindings : Bindings} {fuel : Nat} {live : List Atom}
    {results : ResultSet} {property : ResultPair → Prop}
    (accepted : attempt space dispatch call range bindings fuel live = some results)
    (equations : ∀ reply ∈ rawQueryResults space call (callReturnType range)
        bindings (fuel + 1) live,
      ∀ result ∈ ordinaryCallReturn call reply.1 reply.2
          (fun value record => evalAtom space dispatch value (callReturnType range)
            record (fuel + 1) live), property result) :
    ∀ result ∈ results, property result := by
  dsimp only [attempt] at accepted
  split at accepted
  · simp at accepted
  · cases Option.some.inj accepted
    intro result member
    obtain ⟨reply, occurs, produced⟩ := List.mem_flatMap.mp (mem_keep member)
    exact equations reply occurs result produced

namespace Controls

open Mettapedia.Languages.MeTTa.HE.CompletedDelivery.Controls

theorem unmatched_is_decline :
    attempt natSpace GroundedDispatch.none (succ zero) nat Bindings.empty 12 [] = none := by decide

theorem unmatched_is_not_no_answers :
    evalAtom natSpace GroundedDispatch.none (succ zero) Atom.undefinedType
      Bindings.empty 16 [] = [(succ zero, Bindings.empty)] := by decide

theorem erasing_decline_loses_answer :
    (attempt natSpace GroundedDispatch.none (succ zero) nat Bindings.empty 12 []).getD [] ≠
      evalAtom natSpace GroundedDispatch.none (succ zero) Atom.undefinedType
        Bindings.empty 16 [] := by decide

theorem matched_equation_is_accepted :
    attempt rewrittenSpace GroundedDispatch.none (succ zero) nat Bindings.empty 12 [] =
      some [(zero, Bindings.empty)] := by decide

/-- This finite minimal instruction has no result in the executable HE slice.
Its containing equation still matched; it is not an unmatched call. -/
def emptyBodySpace : Space := natSpace.add
  (equation (succ zero) (.expression [.symbol "superpose-bind", .expression []]))

theorem matched_empty_is_accepted :
    attempt emptyBodySpace GroundedDispatch.none (succ zero) nat Bindings.empty 12 [] =
      some [] := by decide

theorem matched_empty_source :
    evalAtom emptyBodySpace GroundedDispatch.none (succ zero) Atom.undefinedType
      Bindings.empty 16 [] = [] := by decide

/-- Refusal emitted by a matched equation is a return-boundary event: its
symbol spelling alone does not imply scalar output. -/
def refusedBodySpace : Space := natSpace.add (equation (succ zero) Atom.notReducible)

theorem matched_refusal_restores_call :
    attempt refusedBodySpace GroundedDispatch.none (succ zero) nat Bindings.empty 12 [] =
      some [(succ zero, Bindings.empty)] := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPreparedReturn
