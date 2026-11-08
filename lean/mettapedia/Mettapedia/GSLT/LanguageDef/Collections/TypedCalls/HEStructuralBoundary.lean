import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPreparedReturn

/-!
# Closed structural argument boundaries for HE calls

Recursive constructor admission supplies both parts of an HE call boundary:
the argument check succeeds exactly once, and evaluation under that formal
returns the argument itself. The latter is derived uniformly above one fuel
threshold, for every incoming binding record and retained-root list.

The resulting typed-call expansion is over the actual HE interpreter. It
retains the singleton stuck-call branch when no equation matches and the
ordered, multiplicity-exact range completion of matched replies otherwise.
No operand evaluation equality is assumed by the call theorem.

This slice uses closed declarations and single applicability. Open formals,
first-success selection and C memory/layout correspondence remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem arguments_checked {space : Space} {dispatch : GroundedDispatch}
    {params args : List Atom} (values : CompletedArguments space dispatch params args) :
    List.Forall₂ (ArgumentChecked space) params args := by
  induction params generalizing args with
  | nil => cases values; exact .nil
  | cons param params ih =>
      cases values with
      | held checked rest => exact .cons checked (ih rest)
      | leaf _ checked rest => exact .cons checked (ih rest)
      | value _ _ checked rest => exact .cons checked (ih rest)

/-- One fuel threshold works for all records and retained roots. The child
constructor theorem supplies thresholds for nested completed values. -/
theorem arguments_deliver {space : Space} {dispatch : GroundedDispatch}
    {params args : List Atom} (values : CompletedArguments space dispatch params args)
    (ground : ∀ param ∈ params, atomVariables param = []) :
    ∃ bound, ∀ extra bindings live,
      interpretArgs space dispatch args params bindings (bound + extra) live =
        [(argumentPacket args, bindings)] := by
  induction params generalizing args with
  | nil =>
      cases values
      refine ⟨1, fun extra bindings live => ?_⟩
      rw [show 1 + extra = extra + 1 by omega]
      exact interpretArgs_nil_self bindings extra live
  | cons param params ih =>
      cases values with
      | held checked rest =>
          obtain ⟨bound, tail⟩ := ih rest fun other member => ground other (by simp [member])
          refine ⟨bound + 2, fun extra bindings live => ?_⟩
          rw [show bound + 2 + extra = bound + 1 + extra + 1 by omega]
          refine interpretArgs_cons_self (fun kept => ?_) (fun kept => ?_) live
          · rw [show bound + 1 + extra = bound + extra + 1 by omega]
            exact evalAtom_held _ bindings _ kept
          · rw [show bound + 1 + extra = bound + (1 + extra) by omega]
            exact tail _ bindings kept
      | leaf leaf checked rest =>
          obtain ⟨bound, tail⟩ := ih rest fun other member => ground other (by simp [member])
          refine ⟨bound + matchFuel param + 2, fun extra bindings live => ?_⟩
          rw [show bound + matchFuel param + 2 + extra =
            bound + matchFuel param + 1 + extra + 1 by omega]
          refine interpretArgs_cons_self (fun kept => ?_) (fun kept => ?_) live
          · rw [show bound + matchFuel param + 1 + extra =
              bound + matchFuel param + extra + 1 by omega]
            exact evalAtom_leaf leaf (ground param (by simp)) checked bindings (by omega) kept
          · rw [show bound + matchFuel param + 1 + extra =
              bound + (matchFuel param + 1 + extra) by omega]
            exact tail _ bindings kept
      | value completed fits checked rest =>
          rename_i arg range args
          obtain ⟨bound, tail⟩ := ih rest fun other member => ground other (by simp [member])
          obtain ⟨childBound, child⟩ := evalAtom_completed_accepted completed
          have accepted : accepts param range = true := by
            rcases fits with rfl | rfl
            · exact accepts_undefined _
            · exact accepts_self _
          refine ⟨bound + childBound + 1, fun extra bindings live => ?_⟩
          rw [show bound + childBound + 1 + extra = bound + childBound + extra + 1 by omega]
          refine interpretArgs_cons_self (fun kept => ?_) (fun kept => ?_) live
          · rw [show bound + childBound + extra = childBound + (bound + extra) by omega]
            exact child _ param bindings kept accepted
          · rw [show bound + childBound + extra = bound + (childBound + extra) by omega]
            exact tail _ bindings kept

/-- The executable field checker discharges the canonical boundary facts. -/
theorem checkedFields_boundary {space : Space} {dispatch : GroundedDispatch}
    {depth : Nat} {params args : List Atom}
    (admitted : HEConstructorAdmission.checkFields space
      (HEConstructorAdmission.check space dispatch depth) params args = true)
    (ground : ∀ param ∈ params, atomVariables param = []) :
    List.Forall₂ (ArgumentChecked space) params args ∧
      ∃ bound, ∀ extra bindings live,
        interpretArgs space dispatch args params bindings (bound + extra) live =
          [(argumentPacket args, bindings)] := by
  have values := HEConstructorAdmission.checkFields_sound
    (HEConstructorAdmission.check_sound space dispatch depth) params args admitted
  exact ⟨arguments_checked values, arguments_deliver values ground⟩

/-- Closed structural arguments checked by the executable admission procedure
give the complete typed-call expansion: stuck on no match, range completion
on actual equation replies. The threshold is independent of expected type,
bindings and retained roots. -/
theorem checkedCall_expansion {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range : Atom} {depth : Nat}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (admitted : HEConstructorAdmission.checkFields space
      (HEConstructorAdmission.check space dispatch depth) params args = true) :
    ∃ threshold, ∀ extra expected bindings live,
      accepts expected range = true → expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
      (∀ reply ∈ rawQueryResults space (.expression (.symbol head :: args)) (callReturnType range)
        bindings (threshold + extra + 1) live,
        ∀ body, reply.1 ≠ .expression [.symbol "function", body]) →
      let replies := rawQueryResults space (.expression (.symbol head :: args))
        (callReturnType range) bindings (threshold + extra + 1) live
      evalAtom space dispatch (.expression (.symbol head :: args)) expected bindings
        (threshold + extra + 4) live =
          if replies = [] then [(.expression (.symbol head :: args), bindings)]
          else HEPreparedReturn.finish space dispatch (.expression (.symbol head :: args))
            range (threshold + extra) live replies := by
  obtain ⟨checked, bound, deliver⟩ := checkedFields_boundary admitted (arrowType_ground ground).1
  refine ⟨matchFuel (arrowType params range) + bound,
    fun extra expected bindings live returns notAtom notExpression plain => ?_⟩
  dsimp only
  have enough : matchFuel (arrowType params range) ≤
      matchFuel (arrowType params range) + bound + extra := by omega
  have arguments : ∀ kept, interpretArgs space dispatch args params bindings
      (matchFuel (arrowType params range) + bound + extra + 1) kept =
        [(argumentPacket args, bindings)] := by
    intro kept
    rw [show matchFuel (arrowType params range) + bound + extra + 1 =
      bound + (matchFuel (arrowType params range) + extra + 1) by omega]
    exact deliver _ bindings kept
  split
  · rename_i unmatched
    exact HEPreparedReturn.unmatched_call declared ground notEmpty notError notExecutable
      notInstruction checked returns notAtom notExpression bindings enough arguments unmatched
  · rename_i matched
    exact HEReturns.typed_call_once declared ground notEmpty notError notExecutable
      notInstruction checked returns notAtom notExpression bindings enough arguments
      rfl matched plain

/-- A shown return value is checked from syntax and type lookup. Refusal and
stopped/error markers are excluded because the ordinary return protocol
treats them specially. This is a value certificate, not a source-body analysis. -/
def checkShown (space : Space) (dispatch : GroundedDispatch) (depth : Nat)
    (range value : Atom) : Bool :=
  !(isEmptyOrError value) && value != Atom.notReducible &&
    (if isLeaf value then HEConstructorAdmission.checkOnce space range value
     else match HEConstructorAdmission.check space dispatch depth value with
       | some found => found == range
       | none => false)

theorem checkShown_delivers {space : Space} {dispatch : GroundedDispatch} {depth : Nat}
    {range value : Atom} (ground : atomVariables range = [])
    (shown : checkShown space dispatch depth range value = true) :
    isEmptyOrError value = false ∧ value ≠ Atom.notReducible ∧
      ∃ bound, ∀ extra bindings live,
        evalAtom space dispatch value range bindings (bound + extra) live = [(value, bindings)] := by
  simp only [checkShown, Bool.and_eq_true, bne_iff_ne] at shown
  obtain ⟨⟨clean, notRefused⟩, form⟩ := shown
  refine ⟨by simpa using clean, notRefused, ?_⟩
  split at form
  · rename_i leaf
    have checked := HEConstructorAdmission.checkOnce_sound form
    refine ⟨matchFuel range + 1, fun extra bindings live => ?_⟩
    rw [show matchFuel range + 1 + extra = matchFuel range + extra + 1 by omega]
    exact evalAtom_leaf leaf ground checked bindings (by omega) live
  · split at form
    · rename_i found accepted
      have same : found = range := by simpa using form
      subst found
      obtain ⟨bound, deliver⟩ := HEConstructorAdmission.checkedBuild_delivers accepted
      exact ⟨bound, fun extra bindings live => deliver extra range bindings live (accepts_self _)⟩
    · simp at form

/-- A syntactically certified return needs no second evaluation at its closed
non-Expression range. The caller/source atom and record are retained exactly. -/
theorem shown_return_elision {space : Space} {dispatch : GroundedDispatch} {depth : Nat}
    {range value : Atom} (ground : atomVariables range = [])
    (notExpression : range ≠ Atom.expressionType)
    (shown : checkShown space dispatch depth range value = true) :
    ∃ bound, ∀ extra original bindings live,
      ordinaryCallReturn original value bindings
        (fun value record => evalAtom space dispatch value (callReturnType range) record
          (bound + extra) live) = [(value, bindings)] := by
  obtain ⟨clean, notRefused, bound, deliver⟩ := checkShown_delivers ground shown
  refine ⟨bound, fun extra original bindings live => ?_⟩
  rw [ordinaryCallReturn_evaluate _ _ _ _ notRefused clean]
  have rangeType : callReturnType range = range := by simp [callReturnType, notExpression]
  rw [rangeType]
  exact deliver extra bindings live

/-- The shared threshold for a finite batch is independent of its caller and
retained roots. Duplicate replies are retained, not collapsed into a set. -/
theorem shown_batch_elision {space : Space} {dispatch : GroundedDispatch} {depth : Nat}
    {range : Atom} (ground : atomVariables range = [])
    (notExpression : range ≠ Atom.expressionType) (replies : ResultSet)
    (shown : ∀ reply ∈ replies, checkShown space dispatch depth range reply.1 = true) :
    ∃ bound, ∀ extra original live,
      HEPreparedReturn.finish space dispatch original range (bound + extra) live replies = replies := by
  have raw : ∃ bound, ∀ extra original live,
      replies.flatMap (fun reply => ordinaryCallReturn original reply.1 reply.2
        (fun value record => evalAtom space dispatch value (callReturnType range) record
          (bound + extra + 1) live)) = replies := by
    induction replies with
    | nil => exact ⟨0, by simp⟩
    | cons first rest ih =>
        obtain ⟨firstBound, firstReturn⟩ := shown_return_elision ground notExpression
          (shown first (by simp))
        obtain ⟨restBound, restReturn⟩ := ih (fun reply member => shown reply (by simp [member]))
        refine ⟨firstBound + restBound, fun extra original live => ?_⟩
        rw [List.flatMap_cons]
        have head := firstReturn (restBound + extra + 1) original first.2 live
        have tail := restReturn (firstBound + extra) original live
        rw [show firstBound + (restBound + extra + 1) =
          firstBound + restBound + extra + 1 by omega] at head
        rw [show restBound + (firstBound + extra) + 1 =
          firstBound + restBound + extra + 1 by omega] at tail
        rw [head, tail]
        rfl
  obtain ⟨bound, execute⟩ := raw
  refine ⟨bound, fun extra original live => ?_⟩
  unfold HEPreparedReturn.finish
  rw [execute]
  apply HEReturns.keep_clean
  intro reply member
  have clean := (checkShown_delivers ground (shown reply member)).1
  simp only [isEmptyOrError, Bool.or_eq_false_iff] at clean
  exact clean.2

namespace Controls

open Mettapedia.Languages.MeTTa.HE.CompletedDelivery.Controls

theorem nested_structural_fields_checked :
    HEConstructorAdmission.checkFields natSpace
      (HEConstructorAdmission.check natSpace GroundedDispatch.none 2)
      [nat] [succ (succ zero)] = true := by decide

theorem nested_arguments_deliver :
    ∃ bound, ∀ extra bindings live,
      interpretArgs natSpace GroundedDispatch.none [succ (succ zero)] [nat] bindings
        (bound + extra) live = [(argumentPacket [succ (succ zero)], bindings)] :=
  (checkedFields_boundary nested_structural_fields_checked (by simp [atomVariables])).2

theorem wrong_structural_field_declines :
    HEConstructorAdmission.checkFields natSpace
      (HEConstructorAdmission.check natSpace GroundedDispatch.none 2)
      [nat] [.grounded (.int 3)] = false := by decide

theorem repeated_typing_declines :
    HEConstructorAdmission.checkFields twiceZeroSpace
      (HEConstructorAdmission.check twiceZeroSpace GroundedDispatch.none 2)
      [nat] [zero] = false := by decide

theorem repeated_typing_is_observable :
    ∃ bound, ∀ extra live,
      evalAtom twiceZeroSpace GroundedDispatch.none (succ zero) Atom.undefinedType
        Bindings.empty (bound + extra) live =
          [(succ zero, Bindings.empty), (succ zero, Bindings.empty)] :=
  argumentChecked_once_required.2

def structuralFunctionSpace : Space :=
  (natSpace.add (declaration (.symbol "pass") (arrowType [nat] nat))).add
    (equation (.expression [.symbol "pass", succ zero]) (succ zero))

theorem structural_function_entry_checked :
    HEConstructorAdmission.checkFields structuralFunctionSpace
      (HEConstructorAdmission.check structuralFunctionSpace GroundedDispatch.none 1)
      [nat] [succ zero] = true := by decide

theorem structural_function_returns_constructor :
    evalAtom structuralFunctionSpace GroundedDispatch.none
      (.expression [.symbol "pass", succ zero]) Atom.undefinedType Bindings.empty 32 [] =
        [(succ zero, Bindings.empty)] := by decide

def duplicateBodySpace : Space := structuralFunctionSpace.add
  (equation (.expression [.symbol "pass", succ zero]) (succ zero))

theorem duplicate_equations_keep_multiplicity :
    evalAtom duplicateBodySpace GroundedDispatch.none
      (.expression [.symbol "pass", succ zero]) Atom.undefinedType Bindings.empty 32 [] =
        [(succ zero, Bindings.empty), (succ zero, Bindings.empty)] := by decide

theorem constructor_shows_range :
    checkShown natSpace GroundedDispatch.none 2 nat (succ (succ zero)) = true := by decide

theorem symbol_shows_range :
    checkShown natSpace GroundedDispatch.none 0 nat zero = true := by decide

theorem shown_duplicate_replies_preserved :
    ∃ bound, ∀ extra original live,
      HEPreparedReturn.finish natSpace GroundedDispatch.none original nat (bound + extra) live
        [(succ (succ zero), Bindings.empty), (succ (succ zero), Bindings.empty)] =
          [(succ (succ zero), Bindings.empty), (succ (succ zero), Bindings.empty)] := by
  apply shown_batch_elision rfl (by decide)
  intro reply member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst reply
  exact constructor_shows_range

def refusalTypedSpace : Space := natSpace.add (declaration Atom.notReducible nat)

/-- A typed scalar spelling can still be a refusal event at return. -/
theorem refusal_not_shown :
    HEConstructorAdmission.checkOnce refusalTypedSpace nat Atom.notReducible = true ∧
      checkShown refusalTypedSpace GroundedDispatch.none 0 nat Atom.notReducible = false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralBoundary
