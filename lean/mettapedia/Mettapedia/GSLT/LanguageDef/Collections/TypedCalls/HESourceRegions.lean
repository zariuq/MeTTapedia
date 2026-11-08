import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralIf
import Mettapedia.Languages.MeTTa.HE.FirstSuccessPreparedArguments

/-!
# Constructed mixed execution of typed HE source regions

Source recognition produces a small return plan, not another source language.
Plans contain the actual HE source image, reached equation occurrences and
binding records. Their execution uses the ordinary return protocol and batch
selection; reached right sides may themselves be specialized regions.

Every accepted plan carries a proof constructed from the interpreter's
typing, operand-delivery and query lemmas. Unsupported nodes retain canonical
execution. A separately checked return mode distinguishes values carrying a
range certificate from canonical answers that may not satisfy that range.
The canonical mode reuses the computed answers and does not replay effects.

The present source recognizer admits leaf values, closed typed heads whose
operands are leaves, and literal-Boolean conditionals at closed expected
types. Open typed calls remain canonical: written-range equality is not a
substitution-transport certificate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESourceRegions

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HEReturns

structure Request where
  source : Atom
  expected : Atom
  bindings : Bindings
  fuel : Nat
  live : List Atom

abbrev Evaluator := Request → ResultSet

def canonical (space : Space) (dispatch : GroundedDispatch) : Evaluator := fun request =>
  evalAtom space dispatch request.source request.expected request.bindings request.fuel request.live

/-- An independently executed result plan: direct delivery or ordinary
completion of reached equation replies through an evaluator service. -/
inductive Plan where
  | direct (answers : ResultSet)
  | returns (original expected : Atom) (replies : ResultSet) (fuel : Nat) (live : List Atom)

def Plan.execute (evaluate : Evaluator) : Plan → ResultSet
  | .direct answers => answers
  | .returns original expected replies fuel live =>
      keep (replies.flatMap fun reply => ordinaryCallReturn original reply.1 reply.2
        fun value record => evaluate ⟨value, expected, record, fuel, live⟩)

theorem Plan.execute_congr {first second : Evaluator}
    (same : ∀ request, first request = second request) (plan : Plan) :
    plan.execute first = plan.execute second := by
  have equal : first = second := funext same
  rw [equal]

structure Compiled (space : Space) (dispatch : GroundedDispatch) (request : Request) where
  plan : Plan
  sound : plan.execute (canonical space dispatch) = canonical space dispatch request

private def plainReply : Atom → Bool
  | .expression [.symbol "function", _] => false
  | _ => true

private theorem plainReplies {replies : ResultSet}
    (plain : replies.all (fun reply => plainReply reply.1) = true) :
    ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body] := by
  intro reply member body equal
  have := List.all_eq_true.mp plain reply member
  simp [equal, plainReply] at this

private theorem leafFields {space : Space} : ∀ params args,
    HEConstructorAdmission.checkFields space (fun _ => none) params args = true →
      List.Forall₂ (fun param arg => isLeaf arg = true ∧ ArgumentChecked space param arg) params args
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [HEConstructorAdmission.checkFields] at h
  | _ :: _, [], h => by simp [HEConstructorAdmission.checkFields] at h
  | param :: params, arg :: args, h => by
      simp only [HEConstructorAdmission.checkFields, Bool.or_false, Bool.and_eq_true] at h
      exact .cons ⟨h.1.2, HEConstructorAdmission.checkOnce_sound h.1.1⟩
        (leafFields params args h.2)

private def callGuard (space : Space) (dispatch : GroundedDispatch) (head : String)
    (params args : List Atom) (range expected : Atom) (bindings : Bindings) (fuel : Nat) : Prop :=
  getAtomTypes space (.symbol head) = [arrowType params range] ∧
  atomVariables (arrowType params range) = [] ∧ head ≠ "Empty" ∧ head ≠ "Error" ∧
  dispatch.isExecutable (.symbol head) = false ∧
  minimalInstruction (.expression (.symbol head :: args)) = false ∧
  expected ≠ Atom.atomType ∧ expected ≠ Atom.expressionType ∧
  HEConstructorAdmission.checkFields space (fun _ => none) params args = true ∧
  matchFuel (arrowType params range) + params.length + 1 ≤ fuel ∧
  checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
    (arrowType params range) expected space bindings (fuel + 2) = .inr [bindings]

private instance (space : Space) (dispatch : GroundedDispatch) (head : String)
    (params args : List Atom) (range expected : Atom) (bindings : Bindings) (fuel : Nat) :
    Decidable (callGuard space dispatch head params args range expected bindings fuel) := by
  unfold callGuard
  infer_instance

/-- The source guard derives operand interpretation from checked leaf syntax;
the remaining source operation is query plus ordinary return. -/
private theorem guardedCall {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected : Atom} {bindings : Bindings} {fuel : Nat}
    {live : List Atom}
    (guard : callGuard space dispatch head params args range expected bindings fuel)
    (plain : (rawQueryResults space (.expression (.symbol head :: args))
      (callReturnType range) bindings (fuel + 1) live).all (fun reply => plainReply reply.1) = true) :
    let source := Atom.expression (.symbol head :: args)
    let replies := rawQueryResults space source (callReturnType range) bindings (fuel + 1) live
    (if replies = [] then Plan.direct [(source, bindings)]
     else Plan.returns source (callReturnType range) replies (fuel + 1) live).execute
       (canonical space dispatch) =
      evalAtom space dispatch source expected bindings (fuel + 4) live := by
  obtain ⟨declared, ground, notEmpty, notError, notExecutable, notInstruction,
    notAtom, notExpression, checked, budget, applicable⟩ := guard
  have grounded := (arrowType_ground ground).1
  have values := leafFields params args checked
  have strengthened := (List.forall₂_and_left params args).mpr ⟨grounded, values⟩
  have arguments : ∀ retained, interpretArgs space dispatch args params bindings (fuel + 1) retained =
      [(argumentPacket args, bindings)] := by
    intro retained
    apply interpretArgs_leaves (strengthened.imp (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩))
      bindings _ (by omega) retained
    intro param member
    have small := matchFuel_param_lt (range := range) member
    omega
  have interpreted : ∀ retained, interpretFunction space dispatch
      (.expression (.symbol head :: args)) (arrowType params range) bindings
      (fuel + 2) retained = [(.expression (.symbol head :: args), bindings)] :=
    fun retained => interpretFunction_completed declared ground notEmpty bindings (by omega)
      arguments retained
  dsimp only
  split
  · rename_i unmatched
    have invoked := invoke_refused notExecutable notInstruction (isErrorAtom_call notError args)
      unmatched none
    rw [evalAtom_expression (isEmptyOrError_call notError args) notAtom notExpression,
      interpretExpression_single declared applicable interpreted invoked]
    symm
    apply keep_clean
    intro result member
    simp only [List.mem_singleton] at member
    subst result
    exact isErrorAtom_call notError args
  · rename_i matched
    have invoked := invoke_queried notExecutable notInstruction (isErrorAtom_call notError args)
      rfl matched (plainReplies plain) none
    rw [evalAtom_expression (isEmptyOrError_call notError args) notAtom notExpression,
      interpretExpression_single declared applicable interpreted invoked]
    rfl

def compileCall (space : Space) (dispatch : GroundedDispatch) (head : String)
    (params args : List Atom) (range expected : Atom) (bindings : Bindings) (fuel : Nat)
    (live : List Atom) : Option (Compiled space dispatch
      ⟨.expression (.symbol head :: args), expected, bindings, fuel + 4, live⟩) :=
  if guard : callGuard space dispatch head params args range expected bindings fuel then
    let source := Atom.expression (.symbol head :: args)
    let replies := rawQueryResults space source (callReturnType range) bindings (fuel + 1) live
    if plain : replies.all (fun reply => plainReply reply.1) = true then
      some ⟨if replies = [] then .direct [(source, bindings)]
            else .returns source (callReturnType range) replies (fuel + 1) live,
        guardedCall guard plain⟩
    else none
  else none

private def ifGuard (space : Space) (dispatch : GroundedDispatch) (name : String) (truth : Bool)
    (chosen other expected : Atom) (bindings : Bindings) (fuel : Nat) : Prop :=
  getAtomTypes space (.symbol "if") = [ifArrow name] ∧
  dispatch.isExecutable (.symbol "if") = false ∧
  minimalInstruction (.expression [.symbol "if", .grounded (.bool truth), chosen, other]) = false ∧
  atomVariables expected = [] ∧ expected ≠ Atom.undefinedType ∧ expected ≠ Atom.atomType ∧
  expected ≠ Atom.expressionType ∧
  HEConstructorAdmission.checkOnce space Atom.atomType chosen = true ∧
  HEConstructorAdmission.checkOnce space Atom.atomType other = true ∧
  bindings.lookup name = none ∧ bindings.equalities = [] ∧ 9 ≤ fuel

private instance (space : Space) (dispatch : GroundedDispatch) (name : String) (truth : Bool)
    (chosen other expected : Atom) (bindings : Bindings) (fuel : Nat) :
    Decidable (ifGuard space dispatch name truth chosen other expected bindings fuel) := by
  unfold ifGuard
  infer_instance

def compileIf (space : Space) (dispatch : GroundedDispatch) (name : String) (truth : Bool)
    (chosen other expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    Option (Compiled space dispatch
      ⟨.expression [.symbol "if", .grounded (.bool truth), chosen, other], expected,
        bindings, fuel + 4, live⟩) :=
  if guard : ifGuard space dispatch name truth chosen other expected bindings fuel then
    let source := Atom.expression [.symbol "if", .grounded (.bool truth), chosen, other]
    let replies := rawQueryResults space source (.var name) (ifRecord bindings name expected)
      (fuel + 1) live
    if nonempty : replies ≠ [] then
      if plain : replies.all (fun reply => plainReply reply.1) = true then
        some ⟨.returns source (.var name) replies (fuel + 1) live, by
          obtain ⟨declared, notExecutable, notInstruction, ground, notUndefined, notAtom,
            notExpression, chosenChecked, otherChecked, unbound, noEqualities, enough⟩ := guard
          exact (HEStructuralIf.if_bool_closed truth declared notExecutable notInstruction
            ground notUndefined notAtom notExpression chosenChecked otherChecked unbound
            noEqualities enough rfl nonempty (plainReplies plain)).symm⟩
      else none
    else none
  else none

def compileValue (space : Space) (dispatch : GroundedDispatch) (source expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    Option (Compiled space dispatch ⟨source, expected, bindings, fuel + 1, live⟩) :=
  if guard : isLeaf source = true ∧ atomVariables source = [] ∧ atomVariables expected = [] ∧
      HEConstructorAdmission.checkOnce space expected source = true ∧ matchFuel expected ≤ fuel then
    some ⟨.direct [(source, bindings)], by
      exact (evalAtom_leaf guard.1 guard.2.2.1
        (HEConstructorAdmission.checkOnce_sound guard.2.2.2.1)
        bindings guard.2.2.2.2 live).symm⟩
  else none

/-- Source syntax selects a separately proved plan. Type rows are checked
again by the boundary guard, so decoding is not a semantic assumption. -/
def compile (space : Space) (dispatch : GroundedDispatch) (request : Request) :
    Option (Compiled space dispatch request) :=
  match request with
  | ⟨source, expected, bindings, fuel + 1, live⟩ =>
      match compileValue space dispatch source expected bindings fuel live with
      | some ready => some ready
      | none =>
          match source, fuel with
          | .expression [.symbol "if", .grounded (.bool truth), chosen, other], fuel + 3 =>
              match getAtomTypes space (.symbol "if") with
              | [.expression [.symbol "->", .symbol "Bool", .symbol "Atom", .symbol "Atom", .var name]] =>
                  compileIf space dispatch name truth chosen other expected bindings fuel live
              | _ => none
          | .expression (.symbol head :: args), fuel + 3 =>
              match getAtomTypes space (.symbol head) with
              | [type] =>
                  match getFunctionArgTypes type, getFunctionRetType type with
                  | some params, some range =>
                      compileCall space dispatch head params args range expected bindings fuel live
                  | _, _ => none
              | _ => none
          | _, _ => none
  | _ => none

/-- Specialize as many reached source boundaries as the depth permits;
every unrecognized boundary keeps the existing canonical evaluator. -/
def run (space : Space) (dispatch : GroundedDispatch) : Nat → Evaluator
  | 0 => canonical space dispatch
  | depth + 1 => fun request =>
      match compile space dispatch request with
      | none => canonical space dispatch request
      | some region => region.plan.execute (run space dispatch depth)

theorem run_eq_canonical (space : Space) (dispatch : GroundedDispatch) :
    ∀ depth request, run space dispatch depth request = canonical space dispatch request := by
  intro depth
  induction depth with
  | zero => intro request; rfl
  | succ depth ih =>
      intro request
      unfold run
      split
      · rfl
      · rename_i region found
        rw [Plan.execute_congr ih]
        exact region.sound

/-- Canonical completion does not promise the prepared region's postcondition. -/
inductive Completion where
  | prepared (answers : ResultSet)
  | canonical (answers : ResultSet)
  deriving DecidableEq

def Completion.answers : Completion → ResultSet
  | .prepared answers | .canonical answers => answers

/-- A failed postcondition returns the already computed answers in canonical
mode. It does not restart source execution or silently re-enter prepared code. -/
def checkedRun (space : Space) (dispatch : GroundedDispatch) (depth valueDepth : Nat)
    (range : Atom) (request : Request) : Completion :=
  let answers := run space dispatch depth request
  if atomVariables range == [] && range != Atom.expressionType &&
      answers.all (fun answer => HEStructuralBoundary.checkShown space dispatch valueDepth range answer.1)
  then .prepared answers else .canonical answers

theorem checkedRun_observes (space : Space) (dispatch : GroundedDispatch) (depth valueDepth : Nat)
    (range : Atom) (request : Request) :
    (checkedRun space dispatch depth valueDepth range request).answers =
      canonical space dispatch request := by
  dsimp only [checkedRun]
  split <;> exact run_eq_canonical space dispatch depth request

theorem checkedRun_prepared {space : Space} {dispatch : GroundedDispatch} {depth valueDepth : Nat}
    {range : Atom} {request : Request} {answers : ResultSet}
    (accepted : checkedRun space dispatch depth valueDepth range request = .prepared answers) :
    ∀ answer ∈ answers, HEStructuralBoundary.checkShown space dispatch valueDepth range answer.1 = true := by
  dsimp only [checkedRun] at accepted
  split at accepted
  · rename_i checked
    cases Completion.prepared.inj accepted
    simp only [Bool.and_eq_true] at checked
    exact List.all_eq_true.mp checked.2
  · cases accepted

/-- A prepared completion carries a genuine range-elision certificate. Its
ground range and non-Expression protocol are checked, not left implicit in
the mode tag. -/
theorem checkedRun_range_certificate {space : Space} {dispatch : GroundedDispatch}
    {depth valueDepth : Nat} {range : Atom} {request : Request} {answers : ResultSet}
    (accepted : checkedRun space dispatch depth valueDepth range request = .prepared answers) :
    atomVariables range = [] ∧ range ≠ Atom.expressionType ∧
      ∃ bound, ∀ extra original live,
        HEPreparedReturn.finish space dispatch original range (bound + extra) live answers = answers := by
  have each := checkedRun_prepared accepted
  dsimp only [checkedRun] at accepted
  split at accepted
  · rename_i checked
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at checked
    exact ⟨checked.1.1, checked.1.2,
      HEStructuralBoundary.shown_batch_elision checked.1.1 checked.1.2 answers each⟩
  · cases accepted

/-- Parameters enter through the maintained source-substitution boundary.
The saved source is instantiated before region recognition, as an equation
reply is instantiated before HE evaluates it. -/
def instantiateRequest (substitution : Spec.Type.Presentation.TypeSubst)
    (source expected : Atom) (fuel : Nat) (live : List Atom) : Request :=
  ⟨substitution.apply source, expected,
    FirstSuccessPreparedArguments.presentedBindings substitution, fuel, live⟩

theorem instantiated_source_agrees (space : Space) (dispatch : GroundedDispatch)
    {substitution : Spec.Type.Presentation.TypeSubst}
    (normal : substitution.Normal) (source expected : Atom) (sourceFuel fuel depth : Nat)
    (live : List Atom)
    (enough : BindingComposition.atomDepth source + 2 ≤ sourceFuel) :
    run space dispatch depth (instantiateRequest substitution source expected fuel live) =
      evalAtom space dispatch
        ((FirstSuccessPreparedArguments.presentedBindings substitution).applyFull source sourceFuel)
        expected (FirstSuccessPreparedArguments.presentedBindings substitution) fuel live := by
  rw [run_eq_canonical, FirstSuccessPreparedArguments.applyFull_presented normal sourceFuel source enough]
  rfl

namespace Controls

open Mettapedia.Languages.MeTTa.HE.CompletedDelivery.Controls

def constructorRequest : Request :=
  ⟨succ zero, nat, Bindings.empty, 32, []⟩

theorem constructor_source_compiles :
    (compile natSpace GroundedDispatch.none constructorRequest).isSome = true := by decide

theorem constructor_source_answer :
    run natSpace GroundedDispatch.none 3 constructorRequest = [(succ zero, Bindings.empty)] := by
  rw [run_eq_canonical]
  decide

def symbolRequest : Request :=
  ⟨HEStructuralIf.Controls.numbers, HEStructuralIf.Controls.listNumbers,
    Bindings.empty, 48, []⟩

theorem symbol_source_compiles :
    (compile HEStructuralIf.Controls.space GroundedDispatch.none symbolRequest).isSome = true := by decide

def tailSpace : Space := Space.ofList
  [declaration zero nat,
   declaration (.symbol "outer") (arrowType [nat] nat),
   declaration (.symbol "inner") (arrowType [nat] nat),
   equation (.expression [.symbol "outer", .var "x"])
     (.expression [.symbol "inner", .var "x"]),
   equation (.expression [.symbol "inner", .var "x"]) (.var "x")]

def tailRequest : Request :=
  ⟨.expression [.symbol "outer", zero], nat, Bindings.empty, 48, []⟩

theorem closed_tail_source_compiles :
    (compile tailSpace GroundedDispatch.none tailRequest).isSome = true := by decide

theorem closed_tail_source_returns :
    (run tailSpace GroundedDispatch.none 3 tailRequest).map Prod.fst = [zero] := by
  rw [run_eq_canonical]
  decide

def refusedSpace : Space := Space.ofList
  [declaration (.symbol "refused") (arrowType [] nat),
   equation (.expression [.symbol "refused"]) Atom.notReducible]

def refusalRequest : Request :=
  ⟨.expression [.symbol "refused"], nat, Bindings.empty, 32, []⟩

theorem refusal_keeps_original_call :
    (run refusedSpace GroundedDispatch.none 3 refusalRequest).map Prod.fst =
      [.expression [.symbol "refused"]] := by
  rw [run_eq_canonical]
  decide

theorem refusal_cannot_claim_prepared_range :
    ∃ answers, checkedRun refusedSpace GroundedDispatch.none 3 2 nat refusalRequest =
      .canonical answers := by
  unfold checkedRun
  rw [run_eq_canonical]
  exact ⟨canonical refusedSpace GroundedDispatch.none refusalRequest, by decide⟩

def branchRequest (truth : Bool) : Request :=
  ⟨HEStructuralIf.Controls.conditional truth, HEStructuralIf.Controls.listNumbers,
    Bindings.empty, 48, []⟩

theorem both_conditional_sources_compile :
    (compile HEStructuralIf.Controls.space GroundedDispatch.none (branchRequest true)).isSome = true ∧
    (compile HEStructuralIf.Controls.space GroundedDispatch.none (branchRequest false)).isSome = true := by
  constructor <;> decide

theorem conditional_source_keeps_recorded_type :
    (run HEStructuralIf.Controls.space GroundedDispatch.none 4 (branchRequest true)).map Prod.fst =
      [HEStructuralIf.Controls.numbers] := by
  rw [run_eq_canonical]
  exact HEStructuralIf.Controls.same_frame_branch_keeps_type

/-- A canonical error is not silently tagged as a prepared range value. -/
theorem rejected_branch_stays_canonical :
    ∃ answers, checkedRun HEStructuralIf.Controls.space GroundedDispatch.none 4 2
      HEStructuralIf.Controls.listNumbers (branchRequest false) = .canonical answers ∧
      (answers.map Prod.fst).all isErrorAtom = true := by
  unfold checkedRun
  rw [run_eq_canonical]
  exact ⟨_, by decide, HEStructuralIf.Controls.incompatible_branch_is_error⟩

def parameterRequest : Request :=
  instantiateRequest [("slot", zero)] (.var "slot") nat 32 []

theorem instantiated_parameter_compiles :
    (compile natSpace GroundedDispatch.none parameterRequest).isSome = true := by
  have applied : Spec.Type.Presentation.TypeSubst.apply [("slot", zero)] (.var "slot") = zero := by
    rw [Spec.Type.Presentation.TypeSubst.apply.eq_2]
    rfl
  have request_eq : parameterRequest =
      ⟨zero, nat, FirstSuccessPreparedArguments.presentedBindings [("slot", zero)], 32, []⟩ := by
    unfold parameterRequest instantiateRequest
    rw [applied]
  rw [request_eq]
  decide

theorem raw_open_parameter_declines :
    (compile natSpace GroundedDispatch.none ⟨.var "slot", nat, Bindings.empty, 32, []⟩).isSome =
      false := by decide

theorem insufficient_source_fuel_declines :
    (compile natSpace GroundedDispatch.none ⟨succ zero, nat, Bindings.empty, 2, []⟩).isSome = false := by
  decide

theorem held_call_stays_canonical_data :
    (compile tailSpace GroundedDispatch.none
      ⟨tailRequest.source, Atom.atomType, Bindings.empty, 48, []⟩).isSome = false ∧
    run tailSpace GroundedDispatch.none 3
      ⟨tailRequest.source, Atom.atomType, Bindings.empty, 48, []⟩ =
        [(tailRequest.source, Bindings.empty)] := by
  constructor
  · decide
  · rw [run_eq_canonical]
    decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESourceRegions
