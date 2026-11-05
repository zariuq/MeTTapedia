import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource

/-!
# Uniform admission of named guarded publication bodies

Captured payload readings and fresh destinations are transported through the
actual operand preparation, clause selection and Boolean-return equations.
No successful guard evaluation or store mutation is an admission premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor)
open NamedPresenceConditional (Input)
open NamedGuardedInsertionSource (Body Evidence afterGuard)

variable {Context : Type}

theorem after_guard_consistent {input : Input Context} (guard : NamedPresenceConditional.Evidence input) :
    ∃ environment, Solves environment (afterGuard guard).bindings :=
  ClosedOnceQueryFrame.refined_consistent _ _ _
    (NamedPresenceSource.returned_refined input.pending.length guard.selected input.waiting.goals
      input.slot input.request false ⟨guard.bodyPrincipal, resolve_sound guard.bodyResolved⟩ (guard.fresh false))

theorem after_guard_inherited {input : Input Context} (guard : NamedPresenceConditional.Evidence input)
    (environment : Environment) (solved : Solves environment (afterGuard guard).bindings) :
    Solves environment input.caller.bindings := by
  have selected : Solves environment guard.selected.bindings := by
    intro pair member
    exact solved pair (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ member))))
  have shape := ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ guard.selected_attempt
  rw [shape.2.2.2] at selected
  apply ScopedCallOperands.ready_inherited input.waiting "in" input.formulaName input.nodeName (.var input.slot) environment
  intro pair member
  exact selected pair (List.mem_append_left _ member)

theorem ready_retained_fresh (caller : Control) (head left right : String) (destination : Atom) (name : String)
    (fresh : FreshFor name caller.bindings) (leftApart : name ≠ left) (rightApart : name ≠ right)
    (retained : name ∈ caller.support) :
    FreshFor name (ScopedCallOperands.ready caller head left right destination).bindings := by
  have supported := GuardedInsertionPairSource.prepend_support caller
    [.evaluate (ScopedCallOperands.source head left right) destination] retained
  have apart (index : Nat) : name ≠ ScopedCallOperands.slot caller head left right destination index :=
    GuardedInsertionPairSource.fresh_apart_of_support _ name index supported
  intro pair member
  rcases List.mem_append.mp member with earlier | last
  · rcases List.mem_append.mp earlier with old | added
    · exact fresh pair old
    · cases List.mem_singleton.mp added
      simp [encode, Mettapedia.Logic.LP.Term.freeVars, leftApart, apart]
  · cases List.mem_singleton.mp last
    simp [encode, Mettapedia.Logic.LP.Term.freeVars, rightApart, apart]

theorem comparison_retained_fresh (caller : Control) (destination : Atom) (request : LiteralQuerySource.Request)
    (present : Bool) (name : String) (fresh : FreshFor name caller.bindings) (retained : name ∈ caller.support) :
    FreshFor name (PresenceGuardSource.comparisonBindings caller destination request present) := by
  have notMember := GuardedInsertionPairSource.prepend_support caller
    [.evaluate (PresenceGuardSource.source request) destination] retained
  have argumentMember : name ∈ (PresenceGuardSource.equalityControl caller destination request).support :=
    GuardedInsertionPairSource.prepend_support caller _ retained
  apply PresenceGuardSource.fresh_append_closed
  · apply PresenceGuardSource.fresh_append_closed
    · apply PresenceGuardSource.fresh_append_closed
      · exact fresh
      · exact GuardedInsertionPairSource.fresh_apart_of_support _ name 0 argumentMember
      · exact PresenceGuardSource.tuple_freeVars request present
    · exact GuardedInsertionPairSource.fresh_apart_of_support _ name 1 argumentMember
    · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  · exact GuardedInsertionPairSource.fresh_apart_of_support _ name 0 notMember
  · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem fresh_apart_literal (bindings : Equations) (principal : Environment) (name argument : String) (value : Atom)
    (resolved : resolve bindings = some principal) (fresh : FreshFor name bindings)
    (reading : read principal (.var argument) = value) (literal : SpaceSemantics.Literal value) : name ≠ argument := by
  intro same
  subst argument
  have equal := (ClosedOnceQueryFrame.fresh_read bindings name principal fresh resolved).symm.trans reading
  rw [← equal] at literal
  cases literal

theorem after_guard_fresh {input : Input Context} (guard : NamedPresenceConditional.Evidence input)
    (principal : Environment) (formula node : Atom) (name : String)
    (resolved : resolve input.caller.bindings = some principal)
    (formulaRead : read principal (.var input.formulaName) = formula)
    (nodeRead : read principal (.var input.nodeName) = node)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (fresh : FreshFor name input.caller.bindings)
    (entryMember : name ∈ input.entry.support) (waitingMember : name ∈ input.waiting.support) :
    FreshFor name (afterGuard guard).bindings := by
  have readyFresh := ready_retained_fresh input.waiting "in" input.formulaName input.nodeName (.var input.slot) name fresh
    (fresh_apart_literal _ _ name _ formula resolved fresh formulaRead formulaLiteral)
    (fresh_apart_literal _ _ name _ node resolved fresh nodeRead nodeLiteral) waitingMember
  have readySupport : input.waiting.support ⊆ input.ready.support := by
    apply ClosedOnceQueryFrame.support_mono input.waiting input.ready rfl (fun _ h => h)
    · intro pair member
      exact List.mem_append_left _ (List.mem_append_left _ member)
    · intro goal member
      exact List.mem_cons_of_mem _ member
  have protectedMember : name ∈ input.protected.support := by
    rw [NamedPresenceConditional.Input.protected, protectControl_support]
    exact Finset.mem_union_left _ (readySupport waitingMember)
  obtain ⟨leftRead, rightRead⟩ := ScopedCallOperands.ready_readings input.waiting "in" input.formulaName input.nodeName
    (.var input.slot) principal guard.principal formula node resolved guard.resolved formulaRead nodeRead
    (LiteralQuerySource.read_literal _ formulaLiteral) (LiteralQuerySource.read_literal _ nodeLiteral)
  change read guard.principal (input.operand 0) = formula at leftRead
  change read guard.principal (input.operand 1) = node at rightRead
  have shape := ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ guard.selected_attempt
  have selectedFresh : FreshFor name guard.selected.bindings := by
    rw [shape.2.2.2, leftRead, rightRead]
    exact NamedPresenceAdmission.selected_result_fresh input.protected guard.occurrence input.request formula node
      (.var input.slot) input.waiting.goals name formulaLiteral nodeLiteral readyFresh protectedMember
  let caller := NamedPresenceSource.caller input.pending.length guard.selected input.waiting.goals
  have callerSupport : input.waiting.support ⊆ caller.support := by
    apply ClosedOnceQueryFrame.support_mono input.waiting caller
      (by exact shape.1.symm) ?_ ?_ ?_
    · intro name kept
      change name ∈ guard.selected.reserved
      rw [shape.2.1]
      exact Finset.mem_union_left _ kept
    · intro pair member
      change pair ∈ guard.selected.bindings
      rw [shape.2.2.2]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
    · intro goal member
      exact List.mem_cons_of_mem _ member
  apply PresenceGuardSource.fresh_append_closed
  · exact comparison_retained_fresh caller (.var input.slot) input.request false name selectedFresh (callerSupport waitingMember)
  · exact GuardedInsertionPairSource.fresh_apart_of_support input.entry name 0 entryMember
  · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem body_names_retained (input : Input Context) (body : Body)
    (destination : input.destination = .var body.result)
    (noBody : input.no = ScopedInsertionSequence.source body.temporary input.request.handle body.secondHandle body.firstCode body.secondCode) :
    (body.temporary ∈ input.entry.support ∧ body.temporary ∈ input.waiting.support) ∧
      (body.result ∈ input.entry.support ∧ body.result ∈ input.waiting.support) := by
  have temp : body.temporary ∈ (encode input.no).freeVars := by
    rw [noBody, ScopedInsertionSequence.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var body.temporary, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  constructor
  · constructor
    · apply GuardedInsertionPairSource.goal_atom_support _ input.source body.temporary
        (by simp [NamedPresenceConditional.Input.entry, Goal.atoms])
      rw [NamedPresenceConditional.Input.source, CapturedPatternSupport.mem_expression_names]
      exact ⟨input.no, by simp, temp⟩
    · exact GuardedInsertionPairSource.goal_atom_support _ input.no body.temporary
        (by simp [NamedPresenceConditional.Input.waiting, Goal.atoms]) temp
  · constructor
    · exact GuardedInsertionPairSource.goal_atom_support _ (.var body.result) body.result
        (by simp [NamedPresenceConditional.Input.entry, Goal.atoms, destination])
        (by simp [encode, Mettapedia.Logic.LP.Term.freeVars])
    · exact GuardedInsertionPairSource.goal_atom_support _ (.var body.result) body.result
        (by simp [NamedPresenceConditional.Input.waiting, Goal.atoms, destination])
        (by simp [encode, Mettapedia.Logic.LP.Term.freeVars])

/-- The original caller's closed readings construct the insertion certificate
after the named guard; no reached post-guard principal is assumed. -/
theorem evidence_constructed (input : Input Context) (guard : NamedPresenceConditional.Evidence input) (body : Body)
    (principal : Environment) (formula node secondValue : Atom)
    (single : guard.alternatives = []) (destination : input.destination = .var body.result)
    (yesEmpty : input.yes = NamedGuardedInsertionSource.empty)
    (noBody : input.no = ScopedInsertionSequence.source body.temporary input.request.handle body.secondHandle body.firstCode body.secondCode)
    (resolved : resolve input.caller.bindings = some principal)
    (formulaRead : read principal (.var input.formulaName) = formula)
    (nodeRead : read principal (.var input.nodeName) = node)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (freshTemporary : FreshFor body.temporary input.caller.bindings) (freshResult : FreshFor body.result input.caller.bindings)
    (distinct : body.temporary ≠ body.result)
    (firstRead : read principal body.firstCode = input.request.pattern)
    (secondRead : read principal body.secondCode = secondValue) (secondLiteral : SpaceSemantics.Literal secondValue)
    (firstOrdinary : ScopedQuerySource.mutationPayload false input.request.pattern = true)
    (secondOrdinary : ScopedQuerySource.mutationPayload false secondValue = true) :
    ∃ evidence : Evidence input guard body, evidence.secondValue = secondValue := by
  obtain ⟨afterPrincipal, afterResolved⟩ := resolve_complete (after_guard_consistent guard)
  have inherited := after_guard_inherited guard afterPrincipal (resolve_sound afterResolved)
  obtain ⟨temporaryNames, resultNames⟩ := body_names_retained input body destination noBody
  exact ⟨{
    single, destination, yesEmpty, noBody, principal := afterPrincipal, resolved := afterResolved,
    freshTemporary := after_guard_fresh guard principal formula node body.temporary resolved formulaRead nodeRead
      formulaLiteral nodeLiteral freshTemporary temporaryNames.1 temporaryNames.2,
    freshResult := after_guard_fresh guard principal formula node body.result resolved formulaRead nodeRead
      formulaLiteral nodeLiteral freshResult resultNames.1 resultNames.2,
    distinct,
    firstRead := CapturedQueryOperands.resolved_forces resolved body.firstCode input.request.pattern firstRead
      (LiteralQuerySource.read_pattern input.request) afterPrincipal inherited,
    secondValue,
    secondRead := CapturedQueryOperands.resolved_forces resolved body.secondCode secondValue secondRead
      (LiteralQuerySource.read_literal _ secondLiteral) afterPrincipal inherited,
    secondLiteral, firstOrdinary, secondOrdinary }, rfl⟩

theorem prepare_accepts (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (evidence : Evidence input guard body) :
    (NamedGuardedInsertionSource.prepare input guard body).isSome = true := by
  unfold NamedGuardedInsertionSource.prepare
  simp only [dif_pos evidence.single, dif_pos evidence.destination,
    dif_pos evidence.yesEmpty, dif_pos evidence.noBody]
  split
  next absent => simp [evidence.resolved] at absent
  next principal resolved =>
    have same := Option.some.inj (resolved.symm.trans evidence.resolved)
    subst principal
    simp only [dif_pos evidence.freshTemporary, dif_pos evidence.freshResult,
      dif_pos evidence.distinct, dif_pos evidence.firstRead, evidence.secondRead,
      dif_pos ((LiteralQuerySource.checkLiteral_iff _).mpr evidence.secondLiteral),
      dif_pos evidence.firstOrdinary, dif_pos evidence.secondOrdinary, Option.isSome_some]

/-- Both executable preparers succeed from the original captured caller and
canonical source. Their actual returned certificates are used throughout. -/
theorem canonical_admission (input : Input Context) (body : Body)
    (principal : Environment) (formula node secondValue : Atom) (occurrence : Nat)
    (resolved : resolve input.caller.bindings = some principal)
    (formulaRead : read principal (.var input.formulaName) = formula)
    (nodeRead : read principal (.var input.nodeName) = node)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (pattern : input.request.pattern = .expression [.symbol "sat", formula, node])
    (row : input.program.equations[occurrence]? = some (NamedPresenceSource.declaration input.request))
    (otherHeads : ∀ index equation, input.program.equations[index]? = some equation → index ≠ occurrence → equation.head ≠ "in")
    (leftEvaluated : Eval.argumentIsRaw input.program "in" 0 = false)
    (rightEvaluated : Eval.argumentIsRaw input.program "in" 1 = false)
    (destination : input.destination = .var body.result)
    (yesEmpty : input.yes = NamedGuardedInsertionSource.empty)
    (noBody : input.no = ScopedInsertionSequence.source body.temporary input.request.handle body.secondHandle body.firstCode body.secondCode)
    (freshTemporary : FreshFor body.temporary input.caller.bindings) (freshResult : FreshFor body.result input.caller.bindings)
    (distinct : body.temporary ≠ body.result)
    (firstRead : read principal body.firstCode = input.request.pattern)
    (secondRead : read principal body.secondCode = secondValue) (secondLiteral : SpaceSemantics.Literal secondValue)
    (firstOrdinary : ScopedQuerySource.mutationPayload false input.request.pattern = true)
    (secondOrdinary : ScopedQuerySource.mutationPayload false secondValue = true) :
    ∃ guard receipt, NamedPresenceConditional.prepare input = some guard ∧
      NamedGuardedInsertionSource.prepare input guard body = some receipt ∧ receipt.secondValue = secondValue := by
  obtain ⟨witness, single⟩ := NamedPresenceAdmission.evidence_constructed input principal formula node occurrence
    resolved formulaRead nodeRead formulaLiteral nodeLiteral pattern row otherHeads leftEvaluated rightEvaluated
  obtain ⟨guard, prepared, guardSingle⟩ := NamedPresenceAdmission.prepare_singleton input witness single
  obtain ⟨candidate, _payload⟩ := evidence_constructed input guard body principal formula node secondValue
    guardSingle destination yesEmpty noBody resolved formulaRead nodeRead formulaLiteral nodeLiteral
    freshTemporary freshResult distinct firstRead secondRead secondLiteral firstOrdinary secondOrdinary
  have accepted := prepare_accepts input guard body candidate
  cases checked : NamedGuardedInsertionSource.prepare input guard body with
  | none => simp [checked] at accepted
  | some receipt =>
    refine ⟨guard, receipt, prepared, checked, ?_⟩
    exact receipt.secondRead.symm.trans
      (CapturedQueryOperands.resolved_forces resolved body.secondCode secondValue secondRead
        (LiteralQuerySource.read_literal _ secondLiteral) receipt.principal
        (after_guard_inherited guard receipt.principal (resolve_sound receipt.resolved)))

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionAdmission
