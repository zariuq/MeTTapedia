import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCallOperands
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceSource

/-!
# Authored named presence conditionals

Admission checks actual equation selection, principal readings and result
freshness after pure variable-operand preparation. It retains all selected
alternatives. No guard result or successful source run is an input to the
certificate. The source snapshot and witness-copy outcome remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditional

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open LiteralQuerySource (Request)

structure Input (Context : Type) where
  program : SpaceSemantics.Program
  allocator : Allocator
  world : World
  scope : CollectionScope Context
  parents : List (CollectionScope Context)
  caller : Control
  context : Context
  origins : List Nat
  pending : List (CollectionWork Context)
  destination : Atom
  formulaName : String
  nodeName : String
  yes : Atom
  no : Atom
  request : Request

variable {Context : Type}

def Input.source (input : Input Context) : Atom :=
  .expression [.symbol "if", ScopedCallOperands.source "in" input.formulaName input.nodeName, input.yes, input.no]
def Input.entry (input : Input Context) : Control :=
  {input.caller with goals := .evaluate input.source input.destination :: input.caller.goals}
def Input.slot (input : Input Context) : String := freshName input.entry 0
def Input.waiting (input : Input Context) : Control :=
  {input.caller with goals := .branch (.var input.slot) input.yes input.no input.destination :: input.caller.goals}
def Input.ready (input : Input Context) : Control :=
  ScopedCallOperands.ready input.waiting "in" input.formulaName input.nodeName (.var input.slot)
def Input.operand (input : Input Context) (index : Nat) : Atom :=
  .var (ScopedCallOperands.slot input.waiting "in" input.formulaName input.nodeName (.var input.slot) index)
def Input.callScope (input : Input Context) : CollectionScope Context :=
  {input.scope with frontier := (input.ready, input.context, input.origins) :: input.pending}
def Input.protected (input : Input Context) : Control :=
  protectControl input.ready (collectionSupport ⟨input.world, input.callScope :: input.parents⟩)
def Input.before (input : Input Context) : ScopedCursor Context :=
  placed input.allocator input.world input.scope input.parents input.entry input.context input.origins input.pending

structure Evidence (input : Input Context) where
  leftEvaluated : Eval.argumentIsRaw input.program "in" 0 = false
  rightEvaluated : Eval.argumentIsRaw input.program "in" 1 = false
  principal : Environment
  resolved : resolve input.ready.bindings = some principal
  representative : String
  unbound : read principal (.var input.slot) = .var representative
  occurrence : Nat
  selected : Control
  alternatives : List (Nat × Control)
  row : input.program.equations[occurrence]? = some (NamedPresenceSource.declaration input.request)
  coverage : ClauseChoice.Frontier input.program input.protected "in"
    [read principal (input.operand 0), read principal (input.operand 1)] (.var input.slot) input.waiting.goals
    (List.range input.program.equations.length) ((occurrence, selected) :: alternatives)
  bodyPrincipal : Environment
  bodyResolved : resolve selected.bindings = some bodyPrincipal
  reading : read bodyPrincipal (.expression [.symbol "sat",
    read principal (input.operand 0), read principal (input.operand 1)]) = input.request.pattern
  fresh : ∀ present : Bool, FreshFor input.slot (PresenceGuardSource.comparisonBindings
    (NamedPresenceSource.caller input.pending.length selected input.waiting.goals)
    (.var input.slot) input.request present)

/-- Executable certificate construction. Refusal provides no invented
answer; the caller can retain ordinary source execution. -/
def prepare (input : Input Context) : Option (Evidence input) := do
  if leftEvaluated : Eval.argumentIsRaw input.program "in" 0 = false then
    if rightEvaluated : Eval.argumentIsRaw input.program "in" 1 = false then
      match resolved : resolve input.ready.bindings with
      | none => none
      | some principal =>
        match unbound : read principal (.var input.slot) with
        | .var representative =>
          match choices : ClauseChoice.choices input.program input.protected "in"
              [read principal (input.operand 0), read principal (input.operand 1)] (.var input.slot) input.waiting.goals with
          | [] => none
          | (occurrence, selected) :: alternatives =>
            match found : input.program.equations[occurrence]? with
            | none => none
            | some equation =>
              if shape : equation.head = (NamedPresenceSource.declaration input.request).head ∧
                  equation.arguments = (NamedPresenceSource.declaration input.request).arguments ∧
                  equation.body = (NamedPresenceSource.declaration input.request).body then
                match bodyResolved : resolve selected.bindings with
                | none => none
                | some bodyPrincipal =>
                  if reading : read bodyPrincipal (.expression [.symbol "sat",
                      read principal (input.operand 0), read principal (input.operand 1)]) = input.request.pattern then
                    if yesFresh : FreshFor input.slot (PresenceGuardSource.comparisonBindings
                        (NamedPresenceSource.caller input.pending.length selected input.waiting.goals)
                        (.var input.slot) input.request true) then
                      if noFresh : FreshFor input.slot (PresenceGuardSource.comparisonBindings
                          (NamedPresenceSource.caller input.pending.length selected input.waiting.goals)
                          (.var input.slot) input.request false) then
                        some {
                          leftEvaluated, rightEvaluated, principal, resolved, representative, unbound,
                          occurrence, selected, alternatives,
                          row := by
                            have same : equation = NamedPresenceSource.declaration input.request := by
                              cases equation
                              simp_all [NamedPresenceSource.declaration]
                            exact found.trans (congrArg some same)
                          coverage := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp choices
                          bodyPrincipal, bodyResolved, reading
                          fresh := by intro present; cases present <;> assumption }
                      else none
                    else none
                  else none
              else none
        | _ => none
    else none
  else none

theorem Evidence.consistent {input : Input Context} (evidence : Evidence input) :
    ∃ environment, Solves environment input.caller.bindings := by
  exact ⟨evidence.principal, ScopedCallOperands.ready_inherited input.waiting "in" input.formulaName input.nodeName
    (.var input.slot) evidence.principal (resolve_sound evidence.resolved)⟩

theorem Evidence.callable {input : Input Context} (evidence : Evidence input) : callable input.program "in" = true := by
  have declared : input.program.equations.any (·.head == "in") = true := by
    apply List.any_eq_true.mpr
    obtain ⟨bound, actual⟩ := List.getElem?_eq_some_iff.mp evidence.row
    exact ⟨_, actual ▸ List.getElem_mem bound, by simp [NamedPresenceSource.declaration]⟩
  simp [EagerDFS.Destination.callable, declared]

theorem Evidence.selected_attempt {input : Input Context} (evidence : Evidence input) :
    ClauseChoice.attempt input.protected "in"
      [read evidence.principal (input.operand 0), read evidence.principal (input.operand 1)]
      (.var input.slot) input.waiting.goals evidence.occurrence
      (NamedPresenceSource.declaration input.request) = some evidence.selected := by
  have member : (evidence.occurrence, evidence.selected) ∈ ClauseChoice.choices input.program input.protected "in"
      [read evidence.principal (input.operand 0), read evidence.principal (input.operand 1)]
      (.var input.slot) input.waiting.goals := by
    rw [(ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr evidence.coverage]
    exact List.mem_cons_self
  obtain ⟨equation, row, attempted⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp member
  have same := Option.some.inj (row.symm.trans evidence.row)
  subst equation
  exact attempted

theorem Evidence.selected_destination {input : Input Context} (evidence : Evidence input) :
    evidence.selected.destination = input.caller.destination := by
  have actual := (ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ evidence.selected_attempt).1
  simpa only [Input.protected, protectControl, Input.ready, ScopedCallOperands.ready, Input.waiting] using actual

theorem Evidence.selected_cut_boundary {input : Input Context} (evidence : Evidence input) :
    evidence.selected.cutBoundary = input.caller.cutBoundary := by
  have source := (ClauseChoice.selection_iff_attempt input.program input.protected "in"
    [read evidence.principal (input.operand 0), read evidence.principal (input.operand 1)]
    (.var input.slot) input.waiting.goals evidence.occurrence (NamedPresenceSource.declaration input.request)
    evidence.selected evidence.row).mpr evidence.selected_attempt
  have actual := ScopedQuerySource.Equations.selected_cut_boundary source
  simpa only [Input.protected, protectControl, Input.ready, ScopedCallOperands.ready, Input.waiting] using actual

theorem preparation (input : Input Context) (evidence : Evidence input) :
    (ScopedQuerySource.machine .relational input.program).run 6 input.before =
      ([], .exhausted (input.allocator, ⟨input.world, input.callScope :: input.parents⟩)) := by
  have first : (ScopedQuerySource.machine .relational input.program).step input.before =
      some (.silent (placed input.allocator input.world input.scope input.parents
        (ScopedCallOperands.entry input.waiting "in" input.formulaName input.nodeName (.var input.slot))
        input.context input.origins input.pending)) := by
    simp [ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
      ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
      Input.before, placed, Input.entry, Input.source, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, EagerDFS.Destination.prepare, replace, installChild, retainChild,
      ScopedCallOperands.entry, Input.waiting, Input.slot]
  rw [Machine.run_succ_silent _ first]
  exact ScopedCallOperands.preparation .relational input.program input.allocator input.world input.scope input.parents
    input.waiting input.context input.origins input.pending "in" input.formulaName input.nodeName (.var input.slot)
    (by decide) evidence.callable evidence.leftEvaluated evidence.rightEvaluated evidence.consistent

def Evidence.remaining {input : Input Context} (evidence : Evidence input) : List (CollectionWork Context) :=
  evidence.alternatives.map (fun choice =>
    (predicateEntry input.pending.length choice.2, input.context, input.origins ++ [choice.1])) ++ input.pending

def Evidence.selectedOrigins {input : Input Context} (evidence : Evidence input) : List Nat :=
  input.origins ++ [evidence.occurrence]

def Evidence.endpoint {input : Input Context} (evidence : Evidence input) (allocator : Allocator)
    (present : Bool) : ScopedCursor Context :=
  placed allocator input.world input.callScope input.parents
    (NamedPresenceSource.branchReached input.pending.length evidence.selected input.caller.goals input.slot
      input.request present input.yes input.no input.destination)
    input.context (evidence.selectedOrigins ++ [0, 0]) evidence.remaining

def Evidence.copyBoundary {input : Input Context} (evidence : Evidence input) (present : Bool) : ScopedCursor Context :=
  PresenceGuardSource.collectionEnd input.allocator input.world input.callScope input.parents
    (NamedPresenceSource.caller input.pending.length evidence.selected input.waiting.goals)
    input.context evidence.selectedOrigins evidence.remaining (.var input.slot) input.request present

/-- From authored `if (in $f $x) ...` through operand preparation, complete
clause entry, the first selected guard, return and branch selection. Other
selected clauses remain pending. Copy refusal retains its reached boundary. -/
theorem source_prefix (input : Input Context) (evidence : Evidence input) (rows : List Atom)
    (snapshot : input.world.state.read input.request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true) :
    let present := decide (input.request.pattern ∈ rows)
    (ScopedQuerySource.machine .relational input.program).run (CollectedOnceQuerySource.childBudget present + 20) input.before =
      ([], match PresenceGuardSource.copyAllocator input.allocator present with
        | some next => .exhausted (evidence.endpoint next present)
        | none => .suspended .allocation (evidence.copyBoundary present)) := by
  dsimp only
  let present := decide (input.request.pattern ∈ rows)
  have called := NamedPresenceSource.call_prefix input.program input.allocator input.world input.callScope input.parents
    input.ready input.context input.origins input.pending (input.operand 0) (input.operand 1) input.slot input.waiting.goals
    evidence.principal evidence.representative evidence.occurrence input.request evidence.selected evidence.alternatives
    evidence.bodyPrincipal rfl rfl evidence.resolved evidence.unbound evidence.row evidence.coverage
    evidence.bodyResolved evidence.reading rows snapshot closed (evidence.fresh present)
  dsimp only at called
  have throughReturn : (ScopedQuerySource.machine .relational input.program).run
      (CollectedOnceQuerySource.childBudget present + 14) (input.allocator, ⟨input.world, input.callScope :: input.parents⟩) =
      ([], match PresenceGuardSource.copyAllocator input.allocator present with
        | some next => .exhausted (evidence.endpoint next present)
        | none => .suspended .allocation (evidence.copyBoundary present)) := by
    cases copied : PresenceGuardSource.copyAllocator input.allocator present with
    | some next =>
      rw [copied] at called
      have restored := NamedPresenceSource.return_to_branch input.program next input.world input.callScope input.parents
        evidence.selected input.context (evidence.selectedOrigins ++ [0, 0]) evidence.remaining input.pending.length
        input.caller.goals input.slot input.request present input.yes input.no input.destination
        ⟨evidence.bodyPrincipal, resolve_sound evidence.bodyResolved⟩ (evidence.fresh present)
      have combined := (ScopedQuerySource.machine .relational input.program).established_and_pending
        (CollectedOnceQuerySource.childBudget present + 11) 3 _ _ [] called
      change (ScopedQuerySource.machine .relational input.program).run _ _ =
        ([] ++ ((ScopedQuerySource.machine .relational input.program).run 3
          (placed next input.world input.callScope input.parents
            (PresenceGuardSource.delivered (NamedPresenceSource.caller input.pending.length evidence.selected input.waiting.goals)
              (.var input.slot) input.request present) input.context (evidence.selectedOrigins ++ [0, 0]) evidence.remaining)).1,
         ((ScopedQuerySource.machine .relational input.program).run 3
          (placed next input.world input.callScope input.parents
            (PresenceGuardSource.delivered (NamedPresenceSource.caller input.pending.length evidence.selected input.waiting.goals)
              (.var input.slot) input.request present) input.context (evidence.selectedOrigins ++ [0, 0]) evidence.remaining)).2) at combined
      simp only [Input.waiting] at combined
      rw [restored] at combined
      simpa only [List.nil_append, Nat.add_assoc, Evidence.endpoint] using combined
    | none =>
      rw [copied] at called
      have stable := (ScopedQuerySource.machine .relational input.program).run_stable
        (CollectedOnceQuerySource.childBudget present + 11) 3
        (input.allocator, ⟨input.world, input.callScope :: input.parents⟩) (fun residual => by rw [called]; simp)
      rw [called] at stable
      simpa only [Nat.add_assoc, Evidence.copyBoundary, Evidence.remaining, Evidence.selectedOrigins] using stable
  have combined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    6 (CollectedOnceQuerySource.childBudget present + 14) _ _ [] (preparation input evidence)
  rw [throughReturn] at combined
  have count : 6 + (CollectedOnceQuerySource.childBudget present + 14) =
      CollectedOnceQuerySource.childBudget present + 20 := by omega
  rw [count] at combined
  simpa [present] using combined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditional
