import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource

/-!
# Named presence predicates retain their selected source frame

Freshening the declaration preserves the guard syntax. A selected invocation
therefore uses the captured-pattern theorem in its actual equation frame,
including the predicate delimiter, pending clauses and allocation boundary.
The canonical space handle is part of this source profile; global binding
and set-space construction are separate frontend obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars applyTypeValuation)
open ClosedOnceQueryFrame (FreshFor placed)
open LiteralQuerySource (Request)

def patternCode (formula node : String) : Atom :=
  .expression [.symbol "sat", .var formula, .var node]

def declaration (request : Request) : SpaceSemantics.Equation :=
  ⟨"in", [.var "f", .var "x"], CapturedPresenceSource.source request (patternCode "f" "x")⟩

def renamedPattern (control : Control) (occurrence : Nat) (request : Request) : Atom :=
  let rename := ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms (declaration request))
  patternCode (rename "f") (rename "x")

theorem fresh_body (control : Control) (occurrence : Nat) (request : Request) :
    ClauseChoice.freshBody control occurrence (declaration request) =
      CapturedPresenceSource.source request (renamedPattern control occurrence request) := by
  have scalar : ∀ (atom : Atom), ConstantQuerySource.Scalar atom →
      ∀ rename : String → String, renameTypeVars rename atom = atom := by
    intro atom scalar rename
    cases scalar <;> simp [renameTypeVars]
  have payload := scalar request.payload request.scalar
  have handle : ∀ rename : String → String,
      renameTypeVars rename (Effects.handleValue request.handle) = Effects.handleValue request.handle := by
    intro rename
    cases request.handle <;> simp [Effects.handleValue, renameTypeVars]
  simp only [ClauseChoice.freshBody, declaration, CapturedPresenceSource.source,
    CapturedPresenceSource.equality, CapturedCollectedOnceSource.source, CapturedOnceSource.source,
    CapturedOnceSource.query, renameTypeVars, List.map_cons, List.map_nil,
    patternCode, renamedPattern, payload, handle]

/-- The fresh guard's pattern is read from the same selected application
constraint. It cannot choose a different assignment for the query body. -/
theorem selected_pattern (control : Control) (occurrence : Nat) (request : Request)
    (formula node destination : Atom) (older : List Goal) (next : Control)
    (principal : Environment)
    (selected : ClauseChoice.attempt control "in" [formula, node] destination older
      occurrence (declaration request) = some next)
    (resolved : resolve next.bindings = some principal) :
    read principal (renamedPattern control occurrence request) =
      read principal (.expression [.symbol "sat", formula, node]) := by
  have retained := ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ selected
  have solved := resolve_sound resolved
  rw [retained.2.2.2] at solved
  have linked := (solves_append_equation _ _ _ _).mp solved |>.2
  simp only [read_eq_applyTypeValuation, ClauseChoice.freshPattern, declaration,
    ClauseChoice.pattern, renameTypeVars, applyTypeValuation, List.map_cons, List.map_nil,
    Atom.expression.injEq, List.cons.injEq, and_true, true_and] at linked
  simp only [read_eq_applyTypeValuation, renamedPattern, patternCode, applyTypeValuation,
    List.map_cons, List.map_nil]
  rcases linked with ⟨formulaEq, nodeEq⟩
  exact congrArg₂ (fun formula node => Atom.expression [.symbol "sat", formula, node])
    formulaEq.symm nodeEq.symm

def caller (retained : Nat) (selected : Control) (older : List Goal) : Control :=
  {selected with goals := .restoreCommit selected.cutBoundary :: older, cutBoundary := retained}

theorem entered (control : Control) (occurrence : Nat) (request : Request)
    (arguments : List Atom) (destination : Atom) (older : List Goal) (next : Control)
    (retained : Nat)
    (selected : ClauseChoice.attempt control "in" arguments destination older
      occurrence (declaration request) = some next) :
    predicateEntry retained next = CapturedPresenceSource.start (caller retained next older)
      destination request (renamedPattern control occurrence request) := by
  have scheduled := (ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ selected).2.2.1
  rw [fresh_body] at scheduled
  simp only [predicateEntry, scheduled, CapturedPresenceSource.start, caller]

/-- Execution of a selected named guard, before restoring the caller's
predicate delimiter. A held row can suspend at copying; an absent row does
not manufacture a successful empty collection when copying was refused. -/
theorem selected_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (original : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (occurrence : Nat) (request : Request) (formula node : Atom) (result : String)
    (older : List Goal) (selected : Control) (retained : Nat) (principal : Environment)
    (attempted : ClauseChoice.attempt original "in" [formula, node] (.var result) older
      occurrence (declaration request) = some selected)
    (resolved : resolve selected.bindings = some principal)
    (reading : read principal (.expression [.symbol "sat", formula, node]) = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true)
    (freshResult : FreshFor result (PresenceGuardSource.comparisonBindings
      (caller retained selected older) (.var result) request (decide (request.pattern ∈ rows)))) :
    let present := decide (request.pattern ∈ rows)
    (ScopedQuerySource.machine .relational program).run (CollectedOnceQuerySource.childBudget present + 10)
      (placed allocator world scope parents (predicateEntry retained selected) context origins pending) =
      ([], match PresenceGuardSource.copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents
            (PresenceGuardSource.delivered (caller retained selected older) (.var result) request present)
            context (origins ++ [0, 0]) pending)
        | none => .suspended .allocation
            (PresenceGuardSource.collectionEnd allocator world scope parents
              (caller retained selected older) context origins pending (.var result) request present)) := by
  rw [entered original occurrence request [formula, node] (.var result) older selected retained attempted]
  apply CapturedPresenceSource.source_guard_prefix
  · exact resolved
  · exact (selected_pattern original occurrence request formula node (.var result) older selected
      principal attempted resolved).trans reading
  · exact snapshot
  · exact closed
  · exact freshResult

/-- From a real ready `in` invocation through its first selected guard body.
The remaining matching declarations stay ahead of the caller's pending
alternatives. The clause scan, body execution and possible copy refusal are
all part of the same source run. -/
theorem call_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (formulaCode nodeCode : Atom) (result : String) (older : List Goal)
    (principal : Environment) (resultName : String)
    (occurrence : Nat) (request : Request) (selected : Control)
    (alternatives : List (Nat × Control)) (bodyPrincipal : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "in" [formulaCode, nodeCode] (.var result) :: older)
    (resolved : resolve control.bindings = some principal)
    (unbound : read principal (.var result) = .var resultName)
    (row : program.equations[occurrence]? = some (declaration request))
    (coverage : ClauseChoice.Frontier program
      (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) "in"
      [read principal formulaCode, read principal nodeCode] (.var result) older
      (List.range program.equations.length) ((occurrence, selected) :: alternatives))
    (bodyResolved : resolve selected.bindings = some bodyPrincipal)
    (reading : read bodyPrincipal
      (.expression [.symbol "sat", read principal formulaCode, read principal nodeCode]) = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true)
    (freshResult : FreshFor result (PresenceGuardSource.comparisonBindings
      (caller pending.length selected older) (.var result) request (decide (request.pattern ∈ rows)))) :
    let present := decide (request.pattern ∈ rows)
    let remaining := alternatives.map (fun choice =>
      (predicateEntry pending.length choice.2, context, origins ++ [choice.1])) ++ pending
    let selectedOrigins := origins ++ [occurrence]
    (ScopedQuerySource.machine .relational program).run (CollectedOnceQuerySource.childBudget present + 11)
      (allocator, ⟨world, scope :: parents⟩) =
      ([], match PresenceGuardSource.copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents
            (PresenceGuardSource.delivered (caller pending.length selected older) (.var result) request present)
            context (selectedOrigins ++ [0, 0]) remaining)
        | none => .suspended .allocation
            (PresenceGuardSource.collectionEnd allocator world scope parents
              (caller pending.length selected older) context selectedOrigins remaining (.var result) request present)) := by
  dsimp only
  have member : (occurrence, selected) ∈ ClauseChoice.choices program
      (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) "in"
      [read principal formulaCode, read principal nodeCode] (.var result) older := by
    rw [(ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr coverage]
    exact List.mem_cons_self
  obtain ⟨equation, actualRow, attempted⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp member
  have same := Option.some.inj (actualRow.symm.trans row)
  subst equation
  have declared : program.equations.any (·.head == "in") = true := by
    apply List.any_eq_true.mpr
    refine ⟨declaration request, ?_, by simp [declaration]⟩
    obtain ⟨bound, actual⟩ := List.getElem?_eq_some_iff.mp row
    exact actual ▸ List.getElem_mem bound
  have entry := ScopedQuerySource.Equations.enter .relational program allocator world scope parents control
    context origins pending "in" [formulaCode, nodeCode] (.var result) older principal resultName
    ((occurrence, selected) :: alternatives) frontier atCall resolved unbound (by decide) (by decide)
    (by decide) declared (by simpa only [List.map_cons, List.map_nil] using coverage)
  have body := selected_prefix program allocator world scope parents
    (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) context (origins ++ [occurrence])
    (alternatives.map (fun choice => (predicateEntry pending.length choice.2, context,
      origins ++ [choice.1])) ++ pending) occurrence request
    (read principal formulaCode) (read principal nodeCode) result older selected pending.length
    bodyPrincipal attempted bodyResolved reading rows snapshot closed freshResult
  have continued := (ScopedQuerySource.machine .relational program).run_succ_silent
    (fuel := CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 10) entry
  simpa only [List.map_cons, List.cons_append, placed] using continued.trans body

def returned (retained : Nat) (selected : Control) (older : List Goal) (result : String)
    (request : Request) (present : Bool) : Control :=
  {selected with
    bindings := PresenceGuardSource.comparisonBindings (caller retained selected older) (.var result) request present ++
      [(Effects.boolean present, .var result)]
    goals := older}

theorem returned_refined (retained : Nat) (selected : Control) (older : List Goal) (result : String)
    (request : Request) (present : Bool) (consistent : ∃ environment, Solves environment selected.bindings)
    (fresh : FreshFor result (PresenceGuardSource.comparisonBindings (caller retained selected older) (.var result) request present)) :
    refine (PresenceGuardSource.comparisonBindings (caller retained selected older) (.var result) request present)
      (Effects.boolean present) (.var result) = some (returned retained selected older result request present).bindings := by
  apply ClosedOnceQueryFrame.refine_fresh_closed
  · exact fresh
  · exact ClosedOnceQueryFrame.refined_consistent _ _ _
      (PresenceGuardSource.comparison_refined (caller retained selected older) (.var result) request present consistent)
  · exact PresenceGuardSource.read_boolean present

/-- The Boolean refinement and predicate-delimiter restoration are two
actual source steps. Older caller work and other clause alternatives remain. -/
theorem return_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (selected : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (retained : Nat)
    (older : List Goal) (result : String) (request : Request) (present : Bool)
    (consistent : ∃ environment, Solves environment selected.bindings)
    (fresh : FreshFor result (PresenceGuardSource.comparisonBindings (caller retained selected older) (.var result) request present)) :
    (ScopedQuerySource.machine .relational program).run 2
      (placed allocator world scope parents
        (PresenceGuardSource.delivered (caller retained selected older) (.var result) request present) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (returned retained selected older result request present) context origins pending)) := by
  have refined := returned_refined retained selected older result request present consistent fresh
  simp only [returned, caller] at refined
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, PresenceGuardSource.delivered, caller, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, installChild, retainChild, returned, refined]

def branchReached (retained : Nat) (selected : Control) (older : List Goal) (result : String)
    (request : Request) (present : Bool) (yes no destination : Atom) : Control :=
  {returned retained selected (.branch (.var result) yes no destination :: older) result request present with
    goals := .evaluate (if present then yes else no) destination :: older}

/-- The restored caller then selects its authored branch using the actual
returned equation. No answer is published by these three return steps. -/
theorem return_to_branch {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (selected : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (retained : Nat)
    (older : List Goal) (result : String) (request : Request) (present : Bool) (yes no destination : Atom)
    (consistent : ∃ environment, Solves environment selected.bindings)
    (fresh : FreshFor result (PresenceGuardSource.comparisonBindings
      (caller retained selected (.branch (.var result) yes no destination :: older)) (.var result) request present)) :
    (ScopedQuerySource.machine .relational program).run 3
      (placed allocator world scope parents
        (PresenceGuardSource.delivered (caller retained selected (.branch (.var result) yes no destination :: older))
          (.var result) request present) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (branchReached retained selected older result request present yes no destination) context origins pending)) := by
  let after := returned retained selected (.branch (.var result) yes no destination :: older) result request present
  have refined := returned_refined retained selected (.branch (.var result) yes no destination :: older) result request present consistent fresh
  obtain ⟨environment, resolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have readResult : read environment (.var result) = Effects.boolean present := by
    have bound := resolve_sound resolved (Effects.boolean present, .var result) (List.mem_append_right _ (by simp))
    rw [PresenceGuardSource.read_boolean] at bound
    exact bound.symm
  have last : (ScopedQuerySource.machine .relational program).step
      (placed allocator world scope parents after context origins pending) =
      some (.silent (placed allocator world scope parents
        (branchReached retained selected older result request present yes no destination) context origins pending)) := by
    rw [ScopedQuerySource.Guards.placed_ordinary_step .relational program allocator world scope parents after
      context origins pending (.branch (.var result) yes no destination) older rfl rfl]
    simp only [placed, after, returned, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
      resolved, readResult, installChild, retainChild, branchReached, replace]
    cases present <;> rfl
  have first := return_prefix program allocator world scope parents selected context origins pending retained
    (.branch (.var result) yes no destination :: older) result request present consistent fresh
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 2 1 _ _ [] first
  rw [Machine.run_succ_silent _ last] at combined
  simpa [Machine.run] using combined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceSource
