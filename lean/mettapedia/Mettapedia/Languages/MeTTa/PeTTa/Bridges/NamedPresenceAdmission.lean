import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditional

/-!
# Uniform construction of canonical guard clause choices

Fresh formals are instantiated from closed captured operands while preserving
every inherited equation. The actual total unifier then selects the clause.
No successful clause attempt or source evaluation is supplied as a premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars applyTypeValuation)
open ClosedOnceQueryFrame (FreshFor)
open LiteralQuerySource (Request)
open NamedPresenceSource (declaration)

def formal (control : Control) (occurrence : Nat) (request : Request) (name : String) : String :=
  ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms (declaration request)) name

theorem formal_fresh (control : Control) (occurrence : Nat) (request : Request) (name : String) :
    FreshFor (formal control occurrence request name) control.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings control _ (ClauseChoice.rename_fresh control occurrence _ name)

theorem formals_distinct (control : Control) (occurrence : Nat) (request : Request) :
    formal control occurrence request "f" ≠ formal control occurrence request "x" := by
  have first : "f" ∈ ClauseChoice.names (ClauseChoice.clauseAtoms (declaration request)) := by
    change "f" ∈ ["f", "x"] ++ _
    simp
  have second : "x" ∈ ClauseChoice.names (ClauseChoice.clauseAtoms (declaration request)) := by
    change "x" ∈ ["f", "x"] ++ _
    simp
  intro same
  exact (by decide : "f" ≠ "x") (ClauseChoice.rename_injective_on control occurrence _ first second same)

def selected (control : Control) (occurrence : Nat) (request : Request)
    (formula node destination : Atom) (older : List Goal) : Control :=
  {control with
    bindings := control.bindings ++ [(.expression [.symbol "in", formula, node],
      ClauseChoice.freshPattern control occurrence (declaration request))]
    goals := .evaluate (ClauseChoice.freshBody control occurrence (declaration request)) destination :: older}

private theorem read_update_self (environment : Environment) (name : String) (value : Atom) :
    read (Function.update environment name (encode value)) (.var name) = value := by
  simp only [EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm]
  exact (congrArg decode (Function.update_self name (encode value) environment)).trans (decode_encode value)

private theorem read_expression (environment : Environment) (atoms : List Atom) :
    read environment (.expression atoms) = .expression (atoms.map (read environment)) := by
  rw [read_eq_applyTypeValuation]
  simp only [applyTypeValuation]
  congr 1
  apply List.map_congr_left
  intro atom _
  exact (read_eq_applyTypeValuation environment atom).symm

theorem instantiated_model (control : Control) (occurrence : Nat) (request : Request)
    (formula node : Atom) (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (consistent : ∃ environment, Solves environment control.bindings) :
    ∃ environment, Solves environment control.bindings ∧
      read environment (.expression [.symbol "in", formula, node]) =
        read environment (ClauseChoice.freshPattern control occurrence (declaration request)) := by
  obtain ⟨original, solved⟩ := consistent
  let first : Environment := Function.update original (formal control occurrence request "f") (encode formula)
  let both : Environment := Function.update first (formal control occurrence request "x") (encode node)
  have inherited : Solves both control.bindings :=
    ClosedOnceQueryFrame.solves_update first control.bindings _ node (formal_fresh control occurrence request "x")
      (ClosedOnceQueryFrame.solves_update original control.bindings _ formula (formal_fresh control occurrence request "f") solved)
  have formulaRead : read both (.var (formal control occurrence request "f")) = formula := by
    change read (Function.update first (formal control occurrence request "x") (encode node))
      (.var (formal control occurrence request "f")) = formula
    rw [ClosedOnceQueryFrame.read_update first (formal control occurrence request "x") node
      (.var (formal control occurrence request "f")) (by
        simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using Ne.symm (formals_distinct control occurrence request))]
    exact read_update_self original (formal control occurrence request "f") formula
  have nodeRead : read both (.var (formal control occurrence request "x")) = node := by
    exact read_update_self first (formal control occurrence request "x") node
  have formulaClosed := LiteralQuerySource.read_literal formula formulaLiteral both
  have nodeClosed := LiteralQuerySource.read_literal node nodeLiteral both
  refine ⟨both, inherited, ?_⟩
  have shape : ClauseChoice.freshPattern control occurrence (declaration request) =
      .expression [.symbol "in", .var (formal control occurrence request "f"), .var (formal control occurrence request "x")] := by
    simp only [ClauseChoice.freshPattern, ClauseChoice.pattern, declaration, formal,
      renameTypeVars, List.map_cons, List.map_nil]
  rw [shape]
  rw [read_expression, read_expression]
  simp only [List.map_cons, List.map_nil, formulaClosed, nodeClosed, formulaRead, nodeRead]

theorem attempt_constructed (control : Control) (occurrence : Nat) (request : Request)
    (formula node destination : Atom) (older : List Goal)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (consistent : ∃ environment, Solves environment control.bindings) :
    ClauseChoice.attempt control "in" [formula, node] destination older occurrence (declaration request) =
      some (selected control occurrence request formula node destination older) := by
  have refined : refine control.bindings (.expression [.symbol "in", formula, node])
      (ClauseChoice.freshPattern control occurrence (declaration request)) =
      some (selected control occurrence request formula node destination older).bindings :=
    (refine_iff _ _ _ _).mpr ⟨rfl, instantiated_model control occurrence request formula node formulaLiteral nodeLiteral consistent⟩
  apply (ClauseChoice.attempt_iff control "in" [formula, node] destination older occurrence
    (declaration request) rfl _).mpr
  exact ⟨_, (refinement_iff _ _ _ _).mpr refined, rfl⟩

theorem fresh_pattern_names (control : Control) (occurrence : Nat) (request : Request) :
    (encode (ClauseChoice.freshPattern control occurrence (declaration request))).freeVars =
      {formal control occurrence request "f", formal control occurrence request "x"} := by
  simp only [ClauseChoice.freshPattern, ClauseChoice.pattern, declaration, renameTypeVars, List.map_cons, List.map_nil]
  ext name
  rw [CapturedPatternSupport.mem_expression_names]
  simp [formal, declaration, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem selected_result_fresh (control : Control) (occurrence : Nat) (request : Request)
    (formula node destination : Atom) (older : List Goal) (result : String)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (fresh : FreshFor result control.bindings) (retained : result ∈ control.support) :
    FreshFor result (selected control occurrence request formula node destination older).bindings := by
  have apart (name : String) : result ≠ formal control occurrence request name := by
    intro same
    apply ClauseChoice.rename_fresh control occurrence (ClauseChoice.clauseAtoms (declaration request)) name
    change formal control occurrence request name ∈ control.support
    rw [← same]
    exact retained
  have applicationLiteral : SpaceSemantics.Literal (.expression [.symbol "in", formula, node]) := by
    apply SpaceSemantics.Literal.constructor "in" _ (by decide)
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> assumption
  intro pair member
  rcases List.mem_append.mp member with old | added
  · exact fresh pair old
  · cases List.mem_singleton.mp added
    constructor
    · rw [CapturedPatternSupport.literal_names_empty _ applicationLiteral]
      simp
    · rw [fresh_pattern_names]
      simp [apart]

/-- Exactly one applicable occurrence is obtained from the actual row and
the refusal of all other positions; no empty-search oracle is used. -/
theorem choices_singleton (program : SpaceSemantics.Program) (control : Control) (occurrence : Nat)
    (request : Request) (formula node destination : Atom) (older : List Goal)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (consistent : ∃ environment, Solves environment control.bindings)
    (row : program.equations[occurrence]? = some (declaration request))
    (otherHeads : ∀ index equation, program.equations[index]? = some equation → index ≠ occurrence → equation.head ≠ "in") :
    ClauseChoice.choices program control "in" [formula, node] destination older =
      [(occurrence, selected control occurrence request formula node destination older)] := by
  let next := selected control occurrence request formula node destination older
  have chosen : ClauseChoice.trial program control "in" [formula, node] destination older occurrence = some next := by
    simp only [ClauseChoice.trial, row]
    exact attempt_constructed control occurrence request formula node destination older formulaLiteral nodeLiteral consistent
  have refused (index : Nat) (different : index ≠ occurrence) :
      ClauseChoice.trial program control "in" [formula, node] destination older index = none := by
    cases found : program.equations[index]? with
    | none => simp [ClauseChoice.trial, found]
    | some equation =>
        simp only [ClauseChoice.trial, found]
        exact ClauseChoice.wrong_head_not_selected control "in" [formula, node] destination older index equation
          (otherHeads index equation found different)
  have scan : ∀ positions : List Nat, positions.Nodup →
      positions.filterMap (fun index =>
        (ClauseChoice.trial program control "in" [formula, node] destination older index).map (index, ·)) =
      if occurrence ∈ positions then [(occurrence, next)] else [] := by
    intro positions nodup
    induction positions with
    | nil => simp
    | cons index rest ih =>
        obtain ⟨notHeld, restDistinct⟩ := List.nodup_cons.mp nodup
        by_cases same : index = occurrence
        · subst index
          simp [chosen, ih restDistinct, notHeld]
        · simp [refused index same, ih restDistinct, Ne.symm same]
  obtain ⟨bound, _actual⟩ := List.getElem?_eq_some_iff.mp row
  simpa only [ClauseChoice.choices, List.mem_range, if_pos bound] using scan (List.range program.equations.length) List.nodup_range

theorem conditional_slot_fresh {Context : Type} (input : NamedPresenceConditional.Input Context) :
    FreshFor input.slot input.caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings input.entry _ (freshName_not_mem _ _)

theorem conditional_slot_apart {Context : Type} (input : NamedPresenceConditional.Input Context)
    (name : String) (argument : name = input.formulaName ∨ name = input.nodeName) : input.slot ≠ name := by
  intro same
  apply freshName_not_mem input.entry 0
  change input.slot ∈ input.entry.support
  rw [same]
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ name).mpr
  refine Or.inr ⟨input.source, ?_, ?_⟩
  · simp [NamedPresenceConditional.Input.entry, Goal.atoms]
  · rw [NamedPresenceConditional.Input.source, CapturedPatternSupport.mem_expression_names]
    refine ⟨ScopedCallOperands.source "in" input.formulaName input.nodeName, by simp, ?_⟩
    rw [ScopedCallOperands.source, CapturedPatternSupport.mem_expression_names]
    refine ⟨.var name, ?_, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
    rcases argument with same | same <;> simp [same]

theorem conditional_ready_fresh {Context : Type} (input : NamedPresenceConditional.Input Context) :
    FreshFor input.slot input.ready.bindings :=
  ScopedCallOperands.ready_result_fresh input.waiting "in" input.formulaName input.nodeName input.slot
    (conditional_slot_fresh input)
    (conditional_slot_apart input input.formulaName (Or.inl rfl))
    (conditional_slot_apart input input.nodeName (Or.inr rfl))

theorem conditional_slot_retained {Context : Type} (input : NamedPresenceConditional.Input Context) :
    input.slot ∈ input.protected.support := by
  rw [NamedPresenceConditional.Input.protected, protectControl_support]
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ input.slot).mpr
  exact Or.inr ⟨.var input.slot, by simp [NamedPresenceConditional.Input.ready, ScopedCallOperands.ready, Goal.atoms],
    by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

/-- Every canonical call from closed captured operands constructs the actual
guard certificate. Store membership and source execution are not premises. -/
theorem evidence_constructed {Context : Type} (input : NamedPresenceConditional.Input Context)
    (principal : Environment) (formula node : Atom) (occurrence : Nat)
    (resolved : resolve input.caller.bindings = some principal)
    (formulaRead : read principal (.var input.formulaName) = formula)
    (nodeRead : read principal (.var input.nodeName) = node)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (pattern : input.request.pattern = .expression [.symbol "sat", formula, node])
    (row : input.program.equations[occurrence]? = some (declaration input.request))
    (otherHeads : ∀ index equation, input.program.equations[index]? = some equation → index ≠ occurrence → equation.head ≠ "in")
    (leftEvaluated : Eval.argumentIsRaw input.program "in" 0 = false)
    (rightEvaluated : Eval.argumentIsRaw input.program "in" 1 = false) :
    ∃ evidence : NamedPresenceConditional.Evidence input, evidence.alternatives = [] := by
  obtain ⟨readyPrincipal, readyResolved⟩ := resolve_complete
    (ScopedCallOperands.ready_consistent input.waiting "in" input.formulaName input.nodeName (.var input.slot)
      ⟨principal, resolve_sound resolved⟩)
  obtain ⟨leftRead, rightRead⟩ := ScopedCallOperands.ready_readings input.waiting "in" input.formulaName input.nodeName
    (.var input.slot) principal readyPrincipal formula node resolved readyResolved formulaRead nodeRead
    (LiteralQuerySource.read_literal _ formulaLiteral) (LiteralQuerySource.read_literal _ nodeLiteral)
  have readyUnbound := ClosedOnceQueryFrame.fresh_read input.ready.bindings input.slot readyPrincipal
    (conditional_ready_fresh input) readyResolved
  let next := selected input.protected occurrence input.request formula node (.var input.slot) input.waiting.goals
  have attempted := attempt_constructed input.protected occurrence input.request formula node (.var input.slot) input.waiting.goals
    formulaLiteral nodeLiteral ⟨readyPrincipal, resolve_sound readyResolved⟩
  have chosen := (ClauseChoice.selection_iff_attempt input.program input.protected "in" [formula, node]
    (.var input.slot) input.waiting.goals occurrence (declaration input.request) next row).mpr attempted
  obtain ⟨bodyPrincipal, bodyResolved⟩ := ClauseChoice.selected_resolves chosen
  have choices := choices_singleton input.program input.protected occurrence input.request formula node (.var input.slot)
    input.waiting.goals formulaLiteral nodeLiteral ⟨readyPrincipal, resolve_sound readyResolved⟩ row otherHeads
  have nextFresh : FreshFor input.slot next.bindings :=
    selected_result_fresh input.protected occurrence input.request formula node (.var input.slot) input.waiting.goals input.slot
      formulaLiteral nodeLiteral (conditional_ready_fresh input) (conditional_slot_retained input)
  have satLiteral : SpaceSemantics.Literal (.expression [.symbol "sat", formula, node]) := by
    apply SpaceSemantics.Literal.constructor "sat" _ (by decide)
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> assumption
  refine ⟨{
    leftEvaluated, rightEvaluated, principal := readyPrincipal, resolved := readyResolved,
    representative := input.slot, unbound := readyUnbound,
    occurrence, selected := next, alternatives := [], row,
    coverage := ?_
    bodyPrincipal, bodyResolved
    reading := ?_
    fresh := ?_ }, rfl⟩
  · apply (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp
    change read readyPrincipal (input.operand 0) = formula at leftRead
    change read readyPrincipal (input.operand 1) = node at rightRead
    rw [leftRead, rightRead]
    exact choices
  · change read readyPrincipal (input.operand 0) = formula at leftRead
    change read readyPrincipal (input.operand 1) = node at rightRead
    rw [leftRead, rightRead, LiteralQuerySource.read_literal _ satLiteral, pattern]
  · intro present
    exact PresenceGuardSource.comparison_fresh _ input.slot input.request present nextFresh

/-- The executable preparer accepts every independently constructed guard
certificate; this is not a kernel reduction of a single closed example. -/
theorem prepare_accepts {Context : Type} (input : NamedPresenceConditional.Input Context)
    (evidence : NamedPresenceConditional.Evidence input) :
    (NamedPresenceConditional.prepare input).isSome = true := by
  have choices := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr evidence.coverage
  unfold NamedPresenceConditional.prepare
  simp only [dif_pos evidence.leftEvaluated, dif_pos evidence.rightEvaluated]
  split
  next absent => simp [evidence.resolved] at absent
  next principal resolved =>
    have same := Option.some.inj (resolved.symm.trans evidence.resolved)
    subst principal
    split
    next representative unbound =>
      split
      next absent => simp [choices] at absent
      next occurrence selected alternatives actual =>
        have same := List.cons.inj (actual.symm.trans choices)
        have first := Prod.mk.inj same.1
        rcases first with ⟨rfl, rfl⟩
        rcases same.2 with rfl
        split
        next absent => simp [evidence.row] at absent
        next equation found =>
          have same := Option.some.inj (found.symm.trans evidence.row)
          subst equation
          split
          next shape =>
            split
            next absent => simp [evidence.bodyResolved] at absent
            next bodyPrincipal resolved =>
              have same := Option.some.inj (resolved.symm.trans evidence.bodyResolved)
              subst bodyPrincipal
              simp only [dif_pos evidence.reading, dif_pos (evidence.fresh true),
                dif_pos (evidence.fresh false), Option.isSome_some]
          next wrong => exact (wrong ⟨rfl, rfl, rfl⟩).elim
    next notVar => exact (notVar evidence.representative evidence.unbound).elim

/-- Actual principal resolution and complete clause coverage determine the
same remaining alternatives in any two admission certificates. -/
theorem alternatives_unique {Context : Type} (input : NamedPresenceConditional.Input Context)
    (first second : NamedPresenceConditional.Evidence input) :
    first.alternatives = second.alternatives := by
  have same := Option.some.inj (first.resolved.symm.trans second.resolved)
  have left := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr first.coverage
  have right := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr second.coverage
  rw [same] at left
  exact (List.cons.inj (left.symm.trans right)).2

/-- The actual executable result, not merely an existential certificate,
retains the independently proved singleton coverage. -/
theorem prepare_singleton {Context : Type} (input : NamedPresenceConditional.Input Context)
    (witness : NamedPresenceConditional.Evidence input) (single : witness.alternatives = []) :
    ∃ actual, NamedPresenceConditional.prepare input = some actual ∧ actual.alternatives = [] := by
  have accepted := prepare_accepts input witness
  cases prepared : NamedPresenceConditional.prepare input with
  | none => simp [prepared] at accepted
  | some actual => exact ⟨actual, rfl, (alternatives_unique input actual witness).trans single⟩

/-- Canonical declarations and closed captured values suffice for executable
admission at every world and retained continuation. -/
theorem prepare_canonical {Context : Type} (input : NamedPresenceConditional.Input Context)
    (principal : Environment) (formula node : Atom) (occurrence : Nat)
    (resolved : resolve input.caller.bindings = some principal)
    (formulaRead : read principal (.var input.formulaName) = formula)
    (nodeRead : read principal (.var input.nodeName) = node)
    (formulaLiteral : SpaceSemantics.Literal formula) (nodeLiteral : SpaceSemantics.Literal node)
    (pattern : input.request.pattern = .expression [.symbol "sat", formula, node])
    (row : input.program.equations[occurrence]? = some (declaration input.request))
    (otherHeads : ∀ index equation, input.program.equations[index]? = some equation → index ≠ occurrence → equation.head ≠ "in")
    (leftEvaluated : Eval.argumentIsRaw input.program "in" 0 = false)
    (rightEvaluated : Eval.argumentIsRaw input.program "in" 1 = false) :
    (NamedPresenceConditional.prepare input).isSome = true := by
  obtain ⟨evidence, _single⟩ := evidence_constructed input principal formula node occurrence resolved formulaRead nodeRead
    formulaLiteral nodeLiteral pattern row otherHeads leftEvaluated rightEvaluated
  exact prepare_accepts input evidence

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceAdmission
