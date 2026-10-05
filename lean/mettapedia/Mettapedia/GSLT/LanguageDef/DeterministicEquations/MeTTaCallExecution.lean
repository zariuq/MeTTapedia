import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaArgumentExecution
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaPatternExecution
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaControlSubstitution

/-!
# Returning generated calls through the independent interpreter

A recursive dispatcher call uses `eval` and then returns its tagged outcome.
These composition laws retain the callee's actual bindings and state. They
apply to a supplied callee execution segment, without assuming anything about
the eventual result of the surrounding checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal (substituteName)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.ModelTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open Metta.Minimal

/-- Every emitted dispatcher has the same two-input interface: source fuel
and one encoded argument vector. The ordered bodies do not alter this header. -/
theorem dispatcher_input_interface (program : Program) (head : String) (first : Nat) :
    ∃ body, (dispatcher program head first).1.2 =
      call "=" [call (dispatchName head)
        [.var (freshName first), .var (freshName (first + 1))],
        call "function" [body]] := by
  exact ⟨_, rfl⟩

theorem expression_runtime_embedded (program : Program) (names : Names) (fuel : Atom)
    (term : Term) (first : Nat) (rename : String → String) :
    isEmbeddedOp (renBy rename
      (toLeaTTaAtom (expression program names fuel term first).1)) = true := by
  have guarded (supplied : Atom) (build : Atom → Emit Atom) (start : Nat) :
      isEmbeddedOp (renBy rename
        (toLeaTTaAtom (withFuel supplied build start).1)) = true := by
    let emitted := build (.var (freshName start)) (start + 1)
    change isEmbeddedOp (renBy rename (toLeaTTaAtom
      (call "chain" [call "eval" [call "==" [supplied, .grounded (.int 0)]],
        .var (freshName emitted.2),
        call "unify" [.var (freshName emitted.2), .grounded (.bool true),
          returned (.symbol "nik:Exhausted"),
          call "chain" [call "eval" [call "-" [supplied, .grounded (.int 1)]],
            .var (freshName start), emitted.1]]]))) = true
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      isEmbeddedOp]
    rfl
  rw [expression]
  exact guarded _ _ _

/-- The actual successful outcome branch fills an operand in the entire
compiled continuation, then starts that continuation. Freshness is checked
against the incoming store; closed-value storage establishes acyclicity and
stable repeated materialization rather than assuming either property. -/
theorem resultBranches_enters_compiled_expression (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (program : Program) (names : Names)
    (sourceFuel payload : Atom) (term : Term)
    (rename : String → String) (injective : Function.Injective rename)
    (index first fuel : Nat) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first sourceFuel)
    (stored : ClosedValueBindings bindings)
    (closed : (toLeaTTaAtom payload).vars = [])
    (freshName : Metta.Bindings.lookupVal bindings (rename (MeTTaEmit.freshName index)) = none)
    (prepared : Metta.instantiate bindings (renBy rename
      (toLeaTTaAtom (expression program names sourceFuel term first).1)) =
      renBy rename (toLeaTTaAtom (expression program names sourceFuel term first).1))
    (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let output := Metta.Bindings.addValRaw bindings (rename (MeTTaEmit.freshName index))
      (toLeaTTaAtom payload)
    interpretFuel environment (fuel + 2) state
        (⟨atomToStack (renBy rename (toLeaTTaAtom
          (resultBranches (value payload) (.var (MeTTaEmit.freshName index))
            (expression program names sourceFuel term first).1)))
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (renBy rename (toLeaTTaAtom (expression program
          (names.map (fun entry => (entry.1,
            Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName
              (MeTTaEmit.freshName index) payload entry.2)))
          (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName
            (MeTTaEmit.freshName index) payload sourceFuel) term first).1))
          (parent :: continuation), output⟩ :: rest) done := by
  intro parent output
  have filled := Control.renamed_expression_runtime_substitution program names sourceFuel
    payload term index first rename injective closed before namesBound fuelBound
  have embedded : isEmbeddedOp (Metta.Subst.apply
      [(rename (MeTTaEmit.freshName index), toLeaTTaAtom payload)]
      (renBy rename (toLeaTTaAtom (expression program names sourceFuel term first).1))) = true := by
    rw [filled]
    exact expression_runtime_embedded _ _ _ _ _ _
  have entered := (renamed_resultBranches_value_enters environment state bindings rename payload
    (expression program names sourceFuel term first).1 (MeTTaEmit.freshName index)
    parentBody scope continuation fuel rest done stored closed freshName prepared embedded).2.2.2
  simpa only [filled] using entered

private theorem let_body_runtime_substitution (program : Program) (sourceBindings : Env)
    (name : String) (payload body : Term) (remaining index first : Nat)
    (before : index < first) (rename : String → String) (injective : Function.Injective rename) :
    Metta.Subst.apply [(rename (freshName index), toLeaTTaAtom (MeTTaData.encode payload))]
      (renBy rename (toLeaTTaAtom (expression program
        ((name, .var (freshName index)) :: sourceBindings.map (fun row =>
          (row.1, MeTTaData.encode row.2)))
        (.grounded (.int remaining)) body first).1)) =
    renBy rename (toLeaTTaAtom (expression program
      (((name, payload) :: sourceBindings).map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int remaining)) body first).1) := by
  have namesBound : ∀ entry ∈ (name, Atom.var (freshName index)) ::
      sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)),
      UsesBefore first entry.2 := by
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact (usesBefore_freshName first index).mpr before
    · obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
      exact usesBefore_data first row.2
  have transported := Control.renamed_expression_runtime_substitution program
    ((name, .var (freshName index)) :: sourceBindings.map (fun row =>
      (row.1, MeTTaData.encode row.2)))
    (.grounded (.int remaining)) (MeTTaData.encode payload) body index first rename injective
    (data_atom_runtime_closed (MeTTaData.encode_data payload)) before namesBound
    (usesBefore_grounded first _)
  simpa only [List.map_cons, List.map_map, Function.comp_def, substituteName,
    if_true, Control.substituteName_encoded] using transported

/-- A computed let value enters the source continuation with the newest
lexical binding first. The actual matcher update preserves closed storage,
runtime principality and every unrelated key. Source variables remain encoded
data, including names shadowed by this binding. -/
theorem resultBranches_enters_let_body (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (program : Program) (sourceBindings : Env)
    (name : String) (payload body : Term) (remaining index first fuel : Nat)
    (before : index < first) (rename : String → String) (injective : Function.Injective rename)
    (stored : ClosedValueBindings bindings) (invariant : LeaRuntimeBindingInvariant bindings)
    (fresh : Metta.Bindings.lookupVal bindings (rename (freshName index)) = none)
    (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let pending := (expression program
      ((name, .var (freshName index)) :: sourceBindings.map (fun row =>
        (row.1, MeTTaData.encode row.2))) (.grounded (.int remaining)) body first).1
    (∀ key ∈ (renBy rename (toLeaTTaAtom pending)).vars,
      Metta.Bindings.lookupVal bindings key = none) →
    let entered := renBy rename (toLeaTTaAtom (expression program
      (((name, payload) :: sourceBindings).map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int remaining)) body first).1)
    let output := Metta.Bindings.addValRaw bindings (rename (freshName index))
      (toLeaTTaAtom (MeTTaData.encode payload))
    let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
    ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
    (∀ other, other ≠ rename (freshName index) →
      Metta.Bindings.lookupVal output other = Metta.Bindings.lookupVal bindings other) ∧
    interpretFuel environment (fuel + 2) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom
        (resultBranches (value (MeTTaData.encode payload)) (.var (freshName index)) pending)))
        (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (⟨atomToStack entered (parent :: continuation), output⟩ :: rest) done := by
  intro pending unassigned entered output parent
  have substituted := let_body_runtime_substitution program sourceBindings name payload body
    remaining index first before rename injective
  change Metta.Subst.apply
    [(rename (freshName index), toLeaTTaAtom (MeTTaData.encode payload))]
    (renBy rename (toLeaTTaAtom pending)) = entered at substituted
  have embedded : isEmbeddedOp (Metta.Subst.apply
      [(rename (freshName index), toLeaTTaAtom (MeTTaData.encode payload))]
      (renBy rename (toLeaTTaAtom pending))) = true := by
    rw [substituted]
    exact expression_runtime_embedded _ _ _ _ _ _
  obtain ⟨closed, preserved, frame, run⟩ := renamed_resultBranches_value_enters environment state
    bindings rename (MeTTaData.encode payload) pending (freshName index) parentBody scope
    continuation fuel rest done stored (data_atom_runtime_closed (MeTTaData.encode_data payload))
    fresh (instantiate_unassigned bindings stored _ unassigned) embedded
  refine ⟨closed, preserved invariant, frame, ?_⟩
  simpa only [substituted] using run


private theorem let_core_substitute_fuel (program : Program) (names : Names)
    (name : String) (bound body : Term) (first remaining : Nat)
    (namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2) :
    let target := Atom.var (freshName (first + 1))
    let assigned := expression program names (.var (freshName first)) bound (first + 2)
    let tail := expression program ((name, target) :: names)
      (.var (freshName first)) body assigned.2
    let assigned' := expression program names (.grounded (.int remaining)) bound (first + 2)
    let tail' := expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned'.2
    (substituteName (freshName first) (.grounded (.int remaining))
      (bindResult assigned.1 target tail.1 tail.2).1,
      (bindResult assigned.1 target tail.1 tail.2).2) =
      bindResult assigned'.1 target tail'.1 tail'.2 := by
  intro target assigned tail assigned' tail'
  have namesBound (endIndex : Nat) : ∀ entry ∈ names, UsesBefore endIndex entry.2 := by
    intro entry member variableName occurrence
    exact False.elim (data_has_no_variables (namesData entry member) variableName occurrence)
  have namesSame : names.map (fun entry => (entry.1,
      substituteName (freshName first) (.grounded (.int remaining)) entry.2)) = names := by
    calc
      _ = names.map id := List.map_congr_left (fun entry member => by
        rw [Control.substituteName_data (namesData entry member)]; rfl)
      _ = _ := List.map_id names
  have fuelSame : substituteName (freshName first) (.grounded (.int remaining))
      (.var (freshName first)) = .grounded (.int remaining) := by simp [substituteName]
  have targetSame : substituteName (freshName first) (.grounded (.int remaining)) target =
      target := by
    simp [target, substituteName, freshName_injective.eq_iff]
  have assignedBound := expression_scope program names (.var (freshName first)) bound
    (first + 2) (namesBound _) ((usesBefore_freshName _ _).mpr (by omega))
  change first + 2 < assigned.2 ∧ UsesBefore assigned.2 assigned.1 at assignedBound
  have bodyNames : ∀ entry ∈ (name, target) :: names, UsesBefore assigned.2 entry.2 := by
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact (usesBefore_freshName _ _).mpr (by omega)
    · exact namesBound _ entry member
  have tailBound := expression_scope program ((name, target) :: names)
    (.var (freshName first)) body assigned.2 bodyNames
    ((usesBefore_freshName _ _).mpr (by omega))
  change assigned.2 < tail.2 ∧ UsesBefore tail.2 tail.1 at tailBound
  have assignedSame := Control.expression_substitution program names (.var (freshName first))
    (.grounded (.int remaining)) bound first (first + 2) (by omega)
    (namesBound _) ((usesBefore_freshName _ _).mpr (by omega))
  simp only [namesSame, fuelSame] at assignedSame
  change (substituteName (freshName first) (.grounded (.int remaining)) assigned.1,
    assigned.2) = assigned' at assignedSame
  have tailSame := Control.expression_substitution program ((name, target) :: names)
    (.var (freshName first)) (.grounded (.int remaining)) body first assigned.2
    (by omega) bodyNames ((usesBefore_freshName _ _).mpr (by omega))
  simp only [List.map_cons, targetSame, namesSame, fuelSame] at tailSame
  change (substituteName (freshName first) (.grounded (.int remaining)) tail.1,
    tail.2) = expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned.2 at tailSame
  dsimp only [tail']
  rw [← assignedSame]
  dsimp only
  rw [← tailSame]
  simpa only [targetSame] using Control.substituteName_bindResult
    (.grounded (.int remaining)) assigned.1 target tail.1 first tail.2 (by omega)

/-- Positive source fuel enters the compiled let binder after the actual
numeric guard. The bound computation and lexical continuation receive the
same predecessor budget as in the source evaluator. -/
theorem let_positive_execution_in_frame (program : Program) (names : Names)
    (name : String) (bound body : Term) (first remaining fuel : Nat)
    (environment : MinEnv) (state : St) (bindings : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2)
    (stored : ClosedValueBindings bindings)
    (groundings : environment.gt = Metta.Builtins.table)
    (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let source := (expression program names (.grounded (.int (remaining + 1)))
      (.expr [.sym "let", .var name, bound, body]) first).1
    (∀ key ∈ (renBy rename (toLeaTTaAtom source)).vars,
      Metta.Bindings.lookupVal bindings key = none) →
    let target := Atom.var (freshName (first + 1))
    let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
    let tail := expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned.2
    let entered := renBy rename (toLeaTTaAtom
      (bindResult assigned.1 target tail.1 tail.2).1)
    let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
    interpretFuel environment (fuel + 8) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom source)) (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (⟨atomToStack entered (parent :: continuation), bindings⟩ :: rest) done := by
  intro source unassigned target assigned tail entered parent
  let build : Atom → Emit Atom := fun n => do
    let t ← fresh
    let a ← expression program names n bound
    let b ← expression program ((name, t) :: names) n body
    bindResult a t b
  let rawAssigned := expression program names (.var (freshName first)) bound (first + 2)
  let rawTail := expression program ((name, target) :: names)
    (.var (freshName first)) body rawAssigned.2
  let raw := bindResult rawAssigned.1 target rawTail.1 rawTail.2
  have buildShape : build (.var (freshName first)) (first + 1) = raw := rfl
  have sourceShape : source = (withFuel (.grounded (.int (remaining + 1))) build first).1 := by
    dsimp only [source]
    rw [expression]
    rfl
  have namesBound (last : Nat) : ∀ entry ∈ names, UsesBefore last entry.2 := by
    intro entry member key occurrence
    exact False.elim (data_has_no_variables (namesData entry member) key occurrence)
  have aBound := expression_scope program names (.var (freshName first)) bound
    (first + 2) (namesBound _) ((usesBefore_freshName _ _).mpr (by omega))
  change first + 2 < rawAssigned.2 ∧ UsesBefore rawAssigned.2 rawAssigned.1 at aBound
  have bBound := expression_scope program ((name, target) :: names) (.var (freshName first))
    body rawAssigned.2 (by
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact (usesBefore_freshName _ _).mpr (by omega)
      · exact namesBound _ entry member)
    ((usesBefore_freshName _ _).mpr (by omega))
  change rawAssigned.2 < rawTail.2 ∧ UsesBefore rawTail.2 rawTail.1 at bBound
  have rBound := bindResult_scope rawAssigned.1 target rawTail.1 rawTail.2
    (aBound.2.mono bBound.1.le) ((usesBefore_freshName _ _).mpr (by omega)) bBound.2
  change raw.2 = rawTail.2 + 1 ∧ UsesBefore (rawTail.2 + 1) raw.1 at rBound
  have rawBound : first + 1 ≤ raw.2 ∧ UsesBefore raw.2 raw.1 := by
    rw [rBound.1]
    exact ⟨by omega, rBound.2⟩
  have privateRemaining : Metta.instantiate bindings (.var (rename (freshName first))) =
      .var (rename (freshName first)) := by
    apply instantiate_unassigned bindings stored
    intro key member
    have same : key = rename (freshName first) := by simpa [Metta.Atom.vars] using member
    subst key
    exact unassigned _ (expression_remaining_occurs program names _ _ first rename)
  have rawFixed : Metta.instantiate bindings (renBy rename (toLeaTTaAtom raw.1)) =
      renBy rename (toLeaTTaAtom raw.1) := by
    apply instantiate_unassigned bindings stored
    intro key member
    apply unassigned key
    have shape : source = call "chain" [call "eval" [call "=="
      [.grounded (.int (remaining + 1)), .grounded (.int 0)]],
      .var (freshName raw.2), call "unify" [.var (freshName raw.2), .grounded (.bool true),
      returned (.symbol "nik:Exhausted"), call "chain" [call "eval" [call "-"
      [.grounded (.int (remaining + 1)), .grounded (.int 1)]], .var (freshName first), raw.1]]] := by
      rw [sourceShape]
      rfl
    simp only [shape, call, returned, toLeaTTaAtom, toLeaTTaAtoms, renBy,
      List.map_cons, List.map_nil, Metta.Atom.vars, List.flatten_cons, List.flatten_nil,
      List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil]
    tauto
  have transported := Control.fillInputs_runtime [(first, Atom.grounded (.int remaining))]
    raw.1 rename injective (by simp [toLeaTTaAtom, Metta.Atom.vars])
  have substituted := congrArg Prod.fst
    (let_core_substitute_fuel program names name bound body first remaining namesData)
  change substituteName (freshName first) (.grounded (.int remaining)) raw.1 =
    (bindResult assigned.1 target tail.1 tail.2).1 at substituted
  simp only [List.map_cons, List.map_nil, Control.fillInputs] at transported
  rw [substituted] at transported
  change Metta.Subst.apply [(rename (freshName first), .gnd (.int remaining))]
    (renBy rename (toLeaTTaAtom raw.1)) = entered at transported
  have run := renamed_withFuel_positive_execution_in_frame environment state bindings rename
    injective build first remaining fuel parentBody scope continuation rest done groundings
    privateRemaining (by simpa only [buildShape] using rawBound)
  simpa only [buildShape, rawFixed, transported, sourceShape] using run


/-- The let receiver and pending lexical continuation are disjoint from the
bound expression's allocated variables. This includes shadowed source names. -/
theorem let_waiting_variables_disjoint (program : Program) (names : Names)
    (name : String) (bound body : Term) (first remaining : Nat)
    (namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2)
    (rename : String → String) (injective : Function.Injective rename) :
    let target := Atom.var (freshName (first + 1))
    let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
    let tail := expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned.2
    ∀ key ∈ (renBy rename (toLeaTTaAtom target)).vars ++
        (renBy rename (toLeaTTaAtom tail.1)).vars,
      key ∉ (renBy rename (toLeaTTaAtom assigned.1)).vars := by
  intro target assigned tail key waiting child
  obtain ⟨index, lower, upper, same⟩ := Control.renamed_expression_data_name_bounds program names
    (.grounded (.int remaining)) bound (first + 2) rename namesData (.grounded _) key child
  change index < assigned.2 at upper
  have variableSame (left right : String) (occurs : AtomOccurs (.var left) right) : left = right := by
    cases occurs
    rfl
  have different : freshName (first + 1) ≠ freshName index := by
    intro same
    have := freshName_injective same
    omega
  rcases List.mem_append.mp waiting with receiver | pending
  · have receiverSame : key = rename (freshName (first + 1)) := by
      simpa only [target, toLeaTTaAtom, renBy, Metta.Atom.vars, List.mem_singleton] using receiver
    have := freshName_injective (injective (receiverSame.symm.trans same))
    omega
  · have targetBound : UsesBefore assigned.2 target :=
      (usesBefore_freshName _ _).mpr (by omega)
    have namesBound : ∀ entry ∈ (name, target) :: names, UsesBefore assigned.2 entry.2 := by
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact targetBound
      · intro variableName occurrence
        exact False.elim (data_has_no_variables (namesData entry member) variableName occurrence)
    have absent := Control.expression_excludes_unused_input program ((name, target) :: names)
      (.grounded (.int remaining)) body index assigned.2 upper namesBound
      (usesBefore_grounded _ _) (by
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · intro occurs
          exact different (variableSame _ _ occurs)
        · exact data_has_no_variables (namesData entry member) _)
      (by intro occurs; cases occurs)
    rw [renBy_vars] at pending
    obtain ⟨original, occurs, spelling⟩ := List.mem_map.mp pending
    have originalSame := injective (spelling.trans same)
    exact absent (originalSame ▸ atomOccurs_of_mem_translated_vars occurs)

/-- Waiting operands remain visible to recursive dispatcher freshening,
even when a chain's explicit shared-variable scope is empty. -/
theorem bindResult_waiting_variables_live (rename : String → String)
    (source name body : Atom) (first : Nat) (previous : Stack) :
    let sourceCall := renBy rename (toLeaTTaAtom (call "function" [source]))
    let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName first)) name body))
    let caller : Frame :=
      {atom := .expr [.sym "chain", sourceCall, .var (rename (freshName first)), template],
        ret := .chain, vars := chainFrameVars previous sourceCall template}
    ∀ key ∈ (renBy rename (toLeaTTaAtom name)).vars ++ (renBy rename (toLeaTTaAtom body)).vars,
      key ∈ liveStackVars (caller :: previous) := by
  intro sourceCall template caller key member
  have waiting : key ∈ template.vars := by
    simp only [template, resultBranches, selectBranches, List.foldr_cons, List.foldr_nil,
      call, value, returned, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      Metta.Atom.vars, List.flatten_cons, List.flatten_nil,
      List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil] at *
    tauto
  have atomMember : key ∈ caller.atom.vars := by
    simp only [caller, Metta.Atom.vars, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil]
    tauto
  simp only [liveStackVars, List.flatMap_cons, List.mem_append]
  exact Or.inl (Or.inr atomMember)

theorem closed_substitution_vars_subset (atom payload : Metta.Atom) (name : String)
    (closed : payload.vars = []) (key : String)
    (member : key ∈ (Metta.Subst.apply [(name, payload)] atom).vars) : key ∈ atom.vars := by
  have transport := instantiate_add_closed_value [] name payload atom .nil closed rfl
  rw [Metta.instantiate_nil] at transport
  rw [← transport] at member
  exact instantiate_closed_vars_subset _ (addValRaw_closed closed .nil) atom key member

private theorem withFuel_body_variable (sourceFuel : Atom) (build : Atom → Emit Atom)
    (first : Nat) (rename : String → String) (key : String)
    (member : key ∈ (renBy rename (toLeaTTaAtom (build (.var (freshName first)) (first + 1)).1)).vars) :
    key ∈ (renBy rename (toLeaTTaAtom (withFuel sourceFuel build first).1)).vars := by
  let raw := build (.var (freshName first)) (first + 1)
  have shape : (withFuel sourceFuel build first).1 = call "chain"
    [call "eval" [call "==" [sourceFuel, .grounded (.int 0)]], .var (freshName raw.2),
      call "unify" [.var (freshName raw.2), .grounded (.bool true),
        returned (.symbol "nik:Exhausted"), call "chain"
          [call "eval" [call "-" [sourceFuel, .grounded (.int 1)]], .var (freshName first), raw.1]]] := rfl
  change key ∈ (renBy rename (toLeaTTaAtom raw.1)).vars at member
  simp only [shape, call, returned, toLeaTTaAtom, toLeaTTaAtoms, renBy,
    List.map_cons, List.map_nil, Metta.Atom.vars, List.flatten_cons, List.flatten_nil,
    List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil]
  tauto

/-- Fuel materialization removes variables and introduces none. Every variable of the
entered let core is protected by freshness of the whole source expression. -/
theorem let_core_variables_in_source (program : Program) (names : Names)
    (name : String) (bound body : Term) (first remaining : Nat)
    (namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2)
    (rename : String → String) (injective : Function.Injective rename) :
    let source := (expression program names (.grounded (.int (remaining + 1)))
      (.expr [.sym "let", .var name, bound, body]) first).1
    let target := Atom.var (freshName (first + 1))
    let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
    let tail := expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned.2
    ∀ key ∈ (renBy rename (toLeaTTaAtom (bindResult assigned.1 target tail.1 tail.2).1)).vars,
      key ∈ (renBy rename (toLeaTTaAtom source)).vars := by
  intro source target assigned tail key member
  let build : Atom → Emit Atom := fun n => do
    let t ← fresh
    let a ← expression program names n bound
    let b ← expression program ((name, t) :: names) n body
    bindResult a t b
  let raw := build (.var (freshName first)) (first + 1)
  have sourceShape : source = (withFuel (.grounded (.int (remaining + 1))) build first).1 := by
    dsimp only [source]
    rw [expression]
    rfl
  have filled := congrArg Prod.fst
    (let_core_substitute_fuel program names name bound body first remaining namesData)
  change Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName (freshName first)
    (.grounded (.int remaining)) raw.1 = (bindResult assigned.1 target tail.1 tail.2).1 at filled
  have transport := Control.fillInputs_runtime [(first, Atom.grounded (.int remaining))]
    raw.1 rename injective (by simp [toLeaTTaAtom, Metta.Atom.vars])
  simp only [List.map_cons, List.map_nil, Control.fillInputs] at transport
  rw [filled] at transport
  rw [← transport] at member
  have rawMember := closed_substitution_vars_subset _ _ _
    (by simp [toLeaTTaAtom, Metta.Atom.vars]) key member
  rw [sourceShape]
  exact withFuel_body_variable _ build first rename key rawMember

/-- The waiting receiver and body are part of the entered let core. -/
theorem let_waiting_variables_in_source (program : Program) (names : Names)
    (name : String) (bound body : Term) (first remaining : Nat)
    (namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2)
    (rename : String → String) (injective : Function.Injective rename) :
    let source := (expression program names (.grounded (.int (remaining + 1)))
      (.expr [.sym "let", .var name, bound, body]) first).1
    let target := Atom.var (freshName (first + 1))
    let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
    let tail := expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned.2
    ∀ key ∈ (renBy rename (toLeaTTaAtom target)).vars ++ (renBy rename (toLeaTTaAtom tail.1)).vars,
      key ∈ (renBy rename (toLeaTTaAtom source)).vars := by
  intro source target assigned tail key member
  apply let_core_variables_in_source program names name bound body first remaining namesData
    rename injective key
  change key ∈ (renBy rename (toLeaTTaAtom (call "chain"
    [call "function" [assigned.1], .var (freshName tail.2),
     resultBranches (.var (freshName tail.2)) target tail.1]))).vars
  simp only [resultBranches, selectBranches, List.foldr_cons, List.foldr_nil, call, value,
    returned, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
    Metta.Atom.vars, List.flatten_cons, List.flatten_nil, List.nil_append,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil] at *
  tauto

private theorem let_operand_variables_in_source (program : Program) (names : Names)
    (name : String) (bound body : Term) (first remaining : Nat)
    (namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2)
    (rename : String → String) (injective : Function.Injective rename) :
    ∀ key ∈ (renBy rename (toLeaTTaAtom
        (expression program names (.grounded (.int remaining)) bound (first + 2)).1)).vars,
      key ∈ (renBy rename (toLeaTTaAtom (expression program names (.grounded (.int (remaining + 1)))
        (.expr [.sym "let", .var name, bound, body]) first).1)).vars := by
  intro key member
  apply let_core_variables_in_source program names name bound body first remaining namesData
    rename injective key
  change key ∈ (renBy rename (toLeaTTaAtom (call "chain" [call "function" [_], _, _]))).vars
  simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
    Metta.Atom.vars, List.flatten_cons, List.flatten_nil, List.nil_append,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil]
  tauto

/-- A completed bound computation enters the let body with its exact value.
The premise is the child interpreter segment and its restricted caller-frame
property. Freshness of the receiver and lexical continuation is derived from
allocated ranges and the real waiting frame, rather than assumed of the child
output. -/
theorem let_value_enters_continuation (program : Program) (sourceBindings : Env)
    (name : String) (bound body payload : Term) (first remaining cost fuel : Nat)
    (environment : MinEnv) (state nextState : St) (incoming middle : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (stored : ClosedValueBindings incoming) (middleStored : ClosedValueBindings middle)
    (middleInvariant : LeaRuntimeBindingInvariant middle)
    (groundings : environment.gt = Metta.Builtins.table)
    (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
    let source := (expression program names (.grounded (.int (remaining + 1)))
      (.expr [.sym "let", .var name, bound, body]) first).1
    let target := Atom.var (freshName (first + 1))
    let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
    let tail := expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned.2
    let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
    let sourceCall := renBy rename (toLeaTTaAtom (call "function" [assigned.1]))
    let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName tail.2)) target tail.1))
    let recipient : Frame :=
      {atom := .expr [.sym "chain", sourceCall, .var (rename (freshName tail.2)), template],
       ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template}
    (∀ key ∈ (renBy rename (toLeaTTaAtom source)).vars,
      Metta.Bindings.lookupVal incoming key = none) →
    (∀ key ∈ liveStackVars (recipient :: parent :: continuation),
      key ∉ (renBy rename (toLeaTTaAtom assigned.1)).vars →
      Metta.Bindings.lookupVal incoming key = none →
      Metta.Bindings.lookupVal middle key = none) →
    (interpretFuel environment (fuel + 4 + cost) state
      (⟨atomToStack sourceCall (recipient :: parent :: continuation), incoming⟩ :: rest) done =
     interpretFuel environment (fuel + 4) nextState
      (finItem (recipient :: parent :: continuation)
        (toLeaTTaAtom (value (MeTTaData.encode payload))) middle :: rest) done) →
    let output := Metta.Bindings.addValRaw middle (rename (freshName (first + 1)))
      (toLeaTTaAtom (MeTTaData.encode payload))
    let entered := renBy rename (toLeaTTaAtom (expression program
      (((name, payload) :: sourceBindings).map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int remaining)) body assigned.2).1)
    ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
    (∀ key ∈ entered.vars, key ∈ (renBy rename (toLeaTTaAtom source)).vars) ∧
    (∀ key ∈ entered.vars, Metta.Bindings.lookupVal output key = none) ∧
    (∀ key ∈ liveStackVars (parent :: continuation),
      key ∉ (renBy rename (toLeaTTaAtom source)).vars →
      Metta.Bindings.lookupVal incoming key = none →
      Metta.Bindings.lookupVal output key = none) ∧
    interpretFuel environment (fuel + 12 + cost) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom source)) (parent :: continuation), incoming⟩ :: rest) done =
    interpretFuel environment fuel nextState
      (⟨atomToStack entered (parent :: continuation), output⟩ :: rest) done := by
  intro names source target assigned tail parent sourceCall template recipient sourcePrivate
    framePreserved operandRun output entered
  have namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact MeTTaData.encode_data row.2
  have namesBound (last : Nat) : ∀ entry ∈ names, UsesBefore last entry.2 := by
    intro entry member key occurs
    exact False.elim (data_has_no_variables (namesData entry member) key occurs)
  have assignedBound := expression_scope program names (.grounded (.int remaining)) bound
    (first + 2) (namesBound _) (usesBefore_grounded _ _)
  change first + 2 < assigned.2 ∧ UsesBefore assigned.2 assigned.1 at assignedBound
  have targetBound : UsesBefore assigned.2 target := (usesBefore_freshName _ _).mpr (by omega)
  have tailBound := expression_scope program ((name, target) :: names)
    (.grounded (.int remaining)) body assigned.2 (by
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact targetBound
      · exact namesBound _ entry member) (usesBefore_grounded _ _)
  change assigned.2 < tail.2 ∧ UsesBefore tail.2 tail.1 at tailBound
  have outputPrivate : ∀ key ∈ (renBy rename (toLeaTTaAtom target)).vars ++
      (renBy rename (toLeaTTaAtom tail.1)).vars, Metta.Bindings.lookupVal middle key = none := by
    intro key member
    apply framePreserved key
    · exact bindResult_waiting_variables_live rename assigned.1 target tail.1 tail.2
        (parent :: continuation) key member
    · exact let_waiting_variables_disjoint program names name bound body first remaining
        namesData rename injective key member
    · exact sourcePrivate key (let_waiting_variables_in_source program names name bound body
        first remaining namesData rename injective key member)
  have receiverPrivate : Metta.Bindings.lookupVal middle (rename (freshName (first + 1))) = none :=
    outputPrivate _ (List.mem_append_left _ (by simp [target, toLeaTTaAtom, Metta.Atom.vars]))
  have pendingPrivate : ∀ key ∈ (renBy rename (toLeaTTaAtom tail.1)).vars,
      Metta.Bindings.lookupVal middle key = none :=
    fun key member => outputPrivate key (List.mem_append_right _ member)
  obtain ⟨outputStored, outputInvariant, _, enteredRun⟩ := resultBranches_enters_let_body environment
    nextState middle program sourceBindings name payload body remaining (first + 1) assigned.2
    fuel (by omega) rename injective middleStored middleInvariant receiverPrivate
    parentBody scope continuation rest done pendingPrivate
  have filled := let_body_runtime_substitution program sourceBindings name payload body
    remaining (first + 1) assigned.2 (by omega) rename injective
  change Metta.Subst.apply [(rename (freshName (first + 1)), toLeaTTaAtom (MeTTaData.encode payload))]
    (renBy rename (toLeaTTaAtom tail.1)) = entered at filled
  have materialized := instantiate_add_closed_value middle (rename (freshName (first + 1)))
    (toLeaTTaAtom (MeTTaData.encode payload)) (renBy rename (toLeaTTaAtom tail.1))
    middleStored (data_atom_runtime_closed (MeTTaData.encode_data payload)) receiverPrivate
  rw [instantiate_unassigned middle middleStored _ pendingPrivate, filled] at materialized
  have fixed : Metta.instantiate output entered = entered := by
    rw [← materialized, instantiate_closed_value_bindings_idempotent outputStored]
  have freshEntered := fixed_closed_bindings_private output outputStored entered fixed
  refine ⟨outputStored, outputInvariant, ?_, ?_, ?_, ?_⟩
  · intro key member
    rw [← filled] at member
    apply let_waiting_variables_in_source program names name bound body first remaining
      namesData rename injective key
    apply List.mem_append_right
    exact closed_substitution_vars_subset _ _ _
      (data_atom_runtime_closed (MeTTaData.encode_data payload)) key member
  · intro key member
    apply outputStored.toValueBindings.lookup_none_of_not_key
    intro storedKey
    exact freshEntered key member (bindingValueKey_mem_vars storedKey)
  · intro key live absent unassigned
    have middlePrivate := framePreserved key
      (by simpa only [liveStackVars, List.flatMap_cons, List.mem_append] using Or.inr live)
      (fun occurs => absent (let_operand_variables_in_source program names name bound body
        first remaining namesData rename injective key occurs)) unassigned
    have different : key ≠ rename (freshName (first + 1)) := by
      intro same
      apply absent
      apply let_waiting_variables_in_source program names name bound body first remaining
        namesData rename injective key
      apply List.mem_append_left
      simp only [toLeaTTaAtom, renBy, Metta.Atom.vars, List.mem_singleton]
      exact same
    exact (lookup_add_other middle _ key _ different).trans middlePrivate
  have guardRun := let_positive_execution_in_frame program names name bound body first remaining
    (fuel + 4 + cost) environment state incoming rename injective namesData stored groundings
    parentBody scope continuation rest done sourcePrivate
  have resultClosed : (toLeaTTaAtom (value (MeTTaData.encode payload))).vars = [] := by
    simp [value, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
      data_atom_runtime_closed (MeTTaData.encode_data payload)]
  have bindRun := renamed_bindResult_of_operand_execution environment state nextState incoming
    middle rename injective assigned.1 (value (MeTTaData.encode payload)) target tail.1 tail.2
    cost (fuel + 2) parent continuation rest done resultClosed (targetBound.mono tailBound.1.le)
    tailBound.2 (by simpa only [show fuel + 2 + 2 = fuel + 4 by omega] using operandRun)
  have combined := guardRun.trans (bindRun.trans enteredRun)
  simpa only [show fuel + 4 + cost + 8 = fuel + 12 + cost by omega] using combined


/-- A renamed argument binder propagates the two stopped source outcomes
without entering the value continuation. -/
theorem renamed_resultBranches_stopped_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name body : Atom) (rename : String → String)
    (result : String) (stopped : result = "nik:Failure" ∨ result = "nik:Exhausted")
    (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (fuel : Nat) (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (acyclic : bindings.hasLoop = false) :
    let steps := if result = "nik:Failure" then 3 else 5
    let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
    interpretFuel environment (fuel + steps) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom (resultBranches (.symbol result) name body)))
        (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (finItem (parent :: continuation) (.expr [.sym "return", .sym result]) bindings :: rest) done := by
  intro steps parent
  have nameRenamed := (renamed_atom_contract rename name).2
  have bodyRenamed := (renamed_atom_contract rename body).2
  rcases stopped with rfl | rfl
  · simpa only [steps, if_true, resultBranches, selectBranches, List.foldr_cons, List.foldr_nil,
      call, value, returned, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      nameRenamed, bodyRenamed] using resultBranches_failure_enters_handler environment state
        bindings (renameTypeVars rename name) (renameTypeVars rename body) parentBody scope
        continuation fuel rest done acyclic
  · simpa only [steps, show ("nik:Exhausted" = "nik:Failure") = False from propext (by decide),
      if_false, resultBranches, selectBranches, List.foldr_cons, List.foldr_nil,
      call, value, returned, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      nameRenamed, bodyRenamed] using resultBranches_exhausted_enters_handler environment state
        bindings (renameTypeVars rename name) (renameTypeVars rename body) parentBody scope
        continuation fuel rest done acyclic

/-- Refusal and source exhaustion in the bound computation bypass the let body.
The steps account for the source guard, actual operand run, sequencing, and
selection of the appropriate stopped branch. -/
theorem let_stopped_execution_in_frame (program : Program) (names : Names)
    (name : String) (bound body : Term) (first remaining cost fuel : Nat)
    (environment : MinEnv) (state nextState : St) (incoming middle : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2)
    (stored : ClosedValueBindings incoming)
    (groundings : environment.gt = Metta.Builtins.table)
    (result : String) (stopped : result = "nik:Failure" ∨ result = "nik:Exhausted")
    (acyclic : middle.hasLoop = false)
    (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let steps := if result = "nik:Failure" then 3 else 5
    let source := (expression program names (.grounded (.int (remaining + 1)))
      (.expr [.sym "let", .var name, bound, body]) first).1
    let target := Atom.var (freshName (first + 1))
    let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
    let tail := expression program ((name, target) :: names)
      (.grounded (.int remaining)) body assigned.2
    let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
    let sourceCall := renBy rename (toLeaTTaAtom (call "function" [assigned.1]))
    let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName tail.2)) target tail.1))
    let recipient : Frame :=
      {atom := .expr [.sym "chain", sourceCall, .var (rename (freshName tail.2)), template],
       ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template}
    (∀ key ∈ (renBy rename (toLeaTTaAtom source)).vars,
      Metta.Bindings.lookupVal incoming key = none) →
    (interpretFuel environment (fuel + steps + 2 + cost) state
      (⟨atomToStack sourceCall (recipient :: parent :: continuation), incoming⟩ :: rest) done =
     interpretFuel environment (fuel + steps + 2) nextState
      (finItem (recipient :: parent :: continuation) (.sym result) middle :: rest) done) →
    interpretFuel environment (fuel + steps + 10 + cost) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom source)) (parent :: continuation), incoming⟩ :: rest) done =
    interpretFuel environment fuel nextState
      (finItem (parent :: continuation) (.expr [.sym "return", .sym result]) middle :: rest) done := by
  intro steps source target assigned tail parent sourceCall template recipient sourcePrivate operandRun
  have namesBound (last : Nat) : ∀ entry ∈ names, UsesBefore last entry.2 := by
    intro entry member key occurs
    exact False.elim (data_has_no_variables (namesData entry member) key occurs)
  have assignedBound := expression_scope program names (.grounded (.int remaining)) bound
    (first + 2) (namesBound _) (usesBefore_grounded _ _)
  change first + 2 < assigned.2 ∧ UsesBefore assigned.2 assigned.1 at assignedBound
  have targetBound : UsesBefore assigned.2 target := (usesBefore_freshName _ _).mpr (by omega)
  have tailBound := expression_scope program ((name, target) :: names)
    (.grounded (.int remaining)) body assigned.2 (by
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact targetBound
      · exact namesBound _ entry member) (usesBefore_grounded _ _)
  change assigned.2 < tail.2 ∧ UsesBefore tail.2 tail.1 at tailBound
  have guardRun := let_positive_execution_in_frame program names name bound body first remaining
    (fuel + steps + 2 + cost) environment state incoming rename injective namesData stored groundings
    parentBody scope continuation rest done sourcePrivate
  have bindRun := renamed_bindResult_of_operand_execution environment state nextState incoming
    middle rename injective assigned.1 (.symbol result) target tail.1 tail.2 cost (fuel + steps)
    parent continuation rest done (by simp [toLeaTTaAtom, Metta.Atom.vars])
      (targetBound.mono tailBound.1.le) tailBound.2 operandRun
  have stopRun := renamed_resultBranches_stopped_enters_handler environment nextState middle
    target tail.1 rename result stopped parentBody scope continuation fuel rest done acyclic
  have combined := guardRun.trans (bindRun.trans stopRun)
  simpa only [show fuel + steps + 2 + cost + 8 = fuel + steps + 10 + cost by omega] using combined

/-- A finished runtime operand enters the expression compiled with that
operand filled in. This composes the interpreter's two sequencing steps
with the substitution law for the entire compiler, including freshening.
The caller, work queue, accumulated answers and allocation state are retained. -/
theorem computed_operand_enters_expression (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (program : Program) (names : Names)
    (sourceFuel replacement : Atom) (term : Term) (source : Metta.Atom)
    (rename : String → String) (injective : Function.Injective rename)
    (index first fuel : Nat) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first sourceFuel)
    (closed : (toLeaTTaAtom replacement).vars = [])
    (scope : List String) (parent : Frame) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let template := renBy rename
      (toLeaTTaAtom (expression program names sourceFuel term first).1)
    let caller : Frame :=
      { atom := .expr [.sym "chain", source, .var (rename (freshName index)), template],
        ret := .chain, vars := scope }
    interpretFuel environment (fuel + 2) state
        (finItem (caller :: parent :: continuation) (toLeaTTaAtom replacement) bindings :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (renBy rename (toLeaTTaAtom (expression program
          (names.map (fun entry => (entry.1,
            Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName
              (freshName index) replacement entry.2)))
          (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName
            (freshName index) replacement sourceFuel) term first).1))
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro template caller
  rw [chain_result_enters environment state bindings source (toLeaTTaAtom replacement)
    template (rename (freshName index)) scope parent continuation fuel rest done,
    Metta.instantiate_of_closed bindings (toLeaTTaAtom replacement) closed]
  rw [Control.renamed_expression_runtime_substitution program names sourceFuel replacement term
    index first rename injective closed before namesBound fuelBound]

/-- Ordinary generated calls evaluate their invocation exactly once, then
return its outcome through the enclosing function. -/
theorem returnInvocation_call_shape (head : String) (arguments : List Atom)
    (first : Nat) (notValue : head ≠ "nik:Value")
    (notPrimitive : head ≠ "nik:primitive") :
    (returnInvocation (call head arguments) first).1 =
      call "chain" [call "eval" [call head arguments], .var (freshName first),
        returned (.var (freshName first))] := by
  simp [returnInvocation, call, notValue, notPrimitive, fresh, freshName]
  rfl

/-- A callee returns to its enclosing function handler. The continuation may
be empty; no outer caller is assumed. -/
theorem renamed_returnInvocation_enters_handler (environment : MinEnv)
    (state nextState : St) (incoming output : Metta.Bindings)
    (rename : String → String)
    (head : String) (arguments : List Atom) (result : Metta.Atom)
    (first cost fuel : Nat) (parentBody : Metta.Atom) (scope : List String)
    (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (notValue : head ≠ "nik:Value") (notPrimitive : head ≠ "nik:primitive")
    (closed : result.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let source := renBy rename (toLeaTTaAtom (call "eval" [call head arguments]))
    let template := renBy rename (toLeaTTaAtom (returned (.var (freshName first))))
    let recipient : Frame :=
      { atom := .expr [.sym "chain", source, .var (rename (freshName first)), template],
        ret := .chain,
        vars := chainFrameVars (parent :: continuation) source template }
    (interpretFuel environment (fuel + 3 + cost) state
          (⟨atomToStack source (recipient :: parent :: continuation), incoming⟩ :: rest)
          done =
        interpretFuel environment (fuel + 3) nextState
          (finItem (recipient :: parent :: continuation) result output :: rest) done) →
    interpretFuel environment (fuel + 3 + cost) state
        (⟨atomToStack (renBy rename (toLeaTTaAtom (returnInvocation (call head arguments) first).1))
          (parent :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (parent :: continuation) (.expr [.sym "return", result]) output :: rest) done := by
  intro parent source template recipient callee
  rw [returnInvocation_call_shape head arguments first notValue notPrimitive]
  have shape : renBy rename (toLeaTTaAtom
      (call "chain" [call "eval" [call head arguments], .var (freshName first),
        returned (.var (freshName first))])) =
      .expr [.sym "chain", source, .var (rename (freshName first)), template] := by
    simp only [source, template, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
      List.map_cons, List.map_nil]
  rw [shape]
  change interpretFuel environment (fuel + 3 + cost) state
    (⟨atomToStack source (recipient :: parent :: continuation), incoming⟩ :: rest)
      done = _
  rw [callee, show fuel + 3 = (fuel + 1) + 2 by omega,
    chain_result_enters environment nextState output source result template (rename (freshName first))
      _ parent (continuation) (fuel + 1) rest done,
    Metta.instantiate_of_closed output result closed]
  have replaced : Metta.Subst.apply [(rename (freshName first), result)] template =
      .expr [.sym "return", result] := by
    simp [template, returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
      Metta.Subst.apply, Metta.Subst.lookup]
  rw [replaced, return_enters_handler environment nextState output parentBody result scope
    continuation fuel rest done]

/-- A completed callee composes with an emitted call after variable
renaming. The four administrative steps substitute its closed result and
return through the retained caller. Only the callee segment at the actual
remaining budget is needed; insufficient budgets need not complete. -/
theorem renamed_returnInvocation_of_call_execution (environment : MinEnv)
    (state nextState : St) (incoming output : Metta.Bindings)
    (rename : String → String)
    (head : String) (arguments : List Atom) (result : Metta.Atom)
    (first cost fuel : Nat) (parentBody : Metta.Atom) (scope : List String)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (notValue : head ≠ "nik:Value") (notPrimitive : head ≠ "nik:primitive")
    (closed : result.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let source := renBy rename (toLeaTTaAtom (call "eval" [call head arguments]))
    let template := renBy rename (toLeaTTaAtom (returned (.var (freshName first))))
    let recipient : Frame :=
      { atom := .expr [.sym "chain", source, .var (rename (freshName first)), template],
        ret := .chain,
        vars := chainFrameVars (parent :: caller :: continuation) source template }
    (interpretFuel environment (fuel + 4 + cost) state
          (⟨atomToStack source (recipient :: parent :: caller :: continuation), incoming⟩ :: rest)
          done =
        interpretFuel environment (fuel + 4) nextState
          (finItem (recipient :: parent :: caller :: continuation) result output :: rest) done) →
    interpretFuel environment (fuel + 4 + cost) state
        (⟨atomToStack (renBy rename (toLeaTTaAtom (returnInvocation (call head arguments) first).1))
          (parent :: caller :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (caller :: continuation) result output :: rest) done := by
  intro parent source template recipient callee
  have prefixRun := renamed_returnInvocation_enters_handler environment state nextState incoming
    output rename head arguments result first cost (fuel + 1) parentBody scope
    (caller :: continuation) rest done notValue notPrimitive closed
      (by simpa only [← Nat.add_assoc] using callee)
  rw [prefixRun]
  simpa only [Metta.instantiate_of_closed output result closed] using
    selected_return_to_caller environment nextState output parentBody result scope
      caller continuation fuel rest done

/-- A completed callee execution composes with the emitted call and return.
The added four steps are the real chain substitution and function return.
The result is materialized before the enclosing caller receives it. -/
theorem returnInvocation_of_call_execution (environment : MinEnv)
    (state nextState : St) (incoming output : Metta.Bindings)
    (head : String) (arguments : List Atom) (result : Metta.Atom)
    (first cost fuel : Nat) (parentBody : Metta.Atom) (scope : List String)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (notValue : head ≠ "nik:Value") (notPrimitive : head ≠ "nik:primitive")
    (closed : result.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let source := toLeaTTaAtom (call "eval" [call head arguments])
    let template := toLeaTTaAtom (returned (.var (freshName first)))
    let recipient : Frame :=
      { atom := .expr [.sym "chain", source, .var (freshName first), template],
        ret := .chain,
        vars := chainFrameVars (parent :: caller :: continuation) source template }
    (interpretFuel environment (fuel + 4 + cost) state
          (⟨atomToStack source (recipient :: parent :: caller :: continuation), incoming⟩ :: rest)
          done =
        interpretFuel environment (fuel + 4) nextState
          (finItem (recipient :: parent :: caller :: continuation) result output :: rest) done) →
    interpretFuel environment (fuel + 4 + cost) state
        (⟨atomToStack (toLeaTTaAtom (returnInvocation (call head arguments) first).1)
          (parent :: caller :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (caller :: continuation) result output :: rest) done := by
  have identity (atom : Metta.Atom) : renBy id atom = atom := by
    change renBy (applyRen []) atom = atom
    rw [← renameVars_eq_renBy]
    exact Metta.renameVars_nil atom
  simpa only [identity, id_eq] using
    renamed_returnInvocation_of_call_execution environment state nextState incoming output id
      head arguments result first cost fuel parentBody scope caller continuation rest done
      notValue notPrimitive closed

/-- The call entry is the real `evalOp`, which materializes its operand
before native dispatch or equation lookup. A callee segment can therefore
start at the resulting work item rather than reconstructing an evaluator. -/
theorem eval_call_of_entry (environment : MinEnv) (state enteredState nextState : St)
    (incoming output : Metta.Bindings) (invocation result : Metta.Atom)
    (callee : Item) (continuation : Stack) (cost fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (entry : evalOp environment state continuation invocation incoming = ([callee], enteredState))
    (pending : isFinal callee = false)
    (execution :
      interpretFuel environment (fuel + cost) enteredState (callee :: rest) done =
        interpretFuel environment fuel nextState
          (finItem continuation result output :: rest) done) :
    interpretFuel environment (fuel + cost + 1) state
        (⟨atomToStack (.expr [.sym "eval", invocation]) continuation, incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem continuation result output :: rest) done := by
  rw [driver_singleton_step environment (fuel + cost) state enteredState _ callee rest done
    (by simpa [atomToStack, step_eval] using entry) pending, execution]

/-- A generated call enters the one loaded dispatcher through the real
equation query. Matching, merge pruning, RHS materialization and the fresh
counter update are all part of the resulting machine step. The loaded-rule
and primitive-dispatch premises are independently checkable properties of
the runtime environment, not a hypothesis about the callee's result. -/
theorem eval_query_enters_function (environment : MinEnv) (state : St)
    (incoming matched output : Metta.Bindings)
    (invocation lhs rhs : Metta.Atom) (body : List Metta.Atom) (head : String)
    (arguments : List Metta.Atom) (caller : Frame) (continuation : Stack)
    (fuel : Nat) (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (materialized : Metta.instantiate incoming invocation = .expr (.sym head :: arguments))
    (nativeMiss : Metta.callGrounded environment.gt head
      (arguments.map (fun atom => resolveStates state.world (subTokens state.world atom))) =
        .noReduce)
    (notEmbedded : isEmbeddedOp (.expr (.sym head :: arguments)) = false)
    (candidates : candidatesW environment state.world (.expr (.sym head :: arguments)) =
      [(lhs, rhs)])
    (stored : ClosedValueBindings incoming)
    (closed : (Metta.Atom.expr (.sym head :: arguments)).vars = [])
    (matching : matched ∈ Metta.matchAtoms
      (Metta.Minimal.freshenRuleAvoiding state.counter
        (Metta.Minimal.queryOpAvoid (caller :: continuation)
          (.expr (.sym head :: arguments)) incoming) lhs rhs).1.1
      (.expr (.sym head :: arguments)))
    (merging : output ∈ Metta.Bindings.merge incoming matched)
    (selectedBody : Metta.instantiate output
      (Metta.Minimal.freshenRuleAvoiding state.counter
        (Metta.Minimal.queryOpAvoid (caller :: continuation)
          (.expr (.sym head :: arguments)) incoming) lhs rhs).1.2 =
        .expr [.sym "function", .expr body]) :
    ClosedValueBindings output ∧
      (∀ name ∈ liveStackVars (caller :: continuation),
        Metta.Bindings.lookupVal incoming name = none →
          Metta.Bindings.lookupVal output name = none) ∧
      interpretFuel environment (fuel + 1) state
        (⟨atomToStack (.expr [.sym "eval", invocation]) (caller :: continuation),
          incoming⟩ :: rest) done =
        interpretFuel environment fuel
          { state with counter := (Metta.Minimal.freshenRuleAvoiding state.counter
            (Metta.Minimal.queryOpAvoid (caller :: continuation)
              (.expr (.sym head :: arguments)) incoming) lhs rhs).2 }
          (⟨atomToStack (.expr [.sym "function", .expr body]) (caller :: continuation),
            output⟩ :: rest) done := by
  obtain ⟨outputClosed, queried⟩ := query_single_rule environment state
    (caller :: continuation) (.expr (.sym head :: arguments)) lhs rhs
    incoming matched output candidates (by rfl) stored closed matching merging
  refine ⟨outputClosed, ?_, ?_⟩
  · intro name live unassigned
    exact query_preserves_unassigned_caller (caller :: continuation)
      (.expr (.sym head :: arguments)) lhs rhs incoming matched output state.counter name
      stored closed live unassigned matching merging
  have entryShape : atomToStack (.expr [.sym "eval", invocation]) (caller :: continuation) =
      { atom := .expr [.sym "eval", invocation], vars := varsCopy (caller :: continuation) } ::
        caller :: continuation := by
    cases invocation <;> simp [atomToStack]
  apply driver_singleton_step
  · rw [entryShape, step_eval, evalOp, materialized]
    simp only [nativeMiss, notEmbedded, Bool.false_eq_true, ↓reduceIte]
    simpa only [selectedBody, evalResult] using queried
  · exact atomToStack_pending _ _ _ _

private theorem restrict_empty_scope (bindings : Metta.Bindings) :
    restrictBnd [] bindings = [] := by
  have raw : restrictBndRaw [] bindings = [] := by
    dsimp only [restrictBndRaw]
    rw [List.filterMap_nil, List.nil_append]
    apply List.filter_eq_nil_iff.mpr
    intro relation _
    cases relation <;> simp
  simp [restrictBnd, raw]

/-- An unconstrained primitive result cannot leak its private evaluation
bindings into the generated caller. The interpreter retains the incoming
bindings, including bindings established by previous operands. -/
theorem primitive_results_keep_caller (continuation : Stack) (incoming : Metta.Bindings)
    (results : List (Metta.Atom × Metta.Bindings)) :
    retainEmbeddedMettaResults continuation incoming (.sym "%Undefined%") results =
      results.map (fun result => finItem continuation result.1 incoming) := by
  simp only [retainEmbeddedMettaResults, embeddedMettaRetentionScope, Metta.Atom.vars,
    List.filter_nil, restrict_empty_scope, Metta.Bindings.merge_empty_right,
    List.map_cons, List.map_nil]
  induction results <;> simp_all

/-- The emitted primitive gateway materializes its request before invoking
the independent evaluator. Only the named primitive's evaluation is a
premise; context selection, binding retention and the actual machine step
are consequences of the interpreter definition. -/
theorem primitive_step_of_materialized_evaluation (environment selectedEnvironment : MinEnv)
    (state nextState : St) (incoming : Metta.Bindings) (fuel : Nat)
    (invocation space : Metta.Atom) (arguments : List Metta.Atom)
    (continuation : Stack) (scope : List String)
    (results : List (Metta.Atom × Metta.Bindings))
    (materialized : Metta.instantiate incoming invocation =
      .expr (.sym "nik:primitive" :: arguments))
    (selected : evalEnvForSpace environment state.world (Metta.instantiate incoming space) =
      some selectedEnvironment)
    (evaluation : mettaEvalExpected selectedEnvironment fuel state incoming
      (.expr (.sym "nik:primitive" :: arguments)) (.sym "%Undefined%") =
        (results, nextState)) :
    interpretStack1 environment fuel state
        ⟨{ atom := .expr [.sym "metta", invocation, .sym "%Undefined%", space],
           vars := scope } :: continuation, incoming⟩ =
      (results.map (fun result => finItem continuation result.1 incoming), nextState) := by
  simp only [interpretStack1, materialized,
    show Metta.instantiate incoming (.sym "%Undefined%") = .sym "%Undefined%" from
      Metta.instantiate_of_closed incoming _ (by simp [Metta.Atom.vars]),
    selected]
  have notEmpty : (Metta.Atom.expr (.sym "nik:primitive" :: arguments) == emptyA) = false := by
    rfl
  simp [notEmpty, Metta.Atom.isError,
    show (Metta.Atom.sym "%Undefined%" == .sym "Atom") = false by decide,
    show (Metta.Atom.sym "%Undefined%" == .sym "Expression") = false by decide,
    evaluation, primitive_results_keep_caller]

/-- A primitive gateway reaches its enclosing return handler with the caller
bindings retained and the actual native result materialized. -/
theorem primitive_gateway_enters_handler (environment selectedEnvironment : MinEnv)
    (state nextState : St) (incoming privateBindings : Metta.Bindings)
    (invocation result : Metta.Atom) (arguments : List Metta.Atom)
    (contextName resultName : String) (fuel : Nat)
    (parentBody : Metta.Atom) (scope : List String)
    (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (freshContext : contextName ∉ invocation.vars)
    (distinct : resultName ≠ contextName)
    (materialized : Metta.instantiate incoming invocation =
      .expr (.sym "nik:primitive" :: arguments))
    (selected : evalEnvForSpace environment state.world
      (contextSpaceAtom environment.contextName) = some selectedEnvironment)
    (evaluation : mettaEvalExpected selectedEnvironment (fuel + 3) state incoming
      (.expr (.sym "nik:primitive" :: arguments)) (.sym "%Undefined%") =
        ([(result, privateBindings)], nextState))
    (closed : result.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let template : Metta.Atom := .expr [.sym "chain",
      .expr [.sym "metta", invocation, .sym "%Undefined%", .var contextName],
      .var resultName, .expr [.sym "return", .var resultName]]
    let body : Metta.Atom := .expr [.sym "chain", .expr [.sym "context-space"],
      .var contextName, template]
    interpretFuel environment (fuel + 7) state
        (⟨atomToStack body (parent :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (parent :: continuation) (.expr [.sym "return", result]) incoming :: rest) done := by
  intro parent template body
  let context : Metta.Atom := .expr [.sym "context-space"]
  let contextValue := contextSpaceAtom environment.contextName
  let contextScope := chainFrameVars (parent :: continuation) context template
  let contextCaller : Frame :=
    { atom := body, ret := .chain, vars := contextScope }
  let received := finItem (contextCaller :: parent :: continuation) contextValue incoming
  have contextClosed : contextValue.vars = [] := by simp [contextValue, contextSpaceAtom, Metta.Atom.vars]
  have firstStep (budget : Nat) :
      interpretStack1 environment budget state
          ⟨atomToStack body (parent :: continuation), incoming⟩ = ([received], state) := by
    simp [body, atomToStack, interpretStack1, received, contextCaller,
      contextScope, context, contextValue]
  rw [show fuel + 7 = (fuel + 6) + 1 by omega,
    driver_singleton_step environment (fuel + 6) state state _ received rest done
      (firstStep _) (by rfl)]
  change interpretFuel environment (fuel + 6) state
    (finItem (contextCaller :: parent :: continuation) contextValue incoming :: rest) done = _
  rw [show fuel + 6 = (fuel + 4) + 2 by omega,
    chain_result_enters environment state incoming context contextValue template contextName
      contextScope parent (continuation) (fuel + 4) rest done,
    Metta.instantiate_of_closed incoming contextValue contextClosed]
  let primitiveCall : Metta.Atom :=
    .expr [.sym "metta", invocation, .sym "%Undefined%", contextValue]
  let resultTemplate : Metta.Atom := .expr [.sym "return", .var resultName]
  have substituted : Metta.Subst.apply [(contextName, contextValue)] template =
      .expr [.sym "chain", primitiveCall, .var resultName, resultTemplate] := by
    simp only [template, Metta.Subst.apply, List.map_cons, List.map_nil]
    rw [substitute_fresh contextName contextValue invocation freshContext]
    simp [Metta.Subst.lookup, distinct, primitiveCall, resultTemplate]
  rw [substituted]
  let resultScope := chainFrameVars (parent :: continuation) primitiveCall resultTemplate
  let resultCaller : Frame :=
    { atom := .expr [.sym "chain", primitiveCall, .var resultName, resultTemplate],
      ret := .chain, vars := resultScope }
  let returnedResult := finItem (resultCaller :: parent :: continuation) result incoming
  have primitiveStep : interpretStack1 environment (fuel + 3) state
      ⟨atomToStack (.expr [.sym "chain", primitiveCall, .var resultName, resultTemplate])
        (parent :: continuation), incoming⟩ = ([returnedResult], nextState) := by
    simpa [atomToStack, primitiveCall, resultCaller, resultScope, returnedResult] using
      primitive_step_of_materialized_evaluation environment selectedEnvironment state nextState
        incoming (fuel + 3) invocation contextValue arguments
        (resultCaller :: parent :: continuation) _ [(result, privateBindings)]
        materialized (by rwa [Metta.instantiate_of_closed incoming contextValue contextClosed])
        evaluation
  rw [show fuel + 4 = (fuel + 3) + 1 by omega,
    driver_singleton_step environment (fuel + 3) state nextState _ returnedResult rest done
      primitiveStep (by rfl)]
  change interpretFuel environment (fuel + 3) nextState
    (finItem (resultCaller :: parent :: continuation) result incoming :: rest) done = _
  rw [show fuel + 3 = (fuel + 1) + 2 by omega,
    chain_result_enters environment nextState incoming primitiveCall result resultTemplate resultName
      resultScope parent (continuation) (fuel + 1) rest done,
    Metta.instantiate_of_closed incoming result closed]
  have returned : Metta.Subst.apply [(resultName, result)] resultTemplate =
      .expr [.sym "return", result] := by
    simp [resultTemplate, Metta.Subst.apply, Metta.Subst.lookup]
  rw [returned, return_enters_handler environment nextState incoming parentBody result scope
    continuation fuel rest done]

/-- Read the current context, evaluate a materialized primitive request, and
return its closed outcome. The eight administrative steps neither change
the request nor retain private bindings from the primitive. -/
theorem primitive_gateway_execution (environment selectedEnvironment : MinEnv)
    (state nextState : St) (incoming privateBindings : Metta.Bindings)
    (invocation result : Metta.Atom) (arguments : List Metta.Atom)
    (contextName resultName : String) (fuel : Nat)
    (parentBody : Metta.Atom) (scope : List String)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (freshContext : contextName ∉ invocation.vars)
    (distinct : resultName ≠ contextName)
    (materialized : Metta.instantiate incoming invocation =
      .expr (.sym "nik:primitive" :: arguments))
    (selected : evalEnvForSpace environment state.world
      (contextSpaceAtom environment.contextName) = some selectedEnvironment)
    (evaluation : mettaEvalExpected selectedEnvironment (fuel + 4) state incoming
      (.expr (.sym "nik:primitive" :: arguments)) (.sym "%Undefined%") =
        ([(result, privateBindings)], nextState))
    (closed : result.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let template : Metta.Atom := .expr [.sym "chain",
      .expr [.sym "metta", invocation, .sym "%Undefined%", .var contextName],
      .var resultName, .expr [.sym "return", .var resultName]]
    let body : Metta.Atom := .expr [.sym "chain", .expr [.sym "context-space"],
      .var contextName, template]
    interpretFuel environment (fuel + 8) state
        (⟨atomToStack body (parent :: caller :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (caller :: continuation) result incoming :: rest) done := by
  intro parent template body
  have prefixRun := primitive_gateway_enters_handler environment selectedEnvironment state nextState
    incoming privateBindings invocation result arguments contextName resultName (fuel + 1)
    parentBody scope (caller :: continuation) rest done freshContext distinct materialized selected
      (by simpa only [← Nat.add_assoc] using evaluation) closed
  rw [prefixRun]
  simpa only [Metta.instantiate_of_closed incoming result closed] using
    selected_return_to_caller environment nextState incoming parentBody result scope
      caller continuation fuel rest done

/-- The primitive prefix is the actual emitted syntax after freshening. -/
theorem renamed_returnInvocation_primitive_enters_handler
    (environment selectedEnvironment : MinEnv) (state nextState : St)
    (incoming privateBindings : Metta.Bindings) (rename : String → String)
    (injective : Function.Injective rename) (arguments : List Atom)
    (materializedArguments : List Metta.Atom) (result : Metta.Atom)
    (first fuel : Nat) (parentBody : Metta.Atom) (scope : List String)
    (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (bounded : UsesBefore first (call "nik:primitive" arguments))
    (materialized : Metta.instantiate incoming
      (renBy rename (toLeaTTaAtom (call "nik:primitive" arguments))) =
        .expr (.sym "nik:primitive" :: materializedArguments))
    (selected : evalEnvForSpace environment state.world
      (contextSpaceAtom environment.contextName) = some selectedEnvironment)
    (evaluation : mettaEvalExpected selectedEnvironment (fuel + 3) state incoming
      (.expr (.sym "nik:primitive" :: materializedArguments)) (.sym "%Undefined%") =
        ([(result, privateBindings)], nextState))
    (closed : result.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 7) state
        (⟨atomToStack (renBy rename
          (toLeaTTaAtom (returnInvocation (call "nik:primitive" arguments) first).1))
          (parent :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (parent :: continuation) (.expr [.sym "return", result]) incoming :: rest) done := by
  intro parent
  have shape : (returnInvocation (call "nik:primitive" arguments) first).1 =
      call "chain" [call "context-space" [], .var (freshName first),
        call "chain" [call "metta" [call "nik:primitive" arguments,
          .symbol "%Undefined%", .var (freshName first)], .var (freshName (first + 1)),
          returned (.var (freshName (first + 1)))]] := by
    rfl
  have distinct : rename (freshName (first + 1)) ≠ rename (freshName first) := by
    intro same
    have impossible := freshName_injective (injective same)
    omega
  rw [shape]
  simpa only [call, returned, toLeaTTaAtom, toLeaTTaAtoms, renBy,
    List.map_cons, List.map_nil] using
    primitive_gateway_enters_handler environment selectedEnvironment state nextState incoming
      privateBindings (renBy rename (toLeaTTaAtom (call "nik:primitive" arguments))) result
      materializedArguments (rename (freshName first)) (rename (freshName (first + 1)))
      fuel parentBody scope continuation rest done
      (bounded.renamed_runtime_fresh rename injective) distinct materialized selected evaluation closed

/-- The primitive gateway above is the emitter's actual syntax, including
both allocated names after runtime freshening. Its fresh context variable
cannot substitute into the invocation's already allocated operands. -/
theorem renamed_returnInvocation_primitive_execution
    (environment selectedEnvironment : MinEnv) (state nextState : St)
    (incoming privateBindings : Metta.Bindings) (rename : String → String)
    (injective : Function.Injective rename) (arguments : List Atom)
    (materializedArguments : List Metta.Atom) (result : Metta.Atom)
    (first fuel : Nat) (parentBody : Metta.Atom) (scope : List String)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (bounded : UsesBefore first (call "nik:primitive" arguments))
    (materialized : Metta.instantiate incoming
      (renBy rename (toLeaTTaAtom (call "nik:primitive" arguments))) =
        .expr (.sym "nik:primitive" :: materializedArguments))
    (selected : evalEnvForSpace environment state.world
      (contextSpaceAtom environment.contextName) = some selectedEnvironment)
    (evaluation : mettaEvalExpected selectedEnvironment (fuel + 4) state incoming
      (.expr (.sym "nik:primitive" :: materializedArguments)) (.sym "%Undefined%") =
        ([(result, privateBindings)], nextState))
    (closed : result.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 8) state
        (⟨atomToStack (renBy rename
          (toLeaTTaAtom (returnInvocation (call "nik:primitive" arguments) first).1))
          (parent :: caller :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (caller :: continuation) result incoming :: rest) done := by
  intro parent
  have prefixRun := renamed_returnInvocation_primitive_enters_handler environment selectedEnvironment
    state nextState incoming privateBindings rename injective arguments materializedArguments result
    first (fuel + 1) parentBody scope (caller :: continuation) rest done bounded materialized selected
      (by simpa only [← Nat.add_assoc] using evaluation) closed
  rw [prefixRun]
  simpa only [Metta.instantiate_of_closed incoming result closed] using
    selected_return_to_caller environment nextState incoming parentBody result scope
      caller continuation fuel rest done

/-- Closed argument values indexed by their allocated pattern occurrences.
This finite table is used by the compiler materialization proof. -/
def matchedInputs (first : Nat) : Env → List (Nat × Atom)
  | [] => []
  | (_, value) :: rest => (first, MeTTaData.encode value) :: matchedInputs (first + 1) rest

theorem matchedInputs_bounds (first : Nat) (environment : Env) :
    ∀ entry ∈ matchedInputs first environment,
      first ≤ entry.1 ∧ entry.1 < first + environment.length ∧
        MeTTaData.DataAtom entry.2 := by
  induction environment generalizing first with
  | nil => simp [matchedInputs]
  | cons entry rest ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨le_rfl, by simp, MeTTaData.encode_data _⟩
    · obtain ⟨lower, upper, data⟩ := ih (first + 1) value member
      exact ⟨by omega, by simpa only [List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using upper, data⟩

private theorem matchedInputs_lookup_sound (first : Nat) (environment : Env)
    (rename : String → String) (valuation : String → Metta.Atom)
    (aligned : ValuationFor (valuation ∘ rename) first environment)
    (name : String) (value : Metta.Atom)
    (found : Metta.Subst.lookup ((matchedInputs first environment).map fun entry =>
      (rename (freshName entry.1), toLeaTTaAtom entry.2)) name = some value) :
    valuation name = value := by
  induction environment generalizing first with
  | nil => simp [matchedInputs, Metta.Subst.lookup] at found
  | cons entry rest ih =>
    by_cases same : name = rename (freshName first)
    · have equal : toLeaTTaAtom (MeTTaData.encode entry.2) = value := by
        simpa [matchedInputs, Metta.Subst.lookup, same] using found
      exact same ▸ aligned.1.trans equal
    · apply ih (first + 1) aligned.2
      simpa only [matchedInputs, List.map_cons, Metta.Subst.lookup,
        beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, if_false] using found

private theorem matchedInputs_lookup_present (first : Nat) (environment : Env)
    (rename : String → String) (index : Nat)
    (inside : first ≤ index ∧ index < first + environment.length) :
    (Metta.Subst.lookup ((matchedInputs first environment).map fun entry =>
      (rename (freshName entry.1), toLeaTTaAtom entry.2))
        (rename (freshName index))).isSome := by
  induction environment generalizing first with
  | nil => simp at inside; omega
  | cons entry rest ih =>
    by_cases same : rename (freshName index) = rename (freshName first)
    · simp [matchedInputs, Metta.Subst.lookup, same]
    · have different : index ≠ first := by intro equal; exact same (equal ▸ rfl)
      simpa only [matchedInputs, List.map_cons, Metta.Subst.lookup,
        beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, if_false] using
        ih (first + 1) ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using inside.2⟩

/-- A real closed-data match materializes exactly its allocated input table;
all other variables in the selected body remain private. -/
theorem matched_body_materialization
    (parameters arguments : List Term) (first : Nat) (sourceBindings : Env)
    (sourceMatch : matchTerms parameters arguments = some sourceBindings)
    (rename : String → String)
    (fresh : Atom) (renamed : AlphaRenameAtomRel rename (patterns parameters first).1.1 fresh)
    (body : Metta.Atom) (incoming matched output : Metta.Bindings)
    (stored : ClosedValueBindings incoming)
    (fixed : Metta.instantiate incoming body = body)
    (aligned : ValuationFor (leaClassSolution output ∘ rename) first sourceBindings)
    (matching : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (MeTTaData.encodeItems arguments)) (toLeaTTaAtom fresh))
    (merging : output ∈ Metta.Bindings.merge incoming matched) :
    Metta.instantiate output body =
      Metta.Subst.apply ((matchedInputs first sourceBindings).map fun entry =>
        (rename (freshName entry.1), toLeaTTaAtom entry.2)) body := by
  apply Control.instantiate_eq_subst_on_variables
  intro name occurrence
  cases found : Metta.Subst.lookup ((matchedInputs first sourceBindings).map fun entry =>
      (rename (freshName entry.1), toLeaTTaAtom entry.2)) name with
  | some value =>
    rw [Metta.Subst.apply, found]
    have reads := matchedInputs_lookup_sound first sourceBindings rename
      (leaClassSolution output) aligned name value found
    simpa only [← applyClassSolution_lea_eq_instantiate, applyClassSolution,
      Option.getD_some] using reads
  | none =>
    rw [Metta.Subst.apply, found]
    apply matching_closed_preserves_private_variable _ _ incoming matched output name stored
      (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)) ?_ ?_ matching merging
    · apply stored.toValueBindings.lookup_none_of_not_key
      intro key
      exact fixed_closed_bindings_private incoming stored body fixed name occurrence
        (bindingValueKey_mem_vars key)
    · intro inPattern
      obtain ⟨original, originalOccurs, equal⟩ := alpha_occurs_image renamed
        (atomOccurs_iff_mem_translated_vars.mpr inPattern)
      obtain ⟨index, lower, upper, same⟩ :=
        (patterns_name_bounds parameters first).2 original originalOccurs
      have present := matchedInputs_lookup_present first sourceBindings rename index
        ⟨lower, by rwa [patterns_end_of_match parameters arguments sourceBindings sourceMatch] at upper⟩
      rw [same] at equal
      rw [equal, found] at present
      contradiction

private theorem fillInputs_data (inputs : List (Nat × Atom)) (atom : Atom)
    (data : MeTTaData.DataAtom atom) : Control.fillInputs inputs atom = atom := by
  induction inputs with
  | nil => rfl
  | cons entry rest ih =>
    simpa only [Control.fillInputs, Control.substituteName_data data] using ih

private theorem fillInputs_matched_get (first : Nat) (environment : Env)
    (index : Nat) (inside : index < environment.length) :
    Control.fillInputs (matchedInputs first environment) (.var (freshName (first + index))) =
      MeTTaData.encode environment[index].2 := by
  induction environment generalizing first index with
  | nil => simp at inside
  | cons entry rest ih =>
    cases index with
    | zero =>
      simpa only [Nat.add_zero, matchedInputs, Control.fillInputs,
        Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName,
        if_true, List.getElem_cons_zero] using
        fillInputs_data (matchedInputs (first + 1) rest) (MeTTaData.encode entry.2)
          (MeTTaData.encode_data entry.2)
    | succ index =>
      have different : freshName (first + (index + 1)) ≠ freshName first := by
        intro same
        have impossible := freshName_injective same
        omega
      simpa only [matchedInputs, Control.fillInputs,
        Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName,
        if_neg different, List.getElem_cons_succ, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using
        ih (first + 1) index (by simpa using inside)

theorem filled_matched_names (first : Nat) (environment : Env) :
    (namesForMatch first environment).map (fun entry =>
      (entry.1, Control.fillInputs (matchedInputs first environment) entry.2)) =
    environment.map (fun entry => (entry.1, MeTTaData.encode entry.2)) := by
  apply List.ext_getElem
  · simp [namesForMatch]
  · intro index leftBound rightBound
    simp only [List.getElem_map, namesForMatch, List.getElem_mapIdx]
    rw [fillInputs_matched_get]

/-- Selecting a generated row fills its actual source environment throughout
the compiled body. Nested binders and calls retain their allocated names. -/
theorem matched_expression_materialization
    (program : Program) (parameters arguments : List Term) (first : Nat) (sourceFuel : Atom) (fuelData : MeTTaData.DataAtom sourceFuel)
    (sourceBindings : Env) (source : Term)
    (sourceMatch : matchTerms parameters arguments = some sourceBindings)
    (rename : String → String) (injective : Function.Injective rename)
    (fresh : Atom) (renamed : AlphaRenameAtomRel rename (patterns parameters first).1.1 fresh)
    (incoming matched output : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (fixed : Metta.instantiate incoming (renBy rename (toLeaTTaAtom
      (expression program (patterns parameters first).1.2 sourceFuel
        source (patterns parameters first).2).1)) = renBy rename (toLeaTTaAtom
      (expression program (patterns parameters first).1.2 sourceFuel
        source (patterns parameters first).2).1))
    (aligned : ValuationFor (leaClassSolution output ∘ rename) first sourceBindings)
    (matching : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (MeTTaData.encodeItems arguments)) (toLeaTTaAtom fresh))
    (merging : output ∈ Metta.Bindings.merge incoming matched) :
    Metta.instantiate output (renBy rename (toLeaTTaAtom
      (expression program (patterns parameters first).1.2 sourceFuel
        source (patterns parameters first).2).1)) = renBy rename (toLeaTTaAtom
      (expression program (sourceBindings.map (fun entry =>
        (entry.1, MeTTaData.encode entry.2))) sourceFuel
        source (patterns parameters first).2).1) := by
  rw [matched_body_materialization parameters arguments first sourceBindings sourceMatch
    rename fresh renamed _ incoming matched output stored fixed aligned matching merging]
  rw [Control.expression_runtime_inputs program _ _ _ (matchedInputs first sourceBindings)
    _ rename injective]
  · rw [patterns_names_of_match parameters arguments sourceBindings sourceMatch,
      filled_matched_names, fillInputs_data _ _ fuelData]
  · intro entry member
    rw [patterns_end_of_match parameters arguments sourceBindings sourceMatch]
    exact (matchedInputs_bounds first sourceBindings entry member).2.1
  · intro entry member name occurrence
    exact False.elim (data_has_no_variables
      (matchedInputs_bounds first sourceBindings entry member).2.2 name occurrence)
  · intro entry member
    exact data_atom_runtime_closed (matchedInputs_bounds first sourceBindings entry member).2.2
  · rw [patterns_names_of_match parameters arguments sourceBindings sourceMatch,
      patterns_end_of_match parameters arguments sourceBindings sourceMatch]
    exact namesForMatch_scope sourceBindings first
  · intro name occurrence
    exact False.elim (data_has_no_variables fuelData name occurrence)


/-- A matched source variable returns its source value through the freshly
renamed generated body. This composes the real match/merge invariant, emitted
name table, materialization, fuel guard and caller return. -/
theorem matched_variable_execution (program : Program) (parameters arguments : List Term)
    (bindings : Env) (first remaining fuel : Nat)
    {spec : Mettapedia.Languages.MeTTa.HE.Bindings}
    {incoming matched output : Metta.Bindings} {rename : String → String} {fresh : Atom}
    (invariant : LeaQueryOpBindingInvariant spec incoming)
    (injective : Function.Injective rename)
    (renamed : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.AlphaRenameAtomRel rename
      (patterns parameters first).1.1 fresh)
    (sourceMatch : matchTerms parameters arguments = some bindings)
    (matchedHere : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (MeTTaData.encodeItems arguments)) (toLeaTTaAtom fresh))
    (mergedHere : output ∈ Metta.Bindings.merge incoming matched)
    (acyclic : output.hasLoop = false)
    (name label target : String) (payload : Term)
    (found : (patterns parameters first).1.2.find? (fun entry => entry.1 == name) =
      some (label, .var target))
    (expected : bindings.lookup name = some payload)
    (environment : MinEnv) (state : St) (caller : Frame) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate output
      (.var (rename (freshName (patterns parameters first).2))) =
        .var (rename (freshName (patterns parameters first).2))) :
    interpretFuel environment (fuel + 10) state
        (⟨atomToStack (renBy rename (toLeaTTaAtom (call "function"
          [(expression program (patterns parameters first).1.2
            (.grounded (.int (remaining + 1))) (.var name)
            (patterns parameters first).2).1]))) (caller :: continuation), output⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation)
          (toLeaTTaAtom (value (MeTTaData.encode payload))) output :: rest) done := by
  have lookup := alpha_patterns_runtime_lookup parameters arguments first invariant renamed
    sourceMatch matchedHere mergedHere acyclic name label target payload found expected
  have bounded : UsesBefore (patterns parameters first).2 (.var target) := by
    have member := List.mem_of_find?_eq_some found
    rw [patterns_names_of_match parameters arguments bindings sourceMatch] at member
    rw [patterns_end_of_match parameters arguments bindings sourceMatch]
    exact namesForMatch_scope bindings first (label, .var target) member
  have resultBound : UsesBefore ((patterns parameters first).2 + 1) (value (.var target)) := by
    simpa [value] using bounded.mono (Nat.le_succ _)
  have resolved : Metta.instantiate output (renBy rename (toLeaTTaAtom (value (.var target)))) =
      toLeaTTaAtom (value (MeTTaData.encode payload)) := by
    simpa only [value, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
      List.map_cons, List.map_nil, Metta.instantiate, Metta.Bindings.resolveAtom] using
      congrArg (fun value => Metta.Atom.expr [.sym "nik:Value", value]) lookup
  have closed : (toLeaTTaAtom (value (MeTTaData.encode payload))).vars = [] := by
    have dataClosed := data_atom_runtime_closed (MeTTaData.encode_data payload)
    simp [value, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars, dataClosed]
  simpa only [expression, found] using
    renamed_withFuel_return_to_caller environment state output rename injective
      (value (.var target)) (toLeaTTaAtom (value (MeTTaData.encode payload)))
      (patterns parameters first).2 remaining fuel caller continuation rest done
      groundings privateRemaining resultBound resolved closed

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
