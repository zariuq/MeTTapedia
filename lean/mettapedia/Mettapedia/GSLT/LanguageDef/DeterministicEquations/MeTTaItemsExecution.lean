import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaExpressionExecution

/-!
# Execution of compiled argument lists

The existing MeTTa interpreter evaluates emitted arguments in source order.
Each returned value materializes the remaining continuation without capturing
caller variables. Refusal and source exhaustion bypass the remaining arguments.
Embedded instructions and direct returns have distinct, proved control paths.
The same composition establishes source list construction.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal (substituteName)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Metta.Minimal

namespace Execution

/-- Syntactic obligations of the compiler's argument continuations. These
are allocation, substitution and control-form laws, not execution assumptions. -/
structure ContinuationSyntax (next : List Atom → Emit Atom) : Prop where
  scope : ∀ first arguments, (∀ atom ∈ arguments, UsesBefore first atom) →
    first ≤ (next arguments first).2 ∧ UsesBefore (next arguments first).2 (next arguments first).1
  substitute : ∀ index first, index < first → ∀ replacement arguments,
    (∀ atom ∈ arguments, UsesBefore first atom) →
    (substituteName (freshName index) replacement (next arguments first).1,
      (next arguments first).2) =
      next (arguments.map (substituteName (freshName index) replacement)) first
  controlled : ∀ first arguments rename,
    isEmbeddedOp (renBy rename (toLeaTTaAtom (next arguments first).1)) = true ∨
      ∃ payload, renBy rename (toLeaTTaAtom (next arguments first).1) = .expr [.sym "return", payload]

/-- Prefixing already computed guest data preserves the continuation laws. -/
theorem ContinuationSyntax.prepend {next : List Atom → Emit Atom}
    (formed : ContinuationSyntax next) (payload : Term) :
    ContinuationSyntax (fun arguments => next (MeTTaData.encode payload :: arguments)) where
  scope first arguments bounded := formed.scope first _ (by
    simpa using And.intro (usesBefore_data first payload) bounded)
  substitute index first before replacement arguments bounded := by
    simpa only [List.map_cons, Control.substituteName_encoded] using
      formed.substitute index first before replacement (MeTTaData.encode payload :: arguments)
        (by simpa using And.intro (usesBefore_data first payload) bounded)
  controlled first arguments rename := formed.controlled first _ rename

/-- Argument-list code retains its embedded-instruction or direct-return shape. -/
theorem expressions_runtime_controlled (program : Program) (names : Names) (fuel : Atom)
    (terms : List Term) (next : List Atom → Emit Atom)
    (controlled : ∀ first arguments rename,
      isEmbeddedOp (renBy rename (toLeaTTaAtom (next arguments first).1)) = true ∨
        ∃ payload, renBy rename (toLeaTTaAtom (next arguments first).1) = .expr [.sym "return", payload])
    (first : Nat) (rename : String → String) :
    isEmbeddedOp (renBy rename (toLeaTTaAtom
      (expressions program names fuel terms next first).1)) = true ∨
      ∃ payload, renBy rename (toLeaTTaAtom (expressions program names fuel terms next first).1) =
        .expr [.sym "return", payload] := by
  cases terms with
  | nil => simpa only [expressions] using controlled first [] rename
  | cons head rest =>
    apply Or.inl
    rw [expressions]
    change isEmbeddedOp (renBy rename (toLeaTTaAtom
      (call "chain" [_, _, _]))) = true
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil, isEmbeddedOp]
    rfl

/-- Filling an earlier operand commutes with all remaining arguments and
with their actual generated continuation. -/
theorem expressions_runtime_substitution (program : Program) (names : Names)
    (sourceFuel replacement : Atom) (terms : List Term)
    (next changed : List Atom → Emit Atom) (index first : Nat)
    (rename : String → String) (injective : Function.Injective rename)
    (closed : (toLeaTTaAtom replacement).vars = []) (before : index < first)
    (namesBound : ∀ entry ∈ names, UsesBefore first entry.2)
    (fuelBound : UsesBefore first sourceFuel)
    (nextBound : ∀ start, first ≤ start → ∀ arguments,
      (∀ atom ∈ arguments, UsesBefore start atom) →
      start ≤ (next arguments start).2 ∧ UsesBefore (next arguments start).2 (next arguments start).1)
    (nextSame : ∀ start, first ≤ start → ∀ arguments,
      (∀ atom ∈ arguments, UsesBefore start atom) →
      (substituteName (freshName index) replacement (next arguments start).1,
        (next arguments start).2) =
        changed (arguments.map (substituteName (freshName index) replacement)) start) :
    Metta.Subst.apply [(rename (freshName index), toLeaTTaAtom replacement)]
      (renBy rename (toLeaTTaAtom (expressions program names sourceFuel terms next first).1)) =
    renBy rename (toLeaTTaAtom (expressions program
      (names.map (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)))
      (substituteName (freshName index) replacement sourceFuel) terms changed first).1) := by
  have transported := Control.fillInputs_runtime [(index, replacement)]
    (expressions program names sourceFuel terms next first).1 rename injective
    (by simpa only [List.mem_singleton] using fun entry equal => equal ▸ closed)
  simp only [List.map_cons, List.map_nil, Control.fillInputs] at transported
  rw [transported]
  exact congrArg (fun emitted : Atom × Nat => renBy rename (toLeaTTaAtom emitted.1))
    (Control.expressions_substitution program names sourceFuel replacement terms next changed
      index first before namesBound fuelBound nextBound nextSame)

/-- A pending continuation mentions no allocated child variable. Its only
older input is the receiver allocated before that child. -/
theorem expressions_excludes_unused_input (program : Program) (sourceBindings : Env)
    (sourceFuel index first receiver : Nat) (terms : List Term)
    (next : List Atom → Emit Atom) (formed : ContinuationSyntax next)
    (before : index < first) (receiverBefore : receiver < first) (different : index ≠ receiver) :
    ¬ AtomOccurs (expressions program
      (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int sourceFuel)) terms
      (fun arguments => next (.var (freshName receiver) :: arguments)) first).1 (freshName index) := by
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  have namesBound (start : Nat) : ∀ entry ∈ names, UsesBefore start entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact usesBefore_data start row.2
  have receiverSame : substituteName (freshName index) (.symbol "") (.var (freshName receiver)) =
      .var (freshName receiver) := by
    simp only [substituteName, if_neg (fun same => different (freshName_injective same).symm)]
  have transformed := congrArg Prod.fst (Control.expressions_substitution program names
    (.grounded (.int sourceFuel)) (.symbol "") terms
    (fun arguments => next (.var (freshName receiver) :: arguments))
    (fun arguments => next (.var (freshName receiver) :: arguments))
    index first before (namesBound first) (usesBefore_grounded first _) (by
      intro start later arguments bounded
      exact formed.scope start _ (by simpa using (And.intro
        ((usesBefore_freshName start receiver).mpr (by omega)) bounded))) (by
      intro start later arguments bounded
      simpa only [List.map_cons, receiverSame] using formed.substitute index start
        (by omega) (.symbol "") (.var (freshName receiver) :: arguments)
        (by simpa using And.intro ((usesBefore_freshName start receiver).mpr (by omega)) bounded)))
  have namesSame : names.map (fun entry =>
      (entry.1, substituteName (freshName index) (.symbol "") entry.2)) = names := by
    simp only [names, List.map_map, Function.comp_def, Control.substituteName_encoded]
  simp only [namesSame, substituteName] at transformed
  exact Control.symbol_substitution_fixed_excludes _ _ transformed

/-- A completed argument fills its pending receiver throughout the remaining
arguments and final continuation, preserving the allocation state. -/
theorem expressions_receiver_substitution (program : Program) (sourceBindings : Env)
    (sourceFuel receiver first : Nat) (terms : List Term)
    (next : List Atom → Emit Atom) (formed : ContinuationSyntax next)
    (payload : Term) (before : receiver < first)
    (rename : String → String) (injective : Function.Injective rename) :
    Metta.Subst.apply [(rename (freshName receiver), toLeaTTaAtom (MeTTaData.encode payload))]
      (renBy rename (toLeaTTaAtom (expressions program
        (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
        (.grounded (.int sourceFuel)) terms
        (fun arguments => next (.var (freshName receiver) :: arguments)) first).1)) =
    renBy rename (toLeaTTaAtom (expressions program
      (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int sourceFuel)) terms
      (fun arguments => next (MeTTaData.encode payload :: arguments)) first).1) := by
  have namesBound : ∀ entry ∈ sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)),
      UsesBefore first entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact usesBefore_data first row.2
  have result := expressions_runtime_substitution program _ (.grounded (.int sourceFuel))
    (MeTTaData.encode payload) terms
    (fun arguments => next (.var (freshName receiver) :: arguments))
    (fun arguments => next (MeTTaData.encode payload :: arguments)) receiver first rename injective
    (data_atom_runtime_closed (MeTTaData.encode_data payload)) before namesBound
    (usesBefore_grounded first _) (by
      intro start later arguments bounded
      exact formed.scope start _ (by simpa using (And.intro
        ((usesBefore_freshName start receiver).mpr (by omega)) bounded))) (by
      intro start later arguments bounded
      simpa only [List.map_cons, substituteName, if_true] using formed.substitute receiver start
        (by omega) (MeTTaData.encode payload) (.var (freshName receiver) :: arguments)
        (by simpa using And.intro ((usesBefore_freshName start receiver).mpr (by omega)) bounded))
  simpa only [List.map_map, Function.comp_def, Control.substituteName_encoded, substituteName] using result

/-- A selected return branch is already at the enclosing handler. At a
positive budget its selection takes exactly the step needed to enter the
same return directly; it need not be treated as an embedded instruction. -/
theorem renamed_resultBranches_value_enters_return (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (rename : String → String) (payload body : Atom) (name : String)
    (actual : Metta.Atom) (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (fuel : Nat) (positive : 1 ≤ fuel) (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (stored : ClosedValueBindings bindings) (closed : (toLeaTTaAtom payload).vars = [])
    (fresh : Metta.Bindings.lookupVal bindings (rename name) = none)
    (fixed : Metta.instantiate bindings (renBy rename (toLeaTTaAtom body)) = renBy rename (toLeaTTaAtom body))
    (returnedShape : Metta.Subst.apply [(rename name, toLeaTTaAtom payload)]
      (renBy rename (toLeaTTaAtom body)) = .expr [.sym "return", actual]) :
    let output := Metta.Bindings.addValRaw bindings (rename name) (toLeaTTaAtom payload)
    let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
    interpretFuel environment fuel state
      (⟨atomToStack (renBy rename (toLeaTTaAtom
        (resultBranches (value payload) (.var name) body))) (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (⟨atomToStack (.expr [.sym "return", actual]) (parent :: continuation), output⟩ :: rest) done := by
  intro output parent
  have materialized : Metta.instantiate output (renBy rename (toLeaTTaAtom body)) =
      .expr [.sym "return", actual] := by
    rw [instantiate_add_closed_value bindings (rename name) (toLeaTTaAtom payload)
      _ stored closed fresh, fixed, returnedShape]
  let otherwise := renBy rename (toLeaTTaAtom
    (selectBranches (value payload)
      [(.symbol "nik:Failure", returned (.symbol "nik:Failure")),
       (.symbol "nik:Exhausted", returned (.symbol "nik:Exhausted"))]
      (returned (.symbol "nik:Malformed"))))
  have shape : renBy rename (toLeaTTaAtom (resultBranches (value payload) (.var name) body)) =
      .expr [.sym "unify", .expr [.sym "nik:Value", toLeaTTaAtom payload],
        .expr [.sym "nik:Value", .var (rename name)], renBy rename (toLeaTTaAtom body), otherwise] := by
    simp only [otherwise, resultBranches, selectBranches, List.foldr_cons, List.foldr_nil,
      value, call, returned, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]
    rw [renBy_eq_self_of_vars_nil rename _ closed]
  have selected := unify_tagged_selects environment state bindings "nik:Value" (toLeaTTaAtom payload)
    (renBy rename (toLeaTTaAtom body)) otherwise (rename name) parent continuation (fuel - 1) rest done
    closed ((stored.toValueBindings.classValues_lookupVal _).1 fresh)
    (addValRaw_closed closed stored).hasLoop_false
  rw [materialized] at selected
  have returnedRun := return_enters_handler environment state output parentBody actual scope continuation
    (fuel - 1) rest done
  rw [shape]
  simpa only [show fuel - 1 + 1 = fuel by omega] using selected.trans returnedRun.symm

/-- The first successful argument supplies the actual value to all later
arguments. The receiver and pending continuation are protected by their
allocation intervals and remain visible to recursive freshening. -/
theorem expressions_cons_value (program : Program) (environment : MinEnv)
    (sourceBindings : Env) (sourceFuel : Nat) (head : Term) (restTerms : List Term)
    (next : List Atom → Emit Atom) (formed : ContinuationSyntax next)
    (payload : Term) (result : Outcome)
    (headRun : ExpressionExecutes program environment sourceFuel sourceBindings head (.value payload))
    (tailRun : CompiledExecutes environment
      (expressions program (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
        (.grounded (.int sourceFuel)) restTerms
        (fun arguments => next (MeTTaData.encode payload :: arguments))) result) :
    CompiledExecutes environment
      (expressions program (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
        (.grounded (.int sourceFuel)) (head :: restTerms) next) result := by
  intro first rename injective state noExtra noImports incoming stored invariant parentBody scope continuation code fresh
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  let assigned := expression program names (.grounded (.int sourceFuel)) head (first + 1)
  let target := Atom.var (freshName first)
  let tail := expressions program names (.grounded (.int sourceFuel)) restTerms
    (fun arguments => next (target :: arguments)) assigned.2
  let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
  let sourceCall := renBy rename (toLeaTTaAtom (call "function" [assigned.1]))
  let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName tail.2)) target tail.1))
  let recipient : Frame :=
    {atom := .expr [.sym "chain", sourceCall, .var (rename (freshName tail.2)), template],
     ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template}
  have namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact MeTTaData.encode_data row.2
  have namesBound (start : Nat) : ∀ entry ∈ names, UsesBefore start entry.2 :=
    fun entry member key occurs => False.elim (data_has_no_variables (namesData entry member) key occurs)
  have headBound := expression_scope program names (.grounded (.int sourceFuel)) head
    (first + 1) (namesBound _) (usesBefore_grounded _ _)
  change first + 1 < assigned.2 ∧ UsesBefore assigned.2 assigned.1 at headBound
  have tailBound := expressions_scope program names (.grounded (.int sourceFuel)) restTerms
    (fun arguments => next (target :: arguments)) assigned.2 (namesBound _) (usesBefore_grounded _ _) (by
      intro start later arguments bounded
      exact formed.scope start _ (by simpa only [List.mem_cons, forall_eq_or_imp] using
        (And.intro ((usesBefore_freshName start first).mpr (by omega)) bounded)))
  change assigned.2 ≤ tail.2 ∧ UsesBefore tail.2 tail.1 at tailBound
  have codeShape : code = renBy rename (toLeaTTaAtom (bindResult assigned.1 target tail.1 tail.2).1) := by
    dsimp only [code]
    rw [expressions]
    rfl
  have allSubset : ∀ key ∈ (renBy rename (toLeaTTaAtom assigned.1)).vars ++
      (renBy rename (toLeaTTaAtom target)).vars ++ (renBy rename (toLeaTTaAtom tail.1)).vars,
      key ∈ code.vars := by
    intro key member
    rw [codeShape]
    change key ∈ (renBy rename (toLeaTTaAtom (call "chain" [_, _, _]))).vars
    simp only [resultBranches, selectBranches, List.foldr_cons, List.foldr_nil, call, value,
      returned, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      Metta.Atom.vars, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    tauto
  have operandSubset : ∀ key ∈ (renBy rename (toLeaTTaAtom assigned.1)).vars, key ∈ code.vars :=
    fun key member => allSubset key (List.mem_append_left _ (List.mem_append_left _ member))
  have waitingSubset : ∀ key ∈ (renBy rename (toLeaTTaAtom target)).vars ++
      (renBy rename (toLeaTTaAtom tail.1)).vars, key ∈ code.vars := by
    intro key member
    apply allSubset key
    simpa only [List.mem_append] using Or.elim (List.mem_append.mp member)
      (fun h => Or.inl (Or.inr h)) Or.inr
  have waitingDisjoint : ∀ key ∈ (renBy rename (toLeaTTaAtom target)).vars ++
      (renBy rename (toLeaTTaAtom tail.1)).vars,
      key ∉ (renBy rename (toLeaTTaAtom assigned.1)).vars := by
    intro key waiting child
    obtain ⟨index, lower, upper, same⟩ := Control.renamed_expression_data_name_bounds program names
      (.grounded (.int sourceFuel)) head (first + 1) rename namesData (.grounded _) key child
    change index < assigned.2 at upper
    rcases List.mem_append.mp waiting with receiver | pending
    · have receiverSame : key = rename (freshName first) := by
        simpa only [target, toLeaTTaAtom, renBy, Metta.Atom.vars, List.mem_singleton] using receiver
      have := freshName_injective (injective (receiverSame.symm.trans same))
      omega
    · have absent := expressions_excludes_unused_input program sourceBindings sourceFuel index
        assigned.2 first restTerms next formed upper (by omega) (by omega)
      rw [renBy_vars] at pending
      obtain ⟨original, occurs, spelling⟩ := List.mem_map.mp pending
      have originalSame := injective (spelling.trans same)
      exact absent (originalSame ▸ atomOccurs_of_mem_translated_vars occurs)
  obtain ⟨middleState, middle, operandCost, operandThreshold, middleWorld, middleStored,
      middleInvariant, operandPreserved, operandExecution⟩ :=
    expression_as_operand program environment sourceFuel sourceBindings head (.value payload) headRun
      (first + 1) rename injective state noExtra noImports incoming stored invariant recipient
      (parent :: continuation) (fun key member => fresh key (operandSubset key member))
  have pendingPrivate : ∀ key ∈ (renBy rename (toLeaTTaAtom target)).vars ++
      (renBy rename (toLeaTTaAtom tail.1)).vars, Metta.Bindings.lookupVal middle key = none := by
    intro key member
    exact operandPreserved key
      (bindResult_waiting_variables_live rename assigned.1 target tail.1 tail.2
        (parent :: continuation) key member) (waitingDisjoint key member)
      (fresh key (waitingSubset key member))
  have receiverPrivate : Metta.Bindings.lookupVal middle (rename (freshName first)) = none :=
    pendingPrivate _ (List.mem_append_left _ (by simp [target, toLeaTTaAtom, Metta.Atom.vars]))
  have tailPrivate : ∀ key ∈ (renBy rename (toLeaTTaAtom tail.1)).vars,
      Metta.Bindings.lookupVal middle key = none :=
    fun key member => pendingPrivate key (List.mem_append_right _ member)
  let output := Metta.Bindings.addValRaw middle (rename (freshName first))
    (toLeaTTaAtom (MeTTaData.encode payload))
  let entered := renBy rename (toLeaTTaAtom (expressions program names
    (.grounded (.int sourceFuel)) restTerms
    (fun arguments => next (MeTTaData.encode payload :: arguments)) assigned.2).1)
  have filled := expressions_receiver_substitution program sourceBindings sourceFuel first
    assigned.2 restTerms next formed payload (by omega) rename injective
  change Metta.Subst.apply [(rename (freshName first), toLeaTTaAtom (MeTTaData.encode payload))]
    (renBy rename (toLeaTTaAtom tail.1)) = entered at filled
  have control := expressions_runtime_controlled program names (.grounded (.int sourceFuel)) restTerms
    (fun arguments => next (MeTTaData.encode payload :: arguments))
    (fun start arguments rename => formed.controlled start _ rename) assigned.2 rename
  change isEmbeddedOp entered = true ∨ ∃ actual, entered = .expr [.sym "return", actual] at control
  let branchSteps := if isEmbeddedOp entered then 2 else 0
  have outputStored : ClosedValueBindings output :=
    addValRaw_closed (data_atom_runtime_closed (MeTTaData.encode_data payload)) middleStored
  have outputInvariant : LeaRuntimeBindingInvariant output :=
    fresh_closed_value_preserves_runtime middle (rename (freshName first))
      (toLeaTTaAtom (MeTTaData.encode payload)) middleStored middleInvariant
      (data_atom_runtime_closed (MeTTaData.encode_data payload))
      (toLeaTTaAtom_noFloat _) receiverPrivate
  have enters (fuel : Nat) (positive : 1 ≤ fuel) (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
      interpretFuel environment (fuel + branchSteps) middleState
        (⟨atomToStack (renBy rename (toLeaTTaAtom
          (resultBranches (value (MeTTaData.encode payload)) target tail.1)))
          (parent :: continuation), middle⟩ :: rest) done =
      interpretFuel environment fuel middleState
        (⟨atomToStack entered (parent :: continuation), output⟩ :: rest) done := by
    rcases control with embedded | ⟨actual, returnedShape⟩
    · have execution := (renamed_resultBranches_value_enters environment middleState middle rename
        (MeTTaData.encode payload) tail.1 (freshName first) parentBody scope continuation fuel rest done
        middleStored (data_atom_runtime_closed (MeTTaData.encode_data payload)) receiverPrivate
        (instantiate_unassigned middle middleStored _ tailPrivate) (filled ▸ embedded)).2.2.2
      simpa only [filled, branchSteps, embedded, if_true] using execution
    · have execution := renamed_resultBranches_value_enters_return environment middleState middle rename
        (MeTTaData.encode payload) tail.1 (freshName first) actual parentBody scope continuation fuel positive
        rest done middleStored (data_atom_runtime_closed (MeTTaData.encode_data payload)) receiverPrivate
        (instantiate_unassigned middle middleStored _ tailPrivate) (filled.trans returnedShape)
      have notEmbedded : isEmbeddedOp entered = false := by rw [returnedShape]; rfl
      have stepsZero : branchSteps = 0 := by simp only [branchSteps, notEmbedded, Bool.false_eq_true, if_false]
      simpa only [stepsZero, Nat.add_zero, returnedShape] using execution
  have materialized := instantiate_add_closed_value middle (rename (freshName first))
    (toLeaTTaAtom (MeTTaData.encode payload)) (renBy rename (toLeaTTaAtom tail.1))
    middleStored (data_atom_runtime_closed (MeTTaData.encode_data payload)) receiverPrivate
  rw [instantiate_unassigned middle middleStored _ tailPrivate, filled] at materialized
  have fixed : Metta.instantiate output entered = entered := by
    rw [← materialized, instantiate_closed_value_bindings_idempotent outputStored]
  have enteredSubset : ∀ key ∈ entered.vars, key ∈ code.vars := by
    intro key member
    rw [← filled] at member
    exact waitingSubset key (List.mem_append_right _
      (closed_substitution_vars_subset _ _ _ (data_atom_runtime_closed (MeTTaData.encode_data payload)) key member))
  have enteredPrivate : ∀ key ∈ entered.vars, Metta.Bindings.lookupVal output key = none := by
    intro key member
    apply outputStored.toValueBindings.lookup_none_of_not_key
    intro storedKey
    exact fixed_closed_bindings_private output outputStored entered fixed key member
      (bindingValueKey_mem_vars storedKey)
  obtain ⟨finalState, finalBindings, tailCost, tailThreshold, finalWorld, finalStored,
      finalInvariant, tailPreserved, tailExecution⟩ :=
    tailRun assigned.2 rename injective middleState (by rw [middleWorld]; exact noExtra)
      (by rw [middleWorld]; exact noImports) output outputStored outputInvariant
      parentBody scope continuation enteredPrivate
  refine ⟨finalState, finalBindings, tailCost + branchSteps + 2 + operandCost,
    max (max operandThreshold tailThreshold) 1, finalWorld.trans middleWorld, finalStored, finalInvariant, ?_, ?_⟩
  · intro key live absent unassigned
    apply tailPreserved key live (fun member => absent (enteredSubset key member))
    have middlePrivate := operandPreserved key (List.mem_append_right _ live)
      (fun member => absent (operandSubset key member)) unassigned
    have different : key ≠ rename (freshName first) := by
      intro same
      exact absent (waitingSubset key (List.mem_append_left _ (by
        simpa only [target, toLeaTTaAtom, renBy, Metta.Atom.vars, List.mem_singleton] using same)))
    exact (lookup_add_other middle _ key _ different).trans middlePrivate
  · intro fuel enough rest done
    have bindRun := renamed_bindResult_of_operand_execution environment state middleState incoming middle
      rename injective assigned.1 (value (MeTTaData.encode payload)) target tail.1 tail.2
      operandCost (fuel + tailCost + branchSteps) parent continuation rest done
      (by simpa only [observation] using observation_closed (.value payload))
      ((usesBefore_freshName tail.2 first).mpr (by omega)) tailBound.2 (by
        simpa only [recipient, parent, sourceCall, template, target, tail, assigned, names,
          call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil, observation,
          Nat.add_assoc] using operandExecution (fuel + tailCost + branchSteps + 2) (by omega) rest done)
    have enterRun := enters (fuel + tailCost) (by omega) rest done
    have finalRun := tailExecution fuel (by omega) rest done
    rw [codeShape]
    simpa only [Nat.add_assoc] using bindRun.trans (enterRun.trans finalRun)

/-- A stopped argument bypasses every later argument and the final
continuation. Source exhaustion is propagated separately from refusal. -/
theorem expressions_cons_stopped (program : Program) (environment : MinEnv)
    (sourceBindings : Env) (sourceFuel : Nat) (head : Term) (restTerms : List Term)
    (next : List Atom → Emit Atom) (formed : ContinuationSyntax next)
    (result : Outcome) (stopped : result = .failure ∨ result = .exhausted)
    (headRun : ExpressionExecutes program environment sourceFuel sourceBindings head result) :
    CompiledExecutes environment
      (expressions program (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
        (.grounded (.int sourceFuel)) (head :: restTerms) next) result := by
  obtain ⟨marker, markers, observed⟩ : ∃ marker : String,
      (marker = "nik:Failure" ∨ marker = "nik:Exhausted") ∧ observation result = .symbol marker := by
    rcases stopped with rfl | rfl
    · exact ⟨"nik:Failure", Or.inl rfl, rfl⟩
    · exact ⟨"nik:Exhausted", Or.inr rfl, rfl⟩
  intro first rename injective state noExtra noImports incoming stored invariant parentBody scope continuation code fresh
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  let assigned := expression program names (.grounded (.int sourceFuel)) head (first + 1)
  let target := Atom.var (freshName first)
  let tail := expressions program names (.grounded (.int sourceFuel)) restTerms
    (fun arguments => next (target :: arguments)) assigned.2
  let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
  let sourceCall := renBy rename (toLeaTTaAtom (call "function" [assigned.1]))
  let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName tail.2)) target tail.1))
  let recipient : Frame :=
    {atom := .expr [.sym "chain", sourceCall, .var (rename (freshName tail.2)), template],
     ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template}
  have namesBound (start : Nat) : ∀ entry ∈ names, UsesBefore start entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact usesBefore_data start row.2
  have headBound := expression_scope program names (.grounded (.int sourceFuel)) head
    (first + 1) (namesBound _) (usesBefore_grounded _ _)
  change first + 1 < assigned.2 ∧ UsesBefore assigned.2 assigned.1 at headBound
  have tailBound := expressions_scope program names (.grounded (.int sourceFuel)) restTerms
    (fun arguments => next (target :: arguments)) assigned.2 (namesBound _) (usesBefore_grounded _ _) (by
      intro start later arguments bounded
      exact formed.scope start _ (by simpa only [List.mem_cons, forall_eq_or_imp] using
        (And.intro ((usesBefore_freshName start first).mpr (by omega)) bounded)))
  change assigned.2 ≤ tail.2 ∧ UsesBefore tail.2 tail.1 at tailBound
  have codeShape : code = renBy rename (toLeaTTaAtom (bindResult assigned.1 target tail.1 tail.2).1) := by
    dsimp only [code]
    rw [expressions]
    rfl
  have operandSubset : ∀ key ∈ (renBy rename (toLeaTTaAtom assigned.1)).vars, key ∈ code.vars := by
    intro key member
    rw [codeShape]
    change key ∈ (renBy rename (toLeaTTaAtom (call "chain" [_, _, _]))).vars
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      Metta.Atom.vars, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil]
    tauto
  obtain ⟨nextState, output, operandCost, operandThreshold, world, outputStored,
      outputInvariant, operandPreserved, operandExecution⟩ :=
    expression_as_operand program environment sourceFuel sourceBindings head result headRun
      (first + 1) rename injective state noExtra noImports incoming stored invariant recipient
      (parent :: continuation) (fun key member => fresh key (operandSubset key member))
  let steps := if marker = "nik:Failure" then 3 else 5
  refine ⟨nextState, output, steps + 2 + operandCost, operandThreshold, world,
    outputStored, outputInvariant, ?_, ?_⟩
  · intro key live absent unassigned
    exact operandPreserved key (List.mem_append_right _ live)
      (fun member => absent (operandSubset key member)) unassigned
  · intro fuel enough rest done
    have bindRun := renamed_bindResult_of_operand_execution environment state nextState incoming output
      rename injective assigned.1 (.symbol marker) target tail.1 tail.2 operandCost (fuel + steps)
      parent continuation rest done (by simp [toLeaTTaAtom, Metta.Atom.vars])
      ((usesBefore_freshName tail.2 first).mpr (by omega)) tailBound.2 (by
        simpa only [observed, recipient, parent, sourceCall, template, target, tail, assigned, names,
          call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil] using
          operandExecution (fuel + steps + 2) (by omega) rest done)
    have stopRun := renamed_resultBranches_stopped_enters_handler environment nextState output
      target tail.1 rename marker markers parentBody scope continuation fuel rest done outputStored.hasLoop_false
    rw [codeShape]
    simpa only [observed, toLeaTTaAtom, steps, Nat.add_assoc] using bindRun.trans stopRun

/-- Every finite argument list executes from left to right. The only
execution premises are the smaller source-expression runs and the final
continuation on the values actually produced. -/
theorem expressions_executes (program : Program) (environment : MinEnv)
    (sourceBindings : Env) (sourceFuel : Nat) (terms : List Term) (ev : Env → Term → Outcome)
    (next : List Atom → Emit Atom) (formed : ContinuationSyntax next)
    (finish : List Term → Outcome)
    (elements : ∀ term ∈ terms, ExpressionExecutes program environment sourceFuel sourceBindings term
      (ev sourceBindings term))
    (nextRun : ∀ values, CompiledExecutes environment (next (values.map MeTTaData.encode)) (finish values)) :
    CompiledExecutes environment
      (expressions program (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
        (.grounded (.int sourceFuel)) terms next)
      (match evalItemsWith ev sourceBindings terms with | .values values => finish values | .stop outcome => outcome) := by
  induction terms generalizing next finish with
  | nil => simpa only [expressions, evalItemsWith, List.map_nil] using nextRun []
  | cons head rest ih =>
    rw [evalItemsWith]
    cases result : ev sourceBindings head with
    | value payload =>
      apply expressions_cons_value program environment sourceBindings sourceFuel head rest next formed payload
      · simpa only [result] using elements head (by simp)
      · have restRun := ih (fun values => next (MeTTaData.encode payload :: values)) (formed.prepend payload)
          (fun values => finish (payload :: values))
          (fun term member => elements term (List.mem_cons_of_mem head member)) (fun values => by
            simpa only [List.map_cons] using nextRun (payload :: values))
        cases restOutcome : evalItemsWith ev sourceBindings rest <;> simpa only [restOutcome] using restRun
    | failure =>
      exact expressions_cons_stopped program environment sourceBindings sourceFuel head rest next formed
        .failure (Or.inl rfl) (by simpa only [result] using elements head (by simp))
    | exhausted =>
      exact expressions_cons_stopped program environment sourceBindings sourceFuel head rest next formed
        .exhausted (Or.inr rfl) (by simpa only [result] using elements head (by simp))

/-- Returning a closed observation is a single actual interpreter step. -/
theorem compiled_return (environment : MinEnv) (result : Outcome) :
    CompiledExecutes environment (pure (returned (observation result))) result := by
  intro first rename _ state _ _ incoming stored invariant parentBody scope continuation code _
  refine ⟨state, incoming, 1, 0, rfl, stored, invariant, ?_, ?_⟩
  · intro key _ _ unassigned
    exact unassigned
  · intro fuel _ rest done
    have closed := observation_closed result
    have shape : code = .expr [.sym "return", toLeaTTaAtom (observation result)] := by
      change renBy rename (toLeaTTaAtom (returned (observation result))) = _
      simp only [returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]
      rw [renBy_eq_self_of_vars_nil rename _ closed]
    rw [shape]
    exact return_enters_handler environment state incoming parentBody _ scope continuation fuel rest done

/-- Lists and data-headed expressions use the same argument continuation. -/
theorem data_continuation_syntax (tag : String) :
    ContinuationSyntax (fun items => pure (returned (value (call tag [sequenceAtom items])))) where
  scope first arguments bounded := by
    refine ⟨le_rfl, ?_⟩
    change UsesBefore first (returned (value (call tag [sequenceAtom arguments])))
    simpa [returned, value] using usesBefore_sequence first arguments bounded
  substitute index first _ replacement arguments _ := by
    change (substituteName (freshName index) replacement
      (returned (value (call tag [sequenceAtom arguments]))), first) = _
    simp only [returned, value, Control.substituteName_call, List.map_cons, List.map_nil,
      Control.substituteName_sequence]
    rfl
  controlled first arguments rename := by
    apply Or.inr
    refine ⟨renBy rename (toLeaTTaAtom (value (call tag [sequenceAtom arguments]))), ?_⟩
    change renBy rename (toLeaTTaAtom (returned (value (call tag [sequenceAtom arguments])))) = _
    simp only [returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]


/-- The positive source guard enters its materialized body, then composes
with that body's execution. No runtime budget is identified with source fuel. -/
theorem withFuel_executes (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) (build : Atom → Emit Atom)
    (remaining : Nat) (result : Outcome)
    (bounded : ∀ first, first + 1 ≤ (build (.var (freshName first)) (first + 1)).2 ∧
      UsesBefore (build (.var (freshName first)) (first + 1)).2
        (build (.var (freshName first)) (first + 1)).1)
    (filled : ∀ first,
      substituteName (freshName first) (.grounded (.int remaining))
        (build (.var (freshName first)) (first + 1)).1 =
        (build (.grounded (.int remaining)) (first + 1)).1)
    (bodyRun : CompiledExecutes environment (build (.grounded (.int remaining))) result) :
    CompiledExecutes environment (withFuel (.grounded (.int (remaining + 1))) build) result := by
  intro first rename injective state noExtra noImports incoming stored invariant parentBody scope continuation code fresh
  let raw := build (.var (freshName first)) (first + 1)
  let entered := renBy rename (toLeaTTaAtom (build (.grounded (.int remaining)) (first + 1)).1)
  have rawSubset : ∀ key ∈ (renBy rename (toLeaTTaAtom raw.1)).vars, key ∈ code.vars := by
    intro key member
    change key ∈ (renBy rename (toLeaTTaAtom (call "chain" [_, _,
      call "unify" [_, _, _, call "chain" [_, _, raw.1]]]))).vars
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      Metta.Atom.vars, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil]
    tauto
  have privateRemaining : Metta.instantiate incoming (.var (rename (freshName first))) =
      .var (rename (freshName first)) := by
    apply instantiate_unassigned incoming stored
    intro key member
    have same : key = rename (freshName first) := by simpa [Metta.Atom.vars] using member
    subst key
    exact fresh _ (withFuel_remaining_occurs _ _ _ _)
  have transport := Control.fillInputs_runtime [(first, Atom.grounded (.int remaining))]
    raw.1 rename injective (by simp [toLeaTTaAtom, Metta.Atom.vars])
  simp only [List.map_cons, List.map_nil, Control.fillInputs] at transport
  rw [show substituteName (freshName first) (.grounded (.int remaining)) raw.1 =
    (build (.grounded (.int remaining)) (first + 1)).1 from filled first] at transport
  have enteredSubset : ∀ key ∈ entered.vars, key ∈ code.vars := by
    intro key member
    change key ∈ (renBy rename (toLeaTTaAtom (build (.grounded (.int remaining)) (first + 1)).1)).vars at member
    rw [← transport] at member
    exact rawSubset key (closed_substitution_vars_subset _ _ _
      (by simp [toLeaTTaAtom, Metta.Atom.vars]) key member)
  obtain ⟨nextState, output, cost, threshold, world, outputStored, outputInvariant,
      preserved, execution⟩ := bodyRun (first + 1) rename injective state noExtra noImports incoming
        stored invariant parentBody scope continuation (fun key member => fresh key (enteredSubset key member))
  refine ⟨nextState, output, cost + 8, threshold, world, outputStored, outputInvariant, ?_, ?_⟩
  · intro key live absent unassigned
    exact preserved key live (fun member => absent (enteredSubset key member)) unassigned
  · intro fuel enough rest done
    have guardRun := renamed_withFuel_positive_execution_in_frame environment state incoming rename
      injective build first remaining (fuel + cost) parentBody scope continuation rest done
      groundings privateRemaining (bounded first)
    dsimp only at guardRun
    change Metta.Subst.apply [(rename (freshName first), .gnd (.int remaining))]
      (renBy rename (toLeaTTaAtom raw.1)) = entered at transport
    rw [instantiate_unassigned incoming stored _ (fun key member => fresh key (rawSubset key member)),
      transport] at guardRun
    simpa only [Nat.add_assoc] using guardRun.trans (execution fuel enough rest done)

/-- The list constructor executes its elements and returns their encoded
values, using the same shared argument machinery as function calls. -/
theorem expression_list (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (remaining : Nat) (terms : List Term)
    (elements : ∀ term ∈ terms, ExpressionExecutes program environment remaining sourceBindings term
      (eval program host remaining sourceBindings term)) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings (.list terms)
      (eval program host (remaining + 1) sourceBindings (.list terms)) := by
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  let next : List Atom → Emit Atom := fun items => pure (returned (value (call "nik:List" [sequenceAtom items])))
  have formed : ContinuationSyntax next := data_continuation_syntax "nik:List"
  have namesBound (first : Nat) : ∀ entry ∈ names, UsesBefore first entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact usesBefore_data first row.2
  change CompiledExecutes environment (expression program names (.grounded (.int (remaining + 1))) (.list terms)) _
  rw [expression, eval, evalStep]
  apply withFuel_executes environment groundings (fun fuel => expressions program names fuel terms next) remaining
  · intro first
    exact expressions_scope program names (.var (freshName first)) terms next (first + 1)
      (namesBound _) ((usesBefore_freshName _ _).mpr (by omega))
      (fun start _ arguments bounded => formed.scope start arguments bounded)
  · intro first
    have transported := congrArg Prod.fst (Control.expressions_substitution program names
      (.var (freshName first)) (.grounded (.int remaining)) terms next next first (first + 1)
      (by omega) (namesBound _) ((usesBefore_freshName _ _).mpr (by omega))
      (fun start _ arguments bounded => formed.scope start arguments bounded)
      (fun start later arguments bounded => formed.substitute first start (by omega) _ arguments bounded))
    have namesSame : names.map (fun entry =>
        (entry.1, substituteName (freshName first) (.grounded (.int remaining)) entry.2)) = names := by
      simp only [names, List.map_map, Function.comp_def, Control.substituteName_encoded]
    simpa only [namesSame, substituteName, if_true] using transported
  · apply expressions_executes program environment sourceBindings remaining terms
      (eval program host remaining) next formed (fun values => .value (.list values)) elements
    intro values
    simpa only [next, sequenceAtom_encode, observation, MeTTaData.encode, call] using
      compiled_return environment (.value (.list values))

/-- Guest variables inside a payload remain data while list order is retained. -/
theorem list_payload_order_control (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) (payload : Term) :
    ExpressionExecutes program environment 2 [("x", payload)] (.list [.var "x", .sym "tail"])
      (.value (.list [payload, .sym "tail"])) := by
  have run := expression_list program host environment groundings [("x", payload)] 1
    [.var "x", .sym "tail"] (by
      intro term member
      rcases List.mem_cons.mp member with rfl | member
      · simpa [eval, evalStep, Env.lookup] using expression_variable program environment groundings [("x", payload)] "x" 0
      · have same := List.mem_singleton.mp member
        subst term
        exact expression_symbol program environment groundings [("x", payload)] "tail" 0)
  simpa [eval, evalStep, Env.lookup, evalItemsWith] using run

/-- Empty lists return successfully without spending fuel on an element. -/
theorem empty_list_control (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) :
    ExpressionExecutes program environment 1 [] (.list []) (.value (.list [])) := by
  simpa only [eval, evalStep, evalItemsWith] using
    expression_list program host environment groundings [] 0 [] (by simp)

/-- A nonempty list with no fuel for its first element reports exhaustion. -/
theorem list_exhaustion_control (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) :
    ExpressionExecutes program environment 1 [] (.list [.sym "value"]) .exhausted := by
  have run := expression_list program host environment groundings [] 0 [.sym "value"] (by
    intro term _
    exact expression_zero program environment groundings [] term)
  simpa only [eval, evalStep, evalItemsWith] using run

/-- A missing argument is refused, regardless of the later valid element. -/
theorem list_refusal_control (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) :
    ExpressionExecutes program environment 2 [] (.list [.var "missing", .sym "value"]) .failure := by
  have run := expression_list program host environment groundings [] 1 [.var "missing", .sym "value"] (by
    intro term member
    rcases List.mem_cons.mp member with rfl | member
    · simpa [eval, evalStep, Env.lookup] using expression_variable program environment groundings [] "missing" 0
    · have same := List.mem_singleton.mp member
      subst term
      exact expression_symbol program environment groundings [] "value" 0)
  simpa [eval, evalStep, evalItemsWith, Env.lookup] using run

/-- The final data continuation is a return, not an embedded operation.
The execution contract explicitly includes this separate control case. -/
theorem data_return_is_not_embedded (tag : String) (arguments : List Atom) (rename : String → String) :
    isEmbeddedOp (renBy rename (toLeaTTaAtom
      (returned (value (call tag [sequenceAtom arguments]))))) = false := by
  simp only [returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil, isEmbeddedOp]
  rfl

end Execution
end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
