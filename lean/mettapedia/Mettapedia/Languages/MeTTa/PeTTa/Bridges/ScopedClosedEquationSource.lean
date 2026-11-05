import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationSource

/-!
# Canonical named clauses from closed captured operands

The actual clause scan freshens a distinct list of formal variables and
extends the reached caller equations. Closed argument values instantiate
that fresh head without constraining an older unbound output. Neither a
chosen body execution nor a replacement formal-only frame is an assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars applyTypeValuation)
open HE.Spec.Type.Presentation (TypeSubst)
open ClosedOnceQueryFrame (FreshFor placed)

structure Definition where
  head : String
  formals : List String
  body : Atom
  distinct : formals.Nodup

#print axioms Definition.mk.congr_simp

def Definition.declaration (definition : Definition) : SpaceSemantics.Equation :=
  ⟨definition.head, definition.formals.map Atom.var, definition.body⟩

def formal (control : Control) (occurrence : Nat) (definition : Definition) (name : String) : String :=
  ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms definition.declaration) name

def formalNames (control : Control) (occurrence : Nat) (definition : Definition) : List String :=
  definition.formals.map (formal control occurrence definition)

def selected (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal) : Control :=
  {control with
    bindings := control.bindings ++ [(.expression (.symbol definition.head :: values),
      ClauseChoice.freshPattern control occurrence definition.declaration)]
    goals := .evaluate (ClauseChoice.freshBody control occurrence definition.declaration) destination :: older}

theorem formal_fresh (control : Control) (occurrence : Nat) (definition : Definition) (name : String) :
    FreshFor (formal control occurrence definition name) control.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings control _ (ClauseChoice.rename_fresh control occurrence _ name)

private theorem vars_list (names : List String) : TypeSubst.typeVarsList (names.map Atom.var) = names := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp [TypeSubst.typeVarsList, TypeSubst.typeVars, ih]

theorem clause_names (definition : Definition) :
    ClauseChoice.names (ClauseChoice.clauseAtoms definition.declaration) =
      definition.formals ++ TypeSubst.typeVars definition.body := by
  simp [ClauseChoice.names, ClauseChoice.clauseAtoms, ClauseChoice.pattern,
    Definition.declaration, TypeSubst.typeVars, TypeSubst.typeVarsList, vars_list]

theorem names_distinct (control : Control) (occurrence : Nat) (definition : Definition) :
    (formalNames control occurrence definition).Nodup := by
  apply definition.distinct.map_on
  intro first firstMember second secondMember same
  exact ClauseChoice.rename_injective_on control occurrence _
    (by rw [clause_names]; exact List.mem_append_left _ firstMember)
    (by rw [clause_names]; exact List.mem_append_left _ secondMember) same

theorem fresh_pattern (control : Control) (occurrence : Nat) (definition : Definition) :
    ClauseChoice.freshPattern control occurrence definition.declaration =
      .expression (.symbol definition.head :: (formalNames control occurrence definition).map Atom.var) := by
  simp [ClauseChoice.freshPattern, ClauseChoice.pattern, Definition.declaration,
    renameTypeVars, formalNames, formal, List.map_map]

theorem read_expression (environment : Environment) (atoms : List Atom) :
    read environment (.expression atoms) = .expression (atoms.map (read environment)) := by
  rw [read_eq_applyTypeValuation]
  simp only [applyTypeValuation]
  congr 1
  apply List.map_congr_left
  intro atom _
  exact (read_eq_applyTypeValuation environment atom).symm

theorem closed_names (atom : Atom) (closed : ∀ environment, read environment atom = atom) :
    (encode atom).freeVars = ∅ := by
  let ground : Environment := fun _ => encode (.symbol "closed")
  have fixed := congrArg encode (closed ground)
  simp only [EagerDFS.Destination.read, encode_decode] at fixed
  rw [← fixed]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro name present
  obtain ⟨sourceName, _, occurs⟩ :=
    (Mettapedia.Logic.LP.Subst.mem_freeVars_applyTerm (θ := ground) (t := encode atom) (x := name)).mp present
  simp [ground, encode, Mettapedia.Logic.LP.Term.freeVars] at occurs

private theorem read_update_self (environment : Environment) (name : String) (value : Atom) :
    read (Function.update environment name (encode value)) (.var name) = value := by
  simp only [EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm]
  exact (congrArg decode (Function.update_self name (encode value) environment)).trans (decode_encode value)

private def instantiate (environment : Environment) : List (String × Atom) → Environment
  | [] => environment
  | (name, value) :: rest => Function.update (instantiate environment rest) name (encode value)

private theorem instantiate_solves (environment : Environment) (bindings : Equations)
    (assignments : List (String × Atom)) (solved : Solves environment bindings)
    (fresh : ∀ pair ∈ assignments, FreshFor pair.1 bindings) :
    Solves (instantiate environment assignments) bindings := by
  induction assignments with
  | nil => exact solved
  | cons pair rest ih =>
    exact ClosedOnceQueryFrame.solves_update _ bindings pair.1 pair.2
      (fresh pair (by simp)) (ih (fun other member => fresh other (by simp [member])))

private theorem instantiate_preserves (environment : Environment) (assignments : List (String × Atom))
    (atom : Atom) (apart : ∀ pair ∈ assignments, pair.1 ∉ (encode atom).freeVars) :
    read (instantiate environment assignments) atom = read environment atom := by
  induction assignments with
  | nil => rfl
  | cons pair rest ih =>
    rw [instantiate, ClosedOnceQueryFrame.read_update _ pair.1 pair.2 atom (apart pair (by simp))]
    exact ih (fun other member => apart other (by simp [member]))

private theorem instantiate_read (environment : Environment) (assignments : List (String × Atom))
    (distinct : (assignments.map Prod.fst).Nodup) (name : String) (value : Atom)
    (member : (name, value) ∈ assignments) :
    read (instantiate environment assignments) (.var name) = value := by
  induction assignments with
  | nil => simp at member
  | cons pair rest ih =>
    obtain ⟨apart, restDistinct⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact read_update_self (instantiate environment rest) name value
    · have different : pair.1 ≠ name := by
        intro same
        apply apart
        rw [same]
        exact List.mem_map.mpr ⟨(name, value), later, rfl⟩
      rw [instantiate, ClosedOnceQueryFrame.read_update _ pair.1 pair.2 (.var name)
        (by simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using different)]
      exact ih restDistinct later

private theorem instantiate_values (environment : Environment) (names : List String) (values : List Atom)
    (sameLength : names.length = values.length) (distinct : names.Nodup) :
    (names.map Atom.var).map (read (instantiate environment (names.zip values))) = values := by
  have left := List.map_fst_zip (l₁ := names) (l₂ := values) (by omega)
  have right := List.map_snd_zip (l₁ := names) (l₂ := values) (by omega)
  have equality : (names.zip values).map (fun pair => read (instantiate environment (names.zip values)) (.var pair.1)) =
      (names.zip values).map Prod.snd := by
    apply List.map_congr_left
    intro pair member
    exact instantiate_read environment (names.zip values) (by rw [left]; exact distinct) pair.1 pair.2 member
  calc
    (names.map Atom.var).map (read (instantiate environment (names.zip values))) =
        ((names.zip values).map Prod.fst).map
          (fun name => read (instantiate environment (names.zip values)) (.var name)) := by
      rw [left]
      simp only [List.map_map, Function.comp_def]
    _ = (names.zip values).map Prod.snd := by
      simpa only [List.map_map, Function.comp_def] using equality
    _ = values := right

private theorem map_closed (values : List Atom)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value) (environment : Environment) :
    values.map (read environment) = values := by
  calc
    values.map (read environment) = values.map id :=
      List.map_congr_left (fun value member => closed value member environment)
    _ = values := List.map_id values

private theorem instantiated_readings (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (environment : Environment)
    (sameLength : values.length = definition.formals.length) (solved : Solves environment control.bindings) :
    let after := instantiate environment ((formalNames control occurrence definition).zip values)
    Solves after control.bindings ∧
      ((formalNames control occurrence definition).map Atom.var).map (read after) = values := by
  constructor
  · apply instantiate_solves _ _ _ solved
    intro pair member
    obtain ⟨name, _, renamed⟩ := List.mem_map.mp (List.of_mem_zip member).1
    rw [← renamed]
    exact formal_fresh control occurrence definition name
  · apply instantiate_values _ _ _ (by simpa [formalNames] using sameLength.symm)
    exact names_distinct control occurrence definition

theorem instantiated_model (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (sameLength : values.length = definition.formals.length)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value)
    (consistent : ∃ environment, Solves environment control.bindings) :
    ∃ environment, Solves environment control.bindings ∧
      read environment (.expression (.symbol definition.head :: values)) =
        read environment (ClauseChoice.freshPattern control occurrence definition.declaration) := by
  obtain ⟨environment, solved⟩ := consistent
  let after := instantiate environment ((formalNames control occurrence definition).zip values)
  obtain ⟨inherited, readings⟩ := instantiated_readings control occurrence definition values environment sameLength solved
  change ((formalNames control occurrence definition).map Atom.var).map (read after) = values at readings
  refine ⟨after, inherited, ?_⟩
  rw [fresh_pattern, read_expression, read_expression]
  have unchanged := map_closed values closed after
  simp only [List.map_cons, unchanged, readings]

theorem head_refined (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal)
    (sameLength : values.length = definition.formals.length)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value)
    (consistent : ∃ environment, Solves environment control.bindings) :
    refine control.bindings (.expression (.symbol definition.head :: values))
      (ClauseChoice.freshPattern control occurrence definition.declaration) =
      some (selected control occurrence definition values destination older).bindings :=
  (refine_iff _ _ _ _).mpr ⟨rfl, instantiated_model control occurrence definition values sameLength closed consistent⟩

theorem attempt_constructed (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal)
    (sameLength : values.length = definition.formals.length)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value)
    (consistent : ∃ environment, Solves environment control.bindings) :
    ClauseChoice.attempt control definition.head values destination older occurrence definition.declaration =
      some (selected control occurrence definition values destination older) := by
  apply (ClauseChoice.attempt_iff _ _ _ _ _ _ _ rfl _).mpr
  exact ⟨_, (refinement_iff _ _ _ _).mpr
    (head_refined control occurrence definition values destination older sameLength closed consistent), rfl⟩

theorem selected_consistent (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal)
    (sameLength : values.length = definition.formals.length)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value)
    (consistent : ∃ environment, Solves environment control.bindings) :
    ∃ environment, Solves environment (selected control occurrence definition values destination older).bindings :=
  ClosedOnceQueryFrame.refined_consistent _ _ _
    (head_refined control occurrence definition values destination older sameLength closed consistent)

/-- A retained caller name remains fresh when closed operands bind the
freshened clause formals. This does not turn an existing alias into a fresh
name: freshness of the original caller equations is required. -/
theorem selected_retained_fresh (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal) (name : String)
    (fresh : FreshFor name control.bindings) (retained : name ∈ control.support)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value) :
    FreshFor name (selected control occurrence definition values destination older).bindings := by
  intro equation member
  rcases List.mem_append.mp member with old | added
  · exact fresh equation old
  · cases List.mem_singleton.mp added
    constructor
    · rw [CapturedPatternSupport.mem_expression_names]
      rintro ⟨atom, present, occurs⟩
      rcases List.mem_cons.mp present with same | member
      · subst atom
        simp [encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
      · rw [closed_names atom (closed atom member)] at occurs
        exact Finset.notMem_empty _ occurs
    · rw [fresh_pattern, CapturedPatternSupport.mem_expression_names]
      rintro ⟨atom, present, occurs⟩
      rcases List.mem_cons.mp present with same | member
      · subst atom
        simp [encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
      · obtain ⟨renamed, renamedMember, rfl⟩ := List.mem_map.mp member
        obtain ⟨original, _, rfl⟩ := List.mem_map.mp renamedMember
        have same : name = formal control occurrence definition original := by
          simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
        apply ClauseChoice.rename_fresh control occurrence (ClauseChoice.clauseAtoms definition.declaration) original
        change formal control occurrence definition original ∈ control.support
        rw [← same]
        exact retained

theorem selected_readings (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal) (environment : Environment)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value)
    (solved : Solves environment (selected control occurrence definition values destination older).bindings) :
    ((formalNames control occurrence definition).map Atom.var).map (read environment) = values := by
  have linked := (solves_append_equation _ _ _ _).mp solved |>.2
  rw [fresh_pattern, read_expression, read_expression] at linked
  have unchanged := map_closed values closed environment
  simp only [List.map_cons, unchanged, Atom.expression.injEq, List.cons.injEq, true_and] at linked
  exact linked.symm

theorem selected_unbound (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal) (principal : Environment) (representative : String)
    (sameLength : values.length = definition.formals.length)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value)
    (resolved : resolve control.bindings = some principal) (unbound : read principal destination = .var representative)
    (retained : (encode destination).freeVars ⊆ control.support) :
    ∃ next name, resolve (selected control occurrence definition values destination older).bindings = some next ∧
      read next destination = .var name := by
  obtain ⟨next, nextResolved⟩ := resolve_complete
    (selected_consistent control occurrence definition values destination older sameLength closed ⟨principal, resolve_sound resolved⟩)
  have models : ∀ value : Bool, ∃ environment,
      Solves environment (selected control occurrence definition values destination older).bindings ∧
        read environment destination = Effects.boolean value := by
    intro value
    let later : Environment := Mettapedia.Logic.LP.Subst.single representative (encode (Effects.boolean value))
    let before : Environment := Mettapedia.Logic.LP.Subst.comp later principal
    let after := instantiate before ((formalNames control occurrence definition).zip values)
    have beforeSolved := ScopedMutationSource.solves_comp later principal control.bindings (resolve_sound resolved)
    obtain ⟨inherited, readings⟩ := instantiated_readings control occurrence definition values before sameLength beforeSolved
    change ((formalNames control occurrence definition).map Atom.var).map (read after) = values at readings
    refine ⟨after, (solves_append_equation _ _ _ _).mpr ⟨inherited, ?_⟩, ?_⟩
    · rw [fresh_pattern, read_expression, read_expression]
      have unchanged := map_closed values closed after
      simp only [List.map_cons, unchanged, readings]
    · have preserved : read after destination = read before destination := by
        apply instantiate_preserves
        intro pair member present
        obtain ⟨name, _, renamed⟩ := List.mem_map.mp (List.of_mem_zip member).1
        apply ClauseChoice.rename_fresh control occurrence (ClauseChoice.clauseAtoms definition.declaration) name
        change formal control occurrence definition name ∈ control.support
        rw [renamed]
        exact retained present
      rw [preserved, ScopedMutationSource.read_comp, unbound]
      simp [later, EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.single, Effects.boolean, decode]
  obtain ⟨name, reading⟩ := ScopedMutationSource.unbound_of_boolean_models _ next destination nextResolved models
  exact ⟨next, name, nextResolved, reading⟩

theorem choices_singleton (program : SpaceSemantics.Program) (control : Control) (occurrence : Nat)
    (definition : Definition) (values : List Atom) (destination : Atom) (older : List Goal)
    (sameLength : values.length = definition.formals.length)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value)
    (consistent : ∃ environment, Solves environment control.bindings)
    (row : program.equations[occurrence]? = some definition.declaration)
    (otherHeads : ∀ index equation, program.equations[index]? = some equation →
      index ≠ occurrence → equation.head ≠ definition.head) :
    ClauseChoice.choices program control definition.head values destination older =
      [(occurrence, selected control occurrence definition values destination older)] := by
  let next := selected control occurrence definition values destination older
  have chosen : ClauseChoice.trial program control definition.head values destination older occurrence = some next := by
    simp only [ClauseChoice.trial, row]
    exact attempt_constructed control occurrence definition values destination older sameLength closed consistent
  have refused (index : Nat) (different : index ≠ occurrence) :
      ClauseChoice.trial program control definition.head values destination older index = none := by
    cases found : program.equations[index]? with
    | none => simp [ClauseChoice.trial, found]
    | some equation =>
      simp only [ClauseChoice.trial, found]
      exact ClauseChoice.wrong_head_not_selected control definition.head values destination older index equation
        (otherHeads index equation found different)
  have scan : ∀ positions : List Nat, positions.Nodup →
      positions.filterMap (fun index =>
        (ClauseChoice.trial program control definition.head values destination older index).map (index, ·)) =
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
  simpa only [ClauseChoice.choices, List.mem_range, if_pos bound] using
    scan (List.range program.equations.length) List.nodup_range

theorem local_fresh (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal) (name : String)
    (bodyName : name ∈ TypeSubst.typeVars definition.body) (notFormal : name ∉ definition.formals)
    (closed : ∀ value ∈ values, ∀ environment, read environment value = value) :
    FreshFor (formal control occurrence definition name)
      (selected control occurrence definition values destination older).bindings := by
  intro pair member
  rcases List.mem_append.mp member with old | added
  · exact formal_fresh control occurrence definition name pair old
  · cases List.mem_singleton.mp added
    constructor
    · rw [CapturedPatternSupport.mem_expression_names]
      rintro ⟨atom, atomMember, occurs⟩
      rcases List.mem_cons.mp atomMember with same | member
      · subst atom
        simp [encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
      · rw [closed_names atom (closed atom member)] at occurs
        exact Finset.notMem_empty _ occurs
    · rw [fresh_pattern, CapturedPatternSupport.mem_expression_names]
      rintro ⟨atom, atomMember, occurs⟩
      rcases List.mem_cons.mp atomMember with same | member
      · subst atom
        simp [encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
      · obtain ⟨renamed, renamedMember, rfl⟩ := List.mem_map.mp member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp renamedMember
        have same : formal control occurrence definition name = formal control occurrence definition original := by
          simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
        have identical := ClauseChoice.rename_injective_on control occurrence _
          (by rw [clause_names]; exact List.mem_append_right _ bodyName)
          (by rw [clause_names]; exact List.mem_append_left _ originalMember) same
        exact notFormal (identical ▸ originalMember)

theorem call_destination_retained (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal)
    (atCall : control.goals = .invoke head arguments destination :: older) :
    (encode destination).freeVars ⊆ control.support := by
  intro name occurs
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  refine Or.inr ⟨destination, ?_, occurs⟩
  simp [atCall, Goal.atoms]

/-- The real invocation uses the complete collection's protection boundary
and the actual occurrence-indexed clause scan. -/
theorem enter {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (definition : Definition) (occurrence : Nat) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (principal : Environment) (representative : String)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke definition.head arguments destination :: older)
    (resolved : resolve control.bindings = some principal) (unbound : read principal destination = .var representative)
    (sameLength : arguments.length = definition.formals.length)
    (closed : ∀ argument ∈ arguments, ∀ environment, read environment (read principal argument) = read principal argument)
    (ordinary : definition.head ≠ "parse") (unknown : StdLib.known definition.head = false)
    (notIO : Eval.ioHead definition.head = false)
    (row : program.equations[occurrence]? = some definition.declaration)
    (otherHeads : ∀ index equation, program.equations[index]? = some equation →
      index ≠ occurrence → equation.head ≠ definition.head) :
    let guardedControl := protectControl control (collectionSupport ⟨world, scope :: parents⟩)
    let next := selected guardedControl occurrence definition (arguments.map (read principal)) destination older
    (ScopedQuerySource.machine policy program).run 1 (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (placed allocator world scope parents (predicateEntry pending.length next)
        context (origins ++ [occurrence]) pending)) := by
  dsimp only
  have valuesClosed : ∀ value ∈ arguments.map (read principal), ∀ environment, read environment value = value := by
    intro value member
    obtain ⟨argument, present, rfl⟩ := List.mem_map.mp member
    exact closed argument present
  have chosen := choices_singleton program
    (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) occurrence definition
    (arguments.map (read principal)) destination older (by simpa using sameLength)
    valuesClosed ⟨principal, resolve_sound resolved⟩ row otherHeads
  have declared : program.equations.any (·.head == definition.head) = true := by
    apply List.any_eq_true.mpr
    obtain ⟨bound, actual⟩ := List.getElem?_eq_some_iff.mp row
    exact ⟨definition.declaration, actual ▸ List.getElem_mem bound, by simp [Definition.declaration]⟩
  have step := ScopedQuerySource.Equations.enter policy program allocator world scope parents control context
    origins pending definition.head arguments destination older principal representative _ frontier atCall resolved
    unbound ordinary unknown notIO declared ((ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp chosen)
  simp [Machine.run, step, placed]

theorem entered_goals (control : Control) (occurrence : Nat) (definition : Definition)
    (values : List Atom) (destination : Atom) (older : List Goal) (retained : Nat) :
    (predicateEntry retained (selected control occurrence definition values destination older)).goals =
      .evaluate (ClauseChoice.freshBody control occurrence definition.declaration) destination ::
        .restoreCommit control.cutBoundary :: older := by
  simp [predicateEntry, selected]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource
