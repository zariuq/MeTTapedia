import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBInitializationSoundness

/-!
# MMB variable histories and hypothesis scope

The histories below are projections of the retained proof commands. Successful
execution determines the variable and bound-rank counters. Dummy allocations
are interpreted in one fixed context, distinct from store-pointer numbering.
Hypothesis evidence uses the independently given original statement premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBStateScopeSoundness

open Formats.MMB Kernel
open MMBMachineSoundness MMBDependencySoundness MMBInitializationSoundness
open MMBUnificationSoundness MMBTheoremSoundness

/-- The dummy sorts in proof-command order. -/
def dummySorts (commands : List ProofCmd) : List Nat :=
  commands.filterMap fun command => match command with
    | .dummy sort => some sort
    | _ => none

theorem dummySorts_append (first rest : List ProofCmd) :
    dummySorts (first ++ rest) = dummySorts first ++ dummySorts rest := by
  simp only [dummySorts, List.filterMap_append]

theorem stepTerm_keeps_scope (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (term : Nat) (save : Bool) (executed : stepTerm tables mode before term save = some after) :
    after.nextBound = before.nextBound ∧ after.varCount = before.varCount ∧ after.hyps = before.hyps := by
  unfold stepTerm at executed
  obtain ⟨entry, _, executed⟩ := Option.bind_eq_some_iff.mp executed
  obtain ⟨pair, popped, executed⟩ := Option.bind_eq_some_iff.mp executed
  rcases pair with ⟨args, state⟩
  obtain ⟨types, _, executed⟩ := Option.bind_eq_some_iff.mp executed
  split at executed
  · have keeps := State.popExprs_keeps_state before state entry.args.length args popped
    cases save <;> simp [State.alloc, State.push] at executed
    all_goals cases executed
    all_goals simpa only [Prod.mk.injEq] using congrArg (fun state => (state.nextBound, state.varCount, state.hyps)) keeps
  · cases executed

theorem stepThm_keeps_scope (tables : Tables) (before after : Formats.MMB.State)
    (index : Nat) (save : Bool) (executed : stepThm tables before index save = some after) :
    after.nextBound = before.nextBound ∧ after.varCount = before.varCount ∧ after.hyps = before.hyps := by
  unfold stepThm at executed
  obtain ⟨entry, _, executed⟩ := Option.bind_eq_some_iff.mp executed
  obtain ⟨pair, popped, executed⟩ := Option.bind_eq_some_iff.mp executed
  rcases pair with ⟨expression, firstState⟩
  obtain ⟨pair, arguments, executed⟩ := Option.bind_eq_some_iff.mp executed
  rcases pair with ⟨args, state⟩
  obtain ⟨types, _, executed⟩ := Option.bind_eq_some_iff.mp executed
  split at executed
  · obtain ⟨unifier, _, executed⟩ := Option.bind_eq_some_iff.mp executed
    have one := State.popExpr_keeps_state before firstState expression popped
    have many := State.popExprs_keeps_state firstState state entry.args.length args arguments
    have keeps : state = { before with stack := state.stack } := by rw [many, one]
    cases save <;> simp at executed
    all_goals cases executed
    all_goals simpa only [Prod.mk.injEq] using congrArg (fun state => (state.nextBound, state.varCount, state.hyps)) keeps
  · cases executed

theorem step_dummy_shape (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (sort : Nat) (executed : step tables mode before (.dummy sort) = some after) :
    ∃ info, tables.sorts[sort]? = some info ∧ info.strict = false ∧ info.free = false ∧
      after = { before with
        store := before.store ++ [⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩]
        stack := .expr before.store.length :: before.stack
        heap := before.heap ++ [.expr before.store.length]
        nextBound := before.nextBound + 1
        varCount := before.varCount + 1 } := by
  simp only [step] at executed
  split at executed
  · rename_i info found
    split at executed
    · rename_i allowed
      exact ⟨info, found, allowed.1, allowed.2, Option.some.inj executed.symm⟩
    · cases executed
  · cases executed

theorem step_hyp_shape (tables : Tables) (before after : Formats.MMB.State)
    (executed : step tables .assertion before .hyp = some after) :
    ∃ position state type info,
      before.popExpr = some (position, state) ∧ state.typeOf position = some type ∧
      tables.sorts[type.sort]? = some info ∧ info.provable = true ∧
      after = { state with hyps := position :: state.hyps, heap := state.heap ++ [.proof position] } := by
  simp only [step, ↓reduceIte] at executed
  obtain ⟨pair, popped, executed⟩ := Option.bind_eq_some_iff.mp executed
  rcases pair with ⟨position, state⟩
  obtain ⟨type, typeRead, executed⟩ := Option.bind_eq_some_iff.mp executed
  obtain ⟨info, sortRead, executed⟩ := Option.bind_eq_some_iff.mp executed
  split at executed
  · rename_i provable
    exact ⟨position, state, type, info, popped, typeRead, sortRead, provable, Option.some.inj executed.symm⟩
  · cases executed

theorem step_counters (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (command : ProofCmd) (executed : step tables mode before command = some after) :
    after.nextBound = before.nextBound + (dummySorts [command]).length ∧
      after.varCount = before.varCount + (dummySorts [command]).length := by
  cases command with
  | term term =>
      have keeps := stepTerm_keeps_scope tables mode before after term false executed
      simpa [dummySorts] using And.intro keeps.1 keeps.2.1
  | termSave term =>
      have keeps := stepTerm_keeps_scope tables mode before after term true executed
      simpa [dummySorts] using And.intro keeps.1 keeps.2.1
  | dummy sort =>
      obtain ⟨_, _, _, _, same⟩ := step_dummy_shape tables mode before after sort executed
      rw [same]
      simp [dummySorts]
  | thm index =>
      simp only [step] at executed
      split at executed
      · have keeps := stepThm_keeps_scope tables before after index false executed
        simpa [dummySorts] using And.intro keeps.1 keeps.2.1
      · cases executed
  | thmSave index =>
      simp only [step] at executed
      split at executed
      · have keeps := stepThm_keeps_scope tables before after index true executed
        simpa [dummySorts] using And.intro keeps.1 keeps.2.1
      · cases executed
  | hyp =>
      cases mode with
      | definition => simp [step] at executed
      | assertion =>
          obtain ⟨position, state, _, _, popped, _, _, _, same⟩ := step_hyp_shape tables before after executed
          rw [same]
          have keeps := State.popExpr_keeps_state before state position popped
          simpa [dummySorts, Prod.mk.injEq] using
            congrArg (fun state => (state.nextBound, state.varCount)) keeps
  | ref _ | conv | refl | symm | convCut | convSave | save =>
      simp only [step, State.push] at executed
      repeat' split at executed <;> simp_all [dummySorts]
      all_goals first
        | (cases executed; simp)
        | (rcases executed with ⟨_, rfl⟩; simp)
  | cong =>
      simp only [step] at executed
      split at executed
      · obtain ⟨leftAllocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        obtain ⟨rightAllocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        split at executed
        · split at executed <;> simp_all [dummySorts]
          cases executed
          simp
        · cases executed
      · cases executed
  | unfold =>
      simp only [step] at executed
      split at executed
      · obtain ⟨allocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        split at executed
        · obtain ⟨entry, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          obtain ⟨value, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          obtain ⟨unifier, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          cases Option.some.inj executed
          simp [dummySorts]
        · cases executed
      · cases executed

theorem run_counters (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (commands : List ProofCmd) (executed : run tables mode before commands = some after) :
    after.nextBound = before.nextBound + (dummySorts commands).length ∧
      after.varCount = before.varCount + (dummySorts commands).length := by
  induction commands generalizing before with
  | nil =>
      simp only [run, Option.some.injEq] at executed
      subst after
      simp [dummySorts]
  | cons command commands ih =>
      obtain ⟨middle, advanced, continued⟩ := Option.bind_eq_some_iff.mp executed
      have one := step_counters tables mode before middle command advanced
      have many := ih middle continued
      change after.nextBound = before.nextBound + (dummySorts ([command] ++ commands)).length ∧
        after.varCount = before.varCount + (dummySorts ([command] ++ commands)).length
      rw [dummySorts_append, List.length_append]
      simpa only [Nat.add_assoc] using
        And.intro (many.1.trans (congrArg (· + (dummySorts commands).length) one.1))
          (many.2.trans (congrArg (· + (dummySorts commands).length) one.2))

theorem run_initialized_counters (tables : Tables) (mode : Mode) (args : List ExprType)
    (loaded after : Formats.MMB.State) (commands : List ProofCmd)
    (initialized : loadArgs tables.sorts args = some loaded)
    (executed : run tables mode loaded commands = some after) :
    after.nextBound = (Statements.boundPositions args).length + (dummySorts commands).length ∧
      after.varCount = args.length + (dummySorts commands).length := by
  obtain ⟨_, _, _, _, variableCount, boundCount⟩ := MMBExecution.loadArgs_variable_shape tables.sorts args loaded initialized
  simpa only [boundCount, variableCount] using run_counters tables mode loaded after commands executed

theorem stepTerm_store_history (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (term : Nat) (save : Bool) (executed : stepTerm tables mode before term save = some after) :
    ∃ suffix, after.store = before.store ++ suffix ∧ after.hyps = before.hyps := by
  have sourceRead := executed
  unfold stepTerm at sourceRead
  obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp sourceRead
  obtain ⟨args, types, _, _, _, store⟩ := stepTerm_operands tables mode before after term save entry entryRead executed
  exact ⟨[⟨.app term args, ⟨entry.sort, false, appDeps mode entry.args entry.ret types⟩⟩], store,
    (stepTerm_keeps_scope tables mode before after term save executed).2.2⟩

theorem step_store_and_hyp_history (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (command : ProofCmd) (executed : step tables mode before command = some after) :
    ∃ allocations hypotheses, after.store = before.store ++ allocations ∧ after.hyps = hypotheses ++ before.hyps := by
  cases command with
  | term term =>
      obtain ⟨suffix, store, hyps⟩ := stepTerm_store_history tables mode before after term false executed
      exact ⟨suffix, [], store, hyps⟩
  | termSave term =>
      obtain ⟨suffix, store, hyps⟩ := stepTerm_store_history tables mode before after term true executed
      exact ⟨suffix, [], store, hyps⟩
  | dummy sort =>
      obtain ⟨_, _, _, _, same⟩ := step_dummy_shape tables mode before after sort executed
      rw [same]
      exact ⟨_, [], rfl, rfl⟩
  | thm index =>
      simp only [step] at executed
      split at executed
      · exact ⟨[], [], by simpa using stepThm_keeps_store tables before after index false executed,
          (stepThm_keeps_scope tables before after index false executed).2.2⟩
      · cases executed
  | thmSave index =>
      simp only [step] at executed
      split at executed
      · exact ⟨[], [], by simpa using stepThm_keeps_store tables before after index true executed,
          (stepThm_keeps_scope tables before after index true executed).2.2⟩
      · cases executed
  | hyp =>
      cases mode with
      | definition => simp [step] at executed
      | assertion =>
          obtain ⟨position, state, _, _, popped, _, _, _, same⟩ := step_hyp_shape tables before after executed
          have keeps := State.popExpr_keeps_state before state position popped
          rw [same, keeps]
          exact ⟨[], [position], by simp, rfl⟩
  | ref _ | conv | refl | symm | convCut | convSave | save =>
      simp only [step, State.push] at executed
      repeat' split at executed <;> simp_all
      all_goals first
        | (cases executed; simp)
        | (rcases executed with ⟨_, rfl⟩; simp)
  | cong =>
      simp only [step] at executed
      split at executed
      · obtain ⟨leftAllocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        obtain ⟨rightAllocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        split at executed
        · split at executed <;> simp_all
          cases executed
          simp
        · cases executed
      · cases executed
  | unfold =>
      simp only [step] at executed
      split at executed
      · obtain ⟨allocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        split at executed
        · obtain ⟨entry, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          obtain ⟨value, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          obtain ⟨unifier, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          cases Option.some.inj executed
          exact ⟨[], [], by simp, rfl⟩
        · cases executed
      · cases executed

theorem run_store_and_hyp_history (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (commands : List ProofCmd) (executed : run tables mode before commands = some after) :
    ∃ allocations hypotheses, after.store = before.store ++ allocations ∧ after.hyps = hypotheses ++ before.hyps := by
  induction commands generalizing before with
  | nil =>
      cases Option.some.inj executed
      exact ⟨[], [], by simp, rfl⟩
  | cons command commands ih =>
      obtain ⟨middle, advanced, continued⟩ := Option.bind_eq_some_iff.mp executed
      obtain ⟨firstAllocations, firstHyps, firstStore, firstHypotheses⟩ :=
        step_store_and_hyp_history tables mode before middle command advanced
      obtain ⟨remainingAllocations, remainingHyps, remainingStore, remainingHypotheses⟩ := ih middle continued
      exact ⟨firstAllocations ++ remainingAllocations, remainingHyps ++ firstHyps,
        by rw [remainingStore, firstStore, List.append_assoc],
        by rw [remainingHypotheses, firstHypotheses, List.append_assoc]⟩

theorem run_preserves_decoded_pointer (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (commands : List ProofCmd) (executed : run tables mode before commands = some after)
    (position : Nat) (expression : Preterm) (decoded : Soundness.decode before.store position = some expression) :
    Soundness.decode after.store position = some expression := by
  obtain ⟨suffix, _, store, _⟩ := run_store_and_hyp_history tables mode before after commands executed
  rw [store, MMBExecution.decode_append_preserves before.store suffix position
    (decoded_pointer_allocated before.store position expression decoded)]
  exact decoded

theorem run_initialized_public_roots (tables : Tables) (mode : Mode) (args : List ExprType)
    (loaded after : Formats.MMB.State) (commands : List ProofCmd)
    (initialized : loadArgs tables.sorts args = some loaded)
    (executed : run tables mode loaded commands = some after) :
    ∀ position < args.length, Soundness.decode after.store position = some (.var position) := by
  intro position inside
  obtain ⟨store, _, _, _, _, _⟩ := MMBExecution.loadArgs_variable_shape tables.sorts args loaded initialized
  have allocation : loaded.store[position]? = some (⟨.var position, args[position]'inside⟩ : Alloc) := by
    rw [store, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem inside]
    simp
  apply run_preserves_decoded_pointer tables mode loaded after commands executed position (.var position)
  rw [Soundness.decode, allocation]

theorem step_nonallocating_keeps_store (tables : Tables) (mode : Mode) (before after : Formats.MMB.State)
    (command : ProofCmd) (noTerm : ∀ term, command ≠ .term term)
    (noSavedTerm : ∀ term, command ≠ .termSave term) (noDummy : ∀ sort, command ≠ .dummy sort)
    (executed : step tables mode before command = some after) : after.store = before.store := by
  cases command with
  | term term => exact False.elim (noTerm term rfl)
  | termSave term => exact False.elim (noSavedTerm term rfl)
  | dummy sort => exact False.elim (noDummy sort rfl)
  | thm index =>
      simp only [step] at executed
      split at executed
      · exact stepThm_keeps_store tables before after index false executed
      · cases executed
  | thmSave index =>
      simp only [step] at executed
      split at executed
      · exact stepThm_keeps_store tables before after index true executed
      · cases executed
  | hyp =>
      cases mode with
      | definition => simp [step] at executed
      | assertion =>
          obtain ⟨position, state, _, _, popped, _, _, _, same⟩ := step_hyp_shape tables before after executed
          rw [same]
          simpa only using congrArg Formats.MMB.State.store (State.popExpr_keeps_state before state position popped)
  | ref _ | conv | refl | symm | convCut | convSave | save =>
      simp only [step, State.push] at executed
      repeat' split at executed <;> simp_all
      all_goals first
        | (cases executed; rfl)
        | (rcases executed with ⟨_, rfl⟩; rfl)
  | cong =>
      simp only [step] at executed
      split at executed
      · obtain ⟨leftAllocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        obtain ⟨rightAllocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        split at executed
        · split at executed <;> simp_all
          cases executed
          rfl
        · cases executed
      · cases executed
  | unfold =>
      simp only [step] at executed
      split at executed
      · obtain ⟨allocation, _, executed⟩ := Option.bind_eq_some_iff.mp executed
        split at executed
        · obtain ⟨entry, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          obtain ⟨value, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          obtain ⟨unifier, _, executed⟩ := Option.bind_eq_some_iff.mp executed
          cases Option.some.inj executed
          rfl
        · cases executed
      · cases executed

theorem read_types_bounded (state : Formats.MMB.State) (positions : List Nat) (types : List ExprType)
    (bound : Nat)
    (bounded : ∀ (position : Nat) (allocation : Alloc), state.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < bound)
    (read : positions.mapM state.typeOf = some types) : ∀ type ∈ types, ∀ rank ∈ type.deps, rank < bound := by
  induction positions generalizing types with
  | nil =>
      simp at read
      subst types
      simp
  | cons position positions ih =>
      cases first : state.typeOf position with
      | none => simp [first] at read
      | some type =>
          cases others : positions.mapM state.typeOf with
          | none => simp [first, others] at read
          | some remaining =>
              simp [first, others] at read
              subst types
              obtain ⟨allocation, allocationRead, same⟩ := Option.map_eq_some_iff.mp first
              intro source member rank occurs
              rcases List.mem_cons.mp member with sameSource | old
              · subst source
                rw [← same] at occurs
                exact bounded position allocation allocationRead rank occurs
              · exact ih remaining others source old rank occurs

theorem stepTerm_preserves_live_ranks (tables : Tables) (before after : Formats.MMB.State)
    (term : Nat) (save : Bool)
    (bounded : ∀ (position : Nat) (allocation : Alloc), before.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < before.nextBound)
    (executed : stepTerm tables .assertion before term save = some after) :
    ∀ (position : Nat) (allocation : Alloc), after.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < after.nextBound := by
  have sourceRead := executed
  unfold stepTerm at sourceRead
  obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp sourceRead
  obtain ⟨args, types, _, typesRead, _, store⟩ := stepTerm_operands tables .assertion before after term save entry entryRead executed
  have typesBounded := read_types_bounded before args types before.nextBound bounded typesRead
  have nextBound := (stepTerm_keeps_scope tables .assertion before after term save executed).1
  rw [store, nextBound]
  intro position allocation read rank member
  by_cases old : position < before.store.length
  · rw [List.getElem?_append_left old] at read
    exact bounded position allocation read rank member
  · have inside := (List.getElem?_eq_some_iff.mp read).choose
    have last : position = before.store.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst position
    have same : allocation = ⟨.app term args, ⟨entry.sort, false, appDeps .assertion entry.args entry.ret types⟩⟩ := by
      simpa using read.symm
    subst allocation
    obtain ⟨source, sourceMember, occurs⟩ := (mem_appDeps_assertion entry.args entry.ret types rank).mp member
    exact typesBounded source sourceMember rank occurs

theorem step_assertion_preserves_live_ranks (tables : Tables) (before after : Formats.MMB.State)
    (command : ProofCmd)
    (bounded : ∀ (position : Nat) (allocation : Alloc), before.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < before.nextBound)
    (executed : step tables .assertion before command = some after) :
    ∀ (position : Nat) (allocation : Alloc), after.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < after.nextBound := by
  cases command with
  | term term => exact stepTerm_preserves_live_ranks tables before after term false bounded executed
  | termSave term => exact stepTerm_preserves_live_ranks tables before after term true bounded executed
  | dummy sort =>
      obtain ⟨_, _, _, _, same⟩ := step_dummy_shape tables .assertion before after sort executed
      rw [same]
      intro position allocation read rank member
      by_cases old : position < before.store.length
      · rw [List.getElem?_append_left old] at read
        exact Nat.lt_succ_of_lt (bounded position allocation read rank member)
      · have inside := (List.getElem?_eq_some_iff.mp read).choose
        have last : position = before.store.length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at inside
          omega
        subst position
        have sameAllocation : allocation = ⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩ := by
          simpa using read.symm
        subst allocation
        have sameRank : rank = before.nextBound := Finset.mem_singleton.mp member
        rw [sameRank]
        exact Nat.lt_succ_self _
  | ref index | thm index | thmSave index | hyp | conv | refl | symm | cong | unfold | convCut | convSave | save =>
      have store := step_nonallocating_keeps_store tables .assertion before after _
        (by intro; simp) (by intro; simp) (by intro; simp) executed
      have counter := (step_counters tables .assertion before after _ executed).1
      simp only [dummySorts, List.filterMap_cons, List.filterMap_nil, List.length_nil, Nat.add_zero] at counter
      simpa only [store, counter] using bounded

theorem run_assertion_preserves_live_ranks (tables : Tables) (before after : Formats.MMB.State)
    (commands : List ProofCmd)
    (bounded : ∀ (position : Nat) (allocation : Alloc), before.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < before.nextBound)
    (executed : run tables .assertion before commands = some after) :
    ∀ (position : Nat) (allocation : Alloc), after.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < after.nextBound := by
  induction commands generalizing before with
  | nil => cases Option.some.inj executed; exact bounded
  | cons command commands ih =>
      obtain ⟨middle, advanced, continued⟩ := Option.bind_eq_some_iff.mp executed
      exact ih middle (step_assertion_preserves_live_ranks tables before middle command bounded advanced) continued

theorem run_initialized_live_ranks (tables : Tables) (args : List ExprType)
    (loaded after : Formats.MMB.State) (commands : List ProofCmd)
    (initialized : loadArgs tables.sorts args = some loaded)
    (executed : run tables .assertion loaded commands = some after) :
    ∀ (position : Nat) (allocation : Alloc), after.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < after.nextBound := by
  have initial := loadArgs_initial_store_ranked tables.sorts args loaded initialized
  obtain ⟨_, _, _, _, _, boundCount⟩ := MMBExecution.loadArgs_variable_shape tables.sorts args loaded initialized
  have bounded : ∀ (position : Nat) (allocation : Alloc), loaded.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < loaded.nextBound := by
    intro position allocation read rank member
    rw [boundCount]
    simpa only [rankPositions_context] using initial.bounded position allocation read rank member
  exact run_assertion_preserves_live_ranks tables loaded after commands bounded executed

theorem rankPositions_appended_bound (context suffix : Context) (sort : Nat) :
    ∃ rest, Soundness.rankPositions (context ++ .bound sort :: suffix) =
      Soundness.rankPositions context ++ context.length :: rest := by
  refine ⟨(suffix.zipIdx (context.length + 1) |>.filter (fun row => match row.1 with
    | .bound _ => true | .regular _ _ => false)).map (·.2), ?_⟩
  rw [rankPositions_append]
  simp only [List.zipIdx_cons, List.filter_cons, ↓reduceIte, List.map_cons]
  rfl

theorem rankPositions_dummy_count (context : Context) (sorts : List Nat) :
    (Soundness.rankPositions (context ++ sorts.map Binder.bound)).length =
      (Soundness.rankPositions context).length + sorts.length := by
  rw [rankPositions_append, List.length_append]
  simp [List.zipIdx_map, List.filter_map, Function.comp_def]

theorem fixed_dummy_position (args : List ExprType) (preceding remaining : List Nat) (sort : Nat) :
    let context := Statements.context args ++ (preceding ++ sort :: remaining).map Binder.bound
    let position := args.length + preceding.length
    let rank := (Statements.boundPositions args).length + preceding.length
    context[position]? = some (.bound sort) ∧
      (Soundness.rankPositions context).getD rank rank = position ∧
      rank < (Soundness.rankPositions context).length := by
  let before := Statements.context args ++ preceding.map Binder.bound
  have positionLength : before.length = args.length + preceding.length := by
    simp [before, Statements.context]
  have rankLength : (Soundness.rankPositions before).length =
      (Statements.boundPositions args).length + preceding.length := by
    rw [rankPositions_dummy_count, rankPositions_context]
  dsimp only
  simp only [List.map_append, List.map_cons, ← List.append_assoc]
  change (before ++ .bound sort :: remaining.map Binder.bound)[args.length + preceding.length]? =
    some (.bound sort) ∧
      (Soundness.rankPositions (before ++ .bound sort :: remaining.map Binder.bound)).getD
        ((Statements.boundPositions args).length + preceding.length)
        ((Statements.boundPositions args).length + preceding.length) = args.length + preceding.length ∧ _
  rw [← positionLength, ← rankLength]
  obtain ⟨rest, ranks⟩ := rankPositions_appended_bound before (remaining.map Binder.bound) sort
  rw [ranks, List.getD_eq_getElem?_getD]
  simp

theorem allocate_bound_variable_typed (signature : TermSignature) (context : Context)
    (before : Formats.MMB.State) (sort : Nat)
    (typed : TypedStore signature context before.store)
    (lookup : context[before.varCount]? = some (.bound sort)) :
    TypedStore signature context
      (before.store ++ [⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩]) := by
  constructor
  intro position allocation read
  by_cases old : position < before.store.length
  · rw [List.getElem?_append_left old] at read
    obtain ⟨expression, decoded, typing, bound⟩ := typed.expression position allocation read
    exact ⟨expression, (MMBExecution.decode_append_preserves before.store
      [⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩] position old).trans decoded, typing, bound⟩
  · have inside := (List.getElem?_eq_some_iff.mp read).choose
    have last : position = before.store.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst position
    have fresh : (before.store ++ [⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩])[before.store.length]? =
        some (⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩ : Alloc) := by simp
    cases Option.some.inj (read.symm.trans fresh)
    refine ⟨.var before.varCount, ?_, .var lookup, fun _ => ⟨before.varCount, rfl, lookup⟩⟩
    rw [Soundness.decode, fresh]

theorem allocate_bound_variable_ranked (context : Context) (before : Formats.MMB.State) (sort : Nat)
    (ranked : RankedStore context before.store)
    (lookup : context[before.varCount]? = some (.bound sort))
    (rankLookup : (Soundness.rankPositions context).getD before.nextBound before.nextBound = before.varCount)
    (rankBound : before.nextBound < (Soundness.rankPositions context).length) :
    RankedStore context
      (before.store ++ [⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩]) := by
  have newSupport : Preterm.Supports context (.var before.varCount)
      (Soundness.positionsOf context {before.nextBound}) := by
    simpa only [Soundness.positionsOf, Finset.image_singleton, rankLookup] using
      (Preterm.Supports.bound lookup : Preterm.Supports context (.var before.varCount) {before.varCount})
  constructor
  · intro position allocation read
    by_cases old : position < before.store.length
    · rw [List.getElem?_append_left old] at read
      obtain ⟨expression, decoded, support⟩ := ranked.supported position allocation read
      exact ⟨expression, (MMBExecution.decode_append_preserves before.store
        [⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩] position old).trans decoded, support⟩
    · have inside := (List.getElem?_eq_some_iff.mp read).choose
      have last : position = before.store.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at inside
        omega
      subst position
      have fresh : (before.store ++ [⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩])[before.store.length]? =
          some (⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩ : Alloc) := by simp
      cases Option.some.inj (read.symm.trans fresh)
      exact ⟨.var before.varCount, by rw [Soundness.decode, fresh], newSupport⟩
  · intro position allocation read rank member
    by_cases old : position < before.store.length
    · rw [List.getElem?_append_left old] at read
      exact ranked.bounded position allocation read rank member
    · have inside := (List.getElem?_eq_some_iff.mp read).choose
      have last : position = before.store.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at inside
        omega
      subst position
      have same : allocation = ⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩ := by
        simpa using read.symm
      subst allocation
      have sameRank : rank = before.nextBound := Finset.mem_singleton.mp member
      rw [sameRank]
      exact rankBound

theorem step_dummy_preserves_evidence (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (tables : Tables) (mode : Mode) (before after : Formats.MMB.State) (sort : Nat)
    (typed : TypedStore signature context before.store) (ranked : RankedStore context before.store)
    (stack : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (lookup : context[before.varCount]? = some (.bound sort))
    (rankLookup : (Soundness.rankPositions context).getD before.nextBound before.nextBound = before.varCount)
    (rankBound : before.nextBound < (Soundness.rankPositions context).length)
    (executed : step tables mode before (.dummy sort) = some after) :
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  obtain ⟨_, _, _, _, same⟩ := step_dummy_shape tables mode before after sort executed
  rw [same]
  let allocation : Alloc := ⟨.var before.varCount, ⟨sort, true, {before.nextBound}⟩⟩
  have pointer : TypedPointer signature context (before.store ++ [allocation]) before.store.length := by
    refine ⟨.var before.varCount, sort, ?_, .var lookup⟩
    have fresh : (before.store ++ [allocation])[before.store.length]? = some allocation := by simp
    rw [Soundness.decode, fresh]
  exact ⟨allocate_bound_variable_typed signature context before sort typed lookup,
    allocate_bound_variable_ranked context before sort ranked lookup rankLookup rankBound,
    .expr pointer (stack.append_store [allocation]),
    (heap.append_store [allocation]).append_certified pointer⟩

/-- The current dummy's context slot and rank are earned from the actual
initialized execution prefix, including intervening allocation commands. -/
theorem step_dummy_preserves_fixed_context (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (hypotheses : List Preterm) (tables : Tables) (mode : Mode)
    (args : List ExprType) (commandsBefore remaining : List ProofCmd) (sort : Nat)
    (loaded before after : Formats.MMB.State)
    (initialized : loadArgs tables.sorts args = some loaded)
    (preceding : run tables mode loaded commandsBefore = some before)
    (typed : TypedStore signature
      (Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound) before.store)
    (ranked : RankedStore
      (Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound) before.store)
    (stack : StackSound signature definitions theorems
      (Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound)
      hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems
      (Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound)
      hypotheses before.store before.heap)
    (executed : step tables mode before (.dummy sort) = some after) :
    let context := Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  have counters := run_initialized_counters tables mode args loaded before commandsBefore initialized preceding
  have position := fixed_dummy_position args (dummySorts commandsBefore) (dummySorts remaining) sort
  have history : dummySorts (commandsBefore ++ .dummy sort :: remaining) =
      dummySorts commandsBefore ++ sort :: dummySorts remaining := by
    rw [dummySorts_append]
    rfl
  dsimp only at position ⊢
  apply step_dummy_preserves_evidence signature definitions theorems _ hypotheses tables mode before after sort
    typed ranked stack heap
  · simpa only [history, counters.2] using position.1
  · simpa only [history, counters.1, counters.2] using position.2.1
  · simpa only [history, counters.1] using position.2.2
  · exact executed

theorem live_store_fresh_future_rank (context : Context) (before : Formats.MMB.State)
    (ranked : RankedStore context before.store)
    (live : ∀ (position : Nat) (allocation : Alloc), before.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < before.nextBound)
    (futureRank : Nat) (future : before.nextBound ≤ futureRank)
    (inside : futureRank < (Soundness.rankPositions context).length) :
    ∀ (position : Nat) (allocation : Alloc), before.store[position]? = some allocation →
      ∃ expression, Soundness.decode before.store position = some expression ∧
        Preterm.FreshFor context ((Soundness.rankPositions context).getD futureRank futureRank) expression := by
  intro position allocation read
  obtain ⟨expression, decoded, support⟩ := ranked.supported position allocation read
  refine ⟨expression, decoded, ⟨⟨_, support⟩, ?_⟩⟩
  intro occurs
  have member := (support.mem_iff_hasVar _).mpr occurs
  obtain ⟨rank, rankMember, samePosition⟩ := Finset.mem_image.mp member
  have sameRank := rankPositions_getD_injective context rank futureRank
    (ranked.bounded position allocation read rank rankMember) inside samePosition
  have earlier := live position allocation read rank rankMember
  omega

theorem run_prefix_fresh_next_dummy (tables : Tables) (args : List ExprType)
    (commandsBefore remaining : List ProofCmd) (sort : Nat) (loaded before : Formats.MMB.State)
    (initialized : loadArgs tables.sorts args = some loaded)
    (executed : run tables .assertion loaded commandsBefore = some before)
    (ranked : RankedStore
      (Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound) before.store) :
    let context := Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound
    ∀ (position : Nat) (allocation : Alloc), before.store[position]? = some allocation →
      ∃ expression, Soundness.decode before.store position = some expression ∧ Preterm.FreshFor context before.varCount expression := by
  have counters := run_initialized_counters tables .assertion args loaded before commandsBefore initialized executed
  have position := fixed_dummy_position args (dummySorts commandsBefore) (dummySorts remaining) sort
  have history : dummySorts (commandsBefore ++ .dummy sort :: remaining) =
      dummySorts commandsBefore ++ sort :: dummySorts remaining := by rw [dummySorts_append]; rfl
  dsimp only at position ⊢
  have rankLookup : (Soundness.rankPositions
      (Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound)).getD
      before.nextBound before.nextBound = before.varCount := by
    simpa only [history, counters.1, counters.2] using position.2.1
  have rankBound : before.nextBound < (Soundness.rankPositions
      (Statements.context args ++ (dummySorts (commandsBefore ++ .dummy sort :: remaining)).map Binder.bound)).length := by
    simpa only [history, counters.1] using position.2.2
  simpa only [rankLookup] using live_store_fresh_future_rank _ before ranked
    (run_initialized_live_ranks tables args loaded before commandsBefore initialized executed) before.nextBound (Nat.le_refl _) rankBound

theorem unify_statement_hyp (store : List Alloc) (before after : Unifier)
    (empty : before.stack = []) (executed : unifyStep store .statement before .hyp = some after) :
    ∃ position rest, before.hyps = position :: rest ∧ after = { before with stack := [position], hyps := rest } := by
  simp only [unifyStep, empty, ↓reduceIte] at executed
  split at executed
  · rename_i position rest shape
    exact ⟨position, rest, shape, Option.some.inj executed.symm⟩
  · cases executed

theorem unifyRun_statement_empty_hypotheses (store : List Alloc) (before after : Unifier)
    (commands : List UnifyCmd) (accepted : unifyRun store .statement before commands = some after) :
    after.hyps = [] := by
  rw [unifyRun_fold] at accepted
  obtain ⟨middle, _, checked⟩ := Option.bind_eq_some_iff.mp accepted
  split at checked
  · rename_i finished
    cases Option.some.inj checked
    simpa using finished.2
  · cases checked

theorem identity_substitution_reflects (source image : Preterm)
    (substituted : Preterm.Substitutes Substitution.identity source image) : image = source := by
  have evaluated := substituted.eval
  simpa using evaluated.symm

theorem initial_identity_slots (store : List Alloc) (arguments : Nat)
    (roots : ∀ position < arguments, Soundness.decode store position = some (.var position)) :
    SlotsSubstitute store Substitution.identity (Statements.initial arguments).slots
      ((List.range arguments).map (·, false)) := by
  constructor
  · simp [Statements.initial]
  · intro index source found
    have inside : index < arguments := by
      have bound := (List.getElem?_eq_some_iff.mp found).choose
      simpa [Statements.initial] using bound
    have same : source = .var index := by simpa [Statements.initial, inside] using found.symm
    subst source
    exact ⟨index, false, .var index, by simp [inside], roots index inside, .var rfl⟩

/-- The retained statement unifier consumes recorded hypotheses from last
to first. The source decoder reconstructs their declaration order. -/
theorem decodeHyps_statement_images (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : TypedStore signature context store)
    (arity : Nat → Option Nat)
    (arities : ∀ term declaration, signature term = some declaration → arity term = some declaration.arguments.length)
    (arguments fuel : Nat) (sourceBefore : Statements.Decoding)
    (commands : List UnifyCmd) (sources : List Preterm) (before after : Unifier)
    (decoded : Statements.decodeHyps arity arguments fuel sourceBefore commands = some sources)
    (accepted : unifyRun store .statement before commands = some after)
    (empty : before.stack = [])
    (matching : SlotsSubstitute store Substitution.identity sourceBefore.slots before.heap) :
    before.hyps.reverse.mapM (Soundness.decode store) = some sources ∧ after.hyps = [] := by
  have consumed := unifyRun_statement_empty_hypotheses store before after commands accepted
  cases commands with
  | nil =>
      have sameSources : [] = sources := by simpa [Statements.decodeHyps] using decoded
      subst sources
      simp only [unifyRun, empty] at accepted
      split at accepted
      · rename_i finished
        have noHyps : before.hyps = [] := by simpa using finished.2
        exact ⟨by simp [noHyps], consumed⟩
      · cases accepted
  | cons command commands =>
      cases fuel with
      | zero => simp [Statements.decodeHyps] at decoded
      | succ fuel =>
          cases command with
          | term term => simp [Statements.decodeHyps] at decoded
          | termSave term => simp [Statements.decodeHyps] at decoded
          | ref index => simp [Statements.decodeHyps] at decoded
          | dummy sort => simp [Statements.decodeHyps] at decoded
          | hyp =>
              obtain ⟨value, first, remainingRead⟩ := Option.bind_eq_some_iff.mp decoded
              rcases value with ⟨source, middleSource, remaining⟩
              obtain ⟨earlier, others, sameSources⟩ := Option.bind_eq_some_iff.mp remainingRead
              have ordered : earlier ++ [source] = sources := Option.some.inj sameSources
              subst sources
              obtain ⟨started, firstStep, restAccepted⟩ := Option.bind_eq_some_iff.mp accepted
              obtain ⟨position, rest, shape, sameStarted⟩ := unify_statement_hyp store before started empty firstStep
              subst started
              obtain ⟨_, commandsBefore, _, consumedRead, _⟩ :=
                Soundness.decodeExpr_source_order arity arguments fuel sourceBefore middleSource commands remaining source first
              have expressionAccepted : unifyRun store .statement { before with stack := [position], hyps := rest }
                  (commandsBefore ++ remaining) = some after := by rw [← consumedRead]; exact restAccepted
              obtain ⟨middle, expressionSteps, remainingAccepted⟩ :=
                unifyRun_prefix store .statement { before with stack := [position], hyps := rest } after
                  commandsBefore remaining expressionAccepted
              have sourceRead : Statements.decodeExpr arity arguments fuel sourceBefore (commandsBefore ++ remaining) =
                  some (source, middleSource, remaining) := by rw [← consumedRead]; exact first
              obtain ⟨image, imageRead, substituted, middleStack, middleSlots, _, middleHyps, _⟩ :=
                decodeExpr_unifies signature context store typed arity arities Substitution.identity .statement (by decide)
                  arguments fuel sourceBefore middleSource commandsBefore remaining source _ middle position []
                  sourceRead expressionSteps rfl matching
              have imageSource := identity_substitution_reflects source image substituted
              subst image
              have earlierImages := (decodeHyps_statement_images signature context store typed arity arities arguments fuel
                middleSource remaining earlier middle after others remainingAccepted middleStack middleSlots).1
              have restImages : rest.reverse.mapM (Soundness.decode store) = some earlier := by
                simpa only [middleHyps] using earlierImages
              exact ⟨by rw [shape, List.reverse_cons, List.mapM_append, restImages]; simp [imageRead], consumed⟩
termination_by fuel

/-- Accepted matching of the actual statement earns the complete original
hypothesis list, including order and multiplicity, independently of proofs. -/
theorem unify_statement_original_hypotheses (signature : TermSignature) (context : Context)
    (store : List Alloc) (typed : TypedStore signature context store)
    (terms : List TermEntry) (entry : ThmEntry) (declaration : TheoremDecl)
    (arities : ∀ term termDeclaration, signature term = some termDeclaration →
      Statements.arityOf terms term = some termDeclaration.arguments.length)
    (declared : Statements.theoremDecl terms entry = some declaration)
    (roots : ∀ position < entry.args.length, Soundness.decode store position = some (.var position))
    (position : Nat) (hyps : List Nat) (after : Unifier)
    (accepted : unifyRun store .statement
      ⟨[position], (List.range entry.args.length).map (·, false), [], hyps⟩ entry.unify = some after) :
    hyps.reverse.mapM (Soundness.decode store) = some declaration.hypotheses := by
  let fuel := 2 * entry.unify.length + 2
  obtain ⟨value, conclusion, sourceDecl⟩ := Option.bind_eq_some_iff.mp declared
  rcases value with ⟨source, middleSource, remaining⟩
  change (if middleSource.dummies ≠ [] then none else
    (Statements.decodeHyps (Statements.arityOf terms) entry.args.length fuel middleSource remaining).bind
      (fun hypotheses => some (⟨Statements.context entry.args, hypotheses, source⟩ : TheoremDecl))) =
        some declaration at sourceDecl
  split at sourceDecl
  · cases sourceDecl
  · obtain ⟨sources, sourcesRead, sameDeclaration⟩ := Option.bind_eq_some_iff.mp sourceDecl
    have declarationSame : (⟨Statements.context entry.args, sources, source⟩ : TheoremDecl) = declaration :=
      Option.some.inj sameDeclaration
    obtain ⟨_, commandsBefore, _, consumedRead, _⟩ :=
      Soundness.decodeExpr_source_order (Statements.arityOf terms) entry.args.length fuel
        (Statements.initial entry.args.length) middleSource entry.unify remaining source conclusion
    have expressionAccepted : unifyRun store .statement
        ⟨[position], (List.range entry.args.length).map (·, false), [], hyps⟩
        (commandsBefore ++ remaining) = some after := by rw [← consumedRead]; exact accepted
    obtain ⟨middle, expressionSteps, remainingAccepted⟩ :=
      unifyRun_prefix store .statement _ after commandsBefore remaining expressionAccepted
    have expressionRead : Statements.decodeExpr (Statements.arityOf terms) entry.args.length fuel
        (Statements.initial entry.args.length) (commandsBefore ++ remaining) = some (source, middleSource, remaining) := by
      rw [← consumedRead]
      exact conclusion
    obtain ⟨_, _, _, middleStack, middleSlots, _, middleHyps, _⟩ :=
      decodeExpr_unifies signature context store typed (Statements.arityOf terms) arities Substitution.identity
        .statement (by decide) entry.args.length fuel (Statements.initial entry.args.length) middleSource
        commandsBefore remaining source _ middle position [] expressionRead expressionSteps rfl
        (initial_identity_slots store entry.args.length roots)
    have images := (decodeHyps_statement_images signature context store typed (Statements.arityOf terms)
      arities entry.args.length fuel middleSource remaining sources middle after sourcesRead remainingAccepted
      middleStack middleSlots).1
    simpa only [middleHyps, ← declarationSame] using images

theorem decoded_recorded_hypothesis_member (store : List Alloc) (positions : List Nat)
    (hypotheses : List Preterm) (recorded : positions.reverse.mapM (Soundness.decode store) = some hypotheses)
    (position : Nat) (expression : Preterm) (member : position ∈ positions)
    (decoded : Soundness.decode store position = some expression) : expression ∈ hypotheses := by
  have ordered := decoded_arguments store positions.reverse hypotheses recorded
  obtain ⟨index, positionRead⟩ := List.mem_iff_getElem?.mp (by simpa using member : position ∈ positions.reverse)
  obtain ⟨inside, samePosition⟩ := List.getElem?_eq_some_iff.mp positionRead
  have imageInside : index < hypotheses.length := by simpa only [← ordered.length_eq] using inside
  have imageRead := ordered.get inside imageInside
  change Soundness.decode store (positions.reverse[index]'inside) = some (hypotheses[index]'imageInside) at imageRead
  rw [samePosition] at imageRead
  have same : expression = hypotheses[index]'imageInside := Option.some.inj (decoded.symm.trans imageRead)
  rw [same]
  exact List.mem_of_getElem (by rfl)

/-- Final statement correspondence earns the new premise's original scope;
the `Hyp` command alone does not authorize a fresh assumption. -/
theorem step_hyp_preserves_original_scope (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (tables : Tables) (before after finalState : Formats.MMB.State) (remaining : List ProofCmd)
    (typed : TypedStore signature context before.store) (ranked : RankedStore context before.store)
    (stack : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (executed : step tables .assertion before .hyp = some after)
    (continued : run tables .assertion after remaining = some finalState)
    (original : finalState.hyps.reverse.mapM (Soundness.decode finalState.store) = some hypotheses) :
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  obtain ⟨position, state, type, _, popped, typeRead, _, _, same⟩ := step_hyp_shape tables before after executed
  have keeps := State.popExpr_keeps_state before state position popped
  have sameStore : state.store = before.store := by simpa only using congrArg Formats.MMB.State.store keeps
  obtain ⟨allocation, allocationRead, allocationType⟩ := Option.map_eq_some_iff.mp typeRead
  rw [sameStore] at allocationRead
  obtain ⟨expression, decoded, typing, _⟩ := typed.expression position allocation allocationRead
  have afterStore : after.store = before.store := by rw [same]; exact sameStore
  have afterDecoded : Soundness.decode after.store position = some expression := afterStore ▸ decoded
  have finalDecoded := run_preserves_decoded_pointer tables .assertion after finalState remaining continued position expression afterDecoded
  obtain ⟨_, newHypotheses, _, finalHyps⟩ := run_store_and_hyp_history tables .assertion after finalState remaining continued
  have member : position ∈ finalState.hyps := by
    rw [finalHyps, same]
    exact List.mem_append_right _ (List.mem_cons_self)
  have originalMember := decoded_recorded_hypothesis_member finalState.store finalState.hyps hypotheses original
    position expression member finalDecoded
  have proved : ProvenPointer signature definitions theorems context hypotheses before.store position :=
    ⟨expression, allocation.type.sort, decoded, typing, .hypothesis originalMember⟩
  have certified : CertifiedElem signature definitions theorems context hypotheses before.store (.proof position) := proved
  have sameHeap : state.heap = before.heap := by simpa only using congrArg Formats.MMB.State.heap keeps
  have rest := StackSound.popExpr before state position stack popped
  rw [same]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [sameStore] using typed
  · simpa only [sameStore] using ranked
  · simpa only [sameStore] using rest
  · simpa only [sameStore, sameHeap] using heap.append_certified certified

theorem step_hyp_preserves_checked_original_scope (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm) (tables : Tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (loaded before after finalState : Formats.MMB.State)
    (proof remaining : List ProofCmd) (conclusion : Nat) (unified : Unifier)
    (initialized : loadArgs tables.sorts entry.args = some loaded)
    (proofRun : run tables .assertion loaded proof = some finalState)
    (finalTyped : TypedStore signature context finalState.store)
    (arities : ∀ term termDeclaration, signature term = some termDeclaration →
      Statements.arityOf tables.terms term = some termDeclaration.arguments.length)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (hypothesesAgree : declaration.hypotheses = hypotheses)
    (accepted : unifyRun finalState.store .statement
      ⟨[conclusion], (List.range entry.args.length).map (·, false), [], finalState.hyps⟩ entry.unify = some unified)
    (typed : TypedStore signature context before.store) (ranked : RankedStore context before.store)
    (stack : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (executed : step tables .assertion before .hyp = some after)
    (continued : run tables .assertion after remaining = some finalState) :
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  have original := unify_statement_original_hypotheses signature context finalState.store finalTyped tables.terms
    entry declaration arities declared (run_initialized_public_roots tables .assertion entry.args loaded finalState proof initialized proofRun)
    conclusion finalState.hyps unified accepted
  rw [hypothesesAgree] at original
  exact step_hyp_preserves_original_scope signature definitions theorems context hypotheses tables before after finalState remaining
    typed ranked stack heap executed continued original

namespace Controls.Dummy

private def sorts : List SortInfo := [⟨false, false, true, false⟩, ⟨false, false, false, false⟩,
  ⟨false, true, false, false⟩, ⟨false, false, false, true⟩]
private def args : List ExprType := [⟨0, false, ∅⟩, ⟨0, true, {0}⟩]
private def constant : TermEntry := ⟨0, [], ⟨0, false, ∅⟩, none⟩
private def binderTerm : TermEntry := ⟨0, [⟨1, true, {0}⟩], ⟨0, false, ∅⟩, none⟩
private def signature : TermSignature := fun term =>
  if term = 0 then some ⟨[], 0, ∅⟩ else if term = 1 then some ⟨[.bound 1], 0, ∅⟩ else none
private def tables : Tables := ⟨sorts, [constant, binderTerm], []⟩
private def commands : List ProofCmd := [.term 0, .dummy 1, .termSave 1, .dummy 0]
private def context : Context := Statements.context args ++ (dummySorts commands).map Binder.bound
private def initial : Formats.MMB.State :=
  ⟨[⟨.var 0, args[0]⟩, ⟨.var 1, args[1]⟩], [], [.expr 0, .expr 1], [], 1, 2⟩
private def afterConstant : Formats.MMB.State :=
  { initial with store := initial.store ++ [⟨.app 0 [], ⟨0, false, ∅⟩⟩], stack := [.expr 2] }
private def firstDummy : Formats.MMB.State :=
  { afterConstant with
    store := afterConstant.store ++ [⟨.var 2, ⟨1, true, {1}⟩⟩]
    stack := [.expr 3, .expr 2], heap := initial.heap ++ [.expr 3], nextBound := 2, varCount := 3 }
private def afterApplication : Formats.MMB.State :=
  { firstDummy with
    store := firstDummy.store ++ [⟨.app 1 [3], ⟨0, false, {1}⟩⟩]
    stack := [.expr 4, .expr 2], heap := firstDummy.heap ++ [.expr 4] }
private def finalState : Formats.MMB.State :=
  { afterApplication with
    store := afterApplication.store ++ [⟨.var 3, ⟨0, true, {2}⟩⟩]
    stack := [.expr 5, .expr 4, .expr 2], heap := afterApplication.heap ++ [.expr 5], nextBound := 3, varCount := 4 }

private theorem initialized : loadArgs tables.sorts args = some initial := by decide
private theorem initialTyped : TypedStore signature context initial.store :=
  (loadArgs_initial_fixed_context signature sorts args (dummySorts commands) initial initialized).1
private theorem initialRanked : RankedStore context initial.store :=
  (loadArgs_initial_fixed_context signature sorts args (dummySorts commands) initial initialized).2
private theorem initialHeap : HeapSound signature (fun _ => none) (fun _ => none) context [] initial.store initial.heap := by
  intro element member
  simp [initial] at member
  rcases member with rfl | rfl
  · exact TypedStore.pointer signature context initial.store initialTyped 0 ⟨.var 0, args[0]⟩ (by decide)
  · exact TypedStore.pointer signature context initial.store initialTyped 1 ⟨.var 1, args[1]⟩ (by decide)

private theorem constantEvidence :
    TypedStore signature context afterConstant.store ∧ RankedStore context afterConstant.store ∧
      StackSound signature (fun _ => none) (fun _ => none) context [] afterConstant.store afterConstant.stack ∧
      HeapSound signature (fun _ => none) (fun _ => none) context [] afterConstant.store afterConstant.heap := by
  have executed : stepTerm tables .assertion initial 0 false = some afterConstant := by decide
  have evidence := stepTerm_preserves_evidence tables .assertion initial afterConstant 0 false constant ⟨[], 0, ∅⟩
    initialTyped .empty initialHeap rfl (by simp [signature]) rfl rfl executed
  exact ⟨evidence.1, stepTerm_preserves_ranked_support context tables initial afterConstant 0 false constant initialRanked rfl executed,
    evidence.2⟩

theorem first_dummy_after_application_preserves_evidence :
    TypedStore signature context firstDummy.store ∧ RankedStore context firstDummy.store ∧
      StackSound signature (fun _ => none) (fun _ => none) context [] firstDummy.store firstDummy.stack ∧
      HeapSound signature (fun _ => none) (fun _ => none) context [] firstDummy.store firstDummy.heap := by
  exact step_dummy_preserves_fixed_context signature (fun _ => none) (fun _ => none) [] tables .assertion args
    [.term 0] [.termSave 1, .dummy 0] 1 initial afterConstant firstDummy initialized (by decide)
    constantEvidence.1 constantEvidence.2.1 constantEvidence.2.2.1 constantEvidence.2.2.2 (by decide)

private theorem applicationEvidence :
    TypedStore signature context afterApplication.store ∧ RankedStore context afterApplication.store ∧
      StackSound signature (fun _ => none) (fun _ => none) context [] afterApplication.store afterApplication.stack ∧
      HeapSound signature (fun _ => none) (fun _ => none) context [] afterApplication.store afterApplication.heap := by
  have executed : stepTerm tables .assertion firstDummy 1 true = some afterApplication := by decide
  have prior := first_dummy_after_application_preserves_evidence
  have evidence := stepTerm_preserves_evidence tables .assertion firstDummy afterApplication 1 true binderTerm ⟨[.bound 1], 0, ∅⟩
    prior.1 prior.2.2.1 prior.2.2.2 rfl (by simp [signature]) rfl rfl executed
  exact ⟨evidence.1, stepTerm_preserves_ranked_support context tables firstDummy afterApplication 1 true binderTerm prior.2.1 rfl executed,
    evidence.2⟩

theorem second_dummy_after_saved_application_preserves_evidence :
    TypedStore signature context finalState.store ∧ RankedStore context finalState.store ∧
      StackSound signature (fun _ => none) (fun _ => none) context [] finalState.store finalState.stack ∧
      HeapSound signature (fun _ => none) (fun _ => none) context [] finalState.store finalState.heap := by
  exact step_dummy_preserves_fixed_context signature (fun _ => none) (fun _ => none) [] tables .assertion args
    [.term 0, .dummy 1, .termSave 1] [] 0 initial afterApplication finalState initialized (by decide)
    applicationEvidence.1 applicationEvidence.2.1 applicationEvidence.2.2.1 applicationEvidence.2.2.2 (by decide)

theorem actual_history_earns_counters : finalState.nextBound = 3 ∧ finalState.varCount = 4 := by
  exact run_initialized_counters tables .assertion args initial finalState commands initialized (by decide)

theorem dummy_context_positions_differ_from_pointers :
    Soundness.decode finalState.store 3 = some (.var 2) ∧ Soundness.decode finalState.store 5 = some (.var 3) := by
  constructor <;> rw [Soundness.decode] <;> rfl

theorem allocated_application_is_fresh_for_future_dummy :
    Preterm.FreshFor context 3 (.app (.term 1) (.var 2)) := by
  have fresh := run_prefix_fresh_next_dummy tables args [.term 0, .dummy 1, .termSave 1] [] 0 initial afterApplication
    initialized (by decide) applicationEvidence.2.1 4 (⟨.app 1 [3], ⟨0, false, {1}⟩⟩ : Alloc) (by decide)
  obtain ⟨expression, decoded, earned⟩ := fresh
  have actualDecoded : Soundness.decode afterApplication.store 4 = some (.app (.term 1) (.var 2)) := by
    have child : Soundness.decode firstDummy.store 3 = some (.var 2) := by rw [Soundness.decode]; rfl
    have application := MMBExecution.decode_alloc_application firstDummy 1 [3] ⟨0, false, {1}⟩ (by simp [firstDummy, afterConstant, initial])
    change Soundness.decode afterApplication.store 4 = _ at application
    simpa [child, Preterm.applyArgs] using application
  have same := Option.some.inj (decoded.symm.trans actualDecoded)
  subst expression
  exact earned

theorem allocated_ranks_stay_below_actual_counter :
    ∀ (position : Nat) (allocation : Alloc), finalState.store[position]? = some allocation →
      ∀ rank ∈ allocation.type.deps, rank < finalState.nextBound :=
  run_initialized_live_ranks tables args initial finalState commands initialized (by decide)

theorem bound_occurrence_prevents_reusing_earlier_dummy :
    Preterm.checkFreshFor context 2 (.app (.term 1) (.var 2)) = false ∧
      unifyStep afterApplication.store .definition ⟨[3], [(4, false)], [], []⟩ (.dummy 1) = none := by decide

theorem repeated_heap_references_preserve_physical_pointer :
    run tables .assertion finalState [.ref 2, .ref 2] =
      some { finalState with stack := .expr 3 :: .expr 3 :: finalState.stack } := by decide

theorem future_heap_reference_refused : step tables .assertion afterApplication (.ref 4) = none := by decide
theorem strict_dummy_sort_refused : step tables .assertion afterApplication (.dummy 2) = none := by decide
theorem free_dummy_sort_refused : step tables .assertion afterApplication (.dummy 3) = none := by decide
theorem unknown_dummy_sort_refused : step tables .assertion afterApplication (.dummy 4) = none := by decide

theorem forged_rank_counter_is_unreachable :
    run tables .assertion initial [.term 0, .dummy 1, .termSave 1] ≠ some { afterApplication with nextBound := 0 } ∧
      (Soundness.rankPositions context).getD 0 0 ≠ afterApplication.varCount := by decide

theorem copied_application_reflexivity_refused :
    let copied := { finalState with
      store := finalState.store ++ [⟨.app 1 [3], ⟨0, false, {1}⟩⟩], stack := [.goal 4 6] }
    step tables .assertion copied .refl = none := by decide

end Controls.Dummy

namespace Controls.Hypothesis

private def type : ExprType := ⟨0, false, ∅⟩
private def termDeclaration : TermDecl := ⟨[], 0, ∅⟩
private def signature : TermSignature := fun term => if term = 0 ∨ term = 1 then some termDeclaration else none
private def tables : Tables := ⟨[⟨false, false, true, false⟩], List.replicate 2 ⟨0, [], type, none⟩, []⟩
private def entry : ThmEntry := ⟨[], [.term 0, .hyp, .term 1, .hyp, .term 0]⟩
private def declaration : TheoremDecl := ⟨[], [.term 0, .term 1], .term 0⟩
private def commands : List ProofCmd := [.term 0, .hyp, .term 1, .hyp, .ref 0]
private def initial : Formats.MMB.State := ⟨[], [], [], [], 0, 0⟩
private def before : Formats.MMB.State := ⟨[⟨.app 0 [], type⟩], [.expr 0], [], [], 0, 0⟩
private def after : Formats.MMB.State := { before with stack := [], heap := [.proof 0], hyps := [0] }
private def finalState : Formats.MMB.State :=
  ⟨[⟨.app 0 [], type⟩, ⟨.app 1 [], type⟩], [.proof 0], [.proof 0, .proof 1], [1, 0], 0, 0⟩
private def unified : Unifier := ⟨[], [], [], []⟩

private theorem arities (term : Nat) (termDecl : TermDecl) (found : signature term = some termDecl) :
    Statements.arityOf tables.terms term = some termDecl.arguments.length := by
  simp only [signature] at found
  split at found
  · rename_i known
    cases Option.some.inj found
    rcases known with rfl | rfl <;> rfl
  · cases found

private theorem finalTyped : TypedStore signature [] finalState.store := by
  constructor
  intro position allocation found
  have inside : position < 2 := by
    have bound := (List.getElem?_eq_some_iff.mp found).choose
    simpa [finalState] using bound
  have casesPosition : position = 0 ∨ position = 1 := by omega
  have same : allocation = ⟨.app position [], type⟩ := by
    rcases casesPosition with rfl | rfl <;> simpa [finalState] using found.symm
  have decoded : Soundness.decode finalState.store position = some (.term position) := by
    rcases casesPosition with rfl | rfl <;> rw [Soundness.decode] <;> rfl
  subst allocation
  exact ⟨.term position, decoded, .term (declaration := termDeclaration) (by simp [signature, casesPosition]), by simp [type]⟩

private theorem beforeTyped : TypedStore signature [] before.store := by
  have initialTyped := loadArgs_initial_store_typed signature tables.sorts [] initial (by decide)
  exact stepTerm_preserves_typing signature [] tables .assertion initial before 0 false ⟨0, [], type, none⟩
    termDeclaration initialTyped rfl (by simp [signature]) rfl rfl (by decide)

private theorem beforeRanked : RankedStore [] before.store := by
  exact stepTerm_preserves_ranked_support [] tables initial before 0 false ⟨0, [], type, none⟩
    (loadArgs_initial_store_ranked tables.sorts [] initial (by decide)) rfl (by decide)

private theorem beforeStack : StackSound signature (fun _ => none) (fun _ => none) [] declaration.hypotheses before.store before.stack :=
  .expr (TypedStore.pointer signature [] before.store beforeTyped 0 ⟨.app 0 [], type⟩ (by decide)) .empty

theorem final_statement_earns_ordered_original_hypotheses :
    finalState.hyps.reverse.mapM (Soundness.decode finalState.store) = some declaration.hypotheses := by
  exact unify_statement_original_hypotheses signature [] finalState.store finalTyped tables.terms entry declaration arities
    (by decide) (by simp [entry]) 0 finalState.hyps unified (by rfl)

theorem first_hypothesis_command_earns_completed_heap_evidence :
    TypedStore signature [] after.store ∧ RankedStore [] after.store ∧
      StackSound signature (fun _ => none) (fun _ => none) [] declaration.hypotheses after.store after.stack ∧
      HeapSound signature (fun _ => none) (fun _ => none) [] declaration.hypotheses after.store after.heap := by
  exact step_hyp_preserves_checked_original_scope signature (fun _ => none) (fun _ => none) [] declaration.hypotheses tables
    entry declaration initial before after finalState commands [.term 1, .hyp, .ref 0] 0 unified
    (by decide) (by decide) finalTyped arities (by decide) rfl (by rfl) beforeTyped beforeRanked beforeStack
    (by simp [HeapSound, before]) (by decide) (by decide)

theorem saved_original_hypothesis_supplies_kernel_derivation :
    Derives signature (fun _ => none) (fun _ => none) [] declaration.hypotheses (.term 0) := by
  have heap := first_hypothesis_command_earns_completed_heap_evidence.2.2.2
  have proof : ProvenPointer signature (fun _ => none) (fun _ => none) [] declaration.hypotheses after.store 0 :=
    heap.lookup (index := 0) (element := .proof 0) (by decide)
  obtain ⟨expression, _, decoded, _, derived⟩ := proof
  have known : Soundness.decode after.store 0 = some (.term 0) := by rw [Soundness.decode]; rfl
  have same := Option.some.inj (decoded.symm.trans known)
  subst expression
  exact derived

theorem actual_hypothesis_proof_is_accepted : checkAssertion tables entry commands false = true := by decide

theorem reversed_recorded_hypotheses_refused :
    unifyRun finalState.store .statement ⟨[0], [], [], [0, 1]⟩ entry.unify = none := by decide

theorem extra_recorded_hypothesis_refused :
    unifyRun finalState.store .statement ⟨[0], [], [], [1, 0, 0]⟩ entry.unify = none := by decide

theorem missing_recorded_hypothesis_refused :
    unifyRun finalState.store .statement ⟨[0], [], [], [1]⟩ entry.unify = none := by decide

theorem repeated_statement_premises_preserve_multiplicity :
    unifyRun finalState.store .statement ⟨[0], [], [], [0, 0]⟩ [.term 0, .hyp, .term 0, .hyp, .term 0] = some unified ∧
      Statements.theoremDecl tables.terms ⟨[], [.term 0, .hyp, .term 0, .hyp, .term 0]⟩ =
        some ⟨[], [.term 0, .term 0], .term 0⟩ := ⟨by rfl, by decide⟩

theorem recorded_hypothesis_does_not_authorize_empty_original_scope :
    checkAssertion tables ⟨[], [.term 0]⟩ commands false = false := by decide

theorem hypothesis_expression_must_have_provable_sort :
    step { tables with sorts := [⟨false, false, false, false⟩] } .assertion before .hyp = none := by decide

theorem hypothesis_is_refused_in_definition_mode : step tables .definition before .hyp = none := by decide

end Controls.Hypothesis

end Mettapedia.Languages.MM0.MeTTa.MMBStateScopeSoundness
