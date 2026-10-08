import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBDependencySoundness

/-!
# MMB argument initialization in the retained context

Descriptor loading validates ranks against the preceding argument history.
The proofs below invert that actual fold and use the existing kernel typing
and occurrence-support judgments. Term-proof return-validation allocations
remain governed by the retained corrected initializer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBInitializationSoundness

open Formats.MMB Kernel
open MMBMachineSoundness MMBDependencySoundness

theorem loadArgs_descriptor_checked (sorts : List SortInfo) (args : List ExprType)
    (loaded : Formats.MMB.State) (accepted : loadArgs sorts args = some loaded)
    (position : Nat) (type : ExprType) (read : args[position]? = some type) :
    if type.bound then
      type.deps = {(Statements.boundPositions (args.take position)).length}
    else type.deps ⊆ Finset.range (Statements.boundPositions (args.take position)).length := by
  let advance : Formats.MMB.State → ExprType × Nat → Option Formats.MMB.State := fun state (type, position) => do
    let info ← sorts[type.sort]?
    if type.bound then
      if info.strict = false ∧ type.deps = {state.nextBound} then
        let (state, e) := state.alloc ⟨.var position, type⟩
        some { state with
          heap := state.heap ++ [.expr e]
          nextBound := state.nextBound + 1
          varCount := state.varCount + 1 }
      else none
    else if type.deps ⊆ Finset.range state.nextBound then
      let (state, e) := state.alloc ⟨.var position, type⟩
      some { state with heap := state.heap ++ [.expr e], varCount := state.varCount + 1 }
    else none
  change args.zipIdx.foldlM advance ⟨[], [], [], [], 0, 0⟩ = some loaded at accepted
  obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp read
  have prefixLength : (args.take position).length = position := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]
  have splitArgs : args = args.take position ++ type :: args.drop (position + 1) := by
    rw [← value, ← List.drop_eq_getElem_cons inside, List.take_append_drop]
  have rows : args.zipIdx = (args.take position).zipIdx ++
      (type, position) :: (args.drop (position + 1)).zipIdx (position + 1) := by
    conv_lhs => rw [splitArgs]
    simp only [List.zipIdx_append, List.zipIdx_cons, Nat.zero_add, prefixLength]
  rw [rows, List.foldlM_append] at accepted
  obtain ⟨before, prefixRead, following⟩ := Option.bind_eq_some_iff.mp accepted
  have prefixLoaded : loadArgs sorts (args.take position) = some before := prefixRead
  obtain ⟨_, _, _, _, _, boundCount⟩ := MMBExecution.loadArgs_variable_shape sorts (args.take position) before prefixLoaded
  change (advance before (type, position)).bind _ = some loaded at following
  obtain ⟨after, advanced, _⟩ := Option.bind_eq_some_iff.mp following
  change (sorts[type.sort]?).bind _ = some after at advanced
  obtain ⟨info, _, checked⟩ := Option.bind_eq_some_iff.mp advanced
  split at checked
  · rename_i bound
    split at checked
    · rename_i passed
      simpa [bound, boundCount] using passed.2
    · cases checked
  · rename_i regular
    split at checked
    · rename_i passed
      simpa [regular, boundCount] using passed
    · cases checked

theorem boundPositions_split_at_bound (args : List ExprType) (position : Nat) (type : ExprType)
    (read : args[position]? = some type) (bound : type.bound = true) :
    ∃ suffix, Statements.boundPositions args = Statements.boundPositions (args.take position) ++ position :: suffix := by
  obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp read
  have prefixLength : (args.take position).length = position := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]
  have splitArgs : args = args.take position ++ type :: args.drop (position + 1) := by
    rw [← value, ← List.drop_eq_getElem_cons inside, List.take_append_drop]
  refine ⟨(((args.drop (position + 1)).zipIdx (position + 1)).filter (·.1.bound)).map (·.2), ?_⟩
  show Statements.boundPositions args = Statements.boundPositions (args.take position) ++
      position :: (((args.drop (position + 1)).zipIdx (position + 1)).filter (·.1.bound)).map (·.2)
  ·
    conv_lhs => rw [splitArgs]
    simp only [Statements.boundPositions, List.zipIdx_append, List.zipIdx_cons, Nat.zero_add,
      prefixLength, List.filter_append, List.filter_cons, bound, ↓reduceIte, List.map_append, List.map_cons]

theorem boundPositions_getD_at_bound (args : List ExprType) (position : Nat) (type : ExprType)
    (read : args[position]? = some type) (bound : type.bound = true) :
    (Statements.boundPositions args).getD (Statements.boundPositions (args.take position)).length
      (Statements.boundPositions (args.take position)).length = position := by
  obtain ⟨suffix, positions⟩ := boundPositions_split_at_bound args position type read bound
  rw [List.getD_eq_getElem?_getD, positions]
  simp

theorem bound_rank_lt (args : List ExprType) (position : Nat) (type : ExprType)
    (read : args[position]? = some type) (bound : type.bound = true) :
    (Statements.boundPositions (args.take position)).length < (Statements.boundPositions args).length := by
  obtain ⟨suffix, positions⟩ := boundPositions_split_at_bound args position type read bound
  rw [positions, List.length_append, List.length_cons]
  omega

theorem rankPositions_context (args : List ExprType) :
    Soundness.rankPositions (Statements.context args) = Statements.boundPositions args := by
  unfold Soundness.rankPositions Statements.context
  rw [List.zipIdx_map, List.filter_map, List.map_map]
  have predicate : (fun row : ExprType × Nat => match Statements.binder (Statements.boundPositions args) row.1 with
      | .bound _ => true | .regular _ _ => false) = (fun row : ExprType × Nat => row.1.bound) := by
    funext row
    cases bound : row.1.bound <;> simp [Statements.binder, bound]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  exact congrArg (fun selected => (args.zipIdx.filter selected).map (·.2)) predicate

theorem loadArgs_allocation (sorts : List SortInfo) (args : List ExprType)
    (loaded : Formats.MMB.State) (accepted : loadArgs sorts args = some loaded)
    (position : Nat) (allocation : Alloc) (read : loaded.store[position]? = some allocation) :
    ∃ type, args[position]? = some type ∧ allocation = ⟨.var position, type⟩ := by
  obtain ⟨store, _, _, _, _, _⟩ := MMBExecution.loadArgs_variable_shape sorts args loaded accepted
  have inside : position < args.length := by
    have allocated := (List.getElem?_eq_some_iff.mp read).choose
    simpa only [store, List.length_map, List.length_zipIdx] using allocated
  have found : loaded.store[position]? = some (⟨.var position, args[position]'inside⟩ : Alloc) := by
    rw [store, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem inside]
    simp
  exact ⟨args[position]'inside, List.getElem?_eq_getElem inside, Option.some.inj (read.symm.trans found)⟩

theorem loadArgs_initial_store_typed (signature : TermSignature) (sorts : List SortInfo)
    (args : List ExprType) (loaded : Formats.MMB.State) (accepted : loadArgs sorts args = some loaded) :
    TypedStore signature (Statements.context args) loaded.store := by
  constructor
  intro position allocation read
  obtain ⟨type, typeRead, same⟩ := loadArgs_allocation sorts args loaded accepted position allocation read
  subst allocation
  have decoded : Soundness.decode loaded.store position = some (.var position) := by
    rw [Soundness.decode, read]
  have lookup : (Statements.context args)[position]? =
      some (Statements.binder (Statements.boundPositions args) type) := by
    simp only [Statements.context, List.getElem?_map, typeRead, Option.map_some]
  have binderSort : (Statements.binder (Statements.boundPositions args) type).sort = type.sort := by
    unfold Statements.binder
    split <;> rfl
  refine ⟨.var position, decoded, ?_, ?_⟩
  · rw [← binderSort]
    exact .var lookup
  · intro bound
    change type.bound = true at bound
    exact ⟨position, rfl, by simpa only [Statements.binder, bound, ↓reduceIte] using lookup⟩

theorem loadArgs_initial_store_ranked (sorts : List SortInfo) (args : List ExprType)
    (loaded : Formats.MMB.State) (accepted : loadArgs sorts args = some loaded) :
    RankedStore (Statements.context args) loaded.store := by
  have mapped : ∀ (position : Nat) (type : ExprType), args[position]? = some type →
      (if type.bound then {position} else Soundness.positionsOf (Statements.context args) type.deps) =
        Soundness.positionsOf (Statements.context args) type.deps := by
    intro position type typeRead
    have checked := loadArgs_descriptor_checked sorts args loaded accepted position type typeRead
    cases bound : type.bound with
    | false => rfl
    | true =>
        rw [bound] at checked
        simp only [↓reduceIte]
        rw [Soundness.positionsOf, checked, Finset.image_singleton, rankPositions_context,
          boundPositions_getD_at_bound args position type typeRead bound]
  constructor
  · intro position allocation read
    obtain ⟨type, typeRead, same⟩ := loadArgs_allocation sorts args loaded accepted position allocation read
    subst allocation
    have decoded : Soundness.decode loaded.store position = some (.var position) := by
      rw [Soundness.decode, read]
    have lookup : (Statements.context args)[position]? =
        some (Statements.binder (Statements.boundPositions args) type) := by
      simp only [Statements.context, List.getElem?_map, typeRead, Option.map_some]
    refine ⟨.var position, decoded, ?_⟩
    cases bound : type.bound with
    | false =>
        have support : Preterm.Supports (Statements.context args) (.var position)
            (Soundness.positionsOf (Statements.context args) type.deps) := by
          apply Preterm.Supports.regular (sort := type.sort)
          simpa only [Statements.binder, bound, Bool.false_eq_true, ↓reduceIte, Soundness.positionsOf,
            rankPositions_context] using lookup
        exact support
    | true =>
        have support : Preterm.Supports (Statements.context args) (.var position) {position} :=
          .bound (by simpa only [Statements.binder, bound, ↓reduceIte] using lookup)
        have supports := mapped position type typeRead
        simp only [bound, ↓reduceIte] at supports
        rw [← supports]
        exact support
  · intro position allocation read rank occurs
    obtain ⟨type, typeRead, same⟩ := loadArgs_allocation sorts args loaded accepted position allocation read
    subst allocation
    rw [rankPositions_context]
    have checked := loadArgs_descriptor_checked sorts args loaded accepted position type typeRead
    cases bound : type.bound with
    | false =>
        rw [bound] at checked
        have earlier := Finset.mem_range.mp (checked occurs)
        obtain ⟨suffix, positions⟩ := boundPositions_take_prefix args position
        rw [positions, List.length_append]
        omega
    | true =>
        rw [bound] at checked
        have sameRank : rank = (Statements.boundPositions (args.take position)).length := by
          rw [checked] at occurs
          exact Finset.mem_singleton.mp occurs
        rw [sameRank]
        exact bound_rank_lt args position type typeRead bound

private theorem lookup_context_append (context suffix : Context) (position : Nat) (binder : Binder)
    (read : context[position]? = some binder) : (context ++ suffix)[position]? = some binder := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).choose]
  exact read

theorem supports_context_append (context suffix : Context) (expression : Preterm) (dependencies : Finset Nat)
    (support : Preterm.Supports context expression dependencies) :
    Preterm.Supports (context ++ suffix) expression dependencies := by
  induction support with
  | bound lookup => exact .bound (lookup_context_append context suffix _ _ lookup)
  | regular lookup => exact .regular (lookup_context_append context suffix _ _ lookup)
  | term index => exact .term index
  | app _ _ first second => exact .app first second

theorem typing_context_append (signature : TermSignature) (context suffix remaining : Context)
    (expression : Preterm) (sort : Nat) (typing : Preterm.HasType signature context expression remaining sort) :
    Preterm.HasType signature (context ++ suffix) expression remaining sort := by
  induction typing with
  | var lookup => exact .var (lookup_context_append context suffix _ _ lookup)
  | term lookup => exact .term lookup
  | bound _ lookup functionTyping => exact .bound functionTyping (lookup_context_append context suffix _ _ lookup)
  | regular _ _ functionTyping argumentTyping => exact .regular functionTyping argumentTyping

theorem rankPositions_append (context suffix : Context) :
    Soundness.rankPositions (context ++ suffix) = Soundness.rankPositions context ++
      (suffix.zipIdx context.length |>.filter (fun row => match row.1 with
        | .bound _ => true | .regular _ _ => false)).map (·.2) := by
  simp only [Soundness.rankPositions, List.zipIdx_append, Nat.zero_add, List.filter_append, List.map_append]
  rfl

theorem positionsOf_append_old (context suffix : Context) (dependencies : Finset Nat)
    (bounded : ∀ rank ∈ dependencies, rank < (Soundness.rankPositions context).length) :
    Soundness.positionsOf (context ++ suffix) dependencies = Soundness.positionsOf context dependencies := by
  apply Finset.image_congr
  intro rank member
  change (Soundness.rankPositions (context ++ suffix)).getD rank rank =
    (Soundness.rankPositions context).getD rank rank
  rw [List.getD_eq_getElem?_getD, rankPositions_append,
    List.getElem?_append_left (bounded rank member), List.getD_eq_getElem?_getD]

theorem typed_store_context_append (signature : TermSignature) (context suffix : Context)
    (store : List Alloc) (typed : TypedStore signature context store) :
    TypedStore signature (context ++ suffix) store := by
  constructor
  intro position allocation read
  obtain ⟨expression, decoded, typing, bound⟩ := typed.expression position allocation read
  refine ⟨expression, decoded, typing_context_append signature context suffix [] expression allocation.type.sort typing, ?_⟩
  intro isBound
  obtain ⟨index, same, lookup⟩ := bound isBound
  exact ⟨index, same, lookup_context_append context suffix index _ lookup⟩

theorem ranked_store_context_append (context suffix : Context) (store : List Alloc)
    (ranked : RankedStore context store) : RankedStore (context ++ suffix) store := by
  constructor
  · intro position allocation read
    obtain ⟨expression, decoded, support⟩ := ranked.supported position allocation read
    refine ⟨expression, decoded, ?_⟩
    rw [positionsOf_append_old context suffix allocation.type.deps (ranked.bounded position allocation read)]
    exact supports_context_append context suffix expression _ support
  · intro position allocation read rank member
    rw [rankPositions_append, List.length_append]
    exact Nat.lt_of_lt_of_le (ranked.bounded position allocation read rank member) (Nat.le_add_right _ _)

/-- Future dummy binders are fixed independently of the initialized store.
The initializer earns typing and complete support in that complete context. -/
theorem loadArgs_initial_fixed_context (signature : TermSignature) (sorts : List SortInfo)
    (args : List ExprType) (dummySorts : List Nat) (loaded : Formats.MMB.State)
    (accepted : loadArgs sorts args = some loaded) :
    TypedStore signature (Statements.context args ++ dummySorts.map Binder.bound) loaded.store ∧
      RankedStore (Statements.context args ++ dummySorts.map Binder.bound) loaded.store := by
  exact ⟨typed_store_context_append signature _ _ _ (loadArgs_initial_store_typed signature sorts args loaded accepted),
    ranked_store_context_append _ _ _ (loadArgs_initial_store_ranked sorts args loaded accepted)⟩

/-- Return validation remains an actual prior check. Its temporary allocation
is discarded by the retained initializer before the fixed-context proof state. -/
theorem termProof_initial_fixed_context (signature : TermSignature) (sorts : List SortInfo)
    (args : List ExprType) (ret : ExprType) (dummySorts : List Nat) (loaded : Formats.MMB.State)
    (accepted : loadArgs sorts (args ++ [ret]) = some loaded) (regularReturn : ret.bound = false) :
    TypedStore signature (Statements.context args ++ dummySorts.map Binder.bound) (loaded.forTermProof args.length).store ∧
      RankedStore (Statements.context args ++ dummySorts.map Binder.bound) (loaded.forTermProof args.length).store := by
  exact loadArgs_initial_fixed_context signature sorts args dummySorts (loaded.forTermProof args.length)
    (MMBExecution.validated_return_initializes_arguments sorts args ret loaded accepted regularReturn)

namespace Controls

private def sorts : List SortInfo := [⟨false, false, false, false⟩, ⟨false, false, false, false⟩]
private def args : List ExprType :=
  [⟨0, false, ∅⟩, ⟨0, true, {0}⟩, ⟨0, false, {0}⟩, ⟨1, true, {1}⟩, ⟨0, false, {0, 1}⟩]
private def initial : Formats.MMB.State :=
  ⟨args.zipIdx.map (fun row => ⟨.var row.2, row.1⟩), [], (List.range 5).map Elem.expr, [], 2, 5⟩
private def dummySorts : List Nat := [1, 0]
private def finalContext : Context := Statements.context args ++ dummySorts.map Binder.bound
private def ret : ExprType := ⟨0, false, {0, 1}⟩
private def combined : Formats.MMB.State :=
  { initial with
    store := initial.store ++ [⟨.var 5, ret⟩]
    heap := initial.heap ++ [.expr 5]
    varCount := 6 }

private theorem accepted : loadArgs sorts args = some initial := by decide

theorem interleaved_descriptors_initialize_fixed_context :
    loadArgs sorts args = some initial ∧
      TypedStore (fun _ => none) finalContext initial.store ∧ RankedStore finalContext initial.store :=
  ⟨accepted, loadArgs_initial_fixed_context (fun _ => none) sorts args dummySorts initial accepted⟩

theorem preceding_history_earns_second_bound_rank :
    (args[3]?).map (·.deps) = some {(Statements.boundPositions (args.take 3)).length} := by
  have checked := loadArgs_descriptor_checked sorts args initial accepted 3 ⟨1, true, {1}⟩ rfl
  change ({1} : Finset Nat) = {(Statements.boundPositions (args.take 3)).length} at checked
  change some ({1} : Finset Nat) = some {(Statements.boundPositions (args.take 3)).length}
  exact congrArg some checked

theorem parameter_support_preserves_nonmatching_ranks_and_positions :
    Preterm.Supports finalContext (.var 4) {1, 3} := by
  have ranked := (loadArgs_initial_fixed_context (fun _ => none) sorts args dummySorts initial accepted).2
  obtain ⟨expression, decoded, support⟩ := ranked.supported 4 ⟨.var 4, ⟨0, false, {0, 1}⟩⟩ rfl
  have actual : Soundness.decode initial.store 4 = some (.var 4) := by
    rw [Soundness.decode]
    rfl
  have same := Option.some.inj (decoded.symm.trans actual)
  subst expression
  change Preterm.Supports finalContext (.var 4) (Soundness.positionsOf finalContext {0, 1}) at support
  have projected : Soundness.positionsOf finalContext {0, 1} = {1, 3} := by decide
  rw [projected] at support
  exact support

theorem future_dummies_are_fresh_for_parameter_support :
    Preterm.FreshFor finalContext 5 (.var 4) ∧ Preterm.FreshFor finalContext 6 (.var 4) := by
  have support := parameter_support_preserves_nonmatching_ranks_and_positions
  constructor
  · refine ⟨⟨_, support⟩, ?_⟩
    intro occurs
    have member := (support.mem_iff_hasVar 5).mpr occurs
    simp at member
  · refine ⟨⟨_, support⟩, ?_⟩
    intro occurs
    have member := (support.mem_iff_hasVar 6).mpr occurs
    simp at member

theorem first_future_dummy_follows_public_variables :
    (Soundness.rankPositions finalContext).getD initial.nextBound initial.nextBound = args.length ∧
      finalContext[args.length]? = some (.bound 1) := by decide

theorem return_validation_preserves_fixed_context_initializer :
    loadArgs sorts (args ++ [ret]) = some combined ∧
      combined.forTermProof args.length = initial ∧
      TypedStore (fun _ => none) finalContext (combined.forTermProof args.length).store ∧
      RankedStore finalContext (combined.forTermProof args.length).store := by
  have combinedRead : loadArgs sorts (args ++ [ret]) = some combined := by decide
  exact ⟨combinedRead, by decide,
    termProof_initial_fixed_context (fun _ => none) sorts args ret dummySorts combined combinedRead rfl⟩

theorem incorrect_first_bound_rank_refused :
    loadArgs sorts [⟨0, false, ∅⟩, ⟨0, true, {1}⟩] = none := by decide

theorem dependency_on_future_bound_argument_refused :
    loadArgs sorts [⟨0, false, {0}⟩, ⟨0, true, {0}⟩] = none := by decide

theorem out_of_range_regular_dependency_refused :
    loadArgs sorts [⟨0, true, {0}⟩, ⟨0, false, {1}⟩] = none := by decide

theorem strict_bound_sort_refused :
    loadArgs [⟨false, true, false, false⟩] [⟨0, true, {0}⟩] = none := by decide

theorem unknown_parameter_sort_refused : loadArgs sorts [⟨2, false, ∅⟩] = none := by decide

theorem free_sort_parameter_is_distinct_from_fresh_dummy :
    (loadArgs [⟨false, false, false, true⟩] [⟨0, true, {0}⟩]).isSome = true ∧
      step ⟨[⟨false, false, false, true⟩], [], []⟩ .assertion ⟨[], [], [], [], 0, 0⟩ (.dummy 0) = none := by decide

end Controls

end Mettapedia.Languages.MM0.MeTTa.MMBInitializationSoundness
