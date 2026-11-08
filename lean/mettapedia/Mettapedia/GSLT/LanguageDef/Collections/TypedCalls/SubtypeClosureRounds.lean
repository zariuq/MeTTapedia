import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeClosure

/-!
# Ordered subtype-closure rounds

The native closure visits one frontier against a fixed pre-round prefix.
Equal discoveries within that round are retained. A discovery already in
the prefix, or alpha-equal to an ancestor of its parent, is skipped. Parent
indices point into the earlier prefix, not into pending discoveries.

This module supplies the previously opaque repeated-subtype service from
the actual whole-row subtype query. Each finite round and every partial run
preserve resource closure and are independent of external resource worlds
under the captured dependency check. No general termination claim is made:
a finite program can generate infinitely many distinct structural types.
The round budget below is not a native instruction or allocation budget.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SubtypeClosureRounds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypeDependencyAdmission TypeScopeClosure
open RetainedTypePayloads (ExternalView)

structure Entry where
  type_ : Atom
  parent : Option Nat := none
  error : Bool := false
  deriving DecidableEq

structure State where
  known : List Entry
  frontier : Nat
  deriving DecidableEq

def start (types : List Atom) : State := ⟨types.map (fun type_ => ⟨type_, none, false⟩), 0⟩

def repeatsAncestor (alpha : Atom → Atom → Bool) (known : List Entry)
    (type_ : Atom) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, index => match known[index]? with
      | none => false
      | some entry => alpha entry.type_ type_ ||
          match entry.parent with
          | none => false
          | some parent => repeatsAncestor alpha known type_ fuel parent

def accept (alpha : Atom → Atom → Bool) (state : State) (parent : Nat) (type_ : Atom) : Bool :=
  !(state.known.any fun entry => entry.type_ == type_) &&
    !repeatsAncestor alpha state.known type_ state.known.length parent

def discoveries (alpha : Atom → Atom → Bool) (supers : Atom → List Atom) (state : State) : List Entry :=
  (state.known.zipIdx.drop state.frontier).flatMap fun (entry, index) =>
    if entry.error then [] else
      ((supers entry.type_).filter (accept alpha state index)).map
        (fun type_ => ⟨type_, some index, false⟩)

theorem discovery_origin (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (state : State) (found : Entry) (member : found ∈ discoveries alpha supers state) :
    ∃ entry index, (entry, index) ∈ state.known.zipIdx ∧
      state.frontier ≤ index ∧ entry.error = false ∧
      found.type_ ∈ supers entry.type_ ∧ found.parent = some index ∧ found.error = false := by
  simp only [discoveries, List.mem_flatMap] at member
  obtain ⟨⟨entry, index⟩, source, produced⟩ := member
  have inKnown : (entry, index) ∈ state.known.zipIdx := List.mem_of_mem_drop source
  have past : state.frontier ≤ index := by
    obtain ⟨offset, bound, atIndex⟩ := List.mem_iff_getElem.mp source
    have sameIndex := congrArg Prod.snd atIndex
    simp only [List.getElem_drop, List.getElem_zipIdx, Nat.zero_add] at sameIndex
    omega
  dsimp only at produced
  cases error : entry.error with
  | true => simp [error] at produced
  | false =>
      simp only [error, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter] at produced
      obtain ⟨type_, ⟨fromQuery, _⟩, same⟩ := produced
      subst found
      exact ⟨entry, index, inKnown, past, error, fromQuery, rfl, rfl⟩

def ParentsBefore (known : List Entry) : Prop :=
  ∀ (index : Nat) (entry : Entry), known[index]? = some entry →
    ∀ parent, entry.parent = some parent → parent < index

theorem start_parents (types : List Atom) : ParentsBefore (start types).known := by
  intro index entry found parent linked
  have present := List.mem_of_getElem? found
  obtain ⟨type_, _, rfl⟩ := List.mem_map.mp present
  cases linked

theorem discovery_parent_bound (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (state : State) (entry : Entry) (member : entry ∈ discoveries alpha supers state)
    (parent : Nat) (linked : entry.parent = some parent) : parent < state.known.length := by
  obtain ⟨_, index, present, _, _, _, parentEq, _⟩ := discovery_origin alpha supers state entry member
  have same := Option.some.inj (parentEq.symm.trans linked)
  subst parent
  simpa using List.snd_lt_of_mem_zipIdx present

theorem append_parents (known added : List Entry) (valid : ParentsBefore known)
    (parentsOld : ∀ entry ∈ added, ∀ parent, entry.parent = some parent → parent < known.length) :
    ParentsBefore (known ++ added) := by
  intro index entry found parent linked
  by_cases old : index < known.length
  · exact valid index entry ((List.getElem?_append_left old).symm.trans found) parent linked
  · have member := List.mem_of_getElem? found
    rcases List.mem_append.mp member with prior | fresh
    · obtain ⟨position, bound, atIndex⟩ := List.mem_iff_getElem.mp prior
      have earlier : known[position]? = some entry := by
        rw [List.getElem?_eq_getElem bound, atIndex]
      have smaller := valid position entry earlier parent linked
      omega
    · have smaller := parentsOld entry fresh parent linked
      omega

def step (alpha : Atom → Atom → Bool) (supers : Atom → List Atom) (state : State) : Option State :=
  let added := discoveries alpha supers state
  if added.isEmpty then none else some ⟨state.known ++ added, state.known.length⟩

theorem step_parents (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (state next : State) (valid : ParentsBefore state.known)
    (advanced : step alpha supers state = some next) : ParentsBefore next.known := by
  dsimp only [step] at advanced
  split at advanced
  · contradiction
  · cases Option.some.inj advanced
    exact append_parents _ _ valid (discovery_parent_bound alpha supers state)

/-- The finite ancestor walker reaches the same answer for every budget
above the current index. Generated parent links strictly decrease indices. -/
theorem ancestor_budget_stable (alpha : Atom → Atom → Bool) (known : List Entry)
    (valid : ParentsBefore known) (type_ : Atom) (index fuel : Nat) (enough : index < fuel) :
    repeatsAncestor alpha known type_ fuel index =
      repeatsAncestor alpha known type_ (index + 1) index := by
  induction index using Nat.strong_induction_on generalizing fuel with
  | h index ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [repeatsAncestor, repeatsAncestor]
          cases found : known[index]? with
          | none => rfl
          | some entry =>
              cases parentEq : entry.parent with
              | none => simp only [parentEq]
              | some parent =>
                  have smaller := valid index entry found parent parentEq
                  have left := ih parent smaller fuel (by omega)
                  have right := ih parent smaller index smaller
                  simp only [parentEq]
                  rw [left, right]

inductive Outcome where
  | complete (state : State)
  | unfinished (state : State)
  deriving DecidableEq

def Outcome.state : Outcome → State
  | .complete state | .unfinished state => state

def run (alpha : Atom → Atom → Bool) (supers : Atom → List Atom) : Nat → State → Outcome
  | 0, state => .unfinished state
  | fuel + 1, state => match step alpha supers state with
      | none => .complete state
      | some next => run alpha supers fuel next

theorem run_parents (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (fuel : Nat) (state : State) (valid : ParentsBefore state.known) :
    ParentsBefore (run alpha supers fuel state).state.known := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      simp only [run]
      split
      · exact valid
      · rename_i next advanced
        exact ih next (step_parents alpha supers state next valid advanced)

def resume (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (budget : Nat) : Outcome → Outcome
  | .complete state => .complete state
  | .unfinished state => run alpha supers budget state

theorem run_add (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (first second : Nat) (state : State) :
    run alpha supers (first + second) state = resume alpha supers second (run alpha supers first state) := by
  induction first generalizing state with
  | zero => simp [run, resume]
  | succ first ih =>
      rw [Nat.succ_add, run, run]
      cases advanced : step alpha supers state with
      | none => rfl
      | some next => exact ih next

theorem completed_has_no_new_round (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (fuel : Nat) (state final : State) (completed : run alpha supers fuel state = .complete final) :
    discoveries alpha supers final = [] := by
  induction fuel generalizing state with
  | zero => cases completed
  | succ fuel ih =>
      simp only [run] at completed
      cases advanced : step alpha supers state with
      | none =>
          simp only [advanced, Outcome.complete.injEq] at completed
          subst final
          dsimp only [step] at advanced
          split at advanced
          · exact List.isEmpty_iff.mp (by assumption)
          · contradiction
      | some next => exact ih next (by simpa [advanced] using completed)

def Reachable (supers : Atom → List Atom) (roots : List Atom) (type_ : Atom) : Prop :=
  ∃ root ∈ roots, Relation.ReflTransGen (fun previous next => next ∈ supers previous) root type_

theorem start_reachable (supers : Atom → List Atom) (roots : List Atom) :
    ∀ entry ∈ (start roots).known, Reachable supers roots entry.type_ := by
  intro entry member
  obtain ⟨type_, present, rfl⟩ := List.mem_map.mp member
  exact ⟨type_, present, .refl⟩

theorem step_reachable (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (roots : List Atom) (state next : State)
    (reached : ∀ entry ∈ state.known, Reachable supers roots entry.type_)
    (advanced : step alpha supers state = some next) :
    ∀ entry ∈ next.known, Reachable supers roots entry.type_ := by
  dsimp only [step] at advanced
  split at advanced
  · contradiction
  · cases Option.some.inj advanced
    intro entry member
    rcases List.mem_append.mp member with prior | fresh
    · exact reached entry prior
    · obtain ⟨parent, index, indexed, _, _, edge, _, _⟩ := discovery_origin alpha supers state entry fresh
      obtain ⟨root, rootIn, path⟩ := reached parent (List.fst_mem_of_mem_zipIdx indexed)
      exact ⟨root, rootIn, path.tail edge⟩

/-- Every published occurrence has an actual finite query path from a
seed. Equal payloads reached along different paths are not collapsed. -/
theorem run_reachable (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (roots : List Atom) (fuel : Nat) (state : State)
    (reached : ∀ entry ∈ state.known, Reachable supers roots entry.type_) :
    ∀ entry ∈ (run alpha supers fuel state).state.known, Reachable supers roots entry.type_ := by
  induction fuel generalizing state with
  | zero => exact reached
  | succ fuel ih =>
      simp only [run]
      split
      · exact reached
      · rename_i next advanced
        exact ih next (step_reachable alpha supers roots state next reached advanced)

def Safe (state : State) : Prop := ∀ entry ∈ state.known, resourceFree entry.type_ = true

theorem start_safe (types : List Atom) (safe : resourceFreeList types = true) : Safe (start types) := by
  intro entry member
  obtain ⟨type_, present, rfl⟩ := List.mem_map.mp member
  exact (resourceFreeList_iff _).mp safe type_ present

theorem discoveries_safe (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (closed : ∀ type_, resourceFree type_ = true → resourceFreeList (supers type_) = true)
    (state : State) (safe : Safe state) (entry : Entry)
    (member : entry ∈ discoveries alpha supers state) : resourceFree entry.type_ = true := by
  obtain ⟨parent, index, indexed, _, _, fromQuery, _, _⟩ := discovery_origin alpha supers state entry member
  have parentIn : parent ∈ state.known := by
    exact List.fst_mem_of_mem_zipIdx indexed
  exact (resourceFreeList_iff _).mp (closed parent.type_ (safe parent parentIn)) entry.type_ fromQuery

theorem step_safe (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (closed : ∀ type_, resourceFree type_ = true → resourceFreeList (supers type_) = true)
    (state next : State) (safe : Safe state) (advanced : step alpha supers state = some next) : Safe next := by
  dsimp only [step] at advanced
  split at advanced
  · contradiction
  · cases Option.some.inj advanced
    intro entry member
    rcases List.mem_append.mp member with old | fresh
    · exact safe entry old
    · exact discoveries_safe alpha supers closed state safe entry fresh

theorem run_safe (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (closed : ∀ type_, resourceFree type_ = true → resourceFreeList (supers type_) = true)
    (fuel : Nat) (state : State) (safe : Safe state) : Safe (run alpha supers fuel state).state := by
  induction fuel generalizing state with
  | zero => exact safe
  | succ fuel ih =>
      simp only [run]
      split
      · exact safe
      · rename_i next advanced
        exact ih next (step_safe alpha supers closed state next safe advanced)

theorem discoveries_congr (alpha : Atom → Atom → Bool) (first second : Atom → List Atom)
    (state : State) (same : ∀ entry ∈ state.known, first entry.type_ = second entry.type_) :
    discoveries alpha first state = discoveries alpha second state := by
  unfold discoveries
  apply List.flatMap_congr
  intro pair member
  have inKnown : pair ∈ state.known.zipIdx := List.mem_of_mem_drop member
  have entryIn : pair.1 ∈ state.known := List.fst_mem_of_mem_zipIdx inKnown
  rcases pair with ⟨entry, index⟩
  dsimp only at entryIn ⊢
  rw [same entry entryIn]

theorem step_congr (alpha : Atom → Atom → Bool) (first second : Atom → List Atom)
    (state : State) (same : ∀ entry ∈ state.known, first entry.type_ = second entry.type_) :
    step alpha first state = step alpha second state := by
  unfold step
  rw [discoveries_congr alpha first second state same]

theorem run_congr_safe (alpha : Atom → Atom → Bool) (first second : Atom → List Atom)
    (closed : ∀ type_, resourceFree type_ = true → resourceFreeList (first type_) = true)
    (same : ∀ type_, resourceFree type_ = true → first type_ = second type_)
    (fuel : Nat) (state : State) (safe : Safe state) :
    run alpha first fuel state = run alpha second fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have one := step_congr alpha first second state (fun entry present => same _ (safe entry present))
      simp only [run, ← one]
      cases advanced : step alpha first state with
      | none => rfl
      | some next => exact ih next (step_safe alpha first closed state next safe advanced)

/-- Full source rows, including variable-headed rows, feed each reached
closure query. Its world-independence is proved from the actual unifier. -/
theorem source_run_world (alpha : Atom → Atom → Bool) (first second : ExternalView)
    (rows : List Atom) (rowsSafe : resourceFreeList rows = true) (fresh : String)
    (fuel : Nat) (state : State) (safe : Safe state) :
    run alpha (fun type_ => subtypeQuery first type_ fresh rows) fuel state =
      run alpha (fun type_ => subtypeQuery second type_ fresh rows) fuel state := by
  apply run_congr_safe alpha _ _ ?_ ?_ fuel state safe
  · intro type_ typeSafe
    exact subtypeQuery_resourceFree first type_ fresh typeSafe rows rowsSafe
  · intro type_ typeSafe
    exact subtypeQuery_world first second type_ fresh typeSafe rows rowsSafe

theorem source_run_safe (alpha : Atom → Atom → Bool) (world : ExternalView)
    (rows : List Atom) (rowsSafe : resourceFreeList rows = true) (fresh : String)
    (fuel : Nat) (state : State) (safe : Safe state) :
    Safe (run alpha (fun type_ => subtypeQuery world type_ fresh rows) fuel state).state :=
  run_safe alpha _ (fun type_ typeSafe => subtypeQuery_resourceFree world type_ fresh typeSafe rows rowsSafe)
    fuel state safe

theorem run_known_prefix (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (fuel : Nat) (state : State) : state.known <+: (run alpha supers fuel state).state.known := by
  induction fuel generalizing state with
  | zero => exact ⟨[], by simp [run, Outcome.state]⟩
  | succ fuel ih =>
      simp only [run]
      cases advanced : step alpha supers state with
      | none => exact ⟨[], by simp [Outcome.state]⟩
      | some next =>
          have preserved : state.known <+: next.known := by
            dsimp only [step] at advanced
            split at advanced
            · contradiction
            · cases Option.some.inj advanced
              exact ⟨_, rfl⟩
          exact preserved.trans (ih next)

/-- Expose only completed closure observations. Native cache publication
still owes its separate groundness, retained-value and representation checks. -/
def completeTypes (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (budget : Nat) (seeds : List Atom) : Option (List Atom) :=
  match run alpha supers budget (start seeds) with
  | .complete final => some (final.known.map Entry.type_)
  | .unfinished _ => none

theorem completeTypes_seed_prefix (alpha : Atom → Atom → Bool) (supers : Atom → List Atom)
    (budget : Nat) (seeds result : List Atom)
    (completed : completeTypes alpha supers budget seeds = some result) : seeds <+: result := by
  unfold completeTypes at completed
  cases ran : run alpha supers budget (start seeds) with
  | unfinished _ => simp [ran] at completed
  | complete final =>
      simp only [ran, Option.some.injEq] at completed
      subst result
      have preserved := run_known_prefix alpha supers budget (start seeds)
      rw [ran] at preserved
      obtain ⟨rest, same⟩ := preserved
      dsimp only [Outcome.state] at same
      refine ⟨rest.map Entry.type_, ?_⟩
      rw [← same, List.map_append]
      simp [start, List.map_map, Function.comp_def]

theorem completeTypes_source_world (alpha : Atom → Atom → Bool) (first second : ExternalView)
    (rows : List Atom) (rowsSafe : resourceFreeList rows = true) (fresh : String)
    (budget : Nat) (seeds : List Atom) (seedSafe : resourceFreeList seeds = true) :
    completeTypes alpha (fun type_ => subtypeQuery first type_ fresh rows) budget seeds =
      completeTypes alpha (fun type_ => subtypeQuery second type_ fresh rows) budget seeds := by
  unfold completeTypes
  rw [source_run_world alpha first second rows rowsSafe fresh budget (start seeds) (start_safe seeds seedSafe)]

theorem completeTypes_source_safe (alpha : Atom → Atom → Bool) (world : ExternalView)
    (rows : List Atom) (rowsSafe : resourceFreeList rows = true) (fresh : String)
    (budget : Nat) (seeds : List Atom) (seedSafe : resourceFreeList seeds = true)
    (result : List Atom)
    (completed : completeTypes alpha (fun type_ => subtypeQuery world type_ fresh rows) budget seeds = some result) :
    resourceFreeList result = true := by
  unfold completeTypes at completed
  cases ran : run alpha (fun type_ => subtypeQuery world type_ fresh rows) budget (start seeds) with
  | unfinished _ => simp [ran] at completed
  | complete final =>
      simp only [ran, Option.some.injEq] at completed
      subst result
      have safe := source_run_safe alpha world rows rowsSafe fresh budget (start seeds) (start_safe seeds seedSafe)
      rw [ran] at safe
      apply (resourceFreeList_iff _).mpr
      intro type_ member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact safe entry present

namespace Controls

def diamond : Atom → List Atom
  | .symbol "A" => [.symbol "B", .symbol "C"]
  | .symbol "B" | .symbol "C" => [.symbol "D"]
  | _ => []

def diamondState : State := start [.symbol "A"]

theorem duplicate_discoveries_are_retained :
    ((run (· == ·) diamond 3 diamondState).state.known.map Entry.type_) =
      [.symbol "A", .symbol "B", .symbol "C", .symbol "D", .symbol "D"] := by decide

theorem diamond_needs_empty_round_to_finish :
    (∃ state, run (· == ·) diamond 2 diamondState = .complete state) = False := by
  have pending : run (· == ·) diamond 2 diamondState = .unfinished
      ⟨[⟨.symbol "A", none, false⟩, ⟨.symbol "B", some 0, false⟩,
        ⟨.symbol "C", some 0, false⟩, ⟨.symbol "D", some 1, false⟩,
        ⟨.symbol "D", some 2, false⟩], 3⟩ := by decide
  simp [pending]

def cycle : Atom → List Atom
  | .symbol "A" => [.symbol "B"]
  | .symbol "B" => [.symbol "A"]
  | _ => []

theorem known_type_stops_cycle :
    run (· == ·) cycle 2 (start [.symbol "A"]) =
      .complete ⟨[⟨.symbol "A", none, false⟩, ⟨.symbol "B", some 0, false⟩], 1⟩ := by decide

def alphaVariables : Atom → Atom → Bool
  | .var _, .var _ => true
  | left, right => left == right

def renameVariable : Atom → List Atom
  | .var "a" => [.var "b"]
  | _ => []

theorem ancestor_renaming_is_not_structural_equality :
    discoveries alphaVariables renameVariable (start [.var "a"]) = [] ∧
    discoveries (· == ·) renameVariable (start [.var "a"]) = [⟨.var "b", some 0, false⟩] := by decide

theorem repeated_seeds_keep_distinct_parents :
    discoveries (· == ·) diamond (start [.symbol "B", .symbol "C", .symbol "B"]) =
      [⟨.symbol "D", some 0, false⟩, ⟨.symbol "D", some 1, false⟩,
        ⟨.symbol "D", some 2, false⟩] := by decide

theorem same_round_set_deduplication_changes_answer :
    (discoveries (· == ·) diamond (start [.symbol "B", .symbol "C"])).map Entry.type_ ≠
      [.symbol "D"] := by decide

theorem error_entries_do_not_produce_supertypes :
    discoveries (· == ·) diamond ⟨[⟨.symbol "A", none, true⟩], 0⟩ = [] := by decide

theorem partial_closure_is_not_publishable :
    completeTypes (· == ·) diamond 2 [.symbol "A"] = none ∧
    completeTypes (· == ·) diamond 3 [.symbol "A"] =
      some [.symbol "A", .symbol "B", .symbol "C", .symbol "D", .symbol "D"] := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SubtypeClosureRounds
