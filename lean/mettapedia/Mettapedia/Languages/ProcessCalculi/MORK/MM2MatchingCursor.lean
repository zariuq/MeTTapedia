import Mettapedia.Languages.ProcessCalculi.MORK.Conformance
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.GSLT.LanguageDef.NativeControlCursor

/-!
# Resumable MM2 input matching

The cursor retains a stack of factor joins and source-entry scans. It never
materializes the join before starting. A poll opens one factor, tries one
finite structural atom match, backtracks, or yields one complete row.
Witnesses retain source positions, including equal atoms at different positions.

The local atom matcher traverses finite syntax and substitutions; a poll is
not a constant-time CPU claim. Recursive evaluation and foreign sources are
not operations of this input fragment. Whole-firing publication belongs to
the separate batch boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingCursor

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull collect)
open Conformance.Computable

abbrev Entry := Atom × Nat
abbrev Row := Subst × List Entry

def eraseRow (row : Row) : Subst × List Atom :=
  (row.1, row.2.map Prod.fst)

def entries (space : List Atom) : List Entry := space.zipIdx

@[simp] theorem entries_atoms (space : List Atom) :
    (entries space).map Prod.fst = space := by simp [entries]

def factors : InputSpec → List SourceFactor
  | .compat pattern => pattern.atoms.map SourceFactor.btm
  | .explicit sources => sources

/-- Selecting candidates does not run the matcher or enumerate join rows. -/
def candidates (space : List Entry) (substitution : Subst) :
    SourceFactor → Atom × List Entry
  | .btm pattern => (pattern, space)
  | .eqConstraint pattern witness =>
      let target := applySubst substitution pattern
      (witness, (space.find? fun item => item.1 == target).toList)
  | .neqConstraint pattern witness =>
      let target := applySubst substitution pattern
      (witness, space.eraseP fun item => item.1 == target)

/-- Independent finite join denotation, retaining physical witness positions. -/
def rows (space : List Entry) : List SourceFactor → Subst → List Entry → List Row
  | [], substitution, witnesses => [(substitution, witnesses)]
  | source :: rest, substitution, witnesses =>
      let selected := candidates space substitution source
      selected.2.flatMap fun item =>
        match matchAtom substitution selected.1 item.1 with
        | none => []
        | some next => rows space rest next (item :: witnesses)

inductive Work where
  | join (remaining : List SourceFactor) (substitution : Subst) (witnesses : List Entry)
  | scan (pattern : Atom) (remaining : List SourceFactor) (candidates : List Entry)
      (substitution : Subst) (witnesses : List Entry)
  deriving Repr

abbrev State := List Work

def start (_space : List Atom) (input : InputSpec) (substitution : Subst := []) :
    State := [.join (factors input) substitution []]

def pull (space : List Entry) : State → Pull State Row
  | [] => .done
  | .join [] substitution witnesses :: pending =>
      .yield (substitution, witnesses) pending
  | .join (source :: rest) substitution witnesses :: pending =>
      let selected := candidates space substitution source
      .suspend (.scan selected.1 rest selected.2 substitution witnesses :: pending)
  | .scan _ _ [] _ _ :: pending => .suspend pending
  | .scan pattern rest (item :: remaining) substitution witnesses :: pending =>
      let later := .scan pattern rest remaining substitution witnesses :: pending
      match matchAtom substitution pattern item.1 with
      | none => .suspend later
      | some next => .suspend (.join rest next (item :: witnesses) :: later)

def workRows (space : List Entry) : Work → List Row
  | .join remaining substitution witnesses => rows space remaining substitution witnesses
  | .scan pattern remaining pending substitution witnesses =>
      pending.flatMap fun item =>
        match matchAtom substitution pattern item.1 with
        | none => []
        | some next => rows space remaining next (item :: witnesses)

def residualRows (space : List Entry) (state : State) : List Row :=
  state.flatMap (workRows space)

/-- The local semantic law accounts for all unfinished joins, not only ready rows. -/
theorem pull_rows (space : List Entry) (state : State) :
    match pull space state with
    | .done => residualRows space state = []
    | .suspend next => residualRows space state = residualRows space next
    | .yield row next => residualRows space state = row :: residualRows space next := by
  cases state with
  | nil => rfl
  | cons work pending =>
      cases work with
      | join remaining substitution witnesses =>
          cases remaining <;> rfl
      | scan pattern remaining pool substitution witnesses =>
          cases pool with
          | nil => rfl
          | cons item rest =>
              simp only [pull]
              cases matched : matchAtom substitution pattern item.1 <;>
                simp [matched, residualRows, workRows, List.flatMap_cons,
                  List.append_assoc]

/-- A finite upper bound counting scans, factor openings, yields, and backtracks.
This bound is a proof/reference calculation; the cursor does not compute it. -/
def joinCost (space : List Entry) : List SourceFactor → Subst → Nat
  | [], _ => 1
  | source :: remaining, substitution =>
      let selected := candidates space substitution source
      2 + (selected.2.map fun item =>
        1 + match matchAtom substitution selected.1 item.1 with
        | none => 0
        | some next => joinCost space remaining next).sum

def workCost (space : List Entry) : Work → Nat
  | .join remaining substitution _ => joinCost space remaining substitution
  | .scan pattern remaining pool substitution _ =>
      1 + (pool.map fun item =>
        1 + match matchAtom substitution pattern item.1 with
        | none => 0
        | some next => joinCost space remaining next).sum

def remainingCost (space : List Entry) (state : State) : Nat :=
  (state.map (workCost space)).sum

/-- Every nonterminal poll strictly consumes finite matcher-generation work. -/
theorem pull_cost (space : List Entry) (state : State) :
    match pull space state with
    | .done => remainingCost space state = 0
    | .suspend next => remainingCost space next < remainingCost space state
    | .yield _ next => remainingCost space next < remainingCost space state := by
  cases state with
  | nil => rfl
  | cons work pending =>
      cases work with
      | join remaining substitution witnesses =>
          cases remaining with
          | nil => simp [pull, remainingCost, workCost, joinCost]
          | cons source rest =>
              simp only [pull, remainingCost, List.map_cons, List.sum_cons, workCost,
                joinCost]
              omega
      | scan pattern remaining pool substitution witnesses =>
          cases pool with
          | nil => simp [pull, remainingCost, workCost]
          | cons item rest =>
              simp only [pull]
              cases matched : matchAtom substitution pattern item.1 <;>
                simp [matched, remainingCost, workCost, List.sum_cons]
              omega

/-- Finite inputs exhaust after a stated finite number of real polls. -/
theorem collect_complete (space : List Entry) (fuel : Nat) (state : State)
    (enough : remainingCost space state < fuel) :
    collect (pull space) fuel state = some (residualRows space state) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have sound := pull_rows space state
      have decrease := pull_cost space state
      cases moved : pull space state with
      | done =>
          simp only [moved] at sound
          simp [collect, moved, sound]
      | suspend next =>
          simp only [moved] at sound decrease
          have small : remainingCost space next < fuel := by omega
          simp [collect, moved, ih next small, sound]
      | yield row next =>
          simp only [moved] at sound decrease
          have small : remainingCost space next < fuel := by omega
          simp [collect, moved, ih next small, sound]

/-- Insufficient fuel never fabricates a partial collection as the full join. -/
theorem collect_sound (space : List Entry) (fuel : Nat) (state : State)
    (result : List Row) (completed : collect (pull space) fuel state = some result) :
    result = residualRows space state := by
  induction fuel generalizing state result with
  | zero => simp [collect] at completed
  | succ fuel ih =>
      have sound := pull_rows space state
      cases moved : pull space state with
      | done =>
          simp only [moved] at sound
          simpa [collect, moved, sound] using completed.symm
      | suspend next =>
          simp only [moved] at sound
          simp only [collect, moved] at completed
          exact (ih next result completed).trans sound.symm
      | yield row next =>
          simp only [moved] at sound
          simp only [collect, moved] at completed
          cases found : collect (pull space) fuel next with
          | none => simp [found] at completed
          | some tail =>
              simp only [found, Option.map_some, Option.some.injEq] at completed
              subst result
              rw [ih next tail found, sound]

abbrev provider (space : List Entry) := NativeControlCursor.provider (pull space)

theorem pause_resume_exact (space : List Entry) (first second : Nat)
    (state : State) (reversed : List Row) :
    Mettapedia.Machines.Cursor.advance (provider space) (NativeControlCursor.client Row)
      (fun _ _ => 1) (first + second)
      (NativeControlCursor.packet (pull space) state reversed) =
    Mettapedia.Machines.Cursor.resume (provider space) (NativeControlCursor.client Row)
      (fun _ _ => 1) second
      (Mettapedia.Machines.Cursor.advance (provider space) (NativeControlCursor.client Row)
        (fun _ _ => 1) first (NativeControlCursor.packet (pull space) state reversed)) :=
  NativeControlCursor.chunk_exact _ _ _ _ _

theorem find_atoms (space : List Entry) (target : Atom) :
    ((space.find? fun item => item.1 == target).toList.map Prod.fst) =
      if (space.map Prod.fst).contains target then [target] else [] := by
  induction space with
  | nil => simp
  | cons item rest ih =>
      by_cases equal : item.1 = target
      · simp [equal]
      · have unequal : (item.1 == target) = false := by simp [equal]
        have reversed : (target == item.1) = false := by simp [Ne.symm equal]
        rw [List.map_cons, List.contains_cons, reversed]
        simpa only [List.find?_cons, unequal, Bool.false_eq_true, if_false,
          Bool.false_or] using ih

theorem erase_atoms (space : List Entry) (target : Atom) :
    (space.eraseP fun item => item.1 == target).map Prod.fst =
      (space.map Prod.fst).erase target := by
  induction space with
  | nil => simp
  | cons item rest ih =>
      by_cases equal : item.1 = target
      · simp [equal]
      · have unequal : (item.1 == target) = false := by simp [equal]
        simp [unequal, ih]

def candidateMatches (space : List Entry) (substitution : Subst)
    (source : SourceFactor) : List (Subst × Entry) :=
  let selected := candidates space substitution source
  selected.2.filterMap fun item =>
    (matchAtom substitution selected.1 item.1).map (·, item)

theorem matched_entries_erase (space : List Entry) (substitution : Subst)
    (pattern : Atom) :
    (space.filterMap fun item =>
      (matchAtom substitution pattern item.1).map (·, item)).map
        (fun item => (item.1, item.2.1)) =
    (space.map Prod.fst).filterMap fun item =>
      (matchAtom substitution pattern item).map (·, item) := by
  simp only [List.map_filterMap, List.filterMap_map, Option.map_map,
    Function.comp_def]

theorem candidateMatches_erase (space : List Entry) (substitution : Subst)
    (source : SourceFactor) :
    (candidateMatches space substitution source).map (fun item => (item.1, item.2.1)) =
      cmatchSourceFactor substitution (space.map Prod.fst) source := by
  unfold candidateMatches
  rw [matched_entries_erase]
  cases source with
  | btm pattern => simp [candidates, cmatchSourceFactor, Conformance.cmatchAtom_eq_matchAtom]
  | eqConstraint pattern witness =>
      simp only [candidates, find_atoms, cmatchSourceFactor,
        Conformance.cmatchAtom_eq_matchAtom]
      split_ifs
      · simp only [List.filterMap_cons, List.filterMap_nil]
        cases matchAtom substitution witness (applySubst substitution pattern) <;> rfl
      · rfl
  | neqConstraint pattern witness =>
      simp [candidates, erase_atoms, cmatchSourceFactor, Conformance.cmatchAtom_eq_matchAtom]

theorem flatMap_matched (space : List Entry) (substitution : Subst) (pattern : Atom)
    (continuation : Subst → Entry → List Row) :
    space.flatMap (fun item => match matchAtom substitution pattern item.1 with
      | none => []
      | some next => continuation next item) =
    (space.filterMap fun item =>
      (matchAtom substitution pattern item.1).map (·, item)).flatMap
        (fun pair => continuation pair.1 pair.2) := by
  induction space with
  | nil => rfl
  | cons item rest ih =>
      cases matched : matchAtom substitution pattern item.1 <;> simp [matched, ih]

theorem rows_cons (space : List Entry) (source : SourceFactor)
    (remaining : List SourceFactor) (substitution : Subst) (witnesses : List Entry) :
    rows space (source :: remaining) substitution witnesses =
      (candidateMatches space substitution source).flatMap fun found =>
        rows space remaining found.1 (found.2 :: witnesses) := by
  change (candidates space substitution source).2.flatMap
    (fun item => match matchAtom substitution (candidates space substitution source).1 item.1 with
      | none => []
      | some next => rows space remaining next (item :: witnesses)) = _
  unfold candidateMatches
  exact flatMap_matched (candidates space substitution source).2 substitution
    (candidates space substitution source).1
    (fun next item => rows space remaining next (item :: witnesses))

/-- Forgetting positions agrees with the existing executable input semantics,
including its witness lists and enumeration order. -/
theorem rows_erase (space : List Entry) (sources : List SourceFactor)
    (substitution : Subst) (witnesses : List Entry) :
    (rows space sources substitution witnesses).map eraseRow =
      cmatchSourceFactors.go (space.map Prod.fst) sources substitution
        (witnesses.map Prod.fst) := by
  induction sources generalizing substitution witnesses with
  | nil => rfl
  | cons source remaining ih =>
      rw [rows_cons, List.map_flatMap]
      simp_rw [ih]
      rw [cmatchSourceFactors.go, ← candidateMatches_erase space substitution source]
      simp [List.flatMap_map]

theorem btm_factors (space : List Atom) (patterns : List Atom)
    (substitution : Subst) (witnesses : List Atom) :
    cmatchSourceFactors.go space (patterns.map SourceFactor.btm) substitution witnesses =
      cmatchPattern.go space patterns substitution witnesses := by
  induction patterns generalizing substitution witnesses with
  | nil => rfl
  | cons pattern rest ih =>
      simp only [List.map_cons, cmatchSourceFactors.go, cmatchPattern.go, cmatchSourceFactor]
      simp_rw [ih]

theorem start_rows_erase (space : List Atom) (input : InputSpec) (substitution : Subst) :
    (residualRows (entries space) (start space input substitution)).map eraseRow =
      cmatchInputSpec substitution space input := by
  simp only [residualRows, start, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    workRows, rows_erase, entries_atoms, List.map_nil]
  cases input with
  | compat pattern => exact btm_factors _ _ _ _
  | explicit sources => rfl

/-- Both directions of the independent support input relation follow from
the computed cursor, not from a correspondence premise. -/
theorem completed_input_iff (space : List Atom) (input : InputSpec)
    (substitution : Subst) (nodup : space.Nodup) (result : List Row)
    (fuel : Nat) (completed : collect (pull (entries space)) fuel
      (start space input substitution) = some result)
    (next : Subst) (witnesses : Finset Atom) :
    (next, witnesses) ∈ matchInputSpec substitution space.toFinset input ↔
      ∃ row ∈ result, row.1 = next ∧ (row.2.map Prod.fst).toFinset = witnesses := by
  have erased : result.map eraseRow = cmatchInputSpec substitution space input := by
    rw [collect_sound _ _ _ _ completed]
    exact start_rows_erase _ _ _
  constructor
  · intro matching
    obtain ⟨atoms, member, same⟩ :=
      Conformance.cmatchInputSpec_toFinset_complete substitution space nodup input
        next witnesses matching
    rw [← erased] at member
    obtain ⟨row, member, equal⟩ := List.mem_map.mp member
    exact ⟨row, member, congrArg Prod.fst equal, by
      simpa only [eraseRow, Prod.mk.injEq] using
        (congrArg List.toFinset (congrArg Prod.snd equal)).trans same⟩
  · rintro ⟨row, member, rfl, rfl⟩
    apply Conformance.cmatchInputSpec_toFinset_sound substitution space nodup input
    rw [← erased]
    exact List.mem_map.mpr ⟨row, member, rfl⟩

theorem completed_atom_iff (substitution : Subst) (pattern concrete : Atom)
    (next : Subst) :
    matchAtom substitution pattern concrete = some next ↔
      MatchAtomRel substitution pattern concrete next := matchAtom_iff

/-- Positions distinguish equal stored atoms without changing atom observations. -/
theorem entry_positions_unique (space : List Atom) :
    ((entries space).map Prod.snd).Nodup := by
  rw [entries, List.zipIdx_map_snd]
  exact List.nodup_range' _

theorem entry_at_position (space : List Atom) (item : Entry)
    (present : item ∈ entries space) : space[item.2]? = some item.1 :=
  List.mem_zipIdx_iff_getElem?.mp present

theorem candidates_subset (space : List Entry) (substitution : Subst)
    (source : SourceFactor) (item : Entry)
    (present : item ∈ (candidates space substitution source).2) : item ∈ space := by
  cases source with
  | btm pattern => exact present
  | eqConstraint pattern witness =>
      simp only [candidates, Option.mem_toList] at present
      exact List.mem_of_find?_eq_some present
  | neqConstraint pattern witness =>
      exact List.mem_of_mem_eraseP present

/-- Every retained witness is either an original prefix witness or an actual
entry from the captured input snapshot. -/
theorem rows_witnesses (space : List Entry) (sources : List SourceFactor)
    (substitution : Subst) (witnesses : List Entry) (row : Row)
    (generated : row ∈ rows space sources substitution witnesses)
    (item : Entry) (used : item ∈ row.2) : item ∈ space ∨ item ∈ witnesses := by
  induction sources generalizing substitution witnesses row with
  | nil =>
      simp only [rows, List.mem_singleton] at generated
      subst row
      exact Or.inr used
  | cons source rest ih =>
      simp only [rows, List.mem_flatMap] at generated
      obtain ⟨candidate, present, generated⟩ := generated
      cases matched : matchAtom substitution (candidates space substitution source).1
          candidate.1 with
      | none => simp [matched] at generated
      | some next =>
          simp only [matched] at generated
          rcases ih next (candidate :: witnesses) row generated used with fromSpace | retained
          · exact Or.inl fromSpace
          · simp only [List.mem_cons] at retained
            rcases retained with rfl | fromPrefix
            · exact Or.inl (candidates_subset _ _ _ _ present)
            · exact Or.inr fromPrefix

theorem completed_witness_positions (space : List Atom) (input : InputSpec)
    (substitution : Subst) (result : List Row) (fuel : Nat)
    (completed : collect (pull (entries space)) fuel
      (start space input substitution) = some result)
    (row : Row) (generated : row ∈ result) (item : Entry) (used : item ∈ row.2) :
    space[item.2]? = some item.1 := by
  rw [collect_sound _ _ _ _ completed] at generated
  simp only [residualRows, start, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, workRows] at generated
  have member := rows_witnesses _ _ _ _ _ generated item used
  exact entry_at_position space item (member.resolve_right (by simp))

theorem finite_completion (space : List Atom) (input : InputSpec) (substitution : Subst) :
    ∃ fuel result, collect (pull (entries space)) fuel (start space input substitution) =
      some result ∧ result.map eraseRow = cmatchInputSpec substitution space input := by
  refine ⟨remainingCost (entries space) (start space input substitution) + 1,
    residualRows (entries space) (start space input substitution), ?_, start_rows_erase ..⟩
  exact collect_complete _ _ _ (Nat.lt_succ_self _)

namespace Controls

def atom (name : String) : Atom := .symbol name
def edge (left right : Atom) : Atom := .expression [atom "edge", left, right]

def diamond : List Atom :=
  [edge (atom "A") (atom "B"), edge (atom "B") (atom "C"),
   edge (atom "A") (atom "D"), edge (atom "D") (atom "C")]

def joined : InputSpec := .compat ⟨[
  edge (atom "A") (.var "middle"), edge (.var "middle") (atom "C")]⟩

theorem join_keeps_both_paths :
    collect (pull (entries diamond)) 40 (start diamond joined) =
      some [
        ([("middle", atom "B")], [(edge (atom "B") (atom "C"), 1),
          (edge (atom "A") (atom "B"), 0)]),
        ([("middle", atom "D")], [(edge (atom "D") (atom "C"), 3),
          (edge (atom "A") (atom "D"), 2)])] := by decide

theorem first_poll_is_not_a_completed_join :
    collect (pull (entries diamond)) 1 (start diamond joined) = none := rfl

theorem duplicate_atoms_have_distinct_witnesses :
    collect (pull (entries [atom "a", atom "a"])) 12
      (start [atom "a", atom "a"] (.compat ⟨[.var "x"]⟩)) =
      some [([("x", atom "a")], [(atom "a", 0)]),
        ([("x", atom "a")], [(atom "a", 1)])] := by decide

theorem atom_erasure_does_not_preserve_occurrence_identity :
    eraseRow ([("x", atom "a")], [(atom "a", 0)]) =
      eraseRow ([("x", atom "a")], [(atom "a", 1)]) ∧
    ([("x", atom "a")], [(atom "a", 0)]) ≠
      ([("x", atom "a")], [(atom "a", 1)]) := by decide

theorem same_support_atom_can_witness_two_factors :
    collect (pull (entries [atom "a"])) 12
      (start [atom "a"] (.compat ⟨[.var "x", .var "x"]⟩)) =
      some [([("x", atom "a")], [(atom "a", 0), (atom "a", 0)])] := by decide

theorem explicit_sources_thread_bindings :
    collect (pull (entries [atom "a", atom "b"])) 30
      (start [atom "a", atom "b"] (.explicit [
        .eqConstraint (atom "a") (.var "x"),
        .neqConstraint (.var "x") (.var "y")])) =
      some [([("y", atom "b"), ("x", atom "a")], [(atom "b", 1), (atom "a", 0)])] := by
  decide

end Controls

#print axioms completed_input_iff
#print axioms finite_completion
#print axioms completed_witness_positions
#print axioms pause_resume_exact

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingCursor
