import Mettapedia.Languages.ProcessCalculi.MORK.Conformance
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.Languages.ProcessCalculi.MORK.MatchCursor
import Mettapedia.GSLT.LanguageDef.NativeControlCursor
import Mettapedia.Machines.Cursor.Scheduling

/-!
# Resumable MM2 input matching

The cursor retains a stack of factor joins and source-entry scans. It never
materializes the join before starting. The recursive reference cursor tries
one finite atom match per poll. The structural cursor retains that match's
unfinished syntax on the same owned stack, and is used by the batch and
private-worker interfaces.
Witnesses retain source positions, including equal atoms at different positions.

The local atom matcher traverses finite syntax and substitutions; a poll is
not a constant-time CPU claim. Recursive evaluation and foreign sources are
not operations of this input fragment. Whole-firing publication belongs to
the separate batch boundary. Privately prepared quanta reuse the shared cursor
scheduler and private-write kernel, preserving every owned packet and its pull
account. This finite atom matcher does not implement the C epoch worklist or
its node, arena, thread-state and invalidation boundaries.
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
    collect (pull space) fuel state = some (residualRows space state) :=
  NativeControlCursor.collect_complete (pull space) (residualRows space)
    (fun state => by cases moved : pull space state <;>
      simpa only [moved] using pull_rows space state)
    (remainingCost space)
    (fun state => by cases moved : pull space state <;>
      simpa only [moved] using pull_cost space state)
    fuel state enough

/-- Insufficient fuel never fabricates a partial collection as the full join. -/
theorem collect_sound (space : List Entry) (fuel : Nat) (state : State)
    (result : List Row) (completed : collect (pull space) fuel state = some result) :
    result = residualRows space state :=
  NativeControlCursor.collect_sound (pull space) (residualRows space)
    (fun state => by cases moved : pull space state <;>
      simpa only [moved] using pull_rows space state)
    fuel state result completed

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

/-! ## Structural matcher quanta inside the same join cursor -/

namespace StructuralQuanta

abbrev OuterWork := MM2MatchingCursor.Work

/-- Only the current atom meeting gets a local matching cursor. The parent
scan and all sibling joins remain on the original owned stack. -/
inductive Work where
  | outer (work : OuterWork)
  | matching (remaining : List SourceFactor) (item : Entry) (witnesses : List Entry)
      (cursor : MatchCursor.State)
  deriving Repr

abbrev State := List Work

def start (space : List Atom) (input : InputSpec) (substitution : Subst := []) : State :=
  (MM2MatchingCursor.start space input substitution).map Work.outer

def pull (space : List Entry) : State → Pull State Row
  | [] => .done
  | .outer (.join [] substitution witnesses) :: pending =>
      .yield (substitution, witnesses) pending
  | .outer (.join (source :: rest) substitution witnesses) :: pending =>
      let selected := candidates space substitution source
      .suspend (.outer (.scan selected.1 rest selected.2 substitution witnesses) :: pending)
  | .outer (.scan _ _ [] _ _) :: pending => .suspend pending
  | .outer (.scan pattern rest (item :: remaining) substitution witnesses) :: pending =>
      .suspend (.matching rest item witnesses (MatchCursor.start substitution pattern item.1) ::
        .outer (.scan pattern rest remaining substitution witnesses) :: pending)
  | .matching rest item witnesses cursor :: pending =>
      match MatchCursor.pull cursor with
      | .done => .suspend pending
      | .suspend next => .suspend (.matching rest item witnesses next :: pending)
      | .yield substitution _ =>
          .suspend (.outer (.join rest substitution (item :: witnesses)) :: pending)

abbrev provider (space : List Entry) := NativeControlCursor.provider (pull space)

def workRows (space : List Entry) : Work → List Row
  | .outer work => MM2MatchingCursor.workRows space work
  | .matching remaining item witnesses cursor =>
      (MatchCursor.residualAnswers cursor).flatMap
        (fun substitution => rows space remaining substitution (item :: witnesses))

def residualRows (space : List Entry) (state : State) : List Row :=
  state.flatMap (workRows space)

/-- Pending local syntax, bindings, parent scans and complete rows all belong
to the same answer-conservation law. No coefficient/body is activated early. -/
theorem pull_rows (space : List Entry) (state : State) :
    match pull space state with
    | .done => residualRows space state = []
    | .suspend next => residualRows space state = residualRows space next
    | .yield row next => residualRows space state = row :: residualRows space next := by
  cases state with
  | nil => rfl
  | cons work pending =>
      cases work with
      | outer work =>
          cases work with
          | join remaining substitution witnesses => cases remaining <;> rfl
          | scan pattern remaining pool substitution witnesses =>
              cases pool with
              | nil => rfl
              | cons item rest =>
                  cases matched : matchAtom substitution pattern item.1 <;>
                    simp [pull, residualRows, workRows, MM2MatchingCursor.workRows,
                      MatchCursor.start_answers, matched, List.append_assoc]
      | matching remaining item witnesses cursor =>
          have conserved := MatchCursor.pull_answers cursor
          cases moved : MatchCursor.pull cursor with
          | done =>
              simp only [moved] at conserved
              simp [pull, moved, residualRows, workRows, conserved]
          | suspend next =>
              simp only [moved] at conserved
              simp [pull, moved, residualRows, workRows, conserved]
          | yield substitution next =>
              have exhausted := MatchCursor.yield_residual cursor substitution next moved
              subst next
              simp only [moved] at conserved
              change MatchCursor.residualAnswers cursor = [substitution] at conserved
              simp [pull, moved, residualRows, workRows, conserved,
                MM2MatchingCursor.workRows]

/-- A proof bound counting join administration and local structural polls.
Atomic comparison primitives keep their independent complexity. -/
noncomputable def joinCost (space : List Entry) : List SourceFactor → Subst → Nat
  | [], _ => 1
  | source :: remaining, substitution =>
      let selected := candidates space substitution source
      2 + (selected.2.map fun item =>
        2 + MatchCursor.remainingCost (MatchCursor.start substitution selected.1 item.1) +
          match matchAtom substitution selected.1 item.1 with
          | none => 0
          | some next => joinCost space remaining next).sum

noncomputable def workCost (space : List Entry) : Work → Nat
  | .outer (.join remaining substitution _) => joinCost space remaining substitution
  | .outer (.scan pattern remaining pool substitution _) =>
      1 + (pool.map fun item =>
        2 + MatchCursor.remainingCost (MatchCursor.start substitution pattern item.1) +
          match matchAtom substitution pattern item.1 with
          | none => 0
          | some next => joinCost space remaining next).sum
  | .matching remaining _ _ cursor =>
      1 + MatchCursor.remainingCost cursor +
        ((MatchCursor.residualAnswers cursor).map (joinCost space remaining)).sum

noncomputable def remainingCost (space : List Entry) (state : State) : Nat :=
  (state.map (workCost space)).sum

theorem pull_cost (space : List Entry) (state : State) :
    match pull space state with
    | .done => remainingCost space state = 0
    | .suspend next => remainingCost space next < remainingCost space state
    | .yield _ next => remainingCost space next < remainingCost space state := by
  cases state with
  | nil => rfl
  | cons work pending =>
      cases work with
      | outer work =>
          cases work with
          | join remaining substitution witnesses =>
              cases remaining with
              | nil => simp [pull, remainingCost, workCost, joinCost]
              | cons source rest =>
                  simp only [pull, remainingCost, List.map_cons, List.sum_cons,
                    workCost, joinCost]
                  omega
          | scan pattern remaining pool substitution witnesses =>
              cases pool with
              | nil => simp [pull, remainingCost, workCost]
              | cons item rest =>
                  cases matched : matchAtom substitution pattern item.1 <;>
                    simp [pull, remainingCost, workCost, MatchCursor.start_answers,
                      matched, List.sum_cons] <;> omega
      | matching remaining item witnesses cursor =>
          have conserved := MatchCursor.pull_answers cursor
          have decrease := MatchCursor.pull_cost cursor
          cases moved : MatchCursor.pull cursor with
          | done =>
              simp only [moved] at conserved decrease
              simp [pull, moved, remainingCost, workCost, conserved, decrease]
          | suspend next =>
              simp only [moved] at conserved decrease
              simp only [pull, moved, remainingCost, List.map_cons, List.sum_cons, workCost]
              rw [conserved]
              omega
          | yield substitution next =>
              have exhausted := MatchCursor.yield_residual cursor substitution next moved
              subst next
              simp only [moved] at conserved
              change MatchCursor.residualAnswers cursor = [substitution] at conserved
              simp [pull, moved, remainingCost, workCost, conserved]

theorem collect_sound (space : List Entry) (fuel : Nat) (state : State)
    (result : List Row) (completed : collect (pull space) fuel state = some result) :
    result = residualRows space state :=
  NativeControlCursor.collect_sound (pull space) (residualRows space)
    (fun state => by cases moved : pull space state <;>
      simpa only [moved] using pull_rows space state)
    fuel state result completed

theorem collect_complete (space : List Entry) (fuel : Nat) (state : State)
    (enough : remainingCost space state < fuel) :
    collect (pull space) fuel state = some (residualRows space state) :=
  NativeControlCursor.collect_complete (pull space) (residualRows space)
    (fun state => by cases moved : pull space state <;>
      simpa only [moved] using pull_rows space state)
    (remainingCost space)
    (fun state => by cases moved : pull space state <;>
      simpa only [moved] using pull_cost space state)
    fuel state enough

/-- The local decomposition changes polling boundaries, while the independent
join denotation and the ordered physical witness list remain exact. -/
theorem start_rows (space : List Atom) (input : InputSpec) (substitution : Subst) :
    residualRows (entries space) (start space input substitution) =
      MM2MatchingCursor.residualRows (entries space)
        (MM2MatchingCursor.start space input substitution) := rfl

theorem start_rows_erase (space : List Atom) (input : InputSpec) (substitution : Subst) :
    (residualRows (entries space) (start space input substitution)).map eraseRow =
      cmatchInputSpec substitution space input := by
  rw [start_rows]
  exact MM2MatchingCursor.start_rows_erase ..

theorem completed_rows (space : List Atom) (input : InputSpec) (substitution : Subst)
    (fuel : Nat) (result : List Row)
    (completed : collect (pull (entries space)) fuel
      (start space input substitution) = some result) :
    result = MM2MatchingCursor.residualRows (entries space)
      (MM2MatchingCursor.start space input substitution) :=
  (collect_sound _ _ _ _ completed).trans (start_rows space input substitution)

theorem completed_rows_erase (space : List Atom) (input : InputSpec) (substitution : Subst)
    (fuel : Nat) (result : List Row)
    (completed : collect (pull (entries space)) fuel
      (start space input substitution) = some result) :
    result.map eraseRow = cmatchInputSpec substitution space input := by
  rw [completed_rows _ _ _ _ _ completed]
  exact MM2MatchingCursor.start_rows_erase ..

theorem pause_resume_exact (space : List Entry) (first later : Nat)
    (state : State) (reversed : List Row) :
    Mettapedia.Machines.Cursor.advance (NativeControlCursor.provider (pull space))
      (NativeControlCursor.client Row) (fun _ _ => 1) (first + later)
      (NativeControlCursor.packet (pull space) state reversed) =
    Mettapedia.Machines.Cursor.resume (NativeControlCursor.provider (pull space))
      (NativeControlCursor.client Row) (fun _ _ => 1) later
      (Mettapedia.Machines.Cursor.advance (NativeControlCursor.provider (pull space))
        (NativeControlCursor.client Row) (fun _ _ => 1) first
        (NativeControlCursor.packet (pull space) state reversed)) :=
  NativeControlCursor.chunk_exact _ _ _ _ _

namespace Controls

theorem local_matching_cannot_publish_the_join :
    collect (pull (entries MM2MatchingCursor.Controls.diamond)) 3
      (start MM2MatchingCursor.Controls.diamond MM2MatchingCursor.Controls.joined) = none := rfl

theorem duplicated_rows_keep_their_positions :
    collect (pull (entries [.symbol "a", .symbol "a"])) 32
      (start [.symbol "a", .symbol "a"] (.compat ⟨[.var "x"]⟩)) =
      some [([("x", .symbol "a")], [(.symbol "a", 0)]),
        ([("x", .symbol "a")], [(.symbol "a", 1)])] := by decide

theorem split_join_keeps_both_paths :
    collect (pull (entries MM2MatchingCursor.Controls.diamond)) 256
      (start MM2MatchingCursor.Controls.diamond MM2MatchingCursor.Controls.joined) =
      some [
        ([("middle", .symbol "B")],
          [(MM2MatchingCursor.Controls.edge (.symbol "B") (.symbol "C"), 1),
           (MM2MatchingCursor.Controls.edge (.symbol "A") (.symbol "B"), 0)]),
        ([("middle", .symbol "D")],
          [(MM2MatchingCursor.Controls.edge (.symbol "D") (.symbol "C"), 3),
           (MM2MatchingCursor.Controls.edge (.symbol "A") (.symbol "D"), 2)])] := by decide

end Controls

end StructuralQuanta

/-! ## Privately prepared matcher quanta -/

namespace PrivateQuanta
open Mettapedia.Machines.Cursor
open Scheduling

variable {Id : Type} [DecidableEq Id]

/-- Independent active queries read one captured physical input list. Selection
 * and later sink commits do not occur in this matching-only pool. -/
def initialPool (space : List Atom) (inputs : Id → InputSpec)
    (substitutions : Id → Subst) :
    Scheduling.Pool (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) Id () :=
  fun id => (0, .paused (NativeControlCursor.packet (StructuralQuanta.pull (entries space))
    (StructuralQuanta.start space (inputs id) (substitutions id)) []))

def prepare (space : List Atom) (schedule : List (Scheduling.Command Id))
    (pool : Scheduling.Pool (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) Id ()) :=
  Scheduling.prepareQuanta (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row)
    (fun _ _ => 1) schedule pool

def install (space : List Atom)
    (writes : List (Id × Scheduling.Cell (StructuralQuanta.provider (entries space))
      (NativeControlCursor.client Row) ()))
    (pool : Scheduling.Pool (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) Id ()) :=
  Scheduling.installQuanta (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) writes pool

/-- The real MM2 cursor retains its complete join stack, collected rows and
 * cumulative pull charge through private preparation and installation. -/
theorem full_state_agreement (space : List Atom) (schedule : List (Scheduling.Command Id))
    (pool : Scheduling.Pool (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) Id ())
    (distinct : (schedule.map Prod.fst).Nodup) (id : Id) :
    install space (prepare space schedule pool) pool id =
      resume (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) (fun _ _ => 1)
        (Scheduling.allocation id schedule) (pool id) :=
  Scheduling.prepared_quanta_at _ _ _ schedule pool distinct id

/-- The actual matcher participates in the tagged-packet pool through the
 * constant-family comparison, retaining its full residual and accumulated rows. -/
theorem packed_matching_agreement (space : List Atom)
    (schedule : List (Scheduling.Command Id))
    (pool : Scheduling.Pool (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) Id ())
    (distinct : (schedule.map Prod.fst).Nodup) (id : Id) :
    Scheduling.installPackedQuanta (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row)
      (Scheduling.preparePackedQuanta (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row)
        (fun _ _ => 1) schedule (fun id => ⟨(), pool id⟩))
      (fun id => ⟨(), pool id⟩) id =
      ⟨(), install space (prepare space schedule pool) pool id⟩ :=
  Scheduling.prepared_packed_constant_family _ _ _ schedule pool distinct id

/-- A sufficient allocated prefix publishes exactly the independently recursive
 * physical-row denotation. Preparation alone never asserts closure. -/
theorem completed_rows (space : List Atom) (inputs : Id → InputSpec)
    (substitutions : Id → Subst) (schedule : List (Scheduling.Command Id))
    (distinct : (schedule.map Prod.fst).Nodup) (id : Id) (fuel : Nat)
    (allocated : Scheduling.allocation id schedule = fuel + 1)
    (enough : StructuralQuanta.remainingCost (entries space)
      (StructuralQuanta.start space (inputs id) (substitutions id)) < fuel) :
    NativeControlCursor.published (StructuralQuanta.pull (entries space))
      (install space (prepare space schedule (initialPool space inputs substitutions))
        (initialPool space inputs substitutions) id).2 =
      some (StructuralQuanta.residualRows (entries space) (StructuralQuanta.start space (inputs id) (substitutions id))) := by
  rw [full_state_agreement space schedule _ distinct id, allocated]
  change NativeControlCursor.published _
    (advance (StructuralQuanta.provider (entries space)) (NativeControlCursor.client Row) (fun _ _ => 1)
      (fuel + 1) (NativeControlCursor.packet (StructuralQuanta.pull (entries space))
        (StructuralQuanta.start space (inputs id) (substitutions id)) [])).2 = _
  rw [NativeControlCursor.advance_collect, StructuralQuanta.collect_complete _ _ _ enough]
  simp

/-- Erasing positions agrees with the existing executable input semantics;
 * the full-state and row observations above retain those physical positions. -/
theorem completed_input (space : List Atom) (inputs : Id → InputSpec)
    (substitutions : Id → Subst) (schedule : List (Scheduling.Command Id))
    (distinct : (schedule.map Prod.fst).Nodup) (id : Id) (fuel : Nat)
    (allocated : Scheduling.allocation id schedule = fuel + 1)
    (enough : StructuralQuanta.remainingCost (entries space)
      (StructuralQuanta.start space (inputs id) (substitutions id)) < fuel) :
    (NativeControlCursor.published (StructuralQuanta.pull (entries space))
      (install space (prepare space schedule (initialPool space inputs substitutions))
        (initialPool space inputs substitutions) id).2).map (List.map eraseRow) =
      some (cmatchInputSpec (substitutions id) space (inputs id)) := by
  rw [completed_rows space inputs substitutions schedule distinct id fuel allocated enough]
  simp only [Option.map_some, StructuralQuanta.start_rows_erase]

namespace Controls
open MM2MatchingCursor.Controls (atom)

def duplicateSpace := [atom "a", atom "a"]
def duplicateInput : InputSpec := .compat ⟨[.var "x"]⟩
def duplicatePool := initialPool duplicateSpace (fun (_ : Bool) => duplicateInput)
  (fun _ => [])
def observed (pool : Scheduling.Pool (StructuralQuanta.provider (entries duplicateSpace))
    (NativeControlCursor.client Row) Bool ()) (id : Bool) : Nat × Option (List Row) :=
  ((pool id).1, NativeControlCursor.published (StructuralQuanta.pull (entries duplicateSpace)) (pool id).2)

theorem independent_equal_queries_keep_both_occurrences :
    let pool := install duplicateSpace (prepare duplicateSpace
      [(false, 16), (true, 16)] duplicatePool) duplicatePool
    observed pool false = (11, some [
      ([("x", atom "a")], [(atom "a", 0)]),
      ([("x", atom "a")], [(atom "a", 1)])]) ∧
    observed pool true = observed pool false := by
  constructor <;> cbv

theorem prepared_progress_is_not_closed :
    observed (install duplicateSpace
      (prepare duplicateSpace [(false, 1)] duplicatePool) duplicatePool) false =
      (1, none) := rfl

/-- Equal queries cannot use the same writable cursor cell in one private batch. -/
theorem shared_owner_overwrites_matching_progress :
    observed (install duplicateSpace
      (prepare duplicateSpace [(false, 9), (false, 9)] duplicatePool) duplicatePool) false =
      (9, none) ∧
    (observed (Scheduling.execute (StructuralQuanta.provider (entries duplicateSpace))
      (NativeControlCursor.client Row) (fun _ _ => 1)
      [(false, 9), (false, 9)] duplicatePool) false).2 ≠ none := by
  constructor
  · cbv
  · cbv
    simp

end Controls
end PrivateQuanta


#print axioms PrivateQuanta.full_state_agreement
#print axioms PrivateQuanta.packed_matching_agreement
#print axioms PrivateQuanta.completed_input
#print axioms completed_input_iff
#print axioms finite_completion
#print axioms completed_witness_positions
#print axioms pause_resume_exact

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingCursor
