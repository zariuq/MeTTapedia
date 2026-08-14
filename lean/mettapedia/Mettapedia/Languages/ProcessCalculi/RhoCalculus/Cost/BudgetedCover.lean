import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeProperties

/-!
# Budgeted exact purse-cover search

`exactPurseCovers` is the finite relational specification for exact funding.
This module gives that relation an explicit depth-first cursor.  A budget pays
for inspected search frames, so a caller can stop without constructing the
unvisited combinatorial suffix.  The cursor retains that suffix verbatim.

The public result distinguishes exhaustive failure from an interrupted
search.  This distinction is essential: an exhausted search budget is never
evidence that no exact cover exists.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- One suspended exact-cover subproblem.  Selected occurrences are stored in
reverse source order, allowing constant-time extension of the prefix. -/
structure CoverFrame where
  remainingPurses : List RawIndexedPurse
  remainingDemand : RawCostSig
  selectedRev : List RawIndexedPurse
  deriving Repr, DecidableEq

/-- A resumable depth-first search frontier.  The first frame is inspected
next. -/
structure CoverCursor where
  stack : List CoverFrame
  deriving Repr, DecidableEq

/-- Start an exact-cover search without inspecting any purse occurrence. -/
def CoverCursor.initial (demand : RawCostSig)
    (purses : List RawIndexedPurse) : CoverCursor :=
  ⟨[⟨purses, demand, []⟩]⟩

/-- One unit of search work either finishes the frontier, changes the cursor,
or emits exactly one occurrence-preserving cover. -/
inductive CoverAdvance where
  | done
  | continued (cursor : CoverCursor)
  | yielded (cover : List RawIndexedPurse) (cursor : CoverCursor)
  deriving Repr, DecidableEq

/-- Inspect one suspended frame.  Taking a purse is explored before skipping
it, matching the order of `exactPurseCovers`. -/
def CoverCursor.advance (cursor : CoverCursor) : CoverAdvance :=
  match cursor.stack with
  | [] => .done
  | frame :: deferred =>
      if frame.remainingDemand.isEmpty then
        .yielded frame.selectedRev.reverse ⟨deferred⟩
      else
        match frame.remainingPurses with
        | [] => .continued ⟨deferred⟩
        | purse :: rest =>
            let skipped : CoverFrame :=
              ⟨rest, frame.remainingDemand, frame.selectedRev⟩
            match RawCostSig.subtract frame.remainingDemand purse.head with
            | none => .continued ⟨skipped :: deferred⟩
            | some remaining =>
                let selected : CoverFrame :=
                  ⟨rest, remaining, purse :: frame.selectedRev⟩
                .continued ⟨selected :: skipped :: deferred⟩

/-- `complete` means the entire retained frontier was inspected.  `exhausted`
means only that the caller's search-work allowance ended. -/
inductive CoverSearchStatus where
  | complete
  | exhausted
  deriving Repr, DecidableEq

/-- A finite page of covers and the exact cursor from which enumeration may
resume. -/
structure CoverPage where
  covers : List (List RawIndexedPurse)
  cursor : CoverCursor
  status : CoverSearchStatus
  deriving Repr, DecidableEq

/-- Inspect at most `budget` frames.  An already-empty cursor is recognized as
complete without consuming work. -/
def CoverCursor.runBudget : Nat → CoverCursor → CoverPage
  | 0, cursor =>
      if cursor.stack.isEmpty then
        ⟨[], cursor, .complete⟩
      else
        ⟨[], cursor, .exhausted⟩
  | budget + 1, cursor =>
      match cursor.advance with
      | .done => ⟨[], cursor, .complete⟩
      | .continued next => next.runBudget budget
      | .yielded cover next =>
          let page := next.runBudget budget
          ⟨cover :: page.covers, page.cursor, page.status⟩

/-- A first-answer view with an honest negative/incomplete distinction. -/
inductive CoverDecision where
  | found (cover : List RawIndexedPurse) (cursor : CoverCursor)
  | noCover
  | searchExhausted (cursor : CoverCursor)
  deriving Repr, DecidableEq

/-- Search for one exact cover within a frame budget.  Unlike `runBudget`, this
operation stops at the first yield, so resuming its returned cursor cannot
skip an unreported cover. -/
def CoverCursor.seek : Nat → CoverCursor → CoverDecision
  | 0, cursor =>
      if cursor.stack.isEmpty then .noCover
      else .searchExhausted cursor
  | budget + 1, cursor =>
      match cursor.advance with
      | .done => .noCover
      | .continued next => next.seek budget
      | .yielded cover next => .found cover next

/-- A first-answer result that also returns unused search work, allowing one
budget to be shared across successive redex tasks. -/
structure MeteredCoverDecision where
  decision : CoverDecision
  remainingBudget : Nat
  deriving Repr, DecidableEq

/-- Metered first-answer search.  An empty cursor costs no work; every
inspected nonempty frame costs exactly one unit. -/
def CoverCursor.seekMetered : Nat → CoverCursor → MeteredCoverDecision
  | 0, cursor =>
      if cursor.stack.isEmpty then ⟨.noCover, 0⟩
      else ⟨.searchExhausted cursor, 0⟩
  | budget + 1, cursor =>
      match cursor.advance with
      | .done => ⟨.noCover, budget + 1⟩
      | .continued next => next.seekMetered budget
      | .yielded cover next => ⟨.found cover next, budget⟩

/-! ## Independent denotational specification of suspended work -/

/-- Covers denoted by one suspended subproblem. -/
def CoverFrame.denote (frame : CoverFrame) :
    List (List RawIndexedPurse) :=
  (exactPurseCovers frame.remainingDemand frame.remainingPurses).map
    (frame.selectedRev.reverse ++ ·)

/-- Covers not yet emitted by a cursor, in deterministic DFS order. -/
def CoverCursor.denote (cursor : CoverCursor) :
    List (List RawIndexedPurse) :=
  cursor.stack.flatMap CoverFrame.denote

/-! ## A structural bound on search work -/

/-- Number of frames inspected by an exhaustive traversal of one subproblem.
This counts the current frame and both children only when both are feasible. -/
def exactCoverWorkAux : List RawIndexedPurse → RawCostSig → Nat
  | [], _ => 1
  | purse :: rest, demand =>
      if demand.isEmpty then 1
      else
        match RawCostSig.subtract demand purse.head with
        | none => 1 + exactCoverWorkAux rest demand
        | some remaining =>
            1 + exactCoverWorkAux rest remaining +
              exactCoverWorkAux rest demand

/-- Work still retained in one frame. -/
def CoverFrame.work (frame : CoverFrame) : Nat :=
  exactCoverWorkAux frame.remainingPurses frame.remainingDemand

/-- Work still retained by an entire cursor. -/
def CoverCursor.work (cursor : CoverCursor) : Nat :=
  (cursor.stack.map CoverFrame.work).sum

theorem exactCoverWorkAux_pos (purses : List RawIndexedPurse)
    (demand : RawCostSig) : 0 < exactCoverWorkAux purses demand := by
  induction purses generalizing demand with
  | nil => simp [exactCoverWorkAux]
  | cons purse rest ih =>
      cases empty : demand.isEmpty <;>
        simp [exactCoverWorkAux, empty]
      cases subtraction : RawCostSig.subtract demand purse.head <;>
        simp

theorem CoverFrame.work_pos (frame : CoverFrame) : 0 < frame.work :=
  exactCoverWorkAux_pos frame.remainingPurses frame.remainingDemand

@[simp]
theorem CoverCursor.work_eq_zero_iff (cursor : CoverCursor) :
    cursor.work = 0 ↔ cursor.stack = [] := by
  rcases cursor with ⟨stack⟩
  cases stack with
  | nil => simp [CoverCursor.work]
  | cons frame deferred =>
      have positive := frame.work_pos
      simp [CoverCursor.work, Nat.ne_of_gt positive]

@[simp]
theorem CoverCursor.denote_initial (demand : RawCostSig)
    (purses : List RawIndexedPurse) :
    (CoverCursor.initial demand purses).denote =
      exactPurseCovers demand purses := by
  simp [CoverCursor.initial, CoverCursor.denote, CoverFrame.denote]

@[simp]
theorem exactPurseCovers_empty_demand (purses : List RawIndexedPurse) :
    exactPurseCovers [] purses = [[]] := by
  cases purses <;> simp [exactPurseCovers, exactPurseCoversAux]

/-- One unit of cursor execution neither invents nor loses a cover.  A yielded
cover is precisely the head removed from the denoted suffix. -/
theorem CoverCursor.advance_denote (cursor : CoverCursor) :
    match cursor.advance with
    | .done => cursor.denote = []
    | .continued next => next.denote = cursor.denote
    | .yielded cover next => cover :: next.denote = cursor.denote := by
  rcases cursor with ⟨stack⟩
  cases stack with
  | nil => simp [CoverCursor.advance, CoverCursor.denote]
  | cons frame deferred =>
      rcases frame with ⟨purses, demand, selectedRev⟩
      cases empty : demand.isEmpty with
      | true =>
          have demand_nil : demand = [] := List.isEmpty_iff.mp empty
          subst demand
          simp [CoverCursor.advance, CoverCursor.denote, CoverFrame.denote,
            exactPurseCovers]
      | false =>
          cases purses with
          | nil =>
              simp [CoverCursor.advance, CoverCursor.denote,
                CoverFrame.denote, exactPurseCovers, empty]
          | cons purse rest =>
              cases subtraction : RawCostSig.subtract demand purse.head with
              | none =>
                  simp [CoverCursor.advance, CoverCursor.denote,
                    CoverFrame.denote, exactPurseCovers,
                    exactPurseCoversAux, empty, subtraction]
              | some remaining =>
                  simp [CoverCursor.advance, CoverCursor.denote,
                    CoverFrame.denote, exactPurseCovers,
                    exactPurseCoversAux, empty, subtraction,
                    List.map_append, Function.comp_def]

/-- Inspecting one nonempty frame consumes exactly one unit of structural
work. -/
theorem CoverCursor.advance_work (cursor : CoverCursor) :
    match cursor.advance with
    | .done => cursor.work = 0
    | .continued next => next.work + 1 = cursor.work
    | .yielded _ next => next.work + 1 = cursor.work := by
  rcases cursor with ⟨stack⟩
  cases stack with
  | nil => simp [CoverCursor.advance, CoverCursor.work]
  | cons frame deferred =>
      rcases frame with ⟨purses, demand, selectedRev⟩
      cases empty : demand.isEmpty with
      | true =>
          cases purses <;>
            simp [CoverCursor.advance, CoverCursor.work, CoverFrame.work,
              exactCoverWorkAux, empty] <;> omega
      | false =>
          cases purses with
          | nil =>
              simp [CoverCursor.advance, CoverCursor.work, CoverFrame.work,
                exactCoverWorkAux, empty]
              omega
          | cons purse rest =>
              cases subtraction : RawCostSig.subtract demand purse.head with
              | none =>
                  simp [CoverCursor.advance, CoverCursor.work,
                    CoverFrame.work, exactCoverWorkAux, empty, subtraction,
                    Nat.add_assoc]
                  omega
              | some remaining =>
                  simp [CoverCursor.advance, CoverCursor.work,
                    CoverFrame.work, exactCoverWorkAux, empty, subtraction,
                    Nat.add_assoc]
                  omega

/-- Every budgeted page is an exact prefix/residual decomposition of the
cursor's denotation. -/
theorem CoverCursor.runBudget_partition (budget : Nat)
    (cursor : CoverCursor) :
    (cursor.runBudget budget).covers ++
        (cursor.runBudget budget).cursor.denote = cursor.denote := by
  induction budget generalizing cursor with
  | zero =>
      rcases cursor with ⟨stack⟩
      cases stack <;>
        simp [CoverCursor.runBudget, CoverCursor.denote]
  | succ budget ih =>
      have step := cursor.advance_denote
      cases advance_eq : cursor.advance with
      | done =>
          simp only [advance_eq] at step
          simp [CoverCursor.runBudget, advance_eq, step]
      | continued next =>
          simp only [advance_eq] at step
          simpa [CoverCursor.runBudget, advance_eq, step] using ih next
      | yielded cover next =>
          simp only [advance_eq] at step
          simpa [CoverCursor.runBudget, advance_eq, step, List.cons_append]
            using congrArg (cover :: ·) (ih next)

/-- Running a second page from the returned cursor preserves the same exact
prefix/residual partition. -/
theorem CoverCursor.runBudget_resume_partition (firstBudget secondBudget : Nat)
    (cursor : CoverCursor) :
    let first := cursor.runBudget firstBudget
    let second := first.cursor.runBudget secondBudget
    first.covers ++ second.covers ++ second.cursor.denote = cursor.denote := by
  dsimp only
  rw [List.append_assoc]
  rw [CoverCursor.runBudget_partition secondBudget
    (cursor.runBudget firstBudget).cursor]
  exact CoverCursor.runBudget_partition firstBudget cursor

/-- Covers emitted across two resumed pages form one exact prefix. -/
theorem CoverCursor.runBudget_resume_prefix (firstBudget secondBudget : Nat)
    (cursor : CoverCursor) :
    let first := cursor.runBudget firstBudget
    let second := first.cursor.runBudget secondBudget
    first.covers ++ second.covers <+: cursor.denote := by
  dsimp only
  exact ⟨((cursor.runBudget firstBudget).cursor.runBudget
      secondBudget).cursor.denote,
    CoverCursor.runBudget_resume_partition firstBudget secondBudget cursor⟩

/-- The emitted page is literally a prefix of the exact DFS denotation. -/
theorem CoverCursor.runBudget_covers_prefix (budget : Nat)
    (cursor : CoverCursor) :
    (cursor.runBudget budget).covers <+: cursor.denote := by
  exact ⟨(cursor.runBudget budget).cursor.denote,
    cursor.runBudget_partition budget⟩

/-- Completing a page leaves no denoted cover hidden in its cursor. -/
theorem CoverCursor.runBudget_complete_denote_empty (budget : Nat)
    (cursor : CoverCursor)
    (complete : (cursor.runBudget budget).status =
      CoverSearchStatus.complete) :
    (cursor.runBudget budget).cursor.denote = [] := by
  induction budget generalizing cursor with
  | zero =>
      rcases cursor with ⟨stack⟩
      cases stack with
      | nil => simp [CoverCursor.runBudget, CoverCursor.denote]
      | cons frame deferred =>
          simp [CoverCursor.runBudget] at complete
  | succ budget ih =>
      have step := cursor.advance_denote
      cases advance_eq : cursor.advance with
      | done =>
          simp only [advance_eq] at step
          simpa [CoverCursor.runBudget, advance_eq] using step
      | continued next =>
          simp only [advance_eq] at step
          have nextComplete : (next.runBudget budget).status =
              CoverSearchStatus.complete := by
            simpa [CoverCursor.runBudget, advance_eq] using complete
          simpa [CoverCursor.runBudget, advance_eq] using
            ih next nextComplete
      | yielded cover next =>
          simp only [advance_eq] at step
          have nextComplete : (next.runBudget budget).status =
              CoverSearchStatus.complete := by
            simpa [CoverCursor.runBudget, advance_eq] using complete
          simpa [CoverCursor.runBudget, advance_eq] using
            ih next nextComplete

/-- A completed page equals the full exact-cover relation in enumeration
order. -/
theorem CoverCursor.runBudget_eq_denote_of_complete (budget : Nat)
    (cursor : CoverCursor)
    (complete : (cursor.runBudget budget).status =
      CoverSearchStatus.complete) :
    (cursor.runBudget budget).covers = cursor.denote := by
  have partition := cursor.runBudget_partition budget
  have residual := cursor.runBudget_complete_denote_empty budget complete
  rw [residual, List.append_nil] at partition
  exact partition

/-- Any budget at least the structural work bound exhausts the cursor. -/
theorem CoverCursor.runBudget_complete_of_work_le (budget : Nat)
    (cursor : CoverCursor) (enough : cursor.work ≤ budget) :
    (cursor.runBudget budget).status = CoverSearchStatus.complete := by
  induction budget generalizing cursor with
  | zero =>
      have workZero : cursor.work = 0 := Nat.eq_zero_of_le_zero enough
      have stackEmpty : cursor.stack = [] :=
        (CoverCursor.work_eq_zero_iff cursor).mp workZero
      rcases cursor with ⟨stack⟩
      simp_all [CoverCursor.runBudget]
  | succ budget ih =>
      have step := cursor.advance_work
      cases advance_eq : cursor.advance with
      | done => simp [CoverCursor.runBudget, advance_eq]
      | continued next =>
          simp only [advance_eq] at step
          have nextEnough : next.work ≤ budget := by omega
          simpa [CoverCursor.runBudget, advance_eq] using ih next nextEnough
      | yielded cover next =>
          simp only [advance_eq] at step
          have nextEnough : next.work ≤ budget := by omega
          simpa [CoverCursor.runBudget, advance_eq] using ih next nextEnough

/-- The structural bound is sufficient for an exhaustive traversal. -/
theorem CoverCursor.runBudget_work_complete (cursor : CoverCursor) :
    (cursor.runBudget cursor.work).status = CoverSearchStatus.complete :=
  CoverCursor.runBudget_complete_of_work_le cursor.work cursor (by rfl)

/-- Exhaustive lazy traversal is extensionally equal, including order, to the
independent eager specification. -/
theorem CoverCursor.runBudget_work_eq_denote (cursor : CoverCursor) :
    (cursor.runBudget cursor.work).covers = cursor.denote :=
  CoverCursor.runBudget_eq_denote_of_complete cursor.work cursor
    cursor.runBudget_work_complete

/-- On an initial cursor, exhaustive lazy traversal computes exactly the
existing occurrence-preserving relation. -/
theorem CoverCursor.runBudget_initial_work_eq_exact
    (demand : RawCostSig) (purses : List RawIndexedPurse) :
    let cursor := CoverCursor.initial demand purses
    (cursor.runBudget cursor.work).covers = exactPurseCovers demand purses := by
  simp only
  rw [CoverCursor.runBudget_work_eq_denote, CoverCursor.denote_initial]

/-- Every exact cover is eventually emitted by the budgeted cursor. -/
theorem CoverCursor.runBudget_initial_complete
    {demand : RawCostSig} {purses cover : List RawIndexedPurse}
    (member : cover ∈ exactPurseCovers demand purses) :
    let cursor := CoverCursor.initial demand purses
    cover ∈ (cursor.runBudget cursor.work).covers := by
  simpa only [CoverCursor.runBudget_initial_work_eq_exact] using member

/-- Every emitted result from an initial cursor belongs to the independent
exact-cover specification. -/
theorem CoverCursor.runBudget_initial_sound
    {budget : Nat} {demand : RawCostSig}
    {purses cover : List RawIndexedPurse}
    (member : cover ∈
      ((CoverCursor.initial demand purses).runBudget budget).covers) :
    List.Mem cover (exactPurseCovers demand purses) := by
  have emittedPrefix : List.IsPrefix
      ((CoverCursor.initial demand purses).runBudget budget).covers
      (exactPurseCovers demand purses) := by
    simpa only [CoverCursor.denote_initial] using
      CoverCursor.runBudget_covers_prefix budget
        (CoverCursor.initial demand purses)
  exact emittedPrefix.mem member

/-- Every budgeted result has exact spend. -/
theorem CoverCursor.runBudget_initial_spend_sound
    {budget : Nat} {demand : RawCostSig}
    {purses cover : List RawIndexedPurse}
    (member : cover ∈
      ((CoverCursor.initial demand purses).runBudget budget).covers) :
    rawSelectedSpend cover = demand.toMultiset :=
  exactPurseCovers_spend_sound (CoverCursor.runBudget_initial_sound member)

/-- Every budgeted result preserves concrete source occurrences and order. -/
theorem CoverCursor.runBudget_initial_sublist
    {budget : Nat} {demand : RawCostSig}
    {purses cover : List RawIndexedPurse}
    (member : cover ∈
      ((CoverCursor.initial demand purses).runBudget budget).covers) :
    cover.Sublist purses :=
  exactPurseCovers_sublist (CoverCursor.runBudget_initial_sound member)

/-! ## Occurrence uniqueness -/

/-- With unique concrete purse records, the exact enumerator produces no
duplicate concrete occurrence-cover. -/
theorem exactPurseCovers_nodup
    {demand : RawCostSig} {purses : List RawIndexedPurse}
    (sourceNodup : purses.Nodup) :
    (exactPurseCovers demand purses).Nodup := by
  induction purses generalizing demand with
  | nil =>
      cases empty : demand.isEmpty <;>
        simp [exactPurseCovers, exactPurseCoversAux, empty]
  | cons purse rest ih =>
      have source := List.nodup_cons.mp sourceNodup
      cases empty : demand.isEmpty with
      | true =>
          simp [exactPurseCovers, exactPurseCoversAux, empty]
      | false =>
          cases subtraction : RawCostSig.subtract demand purse.head with
          | none =>
              simpa [exactPurseCovers, exactPurseCoversAux, empty,
                subtraction] using ih source.2
          | some remaining =>
              have selectedNodup :
                  ((exactPurseCovers remaining rest).map
                    (purse :: ·)).Nodup := by
                apply List.Pairwise.map (R := fun left right => left ≠ right)
                  (S := fun left right => left ≠ right) (purse :: ·)
                · intro left right different equal
                  exact different (List.cons.inj equal).2
                · exact ih source.2
              have skippedNodup :
                  (exactPurseCovers demand rest).Nodup := ih source.2
              have alternativesNodup :
                  ((exactPurseCovers remaining rest).map (purse :: ·) ++
                    exactPurseCovers demand rest).Nodup := by
                apply List.nodup_append.mpr
                refine ⟨selectedNodup, skippedNodup, ?_⟩
                intro selected selectedMember skipped skippedMember equal
                obtain ⟨tail, tailMember, rfl⟩ :=
                  List.mem_map.mp selectedMember
                subst skipped
                have selectedSublist :
                    (purse :: tail).Sublist rest :=
                  exactPurseCovers_sublist skippedMember
                exact source.1 (selectedSublist.mem (by simp))
              simpa [exactPurseCovers, exactPurseCoversAux, empty,
                subtraction] using alternativesNodup

/-- Every finite page is duplicate-free when source occurrence records are
unique. -/
theorem CoverCursor.runBudget_initial_nodup
    {budget : Nat} {demand : RawCostSig}
    {purses : List RawIndexedPurse} (sourceNodup : purses.Nodup) :
    ((CoverCursor.initial demand purses).runBudget budget).covers.Nodup := by
  have emittedPrefix := CoverCursor.runBudget_covers_prefix budget
    (CoverCursor.initial demand purses)
  rw [CoverCursor.denote_initial] at emittedPrefix
  exact emittedPrefix.sublist.nodup (exactPurseCovers_nodup sourceNodup)

/-- Unique occurrence indices imply unique purse records. -/
theorem rawIndexedPurses_nodup_of_indices_nodup
    {purses : List RawIndexedPurse}
    (indicesNodup : (purses.map RawIndexedPurse.index).Nodup) :
    purses.Nodup := by
  induction purses with
  | nil => simp
  | cons purse rest ih =>
      simp only [List.map_cons, List.nodup_cons] at indicesNodup ⊢
      refine ⟨?_, ih indicesNodup.2⟩
      intro purseMember
      apply indicesNodup.1
      exact List.mem_map.mpr ⟨purse, purseMember, rfl⟩

/-- Runtime-style occurrence-index uniqueness is enough to rule out duplicate
emitted covers. -/
theorem CoverCursor.runBudget_initial_nodup_of_indices
    {budget : Nat} {demand : RawCostSig}
    {purses : List RawIndexedPurse}
    (indicesNodup : (purses.map RawIndexedPurse.index).Nodup) :
    ((CoverCursor.initial demand purses).runBudget budget).covers.Nodup :=
  CoverCursor.runBudget_initial_nodup
    (rawIndexedPurses_nodup_of_indices_nodup indicesNodup)

/-- Duplicate-freedom also holds across a pause/resume boundary. -/
theorem CoverCursor.runBudget_initial_resume_nodup_of_indices
    {firstBudget secondBudget : Nat} {demand : RawCostSig}
    {purses : List RawIndexedPurse}
    (indicesNodup : (purses.map RawIndexedPurse.index).Nodup) :
    let cursor := CoverCursor.initial demand purses
    let first := cursor.runBudget firstBudget
    let second := first.cursor.runBudget secondBudget
    (first.covers ++ second.covers).Nodup := by
  dsimp only
  have emittedPrefix := CoverCursor.runBudget_resume_prefix
    firstBudget secondBudget (CoverCursor.initial demand purses)
  rw [CoverCursor.denote_initial] at emittedPrefix
  exact emittedPrefix.sublist.nodup
    (exactPurseCovers_nodup
      (rawIndexedPurses_nodup_of_indices_nodup indicesNodup))

/-! ## Honest first-answer verdicts -/

/-- A zero search budget inspects no frame and reports incompleteness whenever
work remains. -/
theorem CoverCursor.seek_zero_of_nonempty (cursor : CoverCursor)
    (nonempty : cursor.stack ≠ []) :
    cursor.seek 0 = CoverDecision.searchExhausted cursor := by
  rcases cursor with ⟨stack⟩
  cases stack with
  | nil => contradiction
  | cons frame deferred =>
      simp [CoverCursor.seek]

@[simp]
theorem CoverCursor.seek_zero_initial (demand : RawCostSig)
    (purses : List RawIndexedPurse) :
    (CoverCursor.initial demand purses).seek 0 =
      CoverDecision.searchExhausted (CoverCursor.initial demand purses) :=
  CoverCursor.seek_zero_of_nonempty _ (by simp [CoverCursor.initial])

/-- Metering changes only the returned unused allowance, not the search
verdict. -/
theorem CoverCursor.seekMetered_decision (budget : Nat)
    (cursor : CoverCursor) :
    (cursor.seekMetered budget).decision = cursor.seek budget := by
  induction budget generalizing cursor with
  | zero =>
      rcases cursor with ⟨stack⟩
      cases stack <;>
        simp [CoverCursor.seekMetered, CoverCursor.seek]
  | succ budget ih =>
      cases advance_eq : cursor.advance with
      | done => simp [CoverCursor.seekMetered, CoverCursor.seek, advance_eq]
      | continued next =>
          simpa [CoverCursor.seekMetered, CoverCursor.seek, advance_eq] using
            ih next
      | yielded cover next =>
          simp [CoverCursor.seekMetered, CoverCursor.seek, advance_eq]

/-- Metered search never creates work allowance. -/
theorem CoverCursor.seekMetered_remaining_le (budget : Nat)
    (cursor : CoverCursor) :
    (cursor.seekMetered budget).remainingBudget ≤ budget := by
  induction budget generalizing cursor with
  | zero =>
      by_cases empty : cursor.stack = [] <;>
        simp [CoverCursor.seekMetered, empty]
  | succ budget ih =>
      cases advance_eq : cursor.advance with
      | done => simp [CoverCursor.seekMetered, advance_eq]
      | continued next =>
          have remaining := Nat.le_trans (ih next) (Nat.le_succ budget)
          simpa [CoverCursor.seekMetered, advance_eq] using remaining
      | yielded cover next =>
          simp [CoverCursor.seekMetered, advance_eq]

/-- A successful one-answer search removes exactly its reported cover from the
denoted suffix; resumption therefore loses no unreported witness. -/
theorem CoverCursor.seek_found_partition
    {budget : Nat} {cursor next : CoverCursor}
    {cover : List RawIndexedPurse}
    (found : cursor.seek budget = CoverDecision.found cover next) :
    cover :: next.denote = cursor.denote := by
  induction budget generalizing cursor with
  | zero =>
      rcases cursor with ⟨stack⟩
      cases stack <;> simp [CoverCursor.seek] at found
  | succ budget ih =>
      have step := cursor.advance_denote
      cases advance_eq : cursor.advance with
      | done => simp [CoverCursor.seek, advance_eq] at found
      | continued residual =>
          simp only [advance_eq] at step
          have foundResidual : residual.seek budget =
              CoverDecision.found cover next := by
            simpa [CoverCursor.seek, advance_eq] using found
          rw [← step]
          exact ih foundResidual
      | yielded head residual =>
          simp only [advance_eq] at step
          have foundEq : CoverDecision.found head residual =
              CoverDecision.found cover next := by
            simpa [CoverCursor.seek, advance_eq] using found
          cases foundEq
          exact step

/-- A returned first cover belongs to the exact denotation. -/
theorem CoverCursor.seek_found_sound
    {budget : Nat} {cursor next : CoverCursor}
    {cover : List RawIndexedPurse}
    (found : cursor.seek budget = CoverDecision.found cover next) :
    cover ∈ cursor.denote := by
  rw [← CoverCursor.seek_found_partition found]
  simp

/-- `noCover` is issued only after exhaustive search and therefore proves the
exact relation empty. -/
theorem CoverCursor.seek_noCover_denote_empty
    {budget : Nat} {cursor : CoverCursor}
    (absent : cursor.seek budget = CoverDecision.noCover) :
    cursor.denote = [] := by
  induction budget generalizing cursor with
  | zero =>
      rcases cursor with ⟨stack⟩
      cases stack with
      | nil => simp [CoverCursor.denote]
      | cons frame deferred =>
          simp [CoverCursor.seek] at absent
  | succ budget ih =>
      have step := cursor.advance_denote
      cases advance_eq : cursor.advance with
      | done =>
          simp only [advance_eq] at step
          exact step
      | continued residual =>
          simp only [advance_eq] at step
          have absentResidual : residual.seek budget =
              CoverDecision.noCover := by
            simpa [CoverCursor.seek, advance_eq] using absent
          rw [← step]
          exact ih absentResidual
      | yielded head residual =>
          simp [CoverCursor.seek, advance_eq] at absent

/-- A metered negative verdict has the same exhaustive meaning as its
unmetered projection. -/
theorem CoverCursor.seekMetered_noCover_denote_empty
    {budget remaining : Nat} {cursor : CoverCursor}
    (absent : cursor.seekMetered budget =
      ⟨CoverDecision.noCover, remaining⟩) :
    cursor.denote = [] := by
  have decision := CoverCursor.seekMetered_decision budget cursor
  rw [absent] at decision
  exact CoverCursor.seek_noCover_denote_empty decision.symm

/-- A found result from an initial cursor is an exact purse cover. -/
theorem CoverCursor.seek_initial_found_sound
    {budget : Nat} {demand : RawCostSig}
    {purses cover : List RawIndexedPurse} {next : CoverCursor}
    (found : (CoverCursor.initial demand purses).seek budget =
      CoverDecision.found cover next) :
    cover ∈ exactPurseCovers demand purses := by
  have denoted := CoverCursor.seek_found_sound found
  simpa only [CoverCursor.denote_initial] using denoted

/-- An exhaustive negative verdict from an initial cursor is a proof that no
exact funding cover exists. -/
theorem CoverCursor.seek_initial_noCover
    {budget : Nat} {demand : RawCostSig}
    {purses : List RawIndexedPurse}
    (absent : (CoverCursor.initial demand purses).seek budget =
      CoverDecision.noCover) :
    exactPurseCovers demand purses = [] := by
  have empty := CoverCursor.seek_noCover_denote_empty absent
  simpa only [CoverCursor.denote_initial] using empty

/-! ## Positive and negative executable examples -/

private def exampleLocation : RawCostName := .signature ["site"]

private def examplePurse0 : RawIndexedPurse :=
  ⟨0, exampleLocation, ["a"], []⟩

private def examplePurse1 : RawIndexedPurse :=
  ⟨1, exampleLocation, ["a"], []⟩

/-- Equal-valued heads at distinct occurrence indices yield two covers, not
one deduplicated cover. -/
example :
    let cursor := CoverCursor.initial ["a"] [examplePurse0, examplePurse1]
    (cursor.runBudget cursor.work).covers =
      [[examplePurse0], [examplePurse1]] := by
  decide

/-- An exact two-token demand selects both concrete occurrences once. -/
example :
    let cursor := CoverCursor.initial ["a", "a"]
      [examplePurse0, examplePurse1]
    (cursor.runBudget cursor.work).covers =
      [[examplePurse0, examplePurse1]] := by
  decide

/-- Zero search budget is incomplete, never a false negative. -/
example :
    let cursor := CoverCursor.initial ["a"] [examplePurse0]
    cursor.seek 0 = CoverDecision.searchExhausted cursor := by
  decide

/-- Exhaustive search can honestly certify absence. -/
example :
    let cursor := CoverCursor.initial ["missing"] [examplePurse0]
    cursor.seek cursor.work = CoverDecision.noCover := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
