import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SubtypeClosureCoordinates

/-!
# Fresh-name transport through occurrence-scoped closure rounds

Every query may extend the coordinate map. Previously accepted discoveries,
the fixed pre-round prefix and unvisited frontier entries remain protected
while later queries allocate. Parent indices and duplicate occurrences are
retained by the actual closure algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeClosureCoordinates

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open TypeDependencyAdmission SubtypeClosureRounds SubtypeClosureCoordinates
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

def renameFrontier (names : Equiv.Perm String) (frontier : List (Entry × Nat)) : List (Entry × Nat) :=
  frontier.map fun pair => (renameEntry names pair.1, pair.2)

theorem frontier_rename_agrees (first second : Equiv.Perm String) (live : List String)
    (agrees : ∀ name ∈ live, first name = second name) (frontier : List (Entry × Nat))
    (covered : ∀ pair ∈ frontier, atomVariables pair.1.type_ ⊆ live) :
    renameFrontier first frontier = renameFrontier second frontier := by
  apply List.map_congr_left
  intro pair present
  rw [entry_rename_agrees first second live agrees pair.1 (covered pair present)]

theorem discoveries_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (frontier : List (Entry × Nat)) :
    ∀ (previous : Equiv.Perm String) (live : List String) (before : State),
      entryNames before.known ⊆ live →
      (∀ pair ∈ frontier, atomVariables pair.1.type_ ⊆ live) →
      (∀ pair ∈ frontier, resourceFree pair.1.type_ = true) →
      ∀ (first second : Supply), live ⊆ first.used → live.map previous ⊆ second.used →
      EntriesRelated previous live
        (ScopedSubtypeReads.discoveries world sourceRows base alpha before frontier first)
        (ScopedSubtypeReads.discoveries world sourceRows base alpha (renameState previous before)
          (renameFrontier previous frontier) second) := by
  induction frontier with
  | nil =>
      intro previous live before _ _ _ first second firstProtected secondProtected
      exact empty_related previous live first second firstProtected secondProtected
  | cons pair rest ih =>
      intro previous live before beforeCovered frontierCovered frontierSafe first second firstProtected secondProtected
      rcases pair with ⟨entry, index⟩
      have entrySafe := frontierSafe (entry, index) (by simp)
      have restCovered : ∀ pair ∈ rest, atomVariables pair.1.type_ ⊆ live :=
        fun pair member => frontierCovered pair (List.mem_cons_of_mem _ member)
      have restSafe : ∀ pair ∈ rest, resourceFree pair.1.type_ = true :=
        fun pair member => frontierSafe pair (List.mem_cons_of_mem _ member)
      by_cases error : entry.error = true
      · simpa only [ScopedSubtypeReads.discoveries, renameFrontier, List.map_cons,
          renameEntry, error, if_true] using
          ih previous live before beforeCovered restCovered restSafe first second firstProtected secondProtected
      · let firstQuery := ScopedSubtypeReads.query world sourceRows base entry.type_ first
        let secondQuery := ScopedSubtypeReads.query world sourceRows base (renameAtom previous entry.type_) second
        let firstAdded := attachParent index (firstQuery.1.filter (accept alpha before index))
        let secondAdded := attachParent index (secondQuery.1.filter (accept alpha (renameState previous before) index))
        have queried : TypeReadWorlds.ResultRelated previous live firstQuery secondQuery :=
          (ScopedSubtypeReadWorlds.query_coordinates world sourceRows safe previous live base entry.type_
            entrySafe first second firstProtected secondProtected).restrict
              (fun _ member => List.mem_append_left _ member)
        obtain ⟨middle, agrees, carried, firstKeeps, secondKeeps⟩ :=
          accepted_related alpha equivariant previous live before beforeCovered index firstQuery secondQuery queried
        have enlargedBefore : entryNames before.known ⊆ live ++ entryNames firstAdded :=
          fun _ member => List.mem_append_left _ (beforeCovered member)
        have enlargedRest : ∀ pair ∈ rest, atomVariables pair.1.type_ ⊆ live ++ entryNames firstAdded :=
          fun pair member _ occurs => List.mem_append_left _ (restCovered pair member occurs)
        have later := ih middle (live ++ entryNames firstAdded) before enlargedBefore enlargedRest restSafe
          firstQuery.2 secondQuery.2 firstKeeps secondKeeps
        have beforeSame := state_rename_agrees middle previous live agrees before beforeCovered
        have restSame := frontier_rename_agrees middle previous live agrees rest restCovered
        rw [beforeSame, restSame] at later
        have combined := append_related previous middle live firstAdded secondAdded _ _ agrees carried later
        simpa only [ScopedSubtypeReads.discoveries, renameFrontier, List.map_cons, renameEntry,
          error, Bool.false_eq_true, if_false, firstAdded, secondAdded, firstQuery, secondQuery, attachParent] using combined

theorem zipIdx_rename (names : Equiv.Perm String) (entries : List Entry) : ∀ offset,
    (entries.map (renameEntry names)).zipIdx offset = renameFrontier names (entries.zipIdx offset) := by
  induction entries with
  | nil => intro offset; rfl
  | cons entry entries ih =>
      intro offset
      simp [List.zipIdx_cons, ih, renameFrontier]

theorem frontier_rename (names : Equiv.Perm String) (before : State) :
    (renameState names before).known.zipIdx.drop (renameState names before).frontier =
      renameFrontier names (before.known.zipIdx.drop before.frontier) := by
  change ((before.known.map (renameEntry names)).zipIdx).drop before.frontier = _
  rw [zipIdx_rename]
  exact (List.map_drop ..).symm

theorem frontier_covered (before : State) (live : List String)
    (covered : entryNames before.known ⊆ live) :
    ∀ pair ∈ before.known.zipIdx.drop before.frontier, atomVariables pair.1.type_ ⊆ live := by
  intro pair present name occurs
  exact covered (variables_member (List.fst_mem_of_mem_zipIdx (List.mem_of_mem_drop present)) occurs)

/-- The round's unfiltered query allocations are included in the returned
supply even when no accepted discovery remains. -/
theorem round_discoveries_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (previous : Equiv.Perm String) (live : List String) (before : State)
    (beforeSafe : SubtypeClosureRounds.Safe before) (covered : entryNames before.known ⊆ live)
    (first second : Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) :
    EntriesRelated previous live
      (ScopedSubtypeReads.discoveries world sourceRows base alpha before
        (before.known.zipIdx.drop before.frontier) first)
      (ScopedSubtypeReads.discoveries world sourceRows base alpha (renameState previous before)
        ((renameState previous before).known.zipIdx.drop (renameState previous before).frontier) second) := by
  rw [frontier_rename]
  exact discoveries_coordinates world sourceRows safe base alpha equivariant _ previous live before covered
    (frontier_covered before live covered) (ScopedSubtypeReadSafety.frontier_safe before beforeSafe)
    first second firstProtected secondProtected

theorem run_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha) (budget : Nat) :
    ∀ (previous : Equiv.Perm String) (live : List String) (before : State),
      SubtypeClosureRounds.Safe before → entryNames before.known ⊆ live →
      ∀ (first second : Supply), live ⊆ first.used → live.map previous ⊆ second.used →
      OutcomeRelated previous live
        (ScopedSubtypeReads.run world sourceRows base alpha budget before first)
        (ScopedSubtypeReads.run world sourceRows base alpha budget (renameState previous before) second) := by
  induction budget with
  | zero =>
      intro previous live before _ covered first second firstProtected secondProtected
      refine ⟨previous, fun _ _ => rfl, rfl, ?_, ?_⟩
      · intro name member
        apply firstProtected
        rcases List.mem_append.mp member with old | stateName
        · exact old
        · exact covered stateName
      · intro name member
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        apply secondProtected
        apply List.mem_map.mpr
        refine ⟨original, ?_, rfl⟩
        rcases List.mem_append.mp present with old | stateName
        · exact old
        · exact covered stateName
  | succ budget ih =>
      intro previous live before beforeSafe covered first second firstProtected secondProtected
      let firstFound := ScopedSubtypeReads.discoveries world sourceRows base alpha before
        (before.known.zipIdx.drop before.frontier) first
      let secondFound := ScopedSubtypeReads.discoveries world sourceRows base alpha (renameState previous before)
        ((renameState previous before).known.zipIdx.drop (renameState previous before).frontier) second
      obtain ⟨middle, agrees, carried, firstKeeps, secondKeeps⟩ :=
        round_discoveries_coordinates world sourceRows safe base alpha equivariant previous live before
          beforeSafe covered first second firstProtected secondProtected
      change secondFound.1 = firstFound.1.map (renameEntry middle) at carried
      change live ++ entryNames firstFound.1 ⊆ firstFound.2.used at firstKeeps
      change (live ++ entryNames firstFound.1).map middle ⊆ secondFound.2.used at secondKeeps
      have sameEmpty : secondFound.1.isEmpty = firstFound.1.isEmpty := by rw [carried, List.isEmpty_map]
      have sameBefore := state_rename_agrees middle previous live agrees before covered
      let firstNext : State := ⟨before.known ++ firstFound.1, before.known.length⟩
      let secondNext : State := ⟨(renameState previous before).known ++ secondFound.1,
        (renameState previous before).known.length⟩
      have firstRound : ScopedSubtypeReads.round world sourceRows base alpha before first =
          (if firstFound.1.isEmpty then none else some firstNext, firstFound.2) := rfl
      have secondRound : ScopedSubtypeReads.round world sourceRows base alpha (renameState previous before) second =
          (if secondFound.1.isEmpty then none else some secondNext, secondFound.2) := rfl
      simp only [ScopedSubtypeReads.run, firstRound, secondRound, sameEmpty]
      by_cases empty : firstFound.1.isEmpty = true
      · simp only [empty, if_true]
        refine ⟨middle, agrees, ?_, ?_, ?_⟩
        · change Outcome.complete (renameState previous before) = Outcome.complete (renameState middle before)
          rw [sameBefore]
        · intro name member
          apply firstKeeps
          apply List.mem_append_left
          rcases List.mem_append.mp member with old | stateName
          · exact old
          · exact covered stateName
        · intro name member
          obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
          apply secondKeeps
          apply List.mem_map.mpr
          refine ⟨original, List.mem_append_left _ ?_, rfl⟩
          rcases List.mem_append.mp present with old | stateName
          · exact old
          · exact covered stateName
      · simp only [empty]
        have nextSame : secondNext = renameState middle firstNext := by
          dsimp only [secondNext, firstNext]
          rw [← sameBefore, carried]
          simp only [renameState, List.map_append, List.length_map]
        rw [nextSame]
        have nextSafe : SubtypeClosureRounds.Safe firstNext := by
          apply ScopedSubtypeReadSafety.round_safe world sourceRows safe base alpha before firstNext beforeSafe first
          rw [firstRound, if_neg empty]
        have nextCovered : entryNames firstNext.known ⊆ live ++ entryNames firstFound.1 := by
          simp only [firstNext, variables_append]
          intro name member
          rcases List.mem_append.mp member with old | fresh
          · exact List.mem_append_left _ (covered old)
          · exact List.mem_append_right _ fresh
        exact (ih middle (live ++ entryNames firstFound.1) firstNext nextSafe nextCovered
          firstFound.2 secondFound.2 firstKeeps secondKeeps).restrict_base
            (fun _ member => List.mem_append_left _ member) agrees

theorem captured_run_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (previous : Equiv.Perm String) (live : List String) (budget : Nat) (seeds : List Atom)
    (seedSafe : resourceFreeList seeds = true) (first second : Supply)
    (firstProtected : live ⊆ first.used) (secondProtected : live.map previous ⊆ second.used) :
    OutcomeRelated previous (live ++ atomListVariables seeds)
      (ScopedSubtypeReads.run world sourceRows base alpha budget (start seeds) (TypeReadSupply.remember first seeds))
      (ScopedSubtypeReads.run world sourceRows base alpha budget (start (seeds.map (renameAtom previous)))
        (TypeReadSupply.remember second (seeds.map (renameAtom previous)))) := by
  have firstKeeps : live ++ atomListVariables seeds ⊆ (TypeReadSupply.remember first seeds).used := by
    intro name member
    rcases List.mem_append.mp member with old | seedName
    · exact TypeReadSupply.remember_old first seeds (firstProtected old)
    · exact TypeReadSupply.remember_new first seeds seedName
  have secondKeeps : (live ++ atomListVariables seeds).map previous ⊆
      (TypeReadSupply.remember second (seeds.map (renameAtom previous))).used := by
    intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp present with old | seedName
    · exact TypeReadSupply.remember_old second _
        (secondProtected (List.mem_map.mpr ⟨original, old, rfl⟩))
    · apply TypeReadSupply.remember_new
      rw [← renameAtomList_eq_map, TypeReadSupply.variablesList_rename]
      exact List.mem_map.mpr ⟨original, seedName, rfl⟩
  have startCovered : entryNames (start seeds).known ⊆ live ++ atomListVariables seeds := by
    have inclusion : atomListVariables seeds ⊆ live ++ atomListVariables seeds :=
      fun _ member => List.mem_append_right live member
    simpa only [entryNames, start, List.map_map, Function.comp_def, List.map_id'] using
      inclusion
  have starts : renameState previous (start seeds) = start (seeds.map (renameAtom previous)) := by
    simp [renameState, start, List.map_map, Function.comp_def, renameEntry]
  simpa only [starts] using
    run_coordinates world sourceRows safe base alpha equivariant budget previous (live ++ atomListVariables seeds)
      (start seeds) (start_safe seeds seedSafe) startCovered _ _ firstKeeps secondKeeps

/-- The completed observation preserves its tag. A bounded unfinished run
does not turn into a completed empty closure under another allocation history. -/
theorem completeTypes_read_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (previous : Equiv.Perm String) (live : List String) (budget : Nat) (seeds : List Atom)
    (seedSafe : resourceFreeList seeds = true) (first second : Supply)
    (firstProtected : live ⊆ first.used) (secondProtected : live.map previous ⊆ second.used) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live ++ atomListVariables seeds, next name = previous name) ∧
      (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget (seeds.map (renameAtom previous)) second).1 =
        (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds first).1.map
          (List.map (renameAtom next)) ∧
      ((live ++ atomListVariables seeds) ++ atomListVariables
        (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds first).1.toList.flatten) ⊆
          (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds first).2.used ∧
      (((live ++ atomListVariables seeds) ++ atomListVariables
        (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds first).1.toList.flatten).map next) ⊆
          (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget
            (seeds.map (renameAtom previous)) second).2.used := by
  obtain ⟨next, agrees, carried, firstKeeps, secondKeeps⟩ :=
    captured_run_coordinates world sourceRows safe base alpha equivariant previous live budget seeds seedSafe
      first second firstProtected secondProtected
  have exposed : atomListVariables
      (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds first).1.toList.flatten ⊆
        entryNames (ScopedSubtypeReads.run world sourceRows base alpha budget (start seeds)
          (TypeReadSupply.remember first seeds)).1.state.known := by
    dsimp only [ScopedSubtypeReads.completeTypes]
    cases (ScopedSubtypeReads.run world sourceRows base alpha budget (start seeds)
        (TypeReadSupply.remember first seeds)).1 with
    | unfinished state => simp [atomListVariables]
    | complete state => simp [entryNames, Outcome.state]
  refine ⟨next, agrees, ?_, ?_, ?_⟩
  · dsimp only [ScopedSubtypeReads.completeTypes]
    rw [carried]
    cases (ScopedSubtypeReads.run world sourceRows base alpha budget (start seeds)
        (TypeReadSupply.remember first seeds)).1 with
    | unfinished _ => rfl
    | complete state => simp [renameOutcome, renameState, List.map_map, Function.comp_def, renameEntry]
  · intro name member
    apply firstKeeps
    rcases List.mem_append.mp member with old | returned
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (exposed returned)
  · intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    apply secondKeeps
    apply List.mem_map.mpr
    refine ⟨original, ?_, rfl⟩
    rcases List.mem_append.mp present with old | returned
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (exposed returned)

theorem completeTypes_coordinates (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (previous : Equiv.Perm String) (live : List String) (budget : Nat) (seeds : List Atom)
    (seedSafe : resourceFreeList seeds = true) (first second : Supply)
    (firstProtected : live ⊆ first.used) (secondProtected : live.map previous ⊆ second.used) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live ++ atomListVariables seeds, next name = previous name) ∧
      (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget (seeds.map (renameAtom previous)) second).1 =
        (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds first).1.map
          (List.map (renameAtom next)) := by
  obtain ⟨next, agrees, carried, _, _⟩ := completeTypes_read_coordinates world sourceRows safe base alpha
    equivariant previous live budget seeds seedSafe first second firstProtected secondProtected
  exact ⟨next, agrees, carried⟩

/-- At the immutable ground cache boundary, the complete closure's alpha
transport becomes literal ordered answer equality. Completion of the second
run is derived from the actual first result, not assumed. -/
theorem retained_completeTypes_equal (world : ExternalView) (sourceRows : List Atom)
    (safe : ScopedSubtypeReadSafety.RowsSafe sourceRows) (base : String)
    (alpha : Atom → Atom → Bool) (equivariant : AlphaEquivariant alpha)
    (budget : Nat) (seeds : List Atom) (seedSafe : resourceFreeList seeds = true)
    (first second : Supply) (types : List Atom)
    (completed : (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds first).1 = some types)
    (retained : RetainedTypePayloads.admittedList types = true) :
    (ScopedSubtypeReads.completeTypes world sourceRows base alpha budget seeds second).1 = some types := by
  obtain ⟨names, _, carried⟩ := completeTypes_coordinates world sourceRows safe base alpha equivariant
    (Equiv.refl String) [] budget seeds seedSafe first second (by simp) (by simp)
  have fixed : seeds.map (renameAtom (Equiv.refl String)) = seeds := by
    have identity : renameAtom (Equiv.refl String) = id := by
      funext atom
      rw [TypeFreshReadEquivalence.atom_rename_presentation]
      exact Spec.Type.Presentation.ScopeObservation.renameTypeVars_id atom
    rw [identity, List.map_id]
  rw [fixed, completed, Option.map_some, ← renameAtomList_eq_map,
    TypeRowFreshening.admittedList_rename names types retained] at carried
  exact carried

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeClosureCoordinates
