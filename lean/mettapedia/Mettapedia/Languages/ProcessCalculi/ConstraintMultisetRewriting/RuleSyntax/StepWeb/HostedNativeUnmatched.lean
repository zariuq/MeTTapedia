import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNativeRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.UnmatchedControls

/-!
# An admitted `unmatched` firing through the hosted-to-native adapter

The constructions compared are those of `HostedNative`: the contextual rule-syntax step (a bag store
of labelled occurrences; one match per step; guards asked at every solution of the information, after
the firing's own tells; the program a fixed set of rules beside the store; one knowledge store) and
the native step on live firings (a bag store of conditional rows; one match per step, its rule and
rows opened at reserved scopes; guards and queries asked at every solution of the information, after
the firing's own tells; the rule carried by the firing, its unknowns in the private family; one
knowledge store, published along the solver's returned frame).

The rule of a call that no equation matches carries an absence guard: no present row reads as
`eqn(T)` for the call `T` (`Hosting.unmatchedRule`). The adapter's admission law
(`HostedNative.admits_iff`) covers guarded rules; here it is exercised on an admitted firing of that
rule, with the refusing controls beside it.

## The adapter, condition by condition

Admission is four conditions on each side: the shapes, the enabling of the selection, solvable
information, and the guard at every solution. Each corresponds separately along the adapter:
`shapes_iff`, `solvable_iff`, `entails_iff` (the enabling is the same condition on both sides).
`refused_of_stuck`: a hosted state with no firing has no realized live firing of any placed rule of
the program, at any selection, ledger or budget.

## The unmatched call beside other rows, by its canonical firing

Take a state that represents a live alternative at its row `a` beside other rows
(`Composition.Beside`), whose focus is a call that no equation of the program matches.
`Composition.unmatched_beside_iff` says when the program fires there, if the other rows never read as
alternatives' rows: exactly when no other row matches the call at any solution of the knowledge
(`NoMatchingRow`). There the firing is existential; here it is the canonical one.

* `unmatched_admits`: under `NoMatchingRow`, the canonical firing that takes the call's row and makes
  one row not present is admitted (`unmatched_shapes`, `unmatched_solvable`, and its guard by
  `Composition.unmatched_guard_beside`).
* `admits_iff_noRow`, `realized_iff_noRow`: at that selection the canonical firing is admitted, and
  its live firing realized at every ledger and budget, exactly when `NoMatchingRow` holds; nothing is
  asked of what the other rows read as.
* `canonical_admits_iff`: when no other row reads as an alternative's row, the canonical firing of the
  unmatched call's rule at **any** selection is admitted exactly when the selection takes the call's
  row, reads nothing, makes one row not present, and no other row matches the call. The condition is
  needed for this form (`quiet_needed`).
* `realized_iff`: the same for its live firing in the native step, at every ledger and budget.
* `admits_iff_guard`, `realized_iff_guard`: at such a selection the guard alone decides admission, on
  both sides; `native_solvable`: the native information has a solution, so the guard is never asked
  vacuously.
* `live_checks`: the live firing carries the absence check; `ret_live_checks`: the `ret` rule's live
  firing carries none.

## The instance

The program with no equation and the query `(g $x b)`, beside one more row `eqn(t)`: `withRow t`,
presented by `withRowPresented t` (from `startWithPresented`); the rule is placed by
`HostedNative.placedUnmatched` (its collect query is empty, its guard a check).

* **Positive.** The row `eqn((g a $x))` with `$x` the call's own name
  (`Composition.UnmatchedControls.shared_row_fires`): no solution reads `(g a $x)` as `(g $x b)`.
  `shared_admitted`: the canonical firing taking the call's row `0` and making row `2` is admitted;
  `shared_realized`: its live firing is realized, at every ledger and budget; `shared_information`:
  the native information is the hosted information carried along the frame map; `shared_guard`: the
  native information has a solution and the absence check holds at each; `shared_result`: the native
  result is a dead-name extension of the adapted hosted result; `shared_run`: the one-member family
  runs in the native step, ending in a state that agrees with the adapted hosted result up to dead
  names.
* **Negative.** The same row text with `$x` the row's private name
  (`Composition.UnmatchedControls.private_row_stuck`), and the closed row `eqn((g a b))`, which
  matches the call at the solution `$x := a` and not at `$x := c`
  (`Composition.UnmatchedControls.partial_match_stuck`):
  `private_matching`, `partial_matching` (the row matches the call at a solution);
  `private_no_firing`, `partial_no_firing` (no firing on either side, for every placed rule of the
  program); `private_guard_fails`, `partial_guard_fails` (on each side the canonical firing's
  information has a solution, and its guard fails at one: the guard is what refuses).
* **Positive, decided by the knowledge.** The private row again, in `pinnedState`: the same rows and
  labels, with the knowledge that the row's private `$x` is `c` (`pinKnowledge`). The state still
  represents the query's alternative beside the row (`pinned_beside`), and every solution reads the row
  as `eqn((g a c))`, which is not `eqn` of the call (`pinned_noRow`). `pinned_admitted`,
  `pinned_realized`, `pinned_guard`: the canonical firing is admitted, its live firing realized, and
  the native guard holds at every solution of the native information, which has one.
  `knowledge_decides`: the two states differ only in their knowledge, which is their native states'
  equations; with it the live firing is realized, without it it is not.
* **Control of the condition on other rows.** Beside a second copy of the call's own alternative row
  (`twinState`): the copy represents the query's alternative beside the original
  (`twin_beside_copy`), the original never reads as an equation row (`twin_noRow`), and the firing
  taking the copy is admitted and realized (`twin_admitted`, `twin_realized`). So at the original row,
  where every other hypothesis of `canonical_admits_iff` holds and the copy reads as an alternative's
  row, a realized live firing takes another row (`quiet_needed`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative.UnmatchedInstance

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (NativeState LiveFiring native)
open SourceLanguage Hosting Hosting.Alternatives Hosting.Composition

/-! ## The adapter, condition by condition -/

section Conditions

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
  {P : CProgram S} {r : CRule S} (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ)

/-- **Solvable information corresponds**: the hosted information of the canonical firing has a
solution exactly when the native information of its live firing has one. -/
theorem solvable_iff :
    (Interface.Frames.contextual S).Solvable
        ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).information
          (Interface.Frames.contextual S) s) ↔
      (Interface.Frames.contextual S).Solvable (a := (state κ s p occupied).infoFrame)
        (live N s p occupied pl selection fuel).toNative.information := by
  rw [information_eq N s p occupied member pl selection fuel]
  refine (Interface.Frames.contextual_solvable_iff _).trans
    (Iff.trans ?_ (Interface.Frames.contextual_solvable_iff _).symm)
  exact (ContextualConditionalNaturality.solvable_extension_iff
    (infoExtension pl s.frame (ruleScope occupied selection)) _).symm

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The shapes correspond**: the canonical hosted firing has its shapes exactly when its live firing
has the native shapes. -/
theorem shapes_iff :
    (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).Shapes (Interface.Frames.contextual S) s ↔
      native.Shapes (live N s p occupied pl selection fuel).toNative := by
  have take : r.body.take.length = pl.body.take.length := by rw [pl.body_eq]; exact List.length_map ..
  have read : r.body.read.length = pl.body.read.length := by rw [pl.body_eq]; exact List.length_map ..
  have produce : r.body.produce.length = (produced pl s.frame (ruleScope occupied selection)).length := by
    rw [pl.body_eq, produced, List.length_map, List.length_map]
    exact List.length_map ..
  have collect : r.collect.length = ([] : List (Finset ℕ)).length := by
    rw [pl.collect_eq]
    rfl
  unfold RuleSyntax.Firing.Shapes
  constructor
  · rintro ⟨-, takenNodup, madeNodup, takeLength, readLength, produceLength, -⟩
    refine ⟨takenNodup, madeNodup, ?_, ?_, ?_⟩
    · show (pl.body.take.map _).length = _
      rw [List.length_map, ← take]
      exact takeLength
    · show (pl.body.read.map _).length = _
      rw [List.length_map, ← read]
      exact readLength
    · exact map_relabel _ selection.made _ madeNodup (produceLength.symm.trans produce)
  · rintro ⟨takenNodup, madeNodup, takeLength, readLength, outputs⟩
    refine ⟨RuleSyntax.Contextual.canonical_fresh s r member selection [], takenNodup, madeNodup, ?_, ?_, ?_,
      collect⟩
    · show r.body.take.length = selection.taken.length
      rw [take]
      exact (List.length_map ..).symm.trans takeLength
    · show r.body.read.length = selection.read.length
      rw [read]
      exact (List.length_map ..).symm.trans readLength
    · show r.body.produce.length = selection.made.length
      rw [produce]
      exact ((congrArg List.length outputs).symm.trans (List.length_map ..))

/-- **The guards correspond**: the hosted guard holds at every solution of the hosted information
exactly when the native guard holds at every solution of the native information. -/
theorem entails_iff :
    (Interface.Frames.contextual S).Entails
        ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).information
          (Interface.Frames.contextual S) s)
        (fun _ σ => (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).Holds
          (Interface.Frames.contextual S) s σ) ↔
      (Interface.Frames.contextual S).Entails (a := (state κ s p occupied).infoFrame)
        (live N s p occupied pl selection fuel).toNative.information
        (native.Holds (live N s p occupied pl selection fuel).toNative) := by
  rw [information_eq N s p occupied member pl selection fuel]
  constructor
  · intro asked b σ solved
    have restricted := (ContextualResidual.models_mapProblem _ _ _).mp solved
    exact (holds_iff N s p occupied member pl selection fuel σ).mp (asked b _ restricted)
  · intro asked b σ solved
    have lifted := (ContextualConditionalNaturality.models_liftModel_iff
      (infoExtension pl s.frame (ruleScope occupied selection)) σ _).mpr solved
    have held := (holds_iff N s p occupied member pl selection fuel
      (b := ⟨(infoExtension pl s.frame (ruleScope occupied selection)).Complement ⊕ b.Names,
        ContextualPrefixModels.extended (infoExtension pl s.frame (ruleScope occupied selection)).complementDeclarations
          b.arity⟩)
      ((infoExtension pl s.frame (ruleScope occupied selection)).liftModel σ)).mpr
      (asked ⟨(infoExtension pl s.frame (ruleScope occupied selection)).Complement ⊕ b.Names,
        ContextualPrefixModels.extended (infoExtension pl s.frame (ruleScope occupied selection)).complementDeclarations
          b.arity⟩ _ lifted)
    rw [ContextualGuardMatching.Extension.liftModel_square] at held
    exact (firing_holds_inclusion _ _ σ).mp held

end Conditions

section Stuck

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  (N : Nodes S Γ star) {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **No hosted firing, no native one**: at a hosted state where the translated program has no firing,
no live firing of a placed rule of the program is realized, at any selection, ledger or budget. -/
theorem refused_of_stuck {s : HostState S} (p : Presented Γ star s) (stuck : ∀ s', ¬ Fires N P s s')
    {r : CRule S} (member : r ∈ translate N P) (pl : Placed Γ star κ r) (occupied : Finset ℕ)
    (selection : Selection ℕ) (fuel : ℕ) :
    ¬ (live N s p occupied pl selection fuel).toNative.Realized := fun realized =>
  stuck _ ⟨_, (admits_iff N s p occupied member pl selection fuel).mpr realized, rfl⟩

end Stuck

/-! ## The unmatched call beside other rows, by its canonical firing -/

/-- **The canonical firing of the unmatched call's rule** at a hosted state and a selection. -/
abbrev canonicalUnmatched {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S} {Ty : Type}
    (P : SourceLanguage.Program κ Γ star Ty) (w : HostState S) (selection : Selection ℕ) :
    RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) w.frame :=
  RuleSyntax.Contextual.canonical (F := w.frame) (unmatchedRule N) (unmatchedRule_mem N P) selection []

section BesideRows

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S} {Ty : Type}
  {P : SourceLanguage.Program κ Γ star Ty} {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
  {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
  {w : HostState S} {a : ℕ} {others : Finset ℕ}

/-- The canonical firing taking the row `a` and making the row `m` has its shapes. -/
theorem unmatched_shapes (w : HostState S) (a m : ℕ) :
    (canonicalUnmatched N P w ⟨[a], [], [m]⟩).Shapes (Interface.Frames.contextual S) w :=
  ⟨RuleSyntax.Contextual.canonical_fresh w _ _ _ _, List.nodup_singleton a, List.nodup_singleton m, rfl, rfl, rfl,
    rfl⟩

/-- **Its information has a solution** beside other rows, when the alternative's store has one: the
solution of the store reads the call's row, and the rule's unknowns read the call and the stack. -/
theorem unmatched_solvable (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (solvable : Solvable K) (m : ℕ) :
    (Interface.Frames.contextual S).Solvable
      ((canonicalUnmatched N P w ⟨[a], [], [m]⟩).information (Interface.Frames.contextual S) w) := by
  have simple : Simple (canonicalUnmatched N P w ⟨[a], [], [m]⟩) a m
      (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))
      (observe (altN N (valueN N (unk .datum)) (unk .stack))) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨W, target, σ, solved⟩ := solvable
  have reads : branchReads N (⟨K, .value t, fs, ps⟩ : Branch κ Γ star Ty) ⟨W, target⟩
      (observe (encBranch N (instantiate σ) ⟨K, .value t, fs, ps⟩)) := ⟨σ, solved, rfl⟩
  obtain ⟨h, readsB, told, -⟩ :=
    (transfer_unmatched N (b := (⟨K, .eval (.apply t), fs, ps⟩ : Branch κ Γ star Ty)) rfl _).mpr reads
  obtain ⟨g, known, matched⟩ := (beside.hosted.reads _ _).mpr readsB
  obtain ⟨u, solvedU, -⟩ := simple_amalgamate simple (unmatched_shapes (P := P) N w a m).1
    (beside.row_present N) g h known told matched.symm
  exact ⟨_, u, solvedU⟩

/-- **The canonical witness**: beside other rows, at a call that no equation matches, when no other row
matches the call at any solution of the knowledge, the canonical firing of the unmatched call's rule
that takes the call's row and makes any row not present is admitted. -/
theorem unmatched_admits (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)])) (solvable : Solvable K)
    (noRow : NoMatchingRow N w a others) {m : ℕ} (fresh : m ∉ w.present) :
    (canonicalUnmatched N P w ⟨[a], [], [m]⟩).Admits (Interface.Frames.contextual S) w :=
  ⟨unmatched_shapes N w a m, enabled_single (beside.row_present N) fresh, unmatched_solvable N beside solvable m,
    unmatched_guard_beside N beside none noRow⟩

/-- **At the selection that takes the call's row and makes a row not present, exactly when no other
row matches**, whatever the other rows read as: the guard read at one solution of the information
that reads the call as the knowledge's solution does. -/
theorem admits_iff_noRow (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)])) (solvable : Solvable K)
    {m : ℕ} (fresh : m ∉ w.present) :
    (canonicalUnmatched N P w ⟨[a], [], [m]⟩).Admits (Interface.Frames.contextual S) w ↔
      NoMatchingRow N w a others := by
  refine ⟨fun admitted => ?_, fun noRow => unmatched_admits N beside none solvable noRow fresh⟩
  have simple : Simple (canonicalUnmatched N P w ⟨[a], [], [m]⟩) a m
      (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))
      (observe (altN N (valueN N (unk .datum)) (unk .stack))) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro o inO B σ known x y readsA sameRow
  have oPresent : o ∈ w.present := by rw [beside.present]; exact Finset.mem_union_right _ inO
  let h : Assignment (unknownArity Γ star) B.arity := fill x x x x y
  have matchedH : instantiateObservation h (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) =
      instantiateObservation σ (w.label a) := by
    rw [readsA]
    change observe (instantiate h _) = _
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_unk, instantiate_unk]
    rfl
  obtain ⟨u, solvedU, -, onRows, onTerms⟩ := simple_amalgamate simple admitted.1.1 (beside.row_present N) σ h
    known (fun _ inside => by cases inside) matchedH
  have checkMember : (RuleSyntax.Firing.opened (Interface.Frames.contextual S)
      (canonicalUnmatched N P w ⟨[a], [], [m]⟩)).checks =
      [.predicate .none (instantiateObservation (canonicalUnmatched N P w ⟨[a], [], [m]⟩).opening (unmatchedCheck N))] :=
    rfl
  have absent := (admitted.2.2.2 B u solvedU).1 _ (by rw [checkMember]; exact List.mem_singleton_self _)
  have inTerms : unmatchedCheck N ∈ (canonicalUnmatched N P w ⟨[a], [], [m]⟩).rule.terms := by
    show unmatchedCheck N ∈ (unmatchedRule N).terms
    simp [RuleSyntax.Rule.terms, unmatchedRule, RuleSyntax.checkTerms]
  apply absent o oPresent
  change instantiateObservation u
      (instantiateObservation (canonicalUnmatched N P w ⟨[a], [], [m]⟩).opening (unmatchedCheck N)) =
    instantiateObservation u (RuleSyntax.Firing.row (Interface.Frames.contextual S) w _ o)
  rw [onTerms _ inTerms, onRows o oPresent, sameRow]
  change observe (instantiate h (eqnN N (unk .datum))) = _
  rw [instantiate_eqnN, instantiate_unk]
  rfl

/-- **The canonical firing of the unmatched call's rule, at every selection.** Beside rows that never
read as alternatives' rows, at a call that no equation matches, it is admitted exactly when the
selection takes the call's row, reads nothing and makes one row not present, and no other row matches
the call at any solution of the knowledge. -/
theorem canonical_admits_iff (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (quiet : NeverReads (IsAlternative N) w others)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)])) (solvable : Solvable K)
    (selection : Selection ℕ) :
    (canonicalUnmatched N P w selection).Admits (Interface.Frames.contextual S) w ↔
      (∃ m, m ∉ w.present ∧ selection = ⟨[a], [], [m]⟩) ∧ NoMatchingRow N w a others := by
  constructor
  · intro admitted
    obtain ⟨m, taken, read, made, fresh⟩ := beside_takes N beside quiet admitted
    refine ⟨⟨m, fresh, ?_⟩, (unmatched_beside_iff N beside quiet none solvable).mp ⟨_, _, admitted, rfl⟩⟩
    obtain ⟨taken', read', made'⟩ := selection
    change taken' = [a] at taken
    change read' = [] at read
    change made' = [m] at made
    subst taken read made
    rfl
  · rintro ⟨⟨m, fresh, rfl⟩, noRow⟩
    exact unmatched_admits N beside none solvable noRow fresh

/-- **At a selection that takes the call's row and makes a row not present, the guard alone decides**:
the shapes, the enabling and solvable information hold there whatever the other rows are. -/
theorem admits_iff_guard (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others) (solvable : Solvable K)
    {m : ℕ} (fresh : m ∉ w.present) :
    (canonicalUnmatched N P w ⟨[a], [], [m]⟩).Admits (Interface.Frames.contextual S) w ↔
      (Interface.Frames.contextual S).Entails
        ((canonicalUnmatched N P w ⟨[a], [], [m]⟩).information (Interface.Frames.contextual S) w)
        (fun _ σ => (canonicalUnmatched N P w ⟨[a], [], [m]⟩).Holds (Interface.Frames.contextual S) w σ) :=
  ⟨fun admitted => admitted.2.2.2, fun guard =>
    ⟨unmatched_shapes N w a m, enabled_single (beside.row_present N) fresh, unmatched_solvable N beside solvable m,
      guard⟩⟩

/-- **The live firing carries the absence check**: the placed unmatched rule's one check, opened. -/
theorem live_checks (p : Presented Γ star w) (occupied : Finset ℕ) (selection : Selection ℕ) (fuel : ℕ) :
    (live N w p occupied (placedUnmatched (κ := κ) N) selection fuel).rule.checks =
      [.predicate .none (instantiate (place (placedUnmatched (κ := κ) N) w.frame) (eqnN N (unk .datum)))] :=
  rfl

/-- The `ret` rule's live firing carries no check. -/
theorem ret_live_checks (p : Presented Γ star w) (occupied : Finset ℕ) (selection : Selection ℕ) (fuel : ℕ) :
    (live N w p occupied (placedRet (κ := κ) N) selection fuel).rule.checks = [] :=
  rfl

/-- **The native information has a solution** at a selection that takes the call's row, whatever the
other rows are: the guard of the live firing is never asked vacuously. -/
theorem native_solvable (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others) (solvable : Solvable K)
    (m : ℕ) (p : Presented Γ star w) (occupied : Finset ℕ) (fuel : ℕ) :
    (Interface.Frames.contextual S).Solvable (a := (state κ w p occupied).infoFrame)
      (live N w p occupied (placedUnmatched (κ := κ) N) ⟨[a], [], [m]⟩ fuel).toNative.information :=
  (solvable_iff N w p occupied (unmatchedRule_mem N P) (placedUnmatched N) ⟨[a], [], [m]⟩ fuel).mp
    (unmatched_solvable N beside solvable m)

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **Through the adapter, at every selection, ledger and budget**: the live firing of the unmatched
call's rule beside other rows is realized exactly when its selection takes the call's row, reads
nothing and makes one row not present, and no other row matches the call at any solution of the
knowledge. -/
theorem realized_iff (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (quiet : NeverReads (IsAlternative N) w others)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)])) (solvable : Solvable K)
    (p : Presented Γ star w) (occupied : Finset ℕ) (selection : Selection ℕ) (fuel : ℕ) :
    (live N w p occupied (placedUnmatched (κ := κ) N) selection fuel).toNative.Realized ↔
      (∃ m, m ∉ w.present ∧ selection = ⟨[a], [], [m]⟩) ∧ NoMatchingRow N w a others :=
  (admits_iff N w p occupied (unmatchedRule_mem N P) (placedUnmatched N) selection fuel).symm.trans
    (canonical_admits_iff N beside quiet none solvable selection)

/-- **Through the adapter, at the selection that takes the call's row and makes a row not present**: the
live firing is realized exactly when no other row matches the call at any solution of the knowledge,
whatever the other rows read as, at every ledger and budget. -/
theorem realized_iff_noRow (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)])) (solvable : Solvable K)
    {m : ℕ} (fresh : m ∉ w.present) (p : Presented Γ star w) (occupied : Finset ℕ) (fuel : ℕ) :
    (live N w p occupied (placedUnmatched (κ := κ) N) ⟨[a], [], [m]⟩ fuel).toNative.Realized ↔
      NoMatchingRow N w a others :=
  (admits_iff N w p occupied (unmatchedRule_mem N P) (placedUnmatched N) ⟨[a], [], [m]⟩ fuel).symm.trans
    (admits_iff_noRow N beside none solvable fresh)

/-- **The guard alone decides, in the native step**: at a selection that takes the call's row and makes
a row not present, the live firing is realized exactly when the native guard holds at every solution
of the native information. -/
theorem realized_iff_guard (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others) (solvable : Solvable K)
    {m : ℕ} (fresh : m ∉ w.present) (p : Presented Γ star w) (occupied : Finset ℕ) (fuel : ℕ) :
    (live N w p occupied (placedUnmatched (κ := κ) N) ⟨[a], [], [m]⟩ fuel).toNative.Realized ↔
      (Interface.Frames.contextual S).Entails (a := (state κ w p occupied).infoFrame)
        (live N w p occupied (placedUnmatched (κ := κ) N) ⟨[a], [], [m]⟩ fuel).toNative.information
        (native.Holds (live N w p occupied (placedUnmatched (κ := κ) N) ⟨[a], [], [m]⟩ fuel).toNative) :=
  (admits_iff N w p occupied (unmatchedRule_mem N P) (placedUnmatched N) ⟨[a], [], [m]⟩ fuel).symm.trans
    ((admits_iff_guard N beside solvable fresh).trans
      (entails_iff N w p occupied (unmatchedRule_mem N P) (placedUnmatched N) ⟨[a], [], [m]⟩ fuel))

end BesideRows

/-! ## The start of a query beside one more row, presented -/

/-- **The start of a query with one more row, presented**: the start's own terms, and the term `t` at
the identity after the alternative's. -/
def startWithPresented {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S} {Ty : Type}
    (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty)
    (t : Term (signature S (startArity κ)) Γ star) :
    Presented Γ star (startWith N P q (observe t)) where
  term o := if o = P.equations.length + 1 then t else (startPresented N P q).term o
  label_eq o := by
    by_cases row : o = P.equations.length + 1
    · subst row
      rw [if_pos rfl]
      show Function.update (startLabel N P q) (P.equations.length + 1) (observe t) (P.equations.length + 1) = _
      exact Function.update_self _ _ _
    · rw [if_neg row]
      show Function.update (startLabel N P q) (P.equations.length + 1) (observe t) o = _
      rw [Function.update_of_ne row]
      exact (startPresented N P q).label_eq o

/-! ## The instance: the query `(g $x b)` of the program with no equation, beside one row -/

section Instance

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Composition.Controls (N P0 read_queryNames)
open Hosting.Composition.UnmatchedControls (B₀ close gxT gaxT gabT qgx qgx_unopened reads_alt label_row
  eqn_row_quiet shared_row_fires private_row_stuck partial_match_stuck)

/-- The start of the query `(g $x b)` of the program with no equation, beside one more row `eqn(t)`. -/
abbrev withRow (t : Term (signature MSig (startArity mkeys)) [] ()) : HostState MSig :=
  startWith N P0 qgx (observe (eqnN N t))

/-- That state, presented. -/
def withRowPresented (t : Term (signature MSig (startArity mkeys)) [] ()) :
    Presented ([] : Ctx MSig) () (withRow t) :=
  startWithPresented N P0 qgx (eqnN N t)

/-- The live firing of the unmatched call's rule at that state. -/
noncomputable abbrev liveWith (t : Term (signature MSig (startArity mkeys)) [] ()) (occupied : Finset ℕ)
    (selection : Selection ℕ) (fuel : ℕ) :
    LiveFiring (state mkeys (withRow t) (withRowPresented t) occupied) :=
  live N (withRow t) (withRowPresented t) occupied (placedUnmatched (κ := mkeys) N) selection fuel

/-- **Beside one row `eqn(t)`, through the adapter**: the live firing of the unmatched call's rule is
realized exactly when its selection takes the call's row `0`, reads nothing and makes one row not
present, and no solution reads the row `eqn(t)` as `eqn` of the call. -/
theorem withRow_realized_iff (t : Term (signature MSig (startArity mkeys)) [] ()) (occupied : Finset ℕ)
    (selection : Selection ℕ) (fuel : ℕ) :
    (liveWith t occupied selection fuel).toNative.Realized ↔
      (∃ m, m ∉ (withRow t).present ∧ selection = ⟨[0], [], [m]⟩) ∧ NoMatchingRow N (withRow t) 0 {1} :=
  realized_iff N (startWith_beside N (P := P0) qgx (observe (eqnN N t)) qgx_unopened) (eqn_row_quiet t)
    (fun _ member => by cases member) live_nil (withRowPresented t) occupied selection fuel

/-- The row `eqn((g a $x))`, with `$x` the call's own name. -/
abbrev sharedRow : Term (signature MSig (startArity mkeys)) [] () := instantiate queryNames gaxT

/-- The row `eqn((g a $x))`, with `$x` the row's private name. -/
abbrev privateRow : Term (signature MSig (startArity mkeys)) [] () := instantiate (rowNames 7) gaxT

/-- The closed row `eqn((g a b))`. -/
abbrev partialRow : Term (signature MSig (startArity mkeys)) [] () := instantiate (rowNames 7) gabT

/-! ### Positive: the row shares the call's name -/

/-- No solution reads the row `eqn((g a $x))` as `eqn` of the call `(g $x b)` (from
`Composition.UnmatchedControls.shared_row_fires` by `Composition.unmatched_beside_iff`). -/
theorem shared_noRow : NoMatchingRow N (withRow sharedRow) 0 {1} :=
  (unmatched_beside_iff N (startWith_beside N (P := P0) qgx (observe (eqnN N sharedRow)) qgx_unopened)
    (eqn_row_quiet sharedRow) (fun _ member => by cases member) live_nil).mp shared_row_fires

/-- **The canonical firing is admitted**: the unmatched call's rule, taking the call's row `0` and
making the row `2`, beside the row `eqn((g a $x))`. -/
theorem shared_admitted :
    (canonicalUnmatched N P0 (withRow sharedRow) ⟨[0], [], [2]⟩).Admits (Interface.Frames.contextual MSig)
      (withRow sharedRow) :=
  (canonical_admits_iff N (startWith_beside N (P := P0) qgx (observe (eqnN N sharedRow)) qgx_unopened)
    (eqn_row_quiet sharedRow) (fun _ member => by cases member) live_nil _).mpr
    ⟨⟨2, by decide, rfl⟩, shared_noRow⟩

/-- **Positive, through the adapter**: its live firing is realized, at every ledger and budget. -/
theorem shared_realized (occupied : Finset ℕ) (fuel : ℕ) :
    (liveWith sharedRow occupied ⟨[0], [], [2]⟩ fuel).toNative.Realized :=
  (admits_iff N (withRow sharedRow) (withRowPresented sharedRow) occupied (unmatchedRule_mem N P0)
    (placedUnmatched N) ⟨[0], [], [2]⟩ fuel).mp shared_admitted

/-- **Its information**: the native information is the hosted information carried along the
information frame map. -/
theorem shared_information (occupied : Finset ℕ) (fuel : ℕ) :
    (liveWith sharedRow occupied ⟨[0], [], [2]⟩ fuel).toNative.information =
      ContextualResidual.mapProblem
        (infoExtension (placedUnmatched (κ := mkeys) N) (withRow sharedRow).frame
          (ruleScope occupied ⟨[0], [], [2]⟩)).assignment
        ((canonicalUnmatched N P0 (withRow sharedRow) ⟨[0], [], [2]⟩).information
          (Interface.Frames.contextual MSig) (withRow sharedRow)) :=
  information_eq N (withRow sharedRow) (withRowPresented sharedRow) occupied (unmatchedRule_mem N P0)
    (placedUnmatched N) ⟨[0], [], [2]⟩ fuel

/-- **Its guard, not vacuously**: the native information has a solution, and at every solution the
absence check holds. -/
theorem shared_guard (occupied : Finset ℕ) (fuel : ℕ) :
    (Interface.Frames.contextual MSig).Solvable
        (a := (state mkeys (withRow sharedRow) (withRowPresented sharedRow) occupied).infoFrame)
        (liveWith sharedRow occupied ⟨[0], [], [2]⟩ fuel).toNative.information ∧
      (Interface.Frames.contextual MSig).Entails
        (a := (state mkeys (withRow sharedRow) (withRowPresented sharedRow) occupied).infoFrame)
        (liveWith sharedRow occupied ⟨[0], [], [2]⟩ fuel).toNative.information
        ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).Holds
          (liveWith sharedRow occupied ⟨[0], [], [2]⟩ fuel).toNative) :=
  ((Interface.native_admits_iff (liveWith sharedRow occupied ⟨[0], [], [2]⟩ fuel).toNative).mp
    (shared_realized occupied fuel)).2.2

/-- **Its result**: the native result is a dead-name extension of the adapted hosted result, at the
native result's ledger. -/
theorem shared_result (occupied : Finset ℕ) (fuel : ℕ) :
    Nonempty (Interface.NativeDead.DeadExtension
      (resultState N (withRow sharedRow) (withRowPresented sharedRow) occupied (unmatchedRule_mem N P0)
        (placedUnmatched N) ⟨[0], [], [2]⟩ fuel (shared_realized occupied fuel))
      ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).result
        (liveWith sharedRow occupied ⟨[0], [], [2]⟩ fuel).toNative (shared_realized occupied fuel))) :=
  ⟨resultExtension N (withRow sharedRow) (withRowPresented sharedRow) occupied (unmatchedRule_mem N P0)
    (placedUnmatched N) ⟨[0], [], [2]⟩ fuel (shared_realized occupied fuel)⟩

/-- The unmatched call's firing, as a member of a hosted family. -/
def sharedMember : Rounds.Member ([] : Ctx MSig) () mkeys (translate N P0) :=
  ⟨unmatchedRule N, unmatchedRule_mem N P0, placedUnmatched N, ⟨[0], [], [2]⟩, 0⟩

/-- **Its run**: the one-member family is a hosted run, so (`Rounds.sequential_iff`) it runs in the
native step from the adapted state, ending in a state that agrees with the adapted hosted result up
to dead names. -/
theorem shared_run (occupied : Finset ℕ) :
    ∃ u : NativeState MSig ℕ ([] : Ctx MSig) (),
      Interface.NativeIterated.Sequential (state mkeys (withRow sharedRow) (withRowPresented sharedRow) occupied)
        ([sharedMember].map (Rounds.Member.live N (withRow sharedRow) (withRowPresented sharedRow) occupied)) u ∧
      Interface.NativeDead.DeadEquiv
        (state mkeys ((sharedMember.hosted (withRow sharedRow)).result (Interface.Frames.contextual MSig)
          (withRow sharedRow))
          (resultPresented (withRow sharedRow) (withRowPresented sharedRow) sharedMember.member sharedMember.placed
            sharedMember.selection) (Rounds.nextLedger occupied sharedMember.selection)) u :=
  (Rounds.sequential_iff N [sharedMember] (withRow sharedRow) (withRowPresented sharedRow) occupied).2
    (.cons sharedMember [] shared_admitted (.nil _ _ _))

/-! ### Negative: a row that matches the call at a solution -/

/-- The row `eqn((g a $x))` with `$x` the row's private name matches the call at a solution. -/
theorem private_matching : ¬ NoMatchingRow N (withRow privateRow) 0 {1} := fun noRow => by
  obtain ⟨w', fires⟩ := (unmatched_beside_iff N
    (startWith_beside N (P := P0) qgx (observe (eqnN N privateRow)) qgx_unopened)
    (eqn_row_quiet privateRow) (fun _ member => by cases member) live_nil).mpr noRow
  exact private_row_stuck w' fires

/-- The closed row `eqn((g a b))` matches the call at a solution. -/
theorem partial_matching : ¬ NoMatchingRow N (withRow partialRow) 0 {1} := fun noRow => by
  obtain ⟨w', fires⟩ := (unmatched_beside_iff N
    (startWith_beside N (P := P0) qgx (observe (eqnN N partialRow)) qgx_unopened)
    (eqn_row_quiet partialRow) (fun _ member => by cases member) live_nil).mpr noRow
  exact partial_match_stuck w' fires

/-- **Negative, on both sides**: beside the row `eqn((g a $x))` with `$x` the row's private name, the
translated program has no firing, and no live firing of any placed rule of the program is realized,
at any selection, ledger or budget. -/
theorem private_no_firing :
    (∀ w', ¬ Fires N P0 (withRow privateRow) w') ∧
      ∀ {r : CRule MSig}, r ∈ translate N P0 → ∀ (pl : Placed ([] : Ctx MSig) () mkeys r)
        (occupied : Finset ℕ) (selection : Selection ℕ) (fuel : ℕ),
        ¬ (live N (withRow privateRow) (withRowPresented privateRow) occupied pl selection fuel).toNative.Realized :=
  ⟨private_row_stuck, fun member pl occupied selection fuel =>
    refused_of_stuck N (withRowPresented privateRow) private_row_stuck member pl occupied selection fuel⟩

/-- **Negative, on both sides**: beside the closed row `eqn((g a b))`, which matches the call at one
solution only, the translated program has no firing, and no live firing of any placed rule of the
program is realized, at any selection, ledger or budget. -/
theorem partial_no_firing :
    (∀ w', ¬ Fires N P0 (withRow partialRow) w') ∧
      ∀ {r : CRule MSig}, r ∈ translate N P0 → ∀ (pl : Placed ([] : Ctx MSig) () mkeys r)
        (occupied : Finset ℕ) (selection : Selection ℕ) (fuel : ℕ),
        ¬ (live N (withRow partialRow) (withRowPresented partialRow) occupied pl selection fuel).toNative.Realized :=
  ⟨partial_match_stuck, fun member pl occupied selection fuel =>
    refused_of_stuck N (withRowPresented partialRow) partial_match_stuck member pl occupied selection fuel⟩

/-- **The guard is what refuses, on both sides**: beside a row that matches the call at a solution, the
canonical firing taking the call's row `0` and making the row `2` has hosted information with a
solution and its hosted guard fails at one; its live firing has native information with a solution
and its native guard fails at one. -/
theorem guard_fails_of_matching (t : Term (signature MSig (startArity mkeys)) [] ())
    (matching : ¬ NoMatchingRow N (withRow t) 0 {1}) (occupied : Finset ℕ) (fuel : ℕ) :
    ((Interface.Frames.contextual MSig).Solvable
        ((canonicalUnmatched N P0 (withRow t) ⟨[0], [], [2]⟩).information (Interface.Frames.contextual MSig)
          (withRow t)) ∧
      ¬ (Interface.Frames.contextual MSig).Entails
        ((canonicalUnmatched N P0 (withRow t) ⟨[0], [], [2]⟩).information (Interface.Frames.contextual MSig)
          (withRow t))
        (fun _ σ => (canonicalUnmatched N P0 (withRow t) ⟨[0], [], [2]⟩).Holds (Interface.Frames.contextual MSig)
          (withRow t) σ)) ∧
    ((Interface.Frames.contextual MSig).Solvable
        (a := (state mkeys (withRow t) (withRowPresented t) occupied).infoFrame)
        (liveWith t occupied ⟨[0], [], [2]⟩ fuel).toNative.information ∧
      ¬ (Interface.Frames.contextual MSig).Entails
        (a := (state mkeys (withRow t) (withRowPresented t) occupied).infoFrame)
        (liveWith t occupied ⟨[0], [], [2]⟩ fuel).toNative.information
        ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).Holds
          (liveWith t occupied ⟨[0], [], [2]⟩ fuel).toNative)) := by
  have beside := startWith_beside N (P := P0) qgx (observe (eqnN N t)) qgx_unopened
  have fresh : (2 : ℕ) ∉ (withRow t).present := by
    show (2 : ℕ) ∉ hostedRows P0 P0.equations.length ∪ {P0.equations.length + 1}
    decide
  have refused : ¬ (liveWith t occupied ⟨[0], [], [2]⟩ fuel).toNative.Realized := fun realized =>
    matching ((withRow_realized_iff t occupied ⟨[0], [], [2]⟩ fuel).mp realized).2
  refine ⟨⟨unmatched_solvable N beside live_nil 2, fun guard => refused ?_⟩,
    ⟨native_solvable N beside live_nil 2 (withRowPresented t) occupied fuel, fun guard => refused ?_⟩⟩
  · exact (admits_iff N (withRow t) (withRowPresented t) occupied (unmatchedRule_mem N P0) (placedUnmatched N)
      ⟨[0], [], [2]⟩ fuel).mp ((admits_iff_guard N beside live_nil fresh).mpr guard)
  · exact (realized_iff_guard N beside live_nil fresh (withRowPresented t) occupied fuel).mpr guard

/-- **The private row: the guard refuses, on both sides.** -/
theorem private_guard_fails (occupied : Finset ℕ) (fuel : ℕ) :
    ((Interface.Frames.contextual MSig).Solvable
        ((canonicalUnmatched N P0 (withRow privateRow) ⟨[0], [], [2]⟩).information
          (Interface.Frames.contextual MSig) (withRow privateRow)) ∧
      ¬ (Interface.Frames.contextual MSig).Entails
        ((canonicalUnmatched N P0 (withRow privateRow) ⟨[0], [], [2]⟩).information
          (Interface.Frames.contextual MSig) (withRow privateRow))
        (fun _ σ => (canonicalUnmatched N P0 (withRow privateRow) ⟨[0], [], [2]⟩).Holds
          (Interface.Frames.contextual MSig) (withRow privateRow) σ)) ∧
    ((Interface.Frames.contextual MSig).Solvable
        (a := (state mkeys (withRow privateRow) (withRowPresented privateRow) occupied).infoFrame)
        (liveWith privateRow occupied ⟨[0], [], [2]⟩ fuel).toNative.information ∧
      ¬ (Interface.Frames.contextual MSig).Entails
        (a := (state mkeys (withRow privateRow) (withRowPresented privateRow) occupied).infoFrame)
        (liveWith privateRow occupied ⟨[0], [], [2]⟩ fuel).toNative.information
        ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).Holds
          (liveWith privateRow occupied ⟨[0], [], [2]⟩ fuel).toNative)) :=
  guard_fails_of_matching privateRow private_matching occupied fuel

/-- **The closed partial row: the guard refuses, on both sides.** -/
theorem partial_guard_fails (occupied : Finset ℕ) (fuel : ℕ) :
    ((Interface.Frames.contextual MSig).Solvable
        ((canonicalUnmatched N P0 (withRow partialRow) ⟨[0], [], [2]⟩).information
          (Interface.Frames.contextual MSig) (withRow partialRow)) ∧
      ¬ (Interface.Frames.contextual MSig).Entails
        ((canonicalUnmatched N P0 (withRow partialRow) ⟨[0], [], [2]⟩).information
          (Interface.Frames.contextual MSig) (withRow partialRow))
        (fun _ σ => (canonicalUnmatched N P0 (withRow partialRow) ⟨[0], [], [2]⟩).Holds
          (Interface.Frames.contextual MSig) (withRow partialRow) σ)) ∧
    ((Interface.Frames.contextual MSig).Solvable
        (a := (state mkeys (withRow partialRow) (withRowPresented partialRow) occupied).infoFrame)
        (liveWith partialRow occupied ⟨[0], [], [2]⟩ fuel).toNative.information ∧
      ¬ (Interface.Frames.contextual MSig).Entails
        (a := (state mkeys (withRow partialRow) (withRowPresented partialRow) occupied).infoFrame)
        (liveWith partialRow occupied ⟨[0], [], [2]⟩ fuel).toNative.information
        ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).Holds
          (liveWith partialRow occupied ⟨[0], [], [2]⟩ fuel).toNative)) :=
  guard_fails_of_matching partialRow partial_matching occupied fuel

/-! ### Positive: knowledge pins the row's private name -/

/-- The knowledge that the private row's own `$x` (its copy for row `7`) is `c`. -/
abbrev pinKnowledge : EquationStore (Observation MSig (startArity mkeys)) :=
  [(observe (instantiate (rowNames 7) xName), observe (instantiate (rowNames 7) (sym "c")))]

/-- **The private row with its name pinned**: the rows and labels of `withRow privateRow`, with the
knowledge `pinKnowledge`. -/
def pinnedState : HostState MSig :=
  ⟨(withRow privateRow).frame, pinKnowledge, (withRow privateRow).present, (withRow privateRow).label⟩

/-- That state, presented: its labels are those of `withRow privateRow`. -/
def pinnedPresented : Presented ([] : Ctx MSig) () pinnedState :=
  ⟨(withRowPresented privateRow).term, (withRowPresented privateRow).label_eq⟩

/-- What the knowledge says: the row's private `$x` reads as `c`. -/
theorem pinned_known {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models σ pinnedState.knowledge ↔ σ (.inr (7, fo [] [7] 0)) = symAt "c" := by
  have read : ∀ t : MData,
      instantiate σ (instantiate (rowNames 7) t) = instantiate (fun x => σ (.inr (7, x))) t := by
    intro t
    rw [instantiate_comp]
    apply congrArg (fun ρ => instantiate ρ t)
    funext x
    exact instantiate_generator σ (.inr (7, x))
  have atX : instantiate σ (instantiate (rowNames 7) xName) = σ (.inr (7, fo [] [7] 0)) :=
    (read xName).trans (instantiate_foD (fun x => σ (.inr (7, x))) [] [7] 0)
  have atC : instantiate σ (instantiate (rowNames 7) (sym "c")) = symAt "c" := (read (sym "c")).trans rfl
  constructor
  · intro solved
    have same : observe (instantiate σ (instantiate (rowNames 7) xName)) =
        observe (instantiate σ (instantiate (rowNames 7) (sym "c"))) := solved _ (List.mem_singleton_self _)
    rw [atX, atC] at same
    exact observe_injective same
  · intro isC e member
    rw [List.mem_singleton.mp member]
    show observe (instantiate σ (instantiate (rowNames 7) xName)) =
      observe (instantiate σ (instantiate (rowNames 7) (sym "c")))
    rw [atX, atC, isC]

/-- An instantiation of the start's names: the query's names as `σ` reads them, every private copy by
`c`. -/
def pinAt {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    Assignment (startArity mkeys) B.arity
  | .inl x => σ (.inl x)
  | .inr _ => symAt "c"

theorem pinAt_known {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models (pinAt σ) pinnedState.knowledge :=
  (pinned_known (pinAt σ)).mpr rfl

/-- **The pinned state represents the query's alternative beside the private row**: the knowledge speaks
only of the row's private name, so every reading of the call's row is still a reading of the query's
alternative, and conversely. -/
theorem pinned_beside :
    Beside N P0 0 (initialBranch qgx) pinnedState P0.equations.length {P0.equations.length + 1} := by
  have plain := startWith_beside N (P := P0) qgx (observe (eqnN N privateRow)) qgx_unopened
  refine ⟨⟨plain.hosted.notRow, plain.hosted.present, fun B q => Iff.trans ?_ (plain.hosted.reads B q),
    fun _ _ _ i hi => absurd hi (Nat.not_lt_zero i), fun _ _ _ i hi => absurd hi (Nat.not_lt_zero i),
    plain.hosted.fresh, plain.hosted.noPending⟩, plain.present, plain.apart⟩
  constructor
  · rintro ⟨σ, -, rfl⟩
    exact ⟨σ, (fun e member => by cases member), rfl⟩
  · rintro ⟨σ, -, rfl⟩
    refine ⟨pinAt σ, pinAt_known σ, ?_⟩
    show instantiateObservation (pinAt σ) ((startWith N P0 qgx (observe (eqnN N privateRow))).label 0) =
      instantiateObservation σ ((startWith N P0 qgx (observe (eqnN N privateRow))).label 0)
    rw [reads_alt, reads_alt, read_queryNames, read_queryNames, instantiate_emptyN N, instantiate_emptyN N]
    rfl

/-- The private row never reads as an alternative's row in the pinned state either. -/
theorem pinned_quiet : NeverReads (IsAlternative N) pinnedState {P0.equations.length + 1} :=
  fun o inside B σ _ => eqn_row_quiet privateRow o inside B σ (fun e member => by cases member)

/-- **With the pin, no solution reads the private row as `eqn` of the call**: every solution reads the
row as `eqn((g a c))`, and the call as `(g σ($x) b)`. -/
theorem pinned_noRow : NoMatchingRow N pinnedState P0.equations.length {P0.equations.length + 1} := by
  intro o inside B σ known x y readsA sameRow
  rw [Finset.mem_singleton.mp inside] at sameRow
  have call : instantiateObservation σ ((startWith N P0 qgx (observe (eqnN N privateRow))).label 0) =
      observe (altN N (evalN N (applyN N x)) y) := readsA
  rw [reads_alt] at call
  obtain ⟨onFocus, -⟩ := vec2_inj (N.args_eq (observe_injective call))
  have onCall := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
  have row : instantiateObservation σ
      ((startWith N P0 qgx (observe (eqnN N privateRow))).label (P0.equations.length + 1)) =
      observe (eqnN N x) := sameRow
  rw [label_row] at row
  change observe (instantiate σ (eqnN N privateRow)) = _ at row
  rw [instantiate_eqnN] at row
  have onRow := vec1_inj (N.args_eq (observe_injective row))
  have read : instantiate σ (instantiate (rowNames 7) gaxT) = instantiate (fun x => σ (.inr (7, x))) gaxT := by
    rw [instantiate_comp]
    apply congrArg (fun ρ => instantiate ρ gaxT)
    funext x
    exact instantiate_generator σ (.inr (7, x))
  have same : instantiate σ (instantiate (rowNames 7) gaxT) = instantiate σ (instantiate queryNames gxT) :=
    onRow.trans onCall.symm
  rw [read, read_queryNames] at same
  have unfolded : tupleAt [symAt "g", symAt "a", instantiate (fun x => σ (.inr (7, x))) xName] =
      tupleAt [symAt "g", instantiate (fun x => σ (.inl x)) xName, symAt "b"] := same
  obtain ⟨-, -, third⟩ := tuple3_inj unfolded
  have atX : instantiate (fun x => σ (.inr (7, x))) xName = σ (.inr (7, fo [] [7] 0)) :=
    instantiate_foD (fun x => σ (.inr (7, x))) [] [7] 0
  rw [atX, (pinned_known σ).mp known] at third
  simp [symAt] at third

/-- **The canonical firing is admitted in the pinned state**: taking the call's row `0` and making the
row `2`. -/
theorem pinned_admitted :
    (canonicalUnmatched N P0 pinnedState ⟨[0], [], [2]⟩).Admits (Interface.Frames.contextual MSig) pinnedState :=
  (canonical_admits_iff N pinned_beside pinned_quiet (fun _ member => by cases member) live_nil _).mpr
    ⟨⟨2, by decide, rfl⟩, pinned_noRow⟩

/-- **Positive, through the adapter**: its live firing is realized, at every ledger and budget. The
native state's equations are the pin. -/
theorem pinned_realized (occupied : Finset ℕ) (fuel : ℕ) :
    (live N pinnedState pinnedPresented occupied (placedUnmatched (κ := mkeys) N) ⟨[0], [], [2]⟩
      fuel).toNative.Realized :=
  (admits_iff N pinnedState pinnedPresented occupied (unmatchedRule_mem N P0) (placedUnmatched N) ⟨[0], [], [2]⟩
    fuel).mp pinned_admitted

/-- **Its guard, not vacuously**: the native information has a solution, and at every solution the
absence check holds. -/
theorem pinned_guard (occupied : Finset ℕ) (fuel : ℕ) :
    (Interface.Frames.contextual MSig).Solvable
        (a := (state mkeys pinnedState pinnedPresented occupied).infoFrame)
        (live N pinnedState pinnedPresented occupied (placedUnmatched (κ := mkeys) N) ⟨[0], [], [2]⟩
          fuel).toNative.information ∧
      (Interface.Frames.contextual MSig).Entails
        (a := (state mkeys pinnedState pinnedPresented occupied).infoFrame)
        (live N pinnedState pinnedPresented occupied (placedUnmatched (κ := mkeys) N) ⟨[0], [], [2]⟩
          fuel).toNative.information
        ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).Holds
          (live N pinnedState pinnedPresented occupied (placedUnmatched (κ := mkeys) N) ⟨[0], [], [2]⟩
            fuel).toNative) :=
  ((Interface.native_admits_iff (live N pinnedState pinnedPresented occupied (placedUnmatched (κ := mkeys) N)
    ⟨[0], [], [2]⟩ fuel).toNative).mp (pinned_realized occupied fuel)).2.2

/-- **The knowledge decides, on both sides.** The pinned state and `withRow privateRow` have the same
frame, present rows and labels; their native states differ only in their equations, which are their
knowledge. With the pin the live firing is realized; without it, it is not. -/
theorem knowledge_decides (occupied : Finset ℕ) (fuel : ℕ) :
    pinnedState.frame = (withRow privateRow).frame ∧ pinnedState.present = (withRow privateRow).present ∧
      pinnedState.label = (withRow privateRow).label ∧
      (state mkeys pinnedState pinnedPresented occupied).state.equations = pinKnowledge ∧
      (state mkeys (withRow privateRow) (withRowPresented privateRow) occupied).state.equations = [] ∧
      (live N pinnedState pinnedPresented occupied (placedUnmatched (κ := mkeys) N) ⟨[0], [], [2]⟩
        fuel).toNative.Realized ∧
      ¬ (liveWith privateRow occupied ⟨[0], [], [2]⟩ fuel).toNative.Realized :=
  ⟨rfl, rfl, rfl, rfl, rfl, pinned_realized occupied fuel,
    private_no_firing.2 (unmatchedRule_mem N P0) (placedUnmatched N) occupied ⟨[0], [], [2]⟩ fuel⟩

/-! ### Control of the condition on other rows: a second copy of the call's row -/

/-- The start of `(g $x b)` beside a second copy of the call's own alternative row. -/
abbrev twinState : HostState MSig :=
  startWith N P0 qgx (observe (encAlt N (instantiate queryNames) (.eval qgx) []))

/-- That state, presented. -/
def twinPresented : Presented ([] : Ctx MSig) () twinState :=
  startWithPresented N P0 qgx (encAlt N (instantiate queryNames) (.eval qgx) [])

/-- The copy, row `1`, represents the query's alternative beside the original row `0`. -/
theorem twin_beside_copy : Beside N P0 0 (initialBranch qgx) twinState 1 {0} := by
  have first := startWith_beside N (P := P0) qgx (observe (encAlt N (instantiate queryNames) (.eval qgx) []))
    qgx_unopened
  refine ⟨⟨Nat.zero_le 1, rfl, fun B q => first.hosted.reads B q, fun _ _ _ i hi => absurd hi (Nat.not_lt_zero i),
    fun _ _ _ i hi => absurd hi (Nat.not_lt_zero i), first.hosted.fresh, first.hosted.noPending⟩, by decide,
    by decide⟩

/-- Beside the copy, the original row `0` is an alternative's row, never an equation row. -/
theorem twin_noRow : NoMatchingRow N twinState 1 {0} := by
  intro o inside B σ _ x _ _ sameRow
  rw [Finset.mem_singleton.mp inside] at sameRow
  have row := reads_alt σ (observe (encAlt N (instantiate queryNames) (.eval qgx) []))
  rw [sameRow] at row
  exact absurd (N.tag_eq (observe_injective row)) (by decide)

/-- **A second admitted firing**: the canonical firing taking the copy, row `1`, and making row `2`. -/
theorem twin_admitted :
    (canonicalUnmatched N P0 twinState ⟨[1], [], [2]⟩).Admits (Interface.Frames.contextual MSig) twinState :=
  (admits_iff_noRow N twin_beside_copy (fun _ member => by cases member) live_nil (by decide)).mpr twin_noRow

/-- **Through the adapter**: its live firing is realized, at every ledger and budget. -/
theorem twin_realized (occupied : Finset ℕ) (fuel : ℕ) :
    (live N twinState twinPresented occupied (placedUnmatched (κ := mkeys) N) ⟨[1], [], [2]⟩
      fuel).toNative.Realized :=
  (realized_iff_noRow N twin_beside_copy (fun _ member => by cases member) live_nil (by decide) twinPresented
    occupied fuel).mpr twin_noRow

/-- **The condition that no other row reads as an alternative's row is needed for every selection**
(`canonical_admits_iff`, `realized_iff`): at the original row `0` beside the copy, the state
represents the query's alternative, no equation matches the call, and the alternative's store has a
solution; the copy reads as an alternative's row; and the conclusion of `realized_iff` fails at the
selection taking the copy: its live firing is realized, although the selection does not take row `0`. -/
theorem quiet_needed (occupied : Finset ℕ) (fuel : ℕ) :
    Beside N P0 0 (initialBranch qgx) twinState P0.equations.length {P0.equations.length + 1} ∧
      (∀ e ∈ P0.equations, ¬ Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, gxT)])) ∧
      Solvable ([] : List (Constraint mkeys [] ())) ∧
      ¬ NeverReads (IsAlternative N) twinState {P0.equations.length + 1} ∧
      ¬ ((live N twinState twinPresented occupied (placedUnmatched (κ := mkeys) N) ⟨[1], [], [2]⟩
          fuel).toNative.Realized ↔
        (∃ m, m ∉ twinState.present ∧
          (⟨[1], [], [2]⟩ : Selection ℕ) = ⟨[P0.equations.length], [], [m]⟩) ∧
          NoMatchingRow N twinState P0.equations.length {P0.equations.length + 1}) := by
  refine ⟨startWith_beside N (P := P0) qgx _ qgx_unopened, (fun _ member => by cases member), live_nil,
    fun quiet => ?_, fun same => ?_⟩
  · have reads : instantiateObservation (close "a" "a") (twinState.label (P0.equations.length + 1)) =
        observe (altN N (evalN N (applyN N (instantiate (close "a" "a") (instantiate queryNames gxT))))
          (instantiate (close "a" "a") (emptyN N))) := by
      rw [label_row]
      exact reads_alt (close "a" "a") (observe (encAlt N (instantiate queryNames) (.eval qgx) []))
    exact quiet (P0.equations.length + 1) (Finset.mem_singleton_self _) B₀ (close "a" "a")
      (fun e member => by cases member) ⟨_, _, reads⟩
  · obtain ⟨m, -, shape⟩ := (same.mp (twin_realized occupied fuel)).1
    exact absurd (List.head_eq_of_cons_eq (congrArg Selection.taken shape)) (by decide)

end Instance

#print axioms solvable_iff
#print axioms shapes_iff
#print axioms entails_iff
#print axioms refused_of_stuck
#print axioms unmatched_shapes
#print axioms unmatched_solvable
#print axioms unmatched_admits
#print axioms admits_iff_noRow
#print axioms canonical_admits_iff
#print axioms admits_iff_guard
#print axioms live_checks
#print axioms ret_live_checks
#print axioms native_solvable
#print axioms realized_iff
#print axioms realized_iff_noRow
#print axioms realized_iff_guard
#print axioms startWithPresented
#print axioms withRowPresented
#print axioms withRow_realized_iff
#print axioms shared_noRow
#print axioms shared_admitted
#print axioms shared_realized
#print axioms shared_information
#print axioms shared_guard
#print axioms shared_result
#print axioms sharedMember
#print axioms shared_run
#print axioms private_matching
#print axioms partial_matching
#print axioms private_no_firing
#print axioms partial_no_firing
#print axioms guard_fails_of_matching
#print axioms private_guard_fails
#print axioms partial_guard_fails
#print axioms pinnedPresented
#print axioms pinned_known
#print axioms pinAt_known
#print axioms pinned_beside
#print axioms pinned_quiet
#print axioms pinned_noRow
#print axioms pinned_admitted
#print axioms pinned_realized
#print axioms pinned_guard
#print axioms knowledge_decides
#print axioms twinPresented
#print axioms twin_beside_copy
#print axioms twin_noRow
#print axioms twin_admitted
#print axioms twin_realized
#print axioms quiet_needed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative.UnmatchedInstance
