import Mettapedia.Machines.OrderedGuardPipeline
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Ordered member-pattern queries

A member query visits a finite list in order. Each local match supplies an
ordered list of compatible binding refinements, and only those refinements
activate the held result computation. The source plan below creates a separate
choice for each member; the composed plan combines the pure match providers
before entering the same result computation. Their equivalence is proved for
arbitrary success, failure and delimited-commit continuations, including effects.

The concrete pattern instance uses the existing MeTTaIL matcher and consistent
binding merge. This is constructor-pattern matching, not an adequacy proof of
bidirectional or open-atom unification in HE or PeTTa. Matching and
the optional multi-answer acquisition are finite and pure here; the single
effectful acquisition is a total action returning one list and its local frame.
The member list is already acquired: neither ordinary argument evaluation nor
evaluation-based enumeration is silently identified with raw data traversal.
The held result is an opaque `Body` interpreted only after a successful local
match; mapping a dialect's result template to that body requires its own
argument-demand and current-space activation theorem.
Suspension, acquisition faults, effectful multi-answer acquisition, surface
argument demand and adequacy of native implementations are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedPatternQuery

open ScopedCommit OrderedGuardPipeline

variable {Element Local World Result : Type}

/-- A pure local matcher returns occurrences of refined local states, not a
set of states or a Boolean decision. -/
abbrev Matcher (Element Local : Type) := Element → Local → List Local

def memberAnswers (matcher : Matcher Element Local)
    (subjects : List Element) (seed : Local) : List Local :=
  subjects.flatMap (fun subject => matcher subject seed)

/-- The element-by-element source construction. Every member starts from the
same caller frame; bindings from one member do not leak into another. -/
def sourceBody (matcher : Matcher Element Local) :
    List Element → Body Local World → Body Local World
  | [], _ => .fail
  | subject :: subjects, heldResult =>
      .choice (.choose (fun seed _ => matcher subject seed) heldResult)
        (sourceBody matcher subjects heldResult)

/-- The composed executor snapshots the complete ordered pure match results.
It leaves result activation and all effects to the original continuation. -/
def compiledBody (matcher : Matcher Element Local) (subjects : List Element)
    (heldResult : Body Local World) : Body Local World :=
  guard (memberAnswers matcher subjects) heldResult

theorem memberAnswers_append (matcher : Matcher Element Local)
    (first later : List Element) (seed : Local) :
    memberAnswers matcher (first ++ later) seed =
      memberAnswers matcher first seed ++ memberAnswers matcher later seed := by
  simp [memberAnswers]

/-- Duplicating a member duplicates its entire ordered local-match result.
This holds even when both copies contain identical bindings. -/
theorem memberAnswers_duplicate (matcher : Matcher Element Local)
    (subject : Element) (seed : Local) :
    memberAnswers matcher [subject, subject] seed =
      matcher subject seed ++ matcher subject seed := by
  simp [memberAnswers]

theorem memberAnswers_length (matcher : Matcher Element Local)
    (subjects : List Element) (seed : Local) :
    (memberAnswers matcher subjects seed).length =
      (subjects.map (fun subject => (matcher subject seed).length)).sum := by
  simp [memberAnswers, List.length_flatMap]

/-- A structural compiler-correctness theorem. The two plans are independently
constructed, and the proof does not assume their answers equal. -/
theorem source_compiled (matcher : Matcher Element Local)
    (subjects : List Element) (heldResult : Body Local World) (seed : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (sourceBody matcher subjects heldResult) seed success failure saved world =
      eval (compiledBody matcher subjects heldResult) seed success failure saved world := by
  induction subjects generalizing seed success failure saved world with
  | nil => rfl
  | cons subject subjects ih =>
      simp only [sourceBody, eval]
      rw [show (fun world =>
        eval (sourceBody matcher subjects heldResult) seed success failure saved world) =
          (fun world =>
        eval (compiledBody matcher subjects heldResult) seed success failure saved world) by
        funext world
        exact ih seed success failure saved world]
      simp only [compiledBody, OrderedGuardPipeline.guard, eval, memberAnswers,
        List.flatMap_cons, List.foldr_append]

theorem source_readout (matcher : Matcher Element Local)
    (subjects : List Element) (seed : Local) (world : World) :
    run (sourceBody matcher subjects .done) seed world =
      (memberAnswers matcher subjects seed, world) := by
  unfold run
  rw [source_compiled]
  exact guard_readout (memberAnswers matcher subjects) seed world

/-- Empty subjects do not activate even an effectful held result computation. -/
theorem empty_does_not_activate (matcher : Matcher Element Local)
    (heldResult : Body Local World) (seed : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (sourceBody matcher [] heldResult) seed success failure saved world =
      failure world := rfl

theorem all_mismatch_answers (matcher : Matcher Element Local)
    (subjects : List Element) (seed : Local)
    (mismatch : ∀ subject ∈ subjects, matcher subject seed = []) :
    memberAnswers matcher subjects seed = [] := by
  induction subjects with
  | nil => rfl
  | cons subject subjects ih =>
      simp only [memberAnswers, List.flatMap_cons]
      rw [mismatch subject (List.mem_cons_self)]
      exact ih (fun item inside => mismatch item (List.mem_cons_of_mem subject inside))

/-- A nonempty collection with no compatible matches is also effect-free at
the result boundary. Acquisition effects, if any, are not undone. -/
theorem all_mismatch_does_not_activate (matcher : Matcher Element Local)
    (subjects : List Element) (heldResult : Body Local World) (seed : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World)
    (mismatch : ∀ subject ∈ subjects, matcher subject seed = []) :
    eval (sourceBody matcher subjects heldResult) seed success failure saved world =
      failure world := by
  rw [source_compiled]
  simp only [compiledBody, OrderedGuardPipeline.guard, eval,
    all_mismatch_answers matcher subjects seed mismatch]
  rfl

/-- A single subject acquisition may perform effects and refine the caller's
bindings. This interface returns one list, not a nondeterministic query stream. -/
abbrev Acquisition (Element Local World : Type) :=
  Local → World → (List Element × Local) × World

def sourceQuery (acquire : Acquisition Element Local World)
    (matcher : Matcher Element Local) (heldResult : Body Local World) (seed : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) : Result :=
  let acquired := acquire seed world
  eval (sourceBody matcher acquired.1.1 heldResult) acquired.1.2
    success failure saved acquired.2

def compiledQuery (acquire : Acquisition Element Local World)
    (matcher : Matcher Element Local) (heldResult : Body Local World) (seed : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) : Result :=
  let acquired := acquire seed world
  eval (compiledBody matcher acquired.1.1 heldResult) acquired.1.2
    success failure saved acquired.2

theorem query_compilation (acquire : Acquisition Element Local World)
    (matcher : Matcher Element Local) (heldResult : Body Local World) (seed : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    sourceQuery acquire matcher heldResult seed success failure saved world =
      compiledQuery acquire matcher heldResult seed success failure saved world := by
  exact source_compiled matcher (acquire seed world).1.1 heldResult
    (acquire seed world).1.2 success failure saved (acquire seed world).2

theorem acquired_readout (acquire : Acquisition Element Local World)
    (matcher : Matcher Element Local) (seed : Local) (world : World) :
    sourceQuery acquire matcher .done seed collect finish finish world =
      (memberAnswers matcher (acquire seed world).1.1 (acquire seed world).1.2,
        (acquire seed world).2) := by
  exact source_readout matcher (acquire seed world).1.1 (acquire seed world).1.2
    (acquire seed world).2

/-- Multiple acquired lists retain their individual local frames. They are a
complete finite pure acquisition result; no effectful stream is collapsed. -/
def acquiredAnswers (matcher : Matcher Element Local)
    (acquired : List (List Element × Local)) : List Local :=
  acquired.flatMap (fun outcome => memberAnswers matcher outcome.1 outcome.2)

/-- The source consumes each acquired list before proceeding to the next one. -/
def sourceAcquired (matcher : Matcher Element Local) (heldResult : Body Local World) :
    List (List Element × Local) → Success Local World Result →
      Failure World Result → Failure World Result → World → Result
  | [], _, failure, _, world => failure world
  | outcome :: outcomes, success, failure, saved, world =>
      eval (sourceBody matcher outcome.1 heldResult) outcome.2 success
        (fun world => sourceAcquired matcher heldResult outcomes success failure saved world)
        saved world

/-- Ordered pure multi-answer acquisition composes with member matching.
Result effects still happen between successful occurrences in source order. -/
theorem pure_acquisition_compilation (matcher : Matcher Element Local)
    (heldResult : Body Local World) (acquired : List (List Element × Local))
    (seed : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    sourceAcquired matcher heldResult acquired success failure saved world =
      eval (guard (fun _ => acquiredAnswers matcher acquired) heldResult)
        seed success failure saved world := by
  induction acquired generalizing seed success failure saved world with
  | nil => rfl
  | cons outcome outcomes ih =>
      simp only [sourceAcquired]
      rw [source_compiled]
      rw [show (fun world =>
        sourceAcquired matcher heldResult outcomes success failure saved world) =
          (fun world => eval (guard (fun _ => acquiredAnswers matcher outcomes) heldResult)
            seed success failure saved world) by
        funext world
        exact ih seed success failure saved world]
      simp only [compiledBody, OrderedGuardPipeline.guard, eval, acquiredAnswers,
        List.flatMap_cons, List.foldr_append]

/-- An effect counter records exactly one activation per successful binding
occurrence, not one activation per distinct value. -/
def touchingResult : Body Local Nat :=
  .effect (fun state world => (state, world + 1)) .done

theorem activation_count (matcher : Matcher Element Local)
    (subjects : List Element) (seed : Local) (world : Nat) :
    run (sourceBody matcher subjects touchingResult) seed world =
      (memberAnswers matcher subjects seed,
        world + (memberAnswers matcher subjects seed).length) := by
  have folded : ∀ (states : List Local) (world : Nat),
      (states.foldr (fun state rest => fun world => collect state rest (world + 1))
        finish) world = (states, world + states.length) := by
    intro states
    induction states with
    | nil => intro world; rfl
    | cons state states ih =>
        intro world
        simp only [List.foldr_cons]
        change (state :: ((states.foldr (fun state rest => fun world =>
            collect state rest (world + 1)) finish) (world + 1)).1,
          ((states.foldr (fun state rest => fun world =>
            collect state rest (world + 1)) finish) (world + 1)).2) =
          (state :: states, world + (state :: states).length)
        rw [ih (world + 1)]
        simp only [List.length_cons]
        congr 1
        omega
  unfold run
  rw [source_compiled]
  exact folded (memberAnswers matcher subjects seed) world

/-! ## An instance with actual structural matching and consistent bindings -/

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
  Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- Match locally, then merge with the caller frame. Conflicting existing
bindings reject an occurrence instead of being silently overwritten. -/
def patternMatcher (pattern : Pattern) : Matcher Pattern Bindings :=
  fun value seed => (matchPattern pattern value).filterMap (mergeBindings seed)

theorem patternMatcher_witness {pattern value : Pattern} {seed refined : Bindings} :
    refined ∈ patternMatcher pattern value seed ↔
      ∃ captured, MatchRel pattern value captured ∧
        mergeBindings seed captured = some refined := by
  simp only [patternMatcher, List.mem_filterMap, matchPattern_iff_matchRel]

theorem patternMatcher_preserves_existing {pattern value : Pattern}
    {seed refined : Bindings} (matched : refined ∈ patternMatcher pattern value seed) :
    BindingsExtends seed refined := by
  obtain ⟨captured, _, merged⟩ := patternMatcher_witness.mp matched
  intro name value found
  exact mergeBindings_subsumed_left merged found

/-- Binder-free constructor patterns are reconstructed using the successful
caller refinement, not only the isolated bindings returned by the matcher. -/
theorem patternMatcher_reconstructs {pattern value : Pattern} {seed refined : Bindings}
    (matched : refined ∈ patternMatcher pattern value seed)
    (supported : Pattern.isMatchCorrect pattern = true) :
    applyBindings refined pattern = value := by
  obtain ⟨captured, relation, merged⟩ := patternMatcher_witness.mp matched
  apply matchRel_correct_of_extends relation supported
  intro name value found
  exact mergeBindings_subsumed_right merged found

/-- The member query is sound and complete against the independently inductive
structural-match relation together with consistent ambient binding merge. -/
theorem pattern_members_witness {pattern : Pattern} {subjects : List Pattern}
    {seed refined : Bindings} :
    refined ∈ memberAnswers (patternMatcher pattern) subjects seed ↔
      ∃ value ∈ subjects, ∃ captured, MatchRel pattern value captured ∧
        mergeBindings seed captured = some refined := by
  simp only [memberAnswers, List.mem_flatMap, patternMatcher_witness]

theorem pattern_members_preserve_existing {pattern : Pattern} {subjects : List Pattern}
    {seed refined : Bindings}
    (matched : refined ∈ memberAnswers (patternMatcher pattern) subjects seed) :
    BindingsExtends seed refined := by
  obtain ⟨value, _, captured, _, merged⟩ := pattern_members_witness.mp matched
  intro name bound found
  exact mergeBindings_subsumed_left merged found

theorem pattern_members_reconstruct {pattern : Pattern} {subjects : List Pattern}
    {seed refined : Bindings}
    (matched : refined ∈ memberAnswers (patternMatcher pattern) subjects seed)
    (supported : Pattern.isMatchCorrect pattern = true) :
    ∃ value ∈ subjects, applyBindings refined pattern = value := by
  obtain ⟨value, inside, captured, relation, merged⟩ := pattern_members_witness.mp matched
  refine ⟨value, inside, matchRel_correct_of_extends relation supported ?_⟩
  intro name bound found
  exact mergeBindings_subsumed_right merged found

namespace Controls

def selectEven : Matcher Nat Nat := fun member _ =>
  if member % 2 = 0 then [member] else []

theorem source_order_and_duplicates :
    run (sourceBody selectEven [4, 1, 2, 4] touchingResult) 0 0 = ([4, 2, 4], 3) := rfl

theorem every_success_gets_its_own_result_effect :
    run (compiledBody selectEven [4, 4] touchingResult) 0 0 = ([4, 4], 2) := rfl

theorem mismatch_and_empty_have_no_result_effect :
    run (sourceBody selectEven [1, 3] touchingResult) 0 0 = ([], 0) ∧
      run (sourceBody selectEven [] touchingResult) 0 0 = ([], 0) := ⟨rfl, rfl⟩

def acquireTwiceListed : Acquisition Nat Nat Nat :=
  fun seed world => (([4, 4], seed), world + 1)

/-- One acquisition effect, followed by one result effect for each occurrence. -/
theorem subject_acquired_once_not_per_member :
    sourceQuery acquireTwiceListed selectEven touchingResult 0 collect finish finish 0 =
      ([4, 4], 3) := rfl

theorem acquired_empty_list_keeps_only_acquisition_effect :
    sourceQuery (fun seed world => (([], seed), world + 1)) selectEven touchingResult
      0 collect finish finish 0 = ([], 1) := rfl

theorem multiple_acquired_lists_keep_order_and_local_frames :
    sourceAcquired (fun member seed => [member + seed]) touchingResult
      [([1, 1], 10), ([2], 20)] collect finish finish 0 = ([11, 11, 22], 3) := rfl

theorem eager_result_activation_changes_the_empty_query :
    run (sourceBody selectEven [] touchingResult) 0 0 ≠
      run (.effect (fun state world => (state, world + 1))
        (sourceBody selectEven [] touchingResult)) 0 0 := by decide

theorem removing_duplicate_members_changes_results_and_effects :
    run (sourceBody selectEven [4, 4] touchingResult) 0 0 ≠
      run (sourceBody selectEven [4] touchingResult) 0 0 := by decide

theorem incompatible_existing_binding_rejects :
    patternMatcher (.fvar "x") (.bvar 1) [("x", .bvar 0)] = [] := by
  simp only [patternMatcher, matchPattern]
  decide

theorem compatible_existing_binding_retained :
    patternMatcher (.fvar "x") (.bvar 0) [("x", .bvar 0)] =
      [[("x", .bvar 0)]] := by
  simp only [patternMatcher, matchPattern]
  decide

theorem refined_binding_activates_result :
    run (sourceBody (patternMatcher (.fvar "x")) [.bvar 2] touchingResult)
      [] 0 = ([[ ("x", .bvar 2) ]], 1) := by
  rw [activation_count]
  simp only [memberAnswers, List.flatMap_cons, List.flatMap_nil, patternMatcher, matchPattern]
  decide

theorem incompatible_binding_never_activates_result :
    run (sourceBody (patternMatcher (.fvar "x")) [.bvar 1] touchingResult)
      [("x", .bvar 0)] 0 = ([], 0) := by
  rw [activation_count]
  simp only [memberAnswers, List.flatMap_cons, List.flatMap_nil, patternMatcher, matchPattern]
  decide

end Controls

end Mettapedia.Machines.OrderedPatternQuery
