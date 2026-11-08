import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# The frame-free half of the native diamond

Two native firings at one state are **apart** (`NativeFiring.Apart`) when their selections take no
common occurrence, produce no common port, and neither takes what the other reads, and when each is
**blind** to the other (`NativeFiring.Blind`): at every solution of its information, neither its
guards nor its predicate queries, read with its own rows and labels, see an occurrence the other
takes or makes.

The admission of a native firing is a condition on a world of present occurrences, read at the
firing's own frame, rows and labels (`NativeFiring.AdmitsOver`); at the state's present occurrences
it is admission (`realized_iff_admitsOver`).

* **The commits are independent** (`Apart.commits_independent`), in the exact sense of
  `OccurrenceCommits.Exactness`; so each stays enabled after the other and the two physical results
  agree (`Apart.commits_commute`).
* **Observations are stable** (`Apart.holdsAt_after`): guards (`guardHolds_fire`) and predicate
  queries keep their answers over the other's physical result, at every solution.
* **Recipes publish to distinct produced ports** (`Apart.recipes_apart`).
* **The frame-free half of the diamond** (`Apart.diamond_frame_free`): each firing satisfies its
  admission conditions over the other's physical result, and the two physical results agree.

What this does not state: admission of each firing **at the other's published result**, whose frame
the solver's return extends and whose rows the recipes publish, and a relation of the two composite
published states. That needs the firing read at the other's result (a residual) and a comparison of
solver returns. Here an occurrence the other firing makes is read with the state's row at its
identity, not with the row the other firing publishes there.

* **Pattern queries can be read at a later frame** (`matchingQuery_holds_carried`): the query of a
  carried pattern, over carried rows, holds at a candidate exactly when the query holds at the
  candidate read back (`pullCandidate`). A residual needs this of every query; a query given only by
  its region on the rows of its own frame has no such reading.

## Controls

* **Query interference breaks stability** (`NativeDiamondControls.interference_breaks`): an absence
  query of the occurrence `1` holds at `{0}` and fails after a commit makes `1`.
* **A port collision blocks both orders** (`NativeDiamondControls.collision_blocks`): two commits
  that make the same port clash, and neither is enabled after the other.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
  (Commit Enabled fire mem_fire regionOf regionOf_fire_of_no_write Independent Clash
    independent_iff_both_orders fire_comm clash_blocks_both_orders)
open ContextualPredicateQueryAdmission (nativeLabels)

/-! ## Guards over a changed world -/

section Guards

variable {S : Signature} {Local Shared Next O : Type} (locals : Local → MetaArity S)
  {captures : Shared → MetaArity S} {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

/-- **What a guard sees** at a solution: the occurrences whose rows match its pattern. An equality
guard sees nothing. -/
def GuardSees (candidate : Assignment captures next) (rows : O → ContextualConditionalRows.Row locals captures Γ sort) :
    Check (Term (signature S captures) Γ sort) → O → Prop
  | .equal _ _, _ => False
  | .absent pattern, o => ContextualConditionalRows.Matches locals captures candidate (instantiate candidate pattern) (rows o)
  | .count pattern _, o => ContextualConditionalRows.Matches locals captures candidate (instantiate candidate pattern) (rows o)

variable [DecidableEq O]

/-- **A guard keeps its answer over a commit that writes nothing it sees.** -/
theorem guardHolds_fire (candidate : Assignment captures next)
    (rows : O → ContextualConditionalRows.Row locals captures Γ sort) (world : Finset O) {R : Type*}
    (writer : Commit O R) (check : Check (Term (signature S captures) Γ sort))
    (blind : ∀ o ∈ writer.taken ∪ writer.made, ¬ GuardSees locals candidate rows check o) :
    ContextualConditionalGuards.Holds locals candidate rows (fire world writer) check ↔
      ContextualConditionalGuards.Holds locals candidate rows world check := by
  cases check with
  | equal _ _ => exact Iff.rfl
  | absent pattern =>
      constructor
      · intro after o present matched
        by_cases taken : o ∈ writer.taken
        · exact blind o (Finset.mem_union_left _ taken) matched
        · exact after o (mem_fire.mpr (Or.inl ⟨present, taken⟩)) matched
      · intro before o present matched
        rcases mem_fire.mp present with ⟨inWorld, _⟩ | made
        · exact before o inWorld matched
        · exact blind o (Finset.mem_union_right _ made) matched
  | count pattern cardinality =>
      have region : ContextualConditionalGuards.region locals candidate rows (fire world writer) pattern =
          ContextualConditionalGuards.region locals candidate rows world pattern := by
        ext o
        simp only [ContextualConditionalGuards.mem_region, mem_fire]
        constructor
        · rintro ⟨⟨inWorld, _⟩ | made, matched⟩
          · exact ⟨inWorld, matched⟩
          · exact absurd matched (blind o (Finset.mem_union_right _ made))
        · rintro ⟨inWorld, matched⟩
          exact ⟨Or.inl ⟨inWorld, fun taken => blind o (Finset.mem_union_left _ taken) matched⟩, matched⟩
      simp only [ContextualConditionalGuards.Holds, region]

end Guards

/-! ## Pattern queries can be read at a later frame -/

section PatternQueries

variable {S : Signature} {V W Local O : Type} {declaration : V → MetaArity S} {later : W → MetaArity S}
  (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}

/-- A candidate of a later frame, read back at an earlier frame along a morphism of frames. -/
def pullCandidate (change : Assignment declaration later)
    (candidate : ContextualPredicateQueryAdmission.Candidate later) :
    ContextualPredicateQueryAdmission.Candidate declaration :=
  ⟨candidate.Variables, candidate.declarations, Assignment.compose candidate.assignment change⟩

/-- **A pattern query is natural in the frame**: the query of the carried pattern, over rows carried
along a morphism of frames, holds at a candidate exactly when the query holds at the candidate read
back. -/
theorem matchingQuery_holds_carried (change : Assignment declaration later)
    (pattern : Term (signature S declaration) Γ sort) (seen : Finset O)
    (rows : O → ContextualConditionalRows.Row locals declaration Γ sort) (world : Finset O)
    (candidate : ContextualPredicateQueryAdmission.Candidate later) :
    ((ContextualPredicateQueryAdmission.matchingQuery locals (instantiate change pattern) seen).atSolution
        candidate).Holds (fun o => (o, (rows o).map locals declaration change)) world ↔
      ((ContextualPredicateQueryAdmission.matchingQuery locals pattern seen).atSolution
        (pullCandidate change candidate)).Holds (fun o => (o, rows o)) world := by
  rw [ContextualPredicateQueryAdmission.matching_holds_iff locals (instantiate change pattern) seen
      (fun o => (rows o).map locals declaration change),
    ContextualPredicateQueryAdmission.matching_holds_iff locals pattern seen rows,
    ContextualConditionalGuards.region_transport]
  rfl

end PatternQueries

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeFiring

variable {s : NativeState S O Γ sort}

/-- **The guards and predicate queries of a native firing at one solution**, read with the firing's
own rows and labels, over a world of present occurrences. -/
def HoldsAt (f : NativeFiring s) (b : Frames.Frame S) (σ : Assignment s.infoFrame.arity b.arity)
    (world : Finset O) : Prop :=
  (∀ check ∈ f.prepared.rule.checks,
      ContextualConditionalGuards.Holds s.locals σ
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) world check) ∧
    ∀ query ∈ f.queries, (query.atSolution ⟨b.Names, b.arity, σ⟩).Holds (nativeLabels s.locals s.state) world

/-- **The admission conditions of a native firing over a world**: its shapes, its selection enabled
in the world, its information solvable, and its guards and queries over the world at every
solution. -/
def AdmitsOver (f : NativeFiring s) (world : Finset O) : Prop :=
  (native (S := S) (O := O) (Γ := Γ) (sort := sort)).Shapes f ∧
    Enabled (fun _ : O => ()) world (f.selection.commit (T := Unit)) ∧
    (Frames.contextual S).Solvable (a := s.infoFrame) f.information ∧
    (Frames.contextual S).Entails (a := s.infoFrame) f.information (fun b σ => f.HoldsAt b σ world)

/-- At the state's present occurrences, the admission conditions are admission. -/
theorem realized_iff_admitsOver (f : NativeFiring s) : f.Realized ↔ f.AdmitsOver s.state.present :=
  native_admits_iff f

/-- **One firing is blind to another**: at every solution of its information, neither its guards nor
its predicate queries, read with its rows and labels, see an occurrence the other takes or makes. -/
def Blind (f g : NativeFiring s) : Prop :=
  ∀ (b : Frames.Frame S) (σ : Assignment s.infoFrame.arity b.arity),
    (Frames.contextual S).Models (a := s.infoFrame) (b := b) σ f.information →
      ∀ o, o ∈ g.selection.taken ∨ o ∈ g.selection.made →
        (∀ check ∈ f.prepared.rule.checks,
          ¬ GuardSees s.locals σ (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
            check o) ∧
          ∀ query ∈ f.queries, query.region ⟨b.Names, b.arity, σ⟩ (nativeLabels s.locals s.state o) = false

/-- **Two native firings apart at one state.** -/
structure Apart (f g : NativeFiring s) : Prop where
  takes : Disjoint f.selection.taken.toFinset g.selection.taken.toFinset
  ports : Disjoint f.selection.made.toFinset g.selection.made.toFinset
  keepsLeft : Disjoint g.selection.taken.toFinset f.selection.read.toFinset
  keepsRight : Disjoint f.selection.taken.toFinset g.selection.read.toFinset
  blindLeft : f.Blind g
  blindRight : g.Blind f

variable {f g : NativeFiring s}

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem Apart.symm (apart : f.Apart g) : g.Apart f :=
  ⟨apart.takes.symm, apart.ports.symm, apart.keepsRight, apart.keepsLeft, apart.blindRight, apart.blindLeft⟩

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **The commits of apart firings are independent.** -/
theorem Apart.commits_independent (apart : f.Apart g) :
    Independent (fun _ : O => ()) (f.selection.commit (T := Unit)) (g.selection.commit (T := Unit)) := by
  refine ⟨fun clash => clash.elim (fun common => common apart.takes) (fun common => common apart.ports), ?_, ?_⟩
  · rintro (common | ⟨read, member, _⟩)
    · exact common apart.keepsRight
    · simp [Selection.commit] at member
  · rintro (common | ⟨read, member, _⟩)
    · exact common apart.keepsLeft
    · simp [Selection.commit] at member

/-- **The commits of apart admitted firings commute**: each stays enabled after the other, and the
two physical results agree. -/
theorem Apart.commits_commute (apart : f.Apart g) (first : f.Realized) (second : g.Realized) :
    Enabled (fun _ : O => ()) (fire s.state.present (g.selection.commit (T := Unit))) (f.selection.commit (T := Unit)) ∧
      Enabled (fun _ : O => ()) (fire s.state.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit)) ∧
      fire (fire s.state.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit)) =
        fire (fire s.state.present (g.selection.commit (T := Unit))) (f.selection.commit (T := Unit)) := by
  have enabledF := ((native_admits_iff f).mp first).2.1
  have enabledG := ((native_admits_iff g).mp second).2.1
  obtain ⟨afterF, afterG⟩ := (independent_iff_both_orders enabledF enabledG).mp apart.commits_independent
  exact ⟨afterG, afterF, fire_comm enabledF enabledG⟩

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem writes_of_mem {g : NativeFiring s} {o : O}
    (member : o ∈ (g.selection.commit (T := Unit)).taken ∪ (g.selection.commit (T := Unit)).made) :
    o ∈ g.selection.taken ∨ o ∈ g.selection.made := by
  simpa [Selection.commit] using member

/-- **Observations are stable**: at every solution of its information, an admitted firing's guards
and predicate queries keep their answers over the physical result of a firing it is blind to. -/
theorem Apart.holdsAt_after (apart : f.Apart g) (first : f.Realized) :
    (Frames.contextual S).Entails (a := s.infoFrame) f.information
      (fun b σ => f.HoldsAt b σ (fire s.state.present (g.selection.commit (T := Unit)))) := by
  intro b σ solved
  have holds : f.HoldsAt b σ s.state.present := ((native_admits_iff f).mp first).2.2.2 b σ solved
  have blind := apart.blindLeft b σ solved
  refine ⟨fun check member => ?_, fun query member => ?_⟩
  · exact (guardHolds_fire s.locals σ _ s.state.present _ check
      fun o written => (blind o (writes_of_mem written)).1 check member).mpr (holds.1 check member)
  · have unchanged : regionOf (nativeLabels s.locals s.state) (fire s.state.present (g.selection.commit (T := Unit)))
        (query.region ⟨b.Names, b.arity, σ⟩) =
        regionOf (nativeLabels s.locals s.state) s.state.present (query.region ⟨b.Names, b.arity, σ⟩) :=
      regionOf_fire_of_no_write (c := g.selection.commit)
        fun o written => (blind o (writes_of_mem written)).2 query member
    exact unchanged.trans (holds.2 query member)

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Apart firings publish through distinct produced ports.** -/
theorem Apart.recipes_apart (apart : f.Apart g) (o : O) (published : f.recipes o ≠ none) :
    g.recipes o = none := by
  have made : o ∈ f.selection.made := by
    by_contra notMade
    exact published (f.recipes_made o notMade)
  refine g.recipes_made o fun madeG => ?_
  exact Finset.disjoint_left.mp apart.ports (List.mem_toFinset.mpr made) (List.mem_toFinset.mpr madeG)

/-- **The frame-free half of the native diamond**: each of two apart admitted firings satisfies its
admission conditions over the other's physical result, read at its own frame, rows and labels, and
the two physical results agree. -/
theorem Apart.diamond_frame_free (apart : f.Apart g) (first : f.Realized) (second : g.Realized) :
    f.AdmitsOver (fire s.state.present (g.selection.commit (T := Unit))) ∧
      g.AdmitsOver (fire s.state.present (f.selection.commit (T := Unit))) ∧
      fire (fire s.state.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit)) =
        fire (fire s.state.present (g.selection.commit (T := Unit))) (f.selection.commit (T := Unit)) := by
  obtain ⟨afterG, afterF, comm⟩ := apart.commits_commute first second
  have admittedF := (native_admits_iff f).mp first
  have admittedG := (native_admits_iff g).mp second
  exact ⟨⟨admittedF.1, afterG, admittedF.2.2.1, apart.holdsAt_after first⟩,
    ⟨admittedG.1, afterF, admittedG.2.2.1, apart.symm.holdsAt_after second⟩, comm⟩

end NativeFiring

/-! ## Controls -/

namespace NativeDiamondControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (PredicateQuery)

/-- An absence query of the occurrence `1`, over native-style labels carrying identities. -/
def noOne : PredicateQuery ℕ (ℕ × Unit) := ⟨fun label => decide (label.1 = 1), ∅⟩

/-- A commit that makes the occurrence `1`. -/
def makesOne : Commit ℕ Unit := ⟨∅, ∅, {1}, []⟩

/-- **Query interference breaks stability**: the absence query holds at `{0}` and fails after a
commit makes `1` inside its region. -/
theorem interference_breaks :
    noOne.Holds (fun o => (o, ())) {0} ∧ ¬ noOne.Holds (fun o => (o, ())) (fire {0} makesOne) := by
  decide

/-- **A port collision blocks both orders**: two commits that make the same port clash, and neither
is enabled after the other. -/
theorem collision_blocks :
    Clash makesOne makesOne ∧ Enabled (fun _ : ℕ => ()) {0} makesOne ∧
      ¬ Enabled (fun _ : ℕ => ()) (fire {0} makesOne) makesOne :=
  ⟨Or.inr (by decide), by decide, by decide⟩

end NativeDiamondControls

#print axioms guardHolds_fire
#print axioms matchingQuery_holds_carried
#print axioms NativeFiring.realized_iff_admitsOver
#print axioms NativeFiring.Apart.commits_independent
#print axioms NativeFiring.Apart.commits_commute
#print axioms NativeFiring.Apart.holdsAt_after
#print axioms NativeFiring.Apart.recipes_apart
#print axioms NativeFiring.Apart.diamond_frame_free
#print axioms NativeDiamondControls.interference_breaks
#print axioms NativeDiamondControls.collision_blocks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
