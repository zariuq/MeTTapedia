import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readback

/-!
# The discipline of a neighbour's rules: both directions, and asked along a run

`Composition.Disciplined` is a condition for **one direction**. Of a row that a neighbour's firing makes
it asks only that the row never reads as an alternative's row; that keeps every run of the union a
source run (`runs_reflected_neighbour`). It does not keep the moves of the hosted program: a rule that
makes an equation row meets it, and the unmatched call that the row matches has no firing afterwards
(`Composition.NeighbourControls.switched_off`). And it is asked at **every** state that represents an
alternative beside rows that never read as alternatives' rows, among them states that no run from the
start of a query reaches (`Composition.Readers.Flex.readEqn_not_disciplined`).

**The clauses, at one state.**

* `DisciplinedAt N P R w`: the clause of `Disciplined` for the firings of `R` at `w`
  (`disciplined_iff`: `Disciplined` is this clause at every state).
* `BothWaysAt N P R w`: the clause for both directions. Where `w` represents an alternative beside rows
  that never read as alternatives' rows **or as equation rows**, each admitted firing of `R` at `w` is
  apart from the hosted rows, and the rows it makes never read as alternatives' rows or as equation
  rows. It is asked where the invariant of both directions holds and gives that invariant back.

**Where the clauses are asked.**

* At every state: `Disciplined`, and `DisciplinedBothWays N P R` for both directions. A disciplined
  neighbour whose made rows never read as equation rows is disciplined for both directions
  (`bothWays_of_disciplined`).
* Along a run: `DisciplinedAlong N P R w₀` and `BothWaysAlong N P R w₀` ask the clause at the states
  that runs of the union of the translated program with `R` reach from `w₀`. The every-state
  conditions imply them from every start (`along_of_disciplined`, `DisciplinedBothWays.along`), and
  they are strictly weaker (`Composition.ReadersAlong.readEqn_strictly_weaker`).

**The theorems**, for a program and a query under the clauses of the run theorems, from a start that
represents the query's alternative beside other rows.

* `runs_reflected_along`: under `DisciplinedAlong`, from rows that never read as alternatives' rows,
  **every run of the union is a source run with the neighbour's firings silent**.
  `alongReadback`: the same as a readback (`GSLT.IndexedOperational.OperationalReadback`).
* `runs_both_ways_along`: under `BothWaysAlong`, from rows that never read as alternatives' rows or as
  equation rows, every state a run of the union reaches represents an alternative of a reached
  configuration beside rows of which the same holds. `forward_along`: **and at that state every move of
  the represented alternative to a live alternative is one firing of the translated program.**
  `alongCorrespondence`: alternative by alternative, the union is an operational correspondence
  (`GSLT.IndexedOperational.OperationalCorrespondence`) with the neighbour's firings silent;
  `start_representsAlong`: the start is related to the query's alternative.
* `runs_neighbour_both_ways`, `forward_after_neighbour`: the same under the every-state condition
  `DisciplinedBothWays`.
* `disciplinedAlong_of_bothWays`: from such a start the condition for both directions along the runs
  gives the condition of the reflected direction along the runs. A state with solvable knowledge
  represents an alternative beside quiet rows in one way only (`beside_unique`).
* `answers_along`: under `DisciplinedAlong`, the answers the union shows from the start
  (`unionAnswersFrom`) are, as a set, the source's. The inclusion of the source's answers uses the runs
  of the translated program before the neighbour moves; after a neighbour that meets only the reflected
  condition has moved, they may be lost (`Composition.NeighbourControls.never_answers`).

What neither condition gives: the bag of answers, which the step does not determine even with no
neighbour (`Answers.SameStart.bags_differ`); and termination: beside a neighbour that fires for ever,
every union diverges (`Divergence.BesideNeighbours.union_diverges`). What is kept of divergence is
counted by the firings of the translated program (`Divergence.BesideNeighbours.arrow_diverges_iff_beside`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.GSLT.IndexedOperational (OperationalReadback OperationalCorrespondence)
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-! ## The clauses, and where they are asked -/

section Conditions

variable {D : Discipline S Γ star}

/-- **The discipline at one state**: where the state represents an alternative beside rows that never
read as alternatives' rows, each admitted firing of the neighbour's rules is apart from the hosted rows
and makes no row that reads as an alternative's row. -/
def DisciplinedAt (P : SourceLanguage.Program κ Γ star D.Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (w : HostState S) : Prop :=
  ∀ {n : ℕ} {b : Branch κ Γ star D.Ty} {a : ℕ} {others : Finset ℕ}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) R w.frame),
    Beside N P n b w a others → NeverReads (IsAlternative N) w others →
      f.Admits (Interface.Frames.contextual S) w →
        Apart P a w f ∧
          NeverReads (IsAlternative N) (f.result (Interface.Frames.contextual S) w) f.selection.made.toFinset

/-- **The discipline for both directions at one state**: where the state represents an alternative
beside rows that never read as alternatives' rows or as equation rows, each admitted firing of the
neighbour's rules is apart from the hosted rows, and the rows it makes never read as alternatives' rows
or as equation rows. -/
def BothWaysAt (P : SourceLanguage.Program κ Γ star D.Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (w : HostState S) : Prop :=
  ∀ {n : ℕ} {b : Branch κ Γ star D.Ty} {a : ℕ} {others : Finset ℕ}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) R w.frame),
    Beside N P n b w a others → NeverReads (IsAlternative N) w others →
      NeverReads (IsEquationRow N) w others → f.Admits (Interface.Frames.contextual S) w →
        Apart P a w f ∧
          NeverReads (IsAlternative N) (f.result (Interface.Frames.contextual S) w) f.selection.made.toFinset ∧
          NeverReads (IsEquationRow N) (f.result (Interface.Frames.contextual S) w) f.selection.made.toFinset

/-- **The discipline of a neighbour's rules for both directions**, at every state. -/
def DisciplinedBothWays (P : SourceLanguage.Program κ Γ star D.Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) : Prop :=
  ∀ w : HostState S, BothWaysAt N P R w

/-- **The discipline asked along a run**: at every state that a run of the union of the translated
program with the neighbour's rules reaches from `w₀`. -/
def DisciplinedAlong (P : SourceLanguage.Program κ Γ star D.Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (w₀ : HostState S) : Prop :=
  ∀ w : HostState S, Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w → DisciplinedAt N P R w

/-- **The discipline for both directions asked along a run**: at every state that a run of the union
reaches from `w₀`. -/
def BothWaysAlong (P : SourceLanguage.Program κ Γ star D.Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (w₀ : HostState S) : Prop :=
  ∀ w : HostState S, Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w → BothWaysAt N P R w

variable {P : SourceLanguage.Program κ Γ star D.Ty} {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}

/-- **`Disciplined` is its clause at every state.** -/
theorem disciplined_iff : Disciplined N P R ↔ ∀ w : HostState S, DisciplinedAt N P R w := by
  constructor
  · intro d w n b a others f beside quiet admitted
    exact d f beside quiet admitted
  · intro d n b w a others f beside quiet admitted
    exact d w f beside quiet admitted

/-- The every-state condition implies the condition along the runs from every start. -/
theorem along_of_disciplined (d : Disciplined N P R) (w₀ : HostState S) : DisciplinedAlong N P R w₀ := by
  intro w _ n b a others f beside quiet admitted
  exact d f beside quiet admitted

/-- The every-state condition for both directions implies the one along the runs from every start. -/
theorem DisciplinedBothWays.along (both : DisciplinedBothWays N P R) (w₀ : HostState S) :
    BothWaysAlong N P R w₀ :=
  fun w _ => both w

/-- **A disciplined neighbour whose made rows never read as equation rows is disciplined for both
directions.** -/
theorem bothWays_of_disciplined (d : Disciplined N P R)
    (made : ∀ {n : ℕ} {b : Branch κ Γ star D.Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
      (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) R w.frame),
      Beside N P n b w a others → NeverReads (IsAlternative N) w others →
        f.Admits (Interface.Frames.contextual S) w →
          NeverReads (IsEquationRow N) (f.result (Interface.Frames.contextual S) w)
            f.selection.made.toFinset) :
    DisciplinedBothWays N P R := by
  intro w n b a others f beside quietAlt _ admitted
  exact ⟨(d f beside quietAlt admitted).1, (d f beside quietAlt admitted).2, made f beside quietAlt admitted⟩

end Conditions

/-! ## A state represents an alternative beside quiet rows in one way -/

section Unique

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **The alternative's row and the other rows are determined by the state**, when its knowledge has a
solution: the alternative's row reads as an alternative's row, the equation rows are numbered below it,
and the other rows never read as alternatives' rows. -/
theorem beside_unique {n n' : ℕ} {b b' : Branch κ Γ star Ty} {w : HostState S} {a a' : ℕ}
    {others others' : Finset ℕ} (beside : Beside N P n b w a others)
    (beside' : Beside N P n' b' w a' others') (quiet' : NeverReads (IsAlternative N) w others')
    (solvable : (Interface.Frames.contextual S).Solvable w.knowledge) : a = a' ∧ others = others' := by
  obtain ⟨B, σ, known⟩ := solvable
  obtain ⟨σ', _, read⟩ := (beside.hosted.reads B _).mp ⟨σ, known, rfl⟩
  have aPresent : a ∈ hostedRows P a' ∪ others' := by
    rw [← beside'.present]
    exact beside.row_present N
  have same : a = a' := by
    rcases Finset.mem_union.mp aPresent with hosted | other
    · rcases Finset.mem_insert.mp hosted with same | small
      · exact same
      · exact absurd (Finset.mem_range.mp small) (not_lt.mpr beside.hosted.notRow)
    · exact absurd ⟨_, _, read.symm⟩ (quiet' a other B σ known)
  subst same
  refine ⟨rfl, ?_⟩
  ext o
  constructor
  · intro inO
    have present : o ∈ hostedRows P a ∪ others' := by
      rw [← beside'.present, beside.present]
      exact Finset.mem_union_right _ inO
    rcases Finset.mem_union.mp present with hosted | other
    · exact absurd inO (Finset.disjoint_left.mp beside.apart hosted)
    · exact other
  · intro inO
    have present : o ∈ hostedRows P a ∪ others := by
      rw [← beside.present, beside'.present]
      exact Finset.mem_union_right _ inO
    rcases Finset.mem_union.mp present with hosted | other
    · exact absurd inO (Finset.disjoint_left.mp beside'.apart hosted)
    · exact other

end Unique

/-! ## Runs of the union -/

section Runs

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **Every run of the union with a neighbour disciplined along the runs is a source run with silent
steps**: it reaches a state that represents, beside rows that never read as alternatives' rows, an
alternative of a configuration a source run reaches. -/
theorem runs_reflected_along
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ} (along : DisciplinedAlong N P R w₀)
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quiet : NeverReads (IsAlternative N) w₀ others₀) {w : HostState S}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ) (others : Finset ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Beside N P C.world.scope b w a others ∧ NeverReads (IsAlternative N) w others ∧ ArrowBranch b := by
  induction run with
  | refl =>
      exact ⟨_, initialBranch q, a₀, others₀, .refl, Multiset.mem_singleton_self _, start, quiet, trivial,
        .inl ⟨q, rfl, arrowQ⟩⟩
  | tail before fires ih =>
      obtain ⟨C, b, a, others, runs, member, beside, quiet', arrow⟩ := ih
      rcases (firesIn_union _ _ _ _).mp fires with hosted | ⟨f, admitted, rfl⟩
      · have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
        obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
          reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside quiet' arrow
            hygienic hosted
        obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
        refine ⟨⟨v', bs + rest⟩, b', a', others, runs.tail ?_, Multiset.mem_add.mpr (.inl child), beside',
          kept _ quiet', arrow'⟩
        obtain ⟨world, branches⟩ := C
        simp only at split
        subst split
        exact .move world v' b rest bs (live_beside N beside hosted) move
      · obtain ⟨apart, made⟩ := along _ before f beside quiet' admitted
        exact ⟨C, b, a, _, runs, member, beside_after_other N beside admitted apart,
          neverReads_fire admitted (others_sub N beside) quiet' made, arrow⟩

/-- **Every run of the union with a neighbour disciplined for both directions along the runs reaches a
state that represents an alternative of a reached configuration beside rows that never read as
alternatives' rows or as equation rows.** -/
theorem runs_both_ways_along
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ} (along : BothWaysAlong N P R w₀)
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quietAlt : NeverReads (IsAlternative N) w₀ others₀)
    (quietEqn : NeverReads (IsEquationRow N) w₀ others₀) {w : HostState S}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ) (others : Finset ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Beside N P C.world.scope b w a others ∧ NeverReads (IsAlternative N) w others ∧
        NeverReads (IsEquationRow N) w others ∧ ArrowBranch b := by
  induction run with
  | refl =>
      exact ⟨_, initialBranch q, a₀, others₀, .refl, Multiset.mem_singleton_self _, start, quietAlt, quietEqn,
        trivial, .inl ⟨q, rfl, arrowQ⟩⟩
  | tail before fires ih =>
      obtain ⟨C, b, a, others, runs, member, beside, quietAlt', quietEqn', arrow⟩ := ih
      rcases (firesIn_union _ _ _ _).mp fires with hosted | ⟨f, admitted, rfl⟩
      · have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
        obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
          reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside quietAlt'
            arrow hygienic hosted
        obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
        refine ⟨⟨v', bs + rest⟩, b', a', others, runs.tail ?_, Multiset.mem_add.mpr (.inl child), beside',
          kept _ quietAlt', kept _ quietEqn', arrow'⟩
        obtain ⟨world, branches⟩ := C
        simp only at split
        subst split
        exact .move world v' b rest bs (live_beside N beside hosted) move
      · obtain ⟨apart, madeAlt, madeEqn⟩ := along _ before f beside quietAlt' quietEqn' admitted
        exact ⟨C, b, a, _, runs, member, beside_after_other N beside admitted apart,
          neverReads_fire admitted (others_sub N beside) quietAlt' madeAlt,
          neverReads_fire admitted (others_sub N beside) quietEqn' madeEqn, arrow⟩

/-- **The forward direction after the neighbour has moved**: at every state a run of the union
reaches, every move of the represented alternative to a live alternative is one firing of the
translated program, to a state that represents that alternative beside the same rows. -/
theorem forward_along
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ} (along : BothWaysAlong N P R w₀)
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quietAlt : NeverReads (IsAlternative N) w₀ others₀)
    (quietEqn : NeverReads (IsEquationRow N) w₀ others₀) {w : HostState S}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ) (others : Finset ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Beside N P C.world.scope b w a others ∧
        ∀ {v' : World κ Γ star} {bs : Multiset (Branch κ Γ star D.Ty)}, Move D P supply C.world b v' bs →
          ∀ {b' : Branch κ Γ star D.Ty}, b' ∈ bs → Solvable b'.store →
            ∃ w' a', Fires N P w w' ∧ Beside N P v'.scope b' w' a' others := by
  obtain ⟨C, b, a, others, runs, member, beside, _, quietEqn', arrow⟩ :=
    runs_both_ways_along N (supply := supply) spaces q equations qScoped qDistinct arrowQ along start
      quietAlt quietEqn run
  have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
  refine ⟨C, b, a, others, runs, member, beside, ?_⟩
  intro v' bs move b' child live
  obtain ⟨w', a', fired, beside', _, _⟩ :=
    simulation_beside N (fun e inside => (equations e inside).2.2) move beside arrow hygienic
      (fun _ _ _ => noMatchingRow_of_neverReads N quietEqn') child live
  exact ⟨w', a', fired, beside'⟩

/-- **Both directions under the every-state condition**: the invariant of `runs_both_ways_along`. -/
theorem runs_neighbour_both_ways
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (both : DisciplinedBothWays N P R) {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quietAlt : NeverReads (IsAlternative N) w₀ others₀)
    (quietEqn : NeverReads (IsEquationRow N) w₀ others₀) {w : HostState S}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ) (others : Finset ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Beside N P C.world.scope b w a others ∧ NeverReads (IsAlternative N) w others ∧
        NeverReads (IsEquationRow N) w others ∧ ArrowBranch b :=
  runs_both_ways_along N spaces q equations qScoped qDistinct arrowQ (both.along N w₀) start quietAlt quietEqn
    run

/-- **The forward direction after the neighbour has moved, under the every-state condition.** -/
theorem forward_after_neighbour
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (both : DisciplinedBothWays N P R) {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quietAlt : NeverReads (IsAlternative N) w₀ others₀)
    (quietEqn : NeverReads (IsEquationRow N) w₀ others₀) {w : HostState S}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ) (others : Finset ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Beside N P C.world.scope b w a others ∧
        ∀ {v' : World κ Γ star} {bs : Multiset (Branch κ Γ star D.Ty)}, Move D P supply C.world b v' bs →
          ∀ {b' : Branch κ Γ star D.Ty}, b' ∈ bs → Solvable b'.store →
            ∃ w' a', Fires N P w w' ∧ Beside N P v'.scope b' w' a' others :=
  forward_along N spaces q equations qScoped qDistinct arrowQ (both.along N w₀) start quietAlt quietEqn run

/-- **From a start that represents the query's alternative beside quiet rows, the condition for both
directions along the runs gives the condition of the reflected direction along the runs**: at a state
a run reaches, the rows beside the alternative are the ones the run has kept quiet. -/
theorem disciplinedAlong_of_bothWays (supply : ℕ → Term S Γ star)
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ} (along : BothWaysAlong N P R w₀)
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quietAlt : NeverReads (IsAlternative N) w₀ others₀)
    (quietEqn : NeverReads (IsEquationRow N) w₀ others₀) : DisciplinedAlong N P R w₀ := by
  intro w reached n b a others f beside quiet admitted
  obtain ⟨C, b₁, a₁, others₁, _, _, beside₁, _, quietEqn₁, _⟩ :=
    runs_both_ways_along N (supply := supply) (fun _ => 0) q equations qScoped qDistinct arrowQ along start
      quietAlt quietEqn reached
  have solvable : (Interface.Frames.contextual S).Solvable w.knowledge := by
    obtain ⟨B, u, solved⟩ := admitted.2.2.1
    exact ⟨B, _, RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved⟩
  obtain ⟨sameRow, sameOthers⟩ := beside_unique N beside₁ beside quiet solvable
  subst sameRow sameOthers
  obtain ⟨apart, madeAlt, _⟩ := along w reached f beside quiet quietEqn₁ admitted
  exact ⟨apart, madeAlt⟩

end Runs

/-! ## The union as a readback and as a correspondence -/

section Systems

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **The union with a neighbour disciplined along the runs reads back to the source**, with the
neighbour's firings silent: a state is related to a configuration when a run of the union from `w₀`
reaches it and it tracks the configuration beside other rows (`TracksBeside`). -/
def alongReadback
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    (along : DisciplinedAlong N P R w₀) :
    OperationalReadback (Divergence.sourceSystem D P supply) (programSystem (translate N P ∪ R)) where
  related C w := Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w ∧ TracksBeside N spaces q P supply C w
  readStep := by
    rintro C w w' ⟨reached, runs, b, a, others, member, beside, quiet, arrow⟩ fires
    have fires' : FiresIn (translate N P ∪ R) w w' := fires
    have reached' := reached.tail fires'
    rcases (firesIn_union _ _ _ _).mp fires' with hosted | ⟨f, admitted, rfl⟩
    · have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
      obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
        reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside quiet arrow
          hygienic hosted
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      have step : SourceLanguage.Step D P supply C ⟨v', bs + rest⟩ := by
        obtain ⟨world, branches⟩ := C
        simp only at split
        subst split
        exact .move world v' b rest bs (live_beside N beside hosted) move
      exact .inr ⟨⟨v', bs + rest⟩, step, reached', runs.tail step, b', a', others,
        Multiset.mem_add.mpr (.inl child), beside', kept _ quiet, arrow'⟩
    · obtain ⟨apart, made⟩ := along _ reached f beside quiet admitted
      exact .inl ⟨reached', runs, b, a, _, member, beside_after_other N beside admitted apart,
        neverReads_fire admitted (others_sub N beside) quiet made, arrow⟩

/-- **A state represents an alternative with its world along the runs of the union from `w₀`**: a run
reaches it, and it represents the alternative beside rows that never read as alternatives' rows or as
equation rows. The rows are not fixed: the neighbour's firings change them. -/
def RepresentsAlong (P : SourceLanguage.Program κ Γ star D.Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (w₀ : HostState S)
    (x : World κ Γ star × Branch κ Γ star D.Ty) (w : HostState S) : Prop :=
  Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w ∧
    ∃ a others, Beside N P x.1.scope x.2 w a others ∧ ArrowBranch x.2 ∧ Scoping x.1.scope x.2 ∧
      NeverReads (IsAlternative N) w others ∧ NeverReads (IsEquationRow N) w others

/-- **Alternative by alternative, the union with a neighbour disciplined for both directions along the
runs is an operational correspondence**: a firing of the translated program is one move, a firing of
the neighbour is silent, and every move to a live alternative is one firing of the translated
program. -/
def alongCorrespondence
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    (along : BothWaysAlong N P R w₀) :
    OperationalCorrespondence (Divergence.alternativeSystem D P supply)
      (programSystem (translate N P ∪ R)) where
  related := RepresentsAlong N P R w₀
  readStep := by
    rintro ⟨v, b⟩ w w' ⟨reached, a, others, beside, arrow, ⟨Vis, L, Ls, inv⟩, noAlternative, noEquationRow⟩ fires
    have fires' : FiresIn (translate N P ∪ R) w w' := fires
    have reached' := reached.tail fires'
    rcases (firesIn_union _ _ _ _).mp fires' with hosted | ⟨f, admitted, rfl⟩
    · obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
        reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside noAlternative
          arrow (hygienic_of_scopedAt inv) hosted
      have live' : Solvable b'.store := by
        obtain ⟨f, admitted, rfl⟩ := hosted
        obtain ⟨B, u, solved⟩ := admitted.2.2.1
        obtain ⟨σ, solvedσ, _⟩ := (beside'.hosted.reads B _).mp ⟨u, solved, rfl⟩
        exact ⟨B.Names, B.arity, σ, solvedσ⟩
      exact .inr ⟨(v', b'), ⟨live_beside N beside hosted, bs, move, child, live'⟩, reached', a', others,
        beside', arrow', scopedAt_children equations move inv b' child, kept _ noAlternative,
        kept _ noEquationRow⟩
    · obtain ⟨apart, madeAlt, madeEqn⟩ := along _ reached f beside noAlternative noEquationRow admitted
      exact .inl ⟨reached', a, _, beside_after_other N beside admitted apart, arrow, ⟨Vis, L, Ls, inv⟩,
        neverReads_fire admitted (others_sub N beside) noAlternative madeAlt,
        neverReads_fire admitted (others_sub N beside) noEquationRow madeEqn⟩
  forward := by
    rintro ⟨v, b⟩ ⟨v', b'⟩ w ⟨reached, a, others, beside, arrow, ⟨Vis, L, Ls, inv⟩, noAlternative, noEquationRow⟩
      ⟨_, bs, move, child, live⟩
    obtain ⟨w', a', fires, beside', kept, arrow'⟩ :=
      simulation_beside N (fun e inside => (equations e inside).2.2) move beside arrow
        (hygienic_of_scopedAt inv) (fun _ _ _ => noMatchingRow_of_neverReads N noEquationRow) child live
    have fires' : FiresIn (translate N P ∪ R) w w' := (firesIn_union _ _ _ _).mpr (.inl fires)
    exact ⟨w', ⟨.cons ⟨fires'⟩ (.refl _)⟩, reached.tail fires', a', others, beside', arrow',
      scopedAt_children equations move inv b' child, kept _ noAlternative, kept _ noEquationRow⟩

/-- **The start is related to the query's alternative with the initial world.** -/
theorem start_representsAlong {qsite : κ.Site} (qScoped : q.Scoped [qsite])
    (qDistinct : (qsite :: q.sites).Nodup) (arrowQ : ArrowComp q)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quietAlt : NeverReads (IsAlternative N) w₀ others₀)
    (quietEqn : NeverReads (IsEquationRow N) w₀ others₀) :
    RepresentsAlong N P R w₀ (⟨0, 0, spaces⟩, initialBranch q) w₀ :=
  ⟨.refl, a₀, others₀, start, ⟨trivial, .inl ⟨q, rfl, arrowQ⟩⟩,
    ⟨_, _, _, scopedAt_initial arrowQ qScoped qDistinct⟩, quietAlt, quietEqn⟩

end Systems

/-! ## The answers the union shows from the start -/

section Answers

/-- **The answers the union shows from a state**: the answers of finished present rows of the states
that runs of the union of the translated program with the neighbour's rules reach from it. -/
def unionAnswersFrom {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (w₀ : HostState S) : Set (Set (Term S Γ star)) :=
  {A | ∃ s a, Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ s ∧ a ∈ s.present ∧
    StateFinished N s a ∧ stateAnswer N s a = A}

/-- A run of the translated program is a run of its union with any rules. -/
theorem lift_run {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ s : HostState S}
    (run : Relation.ReflTransGen (Fires N P) w₀ s) :
    Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ s := by
  induction run with
  | refl => exact .refl
  | tail _ fires ih => exact ih.tail ((firesIn_union _ _ _ _).mpr (.inl fires))

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **Beside a neighbour disciplined along the runs, the answers the union shows from the start are, as
a set, the source's.** -/
theorem answers_along
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {others : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ} (along : DisciplinedAlong N P R w₀)
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    (noAlternative : NeverReads (IsAlternative N) w₀ others)
    (noEquationRow : NeverReads (IsEquationRow N) w₀ others) :
    unionAnswersFrom N P R w₀ = Answers.sourceAnswers D P supply spaces q := by
  ext A
  constructor
  · rintro ⟨s, a, run, present, fin, rfl⟩
    obtain ⟨C, b, a', others', runs, member, beside, quiet', _⟩ :=
      runs_reflected_along N (supply := supply) spaces q equations qScoped qDistinct arrowQ along start
        noAlternative run
    obtain rfl := finished_row_beside N beside quiet' present fin
    exact ⟨C, runs, Answers.answer_mem N (s := restrict s (hostedRows P a)) member beside.hosted fin⟩
  · intro inSource
    rw [← answers_beside N (supply := supply) spaces q equations qScoped qDistinct arrowQ start noAlternative
      noEquationRow] at inSource
    obtain ⟨s, a, run, present, fin, same⟩ := inSource
    exact ⟨s, a, lift_run N run, present, fin, same⟩

end Answers

#print axioms disciplined_iff
#print axioms along_of_disciplined
#print axioms bothWays_of_disciplined
#print axioms beside_unique
#print axioms runs_reflected_along
#print axioms runs_both_ways_along
#print axioms forward_along
#print axioms runs_neighbour_both_ways
#print axioms forward_after_neighbour
#print axioms disciplinedAlong_of_bothWays
#print axioms alongReadback
#print axioms alongCorrespondence
#print axioms start_representsAlong
#print axioms lift_run
#print axioms answers_along

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
