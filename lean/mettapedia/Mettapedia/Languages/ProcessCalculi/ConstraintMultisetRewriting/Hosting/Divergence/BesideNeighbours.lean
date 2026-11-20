import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.NeighbourControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Examples

/-!
# Divergence beside a neighbour's rules

`Divergence.arrow_diverges_iff` is about the translated program alone: the source diverges from a query
exactly when the translated program has an infinite run from the start. Beside a neighbour's rules the
union may run for ever on the neighbour's firings alone, so the statement that survives counts the
firings of the translated program.

* `spawn_forever`: the rule `Composition.spawnRule` (disciplined for both directions,
  `Composition.NeighbourControls.spawn_both_ways`) has an infinite run from every state whose knowledge
  has a solution. `union_diverges`: so the union of **every** translated program with it has an infinite
  run from the start of **every** query, and `terminating_source_diverging_union`: for the program with
  no equation and the query `ret d` the source has no infinite run and the union has one.
* `TranslatedInfinitely N P R w₀`: a run of the union of the translated program with the rules `R` from
  `w₀` in which the translated program fires infinitely often.
* `source_diverges_of_translated_infinitely`: from a state that represents the query's alternative
  beside rows that never read as alternatives' rows, under the condition asked along the runs
  (`Composition.AlongRuns.DisciplinedAlong`), such a run gives an infinite run of the source. Each firing
  of the translated program is one source step (`tracks_hosted`), each firing of the neighbour is silent
  (`tracks_neighbour`), and between two firings of the translated program there are finitely many of the
  neighbour's.
* `arrow_diverges_iff_beside`: **the source diverges from the query exactly when the union has a run from
  the start in which the translated program fires infinitely often** (the fragment with `let`, scoped
  programs and queries, the condition along the runs from the start). `arrow_diverges_iff_bothWays`: the
  same under the condition for both directions along the runs.
* The instance: beside `spawnRule`, `spawn_diverges_iff`; for `(= (loop) (loop))` and the query `(loop)`
  the union has a run in which the translated program fires infinitely often
  (`loop_translated_infinitely`); and the control of the counting: for the program with no equation and
  the query `ret d` the union diverges and has no such run (`returned_not_translated_infinitely`).
* `plain_alternative_diverges`: for the first fragment, an infinite run of the source moves one
  alternative for ever (`Divergence.arrow_alternative_diverges` is the form for the fragment with `let`).

**Divergence kept after the neighbour has moved**, under the condition for both directions along the
runs (`Composition.AlongRuns.BothWaysAlong`):

* `along_forward_step`, `along_hosted_step`: at a state related along the runs
  (`Composition.AlongRuns.RepresentsAlong`), a move of the alternative is one firing of the translated
  program and a firing of the translated program is one move; `along_neighbour_step`: a firing of the
  neighbour keeps the relation.
* `reached_representsAlong`: every state a run of the union reaches from the start is related to an
  alternative that the alternatives' moves reach from the query's.
* `translated_diverges_after`: if that alternative moves for ever, the translated program **alone** has
  an infinite run from that state. Instance: for `(= (loop) (loop))` beside the spawning rule, after the
  rule has fired at the start (`loop_diverges_after_spawn`). Under the condition of the reflected
  direction alone the forward step can be lost at once: `Composition.NeighbourControls.switched_off`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.BesideNeighbours

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-! ## A neighbour that runs for ever -/

/-- **The spawning rule runs for ever** from every state whose knowledge has a solution. -/
theorem spawn_forever {w : HostState S} (solvable : (Interface.Frames.contextual S).Solvable w.knowledge) :
    ∃ f : ℕ → HostState S, f 0 = w ∧
      ∀ k, FiresIn ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (f k) (f (k + 1)) := by
  have next : ∀ x : {w : HostState S // (Interface.Frames.contextual S).Solvable w.knowledge},
      ∃ y : {w : HostState S // (Interface.Frames.contextual S).Solvable w.knowledge},
        FiresIn ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) x.1 y.1 := by
    intro x
    obtain ⟨w', f, admitted, rfl⟩ := spawn_fires N x.2
    exact ⟨⟨_, admitted.2.2.1⟩, f, admitted, rfl⟩
  let chain : ℕ → {w : HostState S // (Interface.Frames.contextual S).Solvable w.knowledge} :=
    fun k => Nat.rec ⟨w, solvable⟩ (fun _ x => Classical.choose (next x)) k
  exact ⟨fun k => (chain k).1, rfl, fun k => Classical.choose_spec (next (chain k))⟩

/-- **The union of every translated program with the spawning rule diverges from the start of every
query.** -/
theorem union_diverges {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    ∃ f : ℕ → HostState S, f 0 = start N P q ∧
      ∀ k, FiresIn (translate N P ∪ {spawnRule N}) (f k) (f (k + 1)) := by
  obtain ⟨f, first, fires⟩ := spawn_forever N (NeighbourControls.start_solvable N P q)
  exact ⟨f, first, fun k => (firesIn_union _ _ _ _).mpr (.inr (fires k))⟩

/-- **A source that terminates, and its union with the spawning rule, which does not.** -/
theorem terminating_source_diverging_union :
    Acc (fun C' C => SourceLanguage.Step Examples.D Examples.empty Examples.supply C C')
        (Config.initial Examples.sp Examples.returned) ∧
      ∃ f : ℕ → HostState Elaboration.MSig, f 0 = start Examples.N Examples.empty Examples.returned ∧
        ∀ k, FiresIn (translate Examples.N Examples.empty ∪ {spawnRule Examples.N}) (f k) (f (k + 1)) :=
  ⟨Examples.ret_source_terminates, union_diverges Examples.N Examples.empty Examples.returned⟩

/-! ## Counting the firings of the translated program -/

/-- **A run of the union in which the translated program fires infinitely often.** -/
def TranslatedInfinitely {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (w₀ : HostState S) : Prop :=
  ∃ f : ℕ → HostState S, f 0 = w₀ ∧ (∀ k, FiresIn (translate N P ∪ R) (f k) (f (k + 1))) ∧
    ∀ k, ∃ j, k ≤ j ∧ Fires N P (f j) (f (j + 1))

/-- Every state of a run is reached by its prefix. -/
theorem run_reached {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {f : ℕ → HostState S}
    (steps : ∀ k, FiresIn Prog (f k) (f (k + 1))) : ∀ k, Relation.ReflTransGen (FiresIn Prog) (f 0) (f k)
  | 0 => .refl
  | k + 1 => (run_reached steps k).tail (steps k)

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **A firing of the translated program is one source step** of a configuration the state tracks. -/
theorem tracks_hosted
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {C : Config κ Γ star D.Ty} {w w' : HostState S}
    (tracks : TracksBeside N spaces q P supply C w) (fires : Fires N P w w') :
    ∃ C', SourceLanguage.Step D P supply C C' ∧ TracksBeside N spaces q P supply C' w' := by
  obtain ⟨runs, b, a, others, member, beside, quiet, arrow⟩ := tracks
  have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
  obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
    reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside quiet arrow
      hygienic fires
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  have step : SourceLanguage.Step D P supply C ⟨v', bs + rest⟩ := by
    obtain ⟨world, branches⟩ := C
    simp only at split
    subst split
    exact .move world v' b rest bs (live_beside N beside fires) move
  exact ⟨⟨v', bs + rest⟩, step, runs.tail step, b', a', others, Multiset.mem_add.mpr (.inl child), beside',
    kept _ quiet, arrow'⟩

/-- **A firing of a neighbour disciplined along the runs is silent**: the state it makes tracks the same
configuration. -/
theorem tracks_neighbour {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    (along : DisciplinedAlong N P R w₀) {C : Config κ Γ star D.Ty} {w w' : HostState S}
    (reached : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w)
    (tracks : TracksBeside N spaces q P supply C w) (fires : FiresIn R w w') :
    TracksBeside N spaces q P supply C w' := by
  obtain ⟨runs, b, a, others, member, beside, quiet, arrow⟩ := tracks
  obtain ⟨f, admitted, rfl⟩ := fires
  obtain ⟨apart, made⟩ := along _ reached f beside quiet admitted
  exact ⟨runs, b, a, _, member, beside_after_other N beside admitted apart,
    neverReads_fire admitted (others_sub N beside) quiet made, arrow⟩

/-- Between two firings of the translated program the neighbour's firings keep the configuration. -/
theorem tracks_stretch {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {f : ℕ → HostState S}
    (along : DisciplinedAlong N P R (f 0)) (steps : ∀ k, FiresIn (translate N P ∪ R) (f k) (f (k + 1)))
    {C : Config κ Γ star D.Ty} {k : ℕ} (tracks : TracksBeside N spaces q P supply C (f k)) (d : ℕ) :
    (∀ i, k ≤ i → i < k + d → ¬ Fires N P (f i) (f (i + 1))) → TracksBeside N spaces q P supply C (f (k + d)) := by
  induction d with
  | zero => intro _; exact tracks
  | succ d ih =>
      intro silent
      have prev := ih (fun i hk hi => silent i hk (by omega))
      rcases (firesIn_union _ _ _ _).mp (steps (k + d)) with hosted | neighbour
      · exact absurd hosted (silent (k + d) (by omega) (by omega))
      · exact tracks_neighbour N spaces q along (run_reached steps (k + d)) prev neighbour

/-- **A run of the union in which the translated program fires infinitely often gives an infinite run
of the source**, from a state that represents the query's alternative beside rows that never read as
alternatives' rows, under the condition along the runs. -/
theorem source_diverges_of_translated_infinitely
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    (along : DisciplinedAlong N P R w₀) {others₀ : Finset ℕ} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quiet : NeverReads (IsAlternative N) w₀ others₀) (infinitely : TranslatedInfinitely N P R w₀) :
    ∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1)) := by
  obtain ⟨f, first, steps, often⟩ := infinitely
  subst first
  refine (not_acc_iff_exists_descending_chain
    (r := fun C' C => SourceLanguage.Step D P supply C C') (x := Config.initial spaces q)).mp ?_
  intro acc
  have key : ∀ C, Acc (fun C' C => SourceLanguage.Step D P supply C C') C →
      ∀ k, TracksBeside N spaces q P supply C (f k) → False := by
    intro C accC
    induction accC with
    | intro C _ ih =>
        intro k tracks
        have exists' : ∃ j, k ≤ j ∧ Fires N P (f j) (f (j + 1)) := often k
        have spec := Nat.find_spec exists'
        have atJ := tracks_stretch N spaces q along steps tracks (Nat.find exists' - k) (by
          intro i hk hi fires
          exact Nat.find_min exists' (show i < Nat.find exists' by omega) ⟨hk, fires⟩)
        rw [Nat.add_sub_cancel' spec.1] at atJ
        obtain ⟨C', step, tracks'⟩ := tracks_hosted N spaces q equations qScoped qDistinct arrowQ atJ spec.2
        exact ih C' step (Nat.find exists' + 1) tracks'
  exact key _ acc 0 ⟨.refl, initialBranch q, a₀, others₀, Multiset.mem_singleton_self _, start, quiet, trivial,
    .inl ⟨q, rfl, arrowQ⟩⟩

/-- **Divergence beside a neighbour's rules** (the fragment with `let`): under the condition along the
runs from the start, the source diverges from a scoped query exactly when the union has a run from the
start in which the translated program fires infinitely often. -/
theorem arrow_diverges_iff_beside
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (along : DisciplinedAlong N P R (start N P q)) :
    (∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) ↔
      TranslatedInfinitely N P R (start N P q) := by
  constructor
  · rintro ⟨run, first, steps⟩
    obtain ⟨f, f0, fires⟩ :=
      arrow_divergence_preserved N spaces q equations qScoped qDistinct arrowQ run first steps
    exact ⟨f, f0, fun k => (firesIn_union _ _ _ _).mpr (.inl (fires k)), fun k => ⟨k, le_refl k, fires k⟩⟩
  · intro infinitely
    exact source_diverges_of_translated_infinitely N spaces q equations qScoped qDistinct arrowQ along
      ((beside_empty N).mpr (start_represents N P q (query_unopened qScoped qDistinct arrowQ)))
      (fun o inside => absurd inside (Finset.notMem_empty o)) infinitely

/-- **The same under the condition for both directions along the runs.** -/
theorem arrow_diverges_iff_bothWays
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (along : BothWaysAlong N P R (start N P q)) :
    (∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) ↔
      TranslatedInfinitely N P R (start N P q) := by
  have startBeside : Beside N P 0 (initialBranch q) (start N P q) P.equations.length ∅ :=
    (beside_empty N).mpr (start_represents N P q (query_unopened qScoped qDistinct arrowQ))
  exact arrow_diverges_iff_beside N spaces q equations qScoped qDistinct arrowQ
    (disciplinedAlong_of_bothWays N q supply equations qScoped qDistinct arrowQ along startBeside
      (fun o inside => absurd inside (Finset.notMem_empty o))
      (fun o inside => absurd inside (Finset.notMem_empty o)))

/-- **The instance: beside the spawning rule**, which runs for ever, the source diverges exactly when the
translated program fires infinitely often in a run of the union. -/
theorem spawn_diverges_iff
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) :
    (∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) ↔
      TranslatedInfinitely N P {spawnRule N} (start N P q) :=
  arrow_diverges_iff_beside N spaces q equations qScoped qDistinct arrowQ
    (along_of_disciplined N (spawn_disciplined N) _)

include N in
/-- **An infinite run of the source moves one alternative for ever** (the first fragment): no source
run diverges only by infinitely many alternatives each of which is finite. -/
theorem plain_alternative_diverges (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (run : ℕ → Config κ Γ star D.Ty)
    (first : run 0 = Config.initial spaces q)
    (steps : ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) :
    ∃ moves : ℕ → World κ Γ star × Branch κ Γ star D.Ty, moves 0 = (⟨0, 0, spaces⟩, initialBranch q) ∧
      ∀ k, (alternativeSystem D P supply).Step (moves k) (moves (k + 1)) := by
  obtain ⟨f, start, fires⟩ := divergence_preserved N spaces q plainP plainQ unopened run first steps
  refine infinite_reflected (plainCorrespondence N (supply := supply) plainP).toOperationalReadback ?_
    (start_representsPlain N spaces q plainQ unopened) f start fires
  rintro ⟨v, b⟩ s s' ⟨a, rep, plain⟩ fired
  obtain ⟨v', bs, b', a', move, child, rep', plain'⟩ :=
    reflection N (supply := supply) plainP rep plain fired
  exact ⟨(v', b'), ⟨live_of_fires N rep fired, bs, move, child, live_of_result N rep' fired⟩, a', rep', plain'⟩

/-- **The control of the counting**: for the program with no equation and the query `ret d`, the union
with the spawning rule diverges, and it has no run in which the translated program fires infinitely
often. -/
theorem returned_not_translated_infinitely :
    (∃ f : ℕ → HostState Elaboration.MSig, f 0 = start Examples.N Examples.empty Examples.returned ∧
        ∀ k, FiresIn (translate Examples.N Examples.empty ∪ {spawnRule Examples.N}) (f k) (f (k + 1))) ∧
      ¬ TranslatedInfinitely Examples.N Examples.empty {spawnRule Examples.N}
        (start Examples.N Examples.empty Examples.returned) := by
  refine ⟨union_diverges Examples.N Examples.empty Examples.returned, fun infinitely => ?_⟩
  obtain ⟨run, first, steps⟩ :=
    (spawn_diverges_iff Examples.N (D := Examples.D) (supply := Examples.supply) Examples.sp Examples.returned
      (fun e member => by cases member) (qsite := [311]) (by decide) (by decide) trivial).mpr infinitely
  exact not_acc_iff_exists_descending_chain.mpr ⟨run, first, steps⟩ Examples.ret_source_terminates

/-! ## Divergence kept after the neighbour has moved -/

section After

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **A move of the alternative a state represents along the runs is one firing of the translated
program**, to a state that represents the alternative it makes. No condition on the neighbour is used:
it enters through the states that are related. -/
theorem along_forward_step
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    {x y : World κ Γ star × Branch κ Γ star D.Ty} {w : HostState S}
    (rel : RepresentsAlong N P R w₀ x w) (step : (alternativeSystem D P supply).Step x y) :
    ∃ w', Fires N P w w' ∧ RepresentsAlong N P R w₀ y w' := by
  obtain ⟨v, b⟩ := x
  obtain ⟨v', b'⟩ := y
  obtain ⟨reached, a, others, beside, arrow, ⟨Vis, L, Ls, inv⟩, noAlternative, noEquationRow⟩ := rel
  obtain ⟨_, bs, move, child, live⟩ := step
  obtain ⟨w', a', fires, beside', kept, arrow'⟩ :=
    simulation_beside N (fun e inside => (equations e inside).2.2) move beside arrow
      (hygienic_of_scopedAt inv) (fun _ _ _ => noMatchingRow_of_neverReads N noEquationRow) child live
  have fires' : FiresIn (translate N P ∪ R) w w' := (firesIn_union _ _ _ _).mpr (.inl fires)
  exact ⟨w', fires, reached.tail fires', a', others, beside', arrow',
    scopedAt_children equations move inv b' child, kept _ noAlternative, kept _ noEquationRow⟩

/-- **A firing of the translated program at a state related along the runs is one move of its
alternative**, to a state related to the alternative the move makes. -/
theorem along_hosted_step
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    {x : World κ Γ star × Branch κ Γ star D.Ty} {w w' : HostState S}
    (rel : RepresentsAlong N P R w₀ x w) (hosted : FiresIn (translate N P) w w') :
    ∃ y, (alternativeSystem D P supply).Step x y ∧ RepresentsAlong N P R w₀ y w' := by
  obtain ⟨v, b⟩ := x
  obtain ⟨reached, a, others, beside, arrow, ⟨Vis, L, Ls, inv⟩, noAlternative, noEquationRow⟩ := rel
  obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
    reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside noAlternative
      arrow (hygienic_of_scopedAt inv) hosted
  have live' : Solvable b'.store := by
    obtain ⟨f, admitted, rfl⟩ := hosted
    obtain ⟨B, u, solved⟩ := admitted.2.2.1
    obtain ⟨σ, solvedσ, _⟩ := (beside'.hosted.reads B _).mp ⟨u, solved, rfl⟩
    exact ⟨B.Names, B.arity, σ, solvedσ⟩
  have fires' : FiresIn (translate N P ∪ R) w w' := (firesIn_union _ _ _ _).mpr (.inl hosted)
  exact ⟨(v', b'), ⟨live_beside N beside hosted, bs, move, child, live'⟩, reached.tail fires', a', others,
    beside', arrow', scopedAt_children equations move inv b' child, kept _ noAlternative, kept _ noEquationRow⟩

/-- **A firing of a neighbour disciplined for both directions along the runs keeps the relation.** -/
theorem along_neighbour_step {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    (along : BothWaysAlong N P R w₀) {x : World κ Γ star × Branch κ Γ star D.Ty} {w w' : HostState S}
    (rel : RepresentsAlong N P R w₀ x w) (fires : FiresIn R w w') : RepresentsAlong N P R w₀ x w' := by
  obtain ⟨reached, a, others, beside, arrow, scoping, noAlternative, noEquationRow⟩ := rel
  obtain ⟨f, admitted, rfl⟩ := fires
  obtain ⟨apart, madeAlt, madeEqn⟩ := along _ reached f beside noAlternative noEquationRow admitted
  exact ⟨reached.tail ((firesIn_union _ _ _ _).mpr (.inr ⟨f, admitted, rfl⟩)), a, _,
    beside_after_other N beside admitted apart, arrow, scoping,
    neverReads_fire admitted (others_sub N beside) noAlternative madeAlt,
    neverReads_fire admitted (others_sub N beside) noEquationRow madeEqn⟩

/-- **An alternative that moves for ever is followed by an infinite run of the translated program alone**,
from every state that represents it along the runs. -/
theorem translated_diverges_after
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w₀ : HostState S}
    {x : World κ Γ star × Branch κ Γ star D.Ty} {w : HostState S} (rel : RepresentsAlong N P R w₀ x w)
    (moves : ℕ → World κ Γ star × Branch κ Γ star D.Ty) (first : moves 0 = x)
    (steps : ∀ k, (alternativeSystem D P supply).Step (moves k) (moves (k + 1))) :
    ∃ f : ℕ → HostState S, f 0 = w ∧ ∀ k, Fires N P (f k) (f (k + 1)) := by
  have next : ∀ k (s : {s : HostState S // RepresentsAlong N P R w₀ (moves k) s}),
      ∃ t : {t : HostState S // RepresentsAlong N P R w₀ (moves (k + 1)) t}, Fires N P s.1 t.1 := by
    intro k s
    obtain ⟨w', fires, rel'⟩ := along_forward_step N equations s.2 (steps k)
    exact ⟨⟨w', rel'⟩, fires⟩
  let chain : (k : ℕ) → {s : HostState S // RepresentsAlong N P R w₀ (moves k) s} :=
    fun k => Nat.rec (motive := fun k => {s : HostState S // RepresentsAlong N P R w₀ (moves k) s})
      ⟨w, first ▸ rel⟩ (fun k s => Classical.choose (next k s)) k
  exact ⟨fun k => (chain k).1, rfl, fun k => Classical.choose_spec (next k (chain k))⟩

/-- **Every state a run of the union reaches is related along the runs** to an alternative that the
alternatives' moves reach from the query's, under the condition for both directions along the runs. -/
theorem reached_representsAlong
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (along : BothWaysAlong N P R (start N P q)) {w : HostState S}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) (start N P q) w) :
    ∃ x, Relation.ReflTransGen (alternativeSystem D P supply).Step (⟨0, 0, spaces⟩, initialBranch q) x ∧
      RepresentsAlong N P R (start N P q) x w := by
  induction run with
  | refl =>
      exact ⟨_, .refl, start_representsAlong N spaces q qScoped qDistinct arrowQ R
        ((beside_empty N).mpr (start_represents N P q (query_unopened qScoped qDistinct arrowQ)))
        (fun o inside => absurd inside (Finset.notMem_empty o))
        (fun o inside => absurd inside (Finset.notMem_empty o))⟩
  | tail _ fires ih =>
      obtain ⟨x, reachX, rel⟩ := ih
      rcases (firesIn_union _ _ _ _).mp fires with hosted | neighbour
      · obtain ⟨y, fired, rel'⟩ := along_hosted_step N (supply := supply) equations rel hosted
        exact ⟨y, reachX.tail fired, rel'⟩
      · exact ⟨x, reachX, along_neighbour_step N along rel neighbour⟩

end After

/-- **The instance of divergence kept after the neighbour has moved**: for `(= (loop) (loop))` and the
query `(loop)`, after the spawning rule has fired at the start, the translated program alone has an
infinite run from the state it makes. -/
theorem loop_diverges_after_spawn :
    ∃ w, FiresIn ({spawnRule Examples.N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms Elaboration.MSig))
        (start Examples.N Examples.program Examples.query) w ∧
      ∃ f : ℕ → HostState Elaboration.MSig, f 0 = w ∧ ∀ k, Fires Examples.N Examples.program (f k) (f (k + 1)) := by
  obtain ⟨w, fires⟩ :=
    spawn_fires Examples.N (NeighbourControls.start_solvable Examples.N Examples.program Examples.query)
  refine ⟨w, fires, ?_⟩
  have startRel : RepresentsAlong Examples.N (D := Examples.D) Examples.program {spawnRule Examples.N}
      (start Examples.N Examples.program Examples.query) (⟨0, 0, Examples.sp⟩, initialBranch Examples.query)
      (start Examples.N Examples.program Examples.query) :=
    start_representsAlong Examples.N (D := Examples.D) (P := Examples.program) Examples.sp Examples.query
      Examples.loop_scoped.2.1
      Examples.loop_scoped.2.2.1 Examples.loop_scoped.2.2.2 _
      ((beside_empty Examples.N).mpr
        (start_represents Examples.N Examples.program Examples.query Examples.query_unopened))
      (fun o inside => absurd inside (Finset.notMem_empty o))
      (fun o inside => absurd inside (Finset.notMem_empty o))
  have rel := along_neighbour_step Examples.N
    ((NeighbourControls.spawn_both_ways Examples.N (D := Examples.D) (P := Examples.program)).along Examples.N _)
    startRel fires
  obtain ⟨run, first, steps⟩ := Examples.source_diverges
  obtain ⟨moves, movesFirst, movesSteps⟩ :=
    arrow_alternative_diverges Examples.N (D := Examples.D) (P := Examples.program) (supply := Examples.supply)
      Examples.sp Examples.query Examples.loop_scoped.1
      Examples.loop_scoped.2.1 Examples.loop_scoped.2.2.1 Examples.loop_scoped.2.2.2 run first steps
  exact translated_diverges_after Examples.N Examples.loop_scoped.1 rel moves movesFirst movesSteps

/-- **The positive instance of the counting**: for `(= (loop) (loop))` and the query `(loop)`, the union
with the spawning rule has a run in which the translated program fires infinitely often. -/
theorem loop_translated_infinitely :
    TranslatedInfinitely Examples.N Examples.program {spawnRule Examples.N}
      (start Examples.N Examples.program Examples.query) :=
  (spawn_diverges_iff Examples.N (D := Examples.D) (supply := Examples.supply) Examples.sp Examples.query
    Examples.loop_scoped.1 Examples.loop_scoped.2.1 Examples.loop_scoped.2.2.1 Examples.loop_scoped.2.2.2).mp
    Examples.source_diverges

#print axioms loop_translated_infinitely
#print axioms along_forward_step
#print axioms along_hosted_step
#print axioms along_neighbour_step
#print axioms translated_diverges_after
#print axioms reached_representsAlong
#print axioms loop_diverges_after_spawn
#print axioms spawn_forever
#print axioms union_diverges
#print axioms terminating_source_diverging_union
#print axioms run_reached
#print axioms tracks_hosted
#print axioms tracks_neighbour
#print axioms tracks_stretch
#print axioms source_diverges_of_translated_infinitely
#print axioms arrow_diverges_iff_beside
#print axioms arrow_diverges_iff_bothWays
#print axioms spawn_diverges_iff
#print axioms plain_alternative_diverges
#print axioms returned_not_translated_infinitely

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.BesideNeighbours
