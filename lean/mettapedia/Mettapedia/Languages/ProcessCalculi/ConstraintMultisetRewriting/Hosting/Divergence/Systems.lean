import Mettapedia.GSLT.Core.OperationalNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns

/-!
# The hosting as an operational correspondence, and divergence reflected

The tree's general notions of a correspondence between two systems
(`GSLT.IndexedOperational.OperationalReadback`, `OperationalCorrespondence`) relate one state to one
state. The hosting has three systems:

* `sourceSystem D P supply`: the source's configurations (bags of alternatives) and steps;
* `alternativeSystem D P supply`: one alternative with its world, and the moves of a live alternative to
  one live alternative the move makes;
* `hostSystem N P`: the states of the step and the firings of the translated program.

**Alternative by alternative the hosting is an operational correspondence**
(`alternativesCorrespondence`; `plainCorrespondence` for every program of the first fragment): the
relation is `Represents`, with the alternative of the fragment with `let` and scoped at run time;
every firing is one move (`readStep`, never silent) and every move is one firing (`forward`, a path of
length one). The start of a query is related to the query's alternative with the initial world
(`start_representsAlternative`, `start_representsPlain`). So it composes with every other correspondence of the tree
(`OperationalCorrespondence.comp`), observations that agree at related states are reachable on one
side exactly when they are on the other (`OperationalCorrespondence.reachable_iff`), and an
alternative that moves for ever is followed by an infinite run of the translated program
(`alternative_divergence_preserved`, by `OperationalCorrespondence.infinite_execution_preserved`).

**Configuration by configuration the reflected half is a readback** (`arrowReadback`, `plainReadback`):
a state tracks a configuration when it represents one of its alternatives; every firing is one step of
the configuration. The forward half is not an instance of the general notions at this relation: a
configuration is followed by a frontier of several states, one for each live alternative
(`arrow_runs_forward_of_scoped`, `runs_forward`). At this relation, when the tracked alternative's
move makes no live alternative, no state tracks the configuration that the step reaches
(`Examples.no_forward_at_fail`), because the relation relates a state to a configuration only through
one of its alternatives; at the same program and query another relation has both halves
(`OneAnswer.failCorrespondence`). What rules out a forward law for every relation that carries the
answers of a configuration to one state is that a reachable state shows at most one answer
(`OneAnswer.one_finished_row`, `OneAnswer.no_state_shows_both`).

**Divergence is reflected** (`arrow_divergence_reflected`, `divergence_reflected`): an infinite run of
the translated program from the start gives an infinite run of the source from the query. The
translation adds no divergence. It is `infinite_reflected`, for any readback in which no step of the
target is silent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Mettapedia.GSLT.IndexedOperational (OperationalReadback OperationalCorrespondence ExecutionPath)

universe uSource uTarget

/-! ## A readback without silent steps reflects infinite runs -/

/-- **A readback in which every step of the target is a step of the source reflects infinite runs.** -/
theorem infinite_reflected {source : Mettapedia.GSLT.GSLT.{uSource}} {target : Mettapedia.GSLT.GSLT.{uTarget}}
    (readback : OperationalReadback source target)
    (strict : ∀ {origin : source.Term} {current next : target.Term}, readback.related origin current →
      target.Step current next → ∃ after, source.Step origin after ∧ readback.related after next)
    {origin : source.Term} {current : target.Term} (related : readback.related origin current)
    (run : ℕ → target.Term) (first : run 0 = current) (steps : ∀ k, target.Step (run k) (run (k + 1))) :
    ∃ execution : ℕ → source.Term, execution 0 = origin ∧
      ∀ k, source.Step (execution k) (execution (k + 1)) := by
  classical
  have next : ∀ k (x : {x : source.Term // readback.related x (run k)}),
      ∃ y : {y : source.Term // readback.related y (run (k + 1))}, source.Step x.1 y.1 := by
    intro k x
    obtain ⟨y, step, rel⟩ := strict x.2 (steps k)
    exact ⟨⟨y, rel⟩, step⟩
  let chain : (k : ℕ) → {x : source.Term // readback.related x (run k)} :=
    fun k => Nat.rec (motive := fun k => {x : source.Term // readback.related x (run k)})
      ⟨origin, first ▸ related⟩ (fun k x => Classical.choose (next k x)) k
  exact ⟨fun k => (chain k).1, rfl, fun k => Classical.choose_spec (next k (chain k))⟩

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-! ## The three systems -/

/-- **The source language as a system**: configurations and steps. -/
def sourceSystem (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
    (supply : ℕ → Term S Γ star) : Mettapedia.GSLT.GSLT where
  Term := Config κ Γ star D.Ty
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SourceLanguage.Step D P supply
  rewrites_resp_left := by
    rintro t t' u same step
    subst same
    exact ⟨u, step, rfl⟩
  rewrites_resp_right := by
    rintro t u u' step same
    subst same
    exact step

/-- **One alternative with its world, as a system**: a live alternative moves to one live alternative
that its move makes. -/
def alternativeSystem (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
    (supply : ℕ → Term S Γ star) : Mettapedia.GSLT.GSLT where
  Term := World κ Γ star × Branch κ Γ star D.Ty
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites x y := Solvable x.2.store ∧ ∃ bs, Move D P supply x.1 x.2 y.1 bs ∧ y.2 ∈ bs ∧ Solvable y.2.store
  rewrites_resp_left := by
    rintro t t' u same step
    subst same
    exact ⟨u, step, rfl⟩
  rewrites_resp_right := by
    rintro t u u' step same
    subst same
    exact step

/-- **The step of a translated program as a system**: states and firings. -/
def hostSystem {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) : Mettapedia.GSLT.GSLT where
  Term := HostState S
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Fires N P
  rewrites_resp_left := by
    rintro t t' u same step
    subst same
    exact ⟨u, step, rfl⟩
  rewrites_resp_right := by
    rintro t u u' step same
    subst same
    exact step

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- The state a firing makes represents a live alternative. -/
theorem live_of_result {n : ℕ} {b : Branch κ Γ star D.Ty} {s s' : HostState S} {a : ℕ}
    (rep : Represents N P n b s' a) (fires : Fires N P s s') : Solvable b.store := by
  obtain ⟨f, admitted, rfl⟩ := fires
  obtain ⟨B, u, solved⟩ := admitted.2.2.1
  obtain ⟨σ, solvedσ, _⟩ := (rep.reads B _).mp ⟨u, solved, rfl⟩
  exact ⟨B.Names, B.arity, σ, solvedσ⟩

/-! ## Alternative by alternative: an operational correspondence -/

section Alternatives

variable (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)

/-- **A state represents an alternative with its world**: the representation, for an alternative of the
fragment with `let` that is scoped at run time. -/
def RepresentsAlternative (P : SourceLanguage.Program κ Γ star D.Ty)
    (x : World κ Γ star × Branch κ Γ star D.Ty) (s : HostState S) : Prop :=
  ∃ a, Represents N P x.1.scope x.2 s a ∧ ArrowBranch x.2 ∧ Scoping x.1.scope x.2

include equations in
/-- Every move of a represented alternative to a live alternative is one firing. -/
theorem alternative_forward {x y : World κ Γ star × Branch κ Γ star D.Ty} {s : HostState S}
    (related : RepresentsAlternative N P x s) (step : (alternativeSystem D P supply).Step x y) :
    ∃ s', Fires N P s s' ∧ RepresentsAlternative N P y s' := by
  obtain ⟨a, rep, arrow, Vis, L, Ls, inv⟩ := related
  obtain ⟨_, bs, move, child, live⟩ := step
  obtain ⟨s', a', fires, rep', arrow'⟩ :=
    simulation_arrows N (fun e member => (equations e member).2.2) move rep arrow (hygienic_of_scopedAt inv)
      child live
  exact ⟨s', fires, a', rep', arrow', scopedAt_children equations move inv _ child⟩

include equations in
/-- Every firing from a state that represents an alternative is one move of it to a live alternative. -/
theorem alternative_read {x : World κ Γ star × Branch κ Γ star D.Ty} {s s' : HostState S}
    (related : RepresentsAlternative N P x s) (fires : Fires N P s s') :
    ∃ y, (alternativeSystem D P supply).Step x y ∧ RepresentsAlternative N P y s' := by
  obtain ⟨a, rep, arrow, Vis, L, Ls, inv⟩ := related
  obtain ⟨v', bs, b', a', move, child, rep', arrow'⟩ :=
    reflection_arrows N (supply := supply) (fun e member => (equations e member).2.2) rep arrow
      (hygienic_of_scopedAt inv) fires
  exact ⟨(v', b'), ⟨live_of_fires N rep fires, bs, move, child, live_of_result N rep' fires⟩, a', rep', arrow',
    scopedAt_children equations move inv b' child⟩

/-- **The hosting, alternative by alternative, is an operational correspondence**: every firing is one
move, and every move is one firing. -/
def alternativesCorrespondence :
    OperationalCorrespondence (alternativeSystem D P supply) (hostSystem N P) where
  related := RepresentsAlternative N P
  readStep := fun related step => .inr (alternative_read N equations related step)
  forward := fun related step => by
    obtain ⟨s', fires, related'⟩ := alternative_forward N equations related step
    exact ⟨s', ⟨.cons ⟨fires⟩ (.refl _)⟩, related'⟩

/-- **The start represents the query's alternative with the initial world.** -/
theorem start_representsAlternative (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup) (arrowQ : ArrowComp q) :
    RepresentsAlternative N P (⟨0, 0, spaces⟩, initialBranch q) (start N P q) :=
  ⟨_, start_represents N P q (query_unopened qScoped qDistinct arrowQ), ⟨trivial, .inl ⟨q, rfl, arrowQ⟩⟩,
    _, _, _, scopedAt_initial arrowQ qScoped qDistinct⟩

include equations in
/-- **An alternative that moves for ever is followed by an infinite run of the translated program.** -/
theorem alternative_divergence_preserved {x : World κ Γ star × Branch κ Γ star D.Ty} {s : HostState S}
    (related : RepresentsAlternative N P x s) (moves : ℕ → World κ Γ star × Branch κ Γ star D.Ty)
    (first : moves 0 = x) (steps : ∀ k, (alternativeSystem D P supply).Step (moves k) (moves (k + 1))) :
    ∃ run : ℕ → HostState S, run 0 = s ∧ ∀ k, Fires N P (run k) (run (k + 1)) :=
  (alternativesCorrespondence N equations).infinite_execution_preserved
    (fun related' step => by
      obtain ⟨s', fires, related''⟩ := alternative_forward N equations related' step
      exact ⟨s', .cons ⟨fires⟩ (.refl _), Nat.succ_pos _, related''⟩)
    related moves first steps

include equations in
/-- **An infinite run of the translated program from a state that represents an alternative is an
alternative that moves for ever.** -/
theorem alternative_divergence_reflected {x : World κ Γ star × Branch κ Γ star D.Ty} {s : HostState S}
    (related : RepresentsAlternative N P x s) (run : ℕ → HostState S) (first : run 0 = s)
    (fires : ∀ k, Fires N P (run k) (run (k + 1))) :
    ∃ moves : ℕ → World κ Γ star × Branch κ Γ star D.Ty, moves 0 = x ∧
      ∀ k, (alternativeSystem D P supply).Step (moves k) (moves (k + 1)) :=
  infinite_reflected (alternativesCorrespondence N equations).toOperationalReadback
    (fun related' step => alternative_read N equations related' step) related run first fires

end Alternatives

/-! ## The first fragment, alternative by alternative -/

section PlainAlternatives

/-- **A state represents an alternative of the first fragment with its world.** -/
def RepresentsPlain (P : SourceLanguage.Program κ Γ star D.Ty)
    (x : World κ Γ star × Branch κ Γ star D.Ty) (s : HostState S) : Prop :=
  ∃ a, Represents N P x.1.scope x.2 s a ∧ PlainBranch x.2

/-- **The hosting of the first fragment, alternative by alternative, is an operational
correspondence**, for every program of the fragment: `simulation` is its forward law and `reflection`
its readback, with no silent step. -/
def plainCorrespondence (plainP : PlainProgram P) :
    OperationalCorrespondence (alternativeSystem D P supply) (hostSystem N P) where
  related := RepresentsPlain N P
  readStep := by
    rintro ⟨v, b⟩ s s' ⟨a, rep, plain⟩ fires
    obtain ⟨v', bs, b', a', move, child, rep', plain'⟩ :=
      reflection N (supply := supply) plainP rep plain fires
    exact .inr ⟨(v', b'), ⟨live_of_fires N rep fires, bs, move, child, live_of_result N rep' fires⟩, a',
      rep', plain'⟩
  forward := by
    rintro ⟨v, b⟩ ⟨v', b'⟩ s ⟨a, rep, plain⟩ ⟨_, bs, move, child, live⟩
    obtain ⟨s', a', fires, rep', plain'⟩ := simulation N plainP move rep plain child live
    exact ⟨s', ⟨.cons ⟨fires⟩ (.refl _)⟩, a', rep', plain'⟩

/-- The start represents the query's alternative with the initial world (the first fragment). -/
theorem start_representsPlain (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    RepresentsPlain N P (⟨0, 0, spaces⟩, initialBranch q) (start N P q) :=
  ⟨_, start_represents N P q unopened, rfl, .inl ⟨q, rfl, plainQ⟩⟩

end PlainAlternatives

/-! ## Configuration by configuration: the reflected half is a readback -/

section Configurations

variable (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **A state tracks a configuration** (the fragment with `let`): the configuration is reached from
the query, and the state represents one of its alternatives. -/
def Tracks (P : SourceLanguage.Program κ Γ star D.Ty) (supply : ℕ → Term S Γ star)
    (C : Config κ Γ star D.Ty) (s : HostState S) : Prop :=
  Runs D P supply (Config.initial spaces q) C ∧
    ∃ b a, b ∈ C.branches ∧ Represents N P C.world.scope b s a ∧ ArrowBranch b

/-- **A state tracks a configuration** (the first fragment): it represents one of its alternatives. -/
def TracksPlain (P : SourceLanguage.Program κ Γ star D.Ty) (C : Config κ Γ star D.Ty) (s : HostState S) :
    Prop :=
  ∃ b a, b ∈ C.branches ∧ Represents N P C.world.scope b s a ∧ PlainBranch b

/-- One firing moves the tracked configuration by one source step (the fragment with `let`). -/
theorem tracks_step
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {C : Config κ Γ star D.Ty} {s s' : HostState S}
    (tracks : Tracks N spaces q P supply C s) (fires : Fires N P s s') :
    ∃ C', SourceLanguage.Step D P supply C C' ∧ Tracks N spaces q P supply C' s' := by
  obtain ⟨runs, b, a, member, rep, arrow⟩ := tracks
  have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
  obtain ⟨v', bs, b', a', move, child, rep', arrow'⟩ :=
    reflection_arrows N (supply := supply) (fun e inside => (equations e inside).2.2) rep arrow hygienic fires
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  have step : SourceLanguage.Step D P supply C ⟨v', bs + rest⟩ := by
    obtain ⟨world, branches⟩ := C
    simp only at split
    subst split
    exact .move world v' b rest bs (live_of_fires N rep fires) move
  exact ⟨⟨v', bs + rest⟩, step, runs.tail step, b', a', Multiset.mem_add.mpr (.inl child), rep', arrow'⟩

/-- One firing moves the tracked configuration by one source step (the first fragment). -/
theorem tracksPlain_step (plainP : PlainProgram P) {C : Config κ Γ star D.Ty} {s s' : HostState S}
    (tracks : TracksPlain N P C s) (fires : Fires N P s s') :
    ∃ C', SourceLanguage.Step D P supply C C' ∧ TracksPlain N P C' s' := by
  obtain ⟨b, a, member, rep, plain⟩ := tracks
  obtain ⟨v', bs, b', a', move, child, rep', plain'⟩ := reflection N (supply := supply) plainP rep plain fires
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  refine ⟨⟨v', bs + rest⟩, ?_, b', a', Multiset.mem_add.mpr (.inl child), rep', plain'⟩
  obtain ⟨world, branches⟩ := C
  simp only at split
  subst split
  exact .move world v' b rest bs (live_of_fires N rep fires) move

/-- **The reflected half of the hosting is a readback** (the fragment with `let`, scoped programs and
queries): every firing is one step of the tracked configuration. -/
def arrowReadback
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) : OperationalReadback (sourceSystem D P supply) (hostSystem N P) where
  related := Tracks N spaces q P supply
  readStep := fun tracks fires => .inr (tracks_step N spaces q equations qScoped qDistinct arrowQ tracks fires)

/-- **The reflected half of the hosting is a readback** (the first fragment). -/
def plainReadback (plainP : PlainProgram P) : OperationalReadback (sourceSystem D P supply) (hostSystem N P) where
  related := TracksPlain N P
  readStep := fun tracks fires => .inr (tracksPlain_step N plainP tracks fires)

/-- **Divergence is reflected** (the fragment with `let`): an infinite run of the translated program
from the start of a scoped query gives an infinite run of the source from the query. -/
theorem arrow_divergence_reflected
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) (run : ℕ → HostState S) (first : run 0 = start N P q)
    (fires : ∀ k, Fires N P (run k) (run (k + 1))) :
    ∃ C : ℕ → Config κ Γ star D.Ty, C 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (C k) (C (k + 1)) :=
  infinite_reflected (arrowReadback N spaces q equations qScoped qDistinct arrowQ)
    (fun tracks step => tracks_step N spaces q equations qScoped qDistinct arrowQ tracks step)
    (origin := Config.initial spaces q)
    ⟨.refl, initialBranch q, _, Multiset.mem_singleton_self _,
      start_represents N P q (query_unopened qScoped qDistinct arrowQ), trivial, .inl ⟨q, rfl, arrowQ⟩⟩
    run first fires

/-- **Divergence is reflected** (the first fragment): an infinite run of the translated program from
the start of a query whose names are unopened gives an infinite run of the source from the query. -/
theorem divergence_reflected (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (run : ℕ → HostState S)
    (first : run 0 = start N P q) (fires : ∀ k, Fires N P (run k) (run (k + 1))) :
    ∃ C : ℕ → Config κ Γ star D.Ty, C 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (C k) (C (k + 1)) :=
  infinite_reflected (plainReadback N (supply := supply) plainP)
    (fun tracks step => tracksPlain_step N plainP tracks step)
    (origin := Config.initial spaces q)
    ⟨initialBranch q, _, Multiset.mem_singleton_self _, start_represents N P q unopened, rfl,
      .inl ⟨q, rfl, plainQ⟩⟩
    run first fires

end Configurations

#print axioms infinite_reflected
#print axioms alternative_forward
#print axioms alternative_read
#print axioms alternativesCorrespondence
#print axioms alternative_divergence_preserved
#print axioms alternative_divergence_reflected
#print axioms plainCorrespondence
#print axioms start_representsAlternative
#print axioms start_representsPlain
#print axioms arrowReadback
#print axioms plainReadback
#print axioms arrow_divergence_reflected
#print axioms divergence_reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence
