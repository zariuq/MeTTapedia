import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hygiene

/-!
# Whole runs of scoped programs with arrows

The run theorems for `ret`, `apply`, `let_`, `choice`, `fail`, under the clauses of well-formedness
their proofs use. Calls inside `let`s, calls inside the bodies of `let`s, recursion and nested `let`s
are all included: hygiene along the run is a lemma (`reachableHygienic_of_scoped`), not a hypothesis.

* `arrow_runs_forward_of_scoped`: every source run is followed by runs of the step from the
  translation's start, to a frontier of the reached configuration.
* `arrow_answers_of_scoped`: the answers of every reached configuration, as a bag, are those of a
  frontier reached by the step.
* `arrow_runs_reflected_of_scoped`: every run of the step from the start represents an alternative of
  a configuration that a source run reaches.

**The `_of_scoped` forms are the theorems.** They state exactly the clauses used: every equation is
scoped, with its own site and its binder sites distinct, and of the fragment with arrows; the query is
scoped from its site, with its site and its binder sites distinct, and of the fragment. The forms
without the suffix (`arrow_runs_forward`, `arrow_answers`, `arrow_runs_reflected`) are their
corollaries for programs and queries satisfying the source's `WellFormed` and `QueryWellFormed`, which
give these clauses and ask more: the patterns clause, and distinctness of sites across equations and
between the query and the program, which no proof here uses. A program that is not well formed and to
which the `_of_scoped` forms apply is `Controls.UnusedClauses`.

The frontier is one represented state per live alternative; the step does not count alternatives by
itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {D : Discipline S Γ star}
  {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
variable (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-! ## With the clauses the theorems use -/

/-- **Every source run is followed by runs of the step**, for scoped programs and queries with arrows
and distinct binder sites. The frontier is one represented state per live alternative; the step does
not count alternatives by itself. -/
theorem arrow_runs_forward_of_scoped
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {C : Config κ Γ star D.Ty} (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L, ArrowFrontier N P C L ∧ ∀ x ∈ L, Relation.ReflTransGen (Fires N P) (start N P q) x.2.1 :=
  arrow_runs_forward_of_hygienic N spaces q (fun e member => (equations e member).2.2) arrowQ
    (query_unopened qScoped qDistinct arrowQ)
    (reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ) runs

/-- **The answers of every configuration a source run reaches, as a bag, are those of a frontier
reached by the step**, for scoped programs and queries with arrows and distinct binder sites. The
frontier is one represented state per live alternative; the step does not count alternatives by
itself. -/
theorem arrow_answers_of_scoped
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {C : Config κ Γ star D.Ty} (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ), C.answers (D := D) = frontierAnswers N L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N P) (start N P q) x.2.1 := by
  obtain ⟨L, frontier, reached⟩ :=
    arrow_runs_forward_of_scoped N spaces q equations qScoped qDistinct arrowQ runs
  exact ⟨L, arrowFrontier_answers N frontier, reached⟩

/-- **Every run of the step from the translation's start is a source run**, for scoped programs and
queries with arrows and distinct binder sites: it reaches a state that represents an alternative of a
configuration a source run reaches. -/
theorem arrow_runs_reflected_of_scoped
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {s : HostState S} (run : Relation.ReflTransGen (Fires N P) (start N P q) s) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Represents N P C.world.scope b s a ∧ ArrowBranch b :=
  arrow_runs_reflected_of_hygienic N spaces q (fun e member => (equations e member).2.2) arrowQ
    (query_unopened qScoped qDistinct arrowQ)
    (reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ) run

/-- **One frontier step along a run whose configurations are hygienic**, keeping every state of the
frontier reached by runs of the step. This is the step of `arrow_runs_forward_of_hygienic`, for a run
that is hygienic only up to where it is used (the controls use it on runs that are not hygienic
afterwards). -/
theorem arrowFrontier_reached_step (arrowP : ArrowProgram P) {s₀ : HostState S}
    {C C' : Config κ Γ star D.Ty} {L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)}
    (frontier : ArrowFrontier N P C L) (reached : ∀ x ∈ L, Relation.ReflTransGen (Fires N P) s₀ x.2.1)
    (hygienic : ∀ b ∈ C.branches, Hygienic b) (step : SourceLanguage.Step D P supply C C') :
    ∃ L', ArrowFrontier N P C' L' ∧ ∀ x ∈ L', Relation.ReflTransGen (Fires N P) s₀ x.2.1 := by
  obtain ⟨L', frontier', x, rest, new, split, rfl, fires⟩ := arrowFrontier_step N arrowP frontier hygienic step
  refine ⟨_, frontier', ?_⟩
  intro y member
  rcases Multiset.mem_add.mp member with fresh | old
  · exact (reached x (by rw [split]; exact Multiset.mem_cons_self _ _)).tail (fires y fresh)
  · exact reached y (by rw [split]; exact Multiset.mem_cons_of_mem old)

/-! ## Corollaries for well-formed programs and queries -/

variable [DecidableEq κ.Key]

/-- The query's distinct sites, from its well-formedness. -/
theorem query_distinct {qsite : κ.Site} (qwf : QueryWellFormed P qsite q) :
    (qsite :: q.sites).Nodup :=
  qwf.distinctSites.sublist (List.sublist_append_left _ _)

/-- **Corollary of `arrow_runs_forward_of_scoped` for well-formed programs and queries with arrows**:
every source run is followed by runs of the step. `WellFormed` and `QueryWellFormed` give the clauses
that theorem uses and ask more, which is not used. The frontier is one represented state per live
alternative; the step does not count alternatives by itself. -/
theorem arrow_runs_forward (wf : WellFormed P) (arrowP : ArrowProgram P) {qsite : κ.Site}
    (qwf : QueryWellFormed P qsite q) (arrowQ : ArrowComp q) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L, ArrowFrontier N P C L ∧ ∀ x ∈ L, Relation.ReflTransGen (Fires N P) (start N P q) x.2.1 :=
  arrow_runs_forward_of_scoped N spaces q (equations_of_wellFormed wf arrowP) qwf.inScope
    (query_distinct q qwf) arrowQ runs

/-- **Corollary of `arrow_answers_of_scoped` for well-formed programs and queries with arrows**: the
answers of every configuration a source run reaches, as a bag, are those of a frontier reached by the
step. The frontier is one represented state per live alternative; the step does not count
alternatives by itself. -/
theorem arrow_answers (wf : WellFormed P) (arrowP : ArrowProgram P) {qsite : κ.Site}
    (qwf : QueryWellFormed P qsite q) (arrowQ : ArrowComp q) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ), C.answers (D := D) = frontierAnswers N L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N P) (start N P q) x.2.1 :=
  arrow_answers_of_scoped N spaces q (equations_of_wellFormed wf arrowP) qwf.inScope
    (query_distinct q qwf) arrowQ runs

/-- **Corollary of `arrow_runs_reflected_of_scoped` for well-formed programs and queries with
arrows**: every run of the step from the translation's start reaches a state that represents an
alternative of a configuration a source run reaches. -/
theorem arrow_runs_reflected (wf : WellFormed P) (arrowP : ArrowProgram P) {qsite : κ.Site}
    (qwf : QueryWellFormed P qsite q) (arrowQ : ArrowComp q) {s : HostState S}
    (run : Relation.ReflTransGen (Fires N P) (start N P q) s) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Represents N P C.world.scope b s a ∧ ArrowBranch b :=
  arrow_runs_reflected_of_scoped N spaces q (equations_of_wellFormed wf arrowP) qwf.inScope
    (query_distinct q qwf) arrowQ run

#print axioms arrow_runs_forward_of_scoped
#print axioms arrow_answers_of_scoped
#print axioms arrow_runs_reflected_of_scoped
#print axioms arrow_runs_forward
#print axioms arrow_answers
#print axioms arrow_runs_reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
