import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition

/-!
# The unmatched call is the one place where a hosted program is not monotone

MeTTa returns a call that no equation matches as data. The translation hosts that by the one rule with
an absence check, `unmatchedRule`: every other rule of a translation is positive, its checks being
equations (there are none) and its collect query empty (`positive_of_ne_unmatched`); the unmatched call's rule
is not (`unmatched_not_positive`).

* `NoUnmatchedCall D P supply spaces q`: **no reachable call is unmatched**: every live alternative of
  every configuration a source run reaches, whose focus is a call, has an equation whose fresh copy
  unifies with the call.
* `only_positive` (the fragment with `let`, under the clauses the run theorems use) and
  `only_positive_plain` (the first fragment): for such a program and query, **every admitted firing at
  every state that a run of the translated program reaches from the start is a firing of a positive
  rule**: the hosted runs use no absence check.

**Exactly where the unmatched call is stable.** A live alternative at a call that no equation matches,
beside other rows that never read as alternatives' rows, has its firing exactly when no other row
matches the call at a solution of the knowledge (`Composition.unmatched_beside_iff`). So "a call that
no equation matches is data" is kept by every neighbour that adds no row matching that call, and is
switched off by one row that does (`Controls.neighbour_stuck`), even when the row matches at one
solution only (`Composition.UnmatchedControls.partial_match_stuck`). What decides is matching: a row
with the call's head that does not match leaves the firing (`Controls.same_head_fires`); the row
`eqn($x)` with `$x` the row's private name matches every call and removes it
(`Controls.variable_row_stuck`); and which unknowns a row shares with the call matters: the one row
text `eqn((g a $x))` leaves the firing of the call `(g $x b)` when `$x` is the call's own name, and
removes it when `$x` is the row's private name (`Composition.UnmatchedControls.shared_row_fires`,
`Composition.UnmatchedControls.private_row_stuck`). The source language has the same non-monotonicity, in the
form in which it is a law: adding an equation to a program changes the answer of a call it matches,
and the hosted system of the union, rules and rows together (`Composition.hosted_union`), answers as
the union does. A row without its schema is half of that: it removes the old answer and gives no new
one.

**Programs with no reachable unmatched call** need no condition on the neighbour's equation rows:
`Composition.runs_forward_beside_of_matched`, `Composition.answers_beside_of_matched`.

**The dividing line of the reflective encodings does not apply as it stands.**
`Encodings.succeeds_beside` keeps reachable success of a system whose rules are all positive beside
every neighbour with solvable knowledge. Its hypotheses do not fit a hosted system: its systems are
states over the twin-binder signature with the frame action whose equality is similarity under every
grounding, and the hosted ones are states over the source's signature with syntactic equality; it asks
every rule of the program to be positive, and a translation always contains the unmatched call's rule,
so positivity holds here of runs (`only_positive`), not of the program; and it keeps may-success, one
reachable barb, which is the forward half of a run correspondence only: it says nothing of the runs a
neighbour adds, which is where reflection fails (`Controls.alternative_row_answers`). What it says of
positive firings holds at the hosting's frames for a neighbour inside the same state:
`Composition.admits_extend_positive` (a positive firing asks nothing of the rows it does not select),
and the run statement with the matching-row condition discharged is
`Composition.runs_forward_beside_of_matched`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-! ## Positive rules -/

/-- **Every rule of a translation but the unmatched call's is positive.** -/
theorem positive_of_ne_unmatched {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)} (member : r ∈ translate N P)
    (other : r ≠ unmatchedRule N) : RuleSyntax.Scope.Positive r := by
  rcases (mem_translate N).mp member with control | ⟨e, _, rfl⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun c inside => by simp [retRule] at inside, rfl⟩
    · exact absurd rfl other
    · exact ⟨fun c inside => by simp [choiceLeftRule] at inside, rfl⟩
    · exact ⟨fun c inside => by simp [choiceRightRule] at inside, rfl⟩
    · exact ⟨fun c inside => by simp [bindStartRule] at inside, rfl⟩
    · exact ⟨fun c inside => by simp [bindValueRule] at inside, rfl⟩
  · exact ⟨fun c inside => by simp [schema] at inside, rfl⟩

/-- **The unmatched call's rule is not positive**: its check is an absence. -/
theorem unmatched_not_positive : ¬ RuleSyntax.Scope.Positive (unmatchedRule N) := by
  rintro ⟨checks, _⟩
  obtain ⟨l, l', same⟩ := checks _ (List.mem_singleton_self _)
  cases same

/-! ## No reachable unmatched call -/

/-- **No reachable call is unmatched**: every live alternative of every configuration a source run
reaches, whose focus is a call, has an equation whose fresh copy unifies with the call. -/
def NoUnmatchedCall (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
    (supply : ℕ → Term S Γ star) (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty) :
    Prop :=
  ∀ C, Runs D P supply (Config.initial spaces q) C → ∀ b ∈ C.branches, Solvable b.store →
    ∀ t, b.focus = .eval (.apply t) →
      ∃ e ∈ P.equations, Solvable (b.store ++ [(instantiate (copyAt κ C.world.scope) e.lhs, t)])

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- An admitted firing of the unmatched call's rule at a state that represents a live alternative of
a reached configuration contradicts a matching equation there. -/
theorem not_unmatched_at {C : Config κ Γ star D.Ty} {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ}
    (runs : Runs D P supply (Config.initial spaces q) C) (member : b ∈ C.branches)
    (rep : Represents N P C.world.scope b s a) (matched : NoUnmatchedCall D P supply spaces q)
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame)
    (admitted : f.Admits (Interface.Frames.contextual S) s) : f.rule ≠ unmatchedRule N := by
  intro unmatched
  obtain ⟨rule, rmember, ext, opening, selection, seen⟩ := f
  simp only at unmatched
  subst unmatched
  obtain ⟨K, focus, fs, ps⟩ := b
  obtain ⟨a', simple, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
    (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
  change branchReads N _ B (observe (instantiate h _)) at reads
  rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
  obtain ⟨t, σ, rfl, _, _⟩ := shape_apply N reads
  have none := unmatched_none N rep simple admitted
  have live := live_of_fires N rep ⟨_, admitted, rfl⟩
  obtain ⟨e, eMember, solvable⟩ := matched C runs _ member live t rfl
  exact none e eMember solvable

/-- **Only positive rules fire** (the fragment with `let`): when no reachable call is unmatched, every
admitted firing at every state that a run of the translated program reaches from the start is a
firing of a positive rule. -/
theorem only_positive
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) (matched : NoUnmatchedCall D P supply spaces q)
    {s : HostState S} (run : Relation.ReflTransGen (Fires N P) (start N P q) s)
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame)
    (admitted : f.Admits (Interface.Frames.contextual S) s) : RuleSyntax.Scope.Positive f.rule := by
  obtain ⟨C, b, a, runs, member, rep, _⟩ :=
    arrow_runs_reflected_of_scoped N (supply := supply) spaces q equations qScoped qDistinct arrowQ run
  exact positive_of_ne_unmatched N f.member (not_unmatched_at N spaces q runs member rep matched f admitted)

/-- **Only positive rules fire** (the first fragment), for queries whose names are unopened. -/
theorem only_positive_plain (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (matched : NoUnmatchedCall D P supply spaces q)
    {s : HostState S} (run : Relation.ReflTransGen (Fires N P) (start N P q) s)
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame)
    (admitted : f.Admits (Interface.Frames.contextual S) s) : RuleSyntax.Scope.Positive f.rule := by
  obtain ⟨C, b, a, runs, member, rep, _⟩ :=
    runs_reflected N (supply := supply) spaces q plainP plainQ unopened run
  exact positive_of_ne_unmatched N f.member (not_unmatched_at N spaces q runs member rep matched f admitted)

#print axioms positive_of_ne_unmatched
#print axioms unmatched_not_positive
#print axioms not_unmatched_at
#print axioms only_positive
#print axioms only_positive_plain

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
