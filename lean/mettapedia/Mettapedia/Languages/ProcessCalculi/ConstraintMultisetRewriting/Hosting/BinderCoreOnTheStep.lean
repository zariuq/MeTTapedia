import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCore

/-!
# The binder core on the step of its translated program

The binder core (equations under binders, rewritten at the root of a closed call) is a fragment of the
source language (`SourceLanguage.BinderCore.execution_iff`): its embedded program has right sides
`apply rhs`, so it is a program of the first fragment (`program_plain`), and its query is a call.
With the hosting theorem:

* `binderCore_on_the_step`: **the binder core's rewriting from a closed call reaches exactly the
  closed terms that the states reached by runs of the translated program show** (as the call or the
  value of their alternative's row).
* `binderCore_two_steps`: the older correspondence (`ProgramBinders.execution_iff`, on a restriction
  of the contextual guarded step to the program's schemas, with its own states and readings) and this
  one characterize the same relation. It is the two equivalences composed, and adds nothing to them:
  no relation between the states of the two steps is stated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.BinderCoreOnTheStep

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open SourceLanguage.BinderCore (keys program start Shows)
open Classical

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} (N : Nodes S Γ sort)
  (l : List (ProgramBinders.Equation S Γ sort)) (D : Discipline S Γ sort) (supply : ℕ → Term S Γ sort)

/-- **The embedded binder core is a program of the first fragment.** -/
theorem program_plain : PlainProgram (program l (Ty := D.Ty)) := by
  intro e member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  trivial

/-- The query of a closed call. -/
abbrev callQuery (call : Term S Γ sort) : Comp (keys l) Γ sort D.Ty :=
  .apply (Rigid.includeTerm (fam (keys l)) call)

theorem callQuery_unopened (call : Term S Γ sort) :
    ∀ t ∈ (callQuery l D call).data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [Comp.data, List.mem_singleton] at member
  subst member
  rw [Rigid.support_include] at inside
  cases inside

/-- **What a state shows**: a present row reads as the call `g`, or as the value `g`, of an
alternative with no frames. -/
def StateShows (s : HostState S) (g : Term S Γ sort) : Prop :=
  ∃ a ∈ s.present, ∃ B : Interface.Frames.Frame S,
    rowReads s a B (observe (altN N (evalN N (applyN N (Rigid.includeTerm B.arity g))) (emptyN N))) ∨
    rowReads s a B (observe (altN N (valueN N (Rigid.includeTerm B.arity g)) (emptyN N)))

/-- A represented alternative with no frames shows `g` exactly when its row does. -/
theorem shows_iff {n : ℕ} {b : Branch (keys l) Γ sort D.Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N (program l (Ty := D.Ty)) n b s a) (frames : b.frames = []) (g : Term S Γ sort) :
    Shows l b g ↔ ∃ B : Interface.Frames.Frame S,
      rowReads s a B (observe (altN N (evalN N (applyN N (Rigid.includeTerm B.arity g))) (emptyN N))) ∨
      rowReads s a B (observe (altN N (valueN N (Rigid.includeTerm B.arity g)) (emptyN N))) := by
  constructor
  · rintro ⟨t, focus | focus, X, target, σ, solved, read⟩
    · refine ⟨⟨X, target⟩, .inl ((rep.reads _ _).mpr ((branchReads_observe N).mpr ⟨σ, solved, ?_⟩))⟩
      rw [encBranch, encAlt, focus, frames]
      show N.node .alt ![N.node .eval ![N.node .apply ![instantiate σ t]], _] = _
      rw [read]
      rfl
    · refine ⟨⟨X, target⟩, .inr ((rep.reads _ _).mpr ((branchReads_observe N).mpr ⟨σ, solved, ?_⟩))⟩
      rw [encBranch, encAlt, focus, frames]
      show N.node .alt ![N.node .value ![instantiate σ t], _] = _
      rw [read]
      rfl
  · rintro ⟨B, reads | reads⟩
    · obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp ((rep.reads B _).mp reads)
      obtain ⟨onFocus, _⟩ := alt_eq_encAlt N (instantiate σ) same.symm
      obtain ⟨c, focus, onComp⟩ := eval_eq_encFocus N (instantiate σ) onFocus
      obtain ⟨t, rfl, onCall⟩ := apply_eq_encComp N (instantiate σ) onComp
      exact ⟨t, .inl focus, B.Names, B.arity, σ, solved, onCall.symm⟩
    · obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp ((rep.reads B _).mp reads)
      obtain ⟨onFocus, _⟩ := alt_eq_encAlt N (instantiate σ) same.symm
      obtain ⟨t, focus, onValue⟩ := value_eq_encFocus N (instantiate σ) onFocus
      exact ⟨t, .inr focus, B.Names, B.arity, σ, solved, onValue.symm⟩

/-- An equation row never reads as an alternative. -/
theorem row_not_alt {P : SourceLanguage.Program (keys l) Γ sort D.Ty} {n : ℕ} {b : Branch (keys l) Γ sort D.Ty}
    {s : HostState S} {a i : ℕ} (rep : Represents N P n b s a) (small : i < P.equations.length)
    {B : Interface.Frames.Frame S} {x y : Term (signature S B.arity) Γ sort}
    (reads : rowReads s i B (observe (altN N x y))) : False := by
  obtain ⟨σ, known, read⟩ := reads
  obtain ⟨θ, row⟩ := rep.rows B σ known i small
  have same := read.symm.trans row
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

include supply in
/-- **The binder core on the step.** The binder core's rewriting from a closed call reaches exactly the
closed terms that a state reached by a run of the translated program shows. -/
theorem binderCore_on_the_step [ProgramBinders.ClosedTerms S] (call answer : Term S Γ sort) :
    Relation.ReflTransGen (ProgramBinders.Rewrites l.get) call answer ↔
      ∃ s, Relation.ReflTransGen (Fires N (program l (Ty := D.Ty)))
        (Hosting.start N (program l (Ty := D.Ty)) (callQuery l D call)) s ∧ StateShows N s answer := by
  rw [BinderCore.execution_iff l D supply call answer]
  constructor
  · rintro ⟨C, runs, b, member, shows⟩
    obtain ⟨L, frontier, reached⟩ := runs_forward N (fun _ => 0) (callQuery l D call)
      (program_plain l D) trivial (callQuery_unopened l D call) runs
    have live : Solvable b.store := by
      obtain ⟨t, _, X, target, σ, solved, _⟩ := shows
      exact ⟨X, target, σ, solved⟩
    have inside : b ∈ L.map Prod.fst := by
      rw [frontier.branches]
      exact Multiset.mem_filter.mpr ⟨member, live⟩
    obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp inside
    obtain ⟨rep, plain⟩ := frontier.represents x xMember
    refine ⟨x.2.1, reached x xMember, x.2.2, ?_, (shows_iff N l D rep plain.1 answer).mp shows⟩
    rw [rep.present]
    exact Finset.mem_insert_self _ _
  · rintro ⟨s, run, a, present, readsShow⟩
    obtain ⟨C, b, a', runs, member, rep, plain⟩ := runs_reflected N (supply := supply) (fun _ => 0)
      (callQuery l D call) (program_plain l D) trivial (callQuery_unopened l D call) run
    have same : a = a' := by
      rw [rep.present, Finset.mem_insert, Finset.mem_range] at present
      rcases present with same | small
      · exact same
      · obtain ⟨B, reads | reads⟩ := readsShow
        · exact (row_not_alt N l D rep small reads).elim
        · exact (row_not_alt N l D rep small reads).elim
    subst same
    exact ⟨C, runs, b, member, (shows_iff N l D rep plain.1 answer).mpr readsShow⟩

include supply in
/-- **The older correspondence and this one say the same thing.** The binder core's correspondence on
a restriction of the contextual guarded step (`ProgramBinders.execution_iff`) and its correspondence
on the step of the translated program characterize the same rewriting relation: the two equivalences
composed, with the binder core's rewriting between them. -/
theorem binderCore_two_steps [ProgramBinders.ClosedTerms S] (call answer : Term S Γ sort) :
    (∃ after, Relation.ReflTransGen (ProgramBinders.Transition l.get) (ProgramBinders.initial call) after ∧
        ProgramBinders.Reads l.get after answer) ↔
      ∃ s, Relation.ReflTransGen (Fires N (program l (Ty := D.Ty)))
        (Hosting.start N (program l (Ty := D.Ty)) (callQuery l D call)) s ∧ StateShows N s answer :=
  (ProgramBinders.execution_iff (program := l.get) call answer).symm.trans
    (binderCore_on_the_step N l D supply call answer)

#print axioms program_plain
#print axioms shows_iff
#print axioms binderCore_on_the_step
#print axioms binderCore_two_steps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.BinderCoreOnTheStep
