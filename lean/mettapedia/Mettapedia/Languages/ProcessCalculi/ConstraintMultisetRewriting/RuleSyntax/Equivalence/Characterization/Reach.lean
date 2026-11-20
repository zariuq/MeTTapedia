import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.EveryState

/-!
# Two programs at one state: answering at every configuration a context can reach

`congruent_iff_static_and_same` reduces the congruence of two systems to the static equivalence of their
states and the congruence of the two programs at one state `s`. This module says when the latter holds.

**A reachable configuration** (`Reachable P P' s Q u`): from `s` with no added rules, contexts add rows,
tell equations and add rules one at a time (collected in `Q`), and firings of `P`, `P'` or `Q` move
the state.

* **`congruent_iff_reachable`** (bounded `P`, `P'`): `⟨P, s⟩` and `⟨P', s⟩` are congruent exactly when, at
  every reachable configuration `(Q, u)`, each of `P ∪ Q` and `P' ∪ Q` answers the other's firings at
  `u` with statically equivalent results (`AnswersStaticAt`).
* The direction from answering is `congruent_of_reachable`, for every pair of programs.
* With `congruent_iff_static_and_same`: `⟨P, s⟩` and `⟨P', t⟩` are congruent exactly when `s` and `t`
  are statically equivalent and the programs answer each other at every configuration reachable from
  `s` (`congruent_iff_static_and_reachable`).

Only the programs' own firings need answers (`answersStaticAt_union_iff`, `congruent_iff_reachable_own`):
a firing of an added rule is answered by itself. The rules the context adds may answer as well: a
firing of `P` at a reachable state may be answered by a firing of a rule of `Q`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong extendState_eq_self)

/-- **A configuration reachable from `s`**: rules added one at a time, rows added, equations told, and
firings of `P`, `P'` or the added rules. -/
inductive Reachable (P P' : Program Tm) (s : State Tm ℕ) : Program Tm → State Tm ℕ → Prop
  | start : Reachable P P' s ∅ s
  | rows {Q : Program Tm} {u : State Tm ℕ} (ids : Finset ℕ) (label : ℕ → Term atoms) :
      Reachable P P' s Q u → Disjoint ids u.present → Reachable P P' s Q (addRows u ids label)
  | tell {Q : Program Tm} {u : State Tm ℕ} (L : EquationStore (Term atoms)) :
      Reachable P P' s Q u → Reachable P P' s Q (tellState u L)
  | rule {Q : Program Tm} {u : State Tm ℕ} (r : Rule Tm) :
      Reachable P P' s Q u → Reachable P P' s (Q ∪ {r}) u
  | fire {Q : Program Tm} {u : State Tm ℕ} (f : Firing ℕ E (P ∪ P' ∪ Q) u.frame) :
      Reachable P P' s Q u → f.Admits X u → Reachable P P' s Q (f.result X u)

/-- **Static answering at one state.** -/
def AnswersStaticAt (P P' : Program Tm) (u : State Tm ℕ) : Prop :=
  ∀ f : Firing ℕ E P u.frame, f.Admits X u →
    ∃ g : Firing ℕ E P' u.frame, g.Admits X u ∧ Static (f.result X u) (g.result X u)

theorem reachable_finite {P P' : Program Tm} {s : State Tm ℕ} {Q : Program Tm} {u : State Tm ℕ}
    (reached : Reachable P P' s Q u) : Q.Finite := by
  induction reached with
  | start => exact Set.finite_empty
  | rows _ _ _ _ ih => exact ih
  | tell _ _ ih => exact ih
  | rule r _ ih => exact ih.union (Set.finite_singleton r)
  | fire _ _ _ ih => exact ih

theorem bounded_union {P Q : Program Tm} (bounded : Bounded P) (finite : Q.Finite) :
    Bounded (P ∪ Q) := by
  obtain ⟨B₁, bound₁⟩ := bounded
  obtain ⟨B₂, bound₂⟩ := bounded_of_finite finite
  refine ⟨B₁ + B₂, fun r member t inside k same => ?_⟩
  rcases (Set.mem_union _ _ _).mp member with inP | inQ
  · have small := bound₁ r inP t inside k same
    omega
  · have small := bound₂ r inQ t inside k same
    omega

/-- **Along reachable configurations the two programs stay congruent**, beside the added rules. -/
theorem congruent_of_reachable_config {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P')
    {s : State Tm ℕ} (related : Cong ⟨P, s⟩ ⟨P', s⟩) {Q : Program Tm} {u : State Tm ℕ}
    (reached : Reachable P P' s Q u) : Cong ⟨P ∪ Q, u⟩ ⟨P' ∪ Q, u⟩ := by
  induction reached with
  | start =>
      rw [Set.union_empty, Set.union_empty]
      exact related
  | rows ids label _ apart ih =>
      exact cong_basic_same ih (.rows ids fun _ => label) apart apart
  | tell L _ ih =>
      exact cong_basic_same ih (.tell fun _ => L) (Basic.applies_of_ids_empty rfl _)
        (Basic.applies_of_ids_empty rfl _)
  | rule r _ ih =>
      have added := ih.addRules {r}
      rw [Set.union_assoc, Set.union_assoc] at added
      exact added
  | @fire Q u f reached admitted ih =>
      have finite := reachable_finite reached
      have boundLeft := bounded_union boundP finite
      have boundRight := bounded_union boundP' finite
      rcases (Set.mem_union _ _ _).mp f.member with inPP' | inQ
      · rcases (Set.mem_union _ _ _).mp inPP' with inP | inP'
        · -- The left fires; its answer is statically equivalent.
          obtain ⟨T', moved, results⟩ := candidate_congruent.reduces ih
            (reduces_of_admits (reprogram f (Or.inl inP)) admitted)
          obtain ⟨program, g, admittedG, reachedT⟩ := moved
          have reachedT' : g.result X u = T'.state := reachedT
          obtain ⟨TP, Ts⟩ := T'
          simp only at program reachedT'
          subst program reachedT'
          have static := static_of_congruent boundLeft boundRight results
          exact results.trans (congruent_of_static (P' ∪ Q) static).symm
        · -- The right fires.
          obtain ⟨T', moved, results⟩ := candidate_congruent.reduces ih.symm
            (reduces_of_admits (reprogram f (Or.inl inP')) admitted)
          obtain ⟨program, g, admittedG, reachedT⟩ := moved
          have reachedT' : g.result X u = T'.state := reachedT
          obtain ⟨TP, Ts⟩ := T'
          simp only at program reachedT'
          subst program reachedT'
          have static := static_of_congruent boundRight boundLeft results
          exact (results.trans (congruent_of_static (P ∪ Q) static).symm).symm
      · -- A rule the context added fires at both sides.
        obtain ⟨T', moved, results⟩ := candidate_congruent.reduces ih
          (reduces_of_admits (reprogram f (Or.inr inQ)) admitted)
        obtain ⟨program, g, admittedG, reachedT⟩ := moved
        have reachedT' : g.result X u = T'.state := reachedT
        obtain ⟨TP, Ts⟩ := T'
        simp only at program reachedT'
        subst program reachedT'
        have static := static_of_congruent boundLeft boundRight results
        exact results.trans (congruent_of_static (P' ∪ Q) static).symm

/-- **The sound direction, for every pair of programs**: answering at every reachable configuration
gives congruence at `s`. -/
theorem congruent_of_reachable {P P' : Program Tm} {s : State Tm ℕ}
    (answers : ∀ Q u, Reachable P P' s Q u →
      AnswersStaticAt (P ∪ Q) (P' ∪ Q) u ∧ AnswersStaticAt (P' ∪ Q) (P ∪ Q) u) :
    Cong ⟨P, s⟩ ⟨P', s⟩ := by
  let R : Sys → Sys → Prop := fun S T => ∃ Q Q₀ u, Q₀ ⊆ Q ∧ Reachable P P' s Q₀ u ∧
    ((S = ⟨P ∪ Q, u⟩ ∧ T = ⟨P' ∪ Q, u⟩) ∨ (S = ⟨P' ∪ Q, u⟩ ∧ T = ⟨P ∪ Q, u⟩))
  have start : R ⟨P, s⟩ ⟨P', s⟩ := ⟨∅, ∅, s, le_rfl, .start, Or.inl ⟨by rw [Set.union_empty],
    by rw [Set.union_empty]⟩⟩
  refine congruent_of_upTo (R := R) ?_ ?_ ?_ ?_ start
  · rintro S T ⟨Q, Q₀, u, sub, reached, orient⟩
    refine ⟨Q, Q₀, u, sub, reached, ?_⟩
    rcases orient with ⟨left, right⟩ | ⟨left, right⟩
    · exact Or.inr ⟨right, left⟩
    · exact Or.inl ⟨right, left⟩
  · rintro S T ⟨Q, Q₀, u, -, -, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ β holds <;> exact holds
  · rintro S T ⟨Q, Q₀, u, sub, reached, orient⟩ S' ⟨programSame, f, admitted, reachedS⟩
    obtain ⟨S'P, S's⟩ := S'
    -- One orientation at a time: `mine` fires, `other` answers.
    have step : ∀ (mine other : Program Tm),
        ((mine = P ∧ other = P') ∨ (mine = P' ∧ other = P)) →
        (∀ f : Firing ℕ E (mine ∪ Q₀) u.frame, f.Admits X u →
          ∃ g : Firing ℕ E (other ∪ Q₀) u.frame, g.Admits X u ∧ Static (f.result X u) (g.result X u)) →
        ∀ f : Firing ℕ E (mine ∪ Q) u.frame, f.Admits X u →
          ∃ T', Reduces X ℕ E ⟨other ∪ Q, u⟩ T' ∧
            UpTo X ℕ E (MayBarb X) R ⟨mine ∪ Q, f.result X u⟩ T' ∧
            ∃ Q₀', Q₀' ⊆ Q ∧ Reachable P P' s Q₀' (f.result X u) := by
      intro mine other orientation answer f admitted
      have inBoth : ∀ {r : Rule Tm}, r ∈ mine → r ∈ P ∪ P' ∪ Q₀ := fun {r} member => by
        rcases orientation with ⟨hm, -⟩ | ⟨hm, -⟩
        · rw [hm] at member
          exact Or.inl (Or.inl member)
        · rw [hm] at member
          exact Or.inl (Or.inr member)
      by_cases known : f.rule ∈ mine ∪ Q₀
      · obtain ⟨g, admittedG, static⟩ := answer (reprogram f known) admitted
        have reachedF : Reachable P P' s Q₀ (f.result X u) := by
          refine .fire (reprogram f ?_) reached admitted
          rcases (Set.mem_union _ _ _).mp known with inMine | inQ₀
          · exact inBoth inMine
          · exact Or.inr inQ₀
        have gIn : g.rule ∈ other ∪ Q := by
          rcases (Set.mem_union _ _ _).mp g.member with inOther | inQ₀
          · exact Or.inl inOther
          · exact Or.inr (sub inQ₀)
        refine ⟨⟨other ∪ Q, g.result X u⟩, reduces_of_admits (reprogram g gIn) admittedG,
          ⟨⟨mine ∪ Q, f.result X u⟩, ⟨other ∪ Q, f.result X u⟩, Congruent.refl _, ⟨Q, Q₀,
            f.result X u, sub, reachedF, ?_⟩, congruent_of_static (other ∪ Q) static⟩,
          ⟨Q₀, sub, reachedF⟩⟩
        rcases orientation with ⟨hm, ho⟩ | ⟨hm, ho⟩
        · exact Or.inl ⟨congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) hm,
            congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) ho⟩
        · exact Or.inr ⟨congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) hm,
            congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) ho⟩
      · -- A rule of the context outside what was used so far: fired at both sides alike.
        have inQ : f.rule ∈ Q := by
          rcases (Set.mem_union _ _ _).mp f.member with inMine | inQ
          · exact absurd (Or.inl inMine) known
          · exact inQ
        have reachedF : Reachable P P' s (Q₀ ∪ {f.rule}) (f.result X u) :=
          .fire (reprogram f (Or.inr (Or.inr (Set.mem_singleton _)))) (.rule f.rule reached) admitted
        have sub' : Q₀ ∪ {f.rule} ⊆ Q := Set.union_subset sub (Set.singleton_subset_iff.mpr inQ)
        refine ⟨⟨other ∪ Q, f.result X u⟩, reduces_of_admits (reprogram f (Or.inr inQ)) admitted,
          ⟨⟨mine ∪ Q, f.result X u⟩, ⟨other ∪ Q, f.result X u⟩, Congruent.refl _, ⟨Q, Q₀ ∪ {f.rule},
            f.result X u, sub', reachedF, ?_⟩, Congruent.refl _⟩, ⟨_, sub', reachedF⟩⟩
        rcases orientation with ⟨hm, ho⟩ | ⟨hm, ho⟩
        · exact Or.inl ⟨congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) hm,
            congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) ho⟩
        · exact Or.inr ⟨congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) hm,
            congrArg (fun p => (⟨p ∪ Q, f.result X u⟩ : Sys)) ho⟩
    rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only at programSame
      subst programSame
      have reached' : f.result X u = S's := reachedS
      subst reached'
      obtain ⟨T', moved, upTo, -⟩ := step P P' (Or.inl ⟨rfl, rfl⟩) (answers Q₀ u reached).1 f
        admitted
      exact ⟨T', moved, upTo⟩
    · simp only at programSame
      subst programSame
      have reached' : f.result X u = S's := reachedS
      subst reached'
      obtain ⟨T', moved, upTo, -⟩ := step P' P (Or.inr ⟨rfl, rfl⟩) (answers Q₀ u reached).2 f
        admitted
      exact ⟨T', moved, upTo⟩
  · rintro S T ⟨Q, Q₀, u, sub, reached, orient⟩ c applies
    refine ⟨1, ?_, ?_⟩
    · rw [Basic.rename_one]
      rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases c <;> exact applies
    · rw [Basic.rename_one]
      rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases c with
        | rows ids label =>
            exact ⟨Q, Q₀, _, sub, .rows ids (label PUnit.unit) reached applies, Or.inl ⟨rfl, rfl⟩⟩
        | rules added =>
            refine ⟨Q ∪ added, Q₀, u, sub.trans Set.subset_union_left, reached, Or.inl ⟨?_, ?_⟩⟩
            · show (⟨(P ∪ Q) ∪ added, u⟩ : Sys) = ⟨P ∪ (Q ∪ added), u⟩
              rw [Set.union_assoc]
            · show (⟨(P' ∪ Q) ∪ added, u⟩ : Sys) = ⟨P' ∪ (Q ∪ added), u⟩
              rw [Set.union_assoc]
        | tell equations =>
            exact ⟨Q, Q₀, _, sub, .tell (equations PUnit.unit) reached, Or.inl ⟨rfl, rfl⟩⟩
        | extend extension =>
            refine ⟨Q, Q₀, u, sub, reached, Or.inl ⟨?_, ?_⟩⟩
            · show (⟨P ∪ Q, extendState X E u (extension u.frame)⟩ : Sys) = ⟨P ∪ Q, u⟩
              rw [extendState_eq_self]
            · show (⟨P' ∪ Q, extendState X E u (extension u.frame)⟩ : Sys) = ⟨P' ∪ Q, u⟩
              rw [extendState_eq_self]
      · cases c with
        | rows ids label =>
            exact ⟨Q, Q₀, _, sub, .rows ids (label PUnit.unit) reached applies, Or.inr ⟨rfl, rfl⟩⟩
        | rules added =>
            refine ⟨Q ∪ added, Q₀, u, sub.trans Set.subset_union_left, reached, Or.inr ⟨?_, ?_⟩⟩
            · show (⟨(P' ∪ Q) ∪ added, u⟩ : Sys) = ⟨P' ∪ (Q ∪ added), u⟩
              rw [Set.union_assoc]
            · show (⟨(P ∪ Q) ∪ added, u⟩ : Sys) = ⟨P ∪ (Q ∪ added), u⟩
              rw [Set.union_assoc]
        | tell equations =>
            exact ⟨Q, Q₀, _, sub, .tell (equations PUnit.unit) reached, Or.inr ⟨rfl, rfl⟩⟩
        | extend extension =>
            refine ⟨Q, Q₀, u, sub, reached, Or.inr ⟨?_, ?_⟩⟩
            · show (⟨P' ∪ Q, extendState X E u (extension u.frame)⟩ : Sys) = ⟨P' ∪ Q, u⟩
              rw [extendState_eq_self]
            · show (⟨P ∪ Q, extendState X E u (extension u.frame)⟩ : Sys) = ⟨P ∪ Q, u⟩
              rw [extendState_eq_self]

/-- **Two bounded programs are congruent at a state exactly when they answer each other statically at
every configuration reachable from it.** -/
theorem congruent_iff_reachable {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P')
    (s : State Tm ℕ) :
    Cong ⟨P, s⟩ ⟨P', s⟩ ↔ ∀ Q u, Reachable P P' s Q u →
      AnswersStaticAt (P ∪ Q) (P' ∪ Q) u ∧ AnswersStaticAt (P' ∪ Q) (P ∪ Q) u := by
  refine ⟨fun related Q u reached => ?_, congruent_of_reachable⟩
  have config := congruent_of_reachable_config boundP boundP' related reached
  have finite := reachable_finite reached
  exact ⟨fun f admitted => answers_of_congruent (bounded_union boundP finite)
      (bounded_union boundP' finite) config f admitted,
    fun f admitted => answers_of_congruent (bounded_union boundP' finite)
      (bounded_union boundP finite) config.symm f admitted⟩

/-- **The congruence of systems, explicitly**: for bounded programs, `⟨P, s⟩` and `⟨P', t⟩` are
congruent exactly when `s` and `t` are statically equivalent and the programs answer each other
statically at every configuration reachable from `s`. -/
theorem congruent_iff_static_and_reachable {P P' : Program Tm} (boundP : Bounded P)
    (boundP' : Bounded P') (s t : State Tm ℕ) :
    Cong ⟨P, s⟩ ⟨P', t⟩ ↔ Static s t ∧ ∀ Q u, Reachable P P' s Q u →
      AnswersStaticAt (P ∪ Q) (P' ∪ Q) u ∧ AnswersStaticAt (P' ∪ Q) (P ∪ Q) u := by
  rw [congruent_iff_static_and_same boundP boundP', congruent_iff_reachable boundP boundP']

/-- **Only the program's own firings need answers**: a firing of an added rule is answered by itself. -/
theorem answersStaticAt_union_iff {P P' Q : Program Tm} {u : State Tm ℕ} :
    AnswersStaticAt (P ∪ Q) (P' ∪ Q) u ↔ AnswersStaticAt P (P' ∪ Q) u := by
  constructor
  · intro answers f admitted
    exact answers ⟨f.rule, Set.mem_union_left _ f.member, f.ext, f.opening, f.selection, f.seen⟩
      admitted
  · intro answers f admitted
    rcases f.member with inP | inQ
    · exact answers ⟨f.rule, inP, f.ext, f.opening, f.selection, f.seen⟩ admitted
    · exact ⟨⟨f.rule, Set.mem_union_right _ inQ, f.ext, f.opening, f.selection, f.seen⟩, admitted,
        static_refl _⟩

/-- **The general form with only the programs' own firings answered** (bounded `P`, `P'`): each
firing of `P` at a reachable configuration `(Q, u)` is answered statically by `P'` or by a rule the
context added, and each firing of `P'` likewise. -/
theorem congruent_iff_reachable_own {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P')
    (s : State Tm ℕ) :
    Cong ⟨P, s⟩ ⟨P', s⟩ ↔ ∀ Q u, Reachable P P' s Q u →
      AnswersStaticAt P (P' ∪ Q) u ∧ AnswersStaticAt P' (P ∪ Q) u := by
  rw [congruent_iff_reachable boundP boundP' s]
  simp only [answersStaticAt_union_iff]

#print axioms reachable_finite
#print axioms bounded_union
#print axioms congruent_of_reachable_config
#print axioms congruent_of_reachable
#print axioms congruent_iff_reachable
#print axioms congruent_iff_static_and_reachable
#print axioms answersStaticAt_union_iff
#print axioms congruent_iff_reachable_own

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
