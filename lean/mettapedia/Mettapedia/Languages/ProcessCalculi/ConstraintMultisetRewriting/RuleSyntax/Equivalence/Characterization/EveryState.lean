import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Instances

/-!
# Congruence of programs at the empty store is congruence at every state

At one frame every state is reached from the empty store by a context: add its rows, then tell its
knowledge. The result is statically equivalent to the state (`static_built`). Hence two programs are
congruent at the empty store exactly when they are congruent at every state (`congruent_empty_iff`),
and, for bounded programs, exactly when they answer each other statically (`congruent_empty_iff_answers`).
A firing without a static answer at `s` gives the separating context: `build s` (`separated_by_build`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong empty)

/-- The context that builds a state from the empty store: its rows, then its knowledge. -/
def build (s : State Tm ℕ) : List (Basic Tm ℕ E) :=
  [.rows s.present (fun _ o => s.label o), .tell (fun _ => s.knowledge)]

theorem appliesAll_build (s : State Tm ℕ) (P : Program Tm) :
    AppliesAll X (build s) (⟨P, empty⟩ : Sys) :=
  .cons (Finset.disjoint_empty_right _) (.cons (Basic.applies_of_ids_empty rfl _) (.nil _))

/-- **The state built from the empty store is statically equivalent to the state.** -/
theorem static_built (s : State Tm ℕ) (P : Program Tm) :
    Static (applyAll X (build s) (⟨P, empty⟩ : Sys)).state s := by
  obtain ⟨frame, knowledge, present, label⟩ := s
  apply static_of_modulo
  refine ⟨knowledge, label, ⟨fun b σ => ?_, fun o inside b σ _ => ?_, fun b φ ψ => ?_⟩, ?_⟩
  · show X.Models σ ([] ++ knowledge) ↔ X.Models σ knowledge
    rw [List.nil_append]
  · have present' : o ∈ present := by simpa [build, applyAll, Basic.apply, addRows, tellState,
      empty] using inside
    show X.E (X.act σ (if o ∈ present then label o else c 0)) (X.act σ (label o))
    rw [if_pos present']
    exact (X.equivalence b).refl _
  · cases b
    rw [supports_iff_vars, supports_iff_vars]
    have sameMentions : ∀ w, (applyAll X (build ⟨frame, knowledge, present, label⟩)
        (⟨P, empty⟩ : Sys)).state.Mentions (.var w) ↔
        (⟨(applyAll X (build ⟨frame, knowledge, present, label⟩) (⟨P, empty⟩ : Sys)).state.frame,
          knowledge, (applyAll X (build ⟨frame, knowledge, present, label⟩) (⟨P, empty⟩ : Sys)).state.present,
          label⟩ : State Tm ℕ).Mentions (.var w) := by
      intro w
      constructor
      · rintro (inside | inside | ⟨o, inside, same⟩)
        · exact Or.inl (by simpa [build, applyAll, Basic.apply, tellState, addRows, empty] using inside)
        · exact Or.inr (Or.inl (by simpa [build, applyAll, Basic.apply, tellState, addRows, empty]
            using inside))
        · have present' : o ∈ present := by simpa [build, applyAll, Basic.apply, addRows, tellState,
            empty] using inside
          refine Or.inr (Or.inr ⟨o, inside, ?_⟩)
          have relabelled : (if o ∈ present then label o else c 0) = .var w := same
          rw [if_pos present'] at relabelled
          exact relabelled
      · rintro (inside | inside | ⟨o, inside, same⟩)
        · exact Or.inl (by simpa [build, applyAll, Basic.apply, tellState, addRows, empty] using inside)
        · exact Or.inr (Or.inl (by simpa [build, applyAll, Basic.apply, tellState, addRows, empty]
            using inside))
        · have present' : o ∈ present := by simpa [build, applyAll, Basic.apply, addRows, tellState,
            empty] using inside
          refine Or.inr (Or.inr ⟨o, inside, ?_⟩)
          show (if o ∈ present then label o else c 0) = .var w
          rw [if_pos present']
          exact same
    constructor
    · intro agree w mentions
      exact agree w ((sameMentions w).mpr mentions)
    · intro agree w mentions
      exact agree w ((sameMentions w).mp mentions)
  · show (⟨frame, knowledge, present, label⟩ : State Tm ℕ) =
      ⟨PUnit.unit, knowledge, ∅ ∪ present, label⟩
    rw [Finset.empty_union]

/-- **Two programs are congruent at the empty store exactly when they are congruent at every
state.** -/
theorem congruent_empty_iff {P P' : Program Tm} :
    Cong ⟨P, empty⟩ ⟨P', empty⟩ ↔ ∀ s : State Tm ℕ, Cong ⟨P, s⟩ ⟨P', s⟩ := by
  constructor
  · intro related s
    have built := related.applyAll_same (fun π p s => mayBarb_renameState X π p s)
      (fun related p => mayBarb_modulo related p) (appliesAll_build s P) (appliesAll_build s P')
    have left : Cong ⟨P, (applyAll X (build s) (⟨P, empty⟩ : Sys)).state⟩ ⟨P, s⟩ :=
      congruent_of_static P (static_built s P)
    have right : Cong ⟨P', (applyAll X (build s) (⟨P', empty⟩ : Sys)).state⟩ ⟨P', s⟩ :=
      congruent_of_static P' (static_built s P')
    exact left.symm.trans (built.trans right)
  · intro related
    exact related empty

/-- **For bounded programs, congruence at the empty store is mutual static answering.** -/
theorem congruent_empty_iff_answers {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P') :
    Cong ⟨P, empty⟩ ⟨P', empty⟩ ↔ AnswersStatic P P' ∧ AnswersStatic P' P :=
  congruent_empty_iff.trans (programs_iff boundP boundP')

/-- **The separating context, computed**: when a firing of `P` at `s` has no statically equivalent
answer by `P'` at `s`, the context `build s` (the rows of `s`, then its knowledge) separates the two
bounded programs from the empty store. -/
theorem separated_by_build {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P')
    {s : State Tm ℕ} (f : Firing ℕ E P s.frame) (admitted : f.Admits X s)
    (unanswered : ¬ ∃ g : Firing ℕ E P' s.frame, g.Admits X s ∧
      Static (f.result X s) (g.result X s)) :
    ¬ Cong (applyAll X (build s) (⟨P, empty⟩ : Sys)) (applyAll X (build s) (⟨P', empty⟩ : Sys)) := by
  intro built
  have left : Cong ⟨P, (applyAll X (build s) (⟨P, empty⟩ : Sys)).state⟩ ⟨P, s⟩ :=
    congruent_of_static P (static_built s P)
  have right : Cong ⟨P', (applyAll X (build s) (⟨P', empty⟩ : Sys)).state⟩ ⟨P', s⟩ :=
    congruent_of_static P' (static_built s P')
  exact unanswered
    (answers_of_congruent boundP boundP' (left.symm.trans (built.trans right)) f admitted)

#print axioms appliesAll_build
#print axioms static_built
#print axioms congruent_empty_iff
#print axioms congruent_empty_iff_answers
#print axioms separated_by_build

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
