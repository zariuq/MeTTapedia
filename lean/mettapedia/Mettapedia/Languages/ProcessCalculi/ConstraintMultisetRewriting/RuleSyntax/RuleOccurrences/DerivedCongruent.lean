import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Modulo

/-!
# A derived rule adds nothing: the run and the derived firing end in congruent states

`Derived.derived_firing` matches every firing of a derived link by a run of two firings whose result
agrees with it away from one missing identity and has one more equation `m ≐ m` in its knowledge, `m`
a term that every substitution fixes.

* `modulo_of_agree`: two such states are **equivalent modulo the knowledge** in the sense of
  `Equivalence.Modulo` (the same rows, knowledge with the same solutions, labels of present rows equal,
  and the same support: the extra equation mentions only a term that every instantiation fixes).
* **`derived_congruent`**: so, by the law that states equivalent modulo the knowledge are congruent
  (`Equivalence.modulo_congruent_mayBarb`), the result of the derived firing and the result of the
  run are **congruent with every program**: in every context they show the same barbs and answer each
  other's reductions.

* `step_with_derived`: with infinitely many identities, one firing of the program with the derived
  link is a run of one or two firings of the program without it, ending in a congruent state.
* **`reach_with_derived`**: every state that the program with the derived link reaches is congruent,
  beside the program, to a state that the program without it reaches. The converse inclusion is plain:
  every firing of a program is a firing of every larger program.

The instances over first-order atoms are `Atoms.derived_congruent_token` and
`Atoms.reach_with_derived_token`, with `Atoms.derived_result_reached` for existence; the control of a
rule that is not derived is `Derived.Atoms.no_four` with `Derived.Atoms.stray_makes_four`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open OneFrame (Terms frames ext)
open LogicOverTheStep.StepSpan (Succ)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (Modulo Congruent MayBarb modulo_congruent_mayBarb System Reaches Reduces reprogram)

section Link

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO}

/-- **States that agree away from a missing identity, one with an extra equation between a fixed term
and itself, are equivalent modulo the knowledge.** -/
theorem modulo_of_agree {m : T} (groundM : ∀ σ : S, A.apply σ m = m) {via : O}
    {u v : State (Terms T) O} (agree : Agree A via u v)
    (knowledge : u.knowledge = v.knowledge ++ [(m, m)]) (missing : via ∉ v.present) :
    Modulo (frames A) v u := by
  obtain ⟨present, labels, solutions⟩ := agree
  obtain ⟨uframe, uknow, upresent, ulabel⟩ := u
  obtain ⟨vframe, vknow, vpresent, vlabel⟩ := v
  simp only at present labels solutions knowledge missing
  subst present knowledge
  have fixed : ∀ (b : PUnit.{1}) (φ ψ : S),
      (frames A).E ((frames A).act (a := vframe) (b := b) φ m)
        ((frames A).act (a := vframe) (b := b) ψ m) := by
    intro b φ ψ
    show A.E (A.apply φ m) (A.apply ψ m)
    rw [groundM φ, groundM ψ]
    exact A.equivalence.refl _
  refine ⟨vknow ++ [(m, m)], ulabel, ⟨fun b σ => (solutions b σ).symm, ?_, ?_⟩, rfl⟩
  · intro o inside b σ _
    have other : o ≠ via := fun same => missing (same ▸ inside)
    show A.E (A.apply σ (vlabel o)) (A.apply σ (ulabel o))
    rw [labels o other]
    exact A.equivalence.refl _
  · intro b φ ψ
    constructor
    · intro supports t mentioned
      rcases mentioned with inFst | inSnd | ⟨o, inside, rfl⟩
      · have split : t ∈ vknow.map Prod.fst ∨ t ∈ [m] := by
          have whole : t ∈ vknow.map Prod.fst ++ [m] := by
            have mapped : (vknow ++ [(m, m)]).map Prod.fst = vknow.map Prod.fst ++ [m] :=
              List.map_append
            rw [← mapped]
            exact inFst
          exact List.mem_append.mp whole
        rcases split with old | new
        · exact supports t (Or.inl old)
        · rw [List.mem_singleton.mp new]
          exact fixed b φ ψ
      · have split : t ∈ vknow.map Prod.snd ∨ t ∈ [m] := by
          have whole : t ∈ vknow.map Prod.snd ++ [m] := by
            have mapped : (vknow ++ [(m, m)]).map Prod.snd = vknow.map Prod.snd ++ [m] :=
              List.map_append
            rw [← mapped]
            exact inSnd
          exact List.mem_append.mp whole
        rcases split with old | new
        · exact supports t (Or.inr (Or.inl old))
        · rw [List.mem_singleton.mp new]
          exact fixed b φ ψ
      · have other : o ≠ via := fun same => missing (same ▸ inside)
        show (frames A).E ((frames A).act φ (ulabel o)) ((frames A).act ψ (ulabel o))
        rw [labels o other]
        exact supports (vlabel o) (Or.inr (Or.inr ⟨o, inside, rfl⟩))
    · intro supports t mentioned
      rcases mentioned with inFst | inSnd | ⟨o, inside, rfl⟩
      · refine supports t (Or.inl ?_)
        show t ∈ (vknow ++ [(m, m)]).map Prod.fst
        rw [List.map_append]
        exact List.mem_append_left _ inFst
      · refine supports t (Or.inr (Or.inl ?_))
        show t ∈ (vknow ++ [(m, m)]).map Prod.snd
        rw [List.map_append]
        exact List.mem_append_left _ inSnd
      · have other : o ≠ via := fun same => missing (same ▸ inside)
        exact supports (vlabel o) (Or.inr (Or.inr ⟨o, inside, labels o other⟩))

variable [DecidableEq O]

/-- **A derived link adds nothing**: every admitted firing of the derived link is matched by a run of
the two links it is derived from, and the two results are congruent with every program. -/
theorem derived_congruent {P : Program (Terms T)} {a m b : T} (groundA : ∀ σ : S, A.apply σ a = a)
    (groundM : ∀ σ : S, A.apply σ m = m) (groundB : ∀ σ : S, A.apply σ b = b)
    (first : link a m ∈ P) (second : link m b ∈ P) (s : State (Terms T) O)
    (g : Firing O (ext A) P s.frame) (fires : g.rule = link a b) (admitted : g.Admits (frames A) s)
    {via : O} (missing : via ∉ s.present) (other : via ∉ g.selection.made) (Q : Program (Terms T)) :
    ∃ (g₁ : Firing O (ext A) P s.frame) (g₂ : Firing O (ext A) P (g₁.result (frames A) s).frame),
      g₁.rule = link a m ∧ g₁.Admits (frames A) s ∧ g₂.rule = link m b ∧
        g₂.Admits (frames A) (g₁.result (frames A) s) ∧
          Congruent (frames A) O (ext A) (MayBarb (frames A)) ⟨Q, g.result (frames A) s⟩
            ⟨Q, g₂.result (frames A) (g₁.result (frames A) s)⟩ := by
  obtain ⟨g₁, g₂, rule₁, admitted₁, rule₂, admitted₂, agree, knowledge⟩ :=
    derived_firing A groundA groundM groundB first second s g fires admitted missing other
  have gone : via ∉ (g.result (frames A) s).present := by
    intro inside
    rcases mem_fire.mp inside with ⟨old, -⟩ | made
    · exact missing old
    · exact other (List.mem_toFinset.mp made)
  exact ⟨g₁, g₂, rule₁, admitted₁, rule₂, admitted₂,
    modulo_congruent_mayBarb Q (modulo_of_agree A groundM agree knowledge gone)⟩

/-! ## Reachable states -/

omit [DecidableEq O] in
/-- A run of the step of a program, as a run of the system with that program. -/
theorem reaches_of_run [DecidableEq O] {P : Program (Terms T)} {s t : State (Terms T) O}
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t) :
    Reaches (frames A) O (ext A) ⟨P, s⟩ ⟨P, t⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ moved ih => exact ih.tail ⟨rfl, moved⟩

omit [DecidableEq O] in
/-- A run of a system keeps its program and is a run of the step of that program. -/
theorem run_of_reaches [DecidableEq O] {P : Program (Terms T)} {s : State (Terms T) O}
    {U : System (Terms T) O} (reached : Reaches (frames A) O (ext A) ⟨P, s⟩ U) :
    U.program = P ∧ Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s U.state := by
  induction reached with
  | refl => exact ⟨rfl, .refl⟩
  | @tail V W _ moved ih =>
      obtain ⟨program, run⟩ := ih
      obtain ⟨same, step⟩ := moved
      refine ⟨same.trans program, run.tail ?_⟩
      rw [program] at step
      exact step

variable [Infinite O]

/-- **One firing of the program with the derived link is a run of the program without it**, of one or
two firings, ending in a state congruent to its result with every program. -/
theorem step_with_derived {P : Program (Terms T)} {a m b : T} (groundA : ∀ σ : S, A.apply σ a = a)
    (groundM : ∀ σ : S, A.apply σ m = m) (groundB : ∀ σ : S, A.apply σ b = b)
    (first : link a m ∈ P) (second : link m b ∈ P) {s t : State (Terms T) O}
    (moved : Succ (step (frames A) O (ext A) (P ∪ {link a b})).toStep s t) (Q : Program (Terms T)) :
    ∃ u, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s u ∧
      Congruent (frames A) O (ext A) (MayBarb (frames A)) ⟨Q, t⟩ ⟨Q, u⟩ := by
  obtain ⟨g, admitted, rfl⟩ := moved
  have rule : g.rule ∈ P ∨ g.rule = link a b := g.member
  rcases rule with inP | derived
  · exact ⟨g.result (frames A) s, .single ⟨reprogram g inP, admitted, rfl⟩, Congruent.refl _⟩
  · obtain ⟨via, fresh⟩ := Infinite.exists_notMem_finset (s.present ∪ g.selection.made.toFinset)
    have missing : via ∉ s.present := fun inside => fresh (Finset.mem_union_left _ inside)
    have other : via ∉ g.selection.made := fun inside =>
      fresh (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))
    obtain ⟨g₁, g₂, rule₁, admitted₁, rule₂, admitted₂, congruent⟩ :=
      derived_congruent A groundA groundM groundB (Or.inl first) (Or.inl second) s g derived admitted
        missing other Q
    have in₁ : g₁.rule ∈ P := by
      rw [rule₁]
      exact first
    have in₂ : g₂.rule ∈ P := by
      rw [rule₂]
      exact second
    exact ⟨g₂.result (frames A) (g₁.result (frames A) s),
      Relation.ReflTransGen.tail (.single ⟨reprogram g₁ in₁, admitted₁, rfl⟩)
        ⟨reprogram g₂ in₂, admitted₂, rfl⟩, congruent⟩

/-- **A derived link adds no reachable state**: every state that the program with the derived link
reaches is congruent, beside the program, to a state that the program without it reaches. -/
theorem reach_with_derived {P : Program (Terms T)} {a m b : T} (groundA : ∀ σ : S, A.apply σ a = a)
    (groundM : ∀ σ : S, A.apply σ m = m) (groundB : ∀ σ : S, A.apply σ b = b)
    (first : link a m ∈ P) (second : link m b ∈ P) {s t : State (Terms T) O}
    (reached : Relation.ReflTransGen (Succ (step (frames A) O (ext A) (P ∪ {link a b})).toStep) s t) :
    ∃ u, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s u ∧
      Congruent (frames A) O (ext A) (MayBarb (frames A)) ⟨P, t⟩ ⟨P, u⟩ := by
  induction reached with
  | refl => exact ⟨s, .refl, Congruent.refl _⟩
  | tail _ moved ih =>
      obtain ⟨u, reachedU, related⟩ := ih
      obtain ⟨v, reachedV, relatedV⟩ :=
        step_with_derived A groundA groundM groundB first second moved P
      obtain ⟨W, reachedW, relatedW⟩ := related.reaches (reaches_of_run A reachedV)
      obtain ⟨program, runW⟩ := run_of_reaches A reachedW
      obtain ⟨Wprogram, Wstate⟩ := W
      simp only at program runW
      subst program
      exact ⟨Wstate, reachedU.trans runW, relatedV.trans relatedW⟩

end Link

namespace Atoms

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **The instance**: at the token, the firing of the link from `1` to `3` and the run through `2`
end in states that are congruent with every program. -/
theorem derived_congruent_token (Q : Program Tm) :
    ∃ (g₁ : Firing ℕ E withDerived Examples.tokenState.frame)
      (g₂ : Firing ℕ E withDerived (g₁.result X Examples.tokenState).frame),
      g₁.rule = link (c 1) (c 2) ∧ g₁.Admits X Examples.tokenState ∧ g₂.rule = link (c 2) (c 3) ∧
        g₂.Admits X (g₁.result X Examples.tokenState) ∧
          Congruent X ℕ E (MayBarb X)
            ⟨Q, (tokenFiring (P := withDerived) 3 (Or.inr rfl)).result X Examples.tokenState⟩
            ⟨Q, g₂.result X (g₁.result X Examples.tokenState)⟩ :=
  derived_congruent action (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inl (Or.inl rfl))
    (Or.inl (Or.inr rfl)) Examples.tokenState _ rfl derived_admitted (via := 2) (by decide)
    (by decide) Q

/-- **From the token, the derived link reaches nothing new**: every state the chain with the derived
link reaches is congruent, beside the chain, to a state the chain reaches. -/
theorem reach_with_derived_token {t : State Tm ℕ}
    (reached : Relation.ReflTransGen (Succ (step X ℕ E withDerived).toStep) Examples.tokenState t) :
    ∃ u, Relation.ReflTransGen (Succ (step X ℕ E chain).toStep) Examples.tokenState u ∧
      Congruent X ℕ E (MayBarb X) ⟨chain, t⟩ ⟨chain, u⟩ :=
  reach_with_derived action (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inl rfl) (Or.inr rfl)
    reached

/-- Such a state exists: the result of the derived firing is reached. -/
theorem derived_result_reached :
    Relation.ReflTransGen (Succ (step X ℕ E withDerived).toStep) Examples.tokenState
      ((tokenFiring (P := withDerived) 3 (Or.inr rfl)).result X Examples.tokenState) :=
  .single ⟨tokenFiring 3 (Or.inr rfl), derived_admitted, rfl⟩

#print axioms derived_congruent_token
#print axioms reach_with_derived_token
#print axioms derived_result_reached

end Atoms

#print axioms modulo_of_agree
#print axioms derived_congruent
#print axioms step_with_derived
#print axioms reach_with_derived

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived
