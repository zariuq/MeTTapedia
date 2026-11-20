import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Modulo
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.ProgramLaws

/-!
# A told equation that the rule already entails is a no-op

The rule `withTell r e` tells `e` besides the tells of `r`. When the tells of `r` entail `e`, and
both sides of `e` are terms that the results of `r` keep (`keptTerms`: patterns, tells and made
rows), the two rules are interchangeable beside every program, at every state
(`entailedTell_congruent`): their firings with one opening and selection are admitted together, and
their results differ only by an equation with no new solutions and no new support, so they are
equivalent modulo the knowledge (Law 2).

Both hypotheses are needed, at one frame (`TellReadControls`): an equation the tells do not entail
refuses firings (`AtOneFrame.tell_not_entailed_separated`), and the rule that tells `y = y`, with `y`
its own unknown that its results do not otherwise keep, entails that equation yet reserves the unknown
it is opened as, which a context can then see (`AtOneFrame.tell_unkept_separated`). An instance:
`AtOneFrame.tell_example`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- The terms of a rule that its results keep: patterns, tells and made rows. -/
def keptTerms (r : Rule Tm) : List (Tm r.locals) :=
  r.body.take ++ r.body.read ++ r.body.tell.map Prod.fst ++ r.body.tell.map Prod.snd ++ r.body.produce

theorem keptTerms_subset (r : Rule Tm) (u : Tm r.locals) (inside : u ∈ keptTerms r) :
    u ∈ r.terms := by
  unfold keptTerms at inside
  unfold Rule.terms
  simp only [List.mem_append] at inside ⊢
  tauto

/-- The rule with one more told equation. -/
abbrev withTell (r : Rule Tm) (e : Equation (Tm r.locals)) : Rule Tm :=
  ⟨r.locals, ⟨r.body.take, r.body.read, e :: r.body.tell, r.body.checks, r.body.produce⟩, r.collect⟩

section Law

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

omit [DecidableEq O] in
theorem resultTerms_eq {P : Program Tm} {a : Obj} (f : Firing O E P a) :
    resultTerms X f = (keptTerms f.rule).map (X.act f.opening) := by
  simp [resultTerms, keptTerms, Firing.opened, RuleInstance.map, List.map_append, List.map_map]
  rfl

/-- **A told equation already entailed is a no-op**: when the tells of `r` entail `e` and the sides of
`e` are terms the results keep, `withTell r e` and `r` are interchangeable beside every program. -/
theorem entailedTell_congruent
    (invariant : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {r : Rule Tm} {e : Equation (Tm r.locals)}
    (entailed : X.Entails r.body.tell (fun _ h => X.E (X.act h e.1) (X.act h e.2)))
    (leftKept : e.1 ∈ keptTerms r) (rightKept : e.2 ∈ keptTerms r) (Q : Program Tm)
    (s : State Tm O) : Congruent X O E obs ⟨Q ∪ {withTell r e}, s⟩ ⟨Q ∪ {r}, s⟩ := by
  have termsCases : ∀ u : Tm r.locals, u ∈ (withTell r e).terms → u ∈ r.terms ∨ u = e.1 ∨ u = e.2 := by
    intro u inside
    simp only [Rule.terms, List.mem_append, List.map_cons, List.mem_cons] at inside ⊢
    tauto
  have termsMono : ∀ u : Tm r.locals, u ∈ r.terms → u ∈ (withTell r e).terms := by
    intro u inside
    simp only [Rule.terms, List.mem_append, List.map_cons, List.mem_cons] at inside ⊢
    tauto
  have terms : ∀ u : Tm r.locals, u ∈ (withTell r e).terms ↔ u ∈ r.terms := fun u =>
    ⟨fun inside => by
      rcases termsCases u inside with old | rfl | rfl
      · exact old
      · exact keptTerms_subset r _ leftKept
      · exact keptTerms_subset r _ rightKept, termsMono u⟩
  have keptCases : ∀ v : Tm r.locals, v ∈ keptTerms (withTell r e) →
      v ∈ keptTerms r ∨ v = e.1 ∨ v = e.2 := by
    intro v inside
    simp only [keptTerms, List.mem_append, List.map_cons, List.mem_cons] at inside ⊢
    tauto
  have keptMono : ∀ v : Tm r.locals, v ∈ keptTerms r → v ∈ keptTerms (withTell r e) := by
    intro v inside
    simp only [keptTerms, List.mem_append, List.map_cons, List.mem_cons] at inside ⊢
    tauto
  -- Along any opening, a solution of the opened tells of `r` solves the opened `e`.
  have told : ∀ {a b : Obj} (σ : Hom a b) (ι : Hom r.locals a),
      X.Models σ (r.body.tell.map fun pair => (X.act ι pair.1, X.act ι pair.2)) →
      X.E (X.act σ (X.act ι e.1)) (X.act σ (X.act ι e.2)) := by
    intro a b σ ι solved
    have composite : X.Models (X.comp σ ι) r.body.tell := by
      intro e' member
      have opened := solved _ (List.mem_map.mpr ⟨e', member, rfl⟩)
      show X.E (X.act (X.comp σ ι) e'.1) (X.act (X.comp σ ι) e'.2)
      rw [X.act_comp, X.act_comp]
      exact opened
    have holds : X.E (X.act (X.comp σ ι) e.1) (X.act (X.comp σ ι) e.2) :=
      entailed b (X.comp σ ι) composite
    rw [X.act_comp, X.act_comp] at holds
    exact holds
  -- One opening and selection: the two firings.
  have step : ∀ (s : State Tm O) (ext : E.Ext s.frame) (ι : Hom r.locals (E.target ext))
      (selection : Selection O) (seen : List (Finset O)),
      ((step X O E ({withTell r e} : Program Tm)).Admits (s := s)
          (⟨withTell r e, Set.mem_singleton _, ext, ι, selection, seen⟩ :
            Firing O E ({withTell r e} : Program Tm) s.frame) ↔
        (step X O E ({r} : Program Tm)).Admits (s := s)
          (⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩ : Firing O E ({r} : Program Tm) s.frame)) ∧
      ((step X O E ({withTell r e} : Program Tm)).Admits (s := s)
          (⟨withTell r e, Set.mem_singleton _, ext, ι, selection, seen⟩ :
            Firing O E ({withTell r e} : Program Tm) s.frame) →
        Modulo X ((⟨withTell r e, Set.mem_singleton _, ext, ι, selection, seen⟩ :
            Firing O E ({withTell r e} : Program Tm) s.frame).result X s)
          ((⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩ :
            Firing O E ({r} : Program Tm) s.frame).result X s)) := by
    intro s ext ι selection seen
    let f : Firing O E ({withTell r e} : Program Tm) s.frame :=
      ⟨withTell r e, Set.mem_singleton _, ext, ι, selection, seen⟩
    let g : Firing O E ({r} : Program Tm) s.frame := ⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩
    -- The informations have the same solutions.
    have equivalent : X.Equivalent (f.information X s) (g.information X s) := by
      intro b σ
      constructor
      · intro solved e' inside
        rcases (mem_information g).mp inside with old | take | read | tells
        · exact solved e' ((mem_information f).mpr (Or.inl old))
        · exact solved e' ((mem_information f).mpr (Or.inr (Or.inl take)))
        · exact solved e' ((mem_information f).mpr (Or.inr (Or.inr (Or.inl read))))
        · exact solved e' ((mem_information f).mpr
            (Or.inr (Or.inr (Or.inr (List.mem_cons_of_mem _ tells)))))
      · intro solved e' inside
        rcases (mem_information f).mp inside with old | take | read | tells
        · exact solved e' ((mem_information g).mpr (Or.inl old))
        · exact solved e' ((mem_information g).mpr (Or.inr (Or.inl take)))
        · exact solved e' ((mem_information g).mpr (Or.inr (Or.inr (Or.inl read))))
        · rcases List.mem_cons.mp tells with rfl | later
          · exact told σ ι (fun e'' member =>
              solved e'' ((mem_information g).mpr (Or.inr (Or.inr (Or.inr member)))))
          · exact solved e' ((mem_information g).mpr (Or.inr (Or.inr (Or.inr later))))
    have freshIff : f.Fresh X s ↔ g.Fresh X s := by
      constructor
      · intro fresh b g' h
        obtain ⟨u, state, rule⟩ := fresh b g' h
        exact ⟨u, state, fun v inside => rule v ((terms v).mpr inside)⟩
      · intro fresh b g' h
        obtain ⟨u, state, rule⟩ := fresh b g' h
        exact ⟨u, state, fun v inside => rule v ((terms v).mp inside)⟩
    have admitsIff : f.Admits X s ↔ g.Admits X s := by
      refine and_congr (and_congr freshIff Iff.rfl) (and_congr Iff.rfl (and_congr
        (Frames.Equivalent.solvable_iff equivalent) (Frames.Equivalent.entails_iff equivalent _)))
    refine ⟨admitsIff, fun admitted => ?_⟩
    have admittedG : g.Admits X s := admitsIff.mp admitted
    refine ⟨g.information X s, relabel (g.row X s) selection.made (g.opened X).produce,
      ⟨equivalent, fun o _ b σ _ => (X.equivalence b).refl _, fun b φ ψ => ?_⟩, rfl⟩
    have sameTerms : (∀ u ∈ resultTerms X f, X.E (X.act φ u) (X.act ψ u)) ↔
        ∀ u ∈ resultTerms X g, X.E (X.act φ u) (X.act ψ u) := by
      rw [resultTerms_eq f, resultTerms_eq g]
      constructor
      · intro agree u inside
        obtain ⟨v, member, rfl⟩ := List.mem_map.mp inside
        exact agree _ (List.mem_map.mpr ⟨v, keptMono v member, rfl⟩)
      · intro agree u inside
        obtain ⟨v, member, rfl⟩ := List.mem_map.mp inside
        rcases keptCases v member with old | rfl | rfl
        · exact agree _ (List.mem_map.mpr ⟨_, old, rfl⟩)
        · exact agree _ (List.mem_map.mpr ⟨_, leftKept, rfl⟩)
        · exact agree _ (List.mem_map.mpr ⟨_, rightKept, rfl⟩)
    exact (supports_result admitted.1 admitted.2.1 φ ψ).trans
      ((and_congr Iff.rfl sameTerms).trans (supports_result admittedG.1 admittedG.2.1 φ ψ).symm)
  have forward : Answers X O E obs ({withTell r e} : Program Tm) {r} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = withTell r e := member
    subst rule
    obtain ⟨admitsIff, results⟩ := step s ext ι selection seen
    exact ⟨⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩, admitsIff.mp admitted,
      fun P => modulo_congruent invariant P (results admitted)⟩
  have backward : Answers X O E obs ({r} : Program Tm) {withTell r e} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = r := member
    subst rule
    obtain ⟨admitsIff, results⟩ := step s ext ι selection seen
    have admittedF := admitsIff.mpr admitted
    exact ⟨⟨withTell r e, Set.mem_singleton _, ext, ι, selection, seen⟩, admittedF,
      fun P => modulo_congruent invariant P (results admittedF).symm⟩
  have replaced := replace_congruent forward backward Q s
  rw [Set.union_comm, Set.union_comm ({r} : Program Tm)] at replaced
  exact replaced

end Law

#print axioms keptTerms_subset
#print axioms resultTerms_eq
#print axioms entailedTell_congruent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
