import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Congruence

/-!
# Laws of programs: union, rules that never fire, entailed guards

For every frame action, extensions and barb family.

* **Union of rule sets is idempotent, commutative and associative** (`union_comm_congruent`,
  `union_assoc_congruent`, `union_self_congruent`). A program is a set of rules, so these hold on the
  nose; the step depends on a program only through which rules belong to it.
* **A rule that never fires may be dropped** (`neverFires_congruent`). The condition is on the rule
  alone (`NeverFires`): every solution of its own tells falsifies one of its equation guards (this
  includes rules whose tells are unsolvable). Such a rule is admitted at no state
  (`not_admits_of_neverFires`), so no context can make it fire. The condition cannot be weakened to
  "it fires at no state the system reaches": a rule waiting for a row that only a context adds fires in
  that context (`AtOneFrame.dormant_rule_separated`).
* **An entailed equation guard may be dropped** (`entailedGuard_congruent`): when the rule's own tells
  entail the guard and the guard's two terms are terms of the rule, the rule with and without the guard
  are interchangeable in every program. Entailment is needed: a guard the tells do not entail refuses
  firings (`AtOneFrame.guard_not_entailed_separated`). The terms hypothesis is about freshness, since
  an opening is fresh on every term of its rule, and whether it is needed depends on the frame's
  supply of unknowns: at the frame with one unknown the law fails without it
  (`AtOneUnknown.guard_terms_needed`: the guard `v = v` on the rule that makes `5` refuses every firing
  at a state that mentions `v`), and what that frame lacks is a fresh unknown, since no rule with `v`
  among its terms fires there, guard or no guard (`AtOneUnknown.fresh_supply_needed`); at the one
  frame over first-order terms with the numbers as unknowns, with function symbols or without, it is
  not needed (`AtFirstOrder.entailedGuard_congruent_firstOrder`, and for the flat signature
  `AtOneFrame.entailedGuard_congruent_oneFrame`: an opening can send the guard's new unknowns apart
  from everything the state mentions, and an entailed guard may be dropped whatever its terms).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)

universe uO uT uH uE uOcc uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

/-! ## Union of rule sets -/

theorem union_comm_congruent (P Q : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨P ∪ Q, s⟩ ⟨Q ∪ P, s⟩ := by
  rw [Set.union_comm]
  exact Congruent.refl _

theorem union_assoc_congruent (P Q R : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨(P ∪ Q) ∪ R, s⟩ ⟨P ∪ (Q ∪ R), s⟩ := by
  rw [Set.union_assoc]
  exact Congruent.refl _

theorem union_self_congruent (P : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨P ∪ P, s⟩ ⟨P, s⟩ := by
  rw [Set.union_self]
  exact Congruent.refl _

/-! ## A rule that never fires -/

variable (X) in
/-- **A rule that never fires**: every solution of its own tells falsifies one of its equation
guards. -/
def NeverFires (r : Rule Tm) : Prop :=
  ∀ (b : Obj) (h : Hom r.locals b), X.Models h r.body.tell →
    ∃ l t, Check.equal l t ∈ r.body.checks ∧ ¬ X.E (X.act h l) (X.act h t)

/-- **Such a rule is admitted at no state**: a solution of a firing's information is, along the
opening, a solution of the rule's tells, and there the guard fails. -/
theorem not_admits_of_neverFires {r : Rule Tm} (dead : NeverFires X r) {P : Program Tm}
    {s : State Tm O} (f : Firing O E P s.frame) (rule : f.rule = r) : ¬ f.Admits X s := by
  subst rule
  intro admitted
  obtain ⟨-, -, -, ⟨b, σ, solved⟩, checks, -⟩ := (admits_iff f).mp admitted
  have told : X.Models (X.comp σ f.opening) f.rule.body.tell := by
    intro e member
    have opened : X.Solves σ (X.act f.opening e.1, X.act f.opening e.2) :=
      Firing.tell_solved f solved (List.mem_map.mpr ⟨e, member, rfl⟩)
    show X.E (X.act (X.comp σ f.opening) e.1) (X.act (X.comp σ f.opening) e.2)
    rw [X.act_comp, X.act_comp]
    exact opened
  obtain ⟨l, t, member, fails⟩ := dead b (X.comp σ f.opening) told
  have holds : X.E (X.act σ (X.act f.opening l)) (X.act σ (X.act f.opening t)) :=
    checks (Check.equal (X.act f.opening l) (X.act f.opening t))
      (List.mem_map.mpr ⟨.equal l t, member, rfl⟩) b σ solved
  rw [X.act_comp, X.act_comp] at fails
  exact fails holds

/-- **A rule that never fires may be dropped**, beside every program and at every state. -/
theorem neverFires_congruent {r : Rule Tm} (dead : NeverFires X r) (Q : Program Tm)
    (s : State Tm O) : Congruent X O E obs ⟨Q ∪ {r}, s⟩ ⟨Q, s⟩ := by
  have replaced := replace_congruent (X := X) (E := E) (obs := obs) (P₁ := {r}) (P₂ := ∅)
    (fun s f admitted => absurd admitted (not_admits_of_neverFires dead f f.member))
    (fun _ f _ => absurd f.member (Set.notMem_empty _)) Q s
  rw [Set.union_comm, Set.empty_union] at replaced
  exact replaced

/-! ## An entailed equation guard -/

/-- The rule with one more equation guard. -/
abbrev withGuard (r : Rule Tm) (l t : Tm r.locals) : Rule Tm :=
  ⟨r.locals, ⟨r.body.take, r.body.read, r.body.tell, .equal l t :: r.body.checks, r.body.produce⟩,
    r.collect⟩

theorem mem_withGuard_terms (r : Rule Tm) (l t : Tm r.locals) (u : Tm r.locals) :
    u ∈ (withGuard r l t).terms ↔ u ∈ r.terms ∨ u = l ∨ u = t := by
  simp only [Rule.terms, withGuard, List.flatMap_cons, checkTerms, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  tauto

/-- **An entailed equation guard may be dropped**: when the rule's tells entail the guard and its two
terms are terms of the rule, the rule with and without the guard are interchangeable beside every
program, at every state. -/
theorem entailedGuard_congruent {r : Rule Tm} {l t : Tm r.locals}
    (entailed : X.Entails r.body.tell (fun _ h => X.E (X.act h l) (X.act h t)))
    (leftTerm : l ∈ r.terms) (rightTerm : t ∈ r.terms) (Q : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨Q ∪ {withGuard r l t}, s⟩ ⟨Q ∪ {r}, s⟩ := by
  -- Both rules have the same frame, takes, reads, tells, made rows and collect query.
  have terms : ∀ u : Tm r.locals, u ∈ (withGuard r l t).terms ↔ u ∈ r.terms := fun u => by
    rw [mem_withGuard_terms]
    constructor
    · rintro (inside | rfl | rfl)
      · exact inside
      · exact leftTerm
      · exact rightTerm
    · exact fun inside => Or.inl inside
  -- The guard holds at every solution of a firing's information.
  have guard : ∀ {a b : Obj} (σ : Hom a b) (ι : Hom r.locals a)
      (told : X.Models σ (r.body.tell.map fun pair => (X.act ι pair.1, X.act ι pair.2))),
      X.E (X.act σ (X.act ι l)) (X.act σ (X.act ι t)) := by
    intro a b σ ι told
    have solved : X.Models (X.comp σ ι) r.body.tell := by
      intro e member
      have opened := told _ (List.mem_map.mpr ⟨e, member, rfl⟩)
      show X.E (X.act (X.comp σ ι) e.1) (X.act (X.comp σ ι) e.2)
      rw [X.act_comp, X.act_comp]
      exact opened
    have holds : X.E (X.act (X.comp σ ι) l) (X.act (X.comp σ ι) t) := entailed b (X.comp σ ι) solved
    rw [X.act_comp, X.act_comp] at holds
    exact holds
  -- Firings of the two rules with one opening and selection are admitted together, with one result.
  have same : ∀ (s : State Tm O) (ext : E.Ext s.frame) (ι : Hom r.locals (E.target ext))
      (selection : Selection O) (seen : List (Finset O)),
      (step X O E ({withGuard r l t} : Program Tm)).Admits (s := s)
          (⟨withGuard r l t, Set.mem_singleton _, ext, ι, selection, seen⟩ :
            Firing O E ({withGuard r l t} : Program Tm) s.frame) ↔
        (step X O E ({r} : Program Tm)).Admits (s := s)
          (⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩ :
            Firing O E ({r} : Program Tm) s.frame) := by
    intro s ext ι selection seen
    rw [admits_iff, admits_iff]
    have fresh : (⟨withGuard r l t, Set.mem_singleton _, ext, ι, selection, seen⟩ :
          Firing O E ({withGuard r l t} : Program Tm) s.frame).Fresh X s ↔
        (⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩ :
          Firing O E ({r} : Program Tm) s.frame).Fresh X s := by
      constructor
      · intro fresh b g h
        obtain ⟨u, state, rule⟩ := fresh b g h
        exact ⟨u, state, fun v inside => rule v ((terms v).mpr inside)⟩
      · intro fresh b g h
        obtain ⟨u, state, rule⟩ := fresh b g h
        exact ⟨u, state, fun v inside => rule v ((terms v).mp inside)⟩
    rw [fresh]
    constructor
    · rintro ⟨freshness, shapes, enabled, solvable, checks, collect⟩
      refine ⟨freshness, shapes, enabled, solvable, fun c member => checks c ?_, collect⟩
      exact List.mem_cons_of_mem _ member
    · rintro ⟨freshness, shapes, enabled, solvable, checks, collect⟩
      refine ⟨freshness, shapes, enabled, solvable, fun c member => ?_, collect⟩
      rcases List.mem_cons.mp member with rfl | later
      · intro b σ solved
        exact guard σ ι (fun e inside => solved e (List.mem_append_right _ inside))
      · exact checks c later
  have forward : Answers X O E obs ({withGuard r l t} : Program Tm) {r} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = withGuard r l t := member
    subst rule
    exact ⟨⟨r, Set.mem_singleton _, ext, ι, selection, seen⟩, (same s ext ι selection seen).mp admitted,
      fun _ => Congruent.refl _⟩
  have backward : Answers X O E obs ({r} : Program Tm) {withGuard r l t} := by
    rintro s ⟨rule, member, ext, ι, selection, seen⟩ admitted
    have isRule : rule = r := member
    subst rule
    exact ⟨⟨withGuard r l t, Set.mem_singleton _, ext, ι, selection, seen⟩,
      (same s ext ι selection seen).mpr admitted, fun _ => Congruent.refl _⟩
  have replaced := replace_congruent forward backward Q s
  rw [Set.union_comm, Set.union_comm ({r} : Program Tm)] at replaced
  exact replaced

#print axioms union_comm_congruent
#print axioms union_assoc_congruent
#print axioms union_self_congruent
#print axioms not_admits_of_neverFires
#print axioms neverFires_congruent
#print axioms mem_withGuard_terms
#print axioms entailedGuard_congruent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
