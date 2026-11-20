import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms

/-!
# A held rule that mentions an unknown of the state: the closure's equations

Over first-order atoms at one frame. The code `watch` has one **parameter**, its own unknown `x`; it
takes a token `1`, guards `x = 5`, and makes a token `2`. It is held with the **state's** unknown
`x` as its argument: a rule that mentions an unknown of the state. When it fires, its parameter is
opened freshly (as `x₁`) and the closure's equation `x₁ ≐ x` joins the information.

* `bound_admitted`: when the state's knowledge binds its unknown to `5`, the rule fires: the guard is
  entailed by the knowledge, the take equation and the closure's equation together.
* `unbound_refused`: with the same rows and the same held rule and no knowledge about the unknown,
  the rule is refused: a solution may send the unknown elsewhere.

The two states differ by the one equation `x ≐ 5` of the knowledge. So a tell on an unknown that a
held rule mentions changes what that rule does at its next firing, through the closure's equations,
and nothing of the rule's label is rewritten.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Closure

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Examples (Tm X E x c shift)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **A rule with a parameter**: take a token `1`, guard that the parameter `x` is `5`, make `2`. -/
def watch : Spec Tm Unit Unit :=
  ⟨PUnit.unit, ⟨[c 1], [], [], [.equal x (c 5)], [c 2]⟩, [], [x], [], [], [], [], []⟩

/-- The code system with the one code `watch`. -/
def codes : Codes Tm Unit Unit := ⟨fun _ => watch, fun _ _ _ => False, fun _ _ _ => none⟩

/-- A token `1` at row `0`, the given knowledge, and `watch` held with the state's unknown `x` as its
argument. -/
def closing (knowledge : EquationStore (Term atoms)) : RState Tm ℕ ℕ Unit Unit :=
  ⟨⟨PUnit.unit, knowledge, {0}, fun _ => c 1⟩, {0}, fun _ => ⟨(), [x], .persistent, ()⟩⟩

/-- The held rule fires with its parameter opened as `x₁`: it takes the token and makes row `1`. -/
def watchFiring (knowledge : EquationStore (Term atoms)) :
    RFiring ℕ ℕ E codes (closing knowledge) :=
  ⟨.held 0, PUnit.unit, shift, ⟨[0], [], [1]⟩, [], [], [], [], []⟩

/-- The closure's equation: the opened parameter with the state's unknown. -/
theorem watch_env (knowledge : EquationStore (Term atoms)) :
    (watchFiring knowledge).env X = [(.var 1, x)] := rfl

theorem bound_information :
    (watchFiring [(x, c 5)]).information X = [(x, c 5), (c 1, c 1), (.var 1, x)] := rfl

theorem unbound_information :
    (watchFiring []).information X = [(c 1, c 1), (.var 1, x)] := rfl

theorem bound_fresh : (watchFiring [(x, c 5)]).Fresh X := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t ((member | member | ⟨o, -, rfl⟩) | ⟨ρ, -, member⟩)
    · have inside : t ∈ [x] := member
      obtain rfl := List.mem_singleton.mp inside
      rfl
    · have inside : t ∈ [c 5] := member
      obtain rfl := List.mem_singleton.mp inside
      rfl
    · rfl
    · have inside : t ∈ [x] := member
      obtain rfl := List.mem_singleton.mp inside
      rfl
  · intro t member
    have inside : t ∈ watch.terms := member
    simp [watch, Spec.terms, Rule.terms, checkTerms] at inside
    rcases inside with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The rule fires when the knowledge binds the unknown it mentions.** -/
theorem bound_admitted : (watchFiring [(x, c 5)]).Admits X (∅ : Set Unit) := by
  refine ⟨⟨bound_fresh, ⟨List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩,
    ⟨Finset.mem_singleton_self 0, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩⟩, ?_, ?_, ?_⟩
  · apply enabled_of <;> simp [watchFiring, closing]
  · rw [bound_information]
    refine ⟨PUnit.unit, fun _ => c 5, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · rw [bound_information]
    intro b σ solved
    have bound : σ 0 = c 5 := solved (x, c 5) List.mem_cons_self
    have closure : σ 1 = σ 0 :=
      solved (.var 1, x) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro check member
      have inside : check ∈ [Check.equal (Term.var 1 : Term atoms) (c 5)] := member
      obtain rfl := List.mem_singleton.mp inside
      exact closure.trans bound
    · intro q member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil

/-- **Without that knowledge the same held rule is refused.** -/
theorem unbound_refused : ¬ (watchFiring []).Admits X (∅ : Set Unit) := by
  intro admitted
  have asks := admitted.2.2.2
  rw [unbound_information] at asks
  have holds := asks PUnit.unit (fun _ => c 6) (fun e member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)
  have guard : c 6 = c 5 :=
    holds.1.1 (Check.equal (Term.var 1 : Term atoms) (c 5)) (List.mem_singleton_self _)
  exact absurd (Term.const.inj guard) (by decide)

/-- **The label is not rewritten**: after the firing the rule is held with the same argument. -/
theorem bound_result_holds :
    ((watchFiring [(x, c 5)]).result X).held 0 = ⟨(), [x], .persistent, ()⟩ := rfl

#print axioms bound_admitted
#print axioms unbound_refused
#print axioms bound_result_holds

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Closure
