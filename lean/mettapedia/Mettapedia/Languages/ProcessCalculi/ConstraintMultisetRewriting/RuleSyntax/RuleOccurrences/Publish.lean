import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms

/-!
# Publishing a closed row is a firing that makes a rule occurrence

Over first-order atoms at one frame. The code system (`codes`) has every rule of the present step as
a code, and the **publisher**; the closed row of a term under a knowledge is the rule that tells that
knowledge and makes that term (`Spec.closedRow`, `Codes.close`).

**The publisher** (`publisher`) reads a row `x` and publishes it: its firing makes a rule occurrence
whose code is the closed row of the opened `x` under the firing's information, with no arguments.

* **Published, then bound** (`publish_admitted`, `published_holds`, `free_copy_admitted`,
  `original_bound`, `free_copy_not_bound`): the row is labelled by an unknown that nothing binds; the
  publisher fires and the result holds the closed row; then an equation binding the publisher's
  unknown to `5` is told. The closed row still fires, with its unknowns opened apart, and the copy it
  makes is **not** bound: the knowledge after it has a solution that sends the publisher's unknown to
  `5` and the copy to `7`. A tell made after the publication does not reach the published row.
* **Bound, then published** (`publish_bound_admitted`, `published_bound_holds`,
  `bound_copy_admitted`, `bound_copy_bound`): the knowledge binds the unknown to `5` before the
  publication. The closed row then carries that equation, and every solution of the knowledge after
  its firing sends the copy to `5`.

So a published row carries the knowledge its publisher had and nothing later. The other way of making
a rule, a code with arguments (`Spec.makes`), shares the arguments' unknowns with the state: such a
rule is reached by a later tell (`Closure.bound_admitted`, `Closure.unbound_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

universe uO uT uOcc uR uC uZ

/-- **Tell equations to a state that holds rules**: they join the knowledge; the rows and the held
rules stay. -/
def RState.tell {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc} {R : Type uR} {C : Type uC}
    {Z : Type uZ} (s : RState Tm O R C Z) (equations : EquationStore (Tm s.frame)) :
    RState Tm O R C Z :=
  { s with knowledge := s.knowledge ++ equations }

namespace Publish

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Examples (Tm X E x c shift)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## The code system -/

/-- The codes: a rule of the present step, or the publisher. -/
inductive Code where
  | rule (r : Rule Tm)
  | publisher

/-- **The publisher**: read a row `x` and publish it as a closed row, persistently. -/
def publisher : Spec Tm Code Unit :=
  ⟨PUnit.unit, ⟨[], [x], [], [], []⟩, [], [], [], [], [], [], [(x, .persistent, ())]⟩

/-- The code system: every rule is a code, and the closed row of a term under a knowledge is the
rule that tells the knowledge and makes the term. -/
def codes : Codes Tm Code Unit where
  unfold
    | .rule r => Spec.ofRule r
    | .publisher => publisher
  denotes _ _ _ := False
  close a knowledge t := some (.rule (Spec.closedRow a knowledge t))

/-- The opening that moves every unknown ten places up. -/
def far : Subst atoms := fun v => Term.var (v + 10)

/-! ## Published, then bound -/

/-- A row labelled by the unknown `x`, the given knowledge, and the publisher held. -/
def start (knowledge : EquationStore (Term atoms)) : RState Tm ℕ ℕ Code Unit :=
  ⟨⟨PUnit.unit, knowledge, {0}, fun _ => x⟩, {0}, fun _ => ⟨Code.publisher, [], .persistent, ()⟩⟩

/-- The publisher reads the row, with its own `x` opened as `x₁`, and publishes it at identity `5`. -/
def publishFiring (knowledge : EquationStore (Term atoms)) : RFiring ℕ ℕ E codes (start knowledge) :=
  ⟨.held 0, PUnit.unit, shift, ⟨[], [0], []⟩, [], [5], [], [],
    [Code.rule (Spec.closedRow PUnit.unit (knowledge ++ [(.var 1, x)]) (.var 1))]⟩

theorem publish_information : (publishFiring []).information X = [(.var 1, x)] := rfl

theorem publish_fresh : (publishFiring []).Fresh X := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t ((member | member | ⟨o, -, rfl⟩) | ⟨held, -, member⟩)
    · exact absurd member List.not_mem_nil
    · exact absurd member List.not_mem_nil
    · rfl
    · exact absurd member List.not_mem_nil
  · intro t member
    have inside : t ∈ publisher.terms := member
    simp [publisher, Spec.terms, Rule.terms] at inside
    subst inside
    rfl

/-- **Publication is a firing.** -/
theorem publish_admitted : (publishFiring []).Admits X (∅ : Set Code) := by
  refine ⟨⟨publish_fresh, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ⟨Finset.mem_singleton_self 0, rfl, rfl, List.nodup_singleton 5, rfl, ?_, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩⟩, ?_, ?_, ?_⟩
  · intro ρ inside held
    obtain rfl := List.mem_singleton.mp inside
    exact absurd (Finset.mem_singleton.mp held) (by decide)
  · apply enabled_of <;> simp [publishFiring, start]
  · rw [publish_information]
    exact ⟨PUnit.unit, fun _ => c 0, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · intro b σ _
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      have inside : y ∈ [(((x, Mode.persistent, ()) : Term atoms × Mode × Unit),
          Code.rule (Spec.closedRow PUnit.unit ([] ++ [(.var 1, x)]) (.var 1)))] := member
      obtain rfl := List.mem_singleton.mp inside
      rfl

/-- The closed row published under no knowledge: it tells the read equation and makes the row. -/
def freeRow : Rule Tm := Spec.closedRow PUnit.unit [(.var 1, x)] (.var 1)

/-- **The result holds the closed row**, with no arguments. -/
theorem published_holds :
    ((publishFiring []).result X).held 5 = ⟨Code.rule freeRow, [], .persistent, ()⟩ := rfl

theorem published_mem_rules : 5 ∈ ((publishFiring []).result X).rules :=
  (RFiring.mem_result_rules _).mpr (Or.inr (List.mem_singleton_self 5))

/-- The state after the publication and a later tell that binds the publisher's unknown to `5`. -/
def later : RState Tm ℕ ℕ Code Unit := ((publishFiring []).result X).tell [(x, c 5)]

theorem later_knowledge : later.knowledge = [(.var 1, x), (x, c 5)] := rfl

/-- **The publisher's unknown is bound.** -/
theorem original_bound (σ : Subst atoms) (solved : action.Models σ later.knowledge) : σ 0 = c 5 :=
  solved (x, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)

theorem later_closed : later.Closed := by
  intro ρ inside
  have member : ρ ∈ ((publishFiring []).result X).rules := inside
  rcases (RFiring.mem_result_rules _).mp member with kept | made
  · rw [RFiring.kept_persistent (publishFiring []) rfl rfl rfl] at kept
    obtain rfl := Finset.mem_singleton.mp kept
    rfl
  · obtain rfl := List.mem_singleton.mp made
    rfl

/-- The closed row fires, with its unknowns opened ten places up, and makes row `7`. -/
def useFree : RFiring ℕ ℕ E codes later :=
  ⟨.held 5, PUnit.unit, far, ⟨[], [], [7]⟩, [], [], [], [], []⟩

theorem useFree_information :
    useFree.base.information X later.toState =
      [(.var 1, x), (x, c 5), (.var 11, .var 10)] := rfl

theorem useFree_base_admitted : useFree.base.Admits X later.toState := by
  refine ⟨⟨?_, List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 10 then h 0 else if v = 11 then h 1 else g v, ?_, ?_⟩
    · rintro t (member | member | ⟨o, -, rfl⟩)
      · have inside : t ∈ [(Term.var 1 : Term atoms), x] := member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with isTerm | isTerm <;> rw [isTerm] <;> rfl
      · have inside : t ∈ [x, c 5] := member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with isTerm | isTerm <;> rw [isTerm] <;> rfl
      · rfl
    · intro t member
      have inside : t ∈ [(Term.var 1 : Term atoms), x, Term.var 1] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with isTerm | isTerm | isTerm <;> rw [isTerm] <;> rfl
  · apply enabled_of
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      obtain rfl := List.mem_singleton.mp inside
      have present : later.toState.present = {0} := rfl
      rw [present]
      decide
  · rw [useFree_information]
    refine ⟨PUnit.unit, fun v => if v = 10 then c 7 else if v = 11 then c 7 else c 5,
      fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with isEquation | isEquation | isEquation <;> rw [isEquation] <;> rfl
  · intro b σ _
    exact ⟨fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩

/-- **The published row still fires after the later tell.** -/
theorem free_copy_admitted : useFree.Admits X (∅ : Set Code) :=
  (useFree.admits_plain X later_closed (Spec.plain_ofRule freeRow) ∅).mpr
    ⟨useFree_base_admitted, published_mem_rules, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- The copy is the row at identity `7`, labelled by a new unknown. -/
theorem free_copy_label : (useFree.result X).label 7 = .var 11 := rfl

/-- **The copy is not bound by the later tell**: after its firing, some solution of the knowledge
sends the publisher's unknown to `5` and the copy to `7`. -/
theorem free_copy_not_bound :
    ∃ σ : Subst atoms, action.Models σ (useFree.result X).knowledge ∧ σ 0 = c 5 ∧
      action.apply σ ((useFree.result X).label 7) = c 7 := by
  refine ⟨fun v => if v = 10 then c 7 else if v = 11 then c 7 else c 5, ?_, rfl, rfl⟩
  intro e member
  have inside : e ∈ [((Term.var 1 : Term atoms), x), (x, c 5), (Term.var 11, Term.var 10)] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with isEquation | isEquation | isEquation <;> rw [isEquation] <;> rfl

/-! ## Bound, then published -/

theorem publish_bound_information :
    (publishFiring [(x, c 5)]).information X = [(x, c 5), (.var 1, x)] := rfl

theorem publish_bound_fresh : (publishFiring [(x, c 5)]).Fresh X := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t ((member | member | ⟨o, -, rfl⟩) | ⟨held, -, member⟩)
    · have inside : t ∈ [x] := member
      obtain rfl := List.mem_singleton.mp inside
      rfl
    · have inside : t ∈ [c 5] := member
      obtain rfl := List.mem_singleton.mp inside
      rfl
    · rfl
    · exact absurd member List.not_mem_nil
  · intro t member
    have inside : t ∈ publisher.terms := member
    simp [publisher, Spec.terms, Rule.terms] at inside
    subst inside
    rfl

/-- **Publication after the binding.** -/
theorem publish_bound_admitted : (publishFiring [(x, c 5)]).Admits X (∅ : Set Code) := by
  refine ⟨⟨publish_bound_fresh, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ⟨Finset.mem_singleton_self 0, rfl, rfl, List.nodup_singleton 5, rfl, ?_, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩⟩, ?_, ?_, ?_⟩
  · intro ρ inside held
    obtain rfl := List.mem_singleton.mp inside
    exact absurd (Finset.mem_singleton.mp held) (by decide)
  · apply enabled_of <;> simp [publishFiring, start]
  · rw [publish_bound_information]
    refine ⟨PUnit.unit, fun _ => c 5, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with isEquation | isEquation <;> rw [isEquation] <;> rfl
  · intro b σ _
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      have inside : y ∈ [(((x, Mode.persistent, ()) : Term atoms × Mode × Unit),
          Code.rule (Spec.closedRow PUnit.unit ([(x, c 5)] ++ [(.var 1, x)]) (.var 1)))] := member
      obtain rfl := List.mem_singleton.mp inside
      rfl

/-- The closed row published under the knowledge that binds the unknown: it carries that equation. -/
def boundRow : Rule Tm := Spec.closedRow PUnit.unit [(x, c 5), (.var 1, x)] (.var 1)

/-- **The result holds the closed row with the publisher's knowledge.** -/
theorem published_bound_holds :
    ((publishFiring [(x, c 5)]).result X).held 5 = ⟨Code.rule boundRow, [], .persistent, ()⟩ := rfl

theorem published_bound_mem_rules : 5 ∈ ((publishFiring [(x, c 5)]).result X).rules :=
  (RFiring.mem_result_rules _).mpr (Or.inr (List.mem_singleton_self 5))

theorem published_bound_closed : ((publishFiring [(x, c 5)]).result X).Closed := by
  intro ρ inside
  rcases (RFiring.mem_result_rules _).mp inside with kept | made
  · rw [RFiring.kept_persistent (publishFiring [(x, c 5)]) rfl rfl rfl] at kept
    obtain rfl := Finset.mem_singleton.mp kept
    rfl
  · obtain rfl := List.mem_singleton.mp made
    rfl

/-- The closed row fires, with its unknowns opened ten places up, and makes row `7`. -/
def useBound : RFiring ℕ ℕ E codes ((publishFiring [(x, c 5)]).result X) :=
  ⟨.held 5, PUnit.unit, far, ⟨[], [], [7]⟩, [], [], [], [], []⟩

theorem useBound_information :
    useBound.base.information X ((publishFiring [(x, c 5)]).result X).toState =
      [(x, c 5), (.var 1, x), (.var 10, c 5), (.var 11, .var 10)] := rfl

theorem useBound_base_admitted :
    useBound.base.Admits X ((publishFiring [(x, c 5)]).result X).toState := by
  refine ⟨⟨?_, List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 10 then h 0 else if v = 11 then h 1 else g v, ?_, ?_⟩
    · rintro t (member | member | ⟨o, -, rfl⟩)
      · have inside : t ∈ [x, (Term.var 1 : Term atoms)] := member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with isTerm | isTerm <;> rw [isTerm] <;> rfl
      · have inside : t ∈ [c 5, x] := member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with isTerm | isTerm <;> rw [isTerm] <;> rfl
      · rfl
    · intro t member
      have inside : t ∈ [x, (Term.var 1 : Term atoms), c 5, x, Term.var 1] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with isTerm | isTerm | isTerm | isTerm | isTerm <;> rw [isTerm] <;> rfl
  · apply enabled_of
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      obtain rfl := List.mem_singleton.mp inside
      have present : ((publishFiring [(x, c 5)]).result X).toState.present = {0} := rfl
      rw [present]
      decide
  · rw [useBound_information]
    refine ⟨PUnit.unit, fun _ => c 5, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with isEquation | isEquation | isEquation | isEquation <;> rw [isEquation] <;> rfl
  · intro b σ _
    exact ⟨fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩

theorem bound_copy_admitted : useBound.Admits X (∅ : Set Code) :=
  (useBound.admits_plain X published_bound_closed (Spec.plain_ofRule boundRow) ∅).mpr
    ⟨useBound_base_admitted, published_bound_mem_rules, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- **The copy carries the binding its publisher had**: every solution of the knowledge after its
firing sends the copy to `5`. -/
theorem bound_copy_bound (σ : Subst atoms)
    (solved : action.Models σ (useBound.result X).knowledge) :
    action.apply σ ((useBound.result X).label 7) = c 5 := by
  have known : (useBound.result X).knowledge =
      [(x, c 5), (.var 1, x), (.var 10, c 5), (.var 11, .var 10)] := rfl
  rw [known] at solved
  have copy : σ 11 = σ 10 :=
    solved (.var 11, .var 10)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have carried : σ 10 = c 5 :=
    solved (.var 10, c 5) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact copy.trans carried

#print axioms publish_admitted
#print axioms published_holds
#print axioms original_bound
#print axioms free_copy_admitted
#print axioms free_copy_label
#print axioms free_copy_not_bound
#print axioms publish_bound_admitted
#print axioms published_bound_holds
#print axioms bound_copy_admitted
#print axioms bound_copy_bound

end Publish

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
