import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Exec

/-!
# The bag without members, under each candidate

At the one frame (`OneAfterAnother.admits_nil_iff_consistent`, `OneAfterAnother.result_nil`) the bag
without members is jointly admissible exactly when the knowledge is solvable, and its result is the state
itself. Were it a step, every state with solvable knowledge would have a step to itself, and a state where
nothing fires would run forever. `bagStep` asks for a member. With members:

* **any compatible bag**, guards at each member's own information: the bag step stops exactly where the
  step of the program stops (`Members.can_fire_iff`); guards at the joint information: it may fire where
  the step of the program has stopped (`Knowledge.stopped_and_fires`), a difference of what is committed,
  not of an idle step;
* **`every`** (`nil_every_iff`): the empty bag is `every` exactly when the knowledge is solvable and no
  firing of the rules is admitted. It commits nothing, so `every` with no match is no step of the bag step.
  An exec of MM2 with no match is still one step (`exec_without_match`): its kernel takes the exec row;
* **a maximal bag** (`nil_maximal_iff`): the empty bag is maximal exactly when the knowledge is solvable
  and no bag of distinct matches with a member is admitted: where the bag step has stopped.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open OneFrame (Terms frames ext)

section Empty

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]
  {P : Program (Terms T)}

/-- **The empty bag is complete exactly when no firing of the rules is admitted.** -/
theorem nil_complete_iff (s : State (Terms T) O) (Q : Set (Rule (Terms T))) :
    (bagOf A ([] : List (OneMember A O P))).Complete (frames A) s Q ↔
      ∀ g : Firing O (ext A) P s.frame, g.rule ∈ Q → ¬ g.Admits (frames A) s := by
  constructor
  · intro complete g inQ admitted
    exact absurd (complete g inQ admitted) List.not_mem_nil
  · intro none g inQ admitted
    exact absurd admitted (none g inQ)

/-- The empty bag is admitted with each member's guards at its own information exactly when it is
admitted. -/
theorem nil_admitsOwn_iff (s : State (Terms T) O) :
    (bagOf A ([] : List (OneMember A O P))).AdmitsOwn (frames A) s ↔
      (bagOf A ([] : List (OneMember A O P))).Admits (frames A) s :=
  ⟨Bag.admits_of_admitsOwn (frames A), fun admitted =>
    ⟨admitted.1, admitted.2.1, admitted.2.2.1, fun _ inside => absurd inside List.not_mem_nil⟩⟩

/-- **`every` with no match**: the empty bag is `every` over the rules exactly when the knowledge is
solvable and no firing of the rules is admitted. -/
theorem nil_every_iff (s : State (Terms T) O) (Q : Set (Rule (Terms T))) :
    (bagOf A ([] : List (OneMember A O P))).AdmitsEvery (frames A) s Q ↔
      A.Consistent s.knowledge ∧ ∀ g : Firing O (ext A) P s.frame, g.rule ∈ Q → ¬ g.Admits (frames A) s := by
  constructor
  · rintro ⟨own, -, -, complete⟩
    exact ⟨(admits_nil_iff_consistent A s).mp ((nil_admitsOwn_iff A s).mp own),
      (nil_complete_iff A s Q).mp complete⟩
  · rintro ⟨consistent, none⟩
    exact ⟨(nil_admitsOwn_iff A s).mpr ((admits_nil_iff_consistent A s).mpr consistent),
      fun _ inside => absurd inside List.not_mem_nil, List.nodup_nil, (nil_complete_iff A s Q).mpr none⟩

/-- **The empty bag is maximal exactly where no bag of distinct matches with a member is admitted.** -/
theorem nil_maximal_iff (s : State (Terms T) O) :
    (bagOf A ([] : List (OneMember A O P))).AdmitsMaximal (frames A) s ↔
      A.Consistent s.knowledge ∧
        ¬ ∃ f : Bag O (ext A) P s.frame, f.Admits (frames A) s ∧ f.Distinct ∧ f.members ≠ [] := by
  rw [Bag.admitsMaximal_iff, admits_nil_iff_consistent]
  constructor
  · rintro ⟨consistent, -, none⟩
    refine ⟨consistent, fun ⟨f, admitted, distinct, nonempty⟩ => none ⟨f, admitted, distinct,
      fun _ inside => absurd inside List.not_mem_nil, ?_⟩⟩
    obtain ⟨m, inside⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨m.key, List.mem_map_of_mem inside, List.not_mem_nil⟩
  · rintro ⟨consistent, none⟩
    refine ⟨consistent, List.nodup_nil, ?_⟩
    rintro ⟨f, admitted, distinct, -, k, inside, -⟩
    refine none ⟨f, admitted, distinct, fun empty => ?_⟩
    rw [empty] at inside
    exact absurd inside List.not_mem_nil

end Empty

/-! ## An exec with no match is one step -/

section NoMatch

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open ExecStep
open ExecControls (items items_presented items_consume)

/-- **An exec with no match is one step of `every`**: at the space holding only the exec, the exec's
result is empty, a step of `every` over its program exists, has a member (the kernel), and has that
result. -/
theorem exec_without_match :
    items.step {100} 100 = ∅ ∧
      ∃ f : Bag ℕ E (program items 100) PUnit.unit,
        f.AdmitsEveryAsSet X (space {100}) (program items 100) ∧ f.members ≠ [] ∧
          (f.result X (space {100})).present = ∅ := by
  have addsNew : ∀ σ ∈ items.solutions {100}, Disjoint (items.adds σ) {100} := by
    intro σ solution
    cases σ <;> simp [items] at solution
  obtain ⟨⟨f, every⟩, all⟩ := exec_is_every items_presented items_consume (S := {100}) (e := 100)
    (by decide) addsNew
  refine ⟨by decide, f, every, fun empty => ?_, (all f every).1.trans (by decide)⟩
  have listed := every.2.2 (kernelMember items 100).firing (Or.inl rfl)
    (kernelMember_admitted items (S := {100}) (by decide))
  rw [empty] at listed
  exact absurd listed List.not_mem_nil

end NoMatch

#print axioms nil_complete_iff
#print axioms nil_admitsOwn_iff
#print axioms nil_every_iff
#print axioms nil_maximal_iff
#print axioms exec_without_match

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
