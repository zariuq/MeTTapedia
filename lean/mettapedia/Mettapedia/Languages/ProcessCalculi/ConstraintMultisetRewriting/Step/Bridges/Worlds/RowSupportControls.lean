import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.RowSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.SupportControls

/-!
# Support observations of actual world and persistent-rule executions

An inconsistent state has a physical row but its support function returns
the empty set. It fails the settled support observation for every proposed
answer. The positive controls use the existing admitted propagation firing
that reads `a` and makes `b`, both in a world and through a persistent held
rule. A separate infinite execution records the limit of support erasure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.RowSupport.Controls

open Mettapedia.Logic.LP
open RuleSyntax RuleSyntax.Worlds RuleSyntax.RuleOccurrences
open RuleSyntax.StepWeb.Support RuleSyntax.StepWeb.Support.Controls
open RuleSyntax.SetStoreSyntax
open OneFrame (Terms)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

/-- A physical occurrence survives even though its knowledge is contradictory. -/
def inconsistent : State (Terms (Term atoms)) ℕ :=
  ⟨PUnit.unit, [(a, b)], {0}, fun _ => a⟩

theorem inconsistent_has_row : 0 ∈ inconsistent.present ∧ inconsistent.label 0 = a :=
  ⟨Finset.mem_singleton_self 0, rfl⟩

theorem inconsistent_has_no_model :
    ¬ (FirstOrder.action atoms).Consistent inconsistent.knowledge := by
  rintro ⟨answer, solved⟩
  have same := solved (a, b) (List.mem_singleton_self _)
  change a = b at same
  exact b_ne_a same.symm

theorem inconsistent_unification_rejected : unifyTotal inconsistent.knowledge = none := by
  simp [inconsistent, a, b, unifyTotal]

theorem inconsistent_support_empty : support inconsistent = ∅ := by
  simp only [support, inconsistent_unification_rejected]

theorem inconsistent_not_settled : ¬ Settled inconsistent := by
  rintro ⟨answer, accepted, _⟩
  rw [inconsistent_unification_rejected] at accepted
  contradiction

/-- A failed principal reading is never accepted as an empty support result. -/
theorem inconsistent_reading_refused (rows : Finset (Term atoms)) :
    ¬ ReadsSupport rows inconsistent :=
  fun reading => inconsistent_not_settled reading.1

private theorem grow_union_propagates :
    ∀ rule ∈ (∅ : Program (Terms (Term atoms))) ∪ growProgram, Propagates rule := by
  simpa only [Set.empty_union] using grow_pure

/-- The existing admitted read/make firing changes the actual singleton world. -/
theorem grow_world_firing :
    Fires (events X ℕ E) (singleton ∅ growProgram oneA)
      (singleton ∅ growProgram (growFiring.result X oneA)) := by
  apply (one_world_bisimulation (X := X) (E := E) (O := ℕ) ∅ growProgram).zig
  simpa only [Set.empty_union] using (grow_steps .afterTells).1

theorem grow_world_result : ReadsSupport {a, b} (growFiring.result X oneA) :=
  ⟨result_settled growFiring grow_pure oneA_settled growFiring_admitted, growFiring_support⟩

theorem grow_changes_support : support oneA ≠ support (growFiring.result X oneA) := by
  rw [oneA_support, growFiring_support]
  intro same
  have inside : b ∈ ({a} : Finset (Term atoms)) :=
    same ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  exact b_ne_a (Finset.mem_singleton.mp inside)

/-- The generic support bridge is exercised with an actual changed set step. -/
theorem grow_world_support_reachable (timing : SetStore.AskTiming) :
    Reaches (events X ℕ E) (ReadsSupport {a, b}) (singleton ∅ growProgram oneA) := by
  apply (singleton_support_reachable_iff timing grow_union_propagates
    (Equiv.refl ℕ) oneA_settled {a, b}).mpr
  have moved : SetStore.Step timing growProgram {a} {a, b} :=
    disciplined_is_step (grow_steps timing).2
  simpa only [Set.empty_union, oneA_support] using Relation.ReflTransGen.single moved

private def growCode (_ : Fin 1) : Rule (Terms (Term atoms)) := grow
private def growZone (_ : Fin 1) : Unit := ()

private theorem grow_offers : Offers growProgram (Finset.univ : Finset (Fin 1)) growCode := by
  intro rule
  constructor
  · intro member
    exact ⟨0, Finset.mem_univ _, (Set.mem_singleton_iff.mp member).symm⟩
  · rintro ⟨_, _, same⟩
    exact Set.mem_singleton_iff.mpr same.symm

/-- A genuine persistent rule, with its actual offered code, reaches the same
support through the existing admitted held-rule step. -/
theorem grow_held_support_reachable (timing : SetStore.AskTiming) :
    ∃ after, Relation.ReflTransGen
        (LogicOverTheStep.StepSpan.Succ (rstep X ℕ (Fin 1) E (ofRules Unit) ∅).toStep)
        (holding oneA Finset.univ growCode growZone) after ∧ ReadsSupport {a, b} after.toState := by
  apply (held_support_reachable_iff growZone grow_offers timing grow_union_propagates
    (Equiv.refl ℕ) oneA_settled {a, b}).mpr
  have moved : SetStore.Step timing growProgram {a} {a, b} :=
    disciplined_is_step (grow_steps timing).2
  simpa only [Set.empty_union, oneA_support] using Relation.ReflTransGen.single moved

/-- An actual infinite world execution may erase to a terminal support. The
finite reachability comparisons do not assert divergence reflection. -/
theorem world_divergence_set_terminal (timing : SetStore.AskTiming) :
    (∃ run : ℕ → Bag (Terms (Term atoms)) ℕ,
      run 0 = singleton ∅ againProgram oneA ∧
        ∀ n, Fires (events X ℕ E) (run n) (run (n + 1))) ∧
      ∀ after, ¬ SetStore.Step timing againProgram {a} after := by
  obtain ⟨⟨run, initial, moves⟩, terminal⟩ := again_diverges timing
  refine ⟨⟨fun n => singleton ∅ againProgram (run n), ?_, ?_⟩, terminal⟩
  · exact congrArg (singleton ∅ againProgram) initial
  · intro n
    apply (one_world_bisimulation (X := X) (E := E) (O := ℕ) ∅ againProgram).zig
    simpa only [Set.empty_union] using moves n

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.RowSupport.Controls
