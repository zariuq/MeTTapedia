import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeStepBisimControls

/-!
# Carrying live firings up to dead names is not total

The interface's `Transport` moves every firing along every isomorphism of states. Along a dead-name
extension, live firings are carried from the smaller state to the larger (`Inclusion.firing`), and
the step theorem relates exactly the carried ones. The converse direction is not total:

* **A firing that mentions a dead name has no preimage** (`dead_not_carried`,
  `carrying_not_surjective`): at `Controls.extended`, a live firing whose query pattern is the dead
  name is admitted (`deadQuery_realized`), and it is the carrying of no live firing at `initial`.
  Two solutions that differ only at the dead name agree on everything carried from `initial`, and
  they disagree on the dead name.

So a `Transport` up to dead names cannot have a total `move` that commutes with carrying on all live
firings; programs must not see dead names (`NativeDead.DeadInvariant`), which is the hypothesis the
bisimulation uses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPredicateQueryAdmission (matchingQuery)
open NativeResidualExample

namespace NativeDead

namespace Controls

/-- The dead name of `extended`, in its information frame. -/
def deadName : Term (signature tiny (ContextualActivatedStep.target noLocals twoNames)) ([] : Ctx tiny) () :=
  generator (ContextualActivatedStep.target noLocals twoNames) (.inr (.inr ()))

/-- A solution of `extended`'s information frame giving the dead name a constant. -/
def valued (value : Bool) :
    Assignment (ContextualActivatedStep.target noLocals twoNames) (ContextualActivatedStep.target noLocals twoNames)
  | .inl name => nomatch name.name
  | .inr (.inl ()) => generator (ContextualActivatedStep.target noLocals twoNames) (.inr (.inl ()))
  | .inr (.inr ()) => bit (ContextualActivatedStep.target noLocals twoNames) value

/-- **The two solutions agree on everything carried from `initial`.** -/
theorem valued_carried (first second : Bool) :
    Assignment.compose (valued first) initial_extended.target = Assignment.compose (valued second) initial_extended.target := by
  funext name
  rcases name with ⟨_, impossible⟩ | ⟨⟩
  · exact nomatch impossible
  · exact (instantiate_reindex _ _ (valued first) (Sum.inr ())).trans
      (instantiate_reindex _ _ (valued second) (Sum.inr ())).symm

/-- **The dead name is carried from no term of `initial`.** -/
theorem dead_not_carried
    (term : Term (signature tiny (ContextualActivatedStep.target noLocals oneName)) ([] : Ctx tiny) ()) :
    instantiate initial_extended.target term ≠ deadName := by
  intro same
  have key : instantiate (valued true) (instantiate initial_extended.target term) =
      instantiate (valued false) (instantiate initial_extended.target term) :=
    (Assignment.instantiate_compose (valued true) initial_extended.target term).symm.trans
      ((congrArg (fun assignment => instantiate assignment term) (valued_carried true false)).trans
        (Assignment.instantiate_compose (valued false) initial_extended.target term))
  have one : instantiate (valued true) (instantiate initial_extended.target term) =
      bit (ContextualActivatedStep.target noLocals twoNames) true :=
    (congrArg (instantiate (valued true)) same).trans (instantiate_generator (valued true) (Sum.inr (Sum.inr ())))
  have two : instantiate (valued false) (instantiate initial_extended.target term) =
      bit (ContextualActivatedStep.target noLocals twoNames) false :=
    (congrArg (instantiate (valued false)) same).trans (instantiate_generator (valued false) (Sum.inr (Sum.inr ())))
  have clash : bit (ContextualActivatedStep.target noLocals twoNames) true =
      bit (ContextualActivatedStep.target noLocals twoNames) false := one.symm.trans (key.trans two)
  unfold bit at clash
  cases clash

/-- A live firing at `extended` that selects nothing and asks that no present occurrence match the
dead name. -/
def deadQuery : LiveFiring extended where
  rule := ⟨[], [], [], [], []⟩
  selection := ⟨[], [], []⟩
  outputs _ := deadName
  patterns := [(deadName, ∅)]
  fuel := 0

/-- **The firing that mentions the dead name is admitted.** -/
theorem deadQuery_realized : deadQuery.toNative.Realized := by
  apply (native_admits_iff (S := tiny) deadQuery.toNative).mpr
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, fun _ member => by simp [Selection.commit] at member⟩
    · show ([] : List ℕ).toFinset ⊆ (∅ : Finset ℕ)
      simp
    · show ([] : List ℕ).toFinset ⊆ (∅ : Finset ℕ)
      simp
    · show Disjoint ([] : List ℕ).toFinset ([] : List ℕ).toFinset
      simp
    · show Disjoint ([] : List ℕ).toFinset (∅ : Finset ℕ)
      simp
  · exact ⟨extended.infoFrame, generator _, fun _ member => absurd member List.not_mem_nil⟩
  · intro b σ _
    refine ⟨fun _ member => absurd member List.not_mem_nil, fun query member => ?_⟩
    rw [List.mem_singleton.mp member]
    refine (ContextualPredicateQueryAdmission.matching_holds_iff noLocals deadName ∅
      (ContextualConditionalExecution.guardRows noLocals twoNames extended.state.rows) ∅ ⟨b.Names, b.arity, σ⟩).mpr ?_
    classical
    exact Finset.eq_empty_of_forall_notMem fun o inside =>
      (Finset.notMem_empty o) ((ContextualConditionalGuards.mem_region _ _ _ _ _ o).mp inside).1

/-- **Carrying from `initial` to `extended` is not surjective on live firings**: the admitted firing
that mentions the dead name is the carrying of none. -/
theorem carrying_not_surjective : ∀ f : LiveFiring initial, initial_extended.firing f ≠ deadQuery := by
  intro f same
  have outputs := congrArg (fun g : LiveFiring extended => g.outputs 0) same
  exact dead_not_carried (f.outputs 0) outputs

end Controls

end NativeDead

#print axioms NativeDead.Controls.valued_carried
#print axioms NativeDead.Controls.dead_not_carried
#print axioms NativeDead.Controls.deadQuery_realized
#print axioms NativeDead.Controls.carrying_not_surjective

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
