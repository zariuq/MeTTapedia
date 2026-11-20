import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOpenControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplines
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFiringModels

/-!
# A complete batch cannot make incompatible refinements of one shared row

Every offered class in an admitted complete bag has a realization at the bag's
one common source model. On the existing open-input control, completeness asks
for both the five and six refinements of the same unknown. No such model exists,
although the two branches are individually admitted and have terminal outcomes.
This is a failure of ground propagation's hypothesis, not a scheduling default.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.OpenControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings
open JointFirings.SymmetricMatches

section CommonModel

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P : Program (Terms (Term signature))}

theorem complete_match_realized (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (complete : bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity Set.univ)
    (assignment : Subst signature)
    (solved : Unifies assignment (bag.information (frames (FirstOrder.action signature)) s))
    (candidate : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : candidate.Admits (frames (FirstOrder.action signature)) s) :
    ∃ output, (presentation candidate).Realizes s.label assignment output := by
  have listed := complete.2.2.2 candidate (Set.mem_univ (identity.key candidate)) admitted
  obtain ⟨member, inside, sameKey⟩ := List.mem_map.mp listed
  have memberModel := Bag.models_member (frames (FirstOrder.action signature)) inside
    (b := PUnit.unit) solved
  obtain ⟨_, uses, tells⟩ := (models_information_iff s member.firing assignment).mp memberModel
  let output := member.rule.body.produce.map (assignment.comp member.opening).applyTerm
  have realizes : (presentation member.firing).Realizes s.label assignment output :=
    ⟨assignment.comp member.opening, uses, tells, rfl⟩
  have same : Same (presentation member.firing) (presentation candidate) := Quotient.exact sameKey
  exact ⟨output, (same.realizes_iff _ _ _).mp realizes⟩

end CommonModel

open SetStoreOpenControls (c v choose program source chooseFiring)
open RuleSyntax.Controls (atoms action)

abbrev X := frames action

theorem complete_forces_value
    (bag : SetStore.Candidate program)
    (complete : bag.AdmitsEveryBy X (SetStore.represent source) identity Set.univ)
    (assignment : Subst atoms)
    (solved : Unifies assignment (bag.information X (SetStore.represent source)))
    (n : Nat) (which : n = 5 ∨ n = 6) : assignment.applyTerm v = c n := by
  obtain ⟨_, locals, pairs, _, _⟩ := complete_match_realized (SetStore.represent source) bag
    complete assignment solved (chooseFiring n which) (SetStoreOpenControls.choose_admitted n which)
  have equation := pairs (c n, (v, 0)) (by
    simp [Presentation.uses, presentation, chooseFiring, choose])
  simpa only [SetStore.represent, c, Subst.applyTerm] using equation.symm

theorem no_every_bag (bag : SetStore.Candidate program) :
    ¬ bag.AdmitsEveryBy X (SetStore.represent source) identity Set.univ := by
  intro complete
  obtain ⟨b, assignment, solved⟩ := complete.1.2.2.1
  cases b
  have five := complete_forces_value bag complete assignment solved 5 (Or.inl rfl)
  have six := complete_forces_value bag complete assignment solved 6 (Or.inr rfl)
  have impossible : c 5 = c 6 := five.symm.trans six
  cases Term.const.inj impossible

theorem no_every_step (timing : SetStore.AskTiming) (after : Finset (Term atoms)) :
    ¬ SetStoreSyntax.DisciplinedStep .every timing program source after := by
  rintro ⟨bag, _, _, allowed, _⟩
  exact no_every_bag bag allowed

theorem branches_exist_but_every_refuses (timing : SetStore.AskTiming) :
    SetStore.Step timing program source (SetStoreOpenControls.target 5) ∧
      SetStore.Step timing program source (SetStoreOpenControls.target 6) ∧
      SetStoreOpenControls.target 5 ≠ SetStoreOpenControls.target 6 ∧
      ∀ after, ¬ SetStoreSyntax.DisciplinedStep .every timing program source after :=
  ⟨SetStoreOpenControls.choose_step timing 5 (Or.inl rfl),
    SetStoreOpenControls.choose_step timing 6 (Or.inr rfl), SetStoreOpenControls.targets_differ,
    no_every_step timing⟩

#print axioms complete_match_realized
#print axioms complete_forces_value
#print axioms no_every_bag
#print axioms no_every_step
#print axioms branches_exist_but_every_refuses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.OpenControls
