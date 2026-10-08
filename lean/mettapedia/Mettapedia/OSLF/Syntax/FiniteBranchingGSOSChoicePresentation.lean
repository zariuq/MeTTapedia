import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSPresentation
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSControls

/-!
# Independent GSOS clauses for the actual binary-choice law

One clause selects a transition from the first child; another selects one
from the second. Each retains both original arguments, including its passive
child. Their complete target sets give exactly the independently specified
finite-branching choice law at every natural-number action. This forward
consumer does not restrict the action alphabet. The equality joins the
authored clauses to the existing actual source-retaining operational lifting.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises.ChoicePresentation

open _root_.CategoryTheory Mettapedia.TypeTheory
open Classical GSOSControls

def onePattern (position : Bool) (action : Nat) :
    Pattern (Actions := actions) (sort := ()) (Operator.choose : signature.Operator ()) where
  Occurrence := PUnit
  finite := inferInstance
  address _ := ⟨position, action⟩
  negative := ∅

def oneRule (position : Bool) (action : Nat) :
    Rule (Actions := actions) (sort := ()) (Operator.choose : signature.Operator ()) where
  pattern := onePattern position action
  target := pure (Variable.derivative PUnit.unit)

theorem one_targets (position : Bool) (action : Nat) {X : signature.Families}
    (arguments : Offered X) :
    (oneRule position action).targets arguments =
      Mettapedia.CategoryTheory.FinitePowerset.map (pure (X := X)) ((arguments position).2 action) := by
  apply Finset.ext
  intro target
  rw [Rule.mem_targets, Mettapedia.CategoryTheory.FinitePowerset.mem_map]
  constructor
  · rintro ⟨input, matching, same⟩
    exact ⟨input.derivatives PUnit.unit, matching.2.1 PUnit.unit, same⟩
  · rintro ⟨value, member, same⟩
    refine ⟨⟨fun position => (arguments position).1, fun _ => value⟩, ?_, same⟩
    exact ⟨fun _ => rfl, fun _ => member, fun _ held => (Finset.notMem_empty _ held).elim⟩

def presentation : Presentation signature actions := fun _ operator action => match operator with
  | .stopped => ∅
  | .choose => {oneRule false action, oneRule true action}

/-- Whole target equality is derived from independent premise instantiation. -/
theorem toLaw_eq_actual_choice : Presentation.toLaw presentation = law := by
  apply NatTrans.ext
  funext X base sort
  cases base
  cases sort
  apply ConcreteCategory.hom_ext
  intro layer
  rcases layer with ⟨operator, arguments⟩
  cases operator with
  | stopped =>
      funext action
      change Presentation.targets presentation Operator.stopped arguments action = ∅
      simp [Presentation.targets, presentation]
  | choose =>
      funext action
      let supplied : Offered X := arguments
      change (({oneRule false action, oneRule true action} :
          Finset (Rule (Actions := actions) (sort := ()) Operator.choose)).biUnion
        (fun rule => rule.targets supplied)) =
          Mettapedia.CategoryTheory.FinitePowerset.map (pure (X := X))
            ((supplied false).2 action ∪ (supplied true).2 action)
      rw [Finset.biUnion_insert, Finset.singleton_biUnion, one_targets, one_targets]
      exact (Finset.image_union _ _).symm

theorem complete_constructor_lifting {X : signature.Families}
    (steps : VariableCoalgebra signature actions X) (first second : signature.Term X ()) (action : Nat) :
    Operational.coalgebra (Presentation.toLaw presentation) steps PUnit.unit () (GSOSControls.choose first second) action =
      Operational.coalgebra (Presentation.toLaw presentation) steps PUnit.unit () first action ∪
        Operational.coalgebra (Presentation.toLaw presentation) steps PUnit.unit () second action := by
  rw [toLaw_eq_actual_choice]
  exact operational_choice steps first second action

theorem supplied_both_child_targets :
    Presentation.targets presentation Operator.choose offered 7 =
      {pureNat 11, pureNat 21, pureNat 31} := by
  have same := congrArg (fun mapping => mapping.app naturals PUnit.unit () ⟨Operator.choose, offered⟩ 7)
    toLaw_eq_actual_choice
  exact same.trans independently_authored_law_readout

end Mettapedia.OSLF.FiniteBranching.Premises.ChoicePresentation
