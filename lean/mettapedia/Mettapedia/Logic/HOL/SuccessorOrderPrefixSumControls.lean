import Mettapedia.Logic.HOL.SuccessorOrderPrefixSums
import Mettapedia.Logic.HOL.OrderedPositionFunctionalityControls
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Positive prefix witnesses and an unreachable-count countermodel

The natural model realizes the induction premise used for totality. A
separate proposition carrier with identity successor has an unreachable count;
its closure relation therefore has no output at that count. It is a
countermodel to removing induction, not a natural-number representation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrderPrefixSumControls

open SuccessorOrder
open OrderedPositionProofControls (number Symbol zero successor one)
open OrderedPositionFunctionalityControls (assumptions arithmetic)

def onePrefix : ProofSyntax Symbol assumptions
    (.app (.app (.app (sum zero successor) one) one) (.app successor one)) :=
  sumSuccLeft successor zero zero one one (sumZeroLeft successor zero one arithmetic.induction)

theorem onePrefix_free : onePrefix.FunctionExtensionalityFree := by
  apply sumSuccLeft_free
  apply sumZeroLeft_free
  trivial

def dynamicPrefix (first count : ClosedTerm Symbol number) :
    ProofSyntax Symbol assumptions (sumExists successor zero first count) :=
  sumTotal successor zero first count arithmetic.induction

theorem dynamicPrefix_free (first count : ClosedTerm Symbol number) :
    (dynamicPrefix first count).FunctionExtensionalityFree := by
  apply sumTotal_free
  trivial

abbrev BooleanConstants := FiniteConstructorEncoding.Controls.Constants
def identitySuccessor : ClosedTerm BooleanConstants (.prop ⇒ .prop) := .lam (.var .vz)

theorem unreachable_count_has_no_output :
    ¬ ∃ result : Ty.denote FiniteConstructorEncoding.Controls.model.Carrier .prop,
      (FiniteConstructorEncoding.Controls.model.denote
        (sum (.bot : ClosedFormula BooleanConstants) identitySuccessor)
        @FiniteConstructorEncoding.Controls.values (ULift.up False) (ULift.up True) result).down := by
  rintro ⟨result, present⟩
  have every := (sum_denote FiniteConstructorEncoding.Controls.model
    (HenkinModel.fullDomains_standard _ _) identitySuccessor @FiniteConstructorEncoding.Controls.values
      (.bot : ClosedFormula BooleanConstants) (ULift.up False) (ULift.up True) result).mp present
  have impossible : ¬ True := every (fun count _ => ¬ count.down)
    (fun absent => absent) (fun _ _ previous => previous)
  exact impossible True.intro

#print axioms onePrefix_free
#print axioms dynamicPrefix_free
#print axioms unreachable_count_has_no_output

end Mettapedia.Logic.HOL.SuccessorOrderPrefixSumControls
