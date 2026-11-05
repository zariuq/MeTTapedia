import Mettapedia.Logic.HOL.SetCodeOperators
import Mettapedia.Logic.HOL.Syntax.ConstantSubstitutionComposition

/-!
# Constant renaming commutes with the set-code constructions

The laws factor through the actual pairing, sum, trace and projection
constructors. They avoid unfolding the complete closed operator bodies when
the primitive signature is embedded in a larger one.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetCodeConstantMap
open SetComprehensionProofs SetPairingProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mapping)
universe v w
variable {Const : Ty Unit → Type v} {Target : Ty Unit → Type w}
variable (core : Core Const) (constants : ∀ {type}, Const type → Target type)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ : Ctx Unit}

def mappedCore : Core Target := fun symbol => constants (core symbol)

theorem map_choose (question : Formula Const Γ) (left right : Term Const Γ object) :
    HOL.mapConst constants (choose epsilon question left right) =
      choose (HOL.mapConst constants epsilon) (HOL.mapConst constants question)
        (HOL.mapConst constants left) (HOL.mapConst constants right) := by
  simp only [choose,SelectionProofs.selected,HOL.mapConst,HOL.mapConst_weakenCtx,HOL.mapConst_weaken]

theorem map_index : HOL.mapConst constants (index (Γ := Γ) core) = index (mappedCore core constants) := rfl

theorem map_send (left right : Term Const Γ object) : HOL.mapConst constants (send core epsilon left right) =
    send (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants left) (HOL.mapConst constants right) := by
  simp only [send,map_choose,HOL.mapConst,HOL.mapConst_weaken,condition]
  rfl

theorem map_unordered (left right : Term Const Γ object) : HOL.mapConst constants (unordered core epsilon left right) =
    unordered (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants left) (HOL.mapConst constants right) := by
  simp only [unordered,image,HOL.mapConst,map_index,map_send]
  rfl

theorem map_ordered (left right : Term Const Γ object) : HOL.mapConst constants (ordered core epsilon left right) =
    ordered (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants left) (HOL.mapConst constants right) := by
  simp only [ordered,map_unordered]

theorem map_fibreMap (point : Term Const Γ object) : HOL.mapConst constants (SetDependentSumProofs.fibreMap core epsilon point) =
    SetDependentSumProofs.fibreMap (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants point) := by
  simp only [SetDependentSumProofs.fibreMap,map_ordered,HOL.mapConst,HOL.mapConst_weaken]

theorem map_pairImage (point fibre : Term Const Γ object) : HOL.mapConst constants (SetDependentSumProofs.pairImage core epsilon point fibre) =
    SetDependentSumProofs.pairImage (mappedCore core constants) (HOL.mapConst constants epsilon)
      (HOL.mapConst constants point) (HOL.mapConst constants fibre) := by
  simp only [SetDependentSumProofs.pairImage,image,map_fibreMap,HOL.mapConst]
  rfl

theorem map_familyMap (family : Term Const Γ mapping) : HOL.mapConst constants (SetDependentSumProofs.familyMap core epsilon family) =
    SetDependentSumProofs.familyMap (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants family) := by
  simp only [SetDependentSumProofs.familyMap,map_pairImage,HOL.mapConst,HOL.mapConst_weaken]

theorem map_sum (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.mapConst constants (SetDependentSumProofs.sum core epsilon domain family) =
      SetDependentSumProofs.sum (mappedCore core constants) (HOL.mapConst constants epsilon)
        (HOL.mapConst constants domain) (HOL.mapConst constants family) := by
  simp only [SetDependentSumProofs.sum,familyUnion,image,map_familyMap,HOL.mapConst]
  rfl

theorem map_firstBody (point : Term Const Γ object) : HOL.mapConst constants (SetPairProjectionProofs.firstBody core epsilon point) =
    SetPairProjectionProofs.firstBody (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants point) := by
  simp only [SetPairProjectionProofs.firstBody,map_ordered,HOL.mapConst,HOL.mapConst_weaken]

theorem map_first (point : Term Const Γ object) : HOL.mapConst constants (SetPairProjectionProofs.first core epsilon point) =
    SetPairProjectionProofs.first (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants point) := by
  simp only [SetPairProjectionProofs.first,SelectionProofs.selected,map_firstBody,HOL.mapConst,HOL.mapConst_weakenCtx]

theorem map_secondBody (point : Term Const Γ object) : HOL.mapConst constants (SetPairProjectionProofs.secondBody core epsilon point) =
    SetPairProjectionProofs.secondBody (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants point) := by
  simp only [SetPairProjectionProofs.secondBody,map_ordered,map_first,HOL.mapConst,HOL.mapConst_weaken]

theorem map_second (point : Term Const Γ object) : HOL.mapConst constants (SetPairProjectionProofs.second core epsilon point) =
    SetPairProjectionProofs.second (mappedCore core constants) (HOL.mapConst constants epsilon) (HOL.mapConst constants point) := by
  simp only [SetPairProjectionProofs.second,SelectionProofs.selected,map_secondBody,HOL.mapConst,HOL.mapConst_weakenCtx]

theorem map_application (relation point : Term Const Γ object) :
    HOL.mapConst constants (SetTraceProofs.application core epsilon relation point) =
      SetTraceProofs.application (mappedCore core constants) (HOL.mapConst constants epsilon)
        (HOL.mapConst constants relation) (HOL.mapConst constants point) := by
  simp only [SetTraceProofs.application,SetTraceProofs.coordinates,separate,member,map_ordered,HOL.mapConst,HOL.mapConst_weaken]
  rfl

theorem map_values (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.mapConst constants (SetTraceProductProofs.values core domain family) =
      SetTraceProductProofs.values (mappedCore core constants) (HOL.mapConst constants domain) (HOL.mapConst constants family) := rfl

theorem map_supportFamily (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.mapConst constants (SetTraceProductProofs.supportFamily core domain family) =
      SetTraceProductProofs.supportFamily (mappedCore core constants) (HOL.mapConst constants domain) (HOL.mapConst constants family) := by
  simp only [SetTraceProductProofs.supportFamily,map_values,HOL.mapConst,HOL.mapConst_weaken]

theorem map_support (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.mapConst constants (SetTraceProductProofs.support core epsilon domain family) =
      SetTraceProductProofs.support (mappedCore core constants) (HOL.mapConst constants epsilon)
        (HOL.mapConst constants domain) (HOL.mapConst constants family) := by
  simp only [SetTraceProductProofs.support,map_sum,map_supportFamily]

theorem map_guard (domain : Term Const Γ object) (family : Term Const Γ mapping) (relation : Term Const Γ object) :
    HOL.mapConst constants (SetTraceProductProofs.guard core epsilon domain family relation) =
      SetTraceProductProofs.guard (mappedCore core constants) (HOL.mapConst constants epsilon)
        (HOL.mapConst constants domain) (HOL.mapConst constants family) (HOL.mapConst constants relation) := by
  simp only [SetTraceProductProofs.guard,member,map_application,HOL.mapConst,HOL.mapConst_weaken]
  rfl

theorem map_product (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.mapConst constants (SetTraceProductProofs.product core epsilon domain family) =
      SetTraceProductProofs.product (mappedCore core constants) (HOL.mapConst constants epsilon)
        (HOL.mapConst constants domain) (HOL.mapConst constants family) := by
  simp only [SetTraceProductProofs.product,separate,power,map_support,map_guard,HOL.mapConst,HOL.mapConst_weaken]
  rfl

theorem map_truth (proposition : Formula Const Γ) : HOL.mapConst constants (truthCode core proposition) =
    truthCode (mappedCore core constants) (HOL.mapConst constants proposition) := by
  simp only [truthCode,separate,power,HOL.mapConst,HOL.mapConst_weaken]
  rfl

theorem map_body {type : Ty Unit} (operator : SetCodeOperators.Operator type) :
    HOL.mapConst constants (SetCodeOperators.body core epsilon operator) =
      SetCodeOperators.body (mappedCore core constants) (HOL.mapConst constants epsilon) operator := by
  cases operator <;>
    simp only [SetCodeOperators.body,SetCodeOperators.binary,SetCodeOperators.unary,
      BinaryOperation.body,BinaryOperation.bodyAt,UnaryOperation.body,UnaryOperation.bodyAt,
      map_product,map_sum,SetTraceProofs.abstraction,map_application,map_ordered,map_first,map_second,map_truth,HOL.mapConst]

end Mettapedia.Logic.HOL.SetCodeConstantMap
