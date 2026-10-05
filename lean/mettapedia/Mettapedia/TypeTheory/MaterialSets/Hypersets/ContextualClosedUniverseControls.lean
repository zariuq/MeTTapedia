import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseComparisons
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWBaseChange

/-!
# Closed-code controls on the observed growing family

All four type formers below receive actual quotient codes. The dependent
body is constructed by code reindexing along the real comprehension
projection. Full future functions remain distinct beyond present evaluation;
Sigma and W retain cyclic material payloads; identity detects the new
observed position. A separate control keeps distinct formation recipes even
when their complete interpreted families agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseControls

open CategoryTheory
open ContextualGeneratedUniverse (LabelledContext MaterialFamily)

namespace Recipes

open ContextualGeneratedUniverse.Growing (Stages context arrowCoding)

def Seeds (_context : LabelledContext Stages) : Type 1 := ULift.{1, 0} PUnit

def seedModel (declared : LabelledContext Stages) (_label : Seeds declared) : MaterialFamily declared :=
  MaterialFamily.unit declared

def declaredUnit : ContextualClosedUniverseCodes.Code Seeds seedModel arrowCoding context :=
  ContextualClosedUniverseCodes.seed Seeds seedModel arrowCoding context (ULift.up PUnit.unit)

def primitiveUnit : ContextualClosedUniverseCodes.Code Seeds seedModel arrowCoding context :=
  ContextualClosedUniverseCodes.unit Seeds seedModel arrowCoding context

theorem same_complete_family :
    ContextualClosedUniverseCodes.decodeFamily Seeds seedModel arrowCoding declaredUnit =
      ContextualClosedUniverseCodes.decodeFamily Seeds seedModel arrowCoding primitiveUnit := rfl

/-- Equal complete interpretations do not reflect to code equality. -/
theorem distinct_formation_codes : declaredUnit ≠ primitiveUnit := by
  intro same
  have shapes := congrArg (ContextualClosedUniverseCodes.codeSkeleton Seeds seedModel arrowCoding) same
  change ContextualClosedUniverseCodes.FormationSkeleton.seed =
    ContextualClosedUniverseCodes.FormationSkeleton.unit at shapes
  cases shapes

def declaredPi : ContextualClosedUniverseCodes.Code Seeds seedModel arrowCoding context :=
  ContextualClosedUniverseCodes.pi Seeds seedModel arrowCoding declaredUnit
    (ContextualClosedUniverseCodes.unit Seeds seedModel arrowCoding
      (ContextualClosedUniverseCodes.decodeFamily Seeds seedModel arrowCoding declaredUnit).extension)

def primitivePi : ContextualClosedUniverseCodes.Code Seeds seedModel arrowCoding context :=
  ContextualClosedUniverseCodes.pi Seeds seedModel arrowCoding primitiveUnit
    (ContextualClosedUniverseCodes.unit Seeds seedModel arrowCoding
      (ContextualClosedUniverseCodes.decodeFamily Seeds seedModel arrowCoding primitiveUnit).extension)

theorem same_complete_pi_family :
    ContextualClosedUniverseCodes.decodeFamily Seeds seedModel arrowCoding declaredPi =
      ContextualClosedUniverseCodes.decodeFamily Seeds seedModel arrowCoding primitivePi := rfl

theorem distinct_pi_formation_codes : declaredPi ≠ primitivePi := by
  intro same
  have shapes := congrArg (ContextualClosedUniverseCodes.codeSkeleton Seeds seedModel arrowCoding) same
  change ContextualClosedUniverseCodes.FormationSkeleton.pi .seed .unit =
    ContextualClosedUniverseCodes.FormationSkeleton.pi .unit .unit at shapes
  have seeds := ContextualClosedUniverseCodes.FormationSkeleton.pi.inj shapes |>.1
  cases seeds

theorem actual_code_substitution_identity :
    ContextualClosedUniverseCodes.reindex Seeds seedModel arrowCoding
      (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity context.base) declaredPi = declaredPi :=
  ContextualClosedUniverseCodes.reindex_identity Seeds seedModel arrowCoding declaredPi

end Recipes

namespace Growing

open ContextualGeneratedUniverse.Growing

def inputCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.ofRaw Seeds observedSeedModel arrowCoding ⟨input, inputGenerated⟩

def bodyCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding
    (ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding inputCode).extension :=
  ContextualClosedUniverseCodes.reindex Seeds observedSeedModel arrowCoding
    (PowerClassPresheafProducts.projection input.family) inputCode

def piCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.pi Seeds observedSeedModel arrowCoding inputCode bodyCode

def sigmaCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.sigma Seeds observedSeedModel arrowCoding inputCode bodyCode

def identityCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.identity Seeds observedSeedModel arrowCoding inputCode emptySection positiveSection

def leafWCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.w Seeds observedSeedModel arrowCoding inputCode
    (ContextualClosedUniverseCodes.empty Seeds observedSeedModel arrowCoding input.extension)

def unaryWCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.w Seeds observedSeedModel arrowCoding inputCode
    (ContextualClosedUniverseCodes.unit Seeds observedSeedModel arrowCoding input.extension)

theorem full_future_material_members_differ :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding piCode).model old).value
      (PowerClassContextualMaterialization.Growing.identityFunction.val old) ≠
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding piCode).model old).value
      (PowerClassContextualMaterialization.Growing.constantFunction.val old) := future_functions_differ

theorem present_evaluation_cannot_decode_full_pi :
    ¬ Function.Injective (fun function :
      (ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding piCode).family.obj old =>
        fun argument : input.family.obj old => function.app old (𝟙 old) argument) :=
  present_evaluation_not_injective

theorem sigma_retains_cyclic_first :
    HSet.fst (((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding sigmaCode).model later).value
      cyclicPair) = HSet.quineAtom := cyclicPair_first

theorem identity_old_inhabited :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding identityCode).model old).carrier = {∅} :=
  identity_old_carrier

theorem identity_new_empty :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding identityCode).model newPoint).carrier = ∅ :=
  identity_new_carrier

theorem cyclic_w_leaf_is_actual_member :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding leafWCode).model later).value
      (leaf later PowerClassContextualMaterialization.Growing.futureArgument) ∈
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding leafWCode).model later).carrier :=
  cyclic_leaf_material_member

theorem unary_w_is_empty (point : context.base.Elements) :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding unaryWCode).model point).carrier = ∅ :=
  unary_w_empty point

/-- Transported formation uses the actual comprehension projection, whose
source retains the future cyclic member. -/
def projection := PowerClassPresheafProducts.projection input.family

def cyclicPoint : input.extension.base.Elements :=
  ⟨later.1, ⟨later.2, PowerClassContextualMaterialization.Growing.futureArgument⟩⟩

theorem substituted_pi_carrier (point : input.extension.base.Elements) :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding
      (ContextualClosedUniverseCodes.piUnder (other := input.extension) Seeds observedSeedModel arrowCoding projection inputCode bodyCode)).model point).carrier =
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding
      (ContextualClosedUniverseCodes.reindex (other := input.extension) Seeds observedSeedModel arrowCoding projection piCode)).model point).carrier :=
  ContextualClosedUniverseComparisons.piUnder_carrier (other := input.extension) Seeds observedSeedModel arrowCoding projection inputCode bodyCode point

theorem substituted_function_value (point : input.extension.base.Elements)
    (function : (ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding
      (ContextualClosedUniverseCodes.reindex (other := input.extension) Seeds observedSeedModel arrowCoding projection piCode)).family.obj point) :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding
      (ContextualClosedUniverseCodes.piUnder (other := input.extension) Seeds observedSeedModel arrowCoding projection inputCode bodyCode)).model point).value
        (ContextualClosedUniverseComparisons.piComparison (other := input.extension) Seeds observedSeedModel arrowCoding projection inputCode bodyCode point function) =
      ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding
        (ContextualClosedUniverseCodes.reindex (other := input.extension) Seeds observedSeedModel arrowCoding projection piCode)).model point).value function :=
  ContextualClosedUniverseComparisons.piComparison_value (other := input.extension) Seeds observedSeedModel arrowCoding projection inputCode bodyCode point function

end Growing

namespace FreshLabels

open ContextualGeneratedUniverse.Growing

def taggedContext : LabelledContext Stages where
  base := MaterialContextualWBaseChange.Growing.tagged
  labels := MaterialContextualWBaseChange.Growing.worlds

def forgetTag : NatTrans taggedContext.base context.base := MaterialContextualWBaseChange.Growing.forgetTag

def domainCode := Growing.inputCode

def positionsCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding input.extension :=
  ContextualClosedUniverseCodes.empty Seeds observedSeedModel arrowCoding input.extension

def changedDomain : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding taggedContext :=
  ContextualClosedUniverseCodes.reindex Seeds observedSeedModel arrowCoding forgetTag domainCode

def changedPositions : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding
    (ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding changedDomain).extension :=
  ContextualClosedUniverseComparisons.bodyReindex (other := taggedContext) Seeds observedSeedModel arrowCoding forgetTag domainCode positionsCode

def freshCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding taggedContext :=
  ContextualClosedUniverseComparisons.freshW (other := taggedContext) Seeds observedSeedModel arrowCoding forgetTag domainCode positionsCode

def oldCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding taggedContext :=
  ContextualClosedUniverseCodes.reindex Seeds observedSeedModel arrowCoding forgetTag Growing.leafWCode

def point (tag : Bool) : taggedContext.base.Elements := MaterialContextualWBaseChange.Growing.point later tag

noncomputable def freshLeaf (tag : Bool) :
    (ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding freshCode).family.obj (point tag) :=
  ContextualClosedUniverseComparisons.wFreshComparison (other := taggedContext) Seeds observedSeedModel arrowCoding forgetTag domainCode positionsCode
    (point tag) (leaf later PowerClassContextualMaterialization.Growing.futureArgument)

theorem old_labels_merge_values :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding oldCode).model (point false)).value
      (leaf later PowerClassContextualMaterialization.Growing.futureArgument) =
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding oldCode).model (point true)).value
      (leaf later PowerClassContextualMaterialization.Growing.futureArgument) := rfl

theorem fresh_labels_separate_values :
    ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding freshCode).model (point false)).value (freshLeaf false) ≠
      ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding freshCode).model (point true)).value (freshLeaf true) :=
  ContextualClosedUniverseComparisons.w_values_separate_contexts Seeds observedSeedModel arrowCoding
    changedDomain changedPositions (MaterialContextualWBaseChange.Growing.tags_are_distinct later) _ _

/-- Full semantic W substitution exists, but faithful fresh context labels
make simultaneous literal value preservation impossible on this real map. -/
theorem fresh_w_cannot_preserve_all_merged_values :
    ¬ ∀ tag : Bool,
      ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding freshCode).model (point tag)).value (freshLeaf tag) =
      ((ContextualClosedUniverseCodes.decodeFamily Seeds observedSeedModel arrowCoding oldCode).model (point tag)).value
        (leaf later PowerClassContextualMaterialization.Growing.futureArgument) := by
  intro preserves
  exact fresh_labels_separate_values ((preserves false).trans (old_labels_merge_values.trans (preserves true).symm))

end FreshLabels

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseControls
