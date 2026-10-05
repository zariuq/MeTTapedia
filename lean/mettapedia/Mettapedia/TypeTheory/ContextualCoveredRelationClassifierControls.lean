import Mettapedia.TypeTheory.ContextualCoveredRelationClassifier
import Mettapedia.TypeTheory.ContextualImageFactorizationControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls

/-!
# Growing covered relation and receipt controls

At stage n the argument family has n+1 positions and authored Boolean tags.
Parameters retain an arbitrary bare hyperset, so they have no cover at the
original small bound. The relation admits every true-tag argument precisely
when that parameter is the cyclic hyperset. Its full future enumerations
construct actual membership pullbacks and whole natural sections.

A supplied current fibre enumeration, mapped along the next context arrow,
misses the newly available related position. A fresh future enumeration
reaches it. This distinguishes the authored data without asserting that
pointwise nonemptiness contradicts a host Choice construction of future data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCoveredRelationClassifierControls

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoveredRelationClassifier
open ContextualImageFactorizationControls (authored positions extension newReceipt new_receipt_not_old_image)
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open CoveredFuturePowerClassifier
open CoveredFuturePowerFamilies (family current)

def ambient : Nat ⥤ Type 1 where
  obj _ := HSet.{0}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev parameters := product positions ambient

def cyclicTrue : StablePredicate (product parameters authored) where
  holds point := point.2.2.down.2 = true ∧ point.2.1.2 = HSet.quineAtom
  closed {first second} move available := by
    have tagEq := congrArg (fun pair : (product parameters authored).obj second.1 => pair.2.down.2) move.2
    have materialEq := congrArg (fun pair : (product parameters authored).obj second.1 => pair.1.2) move.2
    change first.2.2.down.2 = second.2.2.down.2 at tagEq
    change first.2.1.2 = second.2.1.2 at materialEq
    exact ⟨tagEq.symm.trans available.1, materialEq.symm.trans available.2⟩

def enumeration (stage : Nat) (parameter : parameters.obj stage) :
    RelationEnumeration parameters authored cyclicTrue stage parameter where
  Carrier future := {position : Fin (future.1 + 1) // parameter.2 = HSet.quineAtom}
  value _ code := ULift.up (code.val, true)
  covered future argument := by
    change (argument.down.2 = true ∧ parameter.2 = HSet.quineAtom) ↔ _
    constructor
    · intro related
      exact ⟨⟨argument.down.1, related.2⟩, ULift.ext _ _ (Prod.ext rfl related.1.symm)⟩
    · rintro ⟨code, same⟩
      have tagEq := congrArg (fun receipt : authored.obj future.1 => receipt.down.2) same
      exact ⟨tagEq.symm, code.property⟩

def relation : CoveredRelation parameters authored where
  predicate := cyclicTrue
  covered stage parameter := ⟨enumeration stage parameter⟩

def operation : NaturalHom parameters (family authored) := classifier parameters authored relation

def parameter (stage : Nat) (material : HSet.{0}) : parameters.obj stage :=
  (ULift.up ⟨0, Nat.zero_lt_succ stage⟩, material)

def cyclicParameter (stage : Nat) := parameter stage HSet.quineAtom

def emptyParameter (stage : Nat) := parameter stage (∅ : HSet.{0})

theorem cyclicParameter_natural {first second : Nat} (step : first ⟶ second) :
    parameters.map step (cyclicParameter first) = cyclicParameter second :=
  Prod.ext (ULift.ext _ _ (Fin.ext rfl)) rfl

def originalReceipt (stage : Nat) : (total parameters authored cyclicTrue).obj stage :=
  ⟨(cyclicParameter stage, ULift.up (⟨0, Nat.zero_lt_succ stage⟩, true)), rfl, rfl⟩

def relationSection : (total parameters authored cyclicTrue).sections :=
  ⟨originalReceipt, by
    intro first second step
    exact Subtype.ext (Prod.ext (cyclicParameter_natural step) (ULift.ext _ _ (Prod.ext (Fin.ext rfl) rfl)))⟩

def universalSection : (membershipPullback parameters authored relation).sections :=
  membershipSectionEquiv parameters authored relation relationSection

theorem universal_section_whole_inverse :
    (membershipSectionEquiv parameters authored relation).symm universalSection = relationSection :=
  (membershipSectionEquiv parameters authored relation).symm_apply_apply relationSection

theorem universal_section_parameter (stage : Nat) :
    (universalSection.val stage).val.2 = cyclicParameter stage := rfl

theorem universal_section_argument (stage : Nat) :
    (universalSection.val stage).val.1.val.2 = ULift.up (⟨0, Nat.zero_lt_succ stage⟩, true) := rfl

/-- The parameter object is genuinely not covered at the original bound,
although this relation's argument fibres have constructed covers there. -/
theorem parameters_have_no_small_cover {I : Type} (reading : I → parameters.obj 0) :
    ¬ Function.Surjective reading := by
  intro onto
  apply CoveredFuturePowerControls.hset_has_no_small_cover (fun code => (reading code).2)
  intro value
  obtain ⟨code, same⟩ := onto (parameter 0 value)
  exact ⟨code, congrArg Prod.snd same⟩

theorem actual_projection_smallFibres : SmallFibres (parameterProjection parameters authored cyclicTrue) :=
  projection_smallFibres parameters authored relation

def actualFutureEnumerations (stage : Nat) (value : parameters.obj stage) :
    ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection parameters authored cyclicTrue) stage value :=
  relationFutureEnumerations parameters authored cyclicTrue stage value (enumeration stage value)

theorem empty_parameter_has_no_related_argument (stage : Nat) :
    ¬ ∃ receipt : (total parameters authored cyclicTrue).obj stage,
      (parameterProjection parameters authored cyclicTrue).app stage receipt = emptyParameter stage := by
  rintro ⟨receipt, same⟩
  have materialEq := congrArg (fun value : parameters.obj stage => value.2) same
  exact HSet.empty_ne_quineAtom (materialEq.symm.trans receipt.property.2)

theorem parameter_changes_full_classifier (stage : Nat) :
    (operation.app stage (cyclicParameter stage)).val.holds
        (current authored stage (originalReceipt stage).val.2) ∧
      ¬ (operation.app stage (emptyParameter stage)).val.holds
        (current authored stage (originalReceipt stage).val.2) := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro related
    exact HSet.empty_ne_quineAtom related.2

def futureReceipt (stage : Nat) : (total parameters authored cyclicTrue).obj (stage + 1) :=
  ⟨(parameters.map (extension stage) (cyclicParameter stage), newReceipt stage), rfl, rfl⟩

theorem future_receipt_not_in_old_relation (stage : Nat) :
    ¬ ∃ old : (total parameters authored cyclicTrue).obj stage,
      (total parameters authored cyclicTrue).map (extension stage) old = futureReceipt stage := by
  rintro ⟨old, same⟩
  have argumentEq := congrArg (fun receipt : (total parameters authored cyclicTrue).obj (stage + 1) =>
    receipt.val.2) same
  exact new_receipt_not_old_image stage ⟨old.val.2, argumentEq⟩

def currentEnumeration (stage : Nat) : Enumeration.{0, 1}
    (Fibre (parameterProjection parameters authored cyclicTrue) stage (cyclicParameter stage)) :=
  presentFibreEnumeration parameters authored cyclicTrue stage (cyclicParameter stage)
    (enumeration stage (cyclicParameter stage))

/-- Even an actual current fibre enumeration fails when its old receipt
values alone are transported into a genuinely larger future fibre. -/
theorem transported_current_enumeration_misses_future (stage : Nat) :
    ¬ ∃ code : (currentEnumeration stage).Carrier,
      (total parameters authored cyclicTrue).map (extension stage)
        ((currentEnumeration stage).value code).val = futureReceipt stage :=
  fun ⟨code, same⟩ => future_receipt_not_in_old_relation stage
    ⟨((currentEnumeration stage).value code).val, same⟩

theorem full_future_enumeration_reaches_new_receipt (stage : Nat) :
    ∃ code : (actualFutureEnumerations stage (cyclicParameter stage) ⟨stage + 1, extension stage⟩).Carrier,
      ((actualFutureEnumerations stage (cyclicParameter stage) ⟨stage + 1, extension stage⟩).value code).val =
        futureReceipt stage :=
  ⟨⟨⟨stage + 1, Nat.lt_succ_self (stage + 1)⟩, rfl⟩, Subtype.ext rfl⟩

def selectFirst : NaturalHom (product parameters parameters) parameters :=
  firstProjection parameters parameters

theorem selectFirst_not_injective : ¬ Function.Injective (selectFirst.app 0) := by
  intro injective
  have same := injective (a₁ := (cyclicParameter 0, cyclicParameter 0))
    (a₂ := (cyclicParameter 0, emptyParameter 0)) rfl
  have impossible := congrArg (fun pair : (product parameters parameters).obj 0 => pair.2.2) same
  exact HSet.empty_ne_quineAtom impossible.symm

def substitutedReceipt :
    (total (product parameters parameters) authored
      (parameterSubstitution parameters authored selectFirst relation).predicate).obj 0 :=
  ⟨((cyclicParameter 0, emptyParameter 0), (originalReceipt 0).val.2), rfl, rfl⟩

theorem substituted_pullback_retains_full_parameter :
    ((substitutionForward parameters authored selectFirst relation).app 0 substitutedReceipt).val.2 =
      (cyclicParameter 0, emptyParameter 0) := rfl

theorem substituted_pullback_actual_inverse :
    (substitutionBackward parameters authored selectFirst relation).app 0
      ((substitutionForward parameters authored selectFirst relation).app 0 substitutedReceipt) =
        substitutedReceipt := substitution_left parameters authored selectFirst relation 0 substitutedReceipt

theorem substituted_future_argument_preserved (stage : Nat)
    (value : (product parameters parameters).obj stage)
    (future : PowerClassPresheafBaseChange.Future.Objects stage)
    (code : (actualFutureEnumerations stage (selectFirst.app stage value) future).Carrier) :
    (((substitutionFutureEnumerations parameters authored selectFirst relation stage value
      (actualFutureEnumerations stage (selectFirst.app stage value)) future).value code).val).val.2 =
        ((actualFutureEnumerations stage (selectFirst.app stage value) future).value code).val.val.2 :=
  substitutionFutureEnumerations_argument parameters authored selectFirst relation stage value
    (actualFutureEnumerations stage (selectFirst.app stage value)) future code

end Mettapedia.TypeTheory.ContextualCoveredRelationClassifierControls
