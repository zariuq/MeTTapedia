import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModel
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction
import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence

/-!
# Dependent closure of actual contextual member families

A parameter family supplies an actual parent set. Its constructed small
member family supplies the comprehension context. A natural set-valued map
on that comprehension supplies an arbitrary argument-dependent body, whose
members again have a constructed original-bound decoder. Dependent sums,
complete future products, discrete identity and contextual W formation
therefore apply to actual material membership without a supplied smallness
or type-former capability.

The small-family universe codes classify the complete formed functors.
These host codes are distinguished from internal material set values.
External host choice is inherited from the actual member-family factory.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosure

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetModel
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality

universe u v w h
variable {D : Type u} [Category.{u} D] {parameters : D ⥤ Type v}
variable (parent : NaturalHom parameters sets)

noncomputable abbrev domain : parameters.Elements ⥤ Type u := memberFamilyUnder parent
noncomputable abbrev comprehension := ContextualSmallFamilyUniverse.total (domain parent)

noncomputable def argumentReading : NaturalHom (comprehension parent) sets where
  app point receipt := (memberDecoder ⟨point, parent.app point receipt.1⟩ receipt.2).val
  naturality {first second} step receipt := by
    exact memberDecoder_restriction_value
      ((ContextualSmallFamilyUniverse.elementMap parent).map
        (CategoryOfElements.homMk (F := parameters) ⟨first, receipt.1⟩
          ⟨second, parameters.map step receipt.1⟩ step rfl)) receipt.2

variable (bodyMap : NaturalHom (comprehension parent) sets)

noncomputable abbrev bodyMembers : (comprehension parent).Elements ⥤ Type u :=
  memberFamilyUnder bodyMap

noncomputable def body : (domain parent).Elements ⥤ Type u :=
  ContextualSmallFamilyComprehension.indexedBody (domain parent) (bodyMembers parent bodyMap)

noncomputable def literalBody : (domain parent).Elements ⥤ Type (u+1) :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyComprehension.flatten (domain parent))
    (actualMemberFamilyUnder bodyMap)

noncomputable def bodyDecoder (argument : (domain parent).Elements) :
    (body parent bodyMap).obj argument ≃ (literalBody parent bodyMap).obj argument :=
  memberDecoder ⟨argument.1.1, bodyMap.app argument.1.1 ⟨argument.1.2, argument.2⟩⟩

theorem bodyDecoder_natural {first second : (domain parent).Elements} (step : first ⟶ second)
    (code : (body parent bodyMap).obj first) :
    (literalBody parent bodyMap).map step (bodyDecoder parent bodyMap first code) =
      bodyDecoder parent bodyMap second ((body parent bodyMap).map step code) :=
  memberDecoder_restriction
    ((ContextualSmallFamilyUniverse.elementMap bodyMap).map
      ((ContextualSmallFamilyComprehension.flatten (domain parent)).map step)) code

theorem bodyDecoder_value_natural {first second : (domain parent).Elements} (step : first ⟶ second)
    (code : (body parent bodyMap).obj first) :
    sets.map step.1.1 (bodyDecoder parent bodyMap first code).val =
      (bodyDecoder parent bodyMap second ((body parent bodyMap).map step code)).val :=
  congrArg Subtype.val (bodyDecoder_natural parent bodyMap step code)

theorem bodyDecoder_value_heq {first second : (domain parent).Elements} (same : first = second)
    (left : (body parent bodyMap).obj first) (right : (body parent bodyMap).obj second)
    (values : HEq left right) :
    HEq (bodyDecoder parent bodyMap first left).val (bodyDecoder parent bodyMap second right).val := by
  cases same
  cases eq_of_heq values
  rfl

noncomputable def sigmaFamily : parameters.Elements ⥤ Type u :=
  ContextualSmallFamilyTypeFormers.sigma (domain parent) (body parent bodyMap)

noncomputable def piFamily : parameters.Elements ⥤ Type u :=
  ContextualSmallFamilyTypeFormers.pi (domain parent) (body parent bodyMap)

noncomputable def wFamily : parameters.Elements ⥤ Type u :=
  ContextualSmallFamilyWTypes.w (domain parent) (body parent bodyMap)

/-- The first coordinate retains its actual member code, with an injective
literal-member decoder; the dependent second coordinate is a literal member
of the body set selected by that first coordinate. -/
noncomputable def sigmaDecoder (point : parameters.Elements) :
    (sigmaFamily parent bodyMap).obj point ≃
      (Σ argument : (domain parent).obj point, (literalBody parent bodyMap).obj ⟨point, argument⟩) where
  toFun receipt := ⟨receipt.1, bodyDecoder parent bodyMap ⟨point, receipt.1⟩ receipt.2⟩
  invFun receipt := ⟨receipt.1, (bodyDecoder parent bodyMap ⟨point, receipt.1⟩).symm receipt.2⟩
  left_inv receipt := Sigma.ext rfl (heq_of_eq ((bodyDecoder parent bodyMap _).symm_apply_apply receipt.2))
  right_inv receipt := Sigma.ext rfl (heq_of_eq ((bodyDecoder parent bodyMap _).apply_symm_apply receipt.2))

theorem sigmaDecoder_first_value (point : parameters.Elements) (receipt : (sigmaFamily parent bodyMap).obj point) :
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj point)
      (sigmaDecoder parent bodyMap point receipt).1).val =
      (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj point) receipt.1).val := rfl

theorem sigmaDecoder_second_value (point : parameters.Elements) (receipt : (sigmaFamily parent bodyMap).obj point) :
    (sigmaDecoder parent bodyMap point receipt).2.val = (bodyDecoder parent bodyMap ⟨point, receipt.1⟩ receipt.2).val := rfl

theorem sigmaDecoder_restriction_values {first second : parameters.Elements} (step : first ⟶ second)
    (receipt : (sigmaFamily parent bodyMap).obj first) :
    (sets.map step.1 (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj first) receipt.1).val,
      sets.map step.1 (bodyDecoder parent bodyMap ⟨first, receipt.1⟩ receipt.2).val) =
    ((memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj second)
        ((sigmaFamily parent bodyMap).map step receipt).1).val,
      (sigmaDecoder parent bodyMap second ((sigmaFamily parent bodyMap).map step receipt)).2.val) :=
  Prod.ext (memberDecoder_restriction_value ((ContextualSmallFamilyUniverse.elementMap parent).map step) receipt.1)
    (bodyDecoder_value_natural parent bodyMap
      (ContextualSmallFamilyTypeFormers.argumentStep (domain parent) step receipt.1) receipt.2)

noncomputable def futureLiteralBody (point : parameters.Elements) :
    (ContextualSmallFamilyTypeFormers.futureDomain (domain parent) point).Elements ⥤ Type (u+1) :=
  ContextualSmallFamilyUniverse.restrict
    (ContextualSmallFamilyTypeFormers.futureArguments (domain parent) point) (literalBody parent bodyMap)

/-- All future context arrows and typed arguments remain in this decoder;
the result is an actual compatible section of literal material body members. -/
noncomputable def piDecoder (point : parameters.Elements) :
    (piFamily parent bodyMap).obj point ≃ (futureLiteralBody parent bodyMap point).sections where
  toFun term := ⟨fun argument => bodyDecoder parent bodyMap
    ((ContextualSmallFamilyTypeFormers.futureArguments (domain parent) point).obj argument) (term.val argument), by
    intro first second step
    exact (bodyDecoder_natural parent bodyMap
      ((ContextualSmallFamilyTypeFormers.futureArguments (domain parent) point).map step) (term.val first)).trans
        (congrArg (bodyDecoder parent bodyMap _) (term.property step))⟩
  invFun term := ⟨fun argument => (bodyDecoder parent bodyMap
    ((ContextualSmallFamilyTypeFormers.futureArguments (domain parent) point).obj argument)).symm (term.val argument), by
    intro first second step
    apply (bodyDecoder parent bodyMap _).injective
    exact (bodyDecoder_natural parent bodyMap
      ((ContextualSmallFamilyTypeFormers.futureArguments (domain parent) point).map step)
      ((bodyDecoder parent bodyMap _).symm (term.val first))).symm.trans
        ((congrArg ((futureLiteralBody parent bodyMap point).map step)
          ((bodyDecoder parent bodyMap _).apply_symm_apply (term.val first))).trans
          ((term.property step).trans ((bodyDecoder parent bodyMap _).apply_symm_apply (term.val second)).symm))⟩
  left_inv term := by
    apply Subtype.ext
    funext argument
    exact (bodyDecoder parent bodyMap _).symm_apply_apply (term.val argument)
  right_inv term := by
    apply Subtype.ext
    funext argument
    exact (bodyDecoder parent bodyMap _).apply_symm_apply (term.val argument)

noncomputable def nativePiDecoder (point : parameters.Elements) :
    WiderPresheafDependentFunctions.DependentSection (domain parent) (body parent bodyMap) point ≃
      (futureLiteralBody parent bodyMap point).sections :=
  (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (domain parent) (body parent bodyMap) point).trans
    (piDecoder parent bodyMap point)

theorem piDecoder_value (point : parameters.Elements) (term : (piFamily parent bodyMap).obj point)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (domain parent) point).Elements) :
    ((piDecoder parent bodyMap point term).val argument).val =
      (bodyDecoder parent bodyMap
        ((ContextualSmallFamilyTypeFormers.futureArguments (domain parent) point).obj argument) (term.val argument)).val := rfl

theorem piDecoder_restriction_value {first second : parameters.Elements} (step : first ⟶ second)
    (term : (piFamily parent bodyMap).obj first)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (domain parent) second).Elements) :
    HEq (((piDecoder parent bodyMap second ((piFamily parent bodyMap).map step term)).val argument).val)
      (((piDecoder parent bodyMap first term).val
        ((ContextualSmallFamilyTypeFormers.prefixArguments (domain parent) step).obj argument)).val) :=
  bodyDecoder_value_heq parent bodyMap
    (ContextualSmallFamilyTypeFormers.prefixArguments_embedding (domain parent) step argument).symm _ _
    (ContextualSmallFamilyTypeFormers.productMap_value (domain parent) (body parent bodyMap) step term argument)

/-- Literal members at every future argument, with both inner naturality
and the complete outer context-restriction law. Material value equality
suffices because the constructed typed member decoder is injective. -/
structure LiteralProducts where
  value : (point : parameters.Elements) → (futureLiteralBody parent bodyMap point).sections
  compatible : ∀ {first second : parameters.Elements} (step : first ⟶ second)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (domain parent) second).Elements),
    HEq ((value second).val argument).val
      ((value first).val ((ContextualSmallFamilyTypeFormers.prefixArguments (domain parent) step).obj argument)).val

theorem LiteralProducts.ext (first second : LiteralProducts parent bodyMap)
    (values : first.value = second.value) : first = second := by
  cases first
  cases second
  cases values
  rfl

noncomputable def piSectionDecoder : (piFamily parent bodyMap).sections ≃ LiteralProducts parent bodyMap where
  toFun term := {
    value point := piDecoder parent bodyMap point (term.val point)
    compatible {first second} step argument := by
      rw [← term.property step]
      exact piDecoder_restriction_value parent bodyMap step (term.val first) argument }
  invFun term := ⟨fun point => (piDecoder parent bodyMap point).symm (term.value point), by
    intro first second step
    apply Subtype.ext
    funext argument
    apply (bodyDecoder parent bodyMap
      ((ContextualSmallFamilyTypeFormers.futureArguments (domain parent) second).obj argument)).injective
    apply Subtype.ext
    have moved := piDecoder_restriction_value parent bodyMap step
      ((piDecoder parent bodyMap first).symm (term.value first)) argument
    have old := congrArg (fun row : (futureLiteralBody parent bodyMap first).sections =>
      (row.val ((ContextualSmallFamilyTypeFormers.prefixArguments (domain parent) step).obj argument)).val)
      ((piDecoder parent bodyMap first).apply_symm_apply (term.value first))
    have new := congrArg (fun row : (futureLiteralBody parent bodyMap second).sections =>
      (row.val argument).val)
      ((piDecoder parent bodyMap second).apply_symm_apply (term.value second))
    exact eq_of_heq (moved.trans ((heq_of_eq old).trans
      ((term.compatible step argument).symm.trans (heq_of_eq new).symm)))⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (piDecoder parent bodyMap point).symm_apply_apply (term.val point)
  right_inv term := by
    apply LiteralProducts.ext
    funext point
    exact (piDecoder parent bodyMap point).apply_symm_apply (term.value point)

noncomputable def sigmaClassifier : NaturalHom parameters ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (sigmaFamily parent bodyMap)

noncomputable def piClassifier : NaturalHom parameters ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (piFamily parent bodyMap)

noncomputable def wClassifier : NaturalHom parameters ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (wFamily parent bodyMap)

theorem sigma_full_decode : ContextualSmallFamilyUniverse.decodedFamily (sigmaClassifier parent bodyMap) =
    sigmaFamily parent bodyMap := ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem pi_full_decode : ContextualSmallFamilyUniverse.decodedFamily (piClassifier parent bodyMap) =
    piFamily parent bodyMap := ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem w_full_decode : ContextualSmallFamilyUniverse.decodedFamily (wClassifier parent bodyMap) =
    wFamily parent bodyMap := ContextualSmallFamilyUniverse.decoded_classifier_eq _

noncomputable def piHomEquiv (consumer : parameters.Elements ⥤ Type h) :
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over (domain parent) consumer) (body parent bodyMap) ≃
    WiderPresheafDependentFunctions.Hom consumer (piFamily parent bodyMap) :=
  ContextualSmallFamilyNativeAdjunction.smallHomEquiv (domain parent) (body parent bodyMap) consumer

theorem pi_beta (consumer : parameters.Elements ⥤ Type h)
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over (domain parent) consumer) (body parent bodyMap)) :
    ContextualSmallFamilyNativeAdjunction.smallUncurry (domain parent) (body parent bodyMap)
      (piHomEquiv parent bodyMap consumer operation) = operation :=
  ContextualSmallFamilyNativeAdjunction.small_uncurry_curry (domain parent) (body parent bodyMap) operation

theorem pi_eta (consumer : parameters.Elements ⥤ Type h)
    (operation : WiderPresheafDependentFunctions.Hom consumer (piFamily parent bodyMap)) :
    piHomEquiv parent bodyMap consumer
      (ContextualSmallFamilyNativeAdjunction.smallUncurry (domain parent) (body parent bodyMap) operation) = operation :=
  ContextualSmallFamilyNativeAdjunction.small_curry_uncurry (domain parent) (body parent bodyMap) operation

noncomputable def identityFamily (left right : (domain parent).sections) : parameters.Elements ⥤ Type u :=
  ContextualSmallFamilyIdentity.identityFamily (domain parent) left right

theorem identity_literal_values (left right : (domain parent).sections) (point : parameters.Elements) :
    Nonempty ((identityFamily parent left right).obj point) ↔
      (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj point) (left.val point)).val =
        (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj point) (right.val point)).val := by
  constructor
  · rintro ⟨witness⟩
    exact congrArg (fun code => (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj point) code).val)
      (PresheafIdentityWitness.decode witness)
  · intro values
    exact ⟨PresheafIdentityWitness.encode ((memberDecoder _).injective (Subtype.ext values))⟩

theorem identity_full_decode (left right : (domain parent).sections) :
    ContextualSmallFamilyUniverse.decodedFamily
      (ContextualSmallFamilyUniverse.classifier (identityFamily parent left right)) = identityFamily parent left right :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem identity_J_beta
    (motive : (ContextualSmallFamilyIdentity.identityContext (domain parent)).Elements ⥤ Type h)
    (method : (ContextualSmallFamilyIdentity.reindex motive
      (ContextualSmallFamilyIdentity.diagonal (domain parent))).sections) :
    ContextualSmallFamilyIdentity.reindexSection (ContextualSmallFamilyIdentity.diagonal (domain parent)) motive
      (ContextualSmallFamilyIdentity.J (domain parent) motive method) = method :=
  ContextualSmallFamilyIdentity.J_beta (domain parent) motive method

/-- The W constructor and algebra universal property use whole compatible
future branches. Well-foundedness of these trees does not assert foundation
for their cyclic material shape or position values. -/
theorem w_initiality (target : parameters.Elements ⥤ Type u)
    (algebra : ContextualSmallFamilyWAlgebra.Algebra (domain parent) (body parent bodyMap) (target := target)) :
    ∃! operation : NatTrans (wFamily parent bodyMap) target,
      ∀ (point : parameters.Elements)
        (node : ContextualSmallFamilyWPolynomial.At (domain parent) (body parent bodyMap) (wFamily parent bodyMap) point),
        operation.app point (ContextualSmallFamilyWAlgebra.constructorValue (domain parent) (body parent bodyMap) point node) =
          algebra.app point (ContextualSmallFamilyWAction.mapValue (domain parent) (body parent bodyMap) operation point node) :=
  ContextualSmallFamilyWInitiality.initiality (domain parent) (body parent bodyMap) algebra

section Substitution

variable {other : D ⥤ Type w} (change : NaturalHom other parameters)

theorem member_formation_substitution : domain (change.comp parent) =
    ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

noncomputable def bodyMapUnder : NaturalHom
    (ContextualSmallFamilyUniverse.total
      (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change)) sets :=
  (ContextualSmallFamilyComprehension.totalChange (domain parent) change).comp bodyMap

noncomputable def freshBody :
    (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change).Elements ⥤ Type u :=
  ContextualSmallFamilyComprehension.indexedBody
    (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change)
    (memberFamilyUnder (bodyMapUnder parent bodyMap change))

theorem freshBody_eq : freshBody parent bodyMap change =
    ContextualSmallFamilyTypeFormerCoherence.bodyUnder change (domain parent) (body parent bodyMap) := by
  have members : memberFamilyUnder (bodyMapUnder parent bodyMap change) =
      ContextualSmallFamilyUniverse.substitutedFamily (bodyMembers parent bodyMap)
        (ContextualSmallFamilyComprehension.totalChange (domain parent) change) := by
    refine Functor.hext (fun _ => rfl) ?_
    intro _ _ _
    rfl
  unfold freshBody
  rw [members]
  exact ContextualSmallFamilyComprehension.indexedBody_substitution (domain parent) change (bodyMembers parent bodyMap)

noncomputable def freshSigma : other.Elements ⥤ Type u :=
  ContextualSmallFamilyTypeFormers.sigma
    (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change) (freshBody parent bodyMap change)

noncomputable def freshPi : other.Elements ⥤ Type u :=
  ContextualSmallFamilyTypeFormers.pi
    (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change) (freshBody parent bodyMap change)

noncomputable def freshW : other.Elements ⥤ Type u :=
  ContextualSmallFamilyWTypes.w
    (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change) (freshBody parent bodyMap change)

theorem sigma_substitution : freshSigma parent bodyMap change =
    ContextualSmallFamilyUniverse.substitutedFamily (sigmaFamily parent bodyMap) change := by
  unfold freshSigma
  rw [freshBody_eq]
  exact ContextualSmallFamilyTypeFormerCoherence.sigma_substitution change (domain parent) (body parent bodyMap)

theorem freshPi_eq : freshPi parent bodyMap change =
    ContextualSmallFamilyTypeFormers.pi
      (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change)
      (ContextualSmallFamilyTypeFormerCoherence.bodyUnder change (domain parent) (body parent bodyMap)) :=
  congrArg (ContextualSmallFamilyTypeFormers.pi
    (ContextualSmallFamilyUniverse.substitutedFamily (domain parent) change)) (freshBody_eq parent bodyMap change)

theorem w_substitution : ContextualSmallFamilyUniverse.substitutedFamily (wFamily parent bodyMap) change =
    freshW parent bodyMap change := by
  unfold freshW
  rw [freshBody_eq]
  exact ContextualSmallFamilyWSubstitutionCoherence.w_substitution_eq change (domain parent) (body parent bodyMap)

def familyEqHom {E : Type v} [Category.{u} E] {first second : E ⥤ Type h}
    (same : first = second) : NatTrans first second := by
  cases same
  exact ContextualSmallFamilyTypeFormers.identityNat first

theorem familyEqHom_left {E : Type v} [Category.{u} E] {first second : E ⥤ Type h}
    (same : first = second) (point : E) (value : first.obj point) :
    (familyEqHom same.symm).app point ((familyEqHom same).app point value) = value := by
  cases same
  rfl

theorem familyEqHom_heq {E : Type v} [Category.{u} E] {first second : E ⥤ Type h}
    (same : first = second) (point : E) (value : first.obj point) :
    HEq ((familyEqHom same).app point value) value := by
  cases same
  rfl

theorem inverseAfterFamilyEquality {E : Type v} [Category.{u} E]
    {first middle last : E ⥤ Type h} (same : last = middle)
    (forward : NatTrans first middle) (backward : NatTrans middle first)
    (inverse : ContextualSmallFamilyTypeFormers.composeNat forward backward =
      ContextualSmallFamilyTypeFormers.identityNat first) :
    ContextualSmallFamilyTypeFormers.composeNat
      (ContextualSmallFamilyTypeFormers.composeNat forward (familyEqHom same.symm))
      (ContextualSmallFamilyTypeFormers.composeNat (familyEqHom same) backward) =
        ContextualSmallFamilyTypeFormers.identityNat first := by
  cases same
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  exact congrArg (fun operation : NatTrans first first => operation.app point term) inverse

theorem equalityAfterInverse {E : Type v} [Category.{u} E]
    {first middle last : E ⥤ Type h} (same : last = middle)
    (forward : NatTrans first middle) (backward : NatTrans middle first)
    (inverse : ContextualSmallFamilyTypeFormers.composeNat backward forward =
      ContextualSmallFamilyTypeFormers.identityNat middle) :
    ContextualSmallFamilyTypeFormers.composeNat
      (ContextualSmallFamilyTypeFormers.composeNat (familyEqHom same) backward)
      (ContextualSmallFamilyTypeFormers.composeNat forward (familyEqHom same.symm)) =
        ContextualSmallFamilyTypeFormers.identityNat last := by
  cases same
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  exact congrArg (fun operation : NatTrans middle middle => operation.app point term) inverse

noncomputable def piSubstitution :
    NatTrans (ContextualSmallFamilyUniverse.substitutedFamily (piFamily parent bodyMap) change)
      (freshPi parent bodyMap change) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution change (domain parent) (body parent bodyMap))
    (familyEqHom (freshPi_eq parent bodyMap change).symm)

noncomputable def piSubstitutionInverse :
    NatTrans (freshPi parent bodyMap change)
      (ContextualSmallFamilyUniverse.substitutedFamily (piFamily parent bodyMap) change) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (familyEqHom (freshPi_eq parent bodyMap change))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitutionInverse change (domain parent) (body parent bodyMap))

theorem piSubstitution_left :
    ContextualSmallFamilyTypeFormers.composeNat (piSubstitution parent bodyMap change)
      (piSubstitutionInverse parent bodyMap change) = ContextualSmallFamilyTypeFormers.identityNat
        (ContextualSmallFamilyUniverse.substitutedFamily (piFamily parent bodyMap) change) :=
  inverseAfterFamilyEquality (freshPi_eq parent bodyMap change)
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution change (domain parent) (body parent bodyMap))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitutionInverse change (domain parent) (body parent bodyMap))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_left change (domain parent) (body parent bodyMap))

theorem piSubstitution_right :
    ContextualSmallFamilyTypeFormers.composeNat (piSubstitutionInverse parent bodyMap change)
      (piSubstitution parent bodyMap change) = ContextualSmallFamilyTypeFormers.identityNat
        (freshPi parent bodyMap change) :=
  equalityAfterInverse (freshPi_eq parent bodyMap change)
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution change (domain parent) (body parent bodyMap))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitutionInverse change (domain parent) (body parent bodyMap))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_right change (domain parent) (body parent bodyMap))

noncomputable def piSubstitutionCode (point : other.Elements) : NatTrans
    (ContextualSmallFamilyUniverse.familyCode
      (ContextualSmallFamilyUniverse.substitutedFamily (piFamily parent bodyMap) change) point.1 point.2)
    (ContextualSmallFamilyUniverse.familyCode (freshPi parent bodyMap change) point.1 point.2) :=
  ContextualSmallFamilyTypeFormerCoherence.restrictNat
    (ContextualSmallFamilyUniverse.futureElement point.1 point.2) (piSubstitution parent bodyMap change)

noncomputable def piSubstitutionSections :
    (ContextualSmallFamilyUniverse.substitutedFamily (piFamily parent bodyMap) change).sections ≃
      (freshPi parent bodyMap change).sections :=
  (ContextualSmallFamilyTypeFormerCoherence.productSectionComparison change (domain parent) (body parent bodyMap)).trans
    (ContextualSmallFamilyUniverse.typeEqualityEquiv
      (congrArg (fun family : other.Elements ⥤ Type u => (family.sections : Type (max u w)))
        (freshPi_eq parent bodyMap change).symm))

theorem freshSigma_full_decode : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (freshSigma parent bodyMap change)) = freshSigma parent bodyMap change :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem freshPi_full_decode : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (freshPi parent bodyMap change)) = freshPi parent bodyMap change :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem freshW_full_decode : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (freshW parent bodyMap change)) = freshW parent bodyMap change :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

end Substitution

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosure
