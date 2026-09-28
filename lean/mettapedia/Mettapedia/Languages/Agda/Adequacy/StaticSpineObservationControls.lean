import Mettapedia.Languages.Agda.Adequacy.StaticSpineObservation
import Mettapedia.Languages.Agda.StaticSpecification.Examples

/-!
# Actual typing witnesses for administrative observation

The controls use retained native and source derivations. Two ordered arguments,
an administrative argument, append, and both conversion directions use the
six constructor interpretations. Distinct native representations and histories
can have the same observation; their native trees remain in the witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Observation.SpineControls

open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory
open Structural (sig scope)

def domain : StaticSpecification.Ty 0 := .universe 1
def arrow : StaticSpecification.Ty 0 := .pi domain (.noBind domain)
def doubleArrow : StaticSpecification.Ty 0 := .pi domain (.noBind arrow)
def nativeDomain := embedTypeParameter domain
def nativeArrow := embedTypeParameter arrow
def nativeDoubleArrow := embedTypeParameter doubleArrow

def firstArgument : StaticSpecification.Term 0 := .sort 0
def secondArgument : StaticSpecification.Term 0 :=
  StaticSpecification.Examples.closedIdentity.app firstArgument

def firstArgumentTyped : StaticSpecification.Typing .nil firstArgument domain := .sort 0 .nil
def secondArgumentTyped : StaticSpecification.Typing .nil secondArgument domain :=
  .app StaticSpecification.Examples.closedIdentityTyping firstArgumentTyped

noncomputable def firstWitness := TypingWitness.ofSource firstArgumentTyped
noncomputable def secondCanonicalWitness := TypingWitness.ofSource secondArgumentTyped

def domainNil : ActionWitness (.nil : Structural.Statics.RawContext 0) .nil
    nativeDomain.code Structural.nil nativeDomain.code domain [] domain :=
  .nil rfl (type_embed domain)

noncomputable def secondWitness := ActionWitness.elimination secondCanonicalWitness domainNil

def firstSpine : Structural.Spine (scope 0) :=
  Structural.cons (Structural.apply (embedTerm firstArgument)) Structural.nil
def secondSpine : Structural.Spine (scope 0) :=
  Structural.cons (Structural.apply (Structural.eliminate (embedTerm secondArgument) Structural.nil)) Structural.nil

noncomputable def firstAction : ActionWitness (.nil : Structural.Statics.RawContext 0) .nil
    nativeDoubleArrow.code firstSpine nativeArrow.code doubleArrow [.apply firstArgument] arrow :=
  ActionWitness.cons (A := nativeDomain) (B := .noBind nativeArrow)
    (typeBody_embed (.noBind arrow)) firstWitness
    (ActionWitness.nil rfl (type_embed arrow))

noncomputable def secondAction : ActionWitness (.nil : Structural.Statics.RawContext 0) .nil
    nativeArrow.code secondSpine nativeDomain.code arrow [.apply secondArgument] domain :=
  ActionWitness.cons (A := nativeDomain) (B := .noBind nativeDomain)
    (typeBody_embed (.noBind domain)) secondWitness domainNil

noncomputable def appendedAction := ActionWitness.append firstAction secondAction

noncomputable def functionWitness :=
  TypingWitness.ofSource StaticSpecification.Examples.constantFunctionTyping

noncomputable def appliedWitness := ActionWitness.elimination functionWitness appendedAction

/-- Both the native typing and this source typing are fields of the same witness. -/
noncomputable def orderedSourceTyping : StaticSpecification.Typing .nil
    ((StaticSpecification.Examples.constantFunction.app firstArgument).app secondArgument) domain :=
  appliedWitness.source

theorem administrative_argument_observation :
    term (Structural.eliminate (embedTerm secondArgument) Structural.nil) = some secondArgument :=
  secondWitness.term_eq

theorem administrative_argument_is_not_canonical :
    Structural.eliminate (embedTerm secondArgument) Structural.nil ≠ embedTerm secondArgument := by
  intro same
  cases same

theorem ordered_arguments_are_distinct : firstArgument ≠ secondArgument := by
  intro same
  cases same

def dependentBody : Structural.Statics.TypeBody 0 :=
  .bind ⟨1, Structural.eliminate (.var .zero) Structural.nil⟩

theorem dependent_body_observation :
    typeBody dependentBody = some (.bind (.el 1 (.var 0))) := rfl

theorem dependent_instantiation_observation :
    type (dependentBody.instantiate (embedTerm firstArgument)).code = some (.el 1 firstArgument) :=
  typeBody_instantiate dependentBody dependent_body_observation (term_embed firstArgument)

def betaTypeEquality : StaticSpecification.TypeEq .nil
    (.el 1 secondArgument) (.universe 0) :=
  .atSort StaticSpecification.Examples.closedBeta

noncomputable def equalityWitness := TypeEqualityWitness.ofSource betaTypeEquality

noncomputable def convertedInput := ActionWitness.inputConversion equalityWitness
  (ActionWitness.nil rfl (type_embed (.universe 0)))

noncomputable def convertedOutput := ActionWitness.outputConversion
  (ActionWitness.nil rfl (type_embed (.el 1 secondArgument))) equalityWitness

theorem conversions_change_the_type_code :
    embedTy (.el 1 secondArgument) ≠ embedTy (StaticSpecification.Ty.universe (n := 0) 0) := by
  intro same
  cases same

theorem conversion_histories_remain_distinct : convertedInput.native ≠ convertedOutput.native := by
  intro same
  have shape := (IndexedPolynomial.Fix.roll.inj same).1
  cases shape

/-- Different native conversion positions can yield the same source proof transformer. -/
theorem conversion_source_actions_agree (f : StaticSpecification.Term 0) :
    convertedInput.source (f := f) = convertedOutput.source (f := f) := rfl

def appendedNil := ActionWitness.append domainNil domainNil

noncomputable def directAdministrative := ActionWitness.elimination firstWitness domainNil
noncomputable def appendedAdministrative := ActionWitness.elimination firstWitness appendedNil

theorem raw_administrative_representations_differ :
    Structural.eliminate (embedTerm firstArgument) Structural.nil ≠
      Structural.eliminate (embedTerm firstArgument) (Structural.append Structural.nil Structural.nil) := by
  intro same
  cases same

theorem two_administrative_observations_agree :
    term (Structural.eliminate (embedTerm firstArgument) Structural.nil) =
      term (Structural.eliminate (embedTerm firstArgument) (Structural.append Structural.nil Structural.nil)) := rfl

/-- The interpretation can even identify source receipts, while retaining both native witnesses. -/
theorem source_typing_receipts_can_agree : directAdministrative.source = appendedAdministrative.source := rfl

end Mettapedia.Languages.Agda.StaticAdequacy.Observation.SpineControls
