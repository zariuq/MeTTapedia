import Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualFamilies

/-!
# Contextual dependent formation from bare material seeds

Every primitive dictionary is constructed from a bare lower-level carrier
and its authored actual member maps. This includes arbitrary dependent
bodies over actual raised comprehension contexts. The existing full-future
Pi, material Sigma, discrete identity and hereditary W constructors then
form their actual graphs and inverse decoders at the common successor
bound. The external generated carrier enclosure lives one further level up.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualGeneration

open CategoryTheory ContextualGeneratedUniverse BareContextualFamilies

universe u
variable {D : Type (u + 1)} [Category.{u + 1} D]

def Seeds (context : LabelledContext D) : Type (u + 2) := ULift.{u + 2, u + 1} (Family.{u, u + 1} context)

def seedModel (context : LabelledContext D) (seed : Seeds context) : MaterialFamily context := seed.down.atRaised

variable (arrows : (first second : Dᵒᵖ) → ArgumentCoding (first ⟶ second))

def generated {context : LabelledContext D} (family : Family.{u, u + 1} context) :
    Generation Seeds seedModel arrows family.atRaised :=
  Generation.seed (seeds := Seeds) (seedModel := seedModel) (arrows := arrows) context (ULift.up family)

variable {context : LabelledContext D} (domain : Family.{u, u + 1} context)
variable (body : Family.{u, u + 1} domain.atRaised.extension)

def piGenerated : Generation Seeds seedModel arrows (domain.atRaised.pi body.atRaised arrows) :=
  .pi (generated arrows domain) (generated arrows body)

def sigmaGenerated : Generation Seeds seedModel arrows (domain.atRaised.sigma body.atRaised) :=
  .sigma (generated arrows domain) (generated arrows body)

def wGenerated : Generation Seeds seedModel arrows (domain.atRaised.w body.atRaised arrows) :=
  .w (generated arrows domain) (generated arrows body)

def identityGenerated (left right : domain.atRaised.family.sections) :
    Generation Seeds seedModel arrows (domain.atRaised.identity left right) :=
  .identity (generated arrows domain) left right

theorem pi_evaluation (point : context.base.Elements)
    (function : (domain.atRaised.pi body.atRaised arrows).family.obj point)
    (argument : PowerClassContextualMaterialization.FutureArguments domain.atRaised.family point) :
    LabelledDependentProducts.evalValue (domain.atRaised.futureCoding arrows point)
      (domain.atRaised.futureOutputs body.atRaised point)
      (((domain.atRaised.pi body.atRaised arrows).model point).value function) argument =
        HSet.lift (function.app argument.1.1 argument.1.2 argument.2).val :=
  domain.atRaised.pi_evaluation body.atRaised arrows point function argument

theorem sigma_first (point : context.base.Elements) (pair : (domain.atRaised.sigma body.atRaised).family.obj point) :
    HSet.fst (((domain.atRaised.sigma body.atRaised).model point).value pair) = HSet.lift pair.1.val :=
  domain.atRaised.sigma_first body.atRaised point pair

theorem sigma_second (point : context.base.Elements) (pair : (domain.atRaised.sigma body.atRaised).family.obj point) :
    HSet.snd (((domain.atRaised.sigma body.atRaised).model point).value pair) = HSet.lift pair.2.val :=
  domain.atRaised.sigma_second body.atRaised point pair

theorem identity_inhabited (left right : domain.atRaised.family.sections) (point : context.base.Elements) :
    Nonempty ((domain.atRaised.identity left right).family.obj point) ↔ left.val point = right.val point := by
  constructor
  · rintro ⟨witness⟩
    exact PresheafIdentityWitness.decode witness
  · intro same
    exact ⟨PresheafIdentityWitness.encode same⟩

theorem dependent_types_enclosed (point : context.base.Elements) :
    HSet.lift ((domain.atRaised.pi body.atRaised arrows).model point).carrier ∈ enclosure Seeds seedModel arrows context point ∧
    HSet.lift ((domain.atRaised.sigma body.atRaised).model point).carrier ∈ enclosure Seeds seedModel arrows context point ∧
    HSet.lift ((domain.atRaised.w body.atRaised arrows).model point).carrier ∈ enclosure Seeds seedModel arrows context point :=
  ⟨generated_mem_enclosure Seeds seedModel arrows (piGenerated arrows domain body) point,
    generated_mem_enclosure Seeds seedModel arrows (sigmaGenerated arrows domain body) point,
    generated_mem_enclosure Seeds seedModel arrows (wGenerated arrows domain body) point⟩

theorem identity_enclosed (left right : domain.atRaised.family.sections) (point : context.base.Elements) :
    HSet.lift ((domain.atRaised.identity left right).model point).carrier ∈
      enclosure Seeds seedModel arrows context point :=
  generated_mem_enclosure Seeds seedModel arrows (identityGenerated arrows domain left right) point

variable {family : MaterialFamily context}

def memberDecoder (derivation : Generation Seeds seedModel arrows family) (point : context.base.Elements) :
    {value : HSet.{u + 1} // value ∈ (family.model point).carrier} ≃ family.family.obj point :=
  decode Seeds seedModel arrows derivation point

theorem memberDecoder_encode_decode (derivation : Generation Seeds seedModel arrows family)
    (point : context.base.Elements) (member : {value : HSet.{u + 1} // value ∈ (family.model point).carrier}) :
    (memberDecoder arrows derivation point).symm (memberDecoder arrows derivation point member) = member :=
  encode_decode Seeds seedModel arrows derivation point member

theorem memberDecoder_decode_encode (derivation : Generation Seeds seedModel arrows family)
    (point : context.base.Elements) (term : family.family.obj point) :
    memberDecoder arrows derivation point ((memberDecoder arrows derivation point).symm term) = term :=
  decode_encode Seeds seedModel arrows derivation point term

theorem memberDecoder_natural (derivation : Generation Seeds seedModel arrows family)
    {point next : context.base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u + 1} // value ∈ (family.model point).carrier}) :
    memberDecoder arrows derivation next (family.memberRestriction step member) =
      family.family.map step (memberDecoder arrows derivation point member) :=
  family.memberRestriction_decode step member

theorem memberEncoder_natural (derivation : Generation Seeds seedModel arrows family)
    {point next : context.base.Elements} (step : point ⟶ next) (term : family.family.obj point) :
    family.memberRestriction step ((memberDecoder arrows derivation point).symm term) =
      (memberDecoder arrows derivation next).symm (family.family.map step term) :=
  family.memberRestriction_encode step term

end Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualGeneration
