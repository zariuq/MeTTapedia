import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfSubstitution
import Mettapedia.TypeTheory.ContextualCwfUniverseLift

/-!
# Generated source declarations at arbitrary original carrier levels

The earned contextual universe lift places contexts and substitutions at a
common level. Original types and terms keep their independent levels. The
generated declaration then retains every original source term, with complete
section recovery and the actual original substitution and pairing readouts.
This is an external carrier comparison, not an internal universe type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfUniverseReadout

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open SourceCwfDeclarations
open DisplayedPresheafComprehension

universe u v w w'
variable (K : Cwf.{u, v, w, w'})

abbrev raised : Cwf.{max u v, max u v, w, w'} :=
  ContextualCwfUniverseLift.lift.{u, v, w, w', max u v, max u v, 0, 0} K

abbrev raisedContext (context : K.Ctx) : (raised K).Ctx := ⟨context⟩
abbrev raisedType {context : K.Ctx} (type : K.Ty context) :
    (raised K).Ty (raisedContext K context) := ⟨type⟩
abbrev raisedTerm {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    (raised K).Tm (raisedContext K context) (raisedType K type) := ⟨term⟩
abbrev raisedSubstitution {source target : K.Ctx} (before : K.Sub source target) :
    (raised K).Sub (raisedContext K source) (raisedContext K target) := ⟨before⟩

noncomputable section

/-- All original source terms are recovered from all generated native sections. -/
def completeOriginalTermEquiv {context : K.Ctx} (type : K.Ty context) :
    K.Tm context type ≃ (sourceMeaning (raisedType K type)).decoded.sections :=
  (Equiv.ulift : (raised K).Tm (raisedContext K context) (raisedType K type) ≃
    K.Tm context type).symm.trans (sourceTermEquiv (raisedType K type))

def originalValue {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    (sourceMeaning (raisedType K type)).decoded.sections := sourceValue (raisedTerm K term)

def recoverOriginalTerm {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning (raisedType K type)).decoded.sections) : K.Tm context type :=
  (completeOriginalTermEquiv K type).symm sectionValue

theorem recover_originalValue {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    recoverOriginalTerm K (originalValue K term) = term :=
  (completeOriginalTermEquiv K type).symm_apply_apply term

theorem originalValue_recover {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning (raisedType K type)).decoded.sections) :
    originalValue K (recoverOriginalTerm K sectionValue) = sectionValue :=
  (completeOriginalTermEquiv K type).apply_symm_apply sectionValue

theorem originalValue_injective {context : K.Ctx} {type : K.Ty context} :
    Function.Injective (originalValue K (type := type)) :=
  (completeOriginalTermEquiv K type).injective

theorem complete_original_unique {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning (raisedType K type)).decoded.sections) :
    ∃! term : K.Tm context type, originalValue K term = sectionValue := by
  refine ⟨recoverOriginalTerm K sectionValue, originalValue_recover K sectionValue, ?_⟩
  intro term read
  exact originalValue_injective K (read.trans (originalValue_recover K sectionValue).symm)

/-- The whole represented arrow retains the original environment and term. -/
theorem originalValue_pair_readout {context world : K.Ctx} {type : K.Ty context}
    (term : K.Tm context type) (environment : K.Sub world context) :
    ((originalValue K term).val
      ⟨op (⟨raisedContext K world⟩ : Base (raised K)),
        ⟨PUnit.unit, raisedSubstitution K environment⟩⟩).val.down =
      K.pair environment type (K.tmSub term environment) := rfl

theorem original_parser_conservative {context : K.Ctx} {type : K.Ty context}
    (first second : K.Tm context type) :
    (model (raised K)).evaluateTerm (objectScope (⟨raisedContext K context⟩ : Base (raised K)))
        (sourceTerm (raisedTerm K first)) =
      (model (raised K)).evaluateTerm (objectScope (⟨raisedContext K context⟩ : Base (raised K)))
        (sourceTerm (raisedTerm K second)) ↔ first = second := by
  rw [parser_conservative]
  exact ⟨fun equal => congrArg ULift.down equal, fun equal => congrArg ULift.up equal⟩

/-- The actual generated substituted term keeps the original substituted
term through the earned source family comparison. -/
theorem original_generated_substitution {context replacement : K.Ctx} {type : K.Ty context}
    (term : K.Tm context type) (before : K.Sub replacement context) :
    (model (raised K)).evaluateTerm
        (objectScope (⟨raisedContext K replacement⟩ : Base (raised K)))
        ((sourceTerm (raisedTerm K term)).substitute
          (originalSubstitution
            (show (⟨raisedContext K replacement⟩ : Base (raised K)) ⟶
              ⟨raisedContext K context⟩ from raisedSubstitution K before))) =
      some ⟨(sourceMeaning (raisedType K type)).reindex
        (originalMap (show (⟨raisedContext K replacement⟩ : Base (raised K)) ⟶
          ⟨raisedContext K context⟩ from raisedSubstitution K before)),
        (Functor.sectionsFunctor _).map
          (sourceSubstitutionIso (raisedType K type) (raisedSubstitution K before)).hom
          (sourceValue (raisedTerm K (K.tmSub term before)))⟩ :=
  generated_source_term_substitution (raisedTerm K term) (raisedSubstitution K before)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfUniverseReadout
