import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListInduction
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListEquationInputs

/-!
# Supplying the original compiled proof's theory inputs

Native witnesses of represented source premises are applied to the retained
compiled proof using the actual native implication eliminator. All five
original inputs are preserved in their original order. The derived interface
keeps source representation, formed target propositions and native proof
typing connected throughout the application.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeListProofInputs

open Presentation Presentation.FormationSensitive ConstantExpansion
open HOLNativeListConstantBodies HOLNativeListDeclarationInterpretation
open FormationSensitiveHOLProofFamily (proof)
open FormationSensitiveHOLUniformList (rawImp)
open Mettapedia.Logic HOL.UniformListInduction
open HOLLeibnizNativeProofTranslation (represent)

theorem represented_proposition_typed {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {formula : HOL.Formula Symbol []} {code : Tower.Tm 0}
    (represented : represent formula = some code) :
    Typing .nil (expand (bodies element) code) (.const `HOLUniformList.prop) := by
  have sourceTyped := FormationSensitiveHOLProofFamily.include_typed
    (FormationSensitiveHOLInterface.represent_typed
      FormationSensitiveHOLLeibnizInterface.signature formula represented)
  exact (interpretation elementTyped).typing sourceTyped

theorem application {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {premise conclusion : HOL.Formula Symbol []} {major minor : Tower.Tm 0}
    (majorInput : ∃ code, represent (.imp premise conclusion) = some code ∧
      Typing .nil major (expand (bodies element) (proof code)))
    (minorInput : ∃ code, represent premise = some code ∧
      Typing .nil minor (expand (bodies element) (proof code))) :
    ∃ code, represent conclusion = some code ∧
      Typing .nil (.app major minor) (expand (bodies element) (proof code)) := by
  obtain ⟨majorCode, majorRepresented, majorTyped⟩ := majorInput
  obtain ⟨premiseCode, premiseRepresented, premiseTyped⟩ := minorInput
  rw [HOLLeibnizNativeProofTranslation.represent_imp, premiseRepresented] at majorRepresented
  cases conclusionRepresented : represent conclusion with
  | none => simp only [conclusionRepresented] at majorRepresented; cases majorRepresented
  | some conclusionCode =>
      rw [conclusionRepresented] at majorRepresented
      change some (rawImp premiseCode conclusionCode) = some majorCode at majorRepresented
      have codeEquality : rawImp premiseCode conclusionCode = majorCode := by
        exact Option.some.inj majorRepresented
      subst majorCode
      have premiseFormed := represented_proposition_typed elementTyped premiseRepresented
      have conclusionFormed := represented_proposition_typed elementTyped conclusionRepresented
      have applied := FormationSensitiveMixedHOLProofRules.implication_elim
        premiseFormed conclusionFormed majorTyped premiseTyped
      exact ⟨conclusionCode, rfl, applied⟩

def applyFive (native lengthCons lengthNil mapCons mapNil induction : Tower.Tm 0) : Tower.Tm 0 :=
  .app (.app (.app (.app (.app native lengthCons) lengthNil) mapCons) mapNil) induction

/-- No source premise is silently deleted, even though the retained proof
does not use its two length inputs. Supplying genuine witnesses discharges
the exact original conditional theorem. -/
theorem original_five_inputs {element lengthConsWitness lengthNilWitness mapConsWitness mapNilWitness inductionWitness : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    (lengthConsInput : ∃ code, represent (lengthCons (Γ := [])) = some code ∧
      Typing .nil lengthConsWitness (expand (bodies element) (proof code)))
    (lengthNilInput : ∃ code, represent (lengthNil (Γ := [])) = some code ∧
      Typing .nil lengthNilWitness (expand (bodies element) (proof code)))
    (mapConsInput : ∃ code, represent (mapCons (Γ := [])) = some code ∧
      Typing .nil mapConsWitness (expand (bodies element) (proof code)))
    (mapNilInput : ∃ code, represent (mapNil (Γ := [])) = some code ∧
      Typing .nil mapNilWitness (expand (bodies element) (proof code)))
    (inductionInput : ∃ code, represent (inductionPrinciple (Γ := [])) = some code ∧
      Typing .nil inductionWitness (expand (bodies element) (proof code))) :
    ∃ code, represent (HOL.UniformListMapFusion.mapFusion (Γ := [])) = some code ∧
      Judgment rules .nil
        (applyFive (interpretedProof element) lengthConsWitness lengthNilWitness mapConsWitness mapNilWitness inductionWitness)
        (expand (bodies element) (proof code)) := by
  obtain ⟨code, represented, admitted⟩ := original_compiled_judgment elementTyped
  have first := application elementTyped ⟨code, represented, admitted.typing⟩ lengthConsInput
  have second := application elementTyped first lengthNilInput
  have third := application elementTyped second mapConsInput
  have fourth := application elementTyped third mapNilInput
  obtain ⟨finalCode, finalRepresented, finalTyped⟩ := application elementTyped fourth inductionInput
  exact ⟨finalCode, finalRepresented, .nil, finalTyped⟩

/-- The original retained compiler output, interpreted into native lists and
applied to independently constructed witnesses of its five source inputs. -/
def nativeMapFusionProof (element : Tower.Tm 0) : Tower.Tm 0 :=
  applyFive (interpretedProof element)
    (.lam (.lam (.lam (.lam (.var 0)))))
    (.lam (.lam (.var 0)))
    (.lam (.lam (.lam (.lam (.lam (.var 0))))))
    (.lam (.lam (.lam (.var 0))))
    (HOLNativeListInduction.inductionWitness (liftClosed element))

/-- All five original theory premises are discharged in the unchanged mixed
presentation. The source theorem remains uniformly quantified; its sequence
and map constants are interpreted by actual native List and map operations.
No equation proof or induction proof is supplied as an opaque declaration. -/
theorem native_map_fusion {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    ∃ code, represent (HOL.UniformListMapFusion.mapFusion (Γ := [])) = some code ∧
      Judgment rules .nil (nativeMapFusionProof element)
        (expand (bodies element) (proof code)) :=
  original_five_inputs elementTyped
    (HOLNativeListEquationInputs.lengthCons_input elementTyped)
    (HOLNativeListEquationInputs.lengthNil_input elementTyped)
    (HOLNativeListEquationInputs.mapCons_input elementTyped)
    (HOLNativeListEquationInputs.mapNil_input elementTyped)
    (HOLNativeListInduction.original_induction_input elementTyped)

/-- A concrete member uses the existing small count carrier, rather than an
uninstantiated assumption about an element interpretation. The declared count
signature is retained; no natural-number interpretation is asserted here. -/
theorem count_map_fusion :
    ∃ code, represent (HOL.UniformListMapFusion.mapFusion (Γ := [])) = some code ∧
      Judgment rules .nil (nativeMapFusionProof countType)
        (expand (bodies countType) (proof code)) :=
  native_map_fusion (count_typed .nil)

#print axioms represented_proposition_typed
#print axioms application
#print axioms original_five_inputs
#print axioms native_map_fusion
#print axioms count_map_fusion

end HOLNativeListProofInputs
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
