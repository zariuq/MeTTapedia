import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLImpredicativeDenotation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLHenkinFamilySemantics

/-!
# One source value in the simple and dependent-family native denotations

The signature-generic simple denotation and the proof-compiler's dependent
family denotation are different relations over different environments. For
every translated source HOL term, both nonetheless realize the *same source
Henkin value*, with the family relation reading it through its explicit
source-valuation map. This is a comparison on the translated HOL fragment,
not a claim of equivalence for arbitrary native derivations or conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLDenotationComparison

open Mettapedia.Logic
open Mettapedia.Logic.HOL.ImpredicativeConnectives
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLImpredicativeRepresentation

universe u v w
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The two existing native judgments agree through the independently
interpreted source term. The family side uses the actual object substitution
and source valuation retained by its semantic state. -/
theorem translated_hol_common_source_value
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term Const gamma type)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : HOLNativeGenericProofCompiler.HenkinFamilySemantics.State
      signature model objects) :
    NativeHOLSignatureDenotation.Denotes signature model
      (translate signature term)
      (fun valuation => model.denote term valuation) ∧
    HOLNativeGenericProofCompiler.HenkinFamilySemantics.Denotes
      signature model state.context
      (subst objects (translate signature term))
      (HOLNativeGenericProofCompiler.HenkinFamilySemantics.typeFamily model type)
      (fun environment => model.denote term (state.valuation environment)) := by
  constructor
  · exact NativeHOLImpredicativeDenotation.translate_denotes signature model term
  · have represented := translate_eq signature term
    have family :=
      HOLNativeGenericProofCompiler.HenkinFamilySemantics.representation_denotes
        (expand term) represented state
    simpa only [HOL.ImpredicativeConnectives.denote_expand] using family

/-- The comparison is inhabited at the empty object telescope; it does not
rely on an assumed or impossible mixed state. -/
def closedState (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const) :
    HOLNativeGenericProofCompiler.HenkinFamilySemantics.State
      (gamma := []) (n := 0) signature model (ids : Sub Tower.Head 0 0) where
  context := .nil
  valuation := fun _ =>
    (fun {type} (index : HOL.Var ([] : HOL.Ctx Base) type) => nomatch index)
  objectsDenote := by
    intro type index
    nomatch index

theorem closedState_has_environment
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const) :
    Nonempty (closedState signature model).context.Environment :=
  ⟨PUnit.unit⟩

/-- Both native relations interpret every closed translated HOL term as its
source value. On this concrete state, the native syntax is literally the
same term on both sides because substitution by `ids` is the identity. -/
theorem closed_hol_common_source_value
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const)
    {type : HOL.Ty Base} (term : HOL.Term Const [] type) :
    NativeHOLSignatureDenotation.Denotes signature model
      (translate signature term)
      (fun valuation => model.denote term valuation) ∧
    HOLNativeGenericProofCompiler.HenkinFamilySemantics.Denotes
      signature model (closedState signature model).context
      (translate signature term)
      (HOLNativeGenericProofCompiler.HenkinFamilySemantics.typeFamily model type)
      (fun environment => model.denote term
        ((closedState signature model).valuation environment)) := by
  simpa only [subst_ids] using
    translated_hol_common_source_value signature model term
      (closedState signature model)

#print axioms translated_hol_common_source_value
#print axioms closedState_has_environment
#print axioms closed_hol_common_source_value

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLDenotationComparison
