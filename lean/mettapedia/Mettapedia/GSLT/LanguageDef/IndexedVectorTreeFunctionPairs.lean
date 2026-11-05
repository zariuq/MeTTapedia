import Mettapedia.Logic.HOL.ConstructorFunctionPairs
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditionsControls

/-!
# Evidence pairs on the existing recursive-space/function-vector carrier

The reserved tag stores an actual two-child function array in the same raw
constructor. A fixed branch-row payload needs no original-answer filler.
Retained projection laws use the existing element-selection and recursion
premises plus the actual raw constructor field law. The chosen model realizes
all ten joined premises and distinguishes swapped pair components.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeFunctionPairs

open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding
open FiniteConstructorFieldEmbeddingControls (Base N A E P)
open IndexedVectorTreeFunctionVectorFixture

def rawLaw : ClosedFormula Const := ConstructorProjections.fieldInjective given.raw
def assumptions : List (ClosedFormula Const) := rawLaw :: IndexedVectorTreeFunctionVectorFixture.assumptions

def input : ConstructorFunctionPairs.Inputs ops P where
  raw := given.raw
  tag := numeral 2
  payload := encode (VectorTreeFieldEmbedding.rawSignature N A)
    (VectorTreeFieldEmbedding.branchOccurrence (number := N) (element := A)) (zero,zero,PUnit.unit)
  bottom := bottom

def pairs : PredicateSigma.Operations Const E := input.operations

def arrayPremises : ops.ComputationPremises assumptions :=
  IndexedVectorTreeFunctionVectorFixture.premises.prepend rawLaw
theorem arrayPremises_free : arrayPremises.FunctionExtensionalityFree :=
  IndexedVectorTreeFunctionVectorFixture.premises.prepend_free rawLaw
    IndexedVectorTreeFunctionVectorFixture.premises_free

def pairPremises : input.Premises assumptions where
  choice := arrayPremises.elementChoice
  recursion := arrayPremises.elementRecursion
  injectivity := .hyp ⟨0,by simp [assumptions]⟩
theorem pairPremises_free : pairPremises.Free :=
  ⟨arrayPremises_free.1,arrayPremises_free.2.1,True.intro⟩

@[irreducible] def firstLaw : ProofSyntax Const assumptions (PredicateSigma.firstLaw pairs) :=
  input.first_law pairPremises
@[irreducible] def secondLaw : ProofSyntax Const assumptions (PredicateSigma.secondLaw pairs) :=
  input.second_law pairPremises
theorem firstLaw_free : firstLaw.FunctionExtensionalityFree := by
  unfold firstLaw
  exact input.first_law_free pairPremises pairPremises_free
theorem secondLaw_free : secondLaw.FunctionExtensionalityFree := by
  unfold secondLaw
  exact input.second_law_free pairPremises pairPremises_free

theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := by
  intro formula present
  rcases List.mem_cons.mp present with rfl | inherited
  · exact (model.models_iff_denote_closed rawLaw values).mp raw_injective_holds
  · exact IndexedVectorTreeFunctionVectorFixture.assumptions_realizable formula inherited

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

def firstValue : ClosedTerm Const E := IndexedVectorTreeNativeChildConditionsControls.solvedValue
def secondValue : ClosedTerm Const E := IndexedVectorTreeNativeChildConditionsControls.branchValue
def packed : ClosedTerm Const E := PredicateSigma.pair pairs firstValue secondValue
def swapped : ClosedTerm Const E := PredicateSigma.pair pairs secondValue firstValue

theorem first_projection_holds : model.denote (PredicateSigma.first pairs packed) values = model.denote firstValue values :=
  model.eq_of_eqv_of_fullDomains full (sound (input.first_at firstValue secondValue pairPremises))
theorem second_projection_holds : model.denote (PredicateSigma.second pairs packed) values = model.denote secondValue values :=
  model.eq_of_eqv_of_fullDomains full (sound (input.second_at firstValue secondValue pairPremises))
theorem swapped_first_projection_holds :
    model.denote (PredicateSigma.first pairs swapped) values = model.denote secondValue values :=
  model.eq_of_eqv_of_fullDomains full (sound (input.first_at secondValue firstValue pairPremises))

theorem recovered_components_distinct :
    model.denote (PredicateSigma.first pairs packed) values ≠ model.denote (PredicateSigma.second pairs packed) values := by
  intro same
  exact IndexedVectorTreeNativeChildConditionsControls.constructor_values_distinct
    (first_projection_holds.symm.trans (same.trans second_projection_holds))

theorem swapped_components_refused : model.denote packed values ≠ model.denote swapped values := by
  intro same
  have observed := congrArg (model.denote pairs.first values) same
  change model.denote (PredicateSigma.first pairs packed) values =
    model.denote (PredicateSigma.first pairs swapped) values at observed
  exact IndexedVectorTreeNativeChildConditionsControls.constructor_values_distinct
    (first_projection_holds.symm.trans (observed.trans swapped_first_projection_holds))

theorem pair_laws_realized :
    model.models (PredicateSigma.firstLaw pairs) ∧ model.models (PredicateSigma.secondLaw pairs) :=
  ⟨(model.models_iff_denote_closed _ values).mpr (sound firstLaw),
    (model.models_iff_denote_closed _ values).mpr (sound secondLaw)⟩

#print axioms firstLaw_free
#print axioms secondLaw_free
#print axioms assumptions_realizable
#print axioms first_projection_holds
#print axioms second_projection_holds
#print axioms recovered_components_distinct
#print axioms swapped_components_refused

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeFunctionPairs
