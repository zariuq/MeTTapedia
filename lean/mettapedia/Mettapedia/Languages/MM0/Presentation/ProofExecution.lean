import Mettapedia.Languages.MM0.Presentation.ProofInstantiation

/-! # Lookup and composition laws for supplied MM0 proofs -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalProof

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalConversion
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "A" => proofEquations
local notation "H" => dataEqualityHost

theorem hypothesis_lookup_computes (hypotheses : List Preterm) (index : Nat) :
    Applies P H "mm0:data-at" [encodeExpressions hypotheses, natural index] (encodeResult hypotheses[index]?) := by
  let tail := listAppendProgram ++ ComputationalSupport.supportEquations ++ naturalMembershipProgram ++
    ComputationalDependency.dependencyEquations ++ argumentEquations
  have run := (Applies.append_iff typingProgram tail computationalHost (by decide)
    "mm0:data-at" (by decide) _ _).mpr (at_computes (hypotheses.map encode) index)
  have inArguments : Applies argumentProgram computationalHost "mm0:data-at"
      [encodeExpressions hypotheses, natural index] (encodeItemResult (hypotheses.map encode)[index]?) := by
    simpa only [argumentProgram, ComputationalDependency.dependencyProgram,
      ComputationalSupport.supportProgram, tail, List.append_assoc, encodeExpressions] using run
  have result := conversion_reused _ (by decide) _ _
    (ComputationalConversion.argument_reused _ (by decide) _ _ inArguments)
  rw [List.getElem?_map] at result
  cases found : hypotheses[index]? <;> simpa [found, encodeItemResult, encodeResult] using result

theorem theorem_lookup_computes (theorems : TheoremTable) (index : Nat) :
    Applies P H "nik:nat-table-get" [encodeTheorems theorems, natural index]
      (encodeLookupResult ((theoremsOf theorems index).map encodeTheorem)) := by
  have run := (Applies.frame_iff naturalLookupProgram
    (ComputationalInstantiation.instantiationProgram ++ ComputationalFreshDummies.freshEquations) unfoldingEquations
    computationalHost (by decide) (by decide) "nik:nat-table-get" (by decide) _ _).mpr
      (natural_lookup_computes encodeTheorem theorems index)
  have inUnfolding : Applies unfoldingProgram computationalHost "nik:nat-table-get"
      [encodeTheorems theorems, natural index]
      (encodeLookupResult ((theoremsOf theorems index).map encodeTheorem)) := by
    simpa only [unfoldingProgram, List.append_assoc, encodeTheorems, theoremsOf] using run
  have used : "nik:nat-table-get" ∈ unfoldingProgram.calledHeads := by
    simp only [unfoldingProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  have included : "nik:nat-table-get" ∈ conversionProgram.calledHeads := by
    simp only [conversionProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl used
  exact conversion_reused _ included _ _
    (ComputationalConversion.unfolding_reused _ used _ _ inUnfolding)

theorem premises_computes (actual : Option (List Preterm)) (premises : List Preterm) (conclusion : Preterm) :
    Applies P H "mm0:proof-premises" [encodeResults actual, encodeExpressions premises, encode conclusion]
      (encodeResult (do
        let actual ← actual
        if actual = premises then some conclusion else none)) := by
  cases actual with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some actual =>
      refine proof_equation (equation := A[23]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (actual = premises)), encode conclusion])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · refine Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ?_
        simpa only [encoded_expression_list_equality] using
          data_equality_computes P (encodeExpressions actual) (encodeExpressions premises) (by rfl)
      · by_cases same : actual = premises <;>
          simp [same, boolean] <;>
          exact ⟨2, by rw [proof_apply _ (by decide)]; rfl⟩

theorem converted_left_computes (actual : Option Preterm) (left right : Preterm) :
    Applies P H "mm0:proof-left" [encodeResult actual, encode left, encode right]
      (encodeResult (do
        let actual ← actual
        if actual = left then some right else none)) := by
  cases actual with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some actual =>
      refine proof_equation (equation := A[29]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (actual = left)), encode right])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · refine Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ?_
        simpa only [encoded_preterm_equality] using
          data_equality_computes P (encode actual) (encode left) (by rfl)
      · by_cases same : actual = left <;>
          simp [same, boolean] <;>
          exact ⟨2, by rw [proof_apply _ (by decide)]; rfl⟩

theorem proof_tail_computes (first : Preterm) (rest : Option (List Preterm)) :
    Applies P H "mm0:proof-tail" [encodeResults rest, encode first]
      (encodeResults (rest.map (first :: ·))) := by
  cases rest with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some rest =>
      refine proof_equation (equation := A[38]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (.constructor (by rfl) (by rfl))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (.primitive (by rfl) (by rfl))

theorem proof_child_computes (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (children : List ProofWitness)
    (first : Option Preterm) (rest : Option (List Preterm))
    (computed : Applies P H "mm0:proof-children"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProofs children] (encodeResults rest)) :
    Applies P H "mm0:proof-child"
      [encodeResult first, encodeTable table, encodeDefinitions definitions, encodeTheorems theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProofs children]
      (encodeResults (do
        let first ← first
        let rest ← rest
        pure (first :: rest))) := by
  cases first with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some first =>
      refine proof_equation (equation := A[36]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [encodeResults rest, encode first])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) computed
      · simpa [Option.map_eq_bind] using proof_tail_computes first rest

theorem proof_instance_computes (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (children : List ProofWitness)
    (instantiated : Option TheoremInstance) (premises : Option (List Preterm))
    (computed : Applies P H "mm0:proof-children"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProofs children] (encodeResults premises)) :
    Applies P H "mm0:proof-instance"
      [encodeInstance instantiated, encodeTable table, encodeDefinitions definitions, encodeTheorems theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProofs children]
      (encodeResult (do
        let instantiated ← instantiated
        let premises ← premises
        if premises = instantiated.hypotheses then some instantiated.conclusion else none)) := by
  cases instantiated with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some instantiated =>
      refine proof_equation (equation := A[21]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (premises_computes premises instantiated.hypotheses instantiated.conclusion)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) computed

theorem proof_declaration_computes (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (arguments : List Preterm) (children : List ProofWitness)
    (declaration : Option TheoremDecl) (premises : Option (List Preterm))
    (computed : Applies P H "mm0:proof-children"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProofs children] (encodeResults premises)) :
    Applies P H "mm0:proof-declaration"
      [encodeLookupResult (declaration.map encodeTheorem), encodeTable table, encodeDefinitions definitions,
        encodeTheorems theorems, encodeContext context, encodeExpressions hypotheses, encodeExpressions arguments, encodeProofs children]
      (encodeResult (do
        let declaration ← declaration
        let instantiated ← declaration.instantiate? (signatureOf table) context arguments
        let premises ← premises
        if premises = instantiated.hypotheses then some instantiated.conclusion else none)) := by
  cases declaration with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some declaration =>
      refine proof_equation (equation := A[19]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))
        (proof_instance_computes table definitions theorems context hypotheses children
          (declaration.instantiate? (signatureOf table) context arguments) premises computed)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (theorem_instantiation_computes table context declaration arguments)

theorem proof_converted_computes (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (child : ProofWitness)
    (converted : Option ConversionResult) (actual : Option Preterm)
    (computed : Applies P H "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof child] (encodeResult actual)) :
    Applies P H "mm0:proof-converted"
      [encodeConversion converted, encodeTable table, encodeDefinitions definitions, encodeTheorems theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof child]
      (encodeResult (do
        let converted ← converted
        let actual ← actual
        if actual = converted.left then some converted.right else none)) := by
  cases converted with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some converted =>
      refine proof_equation (equation := A[27]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (converted_left_computes actual converted.left converted.right)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) computed

end Mettapedia.Languages.MM0.Presentation.ComputationalProof
