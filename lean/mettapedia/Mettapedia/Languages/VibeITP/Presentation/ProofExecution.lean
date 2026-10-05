import Mettapedia.Languages.VibeITP.Presentation.ProofAccess

/-!
# Finite execution of complete supplied Vibe proofs

Each recursive call is the actual supplied child. Ordered index access and
previously verified operations supply the leaves. Completed missing children
propagate refusal; no search or alternative derivation replaces them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs

open ComputationalData ComputationalShift ComputationalInference ComputationalLiterals ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "A" => proofEquations
local notation "H" => productDivisionHost

private theorem inference_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ inferenceProgram.calledHeads)
    (computed : Applies inferenceProgram computationalHost head arguments result) :
    Applies P H head arguments result := by
  have literalUsed : head ∈ literalProgram.calledHeads := by
    simp only [literalProgram, Program.calledHeads, List.flatMap_append]
    exact List.mem_append_left _ used
  have definitionUsed : head ∈ definitionProgram.calledHeads := by
    simp only [definitionProgram, Program.calledHeads, List.flatMap_append]
    exact List.mem_append_left _ literalUsed
  exact reuse_definition_call definitionUsed
    (reuse_literal_call literalUsed (reuse_inference_call used computed))

private theorem proof_mp (implication premise : Spec.Term) :
    Applies P H "vibe:modus-ponens" [encode implication, encode premise]
      (encodeResult (modusPonensResult implication premise)) :=
  inference_call (by decide +kernel) (modusPonens_computes implication premise)

private theorem proof_inst (table : SignatureTable) (symbol : Spec.SymId) (value statement : Spec.Term) :
    Applies P H "vibe:thm-instantiate" [encodeTable table, encodeSymbol symbol, encode value, encode statement]
      (encodeResult (if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none)) :=
  inference_call (by decide +kernel) (theoremInstantiation_computes table symbol value statement)

private theorem proof_literal (request : LiteralRequest) :
    Applies P H "vibe:literal-query" [encodeRequest request] (encodeResult request.result) :=
  reuse_definition_call (by decide +kernel)
    (reuse_literal_call (by decide +kernel) (literalQuery_computes request))

private theorem definition_selected (table : SignatureTable) (declaration : Option Spec.Definition) (hints : List Nat) :
    Applies P H "vibe:proof-definition"
      [encodeAccessResult (declaration.map encodeDefinition), encodeTable table, encodeBinders hints]
      (encodeResult (declaration.bind fun d => (definitionRequest d hints).result (signatureOf table))) := by
  cases declaration with
  | none => exact ⟨1, by rw [proof_apply _ (by decide +kernel)]; rfl⟩
  | some d =>
      refine proof_equation (equation := A[8])
        (environment := [("constant", encodeSymbol d.symbol), ("parameters", encodeSymbols d.fvars),
          ("body", encode d.value), ("table", encodeTable table), ("hints", encodeBinders hints)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
        (reuse_definition_call (by decide +kernel) (definitionQuery_computes table (definitionRequest d hints)))

private theorem mp_second (implication : Spec.Term) (premise : Option Spec.Term) :
    Applies P H "vibe:proof-mp-second" [encode implication, encodeResult premise]
      (encodeResult (premise.bind (modusPonensResult implication))) := by
  cases premise with
  | none => exact ⟨1, by rw [proof_apply _ (by decide +kernel)]; rfl⟩
  | some premise =>
      refine proof_equation (equation := A[13])
        (environment := [("implication", encode implication), ("premise", encode premise)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (proof_mp implication premise)

private theorem mp_first (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (implication : Option Spec.Term) (premise : ProofWitness)
    (child : Applies P H "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness premise]
      (encodeResult (premise.result (theoryOf table axioms definitions)))) :
    Applies P H "vibe:proof-mp-first"
      [encodeResult implication, encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness premise]
      (encodeResult (implication.bind fun left =>
        (premise.result (theoryOf table axioms definitions)).bind (modusPonensResult left))) := by
  cases implication with
  | none => exact ⟨1, by rw [proof_apply _ (by decide +kernel)]; rfl⟩
  | some implication =>
      refine proof_equation (equation := A[11])
        (environment := [("implication", encode implication), ("table", encodeTable table),
          ("axioms", encodeAxioms axioms), ("definitions", encodeDefinitions definitions),
          ("premise", encodeWitness premise)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) (mp_second _ _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) child

private theorem instantiation_child (table : SignatureTable) (symbol : Spec.SymId) (value : Spec.Term)
    (statement : Option Spec.Term) :
    Applies P H "vibe:proof-instantiation"
      [encodeResult statement, encodeTable table, encodeSymbol symbol, encode value]
      (encodeResult (statement.bind fun statement => if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none)) := by
  cases statement with
  | none => exact ⟨1, by rw [proof_apply _ (by decide +kernel)]; rfl⟩
  | some statement =>
      refine proof_equation (equation := A[16])
        (environment := [("statement", encode statement), ("table", encodeTable table),
          ("F", encodeSymbol symbol), ("value", encode value)]) (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) (proof_inst _ _ _ _)

theorem proofQuery_computes (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) :
    Applies P H "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness]
      (encodeResult (witness.result (theoryOf table axioms definitions))) := by
  induction witness with
  | «axiom» index =>
      refine proof_equation (equation := A[5])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("index", natural index)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (axiomAt_computes _ _)
  | definition index hints =>
      refine proof_equation (equation := A[6])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("index", natural index), ("hints", encodeBinders hints)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (definition_selected _ _ _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definitionAt_computes _ _)
  | modusPonens implication premise implicationIH premiseIH =>
      refine proof_equation (equation := A[9])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("implication", encodeWitness implication),
          ("premise", encodeWitness premise)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) (mp_first _ _ _ _ _ premiseIH)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) implicationIH
  | instantiate symbol value child childIH =>
      refine proof_equation (equation := A[14])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("F", encodeSymbol symbol),
          ("value", encode value), ("child", encodeWitness child)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))) (instantiation_child _ _ _ _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) childIH
  | literal request =>
      refine proof_equation (equation := A[17])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("request", encodeRequest request)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (proof_literal request)

private theorem check_result (actual : Option Spec.Term) (claimed : Spec.Term) :
    Applies P H "vibe:proof-check-result" [encodeResult actual, encode claimed]
      (boolean (decide (actual = some claimed))) := by
  cases actual with
  | none => exact ⟨1, by rw [proof_apply _ (by decide +kernel)]; rfl⟩
  | some actual =>
      simp only [Option.some.injEq]
      refine proof_equation (equation := A[21])
        (environment := [("actual", encode actual), ("claimed", encode claimed)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (inference_call (by decide +kernel) (term_equality_computes _ _))

theorem checkProof_computes (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (boolean (ProofWitness.check (theoryOf table axioms definitions) witness claimed)) := by
  refine proof_equation (equation := A[19])
    (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
      ("definitions", encodeDefinitions definitions), ("witness", encodeWitness witness), ("claimed", encode claimed)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (check_result _ _)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) (proofQuery_computes _ _ _ _)

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs
