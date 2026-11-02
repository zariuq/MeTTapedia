import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofProgram

/-! Execution agrees with the independent supplied-witness checker at every
finite witness. Refusal propagates from the actual selected child. These laws
concern the authored evaluator; physical runtime realization is qualified
separately. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2

open ComputationalData ComputationalShift ComputationalInference ComputationalProofs ComputationalSimultaneous
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => wholeProgram
local notation "A" => proofEquationsV2
local notation "H" => productDivisionHost

private theorem mp_computes (implication premise : Spec.Term) :
    Applies P H "vibe:modus-ponens" [encode implication, encode premise]
      (encodeResult (modusPonensResult implication premise)) :=
  reuse_simultaneous_call (by decide +kernel)
    (ComputationalSimultaneous.reuse_inference_call (by decide +kernel) (modusPonens_computes _ _))

private theorem mp_second (implication : Spec.Term) (premise : Option Spec.Term) :
    Applies P H "vibe:proof-v2-mp-second" [encode implication, encodeResult premise]
      (encodeResult (premise.bind (modusPonensResult implication))) := by
  cases premise with
  | none => exact ⟨1, by rw [whole_apply _ (by decide +kernel)]; rfl⟩
  | some premise =>
      refine whole_equation (equation := A[5])
        (environment := [("implication", encode implication), ("premise", encode premise)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (mp_computes implication premise)

private theorem mp_first (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (implication : Option Spec.Term) (premise : SimultaneousProofs.Witness)
    (child : Applies P H "vibe:proof-v2-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness premise]
      (encodeResult (premise.result (theoryOf table axioms definitions)))) :
    Applies P H "vibe:proof-v2-mp-first"
      [encodeResult implication, encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness premise]
      (encodeResult (implication.bind fun left =>
        (premise.result (theoryOf table axioms definitions)).bind (modusPonensResult left))) := by
  cases implication with
  | none => exact ⟨1, by rw [whole_apply _ (by decide +kernel)]; rfl⟩
  | some implication =>
      refine whole_equation (equation := A[3])
        (environment := [("implication", encode implication), ("table", encodeTable table),
          ("axioms", encodeAxioms axioms), ("definitions", encodeDefinitions definitions),
          ("premise", encodeWitness premise)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) (mp_second _ _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) child

private theorem many_child (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (source : Option Spec.Term) :
    Applies P H "vibe:proof-v2-many-child" [encodeResult source, encodeTable table, encodeReplacements replacements]
      (encodeResult (source.bind fun statement =>
        if replacements.all (fun pair => Spec.WellFormed (signatureOf table) pair.2) then
          Spec.SimultaneousInstantiation.statement (signatureOf table) replacements statement else none)) := by
  cases source with
  | none => exact ⟨1, by rw [whole_apply _ (by decide +kernel)]; rfl⟩
  | some source =>
      refine whole_equation (equation := A[8])
        (environment := [("statement", encode source), ("table", encodeTable table),
          ("replacements", encodeReplacements replacements)]) (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
        (reuse_simultaneous_call (by decide +kernel) (theorem_computes table replacements source))

theorem proofQuery_computes (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) :
    Applies P H "vibe:proof-v2-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness]
      (encodeResult (witness.result (theoryOf table axioms definitions))) := by
  induction witness with
  | base original =>
      refine whole_equation (equation := A[0])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("original", ComputationalProofs.encodeWitness original)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (reuse_proof_call (by decide +kernel) (ComputationalProofs.proofQuery_computes _ _ _ original))
  | modusPonens implication premise left right =>
      refine whole_equation (equation := A[1])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("implication", encodeWitness implication),
          ("premise", encodeWitness premise)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) (mp_first _ _ _ _ premise right)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) left
  | instantiateMany replacements child ih =>
      refine whole_equation (equation := A[6])
        (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
          ("definitions", encodeDefinitions definitions), ("replacements", encodeReplacements replacements),
          ("child", encodeWitness child)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (many_child table replacements _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ih

private theorem check_result (actual : Option Spec.Term) (claimed : Spec.Term) :
    Applies P H "vibe:proof-v2-check-result" [encodeResult actual, encode claimed]
      (boolean (decide (actual = some claimed))) := by
  cases actual with
  | none => exact ⟨1, by rw [whole_apply _ (by decide +kernel)]; rfl⟩
  | some actual =>
      simp only [Option.some.injEq]
      refine whole_equation (equation := A[12])
        (environment := [("actual", encode actual), ("claimed", encode claimed)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (reuse_simultaneous_call (by decide +kernel)
          (ComputationalSimultaneous.reuse_inference_call (by decide +kernel) (term_equality_computes _ _)))

theorem checkProof_computes (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof-v2"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (boolean (SimultaneousProofs.Witness.check (theoryOf table axioms definitions) witness claimed)) := by
  refine whole_equation (equation := A[10])
    (environment := [("table", encodeTable table), ("axioms", encodeAxioms axioms),
      ("definitions", encodeDefinitions definitions), ("witness", encodeWitness witness), ("claimed", encode claimed)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (check_result _ _)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) (proofQuery_computes _ _ _ _)

theorem proofQuery_accepts_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) (claimed : Spec.Term) :
    Applies P H "vibe:proof-v2-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness]
      (encodeResult (some claimed)) ↔ SimultaneousProofs.Witness.Checks (theoryOf table axioms definitions) witness claimed := by
  constructor
  · intro computed
    exact SimultaneousProofs.Witness.result_sound
      (encodeResult_injective (computed.deterministic (proofQuery_computes table axioms definitions witness))).symm
  · intro checked
    simpa only [checked.eval] using proofQuery_computes table axioms definitions witness

theorem proofQuery_refuses_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) :
    Applies P H "vibe:proof-v2-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness] (.sym "None") ↔
      ¬ ∃ claimed, SimultaneousProofs.Witness.Checks (theoryOf table axioms definitions) witness claimed := by
  rw [← SimultaneousProofs.Witness.result_none_iff]
  constructor
  · intro computed
    have same : encodeResult none = encodeResult (witness.result (theoryOf table axioms definitions)) :=
      computed.deterministic (proofQuery_computes table axioms definitions witness)
    exact (encodeResult_injective same).symm
  · intro refused
    simpa only [refused, encodeResult] using proofQuery_computes table axioms definitions witness

theorem checkProof_accepts_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof-v2"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (.sym "True") ↔ SimultaneousProofs.Witness.Checks (theoryOf table axioms definitions) witness claimed := by
  have exactResult := checkProof_computes table axioms definitions witness claimed
  constructor
  · intro computed
    have same := computed.deterministic exactResult
    apply (SimultaneousProofs.Witness.check_iff _ _ _).mp
    cases checked : SimultaneousProofs.Witness.check (theoryOf table axioms definitions) witness claimed with
    | false =>
        have impossible : ("True" : String) = "False" := Term.sym.inj
          (by simpa only [checked, boolean, Bool.false_eq_true, if_false] using same)
        exact False.elim ((by decide : ("True" : String) ≠ "False") impossible)
    | true => rfl
  · intro checked
    simpa [(SimultaneousProofs.Witness.check_iff _ _ _).mpr checked, boolean] using exactResult

theorem checkProof_result_exact (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) (claimed : Spec.Term) (result : Term) :
    Applies P H "vibe:check-proof-v2"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      result ↔ result = boolean (SimultaneousProofs.Witness.check (theoryOf table axioms definitions) witness claimed) := by
  constructor
  · intro computed
    exact computed.deterministic (checkProof_computes table axioms definitions witness claimed)
  · rintro rfl
    exact checkProof_computes table axioms definitions witness claimed

theorem checkProof_refuses_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof-v2"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (.sym "False") ↔ ¬ SimultaneousProofs.Witness.Checks (theoryOf table axioms definitions) witness claimed := by
  rw [checkProof_result_exact, ← SimultaneousProofs.Witness.check_iff]
  cases SimultaneousProofs.Witness.check (theoryOf table axioms definitions) witness claimed <;> simp [boolean]

theorem proofQuery_completed_exact (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) (fuel : Nat)
    (finished : apply P H fuel "vibe:proof-v2-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness] ≠ .exhausted) :
    apply P H fuel "vibe:proof-v2-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness] =
      .value (encodeResult (witness.result (theoryOf table axioms definitions))) :=
  (proofQuery_computes table axioms definitions witness).completed fuel finished

theorem checkProof_completed_exact (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : SimultaneousProofs.Witness) (claimed : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:check-proof-v2"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed] ≠ .exhausted) :
    apply P H fuel "vibe:check-proof-v2"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed] =
      .value (boolean (SimultaneousProofs.Witness.check (theoryOf table axioms definitions) witness claimed)) :=
  (checkProof_computes table axioms definitions witness claimed).completed fuel finished

#print axioms proofQuery_computes
#print axioms checkProof_computes

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2
