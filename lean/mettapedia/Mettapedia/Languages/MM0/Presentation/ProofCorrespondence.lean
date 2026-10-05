import Mettapedia.Languages.MM0.Presentation.ProofExecution

/-!
# Complete supplied-proof correspondence for authored MM0 equations

The same finite witness is checked on both sides. Existence of an accepted
witness agrees with independent derivability; refusal of one submitted
witness says nothing about other proofs. Every canonical finite input
eventually has a stable completed result, including invalid evidence.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalProof

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalConversion
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "A" => proofEquations
local notation "H" => dataEqualityHost

mutual

theorem proof_computes (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) :
    Applies P H "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness]
      (encodeResult (ProofWitness.proof? (signatureOf table) (definitionsOf definitions)
        (theoremsOf theorems) context hypotheses witness)) := by
  cases witness with
  | hyp index =>
      rw [encodeProof, ProofWitness.proof?]
      refine proof_equation (equation := A[15]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (hypothesis_lookup_computes hypotheses index)
  | theoremApp index arguments children =>
      rw [encodeProof, ProofWitness.proof?]
      refine proof_equation (equation := A[16]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))))
        (proof_declaration_computes table definitions theorems context hypotheses arguments children
          (theoremsOf theorems index)
          (ProofWitness.children? (signatureOf table) (definitionsOf definitions) (theoremsOf theorems) context hypotheses children)
          (proof_children_computes table definitions theorems context hypotheses children))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (theorem_lookup_computes theorems index)
  | conversion witness child =>
      rw [encodeProof, ProofWitness.proof?]
      refine proof_equation (equation := A[17]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))
        (proof_converted_computes table definitions theorems context hypotheses child
          (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context witness)
          (ProofWitness.proof? (signatureOf table) (definitionsOf definitions) (theoremsOf theorems) context hypotheses child)
          (proof_computes table definitions theorems context hypotheses child))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (conversion_reused _ (by
          simp only [conversionProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
          exact Or.inr (by decide)) _ _ (conversion_computes table definitions context witness))
termination_by sizeOf witness

theorem proof_children_computes (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (children : List ProofWitness) :
    Applies P H "mm0:proof-children"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProofs children]
      (encodeResults (ProofWitness.children? (signatureOf table) (definitionsOf definitions)
        (theoremsOf theorems) context hypotheses children)) := by
  cases children with
  | nil =>
      rw [ProofWitness.children?]
      exact ⟨3, by rw [proof_apply _ (by decide)]; rfl⟩
  | cons child children =>
      rw [ProofWitness.children?]
      refine proof_equation (equation := A[32]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [listView ((child :: children).map encodeProof), encodeTable table, encodeDefinitions definitions,
          encodeTheorems theorems, encodeContext context, encodeExpressions hypotheses])
        (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) (by rfl))
      · refine proof_equation (equation := A[34]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))
          (proof_child_computes table definitions theorems context hypotheses children
            (ProofWitness.proof? (signatureOf table) (definitionsOf definitions) (theoremsOf theorems) context hypotheses child)
            (ProofWitness.children? (signatureOf table) (definitionsOf definitions) (theoremsOf theorems) context hypotheses children)
            (proof_children_computes table definitions theorems context hypotheses children))
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))
          (proof_computes table definitions theorems context hypotheses child)
termination_by sizeOf children

end

theorem proof_result_exact (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (result : Term) :
    Applies P H "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness] result ↔
      result = encodeResult (ProofWitness.proof? (signatureOf table) (definitionsOf definitions)
        (theoremsOf theorems) context hypotheses witness) := by
  constructor
  · exact fun computed => computed.deterministic (proof_computes table definitions theorems context hypotheses witness)
  · rintro rfl; exact proof_computes table definitions theorems context hypotheses witness

theorem proof_accepts_iff (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (result : Preterm) :
    Applies P H "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness] (encodeResult (some result)) ↔
      ProofWitness.Checks (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
        context hypotheses witness result := by
  rw [proof_result_exact, ← ProofWitness.proof_eq_some_iff]
  constructor
  · exact fun same => (encodeResult_injective same).symm
  · exact fun same => congrArg encodeResult same.symm

theorem proof_refuses_iff (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) :
    Applies P H "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness] (.sym "None") ↔
      ¬ ∃ result, ProofWitness.Checks (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
        context hypotheses witness result := by
  rw [proof_result_exact, ← ProofWitness.proof_none_iff]
  constructor
  · exact fun same => (encodeResult_injective (show encodeResult none = _ from same)).symm
  · exact fun same => congrArg encodeResult same.symm

theorem derives_iff_authored (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (result : Preterm) :
    Derives (signatureOf table) (definitionsOf definitions) (theoremsOf theorems) context hypotheses result ↔
      ∃ witness, Applies P H "mm0:proof"
        [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
          encodeExpressions hypotheses, encodeProof witness] (encodeResult (some result)) := by
  constructor
  · intro derived
    obtain ⟨witness, checked⟩ := derived.certificate_exists
    exact ⟨witness, (proof_accepts_iff _ _ _ _ _ _ _).mpr checked⟩
  · rintro ⟨witness, accepted⟩
    exact ((proof_accepts_iff _ _ _ _ _ _ _).mp accepted).derives

theorem children_result_exact (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (children : List ProofWitness) (result : Term) :
    Applies P H "mm0:proof-children"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProofs children] result ↔
      result = encodeResults (ProofWitness.children? (signatureOf table) (definitionsOf definitions)
        (theoremsOf theorems) context hypotheses children) := by
  constructor
  · exact fun computed => computed.deterministic (proof_children_computes table definitions theorems context hypotheses children)
  · rintro rfl; exact proof_children_computes table definitions theorems context hypotheses children

theorem children_accepts_iff (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (children : List ProofWitness) (results : List Preterm) :
    Applies P H "mm0:proof-children"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProofs children] (encodeResults (some results)) ↔
      ProofWitness.ChecksList (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
        context hypotheses children results := by
  rw [children_result_exact, ← ProofWitness.children_eq_some_iff]
  constructor
  · exact fun same => (encodeResults_injective same).symm
  · exact fun same => congrArg encodeResults same.symm

theorem check_computes (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness, encode claim]
      (boolean (ProofWitness.check (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
        context hypotheses witness claim)) := by
  refine proof_equation (equation := A[39]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call
    (values := [encodeResult (ProofWitness.proof? (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
      context hypotheses witness), encodeResult (some claim)]) (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))
      (proof_computes table definitions theorems context hypotheses witness)
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.constructor (by rfl) (by rfl))
  · simpa only [encodeResult_injective.eq_iff, ProofWitness.check] using
      data_equality_computes P
        (encodeResult (ProofWitness.proof? (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
          context hypotheses witness)) (encodeResult (some claim)) (by rfl)

theorem check_result_exact (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (result : Term) :
    Applies P H "mm0:check-proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness, encode claim] result ↔
      result = boolean (ProofWitness.check (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
        context hypotheses witness claim) := by
  constructor
  · exact fun computed => computed.deterministic (check_computes table definitions theorems context hypotheses witness claim)
  · rintro rfl; exact check_computes table definitions theorems context hypotheses witness claim

theorem check_accepts_iff (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness, encode claim] (.sym "True") ↔
      ProofWitness.Checks (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
        context hypotheses witness claim := by
  rw [check_result_exact, ← ProofWitness.check_iff]
  cases ProofWitness.check (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
    context hypotheses witness claim <;> simp [boolean]

theorem check_refuses_iff (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness, encode claim] (.sym "False") ↔
      ¬ ProofWitness.Checks (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
        context hypotheses witness claim := by
  rw [check_result_exact, ← ProofWitness.check_iff]
  cases ProofWitness.check (signatureOf table) (definitionsOf definitions) (theoremsOf theorems)
    context hypotheses witness claim <;> simp [boolean]

theorem proof_completed_result (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (fuel : Nat)
    (finished : apply P H fuel "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness] ≠ .exhausted) :
    apply P H fuel "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness] =
      .value (encodeResult (ProofWitness.proof? (signatureOf table) (definitionsOf definitions)
        (theoremsOf theorems) context hypotheses witness)) :=
  (proof_computes table definitions theorems context hypotheses witness).completed fuel finished

theorem proof_eventually_stable (table : SignatureTable) (definitions : DefinitionTable) (theorems : TheoremTable)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) :
    ∃ needed, ∀ fuel, needed ≤ fuel → apply P H fuel "mm0:proof"
      [encodeTable table, encodeDefinitions definitions, encodeTheorems theorems, encodeContext context,
        encodeExpressions hypotheses, encodeProof witness] =
      .value (encodeResult (ProofWitness.proof? (signatureOf table) (definitionsOf definitions)
        (theoremsOf theorems) context hypotheses witness)) :=
  (proof_computes table definitions theorems context hypotheses witness).at_least

end Mettapedia.Languages.MM0.Presentation.ComputationalProof
