import Mettapedia.Languages.MM0.Presentation.ProofCorrespondence
import Mettapedia.Languages.MM0.Kernel.TheoryInvariant
import Mettapedia.Languages.MM0.Kernel.ProofExtension

/-!
# Authored proof checking in the actual MM0 theory

The program reads the current term, definition and theorem tables. A checked
admission run supplies statement validity. This composition does not claim
that the admission algorithm has already been lowered to authored equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalProof

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "H" => dataEqualityHost

theorem theory_theorems (theory : Theory) : theoremsOf theory.theorems = theory.theoremSignature := rfl

theorem theory_proof_computes (theory : Theory) (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) :
    Applies P H "mm0:proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof witness]
      (encodeResult (ProofWitness.proof? theory.termSignature theory.definitionSignature
        theory.theoremSignature context hypotheses witness)) := by
  simpa only [theory_signature, theory_definitions, theory_theorems] using
    proof_computes theory.terms theory.definitions theory.theorems context hypotheses witness

theorem theory_proof_accepts_iff (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (result : Preterm) :
    Applies P H "mm0:proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof witness] (encodeResult (some result)) ↔
      ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness result := by
  simpa only [theory_signature, theory_definitions, theory_theorems] using
    proof_accepts_iff theory.terms theory.definitions theory.theorems context hypotheses witness result

theorem theory_derives_iff_authored (theory : Theory) (context : Context) (hypotheses : List Preterm) (result : Preterm) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses result ↔
      ∃ witness, Applies P H "mm0:proof"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
          encodeContext context, encodeExpressions hypotheses, encodeProof witness] (encodeResult (some result)) := by
  simpa only [theory_signature, theory_definitions, theory_theorems] using
    derives_iff_authored theory.terms theory.definitions theory.theorems context hypotheses result

theorem theory_check_accepts_iff (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof witness, encode claim] (.sym "True") ↔
      ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness claim := by
  simpa only [theory_signature, theory_definitions, theory_theorems] using
    check_accepts_iff theory.terms theory.definitions theory.theorems context hypotheses witness claim

theorem admitted_run_checked_proof_is_statement {theory : Theory} {admissions : List Admission}
    (admitted : Theory.run? {} admissions = some theory)
    {context : Context} {hypotheses : List Preterm} {witness : ProofWitness} {claim : Preterm}
    (localStatements : ∀ hypothesis ∈ hypotheses,
      Preterm.IsStatement theory.sortSignature theory.termSignature context hypothesis)
    (checked : Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof witness, encode claim] (.sym "True")) :
    Preterm.IsStatement theory.sortSignature theory.termSignature context claim :=
  (Theory.run_from_empty_wellFormed admitted).derives_statement localStatements
    ((theory_check_accepts_iff _ _ _ _ _).mp checked).derives

theorem admitted_extension_preserves_proof {before after : Theory} {admissions : List Admission}
    (admitted : Theory.run? before admissions = some after)
    {context : Context} {hypotheses : List Preterm} {witness : ProofWitness} {claim : Preterm}
    (checked : Applies P H "mm0:check-proof"
      [encodeTable before.terms, encodeDefinitions before.definitions, encodeTheorems before.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof witness, encode claim] (.sym "True")) :
    Applies P H "mm0:check-proof"
      [encodeTable after.terms, encodeDefinitions after.definitions, encodeTheorems after.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof witness, encode claim] (.sym "True") := by
  have extension := ((Theory.run_eq_some_iff _ _ _).mp admitted).extends
  apply (theory_check_accepts_iff _ _ _ _ _).mpr
  exact ((theory_check_accepts_iff _ _ _ _ _).mp checked).extendSignatures
    extension.terms extension.definitions extension.theorems

end Mettapedia.Languages.MM0.Presentation.ComputationalProof
