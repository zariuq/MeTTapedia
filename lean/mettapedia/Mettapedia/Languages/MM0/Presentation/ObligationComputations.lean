import Mettapedia.Languages.MM0.Presentation.AdmissionCorrespondence

/-!
# Local MM0 rule computations in the complete authored program

These queries read an actual hypothesis position or theorem table and compute
the admissible theorem instance or the endpoints of a submitted conversion.
Each query has an independent exactness law. No query checks a whole proof.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalObligations

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open ComputationalProof ComputationalConversion ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem hypothesis_query_computes (hypotheses : List Preterm) (index : Nat) :
    Applies admissionProgram dataEqualityHost "mm0:data-at" [encodeExpressions hypotheses, natural index]
      (encodeResult hypotheses[index]?) :=
  proof_suffix_imported _ (by decide) _ _ (hypothesis_lookup_computes hypotheses index)

theorem hypothesis_query_exact (hypotheses : List Preterm) (index : Nat) (claim : Preterm) :
    Applies admissionProgram dataEqualityHost "mm0:data-at" [encodeExpressions hypotheses, natural index]
      (encodeResult (some claim)) ↔ hypotheses[index]? = some claim := by
  constructor
  · intro accepted
    exact (encodeResult_injective (accepted.deterministic (hypothesis_query_computes hypotheses index))).symm
  · intro lookup
    simpa only [lookup] using hypothesis_query_computes hypotheses index

theorem encodeTheoremLookup_injective :
    Function.Injective (fun entry : Option TheoremDecl => encodeLookupResult (entry.map encodeTheorem)) := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [encodeLookupResult]
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have encoded : encodeTheorem first = encodeTheorem second := by
            simpa only [Option.map_some, encodeLookupResult, Term.expr.injEq, List.cons.injEq,
              true_and, and_true] using same
          exact congrArg some (ComputationalAdmission.encodeTheorem_injective encoded)

theorem theorem_query_computes (theory : Theory) (index : Nat) :
    Applies admissionProgram dataEqualityHost "nik:nat-table-get" [encodeTheorems theory.theorems, natural index]
      (encodeLookupResult ((theory.theoremSignature index).map encodeTheorem)) :=
  proof_suffix_imported _ (by decide) _ _ (theorem_lookup_computes theory.theorems index)

theorem theorem_query_exact (theory : Theory) (index : Nat) (declaration : TheoremDecl) :
    Applies admissionProgram dataEqualityHost "nik:nat-table-get" [encodeTheorems theory.theorems, natural index]
      (encodeLookupResult (some (encodeTheorem declaration))) ↔
      theory.theoremSignature index = some declaration := by
  constructor
  · intro accepted
    have same : (some declaration : Option TheoremDecl) = theory.theoremSignature index :=
      @encodeTheoremLookup_injective (some declaration) (theory.theoremSignature index)
        (by simpa only [Option.map_some] using accepted.deterministic (theorem_query_computes theory index))
    exact same.symm
  · intro lookup
    simpa only [lookup, Option.map_some] using theorem_query_computes theory index

theorem instance_query_computes (theory : Theory) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) :
    Applies admissionProgram dataEqualityHost "mm0:instantiate-theorem"
      [encodeTable theory.terms, encodeContext context, encodeTheorem declaration, encodeExpressions arguments]
      (encodeInstance (declaration.instantiate? theory.termSignature context arguments)) := by
  rw [← theory_signature theory]
  exact proof_suffix_imported _ (by decide) _ _
    (theorem_instantiation_computes theory.terms context declaration arguments)

theorem instance_query_exact (theory : Theory) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (instantiation : TheoremInstance) :
    Applies admissionProgram dataEqualityHost "mm0:instantiate-theorem"
      [encodeTable theory.terms, encodeContext context, encodeTheorem declaration, encodeExpressions arguments]
      (encodeInstance (some instantiation)) ↔
      TheoremDecl.Instantiates theory.termSignature context declaration arguments instantiation := by
  constructor
  · intro accepted
    apply (TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp
    exact (encodeInstance_injective (accepted.deterministic
      (instance_query_computes theory context declaration arguments))).symm
  · intro instantiated
    simpa only [instantiated.eval] using instance_query_computes theory context declaration arguments

theorem conversion_query_computes (theory : Theory) (context : Context) (witness : ConvWitness) :
    Applies admissionProgram dataEqualityHost "mm0:conversion"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext context,
        ComputationalConversion.encodeWitness witness]
      (encodeConversion (witness.conversion? theory.termSignature theory.definitionSignature context)) := by
  rw [← theory_signature theory, ← theory_definitions theory]
  exact proof_suffix_imported _ (by decide) _ _
    (ComputationalProof.conversion_reused _ (by decide +kernel) _ _
      (conversion_computes theory.terms theory.definitions context witness))

theorem conversion_query_exact (theory : Theory) (context : Context) (witness : ConvWitness)
    (left right : Preterm) (sort : Nat) :
    Applies admissionProgram dataEqualityHost "mm0:conversion"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext context,
        ComputationalConversion.encodeWitness witness] (encodeConversion (some ⟨left, right, sort⟩)) ↔
      ConvWitness.Checks theory.termSignature theory.definitionSignature context witness left right sort := by
  constructor
  · intro accepted
    apply ConvWitness.conversion_sound (result := ⟨left, right, sort⟩)
    exact (encodeConversion_injective (accepted.deterministic
      (conversion_query_computes theory context witness))).symm
  · intro checked
    simpa only [checked.eval] using conversion_query_computes theory context witness

end Mettapedia.Languages.MM0.Presentation.ComputationalObligations
