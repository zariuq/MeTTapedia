import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaExecutionCorrespondence
import Mettapedia.Languages.MM0.Presentation.ServiceProgram
import Mettapedia.Languages.MM0.Kernel.ProofSharing
import Mettapedia.Languages.MM0.Presentation.SpecificationCorrespondence

/-!
# Execution of the MM0 service in independent MeTTa semantics

The generic compiler theorem is instantiated with the existing joined program.
The same submitted witness, context, theory and expected specification reach the
checker. Stable observations preserve and reflect source results at sufficient
independent target budget. The loader and named primitive obligations remain
explicit; physical CeTTa agreement and premature target-budget results are
separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.Service

open Kernel Calculus ComputationalCalculus ComputationalSpecification
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Execution
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
open Metta.Minimal

/-- Load the generated MM0 equations alongside an explicitly disjoint library.
Name separation follows from the shared UTF-8 encoding theorem. -/
def environment (library : List Metta.Atom) : MinEnv :=
  MinEnv.ofAtomsGT
    (((programAtoms program).flatMap fun pair =>
      [Mettapedia.Languages.MeTTa.HE.LeaTTaBridge.toLeaTTaAtom pair.1,
       Mettapedia.Languages.MeTTa.HE.LeaTTaBridge.toLeaTTaAtom pair.2]) ++ library)
    Metta.Builtins.table

theorem program_loaded (library : List Metta.Atom)
    (noHeadless : (extractRules library).filter (fun rule => (headKey rule.1).isNone) = [])
    (disjoint : ∀ head ∈ program.map Equation.head,
      (extractRules library).filter (fun rule => headKey rule.1 == some (dispatchName head)) = []) :
    LoadedProgram program (environment library) :=
  programAtoms_loaded program library noHeadless disjoint

/-- The emitted request's actual stable public observation. -/
def Returns (environment : MinEnv) (sourceFuel : Nat) (head : String)
    (arguments : List Term) (result : Term) : Prop :=
  StableReturns environment
    (returnInvocation (requestAtom program sourceFuel head arguments)) (.value result)

theorem returns_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (sourceFuel : Nat) (head : String) (arguments : List Term) (result : Term) :
    Returns environment sourceFuel head arguments result ↔
      apply program dataEqualityHost sourceFuel head arguments = .value result :=
  invocation_stable_iff program dataEqualityHost environment loaded primitives
    dataEqualityHost_unlisted sourceFuel head arguments (.value result)

theorem some_fuel_returns_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (head : String) (arguments : List Term) (result : Term) :
    (∃ sourceFuel, Returns environment sourceFuel head arguments result) ↔
      Applies program dataEqualityHost head arguments result := by
  simp only [returns_iff environment loaded primitives, Applies]

private theorem certificate_called : "mm0:certificate" ∈ calculusProgram.calledHeads := by
  decide +kernel

private theorem verification_called : "mm0:spec-verify" ∈ specificationProgram.calledHeads := by
  decide +kernel

/-- Acceptance preserves and reflects the supplied MM0 witness, rather than
existence of some proof or success of proof search. -/
theorem supplied_witness_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (claim : Preterm) :
    ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness claim ↔
      ∃ sourceFuel, Returns environment sourceFuel "mm0:certificate"
        (ComputationalCalculus.request theory (derivesJ context hypotheses claim)
          (Witness.translate theory 0 context hypotheses witness)) (.sym "True") := by
  rw [some_fuel_returns_iff environment loaded primitives,
    calculus_returns _ certificate_called]
  exact witness_accepted_iff theory 0 context hypotheses witness claim

/-- Logical rejection has its own completed Boolean observation. It is
separate from source and target resource exhaustion. -/
theorem supplied_witness_refused_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (claim : Preterm) :
    ¬ ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness claim ↔
      ∃ sourceFuel, Returns environment sourceFuel "mm0:certificate"
        (ComputationalCalculus.request theory (derivesJ context hypotheses claim)
          (Witness.translate theory 0 context hypotheses witness)) (.sym "False") := by
  rw [some_fuel_returns_iff environment loaded primitives,
    calculus_returns _ certificate_called]
  exact witness_refused_iff theory 0 context hypotheses witness claim

/-- Fixed-specification sequential admission returns exactly its resulting
theory. The proof file cannot supply its own axiom basis. -/
theorem verification_result_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (result : Term) :
    (∃ sourceFuel, Returns environment sourceFuel "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] result) ↔
      result = ComputationalAdmission.encodeTheoryResult
        (SpecificationAdmission.verify? specification declarations) := by
  rw [some_fuel_returns_iff environment loaded primitives]
  change (∃ sourceFuel, apply program dataEqualityHost sourceFuel _ _ = .value result) ↔ _
  simp only [specification_outcomes _ _ verification_called]
  exact verify_result_exact specification declarations result

theorem verification_accepted_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (theory : Theory) :
    (∃ sourceFuel, Returns environment sourceFuel "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations]
      (ComputationalAdmission.encodeTheoryResult (some theory))) ↔
      SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨theory, []⟩ := by
  rw [verification_result_iff environment loaded primitives,
    ComputationalAdmission.encodeTheoryResult_injective.eq_iff, eq_comm,
    SpecificationAdmission.verify_eq_some_iff]

theorem verification_refused_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration) :
    (∃ sourceFuel, Returns environment sourceFuel "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] (.sym "None")) ↔
      ¬ ∃ theory, SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨theory, []⟩ := by
  change (∃ sourceFuel, Returns environment sourceFuel _ _
    (ComputationalAdmission.encodeTheoryResult none)) ↔ _
  rw [verification_result_iff environment loaded primitives,
    ComputationalAdmission.encodeTheoryResult_injective.eq_iff]
  simp only [eq_comm, ← SpecificationAdmission.verify_eq_some_iff]
  cases SpecificationAdmission.verify? specification declarations <;> simp

/-- Admitted axioms agree with the external specification in order and payload. -/
theorem verification_axioms_exact (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    {specification : List SpecificationEntry} {declarations : List ProofDeclaration} {theory : Theory}
    (accepted : ∃ sourceFuel, Returns environment sourceFuel "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations]
      (ComputationalAdmission.encodeTheoryResult (some theory))) :
    SpecificationAdmission.declarationAxioms declarations =
      SpecificationAdmission.specificationAxioms specification :=
  SpecificationAdmission.verified_axioms_exact
    ((SpecificationAdmission.verify_eq_some_iff _ _ _).mpr
      ((verification_accepted_iff environment loaded primitives _ _ _).mp accepted))

/-- A supplied hypothesis witness succeeds through the emitted service. -/
theorem hypothesis_execution (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (theory : Theory) (context : Context) (claim : Preterm) :
    ∃ sourceFuel, Returns environment sourceFuel "mm0:certificate"
      (ComputationalCalculus.request theory (derivesJ context [claim] claim)
        (Witness.translate theory 0 context [claim] (.hyp 0))) (.sym "True") :=
  (supplied_witness_iff environment loaded primitives theory context [claim] (.hyp 0) claim).mp
    (.hyp rfl)

/-- No proof witness can create the first theorem in an empty theory. This
negative control reflects through the same generated execution, for every
supplied witness and every context. -/
theorem empty_theory_refuses (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (context : Context) (witness : ProofWitness) (claim : Preterm) :
    ∃ sourceFuel, Returns environment sourceFuel "mm0:certificate"
      (ComputationalCalculus.request {} (derivesJ context [] claim)
        (Witness.translate {} 0 context [] witness)) (.sym "False") := by
  apply (supplied_witness_refused_iff environment loaded primitives {} context [] witness claim).mp
  intro checked
  exact no_derivation_without_hypotheses_or_theorems
    (Theory.termSignature {}) (Theory.definitionSignature {}) context claim checked.derives

/-- An exhausted source call cannot be mistaken for completed rejection. -/
theorem exhausted_not_refused (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (sourceFuel : Nat) (head : String) (arguments : List Term)
    (exhausted : apply program dataEqualityHost sourceFuel head arguments = .exhausted) :
    ¬ Returns environment sourceFuel head arguments (.sym "False") := by
  rw [returns_iff environment loaded primitives, exhausted]
  simp

end Mettapedia.Languages.MM0.Presentation.Service
