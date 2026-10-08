import Mettapedia.Languages.MM0.MeTTa.Admission.AdmissionChecks
import Mettapedia.Languages.MM0.Upstream.Lean3ProofAdmission

/-!
# Proof certificates in chronological MM0 sessions

The session's native rows are chronological. Their unique-key representation
derives the signatures used by the existing supplied-proof checker and MM0
calculus. This avoids requiring native row order to equal the kernel's
newest-first association lists.

A fixed witness is related to its own translated certificate. Derivability
and the specified source judgment quantify a witness separately. Neither
physical table readiness nor logical derivability authorizes an unmatched
specification declaration or repairs a rejected submitted witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SessionProof

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Theory Context Preterm ProofWitness TheoremDecl Admission)
open SessionInitialization (Spaces)
open TableAccess (tableValue)
open AdmissionChecks (Ready proofTables)

private def environment (spaces : Spaces) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (claim : Preterm) : Subst :=
  [("claim", Data.preterm claim), ("proof", Proof.witnessValue witness),
    ("hypotheses", ListSubstitution.expressionsValue hypotheses), ("context", Data.context context),
    ("theorems", tableValue spaces.theorems), ("definitions", tableValue spaces.definitions),
    ("table", tableValue spaces.terms)]

def requestConfiguration (state : State) (spaces : Spaces) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) : Configuration :=
  { state, control := .evaluate (environment spaces context hypotheses witness claim)
      (.expression [.symbol "mm0:check-proof", .var "table", .var "definitions", .var "theorems",
        .var "context", .var "hypotheses", .var "proof", .var "claim"]) }

private theorem request_is_existing_check (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    requestConfiguration before spaces context hypotheses witness claim =
      Proof.checkRequestConfiguration before (proofTables spaces theory hypotheses ready) context witness claim := rfl

theorem sufficient_fuel (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean (ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
          context hypotheses witness claim)] [] []) ∧
      Ready spaces theory after ∧ InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  obtain ⟨after, bound, fuel, completed, readyAfter, frame⟩ :=
    Proof.check_sufficient_fuel (proofTables spaces theory hypotheses ready) context witness claim before
      (AdmissionChecks.proof_tables_ready spaces theory hypotheses ready)
  have cache : InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after := by
    simpa only [proofTables, ready.term_signature] using readyAfter.cache
  refine ⟨after, bound, fuel, ?_, ready.after_frame frame cache, frame⟩
  intro extra
  rw [request_is_existing_check spaces theory context hypotheses witness claim before ready]
  simpa only [proofTables, ready.term_signature, ready.definition_signature, ready.theorem_signature] using completed extra

theorem completed_frame (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before after : State)
    (ready : Ready spaces theory before) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
      .complete after answers [] []) :
    Ready spaces theory after ∧ ∃ bound, InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  obtain ⟨reference, bound, referenceFuel, completed, readyReference, frame⟩ :=
    sufficient_fuel spaces theory context hypotheses witness claim before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨readyReference, bound, frame⟩

theorem result_iff_source_returns (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) (answer : Bool) :
    ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness claim = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean answer] [] [] := by
  rw [request_is_existing_check spaces theory context hypotheses witness claim before ready]
  have returned := Proof.check_result_iff_source_returns (proofTables spaces theory hypotheses ready)
    context witness claim before (AdmissionChecks.proof_tables_ready spaces theory hypotheses ready) answer
  simpa only [proofTables, ready.term_signature, ready.definition_signature, ready.theorem_signature] using returned

theorem checks_iff_source_accepts (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness claim ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean true] [] [] :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).symm.trans
    (result_iff_source_returns spaces theory context hypotheses witness claim before ready true)

theorem checks_iff_judgment (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses witness claim ↔
      ∃ after, DeclarativeSpec.Runs program (requestConfiguration before spaces context hypotheses witness claim)
        (.complete after [boolean true] [] []) := by
  rw [checks_iff_source_accepts spaces theory context hypotheses witness claim before ready]
  exact exists_congr fun after => completed_run_iff_derivation program _ after _ [] []

/-- The submitted witness is retained in its certificate; no other derivation
can replace it in this equivalence. Native ordering is accounted for by the
signature theorems earned by physical readiness. -/
theorem certificate_accepted_iff_source_accepts (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    (∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
      Presentation.Calculus.formMM0 (Presentation.Calculus.family theory).evaluate
      (Presentation.Calculus.derivesJ context hypotheses claim)
      (Presentation.Calculus.Witness.translate theory fuel context hypotheses witness) = true) ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean true] [] [] :=
  (Presentation.Calculus.Witness.checks_iff_accepted (T := theory) context hypotheses witness claim).symm.trans
    (checks_iff_source_accepts spaces theory context hypotheses witness claim before ready)

theorem certificate_accepted_iff_judgment (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    (∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
      Presentation.Calculus.formMM0 (Presentation.Calculus.family theory).evaluate
      (Presentation.Calculus.derivesJ context hypotheses claim)
      (Presentation.Calculus.Witness.translate theory fuel context hypotheses witness) = true) ↔
      ∃ after, DeclarativeSpec.Runs program (requestConfiguration before spaces context hypotheses witness claim)
        (.complete after [boolean true] [] []) :=
  (Presentation.Calculus.Witness.checks_iff_accepted (T := theory) context hypotheses witness claim).symm.trans
    (checks_iff_judgment spaces theory context hypotheses witness claim before ready)

theorem certificate_accepted_iff_gslt_path (spaces : Spaces) (kernelTheory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces kernelTheory before) :
    (∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
      Presentation.Calculus.formMM0 (Presentation.Calculus.family kernelTheory).evaluate
      (Presentation.Calculus.derivesJ context hypotheses claim)
      (Presentation.Calculus.Witness.translate kernelTheory fuel context hypotheses witness) = true) ↔
      ∃ after, (theory program).MultiStep (requestConfiguration before spaces context hypotheses witness claim)
        (finished after [boolean true] [] []) := by
  rw [certificate_accepted_iff_source_accepts spaces kernelTheory context hypotheses witness claim before ready]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem rejected_certificate_iff_source_refuses (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    (¬ ∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
      Presentation.Calculus.formMM0 (Presentation.Calculus.family theory).evaluate
      (Presentation.Calculus.derivesJ context hypotheses claim)
      (Presentation.Calculus.Witness.translate theory fuel context hypotheses witness) = true) ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean false] [] [] := by
  rw [← Presentation.Calculus.Witness.checks_iff_accepted (T := theory) context hypotheses witness claim,
    ← ProofWitness.check_iff]
  exact Bool.eq_false_iff.symm.trans (result_iff_source_returns spaces theory context hypotheses witness claim before ready false)

theorem derives_iff_source_some_witness (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (claim : Preterm) (before : State) (ready : Ready spaces theory before) :
    Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses claim ↔
      ∃ witness after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean true] [] [] := by
  rw [Kernel.derives_iff_checked]
  exact exists_congr fun witness => result_iff_source_returns spaces theory context hypotheses witness claim before ready true

theorem formMM0_accepts_iff_source_some_witness (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (claim : Preterm) (before : State) (ready : Ready spaces theory before) :
    (Presentation.Calculus.mm0 theory).Accepts (Presentation.Calculus.derivesJ context hypotheses claim) ↔
      ∃ witness after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean true] [] [] :=
  (Presentation.Calculus.accepts_iff_derives (T := theory) context hypotheses claim).trans
    (derives_iff_source_some_witness spaces theory context hypotheses claim before ready)

theorem source_acceptance_derives (spaces : Spaces) (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm) (before after : State)
    (ready : Ready spaces theory before) (fuel : Nat)
    (accepted : run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
      .complete after [boolean true] [] []) :
    Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses claim :=
  ((checks_iff_source_accepts spaces theory context hypotheses witness claim before ready).mpr
    ⟨after, fuel, accepted⟩).derives

private def admissionEnvironment (spaces : Spaces) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) : Subst :=
  [("proof", Proof.witnessValue proof), ("dummies", Support.indicesValue dummies),
    ("declaration", TheoremInstantiation.declarationValue declaration),
    ("theorems", tableValue spaces.theorems), ("definitions", tableValue spaces.definitions),
    ("terms", tableValue spaces.terms)]

def admissionProofConfiguration (state : State) (spaces : Spaces) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) : Configuration :=
  { state, control := .evaluate (admissionEnvironment spaces declaration dummies proof)
      (.expression [.symbol "mm0:admission-proof", .var "terms", .var "definitions", .var "theorems",
        .var "declaration", .var "dummies", .var "proof"]) }

theorem admission_proof_sufficient_fuel (spaces : Spaces) (theory : Theory) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) (before : State) (ready : Ready spaces theory before) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (admissionProofConfiguration before spaces declaration dummies proof) =
        .complete after [boolean (ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
          (Admission.proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion)] [] []) ∧
      Ready spaces theory after ∧ InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  obtain ⟨after, bound, returned, readyAfter, frame⟩ :=
    AdmissionChecks.proof_captured_returns spaces theory declaration dummies proof before ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (admissionEnvironment spaces declaration dummies proof)
    before after _ _ (returned _ "terms" "definitions" "theorems" "declaration" "dummies" "proof" rfl rfl rfl rfl rfl rfl)
  exact ⟨after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem admission_proof_result_iff_source_returns (spaces : Spaces) (theory : Theory) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) (before : State) (ready : Ready spaces theory before) (answer : Bool) :
    ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
      (Admission.proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion = answer ↔
      ∃ after fuel, run program fuel (admissionProofConfiguration before spaces declaration dummies proof) =
        .complete after [boolean answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ := admission_proof_sufficient_fuel spaces theory declaration dummies proof before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    have values := List.singleton_inj.mp same.2.1
    simpa [boolean] using values

theorem admission_proof_completed_frame (spaces : Spaces) (theory : Theory) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) (before after : State) (ready : Ready spaces theory before)
    (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (admissionProofConfiguration before spaces declaration dummies proof) =
      .complete after answers [] []) :
    Ready spaces theory after ∧ ∃ bound, InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  obtain ⟨reference, bound, referenceFuel, completed, readyReference, frame⟩ :=
    admission_proof_sufficient_fuel spaces theory declaration dummies proof before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨readyReference, bound, frame⟩

theorem certificate_accepted_iff_admission_proof (spaces : Spaces) (theory : Theory) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) (before : State) (ready : Ready spaces theory before) :
    (∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
      Presentation.Calculus.formMM0 (Presentation.Calculus.family theory).evaluate
      (Presentation.Calculus.derivesJ (Admission.proofContext declaration dummies) declaration.hypotheses declaration.conclusion)
      (Presentation.Calculus.Witness.translate theory fuel (Admission.proofContext declaration dummies) declaration.hypotheses proof) = true) ↔
      ∃ after fuel, run program fuel (admissionProofConfiguration before spaces declaration dummies proof) =
        .complete after [boolean true] [] [] :=
  (Presentation.Calculus.Witness.checks_iff_accepted (T := theory) (Admission.proofContext declaration dummies)
    declaration.hypotheses proof declaration.conclusion).symm.trans
      ((ProofWitness.check_iff _ _ _ _ _ _ _).symm.trans
        (admission_proof_result_iff_source_returns spaces theory declaration dummies proof before ready true))

/-- The enclosing admission retains the separate freshness, declaration and
dummy-sort restrictions. Proof acceptance alone does not establish them. -/
theorem theorem_admission_iff_certificate_and_restrictions (spaces : Spaces) (theory : Theory) (index : Nat)
    (declaration : TheoremDecl) (dummies : List Nat) (proof : ProofWitness) (before : State)
    (ready : Ready spaces theory before) :
    (∃ after, DeclarativeSpec.Runs program
      (AdmissionChecks.requestConfiguration before spaces (.theoremDecl index declaration dummies proof))
      (.complete after [boolean true] [] [])) ↔
      theory.theoremSignature index = none ∧
      TheoremDecl.Admissible theory.sortSignature theory.termSignature declaration ∧
      (∀ sort ∈ dummies, ∃ info, theory.sortSignature sort = some info ∧ info.strict = false ∧ info.free = false) ∧
      ∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
        Presentation.Calculus.formMM0 (Presentation.Calculus.family theory).evaluate
        (Presentation.Calculus.derivesJ (Admission.proofContext declaration dummies) declaration.hypotheses declaration.conclusion)
        (Presentation.Calculus.Witness.translate theory fuel (Admission.proofContext declaration dummies) declaration.hypotheses proof) = true := by
  rw [← AdmissionChecks.authorized_iff_judgment spaces theory (.theoremDecl index declaration dummies proof) before ready]
  constructor
  · intro authorized
    cases authorized with
    | theoremDecl fresh formed allowed checked =>
      exact ⟨fresh, formed, allowed, (Presentation.Calculus.Witness.checks_iff_accepted (T := theory) _ _ _ _).mp checked⟩
  · rintro ⟨fresh, formed, allowed, certificate⟩
    exact .theoremDecl fresh formed allowed
      ((Presentation.Calculus.Witness.checks_iff_accepted (T := theory) _ _ _ _).mpr certificate)

/-- A running session may still have pending specification entries. Its
actual checked prefix suffices for source proof correspondence. -/
theorem preceding_specification_iff_source_some_witness (spaces : Spaces) (theory : Theory)
    (specification pending : List Kernel.SpecificationEntry) (declarations : List Kernel.ProofDeclaration)
    (checked : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨theory, pending⟩)
    (context : Context) (hypotheses : List Preterm) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (declarations.map Kernel.ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext context) (Upstream.Lean3ProofAdmission.sourceHypotheses hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel claim) ↔
      ∃ witness after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean true] [] [] := by
  have admitted : Kernel.Theory.run? {} (declarations.map Kernel.ProofDeclaration.admission) = some theory :=
    (Kernel.Theory.run_eq_some_iff _ _ _).mpr checked.theory_run
  exact (Upstream.Lean3ProofAdmission.checked_run_proof_iff admitted context hypotheses claim).trans
    (derives_iff_source_some_witness spaces theory context hypotheses claim before ready)

theorem admission_proof_has_specified_preceding_proof (spaces : Spaces) (theory : Theory)
    (specification pending : List Kernel.SpecificationEntry) (declarations : List Kernel.ProofDeclaration)
    (checked : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨theory, pending⟩)
    (declaration : TheoremDecl) (dummies : List Nat) (proof : ProofWitness) (before after : State)
    (ready : Ready spaces theory before) (fuel : Nat)
    (accepted : run program fuel (admissionProofConfiguration before spaces declaration dummies proof) =
      .complete after [boolean true] [] []) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (declarations.map Kernel.ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext (Admission.proofContext declaration dummies))
      (Upstream.Lean3ProofAdmission.sourceHypotheses declaration.hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel declaration.conclusion) := by
  have proofChecked := (admission_proof_result_iff_source_returns spaces theory declaration dummies proof before ready true).mpr
    ⟨after, fuel, accepted⟩
  have admitted : Kernel.Theory.run? {} (declarations.map Kernel.ProofDeclaration.admission) = some theory :=
    (Kernel.Theory.run_eq_some_iff _ _ _).mpr checked.theory_run
  exact (Upstream.Lean3ProofAdmission.checked_run_proof_iff admitted (Admission.proofContext declaration dummies)
    declaration.hypotheses declaration.conclusion).mpr (ProofWitness.check_sound proofChecked)

/-- Accepted theorem admission checks the supplied proof in the preceding
environment, while retaining every separate declaration restriction. -/
theorem theorem_admission_has_specified_preceding_proof (spaces : Spaces) (theory : Theory)
    (specification pending : List Kernel.SpecificationEntry) (declarations : List Kernel.ProofDeclaration)
    (checked : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨theory, pending⟩)
    (index : Nat) (declaration : TheoremDecl) (dummies : List Nat) (proof : ProofWitness)
    (before after : State) (ready : Ready spaces theory before) (fuel : Nat)
    (accepted : run program fuel
      (AdmissionChecks.requestConfiguration before spaces (.theoremDecl index declaration dummies proof)) =
      .complete after [boolean true] [] []) :
    theory.theoremSignature index = none ∧
      TheoremDecl.Admissible theory.sortSignature theory.termSignature declaration ∧
      (∀ sort ∈ dummies, ∃ info, theory.sortSignature sort = some info ∧ info.strict = false ∧ info.free = false) ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
        (Upstream.Lean3Typing.projectRun (declarations.map Kernel.ProofDeclaration.admission))
        (Upstream.Lean3Typing.Reference.ofContext (Admission.proofContext declaration dummies))
        (Upstream.Lean3ProofAdmission.sourceHypotheses declaration.hypotheses)
        (Upstream.Lean3Typing.Reference.SExpr.ofKernel declaration.conclusion) := by
  have authorized := (AdmissionChecks.authorized_iff_source_accepts spaces theory
    (.theoremDecl index declaration dummies proof) before ready).mpr ⟨after, fuel, accepted⟩
  have admitted : Kernel.Theory.run? {} (declarations.map Kernel.ProofDeclaration.admission) = some theory :=
    (Kernel.Theory.run_eq_some_iff _ _ _).mpr checked.theory_run
  cases authorized with
  | theoremDecl fresh formed allowed proofChecked =>
    exact ⟨fresh, formed, allowed,
      (Upstream.Lean3ProofAdmission.checked_run_proof_iff admitted (Admission.proofContext declaration dummies)
        declaration.hypotheses declaration.conclusion).mpr proofChecked.derives⟩

/-- The specified source judgment is connected only after an independently
checked preceding specification history. The driver earns that premise. -/
theorem specified_iff_source_some_witness (spaces : Spaces) (theory : Theory)
    (specification : List Kernel.SpecificationEntry) (declarations : List Kernel.ProofDeclaration)
    (checked : Kernel.SpecificationAdmission.verify? specification declarations = some theory)
    (context : Context) (hypotheses : List Preterm) (claim : Preterm) (before : State)
    (ready : Ready spaces theory before) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (declarations.map Kernel.ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext context) (Upstream.Lean3ProofAdmission.sourceHypotheses hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel claim) ↔
      ∃ witness after fuel, run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
        .complete after [boolean true] [] [] :=
  (Upstream.Lean3ProofAdmission.checked_specification_proof_iff checked context hypotheses claim).trans
    (derives_iff_source_some_witness spaces theory context hypotheses claim before ready)

theorem source_acceptance_has_specified_proof (spaces : Spaces) (theory : Theory)
    (specification : List Kernel.SpecificationEntry) (declarations : List Kernel.ProofDeclaration)
    (checked : Kernel.SpecificationAdmission.verify? specification declarations = some theory)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) (claim : Preterm)
    (before after : State) (ready : Ready spaces theory before) (fuel : Nat)
    (accepted : run program fuel (requestConfiguration before spaces context hypotheses witness claim) =
      .complete after [boolean true] [] []) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (declarations.map Kernel.ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext context) (Upstream.Lean3ProofAdmission.sourceHypotheses hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel claim) :=
  (specified_iff_source_some_witness spaces theory specification declarations checked context hypotheses claim before ready).mpr
    ⟨witness, after, fuel, accepted⟩

namespace Controls

open Kernel

private def spaces : Spaces :=
  ⟨.privateSpace 0, .privateSpace 1, .privateSpace 2, .privateSpace 3, .privateSpace 4, .privateSpace 5⟩
private def info : SortInfo := { provable := true }
private def primitive : TermDecl := ⟨[], 0, ∅⟩
private def first : TheoremDecl := ⟨[], [], .term 1⟩
private def second : TheoremDecl := ⟨[], [], .term 2⟩
private def declarations : Theory :=
  { sorts := [(0, info)], terms := [(2, primitive), (1, primitive)],
    theorems := [(11, second), (10, first)] }
private def initial : State :=
  { core := []
    next := 6
    spaces := fun index =>
      if index = 2 then SortFormation.rows declarations.sorts.reverse
      else if index = 3 then TableAccess.declarationRows declarations.terms.reverse
      else if index = 5 then Proof.theoremRows declarations.theorems.reverse
      else []
    cells := fun name => if name = InferenceCache.cell then some (Effects.handleValue spaces.cache) else none }

private theorem ready : Ready spaces declarations initial := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩, ?_⟩
  · simp [initial, spaces, NamedSpaces.Store.read]
  · simp [initial, spaces, NamedSpaces.Store.read]
  · simp [initial, spaces, declarations, Unfolding.definitionRows, Store.rows, NamedSpaces.Store.read]
  · simp [initial, spaces, NamedSpaces.Store.read]
  · intro key; by_cases same : 0 = key <;> simp [declarations, same]
  · intro key
    by_cases two : 2 = key
    · subst key; decide +kernel
    · by_cases one : 1 = key
      · subst key; decide +kernel
      · simp [declarations, two, one]
  · intro key; simp [declarations]
  · intro key
    by_cases eleven : 11 = key
    · subst key; decide +kernel
    · by_cases ten : 10 = key
      · subst key; decide +kernel
      · simp [declarations, eleven, ten]
  · refine ⟨?_, [], ?_, InferenceCache.empty_valid _ _⟩ <;>
      simp [initial, spaces, NamedSpaces.Store.read]

private def specification : List SpecificationEntry :=
  [.sort 0 info, .term 1 primitive, .term 2 primitive, .axiomDecl 10 first, .axiomDecl 11 second]
private def history : List ProofDeclaration :=
  [⟨.sort 0 info, false⟩, ⟨.term 1 primitive, false⟩, ⟨.term 2 primitive, false⟩,
    ⟨.axiomDecl 10 first, false⟩, ⟨.axiomDecl 11 second, false⟩]
private theorem verified : SpecificationAdmission.verify? specification history = some declarations := by
  apply (SpecificationAdmission.verify_eq_some_iff _ _ _).mpr
  refine .cons (.publicDecl (.sort _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
    (.cons (.publicDecl (.term _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
      (.cons (.publicDecl (.term _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
        (.cons (.publicDecl (.axiomDecl _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
          (.cons (.publicDecl (.axiomDecl _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
            (.nil _)))))
  all_goals decide +kernel

/-- Native rows are ordered opposite to the independently admitted theory. -/
theorem physical_rows_are_chronological :
    initial.read spaces.terms = some (TableAccess.declarationRows [(1, primitive), (2, primitive)]) ∧
      [(1, primitive), (2, primitive)] ≠ declarations.terms := by
  constructor
  · rfl
  · decide +kernel

/-- A lookup of the earlier theorem succeeds through chronological native rows. -/
theorem chronological_source_accepts :
    ∃ after fuel, run program fuel (requestConfiguration initial spaces [] [] (.theoremApp 10 [] []) (.term 1)) =
      .complete after [boolean true] [] [] := by
  apply (result_iff_source_returns spaces declarations [] [] _ _ initial ready true).mp
  decide +kernel

/-- A stored theorem cannot prove a different requested conclusion. -/
theorem wrong_conclusion_source_refuses :
    ∃ after fuel, run program fuel (requestConfiguration initial spaces [] [] (.theoremApp 10 [] []) (.term 2)) =
      .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns spaces declarations [] [] _ _ initial ready false).mp
  decide +kernel

/-- The admitted history proves the claim, but a missing supplied hypothesis
still yields a completed refusal in the actual source checker. -/
theorem specified_proof_does_not_repair_submitted_witness :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (history.map ProofDeclaration.admission)) []
      (Upstream.Lean3ProofAdmission.sourceHypotheses []) (.term 1) ∧
      ∃ after fuel, run program fuel (requestConfiguration initial spaces [] [] (.hyp 0) (.term 1)) =
        .complete after [boolean false] [] [] := by
  constructor
  · simpa only [Upstream.Lean3Typing.Reference.ofContext, List.map_nil,
      Upstream.Lean3Typing.Reference.SExpr.ofKernel] using
      (Upstream.Lean3ProofAdmission.checked_specification_proof_iff verified [] [] (.term 1)).mpr
        (ProofWitness.check_sound (witness := .theoremApp 10 [] []) (by decide +kernel))
  · apply (result_iff_source_returns spaces declarations [] [] _ _ initial ready false).mp
    decide +kernel

end Controls

end Mettapedia.Languages.MM0.MeTTa.SessionProof
