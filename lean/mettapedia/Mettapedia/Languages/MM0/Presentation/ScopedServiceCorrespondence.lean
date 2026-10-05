import Mettapedia.Languages.MM0.Presentation.ScopedServiceProgram

/-!
# Submitted shared MM0 proofs through generated execution

The sequential protocol is equivalent to the existing checked-store judgment.
Instantiating the common emitter theorem carries that equivalence to the
independent MeTTa interpreter. Initializers are retained even when the root
does not use them. The actual theory, variable context and hypotheses are
fixed throughout one store, and each later initializer sees only its prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ScopedService

open Kernel Calculus ComputationalCalculus SharedCertificates
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Execution
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
open Metta.Minimal

theorem verdict_accepted (T : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) (certificate : Certificate T) :
    verdict T context hypotheses claim certificate = true ↔
      Accepted T context hypotheses claim certificate := by
  unfold Accepted
  rw [Service.calculus_returns _ (by decide +kernel), certificate_returns_iff]
  change _ ↔ Term.sym "True" = boolean (verdict T context hypotheses claim certificate)
  cases verdict T context hypotheses claim certificate <;> simp [boolean]

theorem checkSaved_append (T : Theory) (context : Context) (hypotheses : List Preterm)
    (before after : List (Preterm × Certificate T)) :
    checkSaved T context hypotheses (before ++ after) =
      (checkSaved T context hypotheses before &&
        checkSaved T context (hypotheses ++ before.map Prod.fst) after) := by
  induction before generalizing hypotheses with
  | nil => simp [checkSaved]
  | cons entry rest ih =>
      obtain ⟨claim, certificate⟩ := entry
      simp only [List.cons_append, checkSaved, ih, List.map_cons]
      simp [List.append_assoc, Bool.and_assoc]

private theorem store_snoc_iff (T : Theory) (context : Context) (hypotheses : List Preterm)
    (before : List (Preterm × Certificate T)) (claim : Preterm) (certificate : Certificate T) :
    StoreChecked T context hypotheses (before ++ [(claim, certificate)]) ↔
      StoreChecked T context hypotheses before ∧
        Accepted T context (hypotheses ++ before.map Prod.fst) claim certificate := by
  constructor
  · intro checked
    generalize same : before ++ [(claim, certificate)] = saved at checked
    cases checked with
    | nil => simp at same
    | record prior accepted =>
        obtain ⟨rfl, pair⟩ := List.append_singleton_inj.mp same
        cases pair
        exact ⟨prior, accepted⟩
  · rintro ⟨prior, accepted⟩
    exact .record prior accepted

theorem checkSaved_true_iff (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) :
    checkSaved T context hypotheses saved = true ↔ StoreChecked T context hypotheses saved := by
  induction saved using List.reverseRecOn with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | append_singleton before entry ih =>
      obtain ⟨claim, certificate⟩ := entry
      rw [checkSaved_append, checkSaved, checkSaved, Bool.and_true,
        Bool.and_eq_true, ih, verdict_accepted, store_snoc_iff]

theorem checkRun_split (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) (claim : Preterm) (certificate : Certificate T) :
    checkRun T context hypotheses saved claim certificate =
      (checkSaved T context hypotheses saved &&
        verdict T context (hypotheses ++ saved.map Prod.fst) claim certificate) := by
  induction saved generalizing hypotheses with
  | nil => simp [checkRun, checkSaved]
  | cons entry rest ih =>
      obtain ⟨first, initializer⟩ := entry
      simp only [checkRun, checkSaved, ih, List.map_cons]
      simp [List.append_assoc, Bool.and_assoc]

private theorem boolean_true (value : Bool) : Term.sym "True" = boolean value ↔ value = true := by
  cases value <;> simp [boolean]

theorem run_accepted_iff (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) (claim : Preterm) (certificate : Certificate T) :
    Applies program dataEqualityHost "mm0:scoped-run"
        (request T context hypotheses saved claim certificate) (.sym "True") ↔
      StoreChecked T context hypotheses saved ∧
        Accepted T context (hypotheses ++ saved.map Prod.fst) claim certificate := by
  rw [run_result_exact, boolean_true, checkRun_split, Bool.and_eq_true,
    checkSaved_true_iff, verdict_accepted]

/-- Same submitted initializers and root, including unused initializers. -/
theorem shared_witness_iff (T : Theory) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : SharedProof) :
    SharedProof.Checks T declaration dummies proof ↔
      Applies program dataEqualityHost "mm0:scoped-run"
        (request T (Admission.proofContext declaration dummies) declaration.hypotheses
          (translatedEntries T 0 (Admission.proofContext declaration dummies)
            declaration.hypotheses proof.saved) declaration.conclusion
          (Witness.translate T 0 (Admission.proofContext declaration dummies)
            (declaration.hypotheses ++ proof.saved.map Prod.fst) proof.root)) (.sym "True") := by
  rw [run_accepted_iff, translatedEntries_claims]
  exact SharedCertificates.shared_witness_iff T 0 declaration dummies proof

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

def Returns (environment : MinEnv) (sourceFuel : Nat) (arguments : List Term) (result : Term) : Prop :=
  StableReturns environment
    (returnInvocation (requestAtom program sourceFuel "mm0:scoped-run" arguments)) (.value result)

theorem some_fuel_returns_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (arguments : List Term) (result : Term) :
    (∃ sourceFuel, Returns environment sourceFuel arguments result) ↔
      Applies program dataEqualityHost "mm0:scoped-run" arguments result := by
  simp only [Returns, invocation_stable_iff program dataEqualityHost environment loaded primitives
    dataEqualityHost_unlisted, Applies]

/-- The actual emitted program preserves and reflects the shared witness. -/
theorem emitted_shared_witness_iff (environment : MinEnv) (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute dataEqualityHost environment)
    (T : Theory) (declaration : TheoremDecl) (dummies : List Nat) (proof : SharedProof) :
    SharedProof.Checks T declaration dummies proof ↔
      ∃ sourceFuel, Returns environment sourceFuel
        (request T (Admission.proofContext declaration dummies) declaration.hypotheses
          (translatedEntries T 0 (Admission.proofContext declaration dummies)
            declaration.hypotheses proof.saved) declaration.conclusion
          (Witness.translate T 0 (Admission.proofContext declaration dummies)
            (declaration.hypotheses ++ proof.saved.map Prod.fst) proof.root)) (.sym "True") := by
  rw [some_fuel_returns_iff environment loaded primitives]
  exact shared_witness_iff T declaration dummies proof

theorem run_refused_iff (T : Theory) (context : Context) (hypotheses : List Preterm)
    (saved : List (Preterm × Certificate T)) (claim : Preterm) (certificate : Certificate T) :
    Applies program dataEqualityHost "mm0:scoped-run"
        (request T context hypotheses saved claim certificate) (.sym "False") ↔
      ¬ (StoreChecked T context hypotheses saved ∧
        Accepted T context (hypotheses ++ saved.map Prod.fst) claim certificate) := by
  rw [← run_accepted_iff, run_result_exact, run_result_exact]
  cases checkRun T context hypotheses saved claim certificate <;> simp [boolean]

/-- A returned store cannot manufacture the first theorem of an empty theory. -/
theorem empty_theory_refuses (context : Context) (saved : List (Preterm × Certificate {}))
    (claim : Preterm) (certificate : Certificate {}) :
    Applies program dataEqualityHost "mm0:scoped-run"
      (request {} context [] saved claim certificate) (.sym "False") := by
  apply (run_refused_iff {} context [] saved claim certificate).mpr
  rintro ⟨checked, root⟩
  exact checked_store_cannot_create_first_theorem context checked root

def repeatedHypothesis (claim : Preterm) : SharedProof :=
  ⟨[(claim, .hyp 0), (claim, .hyp 1)], .hyp 2⟩

theorem repeated_hypothesis_checked (context : Context) (claim : Preterm) :
    SharedProof.Checks {} ⟨context, [claim], claim⟩ [] (repeatedHypothesis claim) := by
  constructor
  · dsimp only [repeatedHypothesis]
    apply SavedWitnessesChecked.record (before := [(claim, .hyp 0)])
    · apply SavedWitnessesChecked.record (before := [])
      · exact .nil
      · simp [ProofWitness.check, ProofWitness.proof?,
          Admission.proofContext]
    · simp [ProofWitness.check, ProofWitness.proof?,
        Admission.proofContext]
  · simp [ProofWitness.check, ProofWitness.proof?, repeatedHypothesis, Admission.proofContext]

/-- Later initializers may use the preceding entry, while the root sees both. -/
theorem repeated_hypothesis_executes (context : Context) (claim : Preterm) :
    Applies program dataEqualityHost "mm0:scoped-run"
      (request {} context [claim]
        (translatedEntries {} 0 context [claim] (repeatedHypothesis claim).saved) claim
        (Witness.translate {} 0 context
          ([claim] ++ (repeatedHypothesis claim).saved.map Prod.fst) (repeatedHypothesis claim).root))
      (.sym "True") := by
  simpa only [Admission.proofContext,
    List.map_nil, List.append_nil] using
    (shared_witness_iff {} ⟨context, [claim], claim⟩ [] (repeatedHypothesis claim)).mp
      (repeated_hypothesis_checked context claim)

/-- An invalid unused initializer is not excused by a valid root. -/
theorem unused_forward_reference_rejected (context : Context) (claim : Preterm) :
    ¬ SharedProof.Checks {} ⟨context, [claim], claim⟩ []
      ⟨[(claim, .hyp 1)], .hyp 0⟩ := by
  rintro ⟨store, _⟩
  generalize same : [(claim, ProofWitness.hyp 1)] = saved at store
  cases store with
  | nil => simp at same
  | @record before expression witness prior checked =>
      have pair : before = [] ∧ (expression, witness) = (claim, ProofWitness.hyp 1) :=
        List.append_singleton_inj.mp same.symm
      obtain ⟨rfl, pair⟩ := pair
      cases pair
      simp [ProofWitness.check, ProofWitness.proof?, Admission.proofContext] at checked

end Mettapedia.Languages.MM0.Presentation.ScopedService
