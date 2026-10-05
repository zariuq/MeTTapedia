import Mettapedia.Languages.MM0.Presentation.CalculusWitness
import Mettapedia.Languages.MM0.Presentation.AdmissionCorrespondence
import Mettapedia.Languages.MM0.Kernel.SpecificationChecking

/-!
# Admission in the MM0 tier

A theory grows by admissions. A sort, term, definition or axiom is admitted when
the authored admission program accepts it against the current theory. A theorem
is admitted when its index is fresh, its statement is formed and its dummy sorts
are allowed, each decided by an authored program, and when the shared checker
accepts the certificate of its proof in the MM0 calculus of the current theory.
The proof is the submitted witness, translated node for node.

This admission is exactly the kernel's, step by step and along every run, and
the resulting theories are the same. A proof file verified against its
specification therefore has every proof accepted by the shared checker, and its
axioms are exactly the specification's.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.Calculus.Admission

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.Languages.MM0.Kernel
open ComputationalContext ComputationalArguments ComputationalProof ComputationalTyping
open ComputationalDeclaration ComputationalAdmission
open Mettapedia.Languages.MM0.Presentation.Calculus.Witness

/-- A program returning the boolean of a check accepts exactly when the check
holds. -/
theorem applies_true_iff {P : Program} {H : Host} {head : String} {arguments : List Term}
    {value : Bool} (computes : Applies P H head arguments (boolean value)) :
    Applies P H head arguments (.sym "True") ↔ value = true := by
  constructor
  · intro run
    have same := run.deterministic computes
    cases value
    · simp [boolean] at same
    · rfl
  · intro holds
    subst holds
    exact computes

/-- The proof obligation of a theorem: the shared checker accepts the
certificate of its witness for its statement. -/
def ProofAccepted (theory : Theory) (declaration : TheoremDecl) (dummies : List Nat)
    (proof : ProofWitness) : Prop :=
  ∃ fuel, check formMM0 (family theory).evaluate
    (derivesJ (Kernel.Admission.proofContext declaration dummies) declaration.hypotheses
      declaration.conclusion)
    (translate theory fuel (Kernel.Admission.proofContext declaration dummies)
      declaration.hypotheses proof) = true

/-- **Authorization in the MM0 tier.** -/
def Authorized (theory : Theory) : Kernel.Admission → Prop
  | .theoremDecl index declaration dummies proof =>
      Applies admissionProgram dataEqualityHost "mm0:admission-fresh"
          [encodeTheorems theory.theorems, natural index] (.sym "True") ∧
        Applies declarationProgram dataEqualityHost "mm0:form-theorem"
          [encodeSorts theory.sorts, encodeTable theory.terms, encodeTheorem declaration]
          (.sym "True") ∧
        Applies declarationProgram dataEqualityHost "mm0:form-dummies"
          [encodeSorts theory.sorts, encodeNaturals dummies] (.sym "True") ∧
        ProofAccepted theory declaration dummies proof
  | admission =>
      Applies admissionProgram dataEqualityHost "mm0:admission-check"
        [encodeTheory theory, encodeAdmission admission] (.sym "True")

/-- **Authorization is the kernel's.** -/
theorem authorized_iff (theory : Theory) (admission : Kernel.Admission) :
    Authorized theory admission ↔ Kernel.Admission.Authorized theory admission := by
  cases admission with
  | theoremDecl index declaration dummies proof =>
      simp only [Authorized, ProofAccepted]
      have fresh : Applies admissionProgram dataEqualityHost "mm0:admission-fresh"
          [encodeTheorems theory.theorems, natural index]
          (boolean (theory.theorems.lookup index).isNone) :=
        fresh_computes encodeTheorem theory.theorems index
      rw [applies_true_iff fresh,
        applies_true_iff (theorem_computes theory.sorts theory.terms declaration),
        applies_true_iff (dummies_computes theory.sorts dummies),
        ← checks_iff_accepted, theory_sorts, theory_signature, TheoremDecl.check_iff,
        Definition.checkDummySorts_iff, Option.isNone_iff_eq_none]
      constructor
      · rintro ⟨fresh, formed, allowed, checked⟩
        exact .theoremDecl fresh formed allowed checked
      · intro authorized
        cases authorized with
        | theoremDecl fresh formed allowed checked => exact ⟨fresh, formed, allowed, checked⟩
  | sort => exact check_accepts_iff theory _
  | term => exact check_accepts_iff theory _
  | definition => exact check_accepts_iff theory _
  | axiomDecl => exact check_accepts_iff theory _

/-- An admission step of the MM0 tier. -/
inductive Step (before : Theory) (admission : Kernel.Admission) : Theory → Prop where
  | intro : Authorized before admission → Step before admission (admission.insert before)

theorem step_iff (before after : Theory) (admission : Kernel.Admission) :
    Step before admission after ↔ Theory.Step before admission after := by
  constructor
  · rintro ⟨authorized⟩
    exact .intro ((authorized_iff before admission).mp authorized)
  · rintro ⟨authorized⟩
    exact .intro ((authorized_iff before admission).mpr authorized)

/-- Runs of admissions in the MM0 tier. -/
inductive Runs : Theory → List Kernel.Admission → Theory → Prop where
  | nil (theory : Theory) : Runs theory [] theory
  | cons {before middle after : Theory} {head : Kernel.Admission} {tail : List Kernel.Admission} :
      Step before head middle → Runs middle tail after → Runs before (head :: tail) after

/-- **Runs are the kernel's, with the same resulting theory.** -/
theorem runs_iff (before after : Theory) (admissions : List Kernel.Admission) :
    Runs before admissions after ↔ Theory.Runs before admissions after := by
  constructor
  · intro runs
    induction runs with
    | nil theory => exact .nil theory
    | cons step _ ih => exact .cons ((step_iff _ _ _).mp step) ih
  · intro runs
    induction runs with
    | nil theory => exact .nil theory
    | cons step _ ih => exact .cons ((step_iff _ _ _).mpr step) ih

/-- **A verified proof file is admitted by the MM0 tier**: every admission,
including every theorem's proof, is authorized by the authored programs and the
shared checker, and the resulting theory is the verified one. -/
theorem verified_runs {specification : List SpecificationEntry}
    {declarations : List ProofDeclaration} {theory : Theory}
    (accepted : SpecificationAdmission.verify? specification declarations = some theory) :
    Runs {} (declarations.map ProofDeclaration.admission) theory :=
  (runs_iff _ _ _).mpr
    ((SpecificationAdmission.verify_eq_some_iff _ _ _).mp accepted).theory_run

/-- In a verified proof file, every theorem's proof is accepted by the shared
checker in the theory admitted before it. -/
theorem verified_theorem_accepted {before after : Theory} {index : Nat}
    {declaration : TheoremDecl} {dummies : List Nat} {proof : ProofWitness}
    (step : Step before (.theoremDecl index declaration dummies proof) after) :
    ProofAccepted before declaration dummies proof := by
  cases step with
  | intro authorized => exact authorized.2.2.2

end Mettapedia.Languages.MM0.Presentation.Calculus.Admission
