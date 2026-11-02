import Mettapedia.Logic.TierZero.Adequacy.MM0SymbolicExport

/-!
# Conservative theorem-table and actual kernel-catalog installation

An installation retains an actual symbolic source-schedule certificate and
the ordinary declaration checker result. It inserts the inferred declaration
at a fresh theorem identifier. The independent exported derivation proves
conservativity in every later context and under every local hypothesis list.

Rebuilding a running system replaces only the kernel's actual key catalog.
Client schemas, their activation and all actor rights remain unchanged. The
resulting protected outputs are independently derivable in the original
theory. Native mutation, revision publication and atomic registry updates are
separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInstallation

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0ContextualSupport
open MM0Rewriting
open MM0LocatedActivation (Value)

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO} [DecidableEq O]
    {theory : Theory} {formal : Context} {location : O → Space}

structure Installation (system : MM0LocatedKernel.System theory formal C X I O location)
    (payload : O → Tm) where
  certificate : MM0SymbolicExport.Certificate system payload
  index : Nat
  fresh : theory.theoremSignature index = none
  admitted : certificate.declaration.check theory.sortSignature theory.termSignature = true

namespace Installation

variable {system : MM0LocatedKernel.System theory formal C X I O location} {payload : O → Tm}
    (installation : Installation system payload)

def declaration : TheoremDecl := installation.certificate.declaration

def installed : Theory :=
  { theory with theorems := (installation.index, installation.declaration) :: theory.theorems }

theorem installed_theorems : installation.installed.theoremSignature =
    TheoremSignature.extend theory.theoremSignature installation.index installation.declaration := by
  funext queried
  by_cases same : queried = installation.index
  · simp [installed, Theory.theoremSignature, TheoremSignature.extend, same]
  · have compared : (queried == installation.index) = false := by simp [same]
    simp [installed, Theory.theoremSignature, TheoremSignature.extend, List.lookup_cons, same, compared]

theorem declaration_admitted : installation.declaration.Admissible theory.sortSignature theory.termSignature :=
  (TheoremDecl.check_iff _ _ _).mp installation.admitted

theorem justified (wellFormed : theory.WellFormed) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      installation.declaration.arguments installation.declaration.hypotheses installation.declaration.conclusion :=
  installation.certificate.justified wellFormed installation.declaration_admitted.context

theorem installed_wellFormed (wellFormed : theory.WellFormed) : installation.installed.WellFormed := by
  constructor
  · exact wellFormed.terms
  · exact wellFormed.definitions
  · intro index declaration known
    rw [installation.installed_theorems] at known
    by_cases same : index = installation.index
    · subst index
      have payloadEqual : installation.declaration = declaration := by
        simpa [TheoremSignature.extend] using known
      subst declaration
      exact installation.declaration_admitted
    · exact wellFormed.theorems index declaration (by simpa [TheoremSignature.extend, same] using known)

/-- Every use of the new schema is eliminated by independently justified
admissible instantiation and cut, for arbitrary target hypotheses. -/
theorem conservative (wellFormed : theory.WellFormed) (target : Context)
    (hypotheses : List Preterm) (expression : Preterm) :
    Derives installation.installed.termSignature installation.installed.definitionSignature
        installation.installed.theoremSignature target hypotheses expression ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression := by
  change Derives theory.termSignature theory.definitionSignature installation.installed.theoremSignature _ _ _ ↔ _
  rw [installation.installed_theorems]
  exact TheoremSignature.extend_iff installation.fresh (installation.justified wellFormed) target hypotheses expression

theorem natural_reachability_conservative (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    MM0ScopedProcess.Reaches installation.installed target hypotheses expression ↔
      MM0ScopedProcess.Reaches theory target hypotheses expression := by
  rw [MM0ScopedProcess.scoped_reaches_iff_derives (installation.installed_wellFormed wellFormed) formed,
    MM0ScopedProcess.scoped_reaches_iff_derives wellFormed formed]
  exact installation.conservative wellFormed target hypotheses expression

theorem validValue_iff (wellFormed : theory.WellFormed) (target : Context) (hypotheses : List Preterm) (value : Tm) :
    ValidValue installation.installed.termSignature installation.installed.definitionSignature
        installation.installed.theoremSignature target hypotheses value ↔
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
  constructor
  · rintro ⟨proofs, conversions⟩
    exact ⟨fun expression same => (installation.conservative wellFormed target hypotheses expression).mp
      (proofs expression same), conversions⟩
  · rintro ⟨proofs, conversions⟩
    exact ⟨fun expression same => (installation.conservative wellFormed target hypotheses expression).mpr
      (proofs expression same), conversions⟩

section Rebuild

universe uD uY uA uP
variable {D : Type uD} {Y : Type uY} {A : Type uA} {P : Type uP} [DecidableEq A] [DecidableEq P]
    {target : Context} {whereAt : P → Space}
    (consumer : MM0LocatedKernel.System theory target D Y A P whereAt)

def rebuilt : MM0LocatedKernel.System installation.installed target D Y A P whereAt where
  clientActivation := consumer.clientActivation
  authority :=
    { process := fun actor => if actor = consumer.authority.kernel then
        ⟨(consumer.authority.process actor).rights, (catalog installation.installed).map Sum.inl⟩
      else consumer.authority.process actor
      kernel := consumer.authority.kernel
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        simpa only [if_neg notKernel] using consumer.authority.soleWriter actor notKernel occurrence protectedHere }
  kernelSchemas := by simp

omit [DecidableEq P] in
theorem rebuilt_rights (actor : A) :
    ((installation.rebuilt consumer).authority.process actor).rights = (consumer.authority.process actor).rights := by
  by_cases same : actor = consumer.authority.kernel <;> simp [rebuilt, same]

omit [DecidableEq P] in
theorem rebuilt_client_process (actor : A) (client : actor ≠ consumer.authority.kernel) :
    (installation.rebuilt consumer).authority.process actor = consumer.authority.process actor := by
  simp [rebuilt, client]

omit [DecidableEq P] in
theorem rebuilt_client_activation : (installation.rebuilt consumer).clientActivation = consumer.clientActivation := rfl

omit [DecidableEq P] in
theorem protected_valid_iff (wellFormed : theory.WellFormed) (hypotheses : List Preterm)
    (values : P → Tm) (state : Configuration Value P) :
    MM0LocatedKernel.ProtectedValid installation.installed target hypotheses whereAt values state ↔
      MM0LocatedKernel.ProtectedValid theory target hypotheses whereAt values state := by
  constructor <;> intro prior assignment solved occurrence present protectedHere
  · exact (installation.validValue_iff wellFormed target hypotheses _).mp
      (prior assignment solved occurrence present protectedHere)
  · exact (installation.validValue_iff wellFormed target hypotheses _).mpr
      (prior assignment solved occurrence present protectedHere)

/-- A run of the rebuilt real kernel system publishes no new logical
consequence, including when the installed schema is instantiated differently
from the source schedule which justified it. -/
theorem published_proof_is_base_derivable (wellFormed : theory.WellFormed)
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (values : P → Tm)
    {before after : Configuration Value P} {schedule : List A}
    (run : (installation.rebuilt consumer).Run values before schedule after)
    (prior : MM0LocatedKernel.ProtectedValid theory target hypotheses whereAt values before)
    (assignment : ABTProtectedParameters.Assignment Head target.length)
    (solved : (MM0LocatedActivation.action target).Models assignment after.equations)
    (occurrence : P) (present : occurrence ∈ after.present)
    (isProtected : MM0LocatedKernel.protectedOccurrence whereAt occurrence)
    (expression : Preterm)
    (observed : (MM0ConstraintParameters.action target).apply assignment (values occurrence) = proofValue target expression) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression := by
  apply (installation.conservative wellFormed target hypotheses expression).mp
  exact (installation.rebuilt consumer).published_proof_is_derivable
    (installation.installed_wellFormed wellFormed) formed hypotheses values run
    ((installation.protected_valid_iff wellFormed hypotheses values before).mpr prior)
    assignment solved occurrence present isProtected expression observed

end Rebuild
end Installation
end Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInstallation
