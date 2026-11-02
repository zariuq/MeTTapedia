import Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInterface
import Mettapedia.Languages.MM0.Kernel.DerivedTheoremExtension

/-!
# Symbolic source schedules export independently justified MM0 schemas

The export retains source keys, inputs, physical selections, computed
activation, every compiled condition and the final equation solution. Its
logical hypotheses are decoded from the initial protected occurrences that
the existing proof-use calculation actually uses. The complete formal context
and source-argument footprint remain inspectable even for a closed conclusion.

The independent derivation is extracted from the source schedule and used for
admissible substitution and cut. A concrete instance cannot certify a different
formal context or a declaration with fewer used hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0SymbolicExport

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0ContextualSupport
open MM0Rewriting
open MM0LocatedActivation (Value)

def proofExpression (formal : Context) : Tm → Option Preterm
  | .node (.judgment "pf") (.cons 0 body .nil) => decodeExact formal body
  | _ => none

theorem proofExpression_iff (formal : Context) (value : Tm) (expression : Preterm) :
    proofExpression formal value = some expression ↔ value = proofValue formal expression := by
  cases value with
  | idx index => simp [proofExpression, proofValue, judgment]
  | node head fields =>
      cases head <;> try simp [proofExpression, proofValue, judgment]
      rename_i tag
      cases fields with
      | nil => simp [MM0Rewriting.fields]
      | cons depth body rest =>
          cases depth with
          | succ depth => simp [MM0Rewriting.fields]
          | zero =>
              cases rest with
              | cons depth body rest => simp [MM0Rewriting.fields]
              | nil =>
                  by_cases same : tag = "pf"
                  · subst tag
                    simpa [proofExpression, proofValue, judgment, MM0Rewriting.fields] using
                      decodeExact_iff formal body expression
                  · simp [MM0Rewriting.fields, same]

def hypotheses {O : Type*} (formal : Context) (payload : O → Tm) (origins : List O) :
    List Preterm := origins.filterMap (proofExpression formal ∘ payload)

theorem decoded_hypothesis_retained {O : Type*} (formal : Context) (payload : O → Tm)
    {origins : List O} {source : O} {expression : Preterm}
    (member : source ∈ origins) (decoded : proofExpression formal (payload source) = some expression) :
    expression ∈ hypotheses formal payload origins := by
  exact List.mem_filterMap.mpr ⟨source, member, decoded⟩

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO} [DecidableEq O]
    {theory : Theory} {formal : Context} {location : O → Space}

structure Certificate (system : MM0LocatedKernel.System theory formal C X I O location)
    (payload : O → Tm) where
  sources : List (SchemaSchedules.SourceFiring (MM0LocatedKernel.SourceSchema C) (MM0LocatedKernel.Inputs X) O)
  schedule : List (ConditionalSchedule.Firing Value O)
  computed : SchemaSchedules.lowerAll system.activate sources = some schedule
  authorized : ∀ source ∈ sources,
    source.schema ∈ (system.authority.process system.authority.kernel).schemas ∧
      PublicationAuthority.Formed (system.authority.process system.authority.kernel).rights location source.selection
  before : Configuration Value O
  enabled : (ConditionalSchedule.compile (fun occurrence => (location occurrence, payload occurrence)) schedule).Holds
    (MM0LocatedActivation.action formal) (fun occurrence => (location occurrence, payload occurrence)) before
  assignment : ABTProtectedParameters.Assignment Head formal.length
  solved : (MM0LocatedActivation.action formal).Models assignment
    (ConditionalSchedule.follow (fun occurrence => (location occurrence, payload occurrence)) before schedule).equations
  output : O
  present : output ∈ (ConditionalSchedule.follow (fun occurrence => (location occurrence, payload occurrence)) before schedule).present
  protectedOutput : MM0LocatedKernel.protectedOccurrence location output
  conclusion : Preterm
  observed : (MM0ConstraintParameters.action formal).apply assignment (payload output) = proofValue formal conclusion
  originOrder : List O
  originDistinct : originOrder.Nodup
  originInventory : originOrder.toFinset = ProofUse.followOrigins (MM0LocatedKernel.protectedOccurrence location)
    ProofUse.initialOrigins schedule output
  decoded : originOrder.all (fun source => (proofExpression formal (payload source)).isSome) = true

namespace Certificate

variable {system : MM0LocatedKernel.System theory formal C X I O location} {payload : O → Tm}
    (certificate : Certificate system payload)

def used : Finset O := ProofUse.followOrigins (MM0LocatedKernel.protectedOccurrence location)
  ProofUse.initialOrigins certificate.schedule certificate.output

def declaration : TheoremDecl :=
  ⟨formal, hypotheses formal payload certificate.originOrder, certificate.conclusion⟩

def parameterFootprint : Finset Nat := MM0SchemaInterface.parameterFootprint formal certificate.sources
  certificate.declaration.hypotheses certificate.conclusion

theorem used_sources_are_initial_and_protected : ∀ source ∈ certificate.used,
    source ∈ certificate.before.present ∧ MM0LocatedKernel.protectedOccurrence location source := by
  exact ProofUse.inferred_sources_are_initial_protected_occurrences
    (MM0LocatedKernel.protectedOccurrence location) (MM0LocatedActivation.action formal)
    (fun occurrence => (location occurrence, payload occurrence)) certificate.before certificate.schedule
    ((ConditionalSchedule.compile_holds_iff _ _ _ _).mp certificate.enabled)
    certificate.output certificate.present certificate.protectedOutput

theorem actual_system_run : system.Run payload certificate.before
    (List.replicate certificate.schedule.length system.authority.kernel)
    (ConditionalSchedule.follow (fun occurrence => (location occurrence, payload occurrence))
      certificate.before certificate.schedule) :=
  SchemaSchedules.compiled_system_run system.authority system.activate (MM0LocatedActivation.action formal)
    (fun occurrence => (location occurrence, payload occurrence)) certificate.computed certificate.before
    certificate.enabled certificate.authorized

theorem justified (wellFormed : theory.WellFormed)
    (formed : Context.WellFormed theory.sortSignature formal) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      certificate.declaration.arguments certificate.declaration.hypotheses certificate.declaration.conclusion := by
  have derived := SchemaSchedules.compiled_derivation (MM0LocatedKernel.protectedOccurrence location)
    (MM0LocatedActivation.action formal) (fun occurrence => (location occurrence, payload occurrence))
    system.activate (system.authority.process system.authority.kernel).schemas certificate.sources
    certificate.schedule certificate.computed (fun source member => (certificate.authorized source member).1)
    certificate.before certificate.enabled certificate.assignment certificate.solved certificate.output
    certificate.present certificate.protectedOutput
  have valid := MM0LocatedInference.derivable_valid system wellFormed formed certificate.declaration.hypotheses payload
    (ProofUse.Hypotheses (MM0LocatedActivation.action formal) certificate.assignment
      (fun occurrence => (location occurrence, payload occurrence)) certificate.used) ?_ derived
  · exact valid.1 certificate.conclusion certificate.observed
  · intro value assumed
    obtain ⟨source, member, rfl⟩ := assumed
    have sourcePresent : source ∈ certificate.originOrder := by
      apply List.mem_toFinset.mp
      rw [certificate.originInventory]
      exact member
    have isDecoded := List.all_eq_true.mp certificate.decoded source sourcePresent
    obtain ⟨expression, decoded⟩ := Option.isSome_iff_exists.mp isDecoded
    have same := (proofExpression_iff formal (payload source) expression).mp decoded
    change ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature formal
      certificate.declaration.hypotheses ((MM0ConstraintParameters.action formal).apply certificate.assignment (payload source))
    rw [same, MM0ConstraintParameters.proof_value_fixed_of_context formed expression certificate.assignment]
    exact valid_proof (.hypothesis (decoded_hypothesis_retained formal payload sourcePresent decoded))

/-- Later use instantiates the extracted formal-context derivation and cuts
the retained hypotheses. No source schedule is executed by this theorem. -/
theorem instantiate_and_cut (wellFormed : theory.WellFormed)
    (formed : Context.WellFormed theory.sortSignature formal)
    {target : Context} {arguments movedHypotheses ambient : List Preterm} {movedConclusion : Preterm}
    (admitted : Substitution.Admissible theory.termSignature formal target arguments)
    (hypothesesMoved : List.Forall₂ (Preterm.Substitutes (Substitution.ofList arguments))
      certificate.declaration.hypotheses movedHypotheses)
    (conclusionMoved : Preterm.Substitutes (Substitution.ofList arguments) certificate.conclusion movedConclusion)
    (supplied : ∀ hypothesis ∈ movedHypotheses,
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature target ambient hypothesis) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target ambient movedConclusion :=
  (admitted.derives hypothesesMoved (certificate.justified wellFormed formed) conclusionMoved).replaceHypotheses supplied

end Certificate
end Mettapedia.Logic.TierZero.Adequacy.MM0SymbolicExport
