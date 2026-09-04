import Mettapedia.Languages.Metamath.MM2VerifierProgram
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSchemaSafety

/-!
# Executable origin for the complete Metamath verifier

The proof-independent verifier transformation contains active rules and
dormant rules stored inside carrier rows.  Its authority inventory must cover
both.  This module derives one fixed recursive inventory from the compiler
output and proves that compatible matching cannot introduce a value outside
that inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2VerifierExecutableOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.MM2VerifierProgram
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- The complete executable authority emitted by the single fixed verifier
transformation, including directives nested inside data carriers. -/
def verifierExecutableRawFacts : List RawExecFact :=
  ((genericVerifierProgram authoredMetamathVerifierGSLT).flatMap
    rawExecSubterms).dedup

/-- Atom-local authorization against the fixed verifier inventory. -/
def VerifierExecutableAtomAuthorized (atom : Atom) : Prop :=
  ExecutableSubtermsWithin verifierExecutableRawFacts atom

/-- Atom-local authorization that permits source-owned substitutions of the
fixed verifier schemas while retaining the compiler's executable structure. -/
def VerifierExecutableSchemaAuthorized (atom : Atom) : Prop :=
  ExecutableSubtermsFromSchemas verifierExecutableRawFacts atom

theorem verifierExecutableRawFacts_nodup :
    verifierExecutableRawFacts.Nodup := by
  exact List.nodup_dedup _

/-- Every atom emitted by the proof-independent verifier transformation is
authorized by the complete compiler-derived inventory. -/
theorem genericVerifierProgram_executable_authorized :
    AtomsWithin VerifierExecutableAtomAuthorized
      (genericVerifierProgram authoredMetamathVerifierGSLT) := by
  intro atom atomMember raw rawMember
  simp only [verifierExecutableRawFacts, List.mem_dedup,
    List.mem_flatMap]
  exact ⟨atom, atomMember, rawMember⟩

/-- Every initial verifier atom is schema-authorized.  At the initial state,
every schema instance is the fixed directive itself; later firings may carry
only source-owned substitutions of these same schemas. -/
theorem genericVerifierProgram_executable_schemaAuthorized :
    AtomsWithin VerifierExecutableSchemaAuthorized
      (genericVerifierProgram authoredMetamathVerifierGSLT) := by
  intro atom atomMember raw rawMember
  exact rawExecFact_member_is_schema_instance
    (genericVerifierProgram_executable_authorized atom atomMember raw rawMember)

/-- Every directive selected from the fixed verifier inventory retains the
complete authorization of the compiler atom that carried it. -/
theorem verifierExecutableRawFact_authorized
    {raw : RawExecFact} (member : raw ∈ verifierExecutableRawFacts) :
    VerifierExecutableAtomAuthorized raw.atom := by
  simp only [verifierExecutableRawFacts, List.mem_dedup,
    List.mem_flatMap] at member
  obtain ⟨carrier, carrierMember, rawMember⟩ := member
  exact executableSubtermsWithin_rawExecFact
    (genericVerifierProgram_executable_authorized carrier carrierMember)
    rawMember

/-- The verifier executable-origin predicate is hereditary through arbitrary
expression nesting. -/
theorem verifierExecutableAtomAuthorized_hereditary :
    AtomPropertyHereditary VerifierExecutableAtomAuthorized := by
  exact executableSubtermsWithin_hereditary verifierExecutableRawFacts

/-- Schema-derived verifier authorization descends through arbitrary
expression nesting. -/
theorem verifierExecutableSchemaAuthorized_hereditary :
    AtomPropertyHereditary VerifierExecutableSchemaAuthorized := by
  exact executableSubtermsFromSchemas_hereditary verifierExecutableRawFacts

/-- Every value bound by a compatible positive match over the complete fixed
verifier program inherits executable authority from that program. -/
theorem genericVerifierProgram_match_values_authorized
    (pattern : Pattern) {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec []
        (genericVerifierProgram authoredMetamathVerifierGSLT)
        (.compat pattern)).map Prod.fst) :
    SubstitutionValuesWithin VerifierExecutableAtomAuthorized substitution := by
  exact cmatchInputSpec_compat_substitutionValuesWithin
    VerifierExecutableAtomAuthorized
    verifierExecutableAtomAuthorized_hereditary
    (genericVerifierProgram authoredMetamathVerifierGSLT)
    genericVerifierProgram_executable_authorized pattern member

/-- Compatible matches over the initial verifier program carry values whose
every executable subterm is a fixed-schema instance. -/
theorem genericVerifierProgram_match_values_schemaAuthorized
    (pattern : Pattern) {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec []
        (genericVerifierProgram authoredMetamathVerifierGSLT)
        (.compat pattern)).map Prod.fst) :
    SubstitutionValuesWithin VerifierExecutableSchemaAuthorized substitution := by
  exact cmatchInputSpec_compat_substitutionValuesWithin
    VerifierExecutableSchemaAuthorized
    verifierExecutableSchemaAuthorized_hereditary
    (genericVerifierProgram authoredMetamathVerifierGSLT)
    genericVerifierProgram_executable_schemaAuthorized pattern member

/-- Recursive authorization also supplies the existing root-level executable
authority judgment. -/
theorem verifierExecutableAtomAuthorized_implies_root_authorized
    {atom : Atom} (authorized : VerifierExecutableAtomAuthorized atom) :
    RawExecAtomWithin verifierExecutableRawFacts atom := by
  exact executableSubtermsWithin_implies_rawExecAtomWithin authorized

/-! ## Hostile boundary -/

/-- Any directive proved absent from the fixed compiler output remains
unauthorized even when hidden below an inert carrier. -/
theorem nested_directive_absent_from_verifier_inventory_is_rejected
    {directive : Atom} {raw : RawExecFact}
    (extracted : extractRawExecFact directive = some raw)
    (absent : raw ∉ verifierExecutableRawFacts) (carrier : Atom) :
    ¬ VerifierExecutableAtomAuthorized
      (.expression [carrier, directive]) := by
  exact nested_directive_absent_from_inventory_is_rejected
    extracted absent carrier

section AxiomAudit

#print axioms verifierExecutableRawFacts_nodup
#print axioms verifierExecutableRawFact_authorized
#print axioms genericVerifierProgram_executable_authorized
#print axioms genericVerifierProgram_executable_schemaAuthorized
#print axioms verifierExecutableAtomAuthorized_hereditary
#print axioms verifierExecutableSchemaAuthorized_hereditary
#print axioms genericVerifierProgram_match_values_authorized
#print axioms genericVerifierProgram_match_values_schemaAuthorized
#print axioms verifierExecutableAtomAuthorized_implies_root_authorized
#print axioms nested_directive_absent_from_verifier_inventory_is_rejected

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2VerifierExecutableOrigin
