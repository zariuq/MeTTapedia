import Mettapedia.GSLT.Parsing.HornRequestDiscovery
import Mettapedia.GSLT.Parsing.HornSpecializationBody

/-!
# Semantic meaning of normalized Horn parser rules

Operational `LinearRequest` values carry side certificates and search fuel.
Neither belongs to the meaning of the compiled grammar.  This module proves
that existence of a checked request is exactly certificate-independent Horn
specialization followed by declarative stream-path linearization.
-/

namespace Mettapedia.GSLT.Parsing.HornSemanticPlan

open CompilerCorrespondence HornCertificate HornSpecialization
open HornSpecializationBody HornPlan
open HornRequestDiscovery

def SemanticallyCompilableRule (program : Program) (parseRelation : String)
    (normalized : NormalizedRule) : Prop :=
  ∃ rule substitution categories production symbols,
    SemanticLinearCompilation program parseRelation rule substitution categories
      production symbols ∧
    normalized = sourceRuleOf production symbols

theorem requestCompiles_semantically
    {program : Program} {parseRelation : String}
    {request : LinearRequest} {normalized : NormalizedRule}
  (compiled : RequestCompiles program parseRelation request normalized) :
    SemanticallyCompilableRule program parseRelation normalized := by
  cases compiled with
  | intro production symbols accepted =>
      refine ⟨request.certificate.rule, request.certificate.substitution,
        request.certificate.categories, production, symbols, ?_, rfl⟩
      rw [semanticLinearCompilation_iff_exists_certificate]
      exact ⟨request.certificate.sides, request.fuel, accepted⟩

theorem semanticRule_has_checkedRequest
    {program : Program} {parseRelation : String}
    {normalized : NormalizedRule}
    (semantic : SemanticallyCompilableRule program parseRelation normalized) :
    ∃ request : LinearRequest,
      RequestCompiles program parseRelation request normalized := by
  obtain ⟨rule, substitution, categories, production, symbols,
    semanticLinear, normalizedEq⟩ := semantic
  obtain ⟨sides, fuel, accepted⟩ :=
    (semanticLinearCompilation_iff_exists_certificate program parseRelation
      rule substitution categories production symbols).mp semanticLinear
  let request : LinearRequest :=
    { certificate := { rule, substitution, categories, sides }
      fuel := fuel }
  refine ⟨request, ?_⟩
  subst normalized
  exact .intro request production symbols accepted

theorem exists_requestCompiles_iff_semanticallyCompilable
    (program : Program) (parseRelation : String) (normalized : NormalizedRule) :
    (∃ request : LinearRequest,
      RequestCompiles program parseRelation request normalized) ↔
      SemanticallyCompilableRule program parseRelation normalized := by
  constructor
  · rintro ⟨request, compiled⟩
    exact requestCompiles_semantically compiled
  · exact semanticRule_has_checkedRequest

/-- A finite candidate universe covers the root-reachable semantic rule
domain.  `eligible` prevents an overgenerated but valid request from escaping
the declared domain; `covers` prevents a semantically valid admitted rule
from being missed. -/
structure SemanticCandidateCoverage (program : Program) (parseRelation : String)
    (admittedRule : NormalizedRule → Prop)
    (candidates : List LinearRequest) : Prop where
  eligible : ∀ request, request ∈ candidates → ∀ normalized,
    RequestCompiles program parseRelation request normalized →
      admittedRule normalized
  covers : ∀ normalized,
    admittedRule normalized →
    SemanticallyCompilableRule program parseRelation normalized →
    ∃ request ∈ candidates,
      RequestCompiles program parseRelation request normalized

/-- Membership in the recorded output of one finite compiler run.  This is
list bookkeeping, not a definition of semantic admission. -/
def ListedRule (expected : List NormalizedRule)
    (normalized : NormalizedRule) : Prop :=
  normalized ∈ expected

/-- Exact output of one finite compiler run.  It does not establish that the
finite candidates cover every semantically compilable rule. -/
structure ExactCompilationManifest (program : Program) (parseRelation : String)
    (expected : List NormalizedRule) (candidates : List LinearRequest) : Prop where
  exact : discoveredRules program parseRelation candidates = expected

theorem ExactCompilationManifest.listedCandidateCoverage
    {program : Program} {parseRelation : String}
    {expected : List NormalizedRule} {candidates : List LinearRequest}
    (manifest : ExactCompilationManifest program parseRelation expected candidates) :
    SemanticCandidateCoverage program parseRelation (ListedRule expected)
      candidates := by
  constructor
  · intro request requestMember normalized compiled
    have accepted := compileRequest_complete program parseRelation request
      normalized compiled
    have discovered :
        normalized ∈ discoveredRules program parseRelation candidates :=
      (mem_discoveredRules_iff program parseRelation candidates normalized).2
        ⟨request, requestMember, accepted⟩
    simpa [ListedRule, manifest.exact] using discovered
  · intro normalized admitted _semantic
    have discovered :
        normalized ∈ discoveredRules program parseRelation candidates := by
      simpa [ListedRule, manifest.exact] using admitted
    obtain ⟨request, requestMember, accepted⟩ :=
      (mem_discoveredRules_iff program parseRelation candidates normalized).1
        discovered
    exact ⟨request, requestMember,
      compileRequest_sound program parseRelation request normalized accepted⟩

theorem ExactCompilationManifest.listed_iff_discovered
    {program : Program} {parseRelation : String}
    {expected : List NormalizedRule} {candidates : List LinearRequest}
    (manifest : ExactCompilationManifest program parseRelation expected candidates)
    (normalized : NormalizedRule) :
    ListedRule expected normalized ↔
      normalized ∈ discoveredRules program parseRelation candidates := by
  simp only [ListedRule, manifest.exact]

theorem ExactCompilationManifest.listed_semanticallyCompilable
    {program : Program} {parseRelation : String}
    {expected : List NormalizedRule} {candidates : List LinearRequest}
    (manifest : ExactCompilationManifest program parseRelation expected candidates)
    {normalized : NormalizedRule} (listed : ListedRule expected normalized) :
    SemanticallyCompilableRule program parseRelation normalized := by
  have discovered :
      normalized ∈ discoveredRules program parseRelation candidates :=
    (manifest.listed_iff_discovered normalized).mp listed
  obtain ⟨request, _requestMember, accepted⟩ :=
    (mem_discoveredRules_iff program parseRelation candidates normalized).mp
      discovered
  exact requestCompiles_semantically
    (compileRequest_sound program parseRelation request normalized accepted)

/-- The proof obligation that upgrades finite discovery from a compiler-output
manifest to a complete characterization of semantic compilability. -/
structure SemanticCompleteness (program : Program) (parseRelation : String)
    (candidates : List LinearRequest) : Prop where
  covers : ∀ normalized,
    SemanticallyCompilableRule program parseRelation normalized →
    ∃ request ∈ candidates,
      RequestCompiles program parseRelation request normalized

theorem discoveredRules_iff_semanticallyCompilable
    (program : Program) (parseRelation : String)
    (candidates : List LinearRequest)
    (complete : SemanticCompleteness program parseRelation candidates)
    (normalized : NormalizedRule) :
    normalized ∈ discoveredRules program parseRelation candidates ↔
      SemanticallyCompilableRule program parseRelation normalized := by
  constructor
  · intro discovered
    obtain ⟨request, _requestMember, accepted⟩ :=
      (mem_discoveredRules_iff program parseRelation candidates normalized).mp
        discovered
    exact requestCompiles_semantically
      (compileRequest_sound program parseRelation request normalized accepted)
  · intro semantic
    obtain ⟨request, requestMember, compiled⟩ := complete.covers normalized semantic
    exact (mem_discoveredRules_iff program parseRelation candidates normalized).mpr
      ⟨request, requestMember,
        compileRequest_complete program parseRelation request normalized compiled⟩

theorem discoveredRules_iff_admittedSemantic
    (program : Program) (parseRelation : String)
    (admittedRule : NormalizedRule → Prop) (candidates : List LinearRequest)
    (coverage : SemanticCandidateCoverage program parseRelation admittedRule
      candidates)
    (normalized : NormalizedRule) :
    normalized ∈ discoveredRules program parseRelation candidates ↔
      admittedRule normalized ∧
        SemanticallyCompilableRule program parseRelation normalized := by
  constructor
  · intro member
    obtain ⟨request, requestMember, accepted⟩ :=
      (mem_discoveredRules_iff program parseRelation candidates normalized).mp
        member
    have compiled := compileRequest_sound program parseRelation request normalized
      accepted
    exact ⟨coverage.eligible request requestMember normalized compiled,
      requestCompiles_semantically compiled⟩
  · rintro ⟨admitted, semantic⟩
    obtain ⟨request, requestMember, compiled⟩ :=
      coverage.covers normalized admitted semantic
    exact (mem_discoveredRules_iff program parseRelation candidates normalized).2
      ⟨request, requestMember,
        compileRequest_complete program parseRelation request normalized compiled⟩

theorem controlRule_is_semanticallyCompilable :
    SemanticallyCompilableRule exampleProgram "parse" controlRule := by
  exact requestCompiles_semantically
    (compileRequest_sound exampleProgram "parse" controlRequest controlRule
      (by decide))

def controlRuleDomain (normalized : NormalizedRule) : Prop :=
  normalized = controlRule

theorem controlCandidates_have_semantic_coverage :
    SemanticCandidateCoverage exampleProgram "parse" controlRuleDomain
      HornRequestDiscovery.controlCandidates := by
  constructor
  · intro request requestMember normalized compiled
    simp [HornRequestDiscovery.controlCandidates] at requestMember
    rcases requestMember with rfl | rfl
    · have functional := RequestCompiles.functional compiled
        (compileRequest_sound exampleProgram "parse" controlRequest controlRule
          (by decide))
      exact functional
    · have rejected : compileRequest exampleProgram "parse" mutatedRequest = none :=
        by decide
      have accepted := compileRequest_complete exampleProgram "parse"
        mutatedRequest normalized compiled
      rw [rejected] at accepted
      contradiction
  · intro normalized admitted semantic
    subst normalized
    exact ⟨controlRequest,
      by simp [HornRequestDiscovery.controlCandidates],
      compileRequest_sound exampleProgram "parse" controlRequest controlRule
        (by decide)⟩

def controlExpectedRules : List NormalizedRule := [controlRule]

theorem controlCompilationManifest_is_exact :
    ExactCompilationManifest exampleProgram "parse" controlExpectedRules
      HornRequestDiscovery.controlCandidates := by
  constructor
  decide

theorem controlManifest_has_listed_candidate_coverage :
    SemanticCandidateCoverage exampleProgram "parse"
      (ListedRule controlExpectedRules)
      HornRequestDiscovery.controlCandidates :=
  controlCompilationManifest_is_exact.listedCandidateCoverage

theorem controlDiscoveredRules_are_exactly_admittedSemantic
    (normalized : NormalizedRule) :
    normalized ∈ discoveredRules exampleProgram "parse"
        HornRequestDiscovery.controlCandidates ↔
      controlRuleDomain normalized ∧
        SemanticallyCompilableRule exampleProgram "parse" normalized :=
  discoveredRules_iff_admittedSemantic exampleProgram "parse" controlRuleDomain
    HornRequestDiscovery.controlCandidates controlCandidates_have_semantic_coverage
    normalized

def uncompilableNormalizedRule : NormalizedRule :=
  { controlRule with sourceRule := "not-compilable" }

theorem uncompilableNormalizedRule_is_not_semanticallyCompilable :
    ¬ SemanticallyCompilableRule exampleProgram "parse"
      uncompilableNormalizedRule := by
  rintro ⟨rule, substitution, categories, production, symbols,
    semanticLinear, normalizedEq⟩
  have sourceRuleEq : production.sourceRule = rule.name := by
    cases semanticLinear.specialization with
    | intro head body parsedHead member substitutionValid categoriesValid
        instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
        category start finish => exact sourceRule
  have admittedName : rule.name = "parse-char" ∨
      rule.name = "parse-class" ∨ rule.name = "member-digit-97" := by
    have member : rule ∈ exampleProgram := by
      cases semanticLinear.specialization with
      | intro head body parsedHead member substitutionValid categoriesValid
          instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
          category start finish => exact member
    simp [exampleProgram] at member
    rcases member with rfl | rfl | rfl <;>
      simp [parseCharRule, parseClassRule, memberDigitRule]
  have normalizedSource : production.sourceRule = "not-compilable" := by
    have := congrArg (fun normalized : NormalizedRule => normalized.sourceRule)
      normalizedEq
    simpa [uncompilableNormalizedRule, controlRule, sourceRuleOf] using this.symm
  rw [sourceRuleEq] at normalizedSource
  rcases admittedName with name | name | name <;> simp [name] at normalizedSource

end Mettapedia.GSLT.Parsing.HornSemanticPlan
