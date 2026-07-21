import Mettapedia.GSLT.Parsing.HornSemanticPlan

/-!
# End-to-end semantic adequacy for admitted Horn parser plans

`SemanticLinearCompilation` is the certificate-independent meaning of one
normalized parser rule.  This module closes the recursive layer: it defines
whole-parse derivations whose every applied rule has that meaning, proves them
equivalent to the normalized source presentation constructed from a finite
candidate set with checked semantic coverage, and composes the equivalence
with the packed chart and backend theorems.

Certificates and linearization fuel therefore remain existential evidence for
an admitted rule.  They do not become a second parsing semantics.
-/

namespace Mettapedia.GSLT.Parsing.HornSemanticAdequacy

open CompilerCorrespondence GuardCorrespondence PackedForest GroundedChart
open BackendCorrespondence HornCertificate HornPlan HornRequestDiscovery
open HornSemanticPlan

mutual
  /-- Certificate-independent evaluation of an exact input span using only
  admitted, semantically compilable Horn specializations. -/
  inductive SemanticDerivesAt (program : Program) (parseRelation : String)
      (admittedRule : NormalizedRule → Prop) (fullInput : List Codepoint) :
      Category → Nat → Nat → ParseTree → Prop where
    | apply (rule : NormalizedRule)
        (admitted : admittedRule rule)
        (semantic : SemanticallyCompilableRule program parseRelation rule)
        (body : SemanticBodyDerivesAt program parseRelation admittedRule
          fullInput rule.symbols start stop children) :
        SemanticDerivesAt program parseRelation admittedRule fullInput
          rule.category start stop
          (.node rule.sourceRule rule.category children)

  /-- Left-to-right semantic evaluation with exact cursor composition. -/
  inductive SemanticBodyDerivesAt (program : Program) (parseRelation : String)
      (admittedRule : NormalizedRule → Prop) (fullInput : List Codepoint) :
      List SourceSymbol → Nat → Nat → List ParseTree → Prop where
    | nil : SemanticBodyDerivesAt program parseRelation admittedRule fullInput
        [] cursor cursor []
    | exact
        (lookup : fullInput[start]? = some codepoint)
        (rest : SemanticBodyDerivesAt program parseRelation admittedRule
          fullInput symbols (start + 1) stop children) :
        SemanticBodyDerivesAt program parseRelation admittedRule fullInput
          (.exact codepoint :: symbols) start stop
          (.terminal codepoint :: children)
    | any
        (lookup : fullInput[start]? = some codepoint)
        (rest : SemanticBodyDerivesAt program parseRelation admittedRule
          fullInput symbols (start + 1) stop children) :
        SemanticBodyDerivesAt program parseRelation admittedRule fullInput
          (.any :: symbols) start stop (.terminal codepoint :: children)
    | call
        (head : SemanticDerivesAt program parseRelation admittedRule fullInput
          category start middle tree)
        (rest : SemanticBodyDerivesAt program parseRelation admittedRule
          fullInput symbols middle stop children) :
        SemanticBodyDerivesAt program parseRelation admittedRule fullInput
          (.call category :: symbols) start stop (tree :: children)
end

theorem semanticallyCompilableRule_guards_empty
    {program : Program} {parseRelation : String} {rule : NormalizedRule}
    (semantic : SemanticallyCompilableRule program parseRelation rule) :
    rule.guards = [] := by
  obtain ⟨source, substitution, categories, production, symbols,
    semanticLinear, ruleEq⟩ := semantic
  subst rule
  rfl

mutual
  private def preserveDerivation
      {program : Program} {parseRelation : String}
      {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
      (coverage : SemanticCandidateCoverage program parseRelation admittedRule
        candidates)
      (startCategory : Category)
      {fullInput category start stop tree}
      (derivation : SemanticDerivesAt program parseRelation admittedRule
        fullInput category start stop tree) :
      SourceDerivesAt
        (discoveredPresentation program parseRelation startCategory candidates)
        fullInput category start stop tree :=
    match derivation with
    | .apply rule admitted semantic body => by
        have member : rule ∈ discoveredRules program parseRelation candidates :=
          (discoveredRules_iff_admittedSemantic program parseRelation
            admittedRule candidates coverage rule).2 ⟨admitted, semantic⟩
        have sourceBody := preserveBody coverage startCategory body
        have guardsEmpty := semanticallyCompilableRule_guards_empty semantic
        apply SourceDerivesAt.apply rule
        · simpa [discoveredPresentation] using member
        · exact sourceBody
        · rw [guardsEmpty]
          exact .nil

  private def preserveBody
      {program : Program} {parseRelation : String}
      {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
      (coverage : SemanticCandidateCoverage program parseRelation admittedRule
        candidates)
      (startCategory : Category)
      {fullInput symbols start stop children}
      (derivation : SemanticBodyDerivesAt program parseRelation admittedRule
        fullInput symbols start stop children) :
      SourceBodyDerivesAt
        (discoveredPresentation program parseRelation startCategory candidates)
        fullInput symbols start stop children :=
    match derivation with
    | .nil => .nil
    | .exact lookup rest =>
        .exact lookup (preserveBody coverage startCategory rest)
    | .any lookup rest =>
        .any lookup (preserveBody coverage startCategory rest)
    | .call head rest =>
        .call (preserveDerivation coverage startCategory head)
          (preserveBody coverage startCategory rest)
end

mutual
  private def reflectDerivation
      {program : Program} {parseRelation : String}
      {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
      (coverage : SemanticCandidateCoverage program parseRelation admittedRule
        candidates)
      (startCategory : Category)
      {fullInput category start stop tree}
      (derivation : SourceDerivesAt
        (discoveredPresentation program parseRelation startCategory candidates)
        fullInput category start stop tree) :
      SemanticDerivesAt program parseRelation admittedRule fullInput
        category start stop tree :=
    match derivation with
    | .apply rule member body guards => by
        have ruleMember :
            rule ∈ discoveredRules program parseRelation candidates := by
          simpa [discoveredPresentation] using member
        obtain ⟨admitted, semantic⟩ :=
          (discoveredRules_iff_admittedSemantic program parseRelation
            admittedRule candidates coverage rule).1 ruleMember
        exact .apply rule admitted semantic
          (reflectBody coverage startCategory body)

  private def reflectBody
      {program : Program} {parseRelation : String}
      {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
      (coverage : SemanticCandidateCoverage program parseRelation admittedRule
        candidates)
      (startCategory : Category)
      {fullInput symbols start stop children}
      (derivation : SourceBodyDerivesAt
        (discoveredPresentation program parseRelation startCategory candidates)
        fullInput symbols start stop children) :
      SemanticBodyDerivesAt program parseRelation admittedRule fullInput
        symbols start stop children :=
    match derivation with
    | .nil => .nil
    | .exact lookup rest =>
        .exact lookup (reflectBody coverage startCategory rest)
    | .any lookup rest =>
        .any lookup (reflectBody coverage startCategory rest)
    | .call head rest =>
        .call (reflectDerivation coverage startCategory head)
          (reflectBody coverage startCategory rest)
end

theorem source_iff_semantic
    {program : Program} {parseRelation : String}
    {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
    (coverage : SemanticCandidateCoverage program parseRelation admittedRule
      candidates)
    (startCategory : Category) (fullInput : List Codepoint)
    (category : Category) (start stop : Nat) (tree : ParseTree) :
    SourceDerivesAt
        (discoveredPresentation program parseRelation startCategory candidates)
        fullInput category start stop tree ↔
      SemanticDerivesAt program parseRelation admittedRule fullInput
        category start stop tree := by
  constructor
  · exact reflectDerivation coverage startCategory
  · exact preserveDerivation coverage startCategory

def semanticResults (program : Program) (parseRelation : String)
    (admittedRule : NormalizedRule → Prop) (startCategory : Category)
    (input : List Codepoint) : Set ParseTree :=
  { tree | SemanticDerivesAt program parseRelation admittedRule input
      startCategory 0 input.length tree }

theorem source_semantic_result_set_agreement
    {program : Program} {parseRelation : String}
    {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
    (coverage : SemanticCandidateCoverage program parseRelation admittedRule
      candidates)
    (startCategory : Category) (input : List Codepoint) :
    sourceResults
        (discoveredPresentation program parseRelation startCategory candidates)
        input =
      semanticResults program parseRelation admittedRule startCategory input := by
  ext tree
  exact source_iff_semantic coverage startCategory input startCategory 0
    input.length tree

/-- Complete may-set preservation and reflection from certificate-independent
Horn semantics through the compiled chart forest. -/
theorem chart_semantic_result_set_agreement
    {program : Program} {parseRelation : String}
    {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
    (coverage : SemanticCandidateCoverage program parseRelation admittedRule
      candidates)
    (startCategory : Category) (input : List Codepoint) :
    packedResults
        (chartForest
          (compile
            (discoveredPresentation program parseRelation startCategory
              candidates))
          input)
        (discoveredPresentation program parseRelation startCategory candidates)
        input =
      semanticResults program parseRelation admittedRule startCategory input := by
  rw [discoveredPlan_chart_result_set_agreement]
  exact source_semantic_result_set_agreement coverage startCategory input

/-- Any packed backend proved to cover the root-reachable chart has the same
complete semantic may-set. -/
theorem backend_semantic_result_set_agreement
    {program : Program} {parseRelation : String}
    {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
    (coverage : SemanticCandidateCoverage program parseRelation admittedRule
      candidates)
    (startCategory : Category) (input : List Codepoint) (backend : Forest)
    (covers : ForestCovers
      (rootReachableForest
        (chartForest
          (compile
            (discoveredPresentation program parseRelation startCategory
              candidates))
          input))
      backend) :
    packedResults backend
        (discoveredPresentation program parseRelation startCategory candidates)
        input =
      semanticResults program parseRelation admittedRule startCategory input := by
  rw [discoveredPlan_backend_result_set_agreement program parseRelation
    startCategory candidates input backend covers]
  exact source_semantic_result_set_agreement coverage startCategory input

theorem chart_semantic_ambiguity_agreement
    {program : Program} {parseRelation : String}
    {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
    (coverage : SemanticCandidateCoverage program parseRelation admittedRule
      candidates)
    (startCategory : Category) (input : List Codepoint) :
    GuardCorrespondence.Ambiguous
        (packedResults
          (chartForest
            (compile
              (discoveredPresentation program parseRelation startCategory
                candidates))
            input)
          (discoveredPresentation program parseRelation startCategory candidates)
          input) ↔
      GuardCorrespondence.Ambiguous
        (semanticResults program parseRelation admittedRule startCategory input) := by
  rw [chart_semantic_result_set_agreement coverage startCategory input]

/-- A replayed exact-root certificate is sound for the original
certificate-independent Horn semantics, not merely for the compiled grammar. -/
theorem certificate_replay_semantic_sound
    {program : Program} {parseRelation : String}
    {admittedRule : NormalizedRule → Prop} {candidates : List LinearRequest}
    (coverage : SemanticCandidateCoverage program parseRelation admittedRule
      candidates)
    (startCategory : Category) {input certificate tree}
    (replay : RootCertificateReplays
      (discoveredPresentation program parseRelation startCategory candidates)
      input certificate tree) :
    tree ∈ semanticResults program parseRelation admittedRule startCategory input := by
  apply (source_iff_semantic coverage startCategory input startCategory 0
    input.length tree).1
  exact GuardCorrespondence.certificate_replay_sound replay

/-! ## Non-vacuous executable control -/

theorem control_semantic_result_set_contains_tree :
    HornPlan.controlTree ∈
      semanticResults HornSpecialization.exampleProgram "parse"
        HornSemanticPlan.controlRuleDomain "g0" [97] := by
  rw [← source_semantic_result_set_agreement
    controlCandidates_have_semantic_coverage "g0" [97]]
  simpa [controlDiscoveredPresentation_is_controlPresentation] using
    HornPlan.controlTree_mem_sourceResults

end Mettapedia.GSLT.Parsing.HornSemanticAdequacy
