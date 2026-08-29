import Mettapedia.GSLT.Parsing.HornSpecialization
import Mettapedia.GSLT.Parsing.BackendCorrespondence

/-!
# Checked Horn-specialization plans

This module joins the ordinary-Horn specialization checker to the finite
packed-chart correspondence.  A plan is executable data: every requested
source rule carries its specialization certificate and a linearization fuel.
Only requests accepted by `compileLinear` enter the normalized scannerless
presentation.

The result is deliberately narrower than full Horn-specializer adequacy.  It
proves that every rule in an accepted plan came from a checked Horn
specialization and that the complete chart, or any packed backend covering
that chart, has exactly the normalized source result set.  Exhaustiveness of
the request list over every applicable Horn specialization remains a separate
admission obligation.
-/

namespace Mettapedia.GSLT.Parsing.HornPlan

open CompilerCorrespondence GuardCorrespondence HornSpecialization
open PackedForest GroundedChart BackendCorrespondence

abbrev NormalizedRule := GuardCorrespondence.SourceRule
abbrev NormalizedPresentation := GuardCorrespondence.SourceDefinition

structure LinearRequest where
  certificate : SpecializationCertificate
  fuel : Nat
  deriving DecidableEq, Repr

def sourceRuleOf (production : StreamProduction)
    (symbols : List SourceSymbol) : NormalizedRule :=
  { sourceRule := production.sourceRule
    category := production.category
    symbols := symbols
    guards := [] }

def compileRequest (program : HornCertificate.Program) (parseRelation : String)
    (request : LinearRequest) : Option NormalizedRule := do
  let (production, symbols) ←
    compileLinear program parseRelation request.certificate request.fuel
  pure (sourceRuleOf production symbols)

inductive RequestCompiles (program : HornCertificate.Program)
    (parseRelation : String) : LinearRequest → NormalizedRule → Prop where
  | intro (request : LinearRequest) (production : StreamProduction)
      (symbols : List SourceSymbol)
      (accepted : compileLinear program parseRelation request.certificate
        request.fuel = some (production, symbols)) :
      RequestCompiles program parseRelation request
        (sourceRuleOf production symbols)

theorem compileRequest_sound (program : HornCertificate.Program)
    (parseRelation : String) (request : LinearRequest) (rule : NormalizedRule)
    (accepted : compileRequest program parseRelation request = some rule) :
    RequestCompiles program parseRelation request rule := by
  cases compiled : compileLinear program parseRelation request.certificate
      request.fuel with
  | none => simp [compileRequest, compiled] at accepted
  | some result =>
      rcases result with ⟨production, symbols⟩
      simp [compileRequest, compiled] at accepted
      subst rule
      exact .intro request production symbols compiled

theorem compileRequest_complete (program : HornCertificate.Program)
    (parseRelation : String) (request : LinearRequest) (rule : NormalizedRule)
    (derivation : RequestCompiles program parseRelation request rule) :
    compileRequest program parseRelation request = some rule := by
  cases derivation with
  | intro production symbols accepted =>
      simp [compileRequest, accepted]

theorem compileRequest_iff (program : HornCertificate.Program)
    (parseRelation : String) (request : LinearRequest) (rule : NormalizedRule) :
    compileRequest program parseRelation request = some rule ↔
      RequestCompiles program parseRelation request rule :=
  ⟨compileRequest_sound program parseRelation request rule,
    compileRequest_complete program parseRelation request rule⟩

theorem RequestCompiles.functional
    {program : HornCertificate.Program} {parseRelation : String}
    {request : LinearRequest} {left right : NormalizedRule}
    (leftCompiled : RequestCompiles program parseRelation request left)
    (rightCompiled : RequestCompiles program parseRelation request right) :
    left = right := by
  have leftAccepted := compileRequest_complete program parseRelation request left
    leftCompiled
  have rightAccepted := compileRequest_complete program parseRelation request right
    rightCompiled
  rw [leftAccepted] at rightAccepted
  injection rightAccepted

def compileRequests (program : HornCertificate.Program)
    (parseRelation : String) : List LinearRequest → Option (List NormalizedRule)
  | [] => some []
  | request :: requests => do
      let rule ← compileRequest program parseRelation request
      let rules ← compileRequests program parseRelation requests
      pure (rule :: rules)

inductive RequestsCompile (program : HornCertificate.Program)
    (parseRelation : String) : List LinearRequest → List NormalizedRule → Prop where
  | nil : RequestsCompile program parseRelation [] []
  | cons (request : LinearRequest) (requests : List LinearRequest)
      (rule : NormalizedRule) (rules : List NormalizedRule)
      (head : RequestCompiles program parseRelation request rule)
      (tail : RequestsCompile program parseRelation requests rules) :
      RequestsCompile program parseRelation (request :: requests) (rule :: rules)

theorem RequestsCompile.rule_mem
    {program : HornCertificate.Program} {parseRelation : String}
    {requests : List LinearRequest} {rules : List NormalizedRule}
    (compiled : RequestsCompile program parseRelation requests rules)
    {rule : NormalizedRule} (member : rule ∈ rules) :
    ∃ request ∈ requests,
      RequestCompiles program parseRelation request rule := by
  induction compiled with
  | nil => simp at member
  | cons request requests headRule rules head tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨request, by simp, head⟩
      · obtain ⟨source, sourceMember, sourceCompiled⟩ :=
          inductionHypothesis member
        exact ⟨source, by simp [sourceMember], sourceCompiled⟩

theorem RequestsCompile.request_rule_mem
    {program : HornCertificate.Program} {parseRelation : String}
    {requests : List LinearRequest} {rules : List NormalizedRule}
    (compiled : RequestsCompile program parseRelation requests rules)
    {request : LinearRequest} (requestMember : request ∈ requests)
    {rule : NormalizedRule}
    (requestCompiled : RequestCompiles program parseRelation request rule) :
    rule ∈ rules := by
  induction compiled generalizing request rule with
  | nil => simp at requestMember
  | cons headRequest requests headRule rules head tail inductionHypothesis =>
      simp only [List.mem_cons] at requestMember
      rcases requestMember with rfl | requestMember
      · have ruleEq := RequestCompiles.functional requestCompiled head
        simp [ruleEq]
      · exact List.mem_cons_of_mem _
          (inductionHypothesis requestMember requestCompiled)

/-- The finite request list covers every request admitted by the declared
compiler domain.  This is the exact remaining reflection obligation for a
particular admitted Horn presentation. -/
structure RequestsExhaustive (program : HornCertificate.Program)
    (parseRelation : String) (admitted : LinearRequest → Prop)
    (requests : List LinearRequest) : Prop where
  listed : ∀ request, request ∈ requests → admitted request
  covers : ∀ request rule,
    admitted request →
    RequestCompiles program parseRelation request rule →
    ∃ listedRequest ∈ requests,
      RequestCompiles program parseRelation listedRequest rule

theorem RequestsCompile.rules_exact_of_exhaustive
    {program : HornCertificate.Program} {parseRelation : String}
    {requests : List LinearRequest} {rules : List NormalizedRule}
    (compiled : RequestsCompile program parseRelation requests rules)
    (admitted : LinearRequest → Prop)
    (exhaustive : RequestsExhaustive program parseRelation admitted requests)
    (rule : NormalizedRule) :
    rule ∈ rules ↔
      ∃ request, admitted request ∧
        RequestCompiles program parseRelation request rule := by
  constructor
  · intro member
    obtain ⟨request, requestMember, requestCompiled⟩ :=
      compiled.rule_mem member
    exact ⟨request, exhaustive.listed request requestMember, requestCompiled⟩
  · rintro ⟨request, admittedRequest, requestCompiled⟩
    obtain ⟨listedRequest, listedMember, listedCompiled⟩ :=
      exhaustive.covers request rule admittedRequest requestCompiled
    exact compiled.request_rule_mem listedMember listedCompiled

theorem compileRequests_sound (program : HornCertificate.Program)
    (parseRelation : String) (requests : List LinearRequest)
    (rules : List NormalizedRule)
    (accepted : compileRequests program parseRelation requests = some rules) :
    RequestsCompile program parseRelation requests rules := by
  induction requests generalizing rules with
  | nil =>
      simp [compileRequests] at accepted
      subst rules
      exact .nil
  | cons request requests inductionHypothesis =>
      cases headAccepted : compileRequest program parseRelation request with
      | none => simp [compileRequests, headAccepted] at accepted
      | some rule =>
          cases tailAccepted : compileRequests program parseRelation requests with
          | none => simp [compileRequests, headAccepted, tailAccepted] at accepted
          | some tailRules =>
              simp [compileRequests, headAccepted, tailAccepted] at accepted
              subst rules
              exact .cons request requests rule tailRules
                (compileRequest_sound program parseRelation request rule headAccepted)
                (inductionHypothesis tailRules tailAccepted)

theorem compileRequests_exact_of_exhaustive
    (program : HornCertificate.Program) (parseRelation : String)
    (admitted : LinearRequest → Prop) (requests : List LinearRequest)
    (rules : List NormalizedRule)
    (accepted : compileRequests program parseRelation requests = some rules)
    (exhaustive : RequestsExhaustive program parseRelation admitted requests)
    (rule : NormalizedRule) :
    rule ∈ rules ↔
      ∃ request, admitted request ∧
        RequestCompiles program parseRelation request rule :=
  (compileRequests_sound program parseRelation requests rules accepted).rules_exact_of_exhaustive
    admitted exhaustive rule

theorem compileRequests_complete (program : HornCertificate.Program)
    (parseRelation : String) (requests : List LinearRequest)
    (rules : List NormalizedRule)
    (derivation : RequestsCompile program parseRelation requests rules) :
    compileRequests program parseRelation requests = some rules := by
  induction derivation with
  | nil => rfl
  | cons request requests rule rules head tail inductionHypothesis =>
      simp [compileRequests,
        compileRequest_complete program parseRelation request rule head,
        inductionHypothesis]

theorem compileRequests_iff (program : HornCertificate.Program)
    (parseRelation : String) (requests : List LinearRequest)
    (rules : List NormalizedRule) :
    compileRequests program parseRelation requests = some rules ↔
      RequestsCompile program parseRelation requests rules :=
  ⟨compileRequests_sound program parseRelation requests rules,
    compileRequests_complete program parseRelation requests rules⟩

def compilePresentation (program : HornCertificate.Program)
    (parseRelation : String) (start : Category)
    (requests : List LinearRequest) : Option NormalizedPresentation := do
  let rules ← compileRequests program parseRelation requests
  pure { start := start, rules := rules }

theorem compilePresentation_iff (program : HornCertificate.Program)
    (parseRelation : String) (start : Category)
    (requests : List LinearRequest) (presentation : NormalizedPresentation) :
    compilePresentation program parseRelation start requests = some presentation ↔
      presentation.start = start ∧
        RequestsCompile program parseRelation requests presentation.rules := by
  cases presentation with
  | mk actualStart actualRules =>
      cases rulesAccepted : compileRequests program parseRelation requests with
      | none =>
          constructor
          · intro accepted
            simp [compilePresentation, rulesAccepted] at accepted
          · rintro ⟨_, compiled⟩
            have complete := compileRequests_complete program parseRelation
              requests actualRules compiled
            rw [rulesAccepted] at complete
            contradiction
      | some rules =>
          constructor
          · intro accepted
            simp [compilePresentation, rulesAccepted] at accepted
            obtain ⟨rfl, rfl⟩ := accepted
            exact ⟨rfl,
              compileRequests_sound program parseRelation requests rules
                rulesAccepted⟩
          · rintro ⟨startEq, compiled⟩
            have complete := compileRequests_complete program parseRelation
              requests actualRules compiled
            rw [rulesAccepted] at complete
            injection complete with rulesEq
            simp [compilePresentation, rulesAccepted, ← startEq, rulesEq]

theorem acceptedPlan_chart_result_set_agreement
    (program : HornCertificate.Program) (parseRelation : String)
    (start : Category) (requests : List LinearRequest)
    (presentation : NormalizedPresentation)
    (accepted :
      compilePresentation program parseRelation start requests = some presentation)
    (input : List Codepoint) :
    RequestsCompile program parseRelation requests presentation.rules ∧
      packedResults
          (chartForest (GuardCorrespondence.compile presentation) input)
          presentation input =
        GuardCorrespondence.sourceResults presentation input := by
  have plan :=
    (compilePresentation_iff program parseRelation start requests presentation).mp
      accepted
  exact ⟨plan.2, GroundedChart.chartForest_result_set_agreement presentation input⟩

theorem acceptedPlan_backend_result_set_agreement
    (program : HornCertificate.Program) (parseRelation : String)
    (start : Category) (requests : List LinearRequest)
    (presentation : NormalizedPresentation) (input : List Codepoint)
    (backend : Forest)
    (accepted :
      compilePresentation program parseRelation start requests = some presentation)
    (covers : ForestCovers
      (rootReachableForest
        (chartForest (GuardCorrespondence.compile presentation) input))
      backend) :
    RequestsCompile program parseRelation requests presentation.rules ∧
      packedResults backend presentation input =
        GuardCorrespondence.sourceResults presentation input := by
  have plan :=
    (compilePresentation_iff program parseRelation start requests presentation).mp
      accepted
  exact ⟨plan.2,
    BackendCorrespondence.backend_result_set_agreement covers⟩

/-! ## Executable positive and negative controls -/

def controlRequest : LinearRequest :=
  { certificate := HornSpecialization.charCertificate, fuel := 2 }

def controlRule : NormalizedRule :=
  sourceRuleOf HornSpecialization.charProduction [.exact 97]

def controlPresentation : NormalizedPresentation :=
  { start := "g0", rules := [controlRule] }

theorem controlPlan_accepts :
    compilePresentation HornSpecialization.exampleProgram "parse" "g0"
      [controlRequest] = some controlPresentation := by
  decide

theorem controlPlan_has_checked_rule :
    RequestsCompile HornSpecialization.exampleProgram "parse" [controlRequest]
      controlPresentation.rules :=
  (compilePresentation_iff HornSpecialization.exampleProgram "parse" "g0"
    [controlRequest] controlPresentation).mp controlPlan_accepts |>.2

def controlAdmitted (request : LinearRequest) : Prop :=
  request = controlRequest

theorem controlRequestsExhaustive :
    RequestsExhaustive HornSpecialization.exampleProgram "parse"
      controlAdmitted [controlRequest] := by
  constructor
  · intro request member
    simpa [controlAdmitted] using member
  · intro request rule admitted requestCompiled
    subst request
    exact ⟨controlRequest, by simp, requestCompiled⟩

theorem controlRequests_accept :
    compileRequests HornSpecialization.exampleProgram "parse" [controlRequest] =
      some [controlRule] := by
  decide

theorem controlRules_exact (rule : NormalizedRule) :
    rule ∈ [controlRule] ↔
      ∃ request, controlAdmitted request ∧
        RequestCompiles HornSpecialization.exampleProgram "parse" request rule :=
  compileRequests_exact_of_exhaustive HornSpecialization.exampleProgram "parse"
    controlAdmitted [controlRequest] [controlRule] controlRequests_accept
      controlRequestsExhaustive rule

def controlTree : ParseTree :=
  .node "parse-char" "g0" [.terminal 97]

theorem controlSourceDerives :
    SourceDerivesAt controlPresentation [97] "g0" 0 1 controlTree := by
  apply SourceDerivesAt.apply controlRule
  · simp [controlPresentation]
  · apply SourceBodyDerivesAt.exact
    · rfl
    · exact .nil
  · exact .nil

theorem controlTree_mem_sourceResults :
    controlTree ∈ GuardCorrespondence.sourceResults controlPresentation [97] :=
  controlSourceDerives

theorem controlTree_mem_chartResults :
    controlTree ∈
      packedResults
        (chartForest (GuardCorrespondence.compile controlPresentation) [97])
        controlPresentation [97] := by
  rw [GroundedChart.chartForest_result_set_agreement]
  exact controlTree_mem_sourceResults

def mutatedRequest : LinearRequest :=
  { certificate := HornSpecialization.mutatedRuleCertificate, fuel := 2 }

theorem mutatedPlan_rejects :
    compilePresentation HornSpecialization.exampleProgram "parse" "g0"
      [mutatedRequest] = none := by
  decide

end Mettapedia.GSLT.Parsing.HornPlan
