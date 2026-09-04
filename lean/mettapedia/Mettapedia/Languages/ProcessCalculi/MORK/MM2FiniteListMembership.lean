import Mettapedia.GSLT.Core.FiniteListMembership
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Finite list membership in ordinary MM2

This module realizes the reverse-cursor membership GSLT with ordinary MM2
rules.  Exact hit, explicit end, and one constant-work unequal-head advance
are disjoint scheduled transitions.  The rule inventory is reloaded after an
advance from opaque capture rows, so nested rule variables remain scoped to
the captured rules.

Each destructive transition binds the exact compact-expression row that it
observed before removing it.  This matters when a request contains an opaque
captured expression: rebuilding the enclosing row may change the compact
indices of variables inside that capture even though its logical fields are
unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2FiniteListMembership

open Mettapedia.GSLT
open Mettapedia.GSLT.FiniteListMembership
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Semantic source and OSLF-derived native theory -/

abbrev SemanticState :=
  Mettapedia.GSLT.FiniteListMembership.State Atom

def semanticGSLT : GSLT :=
  Mettapedia.GSLT.FiniteListMembership.gslt Atom

def semanticOSLF :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF semanticGSLT

def semanticNTT (target : SemanticState) :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
    semanticGSLT target

theorem semanticStep_inhabits_target_native_type
    {before after : SemanticState}
    (step : Mettapedia.GSLT.FiniteListMembership.Step before after) :
    semanticOSLF.satisfies before (semanticNTT after).pred := by
  exact
    (satisfies_exactTargetNativeType_iff_step
      semanticGSLT before after).2 step

/-! ## Canonical nested-list representation -/

def nilAtom : Atom :=
  .expression [.symbol "mm-nil"]

def consAtom (head tail : Atom) : Atom :=
  .expression [.symbol "mm-cons", head, tail]

def encodedListAtom : List Atom → Atom
  | [] => nilAtom
  | head :: tail => consAtom head (encodedListAtom tail)

def decodeEncodedListAtom : Atom → Option (List Atom)
  | .expression [.symbol "mm-nil"] => some []
  | .expression [.symbol "mm-cons", head, tail] => do
      let decodedTail <- decodeEncodedListAtom tail
      pure (head :: decodedTail)
  | _ => none
termination_by atom => atom

@[simp] theorem decodeEncodedListAtom_encodedListAtom (items : List Atom) :
    decodeEncodedListAtom (encodedListAtom items) = some items := by
  induction items with
  | nil =>
      simp [encodedListAtom, nilAtom, decodeEncodedListAtom]
  | cons head tail induction =>
      simp [encodedListAtom, consAtom, decodeEncodedListAtom, induction]

theorem encodedListAtom_injective : Function.Injective encodedListAtom := by
  intro left right equal
  have decoded := congrArg decodeEncodedListAtom equal
  simpa using decoded

/-! ## Source-bound request and terminal observations -/

def membershipRequestRawAtom
    (owner request target visitedRev remaining : Atom) : Atom :=
  .expression
    [.symbol "mm-list-membership-request", owner, request, target,
      visitedRev, remaining]

def membershipRequestAtom (owner request target : Atom)
    (visitedRev remaining : List Atom) : Atom :=
  membershipRequestRawAtom owner request target
    (encodedListAtom visitedRev) (encodedListAtom remaining)

def membershipFoundRawAtom
    (owner request target visitedRev remaining : Atom) : Atom :=
  .expression
    [.symbol "mm-list-membership-found", owner, request, target,
      visitedRev, remaining]

def membershipFoundAtom (owner request target : Atom)
    (visitedRev remaining : List Atom) : Atom :=
  membershipFoundRawAtom owner request target
    (encodedListAtom visitedRev) (encodedListAtom remaining)

def membershipMissingRawAtom
    (owner request target visitedRev : Atom) : Atom :=
  .expression
    [.symbol "mm-list-membership-missing", owner, request, target,
      visitedRev]

def membershipMissingAtom (owner request target : Atom)
    (visitedRev : List Atom) : Atom :=
  membershipMissingRawAtom owner request target
    (encodedListAtom visitedRev)

/-- A source-bound return capability delays restoration of the caller's
rules until this exact membership request reaches a terminal observation. -/
def membershipReturnCapabilityRow
    (owner request returnRule returnTrigger : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-list-membership-return", owner, request,
      returnRule, returnTrigger]

/-- A concrete terminal observation determines an exact semantic terminal
state.  No arbitrary inventory or occurrence position is supplied. -/
inductive RepresentsObservation (owner request : Atom) :
    SemanticState → Atom → Prop where
  | found (target : Atom) (visitedRev remaining : List Atom) :
      RepresentsObservation owner request
        (.finished target
          (visitedRev.reverse ++ target :: remaining)
          (.found visitedRev.length))
        (membershipFoundAtom owner request target visitedRev remaining)
  | missing (target : Atom) (visitedRev : List Atom) :
      RepresentsObservation owner request
        (.finished target visitedRev.reverse
          (.missing visitedRev.length))
        (membershipMissingAtom owner request target visitedRev)

def SourceBackedObservation : SemanticState → Prop
  | .scanning _ => True
  | .finished target inventory (.found _) => target ∈ inventory
  | .finished _ _ (.missing _) => True

theorem represented_observation_is_source_backed
    {owner request observation : Atom} {state : SemanticState}
    (represented : RepresentsObservation owner request state observation) :
    SourceBackedObservation state := by
  cases represented <;>
    simp [SourceBackedObservation]

/-! ## Authored ordinary-MM2 rules -/

private def location (priority name : String) : Atom :=
  .expression [.symbol priority, .symbol name]

private def hitLocation :=
  location "00" "mm-list-membership-hit"
private def missingLocation :=
  location "01" "mm-list-membership-missing"
private def advanceLocation :=
  location "02" "mm-list-membership-advance"
private def reloadLocation :=
  location "35" "mm-list-membership-reload"

private def nilTemplate : Atom :=
  .expression [.symbol "mm-nil"]

private def consTemplate (head tail : Atom) : Atom :=
  .expression [.symbol "mm-cons", head, tail]

private def selfTemplate (loc : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", loc, .var (stem ++ "-input"),
      .var (stem ++ "-output")]

private def requestTemplate (head tail : Atom) : Atom :=
  .expression
    [.symbol "mm-list-membership-request", .var "membership-owner",
      .var "membership-request", .var "membership-target",
      .var "membership-visited-reverse", consTemplate head tail]

private def emptyRequestTemplate : Atom :=
  .expression
    [.symbol "mm-list-membership-request", .var "membership-owner",
      .var "membership-request", .var "membership-target",
      .var "membership-visited-reverse", nilTemplate]

private def hitRequestTemplate : Atom :=
  requestTemplate (.var "membership-target")
    (.var "membership-remaining")

private def anyRequestTemplate : Atom :=
  requestTemplate (.var "membership-head")
    (.var "membership-remaining")

private def foundTemplate : Atom :=
  .expression
    [.symbol "mm-list-membership-found", .var "membership-owner",
      .var "membership-request", .var "membership-target",
      .var "membership-visited-reverse", .var "membership-remaining"]

private def missingTemplate : Atom :=
  .expression
    [.symbol "mm-list-membership-missing", .var "membership-owner",
      .var "membership-request", .var "membership-target",
      .var "membership-visited-reverse"]

private def nextRequestTemplate : Atom :=
  .expression
    [.symbol "mm-list-membership-request", .var "membership-owner",
      .var "membership-request", .var "membership-target",
      consTemplate (.var "membership-head")
        (.var "membership-visited-reverse"),
      .var "membership-remaining"]

private def returnCapabilityTemplate : Atom :=
  membershipReturnCapabilityRow (.var "membership-owner")
    (.var "membership-request") (.var "membership-return-rule")
    (.var "membership-return-trigger")

private def exactRequestRowTemplate : Atom :=
  .var "membership-exact-request-row"

private def exactReturnCapabilityRowTemplate : Atom :=
  .var "membership-exact-return-capability-row"

private def reloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-list-membership", .var "membership-owner"]

def membershipReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-list-membership", owner]

def membershipReloadCapabilityRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-list-membership-reloader", rule]

private def membershipReloadCapabilityTemplate : Atom :=
  membershipReloadCapabilityRow (.var "membership-reload-rule")

private def sinkAtom : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom =>
      .expression [.symbol "head", .symbol (toString count), atom]
  | .tail count atom =>
      .expression [.symbol "tail", .symbol (toString count), atom]

private def mkRule (loc : Atom) (patterns : List Atom)
    (sinks : List Sink) : Atom :=
  .expression
    [.symbol "exec", loc, .expression (.symbol "," :: patterns),
      .expression (.symbol "O" :: sinks.map sinkAtom)]

private def sourceFactorAtom : SourceFactor → Atom
  | .btm pattern => .expression [.symbol "BTM", pattern]
  | .eqConstraint pattern witness =>
      .expression [.symbol "==", pattern, witness]
  | .neqConstraint pattern witness =>
      .expression [.symbol "!=", pattern, witness]

private def explicitInputAtom (factors : List SourceFactor) : Atom :=
  .expression (.symbol "I" :: factors.map sourceFactorAtom)

private def mkExplicitRule (loc : Atom) (factors : List SourceFactor)
    (sinks : List Sink) : Atom :=
  .expression
    [.symbol "exec", loc, explicitInputAtom factors,
      .expression (.symbol "O" :: sinks.map sinkAtom)]

private def mkDirective (atom loc : Atom) (priority : Nat) (name : String)
    (patterns : List Atom) (sinks : List Sink) : SourceExecFact :=
  { atom
    loc
    rule :=
      { priority
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def hitSelf : Atom := selfTemplate hitLocation "membership-hit"
private def hitFactors : List SourceFactor :=
  [.btm hitSelf,
   .btm hitRequestTemplate,
   .eqConstraint hitRequestTemplate exactRequestRowTemplate,
   .btm returnCapabilityTemplate,
   .eqConstraint returnCapabilityTemplate exactReturnCapabilityRowTemplate]
private def hitSinks : List Sink :=
  [.remove exactRequestRowTemplate,
    .remove exactReturnCapabilityRowTemplate,
    .add foundTemplate, .add (.var "membership-return-rule"),
    .add (.var "membership-return-trigger")]

def membershipHitRule : Atom :=
  mkExplicitRule hitLocation hitFactors hitSinks

def membershipHitDirective : SourceExecFact :=
  { atom := membershipHitRule
    loc := hitLocation
    rule :=
      { priority := 0
        name := "mm-list-membership-hit"
        input := .explicit hitFactors
        guards := []
        tmpl := mkTemplate hitSinks } }

private def missingSelf : Atom :=
  selfTemplate missingLocation "membership-missing"
private def missingFactors : List SourceFactor :=
  [.btm missingSelf,
   .btm emptyRequestTemplate,
   .eqConstraint emptyRequestTemplate exactRequestRowTemplate,
   .btm returnCapabilityTemplate,
   .eqConstraint returnCapabilityTemplate exactReturnCapabilityRowTemplate]
private def missingSinks : List Sink :=
  [.remove exactRequestRowTemplate,
    .remove exactReturnCapabilityRowTemplate,
    .add missingTemplate, .add (.var "membership-return-rule"),
    .add (.var "membership-return-trigger")]

def membershipMissingRule : Atom :=
  mkExplicitRule missingLocation missingFactors missingSinks

def membershipMissingDirective : SourceExecFact :=
  { atom := membershipMissingRule
    loc := missingLocation
    rule :=
      { priority := 1
        name := "mm-list-membership-missing"
        input := .explicit missingFactors
        guards := []
        tmpl := mkTemplate missingSinks } }

private def advanceSelf : Atom :=
  selfTemplate advanceLocation "membership-advance"
/-- Ordered scheduling offers `hit` and `missing` before `advance`.  A terminal
rule removes the exact request row, so the fallback can match any surviving
nonempty request without encoding value disequality as a space query. -/
private def advanceFactors : List SourceFactor :=
  [.btm advanceSelf, .btm membershipReloadCapabilityTemplate,
   .btm anyRequestTemplate,
   .eqConstraint anyRequestTemplate exactRequestRowTemplate]
private def advanceSinks : List Sink :=
  [.add (.var "membership-reload-rule"),
    .remove exactRequestRowTemplate, .add nextRequestTemplate,
    .add reloadTriggerTemplate]

def membershipAdvanceRule : Atom :=
  mkExplicitRule advanceLocation advanceFactors advanceSinks

def membershipAdvanceDirective : SourceExecFact :=
  { atom := membershipAdvanceRule
    loc := advanceLocation
    rule :=
      { priority := 2
        name := "mm-list-membership-advance"
        input := .explicit advanceFactors
        guards := []
        tmpl := mkTemplate advanceSinks } }

theorem extract_membershipHitRule_exact :
    extractSupportedSourceExecFact membershipHitRule =
      some membershipHitDirective := by
  rfl

theorem extract_membershipMissingRule_exact :
    extractSupportedSourceExecFact membershipMissingRule =
      some membershipMissingDirective := by
  rfl

theorem extract_membershipAdvanceRule_exact :
    extractSupportedSourceExecFact membershipAdvanceRule =
      some membershipAdvanceDirective := by
  rfl

/-! ## Opaque rule reload -/

def membershipRuleCaptureRow (kind : String) (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-list-membership-rule", .symbol kind, rule]

private def hitCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-list-membership-rule", .symbol "hit",
      .var "membership-hit-rule"]

private def missingCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-list-membership-rule", .symbol "missing",
      .var "membership-missing-rule"]

private def advanceCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-list-membership-rule", .symbol "advance",
      .var "membership-advance-rule"]

def membershipRuleCaptureRows : List Atom :=
  [membershipRuleCaptureRow "hit" membershipHitRule,
   membershipRuleCaptureRow "missing" membershipMissingRule,
   membershipRuleCaptureRow "advance" membershipAdvanceRule]

private def reloadPatterns : List Atom :=
  [reloadTriggerTemplate, hitCaptureTemplate,
    missingCaptureTemplate, advanceCaptureTemplate]

private def reloadSinks : List Sink :=
  [.remove reloadTriggerTemplate,
    .add (.var "membership-hit-rule"),
    .add (.var "membership-missing-rule"),
    .add (.var "membership-advance-rule")]

def membershipReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks

def membershipReloadDirective : SourceExecFact :=
  mkDirective membershipReloadRule reloadLocation 35
    "mm-list-membership-reload" reloadPatterns reloadSinks

theorem extract_membershipReloadRule_exact :
    extractSupportedSourceExecFact membershipReloadRule =
      some membershipReloadDirective := by
  rfl

def membershipReloadRuleCaptureRow : Atom :=
  membershipReloadCapabilityRow membershipReloadRule

def membershipRules : List Atom :=
  [membershipHitRule, membershipMissingRule, membershipAdvanceRule,
    membershipReloadRule]

def membershipDirectives : List SourceExecFact :=
  [membershipHitDirective, membershipMissingDirective,
    membershipAdvanceDirective, membershipReloadDirective]

theorem membershipRules_extract_exact :
    membershipRules.filterMap extractSupportedSourceExecFact =
      membershipDirectives := by
  rfl

/-! ## Scheduled positive and negative controls -/

private def canaryOwner : Atom := .symbol "membership-owner"
private def canaryRequest : Atom := .symbol "membership-request"
private def canaryNeedle : Atom := .symbol "needle"
private def canaryOther : Atom := .symbol "other"
private def canaryReturnRule : Atom := .symbol "membership-client-reloader"
private def canaryReturnTrigger : Atom := .symbol "membership-client-trigger"

private def canaryReturnCapability : Atom :=
  membershipReturnCapabilityRow canaryOwner canaryRequest
    canaryReturnRule canaryReturnTrigger

private def hitCanaryProgram : List Atom :=
  membershipRules ++ membershipRuleCaptureRows ++
    [membershipReloadRuleCaptureRow] ++
    [canaryReturnCapability] ++
    [membershipRequestAtom canaryOwner canaryRequest canaryNeedle
      [canaryOther] [canaryNeedle, canaryOther]]

theorem hitCanary_selects_exact_hit :
    selectNextScheduled (cSupportedSourceExecFacts hitCanaryProgram) =
      some membershipHitDirective := by
  decide +kernel

def hitCanaryTarget : List Atom :=
  cFireReflectiveSourceExecFact hitCanaryProgram membershipHitDirective

theorem hitCanary_consumes_exact_request :
    membershipRequestAtom canaryOwner canaryRequest canaryNeedle
        [canaryOther] [canaryNeedle, canaryOther] ∉ hitCanaryTarget := by
  decide +kernel

theorem hitCanary_emits_exact_observation :
    membershipFoundAtom canaryOwner canaryRequest canaryNeedle
      [canaryOther] [canaryOther] ∈ hitCanaryTarget := by
  decide +kernel

theorem hitCanary_inhabits_exact_native_target :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      hitCanaryProgram
      (reflectiveNativeListExactTargetNativeType .leaveInert
        hitCanaryTarget).pred := by
  apply
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert hitCanaryProgram hitCanaryTarget).2
  simp [cReflectiveSourceWorkQueueStep, hitCanary_selects_exact_hit,
    hitCanaryTarget]

private def unequalCanaryProgram : List Atom :=
  membershipRules ++ membershipRuleCaptureRows ++
    [membershipReloadRuleCaptureRow] ++
    [canaryReturnCapability] ++
    [membershipRequestAtom canaryOwner canaryRequest canaryNeedle
      [] [canaryOther, canaryNeedle]]

def unequalAfterHitProbe : List Atom :=
  cFireReflectiveSourceExecFact unequalCanaryProgram membershipHitDirective

theorem unequalCanary_hit_probe_has_no_observation :
    membershipFoundAtom canaryOwner canaryRequest canaryNeedle []
      [canaryNeedle] ∉ unequalAfterHitProbe := by
  decide +kernel

theorem unequalAfterHitProbe_selects_missing_probe :
    selectNextScheduled
      (cSupportedSourceExecFacts unequalAfterHitProbe) =
      some membershipMissingDirective := by
  decide +kernel

def unequalAfterMissingProbe : List Atom :=
  cFireReflectiveSourceExecFact unequalAfterHitProbe
    membershipMissingDirective

theorem unequalAfterMissingProbe_selects_advance :
    selectNextScheduled
      (cSupportedSourceExecFacts unequalAfterMissingProbe) =
      some membershipAdvanceDirective := by
  decide +kernel

def unequalAfterAdvance : List Atom :=
  cFireReflectiveSourceExecFact unequalAfterMissingProbe
    membershipAdvanceDirective

theorem unequalAdvance_is_constant_work :
    membershipRequestAtom canaryOwner canaryRequest canaryNeedle
        [canaryOther] [canaryNeedle] ∈ unequalAfterAdvance /\
      membershipReloadTriggerAtom canaryOwner ∈ unequalAfterAdvance := by
  decide +kernel

theorem unequalAfterAdvance_selects_reload :
    selectNextScheduled (cSupportedSourceExecFacts unequalAfterAdvance) =
      some membershipReloadDirective := by
  decide +kernel

def unequalCanonicalSuccessor : List Atom :=
  cFireReflectiveSourceExecFact unequalAfterAdvance
    membershipReloadDirective

theorem unequalCanonicalSuccessor_restores_scan_inventory :
    membershipHitRule ∈ unequalCanonicalSuccessor /\
      membershipMissingRule ∈ unequalCanonicalSuccessor /\
      membershipAdvanceRule ∈ unequalCanonicalSuccessor /\
      membershipReloadRuleCaptureRow ∈ unequalCanonicalSuccessor /\
      canaryReturnCapability ∈ unequalCanonicalSuccessor /\
      membershipRequestAtom canaryOwner canaryRequest canaryNeedle
        [canaryOther] [canaryNeedle] ∈ unequalCanonicalSuccessor := by
  decide +kernel

/-- The four concrete administrative steps implementing one semantic
unequal-head advance are all classified by OSLF into exact target NTTs. -/
def unequalAdvance_has_oslf_native_trace :
    ReflectiveNativeTypeTrace .leaveInert 4 unequalCanaryProgram
      (cReflectiveSourceWorkQueueRunN .leaveInert 4
        unequalCanaryProgram).1 :=
  cReflectiveSourceWorkQueueRunN_nativeTypeTrace .leaveInert 4
    unequalCanaryProgram

private def missingCanaryProgram : List Atom :=
  membershipRules ++ membershipRuleCaptureRows ++
    [membershipReloadRuleCaptureRow] ++
    [canaryReturnCapability] ++
    [membershipRequestAtom canaryOwner canaryRequest canaryNeedle
      [canaryOther] []]

def missingAfterHitProbe : List Atom :=
  cFireReflectiveSourceExecFact missingCanaryProgram membershipHitDirective

theorem missingAfterHitProbe_selects_missing :
    selectNextScheduled (cSupportedSourceExecFacts missingAfterHitProbe) =
      some membershipMissingDirective := by
  decide +kernel

def missingCanaryTarget : List Atom :=
  cFireReflectiveSourceExecFact missingAfterHitProbe
    membershipMissingDirective

theorem missingCanary_emits_explicit_end :
    membershipMissingAtom canaryOwner canaryRequest canaryNeedle
      [canaryOther] ∈ missingCanaryTarget := by
  decide +kernel

theorem hitCanary_activates_exact_return_capability :
    canaryReturnRule ∈ hitCanaryTarget /\
      canaryReturnTrigger ∈ hitCanaryTarget /\
      canaryReturnCapability ∉ hitCanaryTarget := by
  decide +kernel

/-- A request under one owner cannot emit a terminal observation under a
different owner. -/
theorem hit_cannot_change_owner :
    membershipFoundAtom canaryOwner canaryRequest canaryNeedle
        [canaryOther] [canaryOther] ∉
      cFireReflectiveSourceExecFact
        [membershipHitRule,
         membershipRequestAtom (.symbol "wrong-owner") canaryRequest
           canaryNeedle [canaryOther] [canaryNeedle, canaryOther],
         membershipReturnCapabilityRow (.symbol "wrong-owner") canaryRequest
           canaryReturnRule canaryReturnTrigger]
        membershipHitDirective := by
  decide +kernel

#print axioms semanticStep_inhabits_target_native_type
#print axioms decodeEncodedListAtom_encodedListAtom
#print axioms encodedListAtom_injective
#print axioms represented_observation_is_source_backed
#print axioms membershipRules_extract_exact
#print axioms hitCanary_selects_exact_hit
#print axioms hitCanary_consumes_exact_request
#print axioms hitCanary_emits_exact_observation
#print axioms hitCanary_inhabits_exact_native_target
#print axioms unequalCanary_hit_probe_has_no_observation
#print axioms unequalAfterHitProbe_selects_missing_probe
#print axioms unequalAfterMissingProbe_selects_advance
#print axioms unequalAdvance_is_constant_work
#print axioms unequalAfterAdvance_selects_reload
#print axioms unequalCanonicalSuccessor_restores_scan_inventory
#print axioms unequalAdvance_has_oslf_native_trace
#print axioms missingAfterHitProbe_selects_missing
#print axioms missingCanary_emits_explicit_end
#print axioms hitCanary_activates_exact_return_capability
#print axioms hit_cannot_change_owner

end Mettapedia.Languages.ProcessCalculi.MORK.MM2FiniteListMembership
