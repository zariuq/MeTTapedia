import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec

/-!
# Reloading transformation for finite MM2 rule surfaces

MORK removes a selected `exec` before interpreting its input.  A finite
rule family that must remain available across successive state changes can
therefore be transformed into a reload-signalling family: every successful
rule adds one explicit administrative atom.  A separate verifier-owned
dispatcher may use that atom to reinstall the finite family.

This file is deliberately only the strict surface transformation.  The
dispatcher and the semantic adequacy argument remain independent, so a caller
cannot confuse a successfully decorated rule list with an execution proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Append one explicit add sink to a strict ordinary-MM2 `exec` surface.
Malformed shells and non-`O` outputs are rejected rather than silently
preserved. -/
def appendAddSink? (reload rule : Atom) : Option Atom :=
  match rule with
  | .expression [.symbol "exec", location, input,
      .expression (.symbol "O" :: sinks)] =>
      some
        (.expression
          [.symbol "exec", location, input,
            .expression
              (.symbol "O" :: sinks ++
                [.expression [.symbol "+", reload]])])
  | _ => none

/-- Extend a strict ordinary-MM2 executable rule with one captured opaque
code value.  The capture row becomes one additional input premise and the
captured variable becomes an output rule atom; this preserves expression-local
variables inside the captured value rather than embedding a new `exec` shell
inside another rule's output. -/
def appendCapturedRuleSink? (captureRow capturedRule rule : Atom) : Option Atom :=
  match capturedRule, rule with
  | .var _,
      .expression [.symbol "exec", location,
        .expression (.symbol "," :: inputs),
        .expression (.symbol "O" :: sinks)] =>
      some
        (.expression
          [.symbol "exec", location,
            .expression (.symbol "," :: inputs ++ [captureRow]),
            .expression
              (.symbol "O" :: sinks ++
                [.expression [.symbol "+", capturedRule]])])
  | _, _ => none

/-- Extend a strict executable rule with an explicit rearm request and an
opaque verifier-owned continuation.  The continuation is captured from a
separate row instead of being nested in the output, so its expression-local
variables remain local when it is later reinstated as an `exec`. -/
def appendRearmSinks? (reload captureRow capturedRule rule : Atom) : Option Atom := do
  let reloadableRule ← appendAddSink? reload rule
  appendCapturedRuleSink? captureRow capturedRule reloadableRule

/-- Transform every member of a finite executable presentation into a
trigger-created rearming presentation.  A malformed member rejects the whole
transform rather than silently producing a partly rearming machine. -/
def rearmAll? (reload captureRow capturedRule : Atom) : List Atom → Option (List Atom)
  | [] => some []
  | rule :: remaining => do
      let rearmedRule ← appendRearmSinks? reload captureRow capturedRule rule
      let rearmedRemaining ← rearmAll? reload captureRow capturedRule remaining
      pure (rearmedRule :: rearmedRemaining)

/-- Transform every member of a finite executable rule presentation, failing
as a whole when any member is outside the strict surface fragment. -/
def decorateAll? (reload : Atom) : List Atom → Option (List Atom)
  | [] => some []
  | rule :: remaining => do
      let decoratedRule ← appendAddSink? reload rule
      let decoratedRemaining ← decorateAll? reload remaining
      pure (decoratedRule :: decoratedRemaining)

/-- Decorate every occurrence of one selected executable rule while retaining
all other members byte-for-byte.  The transform fails when the selected rule
is absent or malformed; it never inserts a new rule by name. -/
def decorateMatchingLoop? (selected reload : Atom) :
    List Atom → Option (Bool × List Atom)
  | [] => some (false, [])
  | rule :: remaining => do
      let (seenRemaining, decoratedRemaining) ←
        decorateMatchingLoop? selected reload remaining
      if rule = selected then
        let decoratedRule ← appendAddSink? reload rule
        pure (true, decoratedRule :: decoratedRemaining)
      else
        pure (seenRemaining, rule :: decoratedRemaining)

/-- Strict selected-member form of `decorateAll?`.  Multiple equal
occurrences remain multiple occurrences and are all decorated. -/
def decorateMatching? (selected reload : Atom) (rules : List Atom) :
    Option (List Atom) :=
  match decorateMatchingLoop? selected reload rules with
  | some (true, decorated) => some decorated
  | _ => none

/-- Replace every occurrence of one exact opaque surface value.  This is the
strict capture-row counterpart of `decorateMatching?`: an absent selected
value fails rather than returning an unchanged presentation. -/
def replaceMatchingLoop (selected replacement : Atom) :
    List Atom → Bool × List Atom
  | [] => (false, [])
  | rule :: remaining =>
      let (seenRemaining, translatedRemaining) :=
        replaceMatchingLoop selected replacement remaining
      if rule = selected then
        (true, replacement :: translatedRemaining)
      else
        (seenRemaining, rule :: translatedRemaining)

/-- Fail-closed exact replacement on a finite surface presentation. -/
def replaceMatching? (selected replacement : Atom) (rules : List Atom) :
    Option (List Atom) :=
  let (seen, translated) := replaceMatchingLoop selected replacement rules
  if seen then some translated else none

/-- Inspect a strict ordinary-MM2 executable surface for an added observation
with one exact head symbol.  Non-executable or malformed surfaces are rejected
instead of silently treated as non-observing rules. -/
def execAddsOutputHead? (head : String) : Atom → Option Bool
  | .expression [.symbol "exec", _, .expression (.symbol "," :: _),
      .expression (.symbol "O" :: sinks)] =>
      some (sinks.any fun sink =>
        match sink with
        | .expression [.symbol "+", .expression (.symbol actual :: _)] =>
            actual == head
        | _ => false)
  | _ => none

/-- Transform one strict executable surface when it adds the selected output
head.  A well-formed rule with another output head is retained byte-for-byte;
an ill-formed surface is rejected. -/
def captureRuleAddingOutputHead? (head : String) (captureRow capturedRule rule : Atom) :
    Option Atom := do
  let emits ← execAddsOutputHead? head rule
  if emits then appendCapturedRuleSink? captureRow capturedRule rule else pure rule

/-- Decorate every strict executable in a finite presentation that emits a
chosen observation head.  The transform is occurrence-preserving: equal rules
at distinct list positions are independently decorated. -/
def captureOutputHeadLoop? (head : String) (captureRow capturedRule : Atom) :
    List Atom → Option (Bool × List Atom)
  | [] => some (false, [])
  | rule :: remaining => do
      let (seenRemaining, translatedRemaining) ←
        captureOutputHeadLoop? head captureRow capturedRule remaining
      let emits ← execAddsOutputHead? head rule
      let translated ← captureRuleAddingOutputHead? head captureRow capturedRule rule
      pure (emits || seenRemaining, translated :: translatedRemaining)

/-- Fail-closed selected-observation surface transform.  It succeeds only
when every source member is a strict `exec` surface and at least one member
adds the requested observation. -/
def captureRulesAddingOutputHead? (head : String) (captureRow capturedRule : Atom)
    (rules : List Atom) : Option (List Atom) :=
  match captureOutputHeadLoop? head captureRow capturedRule rules with
  | some (true, translated) => some translated
  | _ => none

/-- A finite rule-surface transformation retains both presentations and its
exact successful decoding boundary. -/
structure Artifact where
  reload : Atom
  sourceRules : List Atom
  targetRules : List Atom
  exact : decorateAll? reload sourceRules = some targetRules

/-- Build a reloading surface artifact only when the whole source inventory
belongs to the strict transformed fragment. -/
def build? (reload : Atom) (sourceRules : List Atom) : Option Artifact :=
  match transformed : decorateAll? reload sourceRules with
  | none => none
  | some targetRules => some
      { reload
        sourceRules
        targetRules
        exact := transformed }

/-- A finite rearming transformation retains its input presentation, emitted
presentation, administrative trigger, opaque capture-row shape, and the exact
successful surface translation.  This is the reusable presentation-level
boundary; a caller still supplies the distinct target-level loader and its
execution argument. -/
structure RearmArtifact where
  reload : Atom
  captureRow : Atom
  capturedRule : Atom
  sourceRules : List Atom
  targetRules : List Atom
  exact : rearmAll? reload captureRow capturedRule sourceRules = some targetRules

/-- Build a rearming artifact only when every supplied rule belongs to the
strict ordinary-MM2 executable surface.  The whole transformation fails closed
when any source member is malformed. -/
def buildRearm? (reload captureRow capturedRule : Atom)
    (sourceRules : List Atom) : Option RearmArtifact :=
  match transformed : rearmAll? reload captureRow capturedRule sourceRules with
  | none => none
  | some targetRules => some
      { reload
        captureRow
        capturedRule
        sourceRules
        targetRules
        exact := transformed }

/-- A successful rearming surface transformation preserves every rule
occurrence.  It changes rule interiors and adds their administrative interface,
but it cannot drop or synthesize a presentation member. -/
theorem rearmAll?_target_length
    (reload captureRow capturedRule : Atom)
    {sourceRules targetRules : List Atom}
    (exact :
      rearmAll? reload captureRow capturedRule sourceRules = some targetRules) :
    targetRules.length = sourceRules.length := by
  induction sourceRules generalizing targetRules with
  | nil =>
      simp [rearmAll?] at exact
      cases exact
      rfl
  | cons rule remaining induction =>
      cases ruleResult : appendRearmSinks? reload captureRow capturedRule rule with
      | none =>
          simp [rearmAll?, ruleResult] at exact
      | some rearmedRule =>
          cases remainingResult : rearmAll? reload captureRow capturedRule remaining with
          | none =>
              simp [rearmAll?, ruleResult, remainingResult] at exact
          | some rearmedRemaining =>
              simp [rearmAll?, ruleResult, remainingResult] at exact
              subst targetRules
              simp [induction remainingResult]

/-- Successful artifact construction retains the exact caller-supplied source
presentation.  This closes the small but important distinction between a
transform artifact carrying some rule list and carrying the input list that
was actually transformed. -/
theorem buildRearm?_sourceRules
    (reload captureRow capturedRule : Atom)
    (sourceRules : List Atom) (artifact : RearmArtifact)
    (built : buildRearm? reload captureRow capturedRule sourceRules =
      some artifact) :
    artifact.sourceRules = sourceRules := by
  unfold buildRearm? at built
  split at built
  · contradiction
  · cases built
    rfl

@[simp] theorem appendAddSink?_nonexec_rejected (reload : Atom) :
    appendAddSink? reload (.symbol "not-an-exec") = none := by
  rfl

private def canaryReload : Atom :=
  .expression [.symbol "reload", .var "owner"]

private def canaryRearmCaptureRow : Atom :=
  .expression [.symbol "rearm-code", .var "code"]

private def canaryRearmCode : Atom := .var "code"

private def canaryRule : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "03", .symbol "canary"],
      .expression [.symbol ",", .expression [.symbol "ready", .var "owner"]],
      .expression [.symbol "O",
        .expression [.symbol "-", .expression [.symbol "ready", .var "owner"]],
        .expression [.symbol "+", .expression [.symbol "done", .var "owner"]]]]

private def decoratedCanaryRule : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "03", .symbol "canary"],
      .expression [.symbol ",", .expression [.symbol "ready", .var "owner"]],
      .expression [.symbol "O",
        .expression [.symbol "-", .expression [.symbol "ready", .var "owner"]],
        .expression [.symbol "+", .expression [.symbol "done", .var "owner"]],
        .expression [.symbol "+", canaryReload]]]

private def canaryCaptureRow : Atom :=
  .expression [.symbol "owned-rule", .var "captured"]

private def captureDecoratedCanaryRule : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "03", .symbol "canary"],
      .expression [.symbol ",",
        .expression [.symbol "ready", .var "owner"], canaryCaptureRow],
      .expression [.symbol "O",
        .expression [.symbol "-", .expression [.symbol "ready", .var "owner"]],
        .expression [.symbol "+", .expression [.symbol "done", .var "owner"]],
        .expression [.symbol "+", .var "captured"]]]

private def rearmedCanaryRule : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "03", .symbol "canary"],
      .expression [.symbol ",",
        .expression [.symbol "ready", .var "owner"], canaryRearmCaptureRow],
      .expression [.symbol "O",
        .expression [.symbol "-", .expression [.symbol "ready", .var "owner"]],
        .expression [.symbol "+", .expression [.symbol "done", .var "owner"]],
        .expression [.symbol "+", canaryReload],
        .expression [.symbol "+", canaryRearmCode]]]

/-- Positive surface canary: decoration changes only the output inventory by
the requested explicit reload sink. -/
theorem canary_decorates_exactly :
    appendAddSink? canaryReload canaryRule = some decoratedCanaryRule := by
  rfl

/-- Positive capture canary: the source rule receives exactly one additional
premise and reinstalls the opaque captured value as code. -/
theorem canary_captures_rule_exactly :
    appendCapturedRuleSink? canaryCaptureRow (.var "captured") canaryRule =
      some captureDecoratedCanaryRule := by
  rfl

/-- Positive rearm canary: a successful rule requests the next dispatch round
and restores the separately supplied executable continuation. -/
theorem canary_rearms_exactly :
    appendRearmSinks? canaryReload canaryRearmCaptureRow canaryRearmCode canaryRule =
      some rearmedCanaryRule := by
  rfl

/-- The rearming transform remains fail-closed on a non-executable member. -/
theorem rearmAll_nonexec_rejected :
    rearmAll? canaryReload canaryRearmCaptureRow canaryRearmCode
      [canaryRule, .symbol "not-an-exec"] = none := by
  rfl

/-- A literal output value cannot masquerade as an opaque captured rule. -/
theorem capture_requires_variable :
    appendCapturedRuleSink? canaryCaptureRow (.symbol "not-a-variable")
      canaryRule = none := by
  rfl

/-- A mixed inventory fails as a whole; malformed members cannot evade the
admission boundary by being omitted from the target list. -/
theorem mixed_inventory_rejected :
    decorateAll? canaryReload [canaryRule, .symbol "not-an-exec"] = none := by
  rfl

/-- A selected surface transformation alters its selected occurrence and
leaves unrelated inventory members intact. -/
theorem matching_canary_decorates_exactly :
    decorateMatching? canaryRule canaryReload
      [canaryRule, .symbol "untouched"] =
        some [decoratedCanaryRule, .symbol "untouched"] := by
  rfl

/-- Selection is fail-closed: a miss cannot silently yield the original
inventory. -/
theorem matching_missing_rule_rejected :
    decorateMatching? canaryRule canaryReload [.symbol "untouched"] = none := by
  rfl

/-- Exact capture replacement is occurrence-preserving and fails closed on a
missing source value. -/
theorem capture_replacement_canary :
    replaceMatching? canaryRule decoratedCanaryRule
      [canaryRule, .symbol "untouched", canaryRule] =
        some [decoratedCanaryRule, .symbol "untouched", decoratedCanaryRule] := by
  rfl

theorem capture_replacement_missing_rejected :
    replaceMatching? canaryRule decoratedCanaryRule [.symbol "untouched"] = none := by
  rfl

private def faultCanaryRule : Atom :=
  .expression
    [.symbol "exec", .symbol "fault-location",
      .expression [.symbol ",", .expression [.symbol "trigger"]],
      .expression [.symbol "O",
        .expression [.symbol "+",
          .expression [.symbol "mm-proof-fault", .symbol "reason"]]]]

private def nonfaultCanaryRule : Atom :=
  .expression
    [.symbol "exec", .symbol "ordinary-location",
      .expression [.symbol ",", .expression [.symbol "trigger"]],
      .expression [.symbol "O",
        .expression [.symbol "+", .expression [.symbol "ordinary"]]]]

private def faultCaptureCanaryRow : Atom :=
  .expression [.symbol "fault-capture", .var "captured"]

private def faultCaptureDecoratedCanaryRule : Atom :=
  (appendCapturedRuleSink? faultCaptureCanaryRow (.var "captured")
    faultCanaryRule).get (by decide)

/-- Positive control: fault-producing members receive the captured
continuation while nonfault members retain their exact authored surface. -/
theorem capture_output_head_fault_canary :
    captureRulesAddingOutputHead? "mm-proof-fault" faultCaptureCanaryRow
      (.var "captured") [faultCanaryRule, nonfaultCanaryRule] =
        some [faultCaptureDecoratedCanaryRule, nonfaultCanaryRule] := by
  rfl

/-- The observation-selected transform fails closed when the requested head
is absent; it never returns an unchanged inventory as a successful result. -/
theorem capture_output_head_missing_rejected :
    captureRulesAddingOutputHead? "mm-proof-fault" faultCaptureCanaryRow
      (.var "captured") [nonfaultCanaryRule] = none := by
  rfl

/-- Artifact construction shares the strict all-or-nothing rejection boundary
of `decorateAll?`. -/
theorem build?_mixed_inventory_rejected :
    build? canaryReload [canaryRule, .symbol "not-an-exec"] = none := by
  rfl

/-- Rearm-artifact construction has the same whole-inventory fail-closed
boundary as `rearmAll?`; it cannot silently omit a malformed member. -/
theorem buildRearm?_mixed_inventory_rejected :
    buildRearm? canaryReload canaryRearmCaptureRow canaryRearmCode
      [canaryRule, .symbol "not-an-exec"] = none := by
  rfl

#print axioms canary_decorates_exactly
#print axioms canary_captures_rule_exactly
#print axioms canary_rearms_exactly
#print axioms rearmAll_nonexec_rejected
#print axioms capture_requires_variable
#print axioms mixed_inventory_rejected
#print axioms matching_canary_decorates_exactly
#print axioms matching_missing_rule_rejected
#print axioms capture_replacement_canary
#print axioms capture_replacement_missing_rejected
#print axioms capture_output_head_fault_canary
#print axioms capture_output_head_missing_rejected
#print axioms build?_mixed_inventory_rejected
#print axioms buildRearm?_mixed_inventory_rejected
#print axioms rearmAll?_target_length
#print axioms buildRearm?_sourceRules

end Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface
