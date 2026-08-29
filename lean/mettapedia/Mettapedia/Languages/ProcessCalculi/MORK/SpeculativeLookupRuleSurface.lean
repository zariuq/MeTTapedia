import Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

/-!
# Speculative lookup transformation for finite MM2 rule presentations

A cursor-based lookup rule already contains the complete fallback behavior.
This transformation derives two one-shot direct probes from supplied proof and
opaque-value handlers, equips a supplied request-producing rule to reinstall
those probes, and retains the original cursor handlers as the fallback.

The pass is deliberately strict.  It accepts only ordinary `exec` surfaces,
requires exactly one selected lookup premise in each direct handler, requires
the three selected source rules to occur in the supplied finite presentation,
and replaces exactly one request-producing rule.  It does not select rules by
filename, digest, or fixture identity.

This module proves presentation transformation only.  A caller must separately
prove that scheduler exhaustion of the direct probes realizes semantic absence
and that the retained cursor machine has the required terminal observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

/-- Replace exactly one occurrence of an opaque surface value.  Missing and
duplicated occurrences fail closed. -/
def replaceExactlyOne? (selected replacement : Atom) :
    List Atom -> Option (List Atom)
  | [] => none
  | value :: remaining =>
      if value = selected then
        if selected ∈ remaining then none
        else some (replacement :: remaining)
      else
        (replaceExactlyOne? selected replacement remaining).map
          (fun translated => value :: translated)

theorem replaceExactlyOne?_length
    {selected replacement : Atom} {source target : List Atom}
    (exact : replaceExactlyOne? selected replacement source = some target) :
    target.length = source.length := by
  induction source generalizing target with
  | nil => simp [replaceExactlyOne?] at exact
  | cons value remaining induction =>
      by_cases selectedHere : value = selected
      · subst value
        by_cases duplicated : selected ∈ remaining
        · simp [replaceExactlyOne?, duplicated] at exact
        · simp [replaceExactlyOne?, duplicated] at exact
          subst target
          rfl
      · simp [replaceExactlyOne?, selectedHere] at exact
        obtain ⟨translated, translatedExact, rfl⟩ := exact
        simp [induction translatedExact]

/-- Retarget one strict executable rule while widening exactly one selected
input premise and its corresponding output removal.  The first input must be
the rule's self-premise at the same source location.  Outer location, self
location, input lookup, and removal are retargeted atomically. -/
def retargetInputPremise? (newLocation selectedPremise replacementPremise : Atom) :
    Atom -> Option Atom
  | .expression
      [.symbol "exec", sourceLocation,
        .expression
          (.symbol "," ::
            .expression [.symbol "exec", selfLocation, selfInput, selfOutput] ::
              inputs), .expression (.symbol "O" :: sinks)] =>
      if selfLocation == sourceLocation then do
        let translatedInputs <-
          replaceExactlyOne? selectedPremise replacementPremise inputs
        let selectedRemoval : Atom :=
          .expression [.symbol "-", selectedPremise]
        let replacementRemoval : Atom :=
          .expression [.symbol "-", replacementPremise]
        let translatedSinks <-
          replaceExactlyOne? selectedRemoval replacementRemoval sinks
        let targetSelf : Atom :=
          .expression [.symbol "exec", newLocation, selfInput, selfOutput]
        pure
          (.expression
            [.symbol "exec", newLocation,
              .expression (.symbol "," :: targetSelf :: translatedInputs),
              .expression (.symbol "O" :: translatedSinks)])
      else none
  | _ => none

/-- All target-owned surface data needed to derive the speculative layer.
The profile contains shapes and fresh locations, not selected source rules. -/
structure Profile where
  exactLookupPremise : Atom
  directLookupPremise : Atom
  directProofLocation : Atom
  directOpaqueLocation : Atom
  directProofCaptureRow : Atom
  directProofCaptureVariable : Atom
  directOpaqueCaptureRow : Atom
  directOpaqueCaptureVariable : Atom
deriving DecidableEq

/-- The complete finite presentation artifact returned by `build?`.  Its
fields remain inspectable so later GSLT stages can reify the exact source and
target rule occurrences rather than trusting a generated text file. -/
structure Artifact where
  profile : Profile
  sourceRules : List Atom
  sourceTerminalRule : Atom
  sourceProofRule : Atom
  sourceOpaqueRule : Atom
  directProofRule : Atom
  directOpaqueRule : Atom
  targetTerminalRule : Atom
  targetRules : List Atom
deriving DecidableEq

/-- Occurrence-level selection inside a finite authored presentation.  Using
positions rather than extensional membership keeps duplicate rule occurrences
distinct and makes reordering visible to the transformation. -/
structure Selection where
  terminalPosition : Nat
  proofPosition : Nat
  opaquePosition : Nat
deriving DecidableEq

/-- Inspectable result of position-sensitive transformation. -/
structure SelectedArtifact where
  selection : Selection
  artifact : Artifact
deriving DecidableEq

/-- Scheduler key of one ordinary executable surface. -/
def execLocation? : Atom -> Option Atom
  | .expression [.symbol "exec", location, _input, _output] => some location
  | _ => none

def Selection.rolesDistinct (selection : Selection) : Bool :=
  selection.terminalPosition != selection.proofPosition &&
    selection.terminalPosition != selection.opaquePosition &&
    selection.proofPosition != selection.opaquePosition

/-- Strict physical-inventory boundary.  Every value must be an ordinary
executable, rule values must be unique, and scheduler locations must be
injective. -/
def schedulerInventoryWellFormed (rules : List Atom) : Bool :=
  rules.all (fun rule => (execLocation? rule).isSome) &&
    decide rules.Nodup && decide (rules.filterMap execLocation?).Nodup

/-- Replace the value at one exact finite-list position, retaining every
unselected occurrence byte-for-byte. -/
def replaceAt? (position : Nat) (replacement : Atom) :
    List Atom -> Option (List Atom)
  | [] => none
  | value :: remaining =>
      match position with
      | 0 => some (replacement :: remaining)
      | next + 1 =>
          (replaceAt? next replacement remaining).map
            (fun translated => value :: translated)

theorem replaceAt?_length {position : Nat} {replacement : Atom}
    {source target : List Atom}
    (built : replaceAt? position replacement source = some target) :
    target.length = source.length := by
  induction source generalizing position target with
  | nil => simp [replaceAt?] at built
  | cons value remaining induction =>
      cases position with
      | zero =>
          simp [replaceAt?] at built
          subst target
          rfl
      | succ next =>
          simp [replaceAt?] at built
          obtain ⟨translated, translatedBuilt, rfl⟩ := built
          simp [induction translatedBuilt]

/-- Replace one exact atom occurrence anywhere inside an opaque surface tree.
The count is computed from the source tree before inserting the replacement,
so occurrences inside the replacement cannot affect admission. -/
private def replaceAtomOccurrences (selected replacement : Atom) :
    Atom -> Nat × Atom
  | value@(.expression children) =>
      if value == selected then
        (1, replacement)
      else
        let translated := children.map (replaceAtomOccurrences selected replacement)
        (translated.foldl (fun count entry => count + entry.1) 0,
          .expression (translated.map Prod.snd))
  | value =>
      if value == selected then (1, replacement) else (0, value)

/-- Instantiate a strict one-hole capture-row template.  Missing or duplicated
holes fail closed. -/
def instantiateExactlyOne? (selected replacement source : Atom) : Option Atom :=
  let (count, target) := replaceAtomOccurrences selected replacement source
  if count = 1 then some target else none

/-- Complete runtime-presentation result: transformed executable occurrences
and the persistent opaque rows that install them. -/
structure RuntimeArtifact where
  rules : Artifact
  terminalCaptureTemplate : Atom
  terminalCaptureVariable : Atom
  sourceTerminalCaptureRow : Atom
  targetTerminalCaptureRow : Atom
  directProofHandlerRow : Atom
  directOpaqueHandlerRow : Atom
  targetStaticRows : List Atom
deriving DecidableEq

/-- Transform the persistent code inventory from the same derived rules.
The source terminal row is replaced exactly once and the two direct-handler
rows are instantiated from the profile's capture templates. -/
def buildRuntime? (rules : Artifact)
    (terminalCaptureTemplate terminalCaptureVariable : Atom)
    (sourceStaticRows : List Atom) : Option RuntimeArtifact := do
  let sourceTerminalCaptureRow <-
    instantiateExactlyOne? terminalCaptureVariable rules.sourceTerminalRule
      terminalCaptureTemplate
  let targetTerminalCaptureRow <-
    instantiateExactlyOne? terminalCaptureVariable rules.targetTerminalRule
      terminalCaptureTemplate
  let directProofHandlerRow <-
    instantiateExactlyOne? rules.profile.directProofCaptureVariable
      rules.directProofRule rules.profile.directProofCaptureRow
  let directOpaqueHandlerRow <-
    instantiateExactlyOne? rules.profile.directOpaqueCaptureVariable
      rules.directOpaqueRule rules.profile.directOpaqueCaptureRow
  let retainedStaticRows <-
    replaceExactlyOne? sourceTerminalCaptureRow targetTerminalCaptureRow
      sourceStaticRows
  pure
    { rules
      terminalCaptureTemplate
      terminalCaptureVariable
      sourceTerminalCaptureRow
      targetTerminalCaptureRow
      directProofHandlerRow
      directOpaqueHandlerRow
      targetStaticRows :=
        retainedStaticRows ++ [directProofHandlerRow, directOpaqueHandlerRow] }

/-- Derive the three transformed executable surfaces before changing the
finite inventory. -/
private def deriveRules? (profile : Profile)
    (sourceTerminalRule sourceProofRule sourceOpaqueRule : Atom) :
    Option (Atom × Atom × Atom) := do
  let directProofRule <-
    retargetInputPremise? profile.directProofLocation
      profile.exactLookupPremise profile.directLookupPremise sourceProofRule
  let directOpaqueRule <-
    retargetInputPremise? profile.directOpaqueLocation
      profile.exactLookupPremise profile.directLookupPremise sourceOpaqueRule
  let terminalWithProof <-
    appendCapturedRuleSink? profile.directProofCaptureRow
      profile.directProofCaptureVariable sourceTerminalRule
  let targetTerminalRule <-
    appendCapturedRuleSink? profile.directOpaqueCaptureRow
      profile.directOpaqueCaptureVariable terminalWithProof
  pure (directProofRule, directOpaqueRule, targetTerminalRule)

/-- Derive the speculative layer from three explicit occurrences of the
supplied presentation.  The selected rule values are read from the input;
callers cannot supply a different remembered rule beside the presentation. -/
def buildSelected? (profile : Profile) (selection : Selection)
    (sourceRules : List Atom) : Option SelectedArtifact := do
  let sourceTerminalRule <- sourceRules[selection.terminalPosition]?
  let sourceProofRule <- sourceRules[selection.proofPosition]?
  let sourceOpaqueRule <- sourceRules[selection.opaquePosition]?
  let (directProofRule, directOpaqueRule, targetTerminalRule) <-
    deriveRules? profile sourceTerminalRule sourceProofRule sourceOpaqueRule
  let retainedRules <-
    replaceAt? selection.terminalPosition targetTerminalRule sourceRules
  pure
    { selection
      artifact :=
        { profile
          sourceRules
          sourceTerminalRule
          sourceProofRule
          sourceOpaqueRule
          directProofRule
          directOpaqueRule
          targetTerminalRule
          targetRules := retainedRules ++ [directProofRule, directOpaqueRule] } }

/-- Public fail-closed positional compiler.  The occurrence-aware primitive
above remains useful for semantic inventories, while this boundary rejects
collisions that physical MM2 support semantics would collapse. -/
def buildSelectedStrict? (profile : Profile) (selection : Selection)
    (sourceRules : List Atom) : Option SelectedArtifact :=
  if selection.rolesDistinct && schedulerInventoryWellFormed sourceRules then do
    let artifact <- buildSelected? profile selection sourceRules
    if schedulerInventoryWellFormed artifact.artifact.targetRules then
      some artifact
    else none
  else none

/-- Derive the speculative presentation from the supplied finite rule list.
Every selection is exact and fail-closed.  The original proof and opaque rules
remain in the target as cursor fallback handlers; the two derived rules are
additional one-shot direct probes. -/
def build? (profile : Profile) (sourceRules : List Atom)
    (sourceTerminalRule sourceProofRule sourceOpaqueRule : Atom) :
    Option Artifact :=
  if sourceProofRule ∈ sourceRules then
    if sourceOpaqueRule ∈ sourceRules then
      match deriveRules? profile sourceTerminalRule sourceProofRule
          sourceOpaqueRule with
      | none => none
      | some (directProofRule, directOpaqueRule, targetTerminalRule) =>
          match replaceExactlyOne? sourceTerminalRule targetTerminalRule
              sourceRules with
          | none => none
          | some retainedRules =>
              some
                { profile
                  sourceRules
                  sourceTerminalRule
                  sourceProofRule
                  sourceOpaqueRule
                  directProofRule
                  directOpaqueRule
                  targetTerminalRule
                  targetRules :=
                    retainedRules ++ [directProofRule, directOpaqueRule] }
    else none
  else none

/-- A successful positional build retains the exact caller-supplied
presentation as its source. -/
theorem buildSelected?_sourceRules (profile : Profile) (selection : Selection)
    (sourceRules : List Atom) (artifact : SelectedArtifact)
    (built : buildSelected? profile selection sourceRules = some artifact) :
    artifact.artifact.sourceRules = sourceRules := by
  unfold buildSelected? at built
  cases terminalExact : sourceRules[selection.terminalPosition]? with
  | none => simp [terminalExact] at built
  | some sourceTerminalRule =>
      simp only [terminalExact] at built
      cases proofExact : sourceRules[selection.proofPosition]? with
      | none => simp [proofExact] at built
      | some sourceProofRule =>
          simp only [proofExact] at built
          cases opaqueExact : sourceRules[selection.opaquePosition]? with
          | none => simp [opaqueExact] at built
          | some sourceOpaqueRule =>
              simp only [opaqueExact] at built
              simp only [bind, Option.bind] at built
              cases derivedExact : deriveRules? profile sourceTerminalRule
                  sourceProofRule sourceOpaqueRule with
              | none => simp [derivedExact] at built
              | some derivedRules =>
                  rcases derivedRules with
                    ⟨directProofRule, directOpaqueRule, targetTerminalRule⟩
                  rw [derivedExact] at built
                  cases retainedExact : replaceAt? selection.terminalPosition
                      targetTerminalRule sourceRules with
                  | none => simp [retainedExact] at built
                  | some retainedRules =>
                      simp only [retainedExact] at built
                      cases built
                      rfl

/-- A successful occurrence-sensitive build preserves every source rule
occurrence and appends exactly the two derived direct handlers. -/
theorem buildSelected?_targetRules_length (profile : Profile)
    (selection : Selection) (sourceRules : List Atom)
    (artifact : SelectedArtifact)
    (built : buildSelected? profile selection sourceRules = some artifact) :
    artifact.artifact.targetRules.length = sourceRules.length + 2 := by
  unfold buildSelected? at built
  cases terminalExact : sourceRules[selection.terminalPosition]? with
  | none => simp [terminalExact] at built
  | some sourceTerminalRule =>
      simp only [terminalExact] at built
      cases proofExact : sourceRules[selection.proofPosition]? with
      | none => simp [proofExact] at built
      | some sourceProofRule =>
          simp only [proofExact] at built
          cases opaqueExact : sourceRules[selection.opaquePosition]? with
          | none => simp [opaqueExact] at built
          | some sourceOpaqueRule =>
              simp only [opaqueExact] at built
              simp only [bind, Option.bind] at built
              cases derivedExact : deriveRules? profile sourceTerminalRule
                  sourceProofRule sourceOpaqueRule with
              | none => simp [derivedExact] at built
              | some derivedRules =>
                  rcases derivedRules with
                    ⟨directProofRule, directOpaqueRule, targetTerminalRule⟩
                  rw [derivedExact] at built
                  cases retainedExact : replaceAt? selection.terminalPosition
                      targetTerminalRule sourceRules with
                  | none => simp [retainedExact] at built
                  | some retainedRules =>
                      simp only [retainedExact] at built
                      cases built
                      simp [replaceAt?_length retainedExact]

/-- The strict physical-inventory boundary preserves the same exact source
presentation as the occurrence-aware compiler beneath it. -/
theorem buildSelectedStrict?_sourceRules (profile : Profile)
    (selection : Selection) (sourceRules : List Atom)
    (artifact : SelectedArtifact)
    (built : buildSelectedStrict? profile selection sourceRules = some artifact) :
    artifact.artifact.sourceRules = sourceRules := by
  unfold buildSelectedStrict? at built
  split at built
  · obtain ⟨candidate, candidateBuilt, built⟩ :=
      Option.bind_eq_some_iff.mp built
    split at built
    · cases built
      exact buildSelected?_sourceRules profile selection sourceRules artifact
        candidateBuilt
    · simp at built
  · simp at built

theorem buildSelectedStrict?_targetRules_length (profile : Profile)
    (selection : Selection) (sourceRules : List Atom)
    (artifact : SelectedArtifact)
    (built : buildSelectedStrict? profile selection sourceRules = some artifact) :
    artifact.artifact.targetRules.length = sourceRules.length + 2 := by
  unfold buildSelectedStrict? at built
  split at built
  · obtain ⟨candidate, candidateBuilt, built⟩ :=
      Option.bind_eq_some_iff.mp built
    split at built
    · cases built
      exact buildSelected?_targetRules_length profile selection sourceRules
        artifact candidateBuilt
    · simp at built
  · simp at built

/-- A successful build retains the exact caller-supplied presentation as its
source.  This is an input-retention law; the derived-rule laws below carry the
behavioral content. -/
theorem build?_sourceRules (profile : Profile) (sourceRules : List Atom)
    (sourceTerminalRule sourceProofRule sourceOpaqueRule : Atom)
    (artifact : Artifact)
    (built : build? profile sourceRules sourceTerminalRule sourceProofRule
      sourceOpaqueRule = some artifact) :
    artifact.sourceRules = sourceRules := by
  unfold build? at built
  by_cases proofMember : sourceProofRule ∈ sourceRules
  · simp only [if_pos proofMember] at built
    by_cases opaqueMember : sourceOpaqueRule ∈ sourceRules
    · simp only [if_pos opaqueMember] at built
      cases directExact : deriveRules? profile sourceTerminalRule
          sourceProofRule sourceOpaqueRule with
      | none => simp [directExact] at built
      | some directRules =>
          simp only [directExact] at built
          rcases directRules with ⟨directProofRule, directOpaqueRule,
            targetTerminalRule⟩
          cases retainedExact : replaceExactlyOne? sourceTerminalRule
              targetTerminalRule sourceRules with
          | none => simp [retainedExact] at built
          | some retainedRules =>
              simp only [retainedExact, Option.some.injEq] at built
              subst artifact
              rfl
    · simp [opaqueMember] at built
  · simp [proofMember] at built

/-- Successful derivation preserves the complete source occurrence inventory
and adds exactly the two direct-handler occurrences. -/
theorem build?_targetRules_length (profile : Profile)
    (sourceRules : List Atom)
    (sourceTerminalRule sourceProofRule sourceOpaqueRule : Atom)
    (artifact : Artifact)
    (built : build? profile sourceRules sourceTerminalRule sourceProofRule
      sourceOpaqueRule = some artifact) :
    artifact.targetRules.length = sourceRules.length + 2 := by
  unfold build? at built
  by_cases proofMember : sourceProofRule ∈ sourceRules
  · simp only [if_pos proofMember] at built
    by_cases opaqueMember : sourceOpaqueRule ∈ sourceRules
    · simp only [if_pos opaqueMember] at built
      cases directExact : deriveRules? profile sourceTerminalRule
          sourceProofRule sourceOpaqueRule with
      | none => simp [directExact] at built
      | some directRules =>
          simp only [directExact] at built
          rcases directRules with ⟨directProofRule, directOpaqueRule,
            targetTerminalRule⟩
          cases retainedExact : replaceExactlyOne? sourceTerminalRule
              targetTerminalRule sourceRules with
          | none => simp [retainedExact] at built
          | some retainedRules =>
              simp only [retainedExact, Option.some.injEq] at built
              subst artifact
              simp [replaceExactlyOne?_length retainedExact]
    · simp [opaqueMember] at built
  · simp [proofMember] at built

/-! ## Runtime-inventory controls -/

private def canaryCaptureVariable : Atom := .var "captured-rule"

private def canaryCaptureTemplate : Atom :=
  .expression [.symbol "owned-rule", canaryCaptureVariable]

private def canaryCapturedRule : Atom :=
  .expression [.symbol "exec", .symbol "location", .symbol "I", .symbol "O"]

example :
    instantiateExactlyOne? canaryCaptureVariable canaryCapturedRule
        canaryCaptureTemplate =
      some (.expression [.symbol "owned-rule", canaryCapturedRule]) := by
  simp [instantiateExactlyOne?, replaceAtomOccurrences,
    canaryCaptureVariable, canaryCapturedRule, canaryCaptureTemplate,
    Atom.beq, BEq.beq]

/-- Negative control: a duplicated capture hole is not an admissible opaque
runtime-row template. -/
example :
    instantiateExactlyOne? canaryCaptureVariable canaryCapturedRule
        (.expression
          [.symbol "owned-rule", canaryCaptureVariable,
            canaryCaptureVariable]) = none := by
  simp [instantiateExactlyOne?, replaceAtomOccurrences,
    canaryCaptureVariable, canaryCapturedRule, Atom.beq, BEq.beq]

/-! ## Surface controls -/

private def canaryExact : Atom :=
  .expression [.symbol "lookup", .var "owner", .var "query", .var "query"]

private def canaryDirect : Atom :=
  .expression [.symbol "lookup", .var "owner", .var "query", .var "cursor"]

private def canarySelf : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "08", .symbol "cursor"],
      .var "input", .var "output"]

private def canaryRule (result : String) : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "08", .symbol "cursor"],
      .expression [.symbol ",", canarySelf, canaryExact],
      .expression
        [.symbol "O", .expression [.symbol "-", canaryExact],
          .expression [.symbol "+", .symbol result]]]

private def canaryDirectLocation : Atom :=
  .expression [.symbol "08", .symbol "direct"]

/-- Positive control: changing only the source output changes the derived
direct rule; the pass does not replace a supplied handler with fixed code. -/
example :
    retargetInputPremise? canaryDirectLocation canaryExact canaryDirect
        (canaryRule "left") !=
      retargetInputPremise? canaryDirectLocation canaryExact canaryDirect
        (canaryRule "right") := by
  decide

/-- Negative control: duplicated selected premises are outside the strict
transformation domain. -/
example :
    retargetInputPremise? canaryDirectLocation canaryExact canaryDirect
      (.expression
        [.symbol "exec", .expression [.symbol "08", .symbol "cursor"],
          .expression [.symbol ",", canarySelf, canaryExact, canaryExact],
          .expression
            [.symbol "O", .expression [.symbol "-", canaryExact]]]) = none := by
  rfl

/-- Negative control: a self-premise at another location is not a retargetable
ordinary rule surface. -/
example :
    retargetInputPremise? canaryDirectLocation canaryExact canaryDirect
      (.expression
        [.symbol "exec", .expression [.symbol "08", .symbol "cursor"],
          .expression
            [.symbol ",",
              .expression
                [.symbol "exec", .expression [.symbol "08", .symbol "other"],
                  .var "input", .var "output"],
              canaryExact],
          .expression
            [.symbol "O", .expression [.symbol "-", canaryExact]]]) = none := by
  rfl

/-- Negative control: a direct handler without the corresponding lookup
removal would leave a residual request and is rejected. -/
example :
    retargetInputPremise? canaryDirectLocation canaryExact canaryDirect
      (.expression
        [.symbol "exec", .expression [.symbol "08", .symbol "cursor"],
          .expression [.symbol ",", canarySelf, canaryExact],
          .expression [.symbol "O", .expression [.symbol "+", .symbol "result"]]]) =
      none := by
  rfl

/-- Negative control: duplicated lookup removals are ambiguous and rejected. -/
example :
    retargetInputPremise? canaryDirectLocation canaryExact canaryDirect
      (.expression
        [.symbol "exec", .expression [.symbol "08", .symbol "cursor"],
          .expression [.symbol ",", canarySelf, canaryExact],
          .expression
            [.symbol "O", .expression [.symbol "-", canaryExact],
              .expression [.symbol "-", canaryExact]]]) = none := by
  rfl

#print axioms replaceExactlyOne?_length
#print axioms replaceAt?_length
#print axioms build?_sourceRules
#print axioms buildSelected?_sourceRules
#print axioms buildSelectedStrict?_sourceRules
#print axioms buildSelected?_targetRules_length
#print axioms buildSelectedStrict?_targetRules_length
#print axioms build?_targetRules_length

end Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface
