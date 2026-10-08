import Mettapedia.GSLT.Parsing.ParserPackSelectedValue

/-!
# Transport of token-local ParserPack certificates

Native lexical and positive-guard witnesses use a normalized input slice.
This module transports the existing physically indexed certificate data and
replay judgment to its exact scalar occurrence in the full input. Every
production/action position and physical child slot remains unchanged.

Local EOF alone is insufficient: every EOF leaf must embed at the end of
the full input. Byte-offset coherence, native witness export, the source
binding of span tags, and completeness of a local forest remain separate
obligations. No parser or external-witness acceptance rule is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserPackSliceCertificate

open ClassAwareParserPackCorrespondence
open ClassAwareParserPackCertificate
open ClassAwarePackedForest (ProductionRef)
open ParserProfileSemantics (ParserProfileLayer)
open PresentationExprSemantics (CST)
open ParserPackSelectedValue
open LanguageDefSyntaxCompiler (CompiledRule)

/-- One exact bounded scalar slice of the immutable full input. -/
structure Slice (input : List Nat) where
  start : Nat
  stop : Nat
  ordered : start ≤ stop
  bounded : stop ≤ input.length

def Slice.input {full : List Nat} (slice : Slice full) : List Nat :=
  full.extract slice.start slice.stop

theorem Slice.length {full : List Nat} (slice : Slice full) :
    slice.input.length = slice.stop - slice.start := by
  simp only [Slice.input, List.extract_eq_take_drop, List.length_take,
    List.length_drop]
  have := slice.ordered
  have := slice.bounded
  omega

/-- Successful local lookup identifies the original occurrence; an invalid
local index cannot be repaired by reading beyond the declared slice. -/
theorem Slice.lookup {full : List Nat} (slice : Slice full)
    {cursor scalar : Nat} (found : slice.input[cursor]? = some scalar) :
    full[slice.start + cursor]? = some scalar := by
  simp only [Slice.input, List.extract_eq_take_drop,
    List.getElem?_take] at found
  split at found
  · simpa only [List.getElem?_drop] using found
  · contradiction

mutual
  def shiftCertificate (offset : Nat) : Certificate → Certificate
    | .lexical position matcher start stop =>
        .lexical position matcher (offset + start) (offset + stop)
    | .structural position start stop body =>
        .structural position (offset + start) (offset + stop)
          (shiftItems offset body)

  def shiftItems (offset : Nat) : ItemsCertificate → ItemsCertificate
    | .nil cursor => .nil (offset + cursor)
    | .terminal matcher start stop rest =>
        .terminal matcher (offset + start) (offset + stop)
          (shiftItems offset rest)
    | .nonterminal sort start stop head rest =>
        .nonterminal sort (offset + start) (offset + stop)
          (shiftCertificate offset head) (shiftItems offset rest)
end

mutual
  def shiftTree (offset : Nat) : CST → CST
    | .terminal scalars start stop =>
        .terminal scalars (offset + start) (offset + stop)
    | .node label start stop children =>
        .node label (offset + start) (offset + stop) (shiftTrees offset children)

  def shiftTrees (offset : Nat) : List CST → List CST
    | [] => []
    | first :: rest => shiftTree offset first :: shiftTrees offset rest
end

/-- EOF is checked at its global occurrence, including EOF nested in a
lexical certificate or a structural child. -/
def terminalEndSafe (offset fullLength : Nat)
    (matcher : TerminalMatcher) (cursor : Nat) : Bool :=
  match matcher with
  | .eof => decide (offset + cursor = fullLength)
  | _ => true

mutual
  def certificateEndSafe (offset fullLength : Nat) : Certificate → Bool
    | .lexical _ matcher start _ => terminalEndSafe offset fullLength matcher start
    | .structural _ _ _ body => itemsEndSafe offset fullLength body

  def itemsEndSafe (offset fullLength : Nat) : ItemsCertificate → Bool
    | .nil _ => true
    | .terminal matcher start _ rest =>
        terminalEndSafe offset fullLength matcher start &&
          itemsEndSafe offset fullLength rest
    | .nonterminal _ _ _ head rest =>
        certificateEndSafe offset fullLength head && itemsEndSafe offset fullLength rest
end

mutual
  /-- Redundant spans are checked without consulting adjacent nodes. -/
  def certificateWithin (limit : Nat) : Certificate → Bool
    | .lexical _ _ start stop => decide (start ≤ stop ∧ stop ≤ limit)
    | .structural _ start stop body =>
        decide (start ≤ stop ∧ stop ≤ limit) && itemsWithin limit body

  def itemsWithin (limit : Nat) : ItemsCertificate → Bool
    | .nil cursor => decide (cursor ≤ limit)
    | .terminal _ start stop rest =>
        decide (start ≤ stop ∧ stop ≤ limit) && itemsWithin limit rest
    | .nonterminal _ start stop head rest =>
        decide (start ≤ stop ∧ stop ≤ limit) &&
          certificateWithin limit head && itemsWithin limit rest
end

/-- This checks scalar embedding data. Parser replay remains the separate
authority for the supplied plan, physical identities, and cursor seams. -/
def checkedShift? (full : List Nat) (slice : Slice full)
    (certificate : Certificate) : Option Certificate :=
  if certificateWithin slice.input.length certificate &&
      certificateEndSafe slice.start full.length certificate then
    some (shiftCertificate slice.start certificate)
  else none

mutual
  def positions : Certificate → List ProductionRef
    | .lexical position _ _ _ => [.lexical position]
    | .structural position _ _ body => .structural position :: itemsPositions body

  def itemsPositions : ItemsCertificate → List ProductionRef
    | .nil _ => []
    | .terminal _ _ _ rest => itemsPositions rest
    | .nonterminal _ _ _ head rest => positions head ++ itemsPositions rest
end

mutual
  theorem positions_shift (offset : Nat) (certificate : Certificate) :
      positions (shiftCertificate offset certificate) = positions certificate := by
    cases certificate with
    | lexical => rfl
    | structural position start stop body =>
        simp only [shiftCertificate, positions, itemsPositions_shift]

  theorem itemsPositions_shift (offset : Nat) (certificate : ItemsCertificate) :
      itemsPositions (shiftItems offset certificate) = itemsPositions certificate := by
    cases certificate with
    | nil => rfl
    | terminal matcher start stop rest =>
        simpa only [shiftItems, itemsPositions] using itemsPositions_shift offset rest
    | nonterminal sort start stop head rest =>
        simp only [shiftItems, itemsPositions, positions_shift, itemsPositions_shift]
end

def shiftTerminal {full : List Nat} {profile : ParserProfileLayer}
    (slice : Slice full) {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile slice.input matcher start stop)
    (safe : terminalEndSafe slice.start full.length matcher start = true) :
    TerminalMatchesAt profile full matcher (slice.start + start) (slice.start + stop) := by
  cases matched with
  | any found =>
      simpa only [Nat.add_assoc] using TerminalMatchesAt.any (slice.lookup found)
  | eof atEnd =>
      exact .eof (of_decide_eq_true safe)
  | char found =>
      simpa only [Nat.add_assoc] using TerminalMatchesAt.char (slice.lookup found)
  | classMember found evidence =>
      simpa only [Nat.add_assoc] using
        TerminalMatchesAt.classMember (slice.lookup found) evidence

theorem shiftTerminal_cst {full : List Nat} {profile : ParserProfileLayer}
    (slice : Slice full) {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile slice.input matcher start stop)
    (safe : terminalEndSafe slice.start full.length matcher start = true) :
    (shiftTerminal slice matched safe).cst = shiftTrees slice.start matched.cst := by
  cases matched <;>
    simp [shiftTerminal, TerminalMatchesAt.cst, shiftTrees, shiftTree, Nat.add_assoc]

def shiftTerminalCST {full : List Nat} {profile : ParserProfileLayer}
    (slice : Slice full) {matcher : TerminalMatcher} {start stop : Nat} {children : List CST}
    (matched : CSTTerminalMatchesAt profile slice.input matcher start stop children)
    (safe : terminalEndSafe slice.start full.length matcher start = true) :
    CSTTerminalMatchesAt profile full matcher
      (slice.start + start) (slice.start + stop) (shiftTrees slice.start children) := by
  rcases matched with ⟨derivation, rfl⟩
  exact ⟨shiftTerminal slice derivation safe, shiftTerminal_cst slice derivation safe⟩

theorem terminalValue_shift {full : List Nat} {profile : ParserProfileLayer}
    (slice : Slice full) {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile slice.input matcher start stop)
    (safe : terminalEndSafe slice.start full.length matcher start = true) :
    terminalValue? full matcher (slice.start + start) (slice.start + stop) =
      terminalValue? slice.input matcher start stop := by
  cases matched with
  | any found =>
      simp [terminalValue?, Nat.add_assoc, found, slice.lookup found]
  | eof atEnd =>
      have globalEnd : slice.start + _ = full.length := of_decide_eq_true safe
      have endInput : slice.start + slice.input.length = full.length := by
        simpa only [atEnd] using globalEnd
      simp [terminalValue?, atEnd, endInput]
  | char found =>
      simp [terminalValue?, Nat.add_assoc, found, slice.lookup found]
  | classMember found evidence =>
      simp [terminalValue?, Nat.add_assoc, found, slice.lookup found]

mutual
  /-- Reconstruct the same exact physical derivation at its full-input span. -/
  def shiftReplay {full : List Nat} {profile : ParserProfileLayer}
      {plan : CompiledParserPackPlan} (slice : Slice full)
      {certificate : Certificate} {sort : String} {start stop : Nat} {tree : CST}
      : Replays profile plan slice.input certificate sort start stop tree →
      certificateEndSafe slice.start full.length certificate = true →
      Replays profile plan full (shiftCertificate slice.start certificate) sort
        (slice.start + start) (slice.start + stop) (shiftTree slice.start tree)
    | .lexical position valid matcherExact sortExact labelExact matched, safe =>
        .lexical position valid matcherExact sortExact labelExact
          (shiftTerminalCST slice matched safe)
    | .structural position valid sortExact labelExact body, safe =>
        .structural position valid sortExact labelExact
          (shiftItemsReplay slice body safe)

  /-- Each cursor seam is translated by the same offset. Structural
  terminal slots remain physical slots even though they contribute no CST. -/
  def shiftItemsReplay {full : List Nat} {profile : ParserProfileLayer}
      {plan : CompiledParserPackPlan} (slice : Slice full)
      {certificate : ItemsCertificate} {items : List PackItem}
      {start stop : Nat} {trees : List CST}
      : ItemsReplays profile plan slice.input certificate items start stop trees →
      itemsEndSafe slice.start full.length certificate = true →
      ItemsReplays profile plan full (shiftItems slice.start certificate) items
        (slice.start + start) (slice.start + stop) (shiftTrees slice.start trees)
    | .nil, _ => .nil
    | .terminal matched rest, safe => by
        rcases Bool.and_eq_true_iff.mp safe with ⟨firstSafe, restSafe⟩
        exact .terminal (shiftTerminal slice matched firstSafe)
          (shiftItemsReplay slice rest restSafe)
    | .nonterminal head rest, safe => by
        rcases Bool.and_eq_true_iff.mp safe with ⟨headSafe, restSafe⟩
        exact .nonterminal (shiftReplay slice head headSafe)
          (shiftItemsReplay slice rest restSafe)
end

mutual
  /-- Fixed-head action execution commutes with exact scalar transport.
  An unavailable action remains unavailable at the same physical position. -/
  theorem certificateValue_shift {full : List Nat} {profile : ParserProfileLayer}
      {plan : CompiledParserPackPlan} (slice : Slice full) (actions : ActionTable)
      {certificate : Certificate} {sort : String} {start stop : Nat} {tree : CST}
      : Replays profile plan slice.input certificate sort start stop tree →
      certificateEndSafe slice.start full.length certificate = true →
      certificateValue? actions full (shiftCertificate slice.start certificate) =
        certificateValue? actions slice.input certificate
    | .lexical position valid matcherExact sortExact labelExact matched, safe => by
        simp only [shiftCertificate, certificateValue?]
        rw [terminalValue_shift slice matched.val safe]
    | .structural position valid sortExact labelExact body, safe => by
        simp only [shiftCertificate, certificateValue?]
        rw [itemsValues_shift slice actions body safe]

  theorem itemsValues_shift {full : List Nat} {profile : ParserProfileLayer}
      {plan : CompiledParserPackPlan} (slice : Slice full) (actions : ActionTable)
      {certificate : ItemsCertificate} {items : List PackItem}
      {start stop : Nat} {trees : List CST}
      : ItemsReplays profile plan slice.input certificate items start stop trees →
      itemsEndSafe slice.start full.length certificate = true →
      itemsValues? actions full (shiftItems slice.start certificate) =
        itemsValues? actions slice.input certificate
    | .nil, _ => rfl
    | .terminal matched rest, safe => by
        rcases Bool.and_eq_true_iff.mp safe with ⟨firstSafe, restSafe⟩
        simp only [shiftItems, itemsValues?]
        rw [terminalValue_shift slice matched firstSafe,
          itemsValues_shift slice actions rest restSafe]
    | .nonterminal head rest, safe => by
        rcases Bool.and_eq_true_iff.mp safe with ⟨headSafe, restSafe⟩
        simp only [shiftItems, itemsValues?]
        rw [certificateValue_shift slice actions head headSafe,
          itemsValues_shift slice actions rest restSafe]
end

theorem checkedShift_sound {full : List Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} (slice : Slice full)
    {certificate shifted : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (replay : Replays profile plan slice.input certificate sort start stop tree)
    (accepted : checkedShift? full slice certificate = some shifted) :
    shifted = shiftCertificate slice.start certificate ∧
      positions shifted = positions certificate ∧
      Nonempty (Replays profile plan full shifted sort
        (slice.start + start) (slice.start + stop) (shiftTree slice.start tree)) := by
  unfold checkedShift? at accepted
  split at accepted
  · rename_i safe
    have exactCertificate := Option.some.inj accepted
    subst shifted
    exact ⟨rfl, positions_shift _ _, ⟨shiftReplay slice replay (Bool.and_eq_true_iff.mp safe).2⟩⟩
  · contradiction

theorem checkedShift_value {full : List Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} (slice : Slice full) (actions : ActionTable)
    {certificate shifted : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (replay : Replays profile plan slice.input certificate sort start stop tree)
    (accepted : checkedShift? full slice certificate = some shifted) :
    certificateValue? actions full shifted = certificateValue? actions slice.input certificate := by
  unfold checkedShift? at accepted
  split at accepted
  · rename_i safe
    have exactCertificate := Option.some.inj accepted
    subst shifted
    exact certificateValue_shift slice actions replay (Bool.and_eq_true_iff.mp safe).2
  · contradiction

/-- Scalar transport composes with the existing source-plan reflection.
Exact source/plan agreement is retained as its separate, explicit premise. -/
theorem checkedShift_source {full : List Nat} {profile : ParserProfileLayer}
    {literalScalars? : String → Option (List Nat)} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} (slice : Slice full)
    {certificate shifted : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (agreement : ParserPackPlanAgreement literalScalars? profile rules plan)
    (replay : Replays profile plan slice.input certificate sort start stop tree)
    (accepted : checkedShift? full slice certificate = some shifted) :
    Nonempty (SourcePlanDerivesAt literalScalars? profile rules full sort
      (slice.start + start) (slice.start + stop) (shiftTree slice.start tree)) := by
  obtain ⟨_, _, ⟨shiftedReplay⟩⟩ := checkedShift_sound slice replay accepted
  exact ⟨(sourcePlanDerivationEquiv (input := full) agreement sort _ _ _).symm
    shiftedReplay.derivation⟩

/-- Every local occurrence is retained, including equal-valued alternatives.
This transports the catalogue; it does not assert full-input completeness. -/
def shiftCatalogue (offset : Nat) (rows : Catalogue) : Catalogue :=
  rows.map fun row => (shiftCertificate offset row.1, shiftTree offset row.2)

theorem shiftCatalogue_length (offset : Nat) (rows : Catalogue) :
    (shiftCatalogue offset rows).length = rows.length := by
  simp [shiftCatalogue]

/-- Selection sees the identical ordered action values after transport.
Local replay and every global EOF check remain explicit obligations. -/
theorem evaluateCatalogue_shift {full : List Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} (slice : Slice full) (actions : ActionTable)
    (rows : Catalogue)
    (replays : ∀ row ∈ rows, Nonempty (Replays profile plan slice.input row.1
      plan.lexical.startSort 0 slice.input.length row.2))
    (safe : ∀ row ∈ rows, certificateEndSafe slice.start full.length row.1 = true) :
    evaluateCatalogue? actions full (shiftCatalogue slice.start rows) =
      evaluateCatalogue? actions slice.input rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      obtain ⟨replay⟩ := replays row (by simp)
      have first := certificateValue_shift slice actions replay (safe row (by simp))
      have rest := ih (fun item member => replays item (by simp [member]))
        (fun item member => safe item (by simp [member]))
      simp only [shiftCatalogue, List.map_cons, evaluateCatalogue?] at rest ⊢
      rw [first, rest]

theorem selectCatalogue_shift {full : List Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} (slice : Slice full) (actions : ActionTable)
    (rows : Catalogue)
    (replays : ∀ row ∈ rows, Nonempty (Replays profile plan slice.input row.1
      plan.lexical.startSort 0 slice.input.length row.2))
    (safe : ∀ row ∈ rows, certificateEndSafe slice.start full.length row.1 = true) :
    selectCatalogue? actions full (shiftCatalogue slice.start rows) =
      selectCatalogue? actions slice.input rows := by
  unfold selectCatalogue?
  rw [evaluateCatalogue_shift slice actions rows replays safe]

/-! ## Calibration and corruption controls -/

private def controlProfile : ParserProfileLayer := {
  name := "SliceCertificate"
  startSort := "Value"
  classes := []
  states := []
}

private def controlPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "SliceCertificate"
    startSort := "Value"
    classes := []
    productions := [
      { label := "letter", resultSort := "Letter", matcher := .char 65, childSlots := [0] },
      { label := "letter", resultSort := "Letter", matcher := .char 65, childSlots := [0] }]
  }
  structural := [{
    label := "body"
    resultSort := "Value"
    items := [.nonterminal "Letter", .terminal (.char 66), .terminal .eof]
    childSlots := [0]
    source := { label := "body", category := "Value", params := [], syntaxPattern := [] }
  }]
}

private def controlCertificate : Certificate :=
  .structural 0 0 2
    (.nonterminal "Letter" 0 1 (.lexical 1 (.char 65) 0 1)
      (.terminal (.char 66) 1 2 (.terminal .eof 2 2 (.nil 2))))

private def controlTree : CST :=
  .node "body" 0 2 [.node "letter" 0 1 [.terminal [65] 0 1]]

private def controlSlice : Slice [90, 65, 66] := ⟨1, 3, by decide, by decide⟩

private def controlLocalReplay :
    Replays controlProfile controlPlan controlSlice.input controlCertificate "Value" 0 2
      controlTree :=
  .structural 0 (by decide) rfl rfl
    (.nonterminal
      (.lexical 1 (by decide) rfl rfl rfl ⟨.char (by decide), rfl⟩)
      (.terminal (.char (by decide)) (.terminal (.eof rfl) .nil)))

theorem control_checked_shift :
    checkedShift? [90, 65, 66] controlSlice controlCertificate =
      some (.structural 0 1 3
        (.nonterminal "Letter" 1 2 (.lexical 1 (.char 65) 1 2)
          (.terminal (.char 66) 2 3 (.terminal .eof 3 3 (.nil 3))))) := by decide

theorem control_replay_at_absolute_span :
    Nonempty (Replays controlProfile controlPlan [90, 65, 66]
      (shiftCertificate 1 controlCertificate) "Value" 1 3 (shiftTree 1 controlTree)) :=
  (checkedShift_sound controlSlice controlLocalReplay (by decide)).2.2

theorem control_physical_positions :
    positions (shiftCertificate 1 controlCertificate) = [.structural 0, .lexical 1] := by decide

/-- Equal row payloads stay distinct physical occurrences after transport. -/
theorem control_equal_payload_positions_remain_distinct :
    controlPlan.lexical.productions[0]? = controlPlan.lexical.productions[1]? ∧
      shiftCertificate 1 (.lexical 0 (.char 65) 0 1) ≠
        shiftCertificate 1 (.lexical 1 (.char 65) 0 1) := by decide

private def controlActions : ActionTable :=
  ⟨[.slot 0, .slot 0], [.apply "tuple" [.slot 0, .slot 1, .slot 2]]⟩

/-- The structural character and EOF contribute physical action slots even
though they are absent from the corresponding structural CST children. -/
theorem control_absolute_value :
    certificateValue? controlActions [90, 65, 66] (shiftCertificate 1 controlCertificate) =
      some (.expression [.symbol "tuple",
        .expression [.symbol "cp", .grounded (.int 65)],
        .expression [.symbol "cp", .grounded (.int 66)], .symbol "eof"]) := by decide

theorem control_value_transport :
    certificateValue? controlActions [90, 65, 66] (shiftCertificate 1 controlCertificate) =
      certificateValue? controlActions controlSlice.input controlCertificate :=
  checkedShift_value controlSlice controlActions controlLocalReplay (by decide)

private def controlAlternateCertificate : Certificate :=
  .structural 0 0 2
    (.nonterminal "Letter" 0 1 (.lexical 0 (.char 65) 0 1)
      (.terminal (.char 66) 1 2 (.terminal .eof 2 2 (.nil 2))))

private def controlAlternateReplay :
    Replays controlProfile controlPlan controlSlice.input controlAlternateCertificate
      "Value" 0 2 controlTree :=
  .structural 0 (by decide) rfl rfl
    (.nonterminal
      (.lexical 0 (by decide) rfl rfl rfl ⟨.char (by decide), rfl⟩)
      (.terminal (.char (by decide)) (.terminal (.eof rfl) .nil)))

private def controlRows : Catalogue :=
  [(controlCertificate, controlTree), (controlAlternateCertificate, controlTree)]

theorem control_catalogue_transport :
    selectCatalogue? controlActions [90, 65, 66] (shiftCatalogue 1 controlRows) =
      selectCatalogue? controlActions controlSlice.input controlRows := by
  apply selectCatalogue_shift (profile := controlProfile) (plan := controlPlan)
    controlSlice controlActions controlRows
  · intro row member
    simp only [controlRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨controlLocalReplay⟩
    · exact ⟨controlAlternateReplay⟩
  · intro row member
    simp only [controlRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide

theorem control_equal_values_preserve_multiplicity :
    (shiftCatalogue 1 controlRows).length = 2 ∧
      selectCatalogue? controlActions [90, 65, 66] (shiftCatalogue 1 controlRows) =
        certificateValue? controlActions controlSlice.input controlCertificate := by decide

private def conflictingActions : ActionTable :=
  ⟨[.apply "different" [], .slot 0], [.apply "tuple" [.slot 0, .slot 1, .slot 2]]⟩

theorem control_distinct_values_remain_ambiguous :
    selectCatalogue? conflictingActions controlSlice.input controlRows = none ∧
      selectCatalogue? conflictingActions [90, 65, 66]
        (shiftCatalogue 1 controlRows) = none := by decide

theorem control_missing_action_remains_unavailable :
    evaluateCatalogue? ⟨[.slot 0, .slot 0], []⟩ controlSlice.input controlRows = none ∧
      evaluateCatalogue? ⟨[.slot 0, .slot 0], []⟩ [90, 65, 66]
        (shiftCatalogue 1 controlRows) = none := by decide

private def nonsuffixSlice : Slice [90, 65, 66] := ⟨1, 2, by decide, by decide⟩

theorem control_nonsuffix_consuming_leaf :
    checkedShift? [90, 65, 66] nonsuffixSlice (.lexical 1 (.char 65) 0 1) =
      some (.lexical 1 (.char 65) 1 2) := by decide

private def wrongEndSlice : Slice [90, 65, 66, 67] := ⟨1, 3, by decide, by decide⟩

/-- The same local parse is valid, but its EOF is internal to the full input. -/
theorem control_local_eof_does_not_authorize_global_eof :
    Nonempty (Replays controlProfile controlPlan wrongEndSlice.input controlCertificate
      "Value" 0 2 controlTree) ∧
      checkedShift? [90, 65, 66, 67] wrongEndSlice controlCertificate = none :=
  ⟨⟨controlLocalReplay⟩, by decide⟩

theorem control_unchecked_wrong_eof_not_replayed :
    ¬ Nonempty (Replays controlProfile controlPlan [90, 65, 66, 67]
      (shiftCertificate 1 controlCertificate) "Value" 1 3 (shiftTree 1 controlTree)) := by
  rintro ⟨replay⟩
  cases replay with
  | structural position valid sortExact labelExact body =>
      cases body with
      | nonterminal head rest =>
          cases rest with
          | terminal matched rest =>
              cases rest with
              | terminal matched rest =>
                  cases matched with
                  | eof atEnd => simp at atEnd

private def wrongSeamCertificate : Certificate :=
  .structural 0 0 2
    (.nonterminal "Letter" 0 2 (.lexical 1 (.char 65) 0 1)
      (.terminal (.char 66) 1 2 (.terminal .eof 2 2 (.nil 2))))

/-- Bounds checking never repairs a nonterminal's claimed stop from its child. -/
theorem control_wrong_seam_not_replayed :
    checkedShift? [90, 65, 66] controlSlice wrongSeamCertificate =
      some (shiftCertificate 1 wrongSeamCertificate) ∧
      ¬ Nonempty (Replays controlProfile controlPlan controlSlice.input
        wrongSeamCertificate "Value" 0 2 controlTree) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨replay⟩
  cases replay with
  | structural position valid sortExact labelExact body =>
      cases body with
      | nonterminal head rest => cases head

theorem control_out_of_range_local_span_refused :
    checkedShift? [90, 65, 66] nonsuffixSlice (.lexical 1 (.char 65) 0 2) = none := by decide

theorem control_invalid_physical_position_not_replayed :
    ¬ Nonempty (Replays controlProfile controlPlan nonsuffixSlice.input
      (.lexical 2 (.char 65) 0 1) "Letter" 0 1
      (.node "letter" 0 1 [.terminal [65] 0 1])) := by
  rintro ⟨replay⟩
  cases replay with
  | lexical position valid matcherExact sortExact labelExact matched =>
      simp [controlPlan] at valid

#print axioms checkedShift_sound
#print axioms checkedShift_value
#print axioms checkedShift_source
#print axioms selectCatalogue_shift
#print axioms control_unchecked_wrong_eof_not_replayed

end Mettapedia.GSLT.Parsing.ParserPackSliceCertificate
