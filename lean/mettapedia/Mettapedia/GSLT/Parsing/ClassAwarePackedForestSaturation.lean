import Mettapedia.GSLT.Parsing.ClassAwarePackedForest
import Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration

/-!
# A strong saturation criterion for class-aware packed forests

Sound native-family decoding rules out invented parse alternatives, but it
does not rule out omissions.  This module proves that a deliberately strong
global rule-saturation premise suffices for ParserPack root completeness.

The criterion requires every lexical match and every locally enabled
structural family, including families irrelevant to the requested root.  It
therefore does not characterize the live GLL/GLR forest and must not be used
as its completeness gate.  The root-relative completeness construction is
still absent.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwarePackedForestSaturation

open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-- Every recursively selected family in an item-vector certificate is
present in the shared forest. -/
def ItemsUnfold (forest : Forest) (certificate : ItemsCertificate) : Prop :=
  ∀ family, family ∈ itemsFamilies certificate →
    family ∈ forest.families

/-- The immediate recursive premises of a complete certificate unfold.
Lexical rows have no recursive premise; structural rows carry the exact
item-vector obligation. -/
inductive ImmediateChildrenUnfold (forest : Forest) :
    Certificate → Prop where
  | lexical (production matcher start stop) :
      ImmediateChildrenUnfold forest
        (.lexical production matcher start stop)
  | structural (production start stop body)
      (bodyUnfolds : ItemsUnfold forest body) :
      ImmediateChildrenUnfold forest
        (.structural production start stop body)

theorem ImmediateChildrenUnfold.structural_body
    {forest : Forest} {production start stop : Nat}
    {body : ItemsCertificate}
    (immediate : ImmediateChildrenUnfold forest
      (.structural production start stop body)) :
    ItemsUnfold forest body := by
  cases immediate
  assumption

/-- Local least-fixed-point closure for a supplied ParserPack.  The root key
is kept separate from family saturation because exported-root policy is an
observable of the parser interface. -/
structure RuleSaturated
    (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) : Prop where
  rootPresent :
    ({ resultSort := plan.lexical.startSort, start := 0,
       stop := input.length } : NodeKey) ∈ forest.roots
  headFamilyPresent :
    ∀ {resultSort : String} {start stop : Nat} {tree : CST}
      (derivation : ParserPackDerivesAt profile plan input
        resultSort start stop tree),
      stop ≤ input.length →
      ImmediateChildrenUnfold forest
        (Certificate.ofDerivation derivation) →
      certificateFamily resultSort
        (Certificate.ofDerivation derivation) ∈ forest.families

/-- Local rule saturation unfolds every bounded semantic derivation and every
recursive item-vector certificate. -/
theorem RuleSaturated.derivation_unfolds
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (saturated : RuleSaturated forest profile plan input)
    {resultSort : String} {start stop : Nat} {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree)
    (stopBound : stop ≤ input.length) :
    Unfolds forest resultSort (Certificate.ofDerivation derivation) := by
  induction derivation using ParserPackDerivesAt.rec
    (motive_2 := fun _ _ itemStop _ itemDerivation =>
      itemStop ≤ input.length →
        ItemsUnfold forest
          (ItemsCertificate.ofDerivation itemDerivation)) with
  | lexical position valid matcherExact resultSortExact ruleLabelExact
      matched =>
      have headPresent := saturated.headFamilyPresent
        (.lexical position valid matcherExact resultSortExact ruleLabelExact
          matched) stopBound
        (.lexical position _ _ _)
      intro family member
      simp only [Certificate.ofDerivation, certificateFamilies,
        List.mem_singleton] at member
      subst family
      simpa only [Certificate.ofDerivation] using headPresent
  | structural position valid resultSortExact ruleLabelExact body bodyIH =>
      have bodyUnfolds := bodyIH stopBound
      have headPresent := saturated.headFamilyPresent
        (.structural position valid resultSortExact ruleLabelExact body)
        stopBound (.structural position _ _ _ bodyUnfolds)
      intro family member
      simp only [Certificate.ofDerivation, certificateFamilies,
        List.mem_cons] at member
      rcases member with rfl | nested
      · exact headPresent
      · exact bodyUnfolds family nested
  | nil =>
      intro _family member
      simp [ItemsCertificate.ofDerivation, itemsFamilies]
        at member
  | terminal matched rest restIH =>
      rename_i itemStopBound
      intro family member
      exact restIH itemStopBound family (by
        simpa [ItemsCertificate.ofDerivation, itemsFamilies] using member)
  | nonterminal head rest headIH restIH =>
      rename_i itemStopBound
      intro family member
      have middleBound : _ ≤ input.length :=
        Nat.le_trans (ParserPackItemsDeriveAt.start_le_stop rest)
          itemStopBound
      have headUnfolds := headIH middleBound
      have restUnfolds := restIH itemStopBound
      simp only [ItemsCertificate.ofDerivation, itemsFamilies,
        List.mem_append] at member
      rcases member with fromHead | fromRest
      · exact headUnfolds family fromHead
      · exact restUnfolds family fromRest

/-- Saturation plus the explicit root policy proves full ParserPack root
completeness without expanding the packed forest into a catalogue of CSTs. -/
theorem RuleSaturated.root_complete
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (saturated : RuleSaturated forest profile plan input) :
    ∀ tree : CST, Complete forest profile plan input
      plan.lexical.startSort 0 input.length tree := by
  intro tree derivation
  constructor
  · have keyExact :
        certificateKey plan.lexical.startSort
            (Certificate.ofDerivation derivation) =
          ({ resultSort := plan.lexical.startSort
             start := 0
             stop := input.length } : NodeKey) := by
      cases derivation <;> rfl
    rw [keyExact]
    exact saturated.rootPresent
  · exact saturated.derivation_unfolds derivation (Nat.le_refl _)

/-! ## Executable finite saturation checker -/

/-- A recognized node key is witnessed by at least one exact family.  The
list is canonicalized only to avoid repeated closure work. -/
def recognizedNodeKeys (forest : Forest) : List NodeKey :=
  (forest.families.map Family.parent).eraseDups

/-- One finite left-to-right item recognition result. -/
structure RecognizedItemsRow where
  stop : Nat
  children : List ChildRef
  deriving DecidableEq, Repr

/-- Enumerate all item-vector child-key combinations already recognized by a
finite forest.  Terminals are checked independently against the supplied
profile and input; nonterminals range over the forest's semantic node keys. -/
def enumerateRecognizedItems
    (forest : Forest) (profile : ParserProfileLayer) (input : List Nat) :
    List PackItem → Nat → List RecognizedItemsRow
  | [], cursor => [{ stop := cursor, children := [] }]
  | .terminal matcher :: rest, cursor =>
      match terminalMatch? profile input matcher cursor with
      | none => []
      | some (middle, _children) =>
          (enumerateRecognizedItems forest profile input rest middle).map
            fun tail => {
              stop := tail.stop
              children := .terminal matcher cursor middle :: tail.children
            }
  | .nonterminal resultSort :: rest, cursor =>
      (recognizedNodeKeys forest).filter (fun key =>
        key.resultSort == resultSort && key.start == cursor) |>.flatMap
          fun key =>
            (enumerateRecognizedItems forest profile input rest key.stop).map
              fun tail => {
                stop := tail.stop
                children := .node key :: tail.children
              }

/-- Every semantic terminal match ends inside the supplied scalar input. -/
theorem TerminalMatchesAt.stop_le_length
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile input matcher start stop) :
    stop ≤ input.length := by
  cases matched with
  | any lookup =>
      exact Nat.succ_le_iff.mpr
        (List.getElem?_eq_some_iff.mp lookup).1
  | eof atEnd => omega
  | char lookup =>
      exact Nat.succ_le_iff.mpr
        (List.getElem?_eq_some_iff.mp lookup).1
  | classMember lookup _evidence =>
      exact Nat.succ_le_iff.mpr
        (List.getElem?_eq_some_iff.mp lookup).1

/-- A certificate's head family is one of its recursive family occurrences. -/
theorem certificateFamily_mem_certificateFamilies
    (resultSort : String) (certificate : Certificate) :
    certificateFamily resultSort certificate ∈
      certificateFamilies resultSort certificate := by
  cases certificate <;> simp [certificateFamilies]

/-- Unfolding exposes the certificate's semantic node key to finite node-key
enumeration. -/
theorem certificateKey_mem_recognizedNodeKeys
    {forest : Forest} {resultSort : String} {certificate : Certificate}
    (unfolds : Unfolds forest resultSort certificate) :
    certificateKey resultSort certificate ∈ recognizedNodeKeys forest := by
  have familyMember : certificateFamily resultSort certificate ∈
      forest.families :=
    unfolds _ (certificateFamily_mem_certificateFamilies _ _)
  simp only [recognizedNodeKeys, List.mem_eraseDups, List.mem_map]
  refine ⟨certificateFamily resultSort certificate, familyMember, ?_⟩
  cases certificate <;> rfl

/-- The finite child-key enumerator contains the exact row of every semantic
item derivation whose recursive certificates already unfold in the forest. -/
def items_row_mem_enumerateRecognizedItems
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    {items : List PackItem} {start stop : Nat} {children : List CST} :
    (derivation : ParserPackItemsDeriveAt profile plan input
      items start stop children) →
    ItemsUnfold forest (ItemsCertificate.ofDerivation derivation) →
    ({ stop := stop,
       children := itemsChildRefs (ItemsCertificate.ofDerivation derivation) } :
      RecognizedItemsRow) ∈
      enumerateRecognizedItems forest profile input items start
  | .nil, _ => by
      simp [enumerateRecognizedItems, ItemsCertificate.ofDerivation,
        itemsChildRefs]
  | @ParserPackItemsDeriveAt.terminal _ _ _ matcher start middle items stop
      children matched rest, unfolds => by
      have terminalExact := terminalMatch?_complete
        (show CSTTerminalMatchesAt profile input _ _ _
          matched.cst from ⟨matched, rfl⟩)
      have restUnfolds : ItemsUnfold forest
          (ItemsCertificate.ofDerivation rest) := by
        intro family member
        exact unfolds family (by
          simpa [ItemsCertificate.ofDerivation, itemsFamilies] using member)
      have restMember := items_row_mem_enumerateRecognizedItems rest
        restUnfolds
      simp only [enumerateRecognizedItems, terminalExact]
      apply List.mem_map.mpr
      exact ⟨RecognizedItemsRow.mk stop
          (itemsChildRefs (ItemsCertificate.ofDerivation rest)),
        restMember, rfl⟩
  | @ParserPackItemsDeriveAt.nonterminal _ _ _ resultSort start middle tree
      items stop children head rest, unfolds => by
      have headUnfolds : Unfolds forest resultSort
          (Certificate.ofDerivation head) := by
        intro family member
        exact unfolds family (by
          simp only [ItemsCertificate.ofDerivation, itemsFamilies,
            List.mem_append]
          exact Or.inl member)
      have keyExact : certificateKey resultSort
          (Certificate.ofDerivation head) =
          NodeKey.mk resultSort start middle := by
        cases head <;> rfl
      have keyMember : NodeKey.mk resultSort start middle ∈
          recognizedNodeKeys forest := by
        rw [← keyExact]
        exact certificateKey_mem_recognizedNodeKeys headUnfolds
      have restUnfolds : ItemsUnfold forest
          (ItemsCertificate.ofDerivation rest) := by
        intro family member
        exact unfolds family (by
          simp only [ItemsCertificate.ofDerivation, itemsFamilies,
            List.mem_append]
          exact Or.inr member)
      have restMember := items_row_mem_enumerateRecognizedItems rest
        restUnfolds
      apply List.mem_flatMap.mpr
      refine ⟨NodeKey.mk resultSort start middle, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨keyMember, by
          simp⟩
      · apply List.mem_map.mpr
        refine ⟨RecognizedItemsRow.mk stop
            (itemsChildRefs (ItemsCertificate.ofDerivation rest)),
          restMember, ?_⟩
        simp only [ItemsCertificate.ofDerivation, itemsChildRefs]

/-- Exact lexical families demanded by the supplied plan and scalar input. -/
def expectedLexicalFamilies
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : List Family :=
  (List.finRange plan.lexical.productions.length).flatMap fun position =>
    let production := plan.lexical.productions.get position
    (List.range (input.length + 1)).filterMap fun start =>
      match terminalMatch? profile input production.matcher start with
      | none => none
      | some (stop, _children) => some {
          parent := ⟨production.resultSort, start, stop⟩
          production := .lexical position.val
          children := [.terminal production.matcher start stop]
        }

/-- Exact structural families demanded by every recognized child-key
combination of the supplied plan and forest. -/
def expectedStructuralFamilies
    (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) : List Family :=
  (List.finRange plan.structural.length).flatMap fun position =>
    let production := plan.structural.get position
    (List.range (input.length + 1)).flatMap fun start =>
      (enumerateRecognizedItems forest profile input production.items start).map
        fun body => {
          parent := ⟨production.resultSort, start, body.stop⟩
          production := .structural position.val
          children := body.children
        }

/-- Finite local saturation gate.  It checks the root policy, every lexical
seed, and every structural consequence over the currently recognized shared
node keys. -/
def validateRuleSaturation
    (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) : Bool :=
  decide (({ resultSort := plan.lexical.startSort
             start := 0
             stop := input.length } : NodeKey) ∈ forest.roots) &&
  ((expectedLexicalFamilies profile plan input).all fun family =>
    decide (family ∈ forest.families)) &&
  ((expectedStructuralFamilies forest profile plan input).all fun family =>
    decide (family ∈ forest.families))

/-- Every semantic lexical seed occurs in the finite expected-family list. -/
theorem lexical_family_mem_expected
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat}
    (position : Fin plan.lexical.productions.length)
    {start stop : Nat} {children : List CST}
    (matched : CSTTerminalMatchesAt profile input
      (plan.lexical.productions.get position).matcher start stop children) :
    ({ parent := ⟨(plan.lexical.productions.get position).resultSort,
          start, stop⟩
       production := .lexical position.val
       children := [.terminal
          (plan.lexical.productions.get position).matcher start stop] } :
      Family) ∈ expectedLexicalFamilies profile plan input := by
  have terminalExact := terminalMatch?_complete matched
  have startBound : start < input.length + 1 := by
    have startStop := TerminalMatchesAt.start_le_stop matched.1
    have stopBound := TerminalMatchesAt.stop_le_length matched.1
    omega
  unfold expectedLexicalFamilies
  apply List.mem_flatMap.mpr
  refine ⟨position, List.mem_finRange position, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨start, List.mem_range.mpr startBound, ?_⟩
  rw [terminalExact]

/-- Every structurally recognized child-key row occurs in the finite expected
family list. -/
theorem structural_family_mem_expected
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (position : Fin plan.structural.length)
    {start : Nat} (startBound : start ≤ input.length)
    (body : RecognizedItemsRow)
    (bodyMember : body ∈ enumerateRecognizedItems forest profile input
      (plan.structural.get position).items start) :
    ({ parent := ⟨(plan.structural.get position).resultSort,
          start, body.stop⟩
       production := .structural position.val
       children := body.children } : Family) ∈
      expectedStructuralFamilies forest profile plan input := by
  unfold expectedStructuralFamilies
  apply List.mem_flatMap.mpr
  refine ⟨position, List.mem_finRange position, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨start, List.mem_range.mpr (by omega), ?_⟩
  exact List.mem_map.mpr ⟨body, bodyMember, rfl⟩

/-- Successful finite saturation checking supplies the semantic local closure
used by `RuleSaturated.root_complete`. -/
theorem validateRuleSaturation_sound
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (accepted : validateRuleSaturation forest profile plan input = true) :
    RuleSaturated forest profile plan input := by
  simp only [validateRuleSaturation, Bool.and_eq_true_iff] at accepted
  rcases accepted with ⟨⟨rootAccepted, lexicalAccepted⟩,
    structuralAccepted⟩
  refine {
    rootPresent := of_decide_eq_true rootAccepted
    headFamilyPresent := ?_
  }
  intro resultSort start stop tree derivation stopBound immediate
  cases derivation with
  | lexical position valid matcherExact resultSortExact ruleLabelExact
      matched =>
      let occurrence : Fin plan.lexical.productions.length :=
        ⟨position, valid⟩
      rw [← matcherExact] at matched
      have expectedMember := lexical_family_mem_expected occurrence matched
      have present := (List.all_eq_true.mp lexicalAccepted) _ expectedMember
      have presentProp := of_decide_eq_true present
      simp only [occurrence] at presentProp
      rw [matcherExact, resultSortExact] at presentProp
      simpa [Certificate.ofDerivation, certificateFamily] using presentProp
  | structural position valid resultSortExact ruleLabelExact body =>
      have bodyUnfolds : ItemsUnfold forest
          (ItemsCertificate.ofDerivation body) :=
        immediate.structural_body
      let occurrence : Fin plan.structural.length := ⟨position, valid⟩
      let bodyRow : RecognizedItemsRow := {
        stop := stop
        children := itemsChildRefs (ItemsCertificate.ofDerivation body)
      }
      have bodyMember : bodyRow ∈
          enumerateRecognizedItems forest profile input
            (plan.structural.get occurrence).items start := by
        exact items_row_mem_enumerateRecognizedItems body bodyUnfolds
      have startBound : start ≤ input.length :=
        Nat.le_trans (ParserPackItemsDeriveAt.start_le_stop body) stopBound
      have expectedMember := structural_family_mem_expected occurrence
        startBound bodyRow bodyMember
      have present := (List.all_eq_true.mp structuralAccepted) _
        expectedMember
      have presentProp := of_decide_eq_true present
      have rowResultExact :
          (plan.structural.get occurrence).resultSort = resultSort := by
        simpa [occurrence] using resultSortExact
      rw [rowResultExact] at presentProp
      simpa [occurrence, bodyRow, Certificate.ofDerivation,
        certificateFamily] using presentProp

/-- Passing the deliberately strong global checker closes the backward
ParserPack coverage obligation for every whole-input CST. -/
theorem validateRuleSaturation_root_complete
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (accepted : validateRuleSaturation forest profile plan input = true) :
    ∀ tree : CST, Complete forest profile plan input
      plan.lexical.startSort 0 input.length tree :=
  (validateRuleSaturation_sound accepted).root_complete

/-! ## Saturation controls -/

private def saturationCanaryProfile : ParserProfileLayer := {
  name := "PackedForestSaturationCanary"
  startSort := "Value"
  classes := []
  states := []
}

private def saturationCanaryPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "PackedForestSaturationCanary"
    startSort := "Value"
    classes := []
    productions := [{
      label := "atom-a"
      resultSort := "Atom"
      matcher := .char 65
      childSlots := [0]
    }]
  }
  structural := [{
    label := "value-atom"
    resultSort := "Value"
    items := [.nonterminal "Atom"]
    childSlots := [0]
    source := {
      label := "value-atom"
      category := "Value"
      params := []
      syntaxPattern := []
    }
  }]
}

private def saturationCanaryLexical : Certificate :=
  .lexical 0 (.char 65) 0 1

private def saturationCanaryRoot : Certificate :=
  .structural 0 0 1
    (.nonterminal "Atom" 0 1 saturationCanaryLexical (.nil 1))

private def saturationCanaryForest : Forest :=
  pack [("Value", saturationCanaryRoot)]

private def saturationCanaryOmitted : Forest := {
  roots := saturationCanaryForest.roots
  families := [certificateFamily "Atom" saturationCanaryLexical]
}

/-- Positive control: lexical seeding followed by structural closure admits
the complete packed root certificate. -/
theorem structural_saturation_canary_accepts :
    validateRuleSaturation saturationCanaryForest saturationCanaryProfile
      saturationCanaryPlan [65] = true := by
  decide

/-- Negative control: retaining the recognized lexical child but omitting its
licensed structural parent fails local saturation. -/
theorem missing_structural_family_is_rejected :
    validateRuleSaturation saturationCanaryOmitted saturationCanaryProfile
      saturationCanaryPlan [65] = false := by
  decide

private def saturationCanaryMutation : CompiledParserPackPlan :=
  { saturationCanaryPlan with
    lexical := { saturationCanaryPlan.lexical with
      productions := saturationCanaryPlan.lexical.productions ++ [{
        label := "atom-a-second-occurrence"
        resultSort := "Atom"
        matcher := .char 65
        childSlots := [0]
      }]
    }
  }

/-- A new accepting physical production occurrence changes the required
proof fibre even though its matcher and result sort duplicate an old row. -/
theorem added_lexical_occurrence_is_not_silently_ignored :
    validateRuleSaturation saturationCanaryForest saturationCanaryProfile
      saturationCanaryMutation [65] = false := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwarePackedForestSaturation
