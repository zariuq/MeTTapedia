import Mettapedia.GSLT.Parsing.ClassAwareNativeForestParserCompleteness
import Mettapedia.GSLT.Parsing.FiniteHornSaturation

/-!
# Finite grounded charts for class-aware ParserPack plans

For one supplied parser profile, compiled plan, and finite scalar input, this
module grounds every lexical occurrence and every structural body split into
a finite Horn program.  Saturation computes a backend-independent reference
forest.  The reference is then pruned from whole-input roots, matching the
semantic shape exported by native GLL and GLR engines without requiring
irrelevant local families.

Physical lexical and structural table positions remain part of each family.
Consequently coverage detects a backend that retains one equal-looking
alternative while dropping another occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareGroundedChart

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestParserCompleteness
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.FiniteHornSaturation
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.Logic.LP

/-- A grounded structural body records its final cursor, ordered forest
children, and the symbol nodes that must already be derivable. -/
structure BodyPlan where
  stop : Nat
  children : List ChildRef
  premises : List NodeKey
  deriving DecidableEq, Repr

/-- One finite lexical or structural family instance. -/
structure GroundInstance where
  family : Family
  premises : List NodeKey
  deriving DecidableEq, Repr

def positionsFrom (input : List Nat) (start : Nat) : List Nat :=
  (List.range (input.length + 1)).filter (start ≤ ·)

theorem mem_positionsFrom_iff
    {input : List Nat} {start position : Nat} :
    position ∈ positionsFrom input start ↔
      start ≤ position ∧ position ≤ input.length := by
  simp [positionsFrom, and_comm]

/-- Ground a structural item vector without selecting proof trees.  A
nonterminal contributes its exact result-sort/span node as a Horn premise. -/
def groundItems (profile : ParserProfileLayer) (input : List Nat) :
    List PackItem → Nat → List BodyPlan
  | [], start => [{ stop := start, children := [], premises := [] }]
  | .terminal matcher :: items, start =>
      match terminalMatch? profile input matcher start with
      | none => []
      | some (middle, _) =>
          (groundItems profile input items middle).map fun rest =>
            { stop := rest.stop
              children := .terminal matcher start middle :: rest.children
              premises := rest.premises }
  | .nonterminal resultSort :: items, start =>
      (positionsFrom input start).flatMap fun middle =>
        (groundItems profile input items middle).map fun rest =>
          let key : NodeKey := ⟨resultSort, start, middle⟩
          { stop := rest.stop
            children := .node key :: rest.children
            premises := key :: rest.premises }

/-- Ground every accepting lexical production occurrence at every input
position. -/
def groundLexicalInstances
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : List GroundInstance :=
  (List.finRange plan.lexical.productions.length).flatMap fun position =>
    let production := plan.lexical.productions.get position
    (positionsFrom input 0).flatMap fun start =>
      match terminalMatch? profile input production.matcher start with
      | none => []
      | some (stop, _) =>
          [{ family :=
              { parent := ⟨production.resultSort, start, stop⟩
                production := .lexical position.val
                children := [.terminal production.matcher start stop] }
             premises := [] }]

/-- Ground every structural production occurrence and every finite body
split. -/
def groundStructuralInstances
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : List GroundInstance :=
  (List.finRange plan.structural.length).flatMap fun position =>
    let production := plan.structural.get position
    (positionsFrom input 0).flatMap fun start =>
      (groundItems profile input production.items start).map fun body =>
        { family :=
            { parent := ⟨production.resultSort, start, body.stop⟩
              production := .structural position.val
              children := body.children }
          premises := body.premises }

def groundInstances
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : List GroundInstance :=
  groundLexicalInstances profile plan input ++
    groundStructuralInstances profile plan input

inductive ChartAtom where
  | node (key : NodeKey)
  | family (value : Family)
  deriving DecidableEq, Repr

def familyRule (grounding : GroundInstance) : PropRule ChartAtom :=
  { premises := (grounding.premises.map ChartAtom.node).toFinset
    head := .family grounding.family }

def promotionRule (grounding : GroundInstance) : PropRule ChartAtom :=
  { premises := {.family grounding.family}
    head := .node grounding.family.parent }

def chartProgram
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : PropProgram ChartAtom :=
  let instances := (groundInstances profile plan input).toFinset
  instances.image familyRule ∪ instances.image promotionRule

def chart
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : Finset ChartAtom :=
  FiniteHornSaturation.saturateFast (chartProgram profile plan input) ∅

/-- The complete finite chart before root-relative pruning. -/
def chartForest
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : Forest :=
  let saturated := chart profile plan input
  let root : NodeKey := ⟨plan.lexical.startSort, 0, input.length⟩
  { roots := if .node root ∈ saturated then [root] else []
    families := (groundInstances profile plan input).filterMap fun grounding =>
      if .family grounding.family ∈ saturated then
        some grounding.family
      else none }

theorem groundInstance_enters_chart
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {grounding : GroundInstance}
    (groundingMember : grounding ∈ groundInstances profile plan input)
    (premisesPresent : ∀ key, key ∈ grounding.premises →
      ChartAtom.node key ∈ chart profile plan input) :
    ChartAtom.family grounding.family ∈ chart profile plan input := by
  change ChartAtom.family grounding.family ∈
    FiniteHornSaturation.saturateFast (chartProgram profile plan input) ∅
  apply FiniteHornSaturation.saturateFast_rule_closed
    (program := chartProgram profile plan input) (facts := ∅)
    (rule := familyRule grounding)
  · unfold chartProgram
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    exact ⟨grounding, by simpa using groundingMember, rfl⟩
  · intro atom atomMember
    change atom ∈ (grounding.premises.map ChartAtom.node).toFinset at atomMember
    simp only [List.mem_toFinset, List.mem_map] at atomMember
    obtain ⟨key, keyMember, rfl⟩ := atomMember
    exact premisesPresent key keyMember

theorem groundInstance_promotes
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {grounding : GroundInstance}
    (groundingMember : grounding ∈ groundInstances profile plan input)
    (familyPresent :
      ChartAtom.family grounding.family ∈ chart profile plan input) :
    ChartAtom.node grounding.family.parent ∈ chart profile plan input := by
  change ChartAtom.node grounding.family.parent ∈
    FiniteHornSaturation.saturateFast (chartProgram profile plan input) ∅
  apply FiniteHornSaturation.saturateFast_rule_closed
    (program := chartProgram profile plan input) (facts := ∅)
    (rule := promotionRule grounding)
  · unfold chartProgram
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨grounding, by simpa using groundingMember, rfl⟩
  · intro atom atomMember
    have atomEq : atom = ChartAtom.family grounding.family := by
      simpa [promotionRule] using atomMember
    subst atom
    exact familyPresent

theorem groundInstance_family_mem_chartForest
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {grounding : GroundInstance}
    (groundingMember : grounding ∈ groundInstances profile plan input)
    (familyPresent :
      ChartAtom.family grounding.family ∈ chart profile plan input) :
    grounding.family ∈ (chartForest profile plan input).families := by
  simp only [chartForest, List.mem_filterMap]
  refine ⟨grounding, groundingMember, ?_⟩
  rw [if_pos familyPresent]

theorem TerminalMatchesAt.stop_le_length
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile input matcher start stop) :
    stop ≤ input.length := by
  cases matched with
  | any lookup | char lookup | classMember lookup _ =>
      exact (List.getElem?_eq_some_iff.mp lookup).choose
  | eof atEnd => simp [atEnd]

def terminalChildRef
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat}
    (_ : TerminalMatchesAt profile input matcher start stop) : ChildRef :=
  .terminal matcher start stop

def replayNodeKey
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {certificate : Certificate}
    {resultSort : String} {start stop : Nat} {tree : CST}
    (_ : Replays profile plan input certificate resultSort start stop tree) :
    NodeKey :=
  ⟨resultSort, start, stop⟩

theorem replayCertificateKey_eq
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {certificate : Certificate}
    {resultSort : String} {start stop : Nat} {tree : CST}
    (replay : Replays profile plan input certificate
      resultSort start stop tree) :
    certificateKey resultSort certificate = ⟨resultSort, start, stop⟩ := by
  cases replay <;> rfl

@[simp] theorem certificateKey_ofDerivation
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String} {start stop : Nat}
    {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree) :
    certificateKey resultSort (Certificate.ofDerivation derivation) =
      ⟨resultSort, start, stop⟩ :=
  replayCertificateKey_eq (Replays.ofDerivation derivation)

mutual
  theorem ParserPackDerivesAt.stop_le_length
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {resultSort : String} {start stop : Nat}
      {tree : CST}
      (derivation : ParserPackDerivesAt profile plan input
        resultSort start stop tree)
      (startBound : start ≤ input.length) :
      stop ≤ input.length := by
    cases derivation with
    | lexical _ _ _ _ _ matched =>
        exact TerminalMatchesAt.stop_le_length matched.1
    | structural _ _ _ _ body =>
        exact ParserPackItemsDeriveAt.stop_le_length body startBound

  theorem ParserPackItemsDeriveAt.stop_le_length
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {items : List PackItem} {start stop : Nat}
      {children : List CST}
      (derivation : ParserPackItemsDeriveAt profile plan input
        items start stop children)
      (startBound : start ≤ input.length) :
      stop ≤ input.length := by
    cases derivation with
    | nil => exact startBound
    | terminal matched rest =>
        exact ParserPackItemsDeriveAt.stop_le_length rest
          (TerminalMatchesAt.stop_le_length matched)
    | nonterminal head rest =>
        exact ParserPackItemsDeriveAt.stop_le_length rest
          (ParserPackDerivesAt.stop_le_length head startBound)
end

def familyChildNodes (family : Family) : List NodeKey :=
  family.children.filterMap fun child =>
    match child with
    | .terminal _ _ _ => none
    | .node key => some key

def reachabilityRule (parent child : NodeKey) : PropRule NodeKey :=
  { premises := {parent}, head := child }

def reachabilityProgram (forest : Forest) : PropProgram NodeKey :=
  (forest.families.flatMap fun family =>
    (familyChildNodes family).map
      (reachabilityRule family.parent)).toFinset

def reachableNodes (forest : Forest) : Finset NodeKey :=
  FiniteHornSaturation.saturateFast
    (reachabilityProgram forest) forest.roots.toFinset

/-- Discard families that cannot occur beneath an exported root.  This is the
semantic shape of CeTTa's neutral GLL/GLR forest export. -/
def rootReachableForest (forest : Forest) : Forest :=
  { roots := forest.roots
    families := forest.families.filter
      fun family => family.parent ∈ reachableNodes forest }

theorem root_mem_reachableNodes
    {forest : Forest} {root : NodeKey}
    (member : root ∈ forest.roots) :
    root ∈ reachableNodes forest := by
  apply FiniteHornSaturation.saturateFast_contains_facts
    (program := reachabilityProgram forest) (facts := forest.roots.toFinset)
  simpa using member

theorem child_mem_reachableNodes
    {forest : Forest} {family : Family} {child : NodeKey}
    (familyMember : family ∈ forest.families)
    (parentReachable : family.parent ∈ reachableNodes forest)
    (childMember : child ∈ familyChildNodes family) :
    child ∈ reachableNodes forest := by
  apply FiniteHornSaturation.saturateFast_rule_closed
    (program := reachabilityProgram forest) (facts := forest.roots.toFinset)
    (rule := reachabilityRule family.parent child)
  · unfold reachabilityProgram
    simp only [List.mem_toFinset]
    apply List.mem_flatMap.mpr
    refine ⟨family, familyMember, ?_⟩
    exact List.mem_map.mpr ⟨child, childMember, rfl⟩
  · intro premise premiseMember
    have premiseEq : premise = family.parent := by
      simpa [reachabilityRule] using premiseMember
    subst premise
    exact parentReachable

mutual
  def CertificateLinked : Certificate → Prop
    | .lexical _ _ _ _ => True
    | .structural _ _ _ body => ItemsCertificateLinked body

  def ItemsCertificateLinked : ItemsCertificate → Prop
    | .nil _ => True
    | .terminal _ _ _ rest => ItemsCertificateLinked rest
    | .nonterminal resultSort start stop head rest =>
        certificateKey resultSort head = ⟨resultSort, start, stop⟩ ∧
          CertificateLinked head ∧ ItemsCertificateLinked rest
end

mutual
  theorem replayLinked
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : Certificate}
      {resultSort : String} {start stop : Nat} {tree : CST}
      (replay : Replays profile plan input certificate
        resultSort start stop tree) :
      CertificateLinked certificate := by
    cases replay with
    | lexical => trivial
    | structural _ _ _ _ body =>
        exact itemsReplayLinked body

  theorem itemsReplayLinked
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : ItemsCertificate}
      {items : List PackItem} {start stop : Nat} {children : List CST}
      (replay : ItemsReplays profile plan input certificate
        items start stop children) :
      ItemsCertificateLinked certificate := by
    cases replay with
    | nil => trivial
    | terminal matched rest =>
        simpa only [ItemsCertificateLinked] using itemsReplayLinked rest
    | nonterminal head rest =>
        exact ⟨replayCertificateKey_eq head, replayLinked head,
          itemsReplayLinked rest⟩
end

mutual
  theorem certificateFamilies_parent_reachable
      {forest : Forest} {certificate : Certificate}
      {resultSort : String}
      (linked : CertificateLinked certificate)
      (rootReachable :
        certificateKey resultSort certificate ∈ reachableNodes forest)
      (familiesPresent : ∀ family,
        family ∈ certificateFamilies resultSort certificate →
          family ∈ forest.families) :
      ∀ family, family ∈ certificateFamilies resultSort certificate →
        family.parent ∈ reachableNodes forest := by
    cases certificate with
    | lexical position matcher start stop =>
        intro family familyMember
        simp only [certificateFamilies, List.mem_singleton] at familyMember
        subst family
        simpa [certificateFamily, certificateKey] using rootReachable
    | structural position start stop body =>
        intro family familyMember
        simp only [certificateFamilies, List.mem_cons] at familyMember
        rcases familyMember with rootFamily | descendant
        · subst family
          simpa [certificateFamily, certificateKey] using rootReachable
        · let parent := certificateFamily resultSort
            (.structural position start stop body)
          have parentMember : parent ∈ forest.families := by
            apply familiesPresent parent
            simp [parent, certificateFamilies]
          exact itemsFamilies_parent_reachable
            (body := body) (parent := parent) linked parentMember
            (by simpa [parent, certificateFamily, certificateKey]
              using rootReachable)
            (by
              intro child childMember
              simpa [parent, certificateFamily] using childMember)
            (by
              intro childFamily childMember
              apply familiesPresent childFamily
              simp [certificateFamilies, childMember])
            family descendant

  theorem itemsFamilies_parent_reachable
      {forest : Forest} {body : ItemsCertificate} {parent : Family}
      (linked : ItemsCertificateLinked body)
      (parentMember : parent ∈ forest.families)
      (parentReachable : parent.parent ∈ reachableNodes forest)
      (childrenPresent : ∀ child, child ∈ itemsChildRefs body →
        child ∈ parent.children)
      (familiesPresent : ∀ family, family ∈ itemsFamilies body →
        family ∈ forest.families) :
      ∀ family, family ∈ itemsFamilies body →
        family.parent ∈ reachableNodes forest := by
    cases body with
    | nil cursor => simp [itemsFamilies]
    | terminal matcher start stop rest =>
        apply itemsFamilies_parent_reachable (body := rest)
          linked parentMember parentReachable
        · intro child childMember
          apply childrenPresent child
          simp only [itemsChildRefs, List.mem_cons]
          exact Or.inr childMember
        · intro family familyMember
          exact familiesPresent family
            (by simpa [itemsFamilies] using familyMember)
    | nonterminal resultSort start stop head rest =>
        rcases linked with ⟨headKey, headLinked, restLinked⟩
        intro family familyMember
        simp only [itemsFamilies, List.mem_append] at familyMember
        rcases familyMember with headMember | restMember
        · let childKey := certificateKey resultSort head
          have childRefMember :
              ChildRef.node childKey ∈ parent.children := by
            apply childrenPresent
            simp [itemsChildRefs, childKey, headKey]
          have childKeyMember : childKey ∈ familyChildNodes parent := by
            apply List.mem_filterMap.mpr
            exact ⟨.node childKey, childRefMember, rfl⟩
          have childReachable := child_mem_reachableNodes
            parentMember parentReachable childKeyMember
          exact certificateFamilies_parent_reachable headLinked childReachable
            (by
              intro headFamily headFamilyMember
              apply familiesPresent headFamily
              simp [itemsFamilies, headFamilyMember])
            family headMember
        · exact itemsFamilies_parent_reachable
            (body := rest) restLinked parentMember parentReachable
            (by
              intro child childMember
              apply childrenPresent child
              simp only [itemsChildRefs, List.mem_cons]
              exact Or.inr childMember)
            (by
              intro restFamily restFamilyMember
              apply familiesPresent restFamily
              simp [itemsFamilies, restFamilyMember])
            family restMember
end

theorem certificate_unfolds_rootReachable
    {forest : Forest} {certificate : Certificate} {resultSort : String}
    (linked : CertificateLinked certificate)
    (rootReachable :
      certificateKey resultSort certificate ∈ reachableNodes forest)
    (unfolds : Unfolds forest resultSort certificate) :
    Unfolds (rootReachableForest forest) resultSort certificate := by
  intro family familyMember
  simp only [rootReachableForest, List.mem_filter]
  exact ⟨unfolds family familyMember, by
    simpa using (certificateFamilies_parent_reachable linked
      rootReachable unfolds family familyMember)⟩

theorem rootUnfolds_rootReachable
    {forest : Forest} {certificate : Certificate} {resultSort : String}
    (linked : CertificateLinked certificate)
    (unfolds : RootUnfolds forest resultSort certificate) :
    RootUnfolds (rootReachableForest forest) resultSort certificate := by
  have rootReachable := root_mem_reachableNodes unfolds.1
  exact ⟨by simpa [rootReachableForest] using unfolds.1,
    certificate_unfolds_rootReachable linked rootReachable unfolds.2⟩

theorem rootReachable_complete
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (complete : RootParserComplete forest profile plan input) :
    RootParserComplete (rootReachableForest forest) profile plan input := by
  intro tree derivation
  exact rootUnfolds_rootReachable
    (replayLinked (Replays.ofDerivation derivation))
    (complete tree derivation)

/-- The practical independent reference contains exactly the chart families
that can occur below a whole-input root, while retaining every ParserPack
proof occurrence. -/
def referenceForest
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) : Forest :=
  rootReachableForest (chartForest profile plan input)

/-- Evidence extracted from one replayable structural body: its exact finite
grounding is present, its direct child nodes have entered the chart, and every
descendant certificate family is stored. -/
def ItemsChartWitness
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (certificate : ItemsCertificate)
    (items : List PackItem) (start stop : Nat) : Prop :=
  ∃ body : BodyPlan,
    body ∈ groundItems profile input items start ∧
    body.stop = stop ∧
    body.children = itemsChildRefs certificate ∧
    (∀ key, key ∈ body.premises →
      ChartAtom.node key ∈ chart profile plan input) ∧
    (∀ family, family ∈ itemsFamilies certificate →
      family ∈ (chartForest profile plan input).families)

mutual
  /-- Exact certificate replay enters the independent finite chart and all of
  its occurrence-preserving families are stored. -/
  theorem Replays.chart_unfolds
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : Certificate}
      {resultSort : String} {start stop : Nat} {tree : CST}
      (replay : Replays profile plan input certificate
        resultSort start stop tree)
      (startBound : start ≤ input.length) :
      ChartAtom.node ⟨resultSort, start, stop⟩ ∈
          chart profile plan input ∧
        Unfolds (chartForest profile plan input) resultSort certificate := by
    cases replay with
    | lexical position valid matcherExact resultSortExact _ matched =>
        let occurrence : Fin plan.lexical.productions.length :=
          ⟨position, valid⟩
        let production := plan.lexical.productions.get occurrence
        let grounding : GroundInstance :=
          { family :=
              { parent := ⟨resultSort, start, stop⟩
                production := .lexical position
                children := [.terminal production.matcher start stop] }
            premises := [] }
        have terminalCompleteProduction := terminalMatch?_complete matched
        rw [← matcherExact] at terminalCompleteProduction
        have groundingMember :
            grounding ∈ groundInstances profile plan input := by
          unfold groundInstances
          apply List.mem_append.mpr
          left
          unfold groundLexicalInstances
          apply List.mem_flatMap.mpr
          refine ⟨occurrence, by simp, ?_⟩
          apply List.mem_flatMap.mpr
          refine ⟨start,
            mem_positionsFrom_iff.mpr ⟨Nat.zero_le _, startBound⟩, ?_⟩
          dsimp [production, occurrence] at terminalCompleteProduction
          simp [grounding, production, occurrence, terminalCompleteProduction]
          exact resultSortExact.symm
        have familyPresent := groundInstance_enters_chart groundingMember
          (by simp [grounding])
        have nodePresent := groundInstance_promotes groundingMember familyPresent
        have familyStored :=
          groundInstance_family_mem_chartForest groundingMember familyPresent
        constructor
        · simpa [grounding] using nodePresent
        · intro family familyMember
          simp only [certificateFamilies, List.mem_singleton] at familyMember
          subst family
          simpa only [grounding, certificateFamily, production, occurrence,
            matcherExact] using familyStored
    | structural position valid resultSortExact _ body =>
        have bodyWitness := ItemsReplays.chart_witness body startBound
        obtain ⟨bodyPlan, bodyMember, bodyStop, bodyChildren,
            bodyPremises, bodyFamilies⟩ := bodyWitness
        let occurrence : Fin plan.structural.length := ⟨position, valid⟩
        let production := plan.structural.get occurrence
        let grounding : GroundInstance :=
          { family :=
              { parent := ⟨resultSort, start, stop⟩
                production := .structural position
                children := bodyPlan.children }
            premises := bodyPlan.premises }
        have groundingMember :
            grounding ∈ groundInstances profile plan input := by
          unfold groundInstances
          apply List.mem_append.mpr
          right
          unfold groundStructuralInstances
          apply List.mem_flatMap.mpr
          refine ⟨occurrence, by simp, ?_⟩
          apply List.mem_flatMap.mpr
          refine ⟨start,
            mem_positionsFrom_iff.mpr ⟨Nat.zero_le _, startBound⟩, ?_⟩
          apply List.mem_map.mpr
          refine ⟨bodyPlan, bodyMember, ?_⟩
          simp [grounding, occurrence, bodyStop]
          exact resultSortExact
        have familyPresent := groundInstance_enters_chart groundingMember
          bodyPremises
        have nodePresent := groundInstance_promotes groundingMember familyPresent
        have familyStored :=
          groundInstance_family_mem_chartForest groundingMember familyPresent
        constructor
        · simpa [grounding] using nodePresent
        · intro family familyMember
          simp only [certificateFamilies, List.mem_cons] at familyMember
          rcases familyMember with rootEq | descendant
          · subst family
            simpa [grounding, certificateFamily, bodyChildren] using familyStored
          · exact bodyFamilies family descendant

  theorem ItemsReplays.chart_witness
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : ItemsCertificate}
      {items : List PackItem} {start stop : Nat} {children : List CST}
      (replay : ItemsReplays profile plan input certificate
        items start stop children)
      (startBound : start ≤ input.length) :
      ItemsChartWitness profile plan input certificate items start stop := by
    cases replay with
    | nil =>
        refine ⟨{ stop := start, children := [], premises := [] },
          by simp [groundItems], rfl, rfl, ?_, ?_⟩
        · simp
        · simp [itemsFamilies]
    | terminal matched rest =>
        have middleBound := TerminalMatchesAt.stop_le_length matched
        have restWitness := ItemsReplays.chart_witness rest middleBound
        obtain ⟨restPlan, restMember, restStop, restChildren,
            restPremises, restFamilies⟩ := restWitness
        let bodyPlan : BodyPlan :=
          { stop := restPlan.stop
            children := terminalChildRef matched :: restPlan.children
            premises := restPlan.premises }
        have terminalComplete := terminalMatch?_complete
          (show CSTTerminalMatchesAt profile input _ _ _ matched.cst from
            ⟨matched, rfl⟩)
        refine ⟨bodyPlan, ?_, by simpa [bodyPlan] using restStop, ?_, ?_, ?_⟩
        · simp only [groundItems, terminalComplete]
          exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
        · simp [bodyPlan, terminalChildRef, itemsChildRefs, restChildren]
        · intro key keyMember
          exact restPremises key (by simpa [bodyPlan] using keyMember)
        · intro family familyMember
          exact restFamilies family
            (by simpa [itemsFamilies] using familyMember)
    | nonterminal head rest =>
        have headComplete := Replays.chart_unfolds head startBound
        have middleLower := ParserPackDerivesAt.start_le_stop head.derivation
        have middleBound :=
          ParserPackDerivesAt.stop_le_length head.derivation startBound
        have restWitness := ItemsReplays.chart_witness rest middleBound
        obtain ⟨restPlan, restMember, restStop, restChildren,
            restPremises, restFamilies⟩ := restWitness
        let key : NodeKey := replayNodeKey head
        let bodyPlan : BodyPlan :=
          { stop := restPlan.stop
            children := .node key :: restPlan.children
            premises := key :: restPlan.premises }
        refine ⟨bodyPlan, ?_, by simpa [bodyPlan] using restStop, ?_, ?_, ?_⟩
        · simp only [groundItems]
          apply List.mem_flatMap.mpr
          refine ⟨_, mem_positionsFrom_iff.mpr
            ⟨middleLower, middleBound⟩, ?_⟩
          exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
        · simp [bodyPlan, key, replayNodeKey, itemsChildRefs, restChildren]
        · intro premise premiseMember
          simp only [bodyPlan, List.mem_cons] at premiseMember
          rcases premiseMember with rfl | tailMember
          · simpa [key, replayNodeKey] using headComplete.1
          · exact restPremises premise tailMember
        · intro family familyMember
          simp only [itemsFamilies, List.mem_append] at familyMember
          rcases familyMember with headMember | restMember
          · exact headComplete.2 family headMember
          · exact restFamilies family restMember
end

/-- The unpruned finite chart contains every whole-input ParserPack proof
occurrence. -/
theorem chartForest_rootParserComplete
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) :
    RootParserComplete (chartForest profile plan input)
      profile plan input := by
  intro tree derivation
  have replay := Replays.ofDerivation derivation
  obtain ⟨rootPresent, unfolds⟩ :=
    Replays.chart_unfolds replay (Nat.zero_le _)
  constructor
  · simp [chartForest, rootPresent, replayCertificateKey_eq replay]
  · exact unfolds

theorem referenceForest_rootParserComplete
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) :
    RootParserComplete (referenceForest profile plan input)
      profile plan input :=
  rootReachable_complete (chartForest_rootParserComplete profile plan input)

/-! ## Executable root-relative coverage -/

/-- A backend retains every root and every physical family occurrence in an
independent reference forest.  Extra backend families are allowed because
exact native representation separately proves that they are meaningful, and
root completeness requires only the reference occurrences. -/
structure ForestCovers (reference backend : Forest) : Prop where
  roots : ∀ root, root ∈ reference.roots → root ∈ backend.roots
  families : ∀ family,
    family ∈ reference.families → family ∈ backend.families

def validateForestCovers (reference backend : Forest) : Bool :=
  reference.roots.all (· ∈ backend.roots) &&
    reference.families.all (· ∈ backend.families)

theorem validateForestCovers_sound
    {reference backend : Forest}
    (accepted : validateForestCovers reference backend = true) :
    ForestCovers reference backend := by
  simp only [validateForestCovers, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at accepted
  exact ⟨accepted.1, accepted.2⟩

theorem validateForestCovers_complete
    {reference backend : Forest}
    (covers : ForestCovers reference backend) :
    validateForestCovers reference backend = true := by
  simp only [validateForestCovers, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  exact ⟨covers.roots, covers.families⟩

theorem validateForestCovers_iff
    {reference backend : Forest} :
    validateForestCovers reference backend = true ↔
      ForestCovers reference backend :=
  ⟨validateForestCovers_sound, validateForestCovers_complete⟩

theorem rootUnfolds_of_covers
    {reference backend : Forest}
    (covers : ForestCovers reference backend)
    {resultSort : String} {certificate : Certificate}
    (unfolds : RootUnfolds reference resultSort certificate) :
    RootUnfolds backend resultSort certificate := by
  exact ⟨covers.roots _ unfolds.1, fun family familyMember =>
    covers.families family (unfolds.2 family familyMember)⟩

theorem rootParserComplete_of_covers
    {reference backend : Forest}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat}
    (covers : ForestCovers reference backend)
    (complete : RootParserComplete reference profile plan input) :
    RootParserComplete backend profile plan input := by
  intro tree derivation
  exact rootUnfolds_of_covers covers (complete tree derivation)

/-- Exact native self-representation plus independent root-relative chart
coverage supplies the full ParserPack backward lift. -/
def ParserCompleteRepresentation.ofReferenceCoverage
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {target : Forest}
    (represents :
      Represents view inventory.toTable profile view.codepoints target)
    (accepted : validateForestCovers
      (referenceForest profile plan view.codepoints) target = true) :
    ParserCompleteRepresentation view inventory profile plan target := {
  represents
  parserComplete := rootParserComplete_of_covers
    (validateForestCovers_sound accepted)
    (referenceForest_rootParserComplete profile plan view.codepoints)
}

/-- Resolve physical identities, prove exact meaning for every exported native
choice, and compare the decoded forest against the independent root-relative
chart.  Unlike global rule saturation, this accepts ordinary root-pruned GLL
and GLR forests while still rejecting any omitted live proof occurrence. -/
def validateResolvedReferenceCompleteRepresentation
    (snapshot : Snapshot) (view : ForestView)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  match snapshot.resolveInventory? plan with
  | none => false
  | some inventory =>
      validateExactFamilyRepresentation view inventory profile plan &&
        validateForestCovers (referenceForest profile plan view.codepoints)
          (decodedForestData view inventory profile)

theorem validateResolvedReferenceCompleteRepresentation_sound
    {snapshot : Snapshot} {view : ForestView}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (accepted : validateResolvedReferenceCompleteRepresentation snapshot view
      profile plan = true) :
    ∃ inventory : Inventory,
      snapshot.resolveInventory? plan = some inventory ∧
        ∃ inputs : RootedFamilyDecodingInputs view inventory profile plan,
          ParserCompleteRepresentation view inventory profile plan
            (decodedForest inputs.families
              (enumerateFamilyWitnesses view)) := by
  unfold validateResolvedReferenceCompleteRepresentation at accepted
  generalize resolved : snapshot.resolveInventory? plan = result at accepted
  cases result with
  | none => simp at accepted
  | some inventory =>
      rw [Bool.and_eq_true_iff] at accepted
      rcases validateExactFamilyRepresentation_sound accepted.1 with
        ⟨inputs, represents⟩
      have targetExact := decodedForest_eq_data inputs.families
      rw [← targetExact] at accepted
      exact ⟨inventory, rfl, inputs,
        ParserCompleteRepresentation.ofReferenceCoverage represents
          accepted.2⟩

/-! ### Positive and negative occurrence controls -/

private def coverageRoot : NodeKey := ⟨"Root", 0, 1⟩

private def coverageFamily (position : Nat) : Family := {
  parent := coverageRoot
  production := .lexical position
  children := [.terminal (.char 97) 0 1]
}

private def unreachableFamily : Family := {
  parent := ⟨"Unused", 0, 1⟩
  production := .lexical 2
  children := [.terminal (.char 97) 0 1]
}

private def coverageUnpruned : Forest := {
  roots := [coverageRoot]
  families := [coverageFamily 0, coverageFamily 1, unreachableFamily]
}

private def coverageReference : Forest := {
  roots := [coverageRoot]
  families := [coverageFamily 0, coverageFamily 1]
}

private def coverageBackendWithExtra : Forest := {
  roots := [coverageRoot]
  families := [unreachableFamily, coverageFamily 1, coverageFamily 0]
}

private def coverageBackendMissingOccurrence : Forest := {
  roots := [coverageRoot]
  families := [coverageFamily 0]
}

theorem root_pruning_discards_irrelevant_family :
    rootReachableForest coverageUnpruned = coverageReference := by
  decide

theorem extra_irrelevant_family_is_accepted :
    validateForestCovers coverageReference coverageBackendWithExtra = true := by
  decide

theorem missing_equal_looking_occurrence_is_rejected :
    validateForestCovers coverageReference
      coverageBackendMissingOccurrence = false := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwareGroundedChart
