import Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness

/-!
# Completeness of finite native-family enumeration

The proof-producing decoder returns dependent evidence.  Completeness is
therefore stated first at the computed child/family data, without requiring
equality between proof terms.  The decreasing physical prefix order will then
bound every semantic unfolding by the public node count.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-- Semantic terminal evidence is complete for its executable Boolean check. -/
theorem terminalSemanticValid_complete
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {value : TerminalValue}
    {start stop : Nat}
    (valueAgrees : TerminalValueAgrees input value start stop)
    (terminalMatches :
      TerminalMatchesAt profile input matcher start stop) :
    terminalSemanticValid profile input matcher value start stop = true := by
  cases terminalMatches <;> cases valueAgrees <;>
    simp_all [terminalSemanticValid, ParserProfileLayer.ClassEvidence]

/-- Every semantic leaf derivation is accepted by the executable child
decoder with exactly the same flattened children. -/
theorem decodeChildData?_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer}
    {nodeIndex : Nat} {children : List ChildRef}
    (derivation : ChildDerivation view inventory.toTable profile
      view.codepoints nodeIndex children) :
    decodeChildData? view inventory profile nodeIndex = some children := by
  cases derivation with
  | terminal nodeAt matcherAt valueAgrees terminalMatch =>
      have matcherLookup := matcherAt
      simp only [Inventory.toTable] at matcherLookup
      have semanticAccepted :=
        terminalSemanticValid_complete valueAgrees terminalMatch
      simp [decodeChildData?, nodeAt.1, matcherLookup, semanticAccepted]
  | epsilon nodeAt =>
      simp [decodeChildData?, nodeAt.1]
  | symbol nodeAt sortAt =>
      have sortLookup := sortAt
      simp only [Inventory.toTable] at sortLookup
      simp [decodeChildData?, nodeAt.1, sortLookup]

/-- Semantic binary factorization is complete for the executable geometry
check.  The factorization judgment already contains the pivot judgment. -/
theorem choiceGeometryValid_complete
    {view : ForestView} {choice : Choice}
    (factorization : FactorizationCoherent view choice) :
    choiceGeometryValid view choice = true := by
  rcases factorization with
    ⟨parent, child, parentAt, childAt, scalarPivot, bytePivot,
      scalarStop, byteStop, prefixEvidence⟩
  simp only [choiceGeometryValid, parentAt.1, childAt.1]
  cases prefixLookup : choice.prefixNode with
  | none =>
      simp only [prefixLookup] at prefixEvidence
      rcases prefixEvidence with ⟨scalarStart, byteStart⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨scalarPivot, bytePivot⟩, scalarStop⟩, byteStop⟩,
        scalarStart, byteStart⟩
  | some prefixIndex =>
      simp only [prefixLookup] at prefixEvidence
      rcases prefixEvidence with
        ⟨prefixNode, prefixAt, prefixScalarStart, prefixByteStart,
          prefixScalarStop, prefixByteStop⟩
      simp only [prefixAt.1, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨scalarPivot, bytePivot⟩, scalarStop⟩, byteStop⟩,
        ⟨⟨⟨prefixScalarStart, prefixByteStart⟩,
          prefixScalarStop⟩, prefixByteStop⟩⟩

/-- Every semantic factorization is accepted by the evidence-producing
geometry decoder. -/
theorem choiceGeometry?_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {choice : Choice}
    (factorization : FactorizationCoherent view choice) :
    ∃ evidence, choiceGeometry? inputs choice = some evidence := by
  have accepted := choiceGeometryValid_complete factorization
  refine ⟨choiceGeometryValid_sound inputs accepted, ?_⟩
  simp [choiceGeometry?, accepted]

private def PrefixComplete
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (production : Nat)
    (prefixNode : Option Nat) (children : List ChildRef)
    (_derivation : PrefixDerivation view inventory.toTable profile
      view.codepoints production prefixNode children) : Prop :=
  ∃ witness, decodePrefixData? view inventory profile production
    prefixNode witness = some children

private def ChoiceComplete
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (production : Nat)
    (choice : Choice) (children : List ChildRef)
    (_derivation : ChoiceChildren view inventory.toTable profile
      view.codepoints production choice children) : Prop :=
  ∃ witness, decodeChoiceData? view inventory profile production
    choice witness = some children

private theorem prefixEmptyComplete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {production : Nat} :
    PrefixComplete view inventory profile production none []
      PrefixDerivation.empty := by
  exact ⟨.empty, by simp [decodePrefixData?]⟩

private theorem prefixIntermediateComplete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {production : Nat}
    {nodeIndex dot start stop byteStart byteStop choiceBegin choiceCount : Nat}
    {choice : Choice} {children : List ChildRef}
    (nodeAt : NodeAt view nodeIndex {
      kind := .intermediate production dot
      scalarStart := start
      scalarStop := stop
      byteStart := byteStart
      byteStop := byteStop
      choiceBegin := choiceBegin
      choiceCount := choiceCount })
    (owned : OwnedChoice view nodeIndex choice)
    (body : ChoiceChildren view inventory.toTable profile view.codepoints
      production choice children)
    (bodyComplete :
      ChoiceComplete view inventory profile production choice children body) :
    PrefixComplete view inventory profile production (some nodeIndex) children
      (PrefixDerivation.intermediate nodeAt owned body) := by
  unfold PrefixComplete at *
  rcases owned with
    ⟨parent, localIndex, _parentLookup, _localLt,
      choiceLookup, parentExact⟩
  rcases bodyComplete with ⟨bodyWitness, bodyDecoded⟩
  refine ⟨.intermediate (parent.choiceBegin + localIndex)
    bodyWitness, ?_⟩
  simp only [decodePrefixData?, nodeAt.1]
  rw [choiceLookup]
  simp [parentExact, bodyDecoded]

private theorem choiceBinaryComplete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {production : Nat}
    {choice : Choice} {prefixChildren childChildren : List ChildRef}
    (productionExact : choice.productionIndex = production)
    (pivot : PivotCoherent view choice)
    (factorization : FactorizationCoherent view choice)
    (prefixResult : PrefixDerivation view inventory.toTable profile
      view.codepoints production choice.prefixNode prefixChildren)
    (childResult : ChildDerivation view inventory.toTable profile
      view.codepoints choice.childNode childChildren)
    (prefixComplete : PrefixComplete view inventory profile production
      choice.prefixNode prefixChildren prefixResult) :
    ChoiceComplete view inventory profile production choice
      (prefixChildren ++ childChildren)
      (ChoiceChildren.binary productionExact pivot factorization
        prefixResult childResult) := by
  unfold PrefixComplete at prefixComplete
  unfold ChoiceComplete
  rcases prefixComplete with ⟨prefixWitness, prefixDecoded⟩
  have childDecoded := decodeChildData?_complete childResult
  have geometryAccepted := choiceGeometryValid_complete factorization
  refine ⟨.binary prefixWitness, ?_⟩
  simp [decodeChoiceData?, productionExact, geometryAccepted,
    prefixDecoded, childDecoded]

/-- Every finite semantic prefix unfolding has a finite physical witness
accepted by the pure decoder. -/
theorem decodePrefixData?_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer}
    {production : Nat} {prefixNode : Option Nat}
    {children : List ChildRef}
    (derivation : PrefixDerivation view inventory.toTable profile
      view.codepoints production prefixNode children) :
    ∃ witness, decodePrefixData? view inventory profile production
      prefixNode witness = some children := by
  exact PrefixDerivation.rec
    (motive_1 := PrefixComplete view inventory profile production)
    (motive_2 := ChoiceComplete view inventory profile production)
    prefixEmptyComplete prefixIntermediateComplete choiceBinaryComplete
    derivation

/-- Every finite semantic binary-choice unfolding has a finite physical
witness accepted by the pure decoder. -/
theorem decodeChoiceData?_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer}
    {production : Nat} {choice : Choice}
    {children : List ChildRef}
    (derivation : ChoiceChildren view inventory.toTable profile
      view.codepoints production choice children) :
    ∃ witness, decodeChoiceData? view inventory profile production
      choice witness = some children := by
  exact ChoiceChildren.rec
    (motive_1 := PrefixComplete view inventory profile production)
    (motive_2 := ChoiceComplete view inventory profile production)
    prefixEmptyComplete prefixIntermediateComplete choiceBinaryComplete
    derivation

private theorem zipIdx_member_of_getElem?
    {Alpha : Type} {items : List Alpha} {index : Nat} {item : Alpha}
    (lookup : items[index]? = some item) :
    (item, index) ∈ items.zipIdx := by
  rw [List.getElem?_eq_some_iff] at lookup
  rw [List.mem_iff_getElem]
  refine ⟨index, by simpa using lookup.1, ?_⟩
  rw [List.getElem_zipIdx]
  simp [lookup.2]

private theorem getElem?_eq_some_of_zipIdx_member
    {Alpha : Type} {items : List Alpha} {index : Nat} {item : Alpha}
    (member : (item, index) ∈ items.zipIdx) :
    items[index]? = some item := by
  have located := List.exists_mem_zipIdx'.mp
    (show ∃ entry ∈ items.zipIdx, entry = (item, index) from
      ⟨_, member, rfl⟩)
  obtain ⟨foundIndex, foundBound, pairExact⟩ := located
  have indexExact : foundIndex = index :=
    (Prod.ext_iff.mp pairExact).2
  subst foundIndex
  rw [List.getElem?_eq_getElem foundBound]
  exact congrArg some (Prod.ext_iff.mp pairExact).1

private def PrefixEnumerated
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (production : Nat)
    (prefixNode : Option Nat) (children : List ChildRef)
    (_derivation : PrefixDerivation view inventory.toTable profile
      view.codepoints production prefixNode children) : Prop :=
  ∀ fuel,
    (∀ prefixIndex, prefixNode = some prefixIndex → prefixIndex < fuel) →
    ∃ witness, witness ∈ enumeratePrefixWitnesses view fuel prefixNode ∧
      decodePrefixData? view inventory profile production prefixNode witness =
        some children

private def ChoiceEnumerated
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (production : Nat)
    (choice : Choice) (children : List ChildRef)
    (_derivation : ChoiceChildren view inventory.toTable profile
      view.codepoints production choice children) : Prop :=
  ∀ fuel,
    (∀ prefixIndex, choice.prefixNode = some prefixIndex →
      prefixIndex < fuel) →
    ∃ prefixWitness,
      prefixWitness ∈ enumeratePrefixWitnesses view fuel
        choice.prefixNode ∧
      decodeChoiceData? view inventory profile production choice
        (.binary prefixWitness) = some children

private theorem prefixEmptyEnumerated
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {production : Nat} :
    PrefixEnumerated view inventory profile production none []
      PrefixDerivation.empty := by
  intro fuel _bound
  exact ⟨.empty, by simp [enumeratePrefixWitnesses],
    by simp [decodePrefixData?]⟩

private theorem choiceBinaryEnumerated
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {production : Nat}
    {choice : Choice} {prefixChildren childChildren : List ChildRef}
    (productionExact : choice.productionIndex = production)
    (pivot : PivotCoherent view choice)
    (factorization : FactorizationCoherent view choice)
    (prefixResult : PrefixDerivation view inventory.toTable profile
      view.codepoints production choice.prefixNode prefixChildren)
    (childResult : ChildDerivation view inventory.toTable profile
      view.codepoints choice.childNode childChildren)
    (prefixComplete : PrefixEnumerated view inventory profile production
      choice.prefixNode prefixChildren prefixResult) :
    ChoiceEnumerated view inventory profile production choice
      (prefixChildren ++ childChildren)
      (ChoiceChildren.binary productionExact pivot factorization
        prefixResult childResult) := by
  unfold PrefixEnumerated at prefixComplete
  unfold ChoiceEnumerated
  intro fuel prefixBound
  rcases prefixComplete fuel prefixBound with
    ⟨prefixWitness, prefixMember, prefixDecoded⟩
  have childDecoded := decodeChildData?_complete childResult
  have geometryAccepted := choiceGeometryValid_complete factorization
  exact ⟨prefixWitness, prefixMember,
    by
      simp [decodeChoiceData?, productionExact, geometryAccepted,
        prefixDecoded, childDecoded]⟩

private theorem prefixIntermediateEnumerated
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {production : Nat}
    (order : ∀ choice, choice ∈ view.choices →
      ∀ prefixIndex, choice.prefixNode = some prefixIndex →
        prefixIndex < choice.parent)
    {nodeIndex dot start stop byteStart byteStop choiceBegin choiceCount : Nat}
    {choice : Choice} {children : List ChildRef}
    (nodeAt : NodeAt view nodeIndex {
      kind := .intermediate production dot
      scalarStart := start
      scalarStop := stop
      byteStart := byteStart
      byteStop := byteStop
      choiceBegin := choiceBegin
      choiceCount := choiceCount })
    (owned : OwnedChoice view nodeIndex choice)
    (body : ChoiceChildren view inventory.toTable profile view.codepoints
      production choice children)
    (bodyComplete : ChoiceEnumerated view inventory profile production
      choice children body) :
    PrefixEnumerated view inventory profile production (some nodeIndex)
      children (PrefixDerivation.intermediate nodeAt owned body) := by
  unfold ChoiceEnumerated at bodyComplete
  unfold PrefixEnumerated
  intro fuel nodeBound
  have nodeLt : nodeIndex < fuel := nodeBound nodeIndex rfl
  cases fuel with
  | zero => omega
  | succ remainingFuel =>
      rcases owned with
        ⟨parent, localIndex, _parentLookup, _localLt,
          choiceLookup, parentExact⟩
      have choiceMember : choice ∈ view.choices :=
        list_member_of_getElem?_eq_some choiceLookup
      have bodyBound : ∀ prefixIndex,
          choice.prefixNode = some prefixIndex →
            prefixIndex < remainingFuel := by
        intro prefixIndex prefixExact
        have prefixLtParent := order choice choiceMember
          prefixIndex prefixExact
        rw [parentExact] at prefixLtParent
        omega
      rcases bodyComplete remainingFuel bodyBound with
        ⟨prefixWitness, prefixMember, bodyDecoded⟩
      let choiceIndex := parent.choiceBegin + localIndex
      let witness : PrefixWitness :=
        .intermediate choiceIndex (.binary prefixWitness)
      refine ⟨witness, ?_, ?_⟩
      · simp only [enumeratePrefixWitnesses]
        apply List.mem_flatMap.mpr
        refine ⟨(choice, choiceIndex), ?_, ?_⟩
        · exact zipIdx_member_of_getElem? choiceLookup
        · simp [choiceIndex, parentExact, prefixMember, witness]
      · simp only [witness, choiceIndex, decodePrefixData?, nodeAt.1]
        rw [choiceLookup]
        simp [parentExact, bodyDecoded]

/-- Under the executable decreasing-prefix profile, every finite semantic
prefix unfolding occurs in the fuel-bounded physical enumeration. -/
theorem enumeratePrefixWitnesses_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {production : Nat}
    (order : ∀ choice, choice ∈ view.choices →
      ∀ prefixIndex, choice.prefixNode = some prefixIndex →
        prefixIndex < choice.parent)
    {prefixNode : Option Nat} {children : List ChildRef}
    (derivation : PrefixDerivation view inventory.toTable profile
      view.codepoints production prefixNode children) :
    ∀ fuel,
      (∀ prefixIndex, prefixNode = some prefixIndex →
        prefixIndex < fuel) →
      ∃ witness,
        witness ∈ enumeratePrefixWitnesses view fuel prefixNode ∧
        decodePrefixData? view inventory profile production prefixNode
          witness = some children := by
  exact PrefixDerivation.rec
    (motive_1 := PrefixEnumerated view inventory profile production)
    (motive_2 := ChoiceEnumerated view inventory profile production)
    prefixEmptyEnumerated (prefixIntermediateEnumerated order)
    choiceBinaryEnumerated derivation

/-- Every semantic family derivation has an occurrence-bearing physical
witness accepted by the pure family decoder. -/
theorem decodeFamilyData?_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer}
    {parentIndex : Nat} {choice : Choice} {family : Family}
    (derivation : FamilyDerivation view inventory.toTable profile
      view.codepoints parentIndex choice family) :
    ∃ witness, witness.parentIndex = parentIndex ∧
      witness.choiceIndex < view.choices.length ∧
      decodeFamilyData? view inventory profile witness =
        some (choice, family) := by
  cases derivation with
  | symbol parentAt owned sortAt productionAt body =>
      rcases owned with
        ⟨parent, localIndex, _parentLookup, _localLt,
          choiceLookup, parentExact⟩
      rcases decodeChoiceData?_complete body with
        ⟨bodyWitness, bodyDecoded⟩
      have sortLookup := sortAt
      simp only [Inventory.toTable] at sortLookup
      have productionLookup := productionAt
      simp only [Inventory.toTable] at productionLookup
      have choiceIndexEvidence := choiceLookup
      rw [List.getElem?_eq_some_iff] at choiceIndexEvidence
      have choiceIndexValid :
          parent.choiceBegin + localIndex < view.choices.length := by
        exact choiceIndexEvidence.1
      refine ⟨{
        parentIndex
        choiceIndex := parent.choiceBegin + localIndex
        body := bodyWitness
      }, rfl, choiceIndexValid, ?_⟩
      simp only [decodeFamilyData?, parentAt.1]
      rw [choiceLookup]
      simp [parentExact, sortLookup, productionLookup, bodyDecoded]

/-- Under the decreasing-prefix profile, every semantic family has a witness
in the canonical node-count-bounded enumeration. -/
theorem enumerateFamilyWitnesses_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer}
    (prefixOrder : validatePrefixIndexOrder view = true)
    {parentIndex : Nat} {choice : Choice} {family : Family}
    (derivation : FamilyDerivation view inventory.toTable profile
      view.codepoints parentIndex choice family) :
    ∃ witness, witness ∈ enumerateFamilyWitnesses view ∧
      decodeFamilyData? view inventory profile witness =
        some (choice, family) := by
  have order := validatePrefixIndexOrder_sound prefixOrder
  cases derivation with
  | symbol parentAt owned sortAt productionAt body =>
      rcases owned with
        ⟨parent, localIndex, _parentLookup, _localLt,
          choiceLookup, parentExact⟩
      have choiceMember : choice ∈ view.choices :=
        list_member_of_getElem?_eq_some choiceLookup
      have parentIndexEvidence := parentAt.1
      rw [List.getElem?_eq_some_iff] at parentIndexEvidence
      have prefixBound : ∀ prefixIndex,
          choice.prefixNode = some prefixIndex →
            prefixIndex < view.nodes.length := by
        intro prefixIndex prefixExact
        have prefixLtParent := order choice choiceMember
          prefixIndex prefixExact
        rw [parentExact] at prefixLtParent
        exact Nat.lt_trans prefixLtParent parentIndexEvidence.1
      cases body with
      | binary productionExact pivot factorization prefixResult childResult =>
          rename_i prefixChildren childChildren
          rcases enumeratePrefixWitnesses_complete order prefixResult
              view.nodes.length prefixBound with
            ⟨prefixWitness, prefixMember, prefixDecoded⟩
          have childDecoded := decodeChildData?_complete childResult
          have geometryAccepted := choiceGeometryValid_complete factorization
          have bodyDecoded : decodeChoiceData? view inventory profile
              choice.productionIndex choice (.binary prefixWitness) =
                some (prefixChildren ++ childChildren) := by
            simp [decodeChoiceData?, geometryAccepted,
              prefixDecoded, childDecoded]
          have sortLookup := sortAt
          simp only [Inventory.toTable] at sortLookup
          have productionLookup := productionAt
          simp only [Inventory.toTable] at productionLookup
          let choiceIndex := parent.choiceBegin + localIndex
          let witness : FamilyWitness := {
            parentIndex
            choiceIndex
            body := .binary prefixWitness
          }
          refine ⟨witness, ?_, ?_⟩
          · unfold enumerateFamilyWitnesses
            unfold enumerateFamilyWitnessesWithFuel
            apply List.mem_flatMap.mpr
            refine ⟨(_, parentIndex),
              zipIdx_member_of_getElem? parentAt.1, ?_⟩
            apply List.mem_flatMap.mpr
            refine ⟨(choice, choiceIndex), ?_, ?_⟩
            · exact zipIdx_member_of_getElem? choiceLookup
            · simp [choiceIndex, parentExact, prefixMember, witness]
          · simp only [witness, choiceIndex, decodeFamilyData?, parentAt.1]
            rw [choiceLookup]
            simp [parentExact, sortLookup, productionLookup, bodyDecoded]

/-! ## Executable global choice coverage -/

/-- Finite evidence that one physical choice occurrence is productive.
Symbol choices use a complete family witness; intermediate choices use the
finite prefix witness for their recursive left-hand side. -/
inductive ChoiceCoverageWitness where
  | symbol (family : FamilyWitness)
  | intermediate (prefixWitness : PrefixWitness)
  deriving DecidableEq, Repr

/-- The ordinary data recovered while checking productivity of one physical
choice occurrence.  This stays separate from its dependent semantic proof. -/
inductive ChoiceCoverageData where
  | symbol (family : Family)
  | intermediate (children : List ChildRef)
  deriving DecidableEq, Repr

/-- Canonical finite candidates for one choice.  The parent node class selects
the only witness form that can inhabit `ChoiceCovered`. -/
def enumerateChoiceCoverageWitnesses
    (view : ForestView) (choice : Choice) : List ChoiceCoverageWitness :=
  match view.nodes[choice.parent]? with
  | some { kind := .symbol _, .. } =>
      (enumerateFamilyWitnesses view).map .symbol
  | some { kind := .intermediate _ _, .. } =>
      (enumeratePrefixWitnesses view view.nodes.length choice.prefixNode).map
        .intermediate
  | _ => []

/-- Proof-free productivity check for one exact physical choice occurrence.
The occurrence index is checked explicitly so equal choice records at distinct
array positions cannot exchange evidence. -/
def decodeChoiceCoverageData?
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (choiceIndex : Nat) (choice : Choice) :
    ChoiceCoverageWitness → Option ChoiceCoverageData
  | .symbol witness =>
      match view.nodes[choice.parent]? with
      | some { kind := .symbol _, .. } =>
          if witness.parentIndex = choice.parent then
            if witness.choiceIndex = choiceIndex then
              match decodeFamilyData? view inventory profile witness with
              | some (decodedChoice, family) =>
                  if decodedChoice = choice then some (.symbol family)
                  else none
              | none => none
            else none
          else none
      | _ => none
  | .intermediate prefixWitness =>
      match view.nodes[choice.parent]? with
      | some { kind := .intermediate production _, .. } =>
          (decodeChoiceData? view inventory profile production choice
            (.binary prefixWitness)).map .intermediate
      | _ => none

/-- Boolean productivity of one exact choice occurrence. -/
def choiceOccurrenceCovered
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (choiceIndex : Nat)
    (choice : Choice) : Bool :=
  (enumerateChoiceCoverageWitnesses view choice).any fun witness =>
    (decodeChoiceCoverageData? view inventory profile choiceIndex choice
      witness).isSome

/-- Every physical choice occurrence has at least one finite semantic
unfolding.  This is the executable global condition absent from local family
witness checking. -/
def validateChoiceCoverage
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) : Bool :=
  view.choices.zipIdx.all fun (choice, choiceIndex) =>
    choiceOccurrenceCovered view inventory profile choiceIndex choice

/-- Successful executable productivity checking supplies the exact semantic
coverage judgment selected by the physical parent-node class. -/
theorem decodeChoiceCoverageData?_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (choiceIndex : Nat) (choice : Choice)
    (witness : ChoiceCoverageWitness) (data : ChoiceCoverageData)
    (decoded : decodeChoiceCoverageData? view inventory profile choiceIndex
      choice witness = some data) :
    ∃ parent, NodeAt view choice.parent parent ∧
      ChoiceCovered view inventory.toTable profile view.codepoints
        choice.parent parent choice := by
  cases parentLookup : view.nodes[choice.parent]? with
  | none =>
      cases witness <;>
        simp [decodeChoiceCoverageData?, parentLookup] at decoded
  | some parent =>
      refine ⟨parent, nodeAtOfLookup inputs parentLookup, ?_⟩
      rcases parent with
        ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
          choiceBegin, choiceCount⟩
      cases kind with
      | terminal terminalId value =>
          cases witness <;>
            simp [decodeChoiceCoverageData?, parentLookup] at decoded
      | epsilon =>
          cases witness <;>
            simp [decodeChoiceCoverageData?, parentLookup] at decoded
      | symbol symbolId =>
          cases witness with
          | intermediate prefixWitness =>
              simp [decodeChoiceCoverageData?, parentLookup] at decoded
          | symbol familyWitness =>
              simp only [decodeChoiceCoverageData?, parentLookup] at decoded
              split at decoded
              next parentExact =>
                split at decoded
                next occurrenceExact =>
                  cases familyDecoded : decodeFamilyData? view inventory
                      profile familyWitness with
                  | none => simp [familyDecoded] at decoded
                  | some result =>
                      rcases result with ⟨decodedChoice, family⟩
                      rw [familyDecoded] at decoded
                      have choiceExact : decodedChoice = choice := by
                        by_contra different
                        simp [different] at decoded
                      subst choice
                      have derivation :=
                        (decodeFamilyData?_sound inputs familyWitness
                          familyDecoded).2
                      simp only [ChoiceCovered]
                      refine ⟨family, ⟨?_⟩⟩
                      simpa [parentExact] using derivation
                next => simp at decoded
              next => simp at decoded
      | intermediate production dot =>
          cases witness with
          | symbol familyWitness =>
              simp [decodeChoiceCoverageData?, parentLookup] at decoded
          | intermediate prefixWitness =>
              cases bodyDecoded : decodeChoiceData? view inventory profile
                  production choice (.binary prefixWitness) with
              | none =>
                  simp [decodeChoiceCoverageData?, parentLookup,
                    bodyDecoded] at decoded
              | some children =>
                  simp [decodeChoiceCoverageData?, parentLookup,
                    bodyDecoded] at decoded
                  subst data
                  simp only [ChoiceCovered]
                  exact ⟨children,
                    ⟨decodeChoiceData?_sound inputs bodyDecoded⟩⟩

theorem choiceOccurrenceCovered_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (choiceIndex : Nat) (choice : Choice)
    (accepted : choiceOccurrenceCovered view inventory profile choiceIndex
      choice = true) :
    ∃ parent, NodeAt view choice.parent parent ∧
      ChoiceCovered view inventory.toTable profile view.codepoints
        choice.parent parent choice := by
  rcases List.any_eq_true.mp accepted with ⟨witness, _member, present⟩
  rw [Option.isSome_iff_exists] at present
  rcases present with ⟨data, decoded⟩
  exact decodeChoiceCoverageData?_sound inputs choiceIndex choice
    witness data decoded

/-- Under the decreasing-prefix profile, every semantically productive exact
choice occurrence is found by the finite executable candidate search. -/
theorem choiceOccurrenceCovered_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (prefixOrder : validatePrefixIndexOrder view = true)
    (choiceIndex : Nat) (choice : Choice)
    (choiceLookup : view.choices[choiceIndex]? = some choice)
    (parent : Node) (parentLookup : view.nodes[choice.parent]? = some parent)
    (covered : ChoiceCovered view inventory.toTable profile view.codepoints
      choice.parent parent choice) :
    choiceOccurrenceCovered view inventory profile choiceIndex choice = true := by
  have order := validatePrefixIndexOrder_sound prefixOrder
  have choiceMember : choice ∈ view.choices :=
    list_member_of_getElem?_eq_some choiceLookup
  have parentIndexEvidence := parentLookup
  rw [List.getElem?_eq_some_iff] at parentIndexEvidence
  have prefixBound : ∀ prefixIndex,
      choice.prefixNode = some prefixIndex →
        prefixIndex < view.nodes.length := by
    intro prefixIndex prefixExact
    exact Nat.lt_trans (order choice choiceMember prefixIndex prefixExact)
      parentIndexEvidence.1
  rcases parent with
    ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
      choiceBegin, choiceCount⟩
  cases kind with
  | terminal terminalId value =>
      simp [ChoiceCovered] at covered
  | epsilon =>
      simp [ChoiceCovered] at covered
  | intermediate production dot =>
      rcases covered with ⟨children, ⟨body⟩⟩
      cases body with
      | binary productionExact pivot factorization prefixResult childResult =>
          rename_i prefixChildren childChildren
          rcases enumeratePrefixWitnesses_complete order prefixResult
              view.nodes.length prefixBound with
            ⟨prefixWitness, prefixMember, prefixDecoded⟩
          have childDecoded := decodeChildData?_complete childResult
          have geometryAccepted := choiceGeometryValid_complete factorization
          have bodyDecoded : decodeChoiceData? view inventory profile
              production choice (.binary prefixWitness) =
                some (prefixChildren ++ childChildren) := by
            simp [decodeChoiceData?, productionExact, geometryAccepted,
              prefixDecoded, childDecoded]
          apply List.any_eq_true.mpr
          refine ⟨.intermediate prefixWitness, ?_, ?_⟩
          · simp [enumerateChoiceCoverageWitnesses, parentLookup,
              prefixMember]
          · simp [decodeChoiceCoverageData?, parentLookup, bodyDecoded]
  | symbol symbolId =>
      rcases covered with ⟨family, ⟨derivation⟩⟩
      cases derivation with
      | symbol derivationParentAt owned sortAt productionAt body =>
          have parentAt := nodeAtOfLookup inputs parentLookup
          have parentExact := nodeAt_unique derivationParentAt parentAt
          cases parentExact
          cases body with
          | binary productionExact pivot factorization prefixResult childResult =>
              rename_i prefixChildren childChildren
              rcases enumeratePrefixWitnesses_complete order prefixResult
                  view.nodes.length prefixBound with
                ⟨prefixWitness, prefixMember, prefixDecoded⟩
              have childDecoded := decodeChildData?_complete childResult
              have geometryAccepted :=
                choiceGeometryValid_complete factorization
              have bodyDecoded : decodeChoiceData? view inventory profile
                  choice.productionIndex choice (.binary prefixWitness) =
                    some (prefixChildren ++ childChildren) := by
                simp [decodeChoiceData?, geometryAccepted,
                  prefixDecoded, childDecoded]
              have sortLookup := sortAt
              simp only [Inventory.toTable] at sortLookup
              have productionLookup := productionAt
              simp only [Inventory.toTable] at productionLookup
              let familyWitness : FamilyWitness := {
                parentIndex := choice.parent
                choiceIndex
                body := .binary prefixWitness
              }
              have familyDecodedExists : ∃ decodedFamily,
                  decodeFamilyData? view inventory profile familyWitness =
                    some (choice, decodedFamily) := by
                simp [familyWitness, decodeFamilyData?, parentLookup,
                  choiceLookup, sortLookup, productionLookup, bodyDecoded]
              rcases familyDecodedExists with
                ⟨decodedFamily, familyDecoded⟩
              have familyWitnessMember :
                  familyWitness ∈ enumerateFamilyWitnesses view := by
                unfold enumerateFamilyWitnesses
                unfold enumerateFamilyWitnessesWithFuel
                apply List.mem_flatMap.mpr
                refine ⟨(_, choice.parent),
                  zipIdx_member_of_getElem? parentLookup, ?_⟩
                apply List.mem_flatMap.mpr
                refine ⟨(choice, choiceIndex),
                  zipIdx_member_of_getElem? choiceLookup, ?_⟩
                simp [prefixMember, familyWitness]
              apply List.any_eq_true.mpr
              refine ⟨.symbol familyWitness, ?_, ?_⟩
              · simp [enumerateChoiceCoverageWitnesses, parentLookup,
                  familyWitnessMember]
              · simp [decodeChoiceCoverageData?, parentLookup,
                  familyWitness, familyDecoded]

/-- Global Boolean acceptance covers every exact physical choice occurrence. -/
theorem validateChoiceCoverage_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (accepted : validateChoiceCoverage view inventory profile = true) :
    ∀ (choiceIndex : Nat) (choice : Choice),
      view.choices[choiceIndex]? = some choice →
      ∃ parent, NodeAt view choice.parent parent ∧
        ChoiceCovered view inventory.toTable profile view.codepoints
          choice.parent parent choice := by
  intro choiceIndex choice choiceLookup
  have pairMember : (choice, choiceIndex) ∈ view.choices.zipIdx :=
    zipIdx_member_of_getElem? choiceLookup
  have covered := (List.all_eq_true.mp accepted)
    (choice, choiceIndex) pairMember
  exact choiceOccurrenceCovered_sound inputs choiceIndex choice covered

/-- The finite validator is complete for exact semantic choice coverage under
the same decreasing-prefix profile used by witness enumeration. -/
theorem validateChoiceCoverage_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (prefixOrder : validatePrefixIndexOrder view = true)
    (covered : ∀ (choiceIndex : Nat) (choice : Choice),
      view.choices[choiceIndex]? = some choice →
        ∃ parent, NodeAt view choice.parent parent ∧
          ChoiceCovered view inventory.toTable profile view.codepoints
            choice.parent parent choice) :
    validateChoiceCoverage view inventory profile = true := by
  apply List.all_eq_true.mpr
  rintro ⟨choice, choiceIndex⟩ pairMember
  have choiceLookup : view.choices[choiceIndex]? = some choice :=
    getElem?_eq_some_of_zipIdx_member pairMember
  rcases covered choiceIndex choice choiceLookup with
    ⟨parent, parentAt, semanticCoverage⟩
  exact choiceOccurrenceCovered_complete inputs prefixOrder choiceIndex
    choice choiceLookup parent parentAt.1 semanticCoverage

/-- On the admitted decreasing-prefix profile, executable all-choice
validation is equivalent to exact semantic productivity at every physical
occurrence. -/
theorem validateChoiceCoverage_iff
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (prefixOrder : validatePrefixIndexOrder view = true) :
    validateChoiceCoverage view inventory profile = true ↔
      ∀ (choiceIndex : Nat) (choice : Choice),
        view.choices[choiceIndex]? = some choice →
          ∃ parent, NodeAt view choice.parent parent ∧
            ChoiceCovered view inventory.toTable profile view.codepoints
              choice.parent parent choice :=
  ⟨validateChoiceCoverage_sound inputs,
    validateChoiceCoverage_complete inputs prefixOrder⟩

/-- The dependent family decoder has exactly the pure decoder's ordinary
choice/family observation. -/
theorem decodeFamily?_data
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witness : FamilyWitness) :
    (decodeFamily? inputs witness).map (fun result =>
      (result.1, result.2.2.1)) =
      decodeFamilyData? view inventory profile witness := by
  unfold decodeFamily?
  split
  next decoded =>
    change none = decodeFamilyData? view inventory profile witness
    exact decoded.symm
  next choice family decoded =>
    change some (choice, family) =
      decodeFamilyData? view inventory profile witness
    exact decoded.symm

/-- The first-class occurrence decoder preserves exactly the pure
choice/family observation. -/
theorem decodeFamilyOccurrence?_data
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witness : FamilyWitness) :
    (decodeFamilyOccurrence? inputs witness).map (fun occurrence =>
      (occurrence.choice, occurrence.family)) =
      decodeFamilyData? view inventory profile witness := by
  calc
    (decodeFamilyOccurrence? inputs witness).map (fun occurrence =>
        (occurrence.choice, occurrence.family)) =
      (decodeFamily? inputs witness).map (fun result =>
        (result.1, result.2.2.1)) := by
          cases decoded : decodeFamily? inputs witness with
          | none => simp [decodeFamilyOccurrence?, decoded]
          | some result =>
              rcases result with ⟨choice, ⟨ownedAt, ⟨family, derivation⟩⟩⟩
              simp [decodeFamilyOccurrence?, decoded]
    _ = decodeFamilyData? view inventory profile witness :=
      decodeFamily?_data inputs witness

/-- Pure family success is reflected by the occurrence-bearing public
decoder, with the same physical choice and semantic family data. -/
theorem decodeFamilyOccurrence?_complete
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witness : FamilyWitness) {choice : Choice} {family : Family}
    (decoded : decodeFamilyData? view inventory profile witness =
      some (choice, family)) :
    ∃ occurrence : DecodedFamilyOccurrence view inventory profile,
      decodeFamilyOccurrence? inputs witness = some occurrence ∧
      occurrence.choice = choice ∧ occurrence.family = family := by
  have mapped :
      (decodeFamilyOccurrence? inputs witness).map (fun occurrence =>
        (occurrence.choice, occurrence.family)) =
          some (choice, family) := by
    rw [decodeFamilyOccurrence?_data inputs witness]
    exact decoded
  rcases Option.map_eq_some_iff.mp mapped with
    ⟨occurrence, occurrenceDecoded, dataExact⟩
  exact ⟨occurrence, occurrenceDecoded,
    congrArg Prod.fst dataExact, congrArg Prod.snd dataExact⟩

/-- Any accepted witness present in a submitted finite list contributes its
exact semantic family to `decodedFamilies`. -/
theorem family_mem_decodedFamilies_of_witness
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {witness : FamilyWitness} {choice : Choice} {family : Family}
    {witnesses : List FamilyWitness}
    (decoded : decodeFamilyData? view inventory profile witness =
      some (choice, family))
    (member : witness ∈ witnesses) :
    family ∈ decodedFamilies inputs witnesses := by
  rcases decodeFamilyOccurrence?_complete inputs witness decoded with
    ⟨occurrence, occurrenceDecoded, _choiceExact, familyExact⟩
  rw [← familyExact]
  simp only [decodedFamilies, List.mem_eraseDups, List.mem_map]
  exact ⟨occurrence,
    List.mem_filterMap.mpr ⟨witness, member, occurrenceDecoded⟩, rfl⟩

/-- The canonical decoded-family list is complete for every finite semantic
family derivation under the decreasing-prefix profile. -/
theorem family_mem_decodedFamilies_of_derivation
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (prefixOrder : validatePrefixIndexOrder view = true)
    {parentIndex : Nat} {choice : Choice} {family : Family}
    (derivation : FamilyDerivation view inventory.toTable profile
      view.codepoints parentIndex choice family) :
    family ∈ decodedFamilies inputs (enumerateFamilyWitnesses view) := by
  rcases enumerateFamilyWitnesses_complete prefixOrder derivation with
    ⟨witness, witnessMember, decoded⟩
  exact family_mem_decodedFamilies_of_witness inputs decoded witnessMember

/-- Prefix-order termination and the executable all-choice check discharge
both global obligations for the canonical exhaustive family enumeration. -/
def exactFamilyCoverageOfValidation
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (prefixOrder : validatePrefixIndexOrder view = true)
    (choiceCoverage : validateChoiceCoverage view inventory profile = true) :
    ExactFamilyCoverage inputs (enumerateFamilyWitnesses view) := {
  familiesComplete := by
    intro family derivable
    rcases derivable with ⟨parentIndex, choice, ⟨derivation⟩⟩
    exact family_mem_decodedFamilies_of_derivation inputs prefixOrder derivation
  choicesCovered := by
    intro parentIndex parent choice parentAt owned
    rcases owned with
      ⟨owner, localIndex, _ownerLookup, _localValid,
        choiceLookup, parentExact⟩
    rcases validateChoiceCoverage_sound inputs choiceCoverage
        (owner.choiceBegin + localIndex) choice choiceLookup with
      ⟨decodedParent, decodedParentAt, covered⟩
    rw [parentExact] at decodedParentAt covered
    have parentNodeExact := nodeAt_unique decodedParentAt parentAt
    subst decodedParent
    exact covered
}

/-- One executable admission gate for the complete finite native-forest
representation.  Root/identity/terminal checks, decreasing prefix order, and
global choice productivity remain separately inspectable conjuncts. -/
def validateExactFamilyRepresentation
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  validateRootedFamilyDecodingInputs view inventory profile plan &&
    (validatePrefixIndexOrder view &&
      validateChoiceCoverage view inventory profile)

/-- Successful exhaustive validation constructs the full two-sided native
forest representation over the canonical decoded roots and families. -/
def validateExactFamilyRepresentation_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (accepted :
      validateExactFamilyRepresentation view inventory profile plan = true) :
    ∃ inputs : RootedFamilyDecodingInputs view inventory profile plan,
      Represents view inventory.toTable profile view.codepoints
        (decodedForest inputs.families (enumerateFamilyWitnesses view)) := by
  rw [validateExactFamilyRepresentation, Bool.and_eq_true_iff,
    Bool.and_eq_true_iff] at accepted
  let inputs := validateRootedFamilyDecodingInputs_sound accepted.1
  refine ⟨inputs, inputs.represents (enumerateFamilyWitnesses view) ?_⟩
  exact exactFamilyCoverageOfValidation inputs.families
    accepted.2.1 accepted.2.2

/-- A convenient instance-indexed form used by executable canaries and native
backend adapters without exposing implicit presentation parameters. -/
def validateExactFor
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (_inputs : RootedFamilyDecodingInputs view inventory profile plan) : Bool :=
  validateExactFamilyRepresentation view inventory profile plan

theorem representationCanary_exact_validation_succeeds :
    validateExactFor representationCanaryInputs = true := by
  decide

private def intermediateCoverageProfile : ParserProfileLayer := {
  name := "IntermediateChoiceCoverageCanary"
  startSort := "Value"
  classes := []
  states := []
}

private def intermediateCoveragePlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "IntermediateChoiceCoverageCanary"
    startSort := "Value"
    classes := []
    productions := [{
      label := "value-a"
      resultSort := "Value"
      matcher := .char 65
      childSlots := [0]
    }]
  }
  structural := []
}

private def intermediateCoverageInventory : Inventory := {
  symbols := [{ identifier := 5, meaning := "Value" }]
  terminals := [{ identifier := 3, meaning := .char 65 }]
  productions := [{ identifier := 6, meaning := .lexical 0 }]
}

private def intermediateCoverageView : ForestView := {
  nodes := [
    {
      kind := .intermediate 6 1
      scalarStart := 0
      scalarStop := 1
      byteStart := 0
      byteStop := 1
      choiceBegin := 0
      choiceCount := 1
    },
    {
      kind := .terminal 3 (.scalar 65)
      scalarStart := 0
      scalarStop := 1
      byteStart := 0
      byteStop := 1
      choiceBegin := 2
      choiceCount := 0
    },
    {
      kind := .symbol 5
      scalarStart := 0
      scalarStop := 1
      byteStart := 0
      byteStop := 1
      choiceBegin := 1
      choiceCount := 1
    },
    {
      kind := .epsilon
      scalarStart := 1
      scalarStop := 1
      byteStart := 1
      byteStop := 1
      choiceBegin := 2
      choiceCount := 0
    }
  ]
  choices := [
    {
      parent := 0
      prefixNode := none
      childNode := 1
      productionIndex := 6
      scalarPivot := 0
      bytePivot := 0
    },
    {
      parent := 2
      prefixNode := some 0
      childNode := 3
      productionIndex := 6
      scalarPivot := 1
      bytePivot := 1
    }
  ]
  roots := [2]
  codepoints := [65]
  byteOffsets := [0, 1]
}

/-- The full executable gate exercises a real intermediate-prefix unfolding,
not only the empty-prefix leaf case. -/
theorem intermediate_choice_exact_validation_succeeds :
    validateExactFamilyRepresentation intermediateCoverageView
      intermediateCoverageInventory intermediateCoverageProfile
      intermediateCoveragePlan = true := by
  decide

/-- A terminal or epsilon leaf cannot own a productive family choice. -/
private def leafChoiceCanaryView : ForestView := {
  nodes := [{
    kind := .epsilon
    scalarStart := 0
    scalarStop := 0
    byteStart := 0
    byteStop := 0
    choiceBegin := 0
    choiceCount := 1
  }]
  choices := [{
    parent := 0
    prefixNode := none
    childNode := 0
    productionIndex := 0
    scalarPivot := 0
    bytePivot := 0
  }]
  roots := [0]
  codepoints := []
  byteOffsets := [0]
}

private def leafChoiceCanaryProfile : ParserProfileLayer := {
  name := "LeafChoiceCoverageCanary"
  startSort := "Value"
  classes := []
  states := []
}

/-- Global productivity is not vacuous: an exported leaf choice is rejected
even though its finite candidate list is harmless to evaluate. -/
theorem leaf_owned_choice_coverage_rejected :
    validateChoiceCoverage leafChoiceCanaryView {
      symbols := []
      terminals := []
      productions := []
    } leafChoiceCanaryProfile = false := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness
