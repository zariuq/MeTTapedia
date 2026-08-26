import Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation

/-!
# Finite witnesses for native binary forest families

Binary SPPF arrays may contain sharing and graph cycles, while the semantic
`FamilyDerivation` judgment requires one finite unfolding.  The witness format
below records only the physical choice occurrences selected by such an
unfolding.  Its verifier recovers ownership, geometry, terminal semantics,
and identities from the separately supplied checked inputs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityValidation
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

mutual
  /-- Physical evidence for an absent prefix or one selected intermediate
  choice occurrence. -/
  inductive PrefixWitness where
    | empty
    | intermediate (choiceIndex : Nat) (body : ChoiceWitness)
    deriving DecidableEq, Repr

  /-- A finite binary choice witness.  Its child node is determined by the
  choice array; only the possibly branching prefix needs recursive evidence. -/
  inductive ChoiceWitness where
    | binary (prefixWitness : PrefixWitness)
    deriving DecidableEq, Repr
end

/-- One exact symbol-parent and owned-choice occurrence. -/
structure FamilyWitness where
  parentIndex : Nat
  choiceIndex : Nat
  body : ChoiceWitness
  deriving DecidableEq, Repr

abbrev ChildResult
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (nodeIndex : Nat) :=
  Sigma fun children =>
    ChildDerivation view inventory.toTable profile view.codepoints
      nodeIndex children

abbrev PrefixResult
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (production : Nat)
    (prefixNode : Option Nat) :=
  Sigma fun children =>
    PrefixDerivation view inventory.toTable profile view.codepoints
      production prefixNode children

abbrev ChoiceResult
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (production : Nat)
    (choice : Choice) :=
  Sigma fun children =>
    ChoiceChildren view inventory.toTable profile view.codepoints
      production choice children

abbrev FamilyResult
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (parentIndex : Nat)
    (choice : Choice) :=
  Sigma fun family =>
    FamilyDerivation view inventory.toTable profile view.codepoints
      parentIndex choice family

/-- Exact physical geometry recovered for one binary choice.  `PLift` keeps
the proof-valued fields inside the computational result type without erasing
their propositions. -/
structure GeometryEvidence (view : ForestView) (choice : Choice) : Type where
  pivot : PLift (PivotCoherent view choice)
  factorization : PLift (FactorizationCoherent view choice)

theorem list_member_of_getElem?_eq_some
    {Alpha : Type} {items : List Alpha} {index : Nat} {item : Alpha}
    (lookup : items[index]? = some item) : item ∈ items := by
  rw [List.getElem?_eq_some_iff] at lookup
  rw [List.mem_iff_getElem]
  exact ⟨index, lookup.1, lookup.2⟩

/-- Structural input turns an exact node-array lookup into semantic `NodeAt`
evidence. -/
def nodeAtOfLookup
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {index : Nat} {node : Node}
    (lookup : view.nodes[index]? = some node) : NodeAt view index node :=
  ⟨lookup,
    (inputs.structural.arraysCoherent.nodesCoherent index node lookup).1⟩

/-- Structural input turns an exact choice-array lookup into the
parent-indexed ownership used by semantic derivations. -/
def ownedChoiceOfLookup
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {choiceIndex : Nat} {choice : Choice}
    (lookup : view.choices[choiceIndex]? = some choice) :
    OwnedChoice view choice.parent choice :=
  choiceAtOwned_toOwnedChoice
    (inputs.structural.arraysCoherent.choicesOwned
      choiceIndex choice lookup)

/-- Compute the ordered child data for a terminal, epsilon, or symbol leaf.
Intermediate nodes are intentionally rejected here because they are decoded
only through `PrefixWitness.intermediate`.  This proof-free function is the
inspectable computational layer refined by `decodeChild?`. -/
def decodeChildData?
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (nodeIndex : Nat) :
    Option (List ChildRef) :=
  match view.nodes[nodeIndex]? with
  | none => none
  | some node =>
      match node.kind with
      | .terminal terminalId value =>
          match IdentityRow.lookup terminalId inventory.terminals with
          | none => none
          | some matcher =>
              if terminalSemanticValid profile view.codepoints matcher value
                  node.scalarStart node.scalarStop = true then
                if node.choiceCount = 0 then
                  some [.terminal matcher node.scalarStart node.scalarStop]
                else none
              else none
      | .epsilon =>
          if node.scalarStop = node.scalarStart then
            if node.byteStop = node.byteStart then
              if node.choiceCount = 0 then some [] else none
            else none
          else none
      | .symbol symbolId =>
          match IdentityRow.lookup symbolId inventory.symbols with
          | none => none
          | some resultSort =>
              some [.node ⟨resultSort, node.scalarStart, node.scalarStop⟩]
      | .intermediate _ _ => none

/-- Successful pure child decoding constructs the corresponding semantic
leaf derivation. -/
def decodeChildData?_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {nodeIndex : Nat} {children : List ChildRef}
    (decoded :
      decodeChildData? view inventory profile nodeIndex = some children) :
    ChildDerivation view inventory.toTable profile view.codepoints
      nodeIndex children := by
  cases nodeLookup : view.nodes[nodeIndex]? with
  | none => simp [decodeChildData?, nodeLookup] at decoded
  | some node =>
      have nodeAt := nodeAtOfLookup inputs nodeLookup
      rcases node with
        ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
          choiceBegin, choiceCount⟩
      cases kind with
      | terminal terminalId value =>
          cases matcherLookup :
              IdentityRow.lookup terminalId inventory.terminals with
          | none => simp [decodeChildData?, nodeLookup, matcherLookup] at decoded
          | some matcher =>
              simp only [decodeChildData?, nodeLookup, matcherLookup] at decoded
              split at decoded
              next semanticAccepted =>
                split at decoded
                next noChoices =>
                  simp only [Option.some.injEq] at decoded
                  subst children
                  subst choiceCount
                  rcases terminalSemanticValid_sound semanticAccepted with
                    ⟨valueAgrees, terminalMatches⟩
                  exact ChildDerivation.terminal nodeAt
                    (by simpa [Inventory.toTable] using matcherLookup)
                    valueAgrees terminalMatches
                next => simp at decoded
              next => simp at decoded
      | epsilon =>
          simp only [decodeChildData?, nodeLookup] at decoded
          split at decoded
          next scalarExact =>
            split at decoded
            next byteExact =>
              split at decoded
              next noChoices =>
                simp only [Option.some.injEq] at decoded
                subst children
                subst scalarStop
                subst byteStop
                subst choiceCount
                exact ChildDerivation.epsilon nodeAt
              next => simp at decoded
            next => simp at decoded
          next => simp at decoded
      | symbol symbolId =>
          cases sortLookup :
              IdentityRow.lookup symbolId inventory.symbols with
          | none => simp [decodeChildData?, nodeLookup, sortLookup] at decoded
          | some resultSort =>
              simp only [decodeChildData?, nodeLookup, sortLookup,
                Option.some.injEq] at decoded
              subst children
              exact ChildDerivation.symbol nodeAt
                (by simpa [Inventory.toTable] using sortLookup)
      | intermediate production dot =>
          simp [decodeChildData?, nodeLookup] at decoded

/-- Refine the proof-free child computation with its exact semantic witness. -/
def decodeChild?
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (nodeIndex : Nat) : Option (ChildResult view inventory profile nodeIndex) :=
  match decoded : decodeChildData? view inventory profile nodeIndex with
  | none => none
  | some children => some ⟨children, decodeChildData?_sound inputs decoded⟩

theorem decodeChild?_data
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (nodeIndex : Nat) :
    (decodeChild? inputs nodeIndex).map Sigma.fst =
      decodeChildData? view inventory profile nodeIndex := by
  unfold decodeChild?
  split
  next decoded =>
    change none = decodeChildData? view inventory profile nodeIndex
    exact decoded.symm
  next children decoded =>
    change some children = decodeChildData? view inventory profile nodeIndex
    exact decoded.symm

/-- Executable pivot and binary-factorization check. -/
def choiceGeometryValid (view : ForestView) (choice : Choice) : Bool :=
  match view.nodes[choice.parent]?, view.nodes[choice.childNode]? with
  | some parent, some child =>
      choice.scalarPivot == child.scalarStart &&
        choice.bytePivot == child.byteStart &&
        child.scalarStop == parent.scalarStop &&
        child.byteStop == parent.byteStop &&
        match choice.prefixNode with
        | none =>
            choice.scalarPivot == parent.scalarStart &&
              choice.bytePivot == parent.byteStart
        | some prefixIndex =>
            match view.nodes[prefixIndex]? with
            | none => false
            | some prefixNode =>
                prefixNode.scalarStart == parent.scalarStart &&
                prefixNode.byteStart == parent.byteStart &&
                prefixNode.scalarStop == choice.scalarPivot &&
                prefixNode.byteStop == choice.bytePivot
  | _, _ => false

/-- Successful geometry checking reconstructs both semantic geometry
judgments. -/
def choiceGeometryValid_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {choice : Choice}
    (accepted : choiceGeometryValid view choice = true) :
    GeometryEvidence view choice := by
  cases parentLookup : view.nodes[choice.parent]? with
  | none => simp [choiceGeometryValid, parentLookup] at accepted
  | some parent =>
      cases childLookup : view.nodes[choice.childNode]? with
      | none =>
          simp [choiceGeometryValid, parentLookup, childLookup] at accepted
      | some child =>
          have parentAt := nodeAtOfLookup inputs parentLookup
          have childAt := nodeAtOfLookup inputs childLookup
          cases prefixLookup : choice.prefixNode with
          | none =>
              simp only [choiceGeometryValid, parentLookup, childLookup,
                prefixLookup, Bool.and_eq_true, beq_iff_eq] at accepted
              have scalarPivot := accepted.1.1.1.1
              have bytePivot := accepted.1.1.1.2
              have scalarStop := accepted.1.1.2
              have byteStop := accepted.1.2
              have scalarStart := accepted.2.1
              have byteStart := accepted.2.2
              exact {
                pivot := ⟨child, childAt, scalarPivot, bytePivot⟩
                factorization := ⟨parent, child, parentAt, childAt,
                  scalarPivot, bytePivot, scalarStop, byteStop,
                  by simpa [prefixLookup] using And.intro scalarStart byteStart⟩
              }
          | some prefixIndex =>
              cases prefixNodeLookup : view.nodes[prefixIndex]? with
              | none =>
                  simp [choiceGeometryValid, parentLookup, childLookup,
                    prefixLookup, prefixNodeLookup] at accepted
              | some prefixNode =>
                  simp only [choiceGeometryValid, parentLookup, childLookup,
                    prefixLookup, prefixNodeLookup, Bool.and_eq_true,
                    beq_iff_eq] at accepted
                  have scalarPivot := accepted.1.1.1.1
                  have bytePivot := accepted.1.1.1.2
                  have scalarStop := accepted.1.1.2
                  have byteStop := accepted.1.2
                  have prefixScalarStart := accepted.2.1.1.1
                  have prefixByteStart := accepted.2.1.1.2
                  have prefixScalarStop := accepted.2.1.2
                  have prefixByteStop := accepted.2.2
                  exact {
                    pivot := ⟨child, childAt, scalarPivot, bytePivot⟩
                    factorization := ⟨parent, child, parentAt, childAt,
                      scalarPivot, bytePivot, scalarStop, byteStop,
                      by
                        simp only [prefixLookup]
                        exact ⟨prefixNode,
                          nodeAtOfLookup inputs prefixNodeLookup,
                          prefixScalarStart, prefixByteStart,
                          prefixScalarStop, prefixByteStop⟩⟩
                  }

/-- Reconstruct the exact pivot and binary span factorization from the pure
geometry check. -/
def choiceGeometry?
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (choice : Choice) : Option (GeometryEvidence view choice) :=
  if accepted : choiceGeometryValid view choice = true then
    some (choiceGeometryValid_sound inputs accepted)
  else none

mutual
  /-- Compute flattened prefix data from one finite physical witness. -/
  def decodePrefixData?
      (view : ForestView) (inventory : Inventory)
      (profile : ParserProfileLayer) (production : Nat)
      (prefixNode : Option Nat) (witness : PrefixWitness) :
      Option (List ChildRef) :=
    match witness, prefixNode with
    | .empty, none => some []
    | .empty, some _ => none
    | .intermediate _ _, none => none
    | .intermediate choiceIndex bodyWitness, some nodeIndex =>
        match view.nodes[nodeIndex]? with
        | some { kind := .intermediate nodeProduction _, .. } =>
            if nodeProduction = production then
              match view.choices[choiceIndex]? with
              | some choice =>
                  if choice.parent = nodeIndex then
                    decodeChoiceData? view inventory profile production
                      choice bodyWitness
                  else none
              | none => none
            else none
        | _ => none

  /-- Compute ordered children for one binary choice witness. -/
  def decodeChoiceData?
      (view : ForestView) (inventory : Inventory)
      (profile : ParserProfileLayer) (production : Nat)
      (choice : Choice) (witness : ChoiceWitness) :
      Option (List ChildRef) :=
    match witness with
    | .binary prefixWitness =>
        if choice.productionIndex = production then
          if choiceGeometryValid view choice then
            match decodePrefixData? view inventory profile production
                choice.prefixNode prefixWitness,
              decodeChildData? view inventory profile choice.childNode with
            | some prefixChildren, some childChildren =>
                some (prefixChildren ++ childChildren)
            | _, _ => none
          else none
        else none
end

mutual
  /-- Pure prefix decoding refines to the semantic prefix judgment. -/
  def decodePrefixData?_sound
      {view : ForestView} {inventory : Inventory}
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      (inputs : FamilyDecodingInputs view inventory profile plan)
      {production : Nat} {prefixNode : Option Nat}
      {witness : PrefixWitness} {children : List ChildRef}
      (decoded : decodePrefixData? view inventory profile production
        prefixNode witness = some children) :
      PrefixDerivation view inventory.toTable profile view.codepoints
        production prefixNode children := by
    cases witness with
    | empty =>
        cases prefixNode with
        | none =>
            simp only [decodePrefixData?, Option.some.injEq] at decoded
            subst children
            exact PrefixDerivation.empty
        | some nodeIndex => simp [decodePrefixData?] at decoded
    | intermediate choiceIndex bodyWitness =>
        cases prefixNode with
        | none => simp [decodePrefixData?] at decoded
        | some nodeIndex =>
            cases nodeLookup : view.nodes[nodeIndex]? with
            | none => simp [decodePrefixData?, nodeLookup] at decoded
            | some node =>
                rcases node with
                  ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
                    choiceBegin, choiceCount⟩
                cases kind with
                | terminal terminalId value =>
                    simp [decodePrefixData?, nodeLookup] at decoded
                | epsilon => simp [decodePrefixData?, nodeLookup] at decoded
                | symbol symbolId =>
                    simp [decodePrefixData?, nodeLookup] at decoded
                | intermediate nodeProduction dot =>
                    simp only [decodePrefixData?, nodeLookup] at decoded
                    split at decoded
                    next productionExact =>
                      cases choiceLookup : view.choices[choiceIndex]? with
                      | none => simp [choiceLookup] at decoded
                      | some choice =>
                          simp only [choiceLookup] at decoded
                          split at decoded
                          next parentExact =>
                            subst nodeProduction
                            exact PrefixDerivation.intermediate
                              (nodeAtOfLookup inputs nodeLookup)
                              (by
                                rw [← parentExact]
                                exact ownedChoiceOfLookup inputs choiceLookup)
                              (decodeChoiceData?_sound inputs decoded)
                          next => simp at decoded
                    next => simp at decoded

  /-- Pure choice decoding refines to the semantic binary-choice judgment. -/
  def decodeChoiceData?_sound
      {view : ForestView} {inventory : Inventory}
      {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      (inputs : FamilyDecodingInputs view inventory profile plan)
      {production : Nat} {choice : Choice} {witness : ChoiceWitness}
      {children : List ChildRef}
      (decoded : decodeChoiceData? view inventory profile production
        choice witness = some children) :
      ChoiceChildren view inventory.toTable profile view.codepoints
        production choice children := by
    cases witness with
    | binary prefixWitness =>
        simp only [decodeChoiceData?] at decoded
        split at decoded
        next productionExact =>
          split at decoded
          next geometryAccepted =>
            cases prefixDecoded : decodePrefixData? view inventory profile
                production choice.prefixNode prefixWitness with
            | none => simp [prefixDecoded] at decoded
            | some prefixChildren =>
                rw [prefixDecoded] at decoded
                cases childDecoded : decodeChildData? view inventory profile
                    choice.childNode with
                | none => simp [childDecoded] at decoded
                | some childChildren =>
                    rw [childDecoded] at decoded
                    simp only [Option.some.injEq] at decoded
                    subst children
                    have geometry :=
                      choiceGeometryValid_sound inputs geometryAccepted
                    exact ChoiceChildren.binary productionExact
                      geometry.pivot.down geometry.factorization.down
                      (decodePrefixData?_sound inputs prefixDecoded)
                      (decodeChildData?_sound inputs childDecoded)
          next => simp at decoded
        next => simp at decoded
end

/-- Refine pure prefix computation with its semantic witness. -/
def decodePrefix?
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (production : Nat) (prefixNode : Option Nat)
    (witness : PrefixWitness) :
    Option (PrefixResult view inventory profile production prefixNode) :=
  match decoded : decodePrefixData? view inventory profile production
      prefixNode witness with
  | none => none
  | some children => some ⟨children, decodePrefixData?_sound inputs decoded⟩

/-- Refine pure binary-choice computation with its semantic witness. -/
def decodeChoice?
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (production : Nat) (choice : Choice) (witness : ChoiceWitness) :
    Option (ChoiceResult view inventory profile production choice) :=
  match decoded : decodeChoiceData? view inventory profile production
      choice witness with
  | none => none
  | some children => some ⟨children, decodeChoiceData?_sound inputs decoded⟩

/-- Compute the exact physical choice and flattened semantic family selected
by one finite witness. -/
def decodeFamilyData?
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (witness : FamilyWitness) :
    Option (Choice × Family) :=
  match view.nodes[witness.parentIndex]? with
  | none => none
  | some parent =>
      match parent.kind with
      | .symbol symbolId =>
          match view.choices[witness.choiceIndex]? with
          | some choice =>
              if choice.parent = witness.parentIndex then
                match IdentityRow.lookup symbolId inventory.symbols,
                    IdentityRow.lookup choice.productionIndex
                      inventory.productions with
                | some resultSort, some productionRef =>
                    match decodeChoiceData? view inventory profile
                        choice.productionIndex choice witness.body with
                    | some children => some (choice, {
                        parent := ⟨resultSort, parent.scalarStart,
                          parent.scalarStop⟩
                        production := productionRef
                        children := children
                      })
                    | none => none
                | _, _ => none
              else none
          | none => none
      | _ => none

/-- Successful pure family decoding constructs occurrence ownership and the
exact semantic family derivation. -/
def decodeFamilyData?_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witness : FamilyWitness) {decodedChoice : Choice} {family : Family}
    (decoded : decodeFamilyData? view inventory profile witness =
      some (decodedChoice, family)) :
    PLift (ChoiceAtOwned view witness.choiceIndex decodedChoice) ×
      FamilyDerivation view inventory.toTable profile view.codepoints
        witness.parentIndex decodedChoice family := by
  cases parentLookup : view.nodes[witness.parentIndex]? with
  | none => simp [decodeFamilyData?, parentLookup] at decoded
  | some parent =>
      have parentAt := nodeAtOfLookup inputs parentLookup
      rcases parent with
        ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
          choiceBegin, choiceCount⟩
      cases kind with
      | terminal terminalId value =>
          simp [decodeFamilyData?, parentLookup] at decoded
      | epsilon => simp [decodeFamilyData?, parentLookup] at decoded
      | intermediate production dot =>
          simp [decodeFamilyData?, parentLookup] at decoded
      | symbol symbolId =>
          cases choiceLookup : view.choices[witness.choiceIndex]? with
          | none =>
              simp [decodeFamilyData?, parentLookup, choiceLookup] at decoded
          | some choice =>
              simp only [decodeFamilyData?, parentLookup, choiceLookup] at decoded
              split at decoded
              next parentExact =>
                cases sortLookup :
                    IdentityRow.lookup symbolId inventory.symbols with
                | none => simp [sortLookup] at decoded
                | some resultSort =>
                    rw [sortLookup] at decoded
                    cases productionLookup :
                        IdentityRow.lookup choice.productionIndex
                          inventory.productions with
                    | none => simp [productionLookup] at decoded
                    | some productionRef =>
                        rw [productionLookup] at decoded
                        cases bodyDecoded : decodeChoiceData? view inventory
                            profile choice.productionIndex choice
                            witness.body with
                        | none => simp [bodyDecoded] at decoded
                        | some children =>
                            rw [bodyDecoded] at decoded
                            simp only [Option.some.injEq,
                              Prod.mk.injEq] at decoded
                            rcases decoded with ⟨choiceExact, familyExact⟩
                            subst decodedChoice
                            subst family
                            have ownedAt : ChoiceAtOwned view
                                witness.choiceIndex choice :=
                              inputs.structural.arraysCoherent.choicesOwned
                                witness.choiceIndex choice choiceLookup
                            have owned : OwnedChoice view
                                witness.parentIndex choice := by
                              rw [← parentExact]
                              exact choiceAtOwned_toOwnedChoice ownedAt
                            exact ⟨⟨ownedAt⟩,
                              FamilyDerivation.symbol parentAt owned
                                (by simpa [Inventory.toTable] using sortLookup)
                                (by simpa [Inventory.toTable] using
                                  productionLookup)
                                (decodeChoiceData?_sound inputs bodyDecoded)⟩
              next => simp at decoded

/-- Refine pure family computation with occurrence and semantic evidence. -/
def decodeFamily?
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witness : FamilyWitness) :
    Option (Sigma fun choice =>
      PLift (ChoiceAtOwned view witness.choiceIndex choice) ×
        FamilyResult view inventory profile witness.parentIndex choice) :=
  match decoded : decodeFamilyData? view inventory profile witness with
  | none => none
  | some (choice, family) =>
      let evidence := decodeFamilyData?_sound inputs witness decoded
      some ⟨choice, ⟨evidence.1, ⟨family, evidence.2⟩⟩⟩

/-- A successfully decoded family retains its exact top-level physical
choice occurrence in addition to the semantic family derivation. -/
structure DecodedFamilyOccurrence
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) : Type where
  witness : FamilyWitness
  choice : Choice
  family : Family
  ownedAt : ChoiceAtOwned view witness.choiceIndex choice
  derivation : FamilyDerivation view inventory.toTable profile
    view.codepoints witness.parentIndex choice family

/-- Convert one checked witness into a first-class occurrence-bearing result. -/
def decodeFamilyOccurrence?
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witness : FamilyWitness) :
    Option (DecodedFamilyOccurrence view inventory profile) :=
  match decodeFamily? inputs witness with
  | none => none
  | some ⟨choice, ⟨⟨ownedAt⟩, ⟨family, derivation⟩⟩⟩ =>
      some { witness, choice, family, ownedAt, derivation }

/-- Decode a finite submitted list without inventing output for a rejected
witness.  Completeness is a separate obligation. -/
def decodeFamilyOccurrences
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witnesses : List FamilyWitness) :
    List (DecodedFamilyOccurrence view inventory profile) :=
  witnesses.filterMap (decodeFamilyOccurrence? inputs)

theorem member_decodeFamilyOccurrences
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {witnesses : List FamilyWitness}
    {decoded : DecodedFamilyOccurrence view inventory profile}
    (member : decoded ∈ decodeFamilyOccurrences inputs witnesses) :
    ∃ witness, witness ∈ witnesses ∧
      decodeFamilyOccurrence? inputs witness = some decoded := by
  simpa [decodeFamilyOccurrences] using
    (List.mem_filterMap.mp member)

/-! ## Exact exported-root decoding -/

/-- Decode one physical root index to its semantic shared-node key.  Root-list
membership is intentionally checked by the caller so this helper is reusable
for individual occurrences. -/
def decodeRootKey?
    (view : ForestView) (inventory : Inventory) (rootIndex : Nat) :
    Option NodeKey :=
  match view.nodes[rootIndex]? with
  | some {
      kind := .symbol symbolId
      scalarStart := start
      scalarStop := stop
      .. } =>
      (IdentityRow.lookup symbolId inventory.symbols).map fun resultSort =>
        ⟨resultSort, start, stop⟩
  | _ => none

theorem decodeRootKey_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {rootIndex : Nat} (rootMember : rootIndex ∈ view.roots)
    {key : NodeKey}
    (decoded : decodeRootKey? view inventory rootIndex = some key) :
    RootKeyAt view inventory.toTable key := by
  unfold decodeRootKey? at decoded
  cases nodeLookup : view.nodes[rootIndex]? with
  | none => simp [nodeLookup] at decoded
  | some node =>
      rw [nodeLookup] at decoded
      rcases node with
        ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
          choiceBegin, choiceCount⟩
      cases kind with
      | terminal terminalId value => simp at decoded
      | epsilon => simp at decoded
      | intermediate production dot => simp at decoded
      | symbol symbolId =>
          cases sortLookup :
              IdentityRow.lookup symbolId inventory.symbols with
          | none => simp [sortLookup] at decoded
          | some resultSort =>
              simp only [sortLookup, Option.map_some,
                Option.some.injEq] at decoded
              subst key
              refine ⟨rootIndex, symbolId, byteStart, byteStop,
                choiceBegin, choiceCount, rootMember,
                nodeAtOfLookup inputs nodeLookup, ?_⟩
              simpa [Inventory.toTable] using sortLookup

theorem decodeRootKey_complete
    {view : ForestView} {inventory : Inventory} {key : NodeKey}
    (root : RootKeyAt view inventory.toTable key) :
    ∃ rootIndex, rootIndex ∈ view.roots ∧
      decodeRootKey? view inventory rootIndex = some key := by
  rcases root with
    ⟨rootIndex, symbolId, byteStart, byteStop, choiceBegin, choiceCount,
      rootMember, nodeAt, sortAt⟩
  refine ⟨rootIndex, rootMember, ?_⟩
  simp only [decodeRootKey?, nodeAt.1]
  change IdentityRow.lookup symbolId inventory.symbols =
    some key.resultSort at sortAt
  rw [sortAt]
  rfl

/-- Canonical semantic root list recovered from the exported root occurrences. -/
def decodeRootKeys (view : ForestView) (inventory : Inventory) :
    List NodeKey :=
  view.roots.filterMap (decodeRootKey? view inventory)

theorem mem_decodeRootKeys_iff
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (key : NodeKey) :
    key ∈ decodeRootKeys view inventory ↔
      RootKeyAt view inventory.toTable key := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨rootIndex, rootMember, decoded⟩
    exact decodeRootKey_sound inputs rootMember decoded
  · intro root
    rcases decodeRootKey_complete root with
      ⟨rootIndex, rootMember, decoded⟩
    exact List.mem_filterMap.mpr
      ⟨rootIndex, rootMember, decoded⟩

def validateRootKeys (view : ForestView) (inventory : Inventory) : Bool :=
  view.roots.all fun rootIndex =>
    (decodeRootKey? view inventory rootIndex).isSome

theorem validateRootKeys_sound
    {view : ForestView} {inventory : Inventory}
    (accepted : validateRootKeys view inventory = true) :
    ∀ rootIndex, rootIndex ∈ view.roots →
      ∃ key, decodeRootKey? view inventory rootIndex = some key := by
  intro rootIndex rootMember
  have present := (List.all_eq_true.mp accepted) rootIndex rootMember
  simpa only [Option.isSome_iff_exists] using present

/-- All nonrecursive inputs needed before exact root and family unfolding. -/
structure RootedFamilyDecodingInputs
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Type where
  families : FamilyDecodingInputs view inventory profile plan
  roots : ∀ rootIndex, rootIndex ∈ view.roots →
    ∃ key, decodeRootKey? view inventory rootIndex = some key

def validateRootedFamilyDecodingInputs
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  validateFamilyDecodingInputs view inventory profile plan &&
    validateRootKeys view inventory

def validateRootedFamilyDecodingInputs_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (accepted :
      validateRootedFamilyDecodingInputs view inventory profile plan = true) :
    RootedFamilyDecodingInputs view inventory profile plan := by
  rw [validateRootedFamilyDecodingInputs, Bool.and_eq_true_iff] at accepted
  exact {
    families := validateFamilyDecodingInputs_sound accepted.1
    roots := validateRootKeys_sound accepted.2
  }

/-! ## From finite decoded occurrences to the representation contract -/

/-- Semantic families produced by the finite submitted occurrence list.
Literal duplicates are shared only after their occurrence-bearing proofs have
been checked. -/
def decodedFamilies
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witnesses : List FamilyWitness) : List Family :=
  ((decodeFamilyOccurrences inputs witnesses).map
    DecodedFamilyOccurrence.family).eraseDups

def decodedForest
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witnesses : List FamilyWitness) : Forest := {
  roots := decodeRootKeys view inventory
  families := decodedFamilies inputs witnesses
}

/-- The two genuinely global obligations which local witness checking cannot
infer by itself.  `familiesComplete` forbids an omitted finite unfolding;
`choicesCovered` forbids leaves with choices and nonproductive/cyclic choice
subgraphs.  A later exhaustive enumerator may construct this package, but a
mere list of locally valid witnesses cannot. -/
structure ExactFamilyCoverage
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    (witnesses : List FamilyWitness) : Prop where
  familiesComplete : ∀ family,
    (∃ parentIndex choice,
      Nonempty (FamilyDerivation view inventory.toTable profile
        view.codepoints parentIndex choice family)) →
      family ∈ decodedFamilies inputs witnesses
  choicesCovered : ∀ parentIndex parent choice,
    NodeAt view parentIndex parent →
    OwnedChoice view parentIndex choice →
    ChoiceCovered view inventory.toTable profile view.codepoints
      parentIndex parent choice

/-- Local proof-producing decoding supplies the no-invention half of exact
family membership. -/
theorem mem_decodedFamilies_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan)
    {witnesses : List FamilyWitness} {family : Family}
    (member : family ∈ decodedFamilies inputs witnesses) :
    ∃ parentIndex choice,
      Nonempty (FamilyDerivation view inventory.toTable profile
        view.codepoints parentIndex choice family) := by
  simp only [decodedFamilies, List.mem_eraseDups, List.mem_map] at member
  rcases member with ⟨decoded, decodedMember, familyExact⟩
  subst family
  exact ⟨decoded.witness.parentIndex, decoded.choice,
    ⟨decoded.derivation⟩⟩

/-- Root checking, finite occurrence decoding, explicit completeness, and
the pre-existing structural checks assemble the exact native representation
contract. -/
def RootedFamilyDecodingInputs.represents
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : RootedFamilyDecodingInputs view inventory profile plan)
    (witnesses : List FamilyWitness)
    (coverage : ExactFamilyCoverage inputs.families witnesses) :
    Represents view inventory.toTable profile view.codepoints
      (decodedForest inputs.families witnesses) := {
  arraysCoherent := inputs.families.structural.arraysCoherent
  rootsExact := fun key =>
    mem_decodeRootKeys_iff inputs.families key
  rootsCovered := by
    intro rootIndex rootMember
    rcases inputs.roots rootIndex rootMember with ⟨key, decoded⟩
    exact ⟨key,
      decodeRootKey_sound inputs.families rootMember decoded⟩
  familiesExact := by
    intro family
    constructor
    · exact mem_decodedFamilies_sound inputs.families
    · exact coverage.familiesComplete family
  choicesCovered := coverage.choicesCovered
  nodesReachable := inputs.families.structural.nodesReachable
}

/-! ## Finite exhaustive-witness candidate generation -/

/-- A simple well-founded physical profile: every present prefix points to a
strictly earlier node occurrence.  This is stronger than mere graph
acyclicity, but it is executable and makes the initial completeness proof use
the public array order as its decreasing measure. -/
def prefixIndexDecreases (choice : Choice) : Bool :=
  match choice.prefixNode with
  | none => true
  | some prefixIndex => decide (prefixIndex < choice.parent)

def validatePrefixIndexOrder (view : ForestView) : Bool :=
  view.choices.all prefixIndexDecreases

theorem validatePrefixIndexOrder_sound
    {view : ForestView}
    (accepted : validatePrefixIndexOrder view = true) :
    ∀ choice, choice ∈ view.choices →
      ∀ prefixIndex, choice.prefixNode = some prefixIndex →
        prefixIndex < choice.parent := by
  intro choice choiceMember prefixIndex prefixExact
  have decreases := (List.all_eq_true.mp accepted) choice choiceMember
  simp [prefixIndexDecreases, prefixExact] at decreases
  exact decreases

/-- Enumerate every finite prefix witness allowed by the physical choice
table up to `fuel`.  The semantic decoder remains authoritative: malformed
physical candidates are later rejected rather than interpreted. -/
def enumeratePrefixWitnesses (view : ForestView) :
    Nat → Option Nat → List PrefixWitness
  | _, none => [.empty]
  | 0, some _ => []
  | fuel + 1, some nodeIndex =>
      view.choices.zipIdx.flatMap fun (choice, choiceIndex) =>
        if choice.parent = nodeIndex then
          (enumeratePrefixWitnesses view fuel choice.prefixNode).map fun prefixWitness =>
            .intermediate choiceIndex (.binary prefixWitness)
        else []

/-- Enumerate the physical symbol-family candidates.  Fuel equal to the node
count is sufficient once `validatePrefixIndexOrder` is proved complete. -/
def enumerateFamilyWitnessesWithFuel
    (view : ForestView) (fuel : Nat) : List FamilyWitness :=
  view.nodes.zipIdx.flatMap fun (node, parentIndex) =>
    match node.kind with
    | .symbol _ =>
        view.choices.zipIdx.flatMap fun (choice, choiceIndex) =>
          if choice.parent = parentIndex then
            (enumeratePrefixWitnesses view fuel choice.prefixNode).map fun prefixWitness => {
              parentIndex
              choiceIndex
              body := .binary prefixWitness
            }
          else []
    | _ => []

def enumerateFamilyWitnesses (view : ForestView) : List FamilyWitness :=
  enumerateFamilyWitnessesWithFuel view view.nodes.length

/-- Candidate generation followed by the proof-producing decoder. -/
def enumerateDecodedFamilies
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (inputs : FamilyDecodingInputs view inventory profile plan) :
    List (DecodedFamilyOccurrence view inventory profile) :=
  decodeFamilyOccurrences inputs (enumerateFamilyWitnesses view)

def enumerateFamilyWitnessesFor
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (_inputs : FamilyDecodingInputs view inventory profile plan) :
    List FamilyWitness :=
  enumerateFamilyWitnesses view

private def cyclicPrefixCanary : ForestView := {
  nodes := [{
    kind := .intermediate 0 1
    scalarStart := 0
    scalarStop := 0
    byteStart := 0
    byteStop := 0
    choiceBegin := 0
    choiceCount := 1
  }]
  choices := [{
    parent := 0
    prefixNode := some 0
    childNode := 0
    productionIndex := 0
    scalarPivot := 0
    bytePivot := 0
  }]
  roots := [0]
  codepoints := []
  byteOffsets := [0]
}

/-- A self-referential prefix cannot masquerade as a finitely representable
flattened forest under the decreasing-index profile. -/
theorem cyclic_prefix_order_rejected :
    validatePrefixIndexOrder cyclicPrefixCanary = false := by
  decide

/-! ## Positive and negative controls -/

private def representationCanaryProfile : ParserProfileLayer := {
  name := "NativeFamilyRepresentationCanary"
  startSort := "Value"
  classes := []
  states := []
}

private def representationCanaryPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "NativeFamilyRepresentationCanary"
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

private def representationCanaryInventory : Inventory := {
  symbols := [{ identifier := 5, meaning := "Value" }]
  terminals := [{ identifier := 3, meaning := .char 65 }]
  productions := [{ identifier := 6, meaning := .lexical 0 }]
}

private def representationCanarySymbol : Node := {
  kind := .symbol 5
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 0
  choiceCount := 1
}

private def representationCanaryTerminal : Node := {
  kind := .terminal 3 (.scalar 65)
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 1
  choiceCount := 0
}

private def representationCanaryChoice : Choice := {
  parent := 0
  prefixNode := none
  childNode := 1
  productionIndex := 6
  scalarPivot := 0
  bytePivot := 0
}

private def representationCanaryView : ForestView := {
  nodes := [representationCanarySymbol, representationCanaryTerminal]
  choices := [representationCanaryChoice]
  roots := [0]
  codepoints := [65]
  byteOffsets := [0, 1]
}

theorem representationCanary_validates :
    validateRootedFamilyDecodingInputs representationCanaryView
      representationCanaryInventory representationCanaryProfile
      representationCanaryPlan = true := by
  decide

def representationCanaryInputs :
    RootedFamilyDecodingInputs representationCanaryView
      representationCanaryInventory representationCanaryProfile
      representationCanaryPlan :=
  validateRootedFamilyDecodingInputs_sound representationCanary_validates

/-- The terminal-validation canary's sole symbol family has one empty prefix
and one exact character child. -/
def leafCanaryWitness : FamilyWitness := {
  parentIndex := 0
  choiceIndex := 0
  body := .binary .empty
}

theorem representationCanary_leaf_decodes :
    (decodeFamily?
      representationCanaryInputs.families leafCanaryWitness).isSome = true := by
  decide

private def representationCanaryFamily : Family := {
  parent := ⟨"Value", 0, 1⟩
  production := .lexical 0
  children := [.terminal (.char 65) 0 1]
}

theorem representationCanary_familyData_decodes :
    decodeFamilyData? representationCanaryView
      representationCanaryInventory representationCanaryProfile
      leafCanaryWitness =
        some (representationCanaryChoice, representationCanaryFamily) := by
  decide

private def representationCanaryDataEvidence :=
  decodeFamilyData?_sound representationCanaryInputs.families
    leafCanaryWitness representationCanary_familyData_decodes

def representationCanaryDecoded :
    DecodedFamilyOccurrence representationCanaryView
      representationCanaryInventory representationCanaryProfile := {
  witness := leafCanaryWitness
  choice := representationCanaryChoice
  family := representationCanaryFamily
  ownedAt := representationCanaryDataEvidence.1.down
  derivation := representationCanaryDataEvidence.2
}

theorem representationCanary_ownedChoice_unique
    {parentIndex : Nat} {choice : Choice}
    (owned : OwnedChoice representationCanaryView parentIndex choice) :
    parentIndex = 0 ∧ choice = representationCanaryChoice := by
  rcases owned with
    ⟨parent, localIndex, parentLookup, localValid,
      choiceLookup, parentExact⟩
  cases parentIndex with
  | zero =>
      simp [representationCanaryView, representationCanarySymbol,
        representationCanaryTerminal] at parentLookup
      subst parent
      change localIndex < 1 at localValid
      have localExact : localIndex = 0 := by omega
      subst localIndex
      simp [representationCanaryView] at choiceLookup
      exact ⟨rfl, choiceLookup.symm⟩
  | succ parentIndex =>
      cases parentIndex with
      | zero =>
          simp [representationCanaryView, representationCanarySymbol,
            representationCanaryTerminal] at parentLookup
          subst parent
          change localIndex < 0 at localValid
          omega
      | succ parentIndex =>
          simp [representationCanaryView] at parentLookup

theorem nodeAt_unique
    {view : ForestView} {index : Nat} {left right : Node}
    (leftAt : NodeAt view index left) (rightAt : NodeAt view index right) :
    left = right :=
  Option.some.inj (leftAt.1.symm.trans rightAt.1)

def representationCanaryParentAt :
    NodeAt representationCanaryView 0 representationCanarySymbol := by
  simp [NodeAt, NodeSpanCoherent, representationCanaryView,
    representationCanarySymbol]

def representationCanaryTerminalAt :
    NodeAt representationCanaryView 1 representationCanaryTerminal := by
  simp [NodeAt, NodeSpanCoherent, representationCanaryView,
    representationCanaryTerminal]

theorem representationCanaryDecoded_family :
    representationCanaryDecoded.family = representationCanaryFamily := by
  rfl

theorem representationCanary_family_unique
    {parentIndex : Nat} {choice : Choice} {family : Family}
    (derivation : FamilyDerivation representationCanaryView
      representationCanaryInventory.toTable representationCanaryProfile [65]
      parentIndex choice family) :
    family = representationCanaryDecoded.family := by
  cases derivation with
  | symbol parentAt owned sortAt productionAt body =>
      rcases representationCanary_ownedChoice_unique owned with
        ⟨parentExact, choiceExact⟩
      subst parentIndex
      subst choice
      have parentNodeExact :=
        nodeAt_unique parentAt representationCanaryParentAt
      cases parentNodeExact
      cases body with
      | binary productionExact pivot factorization prefixResult childResult =>
          cases prefixResult
          cases childResult with
          | terminal nodeAt matcherAt valueAgrees terminalMatch =>
              have childNodeExact :=
                nodeAt_unique nodeAt representationCanaryTerminalAt
              cases childNodeExact
              rw [representationCanaryDecoded_family]
              simp_all [representationCanaryFamily,
                representationCanaryInventory, Inventory.toTable,
                representationCanaryChoice]
          | epsilon nodeAt =>
              have impossible :=
                nodeAt_unique nodeAt representationCanaryTerminalAt
              cases impossible
          | symbol nodeAt sortAt =>
              have impossible :=
                nodeAt_unique nodeAt representationCanaryTerminalAt
              cases impossible

theorem representationCanaryDecoded_member :
    representationCanaryDecoded.family ∈
      decodedFamilies representationCanaryInputs.families
        [leafCanaryWitness] := by
  decide

def representationCanaryCoverage :
    ExactFamilyCoverage representationCanaryInputs.families
      [leafCanaryWitness] := by
  constructor
  · intro family derivable
    rcases derivable with ⟨parentIndex, choice, ⟨derivation⟩⟩
    rw [representationCanary_family_unique derivation]
    exact representationCanaryDecoded_member
  · intro parentIndex parent choice parentAt owned
    rcases representationCanary_ownedChoice_unique owned with
      ⟨parentIndexExact, choiceExact⟩
    subst parentIndex
    subst choice
    have parentExact :=
      nodeAt_unique parentAt representationCanaryParentAt
    cases parentExact
    exact ⟨representationCanaryDecoded.family,
      ⟨representationCanaryDecoded.derivation⟩⟩

/-- A nontrivial symbol/choice/terminal instance reaches the full exact
`Represents` contract through the generic decoder and coverage interface. -/
def representationCanaryRepresents :
    Represents representationCanaryView
      representationCanaryInventory.toTable representationCanaryProfile [65]
      (decodedForest representationCanaryInputs.families
        [leafCanaryWitness]) :=
  representationCanaryInputs.represents
    [leafCanaryWitness] representationCanaryCoverage

/-- Local validity is insufficient: omitting the one real family cannot
inhabit exact coverage even though the empty submitted list has no bad entry. -/
theorem representationCanary_empty_witnesses_not_exact :
    ¬ ExactFamilyCoverage representationCanaryInputs.families [] := by
  intro coverage
  have member := coverage.familiesComplete
    representationCanaryDecoded.family
    ⟨representationCanaryDecoded.witness.parentIndex,
      representationCanaryDecoded.choice,
      ⟨representationCanaryDecoded.derivation⟩⟩
  simp [decodedFamilies, decodeFamilyOccurrences] at member

/-- The positive leaf canary exercises complete physical candidate
generation before proof-producing semantic decoding. -/
theorem familyCanary_enumerates_leaf :
    enumerateFamilyWitnessesFor familyCanary_inputs =
      [leafCanaryWitness] := by
  decide

def validateRootedFor
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (_inputs : FamilyDecodingInputs view inventory profile plan) : Bool :=
  validateRootedFamilyDecodingInputs view inventory profile plan

theorem familyCanary_validateRootedInputs :
    validateRootedFor familyCanary_inputs = true := by
  decide

theorem leafCanary_decodes :
    (decodeFamily? familyCanary_inputs leafCanaryWitness).isSome = true := by
  decide

/-- Physical occurrence identity matters: an absent choice occurrence cannot
be replaced by an extensionally similar witness. -/
theorem absent_choice_occurrence_rejected :
    (decodeFamily? familyCanary_inputs
      { leafCanaryWitness with choiceIndex := 1 }).isSome = false := by
  decide

/-- Prefix evidence must agree with the choice's exact optional prefix. -/
theorem invented_prefix_rejected :
    (decodeFamily? familyCanary_inputs
      { leafCanaryWitness with
        body := .binary (.intermediate 0 (.binary .empty)) }).isSome = false := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness
