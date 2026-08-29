import Mettapedia.GSLT.Parsing.FiniteHornSaturation
import Mettapedia.GSLT.Parsing.BoundedScheduler

/-!
# Finite grounded charts for scannerless grammars

For one admitted compiled grammar and one finite codepoint input, every
possible category/span descriptor, production family, body split, and
lookahead witness can be enumerated as finite data.  This module performs that
grounding generically and feeds the resulting propositional Horn program to
the proved finite-support saturation engine.

No guest-language symbol or policy appears here.  Terminals are checked
against the supplied codepoint list, nonterminal and lookahead obligations
become chart premises, and source-rule identities are retained in packed
families.
-/

namespace Mettapedia.GSLT.Parsing.GroundedChart

open CompilerCorrespondence GuardCorrespondence PackedForest
open Mettapedia.Logic.LP
open FiniteHornSaturation

structure BodyPlan where
  stop : Nat
  children : List ChildRef
  premises : List NodeKey
  deriving DecidableEq, Repr

structure GuardPlan where
  premises : List NodeKey
  deriving DecidableEq, Repr

structure GroundInstance where
  production : GuardCorrespondence.CompiledProduction
  start : Nat
  body : BodyPlan
  guards : GuardPlan
  deriving DecidableEq, Repr

def GroundInstance.parent (grounding : GroundInstance) : NodeKey :=
  { category := grounding.production.category
    start := grounding.start
    stop := grounding.body.stop }

def GroundInstance.family (grounding : GroundInstance) : Family :=
  { parent := grounding.parent
    sourceRule := grounding.production.sourceRule
    children := grounding.body.children }

def GroundInstance.premises (grounding : GroundInstance) : List NodeKey :=
  grounding.body.premises ++ grounding.guards.premises

def positionsFrom (input : List Codepoint) (start : Nat) : List Nat :=
  (List.range (input.length + 1)).filter (start ≤ ·)

def groundBody (input : List Codepoint) :
    List CompiledSymbol → Nat → List BodyPlan
  | [], start => [{ stop := start, children := [], premises := [] }]
  | .terminal expected :: symbols, start =>
      match input[start]? with
      | some actual =>
          if actual = expected then
            (groundBody input symbols (start + 1)).map fun rest =>
              { stop := rest.stop
                children := .terminal actual start (start + 1) :: rest.children
                premises := rest.premises }
          else []
      | none => []
  | .anyTerminal :: symbols, start =>
      match input[start]? with
      | some actual =>
          (groundBody input symbols (start + 1)).map fun rest =>
            { stop := rest.stop
              children := .terminal actual start (start + 1) :: rest.children
              premises := rest.premises }
      | none => []
  | .oneOfTerminal choices :: symbols, start =>
      match input[start]? with
      | some actual =>
          if actual ∈ choices then
            (groundBody input symbols (start + 1)).map fun rest =>
              { stop := rest.stop
                children := .terminal actual start (start + 1) :: rest.children
                premises := rest.premises }
          else []
      | none => []
  | .nonterminal category :: symbols, start =>
      (positionsFrom input start).flatMap fun middle =>
        (groundBody input symbols middle).map fun rest =>
          let key : NodeKey :=
            { category := category, start := start, stop := middle }
          { stop := rest.stop
            children := .node key :: rest.children
            premises := key :: rest.premises }

def groundGuards (input : List Codepoint) :
    List GuardCorrespondence.CompiledGuard → Nat → List GuardPlan
  | [], _ => [{ premises := [] }]
  | .atEnd :: guards, cursor =>
      if cursor = input.length then groundGuards input guards cursor else []
  | .nextIn choices allowEof :: guards, cursor =>
      match input[cursor]? with
      | some codepoint =>
          if codepoint ∈ choices then groundGuards input guards cursor else []
      | none =>
          if allowEof && cursor = input.length then
            groundGuards input guards cursor
          else []
  | .lookahead category :: guards, cursor =>
      (positionsFrom input cursor).flatMap fun witnessStop =>
        (groundGuards input guards cursor).map fun rest =>
          { premises :=
              { category := category, start := cursor, stop := witnessStop } ::
                rest.premises }

def groundProduction (input : List Codepoint)
    (production : GuardCorrespondence.CompiledProduction) :
    List GroundInstance :=
  (positionsFrom input 0).flatMap fun start =>
    (groundBody input production.symbols start).flatMap fun body =>
      (groundGuards input production.guards body.stop).map fun guards =>
        { production := production, start := start, body := body, guards := guards }

def groundInstances (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : List GroundInstance :=
  grammar.productions.flatMap (groundProduction input)

inductive ChartAtom where
  | node (key : NodeKey)
  | instance (value : GroundInstance)
  deriving DecidableEq, Repr

def instanceRule (grounding : GroundInstance) : PropRule ChartAtom :=
  { premises := (grounding.premises.map ChartAtom.node).toFinset
    head := .instance grounding }

def promotionRule (grounding : GroundInstance) : PropRule ChartAtom :=
  { premises := {.instance grounding}
    head := .node grounding.parent }

def chartProgram (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : PropProgram ChartAtom :=
  let instances := (groundInstances grammar input).toFinset
  instances.image instanceRule ∪ instances.image promotionRule

def chart (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : Finset ChartAtom :=
  FiniteHornSaturation.saturate (chartProgram grammar input) ∅

def chartForest (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : Forest :=
  let saturated := chart grammar input
  let root : NodeKey :=
    { category := grammar.start, start := 0, stop := input.length }
  { roots := if .node root ∈ saturated then [root] else []
    families := (groundInstances grammar input).filterMap fun grounding =>
      if .instance grounding ∈ saturated then some grounding.family else none }

/-! ## Grounding and saturation soundness -/

def NodeValid (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (key : NodeKey) : Prop :=
  ∃ tree, GuardCorrespondence.CompiledDerivesAt grammar input
    key.category key.start key.stop tree

theorem mem_positionsFrom_iff
  {input : List Codepoint} {start position : Nat} :
    position ∈ positionsFrom input start ↔
      start ≤ position ∧ position ≤ input.length := by
  simp [positionsFrom, Nat.lt_succ_iff, and_comm]

mutual
  theorem compiledDerives_start_le_stop
      {grammar : GuardCorrespondence.CompiledGrammar}
      {input : List Codepoint} {category start stop tree}
      (derivation : GuardCorrespondence.CompiledDerivesAt grammar input
        category start stop tree) :
      start ≤ stop := by
    cases derivation with
    | apply production member body guards =>
        exact compiledBody_start_le_stop body

  theorem compiledBody_start_le_stop
      {grammar : GuardCorrespondence.CompiledGrammar}
      {input : List Codepoint} {symbols start stop trees}
      (derivation : GuardCorrespondence.CompiledBodyDerivesAt grammar input
        symbols start stop trees) :
      start ≤ stop := by
    cases derivation with
    | nil => exact Nat.le_refl _
    | terminal lookup rest =>
        exact Nat.le_trans (Nat.le_succ start)
          (compiledBody_start_le_stop rest)
    | anyTerminal lookup rest =>
        exact Nat.le_trans (Nat.le_succ start)
          (compiledBody_start_le_stop rest)
    | oneOfTerminal lookup member rest =>
        exact Nat.le_trans (Nat.le_succ start)
          (compiledBody_start_le_stop rest)
    | nonterminal head rest =>
        exact Nat.le_trans (compiledDerives_start_le_stop head)
          (compiledBody_start_le_stop rest)
end

mutual
  theorem compiledDerives_stop_le_length
      {grammar : GuardCorrespondence.CompiledGrammar}
      {input : List Codepoint} {category start stop tree}
      (derivation : GuardCorrespondence.CompiledDerivesAt grammar input
        category start stop tree)
      (startBound : start ≤ input.length) :
      stop ≤ input.length := by
    cases derivation with
    | apply production member body guards =>
        exact compiledBody_stop_le_length body startBound

  theorem compiledBody_stop_le_length
      {grammar : GuardCorrespondence.CompiledGrammar}
      {input : List Codepoint} {symbols start stop trees}
      (derivation : GuardCorrespondence.CompiledBodyDerivesAt grammar input
        symbols start stop trees)
      (startBound : start ≤ input.length) :
      stop ≤ input.length := by
    cases derivation with
    | nil => exact startBound
    | terminal lookup rest =>
        have nextBound : start + 1 ≤ input.length := by
          exact (List.getElem?_eq_some_iff.mp lookup).choose
        exact compiledBody_stop_le_length rest nextBound
    | anyTerminal lookup rest =>
        have nextBound : start + 1 ≤ input.length := by
          exact (List.getElem?_eq_some_iff.mp lookup).choose
        exact compiledBody_stop_le_length rest nextBound
    | oneOfTerminal lookup member rest =>
        have nextBound : start + 1 ≤ input.length := by
          exact (List.getElem?_eq_some_iff.mp lookup).choose
        exact compiledBody_stop_le_length rest nextBound
    | nonterminal head rest =>
        have middleBound := compiledDerives_stop_le_length head startBound
        exact compiledBody_stop_le_length rest middleBound
end

theorem groundBody_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {symbols start plan}
    (member : plan ∈ groundBody input symbols start)
    (premisesValid : ∀ key, key ∈ plan.premises →
      NodeValid grammar input key) :
    ∃ trees, GuardCorrespondence.CompiledBodyDerivesAt grammar input
      symbols start plan.stop trees := by
  induction symbols generalizing start plan with
  | nil =>
      simp [groundBody] at member
      subst plan
      exact ⟨[], .nil⟩
  | cons symbol symbols inductionHypothesis =>
      cases symbol with
      | terminal expected =>
          cases lookup : input[start]? with
          | none => simp [groundBody, lookup] at member
          | some actual =>
              by_cases equality : actual = expected
              · simp only [groundBody, lookup, equality, if_pos] at member
                obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp member
                obtain ⟨trees, derivation⟩ :=
                  inductionHypothesis restMember (by
                    intro key keyMember
                    exact premisesValid key keyMember)
                subst actual
                exact ⟨.terminal expected :: trees,
                  .terminal lookup derivation⟩
              · simp [groundBody, lookup, equality] at member
      | anyTerminal =>
          cases lookup : input[start]? with
          | none => simp [groundBody, lookup] at member
          | some codepoint =>
              simp only [groundBody, lookup] at member
              obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp member
              obtain ⟨trees, derivation⟩ :=
                inductionHypothesis restMember (by
                  intro key keyMember
                  exact premisesValid key keyMember)
              exact ⟨.terminal codepoint :: trees,
                .anyTerminal lookup derivation⟩
      | oneOfTerminal choices =>
          cases lookup : input[start]? with
          | none => simp [groundBody, lookup] at member
          | some codepoint =>
              by_cases choiceMember : codepoint ∈ choices
              · simp only [groundBody, lookup, choiceMember, if_pos] at member
                obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp member
                obtain ⟨trees, derivation⟩ :=
                  inductionHypothesis restMember (by
                    intro key keyMember
                    exact premisesValid key keyMember)
                exact ⟨.terminal codepoint :: trees,
                  .oneOfTerminal lookup choiceMember derivation⟩
              · simp [groundBody, lookup, choiceMember] at member
      | nonterminal category =>
          simp only [groundBody] at member
          obtain ⟨middle, middleMember, mappedMember⟩ :=
            List.mem_flatMap.mp member
          obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp mappedMember
          let key : NodeKey :=
            { category := category, start := start, stop := middle }
          obtain ⟨tree, head⟩ := premisesValid key (by
            simp [key])
          obtain ⟨trees, tail⟩ :=
            inductionHypothesis restMember (by
              intro premise premiseMember
              exact premisesValid premise (by
                simp [premiseMember]))
          exact ⟨tree :: trees, .nonterminal head tail⟩

theorem groundGuards_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {guards cursor plan}
    (member : plan ∈ groundGuards input guards cursor)
    (premisesValid : ∀ key, key ∈ plan.premises →
      NodeValid grammar input key) :
    GuardCorrespondence.CompiledGuardsHold grammar input guards cursor := by
  induction guards generalizing plan with
  | nil =>
      simp [groundGuards] at member
      subst plan
      exact .nil
  | cons guard guards inductionHypothesis =>
      cases guard with
      | atEnd =>
          by_cases endEq : cursor = input.length
          · simp only [groundGuards, endEq, if_pos] at member
            subst cursor
            exact .atEnd rfl (inductionHypothesis member premisesValid)
          · simp [groundGuards, endEq] at member
      | nextIn choices allowEof =>
          cases lookup : input[cursor]? with
          | some codepoint =>
              by_cases choiceMember : codepoint ∈ choices
              · simp only [groundGuards, lookup, choiceMember, if_pos] at member
                exact .nextIn lookup choiceMember
                  (inductionHypothesis member premisesValid)
              · simp [groundGuards, lookup, choiceMember] at member
          | none =>
              by_cases accepted : allowEof && cursor = input.length
              · simp only [groundGuards, lookup, accepted, if_pos] at member
                simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
                exact .nextInEof accepted.1 accepted.2
                  (inductionHypothesis member premisesValid)
              · simp [groundGuards, lookup, accepted] at member
      | lookahead category =>
          simp only [groundGuards] at member
          obtain ⟨witnessStop, stopMember, mappedMember⟩ :=
            List.mem_flatMap.mp member
          obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp mappedMember
          let key : NodeKey :=
            { category := category, start := cursor, stop := witnessStop }
          obtain ⟨tree, witness⟩ := premisesValid key (by simp [key])
          have tail := inductionHypothesis restMember (by
            intro premise premiseMember
            exact premisesValid premise (by simp [premiseMember]))
          exact .lookahead witness tail

theorem groundInstance_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {grounding : GroundInstance}
    (member : grounding ∈ groundInstances grammar input)
    (premisesValid : ∀ key, key ∈ grounding.premises →
      NodeValid grammar input key) :
    NodeValid grammar input grounding.parent := by
  unfold groundInstances at member
  obtain ⟨production, productionMember, productionGrounding⟩ :=
    List.mem_flatMap.mp member
  rw [groundProduction] at productionGrounding
  obtain ⟨start, startMember, bodyGrounding⟩ :=
    List.mem_flatMap.mp productionGrounding
  obtain ⟨body, bodyMember, guardGrounding⟩ :=
    List.mem_flatMap.mp bodyGrounding
  obtain ⟨guards, guardsMember, groundingEq⟩ :=
    List.mem_map.mp guardGrounding
  subst grounding
  obtain ⟨trees, bodyDerivation⟩ := groundBody_sound bodyMember (by
    intro key keyMember
    exact premisesValid key (by
      simp [GroundInstance.premises, keyMember]))
  have guardDerivation := groundGuards_sound guardsMember (by
    intro key keyMember
    exact premisesValid key (by
      simp [GroundInstance.premises, keyMember]))
  exact ⟨.node production.sourceRule production.category trees,
    .apply production productionMember bodyDerivation guardDerivation⟩

def AtomValid (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : ChartAtom → Prop
  | .node key => NodeValid grammar input key
  | .instance grounding =>
      grounding ∈ groundInstances grammar input ∧
        ∀ key, key ∈ grounding.premises → NodeValid grammar input key

theorem derivable_atom_valid
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (atom : ChartAtom)
    (derivation : Derivable (chartProgram grammar input) ∅ atom) :
    AtomValid grammar input atom := by
  induction derivation with
  | fact member => simp at member
  | @rule rule ruleMember premises inductionHypothesis =>
      simp only [chartProgram, Finset.mem_union, Finset.mem_image] at ruleMember
      rcases ruleMember with generated | promoted
      · obtain ⟨grounding, groundingMember, ruleEq⟩ := generated
        subst rule
        have groundingListMember : grounding ∈ groundInstances grammar input := by
          simpa using groundingMember
        exact ⟨groundingListMember, by
          intro key keyMember
          have premiseMember : .node key ∈ (instanceRule grounding).premises := by
            simpa [instanceRule] using keyMember
          exact inductionHypothesis (.node key) premiseMember⟩
      · obtain ⟨grounding, groundingMember, ruleEq⟩ := promoted
        subst rule
        have instanceValid := inductionHypothesis (.instance grounding) (by
          simp [promotionRule])
        exact groundInstance_sound instanceValid.1 instanceValid.2

theorem chart_node_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {key : NodeKey}
    (member : .node key ∈ chart grammar input) :
    NodeValid grammar input key := by
  exact derivable_atom_valid grammar input (.node key)
    ((FiniteHornSaturation.saturate_iff_derivable
      (chartProgram grammar input) ∅ (.node key)).mp member)

theorem chart_root_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint}
    (member : ChartAtom.node
        ({ category := grammar.start, start := 0,
           stop := input.length } : NodeKey) ∈ chart grammar input) :
    ∃ tree, GuardCorrespondence.CompiledDerivesAt grammar input
      grammar.start 0 input.length tree :=
  chart_node_sound member

theorem groundInstance_enters_chart
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {grounding : GroundInstance}
    (groundingMember : grounding ∈ groundInstances grammar input)
    (premisesPresent : ∀ key, key ∈ grounding.premises →
      ChartAtom.node key ∈ chart grammar input) :
    ChartAtom.instance grounding ∈ chart grammar input := by
  change ChartAtom.instance grounding ∈
    FiniteHornSaturation.saturate (chartProgram grammar input) ∅
  apply FiniteHornSaturation.saturate_rule_closed
    (program := chartProgram grammar input) (facts := ∅)
    (rule := instanceRule grounding)
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
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {grounding : GroundInstance}
    (groundingMember : grounding ∈ groundInstances grammar input)
    (instancePresent : ChartAtom.instance grounding ∈ chart grammar input) :
    ChartAtom.node grounding.parent ∈ chart grammar input := by
  change ChartAtom.node grounding.parent ∈
    FiniteHornSaturation.saturate (chartProgram grammar input) ∅
  apply FiniteHornSaturation.saturate_rule_closed
    (program := chartProgram grammar input) (facts := ∅)
    (rule := promotionRule grounding)
  · unfold chartProgram
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨grounding, by simpa using groundingMember, rfl⟩
  · intro atom atomMember
    have atomEq : atom = ChartAtom.instance grounding := by
      simpa [promotionRule] using atomMember
    subst atom
    exact instancePresent

theorem compiledDerivation_chart_complete
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {category start stop tree}
    (derivation : GuardCorrespondence.CompiledDerivesAt grammar input
      category start stop tree)
    (startBound : start ≤ input.length) :
    ChartAtom.node { category := category, start := start, stop := stop } ∈
      chart grammar input := by
  exact GuardCorrespondence.CompiledDerivesAt.rec
    (motive_1 := fun category start stop tree _ =>
      start ≤ input.length →
        ChartAtom.node { category := category, start := start, stop := stop } ∈
          chart grammar input)
    (motive_2 := fun symbols start stop trees _ =>
      start ≤ input.length →
        ∃ plan,
          plan ∈ groundBody input symbols start ∧
          plan.stop = stop ∧
          ∀ key, key ∈ plan.premises →
            ChartAtom.node key ∈ chart grammar input)
    (motive_3 := fun guards cursor _ =>
      cursor ≤ input.length →
        ∃ plan,
          plan ∈ groundGuards input guards cursor ∧
          ∀ key, key ∈ plan.premises →
            ChartAtom.node key ∈ chart grammar input)
    (fun {start} {stop} {children} production productionMember body guards
        bodyComplete guardsComplete startBound => by
      obtain ⟨bodyPlan, bodyMember, bodyStop, bodyPremises⟩ :=
        bodyComplete startBound
      have stopBound := compiledBody_stop_le_length body startBound
      obtain ⟨guardPlan, guardMember, guardPremises⟩ :=
        guardsComplete stopBound
      let grounding : GroundInstance :=
        { production := production
          start := start
          body := bodyPlan
          guards := guardPlan }
      have groundingMember : grounding ∈ groundInstances grammar input := by
        unfold groundInstances
        apply List.mem_flatMap.mpr
        refine ⟨production, productionMember, ?_⟩
        rw [groundProduction]
        apply List.mem_flatMap.mpr
        refine ⟨start,
          mem_positionsFrom_iff.mpr ⟨Nat.zero_le _, startBound⟩, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨bodyPlan, bodyMember, ?_⟩
        exact List.mem_map.mpr ⟨guardPlan, by simpa [bodyStop] using guardMember,
          rfl⟩
      have allPremises : ∀ key, key ∈ grounding.premises →
          ChartAtom.node key ∈ chart grammar input := by
        intro key keyMember
        rcases List.mem_append.mp keyMember with bodyKey | guardKey
        · exact bodyPremises key bodyKey
        · exact guardPremises key guardKey
      have entered := groundInstance_enters_chart groundingMember allPremises
      have promoted := groundInstance_promotes groundingMember entered
      simpa [grounding, GroundInstance.parent, bodyStop] using promoted)
    (fun cursorBound =>
      ⟨{ stop := _, children := [], premises := [] }, by simp [groundBody],
        rfl, by simp⟩)
    (fun {start} {codepoint} {symbols} {stop} {children}
        lookup _ restComplete startBound => by
      have nextBound : start + 1 ≤ input.length :=
        (List.getElem?_eq_some_iff.mp lookup).choose
      obtain ⟨restPlan, restMember, restStop, restPremises⟩ :=
        restComplete nextBound
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .terminal codepoint start (start + 1) :: restPlan.children
          premises := restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_⟩
      · simp only [groundBody, lookup, if_pos]
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · intro key keyMember
        exact restPremises key (by simpa [plan] using keyMember))
    (fun {start} {codepoint} {symbols} {stop} {children}
        lookup _ restComplete startBound => by
      have nextBound : start + 1 ≤ input.length :=
        (List.getElem?_eq_some_iff.mp lookup).choose
      obtain ⟨restPlan, restMember, restStop, restPremises⟩ :=
        restComplete nextBound
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .terminal codepoint start (start + 1) :: restPlan.children
          premises := restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_⟩
      · simp only [groundBody, lookup]
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · intro key keyMember
        exact restPremises key (by simpa [plan] using keyMember))
    (fun {start} {codepoint} {codepoints} {symbols} {stop} {children}
        lookup codepointMember _ restComplete startBound => by
      have nextBound : start + 1 ≤ input.length :=
        (List.getElem?_eq_some_iff.mp lookup).choose
      obtain ⟨restPlan, restMember, restStop, restPremises⟩ :=
        restComplete nextBound
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .terminal codepoint start (start + 1) :: restPlan.children
          premises := restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_⟩
      · simp only [groundBody, lookup, codepointMember, if_pos]
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · intro key keyMember
        exact restPremises key (by simpa [plan] using keyMember))
    (fun {category} {start} {middle} {tree} {symbols} {stop} {children}
        head rest headComplete restComplete startBound => by
      have middleLower := compiledDerives_start_le_stop head
      have middleBound := compiledDerives_stop_le_length head startBound
      have headPresent := headComplete startBound
      obtain ⟨restPlan, restMember, restStop, restPremises⟩ :=
        restComplete middleBound
      let key : NodeKey :=
        { category := category, start := start, stop := middle }
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .node key :: restPlan.children
          premises := key :: restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_⟩
      · simp only [groundBody]
        apply List.mem_flatMap.mpr
        refine ⟨middle,
          mem_positionsFrom_iff.mpr ⟨middleLower, middleBound⟩, ?_⟩
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · intro premise premiseMember
        simp only [plan, List.mem_cons] at premiseMember
        rcases premiseMember with rfl | tailMember
        · simpa [key] using headPresent
        · exact restPremises premise tailMember)
    (fun cursorBound =>
      ⟨{ premises := [] }, by simp [groundGuards], by simp⟩)
    (fun endEq rest restComplete cursorBound => by
      obtain ⟨plan, planMember, planPremises⟩ := restComplete cursorBound
      refine ⟨plan, ?_, planPremises⟩
      simpa [groundGuards, endEq] using planMember)
    (fun lookup codepointMember rest restComplete cursorBound => by
      obtain ⟨plan, planMember, planPremises⟩ := restComplete cursorBound
      refine ⟨plan, ?_, planPremises⟩
      simpa [groundGuards, lookup, codepointMember] using planMember)
    (fun {allowEof} {cursor} {guards} {codepoints}
        allowed endEq rest restComplete cursorBound => by
      subst cursor
      obtain ⟨plan, planMember, planPremises⟩ :=
        restComplete (Nat.le_refl _)
      have lookupNone : input[input.length]? = none := by simp
      refine ⟨plan, ?_, planPremises⟩
      simpa [groundGuards, lookupNone, allowed] using planMember)
    (fun {category} {cursor} {witnessStop} {tree} {guards} witness rest
        witnessComplete restComplete cursorBound => by
      have witnessLower := compiledDerives_start_le_stop witness
      have witnessBound := compiledDerives_stop_le_length witness cursorBound
      have witnessPresent := witnessComplete cursorBound
      obtain ⟨restPlan, restMember, restPremises⟩ := restComplete cursorBound
      let key : NodeKey :=
        { category := category, start := cursor, stop := witnessStop }
      let plan : GuardPlan := { premises := key :: restPlan.premises }
      refine ⟨plan, ?_, ?_⟩
      · simp only [groundGuards]
        apply List.mem_flatMap.mpr
        refine ⟨witnessStop,
          mem_positionsFrom_iff.mpr ⟨witnessLower, witnessBound⟩, ?_⟩
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · intro premise premiseMember
        simp only [plan, List.mem_cons] at premiseMember
        rcases premiseMember with rfl | tailMember
        · simpa [key] using witnessPresent
        · exact restPremises premise tailMember)
    derivation startBound

theorem chart_root_complete
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {tree : ParseTree}
    (derivation : GuardCorrespondence.CompiledDerivesAt grammar input
      grammar.start 0 input.length tree) :
    ChartAtom.node
      ({ category := grammar.start, start := 0, stop := input.length } : NodeKey) ∈
      chart grammar input :=
  compiledDerivation_chart_complete derivation (Nat.zero_le _)

theorem chart_root_iff_compiled_result
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) :
    ChartAtom.node
      ({ category := grammar.start, start := 0, stop := input.length } : NodeKey) ∈
        chart grammar input ↔
      ∃ tree, GuardCorrespondence.CompiledDerivesAt grammar input
        grammar.start 0 input.length tree := by
  constructor
  · exact chart_root_sound
  · rintro ⟨tree, derivation⟩
    exact chart_root_complete derivation

theorem compiledGuards_ground_complete
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {guards cursor}
    (derivation : GuardCorrespondence.CompiledGuardsHold grammar input
      guards cursor)
    (cursorBound : cursor ≤ input.length) :
    ∃ plan,
      plan ∈ groundGuards input guards cursor ∧
      ∀ key, key ∈ plan.premises →
        ChartAtom.node key ∈ chart grammar input := by
  induction guards with
  | nil =>
      exact ⟨{ premises := [] }, by simp [groundGuards], by simp⟩
  | cons guard guards inductionHypothesis =>
      cases guard with
      | atEnd =>
          cases derivation with
          | atEnd endEq rest =>
              obtain ⟨plan, planMember, planPremises⟩ :=
                inductionHypothesis rest
              exact ⟨plan, by simpa [groundGuards, endEq] using planMember,
                planPremises⟩
      | nextIn codepoints allowEof =>
          cases derivation with
          | nextIn lookup codepointMember rest =>
              obtain ⟨plan, planMember, planPremises⟩ :=
                inductionHypothesis rest
              exact ⟨plan,
                by simpa [groundGuards, lookup, codepointMember] using planMember,
                planPremises⟩
          | nextInEof allowed endEq rest =>
              subst cursor
              obtain ⟨plan, planMember, planPremises⟩ :=
                inductionHypothesis rest
              have lookupNone : input[input.length]? = none := by simp
              exact ⟨plan,
                by simpa [groundGuards, lookupNone, allowed] using planMember,
                planPremises⟩
      | lookahead category =>
          cases derivation with
          | lookahead witness rest =>
              rename_i witnessStop tree
              obtain ⟨restPlan, restMember, restPremises⟩ :=
                inductionHypothesis rest
              have witnessLower := compiledDerives_start_le_stop witness
              have witnessBound :=
                compiledDerives_stop_le_length witness cursorBound
              have witnessPresent :=
                compiledDerivation_chart_complete witness cursorBound
              let key : NodeKey :=
                { category := category, start := cursor, stop := witnessStop }
              let plan : GuardPlan :=
                { premises := key :: restPlan.premises }
              refine ⟨plan, ?_, ?_⟩
              · simp only [groundGuards]
                apply List.mem_flatMap.mpr
                refine ⟨witnessStop,
                  mem_positionsFrom_iff.mpr ⟨witnessLower, witnessBound⟩, ?_⟩
                exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
              · intro premise premiseMember
                simp only [plan, List.mem_cons] at premiseMember
                rcases premiseMember with rfl | tailMember
                · simpa [key] using witnessPresent
                · exact restPremises premise tailMember

theorem groundInstance_family_mem_chartForest
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {grounding : GroundInstance}
    (groundingMember : grounding ∈ groundInstances grammar input)
    (instancePresent : ChartAtom.instance grounding ∈ chart grammar input) :
    grounding.family ∈ (chartForest grammar input).families := by
  simp only [chartForest, List.mem_filterMap]
  refine ⟨grounding, groundingMember, ?_⟩
  rw [if_pos instancePresent]

theorem mem_certificatesFamilies_iff
    {family : Family} {certificates : List Certificate} :
    family ∈ certificatesFamilies certificates ↔
      ∃ certificate, certificate ∈ certificates ∧
        family ∈ certificateFamilies certificate := by
  induction certificates with
  | nil => simp [certificatesFamilies]
  | cons certificate certificates inductionHypothesis =>
      simp only [certificatesFamilies, List.mem_append, inductionHypothesis,
        List.mem_cons]
      constructor
      · intro member
        rcases member with member | ⟨child, childMember, familyMember⟩
        · exact ⟨certificate, Or.inl rfl, member⟩
        · exact ⟨child, Or.inr childMember, familyMember⟩
      · rintro ⟨child, rfl | childMember, familyMember⟩
        · exact Or.inl familyMember
        · exact Or.inr ⟨child, childMember, familyMember⟩

theorem certificateReplay_chart_unfolds
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {certificate category start stop tree}
    (replay : GuardCorrespondence.CertificateReplays grammar input certificate
      category start stop tree)
    (startBound : start ≤ input.length) :
    ChartAtom.node { category := category, start := start, stop := stop } ∈
        chart grammar input ∧
      Unfolds (chartForest grammar input) certificate := by
  exact GuardCorrespondence.CertificateReplays.rec
    (motive_1 := fun certificate category start stop tree _ =>
      start ≤ input.length →
        ChartAtom.node { category := category, start := start, stop := stop } ∈
            chart grammar input ∧
          Unfolds (chartForest grammar input) certificate)
    (motive_2 := fun symbols start stop certificates trees _ =>
      start ≤ input.length →
        ∃ plan,
          plan ∈ groundBody input symbols start ∧
          plan.stop = stop ∧
          plan.children = certificates.map certificateRef ∧
          (∀ key, key ∈ plan.premises →
            ChartAtom.node key ∈ chart grammar input) ∧
          (∀ child, child ∈ certificates →
            Unfolds (chartForest grammar input) child))
    (fun {start} {stop} {certificates} {trees}
        production productionMember body guards bodyComplete startBound => by
      obtain ⟨bodyPlan, bodyMember, bodyStop, bodyChildren,
          bodyPremises, childrenUnfold⟩ := bodyComplete startBound
      have compiledBody :=
        GuardCorrespondence.certificate_body_replay_compiled_sound body
      have stopBound := compiledBody_stop_le_length compiledBody startBound
      obtain ⟨guardPlan, guardMember, guardPremises⟩ :=
        compiledGuards_ground_complete guards stopBound
      let grounding : GroundInstance :=
        { production := production
          start := start
          body := bodyPlan
          guards := guardPlan }
      have groundingMember : grounding ∈ groundInstances grammar input := by
        unfold groundInstances
        apply List.mem_flatMap.mpr
        refine ⟨production, productionMember, ?_⟩
        rw [groundProduction]
        apply List.mem_flatMap.mpr
        refine ⟨start,
          mem_positionsFrom_iff.mpr ⟨Nat.zero_le _, startBound⟩, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨bodyPlan, bodyMember, ?_⟩
        exact List.mem_map.mpr ⟨guardPlan,
          by simpa [bodyStop] using guardMember, rfl⟩
      have allPremises : ∀ key, key ∈ grounding.premises →
          ChartAtom.node key ∈ chart grammar input := by
        intro key keyMember
        rcases List.mem_append.mp keyMember with bodyKey | guardKey
        · exact bodyPremises key bodyKey
        · exact guardPremises key guardKey
      have instancePresent :=
        groundInstance_enters_chart groundingMember allPremises
      have nodePresent := groundInstance_promotes groundingMember instancePresent
      have storedFamily :=
        groundInstance_family_mem_chartForest groundingMember instancePresent
      constructor
      · simpa [grounding, GroundInstance.parent, bodyStop] using nodePresent
      · intro family familyMember
        simp only [certificateFamilies, certificateFamily, Option.toList_some,
          List.singleton_append, List.mem_cons] at familyMember
        rcases familyMember with rootFamily | childFamily
        · subst family
          simpa [grounding, GroundInstance.family, GroundInstance.parent,
            bodyStop, bodyChildren] using storedFamily
        · obtain ⟨child, childMember, memberInChild⟩ :=
            mem_certificatesFamilies_iff.mp childFamily
          exact childrenUnfold child childMember _ memberInChild)
    (fun cursorBound =>
      ⟨{ stop := _, children := [], premises := [] }, by simp [groundBody],
        rfl, by simp, by simp, by simp⟩)
    (fun {start} {codepoint} {symbols} {stop} {certificates} {trees}
        lookup rest restComplete startBound => by
      have nextBound : start + 1 ≤ input.length :=
        (List.getElem?_eq_some_iff.mp lookup).choose
      obtain ⟨restPlan, restMember, restStop, restChildren,
          restPremises, restUnfold⟩ := restComplete nextBound
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .terminal codepoint start (start + 1) :: restPlan.children
          premises := restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_, ?_, ?_⟩
      · simp only [groundBody, lookup, if_pos]
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · simp [plan, restChildren, certificateRef]
      · intro key keyMember
        exact restPremises key (by simpa [plan] using keyMember)
      · intro child childMember
        simp only [List.mem_cons] at childMember
        rcases childMember with childEq | tailMember
        · subst child
          intro family familyMember
          simp [certificateFamilies] at familyMember
        · exact restUnfold child tailMember)
    (fun {start} {codepoint} {symbols} {stop} {certificates} {trees}
        lookup rest restComplete startBound => by
      have nextBound : start + 1 ≤ input.length :=
        (List.getElem?_eq_some_iff.mp lookup).choose
      obtain ⟨restPlan, restMember, restStop, restChildren,
          restPremises, restUnfold⟩ := restComplete nextBound
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .terminal codepoint start (start + 1) :: restPlan.children
          premises := restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_, ?_, ?_⟩
      · simp only [groundBody, lookup]
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · simp [plan, restChildren, certificateRef]
      · intro key keyMember
        exact restPremises key (by simpa [plan] using keyMember)
      · intro child childMember
        simp only [List.mem_cons] at childMember
        rcases childMember with childEq | tailMember
        · subst child
          intro family familyMember
          simp [certificateFamilies] at familyMember
        · exact restUnfold child tailMember)
    (fun {start} {codepoint} {codepoints} {symbols} {stop}
        {certificates} {trees} lookup codepointMember rest restComplete
        startBound => by
      have nextBound : start + 1 ≤ input.length :=
        (List.getElem?_eq_some_iff.mp lookup).choose
      obtain ⟨restPlan, restMember, restStop, restChildren,
          restPremises, restUnfold⟩ := restComplete nextBound
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .terminal codepoint start (start + 1) :: restPlan.children
          premises := restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_, ?_, ?_⟩
      · simp only [groundBody, lookup, codepointMember, if_pos]
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · simp [plan, restChildren, certificateRef]
      · intro key keyMember
        exact restPremises key (by simpa [plan] using keyMember)
      · intro child childMember
        simp only [List.mem_cons] at childMember
        rcases childMember with childEq | tailMember
        · subst child
          intro family familyMember
          simp [certificateFamilies] at familyMember
        · exact restUnfold child tailMember)
    (fun {sourceRule} {category} {start} {middle} {childCertificates}
        {tree} {symbols} {stop} {certificates} {trees}
        head rest headComplete restComplete startBound => by
      have compiledHead :=
        GuardCorrespondence.certificate_replay_compiled_sound head
      have middleLower := compiledDerives_start_le_stop compiledHead
      have middleBound := compiledDerives_stop_le_length compiledHead startBound
      obtain ⟨headPresent, headUnfold⟩ := headComplete startBound
      obtain ⟨restPlan, restMember, restStop, restChildren,
          restPremises, restUnfold⟩ := restComplete middleBound
      let key : NodeKey :=
        { category := category, start := start, stop := middle }
      let plan : BodyPlan :=
        { stop := restPlan.stop
          children := .node key :: restPlan.children
          premises := key :: restPlan.premises }
      refine ⟨plan, ?_, by simpa [plan] using restStop, ?_, ?_, ?_⟩
      · simp only [groundBody]
        apply List.mem_flatMap.mpr
        refine ⟨middle,
          mem_positionsFrom_iff.mpr ⟨middleLower, middleBound⟩, ?_⟩
        exact List.mem_map.mpr ⟨restPlan, restMember, rfl⟩
      · simp [plan, key, restChildren, certificateRef]
      · intro premise premiseMember
        simp only [plan, List.mem_cons] at premiseMember
        rcases premiseMember with rfl | tailMember
        · simpa [key] using headPresent
        · exact restPremises premise tailMember
      · intro child childMember
        simp only [List.mem_cons] at childMember
        rcases childMember with childEq | tailMember
        · subst child
          exact headUnfold
        · exact restUnfold child tailMember)
    replay startBound

theorem certificateReplay_key
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {certificate category start stop tree}
    (replay : GuardCorrespondence.CertificateReplays grammar input certificate
      category start stop tree) :
    certificateKey certificate =
      some { category := category, start := start, stop := stop } := by
  cases replay
  rfl

theorem certificateReplay_chart_root_unfolds
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {certificate tree}
    (replay : GuardCorrespondence.CertificateReplays grammar input certificate
      grammar.start 0 input.length tree) :
    RootUnfolds (chartForest grammar input) certificate := by
  obtain ⟨nodePresent, unfolds⟩ :=
    certificateReplay_chart_unfolds replay (Nat.zero_le _)
  let root : NodeKey :=
    { category := grammar.start, start := 0, stop := input.length }
  refine ⟨root, ?_, ?_, unfolds⟩
  · simpa [root] using certificateReplay_key replay
  · simp [chartForest, root, nodePresent]

theorem compiledDerivation_has_chart_packed_witness
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {tree}
    (derivation : GuardCorrespondence.CompiledDerivesAt grammar input
      grammar.start 0 input.length tree) :
    ∃ certificate,
      RootUnfolds (chartForest grammar input) certificate ∧
      GuardCorrespondence.CertificateReplays grammar input certificate
        grammar.start 0 input.length tree := by
  obtain ⟨certificate, replay⟩ :=
    compiled_derivation_has_certificate derivation
  exact ⟨certificate, certificateReplay_chart_root_unfolds replay, replay⟩

/-- The finite grounded chart is complete for an arbitrary admitted compiled
grammar, including guarded and finite-terminal-set productions. -/
theorem chartForest_grammar_complete
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) :
    GrammarComplete (chartForest grammar input) grammar input := by
  intro tree derivation
  obtain ⟨certificate, rootUnfolds, replay⟩ :=
    compiledDerivation_has_chart_packed_witness derivation
  have spans := BoundedScheduler.certificateReplays_spans replay
  exact ⟨certificate, rootUnfolds, replay, spans⟩

theorem chartForest_grammar_result_set_agreement
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) :
    grammarPackedResults (chartForest grammar input) grammar input =
      GuardCorrespondence.grammarResults grammar input :=
  grammar_complete_result_set_agreement
    (chartForest_grammar_complete grammar input)

theorem chartForest_grammar_ambiguity_agreement
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) :
    PackedForest.Ambiguous
        (grammarPackedResults (chartForest grammar input) grammar input) ↔
      PackedForest.Ambiguous
        (GuardCorrespondence.grammarResults grammar input) :=
  grammar_complete_ambiguity_agreement
    (chartForest_grammar_complete grammar input)

theorem chartForest_complete
    (presentation : GuardCorrespondence.SourceDefinition)
    (input : List Codepoint) :
    Complete
      (chartForest (GuardCorrespondence.compile presentation) input)
      presentation input := by
  intro tree sourceDerivation
  have compiledDerivation :=
    GuardCorrespondence.compile_preserves sourceDerivation
  obtain ⟨certificate, rootUnfolds, replay⟩ :=
    compiledDerivation_has_chart_packed_witness compiledDerivation
  have spans := BoundedScheduler.certificateReplays_spans replay
  exact ⟨certificate, rootUnfolds, replay, spans⟩

theorem chartForest_result_set_agreement
    (presentation : GuardCorrespondence.SourceDefinition)
    (input : List Codepoint) :
    packedResults
        (chartForest (GuardCorrespondence.compile presentation) input)
        presentation input =
      GuardCorrespondence.sourceResults presentation input :=
  complete_result_set_agreement (chartForest_complete presentation input)

theorem chartForest_ambiguity_agreement
    (presentation : GuardCorrespondence.SourceDefinition)
    (input : List Codepoint) :
    PackedForest.Ambiguous
        (packedResults
          (chartForest (GuardCorrespondence.compile presentation) input)
          presentation input) ↔
      PackedForest.Ambiguous
        (GuardCorrespondence.sourceResults presentation input) :=
  complete_ambiguity_agreement (chartForest_complete presentation input)

theorem chart_saturation_fixed
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) :
    step (chartProgram grammar input) (chart grammar input) =
      chart grammar input :=
  FiniteHornSaturation.saturate_fixed (chartProgram grammar input) ∅

/-! ## Executable grounding controls -/

def controlPresentation : GuardCorrespondence.SourceDefinition :=
  { start := "start"
    rules := [
      { sourceRule := "left", category := "start",
        symbols := [.exact 97], guards := [.atEnd] },
      { sourceRule := "right", category := "start",
        symbols := [.exact 97], guards := [.atEnd] }] }

def controlGrammar : GuardCorrespondence.CompiledGrammar :=
  GuardCorrespondence.compile controlPresentation

theorem control_has_two_ground_instances :
    (groundInstances controlGrammar [97]).length = 2 := by
  decide

theorem control_chart_has_root :
    .node { category := "start", start := 0, stop := 1 } ∈
      chart controlGrammar [97] := by
  decide

theorem control_forest_shares_root :
    (chartForest controlGrammar [97]).roots.length = 1 := by
  decide

theorem control_forest_retains_two_families :
    (chartForest controlGrammar [97]).families.length = 2 := by
  decide

theorem control_rejects_trailing_input :
    (chartForest controlGrammar [97, 98]).roots = [] := by
  decide

theorem productive_left_recursion_saturates :
    ChartAtom.node
      ({ category := "start", start := 0, stop := 2 } : NodeKey) ∈
      chart BoundedScheduler.leftRecursiveGrammar [97, 97] := by
  decide

theorem runtime_lookahead_saturates :
    ChartAtom.node
      ({ category := "start", start := 0, stop := 1 } : NodeKey) ∈
      chart
        (GuardCorrespondence.compile GuardCorrespondence.lookaheadPresentation)
        [97] := by
  decide

def compactedControlGrammar : GuardCorrespondence.CompiledGrammar :=
  { start := "start"
    productions :=
      [{ label := "letter", category := "start",
         symbols := [.oneOfTerminal [97, 98]], guards := [.atEnd],
         sourceRule := "letter" }] }

theorem compacted_terminal_accepts_first :
    ChartAtom.node
      ({ category := "start", start := 0, stop := 1 } : NodeKey) ∈
      chart compactedControlGrammar [97] := by
  decide

theorem compacted_terminal_accepts_second :
    ChartAtom.node
      ({ category := "start", start := 0, stop := 1 } : NodeKey) ∈
      chart compactedControlGrammar [98] := by
  decide

theorem compacted_terminal_rejects_outside :
    ChartAtom.node
      ({ category := "start", start := 0, stop := 1 } : NodeKey) ∉
      chart compactedControlGrammar [99] := by
  decide

end Mettapedia.GSLT.Parsing.GroundedChart
