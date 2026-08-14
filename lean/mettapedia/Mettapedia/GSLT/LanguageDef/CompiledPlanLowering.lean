import Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission

/-!
# Typed lowering to the compiled finite-Horn plan

This module is the stage immediately above the `CGP1` carrier.  Its input is a
typed, vocabulary-independent finite-Horn rule inventory; its output is the
postorder node forest consumed by the generic runtime.  Variable slots and
integer values are already physical carriers at this stage.  Earlier source
lowerings remain responsible for proving that those carriers refine authored
names and unbounded values.

The compiler is total, while `lower?` is fail-closed: the independent structural
admission pass must reconstruct an executable typed program from the emitted
tables.  No runtime fallback interprets a rejected shape.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanLowering

open CompiledPlanWireFormat
open CompiledPlanAdmission

/-! ## Typed input and append-only emitter -/

structure TypedRule where
  name : List UInt8
  head : Term
  body : List Term
  variableCount : UInt32
  deriving DecidableEq, Repr

abbrev TypedProgram := List TypedRule

structure Builder where
  nodeCount : Nat := 0
  nodesRev : List Node := []
  childCount : Nat := 0
  childrenRev : List UInt32 := []
  ruleCount : Nat := 0
  rulesRev : List Rule := []
  bodyCount : Nat := 0
  bodiesRev : List UInt32 := []
  deriving DecidableEq, Repr

def appendNode (builder : Builder) (node : Node) : UInt32 × Builder :=
  let index := UInt32.ofNat builder.nodeCount
  (index,
    { builder with
      nodeCount := builder.nodeCount + 1
      nodesRev := node :: builder.nodesRev })

def scalarNode (kind : UInt8) (integerValue : Int64)
    (variableSlot : UInt32) (text : List UInt8) : Node :=
  { kind
    childOffset := 0
    childCount := 0
    integerValue
    variableSlot
    text }

mutual

/-- Emit one typed term in strict postorder. -/
def emitTerm : Term -> Builder -> UInt32 × Builder
  | .symbol name, builder =>
      appendNode builder (scalarNode 1 0 0 name)
  | .variable slot, builder =>
      appendNode builder (scalarNode 2 0 slot [])
  | .string value, builder =>
      appendNode builder (scalarNode 3 0 0 value)
  | .integer value, builder =>
      appendNode builder (scalarNode 4 value 0 [])
  | .application head arguments, builder =>
      let (roots, afterArguments) := emitTerms arguments builder
      let childOffset := UInt32.ofNat afterArguments.childCount
      let withChildren :=
        { afterArguments with
          childCount := afterArguments.childCount + roots.length
          childrenRev := roots.reverse ++ afterArguments.childrenRev }
      appendNode withChildren
        { kind := 5
          childOffset
          childCount := UInt32.ofNat roots.length
          integerValue := 0
          variableSlot := 0
          text := head }

def emitTerms : Terms -> Builder -> List UInt32 × Builder
  | .nil, builder => ([], builder)
  | .cons head tail, builder =>
      let (root, afterHead) := emitTerm head builder
      let (roots, afterTail) := emitTerms tail afterHead
      (root :: roots, afterTail)

end

def emitTermList : List Term -> Builder -> List UInt32 × Builder
  | [], builder => ([], builder)
  | head :: tail, builder =>
      let (root, afterHead) := emitTerm head builder
      let (roots, afterTail) := emitTermList tail afterHead
      (root :: roots, afterTail)

def emitRule (builder : Builder) (rule : TypedRule) : Builder :=
  let (head, afterHead) := emitTerm rule.head builder
  let bodyOffset := UInt32.ofNat afterHead.bodyCount
  let (body, afterBody) := emitTermList rule.body afterHead
  { afterBody with
    ruleCount := afterBody.ruleCount + 1
    rulesRev :=
      { head
        bodyOffset
        bodyCount := UInt32.ofNat body.length
        variableCount := rule.variableCount
        name := rule.name } :: afterBody.rulesRev
    bodyCount := afterBody.bodyCount + body.length
    bodiesRev := body.reverse ++ afterBody.bodiesRev }

def emitRules : TypedProgram -> Builder -> Builder
  | [], builder => builder
  | rule :: rules, builder => emitRules rules (emitRule builder rule)

/-! ## Builder invariants and exact allocation counts -/

/-- The append-only counters coincide with the sizes of their reverse
accumulators.  This is the central invariant of the linear emitter: every
table entry is consed once, and the finished tables are reversed once. -/
def Builder.WellFormed (builder : Builder) : Prop :=
  builder.nodeCount = builder.nodesRev.length ∧
    builder.childCount = builder.childrenRev.length ∧
    builder.ruleCount = builder.rulesRev.length ∧
    builder.bodyCount = builder.bodiesRev.length

/-- Forward table views of the reverse append accumulators. -/
def Builder.nodes (builder : Builder) : List Node :=
  builder.nodesRev.reverse

def Builder.children (builder : Builder) : List UInt32 :=
  builder.childrenRev.reverse

def Builder.rules (builder : Builder) : List Rule :=
  builder.rulesRev.reverse

def Builder.bodies (builder : Builder) : List UInt32 :=
  builder.bodiesRev.reverse

@[simp] theorem Builder.nodes_length (builder : Builder) :
    builder.nodes.length = builder.nodesRev.length := by
  simp [Builder.nodes]

@[simp] theorem Builder.children_length (builder : Builder) :
    builder.children.length = builder.childrenRev.length := by
  simp [Builder.children]

@[simp] theorem Builder.rules_length (builder : Builder) :
    builder.rules.length = builder.rulesRev.length := by
  simp [Builder.rules]

@[simp] theorem Builder.bodies_length (builder : Builder) :
    builder.bodies.length = builder.bodiesRev.length := by
  simp [Builder.bodies]

@[simp] theorem Builder.empty_wellFormed : ({} : Builder).WellFormed := by
  simp [Builder.WellFormed]

theorem appendNode_wellFormed (builder : Builder) (node : Node)
    (wellFormed : builder.WellFormed) :
    (appendNode builder node).2.WellFormed := by
  rcases wellFormed with ⟨nodes, children, rules, bodies⟩
  simp [appendNode, Builder.WellFormed, nodes, children, rules, bodies]

mutual

theorem emitTerm_wellFormed (term : Term) (builder : Builder)
    (wellFormed : builder.WellFormed) :
    (emitTerm term builder).2.WellFormed := by
  cases term with
  | symbol name =>
      exact appendNode_wellFormed builder (scalarNode 1 0 0 name) wellFormed
  | «variable» slot =>
      exact appendNode_wellFormed builder (scalarNode 2 0 slot []) wellFormed
  | «string» value =>
      exact appendNode_wellFormed builder (scalarNode 3 0 0 value) wellFormed
  | integer value =>
      exact appendNode_wellFormed builder (scalarNode 4 value 0 []) wellFormed
  | application head arguments =>
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have argumentsWellFormed :=
            emitTerms_wellFormed arguments builder wellFormed
          rw [emitted] at argumentsWellFormed
          have withChildrenWellFormed :
              ({ afterArguments with
                  childCount := afterArguments.childCount + roots.length
                  childrenRev := roots.reverse ++ afterArguments.childrenRev } :
                Builder).WellFormed := by
            rcases argumentsWellFormed with
              ⟨nodes, children, rules, bodies⟩
            change afterArguments.nodeCount =
              afterArguments.nodesRev.length at nodes
            change afterArguments.childCount =
              afterArguments.childrenRev.length at children
            change afterArguments.ruleCount =
              afterArguments.rulesRev.length at rules
            change afterArguments.bodyCount =
              afterArguments.bodiesRev.length at bodies
            refine ⟨nodes, ?_, rules, bodies⟩
            simp only [List.length_append, List.length_reverse]
            omega
          simpa [emitTerm, emitted] using
            appendNode_wellFormed
              ({ afterArguments with
                  childCount := afterArguments.childCount + roots.length
                  childrenRev := roots.reverse ++ afterArguments.childrenRev } :
                Builder)
              { kind := 5
                childOffset := UInt32.ofNat afterArguments.childCount
                childCount := UInt32.ofNat roots.length
                integerValue := 0
                variableSlot := 0
                text := head }
              withChildrenWellFormed
termination_by sizeOf term

theorem emitTerms_wellFormed (terms : Terms) (builder : Builder)
    (wellFormed : builder.WellFormed) :
    (emitTerms terms builder).2.WellFormed := by
  cases terms with
  | nil => simpa [emitTerms] using wellFormed
  | cons head tail =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headWellFormed := emitTerm_wellFormed head builder wellFormed
          rw [emittedHead] at headWellFormed
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have tailWellFormed :=
                emitTerms_wellFormed tail afterHead headWellFormed
              rw [emittedTail] at tailWellFormed
              simpa [emitTerms, emittedHead, emittedTail] using tailWellFormed
termination_by sizeOf terms

end

theorem emitTermList_wellFormed (terms : List Term) (builder : Builder)
    (wellFormed : builder.WellFormed) :
    (emitTermList terms builder).2.WellFormed := by
  induction terms generalizing builder with
  | nil => simpa [emitTermList] using wellFormed
  | cons head tail inductionHypothesis =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headWellFormed := emitTerm_wellFormed head builder wellFormed
          rw [emittedHead] at headWellFormed
          cases emittedTail : emitTermList tail afterHead with
          | mk roots afterTail =>
              have tailWellFormed :=
                inductionHypothesis afterHead headWellFormed
              rw [emittedTail] at tailWellFormed
              simpa [emitTermList, emittedHead, emittedTail] using tailWellFormed

theorem emitRule_wellFormed (builder : Builder) (rule : TypedRule)
    (wellFormed : builder.WellFormed) :
    (emitRule builder rule).WellFormed := by
  cases emittedHead : emitTerm rule.head builder with
  | mk head afterHead =>
      have headWellFormed := emitTerm_wellFormed rule.head builder wellFormed
      rw [emittedHead] at headWellFormed
      cases emittedBody : emitTermList rule.body afterHead with
      | mk body afterBody =>
          have bodyWellFormed :=
            emitTermList_wellFormed rule.body afterHead headWellFormed
          rw [emittedBody] at bodyWellFormed
          simp only [emitRule, emittedHead, emittedBody]
          rcases bodyWellFormed with ⟨nodes, children, rules, bodies⟩
          change afterBody.nodeCount = afterBody.nodesRev.length at nodes
          change afterBody.childCount = afterBody.childrenRev.length at children
          change afterBody.ruleCount = afterBody.rulesRev.length at rules
          change afterBody.bodyCount = afterBody.bodiesRev.length at bodies
          refine ⟨nodes, children, ?_, ?_⟩
          · simpa using rules
          · simp only [List.length_append, List.length_reverse]
            omega

theorem emitRules_wellFormed (source : TypedProgram) (builder : Builder)
    (wellFormed : builder.WellFormed) :
    (emitRules source builder).WellFormed := by
  induction source generalizing builder with
  | nil => simpa [emitRules] using wellFormed
  | cons rule rules inductionHypothesis =>
      simpa [emitRules] using inductionHypothesis (emitRule builder rule)
        (emitRule_wellFormed builder rule wellFormed)

mutual

/-- Term emission extends both forward physical tables monotonically.  This
is the structural append-only property used by the independent decoder. -/
theorem emitTerm_tablePrefixes (term : Term) (builder : Builder) :
    builder.nodes <+: (emitTerm term builder).2.nodes ∧
      builder.children <+: (emitTerm term builder).2.children := by
  cases term with
  | symbol name =>
      simp [emitTerm, appendNode, Builder.nodes, Builder.children]
  | «variable» slot =>
      simp [emitTerm, appendNode, Builder.nodes, Builder.children]
  | «string» value =>
      simp [emitTerm, appendNode, Builder.nodes, Builder.children]
  | integer value =>
      simp [emitTerm, appendNode, Builder.nodes, Builder.children]
  | application head arguments =>
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have argumentsPrefix := emitTerms_tablePrefixes arguments builder
          rw [emitted] at argumentsPrefix
          constructor
          · apply argumentsPrefix.1.trans
            simp [emitTerm, emitted, appendNode, Builder.nodes]
          · apply argumentsPrefix.2.trans
            simp [emitTerm, emitted, appendNode, Builder.children,
              List.reverse_append]
termination_by sizeOf term

theorem emitTerms_tablePrefixes (terms : Terms) (builder : Builder) :
    builder.nodes <+: (emitTerms terms builder).2.nodes ∧
      builder.children <+: (emitTerms terms builder).2.children := by
  cases terms with
  | nil => simp [emitTerms]
  | cons head tail =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headPrefix := emitTerm_tablePrefixes head builder
          rw [emittedHead] at headPrefix
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have tailPrefix := emitTerms_tablePrefixes tail afterHead
              rw [emittedTail] at tailPrefix
              simpa only [emitTerms, emittedHead, emittedTail] using
                And.intro (headPrefix.1.trans tailPrefix.1)
                  (headPrefix.2.trans tailPrefix.2)
termination_by sizeOf terms

end

theorem emitTermList_tablePrefixes (terms : List Term) (builder : Builder) :
    builder.nodes <+: (emitTermList terms builder).2.nodes ∧
      builder.children <+: (emitTermList terms builder).2.children := by
  induction terms generalizing builder with
  | nil => simp [emitTermList]
  | cons head tail inductionHypothesis =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headPrefix := emitTerm_tablePrefixes head builder
          rw [emittedHead] at headPrefix
          cases emittedTail : emitTermList tail afterHead with
          | mk roots afterTail =>
              have tailPrefix := inductionHypothesis afterHead
              rw [emittedTail] at tailPrefix
              simpa only [emitTermList, emittedHead, emittedTail] using
                And.intro (headPrefix.1.trans tailPrefix.1)
                  (headPrefix.2.trans tailPrefix.2)

/-- Selecting the last entry of a forward table prefix recovers the head of
its reverse accumulator. -/
theorem getElem?_eq_reverseHead_of_prefix
    {alpha : Type} (reversed whole : List alpha) (value : alpha)
    (tablePrefix : reversed.reverse <+: whole)
    (headEq : reversed.head? = some value) :
    whole[reversed.length - 1]? = some value := by
  cases reversed with
  | nil => simp at headEq
  | cons head tail =>
      simp only [List.head?_cons, Option.some.injEq] at headEq
      subst head
      rw [List.prefix_iff_getElem?] at tablePrefix
      have inRange : tail.length < (value :: tail).reverse.length := by simp
      have selected := tablePrefix tail.length inRange
      simp only [List.length_cons, Nat.add_sub_cancel] at selected ⊢
      rw [selected]
      congr 1
      rw [List.getElem_reverse]
      simp

/-- A contiguous emitted suffix can be recovered through the admission
reader from any larger table having that suffix as part of its prefix. -/
theorem slice?_of_append_prefix (before segment whole : List alpha)
    (tablePrefix : before ++ segment <+: whole) :
    slice? whole before.length segment.length = some segment := by
  rcases tablePrefix with ⟨suffix, equality⟩
  rw [← equality]
  simp [slice?]

/-- The root returned by term emission is exactly the final emitted node.
The bound prevents `UInt32.ofNat` truncation. -/
theorem emitTerm_root_succ_eq_nodeCount (term : Term) (builder : Builder)
    (fits : (emitTerm term builder).2.nodeCount < UInt32.size) :
    (emitTerm term builder).1.toNat + 1 =
      (emitTerm term builder).2.nodeCount := by
  cases term with
  | symbol name =>
      have bound : builder.nodeCount < UInt32.size := by
        have : builder.nodeCount + 1 < UInt32.size := by
          simpa [emitTerm, appendNode] using fits
        omega
      simp [emitTerm, appendNode, Nat.mod_eq_of_lt bound]
  | «variable» slot =>
      have bound : builder.nodeCount < UInt32.size := by
        have : builder.nodeCount + 1 < UInt32.size := by
          simpa [emitTerm, appendNode] using fits
        omega
      simp [emitTerm, appendNode, Nat.mod_eq_of_lt bound]
  | «string» value =>
      have bound : builder.nodeCount < UInt32.size := by
        have : builder.nodeCount + 1 < UInt32.size := by
          simpa [emitTerm, appendNode] using fits
        omega
      simp [emitTerm, appendNode, Nat.mod_eq_of_lt bound]
  | integer value =>
      have bound : builder.nodeCount < UInt32.size := by
        have : builder.nodeCount + 1 < UInt32.size := by
          simpa [emitTerm, appendNode] using fits
        omega
      simp [emitTerm, appendNode, Nat.mod_eq_of_lt bound]
  | application head arguments =>
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have bound : afterArguments.nodeCount < UInt32.size := by
            have : afterArguments.nodeCount + 1 < UInt32.size := by
              simpa [emitTerm, emitted, appendNode] using fits
            omega
          simp [emitTerm, emitted, appendNode, Nat.mod_eq_of_lt bound]

mutual

/-- Number of physical node records emitted for one typed term. -/
def termNodeCount : Term -> Nat
  | .symbol _ | .variable _ | .string _ | .integer _ => 1
  | .application _ arguments => termsNodeCount arguments + 1

def termsNodeCount : Terms -> Nat
  | .nil => 0
  | .cons head tail => termNodeCount head + termsNodeCount tail

end


mutual

/-- Number of physical child-table slots emitted for one typed term. -/
def termChildSlotCount : Term -> Nat
  | .symbol _ | .variable _ | .string _ | .integer _ => 0
  | .application _ arguments =>
      termsChildSlotCount arguments + termsLength arguments

def termsChildSlotCount : Terms -> Nat
  | .nil => 0
  | .cons head tail => termChildSlotCount head + termsChildSlotCount tail

def termsLength : Terms -> Nat
  | .nil => 0
  | .cons _ tail => termsLength tail + 1

end


def termListNodeCount : List Term -> Nat
  | [] => 0
  | head :: tail => termNodeCount head + termListNodeCount tail

def termListChildSlotCount : List Term -> Nat
  | [] => 0
  | head :: tail => termChildSlotCount head + termListChildSlotCount tail

def typedRuleNodeCount (rule : TypedRule) : Nat :=
  termNodeCount rule.head + termListNodeCount rule.body

def typedRuleChildSlotCount (rule : TypedRule) : Nat :=
  termChildSlotCount rule.head + termListChildSlotCount rule.body

def programNodeCount : TypedProgram -> Nat
  | [] => 0
  | rule :: rules => typedRuleNodeCount rule + programNodeCount rules

def programChildSlotCount : TypedProgram -> Nat
  | [] => 0
  | rule :: rules =>
      typedRuleChildSlotCount rule + programChildSlotCount rules

def programBodySlotCount : TypedProgram -> Nat
  | [] => 0
  | rule :: rules => rule.body.length + programBodySlotCount rules

mutual

/-- Exact table-counter effect of emitting one term. -/
theorem emitTerm_counts (term : Term) (builder : Builder) :
    let emitted := emitTerm term builder
    emitted.2.nodeCount = builder.nodeCount + termNodeCount term ∧
      emitted.2.childCount = builder.childCount + termChildSlotCount term ∧
      emitted.2.ruleCount = builder.ruleCount ∧
      emitted.2.bodyCount = builder.bodyCount := by
  cases term with
  | symbol name =>
      simp [emitTerm, appendNode, termNodeCount, termChildSlotCount]
  | «variable» slot =>
      simp [emitTerm, appendNode, termNodeCount, termChildSlotCount]
  | «string» value =>
      simp [emitTerm, appendNode, termNodeCount, termChildSlotCount]
  | integer value =>
      simp [emitTerm, appendNode, termNodeCount, termChildSlotCount]
  | application head arguments =>
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have counts := emitTerms_counts arguments builder
          rw [emitted] at counts
          rcases counts with ⟨rootCount, nodes, children, rules, bodies⟩
          have rootCount' : roots.length = termsLength arguments := by
            simpa using rootCount
          have nodes' : afterArguments.nodeCount =
              builder.nodeCount + termsNodeCount arguments := by
            simpa using nodes
          have children' : afterArguments.childCount =
              builder.childCount + termsChildSlotCount arguments := by
            simpa using children
          have rules' : afterArguments.ruleCount = builder.ruleCount := by
            simpa using rules
          have bodies' : afterArguments.bodyCount = builder.bodyCount := by
            simpa using bodies
          simp only [emitTerm, emitted, appendNode, termNodeCount,
            termChildSlotCount]
          refine ⟨by omega, by omega, rules', bodies'⟩
termination_by sizeOf term

theorem emitTerms_counts (terms : Terms) (builder : Builder) :
    let emitted := emitTerms terms builder
    emitted.1.length = termsLength terms ∧
      emitted.2.nodeCount = builder.nodeCount + termsNodeCount terms ∧
      emitted.2.childCount = builder.childCount + termsChildSlotCount terms ∧
      emitted.2.ruleCount = builder.ruleCount ∧
      emitted.2.bodyCount = builder.bodyCount := by
  cases terms with
  | nil =>
      simp [emitTerms, termsLength, termsNodeCount, termsChildSlotCount]
  | cons head tail =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headCounts := emitTerm_counts head builder
          rw [emittedHead] at headCounts
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have tailCounts := emitTerms_counts tail afterHead
              rw [emittedTail] at tailCounts
              rcases headCounts with
                ⟨headNodes, headChildren, headRules, headBodies⟩
              rcases tailCounts with
                ⟨rootCount, tailNodes, tailChildren, tailRules, tailBodies⟩
              have headNodes' : afterHead.nodeCount =
                  builder.nodeCount + termNodeCount head := by
                simpa using headNodes
              have headChildren' : afterHead.childCount =
                  builder.childCount + termChildSlotCount head := by
                simpa using headChildren
              have headRules' : afterHead.ruleCount = builder.ruleCount := by
                simpa using headRules
              have headBodies' : afterHead.bodyCount = builder.bodyCount := by
                simpa using headBodies
              have rootCount' : roots.length = termsLength tail := by
                simpa using rootCount
              have tailNodes' : afterTail.nodeCount =
                  afterHead.nodeCount + termsNodeCount tail := by
                simpa using tailNodes
              have tailChildren' : afterTail.childCount =
                  afterHead.childCount + termsChildSlotCount tail := by
                simpa using tailChildren
              have tailRules' : afterTail.ruleCount = afterHead.ruleCount := by
                simpa using tailRules
              have tailBodies' : afterTail.bodyCount = afterHead.bodyCount := by
                simpa using tailBodies
              simp only [emitTerms, emittedHead, emittedTail,
                List.length_cons, termsLength, termsNodeCount,
                termsChildSlotCount]
              refine ⟨by omega, by omega, by omega, ?_, ?_⟩
              · omega
              · omega
termination_by sizeOf terms

end

/-- Every root returned by a term-list emission precedes the final node-table
cursor.  This is the exact backward-reference condition consumed by the
generic C and Lean validators. -/
theorem emitTerms_roots_lt_nodeCount (terms : Terms) (builder : Builder)
    (fits : (emitTerms terms builder).2.nodeCount < UInt32.size) :
    ∀ root ∈ (emitTerms terms builder).1,
      root.toNat < (emitTerms terms builder).2.nodeCount := by
  cases terms with
  | nil => simp [emitTerms]
  | cons head tail =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have combined : emitTerms (Terms.cons head tail) builder =
                  (root :: roots, afterTail) := by
                simp [emitTerms, emittedHead, emittedTail]
              have tailCounts := emitTerms_counts tail afterHead
              rw [emittedTail] at tailCounts
              have afterTailNodes : afterTail.nodeCount =
                  afterHead.nodeCount + termsNodeCount tail := by
                simpa using tailCounts.2.1
              have headLe : afterHead.nodeCount <= afterTail.nodeCount := by
                omega
              have totalFits : afterTail.nodeCount < UInt32.size := by
                rw [combined] at fits
                exact fits
              have headFits :
                  (emitTerm head builder).2.nodeCount < UInt32.size := by
                rw [emittedHead]
                exact lt_of_le_of_lt headLe totalFits
              have headIndex :=
                emitTerm_root_succ_eq_nodeCount head builder headFits
              rw [emittedHead] at headIndex
              change root.toNat + 1 = afterHead.nodeCount at headIndex
              have tailFits :
                  (emitTerms tail afterHead).2.nodeCount < UInt32.size := by
                rw [emittedTail]
                exact totalFits
              have tailRoots :=
                emitTerms_roots_lt_nodeCount tail afterHead tailFits
              rw [emittedTail] at tailRoots
              rw [combined]
              intro candidate member
              simp only [List.mem_cons] at member
              rcases member with equality | member
              · subst candidate
                exact lt_of_lt_of_le (by omega) headLe
              · exact tailRoots candidate member
termination_by sizeOf terms

theorem emitTermList_counts (terms : List Term) (builder : Builder) :
    let emitted := emitTermList terms builder
    emitted.1.length = terms.length ∧
      emitted.2.nodeCount = builder.nodeCount + termListNodeCount terms ∧
      emitted.2.childCount =
        builder.childCount + termListChildSlotCount terms ∧
      emitted.2.ruleCount = builder.ruleCount ∧
      emitted.2.bodyCount = builder.bodyCount := by
  induction terms generalizing builder with
  | nil =>
      simp [emitTermList, termListNodeCount, termListChildSlotCount]
  | cons head tail inductionHypothesis =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headCounts := emitTerm_counts head builder
          rw [emittedHead] at headCounts
          cases emittedTail : emitTermList tail afterHead with
          | mk roots afterTail =>
              have tailCounts := inductionHypothesis afterHead
              rw [emittedTail] at tailCounts
              rcases headCounts with
                ⟨headNodes, headChildren, headRules, headBodies⟩
              rcases tailCounts with
                ⟨rootCount, tailNodes, tailChildren, tailRules, tailBodies⟩
              have headNodes' : afterHead.nodeCount =
                  builder.nodeCount + termNodeCount head := by
                simpa using headNodes
              have headChildren' : afterHead.childCount =
                  builder.childCount + termChildSlotCount head := by
                simpa using headChildren
              have headRules' : afterHead.ruleCount = builder.ruleCount := by
                simpa using headRules
              have headBodies' : afterHead.bodyCount = builder.bodyCount := by
                simpa using headBodies
              have rootCount' : roots.length = tail.length := by
                simpa using rootCount
              have tailNodes' : afterTail.nodeCount =
                  afterHead.nodeCount + termListNodeCount tail := by
                simpa using tailNodes
              have tailChildren' : afterTail.childCount =
                  afterHead.childCount + termListChildSlotCount tail := by
                simpa using tailChildren
              have tailRules' : afterTail.ruleCount = afterHead.ruleCount := by
                simpa using tailRules
              have tailBodies' : afterTail.bodyCount = afterHead.bodyCount := by
                simpa using tailBodies
              simp only [emitTermList, emittedHead, emittedTail,
                List.length_cons, termListNodeCount, termListChildSlotCount]
              refine ⟨by omega, by omega, by omega, ?_, ?_⟩
              · omega
              · omega

theorem emitRule_counts (builder : Builder) (rule : TypedRule) :
    let emitted := emitRule builder rule
    emitted.nodeCount = builder.nodeCount + typedRuleNodeCount rule ∧
      emitted.childCount = builder.childCount +
        typedRuleChildSlotCount rule ∧
      emitted.ruleCount = builder.ruleCount + 1 ∧
      emitted.bodyCount = builder.bodyCount + rule.body.length := by
  cases emittedHead : emitTerm rule.head builder with
  | mk head afterHead =>
      have headCounts := emitTerm_counts rule.head builder
      rw [emittedHead] at headCounts
      cases emittedBody : emitTermList rule.body afterHead with
      | mk body afterBody =>
          have bodyCounts := emitTermList_counts rule.body afterHead
          rw [emittedBody] at bodyCounts
          rcases headCounts with
            ⟨headNodes, headChildren, headRules, headBodies⟩
          rcases bodyCounts with
            ⟨bodyLength, bodyNodes, bodyChildren, bodyRules, bodyBodies⟩
          have headNodes' : afterHead.nodeCount =
              builder.nodeCount + termNodeCount rule.head := by
            simpa using headNodes
          have headChildren' : afterHead.childCount =
              builder.childCount + termChildSlotCount rule.head := by
            simpa using headChildren
          have headRules' : afterHead.ruleCount = builder.ruleCount := by
            simpa using headRules
          have headBodies' : afterHead.bodyCount = builder.bodyCount := by
            simpa using headBodies
          have bodyLength' : body.length = rule.body.length := by
            simpa using bodyLength
          have bodyNodes' : afterBody.nodeCount =
              afterHead.nodeCount + termListNodeCount rule.body := by
            simpa using bodyNodes
          have bodyChildren' : afterBody.childCount =
              afterHead.childCount + termListChildSlotCount rule.body := by
            simpa using bodyChildren
          have bodyRules' : afterBody.ruleCount = afterHead.ruleCount := by
            simpa using bodyRules
          have bodyBodies' : afterBody.bodyCount = afterHead.bodyCount := by
            simpa using bodyBodies
          simp only [emitRule, emittedHead, emittedBody, typedRuleNodeCount,
            typedRuleChildSlotCount]
          refine ⟨by omega, by omega, by omega, by omega⟩

theorem emitRules_counts (source : TypedProgram) (builder : Builder) :
    let emitted := emitRules source builder
    emitted.nodeCount = builder.nodeCount + programNodeCount source ∧
      emitted.childCount =
        builder.childCount + programChildSlotCount source ∧
      emitted.ruleCount = builder.ruleCount + source.length ∧
      emitted.bodyCount = builder.bodyCount + programBodySlotCount source := by
  induction source generalizing builder with
  | nil =>
      simp [emitRules, programNodeCount, programChildSlotCount,
        programBodySlotCount]
  | cons rule rules inductionHypothesis =>
      have headCounts := emitRule_counts builder rule
      have tailCounts := inductionHypothesis (emitRule builder rule)
      rcases headCounts with
        ⟨headNodes, headChildren, headRules, headBodies⟩
      rcases tailCounts with
        ⟨tailNodes, tailChildren, tailRules, tailBodies⟩
      simp only [emitRules, programNodeCount, programChildSlotCount,
        programBodySlotCount, List.length_cons]
      refine ⟨by omega, by omega, by omega, by omega⟩

/-- Complete physical lowering before fail-closed admission. -/
def compile (source : TypedProgram) : Program :=
  let builder := emitRules source {}
  { nodes := builder.nodesRev.reverse
    children := builder.childrenRev.reverse
    rules := builder.rulesRev.reverse
    bodies := builder.bodiesRev.reverse }

/-- The compiler's four physical tables have exactly the sizes determined by
the source syntax.  This rules out hidden table growth independently of any
wall-clock benchmark. -/
theorem compile_table_lengths (source : TypedProgram) :
    (compile source).nodes.length = programNodeCount source ∧
      (compile source).children.length = programChildSlotCount source ∧
      (compile source).rules.length = source.length ∧
      (compile source).bodies.length = programBodySlotCount source := by
  generalize builderEquality : emitRules source {} = builder
  have wellFormed := emitRules_wellFormed source ({} : Builder)
    Builder.empty_wellFormed
  rw [builderEquality] at wellFormed
  have counts := emitRules_counts source ({} : Builder)
  rw [builderEquality] at counts
  rcases wellFormed with
    ⟨nodesLength, childrenLength, rulesLength, bodiesLength⟩
  rcases counts with
    ⟨nodesCount, childrenCount, rulesCount, bodiesCount⟩
  change builder.nodeCount = builder.nodesRev.length at nodesLength
  change builder.childCount = builder.childrenRev.length at childrenLength
  change builder.ruleCount = builder.rulesRev.length at rulesLength
  change builder.bodyCount = builder.bodiesRev.length at bodiesLength
  change builder.nodeCount = 0 + programNodeCount source at nodesCount
  change builder.childCount =
    0 + programChildSlotCount source at childrenCount
  change builder.ruleCount = 0 + source.length at rulesCount
  change builder.bodyCount = 0 + programBodySlotCount source at bodiesCount
  simp only [compile, builderEquality, List.length_reverse]
  omega

/-- Intended semantic result of compiling one typed source rule. -/
def TypedRule.toAdmitted (rule : TypedRule) : AdmittedRule :=
  { name := rule.name
    head := rule.head
    body := rule.body
    variableCount := rule.variableCount.toNat }

def TypedProgram.toAdmitted (source : TypedProgram) : AdmittedProgram :=
  { rules := source.map TypedRule.toAdmitted }

/-- Independent translation validation.  The emitter does not authorize its
own output: the physical plan is reconstructed by `admit?` and compared with
the typed source meaning. -/
def validate? (source : TypedProgram) (program : Program) :
    Option AdmittedProgram :=
  if program.encodable? then
    match admit? program with
    | some admitted =>
        if admitted = source.toAdmitted then some admitted else none
    | none => none
  else
    none

/-- Decode and structurally admit the compiler output.  Physical bounds are
checked before admission, and independent translation validation requires the
reconstructed result to equal the typed input meaning. -/
def lower? (source : TypedProgram) : Option AdmittedProgram :=
  validate? source (compile source)

def compileBytes? (source : TypedProgram) : Option (List UInt8) :=
  let program := compile source
  match validate? source program with
  | some _ => some (encodeProgram program)
  | none => none

theorem validate?_success
    {source : TypedProgram} {program : Program} {admitted : AdmittedProgram}
    (success : validate? source program = some admitted) :
    program.Encodable ∧
      admit? program = some admitted ∧
      admitted = source.toAdmitted := by
  unfold validate? at success
  by_cases physical : program.encodable? = true
  · rw [if_pos physical] at success
    cases admission : admit? program with
    | none =>
        rw [admission] at success
        contradiction
    | some reconstructed =>
        rw [admission] at success
        change
          (if reconstructed = source.toAdmitted then some reconstructed
            else none) = some admitted at success
        by_cases exactMeaning : reconstructed = source.toAdmitted
        · rw [if_pos exactMeaning] at success
          have same : reconstructed = admitted := Option.some.inj success
          subst admitted
          exact
            ⟨(Program.encodable?_eq_true_iff program).mp physical,
              rfl, exactMeaning⟩
        · rw [if_neg exactMeaning] at success
          contradiction
  · rw [if_neg physical] at success
    contradiction

/-- Successful typed lowering has exactly the source program's meaning. -/
theorem lower?_sound
    {source : TypedProgram} {admitted : AdmittedProgram}
    (success : lower? source = some admitted) :
    admitted = source.toAdmitted :=
  (validate?_success success).2.2

/-- The typed lowering and exact wire entry point form one commuting stage:
serializing, decoding, and admitting yields precisely direct admission. -/
theorem compileBytes?_bind_admitBytes?_eq_lower?
    (source : TypedProgram) :
    (compileBytes? source).bind admitBytes? = lower? source := by
  unfold compileBytes? lower?
  cases validation : validate? source (compile source) with
  | none => simp [validation]
  | some admitted =>
      have facts := validate?_success validation
      simp [validation,
        admitBytes?_encodeProgram (compile source) facts.1,
        facts.2.1]

/-- Every emitted packet accepted by the compiler decodes to the exact typed
source meaning.  Compact offsets and byte framing cannot become semantic
authority on their own. -/
theorem compileBytes?_sound
    {source : TypedProgram} {bytes : List UInt8}
    (success : compileBytes? source = some bytes) :
    admitBytes? bytes = some source.toAdmitted := by
  unfold compileBytes? at success
  dsimp only at success
  cases validation : validate? source (compile source) with
  | none =>
      rw [validation] at success
      contradiction
  | some admitted =>
      rw [validation] at success
      have byteEquality : encodeProgram (compile source) = bytes :=
        Option.some.inj success
      subst bytes
      have facts := validate?_success validation
      rw [admitBytes?_encodeProgram (compile source) facts.1,
        facts.2.1, facts.2.2]

/-! ## Local source-property recognizers -/

mutual

def termTextsValid : Term -> Bool
  | .symbol name => bytesNonempty name && textEncodable? name
  | .variable _ => true
  | .string value => textEncodable? value
  | .integer _ => true
  | .application head arguments =>
      bytesNonempty head && textEncodable? head && termsTextsValid arguments

def termsTextsValid : Terms -> Bool
  | .nil => true
  | .cons head tail => termTextsValid head && termsTextsValid tail

end

mutual

/-- Source text representability is preserved separately from local node
shape.  The wire encoder needs both facts, while the runtime shape predicate
deliberately does not duplicate the `UInt32` length boundary. -/
theorem emitTerm_nodesTextEncodable (term : Term) (builder : Builder)
    (termValid : termTextsValid term = true)
    (builderValid : builder.nodesRev.all
      (fun node => textEncodable? node.text) = true) :
    (emitTerm term builder).2.nodesRev.all
      (fun node => textEncodable? node.text) = true := by
  cases term with
  | symbol name =>
      simp only [termTextsValid, Bool.and_eq_true] at termValid
      simp only [emitTerm, appendNode, List.all_cons, scalarNode]
      exact Bool.and_eq_true_iff.mpr ⟨termValid.2, builderValid⟩
  | «variable» slot =>
      simp only [emitTerm, appendNode, List.all_cons, scalarNode]
      exact Bool.and_eq_true_iff.mpr ⟨by decide, builderValid⟩
  | «string» value =>
      simp only [termTextsValid] at termValid
      simp only [emitTerm, appendNode, List.all_cons, scalarNode]
      exact Bool.and_eq_true_iff.mpr ⟨termValid, builderValid⟩
  | integer value =>
      simp only [emitTerm, appendNode, List.all_cons, scalarNode]
      exact Bool.and_eq_true_iff.mpr ⟨by decide, builderValid⟩
  | application head arguments =>
      simp only [termTextsValid, Bool.and_eq_true] at termValid
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have argumentsValid := emitTerms_nodesTextEncodable arguments
            builder termValid.2 builderValid
          rw [emitted] at argumentsValid
          simp only [emitTerm, emitted, appendNode, List.all_cons]
          exact Bool.and_eq_true_iff.mpr
            ⟨termValid.1.2, argumentsValid⟩
termination_by sizeOf term

theorem emitTerms_nodesTextEncodable (terms : Terms) (builder : Builder)
    (termsValid : termsTextsValid terms = true)
    (builderValid : builder.nodesRev.all
      (fun node => textEncodable? node.text) = true) :
    (emitTerms terms builder).2.nodesRev.all
      (fun node => textEncodable? node.text) = true := by
  cases terms with
  | nil => simpa [emitTerms] using builderValid
  | cons head tail =>
      rw [termsTextsValid, Bool.and_eq_true] at termsValid
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headValid := emitTerm_nodesTextEncodable head builder
            termsValid.1 builderValid
          rw [emittedHead] at headValid
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have tailValid := emitTerms_nodesTextEncodable tail afterHead
                termsValid.2 headValid
              rw [emittedTail] at tailValid
              simpa [emitTerms, emittedHead, emittedTail] using tailValid
termination_by sizeOf terms

end


theorem emitTermList_nodesTextEncodable (terms : List Term)
    (builder : Builder)
    (termsValid : terms.all termTextsValid = true)
    (builderValid : builder.nodesRev.all
      (fun node => textEncodable? node.text) = true) :
    (emitTermList terms builder).2.nodesRev.all
      (fun node => textEncodable? node.text) = true := by
  induction terms generalizing builder with
  | nil => simpa [emitTermList] using builderValid
  | cons head tail inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at termsValid
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headValid := emitTerm_nodesTextEncodable head builder
            termsValid.1 builderValid
          rw [emittedHead] at headValid
          cases emittedTail : emitTermList tail afterHead with
          | mk roots afterTail =>
              have tailValid := inductionHypothesis afterHead
                termsValid.2 headValid
              rw [emittedTail] at tailValid
              simpa [emitTermList, emittedHead, emittedTail] using tailValid

mutual

/-- Emitting a source term whose texts pass the local source recognizer
preserves local node validity in the reverse accumulator. -/
theorem emitTerm_nodesLocallyValid (term : Term) (builder : Builder)
    (termValid : termTextsValid term = true)
    (builderValid : builder.nodesRev.all Node.locallyValid = true) :
    (emitTerm term builder).2.nodesRev.all Node.locallyValid = true := by
  cases term with
  | symbol name =>
      simp [termTextsValid, bytesNonempty, textEncodable?, bytesNulFree]
        at termValid
      simp [emitTerm, appendNode, scalarNode, Node.locallyValid,
        scalarNodeFieldsAreZero, bytesNonempty, bytesNulFree, termValid,
        builderValid]
  | «variable» slot =>
      simp [emitTerm, appendNode, scalarNode, Node.locallyValid,
        bytesNulFree, builderValid]
  | «string» value =>
      simp [termTextsValid, textEncodable?, bytesNulFree] at termValid
      simp [emitTerm, appendNode, scalarNode, Node.locallyValid,
        bytesNulFree, termValid, builderValid]
  | integer value =>
      simp [emitTerm, appendNode, scalarNode, Node.locallyValid,
        bytesNulFree, builderValid]
  | application head arguments =>
      simp [termTextsValid, bytesNonempty, textEncodable?, bytesNulFree]
        at termValid
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have argumentsValid := emitTerms_nodesLocallyValid arguments builder
            termValid.2 builderValid
          rw [emitted] at argumentsValid
          simp [emitTerm, emitted, appendNode, Node.locallyValid,
            bytesNonempty, bytesNulFree, termValid, argumentsValid]
termination_by sizeOf term

theorem emitTerms_nodesLocallyValid (terms : Terms) (builder : Builder)
    (termsValid : termsTextsValid terms = true)
    (builderValid : builder.nodesRev.all Node.locallyValid = true) :
    (emitTerms terms builder).2.nodesRev.all Node.locallyValid = true := by
  cases terms with
  | nil => simpa [emitTerms] using builderValid
  | cons head tail =>
      simp [termsTextsValid] at termsValid
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headValid := emitTerm_nodesLocallyValid head builder
            termsValid.1 builderValid
          rw [emittedHead] at headValid
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have tailValid := emitTerms_nodesLocallyValid tail afterHead
                termsValid.2 headValid
              rw [emittedTail] at tailValid
              simpa [emitTerms, emittedHead, emittedTail] using tailValid
termination_by sizeOf terms

end

theorem emitTermList_nodesLocallyValid (terms : List Term)
    (builder : Builder)
    (termsValid : terms.all termTextsValid = true)
    (builderValid : builder.nodesRev.all Node.locallyValid = true) :
    (emitTermList terms builder).2.nodesRev.all Node.locallyValid = true := by
  induction terms generalizing builder with
  | nil => simpa [emitTermList] using builderValid
  | cons head tail inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at termsValid
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headValid := emitTerm_nodesLocallyValid head builder
            termsValid.1 builderValid
          rw [emittedHead] at headValid
          cases emittedTail : emitTermList tail afterHead with
          | mk roots afterTail =>
              have tailValid := inductionHypothesis afterHead
                termsValid.2 headValid
              rw [emittedTail] at tailValid
              simpa [emitTermList, emittedHead, emittedTail] using tailValid

mutual

/-- Term emission only appends node and child entries.  In particular it
cannot silently mutate the rule inventory while constructing a rule. -/
theorem emitTerm_rulesRev_eq (term : Term) (builder : Builder) :
    (emitTerm term builder).2.rulesRev = builder.rulesRev := by
  cases term with
  | symbol name => rfl
  | «variable» slot => rfl
  | «string» value => rfl
  | integer value => rfl
  | application head arguments =>
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have unchanged := emitTerms_rulesRev_eq arguments builder
          rw [emitted] at unchanged
          simpa [emitTerm, emitted, appendNode] using unchanged
termination_by sizeOf term

theorem emitTerms_rulesRev_eq (terms : Terms) (builder : Builder) :
    (emitTerms terms builder).2.rulesRev = builder.rulesRev := by
  cases terms with
  | nil => rfl
  | cons head tail =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headUnchanged := emitTerm_rulesRev_eq head builder
          rw [emittedHead] at headUnchanged
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have tailUnchanged := emitTerms_rulesRev_eq tail afterHead
              rw [emittedTail] at tailUnchanged
              simpa only [emitTerms, emittedHead, emittedTail] using
                tailUnchanged.trans headUnchanged
termination_by sizeOf terms

end

theorem emitTermList_rulesRev_eq (terms : List Term) (builder : Builder) :
    (emitTermList terms builder).2.rulesRev = builder.rulesRev := by
  induction terms generalizing builder with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headUnchanged := emitTerm_rulesRev_eq head builder
          rw [emittedHead] at headUnchanged
          cases emittedTail : emitTermList tail afterHead with
          | mk roots afterTail =>
              have tailUnchanged := inductionHypothesis afterHead
              rw [emittedTail] at tailUnchanged
              simpa only [emitTermList, emittedHead, emittedTail] using
                tailUnchanged.trans headUnchanged

mutual

/-- Term emission cannot mutate the body-root inventory while constructing a
rule.  Together with `emitTerm_rulesRev_eq`, this isolates the two tables that
are owned by `emitRule` itself. -/
theorem emitTerm_bodiesRev_eq (term : Term) (builder : Builder) :
    (emitTerm term builder).2.bodiesRev = builder.bodiesRev := by
  cases term with
  | symbol name => rfl
  | «variable» slot => rfl
  | «string» value => rfl
  | integer value => rfl
  | application head arguments =>
      cases emitted : emitTerms arguments builder with
      | mk roots afterArguments =>
          have unchanged := emitTerms_bodiesRev_eq arguments builder
          rw [emitted] at unchanged
          simpa [emitTerm, emitted, appendNode] using unchanged
termination_by sizeOf term

theorem emitTerms_bodiesRev_eq (terms : Terms) (builder : Builder) :
    (emitTerms terms builder).2.bodiesRev = builder.bodiesRev := by
  cases terms with
  | nil => rfl
  | cons head tail =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headUnchanged := emitTerm_bodiesRev_eq head builder
          rw [emittedHead] at headUnchanged
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have tailUnchanged := emitTerms_bodiesRev_eq tail afterHead
              rw [emittedTail] at tailUnchanged
              simpa only [emitTerms, emittedHead, emittedTail] using
                tailUnchanged.trans headUnchanged
termination_by sizeOf terms

end

theorem emitTermList_bodiesRev_eq (terms : List Term) (builder : Builder) :
    (emitTermList terms builder).2.bodiesRev = builder.bodiesRev := by
  induction terms generalizing builder with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          have headUnchanged := emitTerm_bodiesRev_eq head builder
          rw [emittedHead] at headUnchanged
          cases emittedTail : emitTermList tail afterHead with
          | mk roots afterTail =>
              have tailUnchanged := inductionHypothesis afterHead
              rw [emittedTail] at tailUnchanged
              simpa only [emitTermList, emittedHead, emittedTail] using
                tailUnchanged.trans headUnchanged

/-- Rule emission monotonically extends all four forward physical tables. -/
theorem emitRule_tablePrefixes (builder : Builder) (rule : TypedRule) :
    builder.nodes <+: (emitRule builder rule).nodes ∧
      builder.children <+: (emitRule builder rule).children ∧
      builder.rules <+: (emitRule builder rule).rules ∧
      builder.bodies <+: (emitRule builder rule).bodies := by
  cases emittedHead : emitTerm rule.head builder with
  | mk head afterHead =>
      have headPrefix := emitTerm_tablePrefixes rule.head builder
      rw [emittedHead] at headPrefix
      have headRules := emitTerm_rulesRev_eq rule.head builder
      rw [emittedHead] at headRules
      have headBodies := emitTerm_bodiesRev_eq rule.head builder
      rw [emittedHead] at headBodies
      cases emittedBody : emitTermList rule.body afterHead with
      | mk body afterBody =>
          have bodyPrefix := emitTermList_tablePrefixes rule.body afterHead
          rw [emittedBody] at bodyPrefix
          have bodyRules := emitTermList_rulesRev_eq rule.body afterHead
          rw [emittedBody] at bodyRules
          have bodyBodies := emitTermList_bodiesRev_eq rule.body afterHead
          rw [emittedBody] at bodyBodies
          have nodesEq : (emitRule builder rule).nodes = afterBody.nodes := by
            simp [emitRule, emittedHead, emittedBody, Builder.nodes]
          have childrenEq :
              (emitRule builder rule).children = afterBody.children := by
            simp [emitRule, emittedHead, emittedBody, Builder.children]
          have rulesEq : afterBody.rules = builder.rules := by
            unfold Builder.rules
            rw [bodyRules, headRules]
          have bodiesEq : afterBody.bodies = builder.bodies := by
            unfold Builder.bodies
            rw [bodyBodies, headBodies]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [nodesEq]
            exact headPrefix.1.trans bodyPrefix.1
          · rw [childrenEq]
            exact headPrefix.2.trans bodyPrefix.2
          · rw [show (emitRule builder rule).rules = afterBody.rules ++
                [{ head := head
                   bodyOffset := UInt32.ofNat afterHead.bodyCount
                   bodyCount := UInt32.ofNat body.length
                   variableCount := rule.variableCount
                   name := rule.name }] by
              simp [emitRule, emittedHead, emittedBody, Builder.rules]]
            rw [rulesEq]
            simp
          · rw [show (emitRule builder rule).bodies =
                afterBody.bodies ++ body by
              simp [emitRule, emittedHead, emittedBody, Builder.bodies,
                List.reverse_append]]
            rw [bodiesEq]
            simp

/-- A rule-program fold is append-only in every physical table. -/
theorem emitRules_tablePrefixes (source : TypedProgram) (builder : Builder) :
    builder.nodes <+: (emitRules source builder).nodes ∧
      builder.children <+: (emitRules source builder).children ∧
      builder.rules <+: (emitRules source builder).rules ∧
      builder.bodies <+: (emitRules source builder).bodies := by
  induction source generalizing builder with
  | nil => simp [emitRules]
  | cons rule rules inductionHypothesis =>
      have first := emitRule_tablePrefixes builder rule
      have rest := inductionHypothesis (emitRule builder rule)
      simpa only [emitRules] using
        And.intro (first.1.trans rest.1)
          (And.intro (first.2.1.trans rest.2.1)
            (And.intro (first.2.2.1.trans rest.2.2.1)
              (first.2.2.2.trans rest.2.2.2)))

theorem emitRule_nodesLocallyValid (builder : Builder) (rule : TypedRule)
    (headValid : termTextsValid rule.head = true)
    (bodyValid : rule.body.all termTextsValid = true)
    (builderValid : builder.nodesRev.all Node.locallyValid = true) :
    (emitRule builder rule).nodesRev.all Node.locallyValid = true := by
  cases emittedHead : emitTerm rule.head builder with
  | mk head afterHead =>
      have emittedHeadValid := emitTerm_nodesLocallyValid rule.head builder
        headValid builderValid
      rw [emittedHead] at emittedHeadValid
      cases emittedBody : emitTermList rule.body afterHead with
      | mk body afterBody =>
          have emittedBodyValid := emitTermList_nodesLocallyValid rule.body
            afterHead bodyValid emittedHeadValid
          rw [emittedBody] at emittedBodyValid
          simpa [emitRule, emittedHead, emittedBody] using emittedBodyValid

theorem emitRule_nodesTextEncodable (builder : Builder) (rule : TypedRule)
    (headValid : termTextsValid rule.head = true)
    (bodyValid : rule.body.all termTextsValid = true)
    (builderValid : builder.nodesRev.all
      (fun node => textEncodable? node.text) = true) :
    (emitRule builder rule).nodesRev.all
      (fun node => textEncodable? node.text) = true := by
  cases emittedHead : emitTerm rule.head builder with
  | mk head afterHead =>
      have emittedHeadValid := emitTerm_nodesTextEncodable rule.head builder
        headValid builderValid
      rw [emittedHead] at emittedHeadValid
      cases emittedBody : emitTermList rule.body afterHead with
      | mk body afterBody =>
          have emittedBodyValid := emitTermList_nodesTextEncodable rule.body
            afterHead bodyValid emittedHeadValid
          rw [emittedBody] at emittedBodyValid
          simpa [emitRule, emittedHead, emittedBody] using emittedBodyValid

theorem emitRule_rulesLocallyValid (builder : Builder) (rule : TypedRule)
    (nameValid : bytesNonempty rule.name = true)
    (nameEncodable : textEncodable? rule.name = true)
    (builderValid : builder.rulesRev.all Rule.locallyValid = true) :
    (emitRule builder rule).rulesRev.all Rule.locallyValid = true := by
  cases emittedHead : emitTerm rule.head builder with
  | mk head afterHead =>
      have headUnchanged := emitTerm_rulesRev_eq rule.head builder
      rw [emittedHead] at headUnchanged
      cases emittedBody : emitTermList rule.body afterHead with
      | mk body afterBody =>
          have bodyUnchanged := emitTermList_rulesRev_eq rule.body afterHead
          rw [emittedBody] at bodyUnchanged
          simp only [emitRule, emittedHead, emittedBody, List.all_cons]
          rw [bodyUnchanged, headUnchanged, Bool.and_eq_true]
          refine ⟨?_, builderValid⟩
          simp [Rule.locallyValid, nameValid, textEncodable?]
            at nameEncodable ⊢
          exact nameEncodable.2

theorem emitRule_rulesTextEncodable (builder : Builder) (rule : TypedRule)
    (nameEncodable : textEncodable? rule.name = true)
    (builderValid : builder.rulesRev.all
      (fun emitted => textEncodable? emitted.name) = true) :
    (emitRule builder rule).rulesRev.all
      (fun emitted => textEncodable? emitted.name) = true := by
  cases emittedHead : emitTerm rule.head builder with
  | mk head afterHead =>
      have headUnchanged := emitTerm_rulesRev_eq rule.head builder
      rw [emittedHead] at headUnchanged
      cases emittedBody : emitTermList rule.body afterHead with
      | mk body afterBody =>
          have bodyUnchanged := emitTermList_rulesRev_eq rule.body afterHead
          rw [emittedBody] at bodyUnchanged
          simp only [emitRule, emittedHead, emittedBody, List.all_cons]
          rw [bodyUnchanged, headUnchanged]
          exact Bool.and_eq_true_iff.mpr ⟨nameEncodable, builderValid⟩

mutual

/-- Structural depth computed from the typed source before physical lowering. -/
def termDepth : Term -> Nat
  | .symbol _ | .variable _ | .string _ | .integer _ => 0
  | .application _ arguments => termsMaximumDepth arguments + 1

def termsMaximumDepth : Terms -> Nat
  | .nil => 0
  | .cons head tail => max (termDepth head) (termsMaximumDepth tail)

end

def termListMaximumDepth : List Term -> Nat
  | [] => 0
  | head :: tail => max (termDepth head) (termListMaximumDepth tail)

mutual

def termUsedVariables : Term -> List Nat
  | .symbol _ => []
  | .variable slot => [slot.toNat]
  | .string _ => []
  | .integer _ => []
  | .application _ arguments => termsUsedVariables arguments

def termsUsedVariables : Terms -> List Nat
  | .nil => []
  | .cons head tail => termUsedVariables head ++ termsUsedVariables tail

end

mutual

theorem termDepth_le_termNodeCount (term : Term) :
    termDepth term <= termNodeCount term := by
  cases term with
  | symbol name => simp [termDepth, termNodeCount]
  | «variable» slot => simp [termDepth, termNodeCount]
  | «string» value => simp [termDepth, termNodeCount]
  | integer value => simp [termDepth, termNodeCount]
  | application head arguments =>
      have bound := termsMaximumDepth_le_termsNodeCount arguments
      simp only [termDepth, termNodeCount]
      omega
termination_by sizeOf term

theorem termsMaximumDepth_le_termsNodeCount (terms : Terms) :
    termsMaximumDepth terms <= termsNodeCount terms := by
  cases terms with
  | nil => simp [termsMaximumDepth, termsNodeCount]
  | cons head tail =>
      have headBound := termDepth_le_termNodeCount head
      have tailBound := termsMaximumDepth_le_termsNodeCount tail
      simp only [termsMaximumDepth, termsNodeCount]
      omega
termination_by sizeOf terms

end

theorem slotRange_append (base left right : Nat) :
    slotRange base left ++ slotRange (base + left) right =
      slotRange base (left + right) := by
  simp [slotRange, List.range_add, Function.comp_def, Nat.add_assoc]

/-- Semantic and ownership facts reconstructed for one emitted term. -/
def DecodedTermMatchesSourceAt (decoded : DecodedTerm) (source : Term)
    (nodeBase childBase : Nat) : Prop :=
  decoded.term = source ∧
    decoded.claimedNodes.toList.Perm
      (slotRange nodeBase (termNodeCount source)) ∧
    decoded.claimedChildSlots.toList.Perm
      (slotRange childBase (termChildSlotCount source)) ∧
    decoded.usedVariables.toList = termUsedVariables source ∧
    decoded.depth = termDepth source

/-- Aggregate semantic and ownership facts reconstructed for an emitted list
of terms. -/
def DecodedTermsMatchSourceAt (decoded : List DecodedTerm) (source : Terms)
    (nodeBase childBase : Nat) : Prop :=
  decodedTerms decoded = source ∧
    (concatDecodedTerms decoded).1.toList.Perm
      (slotRange nodeBase (termsNodeCount source)) ∧
    (concatDecodedTerms decoded).2.1.toList.Perm
      (slotRange childBase (termsChildSlotCount source)) ∧
    (concatDecodedTerms decoded).2.2.toList = termsUsedVariables source ∧
    maximumDepth decoded = termsMaximumDepth source

def TypedRule.locallySupported (rule : TypedRule) : Bool :=
  bytesNonempty rule.name && textEncodable? rule.name &&
    rule.head.isApplication && termTextsValid rule.head &&
    rule.body.all (fun term => term.isApplication && termTextsValid term) &&
    decide (termDepth rule.head <= 4096) &&
    decide (termListMaximumDepth rule.body <= 4096) &&
    decide (rule.variableCount.toNat <= typedRuleNodeCount rule) &&
    denseVariables rule.variableCount.toNat
      (termUsedVariables rule.head ++ rule.body.flatMap termUsedVariables)

def TypedProgram.locallySupported (source : TypedProgram) : Bool :=
  !source.isEmpty && source.all TypedRule.locallySupported &&
    decide (source.map TypedRule.name).Nodup &&
    decide (programNodeCount source < UInt32.size) &&
    decide (programChildSlotCount source < UInt32.size) &&
    decide (source.length < UInt32.size) &&
    decide (programBodySlotCount source < UInt32.size)

/-- The local rule recognizer exposes exactly the source facts needed by the
physical emitter.  Later admission facts remain separate. -/
theorem TypedRule.locallySupported_emissionFacts (rule : TypedRule)
    (supported : rule.locallySupported = true) :
    bytesNonempty rule.name = true ∧
      textEncodable? rule.name = true ∧
      termTextsValid rule.head = true ∧
      rule.body.all termTextsValid = true := by
  simp [TypedRule.locallySupported] at supported ⊢
  aesop

theorem emitRules_nodesLocallyValid (source : TypedProgram)
    (builder : Builder)
    (sourceValid : source.all TypedRule.locallySupported = true)
    (builderValid : builder.nodesRev.all Node.locallyValid = true) :
    (emitRules source builder).nodesRev.all Node.locallyValid = true := by
  induction source generalizing builder with
  | nil => simpa [emitRules] using builderValid
  | cons rule rules inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at sourceValid
      have facts := rule.locallySupported_emissionFacts sourceValid.1
      have ruleValid := emitRule_nodesLocallyValid builder rule
        facts.2.2.1 facts.2.2.2 builderValid
      simpa [emitRules] using inductionHypothesis (emitRule builder rule)
        sourceValid.2 ruleValid

theorem emitRules_nodesTextEncodable (source : TypedProgram)
    (builder : Builder)
    (sourceValid : source.all TypedRule.locallySupported = true)
    (builderValid : builder.nodesRev.all
      (fun node => textEncodable? node.text) = true) :
    (emitRules source builder).nodesRev.all
      (fun node => textEncodable? node.text) = true := by
  induction source generalizing builder with
  | nil => simpa [emitRules] using builderValid
  | cons rule rules inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at sourceValid
      have facts := rule.locallySupported_emissionFacts sourceValid.1
      have ruleValid := emitRule_nodesTextEncodable builder rule
        facts.2.2.1 facts.2.2.2 builderValid
      simpa [emitRules] using inductionHypothesis (emitRule builder rule)
        sourceValid.2 ruleValid

theorem emitRules_rulesLocallyValid (source : TypedProgram)
    (builder : Builder)
    (sourceValid : source.all TypedRule.locallySupported = true)
    (builderValid : builder.rulesRev.all Rule.locallyValid = true) :
    (emitRules source builder).rulesRev.all Rule.locallyValid = true := by
  induction source generalizing builder with
  | nil => simpa [emitRules] using builderValid
  | cons rule rules inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at sourceValid
      have facts := rule.locallySupported_emissionFacts sourceValid.1
      have ruleValid := emitRule_rulesLocallyValid builder rule
        facts.1 facts.2.1 builderValid
      simpa [emitRules] using inductionHypothesis (emitRule builder rule)
        sourceValid.2 ruleValid

theorem emitRules_rulesTextEncodable (source : TypedProgram)
    (builder : Builder)
    (sourceValid : source.all TypedRule.locallySupported = true)
    (builderValid : builder.rulesRev.all
      (fun rule => textEncodable? rule.name) = true) :
    (emitRules source builder).rulesRev.all
      (fun rule => textEncodable? rule.name) = true := by
  induction source generalizing builder with
  | nil => simpa [emitRules] using builderValid
  | cons rule rules inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at sourceValid
      have facts := rule.locallySupported_emissionFacts sourceValid.1
      have ruleValid := emitRule_rulesTextEncodable builder rule
        facts.2.1 builderValid
      simpa [emitRules] using inductionHypothesis (emitRule builder rule)
        sourceValid.2 ruleValid

theorem TypedProgram.locallySupported_emissionFacts (source : TypedProgram)
    (supported : source.locallySupported = true) :
    source.isEmpty = false ∧
      source.all TypedRule.locallySupported = true ∧
      (source.map TypedRule.name).Nodup ∧
      programNodeCount source < UInt32.size ∧
      programChildSlotCount source < UInt32.size ∧
      source.length < UInt32.size ∧
      programBodySlotCount source < UInt32.size := by
  simp [TypedProgram.locallySupported] at supported ⊢
  aesop

theorem termNodeCount_positive (term : Term) :
    0 < termNodeCount term := by
  cases term <;> simp [termNodeCount]

theorem programNodeCount_positive {source : TypedProgram}
    (nonempty : source.isEmpty = false) :
    0 < programNodeCount source := by
  cases source with
  | nil => simp at nonempty
  | cons rule rules =>
      simp only [programNodeCount, typedRuleNodeCount]
      have := termNodeCount_positive rule.head
      omega

/-- A locally supported source always lowers inside the exact physical carrier
bounds.  This proof follows the emitted tables rather than evaluating a
concrete packet. -/
theorem compile_encodable (source : TypedProgram)
    (supported : source.locallySupported = true) :
    (compile source).Encodable := by
  have facts := source.locallySupported_emissionFacts supported
  have nodesBoolean := emitRules_nodesTextEncodable source ({} : Builder)
    facts.2.1 (by decide)
  have rulesBoolean := emitRules_rulesTextEncodable source ({} : Builder)
    facts.2.1 (by decide)
  have compiledNodesBoolean :
      (compile source).nodes.all
        (fun node => textEncodable? node.text) = true := by
    simpa [compile] using nodesBoolean
  have compiledRulesBoolean :
      (compile source).rules.all
        (fun rule => textEncodable? rule.name) = true := by
    simpa [compile] using rulesBoolean
  have compiledNodesEncodable :
      ∀ node, node ∈ (compile source).nodes -> TextEncodable node.text := by
    rw [List.all_eq_true] at compiledNodesBoolean
    intro node member
    exact (textEncodable?_eq_true_iff node.text).mp
      (compiledNodesBoolean node member)
  have compiledRulesEncodable :
      ∀ rule, rule ∈ (compile source).rules -> TextEncodable rule.name := by
    rw [List.all_eq_true] at compiledRulesBoolean
    intro rule member
    exact (textEncodable?_eq_true_iff rule.name).mp
      (compiledRulesBoolean rule member)
  rcases compile_table_lengths source with
    ⟨nodesLength, childrenLength, rulesLength, bodiesLength⟩
  refine ⟨?_, ?_, ?_, ?_, compiledNodesEncodable,
    compiledRulesEncodable⟩
  · simpa [nodesLength] using facts.2.2.2.1
  · simpa [childrenLength] using facts.2.2.2.2.1
  · simpa [rulesLength] using facts.2.2.2.2.2.1
  · simpa [bodiesLength] using facts.2.2.2.2.2.2

/-- Local source support also entails the generic runtime's record-shape
boundary.  Forest ownership and semantic reconstruction remain the next,
stronger admission layer. -/
theorem compile_headerAndLocalShapesValid (source : TypedProgram)
    (supported : source.locallySupported = true) :
    (compile source).headerAndLocalShapesValid = true := by
  have facts := source.locallySupported_emissionFacts supported
  have nodesBoolean := emitRules_nodesLocallyValid source ({} : Builder)
    facts.2.1 (by decide)
  have rulesBoolean := emitRules_rulesLocallyValid source ({} : Builder)
    facts.2.1 (by decide)
  have compiledNodesBoolean :
      (compile source).nodes.all Node.locallyValid = true := by
    simpa [compile] using nodesBoolean
  have compiledRulesBoolean :
      (compile source).rules.all Rule.locallyValid = true := by
    simpa [compile] using rulesBoolean
  have nodeCountPositive := programNodeCount_positive facts.1
  rcases compile_table_lengths source with
    ⟨nodesLength, childrenLength, rulesLength, bodiesLength⟩
  simp only [Program.headerAndLocalShapesValid, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, compiledNodesBoolean⟩, compiledRulesBoolean⟩
  · rw [Bool.not_eq_true', List.isEmpty_eq_false_iff]
    intro nodesEmpty
    have lengthZero : (compile source).nodes.length = 0 := by
      simp [nodesEmpty]
    rw [nodesLength] at lengthZero
    omega
  · rw [Bool.not_eq_true', List.isEmpty_eq_false_iff]
    intro rulesEmpty
    have lengthZero : (compile source).rules.length = 0 := by
      simp [rulesEmpty]
    rw [rulesLength] at lengthZero
    cases source with
    | nil => simp at facts
    | cons rule rules => simp at lengthZero

/-! ## Exact cross-stage canary -/

def canaryTypedRule : TypedRule :=
  { name := canaryRule.name
    head := .application canaryNode.text .nil
    body := []
    variableCount := 0 }

def canaryTypedProgram : TypedProgram := [canaryTypedRule]

theorem canary_typed_program_supported :
    canaryTypedProgram.locallySupported = true := by
  set_option maxRecDepth 10000 in
  decide

theorem compile_canary_typed_program :
    compile canaryTypedProgram = canaryProgram := by
  decide

theorem lower_canary_typed_program :
    lower? canaryTypedProgram =
      some { rules := [canaryAdmittedRule] } := by
  unfold lower?
  rw [compile_canary_typed_program]
  have physical : canaryProgram.encodable? = true :=
    (Program.encodable?_eq_true_iff canaryProgram).mpr
      canaryProgram_encodable
  have meaning :
      canaryTypedProgram.toAdmitted =
        { rules := [canaryAdmittedRule] } := by decide
  simp [validate?, physical, canary_program_admits, meaning]

theorem compileBytes?_canary_typed_program :
    compileBytes? canaryTypedProgram = some canaryBytes := by
  unfold compileBytes?
  rw [compile_canary_typed_program]
  have validation := lower_canary_typed_program
  unfold lower? at validation
  rw [compile_canary_typed_program] at validation
  change
    (match validate? canaryTypedProgram canaryProgram with
      | some _ => some (encodeProgram canaryProgram)
      | none => none) = some canaryBytes
  rw [validation, encodeProgram_canaryProgram]

/-! ## Structurally different witness and rejection controls -/

def binaryTypedRule : TypedRule :=
  { name := [112, 97, 105, 114]
    head :=
      .application [112, 97, 105, 114]
        (.cons (.variable 0) (.cons (.variable 1) .nil))
    body := []
    variableCount := 2 }

def binaryTypedProgram : TypedProgram := [binaryTypedRule]

def binaryWireProgram : Program :=
  { nodes :=
      [scalarNode 2 0 0 [],
       scalarNode 2 0 1 [],
       { kind := 5
         childOffset := 0
         childCount := 2
         integerValue := 0
         variableSlot := 0
         text := [112, 97, 105, 114] }]
    children := [0, 1]
    rules :=
      [{ head := 2
         bodyOffset := 0
         bodyCount := 0
         variableCount := 2
         name := [112, 97, 105, 114] }]
    bodies := [] }

def binaryBytes : List UInt8 :=
  [ 67, 71, 80, 49,
    3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0,
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0,
    5, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 4, 0, 0, 0, 112, 97, 105, 114,
    0, 0, 0, 0, 1, 0, 0, 0,
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
    4, 0, 0, 0, 112, 97, 105, 114 ]

def binaryAdmittedRule : AdmittedRule :=
  { name := [112, 97, 105, 114]
    head :=
      .application [112, 97, 105, 114]
        (.cons (.variable 0) (.cons (.variable 1) .nil))
    body := []
    variableCount := 2 }

theorem compile_binary_typed_program :
    compile binaryTypedProgram = binaryWireProgram := by
  decide

theorem encode_binaryWireProgram :
    encodeProgram binaryWireProgram = binaryBytes := by decide

theorem binary_typed_program_supported :
    binaryTypedProgram.locallySupported = true := by
  set_option maxRecDepth 10000 in
  decide

theorem binary_typed_program_lowers_exactly :
    lower? binaryTypedProgram =
      some { rules := [binaryAdmittedRule] } := by
  unfold lower?
  rw [compile_binary_typed_program]
  have dense : denseVariables 2 [0, 1] = true := by decide
  have admitted :
      admit? binaryWireProgram = some { rules := [binaryAdmittedRule] } := by
    simp [admit?, decodeRule?, decodeTerm?, decodeTerms?, slice?,
      exactCover, ruleNamesUnique, Term.isApplication, DecodedTerm.leaf,
      concatDecodedTerms, concatDecodedRules, ClaimRope.flatten,
      ClaimRope.toListAcc, ClaimRope.ofList, decodedTerms, Terms.ofList,
      maximumDepth, slotRange,
      binaryWireProgram, binaryAdmittedRule, scalarNode,
      Node.locallyValid, Rule.locallyValid, scalarNodeFieldsAreZero,
      bytesNulFree, bytesNonempty, dense, List.range_succ]
  have physical : binaryWireProgram.encodable? = true := by decide
  have meaning :
      binaryTypedProgram.toAdmitted =
        { rules := [binaryAdmittedRule] } := by decide
  simp [validate?, physical, admitted, meaning]

theorem binary_typed_program_lowers :
    (lower? binaryTypedProgram).isSome = true := by
  rw [binary_typed_program_lowers_exactly]
  rfl

theorem compileBytes?_binary_typed_program :
    compileBytes? binaryTypedProgram = some binaryBytes := by
  unfold compileBytes?
  rw [compile_binary_typed_program]
  change
    (match validate? binaryTypedProgram binaryWireProgram with
      | some _ => some (encodeProgram binaryWireProgram)
      | none => none) = some binaryBytes
  rw [show validate? binaryTypedProgram binaryWireProgram =
      some { rules := [binaryAdmittedRule] } by
        simpa [lower?, compile_binary_typed_program] using
          binary_typed_program_lowers_exactly,
    encode_binaryWireProgram]

def sparseTypedRule : TypedRule :=
  { binaryTypedRule with
      head := .application [112, 97, 105, 114]
        (.cons (.variable 1) .nil) }

theorem sparse_typed_rule_rejected_locally :
    sparseTypedRule.locallySupported = false := by
  set_option maxRecDepth 10000 in
  decide

def sparseWireProgram : Program :=
  { nodes :=
      [scalarNode 2 0 1 [],
       { kind := 5
         childOffset := 0
         childCount := 1
         integerValue := 0
         variableSlot := 0
         text := [112, 97, 105, 114] }]
    children := [0]
    rules :=
      [{ head := 1
         bodyOffset := 0
         bodyCount := 0
         variableCount := 2
         name := [112, 97, 105, 114] }]
    bodies := [] }

def sparseWireRule : Rule :=
  { head := 1
    bodyOffset := 0
    bodyCount := 0
    variableCount := 2
    name := [112, 97, 105, 114] }

theorem compile_sparse_typed_rule :
    compile [sparseTypedRule] = sparseWireProgram := by
  decide

theorem sparseWireProgram_rules :
    sparseWireProgram.rules = [sparseWireRule] := by
  rfl

theorem sparse_typed_program_rejected_by_physical_admission :
    (lower? [sparseTypedRule]).isSome = false := by
  unfold lower?
  rw [compile_sparse_typed_rule]
  have denseReject : denseVariables 2 [1] = false :=
    denseVariables_false_of_missing (slot := 0) (by decide) (by decide)
  have ruleReject : decodeRule? sparseWireProgram sparseWireRule = none := by
    simp [decodeRule?, decodeTerm?, decodeTerms?, slice?,
      Term.isApplication, DecodedTerm.leaf, concatDecodedTerms,
      ClaimRope.flatten, ClaimRope.toListAcc, ClaimRope.ofList, decodedTerms,
      Terms.ofList, maximumDepth, slotRange, sparseWireProgram,
      sparseWireRule, scalarNode, Node.locallyValid, Rule.locallyValid,
      scalarNodeFieldsAreZero, bytesNulFree, bytesNonempty]
    exact denseReject
  have rejected : admit? sparseWireProgram = none := by
    unfold admit?
    rw [sparseWireProgram_rules]
    simp only [List.mapM_cons, List.mapM_nil]
    rw [ruleReject]
    rfl
  have physical : sparseWireProgram.encodable? = true := by decide
  simp [validate?, physical, rejected]

def headlessTypedRule : TypedRule :=
  { binaryTypedRule with head := .symbol [112, 97, 105, 114] }

theorem headless_rule_rejected_locally :
    headlessTypedRule.locallySupported = false := by
  decide

theorem headless_program_rejected_by_physical_admission :
    (lower? [headlessTypedRule]).isSome = false := by
  set_option maxRecDepth 10000 in
  decide

def nulNameTypedRule : TypedRule :=
  { canaryTypedRule with name := [0] }

theorem nul_rule_name_rejected_locally :
    nulNameTypedRule.locallySupported = false := by
  decide

theorem nul_rule_name_rejected_by_physical_admission :
    (lower? [nulNameTypedRule]).isSome = false := by
  set_option maxRecDepth 10000 in
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanLowering
