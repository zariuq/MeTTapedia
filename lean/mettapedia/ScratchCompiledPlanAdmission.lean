import Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat

/-!
# Structural admission for compiled finite-Horn plans

`CompiledPlanWireFormat` specifies the exact physical bytes consumed by the
generic CeTTa loader.  This module specifies the stronger structural boundary
that makes a decoded packet an executable finite-Horn forest.

Admission is independent of guest vocabulary.  It reconstructs typed terms
from postorder nodes, requires every node, child slot, and body slot to have
exactly one owner, checks dense rule-local variable slots, and rejects unknown
node kinds, excessive depth, non-application rule roots, duplicate rule names,
and malformed table slices.  The admitted result retains the reconstructed
terms, so later semantic refinements do not need to reason about unchecked
indices.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission

open CompiledPlanWireFormat

/-! ## Typed reconstruction -/

mutual

/-- Typed meaning of one admitted physical node tree. -/
inductive Term where
  | symbol (name : List UInt8)
  | variable (slot : UInt32)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (arguments : Terms)
  deriving DecidableEq, Repr

inductive Terms where
  | nil
  | cons (head : Term) (tail : Terms)
  deriving DecidableEq, Repr

end

def Terms.ofList : List Term -> Terms
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def Term.isApplication : Term -> Bool
  | .application _ _ => true
  | _ => false

/-- Evidence-producing result of reconstructing one physical tree.  Ownership
lists are checked globally rather than hidden by the recursive decoder. -/
structure DecodedTerm where
  term : Term
  claimedNodes : List Nat
  claimedChildSlots : List Nat
  usedVariables : List Nat
  depth : Nat
  deriving DecidableEq, Repr

def DecodedTerm.leaf (term : Term) (node : Nat)
    (usedVariables : List Nat := []) : DecodedTerm :=
  { term
    claimedNodes := [node]
    claimedChildSlots := []
    usedVariables
    depth := 0 }

def concatDecodedTerms (terms : List DecodedTerm) :
    List Nat × List Nat × List Nat :=
  (terms.flatMap DecodedTerm.claimedNodes,
    terms.flatMap DecodedTerm.claimedChildSlots,
    terms.flatMap DecodedTerm.usedVariables)

def decodedTerms (terms : List DecodedTerm) : Terms :=
  Terms.ofList (terms.map DecodedTerm.term)

def maximumDepth : List DecodedTerm -> Nat
  | [] => 0
  | term :: terms => max term.depth (maximumDepth terms)

/-! ## Total table helpers -/

/-- A checked contiguous table slice. -/
def slice? (values : List alpha) (offset count : Nat) : Option (List alpha) :=
  if offset <= values.length && count <= values.length - offset then
    some ((values.drop offset).take count)
  else
    none

/-- Indices of a contiguous physical table slice. -/
def slotRange (offset count : Nat) : List Nat :=
  (List.range count).map (offset + ·)

/-- Exact ownership of a finite table: every index is in range, occurs once,
and the number of claims equals the table width. -/
def exactCover (width : Nat) (claims : List Nat) : Bool :=
  claims.length == width &&
    claims.all (fun claim => claim < width) &&
    decide claims.Nodup

/-- Dense use of all slots below `width`.  Repeated variable occurrences are
allowed, while holes and out-of-range slots are rejected. -/
def denseVariables (width : Nat) (usedVariables : List Nat) : Bool :=
  usedVariables.all (fun slot => slot < width) &&
    (List.range width).all fun slot => usedVariables.contains slot

/-! ## Postorder node reconstruction -/

mutual

/-- Reconstruct one node tree.  Fuel is independent of the packet's declared
depth; callers use the node-table size, and admission separately enforces the
runtime depth limit. -/
def decodeTerm? (program : Program) : Nat -> Nat -> Option DecodedTerm
  | 0, _ => none
  | fuel + 1, nodeIndex => do
      let node <- program.nodes[nodeIndex]?
      if !node.locallyValid then none else
      match node.kind.toNat with
      | 1 =>
          some (DecodedTerm.leaf (.symbol node.text) nodeIndex)
      | 2 =>
          some (DecodedTerm.leaf (.variable node.variableSlot) nodeIndex
            [node.variableSlot.toNat])
      | 3 =>
          some (DecodedTerm.leaf (.string node.text) nodeIndex)
      | 4 =>
          some (DecodedTerm.leaf (.integer node.integerValue) nodeIndex)
      | 5 => do
          let children <- slice? program.children
            node.childOffset.toNat node.childCount.toNat
          if !children.all (fun child => child.toNat < nodeIndex) then none else
          let decoded <- decodeTerms? program fuel children
          let ownership := concatDecodedTerms decoded
          some
            { term := .application node.text (decodedTerms decoded)
              claimedNodes := nodeIndex :: ownership.1
              claimedChildSlots :=
                slotRange node.childOffset.toNat node.childCount.toNat ++
                  ownership.2.1
              usedVariables := ownership.2.2
              depth := maximumDepth decoded + 1 }
      | _ => none

def decodeTerms? (program : Program) (fuel : Nat) :
    List UInt32 -> Option (List DecodedTerm)
  | [] => some []
  | node :: nodes => do
      let head <- decodeTerm? program fuel node.toNat
      let tail <- decodeTerms? program fuel nodes
      some (head :: tail)

end

/-! ## Rule and complete-program admission -/

structure AdmittedRule where
  name : List UInt8
  head : Term
  body : List Term
  variableCount : Nat
  deriving DecidableEq, Repr

structure DecodedRule where
  rule : AdmittedRule
  claimedNodes : List Nat
  claimedChildSlots : List Nat
  claimedBodySlots : List Nat
  deriving DecidableEq, Repr

def decodeRule? (program : Program) (rule : Rule) : Option DecodedRule := do
  if !rule.locallyValid then none else
  if rule.variableCount.toNat > program.nodes.length then none else
  let head <- decodeTerm? program (program.nodes.length + 1) rule.head.toNat
  let bodyRoots <- slice? program.bodies
    rule.bodyOffset.toNat rule.bodyCount.toNat
  let body <- decodeTerms? program (program.nodes.length + 1) bodyRoots
  if !head.term.isApplication ||
      !body.all (fun decoded => decoded.term.isApplication) then
    none
  else if head.depth > 4096 || body.any (fun decoded => decoded.depth > 4096) then
    none
  else
    let ownership := concatDecodedTerms body
    let usedVariables := head.usedVariables ++ ownership.2.2
    if !denseVariables rule.variableCount.toNat usedVariables then none else
    some
      { rule :=
          { name := rule.name
            head := head.term
            body := body.map DecodedTerm.term
            variableCount := rule.variableCount.toNat }
        claimedNodes := head.claimedNodes ++ ownership.1
        claimedChildSlots := head.claimedChildSlots ++ ownership.2.1
        claimedBodySlots :=
          slotRange rule.bodyOffset.toNat rule.bodyCount.toNat }

def ruleNamesUnique (rules : List AdmittedRule) : Bool :=
  decide (rules.map AdmittedRule.name).Nodup

structure AdmittedProgram where
  rules : List AdmittedRule
  deriving DecidableEq, Repr

/-- Complete structural admission corresponding to the generic compiled-plan
waist.  Byte framing and digest authentication are deliberately prior stages. -/
def admit? (program : Program) : Option AdmittedProgram := do
  if program.nodes.isEmpty || program.rules.isEmpty then none else
  let decoded <- program.rules.mapM (decodeRule? program)
  let rules := decoded.map DecodedRule.rule
  if !ruleNamesUnique rules then none else
  if !exactCover program.nodes.length
      (decoded.flatMap DecodedRule.claimedNodes) then none else
  if !exactCover program.children.length
      (decoded.flatMap DecodedRule.claimedChildSlots) then none else
  if !exactCover program.bodies.length
      (decoded.flatMap DecodedRule.claimedBodySlots) then none else
  some { rules }

def accepted (program : Program) : Bool :=
  (admit? program).isSome

/-! ## Cross-runtime positive and negative controls -/

def canaryAdmittedRule : AdmittedRule :=
  { name := canaryRule.name
    head := .application canaryNode.text .nil
    body := []
    variableCount := 0 }

theorem canary_program_admits :
    admit? canaryProgram = some { rules := [canaryAdmittedRule] } := by
  simp [admit?, decodeRule?, decodeTerm?, decodeTerms?, slice?, exactCover,
    denseVariables, ruleNamesUnique, Term.isApplication,
    DecodedTerm.leaf, concatDecodedTerms, decodedTerms, Terms.ofList,
    maximumDepth, slotRange, canaryProgram, canaryRule, canaryNode,
    canaryAdmittedRule, Node.locallyValid, Rule.locallyValid,
    scalarNodeFieldsAreZero, bytesNulFree, bytesNonempty]

theorem canary_program_accepts : accepted canaryProgram = true := by
  simp [accepted, canary_program_admits]

theorem unknown_kind_rejects : accepted unknownKindProgram = false := by
  simp [accepted, admit?, decodeRule?, decodeTerm?,
    unknownKindProgram, canaryProgram, canaryRule, canaryNode,
    Node.locallyValid, scalarNodeFieldsAreZero, bytesNulFree, bytesNonempty]

def unownedChildProgram : Program :=
  { canaryProgram with children := [0] }

theorem unowned_child_slot_rejects :
    accepted unownedChildProgram = false := by
  simp [accepted, admit?, decodeRule?, decodeTerm?, decodeTerms?, slice?,
    exactCover, denseVariables, ruleNamesUnique, Term.isApplication,
    DecodedTerm.leaf, concatDecodedTerms, decodedTerms, Terms.ofList,
    maximumDepth, slotRange, unownedChildProgram, canaryProgram, canaryRule,
    canaryNode, Node.locallyValid, Rule.locallyValid,
    scalarNodeFieldsAreZero, bytesNulFree, bytesNonempty]

def forwardChildProgram : Program :=
  { nodes :=
      [{ canaryNode with childOffset := 0, childCount := 1 },
       { canaryNode with kind := 1, text := [120] }]
    children := [1]
    rules := [canaryRule]
    bodies := [] }

theorem forward_child_rejects : accepted forwardChildProgram = false := by
  simp [accepted, admit?, decodeRule?, decodeTerm?, decodeTerms?, slice?,
    forwardChildProgram, canaryRule, canaryNode,
    Node.locallyValid, Rule.locallyValid, scalarNodeFieldsAreZero,
    bytesNulFree, bytesNonempty]

def sparseVariableProgram : Program :=
  let variableNode : Node :=
    { kind := 2
      childOffset := 0
      childCount := 0
      integerValue := 0
      variableSlot := 1
      text := [] }
  let applicationNode : Node :=
    { canaryNode with childCount := 1 }
  { nodes :=
      [variableNode, applicationNode]
    children := [0]
    rules :=
      [{ head := 1
         bodyOffset := 0
         bodyCount := 0
         variableCount := 2
         name := canaryRule.name }]
    bodies := [] }


#reduce denseVariables 2 [1]
#reduce decodeRule? sparseVariableProgram sparseVariableProgram.rules[0]!
#reduce admit? sparseVariableProgram
end Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission
