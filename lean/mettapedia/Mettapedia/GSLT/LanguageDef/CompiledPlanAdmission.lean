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

/-! ## Linear ownership evidence -/

/-- Persistent concatenation tree for ownership evidence.  Recursive decoding
shares child evidence instead of copying every descendant list into every
ancestor; admission flattens each complete forest exactly once. -/
inductive ClaimRope where
  | empty
  | singleton (claim : Nat)
  | append (left right : ClaimRope)
  deriving DecidableEq, Repr

def ClaimRope.toList : ClaimRope -> List Nat
  | .empty => []
  | .singleton claim => [claim]
  | .append left right => left.toList ++ right.toList

def ClaimRope.toListAcc : ClaimRope -> List Nat -> List Nat
  | .empty, suffix => suffix
  | .singleton claim, suffix => claim :: suffix
  | .append left right, suffix =>
      left.toListAcc (right.toListAcc suffix)

/-- Linear executable flattening.  `toList` is the simple structural
specification; this accumulator realization is what admission executes. -/
def ClaimRope.flatten (claims : ClaimRope) : List Nat :=
  claims.toListAcc []

def ClaimRope.ofList : List Nat -> ClaimRope
  | [] => .empty
  | claim :: claims => .append (.singleton claim) (ofList claims)

theorem ClaimRope.toListAcc_eq_append (claims : ClaimRope)
    (suffix : List Nat) :
    claims.toListAcc suffix = claims.toList ++ suffix := by
  induction claims generalizing suffix with
  | empty => rfl
  | singleton claim => rfl
  | append left right leftHypothesis rightHypothesis =>
      simp only [ClaimRope.toListAcc, ClaimRope.toList]
      rw [rightHypothesis, leftHypothesis]
      exact List.append_assoc _ _ _ |>.symm

theorem ClaimRope.flatten_eq_toList (claims : ClaimRope) :
    claims.flatten = claims.toList := by
  simpa [ClaimRope.flatten] using claims.toListAcc_eq_append []

@[simp] theorem ClaimRope.toList_empty :
    ClaimRope.empty.toList = [] := rfl

@[simp] theorem ClaimRope.toList_singleton (claim : Nat) :
    (ClaimRope.singleton claim).toList = [claim] := rfl

@[simp] theorem ClaimRope.toList_append (left right : ClaimRope) :
    (ClaimRope.append left right).toList = left.toList ++ right.toList := rfl

@[simp] theorem ClaimRope.toList_ofList (claims : List Nat) :
    (ClaimRope.ofList claims).toList = claims := by
  induction claims with
  | nil => rfl
  | cons claim claims inductionHypothesis =>
      simp [ClaimRope.ofList, inductionHypothesis]

/-- Evidence-producing result of reconstructing one physical tree.  Ownership
ropes are checked globally rather than hidden by the recursive decoder. -/
structure DecodedTerm where
  term : Term
  claimedNodes : ClaimRope
  claimedChildSlots : ClaimRope
  usedVariables : ClaimRope
  depth : Nat
  deriving DecidableEq, Repr

def DecodedTerm.leaf (term : Term) (node : Nat)
    (usedVariables : List Nat := []) : DecodedTerm :=
  { term
    claimedNodes := .singleton node
    claimedChildSlots := .empty
    usedVariables := .ofList usedVariables
    depth := 0 }

def concatDecodedTerms (terms : List DecodedTerm) :
    ClaimRope × ClaimRope × ClaimRope :=
  terms.foldr
    (fun term suffix =>
      (.append term.claimedNodes suffix.1,
       .append term.claimedChildSlots suffix.2.1,
       .append term.usedVariables suffix.2.2))
    (.empty, .empty, .empty)

/-- Rope accumulation preserves the exact left-to-right evidence order of the
structural list specification. -/
theorem concatDecodedTerms_toList (terms : List DecodedTerm) :
    (concatDecodedTerms terms).1.toList =
        terms.flatMap (fun term => term.claimedNodes.toList) ∧
      (concatDecodedTerms terms).2.1.toList =
        terms.flatMap (fun term => term.claimedChildSlots.toList) ∧
      (concatDecodedTerms terms).2.2.toList =
        terms.flatMap (fun term => term.usedVariables.toList) := by
  induction terms with
  | nil => simp [concatDecodedTerms]
  | cons term terms inductionHypothesis =>
      rcases inductionHypothesis with ⟨nodes, children, used⟩
      simp only [concatDecodedTerms, List.foldr_cons, List.flatMap_cons,
        ClaimRope.toList_append]
      exact ⟨congrArg (term.claimedNodes.toList ++ ·) nodes,
        congrArg (term.claimedChildSlots.toList ++ ·) children,
        congrArg (term.usedVariables.toList ++ ·) used⟩

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

/-- A missing slot is a direct, local rejection witness for dense admission. -/
theorem denseVariables_false_of_missing
    {width : Nat} {usedVariables : List Nat} {slot : Nat}
    (inRange : slot < width) (missing : slot ∉ usedVariables) :
    denseVariables width usedVariables = false := by
  unfold denseVariables
  rw [Bool.and_eq_false_iff]
  right
  rw [List.all_eq_false]
  exact ⟨slot, List.mem_range.mpr inRange,
    by simpa using missing⟩

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
              claimedNodes := .append (.singleton nodeIndex) ownership.1
              claimedChildSlots :=
                .append
                  (.ofList
                    (slotRange node.childOffset.toNat node.childCount.toNat))
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
  claimedNodes : ClaimRope
  claimedChildSlots : ClaimRope
  claimedBodySlots : ClaimRope
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
    let usedVariables :=
      (ClaimRope.append head.usedVariables ownership.2.2).flatten
    if !denseVariables rule.variableCount.toNat usedVariables then none else
    some
      { rule :=
          { name := rule.name
            head := head.term
            body := body.map DecodedTerm.term
            variableCount := rule.variableCount.toNat }
        claimedNodes := .append head.claimedNodes ownership.1
        claimedChildSlots := .append head.claimedChildSlots ownership.2.1
        claimedBodySlots :=
          .ofList (slotRange rule.bodyOffset.toNat rule.bodyCount.toNat) }

def ruleNamesUnique (rules : List AdmittedRule) : Bool :=
  decide (rules.map AdmittedRule.name).Nodup

structure AdmittedProgram where
  rules : List AdmittedRule
  deriving DecidableEq, Repr

def concatDecodedRules (rules : List DecodedRule) :
    ClaimRope × ClaimRope × ClaimRope :=
  rules.foldr
    (fun rule suffix =>
      (.append rule.claimedNodes suffix.1,
       .append rule.claimedChildSlots suffix.2.1,
       .append rule.claimedBodySlots suffix.2.2))
    (.empty, .empty, .empty)

/-- Complete-forest rope accumulation is extensionally the prior ordered
`flatMap` specification for all three ownership dimensions. -/
theorem concatDecodedRules_toList (rules : List DecodedRule) :
    (concatDecodedRules rules).1.toList =
        rules.flatMap (fun rule => rule.claimedNodes.toList) ∧
      (concatDecodedRules rules).2.1.toList =
        rules.flatMap (fun rule => rule.claimedChildSlots.toList) ∧
      (concatDecodedRules rules).2.2.toList =
        rules.flatMap (fun rule => rule.claimedBodySlots.toList) := by
  induction rules with
  | nil => simp [concatDecodedRules]
  | cons rule rules inductionHypothesis =>
      rcases inductionHypothesis with ⟨nodes, children, bodies⟩
      simp only [concatDecodedRules, List.foldr_cons, List.flatMap_cons,
        ClaimRope.toList_append]
      exact ⟨congrArg (rule.claimedNodes.toList ++ ·) nodes,
        congrArg (rule.claimedChildSlots.toList ++ ·) children,
        congrArg (rule.claimedBodySlots.toList ++ ·) bodies⟩

/-- Complete structural admission corresponding to the generic compiled-plan
waist.  Byte framing and digest authentication are deliberately prior stages. -/
def admit? (program : Program) : Option AdmittedProgram := do
  if program.nodes.isEmpty || program.rules.isEmpty then none else
  let decoded <- program.rules.mapM (decodeRule? program)
  let rules := decoded.map DecodedRule.rule
  if !ruleNamesUnique rules then none else
  let ownership := concatDecodedRules decoded
  if !exactCover program.nodes.length ownership.1.flatten then none else
  if !exactCover program.children.length ownership.2.1.flatten then none else
  if !exactCover program.bodies.length ownership.2.2.flatten then none else
  some { rules }

def accepted (program : Program) : Bool :=
  (admit? program).isSome

/-- Complete physical entry point: exact `CGP1` consumption followed by
structural admission. -/
def admitBytes? (bytes : List UInt8) : Option AdmittedProgram := do
  let program <- decodeProgram? bytes
  admit? program

theorem admitBytes?_encodeProgram (program : Program)
    (encodable : program.Encodable) :
    admitBytes? (encodeProgram program) = admit? program := by
  simp [admitBytes?, decodeProgram?_encodeProgram program encodable]

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
    concatDecodedRules, ClaimRope.flatten, ClaimRope.toListAcc,
    ClaimRope.ofList, maximumDepth, slotRange, canaryProgram, canaryRule, canaryNode,
    canaryAdmittedRule, Node.locallyValid, Rule.locallyValid,
    scalarNodeFieldsAreZero, bytesNulFree, bytesNonempty]

theorem canary_program_accepts : accepted canaryProgram = true := by
  simp [accepted, canary_program_admits]

theorem canary_bytes_admit :
    admitBytes? canaryBytes = some { rules := [canaryAdmittedRule] } := by
  simp [admitBytes?, decodeProgram?_canaryBytes, canary_program_admits]

theorem trailing_canary_bytes_reject :
    admitBytes? (canaryBytes ++ [0]) = none := by
  simp [admitBytes?, decodeProgram?_rejects_trailing_canary_byte]

theorem corrupt_magic_bytes_reject :
    admitBytes? (0 :: canaryBytes.tail) = none := by
  simp [admitBytes?, decodeProgram?_rejects_corrupt_canary_magic]

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
    concatDecodedRules, ClaimRope.flatten, ClaimRope.toListAcc,
    ClaimRope.ofList, maximumDepth, slotRange, unownedChildProgram,
    canaryProgram, canaryRule,
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

def sparseVariableRule : Rule :=
  { head := 1
    bodyOffset := 0
    bodyCount := 0
    variableCount := 2
    name := canaryRule.name }

theorem sparseVariableProgram_rules :
    sparseVariableProgram.rules = [sparseVariableRule] := by
  rfl

theorem sparse_variable_inventory_rejects :
    accepted sparseVariableProgram = false := by
  change (admit? sparseVariableProgram).isSome = false
  have variableReject : denseVariables 2 [1] = false :=
    denseVariables_false_of_missing (slot := 0) (by decide) (by decide)
  have missingZero : ∃ slot < 2, ¬slot = 1 :=
    ⟨0, by decide, by decide⟩
  have ruleReject :
      decodeRule? sparseVariableProgram sparseVariableRule = none := by
    simp [decodeRule?, decodeTerm?, decodeTerms?, slice?, denseVariables,
      Term.isApplication, DecodedTerm.leaf, concatDecodedTerms, decodedTerms,
      Terms.ofList, ClaimRope.flatten, ClaimRope.toListAcc, ClaimRope.ofList,
      maximumDepth, slotRange, sparseVariableProgram,
      sparseVariableRule, canaryNode, canaryRule, Node.locallyValid, Rule.locallyValid,
      scalarNodeFieldsAreZero, bytesNulFree, bytesNonempty]
    exact missingZero
  have rejected : admit? sparseVariableProgram = none := by
    unfold admit?
    rw [sparseVariableProgram_rules]
    simp only [List.mapM_cons, List.mapM_nil]
    rw [ruleReject]
    rfl
  rw [rejected]
  rfl

def sharedRootProgram : Program :=
  { canaryProgram with
      rules := [canaryRule, { canaryRule with name := [111, 116, 104, 101, 114] }] }

theorem shared_rule_root_rejects : accepted sharedRootProgram = false := by
  simp [accepted, admit?, decodeRule?, decodeTerm?, decodeTerms?, slice?,
    exactCover, denseVariables, ruleNamesUnique, Term.isApplication,
    DecodedTerm.leaf, concatDecodedTerms, decodedTerms, Terms.ofList,
    concatDecodedRules, ClaimRope.flatten, ClaimRope.toListAcc,
    ClaimRope.ofList, maximumDepth, slotRange, sharedRootProgram,
    canaryProgram, canaryRule,
    canaryNode, Node.locallyValid, Rule.locallyValid,
    scalarNodeFieldsAreZero, bytesNulFree, bytesNonempty]

def duplicateNameProgram : Program :=
  let secondNode : Node :=
    { kind := 5
      childOffset := 0
      childCount := 0
      integerValue := 0
      variableSlot := 0
      text := canaryNode.text }
  { nodes := [canaryNode, secondNode]
    children := []
    rules :=
      [canaryRule,
       { head := 1
         bodyOffset := 0
         bodyCount := 0
         variableCount := 0
         name := canaryRule.name }]
    bodies := [] }

theorem duplicate_rule_name_rejects :
    accepted duplicateNameProgram = false := by
  change (admit? duplicateNameProgram).isSome = false
  have rejected : admit? duplicateNameProgram = none := by
    simp [admit?, decodeRule?, decodeTerm?, decodeTerms?, slice?,
      denseVariables, ruleNamesUnique, Term.isApplication, DecodedTerm.leaf,
      concatDecodedTerms, concatDecodedRules, ClaimRope.flatten,
      ClaimRope.toListAcc, ClaimRope.ofList, decodedTerms, Terms.ofList,
      maximumDepth, slotRange,
      duplicateNameProgram, canaryNode, canaryRule,
      Node.locallyValid, Rule.locallyValid, scalarNodeFieldsAreZero,
      bytesNulFree, bytesNonempty]
  rw [rejected]
  rfl

end Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission
