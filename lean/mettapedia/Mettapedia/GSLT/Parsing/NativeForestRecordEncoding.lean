import Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
import Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeExport

/-!
# Direct encoding of neutral forest records

This is the serialization boundary, not a new parser or a C-memory theorem.
Grammar identity fragments are the output of the unchanged ground-term
renderer.  We prove the fixed record constructors and streamed cons-list
framing against a separately constructed S-expression tree.  Consequently
replacing temporary record trees by these bytes preserves every byte observer,
without appealing to hash collision resistance.

The physical allocation, C formatting, sorting and identity-rendering
boundaries require their own realization evidence.  In particular the
theorems below do not certify an arbitrary native forest as a valid parse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NativeForestRecordEncoding

open Algorithms.MeTTa.Simple.Parser (SExpr)
open IntegerProviderNativeTypeExport
open ClassAwareNativeForestContract (Node NodeKind TerminalValue)

def number (n : Nat) : SExpr := .atom (toString n)

def constructor (name : String) (args : List SExpr) : SExpr :=
  .list (.atom name :: args)

def terminalTerm : TerminalValue → SExpr
  | .scalar n => constructor "cp" [number n]
  | .eof => .atom "eof"
  | .witness n => constructor "pf-witness" [number n]

def terminalText : TerminalValue → String
  | .scalar n => "(cp " ++ toString n ++ ")"
  | .eof => "eof"
  | .witness n => "(pf-witness " ++ toString n ++ ")"

theorem terminalText_eq_render (value : TerminalValue) :
    terminalText value = renderSExpr (terminalTerm value) := by
  cases value <;> simp [terminalText, terminalTerm, constructor, number,
    renderSExpr, renderElements] <;> simp only [← String.append_assoc] <;> rfl

/-- Rendered identity fragments indexed by disposable dense native IDs.
Their interpretation is supplied by the grammar owner, not by this codec. -/
structure Names where
  states : List String
  terminals : List String
  productionLabels : List String

def nodeTerm? (names : Names) (node : Node) : Option SExpr := do
  match node.kind with
  | .symbol id =>
      let identity ← names.states[id]?
      pure (constructor "pf-symbol"
        [.atom identity, number node.scalarStart, number node.scalarStop])
  | .intermediate production dot =>
      let label ← names.productionLabels[production]?
      pure (constructor "pf-intermediate"
        [.atom label, number dot, number node.scalarStart, number node.scalarStop])
  | .terminal id value =>
      let identity ← names.terminals[id]?
      pure (constructor "pf-terminal"
        [.atom identity, terminalTerm value, number node.scalarStart, number node.scalarStop])
  | .epsilon => pure (constructor "pf-epsilon" [number node.scalarStart])

def nodeText? (names : Names) (node : Node) : Option String := do
  match node.kind with
  | .symbol id =>
      let identity ← names.states[id]?
      pure ("(pf-symbol " ++ identity ++ " " ++ toString node.scalarStart ++
        " " ++ toString node.scalarStop ++ ")")
  | .intermediate production dot =>
      let label ← names.productionLabels[production]?
      pure ("(pf-intermediate " ++ label ++ " " ++ toString dot ++ " " ++
        toString node.scalarStart ++ " " ++ toString node.scalarStop ++ ")")
  | .terminal id value =>
      let identity ← names.terminals[id]?
      pure ("(pf-terminal " ++ identity ++ " " ++ terminalText value ++ " " ++
        toString node.scalarStart ++ " " ++ toString node.scalarStop ++ ")")
  | .epsilon => pure ("(pf-epsilon " ++ toString node.scalarStart ++ ")")

/-- Every native record kind agrees with tree construction, including failed
identity lookup. Byte coordinates are deliberately not substituted for scalar
coordinates. -/
theorem nodeText?_eq_render (names : Names) (node : Node) :
    nodeText? names node = (nodeTerm? names node).map renderSExpr := by
  cases node with
  | mk kind start stop byteStart byteStop choiceBegin choiceCount =>
      cases kind with
      | epsilon =>
          simp [nodeText?, nodeTerm?, constructor, number, renderSExpr, renderElements]
          rfl
      | symbol id =>
          cases h : names.states[id]? <;>
            simp [nodeText?, nodeTerm?, h, constructor, number, renderSExpr,
              renderElements, String.append_assoc]
          all_goals (simp only [← String.append_assoc]; rfl)
      | intermediate production dot =>
          cases h : names.productionLabels[production]? <;>
            simp [nodeText?, nodeTerm?, h, constructor, number, renderSExpr,
              renderElements, String.append_assoc]
          all_goals (simp only [← String.append_assoc]; rfl)
      | terminal id value =>
          cases h : names.terminals[id]? <;>
            simp [nodeText?, nodeTerm?, h, constructor, number, terminalText_eq_render,
              renderSExpr, renderElements, String.append_assoc]
          all_goals (simp only [← String.append_assoc]; rfl)

/-- Resolved binary choice fields, using the cached node-record words.
The node renderer correspondence is `nodeText?_eq_render`; native-index
validation and construction of this cache are separate boundaries. -/
structure ChoicePayload where
  parent : String
  productionLabel : String
  prefixNode : Option String
  childNode : String
  pivot : Nat

def choiceTerm (choice : ChoicePayload) : SExpr :=
  constructor "pf-choice" [.atom choice.parent, .atom choice.productionLabel,
    .atom (choice.prefixNode.getD "pf-none"), .atom choice.childNode, number choice.pivot]

def choiceText (choice : ChoicePayload) : String :=
  "(pf-choice " ++ choice.parent ++ " " ++ choice.productionLabel ++
    " " ++ choice.prefixNode.getD "pf-none" ++ " " ++
    choice.childNode ++ " " ++ toString choice.pivot ++ ")"

theorem choiceText_eq_render (choice : ChoicePayload) :
    choiceText choice = renderSExpr (choiceTerm choice) := by
  unfold choiceText choiceTerm constructor number
  rw [renderSExpr.eq_2]
  simp only [renderElements.eq_3, renderElements.eq_2]
  simp only [renderSExpr.eq_1]
  simp only [String.append_assoc]
  simp only [← String.append_assoc]
  rfl

/-- A present prefix can be an arbitrary nested node term: caching its
rendered word does not change the independently built choice tree's bytes. -/
theorem choice_cached_nodes_present (parent prefixNode childNode : SExpr)
    (label : String) (pivot : Nat) :
    choiceText ⟨renderSExpr parent, label, some (renderSExpr prefixNode),
      renderSExpr childNode, pivot⟩ =
      renderSExpr (constructor "pf-choice"
        [parent, .atom label, prefixNode, childNode, number pivot]) := by
  unfold choiceText constructor number
  rw [renderSExpr.eq_2]
  simp only [renderElements.eq_3, renderElements.eq_2]
  simp only [renderSExpr.eq_1, Option.getD_some]
  simp only [String.append_assoc]
  simp only [← String.append_assoc]
  rfl

theorem choice_cached_nodes_absent (parent childNode : SExpr)
    (label : String) (pivot : Nat) :
    choiceText ⟨renderSExpr parent, label, none, renderSExpr childNode, pivot⟩ =
      renderSExpr (constructor "pf-choice"
        [parent, .atom label, .atom "pf-none", childNode, number pivot]) := by
  unfold choiceText constructor number
  rw [renderSExpr.eq_2]
  simp only [renderElements.eq_3, renderElements.eq_2]
  simp only [renderSExpr.eq_1, Option.getD_none]
  simp only [String.append_assoc]
  simp only [← String.append_assoc]
  rfl

def consTerm : List SExpr → SExpr
  | [] => .atom "nil"
  | head :: tail => constructor "cons" [head, consTerm tail]

/-- Emit all opening frames first, then nil and one closing frame per entry.
This is the native digest's streaming order, without a nested term tree. -/
def streamList (entries : List String) : String :=
  String.join (entries.map fun entry => "(cons " ++ entry ++ " ") ++ "nil" ++
    String.join (List.replicate entries.length ")")

theorem streamList_nil : streamList [] = "nil" := by
  simp [streamList]

theorem close_frames_succ (n : Nat) :
    String.join (List.replicate (n + 1) ")") =
      String.join (List.replicate n ")") ++ ")" := by
  rw [List.replicate_add, String.join_append]
  rfl

theorem streamList_cons (head : String) (tail : List String) :
    streamList (head :: tail) = "(cons " ++ head ++ " " ++ streamList tail ++ ")" := by
  simp [streamList, close_frames_succ, String.append_assoc]

/-- The optimization changes construction order but not the full byte word. -/
theorem streamList_eq_render (entries : List SExpr) :
    streamList (entries.map renderSExpr) = renderSExpr (consTerm entries) := by
  induction entries with
  | nil => simp [streamList_nil, consTerm, renderSExpr]
  | cons head tail ih =>
      simp [streamList_cons, consTerm, constructor, renderSExpr, renderElements,
        ih, String.append_assoc]
      simp only [← String.append_assoc]
      rfl

def forestTerm (start : SExpr) (scalarLength : Nat)
    (roots nodes choices : List SExpr) : SExpr :=
  constructor "pf-v1" [start, number scalarLength,
    consTerm roots, consTerm nodes, consTerm choices]

def forestText (start : String) (scalarLength : Nat)
    (roots nodes choices : List String) : String :=
  "(pf-v1 " ++ start ++ " " ++ toString scalarLength ++ " " ++ streamList roots ++
    " " ++ streamList nodes ++ " " ++ streamList choices ++ ")"

theorem forestText_eq_render (start : SExpr) (scalarLength : Nat)
    (roots nodes choices : List SExpr) :
    forestText (renderSExpr start) scalarLength
      (roots.map renderSExpr) (nodes.map renderSExpr) (choices.map renderSExpr) =
        renderSExpr (forestTerm start scalarLength roots nodes choices) := by
  simp [forestText, forestTerm, constructor, number, streamList_eq_render,
    renderSExpr, renderElements, String.append_assoc]
  simp only [← String.append_assoc]
  rfl

/-- Exact words imply preservation for every byte observer, not merely a
selected digest. No collision-freedom assumption is needed. -/
theorem byte_observer_preserved {β : Type} (observer : String → β)
    (start : SExpr) (scalarLength : Nat) (roots nodes choices : List SExpr) :
    observer (forestText (renderSExpr start) scalarLength
      (roots.map renderSExpr) (nodes.map renderSExpr) (choices.map renderSExpr)) =
        observer (renderSExpr (forestTerm start scalarLength roots nodes choices)) := by
  exact congrArg observer (forestText_eq_render start scalarLength roots nodes choices)

/-- Collecting successfully resolved records keeps the exact native order.
Missing identities fail on both routes; this projection does not authorize
a parser to omit an unresolved record. -/
theorem resolved_records_eq (names : Names) (nodes : List Node) :
    nodes.filterMap (nodeText? names) =
      (nodes.filterMap (nodeTerm? names)).map renderSExpr := by
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filterMap_cons, nodeText?_eq_render]
      cases h : nodeTerm? names head <;> simp [h, ih]

/-- A common ordering of the independently encoded record bytes is therefore
unchanged. This does not assert C qsort's correctness. -/
theorem ordered_resolved_records_eq (ordering : List String → List String)
    (names : Names) (nodes : List Node) :
    ordering (nodes.filterMap (nodeText? names)) =
      ordering ((nodes.filterMap (nodeTerm? names)).map renderSExpr) :=
  congrArg ordering (resolved_records_eq names nodes)

def nodeTexts? (names : Names) : List Node → Option (List String)
  | [] => some []
  | head :: tail => do
      let first ← nodeText? names head
      let rest ← nodeTexts? names tail
      pure (first :: rest)

def nodeTerms? (names : Names) : List Node → Option (List SExpr)
  | [] => some []
  | head :: tail => do
      let first ← nodeTerm? names head
      let rest ← nodeTerms? names tail
      pure (first :: rest)

/-- The complete cache fails on unresolved identities rather than omitting
them. On success it is the exact ordered renderer image of all node terms. -/
theorem complete_cache_eq (names : Names) (nodes : List Node) :
    nodeTexts? names nodes = (nodeTerms? names nodes).map (List.map renderSExpr) := by
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
      simp only [nodeTexts?, nodeTerms?, nodeText?_eq_render, ih]
      cases h : nodeTerm? names head <;> cases t : nodeTerms? names tail <;>
        simp_all

theorem complete_cache_failure_reflected (names : Names) (nodes : List Node) :
    nodeTexts? names nodes = none ↔ nodeTerms? names nodes = none := by
  rw [complete_cache_eq]
  simp

example : streamList ["a", "b"] = "(cons a (cons b nil))" := by decide

example : streamList ["a", "b"] ≠ streamList ["b", "a"] := by decide

example : streamList ["a", "a"] ≠ streamList ["a"] := by decide

example : terminalText (.witness 4) ≠ terminalText (.scalar 4) := by decide

end Mettapedia.GSLT.Parsing.NativeForestRecordEncoding
