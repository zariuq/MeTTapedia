import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeComposition
import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Cache

/-!
# Chronological sharing of original rewrite recipes

Nodes retain original recipe and conversion data. References name earlier
certificate positions. This dependency serialization is separate from the
order of object-language events: expansion retains every reference use,
including repeated uses of one shared recipe.

Local recipe checks admit internal rule codes. The existing shared-certificate
checker then validates references and literal endpoint judgments. Submitted
nodes contain no proof fields, and no memoizing emitter identifies events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeDAG

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralRewriteRecipe
open GeneralRewriteRecipeComposition
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Framework.PathTypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

abbrev Claim := Pattern × Pattern

/-- Node positions are certificate identifiers. Repeated equal payloads at
different positions remain different declared nodes. -/
inductive Node where
  | refl (state : Pattern)
  | conversion (source target : Pattern) (walk : List GeneralOccurrenceSemantics.Conversion)
  | atomic (source target : Pattern) (recipe : StepTrace)
  | trans (source middle target : Pattern) (left right : Nat)
  deriving Repr

def Node.claim : Node → Claim
  | .refl state => (state, state)
  | .conversion source target _ | .atomic source target _ | .trans source _ target _ _ =>
      (source, target)

def Node.references : Node → List Nat
  | .trans _ _ _ left right => [left, right]
  | _ => []

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

/-- Independent local node authority. The table is an ordered prefix of
already licensed endpoint judgments, not a supplied derivability oracle. -/
inductive Node.Valid (table : List Claim) : Node → Prop where
  | refl (state : Pattern) : Valid table (.refl state)
  | conversion {source target : Pattern} {walk : List GeneralOccurrenceSemantics.Conversion} :
      GeneralOccurrenceSemantics.ConversionPath plan bound type source target walk →
      Valid table (.conversion source target walk)
  | atomic {source target : Pattern} {recipe : StepTrace} :
      StepTrace.Valid plan bound type source target recipe → Valid table (.atomic source target recipe)
  | trans {source middle target : Pattern} {left right : Nat} :
      table[left]? = some (source, middle) → table[right]? = some (middle, target) →
      Valid table (.trans source middle target left right)

inductive NodesValid : List Claim → List Node → List Claim → Prop where
  | nil (table : List Claim) : NodesValid table [] table
  | cons {table final : List Claim} {node : Node} {rest : List Node} :
      Node.Valid plan bound type table node →
      NodesValid (table ++ [node.claim]) rest final → NodesValid table (node :: rest) final

structure Graph where
  nodes : List Node
  root : Nat
  deriving Repr

def Graph.Valid (graph : Graph) (claim : Claim) : Prop :=
  ∃ table, NodesValid plan bound type [] graph.nodes table ∧ table[graph.root]? = some claim

/-- Internal rule evidence is constructed after replay, never requested from
the submitted graph. Proof fields are erased by execution. -/
inductive Rule where
  | refl (state : Pattern)
  | conversion (source target : Pattern) (walk : List GeneralOccurrenceSemantics.Conversion)
      (valid : GeneralOccurrenceSemantics.ConversionPath plan bound type source target walk)
  | atomic (source target : Pattern) (recipe : StepTrace)
      (valid : StepTrace.Valid plan bound type source target recipe)
  | trans (source middle target : Pattern)

def Rule.conclusion : Rule plan bound type → Claim
  | .refl state => (state, state)
  | .conversion source target _ _ | .atomic source target _ _ | .trans source _ target => (source, target)

def Rule.premises : Rule plan bound type → List Claim
  | .trans source middle target => [(source, middle), (middle, target)]
  | _ => []

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule plan bound type
  conclusion := Rule.conclusion plan bound type
  premises := Rule.premises plan bound type

/-- Decode local evidence and preserve its original payload before invoking
the shared reference checker. No alternatives are generated here. -/
def Node.admit? : Node → Option (Shared.Row (presentation plan bound type))
  | .refl state => some ⟨.refl state, fun position => Fin.elim0 position⟩
  | .conversion source target walk =>
      if accepted : GeneralRewriteRecipe.checkConversions plan bound type source target walk = true then
        some ⟨.conversion source target walk
          ((GeneralRewriteRecipe.checkConversions_exact plan bound type source target walk).mp accepted),
          fun position => Fin.elim0 position⟩
      else none
  | .atomic source target recipe =>
      if accepted : GeneralRewriteRecipe.check plan bound type source target recipe = true then
        some ⟨.atomic source target recipe
          ((GeneralRewriteRecipe.check_exact plan bound type source target recipe).mp accepted),
          fun position => Fin.elim0 position⟩
      else none
  | .trans source middle target left right =>
      some ⟨.trans source middle target, fun position => if position.val = 0 then left else right⟩

def prepare? : List Node → Option (List (Shared.Row (presentation plan bound type)))
  | [] => some []
  | node :: rest => do
      let row ← node.admit? plan bound type
      let rows ← prepare? rest
      pure (row :: rows)

/-- Every declared row is checked, including an unused bad row. The shared
checker enforces prior references, exact joins and the selected root. -/
def Graph.check (graph : Graph) (claim : Claim) : Bool :=
  match prepare? plan bound type graph.nodes with
  | none => false
  | some rows => Shared.checkJudgments ⟨rows, graph.root⟩ claim

theorem Node.admitted_conclusion {node : Node} {row : Shared.Row (presentation plan bound type)}
    (admitted : node.admit? plan bound type = some row) :
    Rule.conclusion plan bound type row.rule = node.claim := by
  cases node <;> simp only [Node.admit?] at admitted
  all_goals try split at admitted <;> try contradiction
  all_goals cases Option.some.inj admitted; rfl

theorem Node.admitted_exact {node : Node} {row : Shared.Row (presentation plan bound type)}
    (admitted : node.admit? plan bound type = some row) (table : List Claim) :
    Node.Valid plan bound type table node ↔ Shared.ValidRow table row := by
  cases node with
  | refl state =>
      cases Option.some.inj admitted
      constructor
      · intro _ position; exact Fin.elim0 position
      · intro _; exact .refl state
  | conversion source target walk =>
      simp only [Node.admit?] at admitted
      split at admitted
      next accepted =>
        cases Option.some.inj admitted
        constructor
        · intro _ position; exact Fin.elim0 position
        · intro _
          exact .conversion ((GeneralRewriteRecipe.checkConversions_exact plan bound type _ _ _).mp accepted)
      next => contradiction
  | atomic source target recipe =>
      simp only [Node.admit?] at admitted
      split at admitted
      next accepted =>
        cases Option.some.inj admitted
        constructor
        · intro _ position; exact Fin.elim0 position
        · intro _
          exact .atomic ((GeneralRewriteRecipe.check_exact plan bound type _ _ _).mp accepted)
      next => contradiction
  | trans source middle target left right =>
      cases Option.some.inj admitted
      change Node.Valid plan bound type table (.trans source middle target left right) ↔
        ∀ position : Fin 2, table[if position.val = 0 then left else right]? =
          some ([(source, middle), (middle, target)].get position)
      constructor
      · intro held position
        cases held with
        | trans first second =>
            have positionCases : position.val = 0 ∨ position.val = 1 := by omega
            rcases positionCases with firstPosition | secondPosition
            · have same : position = (0 : Fin 2) := Fin.ext firstPosition
              subst position
              exact first
            · have same : position = (1 : Fin 2) := Fin.ext secondPosition
              subst position
              exact second
      · intro held
        exact .trans (held 0) (held 1)

theorem Node.valid_admitted {table : List Claim} {node : Node}
    (held : Node.Valid plan bound type table node) :
    ∃ row, node.admit? plan bound type = some row := by
  cases held with
  | refl state => exact ⟨_, rfl⟩
  | conversion held =>
      simp only [Node.admit?]
      rw [dif_pos ((GeneralRewriteRecipe.checkConversions_exact plan bound type _ _ _).mpr held)]
      exact ⟨_, rfl⟩
  | atomic held =>
      simp only [Node.admit?]
      rw [dif_pos ((GeneralRewriteRecipe.check_exact plan bound type _ _ _).mpr held)]
      exact ⟨_, rfl⟩
  | trans => exact ⟨_, rfl⟩

theorem prepare_complete {table final : List Claim} {nodes : List Node}
    (held : NodesValid plan bound type table nodes final) :
    ∃ rows, prepare? plan bound type nodes = some rows := by
  induction held with
  | nil => exact ⟨[], rfl⟩
  | cons head _ ih =>
      obtain ⟨row, admitted⟩ := Node.valid_admitted plan bound type head
      obtain ⟨rows, prepared⟩ := ih
      exact ⟨row :: rows, by simp only [prepare?, admitted, prepared, Option.bind_eq_bind, Option.bind_some, pure]⟩

theorem prepared_inspect_exact {nodes : List Node} {rows : List (Shared.Row (presentation plan bound type))}
    (prepared : prepare? plan bound type nodes = some rows) (table final : List Claim) :
    (Shared.inspectRows table rows).table = some final ↔ NodesValid plan bound type table nodes final := by
  induction nodes generalizing rows table with
  | nil =>
      cases Option.some.inj prepared
      constructor
      · intro same
        change some table = some final at same
        have equal := Option.some.inj same
        cases equal
        exact .nil _
      · intro held
        cases held
        rfl
  | cons node rest ih =>
      simp only [prepare?, Option.bind_eq_bind, Option.bind_eq_some_iff] at prepared
      obtain ⟨row, admitted, later, prepared, same⟩ := prepared
      cases Option.some.inj same
      have conclusion := Node.admitted_conclusion plan bound type admitted
      have localExact := Node.admitted_exact plan bound type admitted table
      cases inspected : (Shared.inspectRow table row).1 with
      | false =>
          have invalid : ¬ Node.Valid plan bound type table node := by
            intro valid
            have checked := (Shared.inspectRow_exact table row).mpr (localExact.mp valid)
            simp only [inspected, Bool.false_eq_true] at checked
          constructor
          · intro impossible
            simp only [Shared.inspectRows, inspected, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at impossible
          · intro held
            cases held with
            | cons head tail => exact (invalid head).elim
      | true =>
          have head := localExact.mpr ((Shared.inspectRow_exact table row).mp inspected)
          simp only [Shared.inspectRows, inspected, ↓reduceIte]
          change (Shared.inspectRows (table ++ [Rule.conclusion plan bound type row.rule]) later).table = some final ↔ _
          rw [conclusion, ih prepared]
          constructor
          · intro tail
            exact .cons head tail
          · intro held
            cases held with
            | cons _ tail => exact tail

theorem Graph.check_exact (graph : Graph) (claim : Claim) :
    graph.check plan bound type claim = true ↔ graph.Valid plan bound type claim := by
  cases prepared : prepare? plan bound type graph.nodes with
  | none =>
      constructor
      · intro impossible
        simp only [Graph.check, prepared, Bool.false_eq_true] at impossible
      · rintro ⟨table, valid, _⟩
        obtain ⟨rows, found⟩ := prepare_complete plan bound type valid
        rw [prepared] at found
        cases found
  | some rows =>
      cases inspected : (Shared.inspectRows ([] : List Claim) rows).table with
      | none =>
          constructor
          · intro impossible
            simp only [Graph.check, prepared, Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows,
              inspected, Bool.false_eq_true] at impossible
          · rintro ⟨table, valid, _⟩
            have found := (prepared_inspect_exact plan bound type prepared [] table).mpr valid
            rw [inspected] at found
            cases found
      | some table =>
          have valid := (prepared_inspect_exact plan bound type prepared [] table).mp inspected
          constructor
          · intro accepted
            simp only [Graph.check, prepared, Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows,
              inspected, decide_eq_true_eq] at accepted
            exact ⟨table, valid, accepted⟩
          · rintro ⟨other, otherValid, atRoot⟩
            have found := (prepared_inspect_exact plan bound type prepared [] other).mpr otherValid
            have same := Option.some.inj (inspected.symm.trans found)
            cases same
            simpa only [Graph.check, prepared, Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows,
              inspected, decide_eq_true_eq] using atRoot

def firings (receipt : SemanticTrace) : List GeneralRuleJobs.Receipt :=
  receipt.trace.map (fun link => link.step.before.firing)

theorem firings_append (front back : SemanticTrace) :
    firings (SemanticTrace.append front back) = firings front ++ firings back := by
  cases second : back.trace <;>
    simp [firings, SemanticTrace.append, second, prependConversions]

/-- An expansion retains the original atomic recipe for each use in order.
The equation walks remain in the semantic trace rather than the event list. -/
structure Expansion (claim : Claim) where
  receipt : SemanticTrace
  valid : SemanticTrace.Valid plan bound type claim.1 claim.2 receipt
  recipes : List StepTrace
  count_eq : receipt.trace.length = recipes.length
  firings_eq : firings receipt = recipes.map (fun recipe => recipe.before.firing)

def expansionAlgebra : JudgmentDerivation.Algebra (presentation plan bound type).signature where
  Carrier := Expansion plan bound type
  conclude := by
    intro claim code children
    rcases code with ⟨rule, rfl⟩
    cases rule with
    | refl state =>
        exact ⟨⟨state, state, [], [], []⟩, ⟨.nil _, .nil _, .nil _⟩, [], rfl, rfl⟩
    | conversion source target walk held =>
        exact ⟨⟨source, source, [], [], walk⟩, ⟨.nil _, .nil _, held⟩, [], rfl, rfl⟩
    | atomic source target recipe held =>
        exact ⟨⟨source, target, [], [⟨target, recipe⟩], []⟩,
          ⟨.nil _, .cons held (.nil _), .nil _⟩, [recipe], rfl, rfl⟩
    | trans source middle target =>
        let front := children ⟨(0 : Fin 2)⟩
        let back := children ⟨(1 : Fin 2)⟩
        exact ⟨SemanticTrace.append front.receipt back.receipt,
          SemanticTrace.append_valid plan bound type front.valid back.valid,
          front.recipes ++ back.recipes, by
            rw [SemanticTrace.append_primitive_count, front.count_eq, back.count_eq, List.length_append], by
            rw [firings_append, front.firings_eq, back.firings_eq, List.map_append]⟩

def expandDerivation {claim : Claim} (tree : (presentation plan bound type).Derivation claim) :
    Expansion plan bound type claim :=
  JudgmentDerivation.interpret (expansionAlgebra plan bound type) tree

/-- Shared references are expanded by the existing reconstruction, which
reuses proof data at every premise occurrence rather than counting one row
as one object-language event. -/
def Graph.expand? (graph : Graph) (claim : Claim) : Option (Expansion plan bound type claim) := do
  let rows ← prepare? plan bound type graph.nodes
  let tree ← Shared.reconstruct? ⟨rows, graph.root⟩ claim
  pure (expandDerivation plan bound type tree)

theorem Graph.check_iff_expand (graph : Graph) (claim : Claim) :
    graph.check plan bound type claim = true ↔ (graph.expand? plan bound type claim).isSome = true := by
  cases prepared : prepare? plan bound type graph.nodes with
  | none => simp only [Graph.check, Graph.expand?, prepared, Bool.false_eq_true, Option.bind_eq_bind, Option.bind_none, Option.isSome_none]
  | some rows =>
      simp only [Graph.check, prepared]
      rw [Shared.checkJudgments_eq_check (P := presentation plan bound type)]
      cases reconstructed : Shared.reconstruct? (⟨rows, graph.root⟩ : Shared.Certificate (presentation plan bound type)) claim <;>
        simp only [Shared.check, Graph.expand?, prepared, reconstructed, Option.bind_eq_bind,
          Option.bind_some, Option.bind_none, Option.isSome_none, Option.isSome_some, pure]

theorem Graph.check_sound {graph : Graph} {claim : Claim}
    (accepted : graph.check plan bound type claim = true) :
    Nonempty (SemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) claim.1 claim.2) := by
  have present := (Graph.check_iff_expand plan bound type graph claim).mp accepted
  cases expanded : graph.expand? plan bound type claim with
  | none => simp only [expanded, Option.isSome_none, Bool.false_eq_true] at present
  | some value =>
      exact ⟨SemanticTrace.toSemanticPath plan bound type claim.1 claim.2 value.receipt value.valid⟩

/-- Emit every tree node afresh. This producer never looks up an earlier
judgment to replace a later source occurrence. The checker still permits
explicit sharing in submitted graphs. -/
def emitFresh {claim : Claim} : (tree : (presentation plan bound type).Derivation claim) →
    (cache : Shared.Cache (presentation plan bound type)) → Shared.Result cache claim
  | .node ⟨rule, rfl⟩ children, cache =>
      let forest := Shared.sequence
        (fun position : Fin (Rule.premises plan bound type rule).length =>
          (Rule.premises plan bound type rule).get position)
        (fun position next => emitFresh (children ⟨position⟩) next) cache
      let emitted := Shared.appendRow forest.next rule forest.located
      ⟨emitted.next, forest.prefixTable.trans emitted.prefixTable, emitted.located⟩

def emitCertificate {claim : Claim} (tree : (presentation plan bound type).Derivation claim) :
    Shared.Certificate (presentation plan bound type) :=
  let result := emitFresh plan bound type tree Shared.emptyCache
  ⟨result.next.rows, result.located.position⟩

theorem emitCertificate_checked {claim : Claim}
    (tree : (presentation plan bound type).Derivation claim) :
    Shared.checkJudgments (emitCertificate plan bound type tree) claim = true := by
  rw [Shared.checkJudgments_eq_check (P := presentation plan bound type)]
  let result := emitFresh plan bound type tree Shared.emptyCache
  change (do
    let table ← Shared.decodeFrom? [] result.next.rows
    Shared.lookup? table result.located.position claim).isSome = true
  rw [result.next.decoded]
  exact result.located.pointed

/-- Lower internal admitted rows back to the original submitted node format.
The primitive recipe and conversion payloads are retained literally. -/
def lowerRow : Shared.Row (presentation plan bound type) → Node
  | ⟨.refl state, _⟩ => .refl state
  | ⟨.conversion source target walk _, _⟩ => .conversion source target walk
  | ⟨.atomic source target recipe _, _⟩ => .atomic source target recipe
  | ⟨.trans source middle target, references⟩ =>
      .trans source middle target (references ⟨0, by change 0 < 2; decide⟩) (references ⟨1, by change 1 < 2; decide⟩)

theorem lowerRow_admitted (row : Shared.Row (presentation plan bound type)) :
    (lowerRow plan bound type row).admit? plan bound type = some row := by
  rcases row with ⟨rule, references⟩
  cases rule with
  | refl state =>
      simp only [lowerRow, Node.admit?]
      congr 1
      congr 1
      funext position
      exact Fin.elim0 position
  | conversion source target walk valid =>
      simp only [lowerRow, Node.admit?]
      rw [dif_pos ((GeneralRewriteRecipe.checkConversions_exact plan bound type _ _ _).mpr valid)]
      congr 1
      congr 1
      funext position
      exact Fin.elim0 position
  | atomic source target recipe valid =>
      simp only [lowerRow, Node.admit?]
      rw [dif_pos ((GeneralRewriteRecipe.check_exact plan bound type _ _ _).mpr valid)]
      congr 1
      congr 1
      funext position
      exact Fin.elim0 position
  | trans source middle target =>
      simp only [lowerRow, Node.admit?]
      congr 1
      congr 1
      funext position
      have bounded : position.val < 2 := position.isLt
      have cases : position.val = 0 ∨ position.val = 1 := by omega
      rcases cases with first | second
      · have same : position = (0 : Fin 2) := Fin.ext first
        subst position
        rfl
      · have same : position = (1 : Fin 2) := Fin.ext second
        subst position
        rfl

theorem prepare_lowered (rows : List (Shared.Row (presentation plan bound type))) :
    prepare? plan bound type (rows.map (lowerRow plan bound type)) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.map_cons, prepare?, lowerRow_admitted, ih,
        Option.bind_eq_bind, Option.bind_some, pure]

def emit {claim : Claim} (tree : (presentation plan bound type).Derivation claim) : Graph :=
  let certificate := emitCertificate plan bound type tree
  ⟨certificate.rows.map (lowerRow plan bound type), certificate.root⟩

theorem emit_checked {claim : Claim} (tree : (presentation plan bound type).Derivation claim) :
    (emit plan bound type tree).check plan bound type claim = true := by
  simp only [emit, Graph.check, prepare_lowered]
  exact emitCertificate_checked plan bound type tree

def reflDerivation (state : Pattern) : (presentation plan bound type).Derivation (state, state) :=
  .node ⟨.refl state, rfl⟩ (fun position => Fin.elim0 position.down)

def conversionDerivation {source target : Pattern}
    {walk : List GeneralOccurrenceSemantics.Conversion}
    (valid : GeneralOccurrenceSemantics.ConversionPath plan bound type source target walk) :
    (presentation plan bound type).Derivation (source, target) :=
  .node ⟨.conversion source target walk valid, rfl⟩ (fun position => Fin.elim0 position.down)

def atomicDerivation {source target : Pattern} {recipe : StepTrace}
    (valid : StepTrace.Valid plan bound type source target recipe) :
    (presentation plan bound type).Derivation (source, target) :=
  .node ⟨.atomic source target recipe valid, rfl⟩ (fun position => Fin.elim0 position.down)

def transDerivation {source middle target : Pattern}
    (front : (presentation plan bound type).Derivation (source, middle))
    (back : (presentation plan bound type).Derivation (middle, target)) :
    (presentation plan bound type).Derivation (source, target) := by
  refine .node ⟨.trans source middle target, rfl⟩ ?_
  intro position
  change (presentation plan bound type).Derivation
    ([(source, middle), (middle, target)].get position.down)
  exact Fin.cases
    (motive := fun index : Fin 2 => (presentation plan bound type).Derivation
      ([(source, middle), (middle, target)].get index))
    front (Fin.cases back (fun impossible => Fin.elim0 impossible)) position.down

theorem expand_trans_recipes {source middle target : Pattern}
    (front : (presentation plan bound type).Derivation (source, middle))
    (back : (presentation plan bound type).Derivation (middle, target)) :
    (expandDerivation plan bound type (transDerivation plan bound type front back)).recipes =
      (expandDerivation plan bound type front).recipes ++ (expandDerivation plan bound type back).recipes := rfl

/-- Reusing one derivation twice retains both ordered recipe-use lists.
This is a use count, not a count of graph nodes or distinct payloads. -/
theorem expand_repeated_recipes {state : Pattern}
    (tree : (presentation plan bound type).Derivation (state, state)) :
    (expandDerivation plan bound type (transDerivation plan bound type tree tree)).recipes.length =
      2 * (expandDerivation plan bound type tree).recipes.length := by
  rw [expand_trans_recipes, List.length_append]
  omega

theorem trace_valid_derivation {trace : Trace} {source target : Pattern}
    (valid : Trace.Valid plan bound type trace source target) :
    Nonempty ((presentation plan bound type).Derivation (source, target)) := by
  induction valid with
  | nil state => exact ⟨reflDerivation plan bound type state⟩
  | cons first _ ih =>
      obtain ⟨tail⟩ := ih
      exact ⟨transDerivation plan bound type (atomicDerivation plan bound type first) tail⟩

theorem semanticTrace_valid_derivation {receipt : SemanticTrace} {source target : Pattern}
    (valid : SemanticTrace.Valid plan bound type source target receipt) :
    Nonempty ((presentation plan bound type).Derivation (source, target)) := by
  obtain ⟨middle⟩ := trace_valid_derivation plan bound type valid.2.1
  exact ⟨transDerivation plan bound type
    (transDerivation plan bound type (conversionDerivation plan bound type valid.1) middle)
    (conversionDerivation plan bound type valid.2.2)⟩

/-- Independent source paths have finite checked graphs. The producer emits
fresh rows, so this existence result never discards receipt occurrences by
memoizing endpoint judgments. -/
theorem exists_checked_iff_semanticPath (source target : Pattern) :
    (∃ graph : Graph, graph.check plan bound type (source, target) = true) ↔
      Nonempty (SemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) source target) := by
  constructor
  · rintro ⟨graph, accepted⟩
    exact graph.check_sound plan bound type accepted
  · intro path
    obtain ⟨receipt, valid⟩ := (SemanticTrace.exists_valid_iff_semanticPath plan bound type source target).mpr path
    obtain ⟨tree⟩ := semanticTrace_valid_derivation plan bound type valid
    exact ⟨emit plan bound type tree, emit_checked plan bound type tree⟩

/-- Every explicit dependency is an earlier serialized node, excluding
missing references, self-reference, forward reference and directed cycles. -/
theorem Node.valid_references_lt {table : List Claim} {node : Node}
    (valid : Node.Valid plan bound type table node) :
    ∀ reference ∈ node.references, reference < table.length := by
  cases valid with
  | refl => simp only [Node.references, List.not_mem_nil, false_implies, implies_true]
  | conversion => simp only [Node.references, List.not_mem_nil, false_implies, implies_true]
  | atomic => simp only [Node.references, List.not_mem_nil, false_implies, implies_true]
  | trans first second =>
      intro reference member
      simp only [Node.references, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact (List.getElem?_eq_some_iff.mp first).1
      · exact (List.getElem?_eq_some_iff.mp second).1

theorem NodesValid.references_earlier {table final : List Claim} {nodes : List Node}
    (valid : NodesValid plan bound type table nodes final) :
    ∀ index node, nodes[index]? = some node →
      ∀ reference ∈ node.references, reference < table.length + index := by
  induction valid with
  | nil =>
      intro index node found
      simp only [List.getElem?_nil, reduceCtorEq] at found
  | @cons table final head rest first _ ih =>
      intro index node found reference member
      cases index with
      | zero =>
          have same : head = node := Option.some.inj found
          subst node
          simpa only [Nat.add_zero] using Node.valid_references_lt plan bound type first reference member
      | succ index =>
          have lower := ih index node found reference member
          simp only [List.length_append, List.length_singleton] at lower
          omega

theorem Graph.accepted_references_earlier {graph : Graph} {claim : Claim}
    (accepted : graph.check plan bound type claim = true) :
    ∀ (index : Nat) (node : Node), graph.nodes[index]? = some node →
      ∀ reference ∈ node.references, reference < index := by
  obtain ⟨table, valid, _⟩ := (graph.check_exact plan bound type claim).mp accepted
  simpa only [List.length_nil, Nat.zero_add] using
    NodesValid.references_earlier plan bound type valid

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeDAG
