import Mettapedia.GSLT.LanguageDef.InferenceProofMaterialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RelationComposition

/-! # Checked proofs from relation composition

A relation expression denotes a binary judgment. A composition gives the
checker its actual rule instance and ordered premise proofs. The instance
may arrange or supplement its arguments as required by the declaration.
Its applicability is checked against the calculus language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceRelationComposition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Machines.Specialization
open InferenceChecker RelationComposition

inductive PremiseOrder where
  | leftFirst
  | rightFirst

def PremiseOrder.arrange {α : Type*} (order : PremiseOrder) (left right : α) : List α :=
  match order with
  | .leftFirst => [left, right]
  | .rightFirst => [right, left]

/-- The judgment of each relation and the rule instance used to compose two
relations at a given intermediate value. -/
structure CompositionSchema (Name Key : Type) where
  judgment : Expr Name → Key → Key → Pattern
  instanceAt : Expr Name → Expr Name → Key → Key → Key → RuleInstance
  premiseOrder : Expr Name → Expr Name → Key → Key → Key → PremiseOrder := fun _ _ _ _ _ => .leftFirst

namespace CompositionSchema

variable {Name Key Evidence : Type}
variable (schema : CompositionSchema Name Key) (definition : ValidatedCalculusLanguageDef)

def Applies (left right : Expr Name) (source middle target : Key) : Prop :=
  RuleApplication definition (schema.instanceAt left right source middle target)
    ((schema.premiseOrder left right source middle target).arrange
      (schema.judgment left source middle) (schema.judgment right middle target))
    (schema.judgment (.chain left right) source target)

def node (left right : Expr Name) (source middle target : Key) (first second : RawProof) : RawProof :=
  .node (schema.instanceAt left right source middle target)
    ((schema.premiseOrder left right source middle target).arrange first second)

theorem check_node {left right : Expr Name} {source middle target : Key}
    (applies : schema.Applies definition left right source middle target) (first second : RawProof) :
    checkRaw definition (schema.judgment (.chain left right) source target)
      (schema.node left right source middle target first second) =
    (checkRaw definition (schema.judgment left source middle) first &&
      checkRaw definition (schema.judgment right middle target) second) := by
  have instantiated := instantiateRule?_eq_some_iff_application.mpr applies
  cases order : schema.premiseOrder left right source middle target with
  | leftFirst => simp [node, checkRaw, instantiated, order, PremiseOrder.arrange, checkRawChildren]
  | rightFirst => simp [node, checkRaw, instantiated, order, PremiseOrder.arrange, checkRawChildren, Bool.and_comm]

/-- A changed intermediate cannot reuse a child proof if it changes that
child's judgment, even if the new rule instance is itself applicable. -/
theorem changed_middle_rejected {left right : Expr Name} {source middle changed target : Key}
    (applies : schema.Applies definition left right source changed target) {first : RawProof} (second : RawProof)
    (firstChecked : checkRaw definition (schema.judgment left source middle) first = true)
    (different : schema.judgment left source middle ≠ schema.judgment left source changed) :
    checkRaw definition (schema.judgment (.chain left right) source target)
      (schema.node left right source changed target first second) = false := by
  have rejected : checkRaw definition (schema.judgment left source changed) first = false := by
    cases result : checkRaw definition (schema.judgment left source changed) first with
    | false => rfl
    | true => exact False.elim (different (checkRaw_goal_unique firstChecked result))
  simp only [schema.check_node definition applies, rejected, Bool.false_and]

theorem prepared_checks [DecidableEq Key] (proofOf : Evidence → RawProof)
    (left right : Expr Name) (tables : PathJoin.Tables Key (Row Key Evidence))
    (firsts seconds : List (Row Key Evidence)) (source target : Key)
    (firstsChecked : ∀ row ∈ firsts,
      checkRaw definition (schema.judgment left row.source row.target) (proofOf row.evidence) = true)
    (secondsChecked : ∀ row ∈ seconds,
      checkRaw definition (schema.judgment right row.source row.target) (proofOf row.evidence) = true)
    {first second : Row Key Evidence}
    (found : (first, second) ∈ prepared tables firsts seconds source target)
    (applies : schema.Applies definition left right source first.target target) :
    checkRaw definition (schema.judgment (.chain left right) source target)
      (schema.node left right source first.target target (proofOf first.evidence)
        (proofOf second.evidence)) = true := by
  rw [prepared_eq_compose] at found
  obtain ⟨firstIn, secondIn, rfl, aligned, rfl⟩ := (mem_compose ..).mp found
  have secondChecked := secondsChecked second secondIn
  rw [aligned] at secondChecked
  rw [schema.check_node definition applies, firstsChecked first firstIn, secondChecked]
  rfl

/-- Read a Transform proof back at its declared relation expression. -/
def rawProof? (proofOf : Evidence → RawProof) :
    Expr Name → Key → Key → Proof Key Evidence → Option RawProof
  | .base _, _, _, .leaf receipt => some (proofOf receipt)
  | .chain left right, source, target, .via middle first second => do
      let firstProof ← rawProof? proofOf left source middle first
      let secondProof ← rawProof? proofOf right middle target second
      pure (schema.node left right source middle target firstProof secondProof)
  | _, _, _, _ => none

/-- Each supplied premise is checked at its own judgment, and the schema
instantiates on each joined pair used by this expression. This includes the
side conditions of the installed rule instance. -/
def ValidFor (bank : Name → Relation Key Evidence) (proofOf : Evidence → RawProof) :
    Expr Name → Prop
  | .base name => ∀ row ∈ bank name,
      checkRaw definition (schema.judgment (.base name) row.source row.target) (proofOf row.evidence) = true
  | .chain left right =>
      ValidFor bank proofOf left ∧ ValidFor bank proofOf right ∧
        ∀ (first second : Row Key (Proof Key Evidence)), Holds bank left first → Holds bank right second →
          second.source = first.target → schema.Applies definition left right first.source first.target second.target

theorem rawProof?_checks_of_fires (bank : Name → Relation Key Evidence) (proofOf : Evidence → RawProof)
    {expr : Expr Name} {row : Row Key (Proof Key Evidence)} (fired : Holds bank expr row)
    (valid : schema.ValidFor definition bank proofOf expr) :
    ∃ proof, schema.rawProof? proofOf expr row.source row.target row.evidence = some proof ∧
      checkRaw definition (schema.judgment expr row.source row.target) proof = true := by
  induction fired with
  | fact name receipt stored =>
    exact ⟨proofOf receipt.evidence, rfl, valid receipt stored⟩
  | @fire left right first second leftFires rightFires middle leftIH rightIH =>
    obtain ⟨firstProof, firstRaw, firstChecked⟩ := leftIH valid.1
    obtain ⟨secondProof, secondRaw, secondChecked⟩ := rightIH valid.2.1
    have applies := valid.2.2 first second leftFires rightFires middle
    rw [middle] at secondRaw secondChecked
    refine ⟨schema.node left right first.source first.target second.target firstProof secondProof, ?_, ?_⟩
    · simp [rawProof?, link, firstRaw, secondRaw]
    · rw [show (link first second).source = first.source from rfl,
        show (link first second).target = second.target from rfl,
        schema.check_node definition applies, firstChecked, secondChecked]
      rfl

/-- Run the same checker used by authored proof trees and materialize its
derivation at the judgment of the observed expression. -/
def materialize? (proofOf : Evidence → RawProof) (expr : Expr Name) (row : Row Key (Proof Key Evidence)) :
    Option (Derivation definition (schema.judgment expr row.source row.target)) := do
  let raw ← schema.rawProof? proofOf expr row.source row.target row.evidence
  return (← materializeProof? definition (schema.judgment expr row.source row.target) raw).val

/-- A returned derivation has exactly the rule instances and premise order
read from the Transform witness. -/
theorem rawProof?_eq_erase_of_materialize (proofOf : Evidence → RawProof) (expr : Expr Name)
    (row : Row Key (Proof Key Evidence)) {checked : Derivation definition (schema.judgment expr row.source row.target)}
    (accepted : schema.materialize? definition proofOf expr row = some checked) :
    schema.rawProof? proofOf expr row.source row.target row.evidence = some checked.erase := by
  cases raw : schema.rawProof? proofOf expr row.source row.target row.evidence with
  | none => simp [materialize?, raw] at accepted
  | some proof =>
    cases materialized : materializeProof? definition (schema.judgment expr row.source row.target) proof with
    | none => simp [materialize?, raw, materialized] at accepted
    | some retained =>
      have same : retained.val = checked := by simpa [materialize?, raw, materialized] using accepted
      exact congrArg some (retained.property.symm.trans (congrArg Derivation.erase same))

theorem materializes_of_fires (bank : Name → Relation Key Evidence) (proofOf : Evidence → RawProof)
    {expr : Expr Name} {row : Row Key (Proof Key Evidence)} (fired : Holds bank expr row)
    (valid : schema.ValidFor definition bank proofOf expr) :
    ∃ checked, schema.materialize? definition proofOf expr row = some checked ∧
      schema.rawProof? proofOf expr row.source row.target row.evidence = some checked.erase := by
  obtain ⟨raw, erased, accepted⟩ := schema.rawProof?_checks_of_fires definition bank proofOf fired valid
  have reconstructed :
      schema.materialize? definition proofOf expr row = some (reconstruct raw accepted).val := by
    simp [materialize?, erased, materializeProof?_eq_some accepted]
  exact ⟨_, reconstructed, schema.rawProof?_eq_erase_of_materialize definition proofOf expr row reconstructed⟩

theorem indexed_materializes [DecidableEq Key] (bank : Name → Relation Key Evidence)
    (proofOf : Evidence → RawProof) (tables : PathJoin.Tables Key (Row Key (Proof Key Evidence)))
    {expr : Expr Name} {row : Row Key (Proof Key Evidence)} (delivered : row ∈ indexed bank tables expr)
    (valid : schema.ValidFor definition bank proofOf expr) :
    ∃ checked, schema.materialize? definition proofOf expr row = some checked ∧
      schema.rawProof? proofOf expr row.source row.target row.evidence = some checked.erase := by
  rw [indexed_exact, mem_iff_fires] at delivered
  exact schema.materializes_of_fires definition bank proofOf delivered valid

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.RelationComposition (Fact provider waves waves_subset_closure closure_iff_indexed)

theorem wave_publication_materializes [DecidableEq Name] [DecidableEq Key] [DecidableEq Evidence]
    (declared : Finset (Expr Name)) (inputs : List (Name × Row Key Evidence))
    (proofOf : Evidence → RawProof) (n : Nat) {expr : Expr Name} {row : Row Key (Proof Key Evidence)}
    (published : Fact.holds expr row ∈ waves declared inputs n)
    (valid : schema.ValidFor definition (provider inputs) proofOf expr) :
    ∃ checked, schema.materialize? definition proofOf expr row = some checked ∧
      schema.rawProof? proofOf expr row.source row.target row.evidence = some checked.erase := by
  have stored := waves_subset_closure declared inputs n published
  have delivered := (closure_iff_indexed declared inputs PathJoin.functional expr row).mp stored
  exact schema.indexed_materializes definition (provider inputs) proofOf PathJoin.functional delivered.2 valid

end CompositionSchema
end Mettapedia.GSLT.LanguageDef.InferenceRelationComposition
