import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RelationComposition
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MILNativeMaterializationExamples

/-! # Checking proof occurrences delivered by a two-read transform -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChain

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open InferenceChecker
open Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory
open MILCheckedChain MILCheckedNativePrograms
open Mettapedia.Machines.Specialization
open RelationComposition

structure Receipt where
  occurrence : String
  proof : RawProof
  sources : List String

abbrev Premise := Row Pattern Receipt

def tree (first second : Premise) : RawProof :=
  .node ⟨chainRule.id, [first.source, first.target, second.target]⟩
    [first.evidence.proof, second.evidence.proof]

def Valid (r : Premise) : Prop :=
  argumentValidAt 0 r.source = true ∧ argumentValidAt 0 r.target = true ∧
    checkRaw learned.target (relates r.source r.target) r.evidence.proof = true

private theorem instance_exact (x m z : Pattern) (hx : argumentValidAt 0 x = true)
    (hm : argumentValidAt 0 m = true) (hz : argumentValidAt 0 z = true) :
    instantiateRule? learned.target ⟨chainRule.id, [x, m, z]⟩ =
      some ([relates x m, relates m z], relates x z) := by
  have found : learned.target.1.lookupRule? chainRule.id = some chainRule := by decide
  simp only [instantiateRule?, found]
  simp [chainRule, argumentsValidAt, hx, hm, hz, RuleSchema.sideConditionsHold, relates,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?]

/-- Entry and exit are the requested endpoints. The selected left occurrence
supplies the intermediate term and the selected right proof must start there. -/
theorem every_answer_checks (tables : PathJoin.Tables Pattern Premise) (left right : List Premise)
    (source target : Pattern) (leftValid : ∀ row ∈ left, Valid row) (rightValid : ∀ row ∈ right, Valid row)
    {first second : Premise} (returned : (first, second) ∈ prepared tables left right source target) :
    checkRaw learned.target (relates source target) (tree first second) = true := by
  rw [prepared_eq_compose] at returned
  obtain ⟨hl, hr, rfl, middle, rfl⟩ := (mem_compose ..).mp returned
  obtain ⟨hx, hm, hleft⟩ := leftValid first hl
  obtain ⟨_, hz, hright⟩ := rightValid second hr
  rw [middle] at hright
  simp [tree, checkRaw, instance_exact _ _ _ hx hm hz, checkRawChildren, hleft, hright]

def erase (source target : Pattern) : RelationComposition.Proof Pattern Receipt → RawProof
  | .leaf receipt => receipt.proof
  | .via middle left right =>
    .node ⟨chainRule.id, [source, middle, target]⟩ [erase source middle left, erase middle target right]

private theorem checked_firing {Name : Type} {bank : Name → List Premise}
    (valid : ∀ name row, row ∈ bank name → Valid row) {expr : Expr Name} {row}
    (fired : Holds bank expr row) :
    argumentValidAt 0 row.source = true ∧ argumentValidAt 0 row.target = true ∧
      checkRaw learned.target (relates row.source row.target) (erase row.source row.target row.evidence) = true := by
  induction fired with
  | fact name r stored => exact valid name r stored
  | @fire a b l r _ _ middle lhs rhs =>
    obtain ⟨hx, hm, hl⟩ := lhs
    obtain ⟨_, hz, hr⟩ := rhs
    rw [middle] at hr
    exact ⟨hx, hz, by simp [link, erase, checkRaw, instance_exact _ _ _ hx hm hz, checkRawChildren, hl, hr]⟩

theorem indexed_program_checks {Name : Type} (bank : Name → List Premise)
    (valid : ∀ name row, row ∈ bank name → Valid row) (expr : Expr Name) (tables) {row}
    (delivered : row ∈ indexed bank tables expr) :
    checkRaw learned.target (relates row.source row.target) (erase row.source row.target row.evidence) = true := by
  rw [indexed_exact] at delivered
  exact (checked_firing valid ((mem_iff_fires ..).mp delivered)).2.2

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open scoped Classical in
theorem wave_publication_materializes {Name : Type} [DecidableEq Name]
    (declared : Finset (Expr Name)) (inputs : List (Name × Premise))
    (checked : ∀ entry ∈ inputs, Valid entry.2) (n : Nat) (expr : Expr Name) (row)
    (published : RuleSyntax.RelationComposition.Fact.holds expr row ∈
      RuleSyntax.RelationComposition.waves declared inputs n) :
    (MILNativeMaterialization.materialize? FormedQuotationCanary.quotation row.source row.target
      (erase row.source row.target row.evidence)).isSome = true := by
  rw [MILNativeMaterialization.materialize_isSome]
  have present := RuleSyntax.RelationComposition.waves_subset_closure declared inputs n published
  have entry := (RuleSyntax.RelationComposition.closure_iff_indexed declared inputs
    PathJoin.functional expr row).mp present
  apply indexed_program_checks _ _ _ _ entry.2
  intro name r member
  exact checked (name, r) ((RuleSyntax.RelationComposition.mem_provider_iff inputs).mp member)

def familyLeft : List Premise :=
  [⟨alice, bob, ⟨"l1", motherProof, ["report"]⟩⟩, ⟨alice, bob, ⟨"l2", motherProof, ["report"]⟩⟩]

def familyRight : List Premise := [⟨bob, carol, ⟨"r1", fatherProof, ["certain"]⟩⟩]

theorem family_native_terms :
    ((prepared PathJoin.functional familyLeft familyRight alice carol).map fun (l, r) =>
      (l.evidence.occurrence, r.evidence.occurrence,
        MILNativeMaterialization.materialize? FormedQuotationCanary.quotation alice carol (tree l r))) =
      [("l1", "r1", some MILNativeMaterialization.Examples.grandparentNative),
       ("l2", "r1", some MILNativeMaterialization.Examples.grandparentNative)] := by
  rw [prepared_eq_compose]
  change [("l1", "r1", MILNativeMaterialization.materialize? FormedQuotationCanary.quotation alice carol grandparentProof),
    ("l2", "r1", MILNativeMaterialization.materialize? FormedQuotationCanary.quotation alice carol grandparentProof)] = _
  rw [MILNativeMaterialization.Examples.grandparent_materialized]

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChain
