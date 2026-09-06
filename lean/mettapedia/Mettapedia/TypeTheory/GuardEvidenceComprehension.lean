import Mettapedia.TypeTheory.SetFamilyComprehensionMap
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

/-!
# Dependent evidence and predicate-guard support

An evidence family has a total space retaining a selected witness. Its
inhabited-support predicate records only which indices have a witness.
Projection to that predicate's subtype is always surjective, and is injective
exactly when each evidence fibre is subsingleton. Thus proposition-valued
refinement can be retained by a predicate guard, but arbitrary receipt data
cannot be reconstructed from guard success.

The projection commutes with reindexing. A separate engine theorem connects
support to the existing fully bound echo-query guard semantics. It requires
an independently correct support recognizer and the existing exact row
contract; arbitrary relation queries can instead introduce new bindings.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GuardEvidenceComprehension

universe uContext uEvidence uSource

variable {Context : Type uContext} {Evidence : Context → Type uEvidence}

/-- The predicate support forgets the selected evidence, not the index. -/
abbrev Support (Evidence : Context → Type uEvidence) :=
  {context : Context // Nonempty (Evidence context)}

/-- Retain the index and the fact that its selected evidence exists. -/
def supportProjection (point : Sigma Evidence) : Support Evidence :=
  ⟨point.1, ⟨point.2⟩⟩

/-- Support has exactly the indices reached by actual evidence. This does
not select a canonical witness or supply an executable reconstruction. -/
theorem supportProjection_surjective (Evidence : Context → Type uEvidence) :
    Function.Surjective (supportProjection (Evidence := Evidence)) := by
  rintro ⟨context, ⟨evidence⟩⟩
  exact ⟨⟨context, evidence⟩, rfl⟩

/-- Predicate support preserves selected evidence exactly when the evidence
at each fixed index has at most one inhabitant. -/
theorem supportProjection_injective_iff (Evidence : Context → Type uEvidence) :
    Function.Injective (supportProjection (Evidence := Evidence)) ↔
      ∀ context, Subsingleton (Evidence context) := by
  constructor
  · intro injective context
    refine ⟨fun first second => ?_⟩
    have sameSupport : supportProjection (⟨context, first⟩ : Sigma Evidence) =
        supportProjection ⟨context, second⟩ := rfl
    exact eq_of_heq (Sigma.mk.inj_iff.mp (injective sameSupport)).2
  · intro singletons first second sameSupport
    rcases first with ⟨firstContext, firstEvidence⟩
    rcases second with ⟨secondContext, secondEvidence⟩
    have sameContext : firstContext = secondContext := congrArg Subtype.val sameSupport
    cases sameContext
    exact Sigma.ext rfl (heq_of_eq ((singletons firstContext).elim _ _))

theorem supportProjection_bijective_iff (Evidence : Context → Type uEvidence) :
    Function.Bijective (supportProjection (Evidence := Evidence)) ↔
      ∀ context, Subsingleton (Evidence context) := by
  constructor
  · intro bijective
    exact (supportProjection_injective_iff Evidence).1 bijective.1
  · intro singletons
    exact ⟨(supportProjection_injective_iff Evidence).2 singletons,
      supportProjection_surjective Evidence⟩

/-! ## The same boundary for set-family comprehension -/

/-- Lift support proofs to the universe of the corresponding evidence fibre. -/
def supportFibreMap (Evidence : Context → Type uEvidence) (context : Context) :
    Evidence context → ULift.{uEvidence} (PLift (Nonempty (Evidence context))) :=
  fun evidence => ⟨⟨⟨evidence⟩⟩⟩

/-- The existing set-family comprehension criterion specializes to exactly
the evidence/support boundary, with proposition-valued support lifted to Type. -/
theorem supportTotalMap_bijective_iff {Context : Type uContext}
    (Evidence : Context → Type uContext) :
    Function.Bijective
      (SetFamilyComprehensionMap.totalMap (supportFibreMap Evidence)) ↔
      ∀ context, Subsingleton (Evidence context) := by
  rw [SetFamilyComprehensionMap.totalMap_bijective_iff]
  constructor
  · intro bijective context
    refine ⟨fun first second => ?_⟩
    exact (bijective context).1 (Subsingleton.elim _ _)
  · intro singletons context
    refine ⟨fun _ _ _ => (singletons context).elim _ _, ?_⟩
    rintro ⟨⟨⟨evidence⟩⟩⟩
    exact ⟨evidence, rfl⟩

/-! ## Reindexing preserves the projection square -/

def evidenceReindexMap {Source : Type uSource} (substitution : Source → Context) :
    (Sigma fun source => Evidence (substitution source)) → Sigma Evidence
  | ⟨source, evidence⟩ => ⟨substitution source, evidence⟩

def supportReindexMap {Source : Type uSource} (substitution : Source → Context) :
    Support (fun source => Evidence (substitution source)) → Support Evidence
  | ⟨source, inhabited⟩ => ⟨substitution source, inhabited⟩

theorem supportProjection_reindex {Source : Type uSource}
    (substitution : Source → Context)
    (point : Sigma fun source => Evidence (substitution source)) :
    supportProjection (evidenceReindexMap substitution point) =
      supportReindexMap substitution (supportProjection point) := rfl

theorem supportProjection_injective_reindex {Source : Type uSource}
    (substitution : Source → Context)
    (injective : Function.Injective (supportProjection (Evidence := Evidence))) :
    Function.Injective
      (supportProjection (Evidence := fun source => Evidence (substitution source))) := by
  apply (supportProjection_injective_iff _).2
  intro source
  exact (supportProjection_injective_iff Evidence).1 injective (substitution source)

/-- A surjective context substitution also reflects evidence retention.
Without coverage, reindexing may simply omit a non-subsingleton fibre. -/
theorem supportProjection_injective_reindex_iff {Source : Type uSource}
    (substitution : Source → Context) (covers : Function.Surjective substitution) :
    Function.Injective
        (supportProjection (Evidence := fun source => Evidence (substitution source))) ↔
      Function.Injective (supportProjection (Evidence := Evidence)) := by
  constructor
  · intro injective
    apply (supportProjection_injective_iff Evidence).2
    intro context
    obtain ⟨source, rfl⟩ := covers context
    exact (supportProjection_injective_iff _).1 injective source
  · exact supportProjection_injective_reindex substitution

/-! ## Genuine proposition-valued refinement -/

/-- A proposition's proof-irrelevant evidence total space is precisely its
refinement subtype. No arbitrary data witness is reconstructed here. -/
def predicateEvidenceEquiv (predicate : Context → Prop) :
    (Sigma fun context => PLift (predicate context)) ≃ {context // predicate context} where
  toFun point := ⟨point.1, point.2.down⟩
  invFun point := ⟨point.1, ⟨point.2⟩⟩
  left_inv point := by cases point; rfl
  right_inv point := by cases point; rfl

theorem predicateEvidence_projection_bijective (predicate : Context → Prop) :
    Function.Bijective
      (supportProjection (Evidence := fun context => PLift (predicate context))) := by
  apply (supportProjection_bijective_iff _).2
  intro context
  infer_instance

/-! ## Connection to the actual pure relation guard -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

/-- A fully bound, builtin-free echo query recognizes precisely the inhabited
support of an independently specified evidence fibre. Its returned bindings
do not contain the selected witness. -/
theorem pureGuard_mem_iff_support
    {relEnv : RelationEnv} {language : LanguageDef}
    {bindings result : Bindings} {relation : String}
    {names : List String} {values : List Pattern} {condition : Bool}
    {Evidence : Type uEvidence}
    (aligned : List.Forall₂
      (fun name value => bindings.lookup name = some value) names values)
    (noBuiltin : builtinRelationTuples language relation values = [])
    (echo : relEnv.tuples relation values = if condition then [values] else [])
    (recognizes : condition = true ↔ Nonempty Evidence) :
    result ∈ relationQueryStep relEnv language bindings relation
        (names.map Pattern.fvar) ↔
      result = bindings ∧ Nonempty Evidence := by
  rw [relationQueryStep_boundVariables_echo_eq aligned noBuiltin echo]
  cases condition <;> simp_all

/-! ## A genuinely varying two-receipt boundary -/

namespace Examples

inductive Receipt where
  | cached
  | recomputed
deriving DecidableEq

def ReceiptFamily : Bool → Type
  | false => PUnit
  | true => Receipt

def cachedPoint : Sigma ReceiptFamily := ⟨true, .cached⟩
def recomputedPoint : Sigma ReceiptFamily := ⟨true, .recomputed⟩

theorem every_receipt_fibre_inhabited (index : Bool) : Nonempty (ReceiptFamily index) := by
  cases index
  · exact ⟨PUnit.unit⟩
  · exact ⟨.cached⟩

theorem distinct_receipts_same_support :
    cachedPoint ≠ recomputedPoint ∧
      supportProjection cachedPoint = supportProjection recomputedPoint := by
  refine ⟨?_, rfl⟩
  intro equal
  have impossible : Receipt.cached = .recomputed :=
    eq_of_heq (Sigma.mk.inj_iff.mp equal).2
  cases impossible

theorem receipt_projection_not_injective :
    ¬ Function.Injective (supportProjection (Evidence := ReceiptFamily)) := by
  intro injective
  exact distinct_receipts_same_support.1 (injective distinct_receipts_same_support.2)

/-- Guard success cannot reconstruct which of two receipts was supplied. -/
theorem no_receipt_roundtrip :
    ¬ ∃ reconstruct : Support ReceiptFamily → Sigma ReceiptFamily,
      Function.LeftInverse reconstruct supportProjection := by
  rintro ⟨reconstruct, inverse⟩
  exact receipt_projection_not_injective inverse.injective

/-- Restricting to the singleton branch restores exact evidence retention;
the restriction is not surjective onto the original index context. -/
theorem singleton_branch_projection_bijective :
    Function.Bijective
      (supportProjection (Evidence := fun _ : PUnit => ReceiptFamily false)) := by
  apply (supportProjection_bijective_iff _).2
  intro context
  exact inferInstanceAs (Subsingleton PUnit)

end Examples

#print axioms supportProjection_surjective
#print axioms supportProjection_injective_iff
#print axioms supportProjection_bijective_iff
#print axioms supportTotalMap_bijective_iff
#print axioms supportProjection_reindex
#print axioms supportProjection_injective_reindex_iff
#print axioms predicateEvidenceEquiv
#print axioms predicateEvidence_projection_bijective
#print axioms pureGuard_mem_iff_support
#print axioms Examples.distinct_receipts_same_support
#print axioms Examples.no_receipt_roundtrip
#print axioms Examples.singleton_branch_projection_bijective

end Mettapedia.TypeTheory.GuardEvidenceComprehension
