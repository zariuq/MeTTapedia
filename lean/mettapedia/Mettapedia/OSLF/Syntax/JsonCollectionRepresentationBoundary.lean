import Mettapedia.OSLF.Syntax.JsonAuthoredComparison
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion
import Mettapedia.GSLT.LanguageDef.CollectionConstructorEvidence

/-!
# The two JSON collection constructors need distinct representations

The authored array and object rows both have a single vector parameter and
the same result sort. The current bare-collection typing mode forgets which
row was used. At the empty vector it therefore represents two distinct JSON
values by one raw pattern. A constructor-tagged collection keeps them apart,
but is not admitted by the current bare-collection typing rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.JsonCollectionRepresentationBoundary

open Mettapedia.OSLF.Binding.JsonTermRung
open Mettapedia.OSLF.Binding.JsonAuthoredComparison
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CollectionConstructorEvidence

private def arrayRow : GrammarRule := authored.terms.get ⟨4, by decide⟩
private def objectRow : GrammarRule := authored.terms.get ⟨5, by decide⟩

theorem source_rows_distinct : arrayRow.label ≠ objectRow.label := by decide

theorem both_rows_use_bare_collections :
    UsesBareCollection arrayRow ∧ UsesBareCollection objectRow := by
  constructor
  · exact ⟨"values", .vec, .base "Value", rfl⟩
  · exact ⟨"fields", .vec, .base "Field", rfl⟩

/-- The current checker accepts the same empty vector as an array value. -/
theorem empty_vector_as_array :
    HasType authored FreeTypeContext.empty []
      (.collection .vec [] none) (.base "Value") := by
  change HasType authored FreeTypeContext.empty []
    (.collection .vec [] none) (.base arrayRow.category)
  apply HasType.collectionConstructor
    (rule := arrayRow) (parameterName := "values")
    (elementType := .base "Value")
  · simp [arrayRow, authored]
  · rfl
  · exact ElementsHaveType.nil [] (.base "Value")

/-- The very same raw pattern also has an object derivation. The element
types differ, but the empty vector contains no element that could expose it. -/
theorem empty_vector_as_object :
    HasType authored FreeTypeContext.empty []
      (.collection .vec [] none) (.base "Value") := by
  change HasType authored FreeTypeContext.empty []
    (.collection .vec [] none) (.base objectRow.category)
  apply HasType.collectionConstructor
    (rule := objectRow) (parameterName := "fields")
    (elementType := .base "Field")
  · simp [objectRow, authored]
  · rfl
  · exact ElementsHaveType.nil [] (.base "Field")

/-- In the source's free data model, empty arrays and objects are distinct. -/
theorem intrinsic_empty_array_ne_object :
    encodeValue (.arr .nil) ≠ encodeValue (.obj .nil) := by
  intro equal
  cases equal

/-- The labels distinguish the two collection forms as raw patterns. -/
theorem tagged_empty_array_ne_object :
    (Pattern.apply arrayRow.label [.collection .vec [] none]) ≠
      Pattern.apply objectRow.label [.collection .vec [] none] := by
  intro equal
  have labels : arrayRow.label = objectRow.label :=
    congrArg (fun p => match p with
      | Pattern.apply label _ => label
      | _ => "") equal
  exact source_rows_distinct labels

/-- The canonical bare-collection typing rule cannot type the constructor
tag that would keep the JSON array distinct from an object. -/
theorem tagged_empty_array_not_typed :
    ¬ HasType authored FreeTypeContext.empty []
      (.apply "JArr" [.collection .vec [] none]) (.base "Value") := by
  intro typed
  obtain ⟨rule, membership, label, notBare, _, _⟩ :=
    hasType_apply_inversion typed
  have same : rule = arrayRow := by
    have singleton :
        authored.terms.filter (fun candidate => candidate.label == "JArr") =
          [arrayRow] := by rfl
    have inFiltered :
        rule ∈ authored.terms.filter (fun candidate => candidate.label == "JArr") :=
      List.mem_filter.mpr ⟨membership, by simp [← label]⟩
    rw [singleton] at inFiltered
    simpa using inFiltered
  subst rule
  exact notBare both_rows_use_bare_collections.1

/-- The two distinct source constructors restricted to their empty arguments. -/
inductive EmptyCollectionForm where
  | array
  | object
  deriving DecidableEq

/-- Erasing the constructor label is precisely the current bare representation
at the empty collection. -/
def bareEmpty : EmptyCollectionForm → Pattern
  | .array | .object => .collection .vec [] none

/-- Retaining the authored labels gives a faithful representation of the same
two constructor forms. -/
def taggedEmpty : EmptyCollectionForm → Pattern
  | .array => .apply arrayRow.label [.collection .vec [] none]
  | .object => .apply objectRow.label [.collection .vec [] none]

theorem bareEmpty_not_injective : ¬ Function.Injective bareEmpty := by
  intro injective
  have formsEqual : EmptyCollectionForm.array = .object :=
    injective rfl
  cases formsEqual

theorem no_bareEmpty_decoder :
    ¬ ∃ decode : Pattern → EmptyCollectionForm,
      Function.LeftInverse decode bareEmpty := by
  rintro ⟨decode, inverse⟩
  exact bareEmpty_not_injective inverse.injective

theorem taggedEmpty_injective : Function.Injective taggedEmpty := by
  intro first second equal
  cases first <;> cases second
  · rfl
  · exact False.elim (tagged_empty_array_ne_object equal)
  · exact False.elim (tagged_empty_array_ne_object equal.symm)
  · rfl

/-- Both source rows give a certificate for the same raw empty-vector pattern
at the same result sort. -/
abbrev EmptyRowEvidence :=
  RowEvidence authored FreeTypeContext.empty [] .vec [] none "Value"

def arrayEvidence : EmptyRowEvidence where
  rule := arrayRow
  parameterName := "values"
  elementType := .base "Value"
  member := by simp [arrayRow, authored]
  result := rfl
  parameterShape := rfl
  elementsTyped := ElementsHaveType.nil [] (.base "Value")

def objectEvidence : EmptyRowEvidence where
  rule := objectRow
  parameterName := "fields"
  elementType := .base "Field"
  member := by simp [objectRow, authored]
  result := rfl
  parameterShape := rfl
  elementsTyped := ElementsHaveType.nil [] (.base "Field")

theorem arrayEvidence_ne_objectEvidence :
    arrayEvidence ≠ objectEvidence :=
  RowEvidence.ne_of_label_ne source_rows_distinct

theorem arrayEvidence_same_erased_typing :
    arrayEvidence.toHasType = objectEvidence.toHasType :=
  Subsingleton.elim _ _

/-- Erasing the selected row to the current Prop-valued typing judgment is
not injective, even for the two closed empty JSON forms. -/
theorem row_erasure_not_injective :
    ¬ Function.Injective (fun evidence : EmptyRowEvidence =>
      evidence.toHasType) := by
  intro injective
  exact arrayEvidence_ne_objectEvidence
    (injective arrayEvidence_same_erased_typing)

end Mettapedia.OSLF.Binding.JsonCollectionRepresentationBoundary
