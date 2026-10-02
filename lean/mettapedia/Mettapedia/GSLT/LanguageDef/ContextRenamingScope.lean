import Mettapedia.GSLT.LanguageDef.ContextRenamingTyping
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

/-!
# Quotation-aware ambient context action

The existing ambient-index renaming preserves quotation sealing under an
actual finite scope bound. A sealed quotation body is unchanged by the
ambient action. This does not substitute executable code through quotation.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
namespace ContextSubstitution

/-- A term using only its local prefix is independent of the ambient map. -/
theorem renameAmbientBVarsAt_eq_self_of_isWellScopedAt
    (rename : Nat → Nat) {depth : Nat} {pattern : Pattern}
    (safe : pattern.isWellScopedAt depth = true) :
    renameAmbientBVarsAt rename depth pattern = pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at safe
      simp [renameAmbientBVarsAt, safe]
  | hfvar name => simp [renameAmbientBVarsAt]
  | happly constructor arguments ih =>
      simp only [Pattern.isWellScopedAt] at safe
      rw [isWellScopedListAt_eq_true_iff] at safe
      simp only [renameAmbientBVarsAt, Pattern.apply.injEq, true_and]
      conv_rhs => rw [← List.map_id arguments]
      apply List.map_congr_left
      intro argument member
      exact ih argument member (safe argument member)
  | hlambda binder body ih =>
      simp only [Pattern.isWellScopedAt] at safe
      simp [renameAmbientBVarsAt, ih safe]
  | hmultiLambda arity binders body ih =>
      simp only [Pattern.isWellScopedAt] at safe
      simp [renameAmbientBVarsAt, ih safe]
  | hsubst body replacement bodyIH replacementIH =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at safe
      simp [renameAmbientBVarsAt, bodyIH safe.1, replacementIH safe.2]
  | hcollection collectionType elements rest ih =>
      simp only [Pattern.isWellScopedAt] at safe
      rw [isWellScopedListAt_eq_true_iff] at safe
      simp only [renameAmbientBVarsAt, Pattern.collection.injEq, true_and, and_true]
      conv_rhs => rw [← List.map_id elements]
      apply List.map_congr_left
      intro element member
      exact ih element member (safe element member)

/-- Quote-aware binder scope survives insertion of target-only ambient
binders.  Internal quotation bodies remain sealed rather than merely being
weakened to the larger ambient depth. -/
theorem binderSafeAt_renameAmbientBVarsAt
    (rename : Nat → Nat) {source target : Nat}
    (bounded : ∀ index, index < source → rename index < target)
    (quoteConstructor : String) (depth : Nat) (pattern : Pattern)
    (safe : binderSafeAt quoteConstructor
      (depth + source) pattern = true) :
    binderSafeAt quoteConstructor (depth + target)
      (renameAmbientBVarsAt rename depth pattern) = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [binderSafeAt, renameAmbientBVarsAt,
        decide_eq_true_eq] at safe ⊢
      split <;> simp only [binderSafeAt, decide_eq_true_eq]
      · omega
      · have bound := bounded (index - depth) (by omega)
        omega
  | hfvar name => simp [renameAmbientBVarsAt, binderSafeAt]
  | happly constructor arguments inductionHypothesis =>
      cases arguments with
      | nil => simp [renameAmbientBVarsAt, binderSafeAt, binderSafeListAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                have argumentSafe :
                    binderSafeAt quoteConstructor 0 argument = true := by
                  simpa [binderSafeAt] using safe
                have fixed :=
                  renameAmbientBVarsAt_eq_self_of_isWellScopedAt rename
                    (isWellScopedAt_mono
                      (isWellScopedAt_of_binderSafeAt quoteConstructor argumentSafe)
                      (Nat.zero_le depth))
                simpa [renameAmbientBVarsAt, binderSafeAt, fixed] using
                  argumentSafe
              · have argumentSafe : binderSafeAt quoteConstructor
                    (depth + source) argument = true := by
                  simpa [binderSafeAt, binderSafeListAt, quoted] using safe
                have mappedSafe := inductionHypothesis argument (by simp)
                  depth argumentSafe
                simpa [renameAmbientBVarsAt, binderSafeAt, binderSafeListAt,
                  quoted] using
                  mappedSafe
          | cons second remainder =>
              have argumentsSafe : ∀ member ∈
                  argument :: second :: remainder,
                  binderSafeAt quoteConstructor
                    (depth + source) member = true := by
                rw [← binderSafeListAt_eq_true_iff]
                simpa [binderSafeAt] using safe
              simp only [renameAmbientBVarsAt]
              change binderSafeListAt quoteConstructor
                (depth + target)
                ((argument :: second :: remainder).map
                  (renameAmbientBVarsAt rename depth)) = true
              rw [binderSafeListAt_eq_true_iff]
              intro mapped membership
              rw [List.mem_map] at membership
              obtain ⟨member, memberIn, rfl⟩ := membership
              exact inductionHypothesis member memberIn depth
                (argumentsSafe member memberIn)
  | hlambda binder body inductionHypothesis =>
      have bodySafe : binderSafeAt quoteConstructor
          ((depth + 1) + source) body = true := by
        simpa [binderSafeAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using safe
      simpa [renameAmbientBVarsAt, binderSafeAt, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using inductionHypothesis (depth + 1) bodySafe
  | hmultiLambda arity binders body inductionHypothesis =>
      have bodySafe : binderSafeAt quoteConstructor
          ((depth + arity) + source) body = true := by
        simpa [binderSafeAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using safe
      simpa [renameAmbientBVarsAt, binderSafeAt, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using inductionHypothesis (depth + arity) bodySafe
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [renameAmbientBVarsAt, binderSafeAt,
        Bool.and_eq_true] at safe ⊢
      have bodySafe : binderSafeAt quoteConstructor
          ((depth + 1) + source) body = true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using safe.1
      exact ⟨by
          simpa [renameAmbientBVarsAt, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using bodyHypothesis (depth + 1) bodySafe,
        replacementHypothesis depth safe.2⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsSafe : ∀ element ∈ elements,
          binderSafeAt quoteConstructor
            (depth + source) element = true := by
        rw [← binderSafeListAt_eq_true_iff]
        simpa [binderSafeAt] using safe
      simp only [renameAmbientBVarsAt, binderSafeAt]
      rw [binderSafeListAt_eq_true_iff]
      intro mapped membership
      rw [List.mem_map] at membership
      obtain ⟨element, elementIn, rfl⟩ := membership
      exact inductionHypothesis element elementIn depth
        (elementsSafe element elementIn)


private theorem canonicalBinderMetadataList_renameAmbientBVarsAt
    (rename : Nat → Nat)
    (depth : Nat) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      (renameAmbientBVarsAt rename depth pattern).hasCanonicalBinderMetadata =
        pattern.hasCanonicalBinderMetadata) :
    Pattern.hasCanonicalBinderMetadataList
        (patterns.map (renameAmbientBVarsAt rename depth)) =
      Pattern.hasCanonicalBinderMetadataList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, Pattern.hasCanonicalBinderMetadataList]
      rw [pointwise pattern (by simp), inductionHypothesis]
      intro member membership
      exact pointwise member (by simp [membership])

/-- Ambient binder insertion changes indices only; locally nameless display
metadata and its canonicality are invariant. -/
@[simp]
theorem hasCanonicalBinderMetadata_renameAmbientBVarsAt
    (rename : Nat → Nat)
    (depth : Nat) (pattern : Pattern) :
    (renameAmbientBVarsAt rename depth pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [renameAmbientBVarsAt]
      split <;> rfl
  | hfvar name => simp [renameAmbientBVarsAt, Pattern.hasCanonicalBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameAmbientBVarsAt, Pattern.hasCanonicalBinderMetadata]
      exact canonicalBinderMetadataList_renameAmbientBVarsAt rename depth
        arguments (fun member membership =>
          inductionHypothesis member membership depth)
  | hlambda binder body inductionHypothesis =>
      simp only [renameAmbientBVarsAt, Pattern.hasCanonicalBinderMetadata]
      rw [inductionHypothesis (depth + 1)]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [renameAmbientBVarsAt, Pattern.hasCanonicalBinderMetadata]
      rw [inductionHypothesis (depth + arity)]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [renameAmbientBVarsAt, Pattern.hasCanonicalBinderMetadata,
        bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameAmbientBVarsAt, Pattern.hasCanonicalBinderMetadata]
      exact canonicalBinderMetadataList_renameAmbientBVarsAt rename depth
        elements (fun member membership =>
          inductionHypothesis member membership depth)

private theorem objectPatternList_renameAmbientBVarsAt
    (rename : Nat → Nat)
    (depth : Nat) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      WellSorted.isObjectPattern (renameAmbientBVarsAt rename depth pattern) =
        WellSorted.isObjectPattern pattern) :
    WellSorted.isObjectPatternList
        (patterns.map (renameAmbientBVarsAt rename depth)) =
      WellSorted.isObjectPatternList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, WellSorted.isObjectPatternList]
      rw [pointwise pattern (by simp), inductionHypothesis]
      intro member membership
      exact pointwise member (by simp [membership])

/-- Ambient binder insertion preserves the object/schema boundary. -/
@[simp]
theorem isObjectPattern_renameAmbientBVarsAt
    (rename : Nat → Nat)
    (depth : Nat) (pattern : Pattern) :
    WellSorted.isObjectPattern (renameAmbientBVarsAt rename depth pattern) =
      WellSorted.isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [renameAmbientBVarsAt]
      split <;> rfl
  | hfvar name => simp [renameAmbientBVarsAt, WellSorted.isObjectPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameAmbientBVarsAt, WellSorted.isObjectPattern]
      exact objectPatternList_renameAmbientBVarsAt rename depth arguments
        (fun member membership => inductionHypothesis member membership depth)
  | hlambda binder body inductionHypothesis =>
      simpa [renameAmbientBVarsAt, WellSorted.isObjectPattern] using
        inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [renameAmbientBVarsAt, WellSorted.isObjectPattern] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [renameAmbientBVarsAt, WellSorted.isObjectPattern]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameAmbientBVarsAt, WellSorted.isObjectPattern]
      rw [objectPatternList_renameAmbientBVarsAt rename depth elements
        (fun member membership => inductionHypothesis member membership depth)]


end ContextSubstitution

namespace WellSorted
/-- Preserving each actual typed lookup also preserves the finite scope bound. -/
theorem PreservesBoundTypes.index_lt
    {source target : List TypeExpr} {rename : Nat → Nat}
    (preserves : PreservesBoundTypes source target rename)
    {index : Nat} (inRange : index < source.length) : rename index < target.length := by
  have lookup : source[index]? = some source[index] :=
    List.getElem?_eq_some_iff.mpr ⟨inRange, rfl⟩
  exact (List.getElem?_eq_some_iff.mp (preserves lookup)).1
end WellSorted

namespace ReflectiveWellSorted
/-- Ambient context action on the actual reflective carrier. Metadata,
object syntax, ordinary scope and each declared quotation seal are proved. -/
theorem OpenPatternWellSorted.renameAmbientBVarsAt
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {sourceBound targetBound inner : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (sorted : OpenPatternWellSorted profile language free (inner ++ sourceBound) type pattern)
    (rename : Nat → Nat) (preserves : WellSorted.PreservesBoundTypes sourceBound targetBound rename) :
    OpenPatternWellSorted profile language free (inner ++ targetBound) type
      (ContextSubstitution.renameAmbientBVarsAt rename inner.length pattern) := by
  have typed := sorted.1.1.renameAmbientBVarsAt rename preserves
  refine ⟨⟨typed, ?_, ?_, typed.isWellScopedAt⟩, ?_⟩
  · simpa only [ContextSubstitution.hasCanonicalBinderMetadata_renameAmbientBVarsAt]
      using sorted.1.2.1
  · simpa only [ContextSubstitution.isObjectPattern_renameAmbientBVarsAt]
      using sorted.1.2.2.1
  · intro presentation membership
    have safe := ContextSubstitution.binderSafeAt_renameAmbientBVarsAt
      rename (fun _ member => preserves.index_lt member)
      presentation.quoteConstructor inner.length pattern
      (by simpa only [List.length_append] using sorted.2 presentation membership)
    simpa only [List.length_append] using safe

end ReflectiveWellSorted
end Mettapedia.GSLT.LanguageDef
