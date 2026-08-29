import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Constructor-only language extensions

Adding generated constructors is a common language transformation.  This
module isolates that transformation from any particular generator and proves
its structural validation law once.  The hypotheses expose exactly the
nontrivial obligations: the base is valid and has no equations or rewrites,
the new constructor namespace is internally duplicate-free and disjoint from
the old one, and every new row validates against the unchanged carrier
signature.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace ConstructorTermExtension

/-- The language-extension delta that adds only constructor declarations. -/
def ofList (terms : List GrammarRule) : CalculusLanguageExtension :=
  { newTerms := terms }

@[simp]
theorem ofList_apply_types (base : CalculusLanguageDef)
    (terms : List GrammarRule) :
    ((ofList terms).apply base).types = base.types := by
  simp [ofList]

@[simp]
theorem ofList_apply_terms (base : CalculusLanguageDef)
    (terms : List GrammarRule) :
    ((ofList terms).apply base).terms = base.terms ++ terms := by
  rfl

@[simp]
theorem ofList_apply_equations (base : CalculusLanguageDef)
    (terms : List GrammarRule) :
    ((ofList terms).apply base).equations = base.equations := by
  simp [ofList]

@[simp]
theorem ofList_apply_rewrites (base : CalculusLanguageDef)
    (terms : List GrammarRule) :
    ((ofList terms).apply base).rewrites = base.rewrites := by
  simp [ofList]

private theorem validateTerm_eq_of_typeNames
    (first second : LanguageDef) (term : GrammarRule)
    (typesEqual : first.typeNames = second.typeNames) :
    LanguageDef.validateTerm first term =
      LanguageDef.validateTerm second term := by
  unfold LanguageDef.validateTerm
  rw [typesEqual]

/-- A disjoint family of constructor rows preserves structural validation.

The base restriction to empty equation and rewrite rows is intentional: an
equation or rewrite may mention the constructor namespace, so extending that
namespace requires its own stability interface rather than an implicit
monotonicity claim. -/
theorem apply_language_validate
    (base : CalculusLanguageDef) (terms : List GrammarRule)
    (baseValid : base.toLanguageDef.validate = [])
    (baseEquations : base.equations = [])
    (baseRewrites : base.rewrites = [])
    (termLabelsNodup : (terms.map (·.label)).Nodup)
    (termLabelsDisjoint :
      List.Disjoint (base.terms.map (·.label)) (terms.map (·.label)))
    (termsValid : ∀ term ∈ terms,
      LanguageDef.validateTerm base.toLanguageDef term = []) :
    ((ofList terms).apply base).toLanguageDef.validate = [] := by
  let target := (ofList terms).apply base
  have typeNamesEqual :
      target.toLanguageDef.typeNames = base.toLanguageDef.typeNames := by
    simp [target, ofList, LanguageDef.typeNames]
  apply LanguageDef.validate_eq_nil_of_rows
  · rw [typeNamesEqual]
    exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      base.toLanguageDef baseValid
  · change ((base.terms ++ terms).map (·.label)).Nodup
    rw [List.map_append]
    exact List.Nodup.append
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        base.toLanguageDef baseValid)
      termLabelsNodup termLabelsDisjoint
  · simp [ofList, baseEquations]
  · simp [ofList, baseRewrites]
  · intro term termMembership
    change term ∈ base.terms ++ terms at termMembership
    rcases List.mem_append.mp termMembership with
        baseMembership | addedMembership
    · rw [validateTerm_eq_of_typeNames target.toLanguageDef
        base.toLanguageDef term typeNamesEqual]
      exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
        base.toLanguageDef baseValid term baseMembership
    · rw [validateTerm_eq_of_typeNames target.toLanguageDef
        base.toLanguageDef term typeNamesEqual]
      exact termsValid term addedMembership
  · intro equation equationMembership
    simp [ofList, baseEquations] at equationMembership
  · intro rewrite rewriteMembership
    simp [ofList, baseRewrites] at rewriteMembership

/-! ## Positive and negative controls -/

namespace Canary

private def carrier : TypeDecl := TypeDecl.plain "constructor-extension:T"

private def oldTerm : GrammarRule where
  label := "constructor-extension:old"
  category := carrier.name
  params := []
  syntaxPattern := []

private def newTerm : GrammarRule where
  label := "constructor-extension:new"
  category := carrier.name
  params := []
  syntaxPattern := []

private def base : CalculusLanguageDef where
  name := "constructor-extension"
  types := [carrier]
  terms := [oldTerm]
  equations := []
  rewrites := []

private theorem base_valid : base.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [base, carrier, oldTerm, TypeDecl.plain, LanguageDef.typeNames]

/-- A fresh, well-sorted constructor is admitted by the generic theorem. -/
theorem fresh_constructor_valid :
    ((ofList [newTerm]).apply base).toLanguageDef.validate = [] := by
  apply apply_language_validate base [newTerm] base_valid <;>
    simp [base, oldTerm, newTerm, carrier, LanguageDef.validateTerm,
      LanguageDef.typeNames, TypeDecl.plain]

/-- Reusing an existing constructor label is rejected by structural
validation; append does not silently shadow the old declaration. -/
theorem duplicate_constructor_invalid :
    ((ofList [oldTerm]).apply base).toLanguageDef.validate ≠ [] := by
  intro valid
  have labelsNodup := LanguageDef.constructorLabels_nodup_of_validate_eq_nil
    ((ofList [oldTerm]).apply base).toLanguageDef valid
  simp [ofList, base, oldTerm] at labelsNodup

end Canary

#print axioms apply_language_validate
#print axioms Canary.fresh_constructor_valid
#print axioms Canary.duplicate_constructor_invalid

end ConstructorTermExtension

end Mettapedia.GSLT.LanguageDef
