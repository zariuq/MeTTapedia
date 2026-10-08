import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfTerms
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationArrows

/-!
# Generated source substitutions and dependent section transport

An original substitution has an independently typed raw presentation. Its
actual parser returns the complete represented substitution map. The source
CwF's comprehension comparison then identifies the substituted source type
with the native pullback, and intertwines substitution of whole sections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

def arrowTerm {source target : Base K} (arrow : source ⟶ target) {n : Nat}
    (argument : TermExpr (symbols K) n) : TermExpr (symbols K) n :=
  .primitive (.ordinary ⟨source, target, arrow⟩) (singletonArgument argument)

def arrowFormed {source target : Base K} (arrow : source ⟶ target) {n : Nat}
    {context : ContextExpr (symbols K) n} {argument : TermExpr (symbols K) n}
    (formed : Derivation (signature K) (.context context))
    (typed : Derivation (signature K) (.term context argument (objectType source n))) :
    Derivation (signature K) (.term context (arrowTerm arrow argument) (objectType target n)) := by
  have tree := deriveList (.primitive context (.ordinary ⟨source, target, arrow⟩) (singletonArgument argument))
    (.cons formed (.cons (objectContextFormed source)
      (.cons ((headers K).termResult (.ordinary ⟨source, target, arrow⟩))
        (.cons (objectArguments source formed typed) .nil))))
  change Derivation (signature K) (.term context (arrowTerm arrow argument)
    ((objectType target 1).substitute (singletonArgument argument))) at tree
  rw [objectType_substitute] at tree
  exact tree

def originalSubstitution {source target : Base K} (arrow : source ⟶ target) :
    Substitution (symbols K) 1 1 := singletonArgument (arrowTerm arrow (.var 0))

def originalSubstitutionFormed {source target : Base K} (arrow : source ⟶ target) :
    Derivation (signature K) (.substitution (objectContext source) (objectContext target)
      (originalSubstitution arrow)) :=
  objectArguments target (objectContextFormed source)
    (arrowFormed arrow (objectContextFormed source) (variableFormed source))

abbrev originalMap {source target : Base K} (arrow : source ⟶ target) :=
  RepresentableDeclarations.originalPresheafArrow arrow

theorem arrow_read {source target : Base K} (arrow : source ⟶ target) :
    (model K).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) =
      some ⟨RepresentableDeclarations.arrowMeaning ⟨source, target, arrow⟩,
        RepresentableDeclarations.arrowValue ⟨source, target, arrow⟩⟩ := by
  have read := (model K).evaluate_primitive (objectScope source) (.ordinary ⟨source, target, arrow⟩)
    (singletonArgument (.var 0)) (𝟙 (objectScope source).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact variable_identity source
      | succ impossible => exact Fin.elim0 impossible)
  change (model K).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) =
    some (Value.substitute (K := (NativeModel (Base K)).toCwf)
      (⟨RepresentableDeclarations.arrowMeaning ⟨source, target, arrow⟩,
        RepresentableDeclarations.arrowValue ⟨source, target, arrow⟩⟩ : NativeValue (objectScope source).1)
      (𝟙 (objectScope source).1)) at read
  exact read.trans (congrArg some (Value.substitute_identity
    (K := (NativeModel (Base K)).toCwf)
    ⟨RepresentableDeclarations.arrowMeaning ⟨source, target, arrow⟩,
      RepresentableDeclarations.arrowValue ⟨source, target, arrow⟩⟩))

theorem original_substitution_read {source target : Base K} (arrow : source ⟶ target) :
    (model K).evaluateSubstitution (objectScope source) (objectScope target)
      (originalSubstitution arrow) = some (originalMap arrow) := by
  apply ((model K).evaluateSubstitution_eq_some_iff _ _ _ _).2
  intro position
  cases position using Fin.cases with
  | zero =>
    change (model K).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) = _
    rw [RepresentableDeclarations.original_component]
    exact arrow_read arrow
  | succ impossible => exact Fin.elim0 impossible

def originalModelSubstitution {source target : Base K} (arrow : source ⟶ target) :
    ModelSubstitution (model K) (objectScope source) (objectScope target) (originalSubstitution arrow) :=
  ModelSubstitution.ofEvaluated (model K) _ _ _ _ (original_substitution_read arrow)

theorem complete_type_substitution {source target : Base K} (arrow : source ⟶ target)
    (expression : TypeExpr (symbols K) 1) (family : NativeType (objectScope target).1)
    (read : (model K).evaluateType (objectScope target) expression = some family) :
    (model K).evaluateType (objectScope source) (expression.substitute (originalSubstitution arrow)) =
      some (family.reindex (originalMap arrow)) :=
  (model K).evaluateType_substitute (NativeLocalTypeOperations.products_substitution (Base K))
    expression _ _ _ (originalModelSubstitution arrow) family read

theorem complete_value_substitution {source target : Base K} (arrow : source ⟶ target)
    (expression : TermExpr (symbols K) 1) (value : NativeValue (objectScope target).1)
    (read : (model K).evaluateTerm (objectScope target) expression = some value) :
    (model K).evaluateTerm (objectScope source) (expression.substitute (originalSubstitution arrow)) =
      some (Value.substitute (K := (NativeModel (Base K)).toCwf) value (originalMap arrow)) :=
  (model K).evaluateTerm_substitute (NativeLocalTypeOperations.products_substitution (Base K))
    expression _ _ _ (originalModelSubstitution arrow) value read

theorem complete_predicate_substitution {source target : Base K} (arrow : source ⟶ target)
    (expression : PropExpr (symbols K) 1) (predicate : Subfunctor (objectScope target).1)
    (read : (model K).evaluatePredicate (objectScope target) expression = some predicate) :
    (model K).evaluatePredicate (objectScope source) (expression.substitute (originalSubstitution arrow)) =
      some (predicate.preimage (originalMap arrow)) :=
  (model K).evaluatePredicate_substitute (NativeLocalTypeOperations.products_substitution (Base K))
    expression _ _ _ (originalModelSubstitution arrow) predicate read

/-- The source substitution comparison, pulled back through the actual
generated object scope, compares complete native families. -/
def sourceSubstitutionIso {context replacement : K.Ctx} (type : K.Ty context)
    (before : K.Sub replacement context) :
    sourceFamily (K.tySub type before) ≅
      reindexDisplayed (originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before))
        (sourceFamily type) :=
  Functor.isoWhiskerLeft (objectName (⟨replacement⟩ : Base K)).mapElements
    (CwfYoneda.substitutionIso K type before)

theorem source_substitution_section {context replacement : K.Ctx} {type : K.Ty context}
    (term : K.Tm context type) (before : K.Sub replacement context) :
    (Functor.sectionsFunctor _).map (sourceSubstitutionIso type before).hom
        (sourceValue (K.tmSub term before)) =
      reindexDisplayedSection (originalMap
        (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before))
        (sourceMeaning type).decoded (sourceValue term) := by
  apply (Functor.sections_ext_iff).2
  intro point
  exact CwfYoneda.substitutionIso_term K term before
    ((objectName (⟨replacement⟩ : Base K)).mapElements.obj point)

theorem generated_source_type_substitution {context replacement : K.Ctx} (type : K.Ty context)
    (before : K.Sub replacement context) :
    (model K).evaluateType (objectScope (⟨replacement⟩ : Base K))
      ((sourceType type (.var 0)).substitute
        (originalSubstitution (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before))) =
      some ((sourceMeaning type).reindex
        (originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before))) :=
  complete_type_substitution _ _ _ (source_type_read type)

theorem generated_source_term_substitution {context replacement : K.Ctx} {type : K.Ty context}
    (term : K.Tm context type) (before : K.Sub replacement context) :
    (model K).evaluateTerm (objectScope (⟨replacement⟩ : Base K))
      ((sourceTerm term).substitute
        (originalSubstitution (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before))) =
      some ⟨(sourceMeaning type).reindex
        (originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before)),
        (Functor.sectionsFunctor _).map (sourceSubstitutionIso type before).hom
          (sourceValue (K.tmSub term before))⟩ := by
  rw [source_substitution_section]
  exact complete_value_substitution _ _ _ (source_term_read term)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
