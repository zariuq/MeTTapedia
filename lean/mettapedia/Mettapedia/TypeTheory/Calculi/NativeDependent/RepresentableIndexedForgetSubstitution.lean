import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedSubstitution

/-!
# Generated substitution from an indexed receipt to its whole source value

The raw substitution consists of the generated forgetful term. Its actual
comprehension map and evaluator readout are established before applying the
general type, value and predicate substitution theorems. Composing an
ordinary original arrow with this substitution keeps the entire source
section, rather than selecting one observed coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations

open _root_.CategoryTheory
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def forgetSubstitution (index : ArrowSymbol C) : Substitution (symbols C) 1 2 :=
  singletonArgument (genericForget index)

def forgetSubstitutionFormed (index : ArrowSymbol C) :
    Derivation (signature C) (.substitution (fibreContext index) (objectContext index.source)
      (forgetSubstitution index)) :=
  objectArguments index.source (fibreContextFormed index) (genericForgetFormed index)

def forgetMap (index : ArrowSymbol C) :
    (fibreScope index).1 ⟶ (objectScope index.source).1 :=
  (NativeModel C).toCwf.pair ((NativeModel C).toEmpty (fibreScope index).1)
    (objectMeaning index.source) (forgetValue index)

theorem forgetMap_name (index : ArrowSymbol C) :
    forgetMap index = fibreName index ≫ objectNameInverse index.source := by
  ext world value
  rfl

theorem forgetMap_component (index : ArrowSymbol C) :
    (objectScope index.source).2.components (forgetMap index) 0 =
      ⟨forgetType index, forgetValue index⟩ :=
  ScopeData.components_pair_zero (emptyScope (C := C)).2 (objectMeaning index.source)
    ((NativeModel C).toEmpty (fibreScope index).1) (forgetValue index)

theorem forget_substitution_read (index : ArrowSymbol C) :
    (model C).evaluateSubstitution (fibreScope index) (objectScope index.source)
      (forgetSubstitution index) = some (forgetMap index) := by
  apply ((model C).evaluateSubstitution_eq_some_iff _ _ _ _).2
  intro position
  cases position using Fin.cases with
  | zero =>
    change (model C).evaluateTerm (fibreScope index) (genericForget index) = _
    rw [forgetMap_component]
    exact generic_forget_read index
  | succ impossible => exact Fin.elim0 impossible

def forgetModelSubstitution (index : ArrowSymbol C) :
    ModelSubstitution (model C) (fibreScope index) (objectScope index.source)
      (forgetSubstitution index) :=
  ModelSubstitution.ofEvaluated (model C) _ _ _ _ (forget_substitution_read index)

theorem forget_type_substitution (index : ArrowSymbol C)
    (expression : TypeExpr (symbols C) 1) (family : NativeType (objectScope index.source).1)
    (read : (model C).evaluateType (objectScope index.source) expression = some family) :
    (model C).evaluateType (fibreScope index) (expression.substitute (forgetSubstitution index)) =
      some (family.reindex (forgetMap index)) :=
  (model C).evaluateType_substitute (NativeLocalTypeOperations.products_substitution C)
    expression _ _ _ (forgetModelSubstitution index) family read

theorem forget_value_substitution (index : ArrowSymbol C)
    (expression : TermExpr (symbols C) 1) (value : NativeValue (objectScope index.source).1)
    (read : (model C).evaluateTerm (objectScope index.source) expression = some value) :
    (model C).evaluateTerm (fibreScope index) (expression.substitute (forgetSubstitution index)) =
      some (Value.substitute (K := (NativeModel C).toCwf) value (forgetMap index)) :=
  (model C).evaluateTerm_substitute (NativeLocalTypeOperations.products_substitution C)
    expression _ _ _ (forgetModelSubstitution index) value read

theorem forget_predicate_substitution (index : ArrowSymbol C)
    (expression : PropExpr (symbols C) 1) (predicate : Subfunctor (objectScope index.source).1)
    (read : (model C).evaluatePredicate (objectScope index.source) expression = some predicate) :
    (model C).evaluatePredicate (fibreScope index)
      (expression.substitute (forgetSubstitution index)) =
        some (predicate.preimage (forgetMap index)) :=
  (model C).evaluatePredicate_substitute (NativeLocalTypeOperations.products_substitution C)
    expression _ _ _ (forgetModelSubstitution index) predicate read

def forgetArrowTerm (index : ArrowSymbol C) {target : C} (after : index.source ⟶ target) :
    TermExpr (symbols C) 2 := arrowTerm after (genericForget index)

def forgetArrowFormed (index : ArrowSymbol C) {target : C} (after : index.source ⟶ target) :
    Derivation (signature C) (.term (fibreContext index) (forgetArrowTerm index after)
      (objectType target 2)) :=
  arrowFormed after (fibreContextFormed index) (genericForgetFormed index)

theorem forget_arrow_read (index : ArrowSymbol C) {target : C} (after : index.source ⟶ target) :
    (model C).evaluateTerm (fibreScope index) (forgetArrowTerm index after) =
      some (Value.substitute (K := (NativeModel C).toCwf)
        (⟨RepresentableDeclarations.arrowMeaning ⟨index.source, target, after⟩,
          RepresentableDeclarations.arrowValue ⟨index.source, target, after⟩⟩ :
            NativeValue (objectScope index.source).1) (forgetMap index)) :=
  forget_value_substitution index (arrowTerm after (.var 0)) _ (arrow_read after)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations
