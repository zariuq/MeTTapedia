import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationCategory

/-!
# Complete dependent readouts under represented substitutions

Every admitted generated substitution is evaluated at the actual source and
target representable scopes. The generated action on types, complete values
and predicates agrees with dependent reindexing by that map. Original arrows
recover Yoneda's action through the earned scope isomorphisms.

The categorical quotient identifies its semantic dependent actions. This
does not assert that the complete syntactic type fibre descends through the
additional original-category equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations

open _root_.CategoryTheory
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def arrowModelSubstitution {source target : RepresentedContext C} (arrow : source ⟶ target) :
    ModelSubstitution (model C) (objectScope source.object) (objectScope target.object)
      arrow.substitution :=
  ModelSubstitution.ofEvaluated (model C) _ _ _ _ (readArrow_readout arrow)

theorem complete_type_substitution {source target : RepresentedContext C} (arrow : source ⟶ target)
    (type : TypeExpr (symbols C) 1) (family : NativeType (objectScope target.object).1)
    (readout : (model C).evaluateType (objectScope target.object) type = some family) :
    (model C).evaluateType (objectScope source.object) (type.substitute arrow.substitution) =
      some (family.reindex (readArrow arrow)) :=
  (model C).evaluateType_substitute (NativeLocalTypeOperations.products_substitution C)
    type _ _ arrow.substitution (arrowModelSubstitution arrow) family readout

theorem complete_value_substitution {source target : RepresentedContext C} (arrow : source ⟶ target)
    (term : TermExpr (symbols C) 1) (value : NativeValue (objectScope target.object).1)
    (readout : (model C).evaluateTerm (objectScope target.object) term = some value) :
    (model C).evaluateTerm (objectScope source.object) (term.substitute arrow.substitution) =
      some (Value.substitute (K := (NativeModel C).toCwf) value (readArrow arrow)) :=
  (model C).evaluateTerm_substitute (NativeLocalTypeOperations.products_substitution C)
    term _ _ arrow.substitution (arrowModelSubstitution arrow) value readout

theorem complete_predicate_substitution {source target : RepresentedContext C} (arrow : source ⟶ target)
    (predicate : PropExpr (symbols C) 1) (meaning : Subfunctor (objectScope target.object).1)
    (readout : (model C).evaluatePredicate (objectScope target.object) predicate = some meaning) :
    (model C).evaluatePredicate (objectScope source.object) (predicate.substitute arrow.substitution) =
      some (meaning.preimage (readArrow arrow)) :=
  (model C).evaluatePredicate_substitute (NativeLocalTypeOperations.products_substitution C)
    predicate _ _ arrow.substitution (arrowModelSubstitution arrow) meaning readout

def originalReadoutIso : (originalFunctor (C := C)) ⋙ conservedReadout ≅ yoneda :=
  NatIso.ofComponents (fun object => objectScopeIso object) (by
    intro source target arrow
    change conservedReadout.map (originalFunctor.map arrow) ≫ objectName target =
      objectName source ≫ yoneda.map arrow
    rw [conservedReadout_original, originalPresheafArrow_name]
    have cancellation : objectNameInverse target ≫ objectName target = 𝟙 (yoneda.obj target) :=
      (objectScopeIso target).inv_hom_id
    simp only [Category.assoc, cancellation, Category.comp_id])

theorem complete_original_predicate_substitution {source target : C}
    (arrow : source ⟶ target) (predicate : Subfunctor (yoneda.obj target)) :
    (model C).evaluatePredicate (objectScope source)
      ((predicateTerm predicate (.var 0)).substitute (originalArrow arrow).substitution) =
        some ((predicate.preimage (yoneda.map arrow)).preimage (objectName source)) := by
  have read := complete_predicate_substitution (originalArrow arrow)
    (predicateTerm predicate (.var 0)) _ (predicate_read predicate)
  rw [readArrow_original, originalPresheafArrow_name] at read
  have cancellation : objectNameInverse target ≫ objectName target = 𝟙 (yoneda.obj target) :=
    (objectScopeIso target).inv_hom_id
  rw [← Subfunctor.preimage_comp] at read
  simpa only [Category.assoc, cancellation, Category.comp_id, Subfunctor.preimage_comp] using read

/-- All generated equations and original category equations earn equality
of actual dependent family actions after categorical congruence closure. -/
theorem conserved_family_action {source target : RepresentedContext C}
    (first second : source ⟶ target)
    (same : originalProjection.map first = originalProjection.map second)
    (family : NativeType (objectScope target.object).1) :
    family.reindex (readArrow first) = family.reindex (readArrow second) := by
  have maps := congrArg (conservedReadout.map) same
  change readArrow first = readArrow second at maps
  exact congrArg family.reindex maps

theorem conserved_value_action {source target : RepresentedContext C}
    (first second : source ⟶ target)
    (same : originalProjection.map first = originalProjection.map second)
    (value : NativeValue (objectScope target.object).1) :
    Value.substitute (K := (NativeModel C).toCwf) value (readArrow first) =
      Value.substitute (K := (NativeModel C).toCwf) value (readArrow second) := by
  have maps := congrArg (conservedReadout.map) same
  change readArrow first = readArrow second at maps
  exact congrArg (Value.substitute (K := (NativeModel C).toCwf) value) maps

theorem conserved_predicate_action {source target : RepresentedContext C}
    (first second : source ⟶ target)
    (same : originalProjection.map first = originalProjection.map second)
    (predicate : Subfunctor (objectScope target.object).1) :
    predicate.preimage (readArrow first) = predicate.preimage (readArrow second) := by
  have maps := congrArg (conservedReadout.map) same
  change readArrow first = readArrow second at maps
  exact congrArg predicate.preimage maps

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations
