import Mettapedia.Languages.Agda.Structural.AdministrativeFunctionPredicates
import Mettapedia.Languages.Agda.Structural.AdministrativePresheafControls

/-!
# Native typed application and function-predicate controls

The identity term belongs to an internal function predicate because its
actual typing derivation supplies the application law at every supported
substitution. An unsupported type annotation has no inhabitants. A function
predicate with that empty input can hold vacuously and cannot supply a
missing typing derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.FunctionControls

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

noncomputable def universeSection (level : Nat) : TermSection where
  app _ := TypeCat.ofHom (fun _ => Statics.universeTerm level)
  naturality _ _ _ := rfl

noncomputable def universeMembers (level : Nat) : Subfunctor (terms .term) :=
  inhabitants (annotate (level + 1) (universeSection level))

theorem identity_has_native_function_type (X : Base) :
    lam (.var .zero) ∈ (inhabitants (arrowSection 2 2 (universeSection 1)
      (universeSection 1))).obj X := by
  obtain ⟨context⟩ := X.unop.val.property
  let Γ := X.unop.val.val.2
  let A := Statics.universeType X.unop.val.val.1 1
  let domain := administrativeOperations.universeFormed context 1
  let extended := administrativeOperations.extend context domain
  let codomain := administrativeOperations.universeFormed extended 1
  let body := Derivation.core (.variable (Γ.snoc A.code) .zero)
    (consEvidence CoreDerivation extended (noEvidence CoreDerivation))
  exact ⟨Derivation.core (.lambda Γ A (.noBind A) (.bind (.var .zero)))
    (consEvidence CoreDerivation domain (consEvidence CoreDerivation codomain
      (consEvidence CoreDerivation body (noEvidence CoreDerivation))))⟩

theorem identity_has_internal_function_predicate (X : Base) :
    applicationFunction.app X (lam (.var .zero)) ∈
      (functionPredicate (universeMembers 1) (universeMembers 1)).obj X :=
  typed_function_internal 2 2 (universeSection 1) (universeSection 1) X
    (identity_has_native_function_type X)

theorem identity_argument_is_inhabited :
    Statics.universeTerm 0 ∈ (universeMembers 1).obj Controls.closedWorld :=
  ⟨AdministrativeStatics.Controls.contractedTyped⟩

/-- The function predicate supplies an actual typing derivation for the
unreduced application, not a Boolean verdict. -/
theorem actual_application_is_typed :
    Statics.app Statics.Boundary.identityTerm (Statics.universeTerm 0) ∈
      (universeMembers 1).obj Controls.closedWorld := by
  have typed := functionPredicate_elimination (universeMembers 1) (universeMembers 1)
    Controls.closedWorld (applicationFunction.app Controls.closedWorld Statics.Boundary.identityTerm)
    (identity_has_internal_function_predicate Controls.closedWorld)
    (Statics.universeTerm 0) identity_argument_is_inhabited
  change Statics.app ((terms .term).map (𝟙 Controls.closedWorld) Statics.Boundary.identityTerm)
    (Statics.universeTerm 0) ∈ (universeMembers 1).obj Controls.closedWorld at typed
  exact typed

theorem open_argument_after_actual_substitution :
    (applicationFunction.app Controls.openWorld (lam (.var .zero))).app Controls.closedWorld
      Controls.replaceWithRedex AdministrativeStatics.Controls.expanded ∈
        (universeMembers 1).obj Controls.closedWorld :=
  identity_has_internal_function_predicate Controls.openWorld Controls.closedWorld
    Controls.replaceWithRedex AdministrativeStatics.Controls.expanded
    ⟨AdministrativeStatics.Controls.expandedTyped⟩

theorem different_raw_heads_remain_distinct (X : Base) :
    applicationFunction.app X (lam (.var .zero)) ≠
      applicationFunction.app X (lamNoAbs (Statics.universeTerm 0)) := by
  intro same
  have impossible := applicationFunction_injective X same
  cases impossible

noncomputable def unsupportedAnnotation : TypeSection where
  app _ := TypeCat.ofHom (fun _ => el (prop (levelClosed 1)) (Statics.universeTerm 0))
  naturality _ _ _ := rfl

theorem unsupported_members_empty (X : Base) (term : (terms .term).obj X) :
    term ∉ (inhabitants unsupportedAnnotation).obj X := by
  rintro ⟨tree⟩
  have boundary := tree.typingFormation.formationView.boundary
  cases boundary

theorem unsupported_function_property_vacuous (X : Base) (function : (terms .term).obj X) :
    applicationFunction.app X function ∈
      (functionPredicate (inhabitants unsupportedAnnotation)
        (inhabitants unsupportedAnnotation)).obj X := by
  intro Y substitution argument member
  exact (unsupported_members_empty Y argument member).elim

theorem functional_property_does_not_mint_typing (X : Base) (function : (terms .term).obj X) :
    applicationFunction.app X function ∈
      (functionPredicate (inhabitants unsupportedAnnotation)
        (inhabitants unsupportedAnnotation)).obj X ∧
    function ∉ (inhabitants unsupportedAnnotation).obj X :=
  ⟨unsupported_function_property_vacuous X function, unsupported_members_empty X function⟩

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.FunctionControls
