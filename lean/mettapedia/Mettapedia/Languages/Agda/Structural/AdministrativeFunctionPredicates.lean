import Mettapedia.Languages.Agda.Structural.AdministrativePresheaf
import Mettapedia.GSLT.Topos.ConstructivePresheafFunctionPredicates

/-!
# Application and internal function predicates over formed Agda contexts

Application is the actual spine constructor, and its curried natural map
retains raw function syntax. A finite, nondependent Pi typing derivation
implies the internal function predicate for its domain and codomain fibres.
Neither this map nor that implication identifies conversion classes or
asserts a converse characterization of Agda typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

noncomputable def application : NatTrans
    (FunctorToTypes.prod (terms .term) (terms .term)) (terms .term) where
  app _ := TypeCat.ofHom (fun pair => Statics.app pair.2 pair.1)
  naturality _ _ _ := rfl

noncomputable def applicationFunction :
    NatTrans (terms .term) (functions (terms .term) (terms .term)) :=
  curryFunction application

theorem applicationFunction_apply (X Y : Base) (substitution : X ⟶ Y)
    (function : (terms .term).obj X) (argument : (terms .term).obj Y) :
    (applicationFunction.app X function).app Y substitution argument =
      Statics.app ((terms .term).map substitution function) argument := rfl

theorem applicationFunction_injective (X : Base) :
    Function.Injective (applicationFunction.app X) := by
  intro first second same
  have applied := congrArg
    (fun value => value.app X (𝟙 X) (Statics.universeTerm 0)) same
  change Statics.app ((terms .term).map (𝟙 X) first) (Statics.universeTerm 0) =
    Statics.app ((terms .term).map (𝟙 X) second) (Statics.universeTerm 0) at applied
  rw [(terms .term).map_id_apply, (terms .term).map_id_apply] at applied
  exact (Args.cons.inj (eq_of_heq (Term.op.inj applied).2)).1

/-- The standard constant one-point functor, with explicit laws. -/
def one : Base ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev TermSection := NatTrans one (terms .term)
abbrev TypeSection := NatTrans one (terms .type)

noncomputable def annotate (level : Nat) (denotation : TermSection) : TypeSection where
  app X := TypeCat.ofHom (fun _ => (Statics.TypeParameter.mk level (denotation.app X PUnit.unit)).code)
  naturality X Y substitution := by
    apply ConcreteCategory.hom_ext
    intro value
    have naturally := congrArg (fun h : one.obj X ⟶ (terms .term).obj Y => h PUnit.unit)
      (denotation.naturality substitution)
    change denotation.app Y PUnit.unit = bind substitution.unop.val (denotation.app X PUnit.unit)
      at naturally
    change el (set (levelClosed level)) (denotation.app Y PUnit.unit) =
      el (set (levelClosed level)) (bind substitution.unop.val (denotation.app X PUnit.unit))
    rw [naturally]
    rfl

/-- A fibre of the native typing predicate along a natural type section. -/
noncomputable def inhabitants (type : TypeSection) : Subfunctor (terms .term) where
  obj X := {term | Nonempty (CoreDerivation
    (Statics.typed X.unop.val.val.2 term (type.app X PUnit.unit)))}
  map {X Y} substitution := by
    rintro term ⟨typing⟩
    obtain ⟨evidence⟩ := substitution.unop.property
    have image := CoreDerivation.substitution typing Y.unop.val.val.2
      substitution.unop.val evidence
    have naturally := congrArg (fun h : one.obj X ⟶ (terms .type).obj Y => h PUnit.unit)
      (type.naturality substitution)
    change type.app Y PUnit.unit = bind substitution.unop.val (type.app X PUnit.unit)
      at naturally
    rw [← naturally] at image
    exact ⟨image⟩

noncomputable def arrowSection (domainLevel codomainLevel : Nat)
    (domain codomain : TermSection) : TypeSection where
  app X := TypeCat.ofHom (fun _ =>
    (Statics.piType ⟨domainLevel, domain.app X PUnit.unit⟩
      (.noBind ⟨codomainLevel, codomain.app X PUnit.unit⟩)).code)
  naturality X Y substitution := by
    apply ConcreteCategory.hom_ext
    intro value
    have domainNatural := congrArg (fun h : one.obj X ⟶ (terms .term).obj Y => h PUnit.unit)
      (domain.naturality substitution)
    have codomainNatural := congrArg (fun h : one.obj X ⟶ (terms .term).obj Y => h PUnit.unit)
      (codomain.naturality substitution)
    change domain.app Y PUnit.unit = bind substitution.unop.val (domain.app X PUnit.unit)
      at domainNatural
    change codomain.app Y PUnit.unit = bind substitution.unop.val (codomain.app X PUnit.unit)
      at codomainNatural
    change el _ (piNoAbs (el _ (domain.app Y PUnit.unit)) (el _ (codomain.app Y PUnit.unit))) =
      el _ (piNoAbs (el _ (bind substitution.unop.val (domain.app X PUnit.unit)))
        (el _ (bind substitution.unop.val (codomain.app X PUnit.unit))))
    rw [domainNatural, codomainNatural]
    rfl

/-- The native application rule proves the predicate-preservation premise
of the internal currying theorem. -/
theorem typed_application_preserves_predicates (domainLevel codomainLevel : Nat)
    (domain codomain : TermSection) :
    productPredicate (inhabitants (annotate domainLevel domain))
      (inhabitants (arrowSection domainLevel codomainLevel domain codomain)) ≤
        preimage application (inhabitants (annotate codomainLevel codomain)) := by
  intro X pair member
  obtain ⟨argument⟩ := member.1
  obtain ⟨function⟩ := member.2
  let A : Statics.TypeParameter X.unop.val.val.1 := ⟨domainLevel, domain.app X PUnit.unit⟩
  let B : Statics.TypeParameter X.unop.val.val.1 := ⟨codomainLevel, codomain.app X PUnit.unit⟩
  have result := Derivation.core (.application X.unop.val.val.2 A (.noBind B) pair.2 pair.1)
    (consEvidence CoreDerivation function
      (consEvidence CoreDerivation argument (noEvidence CoreDerivation)))
  exact ⟨(congrArg (fun T : Statics.TypeParameter X.unop.val.val.1 =>
    CoreDerivation (Statics.typed X.unop.val.val.2 (Statics.app pair.2 pair.1) T.code))
    (Statics.TypeBody.instantiate_noBind B pair.1)).mp result⟩

theorem typed_function_internal (domainLevel codomainLevel : Nat)
    (domain codomain : TermSection) :
    inhabitants (arrowSection domainLevel codomainLevel domain codomain) ≤
      preimage applicationFunction
        (functionPredicate (inhabitants (annotate domainLevel domain))
          (inhabitants (annotate codomainLevel codomain))) :=
  (curry_preserves_predicates_iff application _ _ _).2
    (typed_application_preserves_predicates domainLevel codomainLevel domain codomain)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf
