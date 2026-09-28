import Mettapedia.Languages.Agda.Structural.AdministrativePresheaf
import Mettapedia.OSLF.Syntax.BindingTelescopeConstructorPresheaf

/-!
# Constructor-derived predicates over formed Agda contexts

Every operator of the binding signature induces a natural map from its scoped
argument tuple to the corresponding term sort. The image of a tuple predicate
describes the terms built by that operator. This includes binding operators
without erasing their bound arguments or reimplementing substitution.

These structural predicates and the static typing predicate are distinct.
A constructor predicate alone supplies no typing derivation or declaration
admission. The base remains the admitted raw context category.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

noncomputable def arguments (arity : List (List Srt × Srt)) : Base ⥤ Type :=
  restrict administrativeAdmission.forgetContext.op
    (BindingTelescopeConstructorPresheaf.arguments sig .term .type arity)

noncomputable def constructorMap {s : Srt} (operator : Op s) :
    NatTrans (arguments (sig.arity operator)) (terms s) where
  app _ := TypeCat.ofHom (Term.op (S := sig) operator)
  naturality _ _ _ := rfl

/-- Image under the actual authored operator, with arbitrary argument correlation. -/
noncomputable def constructorPredicate {s : Srt} (operator : Op s)
    (predicate : Subfunctor (arguments (sig.arity operator))) : Subfunctor (terms s) :=
  image (constructorMap operator) predicate

theorem constructor_member_iff {s : Srt} (operator : Op s)
    (predicate : Subfunctor (arguments (sig.arity operator)))
    (X : Base) (args : (arguments (sig.arity operator)).obj X) :
    Term.op (S := sig) operator args ∈ (constructorPredicate operator predicate).obj X ↔
      args ∈ predicate.obj X := by
  constructor
  · rintro ⟨other, holds, same⟩
    have equal := eq_of_heq (Term.op.inj same).2
    cases equal
    exact holds
  · intro holds
    exact ⟨args, holds, rfl⟩

theorem constructor_predicate_adjunction {s : Srt} (operator : Op s)
    (predicate : Subfunctor (arguments (sig.arity operator)))
    (result : Subfunctor (terms s)) :
    constructorPredicate operator predicate ≤ result ↔
      predicate ≤ preimage (constructorMap operator) result :=
  image_le_iff (constructorMap operator) predicate result

theorem constructor_preimage_image {s : Srt} (operator : Op s)
    (predicate : Subfunctor (arguments (sig.arity operator))) :
    preimage (constructorMap operator) (constructorPredicate operator predicate) = predicate := by
  apply Subfunctor.ext
  funext X
  funext args
  exact propext (constructor_member_iff operator predicate X args)

theorem constructor_predicate_restrict {s : Srt} (operator : Op s)
    (predicate : Subfunctor (arguments (sig.arity operator)))
    {X Y : Base} (substitution : X ⟶ Y) (term : (terms s).obj X)
    (member : term ∈ (constructorPredicate operator predicate).obj X) :
    (terms s).map substitution term ∈ (constructorPredicate operator predicate).obj Y :=
  (constructorPredicate operator predicate).map substitution member

theorem other_constructor_excluded {s : Srt} (operator other : Op s)
    (different : operator ≠ other)
    (predicate : Subfunctor (arguments (sig.arity operator)))
    (X : Base) (args : (arguments (sig.arity other)).obj X) :
    Term.op (S := sig) other args ∉ (constructorPredicate operator predicate).obj X := by
  rintro ⟨source, _, same⟩
  exact different (Term.op.inj same).1

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf
