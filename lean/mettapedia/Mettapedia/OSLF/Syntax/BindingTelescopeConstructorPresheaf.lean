import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTelescopePresheaf

/-!
# Binding constructors over telescope contexts

Each signature operator acts naturally on its full tuple of scoped arguments.
The action uses the existing `bindArgs`, including each argument's own binder
list. Images of predicates on argument tuples then describe constructed terms;
preimages describe the arguments of a requested term predicate.

These are constructor-derived predicates on the raw telescope presheaves.
They do not identify the telescope base with a classifying lambda theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingTelescopeConstructorPresheaf

open CategoryTheory
open IntrinsicScopedLocalTelescopePresheaf (Base terms)
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

variable (S : Signature) (b k : S.Srt)

/-- Ordered arguments, each with the binder scope declared by the signature. -/
def arguments (arity : List (List S.Srt × S.Srt)) : Base S b k ⥤ Type where
  obj X := Args S arity (Telescope.scope b X.unop.val.1)
  map f := TypeCat.ofHom (bindArgs f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro args
    exact bindArgs_id args
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro args
    exact (bindArgs_comp f.unop g.unop args).symm

/-- The signature's constructor, as a natural map between standard presheaves. -/
def operation {s : S.Srt} (operator : S.Op s) :
    NatTrans (arguments S b k (S.arity operator)) (terms S b k s) where
  app _ := TypeCat.ofHom (Term.op operator)
  naturality _ _ _ := rfl

variable {S b k} {s : S.Srt} (operator : S.Op s)

theorem operation_injective (X : Base S b k) :
    Function.Injective ((operation S b k operator).app X) := by
  intro first second same
  exact eq_of_heq (Term.op.inj same).2

/-- A constructor's image retains the predicate on its entire argument tuple. -/
def constructed (predicate : Subfunctor (arguments S b k (S.arity operator))) :
    Subfunctor (terms S b k s) := image (operation S b k operator) predicate

theorem constructed_iff (predicate : Subfunctor (arguments S b k (S.arity operator)))
    (X : Base S b k) (term : (terms S b k s).obj X) :
    term ∈ (constructed operator predicate).obj X ↔
      ∃ args : (arguments S b k (S.arity operator)).obj X,
        args ∈ predicate.obj X ∧ Term.op operator args = term := Iff.rfl

theorem constructed_operation_iff
    (predicate : Subfunctor (arguments S b k (S.arity operator)))
    (X : Base S b k) (args : (arguments S b k (S.arity operator)).obj X) :
    Term.op operator args ∈ (constructed operator predicate).obj X ↔
      args ∈ predicate.obj X := by
  constructor
  · rintro ⟨other, holds, same⟩
    have equal := operation_injective operator X same
    cases equal
    exact holds
  · intro holds
    exact ⟨args, holds, rfl⟩

theorem constructor_image_preimage
    (predicate : Subfunctor (arguments S b k (S.arity operator))) :
    preimage (operation S b k operator) (constructed operator predicate) = predicate := by
  apply Subfunctor.ext
  funext X
  funext args
  exact propext (constructed_operation_iff operator predicate X args)

theorem constructor_adjunction
    (predicate : Subfunctor (arguments S b k (S.arity operator)))
    (result : Subfunctor (terms S b k s)) :
    constructed operator predicate ≤ result ↔
      predicate ≤ preimage (operation S b k operator) result :=
  image_le_iff (operation S b k operator) predicate result

theorem different_constructor_excluded {other : S.Op s} (different : operator ≠ other)
    (predicate : Subfunctor (arguments S b k (S.arity operator)))
    (X : Base S b k) (args : (arguments S b k (S.arity other)).obj X) :
    Term.op other args ∉ (constructed operator predicate).obj X := by
  rintro ⟨source, _, same⟩
  exact different (Term.op.inj same).1

end Mettapedia.OSLF.Binding.BindingTelescopeConstructorPresheaf
