import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualHeyting
import Mathlib.Order.Heyting.Hom

/-!
# Heyting substitution along generated quotient arrows

The actual generated substitution quotient acts on predicate classes. The
resulting maps preserve the generated Heyting operations and compose with
the category's substitutions. No quotient representative changes the action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.PredicateAction

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

def reindex {source target : quotientContext D} (morphism : source ⟶ target)
    (predicate : QPredicate target.as) : QPredicate source.as :=
  (QPredicate.presheaf D).map morphism.op predicate

@[simp] theorem reindex_project {source target : Context D} (morphism : source ⟶ target)
    (predicate : QPredicate target) :
    reindex ((quotientProjection D).map morphism) predicate = predicate.reindex morphism := rfl

theorem reindex_id {context : quotientContext D} (predicate : QPredicate context.as) :
    reindex (𝟙 context) predicate = predicate := by
  change (QPredicate.presheaf D).map (𝟙 (Opposite.op context)) predicate = predicate
  rw [Functor.map_id]
  rfl

theorem reindex_comp {source middle target : quotientContext D}
    (earlier : source ⟶ middle) (later : middle ⟶ target) (predicate : QPredicate target.as) :
    reindex (earlier ≫ later) predicate = reindex earlier (reindex later predicate) := by
  change (QPredicate.presheaf D).map (later.op ≫ earlier.op) predicate = _
  rw [Functor.map_comp]
  rfl

def substitution {source target : quotientContext D} (morphism : source ⟶ target) :
    HeytingHom (QPredicate target.as) (QPredicate source.as) where
  toFun := reindex morphism
  map_inf' first second := by
    induction morphism using Quot.inductionOn with
    | h raw => exact Logic.meet_reindex raw first second
  map_sup' first second := by
    induction morphism using Quot.inductionOn with
    | h raw => exact Logic.join_reindex raw first second
  map_bot' := by
    induction morphism using Quot.inductionOn with
    | h raw => exact Logic.bot_reindex raw
  map_himp' first second := by
    induction morphism using Quot.inductionOn with
    | h raw => exact Logic.conditional_reindex raw first second

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.PredicateAction
