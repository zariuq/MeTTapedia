import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualQuantifierSubstitution
import Mettapedia.TypeTheory.ContextualPredicateCapabilities

/-!
# The generated source predicate doctrine

The actual quotient CwF supplies a local predicate doctrine. Its Heyting
action, both display adjunctions and quantifier base change are instantiated
by the constructions earned from generated judgments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualPredicateCapabilities

universe u
variable {S : Symbols.{u}}

noncomputable def predicateDoctrine (D : Signature S) : PredicateDoctrine (QuotientCwf.cwf D) where
  Predicate context := QPredicate context.as
  algebra _ := inferInstance
  reindex := PredicateAction.substitution
  reindex_id := PredicateAction.reindex_id
  reindex_comp := PredicateAction.reindex_comp
  all := Quantifiers.all
  some := Quantifiers.some
  all_adjunction := Quantifiers.all_adjunction
  some_adjunction := Quantifiers.some_adjunction
  all_reindex := Quantifiers.all_substitution
  some_reindex := Quantifiers.some_substitution

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
