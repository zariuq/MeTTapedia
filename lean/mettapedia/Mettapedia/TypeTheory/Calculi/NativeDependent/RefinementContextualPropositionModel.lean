import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualDoctrine
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPropositions
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualComprehensionSyntax

/-!
# Ordinary propositions in the generated dependent model

The ordinary proposition type represents exactly the generated predicate
fibre. Its quotation and readout retain the supplied complete term class,
are inverse, and follow actual quotient substitutions. This is a local
logical capability, not a classifier for every source-category subobject.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.PropositionModel

open _root_.CategoryTheory
open QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualPredicateCapabilities

universe u
variable {S : Symbols.{u}} {D : Signature S}

def omega (context : QuotientCwf.QContext D) : QuotientCwf.Ty context :=
  QType.mk (propositionsType context.as)

noncomputable def equivalence (context : QuotientCwf.QContext D) :
    QPredicate context.as ≃ QuotientCwf.Tm context (omega context) :=
  (propositionEquiv context.as).trans (propositionCwfEquiv context.as)

noncomputable def quote {context : QuotientCwf.QContext D} (predicate : QPredicate context.as) :
    QuotientCwf.Tm context (omega context) := equivalence context predicate

noncomputable def holds {context : QuotientCwf.QContext D} (term : QuotientCwf.Tm context (omega context)) :
    QPredicate context.as := (equivalence context).symm term

theorem holds_quote {context : QuotientCwf.QContext D} (predicate : QPredicate context.as) :
    holds (quote predicate) = predicate := (equivalence context).left_inv predicate

theorem quote_holds {context : QuotientCwf.QContext D} (term : QuotientCwf.Tm context (omega context)) :
    quote (holds term) = term := (equivalence context).right_inv term

theorem omega_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target) :
    QuotientCwf.tySub (omega target) morphism = omega source := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

theorem quote_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target)
    (predicate : QPredicate target.as) :
    HEq (QuotientCwf.tmSub (quote predicate) morphism) (quote (PredicateAction.reindex morphism predicate)) := by
  apply heq_of_value
  induction morphism using Quot.inductionOn with
  | h raw =>
    refine _root_.Quotient.inductionOn predicate fun formed => ?_
    rfl

theorem holds_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target)
    (term : QuotientCwf.Tm target (omega target)) (transported : QuotientCwf.Tm source (omega source))
    (same : HEq (QuotientCwf.tmSub term morphism) transported) :
    holds transported = PredicateAction.reindex morphism (holds term) := by
  have natural := quote_substitution morphism (holds term)
  rw [quote_holds] at natural
  have quotations : transported = quote (PredicateAction.reindex morphism (holds term)) :=
    eq_of_heq (same.symm.trans natural)
  rw [quotations, holds_quote]

noncomputable def operations (D : Signature S) : PropositionOperations (predicateDoctrine D) where
  omega := omega
  quote := quote
  holds := holds
  holds_quote := holds_quote
  quote_holds := quote_holds
  omega_substitution := omega_substitution
  quote_substitution := quote_substitution
  holds_substitution := holds_substitution

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.PropositionModel
