import Mettapedia.TypeTheory.ContextualPredicateCapabilities
import Mettapedia.TypeTheory.PresheafNativePredicateQuantifierSubstitution
import Mettapedia.TypeTheory.PresheafNativePropositionSubstitution
import Mettapedia.TypeTheory.PresheafNativeRefinementTermSubstitution
import Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic

/-!
# Actual native predicate capabilities

The predicate doctrine is the complete subfunctor Heyting algebra. Its
quantifiers use the actual native display maps; their substitution laws come
from the earned pullback square. Ordinary proposition values are contextual
sieves, and guarded assumptions are their actual satisfying subfunctors.
The refinement operations retain the supplied section in the stable native
sum with the fixed truth-proof family.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateCapabilities

open _root_.CategoryTheory
open Mettapedia.GSLT.Topos Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities NativeLocalTheoryTransformation NativeLocalTypeFormers
open DisplayedPresheafComprehension DisplayedPresheafCwf ContextualLocalUniverses
open PresheafNativePredicateQuantifierSubstitution
open PresheafNativePropositionReadout PresheafNativePropositionSubstitution
open PresheafNativeRefinementTermSubstitution PresheafNativeStableRefinement

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

/-- Pullback of actual subfunctors is a Heyting homomorphism. -/
def reindex (substitution : Q ⟶ P) : HeytingHom (Subfunctor P) (Subfunctor Q) where
  toFun predicate := predicate.preimage substitution
  map_inf' _ _ := rfl
  map_sup' _ _ := rfl
  map_bot' := rfl
  map_himp' first second := preimage_himp first second substitution

noncomputable def doctrine (C : Type u) [Category.{u} C] :
    PredicateDoctrine (nativeLocalModel C).toCwf where
  Predicate := Subfunctor
  algebra context := (presheafSubfunctorFrame context).toHeytingAlgebra
  reindex := reindex
  reindex_id predicate := by
    ext world value
    rfl
  reindex_comp earlier later predicate := predicate.preimage_comp earlier later
  all := nativeForall
  some := nativeExists
  all_adjunction type body premise := preimage_le_iff_le_forallAlong _ body premise
  some_adjunction type body consequent := Subfunctor.image_le_iff body _ consequent
  all_reindex := nativeForall_substitution
  some_reindex := nativeExists_substitution

noncomputable def propositions (C : Type u) [Category.{u} C] :
    PropositionOperations (doctrine C) where
  omega := nativeOmega
  quote := nativeQuote
  holds := nativeHolds
  holds_quote := nativeHolds_nativeQuote
  quote_holds := nativeQuote_nativeHolds
  omega_substitution := nativeOmega_reindex
  quote_substitution := nativeQuote_substituteTerm
  holds_substitution substitution term transported related := by
    have same : transported = substituteNative substitution term := eq_of_heq
      (related.symm.trans (cast_heq _ _).symm)
    rw [same]
    exact nativeHolds_substituteNative substitution term

/-- The actual pulled guard proves membership at every source point. -/
theorem guard_membership (predicate : Subfunctor P) (substitution : Q ⟶ P)
    (guard : predicate.preimage substitution = ⊤) (world : Cᵒᵖ) (value : Q.obj world) :
    substitution.app world value ∈ predicate.obj world := by
  have selected : value ∈ (predicate.preimage substitution).obj world := by
    rw [guard]
    trivial
  exact selected

def select (predicate : Subfunctor P) (substitution : Q ⟶ P)
    (guard : predicate.preimage substitution = ⊤) : Q ⟶ predicate.toFunctor where
  app world := TypeCat.ofHom fun value =>
    ⟨substitution.app world value, guard_membership predicate substitution guard world value⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact substitution.naturality_apply arrow value

theorem select_beta (predicate : Subfunctor P) (substitution : Q ⟶ P)
    (guard : predicate.preimage substitution = ⊤) :
    select predicate substitution guard ≫ predicate.ι = substitution := by
  ext world value
  rfl

theorem inclusion_monic (predicate : Subfunctor P) (first second : Q ⟶ predicate.toFunctor)
    (equal : first ≫ predicate.ι = second ≫ predicate.ι) : first = second := by
  ext world value
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (NatTrans.congr_app equal world) value

noncomputable def assumptions (C : Type u) [Category.{u} C] :
    AssumptionOperations (doctrine C) where
  assumed _ predicate := predicate.toFunctor
  inclusion predicate := predicate.ι
  select := select
  select_beta := select_beta
  inclusion_monic := inclusion_monic
  consequence := PresheafPredicateAssumptionLogic.inclusion_top_iff

theorem section_guard_iff (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections) :
    (predicate.preimage (ContextualProductComparison.selfExtend (nativeLocalModel C).toCwf term) = ⊤) ↔
      ∀ world (base : P.obj world),
        (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world := by
  constructor
  · intro guard world base
    exact guard_membership predicate (sectionLift A.decoded term) guard world base
  · intro satisfied
    ext world base
    constructor
    · intro _; trivial
    · intro _
      exact satisfied world base

attribute [local irreducible] PresheafNativeStableRefinement.chosen

noncomputable def refinements (C : Type u) [Category.{u} C] :
    RefinementOperations (doctrine C) where
  refined := chosen
  intro A predicate term guard := intro A predicate term ((section_guard_iff A predicate term).mp guard)
  forget := forget
  forget_guard A predicate term := (section_guard_iff A predicate _).mpr
    (forget_satisfies A predicate term)
  beta A predicate term guard := beta A predicate term _
  eta A predicate term := eta A predicate term
  formation_substitution := chosen_reindex
  intro_substitution substitution A predicate term guard transportedGuard := by
    have computation := introduction_substitution substitution A predicate term
      ((section_guard_iff A predicate term).mp guard)
    have sameGuard : substitutedSatisfaction substitution A predicate term
        ((section_guard_iff A predicate term).mp guard) =
        (section_guard_iff (A.reindex substitution)
          (predicate.preimage (totalReindexMap substitution A.decoded))
          (substituteTerm (C := presheafCwf C) (type := A) term substitution)).mp
            transportedGuard := Subsingleton.elim _ _
    rw [sameGuard] at computation
    exact (cast_heq _ _).symm.trans (heq_of_eq computation)
  forget_substitution substitution A predicate term transported related := by
    have same : HEq (substituteChosen substitution A predicate term) transported :=
      (cast_heq _ _).trans related
    have equal := eq_of_heq same
    rw [← equal]
    exact forget_substitution substitution A predicate term

end Mettapedia.TypeTheory.PresheafNativePredicateCapabilities
