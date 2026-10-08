import Mettapedia.TypeTheory.PresheafNativePropositionReadout
import Mettapedia.TypeTheory.NativeLocalTypeOperations

/-!
# Substitution of actual native proposition terms

The fixed ordinary native proposition type makes its chosen type stable
under substitution. The term action below is the actual local CwF term
substitution, transported across that earned type equality. Its quote and
holds operations commute with predicate inverse image.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePropositionSubstitution

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers PresheafNativePropositionReadout

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

private theorem castSection_value {P : Cᵒᵖ ⥤ Type u}
    {A B : DisplayedFamily P} (same : A = B) (term : A.sections) (point : P.Elements) :
    HEq ((cast (congrArg (fun family : DisplayedFamily P => ↥family.sections) same) term).val point)
      (term.val point) := by
  cases same
  rfl

private theorem sections_heq {P : Cᵒᵖ ⥤ Type u}
    {A B : DisplayedFamily P} (same : A = B) (first : A.sections) (second : B.sections)
    (values : ∀ point, HEq (first.val point) (second.val point)) : HEq first second := by
  cases same
  apply heq_of_eq
  apply (Functor.sections_ext_iff).2
  intro point
  exact eq_of_heq (values point)

theorem nativeQuote_value (predicate : Subfunctor P) (point : P.Elements) :
    HEq ((nativeQuote predicate).val point) ((quote predicate).val point) := by
  exact castSection_value (nativeOmega_decode P).symm (quote predicate) point

theorem nativeQuote_substituteTerm (substitution : Q ⟶ P) (predicate : Subfunctor P) :
    HEq (substituteTerm (C := presheafCwf C) (type := nativeOmega P) (nativeQuote predicate) substitution)
      (nativeQuote (predicate.preimage substitution)) := by
  apply sections_heq (congrArg (fun type : NativeType Q => type.decoded)
    (nativeOmega_reindex substitution))
  intro point
  have nativeSub := NativeLocalTypeOperations.substituteTerm_value
    (nativeOmega P) (nativeQuote predicate) substitution point
  have source := nativeQuote_value predicate (substitution.mapElements.obj point)
  have displaySub := congrArg (fun term : PropositionTerm Q => term.val point)
    (substituteProposition_quote substitution predicate)
  have target := nativeQuote_value (predicate.preimage substitution) point
  exact nativeSub.trans (source.trans ((heq_of_eq displaySub).trans target.symm))

def substituteNative (substitution : Q ⟶ P) (term : (nativeOmega P).decoded.sections) :
    (nativeOmega Q).decoded.sections :=
  cast (congrArg (fun type : NativeType Q => ↥type.decoded.sections)
    (nativeOmega_reindex substitution)) (substituteTerm (C := presheafCwf C) (type := nativeOmega P) term substitution)

theorem substituteNative_quote (substitution : Q ⟶ P) (predicate : Subfunctor P) :
    substituteNative substitution (nativeQuote predicate) =
      nativeQuote (predicate.preimage substitution) := by
  apply eq_of_heq
  exact (cast_heq _ _).trans (nativeQuote_substituteTerm substitution predicate)

theorem nativeHolds_substituteNative (substitution : Q ⟶ P)
    (term : (nativeOmega P).decoded.sections) :
    nativeHolds (substituteNative substitution term) = (nativeHolds term).preimage substitution := by
  conv_lhs => rw [← nativeQuote_nativeHolds term]
  rw [substituteNative_quote, nativeHolds_nativeQuote]

end Mettapedia.TypeTheory.PresheafNativePropositionSubstitution
