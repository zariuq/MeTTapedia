import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticContextReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalRankedSoundness

/-!
# Realization of formed ordered declarations in the source model

Each primitive header is interpreted using only meanings of earlier symbols.
The supplied formation trees and their node bounds justify this restricted
soundness step. The complete source readouts then identify its actual context
and result with the independently constructed primitive meanings. Rank
induction earns all declaration-local realization equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticModel

open SyntacticReification

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem type_header_realized (headers : HeaderFormation D) (symbol : S.TypeSymbol)
    (earlier : BoundedRealization (data headers) D (D.typeRank symbol)) :
    (data headers).evaluateContext (D.typeParameters symbol) =
      some ((data headers).typeParameters symbol) := by
  have interpreted := (headers.typeHeader symbol).sound_before (data headers) earlier
    (products_substitution headers) (products_beta headers) (products_eta headers)
    (headers.typeHeader_before symbol)
  rcases interpreted with ⟨context, read⟩
  have same := context_evaluation_normalized headers (D.typeParameters symbol)
    (typeHeader headers symbol).formed context read
  exact read.trans (congrArg some same)

theorem term_header_realized (headers : HeaderFormation D) (symbol : S.TermSymbol)
    (earlier : BoundedRealization (data headers) D (D.termRank symbol)) :
    (data headers).evaluateContext (D.termParameters symbol) =
      some ((data headers).termParameters symbol) := by
  have interpreted := (headers.termHeader symbol).sound_before (data headers) earlier
    (products_substitution headers) (products_beta headers) (products_eta headers)
    (headers.termHeader_before symbol)
  rcases interpreted with ⟨context, read⟩
  have same := context_evaluation_normalized headers (D.termParameters symbol)
    (termHeader headers symbol).formed context read
  exact read.trans (congrArg some same)

set_option backward.isDefEq.respectTransparency false in
theorem term_result_realized (headers : HeaderFormation D) (symbol : S.TermSymbol)
    (earlier : BoundedRealization (data headers) D (D.termRank symbol)) :
    (data headers).evaluateType ((data headers).termParameters symbol) (D.termResult symbol) =
      some ((data headers).termType symbol) := by
  have interpreted := (headers.termResult symbol).sound_before (data headers) earlier
    (products_substitution headers) (products_beta headers) (products_eta headers)
    (headers.termResult_before symbol)
  rcases interpreted with ⟨context, value, contextRead, typeRead⟩
  have contexts := context_evaluation_normalized headers (D.termParameters symbol)
    (termHeader headers symbol).formed context contextRead
  change context = (data headers).termParameters symbol at contexts
  cases contexts
  have same := type_evaluation_class headers ((data headers).termParameters symbol)
    (D.termResult symbol) (rawResult headers symbol) HEq.rfl value typeRead
  exact typeRead.trans (congrArg some same)

theorem bounded_realization (headers : HeaderFormation D) :
    ∀ bound, BoundedRealization (data headers) D bound := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound previous =>
      constructor
      · intro symbol earlier
        exact type_header_realized headers symbol (previous (D.typeRank symbol) earlier)
      · intro symbol earlier
        exact term_header_realized headers symbol (previous (D.termRank symbol) earlier)
      · intro symbol earlier
        exact term_result_realized headers symbol (previous (D.termRank symbol) earlier)

theorem realization (headers : HeaderFormation D) : SignatureRealization (data headers) D where
  typeHeader symbol := type_header_realized headers symbol
    (bounded_realization headers (D.typeRank symbol))
  termHeader symbol := term_header_realized headers symbol
    (bounded_realization headers (D.termRank symbol))
  termResult symbol := term_result_realized headers symbol
    (bounded_realization headers (D.termRank symbol))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticModel
