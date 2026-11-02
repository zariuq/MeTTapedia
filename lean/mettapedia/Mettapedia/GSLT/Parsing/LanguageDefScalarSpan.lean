import Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

/-! The source renderer equals the exact scalar interval of every subtree,
not only a complete root. This supports local lexical selection policies. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

open ParserProfileSemantics ClassAwareParserPackCorrespondence

theorem sequence_slice {input points : List Nat} {start stop : Nat}
    (matched : ScalarSequenceMatchesAt input points start stop) :
    (input.drop start).take (stop - start) = points := by
  have length := sequence_length matched
  cases points with
  | nil => simp only [List.length_nil, Nat.add_zero] at length; simp [length]
  | cons first rest =>
    have found := sequence_lookup matched ⟨rest.length, by simp⟩
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
    have bounded : start + (first :: rest).length ≤ input.length := by
      simp only [List.length_cons]
      exact bound
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]
      omega
    · intro position leftBound rightBound
      have found := sequence_lookup matched ⟨position, rightBound⟩
      have sourceBound : start + position < input.length := by omega
      simpa only [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem sourceBound,
        Option.some.injEq] using found

theorem render_slice {literalScalars? : String → Option (List Nat)} {profile : ParserProfileLayer}
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef} {input : List Nat}
    {sort : String} {start stop : Nat} {tree : PresentationExprSemantics.CST}
    (source : LanguageDefScalarSyntax.DerivesAt literalScalars? profile language input sort start stop tree) :
    (input.drop start).take (stop - start) = render source :=
  sequence_slice (render_matches source)

end Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
