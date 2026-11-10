import Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
import Mathlib.Data.List.TakeDrop

/-! # Determinism from authored leading terminal sequences

A sufficient condition for a structural scalar grammar is that distinct
productions of the same sort have incomparable leading terminal spellings.
The condition is checked on the authored rows, before parser compilation.
It is a qualification of this profile, not a restriction on other grammars.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefScalarDeterminism

open Mettapedia.OSLF.MeTTaIL.Syntax
open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence LanguageDefScalarSyntax LanguageDefScalarPrinter

def leading (literalScalars : String → Option (List Nat)) : List SyntaxItem → List Nat
  | .terminal token :: rest => (literalScalars token).getD [] ++ leading literalScalars rest
  | _ => []

/-- Different row occurrences must be distinguishable within each sort.
Equal labels alone do not identify production occurrences. -/
def Separated (literalScalars : String → Option (List Nat)) (language : LanguageDef) : Prop :=
  ∀ first second : Fin language.terms.length,
    language.terms[first].category = language.terms[second].category →
    ((leading literalScalars language.terms[first].syntaxPattern).IsPrefix
        (leading literalScalars language.terms[second].syntaxPattern) ∨
      (leading literalScalars language.terms[second].syntaxPattern).IsPrefix
        (leading literalScalars language.terms[first].syntaxPattern)) → first = second

variable {literalScalars : String → Option (List Nat)} {profile : ParserProfileLayer}
  {language : LanguageDef} {input : List Nat}

theorem sequence_prefix {points : List Nat} {start stop : Nat}
    (matched : ScalarSequenceMatchesAt input points start stop) :
    points.IsPrefix (input.drop start) := by
  induction matched with
  | nil => exact List.nil_prefix
  | @cons start point points stop lookup _ ih =>
      have bound : start < input.length := List.getElem?_eq_some_iff.mp lookup |>.1
      have value : input[start] = point := List.getElem?_eq_some_iff.mp lookup |>.2
      rw [List.drop_eq_getElem_cons bound, value]
      obtain ⟨suffix, same⟩ := ih
      exact ⟨suffix, by simp only [List.cons_append, same]⟩

theorem leading_matches {rule : GrammarRule} {items : List SyntaxItem}
    {start stop : Nat} {children : List CST}
    (body : ItemsDeriveAt literalScalars profile language input rule items start stop children) :
    ∃ middle, Nonempty (ScalarSequenceMatchesAt input (leading literalScalars items) start middle) := by
  match body with
  | .nil => exact ⟨_, ⟨.nil _⟩⟩
  | .terminal decoded matched rest =>
      obtain ⟨middle, ⟨suffix⟩⟩ := leading_matches rest
      refine ⟨middle, ⟨?_⟩⟩
      simpa only [leading, decoded, Option.getD_some] using sequence_append matched suffix
  | .nonterminal _ _ _ => exact ⟨_, ⟨.nil _⟩⟩
termination_by structural body

theorem same_row (separated : Separated literalScalars language)
    {first second : Fin language.terms.length} {start stop₁ stop₂ : Nat}
    {children₁ children₂ : List CST}
    (sameSort : language.terms[first].category = language.terms[second].category)
    (left : ItemsDeriveAt literalScalars profile language input language.terms[first]
      language.terms[first].syntaxPattern start stop₁ children₁)
    (right : ItemsDeriveAt literalScalars profile language input language.terms[second]
      language.terms[second].syntaxPattern start stop₂ children₂) : first = second := by
  obtain ⟨_, ⟨prefix₁⟩⟩ := leading_matches left
  obtain ⟨_, ⟨prefix₂⟩⟩ := leading_matches right
  exact separated first second sameSort
    (List.prefix_or_prefix_of_prefix (sequence_prefix prefix₁) (sequence_prefix prefix₂))

mutual
  theorem unique (noLexical : profile.states = [])
      (separated : Separated literalScalars language)
      {sort₁ sort₂ : String} {start₁ start₂ stop₁ stop₂ : Nat} {tree₁ tree₂ : CST}
      (first : DerivesAt literalScalars profile language input sort₁ start₁ stop₁ tree₁)
      (second : DerivesAt literalScalars profile language input sort₂ start₂ stop₂ tree₂)
      (sameSort : sort₁ = sort₂) (sameStart : start₁ = start₂) :
      stop₁ = stop₂ ∧ tree₁ = tree₂ := by
    match first with
    | .lexical row _ _ =>
        have impossible := row.isLt
        simp only [noLexical, List.length_nil] at impossible
        exact False.elim (Nat.not_lt_zero _ impossible)
    | .structural row body =>
        cases second with
        | lexical other _ _ =>
            have impossible := other.isLt
            simp only [noLexical, List.length_nil] at impossible
            exact False.elim (Nat.not_lt_zero _ impossible)
        | structural other rest =>
            subst start₂
            have same := same_row separated sameSort body rest
            subst other
            obtain ⟨rfl, rfl⟩ := unique_items noLexical separated body rest rfl rfl rfl
            exact ⟨rfl, rfl⟩
    termination_by structural first

  theorem unique_items (noLexical : profile.states = [])
      (separated : Separated literalScalars language)
      {rule₁ rule₂ : GrammarRule} {items₁ items₂ : List SyntaxItem}
      {start₁ start₂ stop₁ stop₂ : Nat} {trees₁ trees₂ : List CST}
      (first : ItemsDeriveAt literalScalars profile language input rule₁ items₁ start₁ stop₁ trees₁)
      (second : ItemsDeriveAt literalScalars profile language input rule₂ items₂ start₂ stop₂ trees₂)
      (sameRule : rule₁ = rule₂) (sameItems : items₁ = items₂) (sameStart : start₁ = start₂) :
      stop₁ = stop₂ ∧ trees₁ = trees₂ := by
    subst rule₂
    subst items₂
    subst start₂
    match first with
    | .nil => cases second; exact ⟨rfl, rfl⟩
    | .terminal decoded matched rest =>
        cases second with
        | terminal decoded₂ matched₂ rest₂ =>
            have samePoints := Option.some.inj (decoded.symm.trans decoded₂)
            cases samePoints
            have sameMiddle := (sequence_length matched).trans (sequence_length matched₂).symm
            cases sameMiddle
            exact unique_items noLexical separated rest rest₂ rfl rfl rfl
    | .nonterminal lookup head rest =>
        cases second with
        | nonterminal lookup₂ head₂ rest₂ =>
            have sameSort := Option.some.inj (lookup.symm.trans lookup₂)
            obtain ⟨sameMiddle, sameTree⟩ := unique noLexical separated head head₂ sameSort rfl
            cases sameMiddle
            cases sameTree
            obtain ⟨rfl, rfl⟩ := unique_items noLexical separated rest rest₂ rfl rfl rfl
            exact ⟨rfl, rfl⟩
    termination_by structural first
end

#print axioms unique

end Mettapedia.GSLT.Parsing.LanguageDefScalarDeterminism
