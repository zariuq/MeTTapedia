import Mettapedia.GSLT.Parsing.DeclaredConstructorPrinterComposition
import Mettapedia.GSLT.Parsing.GrammarArgumentLayout
import Mathlib.Data.List.Forall2

/-! An authored row's ordered base-sort layout composes successful child
printing into successful row printing. No particular language punctuation or
constructor numbering occurs in this theorem. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

def ArgumentPrintable (language : LanguageDef) (literal : String → List Nat) (lexical : LexicalPrinter)
    (parameter : TermParam) (child : Pattern) : Prop :=
  ∃ name sort, parameter = .simple name (.base sort) ∧ ∃ text, print? language literal lexical sort child = some text

theorem items_total (language : LanguageDef) (literal : String → List Nat) (lexical : LexicalPrinter)
    (row : GrammarRule) (items : List SyntaxItem) (parameters : List TermParam) (children : List Pattern)
    (layout : GrammarArgumentLayout.parameters? row items = some parameters)
    (arguments : List.Forall₂ (ArgumentPrintable language literal lexical) parameters children) :
    ∃ text, printItems? language literal lexical row items children = some text := by
  induction items generalizing parameters children with
  | nil =>
    cases Option.some.inj layout
    cases arguments
    exact ⟨[], by rw [printItems?]⟩
  | cons item rest ih =>
    cases item with
    | terminal token =>
      obtain ⟨text, printed⟩ := ih parameters children layout arguments
      exact ⟨literal token ++ text, by simp [printItems?, printed]⟩
    | nonTerminal parameter =>
      simp only [GrammarArgumentLayout.parameters?] at layout
      obtain ⟨sort, lookup, restLayout⟩ := Option.bind_eq_some_iff.mp layout
      obtain ⟨tail, tailLayout, same⟩ := Option.bind_eq_some_iff.mp restLayout
      cases Option.some.inj same
      cases arguments with
      | cons head rest =>
        obtain ⟨name, childSort, sameParam, text, childRead⟩ := head
        cases sameParam
        obtain ⟨later, laterRead⟩ := ih tail _ tailLayout rest
        exact ⟨text ++ later, by simp [printItems?, lookup, childRead, laterRead]⟩
    | separator _ | delimiter _ _ | op _ => cases layout

end Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter
