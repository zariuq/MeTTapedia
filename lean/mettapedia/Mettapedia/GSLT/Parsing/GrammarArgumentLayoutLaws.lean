import Mettapedia.GSLT.Parsing.GrammarArgumentLayout
import Mettapedia.GSLT.LanguageDef.WellSorted

/-! Authored scalar syntax contributes only simple base-sort arguments.
A successful complete layout therefore cannot be a bare collection row. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarArgumentLayout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef.WellSorted

def isBaseParameter : TermParam → Bool
  | .simple _ (.base _) => true
  | _ => false

theorem parameters_only_base (rule : GrammarRule) (items : List SyntaxItem) (expected : List TermParam)
    (layout : parameters? rule items = some expected) : expected.all isBaseParameter = true := by
  induction items generalizing expected with
  | nil => cases layout; rfl
  | cons item items ih =>
    cases item with
    | terminal token => exact ih expected layout
    | nonTerminal name =>
      cases found : paramSort? rule name with
      | none => simp [parameters?, found] at layout
      | some sort =>
        cases tail : parameters? rule items with
        | none => simp [parameters?, found, tail] at layout
        | some rest =>
          simp [parameters?, found, tail] at layout
          subst expected
          simpa only [List.all_cons, isBaseParameter, Bool.true_and] using ih rest tail
    | separator _ | delimiter _ _ | op _ => cases layout

theorem not_bare_of_parameters (rule : GrammarRule)
    (layout : parameters? rule rule.syntaxPattern = some rule.params) : ¬ UsesBareCollection rule := by
  rintro ⟨name, kind, type, bare⟩
  cases representation : rule.collectionRepresentation with
  | wrapped => simp [GrammarRule.bareParams, representation] at bare
  | bare =>
    have same : rule.params = [.simple name (.collection kind type)] := by
      simpa only [GrammarRule.bareParams, representation] using bare
    have checked := parameters_only_base rule rule.syntaxPattern rule.params layout
    rw [same] at checked
    cases checked

#print axioms parameters_only_base
#print axioms not_bare_of_parameters

end Mettapedia.GSLT.Parsing.GrammarArgumentLayout
