import Mettapedia.OSLF.MeTTaIL.Syntax
import Lean.Elab.Command

/-!
# Ordered base-sort operators

A row supplies a symbol, its result sort, and the ordered names and sorts of
its arguments. The caller's two builders give the pattern constructor and
grammar entry. Both receive the same symbol and argument order, and the
grammar builder retains the caller's lexical and evaluation policy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Lean Elab Command
open Mettapedia.OSLF.MeTTaIL.Syntax

declare_syntax_cat baseSortOperand
syntax "(" ident ":" str ")" : baseSortOperand

declare_syntax_cat baseSortOperator
syntax ident str str "[" baseSortOperand,* "]" : baseSortOperator

/-- Declare pattern constructors and their ordered grammar table from one row list. -/
syntax (name := declareBaseSortOperators) "declare_base_sort_operators " ident
  "(" term "," term ")" "[" baseSortOperator,* "]" : command

elab_rules : command
  | `(command| declare_base_sort_operators $table:ident ($pattern:term, $grammar:term)
        [$rows:baseSortOperator,*]) => do
      let mut rules : Array Term := #[]
      for row in rows.getElems do
        let rule ← withRef row do
          match row with
          | `(baseSortOperator| $name:ident $label:str $category:str [$fields:baseSortOperand,*]) =>
              let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
              let mut arguments : Array Term := #[]
              let mut slots : Array Term := #[]
              let mut names : Array Name := #[]
              for field in fields.getElems do
                match field with
                | `(baseSortOperand| ($parameter:ident : $sort:str)) =>
                    let parameterName := parameter.getId.eraseMacroScopes
                    if names.contains parameterName then
                      throwErrorAt parameter "duplicate operator parameter {parameterName}"
                    names := names.push parameterName
                    binders := binders.push (← `(bracketedBinder| ($parameter : Pattern)))
                    arguments := arguments.push ⟨parameter.raw⟩
                    let fieldName := Syntax.mkStrLit parameterName.toString
                    slots := slots.push (← `(($fieldName, $sort)))
                | _ => throwUnsupportedSyntax
              elabCommand (← `(def $name $binders* : Pattern := $pattern $label [$arguments,*]))
              `($grammar $label $category [$slots,*])
          | _ => throwUnsupportedSyntax
        rules := rules.push rule
      elabCommand (← `(def $table : List GrammarRule := [$rules,*]))

end Mettapedia.GSLT.LanguageDef
