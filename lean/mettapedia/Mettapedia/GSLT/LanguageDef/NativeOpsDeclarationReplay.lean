import Mettapedia.Data.List.OptionMapMReflection
import Mettapedia.GSLT.LanguageDef.NativeOpsAdmissionLaws
import Lean.Elab.Command

/-! Compose checked declaration rows in their authored order. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsDeclarationReplay

open Lean Elab Command
open NativeOps
open Mettapedia.Data.List (option_mapM_cons_of_some)

private def ref (anchor : Syntax) (stem : String) (index : Nat) (suffix := "") : Ident :=
  let digits := toString index
  let padded := String.ofList (List.replicate (3 - digits.length) '0') ++ digits
  mkIdentFrom anchor (Name.mkSimple (stem ++ "_" ++ padded ++ suffix))

/-- Compose the half-open interval of declaration receipts. Its upper endpoint
must already have a checked suffix. -/
syntax (name := declarationSuffix) "native_declaration_suffix " num " to " num : command

elab_rules : command
  | `(command| native_declaration_suffix $first:num to $last:num) => do
      unless first.getNat ≤ last.getNat do
        throwErrorAt first "expected first ≤ last"
      for index in (List.range' first.getNat (last.getNat - first.getNat)).reverse do
        let item := ref first "syntax" index
        let produced := ref first "declaration" index
        let input := ref first "syntaxTail" index
        let inputTail := ref first "syntaxTail" (index + 1)
        let output := ref first "declarationTail" index
        let outputTail := ref first "declarationTail" (index + 1)
        let head := ref first "declaration" index "_exact"
        let tail := ref first "tail" (index + 1) "_exact"
        let proof := ref first "tail" index "_exact"
        let catalogue := mkIdentFrom first `primitiveCatalogue
        elabCommand (← `(def $input := $item :: $inputTail))
        elabCommand (← `(def $output := $produced :: $outputTail))
        elabCommand (← `(theorem $proof : ($input).mapM (declaration? $catalogue) = some $output :=
          option_mapM_cons_of_some (declaration? $catalogue) $head $tail))

end Mettapedia.GSLT.LanguageDef.NativeOpsDeclarationReplay
