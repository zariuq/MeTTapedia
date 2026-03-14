import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef

/-!
# Kernel-Checked Tests for MeTTaFull Language Definition

These theorems verify that the MeTTaFull rewrite engine produces correct
normal forms for specific inputs. They are in a separate file from
`FullLanguageDef.lean` so that `decide +kernel` can efficiently reduce
imported (compiled) definitions — kernel reduction on definitions in the
same file is dramatically slower.

All proofs use `decide +kernel`, which performs reduction entirely in
the Lean kernel (no `trustCompiler` axiom, unlike `native_decide`).
-/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef

namespace Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageTests

private def aFalse : Pattern := .apply "AFalse" []
private def space0 : Pattern := Mettapedia.Languages.MeTTa.OSLFCore.Premises.space0Pattern
private def gStringCodes (codes : List String) : Pattern :=
  .apply "GStringCodes" [codes.foldr (fun tok acc => .apply "ACons" [.apply tok [], acc]) (.apply "ANil" [])]
private def iGrounded2 (op lhs rhs : Pattern) : Pattern := .apply "Grounded2" [op, lhs, rhs]
private def mkState (instr : Pattern) (space : Pattern := space0) (out : Pattern := aFalse) : Pattern :=
  .apply "State" [instr, space, out]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Coded-string concat "hi " ++ "there" = "hi there".
    Kernel-checked: `decide +kernel` uses the Lean kernel for reduction
    (no `trustCompiler` axiom), unlike `native_decide` which bypasses kernel checking. -/
theorem coded_string_concat_normalForm_shape :
    fullRewriteToNormalFormWithPremisesUsing mettaFullRelEnv mettaFull
      (mkState
        (iGrounded2 (.apply "concat" [])
          (gStringCodes ["104", "105", "32"])
          (gStringCodes ["116", "104", "101", "114", "101"]))
        space0 aFalse) 8
    =
      .apply "State"
        [ .apply "Done" []
        , space0
        , gStringCodes ["104", "105", "32", "116", "104", "101", "114", "101"]
        ] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageTests
