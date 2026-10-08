import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
import MeTTailCore.Crypto.SHA256
import Lean.Elab.Term

/-!
# Pinned S-expression source quotation

This elaborator checks a retained file's digest and passes the same byte
string to the existing S-expression quotation. The expansion consists of
ordinary data constructors. Source reading and digest computation remain
elaboration boundaries; the digest supplies no semantic judgment.

Quoting modules must register their retained files as Lake inputs.
-/

namespace Mettapedia.OSLF.MeTTaIL.MeTTaPinnedSourceQuotation

meta section

open Lean Elab Term
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

private def elaboratePinnedFile (petta : Bool) (path pin : TSyntax `str)
    (expectedType : Expr) : TermElabM Expr := do
  let context ← readThe Lean.Core.Context
  let some parent := (System.FilePath.mk context.fileName).parent
    | throwErrorAt path "cannot locate the quoting module"
  let contents ← IO.FS.readFile (parent / path.getString)
  unless MeTTailCore.Crypto.SHA256.sha256Hex contents = pin.getString do
    throwErrorAt pin "source digest differs from the pinned artifact"
  let literal : TSyntax `str := ⟨Syntax.mkStrLit contents⟩
  let quoted ← if petta then `(metta_sexpr% petta $literal:str)
    else `(metta_sexpr% he $literal:str)
  let expanded ← withEnv (← getEnv) do
    activateScoped `Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
    let some expanded ← liftMacroM (expandMacro? quoted)
      | throwErrorAt path "S-expression quotation could not expand"
    pure expanded
  elabTerm expanded expectedType

scoped syntax "metta_sexpr_pinned_file% " (&"petta" <|> &"he") str " sha256 " str : term

elab_rules : term <= expectedType
  | `(metta_sexpr_pinned_file% petta $path:str sha256 $pin:str) =>
      elaboratePinnedFile true path pin expectedType
  | `(metta_sexpr_pinned_file% he $path:str sha256 $pin:str) =>
      elaboratePinnedFile false path pin expectedType

end

end Mettapedia.OSLF.MeTTaIL.MeTTaPinnedSourceQuotation
