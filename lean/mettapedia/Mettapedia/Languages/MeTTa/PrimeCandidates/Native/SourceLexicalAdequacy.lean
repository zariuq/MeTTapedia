import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionCover

/-!
# Named lexical bindings as a separate executable source profile

The source owner is `TemplateScope`: named lexical scopes, crossing sets,
lambda application, quotations and ground-store refinement. Its existing
scope translation inserts explicit lexical introductions and crossings into
the complete query and equation bodies. The target runs those independently
elaborated forms with the lexical-fresh evaluator.

The two directions below retain the full result list and final stores at each
fuel bound, including failure to finish. They preserve the selected matching
direction. This is not a translation into the call-time-choice heap machine:
the ground-store model cannot represent arbitrary aliases between two distinct
unbound names, and its demand policy is not that machine's policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceLexicalAdequacy

open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v
variable {Symbol : Type u} {Name : Type v} [DecidableEq Symbol] [DecidableEq Name]

/-- The target query is scope-elaborated after the explicit source
translation. Equation bodies undergo the same transformation at their own
roots, rather than borrowing the query's variable identities. -/
def execute (direction : Direction) (discipline : Disc) (parameter : Name) (unit : Symbol)
    (equations : Symbol → Option (Src Symbol Name)) (query : Src Symbol Name)
    (fuel : Nat) (path : Path) (store : GStore Symbol (BId Name)) :=
  runDir direction discipline (progLF parameter unit (toLexicalProg equations))
    fuel path store (elabLFFormAt [] (toLexical query))

/-- Both directions compare real executions, including multiplicity and each
branch's bindings. A source timeout remains a timeout at the same bound. -/
theorem execution_exact (direction : Direction) (discipline : Disc)
    (parameter : Name) (unit : Symbol)
    (equations : Symbol → Option (Src Symbol Name)) (query : Src Symbol Name)
    (fuel : Nat) (path : Path) (store : GStore Symbol (BId Name)) :
    execute direction discipline parameter unit equations query fuel path store =
      runDir direction discipline (progM parameter unit equations)
        fuel path store (elabMFormAt [] query) :=
  runDir_toLexical direction parameter unit equations query discipline fuel path store

theorem execution_iff (direction : Direction) (discipline : Disc)
    (parameter : Name) (unit : Symbol)
    (equations : Symbol → Option (Src Symbol Name)) (query : Src Symbol Name)
    (fuel : Nat) (path : Path) (store : GStore Symbol (BId Name))
    (results : Result Symbol (BId Name)) :
    execute direction discipline parameter unit equations query fuel path store = some results ↔
      runDir direction discipline (progM parameter unit equations)
        fuel path store (elabMFormAt [] query) = some results := by
  rw [execution_exact]

/-- The translation may be applied around an arbitrary enclosing source
context. The enclosing form is re-elaborated as a whole, since ownership is
context-dependent; independent elaboration of its hole is not assumed. -/
theorem contextual_execution_exact (direction : Direction) (discipline : Disc)
    (parameter : Name) (unit : Symbol)
    (equations : Symbol → Option (Src Symbol Name))
    (context : Src Symbol Name → Src Symbol Name) (query : Src Symbol Name)
    (fuel : Nat) (path : Path) (store : GStore Symbol (BId Name)) :
    execute direction discipline parameter unit equations (context query) fuel path store =
      runDir direction discipline (progM parameter unit equations)
        fuel path store (elabMFormAt [] (context query)) :=
  execution_exact direction discipline parameter unit equations (context query) fuel path store

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceLexicalAdequacy
