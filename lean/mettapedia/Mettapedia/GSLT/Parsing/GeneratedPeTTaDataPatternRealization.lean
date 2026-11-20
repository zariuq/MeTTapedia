import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternReadback
import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternExecution
import Mettapedia.GSLT.Parsing.GeneratedPeTTaFactMeaning

/-!
# Checked native constructor text reaches its source value

Structural evidence about the actual emitted tree connects to its existing
reader, the source machine's constructor steps, and a finite runner bound.
The connections preserve incoming bindings and arbitrary caller frames.

For whole generic facts this establishes execution of the selector code
extracted from the checked equation. Computed-let selection, fresh clause
activation and the compiler's relational branches remain separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

/-- A successful tree check and successful source reading determine actual
code whose finite execution returns the instantiated source value. -/
theorem checked_run {template emitted : SExpr} {atom : Atom}
    (checked : check template emitted = true)
    (read : SpaceSemantics.readRawExpression template = .ok atom)
    (registry : SpaceSemantics.Program) (base : Unifying.Configuration)
    (bindings : Subst) (valid : Unifying.Idempotent bindings) :
    ∃ code, SpaceSemantics.readRawExpression emitted = .ok code ∧
      ∃ spent, ∀ remaining,
        Unifying.run registry (spent + remaining)
          {base with control := .evaluate bindings code, frames := []} =
        .complete base.state [Unifying.resolve bindings atom] base.input base.output := by
  exact ⟨atomCode atom, checked_read_atomCode checked read,
    atomCode_run registry base bindings valid atom⟩

/-- The same read code returns above saved callers without changing their
frames, the world's state, private code, identity supply, or I/O. -/
theorem checked_under_frames {template emitted : SExpr} {atom : Atom}
    (checked : check template emitted = true)
    (read : SpaceSemantics.readRawExpression template = .ok atom)
    (registry : SpaceSemantics.Program) (base : Unifying.Configuration)
    (bindings : Subst) (valid : Unifying.Idempotent bindings) (frames : List Unifying.Frame) :
    ∃ code, SpaceSemantics.readRawExpression emitted = .ok code ∧
      Relation.ReflTransGen (Unifying.Transition registry)
        {base with control := .evaluate bindings code, frames}
        {base with control := .returned [⟨Unifying.resolve bindings atom, bindings⟩], frames} := by
  exact ⟨atomCode atom, checked_read_atomCode checked read,
    atomCode_under_frames registry base bindings valid atom frames⟩

#print axioms checked_run
#print axioms checked_under_frames

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

/-- Read and execute the selector actually extracted from a whole checked
native equation. Both its result and its finite bound come from the source
head, while the untrusted payload supplies the code being read. -/
theorem checked_source_selector_run {source emitted selector echo : SExpr}
    (checked : checkSource source emitted = true)
    (parts : bodyParts? emitted = some (selector, echo))
    (registry : SpaceSemantics.Program) (base : Unifying.Configuration)
    (bindings : Subst) (valid : Unifying.Idempotent bindings) :
    ∃ atom code, SpaceSemantics.readRawExpression source = .ok atom ∧
      SpaceSemantics.readRawExpression selector = .ok code ∧
      ∃ spent, ∀ remaining,
        Unifying.run registry (spent + remaining)
          {base with control := .evaluate bindings code, frames := []} =
        .complete base.state [Unifying.resolve bindings atom] base.input base.output := by
  obtain ⟨head, syntaxChecked, atom, sourceRead, headRead⟩ :=
    (checkSource_iff source emitted).1 checked
  have selectorExact := (checked_parts_exact syntaxChecked parts).1
  obtain ⟨code, codeRead, bound⟩ := GeneratedPeTTaDataPattern.checked_run
    (GeneratedPeTTaDataPattern.check_encode head) headRead registry base bindings valid
  exact ⟨atom, code, sourceRead, selectorExact ▸ codeRead, bound⟩

#print axioms checked_source_selector_run

end Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax
