import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

/-!
# Marking the existing scoped process syntax

This construction follows the complete constructor tree of its supplied
process. Each prefix and private binder receives the specified default mark;
the process retains all of its actual names, fields and suspended bodies.
The generic fit theorem supplies the shape evidence used by actual structural
transport and selected communication inversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

def mark {Label : Type} (origin : Label) : {Γ : Ctx sig} → Proc Γ → ActiveMarking.Tree Label
  | _, .var _ => .var
  | _, .op .nil .nil => .nil
  | _, .op .par (.cons first (.cons second .nil)) => .par (mark origin first) (mark origin second)
  | _, .op .inp1 (.cons _ (.cons body .nil)) => .inp1 origin (mark origin body)
  | _, .op .inp2 (.cons _ (.cons body .nil)) => .inp2 origin (mark origin body)
  | _, .op .out1 (.cons _ (.cons _ .nil)) => .out1 origin
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => .out2 origin
  | _, .op .nu (.cons body .nil) => .nu origin (mark origin body)
  | _, .op .rep (.cons body .nil) => .rep (mark origin body)
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem mark_fits {Label : Type} (origin : Label) : ∀ {Γ : Ctx sig} (process : Proc Γ),
    Fits (mark origin process) process
  | _, .var name => by simpa only [mark] using Fits.var (Label := Label) name
  | _, .op .nil .nil => by simpa only [mark, nil] using (Fits.nil (Label := Label))
  | _, .op .par (.cons first (.cons second .nil)) => by
      simpa only [mark, par] using Fits.par (mark_fits origin first) (mark_fits origin second)
  | _, .op .inp1 (.cons channel (.cons body .nil)) => by
      simpa only [mark, inp1] using Fits.inp1 origin channel (mark_fits origin body)
  | _, .op .inp2 (.cons channel (.cons body .nil)) => by
      simpa only [mark, inp2] using Fits.inp2 origin channel (mark_fits origin body)
  | _, .op .out1 (.cons channel (.cons datum .nil)) => by
      simpa only [mark, out1] using Fits.out1 origin channel datum
  | _, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      simpa only [mark, out2] using Fits.out2 origin channel first second
  | _, .op .nu (.cons body .nil) => by
      simpa only [mark, nu] using Fits.nu origin (mark_fits origin body)
  | _, .op .rep (.cons body .nil) => by
      simpa only [mark, rep] using Fits.rep (mark_fits origin body)
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking
