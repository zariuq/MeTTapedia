import Mettapedia.Machines.FunctionalCorrespondenceRuns
import Mettapedia.Languages.Lean.CodeEquations.Value

/-!
# Complete source-machine values for differential execution

The observers retain control, environment, continuation, transition count
and outcome. Display instances serve the generated kernel-checked equality
controls; the PeTTa spelling follows the source constructor identities.
-/

namespace Mettapedia.Languages.Lean.CodeEquations

open Mettapedia.Machines

deriving instance Repr for CEK.Val
deriving instance Repr for CEK.Frame
deriving instance Repr for CEK.Ctl
deriving instance Repr for CEK.St
deriving instance Repr for Krivine.NThunk
deriving instance Repr for Krivine.NVal
deriving instance Repr for Krivine.KSt

def renderTm : Tm → String
  | .var n => ctorApp ``Tm.var [render n]
  | .lam body => ctorApp ``Tm.lam [renderTm body]
  | .app function argument => ctorApp ``Tm.app [renderTm function, renderTm argument]
  | .lit n => ctorApp ``Tm.lit [render n]

instance : PeTTaValue Tm := ⟨renderTm⟩

mutual
  def renderCEKValue : CEK.Val → String
    | .lit n => ctorApp ``CEK.Val.lit [render n]
    | .clo term environment => ctorApp ``CEK.Val.clo [render term, renderCEKValues environment]

  def renderCEKValues : List CEK.Val → String
    | [] => ctorSymbol ``List.nil
    | head :: tail => ctorApp ``List.cons [renderCEKValue head, renderCEKValues tail]
end

instance : PeTTaValue CEK.Val := ⟨renderCEKValue⟩

instance : PeTTaValue CEK.Frame where
  render
    | .argOf term environment => ctorApp ``CEK.Frame.argOf [render term, render environment]
    | .callWith value => ctorApp ``CEK.Frame.callWith [render value]

instance : PeTTaValue CEK.Ctl where
  render
    | .ev term environment => ctorApp ``CEK.Ctl.ev [render term, render environment]
    | .ret value => ctorApp ``CEK.Ctl.ret [render value]

instance : PeTTaValue CEK.St where
  render state := ctorApp ``CEK.St.mk [render state.ctl, render state.k]

mutual
  def renderThunk : Krivine.NThunk → String
    | .mk term environment => ctorApp ``Krivine.NThunk.mk [render term, renderThunks environment]

  def renderThunks : List Krivine.NThunk → String
    | [] => ctorSymbol ``List.nil
    | head :: tail => ctorApp ``List.cons [renderThunk head, renderThunks tail]
end

instance : PeTTaValue Krivine.NThunk := ⟨renderThunk⟩

instance : PeTTaValue Krivine.NVal where
  render
    | .lit n => ctorApp ``Krivine.NVal.lit [render n]
    | .clo term environment => ctorApp ``Krivine.NVal.clo [render term, render environment]

instance : PeTTaValue Krivine.KSt where
  render state := ctorApp ``Krivine.KSt.mk [render state.t, render state.ρ, render state.s]

instance : PeTTaValue BoundedDeterministicRun.Outcome where
  render
    | .completed => ctorSymbol ``BoundedDeterministicRun.Outcome.completed
    | .stuck => ctorSymbol ``BoundedDeterministicRun.Outcome.stuck
    | .exhausted => ctorSymbol ``BoundedDeterministicRun.Outcome.exhausted

instance [PeTTaValue State] : PeTTaValue (BoundedDeterministicRun.Result State) where
  render result := ctorApp ``BoundedDeterministicRun.Result.mk
    [render result.state, render result.steps, render result.outcome]

end Mettapedia.Languages.Lean.CodeEquations
