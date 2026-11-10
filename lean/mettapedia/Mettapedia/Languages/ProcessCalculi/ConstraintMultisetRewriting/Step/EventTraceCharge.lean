import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTraceRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Charge

/-!
# Charge readouts through the actual event/trace map

Additive totals descend when their grades respect transport, alikeness and
residuals. Conserved net flux needs only invariance of the state potential.
Both readouts recover the existing run computations after interpreting the
complete admitted-event path.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI uA

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

namespace Transport.Trace

local instance : Category T.StateClass := T.traceCategory

section Totals

variable {A : Type uA} [AddCommMonoid A]
  (flux : (s : State) → Firing s → A)
  (move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s), flux t (T.move i f) = flux s f)
  (alike : ∀ {s : State} {f g : Firing s}, T.Alike f g → flux s f = flux s g)
  (residual : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
    flux _ (T.residual g admitted f) = flux s f)

include move alike residual in
theorem total_respects {x y : T.StateClass} (first second : T.Arrow x y)
    (related : Arrow.Rel first second) : first.run.total flux = second.run.total flux := by
  obtain ⟨middle, similar, equivalent⟩ := related
  have same := Similar.account_eq (fun state firing => Multiplicative.ofAdd (flux state firing))
    (fun i firing => congrArg Multiplicative.ofAdd (move i firing))
    (fun h => congrArg Multiplicative.ofAdd (alike h)) similar
  rw [← Step.Run.ofAdd_total, ← Step.Run.ofAdd_total] at same
  exact (Multiplicative.ofAdd.injective same).trans
    (Step.Run.traceEquiv_total flux move alike residual equivalent)

def total {x y : T.StateClass} : T.Trace x y → A :=
  observe T (fun arrow => arrow.run.total flux) (total_respects T flux move alike residual)

theorem total_eventTrace_run {s : State} (run : P.Run s) :
    total T flux move alike residual (T.eventTraceFunctor.map (run.eventPath P)) = run.total flux :=
  Transport.observation_eventTrace_run T run _ (total_respects T flux move alike residual)

end Totals

section Net

variable {A : Type uA} [AddCommGroup A] (charge : ConservedCharge P A) (invariant : charge.Invariant T)

include invariant in
theorem net_same_classes {x y : T.StateClass} (first second : T.Arrow x y) :
    charge.runMade first.run - charge.runTaken first.run =
      charge.runMade second.run - charge.runTaken second.run := by
  have starts := invariant ((StateClass.mk_eq_mk_iff T).mp (first.start_mem.trans second.start_mem.symm))
  have ends := invariant ((StateClass.mk_eq_mk_iff T).mp (first.last_mem.trans second.last_mem.symm))
  rw [charge.potential_last first.run, charge.potential_last second.run, starts,
    add_sub_assoc, add_sub_assoc] at ends
  exact add_left_cancel ends

def net {x y : T.StateClass} : T.Trace x y → A :=
  observe T (fun arrow => charge.runMade arrow.run - charge.runTaken arrow.run)
    (fun first second _ => net_same_classes T charge invariant first second)

theorem net_eventTrace_run {s : State} (run : P.Run s) :
    net T charge invariant (T.eventTraceFunctor.map (run.eventPath P)) =
      charge.runMade run - charge.runTaken run :=
  Transport.observation_eventTrace_run T run _ (fun first second _ => net_same_classes T charge invariant first second)

end Net

end Transport.Trace

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
