import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterchangeTrace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Cells

/-!
# Moving one admitted event past a complete native run

Each crossing checks the two actual residual admissions. Local closing witnesses
transport the continuation between the resulting frames. The
construction yields two real executions and their trace interchange; it does
not require literal equality of the frames or final native states.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

inductive Crossing : {s : State} → P.Run s → (g : Firing s) → P.Admits g → Type (max uS uF)
  | nil {s : State} (g : Firing s) (admitted : P.Admits g) : Crossing (.nil s) g admitted
  | cons {s : State} {f : Firing s} {first : P.Admits f} {rest : P.Run (P.result f first)}
      {g : Firing s} {second : P.Admits g}
      (afterSecond : P.Admits (T.residual g second f))
      (afterFirst : P.Admits (T.residual f first g))
      (tail : Crossing rest (T.residual f first g) afterFirst) :
      Crossing (.cons f first rest) g second

structure Exchange {s : State} (run : P.Run s) (g : Firing s) (admitted : P.Admits g) where
  residualFiring : Firing run.last
  residualAdmitted : P.Admits residualFiring
  residualRun : P.Run (P.result g admitted)
  interchange : T.TraceEquiv s (.cons g admitted residualRun)
    (run.append (.cons residualFiring residualAdmitted (.nil _)))

variable {T}

theorem Independent.residual_permissions {s : State} {f g : Firing s}
    (independent : T.Independent s f g) (first : P.Admits f) (second : P.Admits g) :
    P.Admits (T.residual f first g) ∧ P.Admits (T.residual g second f) := by
  obtain ⟨_, _, afterFirst, afterSecond, _⟩ := independent
  exact ⟨afterFirst, afterSecond⟩

def Crossing.single {s : State} {f g : Firing s} (independent : T.Independent s f g)
    (first : P.Admits f) (second : P.Admits g) : T.Crossing (.cons f first (.nil _)) g second :=
  .cons (independent.residual_permissions first second).2
    (independent.residual_permissions first second).1 (.nil _ _)

def Crossing.Closings : ∀ {s : State} {run : P.Run s} {g : Firing s} {admitted : P.Admits g},
    T.Crossing run g admitted → Type (max uS uF uI)
  | _, _, _, _, .nil _ _ => PUnit
  | _, .cons f first _, g, second, .cons afterSecond afterFirst tail =>
      T.Iso (P.result (T.residual g second f) afterSecond)
        (P.result (T.residual f first g) afterFirst) × tail.Closings

def Crossing.exchangeWith : ∀ {s : State} {run : P.Run s}
    {g : Firing s} {admitted : P.Admits g} (crossing : T.Crossing run g admitted),
      crossing.Closings → T.Exchange run g admitted
  | _, _, _, _, .nil g admitted, _ => ⟨g, admitted, .nil _, .refl _⟩
  | s, .cons f first rest, g, second, .cons afterSecond afterFirst tail, ⟨square, tailClosings⟩ => by
      let later := tail.exchangeWith tailClosings
      let carried := T.moveRun (T.symm square) later.residualRun
      refine ⟨later.residualFiring, later.residualAdmitted,
        .cons (T.residual g second f) afterSecond carried, ?_⟩
      have swap : T.TraceEquiv s
          (.cons g second (.cons (T.residual g second f) afterSecond carried))
          (.cons f first (.cons (T.residual f first g) afterFirst (T.moveRun square carried))) :=
        .rel _ _ (.inl (Interchange.here second first afterSecond afterFirst square carried).toSwap)
      have returned : T.Similar (T.moveRun square carried) later.residualRun :=
        Similar.trans (Similar.symm (Similar.moveRun square carried))
          (Similar.symm (Similar.moveRun (T.symm square) later.residualRun))
      exact .trans _ _ _ swap (.trans _ _ _
        (.rel _ _ (.inr (Similar.cons_self (Similar.cons_self returned)))) later.interchange.cons)

/-- A profile-wide closing certificate supplies all the required local witnesses. -/
def Crossing.closingsFromGlobal (close : T.Closing) : ∀ {s : State} {run : P.Run s}
    {g : Firing s} {admitted : P.Admits g} (crossing : T.Crossing run g admitted), crossing.Closings
  | _, _, _, _, .nil _ _ => PUnit.unit
  | _, .cons _f first _, _g, second, .cons afterSecond afterFirst tail =>
      ⟨close second first afterSecond afterFirst, tail.closingsFromGlobal close⟩

def Crossing.exchange (close : T.Closing) {s : State} {run : P.Run s}
    {g : Firing s} {admitted : P.Admits g} (crossing : T.Crossing run g admitted) :
    T.Exchange run g admitted := crossing.exchangeWith (crossing.closingsFromGlobal close)

theorem Exchange.same_endpoint {s : State} {run : P.Run s} {g : Firing s} {admitted : P.Admits g}
    (result : T.Exchange run g admitted) :
    T.Same result.residualRun.last (P.result result.residualFiring result.residualAdmitted) := by
  have endpoints := result.interchange.same_last
  simpa only [Step.Run.last, Step.Run.last_append] using endpoints

theorem Exchange.length_preserved {s : State} {run : P.Run s} {g : Firing s} {admitted : P.Admits g}
    (result : T.Exchange run g admitted) : result.residualRun.word.length = run.word.length := by
  have lengths := TraceEquiv.length_eq result.interchange
  simp only [Step.Run.word, Step.Run.word_append, List.length_cons, List.length_nil, List.length_append] at lengths
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport
