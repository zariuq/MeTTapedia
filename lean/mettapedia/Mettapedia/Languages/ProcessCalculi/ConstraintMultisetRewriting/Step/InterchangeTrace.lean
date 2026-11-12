import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport

/-!
# Canonical interchanges and the existing trace equations

A canonical interchange uses the actual two residual firings and transports
its unchanged continuation along the closing isomorphism. General similarity
is a separate generator. Together these generate exactly the existing trace
relation; canonical interchange alone need not identify alike event labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

inductive Interchange : {s : State} → P.Run s → P.Run s → Prop
  | here {s : State} {f g : Firing s} (first : P.Admits f) (second : P.Admits g)
      (afterFirst : P.Admits (T.residual f first g))
      (afterSecond : P.Admits (T.residual g second f))
      (close : T.Iso (P.result (T.residual f first g) afterFirst)
        (P.result (T.residual g second f) afterSecond))
      (rest : P.Run (P.result (T.residual f first g) afterFirst)) :
      Interchange
        (.cons f first (.cons (T.residual f first g) afterFirst rest))
        (.cons g second (.cons (T.residual g second f) afterSecond (T.moveRun close rest)))
  | later {s : State} (f : Firing s) (admitted : P.Admits f)
      {r r' : P.Run (P.result f admitted)} : Interchange r r' →
        Interchange (.cons f admitted r) (.cons f admitted r')

abbrev InterchangeClosure (s : State) : P.Run s → P.Run s → Prop :=
  Relation.EqvGen (T.Interchange (s := s))

abbrev PresentedTrace (s : State) : P.Run s → P.Run s → Prop :=
  Relation.EqvGen fun first second : P.Run s => T.Interchange first second ∨ T.Similar first second

variable {T}

theorem Interchange.toSwap {s : State} {first second : P.Run s}
    (step : T.Interchange first second) : T.SwapStep first second := by
  induction step with
  | here first second afterFirst afterSecond close rest =>
      exact .here first second (Alike.refl _) afterFirst (Alike.refl _) afterSecond
        (Similar.moveRun close rest)
  | later firing admitted _ ih => exact .later firing admitted ih

theorem Interchange.independent {s : State} {f g : Firing s}
    (first : P.Admits f) (second : P.Admits g)
    (afterFirst : P.Admits (T.residual f first g))
    (afterSecond : P.Admits (T.residual g second f))
    (close : T.Iso (P.result (T.residual f first g) afterFirst)
      (P.result (T.residual g second f) afterSecond)) : T.Independent s f g :=
  ⟨first, second, afterFirst, afterSecond, ⟨close⟩⟩

theorem Independent.interchanges {s : State} {f g : Firing s}
    (independent : T.Independent s f g) :
    ∃ (first : P.Admits f) (second : P.Admits g)
      (afterFirst : P.Admits (T.residual f first g))
      (afterSecond : P.Admits (T.residual g second f))
      (close : T.Iso (P.result (T.residual f first g) afterFirst)
        (P.result (T.residual g second f) afterSecond)),
      ∀ rest, T.Interchange
        (.cons f first (.cons (T.residual f first g) afterFirst rest))
        (.cons g second (.cons (T.residual g second f) afterSecond (T.moveRun close rest))) := by
  obtain ⟨first, second, afterFirst, afterSecond, ⟨close⟩⟩ := independent
  exact ⟨first, second, afterFirst, afterSecond, close,
    fun rest => .here first second afterFirst afterSecond close rest⟩

theorem PresentedTrace.cons {s : State} {f : Firing s} {admitted : P.Admits f}
    {first second : P.Run (P.result f admitted)} (related : T.PresentedTrace _ first second) :
    T.PresentedTrace s (.cons f admitted first) (.cons f admitted second) := by
  induction related with
  | rel _ _ generator =>
      rcases generator with step | similar
      · exact .rel _ _ (.inl (.later f admitted step))
      · exact .rel _ _ (.inr (Similar.cons_self similar))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- Every old swap factors into similarities and one actual-residual interchange. -/
theorem SwapStep.presented {s : State} {first second : P.Run s}
    (step : T.SwapStep first second) : T.PresentedTrace s first second := by
  induction step with
  | @here s f g first second g₁ residualG afterFirst f₁ residualF afterSecond rest rest' similar =>
      let canonicalG : P.Admits (T.residual f first g) := (T.admits_alike residualG).mpr afterFirst
      let canonicalF : P.Admits (T.residual g second f) := (T.admits_alike residualF).mpr afterSecond
      let toG := T.result_alike residualG canonicalG afterFirst
      let toF := T.result_alike residualF canonicalF afterSecond
      obtain ⟨bridge⟩ := Similar.same_start similar
      let close := T.trans toG (T.trans bridge (T.symm toF))
      let unchanged := T.moveRun (T.symm toG) rest
      have left : T.Similar
          (.cons f first (.cons g₁ afterFirst rest))
          (.cons f first (.cons (T.residual f first g) canonicalG unchanged)) :=
        Similar.cons_self (Similar.cons_alike residualG.symm afterFirst canonicalG
          (Similar.moveRun (T.symm toG) rest))
      have right : T.Similar
          (.cons g second (.cons (T.residual g second f) canonicalF (T.moveRun close unchanged)))
          (.cons g second (.cons f₁ afterSecond rest')) :=
        Similar.cons_self (Similar.cons_alike residualF canonicalF afterSecond
          (Similar.trans (Similar.symm (Similar.moveRun close unchanged))
            (Similar.trans (Similar.symm (Similar.moveRun (T.symm toG) rest)) similar)))
      exact .trans _ _ _ (.rel _ _ (.inr left))
        (.trans _ _ _ (.rel _ _ (.inl (.here first second canonicalG canonicalF close unchanged)))
          (.rel _ _ (.inr right)))
  | later firing admitted _ ih => exact ih.cons

theorem presentedTrace_iff_traceEquiv {s : State} {first second : P.Run s} :
    T.PresentedTrace s first second ↔ T.TraceEquiv s first second := by
  constructor
  · intro related
    exact Relation.EqvGen.mono
      (r := fun a b : P.Run s => T.Interchange a b ∨ T.Similar a b)
      (p := fun a b : P.Run s => T.SwapStep a b ∨ T.Similar a b)
      (fun _ _ generator => generator.imp Interchange.toSwap id) first second related
  · intro related
    induction related with
    | rel _ _ generator =>
        rcases generator with step | similar
        · exact step.presented
        · exact .rel _ _ (.inr similar)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem InterchangeClosure.traceEquiv {s : State} {first second : P.Run s}
    (related : T.InterchangeClosure s first second) : T.TraceEquiv s first second :=
  Relation.EqvGen.mono (r := T.Interchange (s := s))
    (p := fun a b : P.Run s => T.SwapStep a b ∨ T.Similar a b)
    (fun _ _ step => Or.inl step.toSwap) first second related

theorem InterchangeClosure.rigid_of_length_le_one {s : State} {first second : P.Run s}
    (related : T.InterchangeClosure s first second) (short : first.word.length ≤ 1) : first = second := by
  induction related with
  | rel _ _ generator =>
      have long := generator.toSwap.length_eq.2
      omega
  | refl => rfl
  | symm _ _ back ih =>
      exact (ih (by rw [TraceEquiv.length_eq (InterchangeClosure.traceEquiv back)]; exact short)).symm
  | trans _ _ _ first _ ih₁ ih₂ =>
      exact (ih₁ short).trans
        (ih₂ (by rw [← TraceEquiv.length_eq (InterchangeClosure.traceEquiv first)]; exact short))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport
