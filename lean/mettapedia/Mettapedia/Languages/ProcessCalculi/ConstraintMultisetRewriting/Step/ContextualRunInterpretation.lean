import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeCoexistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunTransport

/-!
# A shared one-step contract for contextual execution

An interpretation constructs a candidate, its updated placement and an exact
admission test for an already admitted local candidate. Its framing domain is
separate from permission. A result isomorphism in the profile's transport
carries the remaining native control. Whole executions are constructed from
these local data; a complete target run is never an assumption of the contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

structure ContextualRunInterpretation where
  Place : State → State → Type uP
  pair : {left right : State} → Place left right → P.effectCore.NativePair left right
  candidate : {left right : State} → (place : Place left right) → Firing left → Firing (pair place).state
  advance : {left right : State} → (place : Place left right) → (f : Firing left) →
    (allowed : P.Admits f) → Place (P.result f allowed) right
  domain : {left right : State} → Place left right → Firing left → Prop
  check : {left right : State} → Place left right → Firing left → Prop
  admission : ∀ {left right : State} (place : Place left right) (f : Firing left), P.Admits f →
    (P.Admits (candidate place f) ↔ check place f)
  resultIso : ∀ {left right : State} (place : Place left right) (f : Firing left)
    (allowed : P.Admits f), domain place f → ∀ (nativeAllowed : P.Admits (candidate place f)),
    T.Iso (P.result (candidate place f) nativeAllowed) (pair (advance place f allowed)).state

namespace ContextualRunInterpretation

variable {T} (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)

inductive Plan : {left right : State} → I.Place left right → P.Run left → Type (max uS uF uP)
  | nil {left right : State} (place : I.Place left right) : Plan place (.nil left)
  | cons {left right : State} {place : I.Place left right} {f : Firing left}
      {allowed : P.Admits f} {rest : P.Run (P.result f allowed)}
      (framed : I.domain place f)
      (nativeAllowed : P.Admits (I.candidate place f))
      (tail : Plan (I.advance place f allowed) rest) : Plan place (.cons f allowed rest)

structure Plan.Decomposition {left right : State} {place : I.Place left right} {f : Firing left}
    {allowed : P.Admits f} {rest : P.Run (P.result f allowed)} (plan : I.Plan place (.cons f allowed rest)) where
  framed : I.domain place f
  nativeAllowed : P.Admits (I.candidate place f)
  tail : I.Plan (I.advance place f allowed) rest
  reconstruct : plan = .cons framed nativeAllowed tail

def Plan.decompose {left right : State} {place : I.Place left right} {f : Firing left}
    {allowed : P.Admits f} {rest : P.Run (P.result f allowed)} (plan : I.Plan place (.cons f allowed rest)) :
    Plan.Decomposition I plan :=
  match plan with
  | .cons framed nativeAllowed tail => ⟨framed, nativeAllowed, tail, rfl⟩

def Checks : {left right : State} → (place : I.Place left right) → P.Run left → Prop
  | _, _, _, .nil _ => True
  | _, _, place, .cons f allowed rest =>
      (I.domain place f ∧ I.check place f) ∧ Checks (I.advance place f allowed) rest

def Plan.ofChecks : ∀ {left right : State} (place : I.Place left right) (run : P.Run left),
    I.Checks place run → I.Plan place run
  | _, _, _, .nil _, _ => .nil _
  | _, _, place, .cons f allowed rest, checked =>
      .cons checked.1.1 ((I.admission place f allowed).mpr checked.1.2)
        (ofChecks (I.advance place f allowed) rest checked.2)

theorem Plan.unique : ∀ {left right : State} {place : I.Place left right} {run : P.Run left}
    (first second : I.Plan place run), first = second
  | _, _, _, .nil _, .nil _, .nil _ => rfl
  | _, _, _, .cons _ _ _, .cons _ _ first, .cons _ _ second => by
      have same := unique first second
      cases same
      rfl

theorem plan_iff_checks : ∀ {left right : State} (place : I.Place left right) (run : P.Run left),
    Nonempty (I.Plan place run) ↔ I.Checks place run
  | _, _, _, .nil _ => ⟨fun _ => trivial, fun _ => ⟨.nil _⟩⟩
  | _, _, place, .cons f allowed rest => by
      constructor
      · rintro ⟨plan⟩
        cases plan with
        | cons framed nativeAllowed tail =>
            exact ⟨⟨framed, (I.admission place f allowed).mp nativeAllowed⟩,
              (plan_iff_checks _ rest).mp ⟨tail⟩⟩
      · rintro ⟨checked, later⟩
        obtain ⟨tail⟩ := (plan_iff_checks _ rest).mpr later
        exact ⟨.cons checked.1 ((I.admission place f allowed).mpr checked.2) tail⟩

structure Realization {left right : State} (place : I.Place left right) (run : P.Run left) where
  target : I.Place run.last right
  execution : P.Run (I.pair place).state
  resultIso : T.Iso execution.last (I.pair target).state
  length_preserved : execution.word.length = run.word.length

def Plan.realize : ∀ {left right : State} (place : I.Place left right) (run : P.Run left),
    I.Plan place run → I.Realization place run
  | _, _, place, .nil _, .nil _ => ⟨place, .nil _, T.refl _, rfl⟩
  | _, _, place, .cons f allowed rest, .cons framed nativeAllowed tail => by
      let later := realize (I.advance place f allowed) rest tail
      let stepIso := I.resultIso place f allowed framed nativeAllowed
      let moved := T.moveRun (T.symm stepIso) later.execution
      refine ⟨later.target, .cons (I.candidate place f) nativeAllowed moved, ?_, ?_⟩
      · exact T.trans (T.symm (T.moveRunEndIso (T.symm stepIso) later.execution)) later.resultIso
      · have lengths := Transport.Similar.length_eq (Transport.Similar.moveRun (T.symm stepIso) later.execution)
        change moved.word.length + 1 = rest.word.length + 1
        rw [← lengths, later.length_preserved]

theorem realization_of_checks {left right : State} (place : I.Place left right) (run : P.Run left)
    (checked : I.Checks place run) : Nonempty (I.Realization place run) := by
  obtain ⟨plan⟩ := (I.plan_iff_checks place run).mpr checked
  exact ⟨plan.realize I place run⟩

end ContextualRunInterpretation
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
