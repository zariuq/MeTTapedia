import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ParallelRunExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunChecks

/-!
# Exact source-level checks for complete native-run interchange

Each stage checks compatible solutions, resource enablement and guards in
both orders, then supplies only the local closing and continuation witnesses
that stage uses. The predicate is equivalent to the actual interchange-plan
domain; it assumes neither global closing nor a completed composite run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}

theorem crossing_unique : ∀ {s : State} (run : P.Run s) (g : Firing s) (allowed : P.Admits g)
    (first second : T.Crossing run g allowed), first = second
  | _, .nil _, _, _, .nil _ _, .nil _ _ => rfl
  | _, .cons f permitted rest, g, _allowed, .cons _firstAfterSecond firstAfterFirst firstTail,
      .cons _secondAfterSecond _secondAfterFirst secondTail => by
      have same := crossing_unique rest (T.residual f permitted g) firstAfterFirst firstTail secondTail
      cases same
      rfl

variable [P.Guarded] {G : P.Guards} (coherent : T.Coherent G)

noncomputable def checkedCrossing {s : State} (run : P.Run s) (g : Firing s) (allowed : P.Admits g)
    (checked : CrossChecks coherent run g allowed) : T.Crossing run g allowed :=
  Classical.choice ((crossing_iff_checks coherent run g allowed).mpr checked)

noncomputable def InterchangeChecks : {s : State} → P.Run s → P.Run s → Prop
  | _, _, .nil _ => True
  | _, left, .cons g allowed right =>
      ∃ check : CrossChecks coherent left g allowed,
        ∃ closed : (checkedCrossing coherent left g allowed check).Closings,
          ∃ _connection : T.Iso
            ((checkedCrossing coherent left g allowed check).exchangeWith closed).residualRun.last
            (P.result ((checkedCrossing coherent left g allowed check).exchangeWith closed).residualFiring
              ((checkedCrossing coherent left g allowed check).exchangeWith closed).residualAdmitted),
            InterchangeChecks ((checkedCrossing coherent left g allowed check).exchangeWith closed).residualRun right

theorem interchange_plan_iff_checks : ∀ {s : State} (left right : P.Run s),
    Nonempty (T.RunInterchangePlan left right) ↔ InterchangeChecks coherent left right
  | _, _, .nil _ => ⟨fun _ => trivial, fun _ => ⟨PUnit.unit⟩⟩
  | _, left, .cons g allowed right => by
      rw [RunInterchangePlan, InterchangeChecks]
      constructor
      · rintro ⟨⟨crossing, closed, connection, tail⟩⟩
        let check := (crossing_iff_checks coherent left g allowed).mp ⟨crossing⟩
        refine ⟨check, ?_⟩
        let continuation := fun crossing : T.Crossing left g allowed =>
          ∃ closed : crossing.Closings,
            ∃ _connection : T.Iso (crossing.exchangeWith closed).residualRun.last
              (P.result (crossing.exchangeWith closed).residualFiring (crossing.exchangeWith closed).residualAdmitted),
              InterchangeChecks coherent (crossing.exchangeWith closed).residualRun right
        have actual : continuation crossing :=
          ⟨closed, connection,
            (interchange_plan_iff_checks (crossing.exchangeWith closed).residualRun right).mp ⟨tail⟩⟩
        have same : checkedCrossing coherent left g allowed check = crossing :=
          crossing_unique left g allowed _ _
        exact Eq.mpr (congrArg continuation same) actual
      · rintro ⟨check, closed, connection, tail⟩
        obtain ⟨later⟩ := (interchange_plan_iff_checks _ right).mpr tail
        exact ⟨⟨checkedCrossing coherent left g allowed check, closed, connection, later⟩⟩

theorem complete_exchange_of_checks {s : State} (left right : P.Run s)
    (checked : InterchangeChecks coherent left right) : Nonempty (T.ParallelExchange left right) := by
  obtain ⟨plan⟩ := (interchange_plan_iff_checks coherent left right).mpr checked
  exact ⟨plan.exchange⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport
