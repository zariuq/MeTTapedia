import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport

/-!
# Exact solution-and-resource checks for native run exchange

The checks mention source shapes, physical enablement, compatible solutions
and guards at those solutions. The existing coherent-residual theorem makes
them equivalent to the crossing construction's native admissions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} [P.Guarded]
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P} {G : P.Guards} (coherent : T.Coherent G)

def CrossChecks : {s : State} → P.Run s → (g : Firing s) → P.Admits g → Prop
  | _, .nil _, _, _ => True
  | _, .cons f first rest, g, second =>
      Step.AdmitsAfter G g second f ∧
        ∃ check : Step.AdmitsAfter G f first g,
          CrossChecks rest (T.residual f first g) ((coherent.admits_iff f first g).mpr check)

theorem crossing_iff_checks : ∀ {s : State} (run : P.Run s) (g : Firing s) (admitted : P.Admits g),
    Nonempty (T.Crossing run g admitted) ↔ CrossChecks coherent run g admitted
  | _, .nil _, g, admitted => ⟨fun _ => trivial, fun _ => ⟨.nil g admitted⟩⟩
  | _, .cons f first rest, g, second => by
      constructor
      · rintro ⟨crossing⟩
        cases crossing with
        | cons afterSecond afterFirst tail =>
            refine ⟨(coherent.admits_iff g second f).mp afterSecond,
              (coherent.admits_iff f first g).mp afterFirst, ?_⟩
            exact (crossing_iff_checks rest _ afterFirst).mp ⟨tail⟩
      · rintro ⟨afterSecond, afterFirst, tail⟩
        obtain ⟨later⟩ := (crossing_iff_checks rest _ _).mpr tail
        exact ⟨.cons ((coherent.admits_iff g second f).mpr afterSecond)
          ((coherent.admits_iff f first g).mpr afterFirst) later⟩

theorem exchange_of_checks (close : T.Closing) {s : State} (run : P.Run s) (g : Firing s)
    (admitted : P.Admits g) (checked : CrossChecks coherent run g admitted) :
    Nonempty (T.Exchange run g admitted) := by
  obtain ⟨crossing⟩ := (crossing_iff_checks coherent run g admitted).mpr checked
  exact ⟨crossing.exchange close⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport
