import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoherentSolutionJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceGuards

/-!
# Positive spatial guards in native residual composition

When an event grows the occurrence store, an already admitted candidate with
a monotone guard needs only fresh outputs and compatible joint solutions.
This exact criterion uses actual result knowledge. It assumes neither exact
knowledge nor conservative settlement, and imposes no guard-blindness law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.Coherent

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} [P.Guarded]
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P} {G : P.Guards} (coherent : T.Coherent G)

include coherent in
theorem admits_residual_growth_iff {s : State} (g : Firing s) (second : P.Admits g)
    (f : Firing s) (first : P.Admits f)
    (grows : P.present s ⊆ P.present (P.result g second))
    (monotone : Coexistence.SpatialGuard.Monotone (G.Guard f)) :
    P.Admits (T.residual g second f) ↔
      Disjoint (P.selection f).made.toFinset (P.present (P.result g second)) ∧
        ∃ b, Nonempty (Step.JointSolution g second f b) := by
  rw [coherent.admits_iff]
  constructor
  · rintro ⟨_, enabled, ⟨b, σ, τ, solvesF, solvesG, compatible⟩, _⟩
    exact ⟨enabled.fresh, b, ⟨σ, τ, solvesF, solvesG, compatible⟩⟩
  · rintro ⟨fresh, b, ⟨pair⟩⟩
    have prepared := P.prepares first
    refine ⟨prepared.1, ?_, ⟨b, pair.first, pair.second,
      pair.first_models, pair.second_models, pair.agree⟩, ?_⟩
    · refine ⟨prepared.2.1.taken_subset.trans grows, prepared.2.1.kept_subset.trans grows,
        prepared.2.1.apart, fresh, ?_⟩
      intro query member
      cases member
    · intro b σ _τ solvesF _solvesG _compatible
      have asked := ((P.admits_iff_prepares f).mp first).2 b σ solvesF
      exact monotone b σ grows ((G.holds_iff f b σ).mp asked)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.Coherent
