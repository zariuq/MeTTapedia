import Mettapedia.GSLT.Distinction.DemandStrategies

/-!
# Eager evaluation against resampling

Resampling never runs a discarded argument, just as lazy evaluation does, so
the discarding law between eager and lazy evaluation is also the law between
eager evaluation and resampling: they give the same outcome bags exactly when
the discarded computation has one answer (`discard_bags_eager_resample_iff`).
A coin separates them in bags and in draws (`eager_resample_coin`); a
computation with one answer is discarded alike in bags and still separated in
draws (`eager_resample_heads`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.DemandStrategies

variable {Computation : Type} (draw : Computation → Multiset (Option Bool))

/-- **Discarding, over bags, eager evaluation against resampling**: the same
outcomes exactly when the computation has one answer. -/
theorem discard_bags_eager_resample_iff {computation : Computation} {values : Multiset Bool}
    (pure : draw computation = values.map some) :
    answers draw .eager (.discard computation) = answers draw .resample (.discard computation) ↔
      Multiset.card values = 1 :=
  discard_bags_iff draw pure

/-- **The witness**: discarding a coin gives two outcomes and one draw eagerly,
and one outcome and no draw under resampling. -/
theorem eager_resample_coin :
    answers answeringDraw .eager (.discard .coin) ≠
        answers answeringDraw .resample (.discard .coin) ∧
      draws (Computation := Answering) .eager (.discard .coin) ≠
        draws .resample (.discard Answering.coin) :=
  ⟨fun same => by
      have one := (discard_bags_eager_resample_iff answeringDraw answeringDraw_coin).mp same
      simp at one,
    by decide⟩

/-- **Positive control**: discarding a computation with one answer gives the
same outcome bag eagerly and under resampling; only the draws differ. -/
theorem eager_resample_heads :
    answers answeringDraw .eager (.discard .heads) =
        answers answeringDraw .resample (.discard .heads) ∧
      draws (Computation := Answering) .eager (.discard .heads) ≠
        draws .resample (.discard Answering.heads) :=
  ⟨(discard_bags_eager_resample_iff answeringDraw (values := {true}) rfl).mpr rfl, by decide⟩

end Mettapedia.GSLT.Distinction.DemandStrategies
