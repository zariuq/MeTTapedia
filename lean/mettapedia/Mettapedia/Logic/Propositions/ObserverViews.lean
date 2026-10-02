import Mettapedia.Logic.Propositions.ScenarioSpaces
import Mettapedia.GSLT.Logic.QuotientObservers

/-!
# Senses as observation

Sameness of sense is an observational equality in the sense of
`Mettapedia.GSLT.Logic.QuotientObservers`: two sentences have the same primary
intension exactly when no scenario tells them apart, and exactly when every
observer that respects sense gives them the same answer.  The space of
scenarios is the observer class; enlarging it refines the equality
(`Mettapedia.Logic.Propositions.ScenarioSpaces`).

* `verdict scenario`: the scenario as an observer of sentences.
* `primary_eq_iff_verdicts`: sameness of primary intension is agreement of all
  scenario observers.
* `respectingEquiv_sameSense_iff`: it is the equality of the quotient bubble
  whose admissible observers are the sense-respecting ones.
* `respects_sameSense_iff_factors`: an observer respects sense exactly when it
  factors through the quotient by sameness of sense; every scenario observer
  does (`verdict_eq_of_sameSense`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

open Mettapedia.GSLT.QuotientObservers
open Mettapedia.GSLT.Core.NonFactorization

universe uS uW uD uN uP

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- A scenario as an observer of sentences: does it verify the sentence? -/
def verdict (scenario : S) (sentence : Sentence N P) : Prop :=
  scenario ∈ I.primary sentence

/-- **Same sense means no scenario tells the sentences apart.** -/
theorem primary_eq_iff_verdicts (first second : Sentence N P) :
    I.primary first = I.primary second ↔
      ∀ scenario, I.verdict scenario first ↔ I.verdict scenario second :=
  Set.ext_iff

/-- Sameness of primary intension, as a relation on sentences. -/
def SameSense (first second : Sentence N P) : Prop :=
  I.primary first = I.primary second

theorem sameSense_equivalence : Equivalence I.SameSense :=
  ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩

/-- **Sameness of sense is the equality of the bubble of sense-respecting
observers.** -/
theorem respectingEquiv_sameSense_iff (first second : Sentence N P) :
    RespectingEquiv I.SameSense first second ↔ I.SameSense first second :=
  respectingEquiv_iff_of_equivalence I.SameSense I.sameSense_equivalence first second

/-- An observer respects sense exactly when it factors through the quotient by
sameness of sense. -/
theorem respects_sameSense_iff_factors {Y : Type (max uN uP)}
    (observer : Sentence N P → Y) :
    Respects I.SameSense observer ↔ Factors (Quot.mk I.SameSense) observer :=
  respects_iff_factors I.SameSense observer

/-- Every scenario observer respects sense. -/
theorem verdict_eq_of_sameSense {first second : Sentence N P} (same : I.SameSense first second)
    (scenario : S) : I.verdict scenario first = I.verdict scenario second :=
  congrArg (scenario ∈ ·) same

end Interpretation

end Mettapedia.Logic.Propositions
