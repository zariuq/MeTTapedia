import Mettapedia.Logic.ASP.WellFounded
import Mettapedia.Logic.ASP.CheckerControls

/-!
# Controls for the Kripke–Kleene and well-founded models

The programs of `CheckerControls`, with their computed fixpoints (by `decide`)
read through `coe_kripkeKleeneFin` and `coe_wellFoundedFin`.

* `p :- p.`: the Kripke–Kleene model leaves `p` undetermined (Fitting's operator
  cannot refute self-support), while the well-founded model makes it false; the
  well-founded model is exact, so `{}` is the only stable model.
* `p :- q. q :- p. r :- not p.`: the well-founded model is exactly `{r}`, which
  is therefore the only stable model, obtained here without enumeration.
* `p :- not q. q :- not p.` and `p :- not p.`: nothing is decided; the
  well-founded model is not exact. The first program has two stable models, the
  second none, so an inexact well-founded model says nothing about existence.
* `p :- q. q :- p. p :- not r. r :- not p.`: nothing is decided; both stable
  models lie between the bounds.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.WellFoundedControls

open CheckerControls CheckerControls.Atom Program AFT.Approx OrderDual

/-- Read a computed pair as the model it computes. -/
theorem wellFoundedModel_of {P : Program Atom} {T U : Finset Atom}
    (lower : P.wellFoundedFin.1 = T) (upper : ofDual P.wellFoundedFin.2 = U) :
    P.wellFoundedModel = mk ↑T ↑U := by
  rw [← coe_wellFoundedFin, FinApprox.toApprox, lower, upper]

theorem kripkeKleeneModel_of {P : Program Atom} {T U : Finset Atom}
    (lower : P.kripkeKleeneFin.1 = T) (upper : ofDual P.kripkeKleeneFin.2 = U) :
    P.kripkeKleeneModel = mk ↑T ↑U := by
  rw [← coe_kripkeKleeneFin, FinApprox.toApprox, lower, upper]

/-! ## `p :- p.` -/

theorem selfSupport_kripkeKleene : selfSupport.kripkeKleeneModel = mk ↑(∅ : Finset Atom) ↑({p} : Finset Atom) :=
  kripkeKleeneModel_of (by decide) (by decide)

theorem selfSupport_wellFounded : selfSupport.wellFoundedModel = exact ↑(∅ : Finset Atom) :=
  wellFoundedModel_of (by decide) (by decide)

/-- The Kripke–Kleene model is strictly less precise here. -/
theorem selfSupport_kripkeKleene_ne : selfSupport.kripkeKleeneModel ≠ selfSupport.wellFoundedModel := by
  rw [selfSupport_kripkeKleene, selfSupport_wellFounded]
  intro same
  have := congrArg AFT.Approx.upper same
  simp only [upper_mk, exact, Finset.coe_empty, Finset.coe_singleton] at this
  exact Set.singleton_ne_empty p this

theorem selfSupport_stable_iff (M : Set Atom) : selfSupport.Stable M ↔ M = ∅ := by
  rw [stable_iff_of_wellFoundedModel_eq _ selfSupport_wellFounded, Finset.coe_empty]

/-! ## `p :- q. q :- p. r :- not p.` -/

set_option maxRecDepth 4000 in
theorem unsupportedLoop_wellFounded : unsupportedLoop.wellFoundedModel = exact ↑({r} : Finset Atom) :=
  wellFoundedModel_of (by decide) (by decide)

/-- The unique stable model, read off the well-founded model. -/
theorem unsupportedLoop_stable_iff (M : Set Atom) : unsupportedLoop.Stable M ↔ M = {r} := by
  rw [stable_iff_of_wellFoundedModel_eq _ unsupportedLoop_wellFounded, Finset.coe_singleton]

/-! ## Undecided programs -/

theorem choice_wellFounded : choice.wellFoundedModel = mk ↑(∅ : Finset Atom) ↑({p, q} : Finset Atom) :=
  wellFoundedModel_of (by decide) (by decide)

theorem liar_wellFounded : liar.wellFoundedModel = mk ↑(∅ : Finset Atom) ↑({p} : Finset Atom) :=
  wellFoundedModel_of (by decide) (by decide)

set_option maxRecDepth 4000 in
theorem supportedLoop_wellFounded :
    supportedLoop.wellFoundedModel = mk ↑(∅ : Finset Atom) ↑({p, q, r} : Finset Atom) :=
  wellFoundedModel_of (by decide) (by decide)

/-- The two stable models of the choice program lie between the well-founded bounds. -/
theorem choice_models_bracketed :
    (∀ M ∈ choice.stableModels, ↑M ⊆ choice.wellFoundedModel.upper) ∧
      choice.wellFoundedModel.lower = ∅ := by
  rw [choice_wellFounded, choice_stableModels]
  refine ⟨?_, by simp⟩
  intro M hM
  simp only [Finset.mem_insert, Finset.mem_singleton] at hM
  rcases hM with rfl | rfl <;> simp

end Mettapedia.Logic.ASP.WellFoundedControls
