import Mathlib.Data.Fintype.Basic
import Mettapedia.Logic.Derivation

/-!
# Finite semantic models of finitary rule systems

A finitary rule predicate describes syntax and inference.  A `FiniteModel`
supplies a separate finite space of worlds, an executable Boolean satisfaction
relation, and a proof that every displayed rule preserves satisfaction at each
world.

This separation is intentional.  Exact replay alone says which finite trees
are derivations; a model that refutes a distinguished judgment is the extra
semantic datum that proves that judgment underivable.  Finiteness makes global
validity executable, but no claim is made that every rule system has a finite
model or enjoys a finite-model property.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open Mettapedia.Logic

universe u v w

/-- A finite, executable semantic model of one finitary rule predicate. -/
structure FiniteModel {J : Type u} (rules : List J → J → Prop) where
  World : Type v
  worldFintype : Fintype World
  satisfies : World → J → Bool
  rulesSound : ∀ premises conclusion, rules premises conclusion →
    ∀ world, (∀ premise ∈ premises, satisfies world premise = true) →
      satisfies world conclusion = true

namespace FiniteModel

variable {J : Type u} {rules : List J → J → Prop}

/-- A judgment is valid when it is satisfied at every world of the model. -/
def Valid (model : FiniteModel.{u, v} rules) (judgment : J) : Prop :=
  ∀ world, model.satisfies world judgment = true

/-- Global validity is decidable by exhaustive evaluation of the finite world
space. -/
def checkValid (model : FiniteModel.{u, v} rules) (judgment : J) : Bool := by
  letI := model.worldFintype
  exact decide (∀ world, model.satisfies world judgment = true)

/-- Exhaustive evaluation decides global validity exactly. -/
theorem checkValid_eq_true_iff (model : FiniteModel.{u, v} rules)
    (judgment : J) :
    model.checkValid judgment = true ↔ model.Valid judgment := by
  letI := model.worldFintype
  simp [checkValid, Valid]

/-- Every derivable judgment is valid in every finite model of the displayed
rules. -/
theorem derives_valid (model : FiniteModel.{u, v} rules) {judgment : J}
    (derivation : Derives rules judgment) : model.Valid judgment := by
  apply Derives.least model.Valid _ derivation
  intro premises conclusion rule premiseValid world
  exact model.rulesSound premises conclusion rule world fun premise member =>
    premiseValid premise member world

/-- A world refutes a judgment when its executable satisfaction test returns
false. -/
def Refutes (model : FiniteModel.{u, v} rules) (judgment : J) : Prop :=
  ∃ world, model.satisfies world judgment = false

/-- A refuted judgment is not globally valid. -/
theorem not_valid_of_refutes (model : FiniteModel.{u, v} rules)
    {judgment : J} (refutation : model.Refutes judgment) :
    ¬ model.Valid judgment := by
  rintro valid
  obtain ⟨world, refuted⟩ := refutation
  rw [valid world] at refuted
  contradiction

/-- A finite countermodel separates a judgment from the least rule closure. -/
theorem not_derives_of_refutes (model : FiniteModel.{u, v} rules)
    {judgment : J} (refutation : model.Refutes judgment) :
    ¬ Derives rules judgment := by
  intro derivation
  exact model.not_valid_of_refutes refutation (model.derives_valid derivation)

end FiniteModel

/-- A finite countermodel to one distinguished judgment. -/
structure FiniteCountermodel {J : Type u}
    (rules : List J → J → Prop) (judgment : J) where
  model : FiniteModel.{u, v} rules
  refutes : model.Refutes judgment

namespace FiniteCountermodel

variable {J : Type u} {rules : List J → J → Prop} {judgment : J}

/-- A finite countermodel proves its distinguished judgment underivable. -/
theorem not_derivable (countermodel : FiniteCountermodel.{u, v} rules judgment) :
    ¬ Derives rules judgment :=
  countermodel.model.not_derives_of_refutes countermodel.refutes

/-- No successfully replayed derivation tree can conclude the refuted
judgment. -/
theorem valid_derivation_does_not_conclude
    {interface : RuleWitness.{u, w} rules}
    (countermodel : FiniteCountermodel.{u, v} rules judgment)
    (certificate : Derivation J interface.W)
    (accepted : certificate.valid interface = true) :
    certificate.concl ≠ judgment := by
  intro concludes
  apply countermodel.not_derivable
  rw [← concludes]
  exact Derivation.valid_sound interface certificate accepted

/-- The Boolean replay-and-conclusion test rejects every certificate for the
refuted judgment.  This is the data-level core of exact replay rejection,
independent of any particular checker wrapper. -/
theorem replay_test_rejects
    [DecidableEq J] {interface : RuleWitness.{u, w} rules}
    (countermodel : FiniteCountermodel.{u, v} rules judgment)
    (certificate : Derivation J interface.W) :
    (certificate.valid interface && decide (certificate.concl = judgment)) =
        false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  rw [Bool.and_eq_true] at accepted
  exact
    (countermodel.valid_derivation_does_not_conclude certificate accepted.1)
      (of_decide_eq_true accepted.2)

end FiniteCountermodel

end Mettapedia.Logic.FinitaryRuleSystem
