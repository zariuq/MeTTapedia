import Mettapedia.UniversalAlgebra.ConservativeExtension

/-!
# Equivalence of generated equational consequence

`EquationSystem.SameConsequences` identifies finite equation systems only at
the level of the deductive closure they generate.  The occurrence-bearing
input lists remain distinct data.

This file proves the invariant consequences of that relation: mutual
derivability of the listed equations is an exact characterization, and
equivalent systems have the same models and the same model-theoretic
consequences in the selected carrier universe.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u

variable {S : Signature.{u}}

namespace EquationSystem

/-- Generated-consequence equivalence is reflexive. -/
protected theorem SameConsequences.refl (system : EquationSystem S) :
    SameConsequences system system :=
  fun _equation => Iff.rfl

/-- Generated-consequence equivalence is symmetric. -/
protected theorem SameConsequences.symm {left right : EquationSystem S}
    (equivalent : SameConsequences left right) :
    SameConsequences right left :=
  fun equation => (equivalent equation).symm

/-- Generated-consequence equivalence is transitive. -/
protected theorem SameConsequences.trans
    {first second third : EquationSystem S}
    (firstSecond : SameConsequences first second)
    (secondThird : SameConsequences second third) :
    SameConsequences first third :=
  fun equation => (firstSecond equation).trans (secondThird equation)

/-- Two systems generate the same consequence relation exactly when every
listed equation of either system is derivable from the other. -/
theorem sameConsequences_iff_mutual_axiom_derivability
    {left right : EquationSystem S} :
    SameConsequences left right ↔
      (∀ equation ∈ left, EquationalConsequence right equation) ∧
      (∀ equation ∈ right, EquationalConsequence left equation) := by
  constructor
  · intro equivalent
    constructor
    · intro equation member
      exact (equivalent equation).mp (EquationalConsequence.of_mem member)
    · intro equation member
      exact (equivalent equation).mpr (EquationalConsequence.of_mem member)
  · rintro ⟨leftFromRight, rightFromLeft⟩ equation
    constructor
    · exact EquationalConsequence.translate_axioms leftFromRight
    · exact EquationalConsequence.translate_axioms rightFromLeft

end EquationSystem

namespace Model

/-- Systems with the same generated consequences have the same models in the
carrier universe used by `Entails`.  This direction needs soundness but not
equational completeness. -/
theorem satisfies_iff_of_sameConsequences
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right)
    {Carrier : Type u} (model : Model S Carrier) :
    model.Satisfies left ↔ model.Satisfies right := by
  constructor
  · intro satisfiesLeft equation member
    have consequenceRight : EquationalConsequence right equation :=
      EquationalConsequence.of_mem member
    have consequenceLeft : EquationalConsequence left equation :=
      (equivalent equation).mpr consequenceRight
    exact equationalConsequence_sound consequenceLeft Carrier model
      satisfiesLeft
  · intro satisfiesRight equation member
    have consequenceLeft : EquationalConsequence left equation :=
      EquationalConsequence.of_mem member
    have consequenceRight : EquationalConsequence right equation :=
      (equivalent equation).mp consequenceLeft
    exact equationalConsequence_sound consequenceRight Carrier model
      satisfiesRight

end Model

/-- Generated-consequence equivalence preserves model-theoretic consequence
in the selected carrier universe. -/
theorem entails_iff_of_sameConsequences
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right)
    (equation : Equation S) :
    Entails left equation ↔ Entails right equation := by
  constructor
  · intro entailed Carrier model satisfiesRight
    exact entailed Carrier model
      ((Model.satisfies_iff_of_sameConsequences equivalent model).mpr
        satisfiesRight)
  · intro entailed Carrier model satisfiesLeft
    exact entailed Carrier model
      ((Model.satisfies_iff_of_sameConsequences equivalent model).mp
        satisfiesLeft)

end Mettapedia.UniversalAlgebra
