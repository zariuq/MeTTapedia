import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.BetaPreservation

/-! # Conversion and beta preservation for the cumulative universe profile -/

open Mettapedia.TypeTheory.UniverseLevel
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace LevelTower

variable {L : Type} [LevelOrder L]

/-- Head equality of the tower over any level order is symmetric. -/
theorem headEq_symmetric : Std.Symm (HeadEq (L := L)) := by
  constructor
  intro left right equality
  cases left <;> cases right <;> simp only [HeadEq] at equality ⊢
  intro valuation
  exact (equality valuation).symm

/-- Church--Rosser for all constructors of the tower's rule package, over any level
order. -/
theorem churchRosser : ConversionCoherence.ChurchRosser (rules L) :=
  EmptyRootConversion.churchRosser (rules L) rfl headEq_symmetric

/-- The tower's package satisfies its Pi-conversion qualification, over any level order. -/
theorem piConversionBoundary : Presentation.PiConversionBoundary (rules L) :=
  EmptyRootConversion.piConversionBoundary (rules L) rfl headEq_symmetric

end LevelTower

namespace FormationSensitive

variable {n : Nat}

/-- Root beta preservation for the actual Tower package, with the conversion
boundary and universe regularity discharged by their proved instances. -/
theorem Typing.betaPi_tower {Γ : Tower.Ctx n} {body : Tower.Tm (n + 1)}
    {argument displayed : Tower.Tm n}
    (typing : Typing Tower.rules Γ (.app (.lam body) argument) displayed)
    (context : ContextFormation Tower.rules Γ) :
    Typing Tower.rules Γ (inst0 argument body) displayed :=
  typing.betaPi towerUniverseRegularity LevelTower.piConversionBoundary context

theorem Judgment.betaPi_tower {Γ : Tower.Ctx n} {body : Tower.Tm (n + 1)}
    {argument displayed : Tower.Tm n}
    (judgment : Judgment Tower.rules Γ (.app (.lam body) argument) displayed) :
    Judgment Tower.rules Γ (inst0 argument body) displayed :=
  ⟨judgment.context, judgment.typing.betaPi_tower judgment.context⟩

namespace EmptyRootConversionExamples

/-- A genuine overlap between beta contraction and semantic universe-head
equality has a common reduct, with every displayed arrow an actual step. -/
theorem beta_head_peak (level : LevelExpr Nat) :
    let redundant : Tower.Tm n := sortTm (.max level level)
    let canonical : Tower.Tm n := sortTm level
    let identity : Tower.Tm n := .lam (.var 0)
    Step Tower.HeadEq (.app identity redundant) redundant ∧
      Step Tower.HeadEq (.app identity redundant) (.app identity canonical) ∧
      Step Tower.HeadEq redundant canonical ∧
      Step Tower.HeadEq (.app identity canonical) canonical := by
  have equality : Tower.HeadEq (.sort (.max level level)) (.sort level) := by
    intro valuation
    exact Nat.max_self _
  exact ⟨.betaPi _ _, .congAppArg (.head equality), .head equality, .betaPi _ _⟩

/-- The genuine type-dependent specialization now uses no assumed
Pi-conversion qualification. -/
theorem polymorphic_identity_beta {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {level : LevelExpr Nat} (context : ContextFormation Tower.rules Γ)
    (formed : Typing Tower.rules Γ A (sortTm level)) :
    Typing Tower.rules Γ (.lam (.var 0)) (.pi A (rename wk A)) :=
  BetaExamples.polymorphic_identity_beta context formed LevelTower.piConversionBoundary

/-- Non-normal Pi components are allowed: no term of the full Tower syntax
can make an outer Pi convertible to the opaque ground head. -/
theorem pi_ne_ground (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) :
    ¬ Conv Tower.HeadEq (.pi domain codomain) (.head .legacyGround) :=
  LevelTower.piConversionBoundary.headDisjoint

end EmptyRootConversionExamples
end FormationSensitive

#print axioms AlgebraicParallel.par_substitute
#print axioms EmptyRootConversion.par_develop
#print axioms EmptyRootConversion.churchRosser
#print axioms EmptyRootConversion.piConversionBoundary
#print axioms LevelTower.churchRosser
#print axioms LevelTower.piConversionBoundary
#print axioms FormationSensitive.Typing.betaPi_tower
#print axioms FormationSensitive.Judgment.betaPi_tower
#print axioms FormationSensitive.EmptyRootConversionExamples.beta_head_peak
#print axioms FormationSensitive.EmptyRootConversionExamples.polymorphic_identity_beta
#print axioms FormationSensitive.EmptyRootConversionExamples.pi_ne_ground

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
