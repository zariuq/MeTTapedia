import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.RuleEvidenceControls

/-!
# Supplied evidence survives substitution under an actual lambda binder

The same free variable is supplied with either a direct formation proof or
that proof followed by reflexive cumulativity. Substitution under a lambda
weakens the supplied proof while preserving its distinct premise history.
Both resulting trees prove the same scoped judgment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.RuleSubstitutionControls

open JudgmentDerivation FormationSensitiveRuleSignature FormationSensitiveRuleReadout

abbrev base {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev sort0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)

def context : Tower.Ctx 1 := .snoc .nil sort0

def sourceGoal : Judgment Tower.Head :=
  judgment context (.lam (.var 1)) (.pi base sort0)

/-- The body uses the older free variable beneath a freshly bound input. -/
def sourceTree : Tree Tower.rules sourceGoal :=
  .node (.lamIntro (LevelTower.IsUniverse.sort (.max Tower.zero (.succ Tower.zero))))
    (Fin.cases
      (.node (.piForm (LevelTower.IsUniverse.sort Tower.zero)
        (LevelTower.IsUniverse.sort (.succ Tower.zero)) (LevelTower.Join.sorts Tower.zero (.succ Tower.zero)))
        (Fin.cases
          (.node (.headType LevelTower.HeadTyping.legacyGround) (fun position => nomatch position))
          (fun _ => .node (.headType (LevelTower.HeadTyping.sort Tower.zero))
            (fun position => nomatch position))))
      (fun _ => .node (.var (1 : Fin 2)) (fun position => nomatch position)))

def substitution : Sub Tower.Head 1 0 := fun _ => base

/-- The component rule tree is supplied at the variable occurrence. -/
def directComponents : TreeSubstitution (R := Tower.rules) context .nil substitution := by
  intro index
  refine Fin.cases ?_ (fun prior => Fin.elim0 prior) index
  exact Examples.RuleEvidenceControls.direct

def cumulativeComponents : TreeSubstitution (R := Tower.rules) context .nil substitution := by
  intro index
  refine Fin.cases ?_ (fun prior => Fin.elim0 prior) index
  exact Examples.RuleEvidenceControls.cumulative

def targetGoal : Judgment Tower.Head := judgment .nil (.lam base) (.pi base sort0)

noncomputable def directResult : Tree Tower.rules targetGoal := sourceTree.substitute directComponents
noncomputable def cumulativeResult : Tree Tower.rules targetGoal := sourceTree.substitute cumulativeComponents

theorem direct_readout : readout directResult =
    [⟨[], .lamIntro⟩, ⟨[0], .piForm⟩, ⟨[0, 0], .headType⟩,
      ⟨[0, 1], .headType⟩, ⟨[1], .headType⟩] := rfl

theorem cumulative_readout : readout cumulativeResult =
    [⟨[], .lamIntro⟩, ⟨[0], .piForm⟩, ⟨[0, 0], .headType⟩,
      ⟨[0, 1], .headType⟩, ⟨[1], .cumul⟩, ⟨[1, 0], .headType⟩] := rfl

/-- The distinct supplied evidence remains distinct beneath the binder. -/
theorem substituted_readouts_distinct : readout directResult ≠ readout cumulativeResult := by
  rw [direct_readout, cumulative_readout]
  intro same
  have lengths := congrArg List.length same
  change (5 : Nat) = 6 at lengths
  exact (by decide : (5 : Nat) ≠ 6) lengths

theorem substituted_trees_distinct : directResult ≠ cumulativeResult :=
  fun same => substituted_readouts_distinct (congrArg readout same)

/-- Equality of proof-irrelevant typing witnesses does not erase the supplied
component's retained rule history. -/
theorem erased_result_proofs_agree : sound directResult = sound cumulativeResult :=
  Subsingleton.elim _ _

theorem result_readout_cannot_factor_through_typing :
    ¬ ∃ read : PLift (FormationSensitive.Typing Tower.rules targetGoal.context
      targetGoal.subject targetGoal.type) → List Use,
      ∀ tree : Tree Tower.rules targetGoal, read ⟨sound tree⟩ = readout tree := by
  rintro ⟨read, computes⟩
  apply substituted_readouts_distinct
  rw [← computes directResult, ← computes cumulativeResult]

/-- The supplied original free-variable tree is weakened past the fresh
lambda input by the actual binder-lifting implementation. -/
noncomputable def noncapturingResult : Tree Tower.rules sourceGoal :=
  sourceTree.substitute (TreeSubstitution.identity context)

theorem noncapturing_readout : readout noncapturingResult =
    [⟨[], .lamIntro⟩, ⟨[0], .piForm⟩, ⟨[0, 0], .headType⟩,
      ⟨[0, 1], .headType⟩, ⟨[1], .variable 1⟩] := rfl

/-- A replacement referring to the outer variable retains index one beneath
the binder, instead of referring to the freshly bound index zero. -/
theorem outer_variable_is_not_captured :
    (⟨[1], .variable 1⟩ : Use) ∈ readout noncapturingResult ∧
      (⟨[1], .variable 0⟩ : Use) ∉ readout noncapturingResult := by
  rw [noncapturing_readout]
  decide

end Examples.RuleSubstitutionControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
