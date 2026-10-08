import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRetainedContextual
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.RuleEvidenceControls

/-!
# Variable-type comprehension and erasure collisions

The telescope `(X : U₀), (x : X)` contains a genuinely variable-dependent
entry. Its newest variable has the weakened earlier type variable as its
annotation. Separate controls use two supplied proofs of the same judgment:
their retained contexts, terms and pairing arrows differ, although the
formation-sensitive erasure identifies them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.RetainedContextualControls

open _root_.CategoryTheory
open FormationSensitiveRuleSignature FormationSensitiveRuleReadout
open FormationSensitiveRetainedContextual

abbrev base {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev sort0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)

abbrev closed : Context Tower.rules := empty Tower.rules

/-- `U₀` itself is formed at its actual successor universe. -/
def universeType : TypeOver closed where
  code := sort0
  level := .sort (.succ Tower.zero)
  universeWitness := .sort _
  formation := .node (.headType (LevelTower.HeadTyping.sort Tower.zero))
    (fun position => nomatch position)

abbrev universeContext : Context Tower.rules := extend closed universeType

/-- The next domain is the earlier type variable, rather than a closed
constant domain or a fixed object sort. -/
def variableDomain : TypeOver universeContext where
  code := .var 0
  level := .sort Tower.zero
  universeWitness := .sort _
  formation := Tree.variableLeaf universeContext.raw 0

abbrev dependentContext : Context Tower.rules := extend universeContext variableDomain

noncomputable def dependentVariable :
    Term dependentContext (variableDomain.reindex (projectionHom universeContext variableDomain)) :=
  newest universeContext variableDomain

theorem variable_domain_is_not_closed : variableDomain.code.freeVariables = {0} := rfl

theorem dependent_telescope :
    dependentContext.raw = .snoc (.snoc .nil sort0) (.var 0) := rfl

/-- The newest term refers to index zero, while its type refers to the older
type variable at index one. -/
theorem dependent_variable_indices :
    dependentVariable.code = .var 0 ∧
      (variableDomain.reindex (projectionHom universeContext variableDomain)).code = .var 1 :=
  ⟨rfl, rfl⟩

theorem dependent_variable_readout :
    readout dependentVariable.evidence = [⟨[], .variable 0⟩] := rfl

theorem dependent_type_readout :
    readout (variableDomain.reindex (projectionHom universeContext variableDomain)).formation =
      [⟨[], .variable 1⟩] := rfl

theorem dependent_erased_judgment :
    FormationSensitive.Judgment Tower.rules dependentContext.raw (.var 0) (.var 1) :=
  ⟨dependentContext.spine.sound, FormationSensitiveRuleSignature.sound dependentVariable.evidence⟩

def directType : TypeOver closed :=
  ⟨base, .sort Tower.zero, .sort _, RuleEvidenceControls.direct⟩

def cumulativeType : TypeOver closed :=
  ⟨base, .sort Tower.zero, .sort _, RuleEvidenceControls.cumulative⟩

/-- Read the supplied formation trees in telescope order. -/
def spineReadout : {n : Nat} → {Γ : Tower.Ctx n} → Spine Tower.rules Γ → List (List Use)
  | _, _, .nil => []
  | _, _, .snoc prior _ formation => spineReadout prior ++ [readout formation]

def contextReadout (context : Context Tower.rules) : List (List Use) :=
  spineReadout context.spine

theorem direct_context_readout : contextReadout (extend closed directType) =
    [[⟨[], .headType⟩]] := rfl

theorem cumulative_context_readout : contextReadout (extend closed cumulativeType) =
    [[⟨[], .cumul⟩, ⟨[0], .headType⟩]] := rfl

/-- Equal raw telescopes and equal erased formation proofs do not identify
the retained telescope spines. -/
theorem retained_contexts_distinct : extend closed directType ≠ extend closed cumulativeType := by
  intro same
  have readouts := congrArg contextReadout same
  rw [direct_context_readout, cumulative_context_readout] at readouts
  have entries := (List.cons.inj readouts).1
  have sizes := congrArg List.length entries
  exact (by decide : (1 : Nat) ≠ 2) sizes

theorem erased_contexts_agree :
    (extend closed directType).erase = (extend closed cumulativeType).erase := rfl

def directValue : Term closed (universeType.reindex (toEmpty closed)) :=
  ⟨base, RuleEvidenceControls.direct⟩

def cumulativeValue : Term closed (universeType.reindex (toEmpty closed)) :=
  ⟨base, RuleEvidenceControls.cumulative⟩

theorem retained_terms_distinct : directValue ≠ cumulativeValue := by
  intro same
  exact RuleEvidenceControls.readouts_distinct
    (congrArg (fun term => readout term.evidence) same)

theorem erased_terms_agree : directValue.erase = cumulativeValue.erase := rfl

noncomputable def directArrow : closed ⟶ universeContext := pair (toEmpty closed) directValue
noncomputable def cumulativeArrow : closed ⟶ universeContext := pair (toEmpty closed) cumulativeValue

theorem direct_component_readout : readout (directArrow.components 0) =
    readout RuleEvidenceControls.direct :=
  congrArg readout (eq_of_heq (pair_component_zero (toEmpty closed) directValue))

theorem cumulative_component_readout : readout (cumulativeArrow.components 0) =
    readout RuleEvidenceControls.cumulative :=
  congrArg readout (eq_of_heq (pair_component_zero (toEmpty closed) cumulativeValue))

/-- Instantiating the variable domain with the closed ground type creates
a genuinely different extension domain. Lifting then keeps the newly bound
term variable while substituting the older type variable. -/
noncomputable def directLift := liftHom directArrow variableDomain
noncomputable def cumulativeLift := liftHom cumulativeArrow variableDomain

theorem lifted_indices_and_domain :
    directLift.substitution 0 = .var 0 ∧
      directLift.substitution 1 = base ∧
        (variableDomain.reindex directArrow).code = base := ⟨rfl, rfl, rfl⟩

theorem lifted_newest_readout : readout (directLift.components 0) =
    [⟨[], .variable 0⟩] := rfl

theorem lifted_direct_readout : readout (directLift.components 1) =
    [⟨[], .headType⟩] := rfl

theorem lifted_cumulative_readout : readout (cumulativeLift.components 1) =
    [⟨[], .cumul⟩, ⟨[0], .headType⟩] := rfl

theorem lifted_older_histories_differ :
    readout (directLift.components 1) ≠ readout (cumulativeLift.components 1) := by
  rw [lifted_direct_readout, lifted_cumulative_readout]
  intro same
  have lengths := congrArg List.length same
  exact (by decide : (1 : Nat) ≠ 2) lengths

theorem lifted_dependent_projection :
    directLift ≫ projectionHom universeContext variableDomain =
      projectionHom closed (variableDomain.reindex directArrow) ≫ directArrow :=
  lift_projection directArrow variableDomain

/-- Pairing remembers which proof was supplied, even though both arrows
have the same raw substitution and the same erased formed arrow. -/
theorem retained_arrows_distinct : directArrow ≠ cumulativeArrow := by
  intro same
  have readouts := congrArg (fun arrow : closed ⟶ universeContext =>
    readout (arrow.components 0)) same
  rw [direct_component_readout, cumulative_component_readout] at readouts
  exact RuleEvidenceControls.readouts_distinct readouts

theorem erased_arrows_agree : directArrow.erase = cumulativeArrow.erase :=
  FormationSensitiveContextual.Hom.ext rfl

/-- Consequently this erasure functor is not faithful. The lost histories
are actual context-substitution components, not hypothetical model data. -/
theorem erasure_not_faithful : ¬ (eraseBase Tower.rules).Faithful := by
  intro faithful
  exact retained_arrows_distinct
    (faithful.map_injective (show (eraseBase Tower.rules).map directArrow =
      (eraseBase Tower.rules).map cumulativeArrow from erased_arrows_agree))

theorem arrow_readout_cannot_factor_through_erasure :
    ¬ ∃ read : (closed.erase ⟶ universeContext.erase) → List Use,
      ∀ arrow : closed ⟶ universeContext,
        read arrow.erase = readout (arrow.components 0) := by
  rintro ⟨read, computes⟩
  apply RuleEvidenceControls.readouts_distinct
  rw [← direct_component_readout, ← cumulative_component_readout,
    ← computes directArrow, ← computes cumulativeArrow, erased_arrows_agree]

end Examples.RetainedContextualControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
