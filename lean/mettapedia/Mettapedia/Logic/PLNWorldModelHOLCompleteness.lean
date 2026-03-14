import Mettapedia.Logic.HOL.WorldModelCompleteness

/-!
# HOL WM Consequence-Closure Wrappers

Public PLN-facing aliases for the real Church-style HOL consequence bridge.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLCompleteness

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Public HOL query alias. -/
abbrev HOLQuery := @Mettapedia.Logic.HOL.WorldModelCompleteness.HOLQuery

/-- Public pointed HOL model alias. -/
abbrev PointedHOL := @Mettapedia.Logic.HOL.HenkinModel

/-- Public HOL state alias. -/
abbrev HOLState := @Mettapedia.Logic.HOL.WorldModelCompleteness.HOLState

/-- Public categorical endpoint alias for HOL world-model states. -/
abbrev WMCategoricalEndpointSurface :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.WMCategoricalEndpointSurface

/-- Public pointwise implication relation for closed HOL formulas. -/
abbrev pointwiseImplies (φ ψ : HOLQuery (Base := Base) Const) : Prop :=
  ∀ M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const,
    Mettapedia.Logic.HOL.WorldModel.holSatisfies (Base := Base) (Const := Const) M φ →
      Mettapedia.Logic.HOL.WorldModel.holSatisfies (Base := Base) (Const := Const) M ψ

/-- Public singleton-strength relation for closed HOL formulas. -/
abbrev singletonStrengthLE (φ ψ : HOLQuery (Base := Base) Const) : Prop :=
  ∀ M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const,
    WorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) φ ≤
      WorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) ψ

/-- Naming alias for the singleton-strength consequence relation. -/
abbrev singletonConsequence (φ ψ : HOLQuery (Base := Base) Const) : Prop :=
  ∀ M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const,
    WorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) φ ≤
      WorldModel.queryStrength
        (State := HOLState (Base := Base) Const)
        (Query := HOLQuery (Base := Base) Const)
        ({M} : HOLState (Base := Base) Const) ψ

abbrev pointwiseImplies_iff_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.pointwiseImplies_iff_singletonStrengthLE

abbrev pointwiseImplies_iff_singletonConsequence :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.pointwiseImplies_iff_singletonConsequence

abbrev pointwiseIff_iff_queryEq :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.pointwiseIff_iff_queryEq

abbrev multiset_strength_le_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_pointwise

abbrev multiset_consequence_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_consequence_of_pointwise

abbrev multiset_strength_le_of_pointwise_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_pointwise_categorical

abbrev multiset_strength_le_of_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_singletonStrengthLE

abbrev multiset_consequence_of_singletonConsequence :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_consequence_of_singletonConsequence

abbrev externalImplication_iff_singletonConsequence_of_sound_complete :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.externalImplication_iff_singletonConsequence_of_sound_complete

abbrev multiset_consequence_of_externalImplication_sound :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_consequence_of_externalImplication_sound

abbrev multiset_strength_le_of_singletonStrengthLE_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_singletonStrengthLE_categorical

abbrev wmConsequenceRule_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRule_of_pointwise

abbrev wmConsequenceRule_of_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRule_of_singletonStrengthLE

abbrev wmConsequenceRuleOn_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_pointwise

abbrev wmConsequenceRuleOn_of_pointwise_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_pointwise_categorical

abbrev wmConsequenceRuleOn_of_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_singletonStrengthLE

abbrev wmConsequenceRuleOn_of_singletonStrengthLE_categorical :=
  @Mettapedia.Logic.HOL.WorldModelCompleteness.wmConsequenceRuleOn_of_singletonStrengthLE_categorical

end Mettapedia.Logic.PLNWorldModelHOLCompleteness
