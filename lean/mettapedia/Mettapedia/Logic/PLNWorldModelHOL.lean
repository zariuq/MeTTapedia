import Mettapedia.Logic.HOL.WorldModel

/-!
# HOL World-Model Bridge

Public PLN-facing aliases for the real Church-style HOL world-model bridge.

This file intentionally re-exports the real Henkin-model semantics rather than
re-implementing them.
-/

namespace Mettapedia.Logic.PLNWorldModelHOL

open Mettapedia.Logic.PLNWorldModel

/-- Public HOL query alias: closed Church-style HOL formulas. -/
abbrev HOLQuery := @Mettapedia.Logic.HOL.WorldModel.HOLQuery

/-- Public pointed HOL state alias: a Henkin model. -/
abbrev PointedHOL := @Mettapedia.Logic.HOL.HenkinModel

/-- Public HOL world-model states are multisets of pointed Henkin models. -/
abbrev HOLState (Base : Type _) (Const : Mettapedia.Logic.HOL.Ty Base → Type _) :=
  Multiset (Mettapedia.Logic.HOL.HenkinModel Base Const)

/-- Closed-formula satisfaction at a pointed Henkin model. -/
abbrev holSatisfies := @Mettapedia.Logic.HOL.WorldModel.holSatisfies

/-- HOL evidence extracted from a multiset of pointed Henkin models. -/
noncomputable abbrev holEvidence := @Mettapedia.Logic.HOL.WorldModel.holEvidence

abbrev holEvidence_add := @Mettapedia.Logic.HOL.WorldModel.holEvidence_add

noncomputable instance {Base : Type _} {Const : Mettapedia.Logic.HOL.Ty Base → Type _} :
    BinaryWorldModel (HOLState Base Const) (HOLQuery (Base := Base) Const) :=
  inferInstance

abbrev holEvidence_singleton_of_satisfies :=
  @Mettapedia.Logic.HOL.WorldModel.holEvidence_singleton_of_satisfies

abbrev holEvidence_singleton_of_not_satisfies :=
  @Mettapedia.Logic.HOL.WorldModel.holEvidence_singleton_of_not_satisfies

abbrev queryStrength_singleton_of_satisfies :=
  @Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_satisfies

abbrev queryStrength_singleton_of_not_satisfies :=
  @Mettapedia.Logic.HOL.WorldModel.queryStrength_singleton_of_not_satisfies

abbrev singleton_adequacy_strength_one :=
  @Mettapedia.Logic.HOL.WorldModel.singleton_adequacy_strength_one

abbrev pointwiseImplies_iff_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModel.pointwiseImplies_iff_singletonStrengthLE

abbrev queryStrength_le_of_pointwise :=
  @Mettapedia.Logic.HOL.WorldModel.queryStrength_le_of_pointwise

abbrev multiset_strength_le_of_singletonStrengthLE :=
  @Mettapedia.Logic.HOL.WorldModel.multiset_strength_le_of_singletonStrengthLE

end Mettapedia.Logic.PLNWorldModelHOL
