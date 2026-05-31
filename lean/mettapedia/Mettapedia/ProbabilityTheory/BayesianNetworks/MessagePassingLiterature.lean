import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingSchedule

/-!
# Literature-Facing Views of the Abstract BP Core

This file gives thin naming wrappers so different BP traditions can reuse the
same core definitions without forking the mathematics.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

/-! ## Pearl-style view -/

namespace Pearl

/-- Pearl's π-style messages can be read as variable-to-factor messages in the
abstract factor-graph core. -/
abbrev πMsg (fg : FactorGraph V K) := VarToFactorMsg fg

/-- Pearl's lambda-style messages can be read as factor-to-variable messages in the
abstract factor-graph core. -/
abbrev lambdaMsg (fg : FactorGraph V K) := FactorToVarMsg fg

abbrev State (fg : FactorGraph V K) := MessageState fg
abbrev Edge (fg : FactorGraph V K) := IncidentEdge fg
abbrev AsyncUpdate (fg : FactorGraph V K) := MessagePassing.AsyncUpdate fg

noncomputable abbrev πUpdate {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K] :=
  varToFactorUpdate (fg := fg)

noncomputable abbrev lambdaUpdate {fg : FactorGraph V K}
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)] :=
  factorToVarUpdate (fg := fg)

noncomputable abbrev syncRound {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] :=
  MessagePassing.syncRound (fg := fg)

noncomputable abbrev runAsyncSchedule {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] :=
  MessagePassing.runAsyncSchedule (fg := fg)

end Pearl

/-! ## Kschischang-Frey-Loeliger sum-product view -/

namespace KschischangFreyLoeliger

abbrev VariableToFactor (fg : FactorGraph V K) := VarToFactorMsg fg
abbrev FactorToVariable (fg : FactorGraph V K) := FactorToVarMsg fg
abbrev State (fg : FactorGraph V K) := MessageState fg

noncomputable abbrev messageVarToFactor {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K] :=
  varToFactorUpdate (fg := fg)

noncomputable abbrev messageFactorToVar {fg : FactorGraph V K}
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)] :=
  factorToVarUpdate (fg := fg)

noncomputable abbrev variableBelief {fg : FactorGraph V K}
    [Fintype fg.factors] [CommMonoid K] :=
  MessagePassing.variableBelief (fg := fg)

noncomputable abbrev factorBelief {fg : FactorGraph V K}
    [CommMonoid K] :=
  MessagePassing.factorBelief (fg := fg)

end KschischangFreyLoeliger

/-! ## Semiring-specialized naming views -/

namespace SumProduct

abbrev State (fg : FactorGraph V K) := MessageState fg
noncomputable abbrev varToFactor {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K] :=
  MessagePassing.varToFactorUpdate (fg := fg)
noncomputable abbrev factorToVar {fg : FactorGraph V K}
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)] :=
  MessagePassing.factorToVarUpdate (fg := fg)

end SumProduct

namespace MaxProduct

/-- Same message equations, intended for carriers whose semiring addition has
been instantiated as a max-like operator. -/
abbrev State (fg : FactorGraph V K) := MessageState fg
noncomputable abbrev varToFactor {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K] :=
  MessagePassing.varToFactorUpdate (fg := fg)
noncomputable abbrev factorToVar {fg : FactorGraph V K}
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)] :=
  MessagePassing.factorToVarUpdate (fg := fg)

end MaxProduct

namespace Tropical

/-- Same message equations, intended for carriers whose semiring structure
encodes min/max-plus cost propagation. -/
abbrev State (fg : FactorGraph V K) := MessageState fg
noncomputable abbrev varToFactor {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K] :=
  MessagePassing.varToFactorUpdate (fg := fg)
noncomputable abbrev factorToVar {fg : FactorGraph V K}
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)] :=
  MessagePassing.factorToVarUpdate (fg := fg)

end Tropical

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
