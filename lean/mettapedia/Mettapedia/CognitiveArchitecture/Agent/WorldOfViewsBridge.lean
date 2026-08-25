import Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation
import Mettapedia.GSLT.Dynamics.WorldOfViews

/-!
# Contextual world models as a relational world of views

The three pairwise probability charts from `MultiAgentFusionNoGo` form an
open relational system: every pair of local contexts can coordinate by
agreeing on its shared one-variable marginal.  Nevertheless, the retained
anti-correlated family has no global classical joint realization.

This bridges the GödelClaw contextual-world-model result to the general
world-of-views interface.  Local compatibility is evidence for coordination;
it is neither a functional translator nor a certificate of global gluing.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge

open Mettapedia.Cybernetics
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.WorldOfViews
open Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo
open Mettapedia.CognitiveArchitecture.Agent.WorldModelRegimeSeparation

/-! ## A faithful modular presentation of a local probability chart -/

inductive ChartCell where
  | mm
  | mp
  | pm
  | pp
deriving DecidableEq, Repr

def chartCellObserver : ChartCell -> Observer PairChart ℚ
  | .mm => ⟨PairChart.mm⟩
  | .mp => ⟨PairChart.mp⟩
  | .pm => ⟨PairChart.pm⟩
  | .pp => ⟨PairChart.pp⟩

def chartModules : ModularView PairChart where
  Module := ChartCell
  module_nonempty := ⟨.mm⟩
  LocalState _ := ℚ
  observer := chartCellObserver
  jointlyFaithful := by
    rintro ⟨firstMM, firstMP, firstPM, firstPP⟩
      ⟨secondMM, secondMP, secondPM, secondPP⟩ same
    have hmm : firstMM = secondMM := by
      simpa [chartCellObserver] using congrFun same ChartCell.mm
    have hmp : firstMP = secondMP := by
      simpa [chartCellObserver] using congrFun same ChartCell.mp
    have hpm : firstPM = secondPM := by
      simpa [chartCellObserver] using congrFun same ChartCell.pm
    have hpp : firstPP = secondPP := by
      simpa [chartCellObserver] using congrFun same ChartCell.pp
    subst hmm
    subst hmp
    subst hpm
    subst hpp
    rfl

/-! ## Shared-marginal coordination -/

def leftMarginal (chart : PairChart) : ℚ × ℚ :=
  (chart.leftMinus, chart.leftPlus)

def rightMarginal (chart : PairChart) : ℚ × ℚ :=
  (chart.rightMinus, chart.rightPlus)

/-- Compatibility of two local charts on the coordinate shared by their
contexts.  A context compared with itself requires the whole chart to agree. -/
def Compatible : PairContext -> PairContext -> PairChart -> PairChart -> Prop
  | .xy, .xy => Eq
  | .xy, .xz => fun source target =>
      leftMarginal source = leftMarginal target
  | .xy, .yz => fun source target =>
      rightMarginal source = leftMarginal target
  | .xz, .xy => fun source target =>
      leftMarginal source = leftMarginal target
  | .xz, .xz => Eq
  | .xz, .yz => fun source target =>
      rightMarginal source = rightMarginal target
  | .yz, .xy => fun source target =>
      leftMarginal source = rightMarginal target
  | .yz, .xz => fun source target =>
      rightMarginal source = rightMarginal target
  | .yz, .yz => Eq

/-- Shared-marginal compatibility retained as a relation witness. -/
def chartRelation (source target : PairContext) : Loose PairChart PairChart :=
  fun sourceChart targetChart =>
    PLift (Compatible source target sourceChart targetChart)

def chartViews : System PairContext where
  State _ := PairChart
  modular _ := chartModules
  relation := chartRelation

theorem antiChart_compatible (source target : PairContext) :
    Compatible source target antiChart antiChart := by
  cases source <;> cases target <;>
    norm_num [Compatible, leftMarginal, rightMarginal,
      antiChart, PairChart.leftMinus, PairChart.leftPlus,
      PairChart.rightMinus, PairChart.rightPlus]

/-- The anti-correlated local chart witnesses coordination between every pair
of contexts. -/
def antiChart_coordinationWitness (source target : PairContext) :
    chartViews.relation source target antiChart antiChart :=
  ⟨antiChart_compatible source target⟩

theorem chartViews_isOpen : chartViews.IsOpen := by
  intro source target _
  exact ⟨⟨antiChart, antiChart, antiChart_coordinationWitness source target⟩⟩

/-! ## Relational openness is not functional convergence -/

def flatChart : PairChart where
  mm := 1 / 4
  mp := 1 / 4
  pm := 1 / 4
  pp := 1 / 4

theorem antiChart_ne_flatChart : antiChart ≠ flatChart := by
  intro same
  have := congrArg PairChart.mm same
  norm_num [antiChart, flatChart] at this

theorem xy_xz_coordinates_two_distinct_targets :
    Nonempty (chartViews.relation .xy .xz antiChart antiChart) /\
      Nonempty (chartViews.relation .xy .xz antiChart flatChart) := by
  constructor
  · exact ⟨antiChart_coordinationWitness .xy .xz⟩
  · refine ⟨⟨?_⟩⟩
    norm_num [Compatible, leftMarginal, PairChart.leftMinus,
      PairChart.leftPlus, antiChart, flatChart]

/-- Agreeing on an overlap leaves other distinctions open, so the `xy` to
`xz` relation has no exact functional translator. -/
theorem xy_xz_not_functional :
    Not (Nonempty (chartViews.FunctionalTransport .xy .xz)) := by
  rintro ⟨transport⟩
  have antiEqual :=
    (transport.exact antiChart antiChart
      (antiChart_coordinationWitness .xy .xz)).down.down
  have flatWitness : chartViews.relation .xy .xz antiChart flatChart := by
    refine ⟨?_⟩
    norm_num [Compatible, leftMarginal, PairChart.leftMinus,
      PairChart.leftPlus, antiChart, flatChart]
  have flatEqual :=
    (transport.exact antiChart flatChart flatWitness).down.down
  exact antiChart_ne_flatChart (antiEqual.symm.trans flatEqual)

/-! ## Local compatibility without global gluing -/

def classicalJointGluing : GluingProblem chartViews where
  Global := Joint3
  restrict joint
    | .xy => joint.xy
    | .xz => joint.xz
    | .yz => joint.yz

/-- The generic gluing predicate recovers the existing classical-realizability
criterion exactly. -/
theorem classicalJointGluing_realizes_iff (family : LocalChartState) :
    classicalJointGluing.Realizes family <-> GloballyRealizable family := by
  constructor
  · rintro ⟨joint, realizes⟩
    exact ⟨joint, realizes .xy, realizes .xz, realizes .yz⟩
  · rintro ⟨joint, xy, xz, yz⟩
    refine ⟨joint, ?_⟩
    intro view
    cases view
    · exact xy
    · exact xz
    · exact yz

/-- The same local family is coherent and relationally open, yet has no global
classical realization. -/
theorem antiFamily_coherent_but_not_gluable :
    LocallyCoherent antiFamily /\
      Not (classicalJointGluing.Realizes antiFamily) := by
  constructor
  · exact antiFamily_is_locally_coherent
  · rw [classicalJointGluing_realizes_iff]
    exact antiFamily_is_not_globally_realizable

/-- No total gluer may turn every locally coherent contextual family into a
global state for this gluing problem. -/
theorem no_total_global_gluer_from_local_coherence :
    Not (Nonempty ((family : LocalChartState) ->
      LocallyCoherent family -> classicalJointGluing.Realizes family)) := by
  rintro ⟨gluer⟩
  exact antiFamily_coherent_but_not_gluable.2
    (gluer antiFamily antiFamily_coherent_but_not_gluable.1)

end Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge

#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge.chartViews_isOpen
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge.xy_xz_not_functional
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge.antiFamily_coherent_but_not_gluable
#print axioms Mettapedia.CognitiveArchitecture.Agent.WorldOfViewsBridge.no_total_global_gluer_from_local_coherence
