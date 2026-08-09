import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Canaries for the ambient-first GSLT scope

These fixtures exercise the distinctions on which the abstract theory rests:

* an adequate finite shadow need not reconstruct its ambient object;
* a perspective family may be genuinely open, while a constant observation is
  precise;
* observational compilation need not be a syntactic round trip;
* two proof routes with the same endpoints remain different data and may carry
  a chosen 2-cell;
* a proof-relevant bisimulation witness erases soundly to Meredith's quotient
  ontology.
-/

namespace Mettapedia.GSLT.Ultrainfinite.Canary

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

/-! ## A shadow can be adequate without being the whole -/

def coarseProjection :
    PerspectiveProjection Bool Unit (fun _ => Unit) (fun _ => Unit) where
  project _ _ := ()
  observeWhole _ _ := ()
  observeShadow _ _ := ()
  adequate := by intros; rfl

theorem coarseProjection_adequate (whole : Bool) :
    coarseProjection.observeShadow ()
        (coarseProjection.project () whole) =
      coarseProjection.observeWhole () whole :=
  coarseProjection.adequate () whole

/-- The only shadow forgets the Boolean distinction, so no decoder can recover
every ambient object. -/
theorem coarseProjection_not_reconstructible :
    ¬ ∃ recover : Unit → Bool,
      ∀ whole, recover (coarseProjection.project () whole) = whole := by
  rintro ⟨recover, recovers⟩
  have falseValue := recovers false
  have trueValue := recovers true
  have impossible : false = true := by
    calc
      false = recover () := falseValue.symm
      _ = true := trueValue
  cases impossible

/-! ## Open and precise perspective families -/

def perspectiveProjection :
    PerspectiveProjection Unit Bool (fun _ => Unit) (fun _ => Bool) where
  project _ _ := ()
  observeWhole perspective _ := perspective
  observeShadow perspective _ := perspective
  adequate := by intros; rfl

def affirmativeVerdict (perspective : Bool) (observation : Bool) : Prop :=
  observation = perspective && perspective = true

theorem perspectiveProjection_open :
    perspectiveProjection.Open () affirmativeVerdict := by
  rw [PerspectiveProjection.Open,
    Mettapedia.Logic.Metaphysics.openFamily_iff]
  refine ⟨⟨true, ?_⟩, ⟨false, ?_⟩⟩ <;>
    simp [PerspectiveProjection.verdictFamily, perspectiveProjection,
      affirmativeVerdict]

theorem perspectiveProjection_constant_precise :
    perspectiveProjection.Precise () (fun _ _ => True) := by
  rw [PerspectiveProjection.Precise,
    Mettapedia.Logic.Metaphysics.preciseFamily_iff]
  left
  intro perspective
  trivial

theorem perspectiveProjection_principal_is_coordinate :
    Mettapedia.Logic.Metaphysics.UltraTrue (pure true)
        (perspectiveProjection.verdictFamily () affirmativeVerdict) ↔
      affirmativeVerdict true
        (perspectiveProjection.observeWhole true ()) :=
  perspectiveProjection.ultraTrue_pure () affirmativeVerdict true

/-! ## Observational rather than syntactic return -/

def forgetSecond : ObservationalRetraction (Bool × Bool) Bool Bool where
  compile pair := pair.1
  decompile first := (first, false)
  observe pair := pair.1
  roundTrip_observation := by intros; rfl

theorem forgetSecond_observational (pair : Bool × Bool) :
    forgetSecond.observe
        (forgetSecond.decompile (forgetSecond.compile pair)) =
      forgetSecond.observe pair :=
  forgetSecond.roundTrip_observation pair

theorem forgetSecond_not_syntactic : ¬ forgetSecond.Syntactic := by
  intro syntactic
  have := syntactic (true, true)
  simp [forgetSecond] at this

/-! ## Two routes and one authored 2-cell -/

inductive Node where
  | start
  | middle
  | done
deriving DecidableEq

inductive Edge : Node → Node → Type where
  | direct : Edge .start .done
  | first : Edge .start .middle
  | second : Edge .middle .done

def directRoute : Route Edge Node.start Node.done :=
  Route.cons Edge.direct (Route.refl Node.done)

def detourRoute : Route Edge Node.start Node.done :=
  Route.cons Edge.first
    (Route.cons Edge.second (Route.refl Node.done))

theorem directRoute_length : directRoute.length = 1 := rfl

theorem detourRoute_length : detourRoute.length = 2 := rfl

theorem routes_remain_distinct : detourRoute ≠ directRoute := by
  intro equal
  have lengths : detourRoute.length = directRoute.length := congrArg Route.length equal
  rw [detourRoute_length, directRoute_length] at lengths
  cases lengths

inductive OptimizationGenerator :
    {source target : Node} →
      Route Edge source target → Route Edge source target → Type where
  | collapse : OptimizationGenerator detourRoute directRoute

def collapseCell :
    GeneratedTwoCell OptimizationGenerator detourRoute directRoute :=
  .generator .collapse

/-- Raw generated cells have not silently been quotiented by bicategorical
identity laws.  Supplying those coherences is part of the higher completion,
not a definitional accident of this syntax. -/
theorem generatedTwoCell_not_yet_left_unital :
    GeneratedTwoCell.vertical
        (GeneratedTwoCell.refl detourRoute) collapseCell ≠ collapseCell := by
  intro equality
  cases equality

/-- A complete diamond retains both compiler routes and the explicit
optimization witness between them. -/
def compilerDiamond :
    FilledDiamond Edge (GeneratedTwoCell OptimizationGenerator)
      Node.start Node.done Node.done where
  leftBranch := detourRoute
  rightBranch := directRoute
  join := Node.done
  closeLeft := Route.refl Node.done
  closeRight := Route.refl Node.done
  filler := GeneratedTwoCell.whiskerRight
    (Route.refl Node.done) collapseCell

/-! ## Proof-relevant bisimulation reaches the quotient ontology -/

def totalSystem : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := by
    intro left left' target _ _
    exact ⟨target, trivial, rfl⟩
  rewrites_resp_right := by
    intros
    trivial

def totalBisimulation : BisimulationWitness totalSystem where
  Related := fun _ _ => Unit
  forward := by
    intro left right related leftTarget step
    exact ⟨leftTarget, trivial, ()⟩
  backward := by
    intro left right related rightTarget step
    exact ⟨rightTarget, trivial, ()⟩

theorem carried_bisimulation : totalSystem.Bisimilar false true :=
  totalBisimulation.toBisimilar ()

theorem carried_bisimulation_identifies_ontology :
    Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass totalSystem false =
      Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass totalSystem true :=
  totalBisimulation.toBisimClass_eq ()

theorem carried_bisimulation_reverses : totalSystem.Bisimilar true false :=
  totalBisimulation.symm.toBisimilar ()

theorem carried_bisimulation_composes : totalSystem.Bisimilar false false :=
  (totalBisimulation.trans totalBisimulation).toBisimilar
    ⟨true, (), ()⟩

#print axioms FilteredGrowth.compact_factor
#print axioms PerspectiveProjection.open_iff_not_precise
#print axioms PerspectiveProjection.ultraTrue_reindex
#print axioms Route.append_assoc
#print axioms BisimulationWitness.toIsBisimulation
#print axioms BisimulationWitness.toBisimClass_eq
#print axioms coarseProjection_not_reconstructible
#print axioms generatedTwoCell_not_yet_left_unital

end Mettapedia.GSLT.Ultrainfinite.Canary
