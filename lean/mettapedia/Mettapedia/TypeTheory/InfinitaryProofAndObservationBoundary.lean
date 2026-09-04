import Mettapedia.Logic.FinitaryRuleSystem.DirectedUnion
import Mettapedia.Coalgebra.CoherentPrefixTower
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary

/-!
# Infinitary proof and observation boundary

Open-ended reasoning has several independent sources of infinity.  They must
not be conflated:

* a finite rule system may generate an unbounded or infinite run;
* one rule may have an infinite family of premises;
* one formula may contain a countable conjunction or disjunction;
* a semantic object may be known only through all of its coherent finite
  observations;
* a genuinely non-well-founded proof or computation needs a separate
  productivity or liveness discipline.

This module relates the middle three without choosing an object logic or a
runtime.  Ordinary list-premise derivations embed exactly into derivations
whose premise arity is an arbitrary type.  The converse compactness property
fails as soon as one inference node has countably many premises: a monotone
directed union can derive a goal which no finite stage derives.  Thus the
finitary hypothesis in `derives_union_exists_stage` is mathematically
load-bearing.

On the semantic side, countable conjunction is equivalent to satisfying all
finite initial segments.  No one fixed segment decides the corresponding
stream property, while the coherent tower of every segment retains exactly
the full stream.  Finite execution can therefore approximate an infinitary
meaning without being mislabeled as a complete decision procedure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary

open Mettapedia.Logic
open Mettapedia.Logic.FinitaryRuleSystem

universe u v

/-! ## Premise arity and indexed derivations -/

/-- A rule premise collection whose arity is represented by an arbitrary
index type.  `Index := Fin n` recovers finite arity; `Index := Nat` supplies
countable arity. -/
structure PremiseFamily (J : Type u) where
  Index : Type v
  premise : Index → J

namespace PremiseFamily

variable {J : Type u}

/-- The premise family represented by a list. -/
def ofList (premises : List J) : PremiseFamily.{u, 0} J where
  Index := Fin premises.length
  premise := premises.get

/-- The empty premise family. -/
def empty : PremiseFamily.{u, 0} J where
  Index := Fin 0
  premise := Fin.elim0

/-- A countably infinite premise family. -/
def countable (premise : Nat → J) : PremiseFamily.{u, 0} J where
  Index := Nat
  premise := premise

/-- Finitarity is a property of the premise index, independent of strict
positivity or the shape of the conclusions. -/
def IsFinitary (premises : PremiseFamily.{u, v} J) : Prop :=
  Finite premises.Index

theorem ofList_isFinitary (premises : List J) :
    IsFinitary (ofList premises) := by
  change Finite (Fin premises.length)
  infer_instance

theorem countable_not_finitary (premise : Nat → J) :
    ¬ IsFinitary (countable premise) := by
  intro finite
  letI : Finite Nat := finite
  exact not_finite Nat

/-- A genuinely countable premise family cannot secretly be a list-shaped
family. -/
theorem countable_ne_ofList (premise : Nat → J) (listed : List J) :
    countable premise ≠ ofList listed := by
  intro equation
  apply countable_not_finitary premise
  rw [equation]
  exact ofList_isFinitary listed

end PremiseFamily

/-- Least well-founded closure under rules with an arbitrary premise arity.
The tree height is inductive even when a node has infinitely many children. -/
inductive IndexedDerives {J : Type u}
    (rules : PremiseFamily.{u, v} J → J → Prop) : J → Prop where
  | node (premises : PremiseFamily J) (conclusion : J)
      (rule : rules premises conclusion)
      (subderivations : ∀ index : premises.Index,
        IndexedDerives rules (premises.premise index)) :
      IndexedDerives rules conclusion

/-- The leastness principle for indexed derivations. -/
theorem IndexedDerives.least {J : Type u}
    {rules : PremiseFamily.{u, v} J → J → Prop} (property : J → Prop)
    (closed : ∀ premises conclusion, rules premises conclusion →
      (∀ index : premises.Index, property (premises.premise index)) →
      property conclusion) :
    ∀ {judgment : J}, IndexedDerives rules judgment → property judgment := by
  intro judgment derivation
  induction derivation with
  | node premises conclusion rule _subderivations inductionHypotheses =>
      exact closed premises conclusion rule inductionHypotheses

/-- Interpret a list-premise rule predicate as an indexed-premise predicate
without changing its rule instances. -/
def liftFinitaryRules {J : Type u} (rules : List J → J → Prop) :
    PremiseFamily.{u, 0} J → J → Prop :=
  fun family conclusion =>
    ∃ premises : List J,
      family = PremiseFamily.ofList premises ∧ rules premises conclusion

/-- Every ordinary finitary derivation has an indexed presentation. -/
theorem derives_to_indexed {J : Type u} {rules : List J → J → Prop}
    {judgment : J} (derivation : Derives rules judgment) :
    IndexedDerives (liftFinitaryRules rules) judgment := by
  induction derivation with
  | node premises conclusion rule _subderivations inductionHypotheses =>
      exact IndexedDerives.node (PremiseFamily.ofList premises) conclusion
        ⟨premises, rfl, rule⟩
        (fun index => inductionHypotheses _ (List.get_mem premises index))

/-- An indexed derivation built only from lifted list rules reconstructs an
ordinary finitary derivation. -/
theorem indexed_to_derives {J : Type u} {rules : List J → J → Prop}
    {judgment : J}
    (derivation : IndexedDerives (liftFinitaryRules rules) judgment) :
    Derives rules judgment := by
  induction derivation with
  | node family conclusion rule _subderivations inductionHypotheses =>
      obtain ⟨premises, familyEquation, sourceRule⟩ := rule
      subst family
      refine Derives.node premises conclusion sourceRule ?_
      intro premise member
      obtain ⟨index, equation⟩ := List.mem_iff_get.mp member
      rw [← equation]
      exact inductionHypotheses index

/-- Indexed derivability is a conservative presentation extension of
ordinary finitary derivability when every admitted rule comes from a list. -/
theorem derives_iff_indexed {J : Type u} (rules : List J → J → Prop)
    (judgment : J) :
    Derives rules judgment ↔
      IndexedDerives (liftFinitaryRules rules) judgment :=
  ⟨derives_to_indexed, indexed_to_derives⟩

/-! ## Directed-union compactness fails at infinite premise arity -/

/-- Pointwise union of indexed-premise rule systems. -/
def UnionIndexedRules {I : Type v} {J : Type u}
    (rules : I → PremiseFamily.{u, v} J → J → Prop) :
    PremiseFamily.{u, v} J → J → Prop :=
  fun premises conclusion => ∃ stage, rules stage premises conclusion

/-- Rule inclusion along the natural-number stage order. -/
def MonotoneIndexedRules {J : Type u}
    (rules : Nat → PremiseFamily.{u, 0} J → J → Prop) : Prop :=
  ∀ {earlier later : Nat}, earlier ≤ later →
    ∀ {premises : PremiseFamily.{u, 0} J} {conclusion : J},
      rules earlier premises conclusion → rules later premises conclusion

namespace OmegaCanary

/-- The countable family `some 0, some 1, ...`. -/
def allNaturals : PremiseFamily (Option Nat) :=
  PremiseFamily.countable some

/-- Stage `bound` contains finite seed rules up to `bound` and the same
countably-premised closing rule at every stage. -/
def StageRules (bound : Nat) :
    PremiseFamily (Option Nat) → Option Nat → Prop :=
  fun premises conclusion =>
    (∃ n, n ≤ bound ∧ premises = PremiseFamily.empty ∧ conclusion = some n) ∨
      (premises = allNaturals ∧ conclusion = none)

/-- Judgments permitted by a finite stage. -/
def Allowed (bound : Nat) : Option Nat → Prop
  | none => False
  | some n => n ≤ bound

theorem stageRules_monotone : MonotoneIndexedRules StageRules := by
  intro earlier later bounded premises conclusion rule
  rcases rule with seed | closing
  · rcases seed with ⟨n, within, familyEquation, conclusionEquation⟩
    exact Or.inl
      ⟨n, within.trans bounded, familyEquation, conclusionEquation⟩
  · exact Or.inr closing

/-- At stage `bound`, every derivable judgment is one of the seeds already
present at that stage. -/
theorem stage_derivation_bounded (bound : Nat) {judgment : Option Nat}
    (derivation : IndexedDerives (StageRules bound) judgment) :
    Allowed bound judgment := by
  refine IndexedDerives.least (Allowed bound) ?_ derivation
  intro premises conclusion rule subderivations
  rcases rule with seed | closing
  · rcases seed with ⟨n, within, _familyEquation, rfl⟩
    exact within
  · rcases closing with ⟨familyEquation, rfl⟩
    subst premises
    have impossible : bound + 1 ≤ bound := subderivations (bound + 1)
    exact (Nat.not_succ_le_self bound impossible).elim

/-- No finite stage derives the closing goal. -/
theorem stage_does_not_derive_goal (bound : Nat) :
    ¬ IndexedDerives (StageRules bound) none := by
  intro derivation
  exact stage_derivation_bounded bound derivation

/-- Every individual natural seed is derivable in the directed union. -/
def unionDerivesSeed (n : Nat) :
    IndexedDerives (UnionIndexedRules StageRules) (some n) :=
  IndexedDerives.node PremiseFamily.empty (some n)
    ⟨n, Or.inl ⟨n, le_rfl, rfl, rfl⟩⟩
    (fun index => Fin.elim0 index)

/-- The union derives the goal by one node with countably many children. -/
def unionDerivesGoal :
    IndexedDerives (UnionIndexedRules StageRules) none :=
  IndexedDerives.node allNaturals none
    ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    unionDerivesSeed

/-- Sharp noncompactness control: the monotone union derives a judgment that
no finite stage derives. -/
theorem union_derives_goal_but_no_stage_does :
    IndexedDerives (UnionIndexedRules StageRules) none ∧
      ∀ bound, ¬ IndexedDerives (StageRules bound) none :=
  ⟨unionDerivesGoal, stage_does_not_derive_goal⟩

end OmegaCanary

/-! ## An infinite run is not an infinitary rule -/

namespace Run

/-- A productive linear computation: every finite time has a state and a
certified next step.  This is an infinite semantic object even when each step
has only one predecessor and one successor. -/
structure EndlessRun {State : Type u} (step : State → State → Prop) where
  state : Nat → State
  advances : ∀ time, step (state time) (state (time + 1))

/-- Validity visible before one finite time horizon. -/
def PrefixValid {State : Type u} (step : State → State → Prop)
    (state : Nat → State) (depth : Nat) : Prop :=
  ∀ time, time + 1 < depth → step (state time) (state (time + 1))

/-- Global productivity is exactly compatibility with every finite horizon;
no one horizon is selected as final. -/
theorem advances_iff_every_prefix {State : Type u}
    (step : State → State → Prop) (state : Nat → State) :
    (∀ time, step (state time) (state (time + 1))) ↔
      ∀ depth, PrefixValid step state depth := by
  constructor
  · intro advances depth time _within
    exact advances time
  · intro everyPrefix time
    exact everyPrefix (time + 2) time (by omega)

/-- A unary successor step supplies an endless run without any infinitary
premise family. -/
def SuccessorStep (source target : Nat) : Prop :=
  target = source + 1

def successorRun : EndlessRun SuccessorStep where
  state := id
  advances := by
    intro time
    rfl

/-- The positive run has no terminal state at any finite time. -/
theorem successorRun_never_terminal (time : Nat) :
    ∃ next, SuccessorStep (successorRun.state time) next :=
  ⟨time + 1, rfl⟩

end Run

/-! ## Finite observations of infinitary meanings -/

namespace Observation

open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Coalgebra.CoherentPrefixTower

/-- The infinitary Boolean conjunction represented as a stream property. -/
def AllTrue (stream : Stream Bool) : Prop :=
  ∀ index, stream index = true

/-- A property factors through one fixed finite prefix. -/
def FactorsThroughPrefix (property : Stream Bool → Prop) (depth : Nat) : Prop :=
  ∃ classifier : Prefix Bool depth → Prop,
    ∀ stream, property stream ↔ classifier (finiteView depth stream)

/-- A property factors through the complete coherent tower of finite views. -/
def FactorsThroughTower (property : Stream Bool → Prop) : Prop :=
  ∃ classifier : Tower Bool → Prop,
    ∀ stream, property stream ↔ classifier (Tower.ofStream stream)

theorem allTrue_constant_true : AllTrue (constant true) := by
  intro index
  rfl

theorem changedAt_false_not_allTrue (depth : Nat) :
    ¬ AllTrue (changedAt depth true false) := by
  intro allTrue
  have atDepth := allTrue depth
  simp [changedAt] at atDepth

/-- No chosen finite observation decides an infinitary conjunction. -/
theorem allTrue_not_factorsThroughPrefix (depth : Nat) :
    ¬ FactorsThroughPrefix AllTrue depth := by
  rintro ⟨classifier, determines⟩
  have fullAccepted : classifier (finiteView depth (constant true)) :=
    (determines (constant true)).mp allTrue_constant_true
  have lateAccepted :
      classifier (finiteView depth (changedAt depth true false)) := by
    rw [← finiteView_constant_changedAt depth true false]
    exact fullAccepted
  exact changedAt_false_not_allTrue depth
    ((determines (changedAt depth true false)).mpr lateAccepted)

/-- The coherent tower is not a guess at infinity: it reconstructs the stream,
so it can classify the full conjunction exactly. -/
theorem allTrue_factorsThroughTower : FactorsThroughTower AllTrue := by
  refine ⟨fun tower => AllTrue (Tower.toStream tower), ?_⟩
  intro stream
  simp only [Tower.toStream_ofStream]

/-- A countable conjunction holds exactly when every finite initial segment
holds. -/
theorem allTrue_iff_every_prefix (stream : Stream Bool) :
    AllTrue stream ↔
      ∀ depth, ∀ index : Fin depth, finiteView depth stream index = true := by
  constructor
  · intro allTrue depth index
    exact allTrue index
  · intro everyPrefix index
    exact everyPrefix (index + 1) ⟨index, Nat.lt_succ_self index⟩

end Observation

/-! ## Countable WM-PLN conjunction as a coherent limit -/

namespace WorldModel

open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLInfinitary

/-- Satisfaction of the first `depth` members of a countable formula family. -/
def SatisfiesPrefix {L : LO.FirstOrder.Language.{u}}
    (model : PointedFOL L) (formulas : Nat → FOLInfQuery L)
    (depth : Nat) : Prop :=
  ∀ index, index < depth → SatisfiesInf model (formulas index)

/-- Countable conjunction semantics is the coherent limit of all finite
conjunction-prefix obligations. -/
theorem satisfiesInf_iAnd_iff_every_finite_prefix
    {L : LO.FirstOrder.Language.{u}}
    (model : PointedFOL L) (formulas : Nat → FOLInfQuery L) :
    SatisfiesInf model (.iAnd formulas) ↔
      ∀ depth, SatisfiesPrefix model formulas depth := by
  rw [satisfiesInf_iAnd_iff]
  constructor
  · intro everyFormula depth index _bounded
    exact everyFormula index
  · intro everyPrefix index
    exact everyPrefix (index + 1) index (Nat.lt_succ_self index)

/-- Countable disjunction has the dual finite-witness behavior: a satisfying
component already appears in some finite prefix. -/
theorem satisfiesInf_iOr_iff_some_finite_prefix
    {L : LO.FirstOrder.Language.{u}}
    (model : PointedFOL L) (formulas : Nat → FOLInfQuery L) :
    SatisfiesInf model (.iOr formulas) ↔
      ∃ depth, ∃ index, index < depth ∧
        SatisfiesInf model (formulas index) := by
  rw [satisfiesInf_iOr_iff]
  constructor
  · rintro ⟨index, satisfied⟩
    exact ⟨index + 1, index, Nat.lt_succ_self index, satisfied⟩
  · rintro ⟨_depth, index, _within, satisfied⟩
    exact ⟨index, satisfied⟩

end WorldModel

/-! ## Audited theorem crowns -/

#print axioms PremiseFamily.countable_not_finitary
#print axioms PremiseFamily.countable_ne_ofList
#print axioms derives_iff_indexed
#print axioms OmegaCanary.stageRules_monotone
#print axioms OmegaCanary.union_derives_goal_but_no_stage_does
#print axioms Run.advances_iff_every_prefix
#print axioms Run.successorRun_never_terminal
#print axioms Observation.allTrue_not_factorsThroughPrefix
#print axioms Observation.allTrue_factorsThroughTower
#print axioms Observation.allTrue_iff_every_prefix
#print axioms WorldModel.satisfiesInf_iAnd_iff_every_finite_prefix
#print axioms WorldModel.satisfiesInf_iOr_iff_some_finite_prefix

end Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary
