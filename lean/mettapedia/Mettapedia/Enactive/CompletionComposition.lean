import Mettapedia.Cybernetics.HierarchicalComplexity.Composition
import Mettapedia.Enactive.CompletionFibre
import Mettapedia.Order.PrincipalCompletion

/-!
# Composition of typed completion fibres

Bennett completion fibres are instances of the general principal-completion
construction on the aspect order.  Consequently, independent composition is
an exact product of informative fibres.  Interacting composition is instead a
compatibility-indexed subtype; it embeds in the product but need not exhaust
it.

This file also separates relational coupling from dynamic MHC coordination.
A strict compatibility relation can coexist with commuting updates, while
noncommuting updates on one completion fibre give an order-sensitive
coordination.  Thus neither notion is silently substituted for the other.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.Completion

open Mettapedia.Cybernetics.HierarchicalComplexity
open Mettapedia.Order.PrincipalCompletion

universe uLeftWorld uRightWorld

variable {LeftWorld : Type uLeftWorld} {RightWorld : Type uRightWorld}
  {leftLayer : AbstractionLayer LeftWorld}
  {rightLayer : AbstractionLayer RightWorld}

/-- The joint principal completion fibre in the componentwise aspect order. -/
abbrev IndependentFibre (left : Aspect leftLayer) (right : Aspect rightLayer) :=
  Mettapedia.Order.PrincipalCompletion.Fibre (left, right)

/-- Independent Bennett completion is exactly the product of the two
component completion fibres. -/
def independentEquiv (left : Aspect leftLayer) (right : Aspect rightLayer) :
    IndependentFibre left right ≃ Fibre left × Fibre right :=
  productEquiv left right

/-- Informative completion variety multiplies under independent composition. -/
theorem mk_independentFibre (left : Aspect leftLayer)
    (right : Aspect rightLayer) :
    Cardinal.mk (IndependentFibre left right) =
      Cardinal.lift.{uRightWorld} (Cardinal.mk (Fibre left)) *
        Cardinal.lift.{uLeftWorld} (Cardinal.mk (Fibre right)) :=
  mk_productFibre left right

/-- An interacting Bennett completion fibre retains precisely the compatible
pairs of component completions. -/
abbrev CoupledFibre (left : Aspect leftLayer) (right : Aspect rightLayer)
    (Compatible : Fibre left → Fibre right → Prop) :=
  Mettapedia.Order.PrincipalCompletion.CoupledFibre
    left right Compatible

/-- Coupled completions embed faithfully in the independent product. -/
def coupledEmbedding (left : Aspect leftLayer) (right : Aspect rightLayer)
    (Compatible : Fibre left → Fibre right → Prop) :
    CoupledFibre left right Compatible ↪ IndependentFibre left right :=
  Mettapedia.Order.PrincipalCompletion.coupledEmbedding
    left right Compatible

/-- A total compatibility relation is exactly the independent case. -/
def coupledEquivIndependent (left : Aspect leftLayer)
    (right : Aspect rightLayer)
    (Compatible : Fibre left → Fibre right → Prop)
    (total : ∀ leftCompletion rightCompletion,
      Compatible leftCompletion rightCompletion) :
    CoupledFibre left right Compatible ≃ IndependentFibre left right :=
  Mettapedia.Order.PrincipalCompletion.coupledEquivProduct
    left right Compatible total

end Mettapedia.Enactive.Completion

namespace Mettapedia.Enactive.Finite.Completion

universe uLeftWorld uRightWorld

variable {LeftWorld : Type uLeftWorld} {RightWorld : Type uRightWorld}
  [Fintype LeftWorld] [DecidableEq LeftWorld]
  [Fintype RightWorld] [DecidableEq RightWorld]
  {leftLayer : Finite.Layer LeftWorld}
  {rightLayer : Finite.Layer RightWorld}

/-- Finite independent completion pairs. -/
abbrev IndependentFibre (left : leftLayer.Statement)
    (right : rightLayer.Statement) :=
  Fibre left × Fibre right

/-- Compatibility-indexed interaction for finite Bennett fibres. -/
abbrev CoupledFibre (left : leftLayer.Statement)
    (right : rightLayer.Statement)
    (Compatible : Fibre left → Fibre right → Prop) :=
  {completion : IndependentFibre left right //
    Compatible completion.1 completion.2}

/-- A compatible finite pair embeds in the independent product. -/
def coupledEmbedding (left : leftLayer.Statement)
    (right : rightLayer.Statement)
    (Compatible : Fibre left → Fibre right → Prop) :
    CoupledFibre left right Compatible ↪ IndependentFibre left right :=
  Function.Embedding.subtype _

/-- Bennett weakness is multiplicative for an independent pair because it is
the finite cardinal readout of the product completion fibre. -/
theorem weakness_independent_mul (left : leftLayer.Statement)
    (right : rightLayer.Statement) :
    Nat.card (IndependentFibre left right) =
      leftLayer.weakness left * rightLayer.weakness right := by
  rw [Nat.card_prod, natCard_fibre, natCard_fibre]

end Mettapedia.Enactive.Finite.Completion

namespace Mettapedia.Enactive.CompletionCompositionCanary

open Mettapedia.Cybernetics.HierarchicalComplexity
open Mettapedia.Cybernetics.HierarchicalComplexity.Composition

abbrev TestFibre :=
  Finite.Completion.Fibre Finite.Canary.emptyStatement

/-- The unconstrained statement completes to itself. -/
def emptyCompletion : TestFibre :=
  ⟨Finite.Canary.emptyStatement, by
    rw [Finite.Layer.mem_extension]⟩

/-- The unconstrained statement also completes to the true-only statement. -/
def trueCompletion : TestFibre :=
  ⟨Finite.Canary.trueStatement, by
    rw [Finite.Layer.mem_extension]
    exact Finset.empty_subset _⟩

theorem emptyCompletion_ne_trueCompletion :
    emptyCompletion ≠ trueCompletion := by
  intro equal
  have targetEqual := congrArg Subtype.val equal
  have factEqual := congrArg (fun statement => statement.val) targetEqual
  simp [emptyCompletion, trueCompletion, Finite.Canary.emptyStatement,
    Finite.Canary.trueStatement, Finite.Canary.trueFact] at factEqual

theorem emptyTarget_ne_trueTarget :
    emptyCompletion.1 ≠ trueCompletion.1 := by
  intro equal
  exact emptyCompletion_ne_trueCompletion (Subtype.ext equal)

/-- Pairwise target equality is a nontrivial coupling on the test fibre. -/
def SameTarget (left right : TestFibre) : Prop :=
  left.1 = right.1

abbrev CoupledTestFibre :=
  Finite.Completion.CoupledFibre
    Finite.Canary.emptyStatement Finite.Canary.emptyStatement SameTarget

/-- The equal-target coupling is strict: the mixed pair is excluded. -/
theorem mixed_pair_incompatible :
    ¬ SameTarget emptyCompletion trueCompletion := by
  simpa only [SameTarget] using emptyTarget_ne_trueTarget

/-- The excluded mixed pair as an independent finite completion. -/
def mixedIndependentCompletion :
    Finite.Completion.IndependentFibre
      Finite.Canary.emptyStatement Finite.Canary.emptyStatement :=
  (emptyCompletion, trueCompletion)

/-- The compatibility-indexed Bennett fibre is strictly smaller than its
independent product in this concrete layer. -/
theorem finiteCoupledEmbedding_not_surjective :
    ¬ Function.Surjective
      (Finite.Completion.coupledEmbedding
        Finite.Canary.emptyStatement Finite.Canary.emptyStatement
        SameTarget) := by
  intro surjective
  obtain ⟨coupled, equal⟩ := surjective mixedIndependentCompletion
  have leftEqual : coupled.1.1 = emptyCompletion :=
    congrArg Prod.fst equal
  have rightEqual : coupled.1.2 = trueCompletion :=
    congrArg Prod.snd equal
  have sameTarget : coupled.1.1.1 = coupled.1.2.1 := coupled.2
  rw [leftEqual, rightEqual] at sameTarget
  exact emptyTarget_ne_trueTarget sameTarget

/-- A canonical coupled state. -/
def coupledInitial : CoupledTestFibre :=
  ⟨(emptyCompletion, emptyCompletion), rfl⟩

/-- Identity updates on a strictly coupled state space. -/
def stationaryCoupledProcess : BinaryProcess CoupledTestFibre where
  initial := coupledInitial
  left := id
  right := id

/-- Strict relational coupling alone does not imply dynamic order
sensitivity. -/
theorem strict_coupling_can_be_chain :
    (¬ SameTarget emptyCompletion trueCompletion) ∧
      IsChain stationaryCoupledProcess.scheduleSemantics := by
  exact ⟨mixed_pair_incompatible,
    BinaryProcess.isChain_of_commute coupledInitial (fun _ => rfl)⟩

/-- Resetting to the unconstrained completion. -/
def reset : TestFibre → TestFibre := fun _ => emptyCompletion

/-- Strengthening to the true-only completion. -/
def strengthen : TestFibre → TestFibre := fun _ => trueCompletion

/-- The same typed completion fibre can carry noncommuting update dynamics. -/
def completionProcess : BinaryProcess TestFibre where
  initial := emptyCompletion
  left := reset
  right := strengthen

theorem completionProcess_isCoordination :
    IsCoordination completionProcess.scheduleSemantics := by
  rw [BinaryProcess.isCoordination_iff]
  exact emptyCompletion_ne_trueCompletion.symm

/-- Dynamic noncommutation raises the corresponding homogeneous MHC action
from order zero to order one. -/
def completionCoordinationAction : Action.{0, 0} TestFibre :=
  BinaryProcess.coordinationAction completionProcess
    completionProcess_isCoordination (fun _ => .simple)

theorem rank_completionCoordinationAction :
    Action.rank completionCoordinationAction = 1 := by
  have rankSuccessor := BinaryProcess.rank_coordinationAction_of_equalRank
    completionProcess completionProcess_isCoordination
      (fun _ => .simple) (fun _ => rfl)
  simpa only [completionCoordinationAction, Action.rank_simple,
    Order.succ_eq_add_one, zero_add] using rankSuccessor

end Mettapedia.Enactive.CompletionCompositionCanary

#print axioms Mettapedia.Enactive.Completion.independentEquiv
#print axioms Mettapedia.Enactive.Finite.Completion.weakness_independent_mul
#print axioms Mettapedia.Enactive.CompletionCompositionCanary.finiteCoupledEmbedding_not_surjective
#print axioms Mettapedia.Enactive.CompletionCompositionCanary.strict_coupling_can_be_chain
#print axioms Mettapedia.Enactive.CompletionCompositionCanary.rank_completionCoordinationAction
