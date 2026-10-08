import Mettapedia.OSLF.Syntax.DeterministicGSOSDistributive
import Mettapedia.OSLF.Syntax.DeterministicGSOSFinalSemantics
import Mettapedia.OSLF.Syntax.DeterministicGSOSFinalBialgebra
import Mettapedia.OSLF.Syntax.DeterministicGSOSControls

/-!
# Cofree, distributive and final-kernel controls

The controls retain genuine future colours and varying finite witnesses,
allow infinitely many enabled actions, and distinguish complete behavior
from root-only readout. The operational example uses the actual prefix
GSOS law, while final-kernel congruence acts on independently supplied
related constructor arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.CofreeControls

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory

def denseTransition (state action : Nat) : Option Nat := some (state + (action + 1))

def denseTree : PartialActionTree Nat Nat := PartialActionTree.coiterate denseTransition id 0

def stoppedTree : PartialActionTree Nat Nat :=
  PartialActionTree.coiterate (fun _ _ => none) id 0

/-- The alphabet and all enabled labels are genuinely infinite. -/
theorem every_action_enabled (action : Nat) : (denseTree.step action).isSome = true := by
  change ((PartialActionTree.coiterate denseTransition id 0).step action).isSome = true
  rw [PartialActionTree.coiterate_step]
  rfl

/-- Two independent future actions retain the exact supplied next colour. -/
theorem complete_future_colour : denseTree.read [2, 3] = some 7 := rfl

theorem root_only_readout_agrees : denseTree.root = stoppedTree.root := rfl

/-- Equal root colours do not determine a cofree tree. -/
theorem root_only_readout_insufficient : denseTree ≠ stoppedTree := by
  intro same
  have impossible := congrArg (fun tree => tree.read [2]) same
  change (some 3 : Option Nat) = none at impossible
  cases impossible

/-- Duplication retains complete future subtrees, not merely their root colours. -/
theorem complete_subtree_retained :
    ((PartialActionTree.duplicate denseTree).read [2]).map (fun tree => tree.read [3]) =
      some (some 7) := rfl

abbrev DependentColour := Σ size : Nat, Fin (size + 2)

def grow (state : DependentColour) (action : Nat) : Option DependentColour :=
  some ⟨state.1 + (action + 1),
    Fin.castLE (Nat.add_le_add_right (Nat.le_add_right state.1 (action + 1)) 2) state.2⟩

def witnessedTree : PartialActionTree Nat DependentColour :=
  PartialActionTree.coiterate grow id ⟨0, 1⟩

/-- The colour's dependent domain varies along the actual supplied action path. -/
theorem varying_domain_readout : (witnessedTree.read [2, 3]).map Sigma.fst = some 7 := rfl

/-- The independently supplied finite witness survives that domain change. -/
theorem supplied_finite_witness_retained :
    (witnessedTree.read [2, 3]).map (fun value => value.2.val) = some 1 := rfl

/-- Replacing that supplied witness by zero changes the complete readout. -/
theorem supplied_finite_witness_not_erased :
    (witnessedTree.read [2, 3]).map (fun value => value.2.val) ≠ some 0 := by decide

open Controls

noncomputable def prefixInput :
    signature.polynomial.Free ((Cofree.comonad signature actions).obj naturals) PUnit.unit () :=
  IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
    (fun _ => IndexedPolynomial.Free.pure signature.polynomial denseTree)

/-- The actual distributive image retains the original constructor and exact root colour. -/
theorem actual_distributive_root_readout :
    ((Distributive.lawOverCofree law).app naturals PUnit.unit () prefixInput).root =
      IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => IndexedPolynomial.Free.pure signature.polynomial (0 : Nat)) := by
  have exactRoot := congrArg (fun arrow => arrow PUnit.unit () prefixInput)
    (Distributive.counit law naturals)
  exact exactRoot

/-- Prefix operational behavior is computed by the actual constructor law. -/
theorem prefix_step {X : signature.Families} (steps : VariableCoalgebra actions X)
    (child : signature.polynomial.Free X PUnit.unit ()) (label action : Nat) :
    Operational.coalgebra law steps PUnit.unit ()
      (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix label) (fun _ => child)) action =
      if action = label then some child else none := by
  classical
  rw [Operational.coalgebra_node]
  change (instantiate actions rules (Operator.prefix label) _ action).map
    (IndexedPolynomial.Free.join signature.polynomial) = _
  by_cases fires : action = label
  · simp only [instantiate, instantiateAt, rules, if_pos fires, Option.map_some]
    rfl
  · simp only [instantiate, instantiateAt, rules, if_neg fires, Option.map_none]

/-- A real operational step followed by a future action retains the complete target colour. -/
theorem actual_distributive_future_readout :
    ((Distributive.lawOverCofree law).app naturals PUnit.unit () prefixInput).read [7, 2] =
      some (IndexedPolynomial.Free.pure signature.polynomial (3 : Nat)) := by
  let firstTree : ((Cofree.functor signature actions).obj naturals).V PUnit.unit () := denseTree
  let laterTree : ((Cofree.functor signature actions).obj naturals).V PUnit.unit () :=
    PartialActionTree.coiterate denseTransition id 3
  let steps : signature.polynomial.Free ((Cofree.functor signature actions).obj naturals).V
      PUnit.unit () → Nat → Option
        (signature.polynomial.Free ((Cofree.functor signature actions).obj naturals).V PUnit.unit ()) :=
    fun term action => Operational.coalgebra law
      ((Cofree.functor signature actions).obj naturals).str PUnit.unit () term action
  have prefixRead : steps prefixInput 7 =
      some (IndexedPolynomial.Free.pure signature.polynomial firstTree) :=
    prefix_step (X := ((Cofree.functor signature actions).obj naturals).V)
      ((Cofree.functor signature actions).obj naturals).str
      (IndexedPolynomial.Free.pure signature.polynomial firstTree) 7 7
  have futureRead : steps (IndexedPolynomial.Free.pure signature.polynomial denseTree) 2 =
      some (IndexedPolynomial.Free.pure signature.polynomial laterTree) := by
    have operational := Operational.coalgebra_pure law
      (X := ((Cofree.functor signature actions).obj naturals).V)
      ((Cofree.functor signature actions).obj naturals).str firstTree 2
    have nextTree : ((Cofree.functor signature actions).obj naturals).str
        PUnit.unit () firstTree 2 = some laterTree :=
      PartialActionTree.coiterate_step denseTransition id 0 2
    exact operational.trans (congrArg
      (Option.map (IndexedPolynomial.Free.pure signature.polynomial)) nextTree)
  have pathRead : PartialActionTree.run steps prefixInput [7, 2] =
      some (IndexedPolynomial.Free.pure signature.polynomial
        (PartialActionTree.coiterate denseTransition id 3)) := by
    change (steps prefixInput 7).bind (fun next => PartialActionTree.run steps next [2]) = _
    rw [prefixRead]
    change steps (IndexedPolynomial.Free.pure signature.polynomial denseTree) 2 = _
    exact futureRead
  rw [Distributive.unfolding_readout]
  change (PartialActionTree.run steps prefixInput [7, 2]).map
    (signature.termMonad.map ((Cofree.comonad signature actions).ε.app naturals) PUnit.unit ()) = _
  rw [pathRead]
  rfl

abbrev stoppedVariables : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str _ _ := ↾(fun _ _ => none)

abbrev independentPairs : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := fun _ _ => Nat × Nat
  str _ _ := ↾(fun _ _ => none)

def independentSpan : Bisimulation.Span stoppedVariables where
  carrier := independentPairs
  first := { f := fun _ _ => ↾Prod.fst, h := rfl }
  second := { f := fun _ _ => ↾Prod.snd, h := rfl }

/-- Independent unequal variables are related through an actual full coalgebra span. -/
theorem independent_pure_related :
    Bisimulation.Related (Operational.liftObject law stoppedVariables) PUnit.unit ()
      (Controls.pure 10) (Controls.pure 20) := by
  exact ⟨⟨⟨Operational.liftObject law independentPairs,
      Operational.liftMap law independentSpan.first,
      Operational.liftMap law independentSpan.second⟩,
    IndexedPolynomial.Free.pure signature.polynomial (10, 20), rfl, rfl⟩⟩

/-- The actual final kernel identifies those independently supplied variables. -/
theorem independent_final_readouts_agree :
    (FinalSemantics.observe signature actions (Operational.liftObject law stoppedVariables)).f
      PUnit.unit () (Controls.pure 10) =
    (FinalSemantics.observe signature actions (Operational.liftObject law stoppedVariables)).f
      PUnit.unit () (Controls.pure 20) :=
  (FinalSemantics.kernel_iff_bisimilar signature actions _ PUnit.unit () _ _).mpr
    independent_pure_related

/-- Constructor congruence uses actual final observations and complete dependent argument positions. -/
theorem prefix_final_congruence :
    (FinalSemantics.observe signature actions (Operational.liftObject law stoppedVariables)).f
      PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => Controls.pure 10)) =
    (FinalSemantics.observe signature actions (Operational.liftObject law stoppedVariables)).f
      PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => Controls.pure 20)) := by
  apply FinalSemantics.constructor_kernel_congruent law stoppedVariables
  intro position
  exact independent_final_readouts_agree

/-- Different enabled behavior cannot belong to the actual final-semantic kernel. -/
theorem prefix_distinguished_from_stopped :
    (FinalSemantics.observe signature actions (Operational.liftObject law stoppedVariables)).f
      PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => Controls.pure 10)) ≠
    (FinalSemantics.observe signature actions (Operational.liftObject law stoppedVariables)).f
      PUnit.unit () (Controls.pure 10) := by
  intro same
  have related := (FinalSemantics.kernel_iff_bisimilar signature actions _ PUnit.unit () _ _).mp same
  have availability := Bisimulation.availability_equal
    (Operational.liftObject law stoppedVariables) PUnit.unit () related 7
  change (Operational.coalgebra law stoppedVariables.str PUnit.unit ()
      (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7) (fun _ => Controls.pure 10)) 7).isSome =
    (Operational.coalgebra law stoppedVariables.str PUnit.unit () (Controls.pure 10) 7).isSome at availability
  have prefixRead := prefix_step (X := naturals) stoppedVariables.str
    (Controls.pure (X := naturals) 10) 7 7
  have pureRead := Operational.coalgebra_pure law (X := naturals) stoppedVariables.str
    (base := PUnit.unit) (sort := ()) (10 : Nat) 7
  have impossible : true = false :=
    (congrArg Option.isSome prefixRead).symm.trans
      (availability.trans (congrArg Option.isSome pureRead))
  cases impossible

/-- Both original states have genuine independent, endlessly enabled successor chains. -/
abbrev cyclingVariables : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str _ _ := ↾(fun state action => if action = 7 then some (state + 1) else none)

abbrev cyclingPairs : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := fun _ _ => Nat × Nat
  str _ _ := ↾(fun pair action =>
    if action = 7 then some (pair.1 + 1, pair.2 + 1) else none)

/-- The supplied span retains two unequal successor values at every enabled step. -/
def cyclingSpan : Bisimulation.Span cyclingVariables where
  carrier := cyclingPairs
  first :=
    { f := fun _ _ => ↾Prod.fst
      h := by
        funext base sort
        apply ConcreteCategory.hom_ext
        intro pair
        funext action
        change (if action = 7 then some (pair.1 + 1, pair.2 + 1) else none).map Prod.fst =
          (if action = 7 then some (pair.1 + 1) else none)
        by_cases enabled : action = 7 <;> simp [enabled] }
  second :=
    { f := fun _ _ => ↾Prod.snd
      h := by
        funext base sort
        apply ConcreteCategory.hom_ext
        intro pair
        funext action
        change (if action = 7 then some (pair.1 + 1, pair.2 + 1) else none).map Prod.snd =
          (if action = 7 then some (pair.2 + 1) else none)
        by_cases enabled : action = 7 <;> simp [enabled] }

theorem independent_enabled_successors :
    cyclingVariables.str PUnit.unit () 10 7 = some 11 ∧
    cyclingVariables.str PUnit.unit () 20 7 = some 21 := by
  constructor <;> rfl

theorem cycling_pure_related :
    Bisimulation.Related (Operational.liftObject law cyclingVariables) PUnit.unit ()
      (Controls.pure 10) (Controls.pure 20) := by
  exact ⟨⟨⟨Operational.liftObject law cyclingPairs,
      Operational.liftMap law cyclingSpan.first,
      Operational.liftMap law cyclingSpan.second⟩,
    IndexedPolynomial.Free.pure signature.polynomial (10, 20), rfl, rfl⟩⟩

/-- Complete final-kernel constructor congruence also acts on enabled, unequal successor chains. -/
theorem cycling_constructor_congruent :
    (FinalSemantics.observe signature actions (Operational.liftObject law cyclingVariables)).f
      PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => Controls.pure 10)) =
    (FinalSemantics.observe signature actions (Operational.liftObject law cyclingVariables)).f
      PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => Controls.pure 20)) := by
  apply FinalSemantics.constructor_kernel_congruent law cyclingVariables
  intro position
  exact (FinalSemantics.kernel_iff_bisimilar signature actions _ PUnit.unit () _ _).mpr
    cycling_pure_related

/-- The actual final algebra commutes with operational observation of the supplied prefix term. -/
theorem final_algebra_operational_readout :
    (FinalBialgebra.finalAlgebra law).a.f PUnit.unit ()
      (signature.termMonad.map (FinalSemantics.observe signature actions cyclingVariables).f
        PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
          (fun _ => Controls.pure 10))) =
    (FinalSemantics.observe signature actions (Operational.liftObject law cyclingVariables)).f
      PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => Controls.pure 10)) :=
  congrArg (fun arrow => arrow PUnit.unit ()
    (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7) (fun _ => Controls.pure 10)))
    (FinalBialgebra.operational_observation law cyclingVariables)

/-- An independently supplied stopped child in the actual final behavior carrier. -/
def stoppedFinalChild : (FinalSemantics.finalObject signature actions).V PUnit.unit () :=
  (FinalSemantics.observe signature actions stoppedVariables).f PUnit.unit () 10

theorem stopped_final_child_disabled : stoppedFinalChild.step 7 = none := by
  rw [stoppedFinalChild, FinalSemantics.observe_step]
  rfl

/-- The complete final-algebra action creates a genuine prefix and retains its exact supplied child. -/
theorem final_prefix_action_readout :
    ((FinalBialgebra.finalAlgebra law).a.f PUnit.unit ()
      (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => IndexedPolynomial.Free.pure signature.polynomial stoppedFinalChild))).step 7 =
      some stoppedFinalChild := by
  let child : (FinalSemantics.finalObject signature actions).V PUnit.unit () := stoppedFinalChild
  let input : signature.polynomial.Free (FinalSemantics.finalObject signature actions).V
      PUnit.unit () :=
    IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
      (fun _ => IndexedPolynomial.Free.pure signature.polynomial child)
  have compatible := congrArg (fun arrow => arrow PUnit.unit ()
    input 7)
      (FinalBialgebra.finalAlgebra law).a.h
  change (Operational.coalgebra law (FinalSemantics.finalObject signature actions).str
    PUnit.unit () input 7).map ((FinalBialgebra.finalAlgebra law).a.f PUnit.unit ()) =
      ((FinalBialgebra.finalAlgebra law).a.f PUnit.unit () input).step 7 at compatible
  have prefixRead := prefix_step (X := (FinalSemantics.finalObject signature actions).V)
    (FinalSemantics.finalObject signature actions).str
      (IndexedPolynomial.Free.pure signature.polynomial child) 7 7
  have mappedPrefix := congrArg
    (Option.map ((FinalBialgebra.finalAlgebra law).a.f PUnit.unit ())) prefixRead
  have unitRead := congrArg (fun arrow => arrow PUnit.unit () stoppedFinalChild)
    (FinalBialgebra.action_unit law)
  change (FinalBialgebra.finalAlgebra law).a.f PUnit.unit ()
    (IndexedPolynomial.Free.pure signature.polynomial stoppedFinalChild) = stoppedFinalChild at unitRead
  exact compatible.symm.trans (mappedPrefix.trans (congrArg Option.some unitRead))

/-- The actual final action is distinguished from its stopped argument by complete enabled behavior. -/
theorem final_prefix_action_not_constant :
    (FinalBialgebra.finalAlgebra law).a.f PUnit.unit ()
      (IndexedPolynomial.Free.node signature.polynomial (Operator.prefix 7)
        (fun _ => IndexedPolynomial.Free.pure signature.polynomial stoppedFinalChild)) ≠
      stoppedFinalChild := by
  intro same
  have impossible := congrArg (fun tree => tree.step 7) same
  rw [final_prefix_action_readout, stopped_final_child_disabled] at impossible
  cases impossible

end Mettapedia.OSLF.DeterministicGSOS.CofreeControls
