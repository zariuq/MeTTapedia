/-
# Atomic refinement actions

This module exposes the policy waist shared by refinement roots.  A policy
chooses one open hole and one checker-legal head.  Spine construction and
acceptance are deliberately absent from the action type: the elaborator owns
the successor state, while terminality is observed as a state predicate.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.RefinementInterface

namespace Mettapedia.GSLT.LanguageDef.AtomicRefinement

open Mettapedia.GSLT.LanguageDef.RefinementInterface

universe uState uHole uHead uProgram

/-- The complete policy-visible action: refine one open hole with one head. -/
structure RefineAction (Hole : Type uHole) (Head : Type uHead) where
  hole : Hole
  head : Head
  deriving DecidableEq, Repr

/--
Data for an atomic refinement root.  `legalHeads` is the finite policy support;
`refine?` remains the checker-owned transition and must be proved exact by the
root laws.
-/
structure AtomicRoot where
  State : Type uState
  Hole : Type uHole
  Head : Type uHead
  Program : Type uProgram
  initial : Nat → State
  holes : State → List Hole
  legalHeads : State → Hole → List Head
  refine? : State → Hole → Head → Option State
  terminal : State → Prop
  decode : List (RefineAction Hole Head) → Option Program
  wellFormed : Program → Prop
  programCost : Program → Nat
  encode : Program → List (RefineAction Hole Head)
  invariant : State → Prop
  canComplete : State → Prop
  budgetOK : Nat → Prop

namespace AtomicRoot

variable (root : AtomicRoot)

/-- The generic interface view; no policy-visible action exists besides `Refine`. -/
def asRefinementInterface : RefinementInterface where
  State := root.State
  Hole := root.Hole
  Action := RefineAction root.Hole root.Head
  Program := root.Program
  initial := root.initial
  holes := root.holes
  legal := fun state action =>
    action.hole ∈ root.holes state ∧
      action.head ∈ root.legalHeads state action.hole
  apply? := fun state action => root.refine? state action.hole action.head
  terminal := root.terminal
  decode := root.decode
  wellFormed := root.wellFormed
  programCost := root.programCost
  encode := root.encode
  invariant := root.invariant
  canComplete := root.canComplete
  budgetOK := root.budgetOK

/-- Finite legal support, factored first by hole and then by head. -/
def legalActions (state : root.State) :
    List (RefineAction root.Hole root.Head) :=
  (root.holes state).flatMap fun hole =>
    (root.legalHeads state hole).map fun head => ⟨hole, head⟩

theorem mem_legalActions_iff (state : root.State)
    (action : RefineAction root.Hole root.Head) :
    action ∈ root.legalActions state ↔
      action.hole ∈ root.holes state ∧
        action.head ∈ root.legalHeads state action.hole := by
  constructor
  · intro hmem
    simp only [legalActions, List.mem_flatMap, List.mem_map] at hmem
    rcases hmem with ⟨hole, hhole, head, hhead, heq⟩
    cases action
    simp only [RefineAction.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact ⟨hhole, hhead⟩
  · rintro ⟨hhole, hhead⟩
    simp only [legalActions, List.mem_flatMap, List.mem_map]
    exact ⟨action.hole, hhole, action.head, hhead, rfl⟩

/-- Compatibility restatement: factored enumeration is the interface legality relation. -/
theorem mem_legalActions_iff_legal (state : root.State)
    (action : RefineAction root.Hole root.Head) :
    action ∈ root.legalActions state ↔
      (root.asRefinementInterface).legal state action := by
  exact root.mem_legalActions_iff state action

/--
When both stages enumerate without repetition, the factored legal support is a
genuine partition: every atomic action occurs in exactly one hole block.
-/
theorem legalActions_nodup (state : root.State)
    (hholes : (root.holes state).Nodup)
    (hheads : ∀ hole, (root.legalHeads state hole).Nodup) :
    (root.legalActions state).Nodup := by
  rw [legalActions, List.nodup_flatMap]
  constructor
  · intro hole _hhole
    exact (hheads hole).map fun first second heq => by
      exact (RefineAction.mk.inj heq).2
  · exact hholes.imp fun {firstHole secondHole} hne action hfirst hsecond => by
      rcases List.mem_map.mp hfirst with ⟨firstHead, _hfirstHead, rfl⟩
      rcases List.mem_map.mp hsecond with ⟨secondHead, _hsecondHead, heq⟩
      exact hne (RefineAction.mk.inj heq).1.symm

/--
A factored policy assigns a normalized nonnegative mass to exposed holes and,
conditional on each exposed hole, to its checker-legal heads.
-/
structure FactoredPolicy (state : root.State) where
  holeMass : root.Hole → NNReal
  headMass : root.Hole → root.Head → NNReal
  holeMass_normalized :
    ((root.holes state).map holeMass).sum = 1
  headMass_normalized :
    ∀ hole, hole ∈ root.holes state →
      ((root.legalHeads state hole).map (headMass hole)).sum = 1

namespace FactoredPolicy

variable {root : AtomicRoot} {state : root.State}

/-- Joint mass is the product of the selected hole and conditional head mass. -/
def actionMass (policy : root.FactoredPolicy state)
    (action : RefineAction root.Hole root.Head) : NNReal :=
  policy.holeMass action.hole * policy.headMass action.hole action.head

/-- Each hole block carries exactly its outer policy mass. -/
theorem headBlock_mass (policy : root.FactoredPolicy state)
    {hole : root.Hole} (hhole : hole ∈ root.holes state) :
    ((root.legalHeads state hole).map fun head =>
      policy.actionMass ⟨hole, head⟩).sum = policy.holeMass hole := by
  rw [show
      ((root.legalHeads state hole).map fun head =>
        policy.actionMass ⟨hole, head⟩) =
        ((root.legalHeads state hole).map fun head =>
          policy.holeMass hole * policy.headMass hole head) by rfl]
  rw [List.sum_map_mul_left, policy.headMass_normalized hole hhole, mul_one]

/--
T5: multiplying the hole policy by the conditional head policy defines a
normalized distribution on exactly the atomic legal-action enumeration.
-/
theorem legalActions_mass_one (policy : root.FactoredPolicy state) :
    ((root.legalActions state).map policy.actionMass).sum = 1 := by
  have hsum : ∀ holes : List root.Hole,
      (∀ hole, hole ∈ holes → hole ∈ root.holes state) →
      ((holes.flatMap fun hole =>
          (root.legalHeads state hole).map fun head =>
            ⟨hole, head⟩).map policy.actionMass).sum =
        (holes.map policy.holeMass).sum := by
    intro holes hsubset
    induction holes with
    | nil => rfl
    | cons hole rest ih =>
        have hhole : hole ∈ root.holes state :=
          hsubset hole (by simp)
        have hrest : ∀ other, other ∈ rest →
            other ∈ root.holes state := by
          intro other hother
          exact hsubset other (by simp [hother])
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons]
        have hblock := policy.headBlock_mass hhole
        rw [show
          (List.map policy.actionMass
            (List.map (fun head => ⟨hole, head⟩)
              (root.legalHeads state hole))).sum = policy.holeMass hole by
            rw [List.map_map]
            exact hblock]
        rw [ih hrest]
  exact (hsum (root.holes state) (fun _ hmem => hmem)).trans
    policy.holeMass_normalized

end FactoredPolicy

/-- Checker-owned refinement has at most one successor. -/
theorem refine_successor_deterministic {state next₁ next₂ : root.State}
    {hole : root.Hole} {head : root.Head}
    (hfirst : root.refine? state hole head = some next₁)
    (hsecond : root.refine? state hole head = some next₂) :
    next₁ = next₂ := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

/-- Atomic actions cannot encode a separate finish or spine event. -/
theorem action_eq_refine (action : RefineAction root.Hole root.Head) :
    action = ⟨action.hole, action.head⟩ := by
  cases action
  rfl

end AtomicRoot

/-- Per-root proof obligations for the atomic view. -/
structure AtomicRootLaws (root : AtomicRoot) where
  refine_iff_legal :
    ∀ state hole head,
      (∃ next, root.refine? state hole head = some next) ↔
        hole ∈ root.holes state ∧ head ∈ root.legalHeads state hole
  interfaceLaws : RefinementLaws root.asRefinementInterface

namespace AtomicRootLaws

variable {root : AtomicRoot} (laws : AtomicRootLaws root)
include laws

/-- Successful checker refinement is exactly membership in factored support. -/
theorem exists_refine_iff_mem_legalActions
    (state : root.State) (action : RefineAction root.Hole root.Head) :
    (∃ next, root.refine? state action.hole action.head = some next) ↔
      action ∈ root.legalActions state := by
  rw [root.mem_legalActions_iff]
  exact AtomicRootLaws.refine_iff_legal laws state action.hole action.head

/--
Compatibility restatement: the sealed search-order theorem applies directly
to any permutation of atomic factored support.
-/
theorem rankedAcceptance_invariant_of_legalActions
    (first second : root.State → List (RefineAction root.Hole root.Head))
    (hfirst : ∀ state action,
      action ∈ first state ↔ action ∈ root.legalActions state)
    (hpermutation : ∀ state, (first state).Perm (second state))
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    root.asRefinementInterface.RankedAccepts first budget trace program ↔
      root.asRefinementInterface.RankedAccepts second budget trace program := by
  have hcoverage :
      root.asRefinementInterface.ListsAllLegalActions first := by
    unfold RefinementInterface.ListsAllLegalActions
    dsimp only [AtomicRoot.asRefinementInterface]
    intro state action
    exact (hfirst state action).trans
      (root.mem_legalActions_iff state action)
  exact laws.interfaceLaws.rankedAcceptance_invariant_of_permutation
    first second hcoverage hpermutation

#print axioms AtomicRoot.legalActions_nodup
#print axioms AtomicRoot.FactoredPolicy.legalActions_mass_one
#print axioms rankedAcceptance_invariant_of_legalActions

end AtomicRootLaws

end Mettapedia.GSLT.LanguageDef.AtomicRefinement
