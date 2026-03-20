import Mettapedia.Logic.BDD.ADTranslation
import Mettapedia.Logic.BDD.FirstOrderProbMeTTaBridge

/-!
# First-Order Annotated Disjunctions via Grounding

This file adds a first-order annotated-disjunction surface layer and reduces it
to the existing ground AD translation by explicit grounding.

Positive example:
- A function-free AD like `0.6::heads(X) ; 0.4::tails(X) :- coin(X)` can be
  represented with first-order atoms and then grounded over all substitutions.

Negative example:
- This file does **not** add a separate non-ground AD semantics. As with the
  first-order normal-rule layer, the semantics is the grounded-expanded one.

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

open Mettapedia.Logic.LP

/-- A first-order annotated disjunction: a multi-headed probabilistic rule
    with first-order heads and body atoms. -/
structure FirstOrderAnnotatedDisjunction (σ : LPSignature) where
  heads : List (Atom σ)
  body  : List (Atom σ)

/-- A ground annotated disjunction with its intended head probabilities. -/
structure WeightedAnnotatedDisjunction (σ : LPSignature) where
  heads : List (GroundAtom σ)
  probs : Fin heads.length → ENNReal
  body  : List (GroundAtom σ)

/-- Validity condition for a weighted ground AD: its head probabilities sum to
    at most one. -/
def WeightedAnnotatedDisjunction.probsValid {σ : LPSignature}
    (ad : WeightedAnnotatedDisjunction σ) : Prop :=
  Finset.univ.sum ad.probs ≤ 1

/-- Forget the probability annotations on a ground AD. -/
def WeightedAnnotatedDisjunction.toAnnotatedDisjunction {σ : LPSignature}
    (ad : WeightedAnnotatedDisjunction σ) : AnnotatedDisjunction σ where
  heads := ad.heads
  body := ad.body

/-- A first-order annotated disjunction with first-class head probabilities. -/
structure FirstOrderWeightedAnnotatedDisjunction (σ : LPSignature) where
  heads : List (Atom σ)
  probs : Fin heads.length → ENNReal
  body  : List (Atom σ)

/-- Validity condition for a weighted first-order AD: its head probabilities
    sum to at most one. -/
def FirstOrderWeightedAnnotatedDisjunction.probsValid {σ : LPSignature}
    (ad : FirstOrderWeightedAnnotatedDisjunction σ) : Prop :=
  Finset.univ.sum ad.probs ≤ 1

/-- Forget the probability annotations on a first-order AD. -/
def FirstOrderWeightedAnnotatedDisjunction.toFirstOrderAnnotatedDisjunction
    {σ : LPSignature} (ad : FirstOrderWeightedAnnotatedDisjunction σ) :
    FirstOrderAnnotatedDisjunction σ where
  heads := ad.heads
  body := ad.body

/-- Ground a first-order annotated disjunction using a grounding substitution. -/
def Grounding.groundFirstOrderAD {σ : LPSignature}
    (g : Grounding σ) (ad : FirstOrderAnnotatedDisjunction σ) :
    AnnotatedDisjunction σ where
  heads := ad.heads.map g.groundAtom
  body := ad.body.map g.groundAtom

/-- Ground a weighted first-order annotated disjunction using a grounding
    substitution. The head probabilities are preserved verbatim. -/
def Grounding.groundFirstOrderWeightedAD {σ : LPSignature}
    (g : Grounding σ) (ad : FirstOrderWeightedAnnotatedDisjunction σ) :
    WeightedAnnotatedDisjunction σ where
  heads := ad.heads.map g.groundAtom
  probs := by
    simpa using ad.probs
  body := ad.body.map g.groundAtom

/-- A grounded first-order AD instance remembers both the source AD and the
    grounding that produced it. This lets auxiliary atoms depend on the
    occurrence, not just on the resulting ground AD value. -/
structure GroundedFirstOrderADInstance (σ : LPSignature) where
  source : FirstOrderAnnotatedDisjunction σ
  grounding : Grounding σ

/-- The corresponding ground annotated disjunction for a grounded instance. -/
def GroundedFirstOrderADInstance.toGroundAD {σ : LPSignature}
    (inst : GroundedFirstOrderADInstance σ) : AnnotatedDisjunction σ :=
  Grounding.groundFirstOrderAD inst.grounding inst.source

/-- A grounded first-order weighted AD instance remembers both the source AD
    and the grounding that produced it. -/
structure GroundedFirstOrderWeightedADInstance (σ : LPSignature) where
  source : FirstOrderWeightedAnnotatedDisjunction σ
  grounding : Grounding σ

/-- The corresponding ground weighted annotated disjunction for a grounded
    weighted instance. -/
def GroundedFirstOrderWeightedADInstance.toGroundWeightedAD {σ : LPSignature}
    (inst : GroundedFirstOrderWeightedADInstance σ) : WeightedAnnotatedDisjunction σ :=
  Grounding.groundFirstOrderWeightedAD inst.grounding inst.source

/-- Forget the probabilities of a grounded weighted instance. -/
def GroundedFirstOrderWeightedADInstance.toGroundAD {σ : LPSignature}
    (inst : GroundedFirstOrderWeightedADInstance σ) : AnnotatedDisjunction σ :=
  inst.toGroundWeightedAD.toAnnotatedDisjunction

/-- A first-order ProbLog surface with both normal rules and annotated
    disjunctions. -/
structure FirstOrderADProbLogProgram (σ : LPSignature) (n : ℕ)
    extends FirstOrderNormalProbLogProgram σ n where
  annotatedDisjunctions : List (FirstOrderAnnotatedDisjunction σ)

/-- A first-order ProbLog surface with weighted annotated disjunctions. -/
structure FirstOrderWeightedADProbLogProgram (σ : LPSignature) (n : ℕ)
    extends FirstOrderNormalProbLogProgram σ n where
  annotatedDisjunctions : List (FirstOrderWeightedAnnotatedDisjunction σ)

/-- Forget the AD surface and keep only the first-order normal-rule layer. -/
def FirstOrderADProbLogProgram.toFirstOrderNormalProgram
    {σ : LPSignature} {n : ℕ}
    (prog : FirstOrderADProbLogProgram σ n) : FirstOrderNormalProbLogProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  rules := prog.rules
  facts_injective := prog.facts_injective
  normalRules := prog.normalRules

/-- Forget the weighted AD surface and keep only the first-order normal-rule
    layer. -/
def FirstOrderWeightedADProbLogProgram.toFirstOrderNormalProgram
    {σ : LPSignature} {n : ℕ}
    (prog : FirstOrderWeightedADProbLogProgram σ n) :
    FirstOrderNormalProbLogProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  rules := prog.rules
  facts_injective := prog.facts_injective
  normalRules := prog.normalRules

/-- Forget the AD probabilities and reuse the existing first-order AD surface. -/
def FirstOrderWeightedADProbLogProgram.toUnweightedFirstOrderADProgram
    {σ : LPSignature} {n : ℕ}
    (prog : FirstOrderWeightedADProbLogProgram σ n) :
    FirstOrderADProbLogProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  rules := prog.rules
  facts_injective := prog.facts_injective
  normalRules := prog.normalRules
  annotatedDisjunctions :=
    prog.annotatedDisjunctions.map
      FirstOrderWeightedAnnotatedDisjunction.toFirstOrderAnnotatedDisjunction

/-- Enumerate all grounded AD instances by grounding each source AD with every
    grounding substitution. -/
noncomputable def FirstOrderADProbLogProgram.groundedADInstances
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n) :
    List (GroundedFirstOrderADInstance σ) :=
  prog.annotatedDisjunctions.flatMap fun ad =>
    (Fintype.elems (α := Grounding σ)).toList.map fun g =>
      { source := ad, grounding := g }

/-- Enumerate all grounded weighted AD instances by grounding each weighted
    source AD with every grounding substitution. -/
noncomputable def FirstOrderWeightedADProbLogProgram.groundedWeightedADInstances
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) :
    List (GroundedFirstOrderWeightedADInstance σ) :=
  prog.annotatedDisjunctions.flatMap fun ad =>
    (Fintype.elems (α := Grounding σ)).toList.map fun g =>
      { source := ad, grounding := g }

/-- Expand all grounded AD instances into normal clauses using the existing
    ground `expandAD` translation. -/
noncomputable def FirstOrderADProbLogProgram.expandGroundedADInstances
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ) :
    List (NormalClause σ) :=
  prog.groundedADInstances.flatMap fun inst =>
    expandAD inst.toGroundAD (auxAtoms inst)

/-- Ground and expand the first-order AD surface into the existing ground
    normal-program layer. -/
noncomputable def FirstOrderADProbLogProgram.toGroundExpandedNormalProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ) :
    NormalProbLogProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  rules := prog.rules
  facts_injective := prog.facts_injective
  normalRules :=
    prog.toFirstOrderNormalProgram.toGroundNormalProgram.normalRules ++
    prog.expandGroundedADInstances auxAtoms

/-- The explicit grounded-expanded AD program is stratified by `s`. -/
def FirstOrderADProbLogProgram.GroundedExpandedStratified
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (s : Stratification σ) : Prop :=
  ∀ c ∈ (prog.toGroundExpandedNormalProgram auxAtoms).normalRules, respectsStratification c s

/-- Query semantics for the first-order AD surface: ground and expand, then use
    the existing ground normal-program semantics. -/
noncomputable def queryHoldsGroundedADA
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (s : Stratification σ) (q : GroundAtom σ) (a : Fin n → Bool) : Prop :=
  queryHoldsNormalA (prog.toGroundExpandedNormalProgram auxAtoms) s q a

/-- Goal-literal interpretation for the grounded-expanded AD surface. -/
noncomputable def GoalLit.holdsGroundedAD
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (s : Stratification σ) (a : Fin n → Bool) : GoalLit σ → Prop :=
  GoalLit.holdsNormal (prog.toGroundExpandedNormalProgram auxAtoms) s a

/-- First-order goal-literal interpretation for the grounded-expanded AD
    surface. -/
noncomputable def FirstOrderGoalLit.holdsGroundedAD
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (goalGrounding : Grounding σ)
    (s : Stratification σ) (a : Fin n → Bool) : FirstOrderGoalLit σ → Prop
  | g => GoalLit.holdsGroundedAD prog auxAtoms s a (goalGrounding.groundFirstOrderGoalLit g)

@[simp] theorem queryHoldsGroundedADA_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (s : Stratification σ) (q : GroundAtom σ) (a : Fin n → Bool) :
    queryHoldsGroundedADA prog auxAtoms s q a =
      queryHoldsNormalA (prog.toGroundExpandedNormalProgram auxAtoms) s q a := rfl

@[simp] theorem GoalLit.holdsGroundedAD_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (s : Stratification σ) (a : Fin n → Bool) (g : GoalLit σ) :
    GoalLit.holdsGroundedAD prog auxAtoms s a g =
      GoalLit.holdsNormal (prog.toGroundExpandedNormalProgram auxAtoms) s a g := rfl

@[simp] theorem FirstOrderGoalLit.holdsGroundedAD_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (goalGrounding : Grounding σ)
    (s : Stratification σ) (a : Fin n → Bool) (g : FirstOrderGoalLit σ) :
    FirstOrderGoalLit.holdsGroundedAD prog auxAtoms goalGrounding s a g =
      GoalLit.holdsGroundedAD prog auxAtoms s a (goalGrounding.groundFirstOrderGoalLit g) := rfl

/-- **First-order AD ProbLog equivalence via grounding and expansion.**

    This is the first-order surface lift of the current ground AD/normal crown
    theorem: first ground the normal rules and ADs, expand the ADs into normal
    clauses, then apply the existing ground theorem. -/
theorem problog_functionFree_ad_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (s : Stratification σ)
    (_hstrat : prog.GroundedExpandedStratified auxAtoms s)
    (goalsQ goalsE : List (GoalLit σ))
    (env : Fin n → ENNReal) (henv : ∀ i, env i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, GoalLit.holdsGroundedAD prog auxAtoms s a g) ∧
      assignmentWeight env a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE env ≠ 0 ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE, GoalLit.holdsGroundedAD prog auxAtoms s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE, GoalLit.holdsGroundedAD prog auxAtoms s a g) := by
  simpa using
    (problog_full_ground_equivalence
      (prog.toGroundExpandedNormalProgram auxAtoms) s goalsQ goalsE env henv hEpos)

/-- **First-order AD ProbLog surface equivalence via grounding and expansion.**

    This lifts `problog_functionFree_ad_equivalence` to first-order query and
    evidence goals by grounding those goals explicitly before invoking the
    existing ground AD/normal bridge. -/
theorem problog_functionFree_ad_surface_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderADProbLogProgram σ n)
    (auxAtoms : (inst : GroundedFirstOrderADInstance σ) →
      Fin inst.toGroundAD.heads.length → GroundAtom σ)
    (s : Stratification σ)
    (_hstrat : prog.GroundedExpandedStratified auxAtoms s)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (env : Fin n → ENNReal) (henv : ∀ i, env i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, FirstOrderGoalLit.holdsGroundedAD prog auxAtoms goalGrounding s a g) ∧
      assignmentWeight env a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE env ≠ 0 ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsGroundedAD prog auxAtoms goalGrounding s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsGroundedAD prog auxAtoms goalGrounding s a g) := by
  obtain ⟨a, haE, haw⟩ := hEpos
  have hEposGround :
      ∃ a : Fin n → Bool,
        (∀ g ∈ goalGrounding.groundFirstOrderGoals goalsE,
          GoalLit.holdsGroundedAD prog auxAtoms s a g) ∧
        assignmentWeight env a ≠ 0 := by
    refine ⟨a, ?_, haw⟩
    rw [Grounding.forall_mem_groundFirstOrderGoals_iff]
    simpa [FirstOrderGoalLit.holdsGroundedAD] using haE
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    problog_functionFree_ad_equivalence
      prog auxAtoms s _hstrat
      (goalGrounding.groundFirstOrderGoals goalsQ)
      (goalGrounding.groundFirstOrderGoals goalsE)
      env henv hEposGround
  refine ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, ?_, ?_⟩
  · intro a'
    constructor
    · intro hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals (goalsQ ++ goalsE),
            GoalLit.holdsGroundedAD prog auxAtoms s a' g := by
        simpa [Grounding.groundFirstOrderGoals, List.map_append] using (hiffQE a').mp hf
      have hFirstOrder :
          ∀ g ∈ goalsQ ++ goalsE,
            GoalLit.holdsGroundedAD prog auxAtoms s a'
              (goalGrounding.groundFirstOrderGoalLit g) :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding (goalsQ ++ goalsE)
          (fun g => GoalLit.holdsGroundedAD prog auxAtoms s a' g)).1 hGround
      simpa [FirstOrderGoalLit.holdsGroundedAD] using hFirstOrder
    · intro hf
      have hFirstOrder :
          ∀ g ∈ goalsQ ++ goalsE,
            GoalLit.holdsGroundedAD prog auxAtoms s a'
              (goalGrounding.groundFirstOrderGoalLit g) := by
        simpa [FirstOrderGoalLit.holdsGroundedAD] using hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals (goalsQ ++ goalsE),
            GoalLit.holdsGroundedAD prog auxAtoms s a' g :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding (goalsQ ++ goalsE)
          (fun g => GoalLit.holdsGroundedAD prog auxAtoms s a' g)).2 hFirstOrder
      exact (hiffQE a').2 (by
        simpa [Grounding.groundFirstOrderGoals, List.map_append] using hGround)
  · intro a'
    constructor
    · intro hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals goalsE,
            GoalLit.holdsGroundedAD prog auxAtoms s a' g := (hiffE a').mp hf
      have hFirstOrder :
          ∀ g ∈ goalsE,
            GoalLit.holdsGroundedAD prog auxAtoms s a'
              (goalGrounding.groundFirstOrderGoalLit g) :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding goalsE
          (fun g => GoalLit.holdsGroundedAD prog auxAtoms s a' g)).1 hGround
      simpa [FirstOrderGoalLit.holdsGroundedAD] using hFirstOrder
    · intro hf
      have hFirstOrder :
          ∀ g ∈ goalsE,
            GoalLit.holdsGroundedAD prog auxAtoms s a'
              (goalGrounding.groundFirstOrderGoalLit g) := by
        simpa [FirstOrderGoalLit.holdsGroundedAD] using hf
      exact (hiffE a').2
        ((Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding goalsE
          (fun g => GoalLit.holdsGroundedAD prog auxAtoms s a' g)).2 hFirstOrder)

/-- A bundled compilation witness for a weighted first-order AD program.

    It chooses which existing probabilistic facts play the role of the
    auxiliary switches for each grounded AD occurrence of `prog`, and records
    the intended calibration/freshness properties for those switches on the
    grounded instances that actually arise from `prog`. -/
structure FirstOrderWeightedADCompilation
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) where
  switchSlot :
    (inst : GroundedFirstOrderWeightedADInstance σ) →
      Fin inst.toGroundWeightedAD.heads.length → Fin n
  slotInjective :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → Function.Injective (switchSlot inst)
  fresh_heads :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → ∀ i,
      prog.probFacts (switchSlot inst i) ∉ inst.toGroundAD.heads
  fresh_body :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → ∀ i,
      prog.probFacts (switchSlot inst i) ∉ inst.toGroundAD.body
  calibrated :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → ∀ i,
      prog.probs (switchSlot inst i) = switchProb inst.toGroundWeightedAD.probs i

/-- The auxiliary ground atom chosen for a particular grounded weighted AD
    occurrence and head. -/
def FirstOrderWeightedADCompilation.auxAtom
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (comp : FirstOrderWeightedADCompilation prog)
    (inst : GroundedFirstOrderWeightedADInstance σ)
    (i : Fin inst.toGroundWeightedAD.heads.length) : GroundAtom σ :=
  prog.probFacts (comp.switchSlot inst i)

/-- Expand all grounded weighted AD instances into normal clauses using the
    auxiliary switches chosen by `comp`. -/
noncomputable def FirstOrderWeightedADProbLogProgram.expandGroundedWeightedADInstances
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog) :
    List (NormalClause σ) :=
  prog.groundedWeightedADInstances.flatMap fun inst =>
    expandAD inst.toGroundAD (FirstOrderWeightedADCompilation.auxAtom comp inst)

/-- Ground and expand the weighted first-order AD surface into the existing
    ground normal-program layer using the switches chosen by `comp`. -/
noncomputable def FirstOrderWeightedADProbLogProgram.toGroundExpandedNormalProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog) :
    NormalProbLogProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  rules := prog.rules
  facts_injective := prog.facts_injective
  normalRules :=
    prog.toFirstOrderNormalProgram.toGroundNormalProgram.normalRules ++
    prog.expandGroundedWeightedADInstances comp

/-- The explicitly grounded-expanded weighted AD program is stratified by `s`. -/
def FirstOrderWeightedADCompilation.GroundedExpandedStratified
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) : Prop :=
  ∀ c ∈ (prog.toGroundExpandedNormalProgram comp).normalRules, respectsStratification c s

/-- The AD-expanded part of a weighted first-order compilation respects `s`
    when every clause produced from every grounded AD instance does so. -/
def FirstOrderWeightedADCompilation.GroundedADRulesRespectStratification
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) : Prop :=
  ∀ inst c,
    inst ∈ prog.groundedWeightedADInstances →
    c ∈ expandAD inst.toGroundAD
      (FirstOrderWeightedADCompilation.auxAtom comp inst) →
    respectsStratification c s

/-- Every positive body atom of a grounded weighted AD lies at or below every
    head atom's stratum. This is a structured sufficient condition for the
    positive body part of the expansion to respect `s`. -/
def GroundedFirstOrderWeightedADInstance.BodyLeAllHeads
    {σ : LPSignature}
    (inst : GroundedFirstOrderWeightedADInstance σ)
    (s : Stratification σ) : Prop :=
  ∀ a ∈ inst.toGroundAD.body,
    ∀ i : Fin inst.toGroundWeightedAD.heads.length,
      s a ≤ s (inst.toGroundWeightedAD.heads.get i)

/-- Every auxiliary switch chosen for a grounded weighted AD lies strictly below
    every head atom's stratum. This is a structured sufficient condition for
    both the positive switch literal and the negative NAF guards introduced by
    the AD expansion. -/
def GroundedFirstOrderWeightedADInstance.AuxLtAllHeads
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (inst : GroundedFirstOrderWeightedADInstance σ)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) : Prop :=
  ∀ j i,
    s (FirstOrderWeightedADCompilation.auxAtom comp inst j) <
      s (inst.toGroundWeightedAD.heads.get i)

/-- Structured grounded AD stratification data for a weighted compilation. -/
def FirstOrderWeightedADCompilation.StructuredGroundedADStratification
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) : Prop :=
  ∀ inst, inst ∈ prog.groundedWeightedADInstances →
    inst.BodyLeAllHeads s ∧
      GroundedFirstOrderWeightedADInstance.AuxLtAllHeads inst comp s

/-- Under the structured body/auxiliary stratum conditions, every clause
    generated by expanding a grounded weighted AD respects `s`. -/
theorem GroundedFirstOrderWeightedADInstance.expandAD_respectsStratification
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (inst : GroundedFirstOrderWeightedADInstance σ)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ)
    (hbody : inst.BodyLeAllHeads s)
    (haux : GroundedFirstOrderWeightedADInstance.AuxLtAllHeads inst comp s) :
    ∀ c ∈ expandAD inst.toGroundAD
        (FirstOrderWeightedADCompilation.auxAtom comp inst), respectsStratification c s := by
  intro c hc g hg
  simp only [expandAD, List.mem_map, List.mem_finRange] at hc
  obtain ⟨idx, _, rfl⟩ := hc
  have hbody_mem := List.mem_append.mp hg
  rcases hbody_mem with hbody_part | hguard_part
  · have hbody_mem2 := List.mem_append.mp hbody_part
    rcases hbody_mem2 with hmap | hsingle
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmap
      have := hbody a ha idx
      simpa [GroundedFirstOrderWeightedADInstance.toGroundAD,
        GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD,
        WeightedAnnotatedDisjunction.toAnnotatedDisjunction] using this
    · rcases List.mem_cons.mp hsingle with rfl | h
      · exact le_of_lt (haux idx idx)
      · exact absurd h (by simp)
  · obtain ⟨fi, hgeq⟩ :=
      nafGuardPrefix_mem_neg (FirstOrderWeightedADCompilation.auxAtom comp inst) idx.val g hguard_part
    rw [hgeq]
    exact haux fi idx

/-- The structured body/auxiliary stratification data implies that all
    grounded AD-expanded rules respect `s`. -/
theorem FirstOrderWeightedADCompilation.groundedADRulesRespectStratification_of_structured
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ)
    (hstructured : comp.StructuredGroundedADStratification s) :
    comp.GroundedADRulesRespectStratification s := by
  intro inst c hinst hc
  obtain ⟨hbody, haux⟩ := hstructured inst hinst
  exact inst.expandAD_respectsStratification comp s hbody haux c hc

/-- Build stratification of the full grounded-expanded program from separate
    stratification facts for the grounded normal rules and the AD-expanded
    rules. -/
theorem FirstOrderWeightedADCompilation.groundedExpandedStratified_of_parts
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ)
    (hnormal : prog.toFirstOrderNormalProgram.GroundedStratified s)
    (hAD : comp.GroundedADRulesRespectStratification s) :
    comp.GroundedExpandedStratified s := by
  intro c hc
  unfold FirstOrderWeightedADProbLogProgram.toGroundExpandedNormalProgram at hc
  simp only at hc
  rcases List.mem_append.mp hc with hnormalMem | hADMem
  · exact hnormal c hnormalMem
  · unfold FirstOrderWeightedADProbLogProgram.expandGroundedWeightedADInstances at hADMem
    rw [List.mem_flatMap] at hADMem
    obtain ⟨inst, hinst, hcinst⟩ := hADMem
    exact hAD inst c hinst hcinst

/-- A compiled weighted first-order AD program packages the switch-layout
    witness together with the stratification proof needed by the operational
    bridge theorems. -/
structure FirstOrderWeightedADCompiledProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) where
  comp : FirstOrderWeightedADCompilation prog
  stratification : Stratification σ
  groundedExpandedStratified : comp.GroundedExpandedStratified stratification

/-- The existing ground normal-program layer produced by a compiled weighted
    first-order AD program. -/
noncomputable def FirstOrderWeightedADCompiledProgram.toGroundExpandedNormalProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog) :
    NormalProbLogProgram σ n :=
  prog.toGroundExpandedNormalProgram compiled.comp

/-- Construct a compiled weighted first-order AD program from separate
    stratification proofs for the grounded normal layer and the AD-expanded
    layer. -/
def FirstOrderWeightedADCompiledProgram.ofParts
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ)
    (hnormal : prog.toFirstOrderNormalProgram.GroundedStratified s)
    (hAD : comp.GroundedADRulesRespectStratification s) :
    FirstOrderWeightedADCompiledProgram prog where
  comp := comp
  stratification := s
  groundedExpandedStratified :=
    comp.groundedExpandedStratified_of_parts s hnormal hAD

/-- A more compositional compiled weighted first-order AD package: instead of
    asking for stratification of the fully expanded program, it stores the
    grounded normal stratification and the structured grounded-AD stratification
    separately. -/
structure FirstOrderWeightedADStructuredCompiledProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) where
  comp : FirstOrderWeightedADCompilation prog
  stratification : Stratification σ
  normalGroundedStratified :
    prog.toFirstOrderNormalProgram.GroundedStratified stratification
  structuredGroundedADStratification :
    comp.StructuredGroundedADStratification stratification

/-- Forget the compositional proof packaging and recover the compiled weighted
    first-order AD program object used by the main bridge theorems. -/
def FirstOrderWeightedADStructuredCompiledProgram.toCompiledProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADStructuredCompiledProgram prog) :
    FirstOrderWeightedADCompiledProgram prog :=
  FirstOrderWeightedADCompiledProgram.ofParts compiled.comp compiled.stratification
    compiled.normalGroundedStratified
    (compiled.comp.groundedADRulesRespectStratification_of_structured
      compiled.stratification compiled.structuredGroundedADStratification)

/-- Query semantics for a weighted first-order AD program compiled using
    `comp`: ground and expand, then use the existing normal-program semantics. -/
noncomputable def queryHoldsCompiledWeightedADA
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) (q : GroundAtom σ) (a : Fin n → Bool) : Prop :=
  queryHoldsNormalA (prog.toGroundExpandedNormalProgram comp) s q a

/-- Goal interpretation for a weighted first-order AD program compiled using
    `comp`. -/
noncomputable def GoalLit.holdsCompiledWeightedAD
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) (a : Fin n → Bool) : GoalLit σ → Prop :=
  GoalLit.holdsNormal (prog.toGroundExpandedNormalProgram comp) s a

@[simp] theorem queryHoldsCompiledWeightedADA_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) (q : GroundAtom σ) (a : Fin n → Bool) :
    queryHoldsCompiledWeightedADA prog comp s q a =
      queryHoldsNormalA (prog.toGroundExpandedNormalProgram comp) s q a := rfl

@[simp] theorem GoalLit.holdsCompiledWeightedAD_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ) (a : Fin n → Bool) (g : GoalLit σ) :
    GoalLit.holdsCompiledWeightedAD prog comp s a g =
      GoalLit.holdsNormal (prog.toGroundExpandedNormalProgram comp) s a g := rfl

/-- Goal interpretation for a weighted first-order AD program compiled using
    `comp`. -/
noncomputable def FirstOrderGoalLit.holdsCompiledWeightedAD
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (goalGrounding : Grounding σ)
    (s : Stratification σ) (a : Fin n → Bool) : FirstOrderGoalLit σ → Prop :=
  GoalLit.holdsCompiledWeightedAD prog comp s a ∘ goalGrounding.groundFirstOrderGoalLit

/-- Query semantics for a compiled weighted first-order AD program. -/
noncomputable def FirstOrderWeightedADCompiledProgram.queryHoldsA
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog)
    (q : GroundAtom σ) (a : Fin n → Bool) : Prop :=
  queryHoldsNormalA compiled.toGroundExpandedNormalProgram compiled.stratification q a

/-- Goal interpretation for a compiled weighted first-order AD program. -/
noncomputable def GoalLit.holdsCompiledWeightedADProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog)
    (a : Fin n → Bool) : GoalLit σ → Prop :=
  GoalLit.holdsNormal compiled.toGroundExpandedNormalProgram compiled.stratification a

/-- First-order goal interpretation for a compiled weighted first-order AD
    program. -/
noncomputable def FirstOrderGoalLit.holdsCompiledWeightedADProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog)
    (goalGrounding : Grounding σ)
    (a : Fin n → Bool) : FirstOrderGoalLit σ → Prop :=
  GoalLit.holdsCompiledWeightedADProgram compiled a ∘ goalGrounding.groundFirstOrderGoalLit

@[simp] theorem FirstOrderGoalLit.holdsCompiledWeightedAD_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (goalGrounding : Grounding σ)
    (s : Stratification σ) (a : Fin n → Bool) (g : FirstOrderGoalLit σ) :
    FirstOrderGoalLit.holdsCompiledWeightedAD prog comp goalGrounding s a g =
      GoalLit.holdsCompiledWeightedAD prog comp s a
        (goalGrounding.groundFirstOrderGoalLit g) := rfl

@[simp] theorem FirstOrderWeightedADCompiledProgram.queryHoldsA_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog)
    (q : GroundAtom σ) (a : Fin n → Bool) :
    compiled.queryHoldsA q a =
      queryHoldsCompiledWeightedADA prog compiled.comp compiled.stratification q a := rfl

@[simp] theorem GoalLit.holdsCompiledWeightedADProgram_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog)
    (a : Fin n → Bool) (g : GoalLit σ) :
    GoalLit.holdsCompiledWeightedADProgram compiled a g =
      GoalLit.holdsCompiledWeightedAD prog compiled.comp compiled.stratification a g := rfl

@[simp] theorem FirstOrderGoalLit.holdsCompiledWeightedADProgram_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog)
    (goalGrounding : Grounding σ)
    (a : Fin n → Bool) (g : FirstOrderGoalLit σ) :
    FirstOrderGoalLit.holdsCompiledWeightedADProgram compiled goalGrounding a g =
      FirstOrderGoalLit.holdsCompiledWeightedAD
        prog compiled.comp goalGrounding compiled.stratification a g := rfl

/-- **Operational weighted first-order AD surface theorem.**

    This is the strongest current user-facing theorem: a function-free
    first-order program with weighted AD syntax, first-order queries/evidence,
    and a bundled switch compilation witness reduces to the proved ground
    AD/normal bridge using the program's own probabilistic fact weights. -/
theorem problog_functionFree_weighted_ad_surface_equivalence
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ)
    (_hstrat : comp.GroundedExpandedStratified s)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, FirstOrderGoalLit.holdsCompiledWeightedAD prog comp goalGrounding s a g) ∧
      assignmentWeight prog.probs a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE prog.probs ≠ 0 ∧
      bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
        weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedAD prog comp goalGrounding s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedAD prog comp goalGrounding s a g) := by
  obtain ⟨a, haE, haw⟩ := hEpos
  have hEposGround :
      ∃ a : Fin n → Bool,
        (∀ g ∈ goalGrounding.groundFirstOrderGoals goalsE,
          GoalLit.holdsCompiledWeightedAD prog comp s a g) ∧
        assignmentWeight prog.probs a ≠ 0 := by
    refine ⟨a, ?_, haw⟩
    rw [Grounding.forall_mem_groundFirstOrderGoals_iff]
    simpa [FirstOrderGoalLit.holdsCompiledWeightedAD] using haE
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    problog_full_ground_equivalence
      (prog.toGroundExpandedNormalProgram comp) s
      (goalGrounding.groundFirstOrderGoals goalsQ)
      (goalGrounding.groundFirstOrderGoals goalsE)
      prog.probs hprobs hEposGround
  refine ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, ?_, ?_⟩
  · intro a'
    constructor
    · intro hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals (goalsQ ++ goalsE),
            GoalLit.holdsCompiledWeightedAD prog comp s a' g := by
        simpa [Grounding.groundFirstOrderGoals, List.map_append] using (hiffQE a').mp hf
      have hFirstOrder :
          ∀ g ∈ goalsQ ++ goalsE,
            GoalLit.holdsCompiledWeightedAD prog comp s a'
              (goalGrounding.groundFirstOrderGoalLit g) :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding (goalsQ ++ goalsE)
          (fun g => GoalLit.holdsCompiledWeightedAD prog comp s a' g)).1 hGround
      simpa [FirstOrderGoalLit.holdsCompiledWeightedAD] using hFirstOrder
    · intro hf
      have hFirstOrder :
          ∀ g ∈ goalsQ ++ goalsE,
            GoalLit.holdsCompiledWeightedAD prog comp s a'
              (goalGrounding.groundFirstOrderGoalLit g) := by
        simpa [FirstOrderGoalLit.holdsCompiledWeightedAD] using hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals (goalsQ ++ goalsE),
            GoalLit.holdsCompiledWeightedAD prog comp s a' g :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding (goalsQ ++ goalsE)
          (fun g => GoalLit.holdsCompiledWeightedAD prog comp s a' g)).2 hFirstOrder
      exact (hiffQE a').2 (by
        simpa [Grounding.groundFirstOrderGoals, List.map_append] using hGround)
  · intro a'
    constructor
    · intro hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals goalsE,
            GoalLit.holdsCompiledWeightedAD prog comp s a' g := (hiffE a').mp hf
      have hFirstOrder :
          ∀ g ∈ goalsE,
            GoalLit.holdsCompiledWeightedAD prog comp s a'
              (goalGrounding.groundFirstOrderGoalLit g) :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding goalsE
          (fun g => GoalLit.holdsCompiledWeightedAD prog comp s a' g)).1 hGround
      simpa [FirstOrderGoalLit.holdsCompiledWeightedAD] using hFirstOrder
    · intro hf
      have hFirstOrder :
          ∀ g ∈ goalsE,
            GoalLit.holdsCompiledWeightedAD prog comp s a'
              (goalGrounding.groundFirstOrderGoalLit g) := by
        simpa [FirstOrderGoalLit.holdsCompiledWeightedAD] using hf
      exact (hiffE a').2
        ((Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding goalsE
          (fun g => GoalLit.holdsCompiledWeightedAD prog comp s a' g)).2 hFirstOrder)

/-- **Operational weighted first-order AD theorem for packaged compiled
    programs.**

    This is the same theorem as
    `problog_functionFree_weighted_ad_surface_equivalence`, but phrased around a
    compiled program object so downstream callers do not need to thread the
    compilation witness and stratification proof separately. -/
theorem FirstOrderWeightedADCompiledProgram.surface_equivalence
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADCompiledProgram prog)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram compiled goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE prog.probs ≠ 0 ∧
      bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
        weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram compiled goalGrounding a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram compiled goalGrounding a g) := by
  have hEpos' :
      ∃ a : Fin n → Bool,
        (∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedAD
            prog compiled.comp goalGrounding compiled.stratification a g) ∧
        assignmentWeight prog.probs a ≠ 0 := by
    simpa [FirstOrderGoalLit.holdsCompiledWeightedADProgram_eq] using hEpos
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    problog_functionFree_weighted_ad_surface_equivalence
      prog compiled.comp compiled.stratification compiled.groundedExpandedStratified
      goalGrounding goalsQ goalsE hprobs hEpos'
  refine ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, ?_, ?_⟩
  · intro a
    simpa [FirstOrderGoalLit.holdsCompiledWeightedADProgram_eq] using hiffQE a
  · intro a
    simpa [FirstOrderGoalLit.holdsCompiledWeightedADProgram_eq] using hiffE a

/-- **Operational weighted first-order AD theorem for compositional compiled
    programs.**

    This packages the grounded normal stratification and the structured
    grounded-AD stratification separately, then recovers the ordinary compiled
    program bridge automatically. -/
theorem FirstOrderWeightedADStructuredCompiledProgram.surface_equivalence
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (compiled : FirstOrderWeightedADStructuredCompiledProgram prog)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          compiled.toCompiledProgram goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE prog.probs ≠ 0 ∧
      bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
        weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            compiled.toCompiledProgram goalGrounding a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            compiled.toCompiledProgram goalGrounding a g) := by
  simpa using
    (FirstOrderWeightedADCompiledProgram.surface_equivalence
      (compiled := compiled.toCompiledProgram)
      goalGrounding goalsQ goalsE hprobs hEpos)

/-- Source-level auxiliary-switch stratification using raw switch-slot data,
    before packaging that data into a `FirstOrderWeightedADCompilation`. -/
def GroundedFirstOrderWeightedADInstance.AuxLtAllHeadsUsingSwitchSlot
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (inst : GroundedFirstOrderWeightedADInstance σ)
    (switchSlot :
      (inst : GroundedFirstOrderWeightedADInstance σ) →
        Fin inst.toGroundWeightedAD.heads.length → Fin n)
    (s : Stratification σ) : Prop :=
  ∀ j i,
    s (prog.probFacts (switchSlot inst j)) <
      s (inst.toGroundWeightedAD.heads.get i)

/-- Source-level structured compilation data for a weighted first-order AD
    program.

    This is slightly more primitive than
    `FirstOrderWeightedADStructuredCompiledProgram`: it records the switch-slot
    assignment and all source-facing proof obligations directly, then builds the
    packaged compiled-program witness canonically. -/
structure FirstOrderWeightedADSourceStructuredCompilation
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) where
  switchSlot :
    (inst : GroundedFirstOrderWeightedADInstance σ) →
      Fin inst.toGroundWeightedAD.heads.length → Fin n
  stratification : Stratification σ
  normalGroundedStratified :
    prog.toFirstOrderNormalProgram.GroundedStratified stratification
  slotInjective :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → Function.Injective (switchSlot inst)
  fresh_heads :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → ∀ i,
      prog.probFacts (switchSlot inst i) ∉ inst.toGroundAD.heads
  fresh_body :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → ∀ i,
      prog.probFacts (switchSlot inst i) ∉ inst.toGroundAD.body
  calibrated :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances → ∀ i,
      prog.probs (switchSlot inst i) = switchProb inst.toGroundWeightedAD.probs i
  bodyLeAllHeads :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances →
      inst.BodyLeAllHeads stratification
  auxLtAllHeads :
    ∀ inst, inst ∈ prog.groundedWeightedADInstances →
      GroundedFirstOrderWeightedADInstance.AuxLtAllHeadsUsingSwitchSlot
        (prog := prog) inst switchSlot stratification

/-- Package source-level structured compilation data into the existing
    compilation witness object. -/
def FirstOrderWeightedADSourceStructuredCompilation.toCompilation
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (data : FirstOrderWeightedADSourceStructuredCompilation prog) :
    FirstOrderWeightedADCompilation prog where
  switchSlot := data.switchSlot
  slotInjective := data.slotInjective
  fresh_heads := data.fresh_heads
  fresh_body := data.fresh_body
  calibrated := data.calibrated

/-- The raw source-level body/head and switch/head obligations imply the
    structured grounded-AD stratification needed by the compiled-program
    interface. -/
theorem FirstOrderWeightedADSourceStructuredCompilation.structuredGroundedADStratification
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (data : FirstOrderWeightedADSourceStructuredCompilation prog) :
    data.toCompilation.StructuredGroundedADStratification data.stratification := by
  intro inst hinst
  refine ⟨data.bodyLeAllHeads inst hinst, ?_⟩
  intro j i
  exact data.auxLtAllHeads inst hinst j i

/-- Canonically package source-level structured compilation data into the
    proof-carrying compiled-program object used by the main bridge theorems. -/
def FirstOrderWeightedADSourceStructuredCompilation.toStructuredCompiledProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (data : FirstOrderWeightedADSourceStructuredCompilation prog) :
    FirstOrderWeightedADStructuredCompiledProgram prog where
  comp := data.toCompilation
  stratification := data.stratification
  normalGroundedStratified := data.normalGroundedStratified
  structuredGroundedADStratification := data.structuredGroundedADStratification

/-- Source-level structured compilation data suffices to invoke the full
    weighted first-order AD surface theorem. -/
theorem FirstOrderWeightedADSourceStructuredCompilation.surface_equivalence
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (data : FirstOrderWeightedADSourceStructuredCompilation prog)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE prog.probs ≠ 0 ∧
      bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
        weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) := by
  simpa using
    (FirstOrderWeightedADStructuredCompiledProgram.surface_equivalence
      (compiled := data.toStructuredCompiledProgram)
      goalGrounding goalsQ goalsE hprobs hEpos)

/-- A weighted first-order AD program is source-structurably compilable when
    some source-level structured compilation data exists for it. -/
def FirstOrderWeightedADProbLogProgram.SourceStructurablyCompilable
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) : Prop :=
  Nonempty (FirstOrderWeightedADSourceStructuredCompilation prog)

/-- Evidence is satisfiable under some source-level structured compilation
    data. -/
def FirstOrderWeightedADProbLogProgram.SourceStructuredEvidenceSatisfiable
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (goalsE : List (FirstOrderGoalLit σ)) : Prop :=
  ∃ data : FirstOrderWeightedADSourceStructuredCompilation prog,
    ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0

/-- Existence-style source-level structured surface theorem. -/
theorem exists_surface_equivalence_of_sourceStructuredEvidenceSatisfiable
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hsat : prog.SourceStructuredEvidenceSatisfiable goalGrounding goalsE) :
    ∃ data : FirstOrderWeightedADSourceStructuredCompilation prog,
      ∃ fQE fE : BDD n,
        fQE.Ordered none ∧ fE.Ordered none ∧
        bdd_wmc fE prog.probs ≠ 0 ∧
        bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
          weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
        (∀ a, fQE.eval a = true ↔
          ∀ g ∈ goalsQ ++ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) ∧
        (∀ a, fE.eval a = true ↔
          ∀ g ∈ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) := by
  rcases hsat with ⟨data, a, haE, haw⟩
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    data.surface_equivalence goalGrounding goalsQ goalsE hprobs ⟨a, haE, haw⟩
  exact ⟨data, fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩

/-- A grounded weighted AD instance is locally structurably compilable at `s`
    when its body atoms lie below its heads and there exists a switch-slot
    assignment satisfying freshness, calibration, and auxiliary/head stratum
    separation for that single instance. -/
def GroundedFirstOrderWeightedADInstance.LocallyStructurablyCompilable
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (inst : GroundedFirstOrderWeightedADInstance σ)
    (s : Stratification σ) : Prop :=
  inst.BodyLeAllHeads s ∧
    ∃ switchSlot : Fin inst.toGroundWeightedAD.heads.length → Fin n,
      Function.Injective switchSlot ∧
      (∀ i, prog.probFacts (switchSlot i) ∉ inst.toGroundAD.heads) ∧
      (∀ i, prog.probFacts (switchSlot i) ∉ inst.toGroundAD.body) ∧
      (∀ i, prog.probs (switchSlot i) = switchProb inst.toGroundWeightedAD.probs i) ∧
      (∀ j i,
        s (prog.probFacts (switchSlot j)) <
          s (inst.toGroundWeightedAD.heads.get i))

/-- A weighted first-order AD program is locally structurably compilable when
    some stratification makes the grounded normal layer stratified and every
    grounded AD instance individually admits a compatible switch-slot
    assignment. -/
def FirstOrderWeightedADProbLogProgram.LocallyStructurablyCompilable
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) : Prop :=
  ∃ s : Stratification σ,
    prog.toFirstOrderNormalProgram.GroundedStratified s ∧
    ∀ inst, inst ∈ prog.groundedWeightedADInstances →
      GroundedFirstOrderWeightedADInstance.LocallyStructurablyCompilable
        (prog := prog) inst s

/-- Choose a source-level structured compilation witness automatically from
    local per-grounded-instance compilability data. For grounded AD instances
    not arising from `prog`, the chosen switch-slot function falls back to a
    constant default slot and is never used by the correctness theorems. -/
noncomputable def FirstOrderWeightedADProbLogProgram.chooseSourceStructuredCompilation
    {σ : LPSignature} {n : ℕ}
    [Nonempty (Fin n)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    {prog : FirstOrderWeightedADProbLogProgram σ n}
    (hcomp : prog.LocallyStructurablyCompilable) :
    FirstOrderWeightedADSourceStructuredCompilation prog := by
  classical
  let s : Stratification σ := Classical.choose hcomp
  have hspec := Classical.choose_spec hcomp
  have hnormal : prog.toFirstOrderNormalProgram.GroundedStratified s := hspec.1
  have hlocal :
      ∀ inst, inst ∈ prog.groundedWeightedADInstances →
        GroundedFirstOrderWeightedADInstance.LocallyStructurablyCompilable
          (prog := prog) inst s := hspec.2
  let defaultSlot : Fin n := Classical.choice inferInstance
  let switchSlot :
      (inst : GroundedFirstOrderWeightedADInstance σ) →
        Fin inst.toGroundWeightedAD.heads.length → Fin n :=
    fun inst =>
      if hinst : inst ∈ prog.groundedWeightedADInstances then
        Classical.choose ((hlocal inst hinst).2)
      else
        fun _ => defaultSlot
  refine
    { switchSlot := switchSlot
      stratification := s
      normalGroundedStratified := hnormal
      slotInjective := ?_
      fresh_heads := ?_
      fresh_body := ?_
      calibrated := ?_
      bodyLeAllHeads := ?_
      auxLtAllHeads := ?_ }
  · intro inst hinst
    have hchosen := Classical.choose_spec ((hlocal inst hinst).2)
    simpa [switchSlot, hinst] using hchosen.1
  · intro inst hinst i
    have hchosen := Classical.choose_spec ((hlocal inst hinst).2)
    simpa [switchSlot, hinst] using hchosen.2.1 i
  · intro inst hinst i
    have hchosen := Classical.choose_spec ((hlocal inst hinst).2)
    simpa [switchSlot, hinst] using hchosen.2.2.1 i
  · intro inst hinst i
    have hchosen := Classical.choose_spec ((hlocal inst hinst).2)
    simpa [switchSlot, hinst] using hchosen.2.2.2.1 i
  · intro inst hinst
    exact (hlocal inst hinst).1
  · intro inst hinst
    have hchosen := Classical.choose_spec ((hlocal inst hinst).2)
    simpa [GroundedFirstOrderWeightedADInstance.AuxLtAllHeadsUsingSwitchSlot,
      switchSlot, hinst] using hchosen.2.2.2.2

/-- Operational weighted first-order AD theorem driven by local per-instance
    compilability assumptions; the global source-structured compilation witness
    is constructed automatically by choice. -/
theorem FirstOrderWeightedADProbLogProgram.surface_equivalence_of_locallyStructurablyCompilable
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Nonempty (Fin n)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (hcomp : prog.LocallyStructurablyCompilable)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          ((prog.chooseSourceStructuredCompilation hcomp).toStructuredCompiledProgram.toCompiledProgram)
          goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE prog.probs ≠ 0 ∧
      bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
        weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            ((prog.chooseSourceStructuredCompilation hcomp).toStructuredCompiledProgram.toCompiledProgram)
            goalGrounding a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            ((prog.chooseSourceStructuredCompilation hcomp).toStructuredCompiledProgram.toCompiledProgram)
            goalGrounding a g) := by
  simpa using
    (FirstOrderWeightedADSourceStructuredCompilation.surface_equivalence
      (data := prog.chooseSourceStructuredCompilation hcomp)
      goalGrounding goalsQ goalsE hprobs hEpos)

/-- Evidence is satisfiable under automatically chosen source-structured
    compilation data coming from local per-instance compilability assumptions. -/
def FirstOrderWeightedADProbLogProgram.LocallyStructuredEvidenceSatisfiable
    {σ : LPSignature} {n : ℕ}
    [Nonempty (Fin n)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (goalsE : List (FirstOrderGoalLit σ)) : Prop :=
  ∃ hcomp : prog.LocallyStructurablyCompilable,
    ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          ((prog.chooseSourceStructuredCompilation hcomp).toStructuredCompiledProgram.toCompiledProgram)
          goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0

/-- Highest-level existence theorem for the automatic local-choice route. -/
theorem exists_surface_equivalence_of_locallyStructuredEvidenceSatisfiable
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Nonempty (Fin n)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hsat : prog.LocallyStructuredEvidenceSatisfiable goalGrounding goalsE) :
    ∃ data : FirstOrderWeightedADSourceStructuredCompilation prog,
      ∃ fQE fE : BDD n,
        fQE.Ordered none ∧ fE.Ordered none ∧
        bdd_wmc fE prog.probs ≠ 0 ∧
        bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
          weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
        (∀ a, fQE.eval a = true ↔
          ∀ g ∈ goalsQ ++ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) ∧
        (∀ a, fE.eval a = true ↔
          ∀ g ∈ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              data.toStructuredCompiledProgram.toCompiledProgram goalGrounding a g) := by
  rcases hsat with ⟨hcomp, a, haE, haw⟩
  let data := prog.chooseSourceStructuredCompilation hcomp
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    prog.surface_equivalence_of_locallyStructurablyCompilable
      hcomp goalGrounding goalsQ goalsE hprobs ⟨a, haE, haw⟩
  exact ⟨data, fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩

/-- A weighted first-order AD program is structurably compilable when some
    compositional compiled-program witness exists for it. -/
def FirstOrderWeightedADProbLogProgram.StructurablyCompilable
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n) : Prop :=
  Nonempty (FirstOrderWeightedADStructuredCompiledProgram prog)

/-- Evidence is satisfiable under some compositional compiled-program witness. -/
def FirstOrderWeightedADProbLogProgram.StructuredEvidenceSatisfiable
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (goalsE : List (FirstOrderGoalLit σ)) : Prop :=
  ∃ compiled : FirstOrderWeightedADStructuredCompiledProgram prog,
    ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          compiled.toCompiledProgram goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0

/-- **Existence-style weighted first-order AD surface theorem.**

    If a weighted first-order AD surface program admits some compiled witness,
    then there exist BDDs realising the corresponding query/evidence semantics.
    This hides the witness from theorem consumers while remaining honest about
    the need for a valid compilation. -/
theorem exists_surface_equivalence_of_exists_compiled
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hexists :
      ∃ compiled : FirstOrderWeightedADCompiledProgram prog,
        ∃ a : Fin n → Bool,
          (∀ g ∈ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram compiled goalGrounding a g) ∧
          assignmentWeight prog.probs a ≠ 0) :
    ∃ compiled : FirstOrderWeightedADCompiledProgram prog,
      ∃ fQE fE : BDD n,
        fQE.Ordered none ∧ fE.Ordered none ∧
        bdd_wmc fE prog.probs ≠ 0 ∧
        bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
          weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
        (∀ a, fQE.eval a = true ↔
          ∀ g ∈ goalsQ ++ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram compiled goalGrounding a g) ∧
        (∀ a, fE.eval a = true ↔
          ∀ g ∈ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram compiled goalGrounding a g) := by
  rcases hexists with ⟨compiled, a, haE, haw⟩
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    compiled.surface_equivalence goalGrounding goalsQ goalsE hprobs ⟨a, haE, haw⟩
  exact ⟨compiled, fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩

/-- **Existence-style weighted first-order AD surface theorem for the
    compositional compiled-program interface.**

    This is the highest-level honest wrapper currently available for the
    compositional route: assume evidence is satisfiable under some structured
    compilation witness, then obtain BDDs realising the query/evidence
    semantics for that witness. -/
theorem exists_surface_equivalence_of_structuredEvidenceSatisfiable
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hsat : prog.StructuredEvidenceSatisfiable goalGrounding goalsE) :
    ∃ compiled : FirstOrderWeightedADStructuredCompiledProgram prog,
      ∃ fQE fE : BDD n,
        fQE.Ordered none ∧ fE.Ordered none ∧
        bdd_wmc fE prog.probs ≠ 0 ∧
        bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
          weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
        (∀ a, fQE.eval a = true ↔
          ∀ g ∈ goalsQ ++ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              compiled.toCompiledProgram goalGrounding a g) ∧
        (∀ a, fE.eval a = true ↔
          ∀ g ∈ goalsE,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              compiled.toCompiledProgram goalGrounding a g) := by
  rcases hsat with ⟨compiled, a, haE, haw⟩
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    compiled.surface_equivalence goalGrounding goalsQ goalsE hprobs ⟨a, haE, haw⟩
  exact ⟨compiled, fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩

/-- **Operational weighted first-order AD theorem from decomposed
    stratification assumptions.**

    This theorem avoids proving stratification of the fully expanded program in
    one shot: it is enough to prove stratification of the grounded normal layer
    and of the grounded AD expansions separately. -/
theorem surface_equivalence_of_parts
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ)
    (hnormal : prog.toFirstOrderNormalProgram.GroundedStratified s)
    (hAD : comp.GroundedADRulesRespectStratification s)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          (FirstOrderWeightedADCompiledProgram.ofParts comp s hnormal hAD)
          goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE prog.probs ≠ 0 ∧
      bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
        weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            (FirstOrderWeightedADCompiledProgram.ofParts comp s hnormal hAD)
            goalGrounding a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            (FirstOrderWeightedADCompiledProgram.ofParts comp s hnormal hAD)
            goalGrounding a g) := by
  simpa using
    (FirstOrderWeightedADCompiledProgram.surface_equivalence
      (compiled :=
        FirstOrderWeightedADCompiledProgram.ofParts comp s hnormal hAD)
      goalGrounding goalsQ goalsE hprobs hEpos)

/-- **Operational weighted first-order AD theorem from structured AD
    stratification data.**

    This is the most compositional route so far: prove the grounded normal
    layer is stratified, and separately prove that each grounded AD instance has
    body atoms below all heads and switches strictly below all heads. The full
    AD-expanded bridge then follows automatically. -/
theorem surface_equivalence_of_structured
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderWeightedADProbLogProgram σ n)
    (comp : FirstOrderWeightedADCompilation prog)
    (s : Stratification σ)
    (hnormal : prog.toFirstOrderNormalProgram.GroundedStratified s)
    (hstructured : comp.StructuredGroundedADStratification s)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (hprobs : ∀ i, prog.probs i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        FirstOrderGoalLit.holdsCompiledWeightedADProgram
          (FirstOrderWeightedADCompiledProgram.ofParts comp s hnormal
            (comp.groundedADRulesRespectStratification_of_structured s hstructured))
          goalGrounding a g) ∧
      assignmentWeight prog.probs a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE prog.probs ≠ 0 ∧
      bdd_wmc fQE prog.probs / bdd_wmc fE prog.probs =
        weightedSat fQE.eval prog.probs / weightedSat fE.eval prog.probs ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            (FirstOrderWeightedADCompiledProgram.ofParts comp s hnormal
              (comp.groundedADRulesRespectStratification_of_structured s hstructured))
            goalGrounding a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          FirstOrderGoalLit.holdsCompiledWeightedADProgram
            (FirstOrderWeightedADCompiledProgram.ofParts comp s hnormal
              (comp.groundedADRulesRespectStratification_of_structured s hstructured))
            goalGrounding a g) := by
  simpa using
    (surface_equivalence_of_parts prog comp s hnormal
      (comp.groundedADRulesRespectStratification_of_structured s hstructured)
      goalGrounding goalsQ goalsE hprobs hEpos)

end Mettapedia.Logic.BDDCore
