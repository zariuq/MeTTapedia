import Mettapedia.Logic.BDD.ProbLogSurface
import Mettapedia.Logic.LP.FunctionFree
import Mathlib.Tactic

/-!
# ProbLog Surface Examples

Worked examples for the current first-order ProbLog surface theorems.

Positive example:
- A function-free first-order weighted annotated disjunction with one variable
  and one constant can be compiled through the structured route and fed into
  the BDD/WMC bridge.
- A gated weighted annotated disjunction with a non-empty body and nontrivial
  evidence can be compiled through the local-choice automation route and fed
  into the same bridge.

Negative example:
- This file does not yet provide a canonical compiler from a source program to
  a structured compiled witness with no assumptions at all; it instantiates the
  current theorem surface on concrete structured or locally compilable data.

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore.Examples

open scoped ENNReal
open Mettapedia.Logic.LP

/-! ## 1. Signature and atoms -/

inductive TossRel
  | coin
  | heads
  | tails
  | sw₁
  | sw₂
  deriving DecidableEq, Fintype

abbrev TossConst := Unit
abbrev TossVar := Unit

def tossSig : LPSignature where
  constants := TossConst
  vars := TossVar
  relationSymbols := TossRel
  relationArity := fun _ => 1
  functionSymbols := PEmpty
  functionArity := PEmpty.elim

instance : IsEmpty tossSig.functionSymbols := inferInstanceAs (IsEmpty PEmpty)
instance : DecidableEq tossSig.constants := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq tossSig.vars := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq tossSig.relationSymbols := inferInstanceAs (DecidableEq TossRel)
instance : Fintype tossSig.constants := inferInstanceAs (Fintype Unit)
instance : Fintype tossSig.vars := inferInstanceAs (Fintype Unit)

def tossConst : GroundTerm tossSig := .const ()
def tossVar : Term tossSig := .var ()
instance : Nonempty (GroundTerm tossSig) := ⟨tossConst⟩

def unaryAtom (r : TossRel) (t : Term tossSig) : Atom tossSig where
  symbol := r
  args := fun _ => t

def unaryGroundAtom (r : TossRel) : GroundAtom tossSig :=
  GroundAtom.ofFinArgs r (fun _ => ())

def headsX : Atom tossSig := unaryAtom .heads tossVar
def tailsX : Atom tossSig := unaryAtom .tails tossVar
def coinX  : Atom tossSig := unaryAtom .coin tossVar

def coin₁  : GroundAtom tossSig := unaryGroundAtom .coin
def heads₁ : GroundAtom tossSig := unaryGroundAtom .heads
def tails₁ : GroundAtom tossSig := unaryGroundAtom .tails
def sw₁₁ : GroundAtom tossSig := unaryGroundAtom .sw₁
def sw₂₁ : GroundAtom tossSig := unaryGroundAtom .sw₂

instance : Unique (Grounding tossSig) where
  default := fun _ => tossConst
  uniq g := by
    funext v
    cases v
    cases h : g () with
    | const c =>
        cases c
        rfl
    | app f _ =>
        cases f

def tossGoalGrounding : Grounding tossSig := default

/-! ## 2. Weighted first-order AD program -/

noncomputable def fairTossAD : FirstOrderWeightedAnnotatedDisjunction tossSig where
  heads := [headsX, tailsX]
  probs := ![(1 / 2 : ENNReal), (1 / 2 : ENNReal)]
  body := []

noncomputable def fairTossProg : FirstOrderWeightedADProbLogProgram tossSig 2 where
  probFacts := ![sw₁₁, sw₂₁]
  probs := ![(1 / 2 : ENNReal), (1 : ENNReal)]
  rules := []
  facts_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · cases hij
    · cases hij
    · rfl
  normalRules := []
  annotatedDisjunctions := [fairTossAD]

/-! ## 3. Example theorem surface -/

def fairTossQuery : List (FirstOrderGoalLit tossSig) := [.pos headsX]
def fairTossEvidence : List (FirstOrderGoalLit tossSig) := []

def fairTossWitnessAssignment : Fin 2 → Bool := fun _ => true

theorem fairToss_probs_le_one :
    ∀ i, fairTossProg.probs i ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [fairTossProg]

theorem fairToss_assignmentWeight_ne_zero :
    assignmentWeight fairTossProg.probs fairTossWitnessAssignment ≠ 0 := by
  norm_num [assignmentWeight, fairTossWitnessAssignment, fairTossProg, varWeight]

/-- The unique grounded weighted AD instance arising from `fairTossAD`. -/
noncomputable def fairTossInst : GroundedFirstOrderWeightedADInstance tossSig where
  source := fairTossAD
  grounding := tossGoalGrounding

@[simp] theorem tossGoalGrounding_ground_headsX :
    tossGoalGrounding.groundAtom headsX = heads₁ := rfl

@[simp] theorem tossGoalGrounding_ground_tailsX :
    tossGoalGrounding.groundAtom tailsX = tails₁ := rfl

@[simp] theorem tossGoalGrounding_ground_coinX :
    tossGoalGrounding.groundAtom coinX = coin₁ := rfl

theorem fairToss_groundedWeightedAD_mem
    (inst : GroundedFirstOrderWeightedADInstance tossSig)
    (hinst : inst ∈ fairTossProg.groundedWeightedADInstances) :
    inst = fairTossInst := by
  classical
  unfold FirstOrderWeightedADProbLogProgram.groundedWeightedADInstances at hinst
  simp [fairTossProg, fairTossAD] at hinst
  rcases hinst with ⟨g, -, hEq⟩
  have hg : g = tossGoalGrounding := Subsingleton.elim _ _
  subst hg
  simpa [fairTossInst, fairTossAD] using hEq.symm

/-- Reuse the two existing probabilistic facts as calibrated switch slots.
Outside the actual grounded instances of `fairTossProg`, the fallback modulo
map is irrelevant: the compilation obligations only apply on real instances. -/
def fairTossSwitchSlot (inst : GroundedFirstOrderWeightedADInstance tossSig)
    (i : Fin inst.toGroundWeightedAD.heads.length) : Fin 2 :=
  ⟨i.1 % 2, by omega⟩

/-- Concrete compilation witness for the fair-toss weighted AD program. -/
noncomputable def fairTossComp : FirstOrderWeightedADCompilation fairTossProg where
  switchSlot := fairTossSwitchSlot
  slotInjective := by
    classical
    intro inst hinst i j hij
    have hinst' : inst = fairTossInst := fairToss_groundedWeightedAD_mem inst hinst
    subst hinst'
    apply Fin.ext
    have hlen : fairTossInst.toGroundWeightedAD.heads.length = 2 := by
      simp [fairTossInst, GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD, fairTossAD]
    have hi : i.1 < 2 := by
      omega
    have hj : j.1 < 2 := by
      omega
    have hvals : i.1 % 2 = j.1 % 2 := congrArg Fin.val hij
    simpa [fairTossSwitchSlot, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hvals
  fresh_heads := by
    classical
    intro inst hinst i
    have hinst' : inst = fairTossInst := fairToss_groundedWeightedAD_mem inst hinst
    subst hinst'
    fin_cases i <;>
      simp [fairTossSwitchSlot, fairTossProg, fairTossAD, fairTossInst,
        GroundedFirstOrderWeightedADInstance.toGroundAD,
        GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD,
        WeightedAnnotatedDisjunction.toAnnotatedDisjunction,
        heads₁, tails₁, sw₁₁, sw₂₁, unaryGroundAtom] <;>
      constructor <;> intro h <;> cases h
  fresh_body := by
    classical
    intro inst hinst i
    have hinst' : inst = fairTossInst := fairToss_groundedWeightedAD_mem inst hinst
    subst hinst'
    fin_cases i <;>
      simp [fairTossSwitchSlot, fairTossProg, fairTossAD, fairTossInst,
        GroundedFirstOrderWeightedADInstance.toGroundAD,
        GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD,
        WeightedAnnotatedDisjunction.toAnnotatedDisjunction]
  calibrated := by
    classical
    intro inst hinst i
    have hinst' : inst = fairTossInst := fairToss_groundedWeightedAD_mem inst hinst
    subst hinst'
    fin_cases i
    · simpa [fairTossProg, fairTossSwitchSlot, fairTossInst, fairTossAD,
        GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD] using
        (show (1 / 2 : ENNReal) =
            switchProb fairTossInst.toGroundWeightedAD.probs ⟨0, by decide⟩ from by
          simp [switchProb, partialSum, fairTossInst, fairTossAD,
            GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
            Grounding.groundFirstOrderWeightedAD])
    · simp [fairTossProg, fairTossSwitchSlot, fairTossInst, fairTossAD,
        GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD, switchProb, partialSum]
      have hsum :
          (∑ x with x = 0, ![(2⁻¹ : ENNReal), (2⁻¹ : ENNReal)] x) =
            (2⁻¹ : ENNReal) := by
        rw [show (Finset.univ.filter (fun x : Fin 2 => x = 0)) = ({0} : Finset (Fin 2)) by
              ext x
              fin_cases x <;> simp]
        simp
      rw [hsum]
      have hhalf_ne_zero : (2⁻¹ : ENNReal) ≠ 0 := by norm_num
      have hhalf_ne_top : (2⁻¹ : ENNReal) ≠ ⊤ := by simp
      simpa using (ENNReal.div_self hhalf_ne_zero hhalf_ne_top).symm

/-- Heads live at stratum `1`, auxiliary switches at stratum `0`. -/
def fairTossStratification : Stratification tossSig := fun a =>
  match a.symbol with
  | .coin => 0
  | .heads => 1
  | .tails => 1
  | .sw₁ => 0
  | .sw₂ => 0

theorem fairToss_normalGroundedStratified :
    fairTossProg.toFirstOrderNormalProgram.GroundedStratified fairTossStratification := by
  intro c hc
  simp [FirstOrderWeightedADProbLogProgram.toFirstOrderNormalProgram,
    FirstOrderNormalProbLogProgram.toGroundNormalProgram,
    FirstOrderNormalProbLogProgram.groundNormalRules, fairTossProg] at hc

theorem fairToss_structuredGroundedADStratification :
    fairTossComp.StructuredGroundedADStratification fairTossStratification := by
  classical
  intro inst hinst
  have hinst' : inst = fairTossInst := fairToss_groundedWeightedAD_mem inst hinst
  subst hinst'
  constructor
  · intro a ha i
    simp [fairTossInst, fairTossAD,
      GroundedFirstOrderWeightedADInstance.toGroundAD,
      GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
      Grounding.groundFirstOrderWeightedAD,
      WeightedAnnotatedDisjunction.toAnnotatedDisjunction] at ha
  · intro j i
    fin_cases j <;> fin_cases i
    · change 0 < 1
      norm_num
    · change 0 < 1
      norm_num
    · change 0 < 1
      norm_num
    · change 0 < 1
      norm_num

/-- Structured compiled witness for the fair-toss example. -/
noncomputable def fairTossCompiled :
    FirstOrderWeightedADStructuredCompiledProgram fairTossProg where
  comp := fairTossComp
  stratification := fairTossStratification
  normalGroundedStratified := fairToss_normalGroundedStratified
  structuredGroundedADStratification := fairToss_structuredGroundedADStratification

theorem fairToss_structuredEvidenceSatisfiable :
    fairTossProg.StructuredEvidenceSatisfiable tossGoalGrounding fairTossEvidence := by
  refine ⟨fairTossCompiled, fairTossWitnessAssignment, ?_, fairToss_assignmentWeight_ne_zero⟩
  intro g hg
  cases hg

/-- End-to-end worked example: the structured weighted first-order AD surface
theorem yields ordered BDDs for the `heads(X)` query of a fair binary choice. -/
theorem fairToss_surface_example :
    ∃ compiled : FirstOrderWeightedADStructuredCompiledProgram fairTossProg,
      ∃ fQE fE : BDD 2,
        fQE.Ordered none ∧ fE.Ordered none ∧
        bdd_wmc fE fairTossProg.probs ≠ 0 ∧
        bdd_wmc fQE fairTossProg.probs / bdd_wmc fE fairTossProg.probs =
          weightedSat fQE.eval fairTossProg.probs /
            weightedSat fE.eval fairTossProg.probs ∧
        (∀ a, fQE.eval a = true ↔
          ∀ g ∈ fairTossQuery ++ fairTossEvidence,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              compiled.toCompiledProgram tossGoalGrounding a g) ∧
        (∀ a, fE.eval a = true ↔
          ∀ g ∈ fairTossEvidence,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              compiled.toCompiledProgram tossGoalGrounding a g) := by
  exact
    exists_surface_equivalence_of_structuredEvidenceSatisfiable
      fairTossProg tossGoalGrounding fairTossQuery fairTossEvidence
      fairToss_probs_le_one fairToss_structuredEvidenceSatisfiable

/-! ## 4. Richer example: non-empty body, nontrivial evidence, local-choice automation -/

noncomputable def gatedTossAD : FirstOrderWeightedAnnotatedDisjunction tossSig where
  heads := [headsX, tailsX]
  probs := ![(1 / 2 : ENNReal), (1 / 2 : ENNReal)]
  body := [coinX]

noncomputable def gatedTossProg : FirstOrderWeightedADProbLogProgram tossSig 3 where
  probFacts := ![coin₁, sw₁₁, sw₂₁]
  probs := ![(1 / 2 : ENNReal), (1 / 2 : ENNReal), (1 : ENNReal)]
  rules := []
  facts_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · cases hij
    · cases hij
    · cases hij
    · rfl
    · cases hij
    · cases hij
    · cases hij
    · rfl
  normalRules := []
  annotatedDisjunctions := [gatedTossAD]

def gatedTossQuery : List (FirstOrderGoalLit tossSig) := [.pos headsX]
def gatedTossEvidence : List (FirstOrderGoalLit tossSig) := [.pos coinX]

def gatedTossWitnessAssignment : Fin 3 → Bool := fun _ => true

theorem gatedToss_probs_le_one :
    ∀ i, gatedTossProg.probs i ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [gatedTossProg]

theorem gatedToss_assignmentWeight_ne_zero :
    assignmentWeight gatedTossProg.probs gatedTossWitnessAssignment ≠ 0 := by
  simp [assignmentWeight, gatedTossWitnessAssignment, gatedTossProg, varWeight,
    Fin.prod_univ_three]

theorem sw₁₁_ne_coin₁ : sw₁₁ ≠ coin₁ := by
  intro h
  cases h

theorem sw₂₁_ne_coin₁ : sw₂₁ ≠ coin₁ := by
  intro h
  cases h

noncomputable def gatedTossInst : GroundedFirstOrderWeightedADInstance tossSig where
  source := gatedTossAD
  grounding := tossGoalGrounding

theorem gatedToss_groundedWeightedAD_mem
    (inst : GroundedFirstOrderWeightedADInstance tossSig)
    (hinst : inst ∈ gatedTossProg.groundedWeightedADInstances) :
    inst = gatedTossInst := by
  classical
  unfold FirstOrderWeightedADProbLogProgram.groundedWeightedADInstances at hinst
  simp [gatedTossProg, gatedTossAD] at hinst
  rcases hinst with ⟨g, -, hEq⟩
  have hg : g = tossGoalGrounding := Subsingleton.elim _ _
  subst hg
  simpa [gatedTossInst, gatedTossAD] using hEq.symm

theorem gatedToss_heads_length :
    gatedTossInst.toGroundWeightedAD.heads.length = 2 := by
  simp [gatedTossInst, GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
    Grounding.groundFirstOrderWeightedAD, gatedTossAD]

def gatedTossLocalSwitchSlot
    (i : Fin gatedTossInst.toGroundWeightedAD.heads.length) : Fin 3 :=
  ⟨i.1 + 1, by
    have hi : i.1 < 2 := by
      simpa [gatedToss_heads_length] using i.2
    omega⟩

def gatedTossStratification : Stratification tossSig := fun a =>
  match a.symbol with
  | .coin => 0
  | .heads => 1
  | .tails => 1
  | .sw₁ => 0
  | .sw₂ => 0

theorem gatedToss_normalGroundedStratified :
    gatedTossProg.toFirstOrderNormalProgram.GroundedStratified gatedTossStratification := by
  intro c hc
  simp [FirstOrderWeightedADProbLogProgram.toFirstOrderNormalProgram,
    FirstOrderNormalProbLogProgram.toGroundNormalProgram,
    FirstOrderNormalProbLogProgram.groundNormalRules, gatedTossProg] at hc

theorem gatedToss_locallyStructurablyCompilable :
    gatedTossProg.LocallyStructurablyCompilable := by
  classical
  refine ⟨gatedTossStratification, gatedToss_normalGroundedStratified, ?_⟩
  intro inst hinst
  have hinst' : inst = gatedTossInst := gatedToss_groundedWeightedAD_mem inst hinst
  subst hinst'
  constructor
  · intro a ha i
    have ha' : a = coin₁ := by
      simpa [gatedTossInst, gatedTossAD,
        GroundedFirstOrderWeightedADInstance.toGroundAD,
        GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD,
        WeightedAnnotatedDisjunction.toAnnotatedDisjunction] using ha
    subst a
    fin_cases i <;>
      simp [gatedTossStratification, gatedTossInst, gatedTossAD,
        GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
        Grounding.groundFirstOrderWeightedAD,
        coin₁, heads₁, tails₁, unaryGroundAtom]
  · refine ⟨gatedTossLocalSwitchSlot, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      have hvals : i.1 + 1 = j.1 + 1 := congrArg Fin.val hij
      omega
    · intro i
      fin_cases i <;>
        simp [gatedTossLocalSwitchSlot, gatedTossProg, gatedTossAD, gatedTossInst,
          GroundedFirstOrderWeightedADInstance.toGroundAD,
          GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
          Grounding.groundFirstOrderWeightedAD,
          WeightedAnnotatedDisjunction.toAnnotatedDisjunction,
          heads₁, tails₁, coin₁, sw₁₁, sw₂₁, unaryGroundAtom] <;>
        constructor <;> intro h <;> cases h
    · intro i
      fin_cases i
      · simpa [gatedTossLocalSwitchSlot, gatedTossProg, gatedTossAD, gatedTossInst,
          GroundedFirstOrderWeightedADInstance.toGroundAD,
          GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
          Grounding.groundFirstOrderWeightedAD,
          WeightedAnnotatedDisjunction.toAnnotatedDisjunction] using
          (show sw₁₁ ∉ [coin₁] from by
            simpa using sw₁₁_ne_coin₁)
      · simpa [gatedTossLocalSwitchSlot, gatedTossProg, gatedTossAD, gatedTossInst,
          GroundedFirstOrderWeightedADInstance.toGroundAD,
          GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
          Grounding.groundFirstOrderWeightedAD,
          WeightedAnnotatedDisjunction.toAnnotatedDisjunction] using
          (show sw₂₁ ∉ [coin₁] from by
            simpa using sw₂₁_ne_coin₁)
    · intro i
      fin_cases i
      · simpa [gatedTossProg, gatedTossLocalSwitchSlot, gatedTossInst, gatedTossAD,
          GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
          Grounding.groundFirstOrderWeightedAD] using
          (show (1 / 2 : ENNReal) =
              switchProb gatedTossInst.toGroundWeightedAD.probs ⟨0, by decide⟩ from by
            simp [switchProb, partialSum, gatedTossInst, gatedTossAD,
              GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
              Grounding.groundFirstOrderWeightedAD])
      · simp [gatedTossProg, gatedTossLocalSwitchSlot, gatedTossInst, gatedTossAD,
          GroundedFirstOrderWeightedADInstance.toGroundWeightedAD,
          Grounding.groundFirstOrderWeightedAD, switchProb, partialSum]
        have hsum :
            (∑ x with x = 0, ![(2⁻¹ : ENNReal), (2⁻¹ : ENNReal)] x) =
              (2⁻¹ : ENNReal) := by
          rw [show (Finset.univ.filter (fun x : Fin 2 => x = 0)) = ({0} : Finset (Fin 2)) by
                ext x
                fin_cases x <;> simp]
          simp
        rw [hsum]
        have hhalf_ne_zero : (2⁻¹ : ENNReal) ≠ 0 := by norm_num
        have hhalf_ne_top : (2⁻¹ : ENNReal) ≠ ⊤ := by simp
        simpa using (ENNReal.div_self hhalf_ne_zero hhalf_ne_top).symm
    · intro j i
      fin_cases j <;> fin_cases i
      · change 0 < 1
        norm_num
      · change 0 < 1
        norm_num
      · change 0 < 1
        norm_num
      · change 0 < 1
        norm_num

noncomputable def gatedTossAutoData :
    FirstOrderWeightedADSourceStructuredCompilation gatedTossProg :=
  gatedTossProg.chooseSourceStructuredCompilation gatedToss_locallyStructurablyCompilable

noncomputable def gatedTossAutoCompiled :
    FirstOrderWeightedADCompiledProgram gatedTossProg :=
  gatedTossAutoData.toStructuredCompiledProgram.toCompiledProgram

theorem gatedToss_coin_in_residualDB :
    coin₁ ∈ residualDBa gatedTossAutoCompiled.toGroundExpandedNormalProgram.toProbLogProgram
      gatedTossWitnessAssignment := by
  refine ⟨0, rfl, ?_⟩
  rfl

theorem gatedToss_coin_holds :
    FirstOrderGoalLit.holdsCompiledWeightedADProgram
      gatedTossAutoCompiled tossGoalGrounding gatedTossWitnessAssignment (.pos coinX) := by
  change queryHoldsNormalA gatedTossAutoCompiled.toGroundExpandedNormalProgram
    gatedTossAutoCompiled.stratification coin₁ gatedTossWitnessAssignment
  exact baseLHM_subset_fullStratifiedModel
    gatedTossAutoCompiled.toGroundExpandedNormalProgram
    gatedTossAutoCompiled.stratification gatedTossWitnessAssignment
    (leastHerbrandModel_db
      (residualKBa gatedTossAutoCompiled.toGroundExpandedNormalProgram.toProbLogProgram
        gatedTossWitnessAssignment)
      coin₁ gatedToss_coin_in_residualDB)

theorem gatedToss_locallyStructuredEvidenceSatisfiable :
    gatedTossProg.LocallyStructuredEvidenceSatisfiable
      tossGoalGrounding gatedTossEvidence := by
  refine ⟨gatedToss_locallyStructurablyCompilable,
    gatedTossWitnessAssignment, ?_, gatedToss_assignmentWeight_ne_zero⟩
  intro g hg
  simp [gatedTossEvidence] at hg
  subst hg
  simpa using gatedToss_coin_holds

/-- End-to-end worked example with a non-empty AD body and nontrivial
evidence: the local-choice automation route constructs the source-structured
witness automatically, then the surface theorem yields ordered BDDs for
`heads(X)` conditioned on `coin(X)`. -/
theorem gatedToss_surface_example :
    ∃ data : FirstOrderWeightedADSourceStructuredCompilation gatedTossProg,
      ∃ fQE fE : BDD 3,
        fQE.Ordered none ∧ fE.Ordered none ∧
        bdd_wmc fE gatedTossProg.probs ≠ 0 ∧
        bdd_wmc fQE gatedTossProg.probs / bdd_wmc fE gatedTossProg.probs =
          weightedSat fQE.eval gatedTossProg.probs /
            weightedSat fE.eval gatedTossProg.probs ∧
        (∀ a, fQE.eval a = true ↔
          ∀ g ∈ gatedTossQuery ++ gatedTossEvidence,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              data.toStructuredCompiledProgram.toCompiledProgram
              tossGoalGrounding a g) ∧
        (∀ a, fE.eval a = true ↔
          ∀ g ∈ gatedTossEvidence,
            FirstOrderGoalLit.holdsCompiledWeightedADProgram
              data.toStructuredCompiledProgram.toCompiledProgram
              tossGoalGrounding a g) := by
  exact
    exists_surface_equivalence_of_locallyStructuredEvidenceSatisfiable
      gatedTossProg tossGoalGrounding gatedTossQuery gatedTossEvidence
      gatedToss_probs_le_one gatedToss_locallyStructuredEvidenceSatisfiable

end Mettapedia.Logic.BDDCore.Examples
