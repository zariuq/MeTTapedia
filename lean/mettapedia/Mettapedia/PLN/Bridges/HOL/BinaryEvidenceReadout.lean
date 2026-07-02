import Mettapedia.PLN.Bridges.HOL.ProvenanceSemiringReadout
import Mettapedia.PLN.Evidence.EvidentialLedger
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInductionAbductionITVBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

/-!
# BinaryEvidence readout for HOL derivation-tree provenance

This module is the WM-3b readout layer: proof-relevant HOL derivation trees are
graded as positive `BinaryEvidence`, finite tree bags aggregate by hplus, and
formula-level readouts compress the WM-2.5 cost spectrum into a single
BinaryEvidence envelope.  The evidence carrier is used only as a readout target;
it is not used as the HOL truth-value algebra.
-/

namespace Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout

open Mettapedia.Logic.HOL
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidentialLedger
open Mettapedia.PLN.RuleFamilies.FirstOrder
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
open scoped ENNReal

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
variable {φ ψ χ : Formula Const Γ}

/-- Adding independent evidence is coordinatewise nondecreasing on the left. -/
theorem binaryEvidence_le_hplus_right (x y : BinaryEvidence) : x ≤ x + y := by
  simp [BinaryEvidence.le_def, BinaryEvidence.hplus_def]

/-- Adding independent evidence is coordinatewise nondecreasing on the right. -/
theorem binaryEvidence_le_hplus_left (x y : BinaryEvidence) : x ≤ y + x := by
  simpa [BinaryEvidence.hplus_comm] using binaryEvidence_le_hplus_right x y

/-- Confidence is monotone under BinaryEvidence order, with the same finiteness
side conditions used by the core BinaryEvidence API. -/
theorem toConfidence_mono_of_le (κ : ℝ≥0∞) (x y : BinaryEvidence)
    (hκ_pos : κ ≠ 0) (hκ_top : κ ≠ ⊤) (hy_top : y.total ≠ ⊤)
    (hxy : x ≤ y) :
    BinaryEvidence.toConfidence κ x ≤ BinaryEvidence.toConfidence κ y := by
  exact BinaryEvidence.confidence_monotone_in_total κ x y hκ_pos hκ_top hy_top
    (add_le_add hxy.1 hxy.2)

/-- A Nat proof grade embedded as positive BinaryEvidence and no negative
counterevidence. -/
noncomputable def positiveEvidence (n : Nat) : BinaryEvidence :=
  ⟨(n : ℝ≥0∞), 0⟩

@[simp] theorem positiveEvidence_pos (n : Nat) :
    (positiveEvidence n).pos = (n : ℝ≥0∞) := rfl

@[simp] theorem positiveEvidence_neg (n : Nat) :
    (positiveEvidence n).neg = 0 := rfl

@[simp] theorem positiveEvidence_zero :
    positiveEvidence 0 = (0 : BinaryEvidence) := by
  ext <;> simp [positiveEvidence]

theorem positiveEvidence_mono {n m : Nat} (h : n ≤ m) :
    positiveEvidence n ≤ positiveEvidence m := by
  constructor
  · simpa [positiveEvidence] using (Nat.cast_le.mpr h : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞))
  · simp

theorem positiveEvidence_one_ne_two :
    positiveEvidence 1 ≠ positiveEvidence 2 := by
  intro h
  have hpos := congrArg BinaryEvidence.pos h
  norm_num [positiveEvidence] at hpos

/-- Per-tree evidence grade: rule-count evidence is positive support, with no
negative support introduced by the tree evaluator itself. -/
noncomputable def evGrade (d : DerivationTree Const Δ φ) : BinaryEvidence :=
  positiveEvidence d.evalNat

@[simp] theorem evGrade_pos (d : DerivationTree Const Δ φ) :
    (evGrade d).pos = (d.evalNat : ℝ≥0∞) := rfl

@[simp] theorem evGrade_neg (d : DerivationTree Const Δ φ) :
    (evGrade d).neg = 0 := rfl

@[simp] theorem evGrade_topI :
    evGrade (Const := Const) (DerivationTree.topI (Γ := Γ) (Δ := Δ)) =
      positiveEvidence 1 := by
  simp [evGrade]

/-- Finite tree-bag evidence aggregate, using BinaryEvidence hplus. -/
noncomputable def treeBagEvGrade :
    DerivationTree.TreeBag Const Δ φ → BinaryEvidence
  | [] => 0
  | d :: bag => evGrade d + treeBagEvGrade bag

@[simp] theorem treeBagEvGrade_nil :
    treeBagEvGrade ([] : DerivationTree.TreeBag Const Δ φ) = 0 := rfl

@[simp] theorem treeBagEvGrade_cons
    (d : DerivationTree Const Δ φ) (bag : DerivationTree.TreeBag Const Δ φ) :
    treeBagEvGrade (d :: bag) = evGrade d + treeBagEvGrade bag := rfl

/-- Finite tree-bag evidence is exactly finite-source PLN Revision of the
per-tree grades.  Provenance independence is a guard on when callers may use
the additive Revision rule, not a second aggregation operation. -/
theorem treeBagEvGrade_eq_revisionMany
    (bag : DerivationTree.TreeBag Const Δ φ) :
    treeBagEvGrade bag = revisionMany (bag.map evGrade) := by
  induction bag with
  | nil => simp [treeBagEvGrade, revisionMany]
  | cons d bag ih =>
      simp [treeBagEvGrade, revisionMany_cons, revision, ih]

theorem treeBagEvGrade_pair_eq_revision
    (d e : DerivationTree Const Δ φ) :
    treeBagEvGrade [d, e] = revision (evGrade d) (evGrade e) := by
  simp [treeBagEvGrade, revision]

/-- The hplus aggregate is monotone under adding one more derivation tree. -/
theorem treeBagEvGrade_le_cons
    (d : DerivationTree Const Δ φ) (bag : DerivationTree.TreeBag Const Δ φ) :
    treeBagEvGrade bag ≤ treeBagEvGrade (d :: bag) := by
  simpa [treeBagEvGrade_cons] using
    binaryEvidence_le_hplus_left (treeBagEvGrade bag) (evGrade d)

/-- Source-disjoint extension theorem.  The inequality only needs hplus
monotonicity; the explicit `SourceDisjoint` hypothesis records the intended
ledger-side independence contract. -/
theorem treeBagEvGrade_le_cons_of_sourceDisjoint
    (d e : DerivationTree Const Δ φ) (bag : DerivationTree.TreeBag Const Δ φ)
    (_h : DerivationTree.SourceDisjoint d e) :
    treeBagEvGrade bag ≤ treeBagEvGrade (d :: bag) :=
  treeBagEvGrade_le_cons d bag

/-- Pairwise source-disjoint finite tree bags are the intended domain for
independent hplus aggregation. -/
def treeBagPairwiseSourceDisjoint (bag : DerivationTree.TreeBag Const Δ φ) : Prop :=
  bag.Pairwise DerivationTree.SourceDisjoint

/-- Unary proof-rule evidence candidate with one local rule token. -/
noncomputable def ruleUnaryCandidate
    (x : BinaryEvidence) : BinaryEvidence :=
  positiveEvidence 1 + x

@[simp] theorem ruleUnaryCandidate_pos (x : BinaryEvidence) :
    (ruleUnaryCandidate x).pos = 1 + x.pos := by
  simp [ruleUnaryCandidate, BinaryEvidence.hplus_def]

@[simp] theorem ruleUnaryCandidate_neg (x : BinaryEvidence) :
    (ruleUnaryCandidate x).neg = x.neg := by
  simp [ruleUnaryCandidate, BinaryEvidence.hplus_def]

/-- Revision/hplus candidate for a binary proof rule with one rule-token of
overhead.  This is the BinaryEvidence revision formula plus the local rule
cost recorded by `DerivationTree.evalNat`. -/
noncomputable def ruleRevisionCandidate
    (x y : BinaryEvidence) : BinaryEvidence :=
  positiveEvidence 1 + x + y

@[simp] theorem ruleRevisionCandidate_pos (x y : BinaryEvidence) :
    (ruleRevisionCandidate x y).pos = 1 + x.pos + y.pos := by
  simp [ruleRevisionCandidate, BinaryEvidence.hplus_def]

@[simp] theorem ruleRevisionCandidate_neg (x y : BinaryEvidence) :
    (ruleRevisionCandidate x y).neg = x.neg + y.neg := by
  simp [ruleRevisionCandidate, BinaryEvidence.hplus_def]

/-- Ternary proof-rule evidence candidate with one local rule token. -/
noncomputable def ruleTernaryCandidate
    (x y z : BinaryEvidence) : BinaryEvidence :=
  positiveEvidence 1 + x + y + z

@[simp] theorem ruleTernaryCandidate_pos (x y z : BinaryEvidence) :
    (ruleTernaryCandidate x y z).pos = 1 + x.pos + y.pos + z.pos := by
  simp [ruleTernaryCandidate, BinaryEvidence.hplus_def]

@[simp] theorem ruleTernaryCandidate_neg (x y z : BinaryEvidence) :
    (ruleTernaryCandidate x y z).neg = x.neg + y.neg + z.neg := by
  simp [ruleTernaryCandidate, BinaryEvidence.hplus_def]

/-- Count payload for the generic derivation-tree grading fold. -/
noncomputable def countPayload :
    DerivationTree.GradePayload Const BinaryEvidence where
  hyp _ := positiveEvidence 1
  topI := positiveEvidence 1
  botE _ x := ruleUnaryCandidate x
  andI _ _ x y := ruleRevisionCandidate x y
  andEL _ x := ruleUnaryCandidate x
  andER _ x := ruleUnaryCandidate x
  orIL _ x := ruleUnaryCandidate x
  orIR _ x := ruleUnaryCandidate x
  orE _ _ _ x y z := ruleTernaryCandidate x y z
  impI _ x := ruleUnaryCandidate x
  impE _ _ x y := ruleRevisionCandidate x y
  notI _ x := ruleUnaryCandidate x
  notE _ _ x y := ruleRevisionCandidate x y
  allI _ x := ruleUnaryCandidate x
  allE _ _ x := ruleUnaryCandidate x
  exI _ _ x := ruleUnaryCandidate x
  exE _ _ x y := ruleRevisionCandidate x y
  eqRefl _ := positiveEvidence 1
  eqSymm _ x := ruleUnaryCandidate x
  eqTrans _ _ x y := ruleRevisionCandidate x y
  eqPropI _ _ x y := ruleRevisionCandidate x y
  eqPropEL _ x := ruleUnaryCandidate x
  eqPropER _ x := ruleUnaryCandidate x
  eqApp _ _ x := ruleUnaryCandidate x
  eqAppArg _ _ x := ruleUnaryCandidate x
  eqLam _ x := ruleUnaryCandidate x
  funExt _ x := ruleUnaryCandidate x
  beta _ _ := positiveEvidence 1
  eta _ := positiveEvidence 1

@[simp] theorem gradeWith_countPayload_pos
    (d : DerivationTree Const Δ φ) :
    (DerivationTree.gradeWith (countPayload (Const := Const)) d).pos =
      (d.evalNat : ℝ≥0∞) := by
  induction d <;>
    simp_all [countPayload, positiveEvidence, ruleUnaryCandidate,
      ruleRevisionCandidate, ruleTernaryCandidate, DerivationTree.evalNat,
      DerivationTree.eval, DerivationTree.evalPayload, BinaryEvidence.hplus_def,
      Nat.cast_add, add_assoc]

@[simp] theorem gradeWith_countPayload_neg
    (d : DerivationTree Const Δ φ) :
    (DerivationTree.gradeWith (countPayload (Const := Const)) d).neg = 0 := by
  induction d <;>
    simp_all [countPayload, positiveEvidence, ruleUnaryCandidate,
      ruleRevisionCandidate, ruleTernaryCandidate, BinaryEvidence.hplus_def,
      add_assoc]

/-- The old `evGrade` is exactly the count-payload instance of the generic
grading fold. -/
theorem gradeWith_countPayload_eq_evGrade
    (d : DerivationTree Const Δ φ) :
    DerivationTree.gradeWith (countPayload (Const := Const)) d = evGrade d := by
  ext <;> simp [evGrade]

theorem evGrade_eq_gradeWith_countPayload
    (d : DerivationTree Const Δ φ) :
    evGrade d = DerivationTree.gradeWith (countPayload (Const := Const)) d :=
  (gradeWith_countPayload_eq_evGrade (Const := Const) d).symm

/-- Positive exactness example: conjunction introduction is exact for the
rule-overhead hplus/revision candidate. -/
theorem evGrade_andI_exact
    (dφ : DerivationTree Const Δ φ) (dψ : DerivationTree Const Δ ψ) :
    evGrade (DerivationTree.andI dφ dψ) =
      ruleRevisionCandidate (evGrade dφ) (evGrade dψ) := by
  calc
    evGrade (DerivationTree.andI dφ dψ)
        = DerivationTree.gradeWith (countPayload (Const := Const))
            (DerivationTree.andI dφ dψ) := by
          exact evGrade_eq_gradeWith_countPayload (Const := Const)
            (DerivationTree.andI dφ dψ)
    _ = ruleRevisionCandidate
          (DerivationTree.gradeWith (countPayload (Const := Const)) dφ)
          (DerivationTree.gradeWith (countPayload (Const := Const)) dψ) := rfl
    _ = ruleRevisionCandidate (evGrade dφ) (evGrade dψ) := by
          rw [gradeWith_countPayload_eq_evGrade, gradeWith_countPayload_eq_evGrade]

/-- Positive exactness example: implication elimination/modus ponens is exact
for the same rule-overhead hplus/revision candidate. -/
theorem evGrade_impE_exact
    (dImp : DerivationTree Const Δ (.imp φ ψ))
    (dφ : DerivationTree Const Δ φ) :
    evGrade (DerivationTree.impE dImp dφ) =
      ruleRevisionCandidate (evGrade dImp) (evGrade dφ) := by
  calc
    evGrade (DerivationTree.impE dImp dφ)
        = DerivationTree.gradeWith (countPayload (Const := Const))
            (DerivationTree.impE dImp dφ) := by
          exact evGrade_eq_gradeWith_countPayload (Const := Const)
            (DerivationTree.impE dImp dφ)
    _ = ruleRevisionCandidate
          (DerivationTree.gradeWith (countPayload (Const := Const)) dImp)
          (DerivationTree.gradeWith (countPayload (Const := Const)) dφ) := by
          rw [DerivationTree.gradeWith_impE]
          rfl
    _ = ruleRevisionCandidate (evGrade dImp) (evGrade dφ) := by
          simp [gradeWith_countPayload_eq_evGrade]

/-- Universal elimination contributes exactly one local rule token under the
count-payload BinaryEvidence readout. -/
theorem evGrade_allE_exact
    {σ : Ty Base} {θ : Formula Const (σ :: Γ)}
    (t : Term Const Γ σ) (dAll : DerivationTree Const Δ (.all θ)) :
    evGrade (DerivationTree.allE t dAll) =
      ruleUnaryCandidate (evGrade dAll) := by
  calc
    evGrade (DerivationTree.allE t dAll)
        = DerivationTree.gradeWith (countPayload (Const := Const))
            (DerivationTree.allE t dAll) := by
          exact evGrade_eq_gradeWith_countPayload (Const := Const)
            (DerivationTree.allE t dAll)
    _ = ruleUnaryCandidate
          (DerivationTree.gradeWith (countPayload (Const := Const)) dAll) := by
          rw [DerivationTree.gradeWith_allE]
          rfl
    _ = ruleUnaryCandidate (evGrade dAll) := by
          simp [gradeWith_countPayload_eq_evGrade]

/-- Lossy/projection-side bound: eliminating the left conjunct is not evidence
identity for this tree-grade; it adds the local rule token. -/
theorem evGrade_andEL_input_le_output
    (d : DerivationTree Const Δ (.and φ ψ)) :
    evGrade d ≤ evGrade (DerivationTree.andEL d) := by
  apply positiveEvidence_mono
  simp [DerivationTree.evalNat, DerivationTree.eval, DerivationTree.evalPayload]

/-- Concrete negative example for exactness-by-identity: the projection step
over `top ∧ top` changes the BinaryEvidence grade. -/
theorem evGrade_andEL_topAndTop_ne_input
    (Δ : List (Formula Const Γ)) :
    evGrade
        (DerivationTree.andEL
          (DerivationTree.topAndTopTree (Const := Const) Δ)) ≠
      evGrade (DerivationTree.topAndTopTree (Const := Const) Δ) := by
  intro h
  have hpos := congrArg BinaryEvidence.pos h
  norm_num [evGrade, positiveEvidence, DerivationTree.topAndTopTree,
    DerivationTree.evalNat, DerivationTree.eval, DerivationTree.evalPayload] at hpos

/-- Strength is a lossy view: it collapses the one-count and two-count
positive evidence grades to the same point estimate. -/
theorem toStrength_positiveEvidence_one_eq_two :
    BinaryEvidence.toStrength (positiveEvidence 1) =
      BinaryEvidence.toStrength (positiveEvidence 2) := by
  have htwo : (2 : ℝ≥0∞) / 2 = 1 := by
    exact ENNReal.div_self (by norm_num) (by norm_num)
  norm_num [BinaryEvidence.toStrength, BinaryEvidence.total, positiveEvidence, htwo]

/-- Explicit lossy-view witness: `toStrength` identifies distinct positive
evidence counts. -/
theorem toStrength_loses_positiveEvidence_count :
    positiveEvidence 1 ≠ positiveEvidence 2 ∧
      BinaryEvidence.toStrength (positiveEvidence 1) =
        BinaryEvidence.toStrength (positiveEvidence 2) :=
  ⟨positiveEvidence_one_ne_two, toStrength_positiveEvidence_one_eq_two⟩

/-- Any nonzero positive-only Nat evidence projects to unit strength. -/
theorem toStrength_positiveEvidence_eq_one {n : Nat} (hn : n ≠ 0) :
    BinaryEvidence.toStrength (positiveEvidence n) = 1 := by
  rw [BinaryEvidence.toStrength, BinaryEvidence.total, positiveEvidence]
  simp only
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have htotal : (n : ℝ≥0∞) + 0 ≠ 0 := by simpa using hn0
  rw [if_neg htotal]
  simpa using ENNReal.div_self hn0 (by simp : (n : ℝ≥0∞) ≠ ⊤)

@[simp] theorem toStrength_evGrade_eq_one
    (d : DerivationTree Const Δ φ) :
    BinaryEvidence.toStrength (evGrade d) = 1 :=
  toStrength_positiveEvidence_eq_one (Nat.ne_of_gt (DerivationTree.evalNat_pos d))

/-- In the count-only evidence readout, implication elimination projects to
the existing BinaryEvidence deduction-strength expression with both premise
strengths supplied by `evGrade`.  The theorem is deliberately about the lossy
`toStrength` view; the exact evidence statement remains `evGrade_impE_exact`. -/
theorem toStrength_evGrade_impE_eq_deductionStrength
    (dImp : DerivationTree Const Δ (.imp φ ψ))
    (dφ : DerivationTree Const Δ φ)
    (pB pC : ℝ≥0∞) :
    BinaryEvidence.toStrength (evGrade (DerivationTree.impE dImp dφ)) =
      BinaryEvidence.deductionStrength
        (BinaryEvidence.toStrength (evGrade dImp))
        (BinaryEvidence.toStrength (evGrade dφ))
        pB pC := by
  simp [BinaryEvidence.deductionStrength, BinaryEvidence.directPathStrength,
    BinaryEvidence.indirectPathStrength]

/-- Count-payload deduction, read through `toStrength` and then `toReal`,
recovers the classic PLN simple deduction formula under the explicit
admissibility hypotheses required by the BinaryEvidence/real bridge. -/
theorem toReal_toStrength_evGrade_impE_eq_simpleDeductionStrengthFormula
    (dImp : DerivationTree Const Δ (.imp φ ψ))
    (dφ : DerivationTree Const Δ φ)
    (pA : ℝ) (pB pC : ℝ≥0∞)
    (hpB_le_one : pB ≤ 1)
    (hpB_le_pC : pB ≤ pC)
    (hpC_ne_top : pC ≠ ⊤)
    (hpB_small : pB.toReal ≤ 0.99)
    (h_consist :
      _root_.Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency
          pA pB.toReal
            (BinaryEvidence.toStrength (evGrade dImp)).toReal ∧
        _root_.Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency
          pB.toReal pC.toReal
            (BinaryEvidence.toStrength (evGrade dφ)).toReal) :
    (BinaryEvidence.toStrength (evGrade (DerivationTree.impE dImp dφ))).toReal =
      _root_.Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.simpleDeductionStrengthFormula
          pA pB.toReal pC.toReal
          (BinaryEvidence.toStrength (evGrade dImp)).toReal
          (BinaryEvidence.toStrength (evGrade dφ)).toReal := by
  calc
    (BinaryEvidence.toStrength
        (evGrade (DerivationTree.impE dImp dφ))).toReal
        =
          (BinaryEvidence.deductionStrength
            (BinaryEvidence.toStrength (evGrade dImp))
            (BinaryEvidence.toStrength (evGrade dφ))
            pB pC).toReal := by
          rw [toStrength_evGrade_impE_eq_deductionStrength]
    _ = _root_.Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.simpleDeductionStrengthFormula
            pA pB.toReal pC.toReal
            (BinaryEvidence.toStrength (evGrade dImp)).toReal
            (BinaryEvidence.toStrength (evGrade dφ)).toReal := by
          exact BinaryEvidence.deductionStrength_toReal_eq_simpleDeductionStrengthFormula
            pA
            (BinaryEvidence.toStrength (evGrade dImp))
            (BinaryEvidence.toStrength (evGrade dφ))
            pB pC
            (BinaryEvidence.toStrength_le_one _)
            hpB_le_one
            (by simpa [toStrength_evGrade_eq_one] using hpB_le_pC)
            hpC_ne_top
            (by simp [BinaryEvidence.directPathStrength, toStrength_evGrade_eq_one])
            (by simp [BinaryEvidence.indirectPathStrength, toStrength_evGrade_eq_one])
            hpB_small
            h_consist

/-- Universal elimination changes the count evidence but not its strength
projection in the positive-only readout. -/
theorem toStrength_evGrade_allE_eq_input
    {σ : Ty Base} {θ : Formula Const (σ :: Γ)}
    (t : Term Const Γ σ) (dAll : DerivationTree Const Δ (.all θ)) :
    BinaryEvidence.toStrength (evGrade (DerivationTree.allE t dAll)) =
      BinaryEvidence.toStrength (evGrade dAll) := by
  simp

/-- Concrete deduction-side lossy witness: modus ponens over `top → top` and
`top` records extra BinaryEvidence count, but `toStrength` forgets it. -/
theorem toStrength_evGrade_impE_top_loses_count
    (Δ : List (Formula Const Γ)) :
    evGrade
        (DerivationTree.impE
          (DerivationTree.impI
            (DerivationTree.topI (Const := Const)
              (Γ := Γ) (Δ := (.top : Formula Const Γ) :: Δ)))
          (DerivationTree.topI (Const := Const) (Γ := Γ) (Δ := Δ))) ≠
      evGrade (DerivationTree.topI (Const := Const) (Γ := Γ) (Δ := Δ)) ∧
    BinaryEvidence.toStrength
        (evGrade
          (DerivationTree.impE
            (DerivationTree.impI
              (DerivationTree.topI (Const := Const)
                (Γ := Γ) (Δ := (.top : Formula Const Γ) :: Δ)))
            (DerivationTree.topI (Const := Const) (Γ := Γ) (Δ := Δ)))) =
      BinaryEvidence.toStrength
        (evGrade (DerivationTree.topI (Const := Const) (Γ := Γ) (Δ := Δ))) := by
  constructor
  · intro h
    have hpos := congrArg BinaryEvidence.pos h
    norm_num [evGrade, positiveEvidence, DerivationTree.evalNat,
      DerivationTree.eval, DerivationTree.evalPayload] at hpos
  · simpa [toStrength_evGrade_eq_one] using
      (toStrength_positiveEvidence_eq_one (n := 1) (by norm_num)).symm

/-! ## Induction/abduction readout bounds

Induction and abduction are not primitive HOL tree constructors in this
readout.  The certificates below therefore use the existing rule-family ITV
surface: the count readout is bounded by the concrete asymmetric intervals,
while explicit canaries prevent point-formula exactness from being claimed for
the positive-count `evGrade` projection.
-/

/-- Positive bound certificate: any nonempty count-grade tree readout projects
inside the concrete source-rule induction interval used by the asymmetric ITV
canary. -/
theorem toReal_toStrength_evGrade_mem_inductionAsymmetryITV
    (d : DerivationTree Const Δ φ) :
    inductionAsymmetryITV.lower ≤
        (BinaryEvidence.toStrength (evGrade d)).toReal ∧
      (BinaryEvidence.toStrength (evGrade d)).toReal ≤
        inductionAsymmetryITV.upper := by
  rcases plnInductionAbductionITV_asymmetric_canary with
    ⟨hIndLower, hIndUpper, _hIndWidth, _hAbdLower, _hAbdUpper,
      _hAbdWidth, _hSeparated⟩
  constructor
  · rw [hIndLower]
    norm_num [toStrength_evGrade_eq_one]
  · rw [hIndUpper]
    norm_num [toStrength_evGrade_eq_one]

/-- Positive bound certificate: the same count-grade tree readout projects
inside the concrete sink-rule abduction interval used by the asymmetric ITV
canary. -/
theorem toReal_toStrength_evGrade_mem_abductionAsymmetryITV
    (d : DerivationTree Const Δ φ) :
    abductionAsymmetryITV.lower ≤
        (BinaryEvidence.toStrength (evGrade d)).toReal ∧
      (BinaryEvidence.toStrength (evGrade d)).toReal ≤
        abductionAsymmetryITV.upper := by
  rcases plnInductionAbductionITV_asymmetric_canary with
    ⟨_hIndLower, _hIndUpper, _hIndWidth, hAbdLower, hAbdUpper,
      _hAbdWidth, _hSeparated⟩
  constructor
  · rw [hAbdLower]
    norm_num [toStrength_evGrade_eq_one]
  · rw [hAbdUpper]
    norm_num [toStrength_evGrade_eq_one]

/-- Negative exactness canary: the count-only tree readout should not be read
as the asymmetric source-rule induction point formula. -/
theorem toReal_toStrength_evGrade_ne_inductionAsymmetryPoint
    (d : DerivationTree Const Δ φ) :
    (BinaryEvidence.toStrength (evGrade d)).toReal ≠
      plnInductionStrength
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) := by
  rcases plnInductionAbduction_asymmetric_canary with
    ⟨hInd, _hAbd, _hNe⟩
  rw [hInd]
  norm_num [toStrength_evGrade_eq_one]

/-- Negative exactness canary: the count-only tree readout should not be read
as the asymmetric sink-rule abduction point formula. -/
theorem toReal_toStrength_evGrade_ne_abductionAsymmetryPoint
    (d : DerivationTree Const Δ φ) :
    (BinaryEvidence.toStrength (evGrade d)).toReal ≠
      plnAbductionStrength
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) := by
  rcases plnInductionAbduction_asymmetric_canary with
    ⟨_hInd, hAbd, _hNe⟩
  rw [hAbd]
  norm_num [toStrength_evGrade_eq_one]

/-- The cost-spectrum evidence envelope: map each exact Nat cost to positive
BinaryEvidence and take the least upper bound. -/
noncomputable def spectrumEvGrade (S : Set Nat) : BinaryEvidence :=
  sSup (positiveEvidence '' S)

theorem spectrumEvGrade_mono
    {A B : Set Nat}
    (hAB : Mettapedia.PLN.Bridges.HOL.ProvenanceSemiringReadout.CostSpectrumLE A B) :
    spectrumEvGrade A ≤ spectrumEvGrade B := by
  unfold spectrumEvGrade
  refine sSup_le ?_
  intro e he
  rcases he with ⟨n, hnA, rfl⟩
  rcases hAB hnA with ⟨m, hmB, hnm⟩
  exact (positiveEvidence_mono hnm).trans
    (le_sSup (Set.mem_image_of_mem positiveEvidence hmB))

/-- Formula-level BinaryEvidence readout obtained by compressing the exact Nat
cost spectrum of all proof-relevant finite derivations. -/
noncomputable def formulaEvGrade
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : BinaryEvidence :=
  spectrumEvGrade (ClosedTheorySet.costSpectrum (Const := Const) T φ)

/-- BinaryEvidence-valued WMReadout along the same derivability order used by
`natCostSpectrumWMReadout`. -/
noncomputable def binaryEvidenceCostSpectrumWMReadout
    (T : ClosedTheorySet Const) :
    Mettapedia.PLN.WorldModel.WMReadout
      (ClosedFormula Const) BinaryEvidence
      (fun φ ψ => ClosedTheorySet.Provable (Const := Const) T (.imp φ ψ))
      (· ≤ ·) where
  mu := formulaEvGrade (Const := Const) T
  monotone := by
    intro φ ψ hImp
    exact spectrumEvGrade_mono
      (ClosedTheorySet.costSpectrum_mono_derivability (Const := Const) hImp)

/-- The strength projection of the readout is bounded by the canonical unit
interval; it is a lossy view of the full BinaryEvidence envelope. -/
theorem formulaEvGrade_toStrength_le_one
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    BinaryEvidence.toStrength (formulaEvGrade (Const := Const) T φ) ≤ 1 :=
  BinaryEvidence.toStrength_le_one _

/-- The confidence projection is monotone whenever the full BinaryEvidence
envelope is monotone and the finite-total side conditions of the view hold. -/
theorem formulaEvGrade_toConfidence_mono
    (κ : ℝ≥0∞) (T : ClosedTheorySet Const)
    {φ ψ : ClosedFormula Const}
    (hκ_pos : κ ≠ 0) (hκ_top : κ ≠ ⊤)
    (hψ_top : (formulaEvGrade (Const := Const) T ψ).total ≠ ⊤)
    (hImp : ClosedTheorySet.Provable (Const := Const) T (.imp φ ψ)) :
    BinaryEvidence.toConfidence κ (formulaEvGrade (Const := Const) T φ) ≤
      BinaryEvidence.toConfidence κ (formulaEvGrade (Const := Const) T ψ) :=
  toConfidence_mono_of_le κ
    (formulaEvGrade (Const := Const) T φ)
    (formulaEvGrade (Const := Const) T ψ)
    hκ_pos hκ_top hψ_top
    ((binaryEvidenceCostSpectrumWMReadout (Const := Const) T).monotone hImp)

/-! ## Minimal ledger adapter for source retraction

`ClosedTheorySet.sourceIdeal` is an upward-closed set of possible source-token
supports, while `EvidentialLedger.forget` filters a concrete list of source
items by decidable source equality.  The direct composition therefore needs a
finite adapter from proof trees to ledger items; the following concrete
two-source adapter is the smallest bridge that preserves the intended
forget-then-aggregate law without refactoring the ledger API.
-/

/-- Named sources for the concrete retraction example. -/
inductive TwoSource where
  | keep
  | drop
  deriving DecidableEq, BEq, Repr

/-- Single candidate used by the concrete two-source ledger example. -/
inductive TwoSourceCandidate where
  | claim
  deriving DecidableEq, BEq, Repr

/-- Nat-valued tree grade for the existing ledger API. -/
def treeBinEvGrade (d : DerivationTree Const Δ φ) : BinEvNat :=
  ⟨d.evalNat, 0⟩

@[simp] theorem treeBinEvGrade_pos (d : DerivationTree Const Δ φ) :
    (treeBinEvGrade d).pos = d.evalNat := rfl

@[simp] theorem treeBinEvGrade_neg (d : DerivationTree Const Δ φ) :
    (treeBinEvGrade d).neg = 0 := rfl

/-- The ledger adapter preserves the BinaryEvidence embedding of the tree
grade. -/
theorem treeBinEvGrade_toBinaryEvidence
    (d : DerivationTree Const Δ φ) :
    BinEvNat.toBinaryEvidence (treeBinEvGrade d) = evGrade d := by
  ext <;> simp [BinEvNat.toBinaryEvidence, treeBinEvGrade, evGrade,
    positiveEvidence]

/-! ## Ledger-backed source independence

The old `DerivationTree.SourceDisjoint` remains the set-level readout over
`sourceSupport`.  The predicates below attach that readout to concrete
`EvidentialLedger` source lists and provide the bridge: when ledger source
sets realize the tree supports, ledger disjointness implies the old predicate.
-/

def ledgerSourceSet {Source Candidate : Type*}
    (items : List (SourceItem Source Candidate)) : Set Source :=
  {s | ∃ item, item ∈ items ∧ item.source = s}

def LedgerSourceDisjoint {Source Candidate : Type*}
    (xs ys : List (SourceItem Source Candidate)) : Prop :=
  Disjoint (ledgerSourceSet xs) (ledgerSourceSet ys)

theorem ledgerSourceDisjoint_symm {Source Candidate : Type*}
    {xs ys : List (SourceItem Source Candidate)}
    (h : LedgerSourceDisjoint xs ys) :
    LedgerSourceDisjoint ys xs := by
  exact Disjoint.symm h

theorem not_LedgerSourceDisjoint_of_shared_source
    {Source Candidate : Type*}
    {xs ys : List (SourceItem Source Candidate)} {s : Source}
    (hxs : s ∈ ledgerSourceSet xs) (hys : s ∈ ledgerSourceSet ys) :
    ¬ LedgerSourceDisjoint xs ys := by
  intro h
  exact (Set.disjoint_left.mp h hxs) hys

/-- A concrete ledger certificate for one tree: the ledger's source set is
exactly the tree's `sourceSupport`, and its aggregate for the target candidate
is exactly the tree's Nat-valued grade. -/
structure LedgerBackedTree (Candidate : Type*) [BEq Candidate]
    (target : Candidate) (Δ : List (Formula Const Γ))
    (φ : Formula Const Γ) where
  tree : DerivationTree Const Δ φ
  ledger :
    List (SourceItem (DerivationTree.SourceToken (Base := Base) Const) Candidate)
  support_exact : ledgerSourceSet ledger = tree.sourceSupport
  aggregate_exact : aggregate ledger target = treeBinEvGrade tree

def ledgerBackedTreeSourceDisjoint
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ) : Prop :=
  LedgerSourceDisjoint x.ledger y.ledger

theorem sourceDisjoint_of_ledgerBackedTreeSourceDisjoint
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ)
    (h : ledgerBackedTreeSourceDisjoint x y) :
    DerivationTree.SourceDisjoint x.tree y.tree := by
  unfold ledgerBackedTreeSourceDisjoint LedgerSourceDisjoint at h
  change Disjoint x.tree.sourceSupport y.tree.sourceSupport
  rw [← x.support_exact, ← y.support_exact]
  exact h

theorem ledgerBackedTree_aggregate_to_evGrade
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (x : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ) :
    BinEvNat.toBinaryEvidence (aggregate x.ledger target) =
      evGrade x.tree := by
  rw [x.aggregate_exact, treeBinEvGrade_toBinaryEvidence]

def ledgerBackedTreeBag
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (xs : List (LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ)) :
    DerivationTree.TreeBag Const Δ φ :=
  xs.map (fun x => x.tree)

theorem ledgerBackedTree_pair_treeBagEvGrade_eq_revision
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (x y : LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ)
    (_h : ledgerBackedTreeSourceDisjoint x y) :
    treeBagEvGrade [x.tree, y.tree] =
      revision (evGrade x.tree) (evGrade y.tree) :=
  treeBagEvGrade_pair_eq_revision x.tree y.tree

theorem ledgerBackedTreeBagEvGrade_eq_revisionMany
    {Candidate : Type*} [BEq Candidate] {target : Candidate}
    (xs : List (LedgerBackedTree (Base := Base) (Const := Const)
      Candidate target Δ φ))
    (_h : xs.Pairwise (fun x y => ledgerBackedTreeSourceDisjoint x y)) :
    treeBagEvGrade (ledgerBackedTreeBag xs) =
      revisionMany (xs.map fun x => evGrade x.tree) := by
  simp [ledgerBackedTreeBag, treeBagEvGrade_eq_revisionMany, List.map_map,
    Function.comp_def]

/-- Turn one tree and one named source into an `EvidentialLedger` item. -/
def treeLedgerItem
    (source : TwoSource) (d : DerivationTree Const Δ φ) :
    SourceItem TwoSource TwoSourceCandidate where
  source := source
  kind := .logicalDerivation
  support := fun _ => treeBinEvGrade d
  note := "derivation-tree adapter"

/-- A concrete two-source ledger whose two entries support the same claim. -/
def twoSourceTreeLedger
    (dKeep dDrop : DerivationTree Const Δ φ) :
    List (SourceItem TwoSource TwoSourceCandidate) :=
  [treeLedgerItem TwoSource.keep dKeep,
    treeLedgerItem TwoSource.drop dDrop]

/-- Aggregate over the source-free residual tree ledger after removing the
named `drop` source. -/
def twoSourceTreeLedgerWithoutDrop
    (dKeep : DerivationTree Const Δ φ) :
    List (SourceItem TwoSource TwoSourceCandidate) :=
  [treeLedgerItem TwoSource.keep dKeep]

/-- Retraction theorem for the concrete adapter: forgetting the named source
and then aggregating is exactly aggregation over the source-free residual
ledger. -/
theorem forget_drop_then_aggregate_eq_source_free
    (dKeep dDrop : DerivationTree Const Δ φ) :
    aggregate
        (forget TwoSource.drop (twoSourceTreeLedger dKeep dDrop))
        TwoSourceCandidate.claim =
      aggregate
        (twoSourceTreeLedgerWithoutDrop dKeep)
        TwoSourceCandidate.claim := by
  simp [twoSourceTreeLedger, twoSourceTreeLedgerWithoutDrop, treeLedgerItem,
    forget, aggregate]

end Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout
