import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.FirstMismatchSurvival
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge

/-!
# Boundaries of partial semantic guidance

Longer observed survival and a smaller first residual are useful ranking
features, but neither is an unconditional repairability theorem.  Terms from
one recurrent evaluation also share a source lineage and therefore cannot be
added as independent PLN observations.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

/-! ## Constructive repairability separations -/

namespace RepairFixtures

inductive Program where
  | nearDead
  | farRepairable
  | solution
  deriving DecidableEq, Repr

/-- Target is the constant-zero sequence.  `nearDead` fails late and by one;
`farRepairable` fails immediately and by ten. -/
def output : Program → ℕ → Int
  | .nearDead, i => if i < 2 then 0 else 1
  | .farRepairable, i => if i = 0 then 10 else 0
  | .solution, _ => 0

def agrees (program : Program) (i : ℕ) : Prop := output program i = 0

noncomputable def depth (program : Program) : ℕ :=
  firstMismatchDepth 3 (agrees program)

/-- A deliberately sparse, declared repair relation. -/
def RepairStep : Program → Program → Prop
  | .farRepairable, .solution => True
  | _, _ => False

def Correct (program : Program) : Prop := ∀ i, output program i = 0

def Repairable (program : Program) : Prop :=
  ∃ repaired, RepairStep program repaired ∧ Correct repaired

noncomputable def firstResidual (program : Program) : ℕ :=
  Int.natAbs (output program (depth program))

theorem nearDead_depth : depth .nearDead = 2 := by
  apply firstMismatchDepth_eq_of_boundary 3 2 (agrees .nearDead)
  · omega
  · intro i hi
    simp [agrees, output, hi]
  · simp [agrees, output]

theorem farRepairable_depth : depth .farRepairable = 0 := by
  apply firstMismatchDepth_eq_of_boundary 3 0 (agrees .farRepairable)
  · omega
  · intro i hi
    omega
  · simp [agrees, output]

theorem solution_is_correct : Correct .solution := by
  intro i
  rfl

theorem far_is_repairable : Repairable .farRepairable := by
  exact ⟨.solution, trivial, solution_is_correct⟩

theorem near_is_not_repairable : ¬ Repairable .nearDead := by
  rintro ⟨repaired, hstep, hcorrect⟩
  cases repaired <;> simp [RepairStep] at hstep

/-- Greater first-mismatch depth does not unconditionally imply that a
declared repair system can reach a correct program. -/
theorem greater_depth_not_unconditionally_repairable :
    depth .farRepairable < depth .nearDead ∧
      Repairable .farRepairable ∧ ¬ Repairable .nearDead := by
  rw [farRepairable_depth, nearDead_depth]
  exact ⟨by omega, far_is_repairable, near_is_not_repairable⟩

theorem nearDead_firstResidual : firstResidual .nearDead = 1 := by
  simp [firstResidual, nearDead_depth, output]

theorem farRepairable_firstResidual : firstResidual .farRepairable = 10 := by
  simp [firstResidual, farRepairable_depth, output]

/-- A numerically closer first failure need not be easier to repair. -/
theorem smaller_residual_not_unconditionally_repairable :
    firstResidual .nearDead < firstResidual .farRepairable ∧
      ¬ Repairable .nearDead ∧ Repairable .farRepairable := by
  rw [nearDead_firstResidual, farRepairable_firstResidual]
  exact ⟨by omega, near_is_not_repairable, far_is_repairable⟩

end RepairFixtures

/-! ## Bounded agreement is not extensional correctness -/

theorem prefixEquivalent_not_extensional :
    Gauthier.PrefixEquivalent 20 1
        Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeId
        Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeZeroAfterZero ∧
      ¬ Mettapedia.GSLT.LanguageDef.GauthierE1.Extensional
        Mettapedia.GSLT.LanguageDef.GauthierE1.orgE1Signature
        Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeId
        Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeZeroAfterZero :=
  Gauthier.one_seed_prefixEquivalent_not_extensional

/-! ## Terms in one recurrent trace share provenance -/

def traceTermPacket (traceId position : ℕ) : SourcePacket Unit ℕ ℕ where
  program := ()
  target := position
  source := traceId
  ancestors := ∅

theorem sameTrace_terms_not_sourceDisjoint (traceId leftPos rightPos : ℕ) :
    ¬ (traceTermPacket traceId leftPos).SourceDisjoint
      (traceTermPacket traceId rightPos) := by
  intro h
  exact h.1 rfl

/-- Even distinct term positions from the same recurrent evaluation are not
source-disjoint evidence packets. -/
theorem distinctPositions_sameTrace_not_independent :
    (traceTermPacket 7 0).target ≠ (traceTermPacket 7 1).target ∧
      ¬ (traceTermPacket 7 0).SourceDisjoint (traceTermPacket 7 1) := by
  exact ⟨by decide, sameTrace_terms_not_sourceDisjoint 7 0 1⟩

#print axioms RepairFixtures.greater_depth_not_unconditionally_repairable
#print axioms RepairFixtures.smaller_residual_not_unconditionally_repairable
#print axioms prefixEquivalent_not_extensional
#print axioms distinctPositions_sameTrace_not_independent

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
