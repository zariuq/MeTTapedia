import Mettapedia.Languages.Agda.Intrinsic.Interpretation
import Mettapedia.Languages.Agda.Intrinsic.Reduction

/-!
# Exact operational comparison for the authored dependent core

The reference relation uses root computations and generic compatible closure.
The presented relation is the image of free firing trees generated from the
authored rule list. Both directions retain open contexts and binder-local
premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables

def judgment {Γ : Ctx sig} (source target : Tm Γ) : Judgment algebra :=
  ⟨Γ, .term, source, target⟩

def sourceStep (j : Judgment algebra) : Prop :=
  match j with
  | ⟨_, .term, source, target⟩ => Step source target

theorem beta_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨0, by decide⟩ v) =
      judgment (app (lam (v 0)) (v 2)) (inst (v 0) (v 2)) := by
  change judgment (eval0 v (appS (lamS (b0 (.var .zero))) m0)) (eval0 v (b0 m0)) = _
  simp only [eval0_app, eval0_lam, eval0_m0, eval1_b0 v, eval0_b0]

theorem first_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨1, by decide⟩ v) =
      judgment (fst (pair (v 2) (v 3))) (v 2) := by
  change judgment (eval0 v (fstS (pairS m0 m1))) (eval0 v (m0)) = _
  simp only [eval0_fst, eval0_pair, eval0_m0, eval0_m1]

theorem second_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨2, by decide⟩ v) =
      judgment (snd (pair (v 2) (v 3))) (v 3) := by
  change judgment (eval0 v (sndS (pairS m0 m1))) (eval0 v (m1)) = _
  simp only [eval0_snd, eval0_pair, eval0_m0, eval0_m1]

theorem annotation_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨3, by decide⟩ v) =
      judgment (ann (v 2) (v 3)) (v 2) := by
  change judgment (eval0 v (annS m0 m1)) (eval0 v (m0)) = _
  simp only [eval0_ann, eval0_m0, eval0_m1]

theorem successor_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨4, by decide⟩ v) =
      judgment (app natSuc (v 2)) (suc (v 2)) := by
  change judgment (eval0 v (appS natSucS m0)) (eval0 v (sucS m0)) = _
  simp only [eval0_app, eval0_natSuc, eval0_suc, eval0_m0]

theorem recZero_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨5, by decide⟩ v) =
      judgment (natrec (v 2) (v 3) (v 4) (v 5) zero) (v 4) := by
  change judgment (eval0 v (natrecS m0 m1 m2 m3 zeroS)) (eval0 v (m2)) = _
  simp only [eval0_natrec, eval0_zero, eval0_m0, eval0_m1, eval0_m2, eval0_m3]

theorem recSuc_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨6, by decide⟩ v) =
      judgment (natrec (v 2) (v 3) (v 4) (v 5) (suc (v 6))) (app (app (v 5) (v 6)) (natrec (v 2) (v 3) (v 4) (v 5) (v 6))) := by
  change judgment (eval0 v (natrecS m0 m1 m2 m3 (sucS m4))) (eval0 v (appS (appS m3 m4) (natrecS m0 m1 m2 m3 m4))) = _
  simp only [eval0_natrec, eval0_suc, eval0_app, eval0_m0, eval0_m1, eval0_m2, eval0_m3, eval0_m4]

theorem piCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨7, by decide⟩ v) =
      judgment (pi (v 2) (v 0)) (pi (v 3) (v 0)) := by
  change judgment (eval0 v (piS m0 (b0 (.var .zero)))) (eval0 v (piS m1 (b0 (.var .zero)))) = _
  simp only [eval0_pi, eval0_m0, eval0_m1, eval1_b0 v]

theorem piCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨7, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem piCong1_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨8, by decide⟩ v) =
      judgment (pi (v 4) (v 0)) (pi (v 4) (v 1)) := by
  change judgment (eval0 v (piS m2 (b0 (.var .zero)))) (eval0 v (piS m2 (b1 (.var .zero)))) = _
  simp only [eval0_pi, eval0_m2, eval1_b0 v, eval1_b1 v]

theorem piCong1_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨8, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 0) (v 1) := by
  change judgment (eval1 v (b0 (.var .zero)))
    (eval1 v (b1 (.var .zero))) = _
  simp only [eval1_b0 v, eval1_b1 v]

theorem lamCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨9, by decide⟩ v) =
      judgment (lam (v 0)) (lam (v 1)) := by
  change judgment (eval0 v (lamS (b0 (.var .zero)))) (eval0 v (lamS (b1 (.var .zero)))) = _
  simp only [eval0_lam, eval1_b0 v, eval1_b1 v]

theorem lamCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨9, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 0) (v 1) := by
  change judgment (eval1 v (b0 (.var .zero)))
    (eval1 v (b1 (.var .zero))) = _
  simp only [eval1_b0 v, eval1_b1 v]

theorem appCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨10, by decide⟩ v) =
      judgment (app (v 2) (v 4)) (app (v 3) (v 4)) := by
  change judgment (eval0 v (appS m0 m2)) (eval0 v (appS m1 m2)) = _
  simp only [eval0_app, eval0_m0, eval0_m2, eval0_m1]

theorem appCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨10, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem appCong1_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨11, by decide⟩ v) =
      judgment (app (v 4) (v 2)) (app (v 4) (v 3)) := by
  change judgment (eval0 v (appS m2 m0)) (eval0 v (appS m2 m1)) = _
  simp only [eval0_app, eval0_m2, eval0_m0, eval0_m1]

theorem appCong1_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨11, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem annCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨12, by decide⟩ v) =
      judgment (ann (v 2) (v 4)) (ann (v 3) (v 4)) := by
  change judgment (eval0 v (annS m0 m2)) (eval0 v (annS m1 m2)) = _
  simp only [eval0_ann, eval0_m0, eval0_m2, eval0_m1]

theorem annCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨12, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem annCong1_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨13, by decide⟩ v) =
      judgment (ann (v 4) (v 2)) (ann (v 4) (v 3)) := by
  change judgment (eval0 v (annS m2 m0)) (eval0 v (annS m2 m1)) = _
  simp only [eval0_ann, eval0_m2, eval0_m0, eval0_m1]

theorem annCong1_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨13, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem sigmaCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨14, by decide⟩ v) =
      judgment (sigma (v 2) (v 0)) (sigma (v 3) (v 0)) := by
  change judgment (eval0 v (sigmaS m0 (b0 (.var .zero)))) (eval0 v (sigmaS m1 (b0 (.var .zero)))) = _
  simp only [eval0_sigma, eval0_m0, eval0_m1, eval1_b0 v]

theorem sigmaCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨14, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem sigmaCong1_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨15, by decide⟩ v) =
      judgment (sigma (v 4) (v 0)) (sigma (v 4) (v 1)) := by
  change judgment (eval0 v (sigmaS m2 (b0 (.var .zero)))) (eval0 v (sigmaS m2 (b1 (.var .zero)))) = _
  simp only [eval0_sigma, eval0_m2, eval1_b0 v, eval1_b1 v]

theorem sigmaCong1_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨15, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 0) (v 1) := by
  change judgment (eval1 v (b0 (.var .zero)))
    (eval1 v (b1 (.var .zero))) = _
  simp only [eval1_b0 v, eval1_b1 v]

theorem pairCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨16, by decide⟩ v) =
      judgment (pair (v 2) (v 4)) (pair (v 3) (v 4)) := by
  change judgment (eval0 v (pairS m0 m2)) (eval0 v (pairS m1 m2)) = _
  simp only [eval0_pair, eval0_m0, eval0_m2, eval0_m1]

theorem pairCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨16, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem pairCong1_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨17, by decide⟩ v) =
      judgment (pair (v 4) (v 2)) (pair (v 4) (v 3)) := by
  change judgment (eval0 v (pairS m2 m0)) (eval0 v (pairS m2 m1)) = _
  simp only [eval0_pair, eval0_m2, eval0_m0, eval0_m1]

theorem pairCong1_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨17, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem fstCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨18, by decide⟩ v) =
      judgment (fst (v 2)) (fst (v 3)) := by
  change judgment (eval0 v (fstS m0)) (eval0 v (fstS m1)) = _
  simp only [eval0_fst, eval0_m0, eval0_m1]

theorem fstCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨18, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem sndCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨19, by decide⟩ v) =
      judgment (snd (v 2)) (snd (v 3)) := by
  change judgment (eval0 v (sndS m0)) (eval0 v (sndS m1)) = _
  simp only [eval0_snd, eval0_m0, eval0_m1]

theorem sndCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨19, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem sucCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨20, by decide⟩ v) =
      judgment (suc (v 2)) (suc (v 3)) := by
  change judgment (eval0 v (sucS m0)) (eval0 v (sucS m1)) = _
  simp only [eval0_suc, eval0_m0, eval0_m1]

theorem sucCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨20, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem natrecCong0_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨21, by decide⟩ v) =
      judgment (natrec (v 2) (v 4) (v 5) (v 6) (v 7)) (natrec (v 3) (v 4) (v 5) (v 6) (v 7)) := by
  change judgment (eval0 v (natrecS m0 m2 m3 m4 m5)) (eval0 v (natrecS m1 m2 m3 m4 m5)) = _
  simp only [eval0_natrec, eval0_m0, eval0_m2, eval0_m3, eval0_m4, eval0_m5, eval0_m1]

theorem natrecCong0_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨21, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem natrecCong1_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨22, by decide⟩ v) =
      judgment (natrec (v 4) (v 2) (v 5) (v 6) (v 7)) (natrec (v 4) (v 3) (v 5) (v 6) (v 7)) := by
  change judgment (eval0 v (natrecS m2 m0 m3 m4 m5)) (eval0 v (natrecS m2 m1 m3 m4 m5)) = _
  simp only [eval0_natrec, eval0_m2, eval0_m0, eval0_m3, eval0_m4, eval0_m5, eval0_m1]

theorem natrecCong1_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨22, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem natrecCong2_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨23, by decide⟩ v) =
      judgment (natrec (v 4) (v 5) (v 2) (v 6) (v 7)) (natrec (v 4) (v 5) (v 3) (v 6) (v 7)) := by
  change judgment (eval0 v (natrecS m2 m3 m0 m4 m5)) (eval0 v (natrecS m2 m3 m1 m4 m5)) = _
  simp only [eval0_natrec, eval0_m2, eval0_m3, eval0_m0, eval0_m4, eval0_m5, eval0_m1]

theorem natrecCong2_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨23, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem natrecCong3_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨24, by decide⟩ v) =
      judgment (natrec (v 4) (v 5) (v 6) (v 2) (v 7)) (natrec (v 4) (v 5) (v 6) (v 3) (v 7)) := by
  change judgment (eval0 v (natrecS m2 m3 m4 m0 m5)) (eval0 v (natrecS m2 m3 m4 m1 m5)) = _
  simp only [eval0_natrec, eval0_m2, eval0_m3, eval0_m4, eval0_m0, eval0_m5, eval0_m1]

theorem natrecCong3_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨24, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

theorem natrecCong4_conclusion {Γ : Ctx sig} (v : Val Γ) :
    conclusionJudgment rules algebra (occurrence ⟨25, by decide⟩ v) =
      judgment (natrec (v 4) (v 5) (v 6) (v 7) (v 2)) (natrec (v 4) (v 5) (v 6) (v 7) (v 3)) := by
  change judgment (eval0 v (natrecS m2 m3 m4 m5 m0)) (eval0 v (natrecS m2 m3 m4 m5 m1)) = _
  simp only [eval0_natrec, eval0_m2, eval0_m3, eval0_m4, eval0_m5, eval0_m0, eval0_m1]

theorem natrecCong4_child {Γ : Ctx sig} (v : Val Γ) :
    childJudgment rules algebra (occurrence ⟨25, by decide⟩ v) ⟨0, by change 0 < 1; decide⟩ =
      judgment (v 2) (v 3) := by
  change judgment (eval0 v m0)
    (eval0 v m1) = _
  simp only [eval0_m0, eval0_m1]

/-- Interpreting every authored constructor yields an actual compatible step. -/
theorem sourceStep_closed : RuleClosed rules sourceStep := by
  intro o children
  rw [occurrence_complete o] at children ⊢
  generalize hi : o.index = i at children ⊢
  fin_cases i
  · rw [beta_conclusion]
    exact Step.root (Root.beta _ _)
  · rw [first_conclusion]
    exact Step.root (Root.first _ _)
  · rw [second_conclusion]
    exact Step.root (Root.second _ _)
  · rw [annotation_conclusion]
    exact Step.root (Root.annotation _ _)
  · rw [successor_conclusion]
    exact Step.root (Root.successor _)
  · rw [recZero_conclusion]
    exact Step.root (Root.recZero _ _ _ _)
  · rw [recSuc_conclusion]
    exact Step.root (Root.recSuc _ _ _ _ _)
  · rw [piCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [piCong0_child] at child
    exact Step.congr Op.pi (ArgsStep.head _ child)
  · rw [piCong1_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [piCong1_child] at child
    exact Step.congr Op.pi (ArgsStep.tail _ (ArgsStep.head _ child))
  · rw [lamCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [lamCong0_child] at child
    exact Step.congr Op.lam (ArgsStep.head _ child)
  · rw [appCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [appCong0_child] at child
    exact Step.congr Op.app (ArgsStep.head _ child)
  · rw [appCong1_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [appCong1_child] at child
    exact Step.congr Op.app (ArgsStep.tail _ (ArgsStep.head _ child))
  · rw [annCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [annCong0_child] at child
    exact Step.congr Op.ann (ArgsStep.head _ child)
  · rw [annCong1_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [annCong1_child] at child
    exact Step.congr Op.ann (ArgsStep.tail _ (ArgsStep.head _ child))
  · rw [sigmaCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [sigmaCong0_child] at child
    exact Step.congr Op.sigma (ArgsStep.head _ child)
  · rw [sigmaCong1_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [sigmaCong1_child] at child
    exact Step.congr Op.sigma (ArgsStep.tail _ (ArgsStep.head _ child))
  · rw [pairCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [pairCong0_child] at child
    exact Step.congr Op.pair (ArgsStep.head _ child)
  · rw [pairCong1_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [pairCong1_child] at child
    exact Step.congr Op.pair (ArgsStep.tail _ (ArgsStep.head _ child))
  · rw [fstCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [fstCong0_child] at child
    exact Step.congr Op.fst (ArgsStep.head _ child)
  · rw [sndCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [sndCong0_child] at child
    exact Step.congr Op.snd (ArgsStep.head _ child)
  · rw [sucCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [sucCong0_child] at child
    exact Step.congr Op.suc (ArgsStep.head _ child)
  · rw [natrecCong0_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [natrecCong0_child] at child
    exact Step.congr Op.natrec (ArgsStep.head _ child)
  · rw [natrecCong1_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [natrecCong1_child] at child
    exact Step.congr Op.natrec (ArgsStep.tail _ (ArgsStep.head _ child))
  · rw [natrecCong2_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [natrecCong2_child] at child
    exact Step.congr Op.natrec (ArgsStep.tail _ (ArgsStep.tail _ (ArgsStep.head _ child)))
  · rw [natrecCong3_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [natrecCong3_child] at child
    exact Step.congr Op.natrec (ArgsStep.tail _ (ArgsStep.tail _ (ArgsStep.tail _ (ArgsStep.head _ child))))
  · rw [natrecCong4_conclusion]
    have child := children ⟨0, by change 0 < 1; decide⟩
    rw [natrecCong4_child] at child
    exact Step.congr Op.natrec (ArgsStep.tail _ (ArgsStep.tail _ (ArgsStep.tail _ (ArgsStep.tail _ (ArgsStep.head _ child)))))

/-- Soundness includes all open terms, not only the closed examples. -/
theorem firing_sound {Γ : Ctx sig} {source target : Tm Γ}
    (firing : Reduces rules (judgment source target)) : Step source target :=
  reduces_least rules sourceStep sourceStep_closed _ firing

end Mettapedia.Languages.Agda.Intrinsic.Authored
