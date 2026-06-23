import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-!
# π → ρ Encoding Correctness (Clean RF Surface)

This module intentionally exposes only the proved, maintained forward-correctness
surface for the π→ρ encoding.

Included:
- encoding image characterization (`Encoded`)
- single-step RF forward correspondence up to weak restricted bisimilarity
- multi-step RF forward correspondence up to weak restricted bisimilarity

Excluded:
- legacy exploratory proofs for non-RF / backward correspondence
- unfinished substitution-heavy infrastructure
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
open Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism

/-- Syntactic image predicate for the encoding function. -/
abbrev Encoded := EncodingMorphism.Encoded

/-- Every encoded π-process is in the `Encoded` image grammar. -/
theorem encode_is_Encoded (P : Process) (n v : String) :
    Encoded n v (encode P n v) :=
  EncodingMorphism.encode_is_Encoded P n v

/-- Forward operational correspondence for one RF π-step. -/
theorem encoding_forward_single_step_rf {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.ReducesRF P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) :=
  EncodingMorphism.forward_single_step_bisim h hrf hsafe n v

/-- Forward operational correspondence for RF π multi-step reductions. -/
theorem encoding_forward_multi_step_rf {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepRF P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.MultiCommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) :=
  EncodingMorphism.forward_multi_step_bisim h hrf hsafe n v

/-- Main RF-forward operational correspondence theorem (Lybech Prop. 4, forward RF).
-/
theorem encoding_operational_correspondence_forward_rf
    {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepRF P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.MultiCommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) :=
  EncodingMorphism.prop4_forward h hrf hsafe n v

/-- Safe generic π multi-step wrapper:
    convert `MultiStepSafe` to the RF development and apply the main theorem. -/
theorem encoding_operational_correspondence_forward_safe_core_direct
    {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepSafe P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) := by
  rcases ForwardSimulation.MultiStepSafe.toRF h with ⟨hRF, hSafe⟩
  exact encoding_operational_correspondence_forward_rf hRF hrf hSafe n v

/-- Derived-layer RF forward correspondence.
    This routes the proven RF result through the derived ρ operational layer. -/
theorem encoding_operational_correspondence_forward_safe_derived
    {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepSafe P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (n v : String) :
    ∃ T, ∃ hs : (encode P n v) ⇝ᵈ* T,
      Nonempty (CoreCompatible hs) ∧ T ≈{N} (encode P' n v) := by
  rcases encoding_operational_correspondence_forward_safe_core_direct (N := N) h hrf n v with
    ⟨T, hStarN, hBisim⟩
  rcases hStarN with ⟨hStar⟩
  let hs : (encode P n v) ⇝ᵈ* T := ReducesStar.toDerived hStar
  let hcc : CoreCompatible hs := ReducesStar.toDerivedCoreCompatible hStar
  exact ⟨T, hs, ⟨⟨hcc⟩, hBisim⟩⟩

/-- Public RF safe wrapper: prove in the derived layer, then transport to core. -/
theorem encoding_operational_correspondence_forward_safe
    {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepSafe P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) := by
  rcases encoding_operational_correspondence_forward_safe_derived (N := N) h hrf n v with
    ⟨T, hs, hccN, hBisim⟩
  rcases hccN with ⟨hcc⟩
  refine ⟨T, ?_, hBisim⟩
  exact ⟨CoreCompatible.toCore (hs := hs) hcc⟩

/-- Script-friendly bridge: package `toRF` conversion and forward wrapper together. -/
theorem encoding_operational_correspondence_forward_safe_packaged
    {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepSafe P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (n v : String) :
    ∃ hrf' : ForwardSimulation.MultiStepRF P P',
      ForwardSimulation.MultiCommSafe hrf' ∧
      (∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v)) := by
  rcases ForwardSimulation.MultiStepSafe.toRF h with ⟨hRF, hSafe⟩
  refine ⟨hRF, hSafe, ?_⟩
  exact encoding_operational_correspondence_forward_rf hRF hrf hSafe n v

/-- Regression canary: compose two safe steps and discharge via the safe wrapper. -/
theorem encoding_operational_correspondence_forward_safe_two_step
    {N : Finset String} {P Q R : Process}
    (h₁ : P ⇝ₛ Q)
    (h₂ : Q ⇝ₛ R)
    (hrf : ForwardSimulation.RestrictionFree P)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode R n v) := by
  let hPQ : P ⇝ₛ* Q := ForwardSimulation.MultiStepSafe.single h₁
  let hQR : Q ⇝ₛ* R := ForwardSimulation.MultiStepSafe.single h₂
  let hPR : P ⇝ₛ* R := ForwardSimulation.MultiStepSafe.trans hPQ hQR
  exact encoding_operational_correspondence_forward_safe (N := N) hPR hrf n v

/-- Regression canary: compose three safe steps and discharge via the safe wrapper. -/
theorem encoding_operational_correspondence_forward_safe_three_step
    {N : Finset String} {P Q R S : Process}
    (h₁ : P ⇝ₛ Q)
    (h₂ : Q ⇝ₛ R)
    (h₃ : R ⇝ₛ S)
    (hrf : ForwardSimulation.RestrictionFree P)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode S n v) := by
  let hPQ : P ⇝ₛ* Q := ForwardSimulation.MultiStepSafe.single h₁
  let hQR : Q ⇝ₛ* R := ForwardSimulation.MultiStepSafe.single h₂
  let hRS : R ⇝ₛ* S := ForwardSimulation.MultiStepSafe.single h₃
  let hPR : P ⇝ₛ* R := ForwardSimulation.MultiStepSafe.trans hPQ hQR
  let hPS : P ⇝ₛ* S := ForwardSimulation.MultiStepSafe.trans hPR hRS
  exact encoding_operational_correspondence_forward_safe (N := N) hPS hrf n v

private def ciRedex1 : Process :=
  Process.par (Process.input "x" "y" Process.nil) (Process.output "x" "z")

private def ciRedex2 : Process :=
  Process.par (Process.input "a" "b" Process.nil) (Process.output "a" "c")

private def ciRedex3 : Process :=
  Process.par (Process.input "p" "q" Process.nil) (Process.output "p" "r")

private def ciStart : Process := (ciRedex1 ||| ciRedex2) ||| ciRedex3
private def ciMid1 : Process := (Process.nil ||| ciRedex2) ||| ciRedex3
private def ciMid2 : Process := (Process.nil ||| Process.nil) ||| ciRedex3
private def ciFinal : Process := (Process.nil ||| Process.nil) ||| Process.nil

/-- Concrete fixed-name CI canary for the safe forward wrapper.
    This gives a stable regression target with explicit COMM-safe steps. -/
theorem ci_canary_fixed_three_comm_steps
    {N : Finset String} (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode ciStart n v) T) ∧ T ≈{N} (encode ciFinal n v) := by
  have hyz : ("y" : Name) ≠ "z" := by decide
  have hbc : ("b" : Name) ≠ "c" := by decide
  have hqr : ("q" : Name) ≠ "r" := by decide
  have hb1 : ForwardSimulation.BarendregtFor "y" "z" Process.nil := by
    simp [ForwardSimulation.BarendregtFor]
  have hb2 : ForwardSimulation.BarendregtFor "b" "c" Process.nil := by
    simp [ForwardSimulation.BarendregtFor]
  have hb3 : ForwardSimulation.BarendregtFor "q" "r" Process.nil := by
    simp [ForwardSimulation.BarendregtFor]
  have h1 : ciStart ⇝ₛ* ciMid1 := by
    simpa [ciStart, ciMid1, ciRedex1, ciRedex2, ciRedex3, Process.substitute] using
      ForwardSimulation.MultiStepSafe.of_comm_par_left_chain "x" "y" "z" Process.nil ciRedex2 ciRedex3 hyz hb1
  have h2step : ciMid1 ⇝ₛ ciMid2 := by
    simpa [ciMid1, ciMid2, ciRedex2, ciRedex3] using
      ForwardSimulation.ReducesSafe.of_par_left
        (Process.nil ||| ciRedex2) (Process.nil ||| Process.nil) ciRedex3
        (ForwardSimulation.ReducesSafe.comm_par_right "a" "b" "c" Process.nil Process.nil hbc hb2)
  have h2 : ciMid1 ⇝ₛ* ciMid2 := ForwardSimulation.MultiStepSafe.single h2step
  have h3step : ciMid2 ⇝ₛ ciFinal := by
    simpa [ciMid2, ciFinal, ciRedex3] using
      ForwardSimulation.ReducesSafe.of_par_right
        (Process.nil ||| Process.nil) ciRedex3 Process.nil
        (ForwardSimulation.ReducesSafe.of_comm "p" "q" "r" Process.nil hqr hb3)
  have h3 : ciMid2 ⇝ₛ* ciFinal := ForwardSimulation.MultiStepSafe.single h3step
  let h12 : ciStart ⇝ₛ* ciMid2 := ForwardSimulation.MultiStepSafe.trans h1 h2
  let h123 : ciStart ⇝ₛ* ciFinal := ForwardSimulation.MultiStepSafe.trans h12 h3
  have hrfStart : ForwardSimulation.RestrictionFree ciStart := by
    simp [ciStart, ciRedex1, ciRedex2, ciRedex3, ForwardSimulation.RestrictionFree]
  rcases encoding_operational_correspondence_forward_safe_packaged (N := N) h123 hrfStart n v with
    ⟨_hRF, _hSafe, hOut⟩
  exact hOut

/-- Derived-layer canary: encoded replication unfolds in one derived step
    (available under arbitrary context via `rep_unfold_par_any`). -/
theorem derived_rep_unfold_encoded_replicate (x y : Name) (P : Process) (n v : String) :
    Nonempty
      ((encode (.replicate x y P) n v) ⇝ᵈ*
        (.collection .hashBag
          [rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v),
           .apply "PReplicate" [rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v)]]
          none)) := by
  refine ⟨?_⟩
  simpa [encode, rhoReplicate] using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.rep_unfold_single
      (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v)))

end Mettapedia.Languages.ProcessCalculi.PiCalculus
