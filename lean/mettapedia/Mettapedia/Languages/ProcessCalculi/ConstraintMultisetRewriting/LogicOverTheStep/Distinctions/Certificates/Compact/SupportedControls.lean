import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Supported
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family

/-!
# Supported certificates: measured

The same claims as the incumbent's certificates, with supports added, checked on supports.

* **The leak chain itself** (four states, no two in a class, so classes cannot help): the leak chain's
  certificate with its supports is accepted (`leakSupported_accepted`) and its check costs `281` counted
  operations against the incumbent's `799` (`leakSupported_work`).
* **The blown-up chain** at `m = 1` and `m = 2` (`8` and `12` states, supports of at most two states):
  the incumbent's certificate of the exact metric with its supports is accepted
  (`blowSupported_accepted_one`, `_two`); its check costs `1206` and `2775` counted operations
  (`blowSupported_work_one`, `_two`), at most a quarter of the products and additions of **every**
  accepted prefixpoint certificate (`supported_four_times_cheaper_one`, `_two`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.SupportedControls

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family

/-! ## The leak chain -/

/-- The supports of the leak chain, as data. -/
def leakSupports : Fin 4 → Finset (Fin 4) := ![{0}, {0, 3}, {2, 3}, {3}]

/-- **The leak chain's certificate with its supports.** -/
def leakSupported : Supported Unit (Fin 4) := ⟨correct, fun _ => leakSupports⟩

theorem leakSupported_accepted : supportedCheck leak discount leakSupported = true := by
  decide +kernel

/-- **On the leak chain the check on supports costs `281` counted operations; the incumbent's `799`.** -/
theorem leakSupported_work :
    supportedWork leak discount leakSupported = (56, 84, 116, 25) ∧
      prefixpointWork leak discount correct = (364, 304, 116, 15) :=
  ⟨by decide +kernel, quotientWork⟩

/-! ## The blown-up chain -/

/-- **The incumbent's certificate of the exact metric with its supports**: the two half-moves. -/
def blowSupported (m : ℕ) : Supported Unit (St m) := ⟨fullCert m, fun _ s => {firstMove s, secondMove s}⟩

theorem blowSupported_accepted_one : supportedCheck (blowup 1) discount (blowSupported 1) = true := by
  decide +kernel

theorem blowSupported_accepted_two : supportedCheck (blowup 2) discount (blowSupported 2) = true := by
  decide +kernel

theorem blowSupported_work_one :
    supportedWork (blowup 1) discount (blowSupported 1) = (256, 384, 488, 78) := by
  decide +kernel

theorem blowSupported_work_two :
    supportedWork (blowup 2) discount (blowSupported 2) = (600, 900, 1116, 159) := by
  decide +kernel

/-- **Four times cheaper at `8` states, without classes.** -/
theorem supported_four_times_cheaper_one {cert : Prefixpoint Unit (St 1)}
    (accepted : check (blowup 1) discount cert = true) :
    4 * (supportedWork (blowup 1) discount (blowSupported 1)).all ≤
      (prefixpointWork (blowup 1) discount cert).1 + (prefixpointWork (blowup 1) discount cert).2.1 := by
  obtain ⟨products, additions⟩ := prefixpointWork_lower accepted
  rw [card_St, Fintype.card_unit] at products additions
  rw [blowSupported_work_one]
  simp only [Work.all]
  omega

/-- **Four times cheaper at `12` states, without classes.** -/
theorem supported_four_times_cheaper_two {cert : Prefixpoint Unit (St 2)}
    (accepted : check (blowup 2) discount cert = true) :
    4 * (supportedWork (blowup 2) discount (blowSupported 2)).all ≤
      (prefixpointWork (blowup 2) discount cert).1 + (prefixpointWork (blowup 2) discount cert).2.1 := by
  obtain ⟨products, additions⟩ := prefixpointWork_lower accepted
  rw [card_St, Fintype.card_unit] at products additions
  rw [blowSupported_work_two]
  simp only [Work.all]
  omega

/-- **The bound is about an accepted certificate**: the incumbent's certificate of the exact metric at
`m = 1` is accepted. -/
theorem incumbent_accepted_one : check (blowup 1) discount (fullCert 1) = true := fullCert_accepted_one

/-! ## An accepted prefixpoint certificate at every size -/

/-- The kernel one off the diagonal, every pair filled in. -/
def trivialBlowCert (m : ℕ) : Prefixpoint Unit (St m) :=
  ⟨fun s t => if s = t then 0 else 1, fun _ _ _ => none⟩

/-- The observation of the blown-up chain differs by at most one. -/
theorem observe_gap_le_one :
    ∀ i j : Fin 4, |(![0, 0, 0, 1] : Fin 4 → ℚ) i - ![0, 0, 0, 1] j| ≤ 1 := by
  decide +kernel

/-- **An accepted prefixpoint certificate of the blown-up chain exists at every size**, so the theorems
about every accepted certificate (`four_times_cheaper`, `prefixpointWork_lower`) are not vacuous. -/
theorem trivialBlowCert_accepted (m : ℕ) : check (blowup m) discount (trivialBlowCert m) = true := by
  have bounded : ∀ u v : St m, (trivialBlowCert m).kernel u v ≤ 1 := by
    intro u v
    change (if u = v then (0 : ℚ) else 1) ≤ 1
    split_ifs <;> norm_num
  refine check_iff.mpr ⟨coreCheck_iff.mpr ⟨fun s t => ?_, fun i s t => ?_, fun a s t => ?_⟩,
    bounded, fun s t => ?_⟩
  · change (0 : ℚ) ≤ if s = t then 0 else 1
    split_ifs <;> norm_num
  · by_cases same : s = t
    · subst same
      simp [trivialBlowCert]
    · change |(![0, 0, 0, 1] : Fin 4 → ℚ) s.1 - ![0, 0, 0, 1] t.1| ≤ if s = t then 0 else 1
      rw [if_neg same]
      exact observe_gap_le_one s.1 t.1
  · by_cases same : s = t
    · subst same
      simp [coveredAt, coveredBetween, trivialBlowCert]
    · exact coveredAt_of_one_le discount_nonneg discount_lt_one.le bounded rfl
        (by change (1 : ℚ) ≤ if s = t then 0 else 1; rw [if_neg same])
  · change (if s = t then (0 : ℚ) else 1) = if t = s then 0 else 1
    by_cases same : s = t
    · subst same
      rfl
    · rw [if_neg same, if_neg (Ne.symm same)]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.SupportedControls
