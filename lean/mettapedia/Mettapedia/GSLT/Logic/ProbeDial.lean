import Mettapedia.GSLT.Logic.ObserverDetermination

/-!
# Probe contexts as a dial on the observer class

Adjoining probe contexts to an observer class `D` gives the class
`D.dial probes`.  In the saturated formulation the dial is an instance of
antitonicity:

* **monotone dial** (`relEquiv_dial_antitone`): more probes give a finer
  equivalence;
* **conservative probes** (`relEquiv_dial_iff`): adjoining probes leaves the
  equivalence unchanged exactly when every probe preserves the
  `D`-equivalence; a probe that maps a `D`-equivalent pair to an inequivalent
  one separates that pair (`not_relEquiv_dial_of_not_preserved`).

`ProbeControl` gives the non-vacuity control: two inert constants are
equivalent for the class with no probes and separated once a probe that opens
one of them is adjoined (`inert_constants_separated_by_probe`).  Labels are
saturated throughout; no minimality of labels is used.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.AdmissibleContextCongruence

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext

universe uS uContext uRule uAtom

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}

namespace AdmissibleClass

/-- The class `D` with probe contexts adjoined. -/
def dial (D : AdmissibleClass rules) (probes : Set rules.Context) : AdmissibleClass rules :=
  D ⊔ generatedBy probes

theorem le_dial (D : AdmissibleClass rules) (probes : Set rules.Context) : D ≤ D.dial probes :=
  le_sup_left

theorem dial_mono (D : AdmissibleClass rules) {probes probes' : Set rules.Context}
    (sub : probes ⊆ probes') : D.dial probes ≤ D.dial probes' :=
  sup_le_sup_left
    ((generatedBy_le_iff (A := generatedBy probes')).mpr fun _ member => generator_mem (sub member)) D

variable (observations : ContextualRules.Observations.{uAtom} S)

/-- **T8 (monotone dial).**  More probes give a finer equivalence. -/
theorem relEquiv_dial_antitone (D : AdmissibleClass rules) {probes probes' : Set rules.Context}
    (sub : probes ⊆ probes') {left right : S.Term}
    (related : (D.dial probes').RelEquiv observations left right) :
    (D.dial probes).RelEquiv observations left right :=
  AdmissibleClass.relEquiv_antitone observations (D.dial_mono sub) related

/-- **Conservative probes.**  Adjoining probes leaves the equivalence unchanged
exactly when every probe preserves it. -/
theorem relEquiv_dial_iff (D : AdmissibleClass rules) (probes : Set rules.Context) :
    (∀ left right, (D.dial probes).RelEquiv observations left right ↔
        D.RelEquiv observations left right) ↔
      ∀ probe ∈ probes, Preserves probe (D.RelEquiv observations) :=
  D.relEquiv_sup_generatedBy_iff observations probes

/-- **A probe that breaks the `D`-equivalence separates.** -/
theorem not_relEquiv_dial_of_not_preserved (D : AdmissibleClass rules)
    {probes : Set rules.Context} {probe : rules.Context} (member : probe ∈ probes)
    {left right : S.Term}
    (separated : ¬ D.RelEquiv observations (rules.plug probe left) (rules.plug probe right)) :
    ¬ (D.dial probes).RelEquiv observations left right :=
  D.not_relEquiv_sup_of_not_preserved observations member separated

end AdmissibleClass

/-! ## Non-vacuity: a probe separates two inert constants -/

namespace ProbeControl

/-- Two constants, the result of opening one of them, and the probe former. -/
inductive Tm where
  | first
  | second
  | opened
  | probe (target : Tm)
  deriving DecidableEq

/-- The probe opens `first` and nothing else. -/
inductive Opens : Tm → Tm → Prop where
  | ask : Opens (.probe .first) .opened

abbrev probeGSLT : GSLT where
  Term := Tm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Opens
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- Wrap a term in `depth` probes. -/
def probeTimes : ℕ → Tm → Tm
  | 0, term => term
  | depth + 1, term => .probe (probeTimes depth term)

theorem probeTimes_add (outer inner : ℕ) (term : Tm) :
    probeTimes (outer + inner) term = probeTimes outer (probeTimes inner term) := by
  induction outer with
  | zero => simp [probeTimes]
  | succ outer ih =>
      rw [Nat.succ_add]
      simp [probeTimes, ih]

/-- Contexts are nested probes. -/
abbrev probeRules : ContextualRules probeGSLT where
  Context := ℕ
  identity := 0
  compose outer inner := outer + inner
  plug := probeTimes
  plug_identity _ := rfl
  plug_compose := probeTimes_add
  plug_resp context := by
    intro left right equal
    subst equal
    rfl
  Rule := Unit
  fires _ := Opens
  fires_resp_left := by
    intro _ left right target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ source target target' fires equal
    subst equal
    exact fires
  fires_step := fun fires => fires

/-- No base observations. -/
abbrev silent : ContextualRules.Observations probeGSLT where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim

/-- The class with no probes. -/
abbrev unprobed : AdmissibleClass probeRules := AdmissibleClass.generatedBy ∅

/-- The class of the identity context only. -/
def depthZero : AdmissibleClass probeRules where
  Admissible depth := depth = 0
  identity_mem := rfl
  compose_mem := by
    rintro _ _ rfl rfl
    rfl

theorem unprobed_depth {depth : ℕ} (admissible : unprobed.Admissible depth) : depth = 0 :=
  (AdmissibleClass.generatedBy_le_iff.mpr (Set.empty_subset _) : unprobed ≤ depthZero)
    depth admissible

/-- The constants are equivalent when no probe may be used. -/
theorem unprobed_relEquiv : unprobed.RelEquiv silent .first .second := by
  refine ⟨fun left right => left = .first ∧ right = .second, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · rintro _ _ ⟨rfl, rfl⟩ label target step
    have isZero := unprobed_depth label.2
    change Opens (probeTimes label.1 .first) target at step
    rw [isZero] at step
    cases step
  · rintro _ _ ⟨rfl, rfl⟩ label target step
    have isZero := unprobed_depth label.2
    change Opens (probeTimes label.1 .second) target at step
    rw [isZero] at step
    cases step
  · intro _ _ _ atom
    exact atom.1.elim

/-- **Non-vacuity.**  Two inert constants are equivalent without probes and
separated once the probe opening the first is adjoined. -/
theorem inert_constants_separated_by_probe :
    unprobed.RelEquiv silent .first .second ∧
      ¬ (unprobed.dial {1}).RelEquiv silent .first .second := by
  refine ⟨unprobed_relEquiv, ?_⟩
  intro related
  have probeAdmissible : (unprobed.dial {1}).Admissible 1 :=
    (le_sup_right : AdmissibleClass.generatedBy (rules := probeRules) {1} ≤ unprobed.dial {1}) 1
      (AdmissibleClass.generator_mem rfl)
  obtain ⟨_, step, _⟩ := AdmissibleContextCongruence.bisimilar_forward related
    ⟨1, probeAdmissible⟩ (Opens.ask : Opens (probeTimes 1 .first) .opened)
  cases step

end ProbeControl

end Mettapedia.GSLT.AdmissibleContextCongruence
