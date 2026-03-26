import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PresentMoment

/-!
# OSLF Paper Section 12 Worked Examples

This file formalizes concrete theorem-level worked examples for the three
`oslf.pdf` Section 12 placeholders:

- §12.1 compile-time firewall
- §12.2 race detection
- §12.3 secrecy
-/

namespace Mettapedia.OSLF.Framework.PaperSection12Examples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PresentMoment

/-- OSLF paper §12.1 (compile-time firewall): the canonical policy blocks
set-context descent while the extension policy admits it. -/
theorem compile_time_firewall_worked_example :
    (∀ q, ¬ langReduces rhoCalc rhoSetDropWitness q) ∧
      (∃ q, langReduces rhoCalcSetExt rhoSetDropWitness q) := by
  exact rhoSetDropWitness_canonical_vs_setExt

/-- Concrete race channel used in §12.2 worked example. -/
def raceChan : Pattern := .fvar "x"

/-- Concrete payload used in §12.2 worked example. -/
def racePayload : Pattern := .apply "PZero" []

/-- First race body. -/
def raceBody1 : Pattern := .bvar 0

/-- Second race body (distinct from `raceBody1`). -/
def raceBody2 : Pattern := .apply "PDrop" [.apply "NQuote" [.bvar 0]]

/-- Bag with one output and two competing inputs on the same channel. -/
def raceElems : List Pattern :=
  [ .apply "POutput" [raceChan, racePayload]
  , .apply "PInput" [raceChan, .lambda none raceBody1]
  , .apply "PInput" [raceChan, .lambda none raceBody2]
  ]

/-- Packed pattern for the race bag. -/
def raceBag : Pattern := .collection .hashBag raceElems none

/-- The concrete race bag satisfies `hasRace`. -/
theorem raceElems_hasRace : hasRace raceElems raceChan := by
  refine ⟨⟨racePayload, by simp [raceElems, raceChan, racePayload]⟩, ?_⟩
  refine ⟨raceBody1, raceBody2, ?_, ?_, ?_⟩
  · simp [raceElems, raceChan, raceBody1]
  · simp [raceElems, raceChan, raceBody2]
  · decide

/-- The concrete race bag has no duplicated subprocesses. -/
theorem raceElems_nodup : raceElems.Nodup := by
  decide

/-- OSLF paper §12.2 (race detection): concrete witness of true
non-deterministic branching from a race. -/
theorem race_detection_worked_example :
    ∃ r₁ r₂,
      Nonempty (Reduces raceBag r₁) ∧
      Nonempty (Reduces raceBag r₂) ∧
      r₁ ≠ r₂ := by
  simpa [raceBag, raceElems] using
    race_nondeterminism (h_race := raceElems_hasRace) (h_nodup := raceElems_nodup)

/-- Secret/private channel used in §12.3 worked example. -/
def secretChan : Pattern := .fvar "secret"

/-- Public/environment channel used in §12.3 worked example. -/
def publicChan : Pattern := .fvar "public"

/-- Minimal payload used in §12.3 worked example. -/
def pzero : Pattern := .apply "PZero" []

/-- Agent with internal communication capability on a private channel. -/
def secrecyAgent : Pattern :=
  .collection .hashBag [
    .apply "POutput" [secretChan, pzero],
    .apply "PInput" [secretChan, .lambda none (.bvar 0)]
  ] none

/-- Environment that does not mention the private channel. -/
def secrecyEnv : Pattern :=
  .collection .hashBag [
    .apply "POutput" [publicChan, pzero]
  ] none

/-- The private channel is internal to the agent against this environment. -/
theorem secrecy_secret_in_internalChannels :
    secretChan ∈ internalChannels secrecyAgent secrecyEnv := by
  unfold internalChannels secrecyAgent secrecyEnv
  refine ⟨?_, ?_⟩
  · constructor
    · simp [secretChan, pzero, Context.allNames]
    · simp [secretChan, publicChan, pzero, Context.freeNames]
  · unfold Context.canInteract
    refine ⟨?_, ?_⟩
    · refine ⟨.bvar 0, by simp [secretChan, pzero]⟩
    · refine ⟨pzero, by simp [secretChan, pzero]⟩

/-- The private channel is not in the environment's free names. -/
theorem secrecy_secret_not_in_env_freeNames :
    secretChan ∉ Context.freeNames secrecyEnv := by
  have hdisj := int_disjoint_env secrecyAgent secrecyEnv
  have hxIn : secretChan ∈ internalChannels secrecyAgent secrecyEnv :=
    secrecy_secret_in_internalChannels
  intro hxEnv
  have : secretChan ∈ internalChannels secrecyAgent secrecyEnv ∩ Context.freeNames secrecyEnv :=
    ⟨hxIn, hxEnv⟩
  have hnone : secretChan ∉ internalChannels secrecyAgent secrecyEnv ∩ Context.freeNames secrecyEnv := by
    simp [hdisj]
  exact hnone this

/-- The private channel does not appear as a surface/external channel. -/
theorem secrecy_secret_not_surface :
    secretChan ∉ surfaceChannels secrecyAgent secrecyEnv := by
  intro hsurf
  unfold surfaceChannels at hsurf
  simp only [Set.mem_setOf, Set.mem_inter_iff] at hsurf
  exact secrecy_secret_not_in_env_freeNames hsurf.1.2

/-- OSLF paper §12.3 (secrecy): concrete private channel remains hidden
from environment-level observability. -/
theorem secrecy_worked_example :
    secretChan ∈ internalChannels secrecyAgent secrecyEnv ∧
    secretChan ∉ Context.freeNames secrecyEnv ∧
    secretChan ∉ surfaceChannels secrecyAgent secrecyEnv := by
  exact ⟨secrecy_secret_in_internalChannels,
    secrecy_secret_not_in_env_freeNames,
    secrecy_secret_not_surface⟩

/-- Canonical bundle for OSLF paper §12 worked examples. -/
theorem section12_worked_examples_bundle :
    ((∀ q, ¬ langReduces rhoCalc rhoSetDropWitness q) ∧
      (∃ q, langReduces rhoCalcSetExt rhoSetDropWitness q)) ∧
    (∃ r₁ r₂,
      Nonempty (Reduces raceBag r₁) ∧
      Nonempty (Reduces raceBag r₂) ∧
      r₁ ≠ r₂) ∧
    (secretChan ∈ internalChannels secrecyAgent secrecyEnv ∧
      secretChan ∉ Context.freeNames secrecyEnv ∧
      secretChan ∉ surfaceChannels secrecyAgent secrecyEnv) := by
  exact ⟨compile_time_firewall_worked_example,
    race_detection_worked_example,
    secrecy_worked_example⟩

end Mettapedia.OSLF.Framework.PaperSection12Examples
