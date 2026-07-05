/-
# Finite-probe rigidity counterexample for the Gauthier E1 evaluator

Finite agreement on a probed prefix does not force extensional equality.  This file keeps the
witness deliberately small and evaluates it through the real E1 semantics and `EmitsPrefix` layer.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.BigStepGSLT

namespace Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT

def probeId : Prog := Org.X

def probeZeroAfterZero : Prog := Org.cond Org.X Org.X Org.z

def oneProbePrefix : List Int := [0]

theorem probeId_emits_one_prefix :
    EmitsPrefix orgE1Signature 20 probeId oneProbePrefix := by
  intro i v hget
  cases i with
  | zero =>
      simp [oneProbePrefix, listGet?] at hget
      subst v
      rw [emitsAt_iff]
      refine ⟨Store.zero, ?_⟩
      simp [probeId, Org.X, eval, orgE1Signature, entryAt, listGet?, entry, seed]
  | succ i =>
      simp [oneProbePrefix, listGet?] at hget

theorem probeZeroAfterZero_emits_one_prefix :
    EmitsPrefix orgE1Signature 20 probeZeroAfterZero oneProbePrefix := by
  intro i v hget
  cases i with
  | zero =>
      simp [oneProbePrefix, listGet?] at hget
      subst v
      rw [emitsAt_iff]
      refine ⟨Store.zero, ?_⟩
      simp [probeZeroAfterZero, Org.cond, Org.X, Org.z, eval, orgE1Signature, entryAt,
        listGet?, entry, seed]
  | succ i =>
      simp [oneProbePrefix, listGet?] at hget

theorem probe_witness_differs_at_seed_one :
    eval 20 orgE1Signature probeId (seed 1) Store.zero =
      some (1, Store.zero) ∧
    eval 20 orgE1Signature probeZeroAfterZero (seed 1) Store.zero =
      some (0, Store.zero) := by
  constructor <;>
    simp [probeId, probeZeroAfterZero, Org.cond, Org.X, Org.z, eval, orgE1Signature,
      entryAt, listGet?, entry, seed]

theorem probe_witness_not_extensional :
    ¬ Extensional orgE1Signature probeId probeZeroAfterZero := by
  intro h
  have hdiff := probe_witness_differs_at_seed_one
  have hsame := h 20 (seed 1) Store.zero
  rw [hdiff.1, hdiff.2] at hsame
  cases hsame

theorem one_probe_agreement_not_extensional :
    oneProbePrefix.length = 1 ∧
      EmitsPrefix orgE1Signature 20 probeId oneProbePrefix ∧
      EmitsPrefix orgE1Signature 20 probeZeroAfterZero oneProbePrefix ∧
      ¬ Extensional orgE1Signature probeId probeZeroAfterZero := by
  exact ⟨rfl, probeId_emits_one_prefix, probeZeroAfterZero_emits_one_prefix,
    probe_witness_not_extensional⟩

theorem finite_probe_rigidity_negative_witness :
    ∃ p q pref fuel,
      pref.length = 1 ∧
        EmitsPrefix orgE1Signature fuel p pref ∧
        EmitsPrefix orgE1Signature fuel q pref ∧
        ¬ Extensional orgE1Signature p q := by
  exact ⟨probeId, probeZeroAfterZero, oneProbePrefix, 20, one_probe_agreement_not_extensional⟩

end Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity
