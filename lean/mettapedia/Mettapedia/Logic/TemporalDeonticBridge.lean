import Mettapedia.Logic.DDLPlus.Core
import Mettapedia.Logic.PLNChapter14TemporalCausal
import Mettapedia.Logic.GovernanceReasoning.Core

/-!
# Temporal-Deontic Bridge

Connects temporal reasoning (PLNTemporal `Lead`/`Lag` shifts) with the DDLPlus
deontic obligation operators.  The central result is `ideal_obl_temporal_persistence`:
under a time-uniform obligation structure, ideal obligations persist as time advances
(with the content interpreted relative to the base time).

Additionally bridges PLN causal heuristics (`SpuriousCausalCandidate`) with DTS
obligation: if an obligation structure respects intensional grounding, then spurious
causal candidates cannot appear as obligatory.

## Mathematical Structure

The world type is `w × T` where `T` is an `AddCommGroup` (time).  A
`TemporallyUniformOb` frame satisfies two shift-invariance conditions:

- `pv_shift`: accessibility is translation-invariant: shifting both endpoints by Δ
  preserves pv-membership.
- `ob_shift`: shifting the base point of pv by Δ shifts the obligation content
  backward by Δ (the "lag" compatibility).

These together give the **temporal-lag persistence** theorem: ideal obligation at
(v,t₀) implies lag-shifted ideal obligation at (v,t₀+Δ).

## References

- Carmo, J. & Jones, A. (2002). "Deontic Logic and Contrary-to-Duties"
- Shanahan, M. (1999). "The event calculus explained" (temporal shift intuition)
- Goertzel, B. et al. *Probabilistic Logic Networks* (extensional vs intensional)
-/

namespace Mettapedia.Logic.TemporalDeonticBridge

open Mettapedia.Logic.DDLPlus.Core
open Mettapedia.Logic.PLNChapter14TemporalCausal
open Mettapedia.Logic.GovernanceReasoning.Core

/-! ## §1 Temporal Meanings -/

/-- A temporal world pairs a base world with a time point. -/
abbrev TemporalWorld (w T : Type*) := w × T

/-- A temporal meaning: a `Meaning` over a `TemporalWorld`.
    Unfolding: `TemporalMeaning c w T = c → w × T → Prop`. -/
abbrev TemporalMeaning (c w T : Type*) := Meaning c (w × T)

section TemporalShifts

variable {c w T : Type*} [Add T]

/-- **Lead** (future shift): evaluate φ at time t+Δ from the current time.

    `(meaningLead φ Δ) ctx ⟨v, t⟩ = φ ctx ⟨v, t + Δ⟩`

    Intuitively: "φ will hold Δ time units from now". -/
def meaningLead (φ : TemporalMeaning c w T) (Δ : T) : TemporalMeaning c w T :=
  fun ctx ⟨v, t⟩ => φ ctx ⟨v, t + Δ⟩

variable [Sub T]

/-- **Lag** (past shift): evaluate φ at time t−Δ from the current time.

    `(meaningLag φ Δ) ctx ⟨v, t⟩ = φ ctx ⟨v, t - Δ⟩`

    Intuitively: "φ held Δ time units ago". -/
def meaningLag (φ : TemporalMeaning c w T) (Δ : T) : TemporalMeaning c w T :=
  fun ctx ⟨v, t⟩ => φ ctx ⟨v, t - Δ⟩

end TemporalShifts

/-! ## §2 Temporally-Uniform Obligation Structure -/

/-- A `DDLPlusFrame` on `w × T` is **temporally uniform** if the accessibility and
    obligation relations are compatible with time translation.

    - `pv_shift`: pv is invariant under simultaneous translation of both endpoints.
      For any Δ, `pv ⟨v,t⟩ ⟨v',t'⟩ ↔ pv ⟨v,t+Δ⟩ ⟨v',t'+Δ⟩`.

    - `ob_shift`: shifting the base point of pv by Δ shifts the obligation content
      backward: `ob (pv ⟨v,t⟩) Y ↔ ob (pv ⟨v,t+Δ⟩) (Y[t' ↦ t'-Δ])`.
      Geometrically: pv ⟨v,t+Δ⟩ is the "Δ-translate" of pv ⟨v,t⟩, so to ask the
      same question on the translated domain one must pre-compose with the inverse
      shift (−Δ) on the content. -/
structure TemporallyUniformOb {w T : Type*} [AddCommGroup T]
    (F : DDLPlusFrame (w × T)) where
  /-- pv is translation-invariant: shift both endpoints by Δ preserves membership. -/
  pv_shift : ∀ (Δ : T) (v : w) (t : T) (v' : w) (t' : T),
      F.pv ⟨v, t⟩ ⟨v', t'⟩ ↔ F.pv ⟨v, t + Δ⟩ ⟨v', t' + Δ⟩
  /-- ob is compatible with base-point shift: shifting base by Δ lags the content by Δ. -/
  ob_shift : ∀ (Δ : T) (v : w) (t : T) (Y : WProp (w × T)),
      F.ob (F.pv ⟨v, t⟩) Y ↔
        F.ob (F.pv ⟨v, t + Δ⟩) (fun p : w × T => Y ⟨p.1, p.2 - Δ⟩)

/-! ## §3 Temporal-Lag Persistence of Ideal Obligation

The main theorem: under a temporally-uniform frame, ideal obligation at ⟨v,t₀⟩
persists at ⟨v,t₀+Δ⟩ with the content shifted back by Δ (the "lag" interpretation).

Proof sketch:
- ob part: apply `ob_shift` forward.
- existence part: shift the violation witness by Δ (using `pv_shift`);
  the negation condition simplifies by `add_sub_cancel_right`. -/

/-- **Temporal-lag persistence of ideal obligation**.

    If φ is ideally obligatory at world (v,t₀), then at world (v,t₀+Δ) the
    "lag-shifted" version `meaningLag φ Δ` (= "φ held Δ ago") is still ideally
    obligatory.

    This captures the stationarity of obligation under time translation:
    the obligation structure does not distinguish absolute time, only relative time. -/
theorem ideal_obl_temporal_persistence
    {w T : Type*} [AddCommGroup T]
    (F : DDLPlusFrame (w × T)) (tub : TemporallyUniformOb F)
    (φ : TemporalMeaning Unit w T) (v : w) (t₀ Δ : T)
    (h : ideal_obl F φ () ⟨v, t₀⟩) :
    ideal_obl F (meaningLag φ Δ) () ⟨v, t₀ + Δ⟩ := by
  obtain ⟨hob, ⟨v_w, t_w⟩, hpv, hne⟩ := h
  refine ⟨?_, ⟨v_w, t_w + Δ⟩, ?_, ?_⟩
  · -- ob part: apply ob_shift forward
    exact (tub.ob_shift Δ v t₀ (φ ())).mp hob
  · -- pv part: use pv_shift to translate the witness
    exact (tub.pv_shift Δ v t₀ v_w t_w).mp hpv
  · -- negation: lag-shift applied at t_w+Δ recovers φ at t_w
    simp only [meaningLag, add_sub_cancel_right]
    exact hne

/-! ## §4 Corollary: Violation Persistence Under Time Shift

The violation witness (∃ v' where ¬φ) is also preserved, as the proof above shows.
We isolate the pv-existence part as a standalone lemma. -/

/-- Under temporal uniformity, pv-accessible violation witnesses shift with the base point. -/
theorem pv_violation_shift
    {w T : Type*} [AddCommGroup T]
    (F : DDLPlusFrame (w × T)) (tub : TemporallyUniformOb F)
    (φ : WProp (w × T)) (v : w) (t₀ Δ : T)
    (h : ∃ p : w × T, F.pv ⟨v, t₀⟩ p ∧ ¬ φ p) :
    ∃ p : w × T, F.pv ⟨v, t₀ + Δ⟩ p ∧ ¬ (fun q : w × T => φ ⟨q.1, q.2 - Δ⟩) p := by
  obtain ⟨⟨v_w, t_w⟩, hpv, hne⟩ := h
  exact ⟨⟨v_w, t_w + Δ⟩, (tub.pv_shift Δ v t₀ v_w t_w).mp hpv,
         by simp [add_sub_cancel_right]; exact hne⟩

/-! ## §5 Intensional Grounding and Spurious Causal Prohibition

Connects PLN causal heuristics with DTS obligation.

A `SpuriousCausalCandidate` is an event x at time t that has extensional
but not intensional predictive support (PLNChapter14TemporalCausal.lean §CausalHeuristics).
An obligation structure that respects intensional grounding cannot oblige spurious candidates. -/

/-- An obligation structure (DTS) **obligates only intensionally-grounded events**
    if: for every element x that is obligated, x has intensional predictive support
    at every time t.

    This is the structural hypothesis linking the causal heuristic layer (PLN)
    with the deontic layer (DTS). -/
structure ObligesOnlyIntensional
    {Domain : Type*} {Time : Type*}
    (profile : PredictiveCausalProfile (Domain := Domain) (Time := Time))
    (d : DTS Domain) : Prop where
  /-- Every obligated element has intensional support at all times. -/
  ob_intensional : ∀ x, d.ob x → ∀ t, profile.intensional x t

/-- **Spurious-prohibition theorem**.

    If a DTS obligation structure respects intensional grounding (`ObligesOnlyIntensional`),
    then no spurious causal candidate can be obligated.

    Proof: a spurious candidate `x` at time `t` satisfies `¬ profile.intensional x t`
    (by `SpuriousCausalCandidate`), but `d.ob x` would imply `profile.intensional x t`
    for all `t` (by `ob_intensional`): contradiction. -/
theorem spurious_not_obligatory
    {Domain : Type*} {Time : Type*}
    (profile : PredictiveCausalProfile (Domain := Domain) (Time := Time))
    (d : DTS Domain)
    (hGnd : ObligesOnlyIntensional profile d)
    {x : Domain} {t : Time}
    (hSpur : SpuriousCausalCandidate profile x t) :
    ¬ d.ob x := by
  intro hOb
  exact hSpur.2 (hGnd.ob_intensional x hOb t)

/-- Contrapositive: if x is obligated, it is not a spurious causal candidate at any time. -/
theorem obligatory_not_spurious
    {Domain : Type*} {Time : Type*}
    (profile : PredictiveCausalProfile (Domain := Domain) (Time := Time))
    (d : DTS Domain)
    (hGnd : ObligesOnlyIntensional profile d)
    {x : Domain} (hOb : d.ob x) (t : Time) :
    ¬ SpuriousCausalCandidate profile x t :=
  fun hSpur => hSpur.2 (hGnd.ob_intensional x hOb t)

/-! ## §6 Summary -/

#check @TemporallyUniformOb
#check @meaningLead
#check @meaningLag
#check @ideal_obl_temporal_persistence
#check @ObligesOnlyIntensional
#check @spurious_not_obligatory
#check @obligatory_not_spurious

end Mettapedia.Logic.TemporalDeonticBridge
