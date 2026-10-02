import Mettapedia.Languages.VibeITP.Presentation.CompleteTerms
import Mettapedia.Languages.VibeITP.Presentation.TermShape
import Mettapedia.Languages.VibeITP.Presentation.Soundness

/-!
# Exact correspondence for shifting encoded Vibe-ITP terms

Constructive witnesses follow the specification's pruning and checked binder
arithmetic. The converse follows from the assembled meaning proof, including
the full hosted rule package. A refused shift has no derivation with an encoded
result, even when unrelated theory facts are present.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem shiftRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ shiftRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

theorem shift_of_depth_le (sig : Sig) (amount cutoff : Nat) (t : Term)
    (h : depth sig t ≤ cutoff) : shift sig amount cutoff t = some t := by
  cases t with
  | bvar i => simp only [depth] at h; simp [shift, h]
  | lit bs => rfl
  | app s args => simp [shift, h]

theorem shiftList_length (sig : Sig) (amount cutoff : Nat)
    (bs : List Nat) (ts us : List Term)
    (hs : shiftList sig amount cutoff bs ts = some us) : us.length = ts.length := by
  induction ts generalizing bs us with
  | nil =>
      have hu : [] = us := by simpa only [shiftList, Option.some.injEq] using hs
      subst us
      rfl
  | cons t ts ih =>
      by_cases hb : cutoff + bs.headD 0 < wordBound
      · rw [shiftList, if_pos hb] at hs
        cases ht : shift sig amount (cutoff + bs.headD 0) t with
        | none =>
            rw [ht] at hs
            cases shiftList sig amount cutoff bs.tail ts <;> cases hs
        | some u =>
            cases hus : shiftList sig amount cutoff bs.tail ts with
            | none => rw [ht, hus] at hs; cases hs
            | some us' =>
                have he : u :: us' = us := by
                  rw [ht, hus] at hs
                  exact Option.some.inj hs
                subst us
                simpa only [List.length_cons] using congrArg Nat.succ (ih bs.tail us' hus)
      · rw [shiftList, if_neg hb] at hs; cases hs

mutual
theorem complete_shift_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (amount cutoff : Nat) (t result : Term)
    (hShape : TermShape sig t) (hs : shift sig amount cutoff t = some result) :
    FODerivable R (jShift (encNat amount) (encNat cutoff)
      (encTerm sig t) (encTerm sig result)) := by
  by_cases hz : amount = 0
  · subst amount
    have he : t = result := Option.some.inj ((shift_zero sig cutoff t).symm.trans hs)
    subst result
    exact intro_rShiftZero (shiftRule_in hR (by simp [shiftRules]))
      (isData_encNat cutoff) (isData_encTerm sig t)
  · by_cases hlo : depth sig t ≤ cutoff
    · have he : t = result :=
        Option.some.inj ((shift_of_depth_le sig amount cutoff t hlo).symm.trans hs)
      subst result
      exact intro_rShiftLow (shiftRule_in hR (by simp [shiftRules]))
        (isData_encNat amount) (isData_encNat cutoff) (isData_encTerm sig t)
        (isData_encNat (depth sig t)) (complete_depth hR sig t)
        (complete_nle hR (depth sig t) cutoff hlo)
    · have hpos : 1 ≤ amount := by omega
      cases t with
      | bvar b =>
          simp only [depth] at hlo
          rw [shift, if_neg (not_or.mpr ⟨hz, hlo⟩)] at hs
          by_cases hb : b + amount + 1 < wordBound
          · have he : Term.bvar (b + amount) = result := by
              simpa only [if_pos hb, Option.some.injEq] using hs
            subst result
            rw [encNat_pos amount hpos]
            exact intro_rShiftBvar (shiftRule_in hR (by simp [shiftRules]))
              (isData_encPos amount) (isData_encNat cutoff) (isData_encNat b)
              (isData_encNat (b + amount)) (complete_nle hR cutoff b (by omega))
              (by simpa only [encNat_pos amount hpos] using complete_nadd hR b amount)
              (complete_nlt hR (b + amount) (wordBound - 1) (by
                have hbound : 0 < wordBound := by decide
                omega))
          · simp [hb] at hs
      | lit bytes => simp [depth] at hlo
      | app s args =>
          obtain ⟨info, hsig, harity, hw⟩ := TermShape.app_iff.mp hShape
          have hlen : (bindersOf sig s).length = args.length := by
            simpa only [bindersOf, hsig, SymInfo.arity] using harity.symm
          simp only [shift, if_neg (not_or.mpr ⟨hz, hlo⟩), shiftArgs_eq,
            List.drop_zero] at hs
          cases hus : shiftList sig amount cutoff (bindersOf sig s) args with
          | none => simp [hus] at hs
          | some us =>
              have he : Term.app s us = result := by
                simpa only [hus, Option.map_some, Option.some.injEq] using hs
              subst result
              have hlen' : (bindersOf sig s).length = us.length :=
                hlen.trans (shiftList_length sig amount cutoff _ _ _ hus).symm
              rw [encNat_pos amount hpos, encTerm_app', encTerm_app',
                encSym_eq, isFvarSym_eq]
              exact intro_rShiftApp (shiftRule_in hR (by simp [shiftRules]))
                (isData_encPos amount) (isData_encNat cutoff)
                (isData_encNat (symNumber s)) (isData_encKind (kindOf sig s))
                (isData_encNatList (bindersOf sig s)) (isData_encTermList sig args)
                (isData_encNat (depthBinders sig (bindersOf sig s) args))
                (isData_encBool ((kindOf sig s == .fvar) || hasFvarList sig args))
                (isData_encTermList sig us)
                (isData_encNat (depthBinders sig (bindersOf sig s) us))
                (isData_encBool (hasFvarList sig us))
                (isData_encBool ((kindOf sig s == .fvar) || hasFvarList sig us))
                (complete_nlt hR cutoff (depthBinders sig (bindersOf sig s) args)
                  (by simpa only [depth_app] using Nat.lt_of_not_ge hlo))
                (by simpa only [encNat_pos amount hpos] using
                  (complete_shiftList_shape hR sig amount cutoff (bindersOf sig s) args us
                    hlen hw hus))
                (complete_annArgs hR sig (bindersOf sig s) us hlen')
                (complete_kindFv hR (kindOf sig s) (hasFvarList sig us))
termination_by sizeOf t

theorem complete_shiftList_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (amount cutoff : Nat) (bs : List Nat) (ts us : List Term)
    (hlen : bs.length = ts.length) (hShape : TermShapeList sig ts)
    (hs : shiftList sig amount cutoff bs ts = some us) :
    FODerivable R (jShiftArgs (encNat amount) (encNat cutoff) (encNatList bs)
      (encTermList sig ts) (encTermList sig us)) := by
  cases ts with
  | nil =>
      have hbs : bs = [] := List.length_eq_zero_iff.mp hlen
      have hus : [] = us := by simpa only [shiftList, Option.some.injEq] using hs
      subst bs us
      exact intro_rShiftargsNil (shiftRule_in hR (by simp [shiftRules]))
        (isData_encNat amount) (isData_encNat cutoff)
  | cons t ts =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : bs.length = ts.length := by simpa using hlen
          have hw : TermShape sig t ∧ TermShapeList sig ts := TermShapeList.cons_iff.mp hShape
          by_cases hb : cutoff + b < wordBound
          · change (if cutoff + b < wordBound then
                match shift sig amount (cutoff + b) t, shiftList sig amount cutoff bs ts with
                | some u, some us' => some (u :: us')
                | _, _ => none
              else none) = some us at hs
            rw [if_pos hb] at hs
            cases ht : shift sig amount (cutoff + b) t with
            | none => simp [ht] at hs
            | some u =>
                cases hus : shiftList sig amount cutoff bs ts with
                | none => simp [ht, hus] at hs
                | some us' =>
                    have he : u :: us' = us := by
                      simpa only [ht, hus, Option.some.injEq] using hs
                    subst us
                    simp only [encNatList_cons, encTermList_cons]
                    exact intro_rShiftargsCons (shiftRule_in hR (by simp [shiftRules]))
                      (isData_encNat amount) (isData_encNat cutoff) (isData_encNat b)
                      (isData_encNatList bs) (isData_encTerm sig t)
                      (isData_encTermList sig ts) (isData_encTerm sig u)
                      (isData_encTermList sig us') (isData_encNat (cutoff + b))
                      (complete_nadd hR cutoff b) (complete_nword hR (cutoff + b) hb)
                      (complete_shift_shape hR sig amount (cutoff + b) t u hw.1 ht)
                      (complete_shiftList_shape hR sig amount cutoff bs ts us' hlen' hw.2 hus)
          · simp [shiftList, hb] at hs
termination_by sizeOf ts
end

theorem complete_shift {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (amount cutoff : Nat) (t result : Term)
    (hWF : WellFormed sig t = true) (hs : shift sig amount cutoff t = some result) :
    FODerivable R (jShift (encNat amount) (encNat cutoff)
      (encTerm sig t) (encTerm sig result)) :=
  complete_shift_shape hR sig amount cutoff t result (wellFormed_termShape sig t hWF) hs

theorem complete_shiftList {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (amount cutoff : Nat) (bs : List Nat) (ts us : List Term)
    (hlen : bs.length = ts.length) (hWF : WellFormedList sig ts = true)
    (hs : shiftList sig amount cutoff bs ts = some us) :
    FODerivable R (jShiftArgs (encNat amount) (encNat cutoff) (encNatList bs)
      (encTermList sig ts) (encTermList sig us)) :=
  complete_shiftList_shape hR sig amount cutoff bs ts us hlen
    (wellFormedList_termShape sig ts hWF) hs

theorem shift_of_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (t result : Term)
    (derivation : FODerivable (kernelRules ++ theoryRules T n)
      (jShift (encNat amount) (encNat cutoff) (encTerm T.sig t) (encTerm T.sig result))) :
    shift T.sig amount cutoff t = some result := by
  have hm : ShiftM T.sig (encNat amount) (encNat cutoff)
      (encTerm T.sig t) (encTerm T.sig result) := meaning_of_foDerivable h derivation
  obtain ⟨u, hu, he⟩ := hm amount cutoff t rfl rfl rfl
  have heu : result = u := encTerm_inj T.sig he
  simpa only [← heu] using hu

theorem shift_iff_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (t result : Term) (hWF : WellFormed T.sig t = true) :
    shift T.sig amount cutoff t = some result ↔
      FODerivable (kernelRules ++ theoryRules T n)
        (jShift (encNat amount) (encNat cutoff) (encTerm T.sig t) (encTerm T.sig result)) :=
  ⟨complete_shift (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig amount cutoff t result hWF,
    shift_of_foDerivable h amount cutoff t result⟩

theorem shift_shape_iff_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (t result : Term) (hShape : TermShape T.sig t) :
    shift T.sig amount cutoff t = some result ↔
      FODerivable (kernelRules ++ theoryRules T n)
        (jShift (encNat amount) (encNat cutoff) (encTerm T.sig t) (encTerm T.sig result)) :=
  ⟨complete_shift_shape (fun _ hr => List.mem_append.mpr (Or.inl hr))
      T.sig amount cutoff t result hShape,
    shift_of_foDerivable h amount cutoff t result⟩

theorem shiftList_of_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (bs : List Nat) (ts us : List Term)
    (derivation : FODerivable (kernelRules ++ theoryRules T n)
      (jShiftArgs (encNat amount) (encNat cutoff) (encNatList bs)
        (encTermList T.sig ts) (encTermList T.sig us))) :
    shiftList T.sig amount cutoff bs ts = some us := by
  have hm : ShiftArgsM T.sig (encNat amount) (encNat cutoff) (encNatList bs)
      (encTermList T.sig ts) (encTermList T.sig us) := meaning_of_foDerivable h derivation
  obtain ⟨us', hus, he⟩ := hm amount cutoff bs ts rfl rfl rfl rfl
  have heu : us = us' := encTermList_inj T.sig he
  simpa only [← heu] using hus

theorem shiftList_iff_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (bs : List Nat) (ts us : List Term)
    (hlen : bs.length = ts.length) (hShape : TermShapeList T.sig ts) :
    shiftList T.sig amount cutoff bs ts = some us ↔
      FODerivable (kernelRules ++ theoryRules T n)
        (jShiftArgs (encNat amount) (encNat cutoff) (encNatList bs)
          (encTermList T.sig ts) (encTermList T.sig us)) :=
  ⟨complete_shiftList_shape (fun _ hr => List.mem_append.mpr (Or.inl hr))
      T.sig amount cutoff bs ts us hlen hShape,
    shiftList_of_foDerivable h amount cutoff bs ts us⟩

theorem shift_refusal {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (t : Term) (hrefuse : shift T.sig amount cutoff t = none) :
    ∀ result, ¬ FODerivable (kernelRules ++ theoryRules T n)
      (jShift (encNat amount) (encNat cutoff) (encTerm T.sig t) (encTerm T.sig result)) := by
  intro result derivation
  have hs := shift_of_foDerivable h amount cutoff t result derivation
  rw [hrefuse] at hs
  cases hs

theorem shift_refusal_iff {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (t : Term) (hShape : TermShape T.sig t) :
    shift T.sig amount cutoff t = none ↔
      ∀ result, ¬ FODerivable (kernelRules ++ theoryRules T n)
        (jShift (encNat amount) (encNat cutoff) (encTerm T.sig t) (encTerm T.sig result)) := by
  constructor
  · exact shift_refusal h amount cutoff t
  · intro hrefuse
    cases hs : shift T.sig amount cutoff t with
    | none => rfl
    | some result =>
        exact False.elim (hrefuse result
          ((shift_shape_iff_foDerivable h amount cutoff t result hShape).mp hs))

theorem shiftList_refusal_iff {T : Theory} {n : Nat} (h : Hosted T n)
    (amount cutoff : Nat) (bs : List Nat) (ts : List Term)
    (hlen : bs.length = ts.length) (hShape : TermShapeList T.sig ts) :
    shiftList T.sig amount cutoff bs ts = none ↔
      ∀ us, ¬ FODerivable (kernelRules ++ theoryRules T n)
        (jShiftArgs (encNat amount) (encNat cutoff) (encNatList bs)
          (encTermList T.sig ts) (encTermList T.sig us)) := by
  constructor
  · intro hrefuse us derivation
    have hs := shiftList_of_foDerivable h amount cutoff bs ts us derivation
    rw [hrefuse] at hs
    cases hs
  · intro hrefuse
    cases hs : shiftList T.sig amount cutoff bs ts with
    | none => rfl
    | some us =>
        exact False.elim (hrefuse us
          ((shiftList_iff_foDerivable h amount cutoff bs ts us hlen hShape).mp hs))

end Mettapedia.Languages.VibeITP.Presentation
