import Mettapedia.Languages.VibeITP.Presentation.CompleteTerms
import Mettapedia.Languages.VibeITP.Presentation.CompleteShift
import Mettapedia.Languages.VibeITP.Presentation.TermShape
import Mettapedia.Languages.VibeITP.Presentation.Soundness

/-!
# Constructive de Bruijn substitution correspondence

The witnesses retain the specification's reversed parameter order, depth
pruning and checks on binder offsets and shifted replacement terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem substRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ substRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

theorem wellFormedList_mem (sig : Sig) (ts : List Term)
    (hWF : WellFormedList sig ts = true) (t : Term) (ht : t ∈ ts) :
    WellFormed sig t = true := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
      have hw : WellFormed sig u = true ∧ WellFormedList sig us = true := by
        simpa only [WellFormedList, Bool.and_eq_true] using hWF
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hw.1
      · exact ih hw.2 ht

theorem complete_nth_terms {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (ts : List Term) (i : Nat) (t : Term) (hget : ts[i]? = some t) :
    FODerivable R (jNth (encTermList sig ts) (encNat i) (encTerm sig t)) := by
  rw [decList_unique (encTermList sig ts) _ (decList_encTermList sig ts)]
  apply complete_nth hR (ts.map (encTerm sig)) i (encTerm sig t)
  · simp [isData_encTerm]
  · simp [List.getElem?_map, hget]

theorem substList_length (sig : Sig) (numArgs : Nat) (args : List Term) (offset : Nat)
    (bs : List Nat) (ts us : List Term)
    (hSubst : substList sig numArgs args offset bs ts = some us) : us.length = ts.length := by
  induction ts generalizing bs us with
  | nil =>
      simp only [substList, Option.some.injEq] at hSubst
      subst us
      rfl
  | cons t ts ih =>
      simp only [substList] at hSubst
      split at hSubst
      · cases ht : substGo sig numArgs args (offset + bs.headD 0) t with
        | none => simp only [ht, reduceCtorEq] at hSubst
        | some u =>
            cases hts : substList sig numArgs args offset bs.tail ts with
            | none => simp only [ht, hts, reduceCtorEq] at hSubst
            | some us' =>
                simp only [ht, hts, Option.some.injEq] at hSubst
                subst us
                simp only [List.length_cons]
                exact congrArg (· + 1) (ih bs.tail us' hts)
      · simp at hSubst

theorem substGoArgs_length (sig : Sig) (numArgs : Nat) (args : List Term)
    (s : SymId) (offset index : Nat) (ts us : List Term)
    (hSubst : substGoArgs sig numArgs args s offset index ts = some us) :
    us.length = ts.length :=
  substList_length sig numArgs args offset ((bindersOf sig s).drop index) ts us
    (by simpa only [substGoArgs_eq] using hSubst)

theorem substGo_of_depth_le (sig : Sig) (numArgs : Nat) (args : List Term)
    (offset : Nat) (t : Term) (h : depth sig t ≤ offset) :
    substGo sig numArgs args offset t = some t := by
  cases t with
  | bvar i => simp only [depth] at h; simp [substGo, h]
  | lit bs => rfl
  | app s ts => simp [substGo, h]

mutual
theorem complete_subst_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (offset : Nat) (t result : Term)
    (harglen : args.length = numArgs) (hargsShape : TermShapeList sig args)
    (hShape : TermShape sig t)
    (hs : substGo sig numArgs args offset t = some result) :
    FODerivable R (jSubst (encNat numArgs) (encTermList sig args) (encNat offset)
      (encTerm sig t) (encTerm sig result)) := by
  by_cases hlo : depth sig t ≤ offset
  · have he : t = result :=
      Option.some.inj ((substGo_of_depth_le sig numArgs args offset t hlo).symm.trans hs)
    subst result
    exact intro_rSubstLow (substRule_in hR (by simp [substRules]))
      (isData_encNat numArgs) (isData_encTermList sig args) (isData_encNat offset)
      (isData_encTerm sig t) (isData_encNat (depth sig t)) (complete_depth hR sig t)
      (complete_nle hR (depth sig t) offset hlo)
  · cases t with
    | bvar b =>
        simp only [depth] at hlo
        rw [substGo, if_neg hlo] at hs
        by_cases hp : b - offset < numArgs
        · rw [if_pos hp] at hs
          let i := numArgs - 1 - (b - offset)
          have hi : i < args.length := by dsimp [i]; omega
          let a := args[i]
          have hget : args[i]? = some a := List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
          have hD : args.getD i (.bvar 0) = a := by
            rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
          change shift sig offset 0 (args.getD i (.bvar 0)) = some result at hs
          rw [hD] at hs
          have hsa : TermShape sig a := hargsShape.of_mem (List.mem_of_getElem? hget)
          have hbase := complete_nadd hR offset (b - offset)
          rw [show offset + (b - offset) = b by omega] at hbase
          have hindex := complete_nadd hR i (b - offset + 1)
          rw [show i + (b - offset + 1) = numArgs by dsimp [i]; omega] at hindex
          exact intro_rSubstParam (substRule_in hR (by simp [substRules]))
            (isData_encNat numArgs) (isData_encTermList sig args) (isData_encNat offset)
            (isData_encNat b) (isData_encNat (b - offset))
            (isData_encNat (b - offset + 1)) (isData_encNat i) (isData_encTerm sig a)
            (isData_encTerm sig result) hbase (complete_nlt hR (b - offset) numArgs hp)
            (complete_nadd hR (b - offset) 1) hindex (complete_nth_terms hR sig args i a hget)
            (complete_shift_shape hR sig offset 0 a result hsa hs)
        · rw [if_neg hp] at hs
          by_cases hb : b - offset + 1 < wordBound
          · rw [if_pos hb] at hs
            have he : Term.bvar (b - offset) = result := Option.some.inj hs
            subst result
            have hbase := complete_nadd hR offset (b - offset)
            rw [show offset + (b - offset) = b by omega] at hbase
            exact intro_rSubstAbove (substRule_in hR (by simp [substRules]))
              (isData_encNat numArgs) (isData_encTermList sig args) (isData_encNat offset)
              (isData_encNat b) (isData_encNat (b - offset))
              (isData_encNat (b - offset + 1)) hbase
              (complete_nle hR numArgs (b - offset) (by omega))
              (complete_nadd hR (b - offset) 1) (complete_nword hR (b - offset + 1) hb)
          · rw [if_neg hb] at hs
            cases hs
    | lit bytes => simp [depth] at hlo
    | app s ts =>
        obtain ⟨info, hsig, harity, hw⟩ := TermShape.app_iff.mp hShape
        have hlen : (bindersOf sig s).length = ts.length := by
          simpa only [bindersOf, hsig, SymInfo.arity] using harity.symm
        simp only [substGo, if_neg hlo, substGoArgs_eq, List.drop_zero] at hs
        cases hus : substList sig numArgs args offset (bindersOf sig s) ts with
        | none => simp [hus] at hs
        | some us =>
            have he : Term.app s us = result := by
              simpa only [hus, Option.map_some, Option.some.injEq] using hs
            subst result
            have hlen' : (bindersOf sig s).length = us.length :=
              hlen.trans (substList_length sig numArgs args offset _ _ _ hus).symm
            rw [encTerm_app', encTerm_app', encSym_eq, isFvarSym_eq]
            exact intro_rSubstApp (substRule_in hR (by simp [substRules]))
              (isData_encNat numArgs) (isData_encTermList sig args) (isData_encNat offset)
              (isData_encNat (symNumber s)) (isData_encKind (kindOf sig s))
              (isData_encNatList (bindersOf sig s)) (isData_encTermList sig ts)
              (isData_encNat (depthBinders sig (bindersOf sig s) ts))
              (isData_encBool ((kindOf sig s == .fvar) || hasFvarList sig ts))
              (isData_encTermList sig us)
              (isData_encNat (depthBinders sig (bindersOf sig s) us))
              (isData_encBool (hasFvarList sig us))
              (isData_encBool ((kindOf sig s == .fvar) || hasFvarList sig us))
              (complete_nlt hR offset (depthBinders sig (bindersOf sig s) ts)
                (by simpa only [depth_app] using Nat.lt_of_not_ge hlo))
              (complete_substList_shape hR sig numArgs args offset (bindersOf sig s) ts us
                harglen hargsShape hlen hw hus)
              (complete_annArgs hR sig (bindersOf sig s) us hlen')
              (complete_kindFv hR (kindOf sig s) (hasFvarList sig us))
termination_by sizeOf t

theorem complete_substList_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (offset : Nat)
    (bs : List Nat) (ts us : List Term) (harglen : args.length = numArgs)
    (hargsShape : TermShapeList sig args) (hlen : bs.length = ts.length)
    (hShape : TermShapeList sig ts)
    (hs : substList sig numArgs args offset bs ts = some us) :
    FODerivable R (jSubstArgs (encNat numArgs) (encTermList sig args) (encNat offset)
      (encNatList bs) (encTermList sig ts) (encTermList sig us)) := by
  cases ts with
  | nil =>
      have hbs : bs = [] := List.length_eq_zero_iff.mp hlen
      have hus : [] = us := by simpa only [substList, Option.some.injEq] using hs
      subst bs us
      exact intro_rSubstargsNil (substRule_in hR (by simp [substRules]))
        (isData_encNat numArgs) (isData_encTermList sig args) (isData_encNat offset)
  | cons t ts =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : bs.length = ts.length := by simpa using hlen
          have hw : TermShape sig t ∧ TermShapeList sig ts := TermShapeList.cons_iff.mp hShape
          by_cases hb : offset + b < wordBound
          · change (if offset + b < wordBound then
                match substGo sig numArgs args (offset + b) t,
                    substList sig numArgs args offset bs ts with
                | some u, some us' => some (u :: us')
                | _, _ => none
              else none) = some us at hs
            rw [if_pos hb] at hs
            cases ht : substGo sig numArgs args (offset + b) t with
            | none => simp [ht] at hs
            | some u =>
                cases hus : substList sig numArgs args offset bs ts with
                | none => simp [ht, hus] at hs
                | some us' =>
                    have he : u :: us' = us := by
                      simpa only [ht, hus, Option.some.injEq] using hs
                    subst us
                    simp only [encNatList_cons, encTermList_cons]
                    exact intro_rSubstargsCons (substRule_in hR (by simp [substRules]))
                      (isData_encNat numArgs) (isData_encTermList sig args)
                      (isData_encNat offset) (isData_encNat b) (isData_encNatList bs)
                      (isData_encTerm sig t) (isData_encTermList sig ts) (isData_encTerm sig u)
                      (isData_encTermList sig us') (isData_encNat (offset + b))
                      (complete_nadd hR offset b) (complete_nword hR (offset + b) hb)
                      (complete_subst_shape hR sig numArgs args (offset + b) t u
                        harglen hargsShape hw.1 ht)
                      (complete_substList_shape hR sig numArgs args offset bs ts us'
                        harglen hargsShape hlen' hw.2 hus)
          · simp [substList, hb] at hs
termination_by sizeOf ts
end

theorem complete_subst {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (offset : Nat) (t result : Term)
    (harglen : args.length = numArgs) (hargsWF : WellFormedList sig args = true)
    (hWF : WellFormed sig t = true)
    (hs : substGo sig numArgs args offset t = some result) :
    FODerivable R (jSubst (encNat numArgs) (encTermList sig args) (encNat offset)
      (encTerm sig t) (encTerm sig result)) :=
  complete_subst_shape hR sig numArgs args offset t result harglen
    (wellFormedList_termShape sig args hargsWF) (wellFormed_termShape sig t hWF) hs

theorem complete_substList {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (offset : Nat)
    (bs : List Nat) (ts us : List Term) (harglen : args.length = numArgs)
    (hargsWF : WellFormedList sig args = true) (hlen : bs.length = ts.length)
    (hWF : WellFormedList sig ts = true)
    (hs : substList sig numArgs args offset bs ts = some us) :
    FODerivable R (jSubstArgs (encNat numArgs) (encTermList sig args) (encNat offset)
      (encNatList bs) (encTermList sig ts) (encTermList sig us)) :=
  complete_substList_shape hR sig numArgs args offset bs ts us harglen
    (wellFormedList_termShape sig args hargsWF) hlen (wellFormedList_termShape sig ts hWF) hs

theorem complete_substGoArgs_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts us : List Term) (harglen : args.length = numArgs)
    (hargsShape : TermShapeList sig args)
    (hlen : ((bindersOf sig s).drop index).length = ts.length)
    (hShape : TermShapeList sig ts)
    (hs : substGoArgs sig numArgs args s offset index ts = some us) :
    FODerivable R (jSubstArgs (encNat numArgs) (encTermList sig args) (encNat offset)
      (encNatList ((bindersOf sig s).drop index)) (encTermList sig ts) (encTermList sig us)) :=
  complete_substList_shape hR sig numArgs args offset ((bindersOf sig s).drop index) ts us
    harglen hargsShape hlen hShape (by simpa only [substGoArgs_eq] using hs)

theorem complete_substGoArgs {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts us : List Term) (harglen : args.length = numArgs)
    (hargsWF : WellFormedList sig args = true)
    (hlen : ((bindersOf sig s).drop index).length = ts.length)
    (hWF : WellFormedList sig ts = true)
    (hs : substGoArgs sig numArgs args s offset index ts = some us) :
    FODerivable R (jSubstArgs (encNat numArgs) (encTermList sig args) (encNat offset)
      (encNatList ((bindersOf sig s).drop index)) (encTermList sig ts) (encTermList sig us)) :=
  complete_substList hR sig numArgs args offset ((bindersOf sig s).drop index) ts us
    harglen hargsWF hlen hWF (by simpa only [substGoArgs_eq] using hs)

theorem complete_substTop_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (t result : Term)
    (harglen : args.length = numArgs) (hargsShape : TermShapeList sig args)
    (hShape : TermShape sig t)
    (hs : substBVars sig numArgs args t 0 = some result) :
    FODerivable R (jSubstTop (encNat numArgs) (encTermList sig args)
      (encTerm sig t) (encTerm sig result)) := by
  by_cases hz : numArgs = 0
  · rw [hz] at hs ⊢
    have he : t = result := by simpa only [substBVars, if_true, Option.some.injEq] using hs
    subst result
    exact intro_rSubsttop0 (substRule_in hR (by simp [substRules]))
      (isData_encTermList sig args) (isData_encTerm sig t)
  · have hpos : 1 ≤ numArgs := by omega
    rw [substBVars, if_neg hz] at hs
    rw [encNat_pos numArgs hpos]
    exact intro_rSubsttopP (substRule_in hR (by simp [substRules]))
      (isData_encPos numArgs) (isData_encTermList sig args) (isData_encTerm sig t)
      (isData_encTerm sig result)
      (by simpa only [encNat_pos numArgs hpos, encNat_zero] using
        complete_subst_shape hR sig numArgs args 0 t result harglen hargsShape hShape hs)

theorem complete_substTop {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (numArgs : Nat) (args : List Term) (t result : Term)
    (harglen : args.length = numArgs) (hargsWF : WellFormedList sig args = true)
    (hWF : WellFormed sig t = true)
    (hs : substBVars sig numArgs args t 0 = some result) :
    FODerivable R (jSubstTop (encNat numArgs) (encTermList sig args)
      (encTerm sig t) (encTerm sig result)) :=
  complete_substTop_shape hR sig numArgs args t result harglen
    (wellFormedList_termShape sig args hargsWF) (wellFormed_termShape sig t hWF) hs

theorem substGo_of_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (t result : Term)
    (harglen : args.length = numArgs)
    (derivation : FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubst (encNat numArgs) (encTermList T.sig args) (encNat offset)
        (encTerm T.sig t) (encTerm T.sig result))) :
    substGo T.sig numArgs args offset t = some result := by
  have hm : SubstM T.sig (encNat numArgs) (encTermList T.sig args) (encNat offset)
      (encTerm T.sig t) (encTerm T.sig result) := meaning_of_foDerivable h derivation
  obtain ⟨u, hu, he⟩ := hm numArgs args offset t rfl rfl harglen rfl rfl
  have heu : result = u := encTerm_inj T.sig he
  simpa only [← heu] using hu

theorem substList_of_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (bs : List Nat) (ts us : List Term)
    (harglen : args.length = numArgs)
    (derivation : FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
        (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us))) :
    substList T.sig numArgs args offset bs ts = some us := by
  have hm : SubstArgsM T.sig (encNat numArgs) (encTermList T.sig args) (encNat offset)
      (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us) :=
    meaning_of_foDerivable h derivation
  obtain ⟨us', hus, he⟩ := hm numArgs args offset bs ts rfl rfl harglen rfl rfl rfl
  have heu : us = us' := encTermList_inj T.sig he
  simpa only [← heu] using hus

theorem substTop_of_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (t result : Term) (harglen : args.length = numArgs)
    (derivation : FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubstTop (encNat numArgs) (encTermList T.sig args)
        (encTerm T.sig t) (encTerm T.sig result))) :
    substBVars T.sig numArgs args t 0 = some result := by
  have hm : SubstTopM T.sig (encNat numArgs) (encTermList T.sig args)
      (encTerm T.sig t) (encTerm T.sig result) := meaning_of_foDerivable h derivation
  obtain ⟨u, hu, he⟩ := hm numArgs args t rfl rfl harglen rfl
  have heu : result = u := encTerm_inj T.sig he
  simpa only [← heu] using hu

theorem substGoArgs_of_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts us : List Term) (harglen : args.length = numArgs)
    (derivation : FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
        (encNatList ((bindersOf T.sig s).drop index)) (encTermList T.sig ts)
        (encTermList T.sig us))) :
    substGoArgs T.sig numArgs args s offset index ts = some us := by
  simpa only [substGoArgs_eq] using
    substList_of_foDerivable h numArgs args offset ((bindersOf T.sig s).drop index)
      ts us harglen derivation

theorem substGo_shape_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (t result : Term)
    (harglen : args.length = numArgs) (hargsShape : TermShapeList T.sig args)
    (hShape : TermShape T.sig t) :
    substGo T.sig numArgs args offset t = some result ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubst (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encTerm T.sig t) (encTerm T.sig result)) :=
  ⟨complete_subst_shape (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig numArgs args
      offset t result harglen hargsShape hShape,
    substGo_of_foDerivable h numArgs args offset t result harglen⟩

theorem substList_shape_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (bs : List Nat) (ts us : List Term)
    (harglen : args.length = numArgs) (hargsShape : TermShapeList T.sig args)
    (hlen : bs.length = ts.length) (hShape : TermShapeList T.sig ts) :
    substList T.sig numArgs args offset bs ts = some us ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us)) :=
  ⟨complete_substList_shape (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig numArgs args
      offset bs ts us harglen hargsShape hlen hShape,
    substList_of_foDerivable h numArgs args offset bs ts us harglen⟩

theorem substGoArgs_shape_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts us : List Term) (harglen : args.length = numArgs)
    (hargsShape : TermShapeList T.sig args)
    (hlen : ((bindersOf T.sig s).drop index).length = ts.length)
    (hShape : TermShapeList T.sig ts) :
    substGoArgs T.sig numArgs args s offset index ts = some us ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList ((bindersOf T.sig s).drop index)) (encTermList T.sig ts)
          (encTermList T.sig us)) :=
  ⟨complete_substGoArgs_shape (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig
      numArgs args s offset index ts us harglen hargsShape hlen hShape,
    substGoArgs_of_foDerivable h numArgs args s offset index ts us harglen⟩

theorem substTop_shape_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (t result : Term) (harglen : args.length = numArgs)
    (hargsShape : TermShapeList T.sig args) (hShape : TermShape T.sig t) :
    substBVars T.sig numArgs args t 0 = some result ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstTop (encNat numArgs) (encTermList T.sig args)
          (encTerm T.sig t) (encTerm T.sig result)) :=
  ⟨complete_substTop_shape (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig numArgs args
      t result harglen hargsShape hShape,
    substTop_of_foDerivable h numArgs args t result harglen⟩

theorem substGo_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (t result : Term)
    (harglen : args.length = numArgs) (hargsWF : WellFormedList T.sig args = true)
    (hWF : WellFormed T.sig t = true) :
    substGo T.sig numArgs args offset t = some result ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubst (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encTerm T.sig t) (encTerm T.sig result)) :=
  ⟨complete_subst (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig numArgs args
      offset t result harglen hargsWF hWF,
    substGo_of_foDerivable h numArgs args offset t result harglen⟩

theorem substList_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (bs : List Nat) (ts us : List Term)
    (harglen : args.length = numArgs) (hargsWF : WellFormedList T.sig args = true)
    (hlen : bs.length = ts.length) (hWF : WellFormedList T.sig ts = true) :
    substList T.sig numArgs args offset bs ts = some us ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us)) :=
  ⟨complete_substList (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig numArgs args
      offset bs ts us harglen hargsWF hlen hWF,
    substList_of_foDerivable h numArgs args offset bs ts us harglen⟩

theorem substGoArgs_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts us : List Term) (harglen : args.length = numArgs)
    (hargsWF : WellFormedList T.sig args = true)
    (hlen : ((bindersOf T.sig s).drop index).length = ts.length)
    (hWF : WellFormedList T.sig ts = true) :
    substGoArgs T.sig numArgs args s offset index ts = some us ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList ((bindersOf T.sig s).drop index)) (encTermList T.sig ts)
          (encTermList T.sig us)) :=
  substGoArgs_shape_iff_foDerivable h numArgs args s offset index ts us harglen
    (wellFormedList_termShape T.sig args hargsWF) hlen
    (wellFormedList_termShape T.sig ts hWF)

theorem substTop_iff_foDerivable {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (t result : Term) (harglen : args.length = numArgs)
    (hargsWF : WellFormedList T.sig args = true) (hWF : WellFormed T.sig t = true) :
    substBVars T.sig numArgs args t 0 = some result ↔
      FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstTop (encNat numArgs) (encTermList T.sig args)
          (encTerm T.sig t) (encTerm T.sig result)) :=
  ⟨complete_substTop (fun _ hr => List.mem_append.mpr (Or.inl hr)) T.sig numArgs args
      t result harglen hargsWF hWF,
    substTop_of_foDerivable h numArgs args t result harglen⟩

/-- A refused operation excludes every presented output pattern on the
canonical input profile; the output need not be assumed to encode a term. -/
theorem substGo_refusal {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (t : Term)
    (harglen : args.length = numArgs) (hrefuse : substGo T.sig numArgs args offset t = none) :
    ∀ result : Pattern, ¬ FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubst (encNat numArgs) (encTermList T.sig args) (encNat offset) (encTerm T.sig t) result) := by
  intro result derivation
  have hm : SubstM T.sig (encNat numArgs) (encTermList T.sig args) (encNat offset)
      (encTerm T.sig t) result := meaning_of_foDerivable h derivation
  obtain ⟨u, hu, _⟩ := hm numArgs args offset t rfl rfl harglen rfl rfl
  rw [hrefuse] at hu
  cases hu

theorem substList_refusal {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (bs : List Nat) (ts : List Term)
    (harglen : args.length = numArgs)
    (hrefuse : substList T.sig numArgs args offset bs ts = none) :
    ∀ result : Pattern, ¬ FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
        (encNatList bs) (encTermList T.sig ts) result) := by
  intro result derivation
  have hm : SubstArgsM T.sig (encNat numArgs) (encTermList T.sig args) (encNat offset)
      (encNatList bs) (encTermList T.sig ts) result := meaning_of_foDerivable h derivation
  obtain ⟨us, hus, _⟩ := hm numArgs args offset bs ts rfl rfl harglen rfl rfl rfl
  rw [hrefuse] at hus
  cases hus

theorem substTop_refusal {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (t : Term) (harglen : args.length = numArgs)
    (hrefuse : substBVars T.sig numArgs args t 0 = none) :
    ∀ result : Pattern, ¬ FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubstTop (encNat numArgs) (encTermList T.sig args) (encTerm T.sig t) result) := by
  intro result derivation
  have hm : SubstTopM T.sig (encNat numArgs) (encTermList T.sig args)
      (encTerm T.sig t) result := meaning_of_foDerivable h derivation
  obtain ⟨u, hu, _⟩ := hm numArgs args t rfl rfl harglen rfl
  rw [hrefuse] at hu
  cases hu

theorem substGoArgs_refusal {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts : List Term) (harglen : args.length = numArgs)
    (hrefuse : substGoArgs T.sig numArgs args s offset index ts = none) :
    ∀ result : Pattern, ¬ FODerivable (kernelRules ++ theoryRules T allocation)
      (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
        (encNatList ((bindersOf T.sig s).drop index)) (encTermList T.sig ts) result) :=
  substList_refusal h numArgs args offset ((bindersOf T.sig s).drop index) ts harglen
    (by simpa only [substGoArgs_eq] using hrefuse)

theorem substGo_shape_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (t : Term)
    (harglen : args.length = numArgs) (hargsShape : TermShapeList T.sig args)
    (hShape : TermShape T.sig t) :
    substGo T.sig numArgs args offset t = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubst (encNat numArgs) (encTermList T.sig args) (encNat offset) (encTerm T.sig t) result) := by
  constructor
  · rintro hrefuse ⟨result, derivation⟩
    exact substGo_refusal h numArgs args offset t harglen hrefuse result derivation
  · intro hnone
    cases hs : substGo T.sig numArgs args offset t with
    | none => rfl
    | some result =>
        exact False.elim (hnone ⟨encTerm T.sig result,
          (substGo_shape_iff_foDerivable h numArgs args offset t result
            harglen hargsShape hShape).mp hs⟩)

theorem substList_shape_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (bs : List Nat) (ts : List Term)
    (harglen : args.length = numArgs) (hargsShape : TermShapeList T.sig args)
    (hlen : bs.length = ts.length) (hShape : TermShapeList T.sig ts) :
    substList T.sig numArgs args offset bs ts = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList bs) (encTermList T.sig ts) result) := by
  constructor
  · rintro hrefuse ⟨result, derivation⟩
    exact substList_refusal h numArgs args offset bs ts harglen hrefuse result derivation
  · intro hnone
    cases hs : substList T.sig numArgs args offset bs ts with
    | none => rfl
    | some us =>
        exact False.elim (hnone ⟨encTermList T.sig us,
          (substList_shape_iff_foDerivable h numArgs args offset bs ts us
            harglen hargsShape hlen hShape).mp hs⟩)

theorem substGoArgs_shape_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts : List Term) (harglen : args.length = numArgs)
    (hargsShape : TermShapeList T.sig args)
    (hlen : ((bindersOf T.sig s).drop index).length = ts.length)
    (hShape : TermShapeList T.sig ts) :
    substGoArgs T.sig numArgs args s offset index ts = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList ((bindersOf T.sig s).drop index)) (encTermList T.sig ts) result) := by
  simpa only [substGoArgs_eq] using
    substList_shape_refusal_iff h numArgs args offset ((bindersOf T.sig s).drop index) ts
      harglen hargsShape hlen hShape

theorem substTop_shape_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (t : Term) (harglen : args.length = numArgs)
    (hargsShape : TermShapeList T.sig args) (hShape : TermShape T.sig t) :
    substBVars T.sig numArgs args t 0 = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstTop (encNat numArgs) (encTermList T.sig args) (encTerm T.sig t) result) := by
  constructor
  · rintro hrefuse ⟨result, derivation⟩
    exact substTop_refusal h numArgs args t harglen hrefuse result derivation
  · intro hnone
    cases hs : substBVars T.sig numArgs args t 0 with
    | none => rfl
    | some result =>
        exact False.elim (hnone ⟨encTerm T.sig result,
          (substTop_shape_iff_foDerivable h numArgs args t result harglen hargsShape hShape).mp hs⟩)

theorem substGo_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (t : Term)
    (harglen : args.length = numArgs) (hargsWF : WellFormedList T.sig args = true)
    (hWF : WellFormed T.sig t = true) :
    substGo T.sig numArgs args offset t = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubst (encNat numArgs) (encTermList T.sig args) (encNat offset) (encTerm T.sig t) result) := by
  constructor
  · rintro hrefuse ⟨result, derivation⟩
    exact substGo_refusal h numArgs args offset t harglen hrefuse result derivation
  · intro hnone
    cases hs : substGo T.sig numArgs args offset t with
    | none => rfl
    | some result =>
        exact False.elim (hnone ⟨encTerm T.sig result,
          (substGo_iff_foDerivable h numArgs args offset t result harglen hargsWF hWF).mp hs⟩)

theorem substList_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (offset : Nat) (bs : List Nat) (ts : List Term)
    (harglen : args.length = numArgs) (hargsWF : WellFormedList T.sig args = true)
    (hlen : bs.length = ts.length) (hWF : WellFormedList T.sig ts = true) :
    substList T.sig numArgs args offset bs ts = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList bs) (encTermList T.sig ts) result) := by
  constructor
  · rintro hrefuse ⟨result, derivation⟩
    exact substList_refusal h numArgs args offset bs ts harglen hrefuse result derivation
  · intro hnone
    cases hs : substList T.sig numArgs args offset bs ts with
    | none => rfl
    | some us =>
        exact False.elim (hnone ⟨encTermList T.sig us,
          (substList_iff_foDerivable h numArgs args offset bs ts us harglen hargsWF hlen hWF).mp hs⟩)

theorem substGoArgs_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (s : SymId) (offset index : Nat)
    (ts : List Term) (harglen : args.length = numArgs)
    (hargsWF : WellFormedList T.sig args = true)
    (hlen : ((bindersOf T.sig s).drop index).length = ts.length)
    (hWF : WellFormedList T.sig ts = true) :
    substGoArgs T.sig numArgs args s offset index ts = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstArgs (encNat numArgs) (encTermList T.sig args) (encNat offset)
          (encNatList ((bindersOf T.sig s).drop index)) (encTermList T.sig ts) result) :=
  substGoArgs_shape_refusal_iff h numArgs args s offset index ts harglen
    (wellFormedList_termShape T.sig args hargsWF) hlen
    (wellFormedList_termShape T.sig ts hWF)

theorem substTop_refusal_iff {T : Theory} {allocation : Nat} (h : Hosted T allocation)
    (numArgs : Nat) (args : List Term) (t : Term) (harglen : args.length = numArgs)
    (hargsWF : WellFormedList T.sig args = true) (hWF : WellFormed T.sig t = true) :
    substBVars T.sig numArgs args t 0 = none ↔
      ¬ ∃ result : Pattern, FODerivable (kernelRules ++ theoryRules T allocation)
        (jSubstTop (encNat numArgs) (encTermList T.sig args) (encTerm T.sig t) result) := by
  constructor
  · rintro hrefuse ⟨result, derivation⟩
    exact substTop_refusal h numArgs args t harglen hrefuse result derivation
  · intro hnone
    cases hs : substBVars T.sig numArgs args t 0 with
    | none => rfl
    | some result =>
        exact False.elim (hnone ⟨encTerm T.sig result,
          (substTop_iff_foDerivable h numArgs args t result harglen hargsWF hWF).mp hs⟩)

end Mettapedia.Languages.VibeITP.Presentation
