import Mettapedia.Languages.VibeITP.Presentation.CompleteLists
import Mettapedia.Languages.VibeITP.Presentation.SoundAdmissions

/-!
# Constructive term-formation and annotation witnesses

The witnesses use the declared signature and the real cached term annotations.
Formation checks the actual word bounds, argument counts and recursively
formed arguments. Annotation witnesses also apply to terms without a formation
assumption, when their explicit binder lists have the matching length.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem termRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ termRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

theorem complete_symDecl {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    (s : SymId) (hs : (T.sig s).isSome = true) :
    FODerivable R (jSymDecl (encSym T.sig s)) := by
  cases s with
  | builtin b =>
      rw [encSym_builtin h.builtin b]
      apply intro_closedRule ("vibe-builtin-" ++ toString b.slot)
        (IsData.app1 _ (isData_patBuiltinSym b))
      apply hR
      have hb : b ∈ Builtin.all := by cases b <;> simp [Builtin.all]
      have hr : mkRule ("vibe-builtin-" ++ toString b.slot) [] []
          (jSymDecl (patBuiltinSym b)) ∈ builtinRules :=
        List.mem_map.mpr ⟨b, hb, rfl⟩
      exact List.mem_append.mpr (Or.inr hr)
  | fresh i =>
      apply intro_symbolRule T.sig i
      apply hT
      have hi : i ∈ List.range n := List.mem_range.mpr ((h.fresh i).mp hs)
      have hr : symbolRule T.sig i ∈ (List.range n).map (symbolRule T.sig) :=
        List.mem_map.mpr ⟨i, hi, rfl⟩
      simp only [theoryRules, List.mem_append]
      exact Or.inl (Or.inl hr)

theorem complete_depth {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (t : Term) :
    FODerivable R (jDepth (encTerm sig t) (encNat (depth sig t))) := by
  cases t with
  | bvar i =>
      exact intro_rDepthBvar (termRule_in hR (by simp [termRules]))
        (isData_encNat i) (isData_encNat (i + 1)) (complete_nadd hR i 1)
  | lit bs =>
      exact intro_rDepthLit (termRule_in hR (by simp [termRules])) (isData_encBytes bs)
  | app s args =>
      exact intro_rDepthApp (termRule_in hR (by simp [termRules]))
        (isData_encSym sig s) (isData_encTermList sig args)
        (isData_encNat (depthArgs sig s 0 args))
        (isData_encBool (isFvarSym sig s || hasFvarList sig args))

theorem complete_hasFvar {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (t : Term) :
    FODerivable R (jHasFv (encTerm sig t) (encBool (hasFvar sig t))) := by
  cases t with
  | bvar i =>
      exact intro_rHasfvBvar (termRule_in hR (by simp [termRules])) (isData_encNat i)
  | lit bs =>
      exact intro_rHasfvLit (termRule_in hR (by simp [termRules])) (isData_encBytes bs)
  | app s args =>
      exact intro_rHasfvApp (termRule_in hR (by simp [termRules]))
        (isData_encSym sig s) (isData_encTermList sig args)
        (isData_encNat (depthArgs sig s 0 args))
        (isData_encBool (isFvarSym sig s || hasFvarList sig args))

theorem complete_kindFv {R : List FORule} (hR : kernelRules ⊆ R)
    (kind : SymKind) (f : Bool) :
    FODerivable R (jKindFv (encKind kind) (encBool f)
      (encBool ((kind == .fvar) || f))) := by
  cases kind with
  | constant =>
      change FODerivable R (jKindFv cKConst (encBool f) (encBool f))
      exact intro_rKindfvConst (termRule_in hR (by simp [termRules])) (isData_encBool f)
  | fvar =>
      change FODerivable R (jKindFv cKFvar (encBool f) cTrue)
      exact intro_rKindfvFvar (termRule_in hR (by simp [termRules])) (isData_encBool f)

theorem complete_annArgs {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (bs : List Nat) (ts : List Term) (hlen : bs.length = ts.length) :
    FODerivable R (jAnnArgs (encNatList bs) (encTermList sig ts)
      (encNat (depthBinders sig bs ts)) (encBool (hasFvarList sig ts))) := by
  induction ts generalizing bs with
  | nil =>
      have hbs : bs = [] := List.length_eq_zero_iff.mp hlen
      subst bs
      exact intro_rAnnargsNil (termRule_in hR (by simp [termRules]))
  | cons t ts ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : bs.length = ts.length := by simpa using hlen
          simp only [encNatList_cons, encTermList_cons, depthBinders, List.headD_cons,
            List.tail_cons, hasFvarList_cons]
          exact intro_rAnnargsCons (termRule_in hR (by simp [termRules]))
            (isData_encNat b) (isData_encNatList bs) (isData_encTerm sig t)
            (isData_encTermList sig ts) (isData_encNat (depth sig t))
            (isData_encNat (depth sig t - b)) (isData_encNat (depthBinders sig bs ts))
            (isData_encBool (hasFvarList sig ts)) (isData_encBool (hasFvar sig t))
            (isData_encNat (max (depth sig t - b) (depthBinders sig bs ts)))
            (isData_encBool (hasFvar sig t || hasFvarList sig ts))
            (complete_depth hR sig t) (complete_nmonus hR (depth sig t) b)
            (complete_hasFvar hR sig t) (ih bs hlen')
            (complete_nmax hR (depth sig t - b) (depthBinders sig bs ts))
            (complete_bor hR (hasFvar sig t) (hasFvarList sig ts))

theorem complete_wf_lit {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (bs : List UInt8) (hbs : bs.length + 8 < wordBound) :
    FODerivable R (jWf (encTerm sig (.lit bs))) :=
  intro_rWfLit (termRule_in hR (by simp [termRules]))
    (isData_encBytes bs) (isData_encNat bs.length) (isData_encNat (bs.length + 8))
    (complete_bytes hR bs) (complete_len_bytes hR bs) (complete_nadd hR bs.length 8)
    (complete_nword hR (bs.length + 8) hbs)

mutual
theorem complete_wf {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    (t : Term) (ht : WellFormed T.sig t = true) :
    FODerivable R (jWf (encTerm T.sig t)) := by
  cases t with
  | bvar i =>
      have hi : i + 1 < wordBound := by simpa only [WellFormed, decide_eq_true_eq] using ht
      exact intro_rWfBvar (termRule_in hR (by simp [termRules]))
        (isData_encNat i) (isData_encNat (i + 1)) (complete_nadd hR i 1)
        (complete_nword hR (i + 1) hi)
  | lit bs =>
      exact complete_wf_lit hR T.sig bs (by simpa only [WellFormed, decide_eq_true_eq] using ht)
  | app s args =>
      cases hs : T.sig s with
      | none => simp [WellFormed, hs] at ht
      | some info =>
          have hw : args.length = info.arity ∧ WellFormedList T.sig args = true := by
            simpa only [WellFormed, hs, Bool.and_eq_true, decide_eq_true_eq] using ht
          have hlen : (bindersOf T.sig s).length = args.length := by
            simpa only [bindersOf, hs, SymInfo.arity] using hw.1.symm
          rw [encTerm_app', encSym_eq, isFvarSym_eq]
          exact intro_rWfApp (termRule_in hR (by simp [termRules]))
            (isData_encNat (symNumber s)) (isData_encKind (kindOf T.sig s))
            (isData_encNatList (bindersOf T.sig s)) (isData_encTermList T.sig args)
            (isData_encNat (depthBinders T.sig (bindersOf T.sig s) args))
            (isData_encBool (hasFvarList T.sig args))
            (isData_encBool ((kindOf T.sig s == .fvar) || hasFvarList T.sig args))
            (by simpa only [encSym_eq] using complete_symDecl hR hT h s (by simp [hs]))
            (complete_wfArgs hR hT h (bindersOf T.sig s) args hlen hw.2)
            (complete_kindFv hR (kindOf T.sig s) (hasFvarList T.sig args))
termination_by sizeOf t

theorem complete_wfArgs {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    (bs : List Nat) (ts : List Term) (hlen : bs.length = ts.length)
    (ht : WellFormedList T.sig ts = true) :
    FODerivable R (jWfArgs (encNatList bs) (encTermList T.sig ts)
      (encNat (depthBinders T.sig bs ts)) (encBool (hasFvarList T.sig ts))) := by
  cases ts with
  | nil =>
      have hbs : bs = [] := List.length_eq_zero_iff.mp hlen
      subst bs
      exact intro_rWfargsNil (termRule_in hR (by simp [termRules]))
  | cons t ts =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : bs.length = ts.length := by simpa using hlen
          have hw : WellFormed T.sig t = true ∧ WellFormedList T.sig ts = true := by
            simpa only [WellFormedList, Bool.and_eq_true] using ht
          simp only [encNatList_cons, encTermList_cons, depthBinders, List.headD_cons,
            List.tail_cons, hasFvarList_cons]
          exact intro_rWfargsCons (termRule_in hR (by simp [termRules]))
            (isData_encNat b) (isData_encNatList bs) (isData_encTerm T.sig t)
            (isData_encTermList T.sig ts) (isData_encNat (depth T.sig t))
            (isData_encNat (depth T.sig t - b)) (isData_encNat (depthBinders T.sig bs ts))
            (isData_encBool (hasFvarList T.sig ts)) (isData_encBool (hasFvar T.sig t))
            (isData_encNat (max (depth T.sig t - b) (depthBinders T.sig bs ts)))
            (isData_encBool (hasFvar T.sig t || hasFvarList T.sig ts))
            (complete_wf hR hT h t hw.1) (complete_depth hR T.sig t)
            (complete_nmonus hR (depth T.sig t) b) (complete_hasFvar hR T.sig t)
            (complete_wfArgs hR hT h bs ts hlen' hw.2)
            (complete_nmax hR (depth T.sig t - b) (depthBinders T.sig bs ts))
            (complete_bor hR (hasFvar T.sig t) (hasFvarList T.sig ts))
termination_by sizeOf ts
end

end Mettapedia.Languages.VibeITP.Presentation
