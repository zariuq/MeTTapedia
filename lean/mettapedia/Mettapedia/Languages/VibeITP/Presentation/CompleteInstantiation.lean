import Mettapedia.Languages.VibeITP.Presentation.CompleteSubstitution
import Mettapedia.Languages.VibeITP.Presentation.OperationsWf

/-!
# Constructive second-order instantiation

Witnesses follow free-variable traversal, retain the identity of other heads,
shift the replacement under crossed binders, and substitute the recursively
instantiated arguments in the specified reverse order. The input profile uses
the actual signature and arities; word guards remain in the executed operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem instRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ instRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

private theorem complete_instOther {R : List FORule} (hR : kernelRules ⊆ R)
    (fid idv : Nat) (hne : fid ≠ idv) {fbs v n o bs ts d us e g : Pattern}
    (hfbs : IsData fbs) (hv : IsData v) (hn : IsData n) (ho : IsData o)
    (hbs : IsData bs) (hts : IsData ts) (hd : IsData d) (hus : IsData us)
    (he : IsData e) (hg : IsData g)
    (hargs : FODerivable R (jInstArgs (cSym (encNat fid) cKFvar fbs) v n o bs ts us))
    (hann : FODerivable R (jAnnArgs bs us e g)) :
    FODerivable R (jInst (cSym (encNat fid) cKFvar fbs) v n o
      (cApp (cSym (encNat idv) cKFvar bs) ts (cAnn d cTrue))
      (cApp (cSym (encNat idv) cKFvar bs) us (cAnn e cTrue))) := by
  by_cases hlt : idv < fid
  · exact intro_rInstOtherLt (instRule_in hR (by simp [instRules]))
      (isData_encNat fid) hfbs hv hn ho (isData_encNat idv) hbs hts hd hus he hg
      (complete_nlt hR idv fid hlt) hargs hann
  · exact intro_rInstOtherGt (instRule_in hR (by simp [instRules]))
      (isData_encNat fid) hfbs hv hn ho (isData_encNat idv) hbs hts hd hus he hg
      (complete_nlt hR fid idv (by omega)) hargs hann

mutual
theorem complete_inst_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (offset : Nat)
    (t result : Term) (hF : IsFvarOf sig F arity) (hvalue : TermShape sig value)
    (hShape : TermShape sig t) (hs : instGo sig F arity value offset t = some result) :
    FODerivable R (jInst (encSym sig F) (encTerm sig value) (encNat arity) (encNat offset)
      (encTerm sig t) (encTerm sig result)) := by
  by_cases hfv : hasFvar sig t = false
  · have he : t = result :=
      Option.some.inj ((instGo_nofv sig F arity value offset t hfv).symm.trans hs)
    subst result
    exact intro_rInstNofv (instRule_in hR (by simp [instRules]))
      (isData_encSym sig F) (isData_encTerm sig value) (isData_encNat arity)
      (isData_encNat offset) (isData_encTerm sig t)
      (by simpa [hfv, encBool] using complete_hasFvar hR sig t)
  · cases t with
    | bvar b => simp [hasFvar] at hfv
    | lit bytes => simp [hasFvar] at hfv
    | app s args =>
        obtain ⟨info, hsig, harity, hargsShape⟩ := TermShape.app_iff.mp hShape
        have hlen : (bindersOf sig s).length = args.length := by
          simpa only [bindersOf, hsig, SymInfo.arity] using harity.symm
        have htrue : hasFvar sig (.app s args) = true := by
          cases hf : hasFvar sig (.app s args) <;> simp_all
        have hinput : (isFvarSym sig s || hasFvarList sig args) = true := htrue
        have hencF : encSym sig F =
            cSym (encNat (symNumber F)) cKFvar (encNatList (bindersOf sig F)) := by
          rw [encSym_eq, hF.2.1]
          rfl
        simp only [instGo, if_neg hfv, instArgs_eq, List.drop_zero] at hs
        cases hus : instList sig F arity value offset (bindersOf sig s) args with
        | none => simp [hus] at hs
        | some us =>
            have hlen' : (bindersOf sig s).length = us.length :=
              hlen.trans (instList_length sig F arity value offset _ _ _ hus).symm
            have hargs := complete_instList_shape hR sig F arity value offset
              (bindersOf sig s) args us hF hvalue hlen hargsShape hus
            by_cases hhit : s = F
            · subst s
              simp only [hus] at hs
              cases hw : shift sig offset arity value with
              | none => simp [hw] at hs
              | some w =>
                  have hsubst : substBVars sig arity us w 0 = some result := by
                    simpa [hw] using hs
                  have husShape := instList_termShape sig F arity value offset
                    (bindersOf sig F) args us hvalue hF hargsShape hus
                  have hwShape := shift_termShape sig offset arity value w hvalue hw
                  have hflen : (bindersOf sig F).length = arity := by
                    simpa only [symArity_eq] using hF.2.2
                  have huslen : us.length = arity := hlen'.symm.trans hflen
                  rw [encTerm_app' sig F args, hinput]
                  simp only [hencF]
                  exact intro_rInstHit (instRule_in hR (by simp [instRules]))
                    (isData_encNat (symNumber F)) (isData_encNatList (bindersOf sig F))
                    (isData_encTerm sig value) (isData_encNat arity) (isData_encNat offset)
                    (isData_encTermList sig args)
                    (isData_encNat (depthBinders sig (bindersOf sig F) args))
                    (isData_encTermList sig us) (isData_encTerm sig w)
                    (isData_encTerm sig result)
                    (by simpa only [hencF] using hargs)
                    (complete_shift_shape hR sig offset arity value w hvalue hw)
                    (complete_substTop_shape hR sig arity us w result huslen
                      husShape hwShape hsubst)
            · have he : Term.app s us = result := by
                simpa only [hus, if_neg hhit, Option.some.injEq] using hs
              subst result
              have hann := complete_annArgs hR sig (bindersOf sig s) us hlen'
              rw [encTerm_app' sig s args, encTerm_app' sig s us, hinput, encSym_eq sig s]
              cases hkind : kindOf sig s with
              | constant =>
                  rw [isFvarSym_eq sig s, hkind]
                  exact intro_rInstConst (instRule_in hR (by simp [instRules]))
                    (isData_encSym sig F) (isData_encTerm sig value) (isData_encNat arity)
                    (isData_encNat offset) (isData_encNat (symNumber s))
                    (isData_encNatList (bindersOf sig s)) (isData_encTermList sig args)
                    (isData_encNat (depthBinders sig (bindersOf sig s) args))
                    (isData_encTermList sig us)
                    (isData_encNat (depthBinders sig (bindersOf sig s) us))
                    (isData_encBool (hasFvarList sig us)) hargs hann
              | fvar =>
                  rw [isFvarSym_eq sig s, hkind]
                  simp only [hencF]
                  have hne : symNumber F ≠ symNumber s := by
                    intro he
                    exact hhit (symNumber_inj he.symm)
                  exact complete_instOther hR (symNumber F) (symNumber s) hne
                    (isData_encNatList (bindersOf sig F)) (isData_encTerm sig value)
                    (isData_encNat arity) (isData_encNat offset)
                    (isData_encNatList (bindersOf sig s)) (isData_encTermList sig args)
                    (isData_encNat (depthBinders sig (bindersOf sig s) args))
                    (isData_encTermList sig us)
                    (isData_encNat (depthBinders sig (bindersOf sig s) us))
                    (isData_encBool (hasFvarList sig us))
                    (by simpa only [hencF] using hargs) hann
termination_by sizeOf t

theorem complete_instList_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (offset : Nat)
    (bs : List Nat) (ts us : List Term) (hF : IsFvarOf sig F arity)
    (hvalue : TermShape sig value) (hlen : bs.length = ts.length)
    (hShape : TermShapeList sig ts)
    (hs : instList sig F arity value offset bs ts = some us) :
    FODerivable R (jInstArgs (encSym sig F) (encTerm sig value) (encNat arity)
      (encNat offset) (encNatList bs) (encTermList sig ts) (encTermList sig us)) := by
  cases ts with
  | nil =>
      have hbs : bs = [] := List.length_eq_zero_iff.mp hlen
      have hus : [] = us := by simpa only [instList, Option.some.injEq] using hs
      subst bs us
      exact intro_rInstargsNil (instRule_in hR (by simp [instRules]))
        (isData_encSym sig F) (isData_encTerm sig value)
        (isData_encNat arity) (isData_encNat offset)
  | cons t ts =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : bs.length = ts.length := by simpa using hlen
          obtain ⟨ht, hts⟩ := TermShapeList.cons_iff.mp hShape
          change (if offset + b < wordBound then
              match instGo sig F arity value (offset + b) t,
                  instList sig F arity value offset bs ts with
              | some u, some us' => some (u :: us')
              | _, _ => none
            else none) = some us at hs
          by_cases hb : offset + b < wordBound
          · rw [if_pos hb] at hs
            cases hterm : instGo sig F arity value (offset + b) t with
            | none => simp [hterm] at hs
            | some u =>
                cases hus : instList sig F arity value offset bs ts with
                | none => simp [hterm, hus] at hs
                | some us' =>
                    have he : u :: us' = us := by
                      simpa only [hterm, hus, Option.some.injEq] using hs
                    subst us
                    simp only [encNatList_cons, encTermList_cons]
                    exact intro_rInstargsCons (instRule_in hR (by simp [instRules]))
                      (isData_encSym sig F) (isData_encTerm sig value)
                      (isData_encNat arity) (isData_encNat offset) (isData_encNat b)
                      (isData_encNatList bs) (isData_encTerm sig t)
                      (isData_encTermList sig ts) (isData_encTerm sig u)
                      (isData_encTermList sig us') (isData_encNat (offset + b))
                      (complete_nadd hR offset b) (complete_nword hR (offset + b) hb)
                      (complete_inst_shape hR sig F arity value (offset + b) t u hF hvalue ht hterm)
                      (complete_instList_shape hR sig F arity value offset bs ts us'
                        hF hvalue hlen' hts hus)
          · rw [if_neg hb] at hs; cases hs
termination_by sizeOf ts
end

theorem complete_inst {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (offset : Nat)
    (t result : Term) (hF : IsFvarOf sig F arity) (hvalue : WellFormed sig value = true)
    (hWF : WellFormed sig t = true) (hs : instGo sig F arity value offset t = some result) :
    FODerivable R (jInst (encSym sig F) (encTerm sig value) (encNat arity) (encNat offset)
      (encTerm sig t) (encTerm sig result)) :=
  complete_inst_shape hR sig F arity value offset t result hF
    (wellFormed_termShape sig value hvalue) (wellFormed_termShape sig t hWF) hs

theorem complete_instArgs_shape {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (s : SymId) (offset index : Nat)
    (ts us : List Term) (hF : IsFvarOf sig F arity) (hvalue : TermShape sig value)
    (hlen : ((bindersOf sig s).drop index).length = ts.length) (ht : TermShapeList sig ts)
    (hs : instArgs sig F arity value s offset index ts = some us) :
    FODerivable R (jInstArgs (encSym sig F) (encTerm sig value) (encNat arity)
      (encNat offset) (encNatList ((bindersOf sig s).drop index))
      (encTermList sig ts) (encTermList sig us)) :=
  complete_instList_shape hR sig F arity value offset ((bindersOf sig s).drop index)
    ts us hF hvalue hlen ht (by simpa only [instArgs_eq] using hs)

theorem instGo_of_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (offset : Nat) (t result : Term)
    (hF : IsFvarOf T.sig F arity)
    (derivation : FODerivable (kernelRules ++ theoryRules T n)
      (jInst (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
        (encTerm T.sig t) (encTerm T.sig result))) :
    instGo T.sig F arity value offset t = some result := by
  have hm : InstM T.sig (encSym T.sig F) (encTerm T.sig value) (encNat arity)
      (encNat offset) (encTerm T.sig t) (encTerm T.sig result) := meaning_of_foDerivable h derivation
  obtain ⟨u, hu, he⟩ := hm F arity value offset t hF rfl rfl rfl rfl rfl
  have heu : result = u := encTerm_inj T.sig he
  simpa only [← heu] using hu

theorem instGo_iff_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (offset : Nat) (t result : Term)
    (hF : IsFvarOf T.sig F arity) (hvalue : TermShape T.sig value) (ht : TermShape T.sig t) :
    instGo T.sig F arity value offset t = some result ↔
      FODerivable (kernelRules ++ theoryRules T n)
        (jInst (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
          (encTerm T.sig t) (encTerm T.sig result)) :=
  ⟨complete_inst_shape (fun _ hr => List.mem_append.mpr (Or.inl hr))
      T.sig F arity value offset t result hF hvalue ht,
    instGo_of_foDerivable h F arity value offset t result hF⟩

theorem instList_of_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (offset : Nat)
    (bs : List Nat) (ts us : List Term) (hF : IsFvarOf T.sig F arity)
    (derivation : FODerivable (kernelRules ++ theoryRules T n)
      (jInstArgs (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
        (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us))) :
    instList T.sig F arity value offset bs ts = some us := by
  have hm : InstArgsM T.sig (encSym T.sig F) (encTerm T.sig value) (encNat arity)
      (encNat offset) (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us) :=
    meaning_of_foDerivable h derivation
  obtain ⟨us', hus, he⟩ := hm F arity value offset bs ts hF rfl rfl rfl rfl rfl rfl
  have heu : us = us' := encTermList_inj T.sig he.1
  simpa only [← heu] using hus

theorem instList_iff_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (offset : Nat)
    (bs : List Nat) (ts us : List Term) (hF : IsFvarOf T.sig F arity)
    (hvalue : TermShape T.sig value) (hlen : bs.length = ts.length)
    (ht : TermShapeList T.sig ts) :
    instList T.sig F arity value offset bs ts = some us ↔
      FODerivable (kernelRules ++ theoryRules T n)
        (jInstArgs (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
          (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us)) :=
  ⟨complete_instList_shape (fun _ hr => List.mem_append.mpr (Or.inl hr))
      T.sig F arity value offset bs ts us hF hvalue hlen ht,
    instList_of_foDerivable h F arity value offset bs ts us hF⟩

theorem instArgs_iff_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (s : SymId) (offset index : Nat)
    (ts us : List Term) (hF : IsFvarOf T.sig F arity) (hvalue : TermShape T.sig value)
    (hlen : ((bindersOf T.sig s).drop index).length = ts.length) (ht : TermShapeList T.sig ts) :
    instArgs T.sig F arity value s offset index ts = some us ↔
      FODerivable (kernelRules ++ theoryRules T n)
        (jInstArgs (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
          (encNatList ((bindersOf T.sig s).drop index))
          (encTermList T.sig ts) (encTermList T.sig us)) := by
  rw [instArgs_eq]
  exact instList_iff_foDerivable h F arity value offset _ ts us hF hvalue hlen ht

theorem instGo_refusal_iff {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (offset : Nat) (t : Term)
    (hF : IsFvarOf T.sig F arity) (hvalue : TermShape T.sig value) (ht : TermShape T.sig t) :
    instGo T.sig F arity value offset t = none ↔
      ∀ result, ¬ FODerivable (kernelRules ++ theoryRules T n)
        (jInst (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
          (encTerm T.sig t) (encTerm T.sig result)) := by
  constructor
  · intro hrefuse result derivation
    have hs := instGo_of_foDerivable h F arity value offset t result hF derivation
    rw [hrefuse] at hs
    cases hs
  · intro hrefuse
    cases hs : instGo T.sig F arity value offset t with
    | none => rfl
    | some result =>
        exact False.elim (hrefuse result
          ((instGo_iff_foDerivable h F arity value offset t result hF hvalue ht).mp hs))

theorem instList_refusal_iff {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (offset : Nat) (bs : List Nat) (ts : List Term)
    (hF : IsFvarOf T.sig F arity) (hvalue : TermShape T.sig value)
    (hlen : bs.length = ts.length) (ht : TermShapeList T.sig ts) :
    instList T.sig F arity value offset bs ts = none ↔
      ∀ us, ¬ FODerivable (kernelRules ++ theoryRules T n)
        (jInstArgs (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
          (encNatList bs) (encTermList T.sig ts) (encTermList T.sig us)) := by
  constructor
  · intro hrefuse us derivation
    have hs := instList_of_foDerivable h F arity value offset bs ts us hF derivation
    rw [hrefuse] at hs
    cases hs
  · intro hrefuse
    cases hs : instList T.sig F arity value offset bs ts with
    | none => rfl
    | some us =>
        exact False.elim (hrefuse us
          ((instList_iff_foDerivable h F arity value offset bs ts us hF hvalue hlen ht).mp hs))

theorem instArgs_refusal_iff {T : Theory} {n : Nat} (h : Hosted T n)
    (F : SymId) (arity : Nat) (value : Term) (s : SymId) (offset index : Nat) (ts : List Term)
    (hF : IsFvarOf T.sig F arity) (hvalue : TermShape T.sig value)
    (hlen : ((bindersOf T.sig s).drop index).length = ts.length) (ht : TermShapeList T.sig ts) :
    instArgs T.sig F arity value s offset index ts = none ↔
      ∀ us, ¬ FODerivable (kernelRules ++ theoryRules T n)
        (jInstArgs (encSym T.sig F) (encTerm T.sig value) (encNat arity) (encNat offset)
          (encNatList ((bindersOf T.sig s).drop index))
          (encTermList T.sig ts) (encTermList T.sig us)) := by
  rw [instArgs_eq]
  exact instList_refusal_iff h F arity value offset _ ts hF hvalue hlen ht

/-- Construct the presented theorem-instantiation rule from the actual
specification operation, including declaration, value depth and result closure. -/
theorem complete_instantiateStatement {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    (F : SymId) (value φ ψ : Term) (hvalue : WellFormed T.sig value = true)
    (hφ : TermShape T.sig φ)
    (hs : instantiateStatement T.sig F value φ = some ψ)
    (hderivation : FODerivable R (jThm (encTerm T.sig φ))) :
    FODerivable R (jThm (encTerm T.sig ψ)) := by
  cases hsig : T.sig F with
  | none => simp [instantiateStatement, hsig] at hs
  | some info =>
      by_cases hgood : info.kind = .fvar ∧ depth T.sig value ≤ info.arity
      · simp only [instantiateStatement, hsig, if_pos hgood] at hs
        cases hinst : instGo T.sig F info.arity value 0 φ with
        | none => simp [hinst] at hs
        | some result =>
            by_cases hclosed : depth T.sig result = 0
            · have he : result = ψ := by
                simpa only [hinst, if_pos hclosed, Option.some.injEq] using hs
              subst ψ
              have hF : IsFvarOf T.sig F info.arity := by
                exact ⟨by simp [hsig], by simp [kindOf, hsig, hgood.1],
                  by simp [symArity, hsig]⟩
              have hdecl := complete_symDecl hR hT h F (by simp [hsig])
              have hlength := complete_len hR (info.binders.map encNat)
                (by simp [isData_encNat])
              have hoperation := complete_inst_shape hR T.sig F info.arity value 0 φ result hF
                (wellFormed_termShape T.sig value hvalue) hφ hinst
              exact intro_rInst (hR (by simp [kernelRules, theoremRules]))
                (isData_encTerm T.sig φ) (isData_encNat (symNumber F))
                (isData_encNatList info.binders) (isData_encNat info.arity)
                (isData_encTerm T.sig value) (isData_encNat (depth T.sig value))
                (isData_encTerm T.sig result) hderivation
                (by simpa only [encSym, hsig, hgood.1, encKind] using hdecl)
                (by simpa only [encNatList, List.length_map, SymInfo.arity] using hlength)
                (complete_wf hR hT h value hvalue) (complete_depth hR T.sig value)
                (complete_nle hR (depth T.sig value) info.arity hgood.2)
                (by simpa only [encSym, hsig, hgood.1, encKind, encNat_zero] using hoperation)
                (by simpa only [hclosed, encNat_zero] using complete_depth hR T.sig result)
            · simp [hinst, hclosed] at hs
      · simp [instantiateStatement, hsig, hgood] at hs

end Mettapedia.Languages.VibeITP.Presentation
