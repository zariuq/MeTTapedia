import Mettapedia.Languages.VibeITP.Presentation.SoundTheorems

/-!
# Vibe-ITP presentation: soundness of the definition rules

The rules checking a definition by a closed body preserve `Meaning`: the
parameter arities, the hint bounds, the consumption of hints by the free
variable occurrences of the body, the eta terms of the parameters, and the
defining equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-! ## Symbol lists -/

theorem encSymList_nil (sig : Sig) : encSymList sig [] = cNil := rfl

theorem encSymList_cons (sig : Sig) (f : SymId) (fs : List SymId) :
    encSymList sig (f :: fs) = cCons (encSym sig f) (encSymList sig fs) := rfl

theorem decList_encSymList (sig : Sig) (fids : List SymId) :
    decList (encSymList sig fids) = some (fids.map (encSym sig)) :=
  decList_encList _

theorem encSymList_eq_nil {sig : Sig} {fids : List SymId} (h : encSymList sig fids = cNil) :
    fids = [] := by
  cases fids with
  | nil => rfl
  | cons f fs => simp [encSymList, encList, cCons, cNil] at h

theorem encSymList_eq_cons {sig : Sig} {fids : List SymId} {x xs : Pattern}
    (h : encSymList sig fids = cCons x xs) :
    ∃ f fs, fids = f :: fs ∧ x = encSym sig f ∧ xs = encSymList sig fs := by
  cases fids with
  | nil => simp [encSymList, encList, cCons, cNil] at h
  | cons f fs =>
      rw [encSymList_cons] at h
      simp only [cCons, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
      exact ⟨f, fs, rfl, h.1.symm, h.2.symm⟩

theorem encSymList_inj {sig : Sig} :
    ∀ {a b : List SymId}, encSymList sig a = encSymList sig b → a = b
  | [], b, h => (encSymList_eq_nil h.symm).symm
  | f :: fs, b, h => by
      rw [encSymList_cons] at h
      obtain ⟨g, gs, rfl, hfg, hrest⟩ := encSymList_eq_cons h.symm
      rw [encSym_inj sig hfg.symm, encSymList_inj hrest]

/-! ## Eta terms -/

theorem range_succ_reverse_map (m : Nat) :
    (List.range (m + 1)).reverse.map Term.bvar =
      Term.bvar m :: (List.range m).reverse.map Term.bvar := by
  simp [List.range_succ]

theorem depthBinders_desc (sig : Sig) :
    ∀ (m : Nat) (bs : List Nat), (∀ b ∈ bs, b = 0) →
      depthBinders sig bs ((List.range m).reverse.map Term.bvar) = m
  | 0, _, _ => by simp [depthBinders]
  | m + 1, bs, h => by
      rw [range_succ_reverse_map, depthBinders]
      have hhead : bs.headD 0 = 0 := by
        cases bs with
        | nil => rfl
        | cons b bs => exact h b (by simp)
      have htail : ∀ b ∈ bs.tail, b = 0 := fun b hb => h b (List.mem_of_mem_tail hb)
      rw [hhead, depthBinders_desc sig m bs.tail htail]
      simp only [depth]
      omega

theorem hasFvarList_desc (sig : Sig) :
    ∀ m : Nat, hasFvarList sig ((List.range m).reverse.map Term.bvar) = false
  | 0 => by simp [hasFvarList_nil]
  | m + 1 => by
      rw [range_succ_reverse_map, hasFvarList_cons, hasFvarList_desc sig m]
      simp [hasFvar]

/-- The eta term of a free variable, encoded. -/
theorem encTerm_etaFvar {sig : Sig} (hfv : FvarsBindNothing sig) {F : SymId}
    (hsome : (sig F).isSome = true) (hk : kindOf sig F = .fvar) :
    encTerm sig (etaFvar F (symArity sig F)) =
      cApp (encSym sig F) (encTermList sig ((List.range (symArity sig F)).reverse.map Term.bvar))
        (cAnn (encNat (symArity sig F)) cTrue) := by
  obtain ⟨info, hinfo⟩ := Option.isSome_iff_exists.mp hsome
  have hkind : info.kind = .fvar := by simpa [kindOf, hinfo] using hk
  have hzero := hfv F info hinfo hkind
  have hbs : bindersOf sig F = info.binders := by simp [bindersOf, hinfo]
  unfold etaFvar
  rw [encTerm_app', hbs, symArity_eq, hbs, depthBinders_desc sig _ _ hzero, isFvarSym_eq, hk]
  rfl

variable (T : Theory)

/-! ## Parameters and hints -/

theorem ms_rAritiesNil : Meaning T (jArities cNil cNil) :=
  ⟨[], rfl, by simp, rfl⟩

theorem ms_rAritiesCons : ∀ idv fbs fvars n bs : Pattern,
    Meaning T (jSymDecl (cSym idv cKFvar fbs)) → Meaning T (jLen fbs n) →
      Meaning T (jArities fvars bs) →
        Meaning T (jArities (cCons (cSym idv cKFvar fbs) fvars) (cCons n bs)) := by
  intro idv fbs fvars n bs h1 h2 h3
  simp only [M_symdecl] at h1
  simp only [M_len, LenM] at h2
  simp only [M_arities, AritiesM] at h3 ⊢
  obtain ⟨sid, hsome, rfl, hkind, rfl⟩ := symDecl_inv h1
  have hk : kindOf T.sig sid = .fvar := encKind_inj hkind.symm
  have hn := h2 _ (decList_encNatList _)
  rw [List.length_map] at hn
  obtain ⟨fids, rfl, hall, rfl⟩ := h3
  refine ⟨sid :: fids, ?_, ?_, ?_⟩
  · rw [encSymList_cons, encSym_eq, hk]; rfl
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨hsome, hk⟩
    · exact hall f hf
  · rw [decNat_unique n _ hn, ← symArity_eq]; rfl

theorem ms_rHintsinNil : ∀ n : Pattern, Meaning T (jHintsIn cNil n) := by
  intro n
  simp only [M_hintsin, HintsInM]
  intro ν _
  exact ⟨[], rfl, by simp⟩

theorem ms_rHintsinCons : ∀ hh hs n : Pattern,
    Meaning T (jNLt hh n) → Meaning T (jHintsIn hs n) → Meaning T (jHintsIn (cCons hh hs) n) := by
  intro hh hs n h1 h2
  simp only [M_nlt, NLtM] at h1
  simp only [M_hintsin, HintsInM] at h2 ⊢
  intro ν hν
  obtain ⟨x, hx, hlt⟩ := h1 ν hν
  obtain ⟨l, rfl, hl⟩ := h2 ν hν
  refine ⟨x :: l, by rw [encNatList_cons, decNat_unique hh x hx], ?_⟩
  intro h hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hlt
  · exact hl h hmem

/-! ## Free-variable occurrences -/

theorem ms_rOccBvar : ∀ fvars i hs : Pattern, Meaning T (jOcc fvars (cBVar i) hs hs) := by
  intro fvars i hs
  simp only [M_occ, OccM]
  intro fids τ hl _ hτ hhs
  obtain ⟨j, rfl, _⟩ := encTerm_eq_bvar T.sig τ i hτ.symm
  exact ⟨hl, by simp [fvarOccurrences, consumeHints], hhs⟩

theorem ms_rOccLit : ∀ fvars bs hs : Pattern, Meaning T (jOcc fvars (cLit bs) hs hs) := by
  intro fvars bs hs
  simp only [M_occ, OccM]
  intro fids τ hl _ hτ hhs
  obtain ⟨bytes, rfl, _⟩ := encTerm_eq_lit T.sig τ bs hτ.symm
  exact ⟨hl, by simp [fvarOccurrences, consumeHints], hhs⟩

theorem ms_rOccConst : ∀ fvars idv bs ts ann hs rest : Pattern,
    Meaning T (jOccArgs fvars ts hs rest) →
      Meaning T (jOcc fvars (cApp (cSym idv cKConst bs) ts ann) hs rest) := by
  intro fvars idv bs ts ann hs rest h1
  simp only [M_occargs, OccArgsM] at h1
  simp only [M_occ, OccM]
  intro fids τ hl hfs hτ hhs
  obtain ⟨s, args, rfl, hs', hts, -⟩ := encTerm_eq_app T.sig τ _ _ _ hτ.symm
  obtain ⟨-, hk, -⟩ := encSym_parts T.sig s hs'
  have hkc : kindOf T.sig s = .constant := encKind_inj hk.symm
  rw [fvarOccurrences_app, isFvarSym_eq, hkc]
  exact h1 fids args hl hfs hts hhs

theorem ms_rOccFvar : ∀ fvars idv bs ts ann hh hs rest : Pattern,
    Meaning T (jNth fvars hh (cSym idv cKFvar bs)) → Meaning T (jOccArgs fvars ts hs rest) →
      Meaning T (jOcc fvars (cApp (cSym idv cKFvar bs) ts ann) (cCons hh hs) rest) := by
  intro fvars idv bs ts ann hh hs rest h1 h2
  simp only [M_nth, NthM] at h1
  simp only [M_occargs, OccArgsM] at h2
  simp only [M_occ, OccM]
  intro fids τ hl hfs hτ hhs
  obtain ⟨s, args, rfl, hs', hts, -⟩ := encTerm_eq_app T.sig τ _ _ _ hτ.symm
  obtain ⟨-, hk, -⟩ := encSym_parts T.sig s hs'
  have hkf : kindOf T.sig s = .fvar := encKind_inj hk.symm
  obtain ⟨k, hl', rfl, rfl, rfl⟩ := encNatList_eq_cons hl _ _ hhs.symm
  obtain ⟨k', hk', hnth⟩ := h1 _ (by rw [hfs]; exact decList_encSymList T.sig fids)
  rw [decNat_encNat] at hk'
  cases hk'
  rw [List.getElem?_map, Option.map_eq_some_iff] at hnth
  obtain ⟨f, hf, hfeq⟩ := hnth
  have hfs' : f = s := encSym_inj T.sig (hfeq.trans hs')
  subst hfs'
  rw [fvarOccurrences_app, isFvarSym_eq, hkf]
  simp only [beq_self_eq_true, if_true, List.singleton_append, consumeHints, hf]
  exact h2 fids args hl' hfs hts rfl

theorem ms_rOccargsNil : ∀ fvars hs : Pattern, Meaning T (jOccArgs fvars cNil hs hs) := by
  intro fvars hs
  simp only [M_occargs, OccArgsM]
  intro fids τs hl _ hts hhs
  rw [encTermList_eq_nil T.sig τs hts.symm]
  exact ⟨hl, by simp [fvarOccurrencesList, consumeHints], hhs⟩

theorem ms_rOccargsCons : ∀ fvars t ts hs mid rest : Pattern,
    Meaning T (jOcc fvars t hs mid) → Meaning T (jOccArgs fvars ts mid rest) →
      Meaning T (jOccArgs fvars (cCons t ts) hs rest) := by
  intro fvars t ts hs mid rest h1 h2
  simp only [M_occ, OccM] at h1
  simp only [M_occargs, OccArgsM] at h2 ⊢
  intro fids τs hl hfs hts hhs
  obtain ⟨τ, τs', rfl, ht, hts'⟩ := encTermList_eq_cons T.sig τs t ts hts.symm
  obtain ⟨ml, hml, rfl⟩ := h1 fids τ hl hfs ht hhs
  obtain ⟨rl, hrl, rfl⟩ := h2 fids τs' ml hfs hts' rfl
  refine ⟨rl, ?_, rfl⟩
  rw [fvarOccurrencesList_cons, consumeHints_append, hml]
  exact hrl

/-! ## Eta terms of the parameters -/

theorem ms_rDesc0 : Meaning T (jDescBVars cN0 cNil) := by
  simp only [M_descbvars, DescBVarsM, decNat_N0, Option.some.injEq]
  rintro ν rfl
  rfl

theorem ms_rDescS : ∀ n k vars : Pattern,
    Meaning T (jNAdd k patOne n) → Meaning T (jDescBVars k vars) →
      Meaning T (jDescBVars n (cCons (cBVar k) vars)) := by
  intro n k vars h1 h2
  simp only [M_nadd, NAddM] at h1
  simp only [M_descbvars, DescBVarsM] at h2 ⊢
  intro ν hν
  obtain ⟨x, one, hx, hone, rfl⟩ := h1.2 ν hν
  rw [decNat_patOne] at hone
  cases hone
  rw [range_succ_reverse_map, encTermList_cons, encTerm_bvar, ← decNat_unique k x hx, h2 x hx]

theorem ms_rEtasNil : Meaning T (jEtas cNil cNil) := by
  simp only [M_etas, EtasM]
  intro fids hfs _
  rw [encSymList_eq_nil hfs.symm]
  rfl

theorem ms_rEtasCons (hfv : FvarsBindNothing T.sig) : ∀ idv fbs fvars n vars etas : Pattern,
    Meaning T (jLen fbs n) → Meaning T (jDescBVars n vars) → Meaning T (jEtas fvars etas) →
      Meaning T (jEtas (cCons (cSym idv cKFvar fbs) fvars)
        (cCons (cApp (cSym idv cKFvar fbs) vars (cAnn n cTrue)) etas)) := by
  intro idv fbs fvars n vars etas h1 h2 h3
  simp only [M_len, LenM] at h1
  simp only [M_descbvars, DescBVarsM] at h2
  simp only [M_etas, EtasM] at h3 ⊢
  intro fids hfs hall
  obtain ⟨F, fs, rfl, hF, hfs'⟩ := encSymList_eq_cons hfs.symm
  obtain ⟨_, _, hbs⟩ := encSym_parts T.sig F hF
  have hn := h1 _ (by rw [hbs]; exact decList_encNatList _)
  rw [List.length_map, ← symArity_eq] at hn
  have hFall := hall F (by simp)
  rw [List.map_cons, encTermList_cons, encTerm_etaFvar hfv hFall.1 hFall.2, ← hF, ← h2 _ hn,
    ← decNat_unique n _ hn, ← h3 fs hfs' (fun f hf => hall f (by simp [hf]))]

/-! ## The defining equation -/

theorem ms_rDefstmt (hb : BuiltinsFixed T.sig) :
    ∀ cid fvars bs n hints value rest etas dl fl de fe : Pattern,
      Meaning T (jArities fvars bs) → Meaning T (jLen fvars n) → Meaning T (jHintsIn hints n) →
      Meaning T (jWf value) → Meaning T (jDepth value cN0) →
      Meaning T (jOcc fvars value hints rest) → Meaning T (jEtas fvars etas) →
      Meaning T (jAnnArgs bs etas dl fl) →
      Meaning T (jAnnArgs (cCons cN0 (cCons cN0 cNil))
        (cCons (cApp (cSym cid cKConst bs) etas (cAnn dl fl)) (cCons value cNil)) de fe) →
      Meaning T (jDefStmt (cSym cid cKConst bs) fvars hints value
        (cApp patEq (cCons (cApp (cSym cid cKConst bs) etas (cAnn dl fl)) (cCons value cNil))
          (cAnn de fe))) := by
  intro cid fvars bs n hints value rest etas dl fl de fe h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp only [M_arities, AritiesM] at h1
  simp only [M_len, LenM] at h2
  simp only [M_hintsin, HintsInM] at h3
  simp only [M_wf, WfM] at h4
  simp only [M_depth, DepthM] at h5
  simp only [M_occ, OccM] at h6
  simp only [M_etas, EtasM] at h7
  simp only [M_annargs, AnnArgsM] at h8 h9
  simp only [M_defstmt, DefStmtM]
  obtain ⟨fids, rfl, hall, rfl⟩ := h1
  obtain ⟨vτ, rfl, _⟩ := h4
  intro fids' hl vτ' hfs hhs hv
  have hf : fids = fids' := encSymList_inj hfs
  subst hf
  have hvv : vτ = vτ' := encTerm_inj T.sig hv
  subst hvv
  have hn := h2 _ (decList_encSymList T.sig fids)
  rw [List.length_map] at hn
  obtain ⟨l, hl', hlt⟩ := h3 _ hn
  have hll : l = hl := encNatList_inj (hl'.symm.trans hhs)
  subst hll
  have hd0 := encNat_eq_N0 (h5 vτ rfl)
  obtain ⟨rl, hrl, _⟩ := h6 fids vτ l rfl rfl hl'
  refine ⟨?_, ?_⟩
  · simp only [definitionAdmissible, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨hd0, fun f hf => ?_⟩, (hintsAdmit_iff _ _ _).mpr ⟨hlt, by rw [hrl]; rfl⟩⟩
    rw [isFvarSym_eq, (hall f hf).2]
    rfl
  · intro cs hcs hsig
    have hetas := h7 fids rfl hall
    subst hetas
    obtain ⟨hdl, hfl⟩ := h8 _ _ rfl rfl
    have hbcs : bindersOf T.sig cs = fids.map (symArity T.sig) := by
      simp [bindersOf, hsig, definitionInfo]
    have hkcs : isFvarSym T.sig cs = false := by
      simp [isFvarSym, hsig, definitionInfo]
    have hlhs : cApp (cSym cid cKConst (encNatList (fids.map (symArity T.sig))))
        (encTermList T.sig (fids.map fun F => etaFvar F (symArity T.sig F))) (cAnn dl fl) =
        encTerm T.sig (.app cs (fids.map fun F => etaFvar F (symArity T.sig F))) := by
      rw [encTerm_app', hbcs, hkcs, ← hcs, hdl, hfl]
      rfl
    obtain ⟨hde, hfe⟩ := h9 [0, 0] [.app cs (fids.map fun F => etaFvar F (symArity T.sig F)), vτ]
      rfl (by rw [encTermList_cons, encTermList_cons, encTermList_nil, hlhs])
    have hstmt : encTerm T.sig (definitionStatement T.sig cs fids vτ) =
        cApp patEq (cCons (encTerm T.sig (.app cs (fids.map fun F => etaFvar F (symArity T.sig F))))
          (cCons (encTerm T.sig vτ) cNil))
          (cAnn (encNat (depthBinders T.sig [0, 0]
              [.app cs (fids.map fun F => etaFvar F (symArity T.sig F)), vτ]))
            (encBool (hasFvarList T.sig
              [.app cs (fids.map fun F => etaFvar F (symArity T.sig F)), vτ]))) := by
      unfold definitionStatement Term.eq
      rw [encTerm_app' T.sig (.builtin .eq), encSym_builtin hb, bindersOf_builtin hb,
        isFvarSym_builtin hb, encTermList_cons, encTermList_cons, encTermList_nil]
      rfl
    rw [hstmt, ← hlhs, hde, hfe]

end Mettapedia.Languages.VibeITP.Presentation
