import Mettapedia.Languages.VibeITP.Presentation.CompleteTerms
import Mettapedia.Languages.VibeITP.Presentation.Soundness
import Mettapedia.Languages.VibeITP.Presentation.TermShape

/-!
# Constructive witnesses for definition admission

Parameter declarations determine their arities. Successful hint consumption
gives occurrence witnesses in the same preorder as the specification. The eta
terms and both levels of cached annotations give the exact defining equation,
under the concrete signature, formation and admission conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

private theorem definitionRule_in {R : List FORule} (hR : kernelRules ⊆ R)
    {r : FORule} (hr : r ∈ definitionRules) : r ∈ R :=
  hR (by simp [kernelRules, hr])

theorem isData_encSymList (sig : Sig) (fs : List SymId) : IsData (encSymList sig fs) :=
  isData_encList _ (by simp [isData_encSym])

theorem complete_len_natList {R : List FORule} (hR : kernelRules ⊆ R) (ns : List Nat) :
    FODerivable R (jLen (encNatList ns) (encNat ns.length)) := by
  simpa only [encNatList, List.length_map] using
    complete_len hR (ns.map encNat) (by simp [isData_encNat])

theorem complete_len_symList {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (fs : List SymId) :
    FODerivable R (jLen (encSymList sig fs) (encNat fs.length)) := by
  simpa only [encSymList, List.length_map] using
    complete_len hR (fs.map (encSym sig)) (by simp [isData_encSym])

theorem definitionAdmissible_parameters (sig : Sig) (fs : List SymId)
    (hints : List Nat) (value : Term)
    (hadmit : definitionAdmissible sig fs hints value = true) :
    ∀ f ∈ fs, (sig f).isSome = true ∧ kindOf sig f = .fvar := by
  simp only [definitionAdmissible, Bool.and_eq_true, List.all_eq_true] at hadmit
  intro f hf
  have hfv := hadmit.1.2 f hf
  cases hinfo : sig f with
  | none => simp [isFvarSym, hinfo] at hfv
  | some info =>
      have hk : info.kind = .fvar := by simpa only [isFvarSym, hinfo, beq_iff_eq] using hfv
      exact ⟨rfl, by simp [kindOf, hinfo, hk]⟩

theorem complete_arities {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    (fs : List SymId)
    (hall : ∀ f ∈ fs, (T.sig f).isSome = true ∧ kindOf T.sig f = .fvar) :
    FODerivable R (jArities (encSymList T.sig fs) (encNatList (fs.map (symArity T.sig)))) := by
  induction fs with
  | nil => exact intro_rAritiesNil (definitionRule_in hR (by simp [definitionRules]))
  | cons f fs ih =>
      have hf := hall f (by simp)
      have htail : ∀ g ∈ fs, (T.sig g).isSome = true ∧ kindOf T.sig g = .fvar :=
        fun g hg => hall g (by simp [hg])
      have hdecl := complete_symDecl hR hT h f hf.1
      rw [encSym_eq, hf.2] at hdecl
      have hlen := complete_len_natList hR (bindersOf T.sig f)
      rw [← symArity_eq] at hlen
      rw [encSymList_cons, List.map_cons, encNatList_cons, encSym_eq, hf.2]
      exact intro_rAritiesCons (definitionRule_in hR (by simp [definitionRules]))
        (isData_encNat (symNumber f)) (isData_encNatList (bindersOf T.sig f))
        (isData_encSymList T.sig fs) (isData_encNat (symArity T.sig f))
        (isData_encNatList (fs.map (symArity T.sig))) hdecl hlen (ih htail)

theorem complete_hintsIn {R : List FORule} (hR : kernelRules ⊆ R)
    (hs : List Nat) (n : Nat) (hall : ∀ h ∈ hs, h < n) :
    FODerivable R (jHintsIn (encNatList hs) (encNat n)) := by
  induction hs with
  | nil =>
      exact intro_rHintsinNil (definitionRule_in hR (by simp [definitionRules]))
        (isData_encNat n)
  | cons hh hs ih =>
      exact intro_rHintsinCons (definitionRule_in hR (by simp [definitionRules]))
        (isData_encNat hh) (isData_encNatList hs) (isData_encNat n)
        (complete_nlt hR hh n (hall hh (by simp))) (ih (fun k hk => hall k (by simp [hk])))

mutual
theorem complete_occ {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (fs : List SymId) (t : Term) (hs rest : List Nat)
    (hconsume : consumeHints fs (fvarOccurrences sig t) hs = some rest) :
    FODerivable R (jOcc (encSymList sig fs) (encTerm sig t)
      (encNatList hs) (encNatList rest)) := by
  cases t with
  | bvar i =>
      have hr : hs = rest := by simpa [fvarOccurrences, consumeHints] using hconsume
      subst rest
      exact intro_rOccBvar (definitionRule_in hR (by simp [definitionRules]))
        (isData_encSymList sig fs) (isData_encNat i) (isData_encNatList hs)
  | lit bytes =>
      have hr : hs = rest := by simpa [fvarOccurrences, consumeHints] using hconsume
      subst rest
      exact intro_rOccLit (definitionRule_in hR (by simp [definitionRules]))
        (isData_encSymList sig fs) (isData_encBytes bytes) (isData_encNatList hs)
  | app s args =>
      rw [fvarOccurrences_app, isFvarSym_eq] at hconsume
      cases hk : kindOf sig s with
      | constant =>
          simp [hk] at hconsume
          have hfv : isFvarSym sig s = false := by rw [isFvarSym_eq, hk]; rfl
          rw [encTerm_app', encSym_eq, hk, hfv]
          exact intro_rOccConst (definitionRule_in hR (by simp [definitionRules]))
            (isData_encSymList sig fs) (isData_encNat (symNumber s))
            (isData_encNatList (bindersOf sig s)) (isData_encTermList sig args)
            (IsData.app2 _ (isData_encNat _) (isData_encBool _))
            (isData_encNatList hs) (isData_encNatList rest)
            (complete_occArgs hR sig fs args hs rest hconsume)
      | fvar =>
          simp only [hk, beq_self_eq_true, ↓reduceIte, List.singleton_append] at hconsume
          cases hs with
          | nil => simp [consumeHints] at hconsume
          | cons hh hs =>
              simp only [consumeHints] at hconsume
              split at hconsume
              next hget =>
                have hnth := complete_nth hR (fs.map (encSym sig)) hh (encSym sig s)
                  (by simp [isData_encSym]) (by simp [List.getElem?_map, hget])
                rw [encSym_eq, hk] at hnth
                have hfv : isFvarSym sig s = true := by rw [isFvarSym_eq, hk]; rfl
                rw [encTerm_app', encSym_eq, hk, hfv, encNatList_cons]
                exact intro_rOccFvar (definitionRule_in hR (by simp [definitionRules]))
                  (isData_encSymList sig fs) (isData_encNat (symNumber s))
                  (isData_encNatList (bindersOf sig s)) (isData_encTermList sig args)
                  (IsData.app2 _ (isData_encNat _) (isData_encBool _))
                  (isData_encNat hh) (isData_encNatList hs) (isData_encNatList rest)
                  hnth (complete_occArgs hR sig fs args hs rest hconsume)
              next hget => simp at hconsume
termination_by sizeOf t

theorem complete_occArgs {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (fs : List SymId) (ts : List Term) (hs rest : List Nat)
    (hconsume : consumeHints fs (fvarOccurrencesList sig ts) hs = some rest) :
    FODerivable R (jOccArgs (encSymList sig fs) (encTermList sig ts)
      (encNatList hs) (encNatList rest)) := by
  cases ts with
  | nil =>
      have hr : hs = rest := by simpa [fvarOccurrencesList, consumeHints] using hconsume
      subst rest
      exact intro_rOccargsNil (definitionRule_in hR (by simp [definitionRules]))
        (isData_encSymList sig fs) (isData_encNatList hs)
  | cons t ts =>
      rw [fvarOccurrencesList_cons, consumeHints_append] at hconsume
      obtain ⟨mid, hfirst, hlast⟩ := Option.bind_eq_some_iff.mp hconsume
      exact intro_rOccargsCons (definitionRule_in hR (by simp [definitionRules]))
        (isData_encSymList sig fs) (isData_encTerm sig t) (isData_encTermList sig ts)
        (isData_encNatList hs) (isData_encNatList mid) (isData_encNatList rest)
        (complete_occ hR sig fs t hs mid hfirst)
        (complete_occArgs hR sig fs ts mid rest hlast)
termination_by sizeOf ts
end

theorem complete_descBVars {R : List FORule} (hR : kernelRules ⊆ R) (sig : Sig) (n : Nat) :
    FODerivable R (jDescBVars (encNat n)
      (encTermList sig ((List.range n).reverse.map Term.bvar))) := by
  induction n with
  | zero => exact intro_rDesc0 (definitionRule_in hR (by simp [definitionRules]))
  | succ n ih =>
      rw [range_succ_reverse_map, encTermList_cons, encTerm_bvar]
      exact intro_rDescS (definitionRule_in hR (by simp [definitionRules]))
        (isData_encNat (n + 1)) (isData_encNat n) (isData_encTermList sig _)
        (complete_nadd hR n 1) ih

theorem complete_etas {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (hfv : FvarsBindNothing sig) (fs : List SymId)
    (hall : ∀ f ∈ fs, (sig f).isSome = true ∧ kindOf sig f = .fvar) :
    FODerivable R (jEtas (encSymList sig fs)
      (encTermList sig (fs.map fun f => etaFvar f (symArity sig f)))) := by
  induction fs with
  | nil => exact intro_rEtasNil (definitionRule_in hR (by simp [definitionRules]))
  | cons f fs ih =>
      have hf := hall f (by simp)
      rw [encSymList_cons, List.map_cons, encTermList_cons, encTerm_etaFvar hfv hf.1 hf.2,
        encSym_eq, hf.2]
      have hlen := complete_len_natList hR (bindersOf sig f)
      rw [← symArity_eq] at hlen
      exact intro_rEtasCons (definitionRule_in hR (by simp [definitionRules]))
        (isData_encNat (symNumber f)) (isData_encNatList (bindersOf sig f))
        (isData_encSymList sig fs) (isData_encNat (symArity sig f))
        (isData_encTermList sig _) (isData_encTermList sig _)
        hlen (complete_descBVars hR sig (symArity sig f))
        (ih (fun g hg => hall g (by simp [hg])))

theorem complete_defStmt {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    (cs : SymId) (fs : List SymId) (hints : List Nat) (value : Term)
    (hsig : T.sig cs = some (definitionInfo T.sig fs))
    (hwf : WellFormed T.sig value = true)
    (hadmit : definitionAdmissible T.sig fs hints value = true) :
    FODerivable R (jDefStmt (encSym T.sig cs) (encSymList T.sig fs) (encNatList hints)
      (encTerm T.sig value) (encTerm T.sig (definitionStatement T.sig cs fs value))) := by
  have conditions : (depth T.sig value = 0 ∧ ∀ f ∈ fs, isFvarSym T.sig f = true) ∧
      hintsAdmit fs hints (fvarOccurrences T.sig value) = true := by
    simpa only [definitionAdmissible, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] using hadmit
  have hall := definitionAdmissible_parameters T.sig fs hints value hadmit
  have hintConditions := (hintsAdmit_iff fs hints (fvarOccurrences T.sig value)).mp conditions.2
  obtain ⟨rest, hconsume⟩ := Option.isSome_iff_exists.mp hintConditions.2
  let etas := fs.map fun f => etaFvar f (symArity T.sig f)
  let bs := fs.map (symArity T.sig)
  let lhs := Term.app cs etas
  let dl := depthBinders T.sig bs etas
  let fl := hasFvarList T.sig etas
  let de := depthBinders T.sig [0, 0] [lhs, value]
  let fe := hasFvarList T.sig [lhs, value]
  have hcs : encSym T.sig cs = cSym (encNat (symNumber cs)) cKConst (encNatList bs) := by
    rw [encSym, hsig]
    rfl
  have hbs : bindersOf T.sig cs = bs := by simp [bindersOf, hsig, definitionInfo, bs]
  have hconst : isFvarSym T.sig cs = false := by simp [isFvarSym, hsig, definitionInfo]
  have hleft : encTerm T.sig lhs =
      cApp (cSym (encNat (symNumber cs)) cKConst (encNatList bs))
        (encTermList T.sig etas) (cAnn (encNat dl) (encBool fl)) := by
    change encTerm T.sig (.app cs etas) = _
    rw [encTerm_app', hcs, hbs, hconst]
    simp only [Bool.false_or]
    rfl
  have hstmt : encTerm T.sig (definitionStatement T.sig cs fs value) =
      cApp patEq (cCons
        (cApp (cSym (encNat (symNumber cs)) cKConst (encNatList bs))
          (encTermList T.sig etas) (cAnn (encNat dl) (encBool fl)))
        (cCons (encTerm T.sig value) cNil)) (cAnn (encNat de) (encBool fe)) := by
    change encTerm T.sig (.eq lhs value) = _
    unfold Term.eq
    rw [encTerm_app' T.sig (.builtin .eq), encSym_builtin h.builtin,
      bindersOf_builtin h.builtin, isFvarSym_builtin h.builtin,
      encTermList_cons, encTermList_cons, encTermList_nil, hleft]
    simp only [Bool.false_or]
    rfl
  have hdepth := complete_depth hR T.sig value
  rw [conditions.1.1] at hdepth
  have hann := complete_annArgs hR T.sig [0, 0] [lhs, value] rfl
  rw [encTermList_cons, encTermList_cons, encTermList_nil, hleft] at hann
  rw [hcs, hstmt]
  exact intro_rDefstmt (definitionRule_in hR (by simp [definitionRules]))
    (isData_encNat (symNumber cs)) (isData_encSymList T.sig fs) (isData_encNatList bs)
    (isData_encNat fs.length) (isData_encNatList hints) (isData_encTerm T.sig value)
    (isData_encNatList rest) (isData_encTermList T.sig etas)
    (isData_encNat dl) (isData_encBool fl) (isData_encNat de) (isData_encBool fe)
    (complete_arities hR hT h fs hall) (complete_len_symList hR T.sig fs)
    (complete_hintsIn hR hints fs.length hintConditions.1)
    (complete_wf hR hT h value hwf) hdepth
    (complete_occ hR T.sig fs value hints rest hconsume)
    (complete_etas hR T.sig h.fvarBinders fs hall)
    (complete_annArgs hR T.sig bs etas (by simp [bs, etas])) hann

theorem complete_admittedDefinition {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    (d : Definition) (hd : d ∈ T.definitions) :
    ∃ hints, FODerivable R (jDefStmt (encSym T.sig d.symbol) (encSymList T.sig d.fvars)
      (encNatList hints) (encTerm T.sig d.value)
      (encTerm T.sig (definitionStatement T.sig d.symbol d.fvars d.value))) := by
  obtain ⟨hsig, hwf, hints, hadmit⟩ := h.definitionsOk d hd
  exact ⟨hints, complete_defStmt hR hT h d.symbol d.fvars hints d.value hsig hwf hadmit⟩

/-! ## Exact encoded admission profiles -/

theorem occ_iff_consumeHints {T : Theory} {n : Nat} (h : Hosted T n)
    (fs : List SymId) (t : Term) (hs rest : List Nat) :
    FODerivable (kernelRules ++ theoryRules T n)
      (jOcc (encSymList T.sig fs) (encTerm T.sig t) (encNatList hs) (encNatList rest)) ↔
        consumeHints fs (fvarOccurrences T.sig t) hs = some rest := by
  constructor
  · intro hd
    have meaning := meaning_of_foDerivable h hd
    simp only [M_occ, OccM] at meaning
    obtain ⟨rl, hconsume, heq⟩ := meaning fs t hs rfl rfl rfl
    have hr : rest = rl := encNatList_inj heq
    exact hr.symm ▸ hconsume
  · exact complete_occ (List.subset_append_left _ _) T.sig fs t hs rest

theorem occArgs_iff_consumeHints {T : Theory} {n : Nat} (h : Hosted T n)
    (fs : List SymId) (ts : List Term) (hs rest : List Nat) :
    FODerivable (kernelRules ++ theoryRules T n)
      (jOccArgs (encSymList T.sig fs) (encTermList T.sig ts) (encNatList hs) (encNatList rest)) ↔
        consumeHints fs (fvarOccurrencesList T.sig ts) hs = some rest := by
  constructor
  · intro hd
    have meaning := meaning_of_foDerivable h hd
    simp only [M_occargs, OccArgsM] at meaning
    obtain ⟨rl, hconsume, heq⟩ := meaning fs ts hs rfl rfl rfl
    have hr : rest = rl := encNatList_inj heq
    exact hr.symm ▸ hconsume
  · exact complete_occArgs (List.subset_append_left _ _) T.sig fs ts hs rest

theorem hintsIn_iff_bounds {T : Theory} {n : Nat} (h : Hosted T n)
    (hs : List Nat) (bound : Nat) :
    FODerivable (kernelRules ++ theoryRules T n) (jHintsIn (encNatList hs) (encNat bound)) ↔
      ∀ i ∈ hs, i < bound := by
  constructor
  · intro hd
    have meaning := meaning_of_foDerivable h hd
    simp only [M_hintsin, HintsInM] at meaning
    obtain ⟨l, heq, hall⟩ := meaning bound (decNat_encNat bound)
    have hl : hs = l := encNatList_inj heq
    exact hl.symm ▸ hall
  · exact complete_hintsIn (List.subset_append_left _ _) hs bound

theorem arities_iff_parameters {T : Theory} {n : Nat} (h : Hosted T n) (fs : List SymId) :
    FODerivable (kernelRules ++ theoryRules T n)
      (jArities (encSymList T.sig fs) (encNatList (fs.map (symArity T.sig)))) ↔
        ∀ f ∈ fs, (T.sig f).isSome = true ∧ kindOf T.sig f = .fvar := by
  constructor
  · intro hd
    have meaning := meaning_of_foDerivable h hd
    simp only [M_arities, AritiesM] at meaning
    obtain ⟨fids, heq, hall, _⟩ := meaning
    have hf : fs = fids := encSymList_inj heq
    exact hf.symm ▸ hall
  · exact complete_arities (List.subset_append_left _ _) (List.subset_append_right _ _) h fs

theorem defStmt_iff_admissible {T : Theory} {n : Nat} (h : Hosted T n)
    (cs : SymId) (fs : List SymId) (hints : List Nat) (value : Term)
    (hsig : T.sig cs = some (definitionInfo T.sig fs))
    (hwf : WellFormed T.sig value = true) :
    FODerivable (kernelRules ++ theoryRules T n)
      (jDefStmt (encSym T.sig cs) (encSymList T.sig fs) (encNatList hints) (encTerm T.sig value)
        (encTerm T.sig (definitionStatement T.sig cs fs value))) ↔
          definitionAdmissible T.sig fs hints value = true := by
  constructor
  · intro hd
    have meaning := meaning_of_foDerivable h hd
    simp only [M_defstmt, DefStmtM] at meaning
    exact (meaning fs hints value rfl rfl rfl).1
  · exact complete_defStmt (List.subset_append_left _ _) (List.subset_append_right _ _) h
      cs fs hints value hsig hwf

theorem no_occ_of_refused {T : Theory} {n : Nat} (h : Hosted T n)
    (fs : List SymId) (t : Term) (hs : List Nat)
    (hrefuse : consumeHints fs (fvarOccurrences T.sig t) hs = none) (rest : List Nat) :
    ¬FODerivable (kernelRules ++ theoryRules T n)
      (jOcc (encSymList T.sig fs) (encTerm T.sig t) (encNatList hs) (encNatList rest)) := by
  intro hd
  have hconsume := (occ_iff_consumeHints h fs t hs rest).mp hd
  rw [hrefuse] at hconsume
  contradiction

theorem no_defStmt_of_refused {T : Theory} {n : Nat} (h : Hosted T n)
    (cs : SymId) (fs : List SymId) (hints : List Nat) (value : Term)
    (hrefuse : definitionAdmissible T.sig fs hints value = false) (stmt : Pattern) :
    ¬FODerivable (kernelRules ++ theoryRules T n)
      (jDefStmt (encSym T.sig cs) (encSymList T.sig fs) (encNatList hints)
        (encTerm T.sig value) stmt) := by
  intro hd
  have meaning := meaning_of_foDerivable h hd
  simp only [M_defstmt, DefStmtM] at meaning
  have hadmit := (meaning fs hints value rfl rfl rfl).1
  rw [hrefuse] at hadmit
  contradiction

/-! ## Structural shapes of definition-generated eta terms -/

theorem termShapeList_of_forall (sig : Sig) : ∀ ts : List Term,
    (∀ t ∈ ts, TermShape sig t) → TermShapeList sig ts
  | [], _ => .nil
  | t :: ts, hall => .cons (hall t (by simp))
      (termShapeList_of_forall sig ts (fun u hu => hall u (by simp [hu])))

theorem etaFvar_termShape (sig : Sig) (f : SymId) (hf : (sig f).isSome = true) :
    TermShape sig (etaFvar f (symArity sig f)) := by
  obtain ⟨info, hinfo⟩ := Option.isSome_iff_exists.mp hf
  apply TermShape.app hinfo
  · simp [symArity, hinfo]
  · apply termShapeList_of_forall sig
    intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    exact .bvar i

theorem definitionStatement_termShape (sig : Sig) (hb : BuiltinsFixed sig)
    (cs : SymId) (fs : List SymId) (value : Term)
    (hsig : sig cs = some (definitionInfo sig fs))
    (hfs : ∀ f ∈ fs, (sig f).isSome = true) (hvalue : TermShape sig value) :
    TermShape sig (definitionStatement sig cs fs value) := by
  have hleft : TermShape sig (.app cs (fs.map fun f => etaFvar f (symArity sig f))) := by
    apply TermShape.app hsig
    · simp [definitionInfo, SymInfo.arity]
    · apply termShapeList_of_forall sig
      intro t ht
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
      exact etaFvar_termShape sig f (hfs f hf)
  exact .app (hb .eq) rfl (.cons hleft (.cons hvalue .nil))

theorem admittedDefinition_termShape {T : Theory} {n : Nat} (h : Hosted T n)
    (d : Definition) (hd : d ∈ T.definitions) :
    TermShape T.sig (definitionStatement T.sig d.symbol d.fvars d.value) := by
  obtain ⟨hsig, hwf, hints, hadmit⟩ := h.definitionsOk d hd
  exact definitionStatement_termShape T.sig h.builtin d.symbol d.fvars d.value hsig
    (fun f hf => (definitionAdmissible_parameters T.sig d.fvars hints d.value hadmit f hf).1)
    (wellFormed_termShape T.sig d.value hwf)

end Mettapedia.Languages.VibeITP.Presentation
