import Mettapedia.Languages.VibeITP.Presentation.SoundArith

/-!
# Vibe-ITP presentation: soundness of the term rules

Formation and annotation rules, shifting, plugging arguments, and
instantiating a free variable each preserve `Meaning`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-! ## Inversion helpers -/

theorem encNat_eq_N0 {α : Nat} (h : cN0 = encNat α) : α = 0 := by
  have := decNat_encNat α
  rw [← h, decNat_N0] at this
  exact (Option.some.inj this).symm

theorem encNat_eq_NPos {α : Nat} {p : Pattern} (h : cNPos p = encNat α) :
    1 ≤ α ∧ decPos p = some α := by
  have := decNat_encNat α
  rw [← h, decNat_NPos] at this
  exact ⟨decPos_pos p α this, this⟩

theorem decNat_of_eq {a : Pattern} {α : Nat} (h : a = encNat α) : decNat a = some α := by
  rw [h, decNat_encNat]

theorem symDecl_inv {sig : Sig} {id kind bs : Pattern} (h : SymDeclM sig (cSym id kind bs)) :
    ∃ sid, (sig sid).isSome ∧ id = encNat (symNumber sid) ∧
      kind = encKind (kindOf sig sid) ∧ bs = encNatList (bindersOf sig sid) := by
  obtain ⟨sid, hsome, heq⟩ := h
  rw [encSym_eq] at heq
  simp only [cSym, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at heq
  exact ⟨sid, hsome, heq.1, heq.2.1, heq.2.2⟩

theorem kindFv_eval {k : SymKind} {b : Bool} {f g : Pattern} (h : KindFvM (encKind k) f g)
    (hf : f = encBool b) : g = encBool ((k == .fvar) || b) := by
  rcases h with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
  · cases k with
    | constant => rw [hf]; cases b <;> rfl
    | fvar => simp [encKind, cKConst, cKFvar] at hk
  · cases k with
    | constant => simp [encKind, cKConst, cKFvar] at hk
    | fvar => rfl

theorem isFvarSym_kind (sig : Sig) (s : SymId) :
    isFvarSym sig s = (kindOf sig s == .fvar) := isFvarSym_eq sig s

theorem encSym_parts (sig : Sig) (s : SymId) {id kind bs : Pattern}
    (h : cSym id kind bs = encSym sig s) :
    id = encNat (symNumber s) ∧ kind = encKind (kindOf sig s) ∧
      bs = encNatList (bindersOf sig s) := by
  rw [encSym_eq] at h
  simp only [cSym, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-! ## Formation and annotations -/

variable (T : Theory)

theorem ms_rWfBvar : ∀ n k : Pattern,
    Meaning T (jNAdd n patOne k) → Meaning T (jNWord k) → Meaning T (jWf (cBVar n)) := by
  intro n k h1 h2
  simp only [M_nadd, NAddM] at h1
  obtain ⟨w, hw, hlt⟩ := h2
  obtain ⟨i, one, hi, hone, rfl⟩ := h1.2 w hw
  rw [decNat_patOne] at hone
  cases hone
  refine ⟨.bvar i, ?_, ?_⟩
  · rw [encTerm_bvar, decNat_unique n i hi]
  · simp [WellFormed, hlt]

theorem ms_rWfLit : ∀ bs len k : Pattern,
    Meaning T (jBytes bs) → Meaning T (jLen bs len) → Meaning T (jNAdd len patEight k) →
      Meaning T (jNWord k) → Meaning T (jWf (cLit bs)) := by
  intro bs len k h1 h2 h3 h4
  obtain ⟨bytes, rfl⟩ := h1
  simp only [M_len, LenM] at h2
  simp only [M_nadd, NAddM] at h3
  obtain ⟨w, hw, hlt⟩ := h4
  have hlen := h2 _ (decList_encBytes bytes)
  have hk := h3.1 _ 8 hlen decNat_patEight
  rw [hw] at hk
  cases hk
  refine ⟨.lit bytes, rfl, ?_⟩
  simp only [WellFormed, decide_eq_true_eq]
  simpa using hlt

theorem ms_rWfApp : ∀ idv kind bs ts d f g : Pattern,
    Meaning T (jSymDecl (cSym idv kind bs)) → Meaning T (jWfArgs bs ts d f) →
      Meaning T (jKindFv kind f g) →
        Meaning T (jWf (cApp (cSym idv kind bs) ts (cAnn d g))) := by
  intro idv kind bs ts d f g h1 h2 h3
  simp only [M_symdecl] at h1
  simp only [M_wfargs, WfArgsM] at h2
  simp only [M_kindfv] at h3
  obtain ⟨sid, hsome, hid, hkind, hbs⟩ := symDecl_inv h1
  obtain ⟨args, rfl, hwf, hlen, rfl, rfl⟩ := h2 _ hbs
  subst hid hkind hbs
  have hg := kindFv_eval h3 rfl
  refine ⟨.app sid args, ?_, ?_⟩
  · rw [encTerm_app', encSym_eq, hg, isFvarSym_eq]
  · obtain ⟨info, hinfo⟩ := Option.isSome_iff_exists.mp hsome
    have hb : bindersOf T.sig sid = info.binders := by simp [bindersOf, hinfo]
    simp only [WellFormed, hinfo, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by rw [hlen, hb]; rfl, hwf⟩

theorem ms_rWfargsNil : Meaning T (jWfArgs cNil cNil cN0 cFalse) := by
  simp only [M_wfargs, WfArgsM]
  intro binders hb
  rw [encNatList_eq_nil binders hb.symm]
  exact ⟨[], by rw [encTermList_nil], by simp [WellFormedList], rfl, rfl, by simp [hasFvarList_nil, encBool]⟩

theorem ms_rWfargsCons : ∀ b bs t ts dt e dr fr ft d f : Pattern,
    Meaning T (jWf t) → Meaning T (jDepth t dt) → Meaning T (jNMonus dt b e) →
      Meaning T (jHasFv t ft) → Meaning T (jWfArgs bs ts dr fr) → Meaning T (jNMax e dr d) →
        Meaning T (jBOr ft fr f) → Meaning T (jWfArgs (cCons b bs) (cCons t ts) d f) := by
  intro b bs t ts dt e dr fr ft d f h1 h2 h3 h4 h5 h6 h7
  simp only [M_wf, WfM] at h1
  simp only [M_depth, DepthM] at h2
  simp only [M_nmonus, NMonusM] at h3
  simp only [M_hasfv, HasFvM] at h4
  simp only [M_wfargs, WfArgsM] at h5
  simp only [M_nmax, NMaxM] at h6
  obtain ⟨bx, byy, hbx, hby, hbz⟩ := h7
  simp only [M_wfargs, WfArgsM]
  intro binders hbs
  obtain ⟨β, βs, rfl, hb, hbs'⟩ := encNatList_eq_cons binders b bs hbs.symm
  obtain ⟨τ, rfl, hwf⟩ := h1
  obtain ⟨args, rfl, hwfs, hlen, rfl, rfl⟩ := h5 βs hbs'
  have hdt := h2 τ rfl
  have hft := h4 τ rfl
  have he := h3 _ β (decNat_of_eq hdt) (decNat_of_eq hb)
  have hd := h6 _ _ he (decNat_encNat _)
  refine ⟨τ :: args, by rw [encTermList_cons], ?_, by simp [hlen], ?_, ?_⟩
  · simp [WellFormedList, hwf, hwfs]
  · rw [decNat_unique d _ hd]; rfl
  · rw [decBool_unique f _ hbz]
    rw [hft, decBool_encBool] at hbx
    rw [decBool_encBool] at hby
    cases hbx; cases hby
    rw [hasFvarList_cons]

theorem ms_rKindfvConst : ∀ f : Pattern, Meaning T (jKindFv cKConst f f) :=
  fun _ => Or.inl ⟨rfl, rfl⟩

theorem ms_rKindfvFvar : ∀ f : Pattern, Meaning T (jKindFv cKFvar f cTrue) :=
  fun _ => Or.inr ⟨rfl, rfl⟩

theorem ms_rDepthBvar : ∀ n d : Pattern,
    Meaning T (jNAdd n patOne d) → Meaning T (jDepth (cBVar n) d) := by
  intro n d h
  simp only [M_nadd, NAddM] at h
  simp only [M_depth, DepthM]
  intro τ hτ
  obtain ⟨i, rfl, rfl⟩ := encTerm_eq_bvar T.sig τ n hτ.symm
  have := h.1 i 1 (decNat_encNat i) decNat_patOne
  rw [decNat_unique d _ this]
  rfl

theorem ms_rDepthLit : ∀ bs : Pattern, Meaning T (jDepth (cLit bs) cN0) := by
  intro bs
  simp only [M_depth, DepthM]
  intro τ hτ
  obtain ⟨bytes, rfl, rfl⟩ := encTerm_eq_lit T.sig τ bs hτ.symm
  rfl

theorem ms_rDepthApp : ∀ s ts d f : Pattern, Meaning T (jDepth (cApp s ts (cAnn d f)) d) := by
  intro s ts d f
  simp only [M_depth, DepthM]
  intro τ hτ
  obtain ⟨h, args, rfl, -, -, hann⟩ := encTerm_eq_app T.sig τ s ts _ hτ.symm
  simp only [cAnn, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at hann
  rw [hann.1]
  rfl

theorem ms_rHasfvBvar : ∀ n : Pattern, Meaning T (jHasFv (cBVar n) cFalse) := by
  intro n
  simp only [M_hasfv, HasFvM]
  intro τ hτ
  obtain ⟨i, rfl, -⟩ := encTerm_eq_bvar T.sig τ n hτ.symm
  rfl

theorem ms_rHasfvLit : ∀ bs : Pattern, Meaning T (jHasFv (cLit bs) cFalse) := by
  intro bs
  simp only [M_hasfv, HasFvM]
  intro τ hτ
  obtain ⟨bytes, rfl, -⟩ := encTerm_eq_lit T.sig τ bs hτ.symm
  rfl

theorem ms_rHasfvApp : ∀ s ts d f : Pattern, Meaning T (jHasFv (cApp s ts (cAnn d f)) f) := by
  intro s ts d f
  simp only [M_hasfv, HasFvM]
  intro τ hτ
  obtain ⟨h, args, rfl, -, -, hann⟩ := encTerm_eq_app T.sig τ s ts _ hτ.symm
  simp only [cAnn, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at hann
  rw [hann.2, hasFvar_app]

theorem ms_rAnnargsNil : Meaning T (jAnnArgs cNil cNil cN0 cFalse) := by
  simp only [M_annargs, AnnArgsM]
  intro binders args hb ha
  rw [encNatList_eq_nil binders hb.symm, encTermList_eq_nil T.sig args ha.symm]
  exact ⟨rfl, by simp [hasFvarList_nil, encBool]⟩

theorem ms_rAnnargsCons : ∀ b bs t ts dt e dr fr ft d f : Pattern,
    Meaning T (jDepth t dt) → Meaning T (jNMonus dt b e) → Meaning T (jHasFv t ft) →
      Meaning T (jAnnArgs bs ts dr fr) → Meaning T (jNMax e dr d) →
        Meaning T (jBOr ft fr f) → Meaning T (jAnnArgs (cCons b bs) (cCons t ts) d f) := by
  intro b bs t ts dt e dr fr ft d f h2 h3 h4 h5 h6 h7
  simp only [M_depth, DepthM] at h2
  simp only [M_nmonus, NMonusM] at h3
  simp only [M_hasfv, HasFvM] at h4
  simp only [M_annargs, AnnArgsM] at h5
  simp only [M_nmax, NMaxM] at h6
  obtain ⟨bx, byy, hbx, hby, hbz⟩ := h7
  simp only [M_annargs, AnnArgsM]
  intro binders args hbs hts
  obtain ⟨β, βs, rfl, hb, hbs'⟩ := encNatList_eq_cons binders b bs hbs.symm
  obtain ⟨τ, τs, rfl, ht, hts'⟩ := encTermList_eq_cons T.sig args t ts hts.symm
  obtain ⟨rfl, rfl⟩ := h5 βs τs hbs' hts'
  have hdt := h2 τ ht
  have hft := h4 τ ht
  have he := h3 _ β (decNat_of_eq hdt) (decNat_of_eq hb)
  have hd := h6 _ _ he (decNat_encNat _)
  refine ⟨?_, ?_⟩
  · rw [decNat_unique d _ hd]; rfl
  · rw [decBool_unique f _ hbz]
    rw [hft, decBool_encBool] at hbx
    rw [decBool_encBool] at hby
    cases hbx; cases hby
    rw [hasFvarList_cons]

/-! ## Shifting -/

theorem shift_zero (sig : Sig) (γ : Nat) (τ : Term) : shift sig 0 γ τ = some τ := by
  cases τ <;> simp [shift]

theorem shift_low (sig : Sig) (α γ : Nat) (τ : Term) (h : depth sig τ ≤ γ) :
    shift sig α γ τ = some τ := by
  cases τ with
  | bvar b => simp only [depth] at h; simp [shift, h]
  | lit bytes => simp [shift]
  | app s args => simp [shift, h]

theorem ms_rShiftZero : ∀ c t : Pattern, Meaning T (jShift cN0 c t t) := by
  intro c t
  simp only [M_shift, ShiftM]
  intro α γ τ ha _ ht
  rw [encNat_eq_N0 ha]
  exact ⟨τ, shift_zero _ _ _, ht⟩

theorem ms_rShiftLow : ∀ a c t d : Pattern,
    Meaning T (jDepth t d) → Meaning T (jNLe d c) → Meaning T (jShift a c t t) := by
  intro a c t d h1 h2
  simp only [M_depth, DepthM] at h1
  simp only [M_nle, NLeM] at h2
  simp only [M_shift, ShiftM]
  intro α γ τ _ hc ht
  have hd := h1 τ ht
  obtain ⟨x, hx, hle⟩ := h2 γ (decNat_of_eq hc)
  rw [decNat_of_eq hd] at hx
  cases hx
  exact ⟨τ, shift_low _ _ _ _ hle, ht⟩

theorem ms_rShiftBvar : ∀ p c b r : Pattern,
    Meaning T (jNLe c b) → Meaning T (jNAdd b (cNPos p) r) → Meaning T (jNLt r patMaxWord) →
      Meaning T (jShift (cNPos p) c (cBVar b) (cBVar r)) := by
  intro p c b r h1 h2 h3
  simp only [M_nle, NLeM] at h1
  simp only [M_nadd, NAddM] at h2
  simp only [M_nlt, NLtM] at h3
  simp only [M_shift, ShiftM]
  intro α γ τ ha hc ht
  obtain ⟨β, rfl, rfl⟩ := encTerm_eq_bvar T.sig τ b ht.symm
  obtain ⟨hα, hp⟩ := encNat_eq_NPos ha
  obtain ⟨γ', hγ', hle⟩ := h1 β (decNat_encNat β)
  rw [decNat_of_eq hc] at hγ'
  cases hγ'
  have hr := h2.1 β α (decNat_encNat β) (by simpa using hp)
  obtain ⟨ρ, hρ, hlt⟩ := h3 _ decNat_patMaxWord
  rw [hr] at hρ
  cases hρ
  refine ⟨.bvar (β + α), ?_, ?_⟩
  · simp only [shift]
    rw [if_neg (by omega), if_pos (by omega)]
  · rw [encTerm_bvar, decNat_unique r _ hr]

theorem ms_rShiftApp : ∀ p c idv kind bs ts d f us e g hh : Pattern,
    Meaning T (jNLt c d) → Meaning T (jShiftArgs (cNPos p) c bs ts us) →
      Meaning T (jAnnArgs bs us e g) → Meaning T (jKindFv kind g hh) →
        Meaning T (jShift (cNPos p) c (cApp (cSym idv kind bs) ts (cAnn d f))
          (cApp (cSym idv kind bs) us (cAnn e hh))) := by
  intro p c idv kind bs ts d f us e g hh h1 h2 h3 h4
  simp only [M_nlt, NLtM] at h1
  simp only [M_shiftargs, ShiftArgsM] at h2
  simp only [M_annargs, AnnArgsM] at h3
  simp only [M_kindfv] at h4
  simp only [M_shift, ShiftM]
  intro α γ τ ha hc ht
  obtain ⟨s, args, rfl, hs, rfl, hann⟩ := encTerm_eq_app T.sig τ _ _ _ ht.symm
  obtain ⟨hid, hkind, hbs⟩ := encSym_parts T.sig s hs
  subst hid hkind hbs
  simp only [cAnn, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at hann
  obtain ⟨hd, -⟩ := hann
  subst hd
  obtain ⟨hα, hp⟩ := encNat_eq_NPos ha
  obtain ⟨γ', hγ', hlt⟩ := h1 _ (decNat_encNat _)
  rw [decNat_of_eq hc] at hγ'
  cases hγ'
  obtain ⟨args', hsh, rfl⟩ := h2 α γ _ args ha hc rfl rfl
  obtain ⟨rfl, rfl⟩ := h3 _ args' rfl rfl
  have hh' := kindFv_eval h4 rfl
  refine ⟨.app s args', ?_, ?_⟩
  · have hdep : depth T.sig (.app s args) = depthArgs T.sig s 0 args := by rw [depth]
    simp only [shift]
    rw [if_neg (by rw [hdep]; omega), shiftArgs_eq, List.drop_zero, hsh]
    rfl
  · rw [encTerm_app', encSym_eq, hh', isFvarSym_eq]

theorem ms_rShiftargsNil : ∀ a c : Pattern, Meaning T (jShiftArgs a c cNil cNil cNil) := by
  intro a c
  simp only [M_shiftargs, ShiftArgsM]
  intro α γ binders args _ _ _ hts
  rw [encTermList_eq_nil T.sig args hts.symm]
  exact ⟨[], by simp [shiftList], by rw [encTermList_nil]⟩

theorem ms_rShiftargsCons : ∀ a c b bs t ts u us k : Pattern,
    Meaning T (jNAdd c b k) → Meaning T (jNWord k) → Meaning T (jShift a k t u) →
      Meaning T (jShiftArgs a c bs ts us) →
        Meaning T (jShiftArgs a c (cCons b bs) (cCons t ts) (cCons u us)) := by
  intro a c b bs t ts u us k h1 h2 h3 h4
  simp only [M_nadd, NAddM] at h1
  obtain ⟨w, hw, hlt⟩ := h2
  simp only [M_shift, ShiftM] at h3
  simp only [M_shiftargs, ShiftArgsM] at h4
  simp only [M_shiftargs, ShiftArgsM]
  intro α γ binders args ha hc hbs hts
  obtain ⟨β, βs, rfl, hb, hbs'⟩ := encNatList_eq_cons binders b bs hbs.symm
  obtain ⟨τ, τs, rfl, ht, hts'⟩ := encTermList_eq_cons T.sig args t ts hts.symm
  have hk := h1.1 γ β (decNat_of_eq hc) (decNat_of_eq hb)
  rw [hw] at hk
  cases hk
  obtain ⟨τ', hτ', rfl⟩ := h3 α (γ + β) τ ha (decNat_unique k _ hw) ht
  obtain ⟨τs', hτs', rfl⟩ := h4 α γ βs τs ha hc hbs' hts'
  refine ⟨τ' :: τs', ?_, by rw [encTermList_cons]⟩
  simp [shiftList, hlt, hτ', hτs']

/-! ## Plugging arguments -/

theorem ms_rSubstLow : ∀ n argv o t d : Pattern,
    Meaning T (jDepth t d) → Meaning T (jNLe d o) → Meaning T (jSubst n argv o t t) := by
  intro n argv o t d h1 h2
  simp only [M_depth, DepthM] at h1
  simp only [M_nle, NLeM] at h2
  simp only [M_subst, SubstM]
  intro ν As ω τ _ _ _ ho ht
  have hd := h1 τ ht
  obtain ⟨x, hx, hle⟩ := h2 ω (decNat_of_eq ho)
  rw [decNat_of_eq hd] at hx
  cases hx
  refine ⟨τ, ?_, ht⟩
  cases τ with
  | bvar b => simp only [depth] at hle; simp [substGo, hle]
  | lit bytes => simp [substGo]
  | app s args => simp [substGo, hle]

theorem ms_rSubstParam : ∀ n argv o b k k1 i a r : Pattern,
    Meaning T (jNAdd o k b) → Meaning T (jNLt k n) → Meaning T (jNAdd k patOne k1) →
      Meaning T (jNAdd i k1 n) → Meaning T (jNth argv i a) → Meaning T (jShift o cN0 a r) →
        Meaning T (jSubst n argv o (cBVar b) r) := by
  intro n argv o b k k1 i a r h1 h2 h3 h4 h5 h6
  simp only [M_nadd, NAddM] at h1 h3 h4
  simp only [M_nlt, NLtM] at h2
  simp only [M_nth, NthM] at h5
  simp only [M_shift, ShiftM] at h6
  simp only [M_subst, SubstM]
  intro ν As ω τ hn hargs hlen ho ht
  obtain ⟨β, rfl, rfl⟩ := encTerm_eq_bvar T.sig τ b ht.symm
  obtain ⟨ω', κ, hω', hκ, hβ⟩ := h1.2 β (decNat_encNat β)
  rw [decNat_of_eq ho] at hω'
  cases hω'
  obtain ⟨κ', hκ', hlt⟩ := h2 ν (decNat_of_eq hn)
  rw [hκ] at hκ'
  cases hκ'
  have hk1 := h3.1 κ 1 hκ decNat_patOne
  obtain ⟨ι, κ1, hι, hκ1, hν⟩ := h4.2 ν (decNat_of_eq hn)
  rw [hk1] at hκ1
  cases hκ1
  have hιlt : ι < As.length := by omega
  obtain ⟨ι', hι', ha⟩ := h5 _ (by rw [hargs]; exact decList_encTermList T.sig As)
  rw [hι] at hι'
  cases hι'
  simp only [List.getElem?_map, List.getElem?_eq_getElem hιlt, Option.map_some,
    Option.some.injEq] at ha
  obtain ⟨ρ, hρ, rfl⟩ := h6 ω 0 As[ι] ho rfl ha.symm
  refine ⟨ρ, ?_, rfl⟩
  simp only [substGo]
  rw [if_neg (by omega), if_pos (by omega)]
  rw [show ν - 1 - (β - ω) = ι by omega, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hιlt, Option.getD_some]
  exact hρ

theorem ms_rSubstAbove : ∀ n argv o b k k1 : Pattern,
    Meaning T (jNAdd o k b) → Meaning T (jNLe n k) → Meaning T (jNAdd k patOne k1) →
      Meaning T (jNWord k1) → Meaning T (jSubst n argv o (cBVar b) (cBVar k)) := by
  intro n argv o b k k1 h1 h2 h3 h4
  simp only [M_nadd, NAddM] at h1 h3
  simp only [M_nle, NLeM] at h2
  obtain ⟨w, hw, hwlt⟩ := h4
  simp only [M_subst, SubstM]
  intro ν As ω τ hn hargs hlen ho ht
  obtain ⟨β, rfl, rfl⟩ := encTerm_eq_bvar T.sig τ b ht.symm
  obtain ⟨ω', κ, hω', hκ, hβ⟩ := h1.2 β (decNat_encNat β)
  rw [decNat_of_eq ho] at hω'
  cases hω'
  obtain ⟨ν', hν', hle⟩ := h2 κ hκ
  rw [decNat_of_eq hn] at hν'
  cases hν'
  have hk1 := h3.1 κ 1 hκ decNat_patOne
  rw [hw] at hk1
  cases hk1
  refine ⟨.bvar κ, ?_, by rw [encTerm_bvar, decNat_unique k κ hκ]⟩
  simp only [substGo]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 2
  omega

theorem ms_rSubstApp : ∀ n argv o idv kind bs ts d f us e g hh : Pattern,
    Meaning T (jNLt o d) → Meaning T (jSubstArgs n argv o bs ts us) →
      Meaning T (jAnnArgs bs us e g) → Meaning T (jKindFv kind g hh) →
        Meaning T (jSubst n argv o (cApp (cSym idv kind bs) ts (cAnn d f))
          (cApp (cSym idv kind bs) us (cAnn e hh))) := by
  intro n argv o idv kind bs ts d f us e g hh h1 h2 h3 h4
  simp only [M_nlt, NLtM] at h1
  simp only [M_substargs, SubstArgsM] at h2
  simp only [M_annargs, AnnArgsM] at h3
  simp only [M_kindfv] at h4
  simp only [M_subst, SubstM]
  intro ν As ω τ hn hargs hlen ho ht
  obtain ⟨s, args, rfl, hs, rfl, hann⟩ := encTerm_eq_app T.sig τ _ _ _ ht.symm
  obtain ⟨hid, hkind, hbs⟩ := encSym_parts T.sig s hs
  subst hid hkind hbs
  simp only [cAnn, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at hann
  obtain ⟨hd, -⟩ := hann
  subst hd
  obtain ⟨ω', hω', hlt⟩ := h1 _ (decNat_encNat _)
  rw [decNat_of_eq ho] at hω'
  cases hω'
  obtain ⟨args', hsb, rfl⟩ := h2 ν As ω _ args hn hargs hlen ho rfl rfl
  obtain ⟨rfl, rfl⟩ := h3 _ args' rfl rfl
  have hh' := kindFv_eval h4 rfl
  refine ⟨.app s args', ?_, ?_⟩
  · have hdep : depth T.sig (.app s args) = depthArgs T.sig s 0 args := by rw [depth]
    simp only [substGo]
    rw [if_neg (by rw [hdep]; omega), substGoArgs_eq, List.drop_zero, hsb]
    rfl
  · rw [encTerm_app', encSym_eq, hh', isFvarSym_eq]

theorem ms_rSubstargsNil : ∀ n argv o : Pattern, Meaning T (jSubstArgs n argv o cNil cNil cNil) := by
  intro n argv o
  simp only [M_substargs, SubstArgsM]
  intro ν As ω binders τs _ _ _ _ _ hts
  rw [encTermList_eq_nil T.sig τs hts.symm]
  exact ⟨[], by simp [substList], by rw [encTermList_nil]⟩

theorem ms_rSubstargsCons : ∀ n argv o b bs t ts u us k : Pattern,
    Meaning T (jNAdd o b k) → Meaning T (jNWord k) → Meaning T (jSubst n argv k t u) →
      Meaning T (jSubstArgs n argv o bs ts us) →
        Meaning T (jSubstArgs n argv o (cCons b bs) (cCons t ts) (cCons u us)) := by
  intro n argv o b bs t ts u us k h1 h2 h3 h4
  simp only [M_nadd, NAddM] at h1
  obtain ⟨w, hw, hlt⟩ := h2
  simp only [M_subst, SubstM] at h3
  simp only [M_substargs, SubstArgsM] at h4
  simp only [M_substargs, SubstArgsM]
  intro ν As ω binders τs hn hargs hlen ho hbs hts
  obtain ⟨β, βs, rfl, hb, hbs'⟩ := encNatList_eq_cons binders b bs hbs.symm
  obtain ⟨τ, τs', rfl, ht, hts'⟩ := encTermList_eq_cons T.sig τs t ts hts.symm
  have hk := h1.1 ω β (decNat_of_eq ho) (decNat_of_eq hb)
  rw [hw] at hk
  cases hk
  obtain ⟨ρ, hρ, rfl⟩ := h3 ν As (ω + β) τ hn hargs hlen (decNat_unique k _ hw) ht
  obtain ⟨ρs, hρs, rfl⟩ := h4 ν As ω βs τs' hn hargs hlen ho hbs' hts'
  refine ⟨ρ :: ρs, ?_, by rw [encTermList_cons]⟩
  simp [substList, hlt, hρ, hρs]

theorem ms_rSubsttop0 : ∀ argv t : Pattern, Meaning T (jSubstTop cN0 argv t t) := by
  intro argv t
  simp only [M_substtop, SubstTopM]
  intro ν As τ hn _ _ ht
  rw [encNat_eq_N0 hn]
  exact ⟨τ, by simp [substBVars], ht⟩

theorem ms_rSubsttopP : ∀ p argv t r : Pattern,
    Meaning T (jSubst (cNPos p) argv cN0 t r) → Meaning T (jSubstTop (cNPos p) argv t r) := by
  intro p argv t r h
  simp only [M_subst, SubstM] at h
  simp only [M_substtop, SubstTopM]
  intro ν As τ hn hargs hlen ht
  obtain ⟨hν, _⟩ := encNat_eq_NPos hn
  obtain ⟨ρ, hρ, rfl⟩ := h ν As 0 τ hn hargs hlen rfl ht
  refine ⟨ρ, ?_, rfl⟩
  simp only [substBVars]
  rw [if_neg (by omega)]
  exact hρ

/-! ## Instantiation -/

theorem instGo_nofv (sig : Sig) (F : SymId) (ν : Nat) (vτ : Term) (ω : Nat) (τ : Term)
    (h : hasFvar sig τ = false) : instGo sig F ν vτ ω τ = some τ := by
  cases τ with
  | bvar b => simp [instGo]
  | lit bytes => simp [instGo]
  | app s args => simp [instGo, h]

theorem ms_rInstNofv : ∀ F v n o t : Pattern,
    Meaning T (jHasFv t cFalse) → Meaning T (jInst F v n o t t) := by
  intro F v n o t h
  simp only [M_hasfv, HasFvM] at h
  simp only [M_inst, InstM]
  intro fid ν vτ ω τ _ _ _ _ _ ht
  have hf := h τ ht
  have : hasFvar T.sig τ = false := by
    cases hb : hasFvar T.sig τ
    · rfl
    · rw [hb] at hf; simp [encBool, cTrue, cFalse] at hf
  exact ⟨τ, instGo_nofv _ _ _ _ _ _ this, ht⟩

theorem ms_rInstConst : ∀ F v n o idv bs ts d us e g : Pattern,
    Meaning T (jInstArgs F v n o bs ts us) → Meaning T (jAnnArgs bs us e g) →
      Meaning T (jInst F v n o (cApp (cSym idv cKConst bs) ts (cAnn d cTrue))
        (cApp (cSym idv cKConst bs) us (cAnn e g))) := by
  intro F v n o idv bs ts d us e g h1 h2
  simp only [M_instargs, InstArgsM] at h1
  simp only [M_annargs, AnnArgsM] at h2
  simp only [M_inst, InstM]
  intro fid ν vτ ω τ hfv hF hn hv ho ht
  obtain ⟨s, args, rfl, hs, rfl, hann⟩ := encTerm_eq_app T.sig τ _ _ _ ht.symm
  obtain ⟨hid, hkind, hbs⟩ := encSym_parts T.sig s hs
  subst hid hbs
  have hks : kindOf T.sig s = .constant := by
    cases hk : kindOf T.sig s
    · rfl
    · rw [hk] at hkind; simp [encKind, cKConst, cKFvar] at hkind
  simp only [cAnn, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at hann
  obtain ⟨-, hfvτ⟩ := hann
  have hne : s ≠ fid := by
    rintro rfl
    rw [hfv.2.1] at hks
    cases hks
  obtain ⟨args', hia, rfl, -⟩ := h1 fid ν vτ ω _ args hfv hF hn hv ho rfl rfl
  obtain ⟨rfl, rfl⟩ := h2 _ args' rfl rfl
  have hhas : hasFvar T.sig (.app s args) = true := by
    rw [hasFvar_app]
    cases hb : (isFvarSym T.sig s || hasFvarList T.sig args)
    · rw [hb] at hfvτ; simp [encBool, cTrue, cFalse] at hfvτ
    · rfl
  refine ⟨.app s args', ?_, ?_⟩
  · simp only [instGo, hhas]
    rw [instArgs_eq, List.drop_zero, hia]
    simp [hne]
  · rw [encTerm_app', encSym_eq, isFvarSym_eq, hks]
    rfl

theorem ms_rInstOther (idv fid' : Pattern)
    (hord : ∀ a b : Nat, decNat idv = some a → decNat fid' = some b → a ≠ b)
    (fbs v n o bs ts d us e g : Pattern)
    (h1 : Meaning T (jInstArgs (cSym fid' cKFvar fbs) v n o bs ts us))
    (h2 : Meaning T (jAnnArgs bs us e g)) :
    Meaning T (jInst (cSym fid' cKFvar fbs) v n o (cApp (cSym idv cKFvar bs) ts (cAnn d cTrue))
      (cApp (cSym idv cKFvar bs) us (cAnn e cTrue))) := by
  simp only [M_instargs, InstArgsM] at h1
  simp only [M_annargs, AnnArgsM] at h2
  simp only [M_inst, InstM]
  intro fid ν vτ ω τ hfv hF hn hv ho ht
  obtain ⟨s, args, rfl, hs, rfl, hann⟩ := encTerm_eq_app T.sig τ _ _ _ ht.symm
  obtain ⟨hid, hkind, hbs⟩ := encSym_parts T.sig s hs
  obtain ⟨hfid, -, -⟩ := encSym_parts T.sig fid hF
  subst hbs
  have hks : kindOf T.sig s = .fvar := by
    cases hk : kindOf T.sig s
    · rw [hk] at hkind; simp [encKind, cKConst, cKFvar] at hkind
    · rfl
  have hne : s ≠ fid := by
    rintro rfl
    exact hord _ _ (decNat_of_eq hid) (decNat_of_eq hfid) rfl
  obtain ⟨args', hia, rfl, -⟩ := h1 fid ν vτ ω _ args hfv hF hn hv ho rfl rfl
  obtain ⟨rfl, -⟩ := h2 _ args' rfl rfl
  have hisf : isFvarSym T.sig s = true := by rw [isFvarSym_eq, hks]; rfl
  have hhas : hasFvar T.sig (.app s args) = true := by
    rw [hasFvar_app, hisf]; rfl
  subst hid
  refine ⟨.app s args', ?_, ?_⟩
  · simp only [instGo, hhas]
    rw [instArgs_eq, List.drop_zero, hia]
    simp [hne]
  · rw [encTerm_app', encSym_eq, hisf, hks]
    rfl

theorem ms_rInstOtherLt : ∀ fid fbs v n o idv bs ts d us e g : Pattern,
    Meaning T (jNLt idv fid) → Meaning T (jInstArgs (cSym fid cKFvar fbs) v n o bs ts us) →
      Meaning T (jAnnArgs bs us e g) →
        Meaning T (jInst (cSym fid cKFvar fbs) v n o (cApp (cSym idv cKFvar bs) ts (cAnn d cTrue))
          (cApp (cSym idv cKFvar bs) us (cAnn e cTrue))) := by
  intro fid fbs v n o idv bs ts d us e g h0 h1 h2
  simp only [M_nlt, NLtM] at h0
  refine ms_rInstOther T idv fid ?_ fbs v n o bs ts d us e g h1 h2
  intro a b ha hb
  obtain ⟨a', ha', hlt⟩ := h0 b hb
  rw [ha] at ha'
  cases ha'
  omega

theorem ms_rInstOtherGt : ∀ fid fbs v n o idv bs ts d us e g : Pattern,
    Meaning T (jNLt fid idv) → Meaning T (jInstArgs (cSym fid cKFvar fbs) v n o bs ts us) →
      Meaning T (jAnnArgs bs us e g) →
        Meaning T (jInst (cSym fid cKFvar fbs) v n o (cApp (cSym idv cKFvar bs) ts (cAnn d cTrue))
          (cApp (cSym idv cKFvar bs) us (cAnn e cTrue))) := by
  intro fid fbs v n o idv bs ts d us e g h0 h1 h2
  simp only [M_nlt, NLtM] at h0
  refine ms_rInstOther T idv fid ?_ fbs v n o bs ts d us e g h1 h2
  intro a b ha hb
  obtain ⟨b', hb', hlt⟩ := h0 a ha
  rw [hb] at hb'
  cases hb'
  omega

theorem ms_rInstHit : ∀ fid fbs v n o ts d us w r : Pattern,
    Meaning T (jInstArgs (cSym fid cKFvar fbs) v n o fbs ts us) → Meaning T (jShift o n v w) →
      Meaning T (jSubstTop n us w r) →
        Meaning T (jInst (cSym fid cKFvar fbs) v n o (cApp (cSym fid cKFvar fbs) ts (cAnn d cTrue)) r) := by
  intro fid' fbs v n o ts d us w r h1 h2 h3
  simp only [M_instargs, InstArgsM] at h1
  simp only [M_shift, ShiftM] at h2
  simp only [M_substtop, SubstTopM] at h3
  simp only [M_inst, InstM]
  intro fid ν vτ ω τ hfv hF hn hv ho ht
  obtain ⟨s, args, rfl, hs, rfl, -⟩ := encTerm_eq_app T.sig τ _ _ _ ht.symm
  have hsf : s = fid := encSym_inj T.sig (hs.symm.trans hF)
  subst hsf
  obtain ⟨-, -, hfbs⟩ := encSym_parts T.sig s hF
  obtain ⟨args', hia, rfl, hlen⟩ := h1 s ν vτ ω _ args hfv hF hn hv ho hfbs rfl
  obtain ⟨w', hw', rfl⟩ := h2 ω ν vτ ho hn hv
  have hlen' : args'.length = ν := by
    rw [instList_length _ _ _ _ _ _ _ _ hia, hlen, ← symArity_eq]
    exact hfv.2.2
  obtain ⟨r', hr', rfl⟩ := h3 ν args' w' hn rfl hlen' rfl
  have hisf : isFvarSym T.sig s = true := by rw [isFvarSym_eq, hfv.2.1]; rfl
  have hhas : hasFvar T.sig (.app s args) = true := by
    rw [hasFvar_app, hisf]; rfl
  refine ⟨r', ?_, rfl⟩
  simp only [instGo, hhas]
  rw [instArgs_eq, List.drop_zero, hia]
  simp only [Bool.true_eq_false, if_false, if_true]
  rw [hw']
  exact hr'

theorem ms_rInstargsNil : ∀ F v n o : Pattern, Meaning T (jInstArgs F v n o cNil cNil cNil) := by
  intro F v n o
  simp only [M_instargs, InstArgsM]
  intro fid ν vτ ω binders τs _ _ _ _ _ hbs hts
  rw [encTermList_eq_nil T.sig τs hts.symm, encNatList_eq_nil binders hbs.symm]
  exact ⟨[], by simp [instList], by rw [encTermList_nil], rfl⟩

theorem ms_rInstargsCons : ∀ F v n o b bs t ts u us k : Pattern,
    Meaning T (jNAdd o b k) → Meaning T (jNWord k) → Meaning T (jInst F v n k t u) →
      Meaning T (jInstArgs F v n o bs ts us) →
        Meaning T (jInstArgs F v n o (cCons b bs) (cCons t ts) (cCons u us)) := by
  intro F v n o b bs t ts u us k h1 h2 h3 h4
  simp only [M_nadd, NAddM] at h1
  obtain ⟨w, hw, hlt⟩ := h2
  simp only [M_inst, InstM] at h3
  simp only [M_instargs, InstArgsM] at h4
  simp only [M_instargs, InstArgsM]
  intro fid ν vτ ω binders τs hfv hF hn hv ho hbs hts
  obtain ⟨β, βs, rfl, hb, hbs'⟩ := encNatList_eq_cons binders b bs hbs.symm
  obtain ⟨τ, τs', rfl, ht, hts'⟩ := encTermList_eq_cons T.sig τs t ts hts.symm
  have hk := h1.1 ω β (decNat_of_eq ho) (decNat_of_eq hb)
  rw [hw] at hk
  cases hk
  obtain ⟨ρ, hρ, rfl⟩ := h3 fid ν vτ (ω + β) τ hfv hF hn hv (decNat_unique k _ hw) ht
  obtain ⟨ρs, hρs, rfl, hlen⟩ := h4 fid ν vτ ω βs τs' hfv hF hn hv ho hbs' hts'
  refine ⟨ρ :: ρs, ?_, by rw [encTermList_cons], by simp [hlen]⟩
  simp [instList, hlt, hρ, hρs]

end Mettapedia.Languages.VibeITP.Presentation
