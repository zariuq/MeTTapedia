import Mettapedia.Languages.VibeITP.Presentation.SoundTerms
import Mettapedia.Languages.VibeITP.Presentation.Theory

/-!
# Vibe-ITP presentation: soundness of the literal, theorem, and definition rules

Number literals, the theorem rules, and the rules checking a definition each
preserve `Meaning`.  The theorem rules for literals refer to the kernel's
built-in constants, so their soundness assumes that the signature gives the
built-ins their fixed data; the eta terms of a definition assume that free
variables bind nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-! ## Built-in constants and closed applications -/

theorem encSym_builtin {sig : Sig} (hb : BuiltinsFixed sig) (b : Builtin) :
    encSym sig (.builtin b) = patBuiltinSym b := by
  simp only [patBuiltinSym, encSym, hb b, sigOf]

theorem isFvarSym_builtin {sig : Sig} (hb : BuiltinsFixed sig) (b : Builtin) :
    isFvarSym sig (.builtin b) = false := by
  simp [isFvarSym, hb b, Builtin.info]

theorem bindersOf_builtin {sig : Sig} (hb : BuiltinsFixed sig) (b : Builtin) :
    bindersOf sig (.builtin b) = List.replicate b.arity 0 := by
  simp [bindersOf, hb b, Builtin.info]

/-- A built-in constant is recognised by its encoding in any signature. -/
theorem patBuiltinSym_eq {sig : Sig} {b : Builtin} {s : SymId}
    (h : patBuiltinSym b = encSym sig s) : s = .builtin b := by
  unfold patBuiltinSym at h
  rw [encSym_eq, encSym_eq] at h
  simp only [cSym, Pattern.apply.injEq, List.cons.injEq, true_and] at h
  exact (symNumber_inj (encNat_inj h.1)).symm

theorem depthBinders_closed (sig : Sig) :
    ∀ (bs : List Nat) (args : List Term), (∀ t ∈ args, depth sig t = 0) →
      depthBinders sig bs args = 0
  | _, [], _ => rfl
  | bs, t :: ts, h => by
      simp only [depthBinders]
      rw [h t (by simp), depthBinders_closed sig bs.tail ts (fun u hu => h u (by simp [hu]))]
      simp

theorem hasFvarList_closed (sig : Sig) :
    ∀ (args : List Term), (∀ t ∈ args, hasFvar sig t = false) → hasFvarList sig args = false
  | [], _ => hasFvarList_nil sig
  | t :: ts, h => by
      rw [hasFvarList_cons, h t (by simp),
        hasFvarList_closed sig ts (fun u hu => h u (by simp [hu]))]
      rfl

theorem depth_builtin_app (sig : Sig) (b : Builtin) (args : List Term)
    (hd : ∀ t ∈ args, depth sig t = 0) : depth sig (.app (.builtin b) args) = 0 := by
  rw [depth_app]; exact depthBinders_closed sig _ args hd

section Builtin
variable {sig : Sig} (hb : BuiltinsFixed sig)
include hb

theorem hasFvar_builtin_app (b : Builtin) (args : List Term)
    (hf : ∀ t ∈ args, hasFvar sig t = false) : hasFvar sig (.app (.builtin b) args) = false := by
  rw [hasFvar_app, isFvarSym_builtin hb, hasFvarList_closed sig args hf]; rfl

theorem encTerm_builtin_app (b : Builtin) (args : List Term)
    (hd : ∀ t ∈ args, depth sig t = 0) (hf : ∀ t ∈ args, hasFvar sig t = false) :
    encTerm sig (.app (.builtin b) args) =
      cApp (patBuiltinSym b) (encTermList sig args) patAnnClosed := by
  rw [encTerm_app', encSym_builtin hb, depthBinders_closed sig _ args hd, isFvarSym_builtin hb,
    hasFvarList_closed sig args hf]
  rfl

end Builtin

theorem depth_lit (sig : Sig) (bytes : List UInt8) : depth sig (.lit bytes) = 0 := by
  rw [depth]

theorem hasFvar_lit (sig : Sig) (bytes : List UInt8) : hasFvar sig (.lit bytes) = false := by
  rw [hasFvar]

theorem encTerm_closed1 {sig : Sig} (hb : BuiltinsFixed sig) (b : Builtin) (t : Term)
    (hd : depth sig t = 0) (hf : hasFvar sig t = false) :
    encTerm sig (.app (.builtin b) [t]) = closedApp1 (patBuiltinSym b) (encTerm sig t) := by
  rw [encTerm_builtin_app hb b [t] (by simp [hd]) (by simp [hf]), encTermList_cons,
    encTermList_nil]
  rfl

theorem encTerm_closed2 {sig : Sig} (hb : BuiltinsFixed sig) (b : Builtin) (t u : Term)
    (hdt : depth sig t = 0) (hft : hasFvar sig t = false)
    (hdu : depth sig u = 0) (hfu : hasFvar sig u = false) :
    encTerm sig (.app (.builtin b) [t, u]) =
      closedApp2 (patBuiltinSym b) (encTerm sig t) (encTerm sig u) := by
  rw [encTerm_builtin_app hb b [t, u] (by simp [hdt, hdu]) (by simp [hft, hfu]), encTermList_cons,
    encTermList_cons, encTermList_nil]
  rfl

/-! ## Number literals -/

theorem uint8_toNat_ofNat_mod (v : Nat) : (UInt8.ofNat (v % 256)).toNat = v % 256 := by
  simp only [UInt8.toNat_ofNat', Nat.reducePow]
  omega

theorem encBytes_natLiteral_small (x : Nat) (h : x < 256) :
    encBytes (natLiteral x) = cCons (encNat x) cNil := by
  have hx : (UInt8.ofNat x).toNat = x := by simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega
  simp only [natLiteral, h, if_true, encBytes_cons, hx, encBytes_nil]

theorem encBytes_leBytes_succ (w v : Nat) :
    encBytes (leBytes (w + 1) v) = cCons (encNat (v % 256)) (encBytes (leBytes w (v / 256))) := by
  simp only [leBytes, encBytes_cons, uint8_toNat_ofNat_mod]

variable (T : Theory)

theorem ms_rNatlitSmall : ∀ n p : Pattern,
    Meaning T (jNAdd n (cNPos p) patByteBound) → Meaning T (jNatLit n (cCons n cNil)) := by
  intro n p h
  simp only [M_nadd, NAddM] at h
  simp only [M_natlit, NatLitM]
  intro x hx
  obtain ⟨x', y, hx', hy, hsum⟩ := h.2 256 decNat_patByteBound
  rw [hx] at hx'
  cases hx'
  have hy1 := decPos_pos p y (by simpa using hy)
  rw [encBytes_natLiteral_small x (by omega), decNat_unique n x hx]

/-- One division step of the large literal rule. -/
theorem divmod256_step {a q r : Pattern} (h : NDivModM a patByteBound q r) {v : Nat}
    (hv : decNat a = some v) : decNat q = some (v / 256) ∧ r = encNat (v % 256) := by
  obtain ⟨u, w, hu, hw, heq, hlt⟩ := h v 256 hv decNat_patByteBound
  have hu' : u = v / 256 := by omega
  have hw' : w = v % 256 := by omega
  subst hu' hw'
  exact ⟨hu, decNat_unique r _ hw⟩

theorem ms_rNatlitLarge : ∀ n q1 q2 q3 q4 q5 q6 q7 q8 r1 r2 r3 r4 r5 r6 r7 r8 : Pattern,
    Meaning T (jNLe patByteBound n) → Meaning T (jNDivMod n patByteBound q1 r1) →
      Meaning T (jNDivMod q1 patByteBound q2 r2) → Meaning T (jNDivMod q2 patByteBound q3 r3) →
      Meaning T (jNDivMod q3 patByteBound q4 r4) → Meaning T (jNDivMod q4 patByteBound q5 r5) →
      Meaning T (jNDivMod q5 patByteBound q6 r6) → Meaning T (jNDivMod q6 patByteBound q7 r7) →
      Meaning T (jNDivMod q7 patByteBound q8 r8) →
      Meaning T (jNatLit n (cCons r1 (cCons r2 (cCons r3 (cCons r4 (cCons r5 (cCons r6
        (cCons r7 (cCons r8 cNil))))))))) := by
  intro n q1 q2 q3 q4 q5 q6 q7 q8 r1 r2 r3 r4 r5 r6 r7 r8 h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp only [M_nle, NLeM, M_ndivmod] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp only [M_natlit, NatLitM]
  intro x hx
  obtain ⟨b, hb, hle⟩ := h0 x hx
  rw [decNat_patByteBound] at hb
  cases hb
  obtain ⟨e1, rfl⟩ := divmod256_step h1 hx
  obtain ⟨e2, rfl⟩ := divmod256_step h2 e1
  obtain ⟨e3, rfl⟩ := divmod256_step h3 e2
  obtain ⟨e4, rfl⟩ := divmod256_step h4 e3
  obtain ⟨e5, rfl⟩ := divmod256_step h5 e4
  obtain ⟨e6, rfl⟩ := divmod256_step h6 e5
  obtain ⟨e7, rfl⟩ := divmod256_step h7 e6
  obtain ⟨_, rfl⟩ := divmod256_step h8 e7
  rw [natLiteral, if_neg (by omega)]
  simp only [leBytes, encBytes_cons, uint8_toNat_ofNat_mod, encBytes_nil]

/-! ## Theorems -/

theorem ms_rMp : ∀ a b ann : Pattern,
    Meaning T (jThm (cApp patImpl (cCons a (cCons b cNil)) ann)) → Meaning T (jThm a) →
      Meaning T (jThm b) := by
  intro a b ann h1 h2
  simp only [M_thm, ThmM] at h1 h2 ⊢
  obtain ⟨φ, hφ, hd⟩ := h1
  obtain ⟨s, args, rfl, hs, hargs, -⟩ := encTerm_eq_app T.sig φ _ _ _ hφ.symm
  have hsid : s = .builtin .impl := patBuiltinSym_eq hs
  subst hsid
  obtain ⟨t1, ts1, rfl, ha, hts1⟩ := encTermList_eq_cons T.sig args a _ hargs.symm
  obtain ⟨t2, ts2, rfl, hb, hts2⟩ := encTermList_eq_cons T.sig ts1 b _ hts1.symm
  have hnil := encTermList_eq_nil T.sig ts2 hts2.symm
  subst hnil
  obtain ⟨α, hα, hdα⟩ := h2
  have hαt : α = t1 := encTerm_inj T.sig (hα.symm.trans ha)
  subst hαt
  exact ⟨t2, hb, Derives.modusPonens (a := α) (b := t2) hd hdα⟩

theorem ms_rInst : ∀ phi fid fbs n v dv psi : Pattern,
    Meaning T (jThm phi) → Meaning T (jSymDecl (cSym fid cKFvar fbs)) → Meaning T (jLen fbs n) →
      Meaning T (jWf v) → Meaning T (jDepth v dv) → Meaning T (jNLe dv n) →
      Meaning T (jInst (cSym fid cKFvar fbs) v n cN0 phi psi) → Meaning T (jDepth psi cN0) →
      Meaning T (jThm psi) := by
  intro phi fid fbs n v dv psi h1 h2 h3 h4 h5 h6 h7 h8
  simp only [M_thm, ThmM, M_symdecl, M_len, LenM, M_wf, WfM, M_depth, DepthM, M_nle, NLeM,
    M_inst, InstM] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  obtain ⟨φ, rfl, hdφ⟩ := h1
  obtain ⟨sid, hsome, rfl, hkind, rfl⟩ := symDecl_inv h2
  have hk : kindOf T.sig sid = .fvar := encKind_inj hkind.symm
  obtain ⟨vτ, rfl, hwf⟩ := h4
  have hn := h3 _ (decList_encNatList _)
  rw [List.length_map] at hn
  have hdv := h5 vτ rfl
  obtain ⟨x, hx, hle⟩ := h6 _ hn
  rw [hdv, decNat_encNat] at hx
  cases hx
  have hfv : IsFvarOf T.sig sid (bindersOf T.sig sid).length :=
    ⟨hsome, hk, symArity_eq T.sig sid⟩
  obtain ⟨ψ, hinst, rfl⟩ :=
    h7 sid _ vτ 0 φ hfv (by rw [encSym_eq, hk]; rfl) (decNat_unique n _ hn) rfl rfl rfl
  have hdψ := encNat_eq_N0 (h8 ψ rfl)
  obtain ⟨info, hinfo⟩ := Option.isSome_iff_exists.mp hsome
  have hkinfo : info.kind = .fvar := by simpa [kindOf, hinfo] using hk
  have harity : (bindersOf T.sig sid).length = info.arity := by
    simp [bindersOf, hinfo, SymInfo.arity]
  refine ⟨ψ, rfl, Derives.instantiate (F := sid) hdφ hwf ?_⟩
  simp only [instantiateStatement, hinfo]
  rw [if_pos ⟨hkinfo, by rw [← harity]; exact hle⟩, ← harity, hinst]
  simp only [hdψ, if_true]

section Literals
variable {T}
variable (hb : BuiltinsFixed T.sig)
include hb

theorem encTerm_litStatement1 (b : Builtin) (bytes : List UInt8) :
    encTerm T.sig (.app (.builtin b) [.lit bytes]) =
      closedApp1 (patBuiltinSym b) (cLit (encBytes bytes)) :=
  encTerm_closed1 hb b (.lit bytes) (depth_lit _ _) (hasFvar_lit _ _)

theorem encTerm_litStatement2 (b : Builtin) (x y : List UInt8) :
    encTerm T.sig (.app (.builtin b) [.lit x, .lit y]) =
      closedApp2 (patBuiltinSym b) (cLit (encBytes x)) (cLit (encBytes y)) :=
  encTerm_closed2 hb b (.lit x) (.lit y) (depth_lit _ _) (hasFvar_lit _ _) (depth_lit _ _)
    (hasFvar_lit _ _)

/-- An equation between a closed built-in application and a literal. -/
theorem encTerm_litEquation (b : Builtin) (args : List Term) (bytes : List UInt8)
    (hd : ∀ t ∈ args, depth T.sig t = 0) (hf : ∀ t ∈ args, hasFvar T.sig t = false) :
    encTerm T.sig (.eq (.app (.builtin b) args) (.lit bytes)) =
      closedApp2 patEq (cApp (patBuiltinSym b) (encTermList T.sig args) patAnnClosed)
        (cLit (encBytes bytes)) := by
  unfold Term.eq
  rw [encTerm_closed2 hb .eq _ (.lit bytes) (depth_builtin_app T.sig b args hd)
    (hasFvar_builtin_app hb b args hf) (depth_lit _ _) (hasFvar_lit _ _),
    encTerm_builtin_app hb b args hd hf]
  rfl

theorem ms_rLitIsnat : ∀ n bn : Pattern,
    Meaning T (jNWord n) → Meaning T (jNatLit n bn) →
      Meaning T (jThm (closedApp1 (patBuiltinSym .litIsNat) (cLit bn))) := by
  intro n bn h1 h2
  obtain ⟨x, hx, hlt⟩ := h1
  simp only [M_natlit, NatLitM] at h2
  rw [h2 x hx]
  exact ⟨litIsNatStatement x, (encTerm_litStatement1 hb _ _).symm, Derives.litIsNat hlt⟩

theorem ms_rLitLt : ∀ a b ba bb : Pattern,
    Meaning T (jNLt a b) → Meaning T (jNWord b) → Meaning T (jNatLit a ba) →
      Meaning T (jNatLit b bb) →
        Meaning T (jThm (closedApp2 (patBuiltinSym .litLt) (cLit ba) (cLit bb))) := by
  intro a b ba bb h1 h2 h3 h4
  simp only [M_nlt, NLtM] at h1
  simp only [M_natlit, NatLitM] at h3 h4
  obtain ⟨y, hy, hyw⟩ := h2
  obtain ⟨x, hx, hxy⟩ := h1 y hy
  rw [h3 x hx, h4 y hy]
  exact ⟨litLtStatement x y, (encTerm_litStatement2 hb _ _ _).symm, Derives.litLt hxy hyw⟩

theorem ms_rLitAdd : ∀ a b s c ba bb bc : Pattern,
    Meaning T (jNWord a) → Meaning T (jNWord b) → Meaning T (jNAdd a b s) →
      Meaning T (jNMod64 s c) → Meaning T (jNatLit a ba) → Meaning T (jNatLit b bb) →
      Meaning T (jNatLit c bc) →
        Meaning T (jThm (closedApp2 patEq
          (closedApp2 (patBuiltinSym .litAdd) (cLit ba) (cLit bb)) (cLit bc))) := by
  intro a b s c ba bb bc h1 h2 h3 h4 h5 h6 h7
  simp only [M_nadd, NAddM] at h3
  simp only [M_nmod64, NMod64M] at h4
  simp only [M_natlit, NatLitM] at h5 h6 h7
  obtain ⟨x, hx, hxw⟩ := h1
  obtain ⟨y, hy, hyw⟩ := h2
  have hc := h4 _ (h3.1 x y hx hy)
  rw [h5 x hx, h6 y hy, h7 _ hc]
  refine ⟨litAddStatement x y, ?_, Derives.litAdd hxw hyw⟩
  unfold litAddStatement Term.natLit
  rw [encTerm_litEquation hb .litAdd _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  rfl

theorem ms_rLitMul : ∀ a b s c ba bb bc : Pattern,
    Meaning T (jNWord a) → Meaning T (jNWord b) → Meaning T (jNMul a b s) →
      Meaning T (jNMod64 s c) → Meaning T (jNatLit a ba) → Meaning T (jNatLit b bb) →
      Meaning T (jNatLit c bc) →
        Meaning T (jThm (closedApp2 patEq
          (closedApp2 (patBuiltinSym .litMul) (cLit ba) (cLit bb)) (cLit bc))) := by
  intro a b s c ba bb bc h1 h2 h3 h4 h5 h6 h7
  simp only [M_nmul, NMulM] at h3
  simp only [M_nmod64, NMod64M] at h4
  simp only [M_natlit, NatLitM] at h5 h6 h7
  obtain ⟨x, hx, hxw⟩ := h1
  obtain ⟨y, hy, hyw⟩ := h2
  have hc := h4 _ (h3.1 x y hx hy)
  rw [h5 x hx, h6 y hy, h7 _ hc]
  refine ⟨litMulStatement x y, ?_, Derives.litMul hxw hyw⟩
  unfold litMulStatement Term.natLit
  rw [encTerm_litEquation hb .litMul _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  rfl

theorem ms_rLitDiv : ∀ a b q r ba bb bq : Pattern,
    Meaning T (jNWord a) → Meaning T (jNWord b) → Meaning T (jNDivMod a b q r) →
      Meaning T (jNatLit a ba) → Meaning T (jNatLit b bb) → Meaning T (jNatLit q bq) →
        Meaning T (jThm (closedApp2 patEq
          (closedApp2 (patBuiltinSym .litDiv) (cLit ba) (cLit bb)) (cLit bq))) := by
  intro a b q r ba bb bq h1 h2 h3 h4 h5 h6
  simp only [M_ndivmod, NDivModM] at h3
  simp only [M_natlit, NatLitM] at h4 h5 h6
  obtain ⟨x, hx, hxw⟩ := h1
  obtain ⟨y, hy, hyw⟩ := h2
  obtain ⟨u, w, hu, _, heq, hlt⟩ := h3 x y hx hy
  have hy0 : y ≠ 0 := by omega
  have hdiv : x / y = u := by
    rw [heq, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt,
      Nat.zero_add]
  rw [h4 x hx, h5 y hy, h6 u hu, ← hdiv]
  refine ⟨litDivStatement x y, ?_, Derives.litDiv hxw hyw hy0⟩
  unfold litDivStatement Term.natLit
  rw [encTerm_litEquation hb .litDiv _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  rfl

theorem ms_rLitLength : ∀ bs n bn : Pattern,
    Meaning T (jWf (cLit bs)) → Meaning T (jLen bs n) → Meaning T (jNatLit n bn) →
      Meaning T (jThm (closedApp2 patEq (closedApp1 (patBuiltinSym .litLength) (cLit bs))
        (cLit bn))) := by
  intro bs n bn h1 h2 h3
  simp only [M_wf, WfM] at h1
  simp only [M_len, LenM] at h2
  simp only [M_natlit, NatLitM] at h3
  obtain ⟨τ, hτ, hwf⟩ := h1
  obtain ⟨bytes, rfl, rfl⟩ := encTerm_eq_lit T.sig τ bs hτ.symm
  have hn := h2 _ (decList_encBytes bytes)
  rw [List.length_map] at hn
  rw [h3 _ hn]
  refine ⟨litLengthStatement bytes, ?_, Derives.litLength hwf⟩
  unfold litLengthStatement Term.natLit
  rw [encTerm_litEquation hb .litLength _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  rfl

theorem ms_rLitGet : ∀ bs i xx bi bx : Pattern,
    Meaning T (jWf (cLit bs)) → Meaning T (jNth bs i xx) → Meaning T (jNatLit i bi) →
      Meaning T (jNatLit xx bx) →
        Meaning T (jThm (closedApp2 patEq
          (closedApp2 (patBuiltinSym .litGet) (cLit bs) (cLit bi)) (cLit bx))) := by
  intro bs i xx bi bx h1 h2 h3 h4
  simp only [M_wf, WfM] at h1
  simp only [M_nth, NthM] at h2
  simp only [M_natlit, NatLitM] at h3 h4
  obtain ⟨τ, hτ, hwf⟩ := h1
  obtain ⟨bytes, rfl, rfl⟩ := encTerm_eq_lit T.sig τ bs hτ.symm
  obtain ⟨k, hk, hx⟩ := h2 _ (decList_encBytes bytes)
  rw [List.getElem?_map, Option.map_eq_some_iff] at hx
  obtain ⟨byte, hbyte, rfl⟩ := hx
  have hklt : k < bytes.length := (List.getElem?_eq_some_iff.mp hbyte).1
  have hget : (bytes.getD k 0) = byte := by
    rw [List.getD_eq_getElem?_getD, hbyte, Option.getD_some]
  rw [h3 k hk, h4 _ (decNat_encNat _)]
  refine ⟨litGetStatement bytes k, ?_, Derives.litGet hwf hklt⟩
  unfold litGetStatement Term.natLit
  rw [hget, encTerm_litEquation hb .litGet _ _ (by simp [depth_lit]) (by simp [hasFvar_lit])]
  rfl

end Literals

end Mettapedia.Languages.VibeITP.Presentation
