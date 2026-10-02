import Mettapedia.Languages.VibeITP.Presentation.SpecFacts

/-!
# Vibe-ITP presentation: meanings of the kernel judgments

Each judgment is read against the specification.  Arithmetic judgments are
read in the modes in which the rules use them: addition, successor, and
multiplication of positive numerals determine their output from their inputs
and their inputs from their output; order judgments recover the smaller
number from the larger.  Term judgments are read relative to a theory's
signature: whenever the input positions are encodings of specification data,
the output position is the encoding of what the specification computes, and
the specification function succeeds.  `VThm` means derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-! ## Arithmetic -/

def PSuccM (p q : Pattern) : Prop :=
  (∀ x, decPos p = some x → decPos q = some (x + 1)) ∧
    (∀ y, decPos q = some y → ∃ x, decPos p = some x ∧ y = x + 1)

def PAddM (p q r : Pattern) : Prop :=
  (∀ x y, decPos p = some x → decPos q = some y → decPos r = some (x + y)) ∧
    (∀ z, decPos r = some z → ∃ x y, decPos p = some x ∧ decPos q = some y ∧ z = x + y)

def PAddCM (p q r : Pattern) : Prop :=
  (∀ x y, decPos p = some x → decPos q = some y → decPos r = some (x + y + 1)) ∧
    (∀ z, decPos r = some z → ∃ x y, decPos p = some x ∧ decPos q = some y ∧ z = x + y + 1)

def NAddM (a b c : Pattern) : Prop :=
  (∀ x y, decNat a = some x → decNat b = some y → decNat c = some (x + y)) ∧
    (∀ z, decNat c = some z → ∃ x y, decNat a = some x ∧ decNat b = some y ∧ z = x + y)

def NLtM (a b : Pattern) : Prop :=
  ∀ y, decNat b = some y → ∃ x, decNat a = some x ∧ x < y

def NLeM (a b : Pattern) : Prop :=
  ∀ y, decNat b = some y → ∃ x, decNat a = some x ∧ x ≤ y

def PMulM (p q r : Pattern) : Prop :=
  (∀ x y, decPos p = some x → decPos q = some y → decPos r = some (x * y)) ∧
    (∀ z, decPos r = some z → ∃ x y, decPos p = some x ∧ decPos q = some y ∧ z = x * y)

def NMulM (a b c : Pattern) : Prop :=
  (∀ x y, decNat a = some x → decNat b = some y → decNat c = some (x * y)) ∧
    (∀ z x, decNat c = some z → decNat a = some x →
      x = 0 ∨ ∃ y, decNat b = some y ∧ z = x * y)

def NDivModM (a b q r : Pattern) : Prop :=
  ∀ x y, decNat a = some x → decNat b = some y →
    ∃ u v, decNat q = some u ∧ decNat r = some v ∧ x = y * u + v ∧ v < y

def NMod64M (a c : Pattern) : Prop :=
  ∀ x, decNat a = some x → decNat c = some (x % wordBound)

def PBitsM (p u : Pattern) : Prop :=
  ∃ x, decPos p = some x ∧ ∀ k, decUnary u = some k → x < 2 ^ k

def NWordM (a : Pattern) : Prop :=
  ∃ x, decNat a = some x ∧ x < wordBound

def NMonusM (a b c : Pattern) : Prop :=
  ∀ x y, decNat a = some x → decNat b = some y → decNat c = some (x - y)

def NMaxM (a b c : Pattern) : Prop :=
  ∀ x y, decNat a = some x → decNat b = some y → decNat c = some (max x y)

def BOrM (x y z : Pattern) : Prop :=
  ∃ bx byy, decBool x = some bx ∧ decBool y = some byy ∧ decBool z = some (bx || byy)

/-! ## Lists -/

def LenM (xs n : Pattern) : Prop :=
  ∀ l, decList xs = some l → decNat n = some l.length

def NthM (xs i x : Pattern) : Prop :=
  ∀ l, decList xs = some l → ∃ k, decNat i = some k ∧ l[k]? = some x

def BytesM (xs : Pattern) : Prop :=
  ∃ bytes : List UInt8, xs = encBytes bytes

/-! ## Terms -/

def SymDeclM (sig : Sig) (s : Pattern) : Prop :=
  ∃ sid, (sig sid).isSome ∧ s = encSym sig sid

def WfM (sig : Sig) (t : Pattern) : Prop :=
  ∃ τ, t = encTerm sig τ ∧ WellFormed sig τ = true

def WfArgsM (sig : Sig) (bs ts d f : Pattern) : Prop :=
  ∀ binders, bs = encNatList binders →
    ∃ args, ts = encTermList sig args ∧ WellFormedList sig args = true ∧
      args.length = binders.length ∧ d = encNat (depthBinders sig binders args) ∧
      f = encBool (hasFvarList sig args)

def KindFvM (k f g : Pattern) : Prop :=
  (k = cKConst ∧ g = f) ∨ (k = cKFvar ∧ g = cTrue)

def DepthM (sig : Sig) (t d : Pattern) : Prop :=
  ∀ τ, t = encTerm sig τ → d = encNat (depth sig τ)

def HasFvM (sig : Sig) (t f : Pattern) : Prop :=
  ∀ τ, t = encTerm sig τ → f = encBool (hasFvar sig τ)

def AnnArgsM (sig : Sig) (bs ts d f : Pattern) : Prop :=
  ∀ binders args, bs = encNatList binders → ts = encTermList sig args →
    d = encNat (depthBinders sig binders args) ∧ f = encBool (hasFvarList sig args)

/-! ## Operations -/

def ShiftM (sig : Sig) (a c t u : Pattern) : Prop :=
  ∀ α γ τ, a = encNat α → c = encNat γ → t = encTerm sig τ →
    ∃ τ', shift sig α γ τ = some τ' ∧ u = encTerm sig τ'

def ShiftArgsM (sig : Sig) (a c bs ts us : Pattern) : Prop :=
  ∀ α γ binders args, a = encNat α → c = encNat γ → bs = encNatList binders →
    ts = encTermList sig args →
      ∃ args', shiftList sig α γ binders args = some args' ∧ us = encTermList sig args'

def SubstM (sig : Sig) (n args o t u : Pattern) : Prop :=
  ∀ ν As ω τ, n = encNat ν → args = encTermList sig As → As.length = ν →
    o = encNat ω → t = encTerm sig τ →
      ∃ τ', substGo sig ν As ω τ = some τ' ∧ u = encTerm sig τ'

def SubstArgsM (sig : Sig) (n args o bs ts us : Pattern) : Prop :=
  ∀ ν As ω binders τs, n = encNat ν → args = encTermList sig As → As.length = ν →
    o = encNat ω → bs = encNatList binders → ts = encTermList sig τs →
      ∃ τs', substList sig ν As ω binders τs = some τs' ∧ us = encTermList sig τs'

def SubstTopM (sig : Sig) (n args t u : Pattern) : Prop :=
  ∀ ν As τ, n = encNat ν → args = encTermList sig As → As.length = ν →
    t = encTerm sig τ →
      ∃ τ', substBVars sig ν As τ 0 = some τ' ∧ u = encTerm sig τ'

/-- A free-variable symbol of the signature, with its arity. -/
def IsFvarOf (sig : Sig) (fid : SymId) (ν : Nat) : Prop :=
  (sig fid).isSome ∧ kindOf sig fid = .fvar ∧ symArity sig fid = ν

def InstM (sig : Sig) (F v n o t u : Pattern) : Prop :=
  ∀ fid ν vτ ω τ, IsFvarOf sig fid ν → F = encSym sig fid → n = encNat ν →
    v = encTerm sig vτ → o = encNat ω → t = encTerm sig τ →
      ∃ τ', instGo sig fid ν vτ ω τ = some τ' ∧ u = encTerm sig τ'

def InstArgsM (sig : Sig) (F v n o bs ts us : Pattern) : Prop :=
  ∀ fid ν vτ ω binders τs, IsFvarOf sig fid ν → F = encSym sig fid → n = encNat ν →
    v = encTerm sig vτ → o = encNat ω → bs = encNatList binders →
    ts = encTermList sig τs →
      ∃ τs', instList sig fid ν vτ ω binders τs = some τs' ∧
        us = encTermList sig τs' ∧ τs.length = binders.length

/-! ## Literals and definitions -/

def NatLitM (n bytes : Pattern) : Prop :=
  ∀ x, decNat n = some x → bytes = encBytes (natLiteral x)

def encSymList (sig : Sig) (fids : List SymId) : Pattern := encList (fids.map (encSym sig))

def AritiesM (sig : Sig) (fs bs : Pattern) : Prop :=
  ∃ fids : List SymId, fs = encSymList sig fids ∧
    (∀ f ∈ fids, (sig f).isSome ∧ kindOf sig f = .fvar) ∧
    bs = encNatList (fids.map (symArity sig))

def HintsInM (hs n : Pattern) : Prop :=
  ∀ ν, decNat n = some ν → ∃ l : List Nat, hs = encNatList l ∧ ∀ h ∈ l, h < ν

def OccM (sig : Sig) (fs t hs rest : Pattern) : Prop :=
  ∀ fids τ hl, fs = encSymList sig fids → t = encTerm sig τ → hs = encNatList hl →
    ∃ rl, consumeHints fids (fvarOccurrences sig τ) hl = some rl ∧ rest = encNatList rl

def OccArgsM (sig : Sig) (fs ts hs rest : Pattern) : Prop :=
  ∀ fids τs hl, fs = encSymList sig fids → ts = encTermList sig τs → hs = encNatList hl →
    ∃ rl, consumeHints fids (fvarOccurrencesList sig τs) hl = some rl ∧ rest = encNatList rl

def DescBVarsM (sig : Sig) (n vars : Pattern) : Prop :=
  ∀ ν, decNat n = some ν → vars = encTermList sig ((List.range ν).reverse.map Term.bvar)

def EtasM (sig : Sig) (fs etas : Pattern) : Prop :=
  ∀ fids, fs = encSymList sig fids → (∀ f ∈ fids, (sig f).isSome ∧ kindOf sig f = .fvar) →
    etas = encTermList sig (fids.map fun F => etaFvar F (symArity sig F))

def DefStmtM (sig : Sig) (c fs hs v stmt : Pattern) : Prop :=
  ∀ fids hl vτ, fs = encSymList sig fids → hs = encNatList hl → v = encTerm sig vτ →
    definitionAdmissible sig fids hl vτ = true ∧
      ∀ cs, c = encSym sig cs → sig cs = some (definitionInfo sig fids) →
        stmt = encTerm sig (definitionStatement sig cs fids vτ)

/-! ## Theorems -/

def ThmM (T : Theory) (P : Pattern) : Prop :=
  ∃ φ, P = encTerm T.sig φ ∧ Derives T φ

/-! ## Dispatch -/

def Meaning (T : Theory) : Pattern → Prop
  | .apply "VPSucc" [p, q] => PSuccM p q
  | .apply "VPAdd" [p, q, r] => PAddM p q r
  | .apply "VPAddC" [p, q, r] => PAddCM p q r
  | .apply "VNAdd" [a, b, c] => NAddM a b c
  | .apply "VNLt" [a, b] => NLtM a b
  | .apply "VNLe" [a, b] => NLeM a b
  | .apply "VPMul" [p, q, r] => PMulM p q r
  | .apply "VNMul" [a, b, c] => NMulM a b c
  | .apply "VNDivMod" [a, b, q, r] => NDivModM a b q r
  | .apply "VNMod64" [a, c] => NMod64M a c
  | .apply "VPBits" [p, u] => PBitsM p u
  | .apply "VNWord" [a] => NWordM a
  | .apply "VNMonus" [a, b, c] => NMonusM a b c
  | .apply "VNMax" [a, b, c] => NMaxM a b c
  | .apply "VBOr" [x, y, z] => BOrM x y z
  | .apply "VLen" [xs, n] => LenM xs n
  | .apply "VNth" [xs, i, x] => NthM xs i x
  | .apply "VBytes" [xs] => BytesM xs
  | .apply "VSymDecl" [s] => SymDeclM T.sig s
  | .apply "VWf" [t] => WfM T.sig t
  | .apply "VWfArgs" [bs, ts, d, f] => WfArgsM T.sig bs ts d f
  | .apply "VKindFv" [k, f, g] => KindFvM k f g
  | .apply "VDepth" [t, d] => DepthM T.sig t d
  | .apply "VHasFv" [t, f] => HasFvM T.sig t f
  | .apply "VAnnArgs" [bs, ts, d, f] => AnnArgsM T.sig bs ts d f
  | .apply "VShift" [a, c, t, u] => ShiftM T.sig a c t u
  | .apply "VShiftArgs" [a, c, bs, ts, us] => ShiftArgsM T.sig a c bs ts us
  | .apply "VSubst" [n, args, o, t, u] => SubstM T.sig n args o t u
  | .apply "VSubstArgs" [n, args, o, bs, ts, us] => SubstArgsM T.sig n args o bs ts us
  | .apply "VSubstTop" [n, args, t, u] => SubstTopM T.sig n args t u
  | .apply "VInst" [F, v, n, o, t, u] => InstM T.sig F v n o t u
  | .apply "VInstArgs" [F, v, n, o, bs, ts, us] => InstArgsM T.sig F v n o bs ts us
  | .apply "VNatLit" [n, bytes] => NatLitM n bytes
  | .apply "VArities" [fs, bs] => AritiesM T.sig fs bs
  | .apply "VHintsIn" [hs, n] => HintsInM hs n
  | .apply "VOcc" [fs, t, hs, rest] => OccM T.sig fs t hs rest
  | .apply "VOccArgs" [fs, ts, hs, rest] => OccArgsM T.sig fs ts hs rest
  | .apply "VEtas" [fs, etas] => EtasM T.sig fs etas
  | .apply "VDescBVars" [n, vars] => DescBVarsM T.sig n vars
  | .apply "VDefStmt" [c, fs, hs, v, stmt] => DefStmtM T.sig c fs hs v stmt
  | .apply "VThm" [φ] => ThmM T φ
  | _ => True

section Unfold
variable (T : Theory)
@[simp] theorem M_psucc (p q : Pattern) : Meaning T (jPSucc p q) = PSuccM p q := rfl
@[simp] theorem M_padd (p q r : Pattern) : Meaning T (jPAdd p q r) = PAddM p q r := rfl
@[simp] theorem M_paddc (p q r : Pattern) : Meaning T (jPAddC p q r) = PAddCM p q r := rfl
@[simp] theorem M_nadd (a b c : Pattern) : Meaning T (jNAdd a b c) = NAddM a b c := rfl
@[simp] theorem M_nlt (a b : Pattern) : Meaning T (jNLt a b) = NLtM a b := rfl
@[simp] theorem M_nle (a b : Pattern) : Meaning T (jNLe a b) = NLeM a b := rfl
@[simp] theorem M_pmul (p q r : Pattern) : Meaning T (jPMul p q r) = PMulM p q r := rfl
@[simp] theorem M_nmul (a b c : Pattern) : Meaning T (jNMul a b c) = NMulM a b c := rfl
@[simp] theorem M_ndivmod (a b q r : Pattern) :
    Meaning T (jNDivMod a b q r) = NDivModM a b q r := rfl
@[simp] theorem M_nmod64 (a c : Pattern) : Meaning T (jNMod64 a c) = NMod64M a c := rfl
@[simp] theorem M_pbits (p u : Pattern) : Meaning T (jPBits p u) = PBitsM p u := rfl
@[simp] theorem M_nword (a : Pattern) : Meaning T (jNWord a) = NWordM a := rfl
@[simp] theorem M_nmonus (a b c : Pattern) : Meaning T (jNMonus a b c) = NMonusM a b c := rfl
@[simp] theorem M_nmax (a b c : Pattern) : Meaning T (jNMax a b c) = NMaxM a b c := rfl
@[simp] theorem M_bor (x y z : Pattern) : Meaning T (jBOr x y z) = BOrM x y z := rfl
@[simp] theorem M_len (xs n : Pattern) : Meaning T (jLen xs n) = LenM xs n := rfl
@[simp] theorem M_nth (xs i x : Pattern) : Meaning T (jNth xs i x) = NthM xs i x := rfl
@[simp] theorem M_bytes (xs : Pattern) : Meaning T (jBytes xs) = BytesM xs := rfl
@[simp] theorem M_symdecl (s : Pattern) : Meaning T (jSymDecl s) = SymDeclM T.sig s := rfl
@[simp] theorem M_wf (t : Pattern) : Meaning T (jWf t) = WfM T.sig t := rfl
@[simp] theorem M_wfargs (bs ts d f : Pattern) :
    Meaning T (jWfArgs bs ts d f) = WfArgsM T.sig bs ts d f := rfl
@[simp] theorem M_kindfv (k f g : Pattern) : Meaning T (jKindFv k f g) = KindFvM k f g := rfl
@[simp] theorem M_depth (t d : Pattern) : Meaning T (jDepth t d) = DepthM T.sig t d := rfl
@[simp] theorem M_hasfv (t f : Pattern) : Meaning T (jHasFv t f) = HasFvM T.sig t f := rfl
@[simp] theorem M_annargs (bs ts d f : Pattern) :
    Meaning T (jAnnArgs bs ts d f) = AnnArgsM T.sig bs ts d f := rfl
@[simp] theorem M_shift (a c t u : Pattern) : Meaning T (jShift a c t u) = ShiftM T.sig a c t u :=
  rfl
@[simp] theorem M_shiftargs (a c bs ts us : Pattern) :
    Meaning T (jShiftArgs a c bs ts us) = ShiftArgsM T.sig a c bs ts us := rfl
@[simp] theorem M_subst (n args o t u : Pattern) :
    Meaning T (jSubst n args o t u) = SubstM T.sig n args o t u := rfl
@[simp] theorem M_substargs (n args o bs ts us : Pattern) :
    Meaning T (jSubstArgs n args o bs ts us) = SubstArgsM T.sig n args o bs ts us := rfl
@[simp] theorem M_substtop (n args t u : Pattern) :
    Meaning T (jSubstTop n args t u) = SubstTopM T.sig n args t u := rfl
@[simp] theorem M_inst (F v n o t u : Pattern) :
    Meaning T (jInst F v n o t u) = InstM T.sig F v n o t u := rfl
@[simp] theorem M_instargs (F v n o bs ts us : Pattern) :
    Meaning T (jInstArgs F v n o bs ts us) = InstArgsM T.sig F v n o bs ts us := rfl
@[simp] theorem M_natlit (n bytes : Pattern) : Meaning T (jNatLit n bytes) = NatLitM n bytes :=
  rfl
@[simp] theorem M_arities (fs bs : Pattern) : Meaning T (jArities fs bs) = AritiesM T.sig fs bs :=
  rfl
@[simp] theorem M_hintsin (hs n : Pattern) : Meaning T (jHintsIn hs n) = HintsInM hs n := rfl
@[simp] theorem M_occ (fs t hs rest : Pattern) :
    Meaning T (jOcc fs t hs rest) = OccM T.sig fs t hs rest := rfl
@[simp] theorem M_occargs (fs ts hs rest : Pattern) :
    Meaning T (jOccArgs fs ts hs rest) = OccArgsM T.sig fs ts hs rest := rfl
@[simp] theorem M_etas (fs etas : Pattern) : Meaning T (jEtas fs etas) = EtasM T.sig fs etas := rfl
@[simp] theorem M_descbvars (n vars : Pattern) :
    Meaning T (jDescBVars n vars) = DescBVarsM T.sig n vars := rfl
@[simp] theorem M_defstmt (c fs hs v stmt : Pattern) :
    Meaning T (jDefStmt c fs hs v stmt) = DefStmtM T.sig c fs hs v stmt := rfl
@[simp] theorem M_thm (φ : Pattern) : Meaning T (jThm φ) = ThmM T φ := rfl
end Unfold

end Mettapedia.Languages.VibeITP.Presentation
