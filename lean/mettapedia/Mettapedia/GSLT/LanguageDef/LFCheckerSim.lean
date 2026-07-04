/-
# LF checker simulation surface

This layer fixes the verdict relation used by E2c-2 and seals the composed
parser-plus-checker corpus against the E2c-1 reference checker.  The universal
fuel-existence theorem is the next proof layer over these definitions.
-/
import Mettapedia.GSLT.LanguageDef.LFCheckerEncoding
import MeTTaILProofs.DecEq

namespace Mettapedia.GSLT.LanguageDef.LFCheckerSim

open MeTTaIL
open Mettapedia.GSLT.LanguageDef.LFEnc
open Mettapedia.GSLT.LanguageDef.LFCheckerEncoding
open Mettapedia.GSLT.LanguageDef.LFEngineCorr (encTerm)

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

/-- Reference pipeline: parser success is followed by the E2c-1 checker; parser failure rejects. -/
def referencePipeline (toks : List LF.Tok) (A : LF.Term) : Option Bool :=
  (LF.recognize 64 toks).bind fun t =>
    some (LFTyping.check checkerFuel LFTyping.corpusSig [] t A)

/-- Engine verdict agreement for checker runs: only `checkOk` is accepting. -/
inductive MatchesCheckVerdict : Option Bool -> AST -> Prop where
  | accept {v} : v = checkOk -> MatchesCheckVerdict (some true) v
  | rejectFalse {v e} : v = checkErr e -> MatchesCheckVerdict (some false) v
  | rejectParse {v e} : v = checkErr e -> MatchesCheckVerdict none v

inductive EngineAccepts (toks : List LF.Tok) (A : LF.Term) : Prop where
  | intro {N} :
      eval pTC N (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks) (encTy A)) = checkOk ->
      EngineAccepts toks A

inductive MatchesBool : Bool -> AST -> Prop where
  | yes {v : AST} : v = ttrue -> MatchesBool true v
  | no {v : AST} : v = ffalse -> MatchesBool false v

/-! ## Boundary dispatch facts for the composed presentation. -/

theorem os_lfcheck_tc (toks A : AST) :
    oneStep pTC (lfcheck toks A) = some (lfcheckK A (lfrec toks)) := by
  rfl

theorem os_lfcheckK_err_tc (A e : AST) :
    oneStep pTC (lfcheckK A (Err e)) = some (checkErr e) := by
  rfl

theorem os_lfcheckK_ok_tc (A raw : AST) :
    oneStep pTC (lfcheckK A (Ok raw)) = some (lfcheckI A (internTerm raw)) := by
  rfl

theorem os_lfcheckI_bad_type_tc (t : AST) :
    oneStep pTC (lfcheckI checkBad (someT t)) = some (checkErr (con0 "unknown-type-name")) := by
  rfl

theorem os_verdict_true_tc :
    oneStep pTC (verdict ttrue) = some checkOk := by
  rfl

theorem os_verdict_false_tc :
    oneStep pTC (verdict ffalse) = some (checkErr (con0 "type-reject")) := by
  rfl

theorem os_lfrec_tc (toks : AST) :
    oneStep pTC (lfrec toks) = some (recK (tm (peano 64) Nil toks)) := by
  rfl

theorem os_recK_err_tc (e : AST) :
    oneStep pTC (recK (PErr e)) = some (Err e) := by
  rfl

theorem os_recK_p_nil_tc (t : AST) :
    oneStep pTC (recK (Pp t Nil)) = some (Ok t) := by
  rfl

theorem os_recK_p_cons_tc (t h r : AST) :
    oneStep pTC (recK (Pp t (Cons h r))) = some (Err (extraToks (Cons h r))) := by
  rfl

theorem isnormal_checkOk_tc : IsNormal pTC checkOk := by
  rfl

/-! ## Checker-core leaves. -/

theorem verdict_true_matches :
    MatchesCheckVerdict (some true) (eval pTC 1 (verdict ttrue)) := by
  exact MatchesCheckVerdict.accept rfl

theorem verdict_false_matches :
    MatchesCheckVerdict (some false) (eval pTC 1 (verdict ffalse)) := by
  exact MatchesCheckVerdict.rejectFalse rfl

theorem verdict_matches_bool {b : Bool} {v : AST} (h : MatchesBool b v) :
    MatchesCheckVerdict (some b) (eval pTC 1 (verdict v)) := by
  cases h with
  | yes hv =>
      subst v
      exact verdict_true_matches
  | no hv =>
      subst v
      exact verdict_false_matches

theorem checkT_z_tc (ctx t A : AST) :
    eval pTC 1 (checkT Z ctx t A) = ffalse := by
  rfl

theorem checkT_s_tc (f ctx t A : AST) :
    eval pTC 1 (checkT (S f) ctx t A) = checkK f A (inferT f ctx t) := by
  rfl

theorem checkK_ok_tc (f A B : AST) :
    eval pTC 1 (checkK f A (someT B)) = convT f B A := by
  rfl

theorem checkK_bad_tc (f A : AST) :
    eval pTC 1 (checkK f A checkBad) = ffalse := by
  rfl

theorem os_lt_ss_tc (x y : AST) :
    oneStep pTC (ltT (S x) (S y)) = some (ltT x y) := by
  rfl

theorem os_lt_zs_tc (y : AST) :
    oneStep pTC (ltT Z (S y)) = some (con0 "tt") := by
  rfl

theorem os_lt_zz_tc :
    oneStep pTC (ltT Z Z) = some (con0 "ff") := by
  rfl

theorem os_lt_sz_tc (x : AST) :
    oneStep pTC (ltT (S x) Z) = some (con0 "ff") := by
  rfl

theorem sig_prop_engine_tc : eval pTC 1 (sigTCall nProp) = someT (Srt typeS) := by
  rfl

theorem sig_nat_engine_tc : eval pTC 1 (sigTCall nNat) = someT (Srt typeS) := by
  rfl

theorem sig_A_engine_tc : eval pTC 1 (sigTCall nA) = someT iPropT := by
  rfl

theorem sig_B_engine_tc : eval pTC 1 (sigTCall nB) = someT iPropT := by
  rfl

theorem sig_z_engine_tc : eval pTC 1 (sigTCall nZ) = someT iNatT := by
  rfl

theorem sig_prf_engine_tc : eval pTC 1 (sigTCall nPrf) = someT (Pi iPropT (Srt typeS)) := by
  rfl

theorem sig_imp_engine_tc : eval pTC 1 (sigTCall nImp) = someT (Pi iPropT (Pi iPropT iPropT)) := by
  rfl

theorem sig_eqn_engine_tc : eval pTC 1 (sigTCall nEqn) =
    someT (Pi iNatT (Pi iNatT (Srt typeS))) := by
  rfl

theorem sig_rfl_engine_tc : eval pTC 1 (sigTCall nRfl) =
    someT (Pi iNatT (iEqn (Var Z) (Var Z))) := by
  rfl

theorem sig_hImpAB_engine_tc : eval pTC 1 (sigTCall nHImpAB) = someT (iPrf iImpAB) := by
  rfl

theorem sig_hA_engine_tc : eval pTC 1 (sigTCall nHA) = someT (iPrf iA) := by
  rfl

theorem sig_mpAB_engine_tc : eval pTC 1 (sigTCall nMpAB) =
    someT (Pi (iPrf iImpAB) (Pi (iPrf iA) (iPrf iB))) := by
  rfl

theorem infer_z_tc (ctx t : AST) :
    eval pTC 1 (inferT Z ctx t) = checkBad := by
  rfl

theorem infer_type_tc (f ctx : AST) :
    eval pTC 1 (inferT (S f) ctx (Srt typeS)) = someT (Srt kindS) := by
  rfl

theorem infer_kind_tc (f ctx : AST) :
    eval pTC 1 (inferT (S f) ctx (Srt kindS)) = checkBad := by
  rfl

theorem infer_con_prop_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nProp)) = someT (Srt typeS) := by
  rfl

theorem infer_con_nat_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nNat)) = someT (Srt typeS) := by
  rfl

theorem infer_con_A_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nA)) = someT iPropT := by
  rfl

theorem infer_con_B_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nB)) = someT iPropT := by
  rfl

theorem infer_con_z_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nZ)) = someT iNatT := by
  rfl

theorem infer_con_prf_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nPrf)) = someT (Pi iPropT (Srt typeS)) := by
  rfl

theorem infer_con_imp_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nImp)) = someT (Pi iPropT (Pi iPropT iPropT)) := by
  rfl

theorem infer_con_eqn_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nEqn)) =
      someT (Pi iNatT (Pi iNatT (Srt typeS))) := by
  rfl

theorem infer_con_rfl_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nRfl)) =
      someT (Pi iNatT (iEqn (Var Z) (Var Z))) := by
  rfl

theorem infer_con_hImpAB_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nHImpAB)) = someT (iPrf iImpAB) := by
  rfl

theorem infer_con_hA_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nHA)) = someT (iPrf iA) := by
  rfl

theorem infer_con_mpAB_tc (f ctx : AST) :
    eval pTC 2 (inferT (S f) ctx (Con nMpAB)) =
      someT (Pi (iPrf iImpAB) (Pi (iPrf iA) (iPrf iB))) := by
  rfl

theorem addN_z_tc (m : AST) :
    eval pTC 1 (addN Z m) = m := by
  rfl

theorem addN_s_tc (n m : AST) :
    eval pTC 1 (addN (S n) m) = S (addN n m) := by
  rfl

theorem predN_z_tc :
    eval pTC 1 (predN Z) = Z := by
  rfl

theorem predN_s_tc (n : AST) :
    eval pTC 1 (predN (S n)) = n := by
  rfl

theorem liftT_var_tc (d c k : AST) :
    eval pTC 1 (liftT d c (Var k)) = liftVarT d c k (ltT k c) := by
  rfl

theorem liftVarT_lt_tc (d c k : AST) :
    eval pTC 1 (liftVarT d c k (con0 "tt")) = Var k := by
  rfl

theorem liftVarT_ge_tc (d c k : AST) :
    eval pTC 1 (liftVarT d c k (con0 "ff")) = Var (addN k d) := by
  rfl

theorem liftT_srt_tc (d c s : AST) :
    eval pTC 1 (liftT d c (Srt s)) = Srt s := by
  rfl

theorem liftT_con_tc (d c x : AST) :
    eval pTC 1 (liftT d c (Con x)) = Con x := by
  rfl

theorem liftT_pi_tc (d c A B : AST) :
    eval pTC 1 (liftT d c (Pi A B)) = Pi (liftT d c A) (liftT d (S c) B) := by
  rfl

theorem liftT_lam_tc (d c A b : AST) :
    eval pTC 1 (liftT d c (Lam A b)) = Lam (liftT d c A) (liftT d (S c) b) := by
  rfl

theorem liftT_app_tc (d c f a : AST) :
    eval pTC 1 (liftT d c (App f a)) = App (liftT d c f) (liftT d c a) := by
  rfl

theorem peano_injective : Function.Injective peano := by
  intro a b h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b =>
          unfold peano Z S con0 at h
          injection h with _ hargs
          cases hargs
  | succ a ih =>
      cases b with
      | zero =>
          unfold peano Z S con0 at h
          injection h with _ hargs
          cases hargs
      | succ b =>
          simp [peano, S] at h
          exact congrArg Nat.succ (ih h)

theorem peano_ne_of_ne {j k : Nat} (h : j ≠ k) : peano j ≠ peano k := by
  intro hp
  exact h (peano_injective hp)

theorem string_beq_self_tc (s : String) : (s == s) = true :=
  beq_iff_eq.mpr rfl

theorem dottedPath_beq_self_tc : ∀ p : DottedPath, (p == p) = true
  | .base s => by
      change (s == s) = true
      exact string_beq_self_tc s
  | .qualified s rest => by
      change ((s == s) && (rest == rest)) = true
      rw [string_beq_self_tc s, dottedPath_beq_self_tc rest]
      rfl

mutual
  theorem cat_beq_self_tc : ∀ c : Cat, (c == c) = true
    | .idCat s => by
        change (s == s) = true
        exact string_beq_self_tc s
    | .listOf c => by
        change (c == c) = true
        exact cat_beq_self_tc c
    | .arrow a b => by
        change ((a == a) && (b == b)) = true
        rw [cat_beq_self_tc a, cat_beq_self_tc b]
        rfl
    | .prod cs => by
        change Cat.beqList cs cs = true
        exact cat_beqList_self_tc cs
  theorem cat_beqList_self_tc : ∀ cs : List Cat, Cat.beqList cs cs = true
    | [] => rfl
    | c :: cs => by
        change ((c == c) && Cat.beqList cs cs) = true
        rw [cat_beq_self_tc c, cat_beqList_self_tc cs]
        rfl
end

theorem label_beq_self_tc : ∀ l : Label, (l == l) = true
  | .id s => by
      change (s == s) = true
      exact string_beq_self_tc s
  | .wild => rfl
  | .listE c => by
      change (c == c) = true
      exact cat_beq_self_tc c
  | .listCons c => by
      change (c == c) = true
      exact cat_beq_self_tc c
  | .listOne c => by
      change (c == c) = true
      exact cat_beq_self_tc c

mutual
  theorem ast_beq_self_tc : ∀ t : AST, (t == t) = true
    | .var p => by
        change (p == p) = true
        exact dottedPath_beq_self_tc p
    | .sexp l args => by
        change ((l == l) && AST.beqList args args) = true
        rw [label_beq_self_tc l, ast_beqList_self_tc args]
        rfl
    | .subst b r v => by
        change ((b == b) && (r == r) && (v == v)) = true
        rw [ast_beq_self_tc b, ast_beq_self_tc r, dottedPath_beq_self_tc v]
        rfl
  theorem ast_beqList_self_tc : ∀ ts : List AST, AST.beqList ts ts = true
    | [] => rfl
    | t :: ts => by
        change ((t == t) && AST.beqList ts ts) = true
        rw [ast_beq_self_tc t, ast_beqList_self_tc ts]
        rfl
end

theorem label_id_beq_tc (a b : String) :
    (Label.id a == Label.id b) = (a == b) := by
  rfl

theorem peano_beq_false_of_ne {j k : Nat} (h : j ≠ k) :
    (peano j == peano k) = false := by
  induction j generalizing k with
  | zero =>
      cases k with
      | zero => exact False.elim (h rfl)
      | succ k => rfl
  | succ j ih =>
      cases k with
      | zero => rfl
      | succ k =>
          change ((peano j == peano k) && true) = false
          rw [ih (by intro hk; exact h (congrArg Nat.succ hk))]
          rfl

theorem substT_var_zero_tc (s : AST) :
    eval pTC 1 (substT Z s (Var Z)) = s := by
  rfl

theorem pLF_no_substT_var_tc (j s k : AST) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var k)))
      (match pLF with
      | Presentation.mk _ _ _ r _ => r) = [] := by
  rfl

theorem arithmetic_no_substT_var_tc (j s k : AST) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var k)))
      arithmeticRules = [] := by
  rfl

theorem intern_no_substT_var_tc (j s k : AST) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var k)))
      internRules = [] := by
  rfl

theorem sig_no_substT_var_tc (j s k : AST) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var k)))
      sigRules = [] := by
  rfl

theorem nf_no_substT_var_tc (j s k : AST) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var k)))
      nfRules = [] := by
  rfl

theorem checkerCore_no_substT_var_tc (j s k : AST) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var k)))
      checkerRulesCore = [] := by
  rfl

theorem subst_var_hit_rewrite_tc (j s : AST) :
    applyBaseRewrite
      (rw "subst-var-hit" (substT (pv "j") (pv "s") (Var (pv "j"))) (pv "s"))
      (substT j s (Var j)) = some s := by
  have h_substT : (("substT" : String) == "substT") = true := by decide
  have h_Var : (("Var" : String) == "Var") = true := by decide
  have h_j_s : (("j" : String) == "s") = false := by decide
  have h_s_j : (("s" : String) == "j") = false := by decide
  have h_j_j : (("j" : String) == "j") = true := by decide
  have h_s_s : (("s" : String) == "s") = true := by decide
  simp only [applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    substT, Var, pv, AST.matchPat, AST.matchPatList, AST.inst,
    Option.bind_some, Option.map_some, List.find?, label_id_beq_tc,
    ast_beq_self_tc, h_substT, h_Var, h_j_s, h_s_j, h_j_j, h_s_s, if_true]

theorem subst_var_hit_rewrite_none_tc {j s k : AST} (hjk : (j == k) = false) :
    applyBaseRewrite
      (rw "subst-var-hit" (substT (pv "j") (pv "s") (Var (pv "j"))) (pv "s"))
      (substT j s (Var k)) = none := by
  have h_substT : (("substT" : String) == "substT") = true := by decide
  have h_Var : (("Var" : String) == "Var") = true := by decide
  have h_j_s : (("j" : String) == "s") = false := by decide
  have h_s_j : (("s" : String) == "j") = false := by decide
  have h_j_j : (("j" : String) == "j") = true := by decide
  simp only [applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    substT, Var, pv, AST.matchPat, AST.matchPatList, AST.inst,
    Option.bind_some, Option.bind_none, Option.map_none, List.find?, label_id_beq_tc,
    hjk, h_substT, h_Var, h_j_s, h_s_j, h_j_j, Bool.false_eq_true, if_true, if_false]

theorem subst_var_miss_rewrite_tc (j s k : AST) :
    applyBaseRewrite
      (rw "subst-var-miss" (substT (pv "j") (pv "s") (Var (pv "k")))
        (substVarLT (pv "j") (pv "s") (pv "k") (ltT (pv "j") (pv "k"))))
      (substT j s (Var k)) = some (substVarLT j s k (ltT j k)) := by
  have h_substT : (("substT" : String) == "substT") = true := by decide
  have h_Var : (("Var" : String) == "Var") = true := by decide
  have h_j_s : (("j" : String) == "s") = false := by decide
  have h_j_k : (("j" : String) == "k") = false := by decide
  have h_s_j : (("s" : String) == "j") = false := by decide
  have h_s_k : (("s" : String) == "k") = false := by decide
  have h_k_j : (("k" : String) == "j") = false := by decide
  have h_k_s : (("k" : String) == "s") = false := by decide
  have h_j_j : (("j" : String) == "j") = true := by decide
  have h_s_s : (("s" : String) == "s") = true := by decide
  have h_k_k : (("k" : String) == "k") = true := by decide
  simp only [applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    substT, substVarLT, ltT, Var, pv, AST.matchPat, AST.matchPatList, AST.inst,
    AST.instList, Option.bind_some, Option.map_some, List.find?, label_id_beq_tc,
    h_substT, h_Var, h_j_s, h_j_k, h_s_j, h_s_k, h_k_j, h_k_s,
    h_j_j, h_s_s, h_k_k, if_true]

theorem termOps_substT_var_self_tc (j s : AST) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var j))) termOpsRules =
      [s, substVarLT j s j (ltT j j)] := by
  have h_liftT : (("liftT" : String) == "substT") = false := by decide
  have h_liftVarT : (("liftVarT" : String) == "substT") = false := by decide
  have h_substVarLT : (("substVarLT" : String) == "substT") = false := by decide
  have h_substT : (("substT" : String) == "substT") = true := by decide
  have h_Srt : (("Srt" : String) == "Var") = false := by decide
  have h_Con : (("Con" : String) == "Var") = false := by decide
  have h_Pi : (("Pi" : String) == "Var") = false := by decide
  have h_Lam : (("Lam" : String) == "Var") = false := by decide
  have h_App : (("App" : String) == "Var") = false := by decide
  have h_j_s : (("j" : String) == "s") = false := by decide
  simp only [termOpsRules, List.filterMap_cons, List.filterMap_nil,
    subst_var_hit_rewrite_tc, subst_var_miss_rewrite_tc]
  simp only [applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    substT, Var, liftT, liftVarT, substVarLT, Srt,
    Mettapedia.GSLT.LanguageDef.LFEnc.Con, Pi, Lam, App,
    pv, AST.matchPat, AST.matchPatList, Option.bind_some, Option.bind_none,
    Option.map_none, List.find?, label_id_beq_tc,
    h_liftT, h_liftVarT, h_substVarLT, h_substT, h_Srt, h_Con, h_Pi, h_Lam, h_App,
    h_j_s, Bool.false_eq_true, if_false, if_true]

theorem termOps_substT_var_miss_tc {j s k : AST} (hjk : (j == k) = false) :
    List.filterMap (fun rd => applyBaseRewrite rd (substT j s (Var k))) termOpsRules =
      [substVarLT j s k (ltT j k)] := by
  have h_liftT : (("liftT" : String) == "substT") = false := by decide
  have h_liftVarT : (("liftVarT" : String) == "substT") = false := by decide
  have h_substVarLT : (("substVarLT" : String) == "substT") = false := by decide
  have h_substT : (("substT" : String) == "substT") = true := by decide
  have h_Srt : (("Srt" : String) == "Var") = false := by decide
  have h_Con : (("Con" : String) == "Var") = false := by decide
  have h_Pi : (("Pi" : String) == "Var") = false := by decide
  have h_Lam : (("Lam" : String) == "Var") = false := by decide
  have h_App : (("App" : String) == "Var") = false := by decide
  have h_j_s : (("j" : String) == "s") = false := by decide
  simp only [termOpsRules, List.filterMap_cons, List.filterMap_nil,
    subst_var_hit_rewrite_none_tc hjk, subst_var_miss_rewrite_tc]
  simp only [applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    substT, Var, liftT, liftVarT, substVarLT, Srt,
    Mettapedia.GSLT.LanguageDef.LFEnc.Con, Pi, Lam, App,
    pv, AST.matchPat, AST.matchPatList, Option.bind_some, Option.bind_none,
    Option.map_none, List.find?, label_id_beq_tc,
    h_liftT, h_liftVarT, h_substVarLT, h_substT, h_Srt, h_Con, h_Pi, h_Lam, h_App,
    h_j_s, Bool.false_eq_true, if_false, if_true]

theorem baseReducts_substT_var_self_tc (j s : AST) :
    baseReducts pTC (substT j s (Var j)) =
      [s, substVarLT j s j (ltT j j)] := by
  simp only [baseReducts, pTC, Presentation.rewrites, checkerRules,
    List.filterMap_append, arithmetic_no_substT_var_tc,
    intern_no_substT_var_tc, sig_no_substT_var_tc, termOps_substT_var_self_tc,
    nf_no_substT_var_tc, checkerCore_no_substT_var_tc, List.nil_append, List.append_nil]
  change [] ++ [s, substVarLT j s j (ltT j j)] =
    [s, substVarLT j s j (ltT j j)]
  rfl

theorem baseReducts_substT_var_miss_tc {j s k : AST} (hjk : (j == k) = false) :
    baseReducts pTC (substT j s (Var k)) =
      [substVarLT j s k (ltT j k)] := by
  simp only [baseReducts, pTC, Presentation.rewrites, checkerRules,
    List.filterMap_append, arithmetic_no_substT_var_tc,
    intern_no_substT_var_tc, sig_no_substT_var_tc, termOps_substT_var_miss_tc hjk,
    nf_no_substT_var_tc, checkerCore_no_substT_var_tc, List.nil_append, List.append_nil]
  change [] ++ [substVarLT j s k (ltT j k)] =
    [substVarLT j s k (ltT j k)]
  rfl

theorem os_substT_var_self_tc (j s : AST) :
    oneStep pTC (substT j s (Var j)) = some s := by
  change (match baseReducts pTC (substT j s (Var j)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "substT") args')
        (oneStepList pTC [j, s, Var j])) = some s
  rw [baseReducts_substT_var_self_tc]

theorem os_substT_var_hit_succ_tc (j : Nat) (s : AST) :
    oneStep pTC (substT (S (peano j)) s (Var (S (peano j)))) = some s := by
  exact os_substT_var_self_tc (S (peano j)) s

theorem os_substT_var_miss_ast_tc {j s k : AST} (hjk : (j == k) = false) :
    oneStep pTC (substT j s (Var k)) =
      some (substVarLT j s k (ltT j k)) := by
  change (match baseReducts pTC (substT j s (Var k)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "substT") args')
        (oneStepList pTC [j, s, Var k])) =
      some (substVarLT j s k (ltT j k))
  rw [baseReducts_substT_var_miss_tc hjk]

theorem substT_var_hit_peano_tc (j : Nat) (s : AST) :
    eval pTC 1 (substT (peano j) s (Var (peano j))) = s := by
  simp only [eval, os_substT_var_self_tc]

theorem os_substT_var_miss_tc (j k : Nat) (s : AST) (h : j ≠ k) :
    oneStep pTC (substT (peano j) s (Var (peano k))) =
      some (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k))) := by
  exact os_substT_var_miss_ast_tc (peano_beq_false_of_ne h)

theorem substVarLT_lt_tc (j s k : AST) :
    eval pTC 1 (substVarLT j s k (con0 "tt")) = Var (predN k) := by
  rfl

theorem substVarLT_ge_tc (j s k : AST) :
    eval pTC 1 (substVarLT j s k (con0 "ff")) = Var k := by
  rfl

theorem substT_srt_tc (j s u : AST) :
    eval pTC 1 (substT j s (Srt u)) = Srt u := by
  rfl

theorem substT_con_tc (j s x : AST) :
    eval pTC 1 (substT j s (Con x)) = Con x := by
  rfl

theorem substT_pi_tc (j s A B : AST) :
    eval pTC 1 (substT j s (Pi A B)) =
      Pi (substT j s A) (substT (S j) (liftT (S Z) Z s) B) := by
  rfl

theorem substT_lam_tc (j s A b : AST) :
    eval pTC 1 (substT j s (Lam A b)) =
      Lam (substT j s A) (substT (S j) (liftT (S Z) Z s) b) := by
  rfl

theorem substT_app_tc (j s f a : AST) :
    eval pTC 1 (substT j s (App f a)) = App (substT j s f) (substT j s a) := by
  rfl

theorem nfT_z_tc (t : AST) :
    eval pTC 1 (nfT Z t) = someT t := by
  rfl

theorem nfT_srt_tc (f s : AST) :
    eval pTC 1 (nfT (S f) (Srt s)) = someT (Srt s) := by
  rfl

theorem nfT_var_tc (f k : AST) :
    eval pTC 1 (nfT (S f) (Var k)) = someT (Var k) := by
  rfl

theorem nfT_con_tc (f x : AST) :
    eval pTC 1 (nfT (S f) (Con x)) = someT (Con x) := by
  rfl

theorem nfT_pi_tc (f A B : AST) :
    eval pTC 1 (nfT (S f) (Pi A B)) = nfPi1 f B (nfT f A) := by
  rfl

theorem nfT_lam_tc (f A b : AST) :
    eval pTC 1 (nfT (S f) (Lam A b)) = nfLam1 f b (nfT f A) := by
  rfl

theorem nfT_app_tc (f g a : AST) :
    eval pTC 1 (nfT (S f) (App g a)) = nfApp1 f a (nfT f g) := by
  rfl

theorem nfPi1_ok_tc (f B A : AST) :
    eval pTC 1 (nfPi1 f B (someT A)) = nfPi2 A (nfT f B) := by
  rfl

theorem nfPi2_ok_tc (A B : AST) :
    eval pTC 1 (nfPi2 A (someT B)) = someT (Pi A B) := by
  rfl

theorem nfLam1_ok_tc (f b A : AST) :
    eval pTC 1 (nfLam1 f b (someT A)) = nfLam2 A (nfT f b) := by
  rfl

theorem nfLam2_ok_tc (A b : AST) :
    eval pTC 1 (nfLam2 A (someT b)) = someT (Lam A b) := by
  rfl

theorem nfApp1_ok_tc (f a g : AST) :
    eval pTC 1 (nfApp1 f a (someT g)) = nfApp2 f g (nfT f a) := by
  rfl

theorem nfApp2_ok_tc (f g a : AST) :
    eval pTC 1 (nfApp2 f g (someT a)) = nfAppT f g a := by
  rfl

theorem nfAppT_z_tc (g a : AST) :
    eval pTC 1 (nfAppT Z g a) = someT (App g a) := by
  rfl

theorem nfAppT_beta_tc (f A body a : AST) :
    eval pTC 1 (nfAppT (S f) (Lam A body) a) = nfT f (substT Z a body) := by
  rfl

theorem nfAppT_srt_fall_tc (f s a : AST) :
    eval pTC 1 (nfAppT (S f) (Srt s) a) = someT (App (Srt s) a) := by
  rfl

theorem nfAppT_var_fall_tc (f k a : AST) :
    eval pTC 1 (nfAppT (S f) (Var k) a) = someT (App (Var k) a) := by
  rfl

theorem nfAppT_con_fall_tc (f x a : AST) :
    eval pTC 1 (nfAppT (S f) (Con x) a) = someT (App (Con x) a) := by
  rfl

theorem nfAppT_pi_fall_tc (f A B a : AST) :
    eval pTC 1 (nfAppT (S f) (Pi A B) a) = someT (App (Pi A B) a) := by
  rfl

theorem nfAppT_app_fall_tc (f g x a : AST) :
    eval pTC 1 (nfAppT (S f) (App g x) a) = someT (App (App g x) a) := by
  rfl

theorem conv_type_type_tc :
    eval pTC 8 (convT (S Z) (Srt typeS) (Srt typeS)) = ttrue := by
  rfl

theorem conv_type_kind_tc :
    eval pTC 8 (convT (S Z) (Srt typeS) (Srt kindS)) = ffalse := by
  rfl

inductive NFActiveShape : AST -> Prop where
  | nf (fuel t : AST) : NFActiveShape (nfT fuel t)
  | pi1 (fuel B s : AST) : NFActiveShape (nfPi1 fuel B s)
  | pi2 (A s : AST) : NFActiveShape (nfPi2 A s)
  | lam1 (fuel b s : AST) : NFActiveShape (nfLam1 fuel b s)
  | lam2 (A s : AST) : NFActiveShape (nfLam2 A s)
  | app1 (fuel a s : AST) : NFActiveShape (nfApp1 fuel a s)
  | app2 (fuel f s : AST) : NFActiveShape (nfApp2 fuel f s)
  | appT (fuel f a : AST) : NFActiveShape (nfAppT fuel f a)

theorem hcong_nfPi1_active_tc (fuel B : AST)
    (hfuel : IsNormal pTC fuel) (hB : IsNormal pTC B) :
    ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (nfPi1 fuel B s) = some (nfPi1 fuel B s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (nfPi1 fuel B s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hfuel hB
  change (match baseReducts pTC (nfPi1 fuel B s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfPi1") args') (oneStepList pTC [fuel, B, s])) =
      some (nfPi1 fuel B s')
  rw [hb]
  simp only [oneStepList, hfuel, hB, hstep, Option.map_some, nfPi1]

theorem hcong_nfPi2_active_tc (A : AST) (hA : IsNormal pTC A) :
    ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (nfPi2 A s) = some (nfPi2 A s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (nfPi2 A s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hA
  change (match baseReducts pTC (nfPi2 A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfPi2") args') (oneStepList pTC [A, s])) =
      some (nfPi2 A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, nfPi2]

theorem hcong_nfLam1_active_tc (fuel b : AST)
    (hfuel : IsNormal pTC fuel) (hb' : IsNormal pTC b) :
    ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (nfLam1 fuel b s) = some (nfLam1 fuel b s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (nfLam1 fuel b s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hfuel hb'
  change (match baseReducts pTC (nfLam1 fuel b s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfLam1") args') (oneStepList pTC [fuel, b, s])) =
      some (nfLam1 fuel b s')
  rw [hb]
  simp only [oneStepList, hfuel, hb', hstep, Option.map_some, nfLam1]

theorem hcong_nfLam2_active_tc (A : AST) (hA : IsNormal pTC A) :
    ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (nfLam2 A s) = some (nfLam2 A s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (nfLam2 A s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hA
  change (match baseReducts pTC (nfLam2 A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfLam2") args') (oneStepList pTC [A, s])) =
      some (nfLam2 A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, nfLam2]

theorem hcong_nfApp1_active_tc (fuel a : AST)
    (hfuel : IsNormal pTC fuel) (ha : IsNormal pTC a) :
    ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (nfApp1 fuel a s) = some (nfApp1 fuel a s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (nfApp1 fuel a s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hfuel ha
  change (match baseReducts pTC (nfApp1 fuel a s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfApp1") args') (oneStepList pTC [fuel, a, s])) =
      some (nfApp1 fuel a s')
  rw [hb]
  simp only [oneStepList, hfuel, ha, hstep, Option.map_some, nfApp1]

theorem hcong_nfApp2_active_tc (fuel f : AST)
    (hfuel : IsNormal pTC fuel) (hf : IsNormal pTC f) :
    ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (nfApp2 fuel f s) = some (nfApp2 fuel f s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (nfApp2 fuel f s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hfuel hf
  change (match baseReducts pTC (nfApp2 fuel f s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfApp2") args') (oneStepList pTC [fuel, f, s])) =
      some (nfApp2 fuel f s')
  rw [hb]
  simp only [oneStepList, hfuel, hf, hstep, Option.map_some, nfApp2]

theorem hcong_someT_tc : ∀ s s', oneStep pTC s = some s' ->
    oneStep pTC (someT s) = some (someT s') := by
  intro s s' hstep
  have hb : baseReducts pTC (someT s) = [] := rfl
  change (match baseReducts pTC (someT s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "SomeT") args') (oneStepList pTC [s])) =
      some (someT s')
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, someT]

theorem hcong_nfPi2_arg_nfT_tc (fuel B : AST) : ∀ A A',
    oneStep pTC A = some A' ->
      oneStep pTC (nfPi2 A (nfT fuel B)) = some (nfPi2 A' (nfT fuel B)) := by
  intro A A' hstep
  have hb : baseReducts pTC (nfPi2 A (nfT fuel B)) = [] := rfl
  change (match baseReducts pTC (nfPi2 A (nfT fuel B)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfPi2") args')
        (oneStepList pTC [A, nfT fuel B])) = some (nfPi2 A' (nfT fuel B))
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, nfPi2]

theorem hcong_nfLam2_arg_nfT_tc (fuel b : AST) : ∀ A A',
    oneStep pTC A = some A' ->
      oneStep pTC (nfLam2 A (nfT fuel b)) = some (nfLam2 A' (nfT fuel b)) := by
  intro A A' hstep
  have hb : baseReducts pTC (nfLam2 A (nfT fuel b)) = [] := rfl
  change (match baseReducts pTC (nfLam2 A (nfT fuel b)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfLam2") args')
        (oneStepList pTC [A, nfT fuel b])) = some (nfLam2 A' (nfT fuel b))
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, nfLam2]

theorem hcong_nfApp2_fun_nfT_tc (fuel a : AST) (hfuel : IsNormal pTC fuel) :
    ∀ f f', oneStep pTC f = some f' ->
      oneStep pTC (nfApp2 fuel f (nfT fuel a)) = some (nfApp2 fuel f' (nfT fuel a)) := by
  intro f f' hstep
  have hb : baseReducts pTC (nfApp2 fuel f (nfT fuel a)) = [] := rfl
  simp only [IsNormal] at hfuel
  change (match baseReducts pTC (nfApp2 fuel f (nfT fuel a)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfApp2") args')
        (oneStepList pTC [fuel, f, nfT fuel a])) = some (nfApp2 fuel f' (nfT fuel a))
  rw [hb]
  simp only [oneStepList, hfuel, hstep, Option.map_some, nfApp2]

theorem hcong_nfPi1_raw_nfT_arg_tc (fuel B A : AST)
    (hfuel : IsNormal pTC fuel) : ∀ B',
      oneStep pTC B = some B' ->
      oneStep pTC (nfPi1 fuel B (nfT fuel A)) = some (nfPi1 fuel B' (nfT fuel A)) := by
  intro B' hstep
  have hb : baseReducts pTC (nfPi1 fuel B (nfT fuel A)) = [] := rfl
  simp only [IsNormal] at hfuel
  change (match baseReducts pTC (nfPi1 fuel B (nfT fuel A)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfPi1") args')
        (oneStepList pTC [fuel, B, nfT fuel A])) = some (nfPi1 fuel B' (nfT fuel A))
  rw [hb]
  simp only [oneStepList, hfuel, hstep, Option.map_some, nfPi1]

theorem hcong_nfLam1_raw_nfT_arg_tc (fuel b A : AST)
    (hfuel : IsNormal pTC fuel) : ∀ b',
      oneStep pTC b = some b' ->
      oneStep pTC (nfLam1 fuel b (nfT fuel A)) = some (nfLam1 fuel b' (nfT fuel A)) := by
  intro b' hstep
  have hb : baseReducts pTC (nfLam1 fuel b (nfT fuel A)) = [] := rfl
  simp only [IsNormal] at hfuel
  change (match baseReducts pTC (nfLam1 fuel b (nfT fuel A)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfLam1") args')
        (oneStepList pTC [fuel, b, nfT fuel A])) = some (nfLam1 fuel b' (nfT fuel A))
  rw [hb]
  simp only [oneStepList, hfuel, hstep, Option.map_some, nfLam1]

theorem hcong_nfApp1_raw_nfT_arg_tc (fuel a f : AST)
    (hfuel : IsNormal pTC fuel) : ∀ a',
      oneStep pTC a = some a' ->
      oneStep pTC (nfApp1 fuel a (nfT fuel f)) = some (nfApp1 fuel a' (nfT fuel f)) := by
  intro a' hstep
  have hb : baseReducts pTC (nfApp1 fuel a (nfT fuel f)) = [] := rfl
  simp only [IsNormal] at hfuel
  change (match baseReducts pTC (nfApp1 fuel a (nfT fuel f)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfApp1") args')
        (oneStepList pTC [fuel, a, nfT fuel f])) = some (nfApp1 fuel a' (nfT fuel f))
  rw [hb]
  simp only [oneStepList, hfuel, hstep, Option.map_some, nfApp1]

theorem cong_eval_nf_active (F : AST -> AST)
    (hcong : ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pTC N s = v ->
      (∀ k, k < N -> NFActiveShape (eval pTC k s)) ->
        ∃ M, eval pTC M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v h _
      simp only [eval] at h
      subst h
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v h hguard
      simp only [eval] at h
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at h
          have hsactive : NFActiveShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguard' : ∀ k, k < n -> NFActiveShape (eval pTC k s') := by
            intro k hk
            have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
            simpa only [eval, hstep] using hguard (k + 1) hk'
          obtain ⟨M, hM⟩ := ih h hguard'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsactive hstep]
          exact hM

theorem cong_eval_nf_active_with_guard (F : AST -> AST)
    (hwrap : ∀ s, NFActiveShape s -> NFActiveShape (F s))
    (hcong : ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pTC N s = v ->
      (∀ k, k < N -> NFActiveShape (eval pTC k s)) ->
        ∃ M, eval pTC M (F s) = F v ∧
          ∀ k, k < M -> NFActiveShape (eval pTC k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v h _
      simp only [eval] at h
      subst h
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v h hguard
      simp only [eval] at h
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at h
          have hsactive : NFActiveShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguard' : ∀ k, k < n -> NFActiveShape (eval pTC k s') := by
            intro k hk
            have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
            simpa only [eval, hstep] using hguard (k + 1) hk'
          obtain ⟨M, hM, hMguard⟩ := ih h hguard'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsactive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsactive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa only [Nat.add_one] using hk)
                have htotal : eval pTC (Nat.succ k) (F s) = eval pTC k (F s') := by
                  simp only [eval, hcong s s' hsactive hstep]
                rw [htotal]
                exact hMguard k hkM

theorem cong_eval_nf_wrapper_with_guard (F : AST -> AST)
    (hwrap : ∀ s, NFActiveShape (F s))
    (hcong : ∀ s s', oneStep pTC s = some s' ->
      oneStep pTC (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pTC N s = v -> IsNormal pTC v ->
        ∃ M, eval pTC M (F s) = F v ∧
          ∀ k, k < M -> NFActiveShape (eval pTC k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v h _
      simp only [eval] at h
      subst h
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v h hv
      simp only [eval] at h
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at h
          obtain ⟨M, hM, hMguard⟩ := ih h hv
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa only [Nat.add_one] using hk)
                have htotal : eval pTC (Nat.succ k) (F s) = eval pTC k (F s') := by
                  simp only [eval, hcong s s' hstep]
                rw [htotal]
                exact hMguard k hkM

inductive FirstActiveNF (u : AST) (call : AST) : Prop where
  | intro {N : Nat} :
      eval pTC N call = someT u ->
      (∀ k, k < N -> NFActiveShape (eval pTC k call)) ->
      FirstActiveNF u call

theorem first_active_nf_one {call u : AST}
    (hstep : eval pTC 1 call = someT u) (hactive : NFActiveShape call) :
    FirstActiveNF u call := by
  refine FirstActiveNF.intro (N := 1) ?_ ?_
  · exact hstep
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simpa only [eval] using hactive

theorem first_active_nf_prepend {u call next : AST}
    (hstep : eval pTC 1 call = next) (hactive : NFActiveShape call)
    (hnext : FirstActiveNF u next) : FirstActiveNF u call := by
  cases hnext with
  | intro hmatch hguard =>
      rename_i N
      refine FirstActiveNF.intro (N := 1 + N) ?_ ?_
      · have htotal : eval pTC (1 + N) call = eval pTC N next :=
          Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans
            pTC 1 N call next (eval pTC N next) hstep rfl
        rw [htotal]
        exact hmatch
      · intro k hk
        cases k with
        | zero =>
            simpa only [eval] using hactive
        | succ k =>
            have hk' : Nat.succ k < Nat.succ N := by
              simpa only [Nat.one_add] using hk
            have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
            have htotal : eval pTC (Nat.succ k) call = eval pTC k next := by
              have h := Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans
                pTC 1 k call next (eval pTC k next) hstep rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [htotal]
            exact hguard k hkN

theorem first_active_nf_bind_active {u v call : AST}
    (F : AST -> AST)
    (hwrap : ∀ s, NFActiveShape s -> NFActiveShape (F s))
    (hcong : ∀ s s', NFActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (F s) = some (F s'))
    (hfirst : FirstActiveNF u call)
    (hend : FirstActiveNF v (F (someT u))) :
    FirstActiveNF v (F call) := by
  cases hfirst with
  | intro hchild hguard =>
      rename_i Nchild
      obtain ⟨Mctx, hMctx, hMguard⟩ :=
        cong_eval_nf_active_with_guard F hwrap hcong Nchild rfl hguard
      cases hend with
      | intro hendMatch hendGuard =>
          rename_i Nend
          refine FirstActiveNF.intro (N := Mctx + Nend) ?_ ?_
          · have hctx' : eval pTC Mctx (F call) = F (someT u) := by
              rw [hMctx, hchild]
            exact Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans
              pTC Mctx Nend _ _ _ hctx' hendMatch
          · intro k hk
            by_cases hkctx : k < Mctx
            · exact hMguard k hkctx
            · have hge : Mctx ≤ k := Nat.le_of_not_gt hkctx
              let j := k - Mctx
              have hjlt : j < Nend := by
                exact Nat.sub_lt_left_of_lt_add hge hk
              have hkdecomp : k = Mctx + j := by
                exact (Nat.add_sub_of_le hge).symm
              subst j
              rw [hkdecomp]
              have hctx' : eval pTC Mctx (F call) = F (someT u) := by
                rw [hMctx, hchild]
              have htotal : eval pTC (Mctx + (k - Mctx)) (F call)
                    = eval pTC (k - Mctx) (F (someT u)) :=
                Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans
                  pTC Mctx (k - Mctx) _ _ _ hctx' rfl
              rw [htotal]
              exact hendGuard (k - Mctx) hjlt

theorem nfT_z_first_active (t : AST) :
    FirstActiveNF t (nfT Z t) :=
  first_active_nf_one (nfT_z_tc t) (NFActiveShape.nf Z t)

theorem nfT_srt_first_active (f s : AST) :
    FirstActiveNF (Srt s) (nfT (S f) (Srt s)) :=
  first_active_nf_one (nfT_srt_tc f s) (NFActiveShape.nf (S f) (Srt s))

theorem nfT_var_first_active (f k : AST) :
    FirstActiveNF (Var k) (nfT (S f) (Var k)) :=
  first_active_nf_one (nfT_var_tc f k) (NFActiveShape.nf (S f) (Var k))

theorem nfT_con_first_active (f x : AST) :
    FirstActiveNF (Con x) (nfT (S f) (Con x)) :=
  first_active_nf_one (nfT_con_tc f x) (NFActiveShape.nf (S f) (Con x))

/-! ## Evaluation bricks for the composed presentation. -/

theorem eval_trans_tc (a b : Nat) (t u w : AST) :
    eval pTC a t = u -> eval pTC b u = w -> eval pTC (a + b) t = w :=
  Mettapedia.GSLT.LanguageDef.LFShiftSim.eval_trans pTC a b t u w

theorem eval_stable_tc {t : AST} (h : IsNormal pTC t) : ∀ N, eval pTC N t = t
  | 0 => rfl
  | n + 1 => by
      simp only [IsNormal] at h
      simp only [eval, h]

theorem cong_eval_tc (F : AST -> AST)
    (hcong : ∀ s s', oneStep pTC s = some s' -> oneStep pTC (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pTC N s = v -> IsNormal pTC v -> ∃ M, eval pTC M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst hs
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hv
      simp only [eval] at hs
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at hs
          subst hs
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          obtain ⟨M, hM⟩ := ih hs hv
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hstep]
          exact hM

inductive FirstPayloadNF (u : AST) (call : AST) : Prop where
  | intro {payload : AST} {N M : Nat} :
      eval pTC N call = someT payload ->
      (∀ k, k < N -> NFActiveShape (eval pTC k call)) ->
      eval pTC M payload = u ->
      FirstPayloadNF u call

theorem first_payload_nf_of_first_active {u call : AST}
    (hfirst : FirstActiveNF u call) : FirstPayloadNF u call := by
  cases hfirst with
  | intro hmatch hguard =>
      exact FirstPayloadNF.intro hmatch hguard (M := 0) rfl

theorem first_payload_nf_to_eval {u call : AST}
    (hfirst : FirstPayloadNF u call) (hu : IsNormal pTC u) :
    ∃ N, eval pTC N call = someT u := by
  cases hfirst with
  | @intro payload N M hmatch _ hpayload =>
      obtain ⟨Mwrap, hMwrap⟩ :=
        cong_eval_tc (fun s => someT s) hcong_someT_tc M hpayload hu
      refine ⟨N + Mwrap, ?_⟩
      exact eval_trans_tc N Mwrap _ _ _ hmatch hMwrap

theorem first_payload_nf_prepend {u call next : AST}
    (hstep : eval pTC 1 call = next) (hactive : NFActiveShape call)
    (hnext : FirstPayloadNF u next) : FirstPayloadNF u call := by
  cases hnext with
  | @intro payload N M hmatch hguard hpayload =>
      refine FirstPayloadNF.intro (payload := payload) (N := 1 + N) (M := M) ?_ ?_ hpayload
      · have htotal : eval pTC (1 + N) call = eval pTC N next :=
          eval_trans_tc 1 N call next (eval pTC N next) hstep rfl
        rw [htotal]
        exact hmatch
      · intro k hk
        cases k with
        | zero =>
            simpa only [eval] using hactive
        | succ k =>
            have hk' : Nat.succ k < Nat.succ N := by
              simpa only [Nat.one_add] using hk
            have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
            have htotal : eval pTC (Nat.succ k) call = eval pTC k next := by
              have h := eval_trans_tc 1 k call next (eval pTC k next) hstep rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [htotal]
            exact hguard k hkN

theorem nfT_z_first_payload {t u : AST}
    (h : ∃ M, eval pTC M t = u) :
    FirstPayloadNF u (nfT Z t) := by
  obtain ⟨M, hM⟩ := h
  refine FirstPayloadNF.intro (payload := t) (N := 1) (M := M) ?_ ?_ hM
  · exact nfT_z_tc t
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    exact NFActiveShape.nf Z t

theorem baseReducts_lfcheckK_active_tc (A s : AST)
    (hactive : Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape s) :
    baseReducts pTC (lfcheckK A s) = [] := by
  cases hactive <;> rfl

theorem hcong_lfcheckK_active_tc (A : AST) (hA : IsNormal pTC A) {s s' : AST}
    (hactive : Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape s)
    (hstep : oneStep pTC s = some s') :
    oneStep pTC (lfcheckK A s) = some (lfcheckK A s') := by
  have hb := baseReducts_lfcheckK_active_tc A s hactive
  simp only [IsNormal] at hA
  change (match baseReducts pTC (lfcheckK A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "lfcheckK") args') (oneStepList pTC [A, s])) =
      some (lfcheckK A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, lfcheckK]

inductive LFCheckKChildOpenShape : AST -> Prop where
  | recCall (toks : AST) : LFCheckKChildOpenShape (lfrec toks)
  | recKCall (r : AST) : LFCheckKChildOpenShape (recK r)
  | parser {s : AST} :
      Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape s ->
        LFCheckKChildOpenShape s

theorem baseReducts_lfcheckK_child_open_tc (A s : AST)
    (hopen : LFCheckKChildOpenShape s) :
    baseReducts pTC (lfcheckK A s) = [] := by
  cases hopen with
  | recCall toks => rfl
  | recKCall r => rfl
  | parser hactive =>
      exact baseReducts_lfcheckK_active_tc A _ hactive

theorem hcong_lfcheckK_child_open_tc (A : AST) (hA : IsNormal pTC A) {s s' : AST}
    (hopen : LFCheckKChildOpenShape s)
    (hstep : oneStep pTC s = some s') :
    oneStep pTC (lfcheckK A s) = some (lfcheckK A s') := by
  have hb := baseReducts_lfcheckK_child_open_tc A s hopen
  simp only [IsNormal] at hA
  change (match baseReducts pTC (lfcheckK A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "lfcheckK") args') (oneStepList pTC [A, s])) =
      some (lfcheckK A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, lfcheckK]

theorem baseReducts_recK_active_tc (s : AST)
    (hactive : Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape s) :
    baseReducts pTC (recK s) = [] := by
  cases hactive <;> rfl

theorem hcong_recK_active_tc {s s' : AST}
    (hactive : Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape s)
    (hstep : oneStep pTC s = some s') :
    oneStep pTC (recK s) = some (recK s') := by
  have hb := baseReducts_recK_active_tc s hactive
  change (match baseReducts pTC (recK s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "recK") args') (oneStepList pTC [s])) =
      some (recK s')
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, recK]

theorem cong_eval_recK_active_with_guard :
    ∀ (N : Nat) {s v : AST},
      eval pTC N s = v ->
      (∀ k, k < N ->
        Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape (eval pTC k s)) ->
      ∃ M, eval pTC M (recK s) = recK v ∧
        ∀ k, k < M -> LFCheckKChildOpenShape (eval pTC k (recK s)) := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst v
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v hs hguard
      simp only [eval] at hs
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at hs
          subst v
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at hs
          have hsactive : Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguardTail :
              ∀ k, k < n ->
                Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape (eval pTC k s') := by
            intro k hk
            have hkSucc : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hone : eval pTC 1 s = s' := by
              simp only [eval, hstep]
            have hshift : eval pTC (Nat.succ k) s = eval pTC k s' := by
              have h := eval_trans_tc 1 k s s' (eval pTC k s') hone rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [← hshift]
            exact hguard (Nat.succ k) hkSucc
          obtain ⟨M, hM, hMguard⟩ := ih hs hguardTail
          refine ⟨1 + M, ?_, ?_⟩
          · have hstepWrap :
                eval pTC 1 (recK s) = recK s' := by
              simp only [eval, hcong_recK_active_tc hsactive hstep]
            exact eval_trans_tc 1 M _ _ _ hstepWrap hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using LFCheckKChildOpenShape.recKCall s
            | succ k =>
                have hkM : k < M := by
                  simpa only [Nat.one_add, Nat.succ_lt_succ_iff] using hk
                have hstepWrap :
                    eval pTC 1 (recK s) = recK s' := by
                  simp only [eval, hcong_recK_active_tc hsactive hstep]
                have hshift : eval pTC (Nat.succ k) (recK s) = eval pTC k (recK s') := by
                  have h := eval_trans_tc 1 k (recK s) (recK s') (eval pTC k (recK s'))
                    hstepWrap rfl
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
                rw [hshift]
                exact hMguard k hkM

theorem cong_eval_lfcheckK_child_open_with_guard (A : AST) (hA : IsNormal pTC A) :
    ∀ (N : Nat) {s v : AST},
      eval pTC N s = v ->
      (∀ k, k < N -> LFCheckKChildOpenShape (eval pTC k s)) ->
      ∃ M, eval pTC M (lfcheckK A s) = lfcheckK A v := by
  intro N
  induction N with
  | zero =>
      intro s v hs _
      simp only [eval] at hs
      subst v
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v hs hguard
      simp only [eval] at hs
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at hs
          subst v
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at hs
          have hopen : LFCheckKChildOpenShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguardTail : ∀ k, k < n -> LFCheckKChildOpenShape (eval pTC k s') := by
            intro k hk
            have hkSucc : Nat.succ k < Nat.succ n := Nat.succ_lt_succ hk
            have hone : eval pTC 1 s = s' := by
              simp only [eval, hstep]
            have hshift : eval pTC (Nat.succ k) s = eval pTC k s' := by
              have h := eval_trans_tc 1 k s s' (eval pTC k s') hone rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [← hshift]
            exact hguard (Nat.succ k) hkSucc
          obtain ⟨M, hM⟩ := ih hs hguardTail
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong_lfcheckK_child_open_tc A hA hopen hstep]
          exact hM

theorem isnormal_sexp1_tc (l : Label) (a : AST)
    (hb : baseReducts pTC (.sexp l [a]) = []) (ha : IsNormal pTC a) :
    IsNormal pTC (.sexp l [a]) := by
  simp only [IsNormal] at ha ⊢
  change (match baseReducts pTC (.sexp l [a]) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp l args') (oneStepList pTC [a])) = none
  rw [hb]
  simp only [oneStepList, ha, Option.map_none]

theorem isnormal_sexp2_tc (l : Label) (a b : AST)
    (hb : baseReducts pTC (.sexp l [a, b]) = [])
    (ha : IsNormal pTC a) (hbarg : IsNormal pTC b) :
    IsNormal pTC (.sexp l [a, b]) := by
  simp only [IsNormal] at ha hbarg ⊢
  change (match baseReducts pTC (.sexp l [a, b]) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp l args') (oneStepList pTC [a, b])) = none
  rw [hb]
  simp only [oneStepList, ha, hbarg, Option.map_none]

theorem isnormal_con0_tc (x : String) : IsNormal pTC (con0 x) := by
  simp [IsNormal, oneStep, oneStepList, baseReducts, applyBaseRewrite, Presentation.rewrites,
    AST.matchPat, AST.matchPatList, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    pTC, pLF, checkerRules, arithmeticRules, internRules, sigRules, termOpsRules, nfRules,
    checkerRulesCore, parserRules, resolveRules, ctxidxRules, shiftRules, ltRules,
    con0, pv, ltT, shift, shiftVar, Var, Mettapedia.GSLT.LanguageDef.LFEnc.Con, Srt,
    Pi, Lam, App, S, Z, Nil, NF, Idx,
    ctxidx, ctxK, resolve, resolveK, tPI, tLAM, tARR, tCOLON, tDOT, tLP, tRP, tTYPE,
    tId, Pp, PErr, Ok, Err, tm, ar, ap, apm, at', tmPi1, tmPi2, tmLam1, tmLam2,
    arK, arK2, apK, apmK, atLPk, recK, lfrec, peano, extraToks,
    typeS, kindS, iName, nProp, nNat, nA, nB, nZ, nPrf, nImp, nEqn, nRfl, nHImpAB,
    nHA, nMpAB, iPropT, iNatT, iA, iB, iZ, iPrf, iImp, iEqn, iImpAB, checkBad,
    someT, ttrue, ffalse, checkOk, checkErr, addN, predN, liftT, liftVarT, substT,
    substVarLT, nfT, nfPi1, nfPi2, nfLam1, nfLam2, nfApp1, nfApp2, nfAppT, convT,
    convA, convB, eqT, sigTCall, retT, ctxLookupAuxT, ctxLookupT, inferT, inferPi1,
    inferPi2, inferLam1, inferLam2, inferApp1, inferApp2, checkT, checkK, verdict,
    internTerm, internPi1, internPi2, internLam1, internLam2, internApp1, internApp2,
    lfcheckK, lfcheckI, lfcheck, checkerFuelA]

theorem hcong_Ok_tc : ∀ s s', oneStep pTC s = some s' ->
    oneStep pTC (Ok s) = some (Ok s') := by
  intro s s' h
  have hb : baseReducts pTC (Ok s) = [] := by
    rfl
  change (match baseReducts pTC (Ok s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Ok") args') (oneStepList pTC [s])) =
      some (Ok s')
  rw [hb]
  simp only [oneStepList, h, Option.map_some, Ok]

theorem hcong_Err_tc : ∀ s s', oneStep pTC s = some s' ->
    oneStep pTC (Err s) = some (Err s') := by
  intro s s' h
  have hb : baseReducts pTC (Err s) = [] := by
    rfl
  change (match baseReducts pTC (Err s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Err") args') (oneStepList pTC [s])) =
      some (Err s')
  rw [hb]
  simp only [oneStepList, h, Option.map_some, Err]

theorem hnone_Err_tc {s : AST} (h : oneStep pTC s = none) :
    oneStep pTC (Err s) = none := by
  have hb : baseReducts pTC (Err s) = [] := by
    rfl
  change (match baseReducts pTC (Err s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Err") args') (oneStepList pTC [s])) =
      none
  rw [hb]
  simp only [oneStepList, h, Option.map_none]

theorem eval_checkErr_shape_tc : ∀ (N : Nat) (e : AST), ∃ e',
    eval pTC N (checkErr e) = checkErr e'
  | 0, e => ⟨e, rfl⟩
  | n + 1, e => by
      cases hstep : oneStep pTC e with
      | none =>
          refine ⟨e, ?_⟩
          simp only [eval, checkErr, hnone_Err_tc hstep]
      | some e' =>
          obtain ⟨e'', htail⟩ := eval_checkErr_shape_tc n e'
          refine ⟨e'', ?_⟩
          have hwrap : oneStep pTC (checkErr e) = some (checkErr e') := by
            simpa only [checkErr] using hcong_Err_tc e e' hstep
          simp only [eval, hwrap]
          exact htail

theorem checkOk_ne_checkErr (e : AST) : checkOk ≠ checkErr e := by
  intro h
  unfold checkOk checkErr Ok Err at h
  injection h with hlabel _
  injection hlabel with hs
  nomatch hs

theorem checkErr_ne_checkOk (e : AST) : checkErr e ≠ checkOk := by
  intro h
  exact checkOk_ne_checkErr e h.symm

theorem eval_checkErr_ne_checkOk_tc (N : Nat) (e : AST) :
    eval pTC N (checkErr e) ≠ checkOk := by
  obtain ⟨e', hshape⟩ := eval_checkErr_shape_tc N e
  intro h
  rw [hshape] at h
  exact checkErr_ne_checkOk e' h

theorem eval_reject_accept_false_tc {start e : AST} {Naccept Nreject : Nat}
    (haccept : eval pTC Naccept start = checkOk)
    (hreject : eval pTC Nreject start = checkErr e) : False := by
  by_cases hle : Nreject ≤ Naccept
  · let K := Naccept - Nreject
    have htotal : eval pTC Naccept start = eval pTC K (checkErr e) := by
      have h := eval_trans_tc Nreject K start (checkErr e)
        (eval pTC K (checkErr e)) hreject rfl
      have hsum : Nreject + K = Naccept := Nat.add_sub_of_le hle
      simpa [K, hsum] using h
    have hbad : eval pTC K (checkErr e) = checkOk := by
      rw [← htotal]
      exact haccept
    exact eval_checkErr_ne_checkOk_tc K e hbad
  · have hlt : Naccept < Nreject := Nat.lt_of_not_ge hle
    let K := Nreject - Naccept
    have htotal : eval pTC Nreject start = checkOk := by
      have h := eval_trans_tc Naccept K start checkOk
        (eval pTC K checkOk) haccept rfl
      have hsum : Naccept + K = Nreject :=
        Nat.add_sub_of_le (Nat.le_of_lt hlt)
      have hstable : eval pTC K checkOk = checkOk :=
        eval_stable_tc isnormal_checkOk_tc K
      simpa [K, hsum, hstable] using h
    have hbad : checkErr e = checkOk := by
      rw [← hreject]
      exact htotal
    exact checkErr_ne_checkOk e hbad

theorem isnormal_peano_tc : ∀ n, IsNormal pTC (peano n)
  | 0 => rfl
  | n + 1 => isnormal_sexp1_tc (.id "S") (peano n) rfl (isnormal_peano_tc n)

theorem hcong_S_tc : ∀ s s', oneStep pTC s = some s' -> oneStep pTC (S s) = some (S s') := by
  intro s s' hstep
  have hb : baseReducts pTC (S s) = [] := rfl
  change (match baseReducts pTC (S s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "S") args') (oneStepList pTC [s])) =
      some (S s')
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, S]

theorem hcong_ltT1_tc (a b : AST) : ∀ a',
    oneStep pTC a = some a' -> baseReducts pTC (ltT a b) = [] ->
      oneStep pTC (ltT a b) = some (ltT a' b) := by
  intro a' hstep hb
  change (match baseReducts pTC (ltT a b) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "lt") args')
        (oneStepList pTC [a, b])) = some (ltT a' b)
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, ltT]

theorem lt_sim_tc : ∀ (a b : Nat),
    ∃ N, eval pTC N (ltT (peano a) (peano b)) =
      con0 (if a < b then "tt" else "ff") := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b with
      | zero =>
          refine ⟨1, ?_⟩
          simp only [peano, eval, os_lt_zz_tc]
          simp
      | succ b' =>
          refine ⟨1, ?_⟩
          simp only [peano, eval, os_lt_zs_tc]
          simp
  | succ a' ih =>
      intro b
      cases b with
      | zero =>
          refine ⟨1, ?_⟩
          simp only [peano, eval, os_lt_sz_tc]
          simp
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b'
          refine ⟨N + 1, ?_⟩
          simp only [peano, eval, os_lt_ss_tc]
          rw [hN]
          simp only [Nat.succ_lt_succ_iff]

theorem addN_sim_tc : ∀ (a b : Nat),
    ∃ N, eval pTC N (addN (peano a) (peano b)) = peano (a + b) := by
  intro a
  induction a with
  | zero =>
      intro b
      refine ⟨1, ?_⟩
      simp [peano, addN_z_tc]
  | succ a ih =>
      intro b
      obtain ⟨N, hN⟩ := ih b
      obtain ⟨M, hM⟩ :=
        cong_eval_tc (fun s => S s) hcong_S_tc N hN (isnormal_peano_tc (a + b))
      refine ⟨1 + M, ?_⟩
      have hstep : eval pTC 1 (addN (peano (Nat.succ a)) (peano b)) =
          S (addN (peano a) (peano b)) := by
        simp only [peano, addN_s_tc]
      have htotal := eval_trans_tc 1 M _ _ _ hstep hM
      rw [htotal]
      have hnat : a + 1 + b = Nat.succ (a + b) := by
        omega
      rw [hnat]
      rfl

theorem predN_sim_tc : ∀ (a : Nat),
    ∃ N, eval pTC N (predN (peano a)) = peano (a - 1) := by
  intro a
  cases a with
  | zero =>
      refine ⟨1, ?_⟩
      change eval pTC 1 (predN Z) = Z
      exact predN_z_tc
  | succ a =>
      refine ⟨1, ?_⟩
      change eval pTC 1 (predN (S (peano a))) = peano a
      exact predN_s_tc (peano a)

theorem os_predN_peano_tc (k : Nat) :
    oneStep pTC (predN (peano k)) = some (peano (k - 1)) := by
  cases k with
  | zero => rfl
  | succ k => rfl

theorem os_liftVarT_lt_ss_tc (d c k x y : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) (hk : IsNormal pTC k) :
    oneStep pTC (liftVarT d c k (ltT (S x) (S y))) =
      some (liftVarT d c k (ltT x y)) := by
  have hb : baseReducts pTC (liftVarT d c k (ltT (S x) (S y))) = [] := rfl
  simp only [IsNormal] at hd hc hk
  change (match baseReducts pTC (liftVarT d c k (ltT (S x) (S y))) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "liftVarT") args')
        (oneStepList pTC [d, c, k, ltT (S x) (S y)])) =
      some (liftVarT d c k (ltT x y))
  rw [hb]
  simp only [oneStepList, hd, hc, hk, os_lt_ss_tc, Option.map_some, liftVarT]

theorem os_liftVarT_lt_zs_tc (d c k y : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) (hk : IsNormal pTC k) :
    oneStep pTC (liftVarT d c k (ltT Z (S y))) =
      some (liftVarT d c k (con0 "tt")) := by
  have hb : baseReducts pTC (liftVarT d c k (ltT Z (S y))) = [] := rfl
  simp only [IsNormal] at hd hc hk
  change (match baseReducts pTC (liftVarT d c k (ltT Z (S y))) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "liftVarT") args')
        (oneStepList pTC [d, c, k, ltT Z (S y)])) =
      some (liftVarT d c k (con0 "tt"))
  rw [hb]
  simp only [oneStepList, hd, hc, hk, os_lt_zs_tc, Option.map_some, liftVarT]

theorem os_liftVarT_lt_zz_tc (d c k : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) (hk : IsNormal pTC k) :
    oneStep pTC (liftVarT d c k (ltT Z Z)) =
      some (liftVarT d c k (con0 "ff")) := by
  have hb : baseReducts pTC (liftVarT d c k (ltT Z Z)) = [] := rfl
  simp only [IsNormal] at hd hc hk
  change (match baseReducts pTC (liftVarT d c k (ltT Z Z)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "liftVarT") args')
        (oneStepList pTC [d, c, k, ltT Z Z])) =
      some (liftVarT d c k (con0 "ff"))
  rw [hb]
  simp only [oneStepList, hd, hc, hk, os_lt_zz_tc, Option.map_some, liftVarT]

theorem os_liftVarT_lt_sz_tc (d c k x : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) (hk : IsNormal pTC k) :
    oneStep pTC (liftVarT d c k (ltT (S x) Z)) =
      some (liftVarT d c k (con0 "ff")) := by
  have hb : baseReducts pTC (liftVarT d c k (ltT (S x) Z)) = [] := rfl
  simp only [IsNormal] at hd hc hk
  change (match baseReducts pTC (liftVarT d c k (ltT (S x) Z)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "liftVarT") args')
        (oneStepList pTC [d, c, k, ltT (S x) Z])) =
      some (liftVarT d c k (con0 "ff"))
  rw [hb]
  simp only [oneStepList, hd, hc, hk, os_lt_sz_tc, Option.map_some, liftVarT]

theorem if_succ_lt_succ_eq {α : Sort u} (a b : Nat) (x y : α) :
    (if Nat.succ a < Nat.succ b then x else y) = (if a < b then x else y) := by
  by_cases h : a < b
  · have hs : Nat.succ a < Nat.succ b := Nat.succ_lt_succ h
    simp only [h, hs]
  · have hs : ¬ Nat.succ a < Nat.succ b := by
      intro hs
      exact h (Nat.succ_lt_succ_iff.mp hs)
    simp only [h, hs]

theorem if_succ_add_one_lt_succ_eq {α : Sort u} (k b : Nat) (x y : α) :
    (if Nat.succ k + 1 < Nat.succ b then x else y) =
      (if k + 1 < b then x else y) := by
  by_cases h : k + 1 < b
  · have hs : Nat.succ k + 1 < Nat.succ b := by
      simpa only [Nat.add_one] using Nat.succ_lt_succ h
    simp only [h, hs]
  · have hs : ¬ Nat.succ k + 1 < Nat.succ b := by
      intro hs
      apply h
      have hs' : Nat.succ (k + 1) < Nat.succ b := by
        simpa only [Nat.add_one] using hs
      exact Nat.succ_lt_succ_iff.mp hs'
    simp only [h, hs]

theorem liftVarT_lt_final_tc : ∀ (a b : Nat) (d c k : AST),
    IsNormal pTC d -> IsNormal pTC c -> IsNormal pTC k ->
    ∃ N, eval pTC N (liftVarT d c k (ltT (peano a) (peano b))) =
      (if a < b then Var k else Var (addN k d)) := by
  intro a
  induction a with
  | zero =>
      intro b d c k hd hc hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1 : eval pTC 1 (liftVarT d c k (ltT (peano 0) (peano 0))) =
              liftVarT d c k (con0 "ff") := by
            simp only [peano, eval, os_liftVarT_lt_zz_tc d c k hd hc hk]
          have h2 : eval pTC 1 (liftVarT d c k (con0 "ff")) = Var (addN k d) :=
            liftVarT_ge_tc d c k
          have hlt : ¬ 0 < 0 := Nat.not_lt_zero 0
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          refine ⟨1 + 1, ?_⟩
          have h1 : eval pTC 1 (liftVarT d c k (ltT (peano 0) (peano (Nat.succ b')))) =
              liftVarT d c k (con0 "tt") := by
            simp only [peano, eval, os_liftVarT_lt_zs_tc d c k (peano b') hd hc hk]
          have h2 : eval pTC 1 (liftVarT d c k (con0 "tt")) = Var k :=
            liftVarT_lt_tc d c k
          have hlt : 0 < Nat.succ b' := Nat.zero_lt_succ b'
          simpa only [hlt, if_true] using eval_trans_tc 1 1 _ _ _ h1 h2
  | succ a ih =>
      intro b d c k hd hc hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1 : eval pTC 1 (liftVarT d c k (ltT (peano (Nat.succ a)) (peano 0))) =
              liftVarT d c k (con0 "ff") := by
            simp only [peano, eval, os_liftVarT_lt_sz_tc d c k (peano a) hd hc hk]
          have h2 : eval pTC 1 (liftVarT d c k (con0 "ff")) = Var (addN k d) :=
            liftVarT_ge_tc d c k
          have hlt : ¬ Nat.succ a < 0 := Nat.not_lt_zero (Nat.succ a)
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b' d c k hd hc hk
          refine ⟨N + 1, ?_⟩
          simp only [peano, eval, os_liftVarT_lt_ss_tc d c k (peano a) (peano b') hd hc hk]
          rw [hN]
          simp only [if_succ_lt_succ_eq]

theorem os_substVarLT_lt_ss_tc (j s k x y : AST)
    (hj : IsNormal pTC j) (hs : IsNormal pTC s) (hk : IsNormal pTC k) :
    oneStep pTC (substVarLT j s k (ltT (S x) (S y))) =
      some (substVarLT j s k (ltT x y)) := by
  have hb : baseReducts pTC (substVarLT j s k (ltT (S x) (S y))) = [] := rfl
  simp only [IsNormal] at hj hs hk
  change (match baseReducts pTC (substVarLT j s k (ltT (S x) (S y))) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "substVarLT") args')
        (oneStepList pTC [j, s, k, ltT (S x) (S y)])) =
      some (substVarLT j s k (ltT x y))
  rw [hb]
  simp only [oneStepList, hj, hs, hk, os_lt_ss_tc, Option.map_some, substVarLT]

theorem os_substVarLT_lt_zs_tc (j s k y : AST)
    (hj : IsNormal pTC j) (hs : IsNormal pTC s) (hk : IsNormal pTC k) :
    oneStep pTC (substVarLT j s k (ltT Z (S y))) =
      some (substVarLT j s k (con0 "tt")) := by
  have hb : baseReducts pTC (substVarLT j s k (ltT Z (S y))) = [] := rfl
  simp only [IsNormal] at hj hs hk
  change (match baseReducts pTC (substVarLT j s k (ltT Z (S y))) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "substVarLT") args')
        (oneStepList pTC [j, s, k, ltT Z (S y)])) =
      some (substVarLT j s k (con0 "tt"))
  rw [hb]
  simp only [oneStepList, hj, hs, hk, os_lt_zs_tc, Option.map_some, substVarLT]

theorem os_substVarLT_lt_zz_tc (j s k : AST)
    (hj : IsNormal pTC j) (hs : IsNormal pTC s) (hk : IsNormal pTC k) :
    oneStep pTC (substVarLT j s k (ltT Z Z)) =
      some (substVarLT j s k (con0 "ff")) := by
  have hb : baseReducts pTC (substVarLT j s k (ltT Z Z)) = [] := rfl
  simp only [IsNormal] at hj hs hk
  change (match baseReducts pTC (substVarLT j s k (ltT Z Z)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "substVarLT") args')
        (oneStepList pTC [j, s, k, ltT Z Z])) =
      some (substVarLT j s k (con0 "ff"))
  rw [hb]
  simp only [oneStepList, hj, hs, hk, os_lt_zz_tc, Option.map_some, substVarLT]

theorem os_substVarLT_lt_sz_tc (j s k x : AST)
    (hj : IsNormal pTC j) (hs : IsNormal pTC s) (hk : IsNormal pTC k) :
    oneStep pTC (substVarLT j s k (ltT (S x) Z)) =
      some (substVarLT j s k (con0 "ff")) := by
  have hb : baseReducts pTC (substVarLT j s k (ltT (S x) Z)) = [] := rfl
  simp only [IsNormal] at hj hs hk
  change (match baseReducts pTC (substVarLT j s k (ltT (S x) Z)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "substVarLT") args')
        (oneStepList pTC [j, s, k, ltT (S x) Z])) =
      some (substVarLT j s k (con0 "ff"))
  rw [hb]
  simp only [oneStepList, hj, hs, hk, os_lt_sz_tc, Option.map_some, substVarLT]

theorem hcong_substVarLT2_lt_tc (j k a b : AST) (hj : IsNormal pTC j) : ∀ s s',
    oneStep pTC s = some s' ->
      oneStep pTC (substVarLT j s k (ltT a b)) = some (substVarLT j s' k (ltT a b)) := by
  intro s s' hstep
  have hb : baseReducts pTC (substVarLT j s k (ltT a b)) = [] := rfl
  simp only [IsNormal] at hj
  change (match baseReducts pTC (substVarLT j s k (ltT a b)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "substVarLT") args')
        (oneStepList pTC [j, s, k, ltT a b])) = some (substVarLT j s' k (ltT a b))
  rw [hb]
  simp only [oneStepList, hj, hstep, Option.map_some, substVarLT]

theorem hcong_nfT_s_substT_arg_tc (fuel j s t s' : AST)
    (hfuel : IsNormal pTC fuel)
    (h : oneStep pTC (substT j s t) = some s') :
    oneStep pTC (nfT (S fuel) (substT j s t)) = some (nfT (S fuel) s') := by
  have hb : baseReducts pTC (nfT (S fuel) (substT j s t)) = [] := rfl
  have hS : IsNormal pTC (S fuel) := isnormal_sexp1_tc (.id "S") fuel rfl hfuel
  simp only [IsNormal] at hS
  change (match baseReducts pTC (nfT (S fuel) (substT j s t)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfT") args')
        (oneStepList pTC [S fuel, substT j s t])) = some (nfT (S fuel) s')
  rw [hb]
  simp only [oneStepList, hS, h, Option.map_some, nfT]

theorem hcong_nfT_s_substVarLT_arg_tc (fuel j s k b s' : AST)
    (hfuel : IsNormal pTC fuel)
    (h : oneStep pTC (substVarLT j s k b) = some s') :
    oneStep pTC (nfT (S fuel) (substVarLT j s k b)) = some (nfT (S fuel) s') := by
  have hb : baseReducts pTC (nfT (S fuel) (substVarLT j s k b)) = [] := rfl
  have hS : IsNormal pTC (S fuel) := isnormal_sexp1_tc (.id "S") fuel rfl hfuel
  simp only [IsNormal] at hS
  change (match baseReducts pTC (nfT (S fuel) (substVarLT j s k b)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfT") args')
        (oneStepList pTC [S fuel, substVarLT j s k b])) = some (nfT (S fuel) s')
  rw [hb]
  simp only [oneStepList, hS, h, Option.map_some, nfT]

theorem hcong_nfT_s_substVarLT2_lt_tc (fuel j k a b : AST)
    (hfuel : IsNormal pTC fuel) (hj : IsNormal pTC j) : ∀ s s',
    oneStep pTC s = some s' ->
      oneStep pTC (nfT (S fuel) (substVarLT j s k (ltT a b))) =
        some (nfT (S fuel) (substVarLT j s' k (ltT a b))) := by
  intro s s' hstep
  exact hcong_nfT_s_substVarLT_arg_tc fuel j s k (ltT a b)
    (substVarLT j s' k (ltT a b)) hfuel
    (hcong_substVarLT2_lt_tc j k a b hj s s' hstep)

theorem hcong_nfT_s_arg_tc (fuel t t' : AST)
    (hfuel : IsNormal pTC fuel)
    (hb : baseReducts pTC (nfT (S fuel) t) = [])
    (h : oneStep pTC t = some t') :
    oneStep pTC (nfT (S fuel) t) = some (nfT (S fuel) t') := by
  have hS : IsNormal pTC (S fuel) := isnormal_sexp1_tc (.id "S") fuel rfl hfuel
  simp only [IsNormal] at hS
  change (match baseReducts pTC (nfT (S fuel) t) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "nfT") args')
        (oneStepList pTC [S fuel, t])) = some (nfT (S fuel) t')
  rw [hb]
  simp only [oneStepList, hS, h, Option.map_some, nfT]

theorem substVarLT_lt_final_tc : ∀ (a b : Nat) (j s k : AST),
    IsNormal pTC j -> IsNormal pTC s -> IsNormal pTC k ->
    ∃ N, eval pTC N (substVarLT j s k (ltT (peano a) (peano b))) =
      (if a < b then Var (predN k) else Var k) := by
  intro a
  induction a with
  | zero =>
      intro b j s k hj hs hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1 : eval pTC 1 (substVarLT j s k (ltT (peano 0) (peano 0))) =
              substVarLT j s k (con0 "ff") := by
            simp only [peano, eval, os_substVarLT_lt_zz_tc j s k hj hs hk]
          have h2 : eval pTC 1 (substVarLT j s k (con0 "ff")) = Var k :=
            substVarLT_ge_tc j s k
          have hlt : ¬ 0 < 0 := Nat.not_lt_zero 0
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          refine ⟨1 + 1, ?_⟩
          have h1 : eval pTC 1 (substVarLT j s k (ltT (peano 0) (peano (Nat.succ b')))) =
              substVarLT j s k (con0 "tt") := by
            simp only [peano, eval, os_substVarLT_lt_zs_tc j s k (peano b') hj hs hk]
          have h2 : eval pTC 1 (substVarLT j s k (con0 "tt")) = Var (predN k) :=
            substVarLT_lt_tc j s k
          have hlt : 0 < Nat.succ b' := Nat.zero_lt_succ b'
          simpa only [hlt, if_true] using eval_trans_tc 1 1 _ _ _ h1 h2
  | succ a ih =>
      intro b j s k hj hs hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1 : eval pTC 1 (substVarLT j s k (ltT (peano (Nat.succ a)) (peano 0))) =
              substVarLT j s k (con0 "ff") := by
            simp only [peano, eval, os_substVarLT_lt_sz_tc j s k (peano a) hj hs hk]
          have h2 : eval pTC 1 (substVarLT j s k (con0 "ff")) = Var k :=
            substVarLT_ge_tc j s k
          have hlt : ¬ Nat.succ a < 0 := Nat.not_lt_zero (Nat.succ a)
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b' j s k hj hs hk
          refine ⟨N + 1, ?_⟩
          simp only [peano, eval, os_substVarLT_lt_ss_tc j s k (peano a) (peano b') hj hs hk]
          rw [hN]
          simp only [if_succ_lt_succ_eq]

theorem hcong_Var_tc : ∀ s s', oneStep pTC s = some s' ->
    oneStep pTC (Var s) = some (Var s') := by
  intro s s' hstep
  have hb : baseReducts pTC (Var s) = [] := rfl
  change (match baseReducts pTC (Var s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Var") args') (oneStepList pTC [s])) =
      some (Var s')
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, Var]

theorem hcong_Pi1_tc (B : AST) : ∀ s s', oneStep pTC s = some s' ->
    oneStep pTC (Pi s B) = some (Pi s' B) := by
  intro s s' hstep
  have hb : baseReducts pTC (Pi s B) = [] := rfl
  change (match baseReducts pTC (Pi s B) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Pi") args') (oneStepList pTC [s, B])) =
      some (Pi s' B)
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, Pi]

theorem hcong_Pi2_tc (A : AST) (hA : IsNormal pTC A) : ∀ s s',
    oneStep pTC s = some s' -> oneStep pTC (Pi A s) = some (Pi A s') := by
  intro s s' hstep
  have hb : baseReducts pTC (Pi A s) = [] := rfl
  simp only [IsNormal] at hA
  change (match baseReducts pTC (Pi A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Pi") args') (oneStepList pTC [A, s])) =
      some (Pi A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, Pi]

theorem hcong_Lam1_tc (b : AST) : ∀ s s', oneStep pTC s = some s' ->
    oneStep pTC (Lam s b) = some (Lam s' b) := by
  intro s s' hstep
  have hb : baseReducts pTC (Lam s b) = [] := rfl
  change (match baseReducts pTC (Lam s b) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Lam") args') (oneStepList pTC [s, b])) =
      some (Lam s' b)
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, Lam]

theorem hcong_Lam2_tc (A : AST) (hA : IsNormal pTC A) : ∀ s s',
    oneStep pTC s = some s' -> oneStep pTC (Lam A s) = some (Lam A s') := by
  intro s s' hstep
  have hb : baseReducts pTC (Lam A s) = [] := rfl
  simp only [IsNormal] at hA
  change (match baseReducts pTC (Lam A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "Lam") args') (oneStepList pTC [A, s])) =
      some (Lam A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, Lam]

theorem hcong_App1_tc (a : AST) : ∀ s s', oneStep pTC s = some s' ->
    oneStep pTC (App s a) = some (App s' a) := by
  intro s s' hstep
  have hb : baseReducts pTC (App s a) = [] := rfl
  change (match baseReducts pTC (App s a) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "App") args') (oneStepList pTC [s, a])) =
      some (App s' a)
  rw [hb]
  simp only [oneStepList, hstep, Option.map_some, App]

theorem hcong_App2_tc (f : AST) (hf : IsNormal pTC f) : ∀ s s',
    oneStep pTC s = some s' -> oneStep pTC (App f s) = some (App f s') := by
  intro s s' hstep
  have hb : baseReducts pTC (App f s) = [] := rfl
  simp only [IsNormal] at hf
  change (match baseReducts pTC (App f s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "App") args') (oneStepList pTC [f, s])) =
      some (App f s')
  rw [hb]
  simp only [oneStepList, hf, hstep, Option.map_some, App]

theorem nfPi2_nfT_first_payload (fuel B Apre Aval Bval : AST)
    (hAeval : ∃ M, eval pTC M Apre = Aval) (hAnorm : IsNormal pTC Aval)
    (hBnorm : IsNormal pTC Bval)
    (hB : FirstPayloadNF Bval (nfT fuel B)) :
    FirstPayloadNF (Pi Aval Bval) (nfPi2 Apre (nfT fuel B)) := by
  obtain ⟨NA, hNA⟩ := hAeval
  obtain ⟨MA, hMA, hMAguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun A => nfPi2 A (nfT fuel B))
      (fun A => NFActiveShape.pi2 A (nfT fuel B))
      (hcong_nfPi2_arg_nfT_tc fuel B) NA hNA hAnorm
  cases hB with
  | @intro Bpre NB MB hBmatch hBguard hBpayload =>
      obtain ⟨MBctx, hMBctx, hMBguard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfPi2 Aval s)
          (fun s _ => NFActiveShape.pi2 Aval s)
          (hcong_nfPi2_active_tc Aval hAnorm) NB hBmatch hBguard
      obtain ⟨MPayload, hMPayload⟩ :=
        cong_eval_tc (fun s => Pi Aval s) (hcong_Pi2_tc Aval hAnorm) MB hBpayload hBnorm
      refine FirstPayloadNF.intro (payload := Pi Aval Bpre) (N := MA + (MBctx + 1))
        (M := MPayload) ?_ ?_ hMPayload
      · have hafterB : eval pTC (MA + MBctx) (nfPi2 Apre (nfT fuel B)) =
            nfPi2 Aval (someT Bpre) := by
          exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
        have hroot : eval pTC 1 (nfPi2 Aval (someT Bpre)) = someT (Pi Aval Bpre) :=
          nfPi2_ok_tc Aval Bpre
        have htotal := eval_trans_tc (MA + MBctx) 1 _ _ _ hafterB hroot
        simpa [Nat.add_assoc] using htotal
      · intro k hk
        by_cases hkA : k < MA
        · exact hMAguard k hkA
        · have hgeA : MA ≤ k := Nat.le_of_not_gt hkA
          by_cases hkB : k < MA + MBctx
          · let j := k - MA
            have hjlt : j < MBctx := by
              exact Nat.sub_lt_left_of_lt_add hgeA hkB
            have hkdecomp : k = MA + j := by
              exact (Nat.add_sub_of_le hgeA).symm
            subst j
            rw [hkdecomp]
            have htotal : eval pTC (MA + (k - MA)) (nfPi2 Apre (nfT fuel B)) =
                eval pTC (k - MA) (nfPi2 Aval (nfT fuel B)) :=
              eval_trans_tc MA (k - MA) _ _ _ hMA rfl
            rw [htotal]
            exact hMBguard (k - MA) hjlt
          · have hkEq : k = MA + MBctx := by omega
            subst k
            have htotal : eval pTC (MA + MBctx) (nfPi2 Apre (nfT fuel B)) =
                nfPi2 Aval (someT Bpre) := by
              exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
            rw [htotal]
            exact NFActiveShape.pi2 Aval (someT Bpre)

theorem nfPi1_nfT_first_payload (fuel B Aval Bval Acall : AST)
    (hfuel : IsNormal pTC fuel) (hBraw : IsNormal pTC B)
    (hAnorm : IsNormal pTC Aval) (hBnorm : IsNormal pTC Bval)
    (hA : FirstPayloadNF Aval Acall)
    (hB : FirstPayloadNF Bval (nfT fuel B)) :
    FirstPayloadNF (Pi Aval Bval) (nfPi1 fuel B Acall) := by
  cases hA with
  | @intro Apre NA MA hAmatch hAguard hApayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfPi1 fuel B s)
          (fun s _ => NFActiveShape.pi1 fuel B s)
          (hcong_nfPi1_active_tc fuel B hfuel hBraw) NA hAmatch hAguard
      have htail := nfPi2_nfT_first_payload fuel B Apre Aval Bval
        ⟨MA, hApayload⟩ hAnorm hBnorm hB
      cases htail with
      | @intro payloadTail NTail MTail hTailMatch hTailGuard hTailPayload =>
          refine FirstPayloadNF.intro (payload := payloadTail) (N := MActx + (1 + NTail))
            (M := MTail) ?_ ?_ hTailPayload
          · have hroot : eval pTC 1 (nfPi1 fuel B (someT Apre)) = nfPi2 Apre (nfT fuel B) :=
              nfPi1_ok_tc fuel B Apre
            have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
            have htotal := eval_trans_tc (MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkA : k < MActx
            · exact hMActxGuard k hkA
            · by_cases hkRoot : k = MActx
              · subst k
                rw [hMActx]
                exact NFActiveShape.pi1 fuel B (someT Apre)
              · let j := k - (MActx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MActx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfPi1 fuel B (someT Apre)) =
                    nfPi2 Apre (nfT fuel B) :=
                  nfPi1_ok_tc fuel B Apre
                have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
                have htotal : eval pTC (MActx + 1 + (k - (MActx + 1))) (nfPi1 fuel B Acall) =
                    eval pTC (k - (MActx + 1)) (nfPi2 Apre (nfT fuel B)) :=
                  eval_trans_tc (MActx + 1) (k - (MActx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MActx + 1)) hjlt

theorem nfLam2_nfT_first_payload (fuel b Apre Aval bval : AST)
    (hAeval : ∃ M, eval pTC M Apre = Aval) (hAnorm : IsNormal pTC Aval)
    (hbnorm : IsNormal pTC bval)
    (hb : FirstPayloadNF bval (nfT fuel b)) :
    FirstPayloadNF (Lam Aval bval) (nfLam2 Apre (nfT fuel b)) := by
  obtain ⟨NA, hNA⟩ := hAeval
  obtain ⟨MA, hMA, hMAguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun A => nfLam2 A (nfT fuel b))
      (fun A => NFActiveShape.lam2 A (nfT fuel b))
      (hcong_nfLam2_arg_nfT_tc fuel b) NA hNA hAnorm
  cases hb with
  | @intro bpre NB MB hbmatch hbguard hbpayload =>
      obtain ⟨MBctx, hMBctx, hMBguard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfLam2 Aval s)
          (fun s _ => NFActiveShape.lam2 Aval s)
          (hcong_nfLam2_active_tc Aval hAnorm) NB hbmatch hbguard
      obtain ⟨MPayload, hMPayload⟩ :=
        cong_eval_tc (fun s => Lam Aval s) (hcong_Lam2_tc Aval hAnorm) MB hbpayload hbnorm
      refine FirstPayloadNF.intro (payload := Lam Aval bpre) (N := MA + (MBctx + 1))
        (M := MPayload) ?_ ?_ hMPayload
      · have hafterB : eval pTC (MA + MBctx) (nfLam2 Apre (nfT fuel b)) =
            nfLam2 Aval (someT bpre) := by
          exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
        have hroot : eval pTC 1 (nfLam2 Aval (someT bpre)) = someT (Lam Aval bpre) :=
          nfLam2_ok_tc Aval bpre
        have htotal := eval_trans_tc (MA + MBctx) 1 _ _ _ hafterB hroot
        simpa [Nat.add_assoc] using htotal
      · intro k hk
        by_cases hkA : k < MA
        · exact hMAguard k hkA
        · have hgeA : MA ≤ k := Nat.le_of_not_gt hkA
          by_cases hkB : k < MA + MBctx
          · let j := k - MA
            have hjlt : j < MBctx := by
              exact Nat.sub_lt_left_of_lt_add hgeA hkB
            have hkdecomp : k = MA + j := by
              exact (Nat.add_sub_of_le hgeA).symm
            subst j
            rw [hkdecomp]
            have htotal : eval pTC (MA + (k - MA)) (nfLam2 Apre (nfT fuel b)) =
                eval pTC (k - MA) (nfLam2 Aval (nfT fuel b)) :=
              eval_trans_tc MA (k - MA) _ _ _ hMA rfl
            rw [htotal]
            exact hMBguard (k - MA) hjlt
          · have hkEq : k = MA + MBctx := by omega
            subst k
            have htotal : eval pTC (MA + MBctx) (nfLam2 Apre (nfT fuel b)) =
                nfLam2 Aval (someT bpre) := by
              exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
            rw [htotal]
            exact NFActiveShape.lam2 Aval (someT bpre)

theorem nfLam1_nfT_first_payload (fuel b Aval bval Acall : AST)
    (hfuel : IsNormal pTC fuel) (hbraw : IsNormal pTC b)
    (hAnorm : IsNormal pTC Aval) (hbvalnorm : IsNormal pTC bval)
    (hA : FirstPayloadNF Aval Acall)
    (hb : FirstPayloadNF bval (nfT fuel b)) :
    FirstPayloadNF (Lam Aval bval) (nfLam1 fuel b Acall) := by
  cases hA with
  | @intro Apre NA MA hAmatch hAguard hApayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfLam1 fuel b s)
          (fun s _ => NFActiveShape.lam1 fuel b s)
          (hcong_nfLam1_active_tc fuel b hfuel hbraw) NA hAmatch hAguard
      have htail := nfLam2_nfT_first_payload fuel b Apre Aval bval
        ⟨MA, hApayload⟩ hAnorm hbvalnorm hb
      cases htail with
      | @intro payloadTail NTail MTail hTailMatch hTailGuard hTailPayload =>
          refine FirstPayloadNF.intro (payload := payloadTail) (N := MActx + (1 + NTail))
            (M := MTail) ?_ ?_ hTailPayload
          · have hroot : eval pTC 1 (nfLam1 fuel b (someT Apre)) = nfLam2 Apre (nfT fuel b) :=
              nfLam1_ok_tc fuel b Apre
            have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
            have htotal := eval_trans_tc (MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkA : k < MActx
            · exact hMActxGuard k hkA
            · by_cases hkRoot : k = MActx
              · subst k
                rw [hMActx]
                exact NFActiveShape.lam1 fuel b (someT Apre)
              · let j := k - (MActx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MActx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfLam1 fuel b (someT Apre)) =
                    nfLam2 Apre (nfT fuel b) :=
                  nfLam1_ok_tc fuel b Apre
                have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
                have htotal : eval pTC (MActx + 1 + (k - (MActx + 1))) (nfLam1 fuel b Acall) =
                    eval pTC (k - (MActx + 1)) (nfLam2 Apre (nfT fuel b)) :=
                  eval_trans_tc (MActx + 1) (k - (MActx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MActx + 1)) hjlt

theorem nfT_pi_first_payload (fuel A B Aval Bval : AST)
    (hfuel : IsNormal pTC fuel) (hBraw : IsNormal pTC B)
    (hAnorm : IsNormal pTC Aval) (hBnorm : IsNormal pTC Bval)
    (hA : FirstPayloadNF Aval (nfT fuel A))
    (hB : FirstPayloadNF Bval (nfT fuel B)) :
    FirstPayloadNF (Pi Aval Bval) (nfT (S fuel) (Pi A B)) := by
  exact first_payload_nf_prepend (nfT_pi_tc fuel A B) (NFActiveShape.nf (S fuel) (Pi A B))
    (nfPi1_nfT_first_payload fuel B Aval Bval (nfT fuel A)
      hfuel hBraw hAnorm hBnorm hA hB)

theorem nfT_lam_first_payload (fuel A b Aval bval : AST)
    (hfuel : IsNormal pTC fuel) (hbraw : IsNormal pTC b)
    (hAnorm : IsNormal pTC Aval) (hbvalnorm : IsNormal pTC bval)
    (hA : FirstPayloadNF Aval (nfT fuel A))
    (hb : FirstPayloadNF bval (nfT fuel b)) :
    FirstPayloadNF (Lam Aval bval) (nfT (S fuel) (Lam A b)) := by
  exact first_payload_nf_prepend (nfT_lam_tc fuel A b) (NFActiveShape.nf (S fuel) (Lam A b))
    (nfLam1_nfT_first_payload fuel b Aval bval (nfT fuel A)
      hfuel hbraw hAnorm hbvalnorm hA hb)

theorem var_addN_sim_tc (k d : Nat) :
    ∃ N, eval pTC N (Var (addN (peano k) (peano d))) = Var (peano (k + d)) := by
  obtain ⟨N, hN⟩ := addN_sim_tc k d
  exact cong_eval_tc (fun s => Var s) hcong_Var_tc N hN (isnormal_peano_tc (k + d))

theorem var_predN_sim_tc (k : Nat) :
    ∃ N, eval pTC N (Var (predN (peano k))) = Var (peano (k - 1)) := by
  obtain ⟨N, hN⟩ := predN_sim_tc k
  exact cong_eval_tc (fun s => Var s) hcong_Var_tc N hN (isnormal_peano_tc (k - 1))

theorem substT_var_peano_tc (j k : Nat) (s : AST) (hs : IsNormal pTC s) :
    ∃ N, eval pTC N (substT (peano j) s (Var (peano k))) =
      (if k = j then s else if j < k then Var (peano (k - 1)) else Var (peano k)) := by
  by_cases hkj : k = j
  · subst k
    refine ⟨1, ?_⟩
    simpa using substT_var_hit_peano_tc j s
  · have hneq : j ≠ k := by
      intro hjk
      exact hkj hjk.symm
    have hstep : eval pTC 1 (substT (peano j) s (Var (peano k))) =
        substVarLT (peano j) s (peano k) (ltT (peano j) (peano k)) := by
      simp only [eval, os_substT_var_miss_tc j k s hneq]
    obtain ⟨Nguard, hguard⟩ :=
      substVarLT_lt_final_tc j k (peano j) s (peano k)
        (isnormal_peano_tc j) hs (isnormal_peano_tc k)
    by_cases hlt : j < k
    · obtain ⟨M, hM⟩ := var_predN_sim_tc k
      refine ⟨1 + (Nguard + M), ?_⟩
      have hguard' : eval pTC Nguard (substVarLT (peano j) s (peano k)
          (ltT (peano j) (peano k))) = Var (predN (peano k)) := by
        simpa [hlt] using hguard
      have htail := eval_trans_tc Nguard M _ _ _ hguard' hM
      have htotal := eval_trans_tc 1 (Nguard + M) _ _ _ hstep htail
      simpa [hkj, hlt] using htotal
    · refine ⟨1 + Nguard, ?_⟩
      have hguard' : eval pTC Nguard (substVarLT (peano j) s (peano k)
          (ltT (peano j) (peano k))) = Var (peano k) := by
        simpa [hlt] using hguard
      have htotal := eval_trans_tc 1 Nguard _ _ _ hstep hguard'
      simpa [hkj, hlt] using htotal

theorem substT_var_payload_peano_tc (j k : Nat) (sCall sVal : AST)
    (hsVal : IsNormal pTC sVal) (hpayload : ∃ Ns, eval pTC Ns sCall = sVal) :
    ∃ N, eval pTC N (substT (peano j) sCall (Var (peano k))) =
      (if k = j then sVal else if j < k then Var (peano (k - 1)) else Var (peano k)) := by
  obtain ⟨Ns, hNs⟩ := hpayload
  by_cases hkj : k = j
  · subst k
    refine ⟨1 + Ns, ?_⟩
    have hstep : eval pTC 1 (substT (peano j) sCall (Var (peano j))) = sCall := by
      simpa using substT_var_hit_peano_tc j sCall
    have htotal := eval_trans_tc 1 Ns _ _ _ hstep hNs
    simpa using htotal
  · have hneq : j ≠ k := by
      intro hjk
      exact hkj hjk.symm
    have hstep : eval pTC 1 (substT (peano j) sCall (Var (peano k))) =
        substVarLT (peano j) sCall (peano k) (ltT (peano j) (peano k)) := by
      simp only [eval, os_substT_var_miss_tc j k sCall hneq]
    obtain ⟨Mpayload, hMpayload⟩ :=
      cong_eval_tc
        (fun s => substVarLT (peano j) s (peano k) (ltT (peano j) (peano k)))
        (hcong_substVarLT2_lt_tc (peano j) (peano k) (peano j) (peano k)
          (isnormal_peano_tc j)) Ns hNs hsVal
    obtain ⟨Nguard, hguard⟩ :=
      substVarLT_lt_final_tc j k (peano j) sVal (peano k)
        (isnormal_peano_tc j) hsVal (isnormal_peano_tc k)
    by_cases hlt : j < k
    · obtain ⟨M, hM⟩ := var_predN_sim_tc k
      refine ⟨1 + (Mpayload + (Nguard + M)), ?_⟩
      have hguard' : eval pTC Nguard (substVarLT (peano j) sVal (peano k)
          (ltT (peano j) (peano k))) = Var (predN (peano k)) := by
        simpa [hlt] using hguard
      have htail2 := eval_trans_tc Nguard M _ _ _ hguard' hM
      have htail := eval_trans_tc Mpayload (Nguard + M) _ _ _ hMpayload htail2
      have htotal := eval_trans_tc 1 (Mpayload + (Nguard + M)) _ _ _ hstep htail
      simpa [hkj, hlt] using htotal
    · refine ⟨1 + (Mpayload + Nguard), ?_⟩
      have hguard' : eval pTC Nguard (substVarLT (peano j) sVal (peano k)
          (ltT (peano j) (peano k))) = Var (peano k) := by
        simpa [hlt] using hguard
      have htail := eval_trans_tc Mpayload Nguard _ _ _ hMpayload hguard'
      have htotal := eval_trans_tc 1 (Mpayload + Nguard) _ _ _ hstep htail
      simpa [hkj, hlt] using htotal

def lift1Stack : Nat -> AST -> AST
  | 0, u => u
  | n + 1, u => lift1Stack n (liftT (S Z) Z u)

def lfLift1Stack : Nat -> LF.Term -> LF.Term
  | 0, t => t
  | n + 1, t => lfLift1Stack n (LFTyping.lift 1 0 t)

def liftStack : List Nat -> AST -> AST
  | [], u => u
  | c :: cs, u => liftStack cs (liftT (S Z) (peano c) u)

def lfLiftStack : List Nat -> LF.Term -> LF.Term
  | [], t => t
  | c :: cs, t => lfLiftStack cs (LFTyping.lift 1 c t)

theorem liftStack_append (cs ds : List Nat) (u : AST) :
    liftStack ds (liftStack cs u) = liftStack (cs ++ ds) u := by
  induction cs generalizing u with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [liftStack, ih]

theorem lfLiftStack_append (cs ds : List Nat) (t : LF.Term) :
    lfLiftStack ds (lfLiftStack cs t) = lfLiftStack (cs ++ ds) t := by
  induction cs generalizing t with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [lfLiftStack, ih]

def ReducesToEncTyCore (u : AST) (t : LF.Term) : Prop :=
  ∃ v N, encTyCore? t = some v ∧ eval pTC N u = v

def LiftablePayload (u : AST) (t : LF.Term) : Prop :=
  ∀ cs : List Nat, ReducesToEncTyCore (liftStack cs u) (lfLiftStack cs t)

theorem LiftablePayload.reduces {u : AST} {t : LF.Term}
    (h : LiftablePayload u t) : ReducesToEncTyCore u t := by
  exact h []

theorem LiftablePayload.lifted {u : AST} {t : LF.Term}
    (h : LiftablePayload u t) (c : Nat) :
    LiftablePayload (liftT (S Z) (peano c) u) (LFTyping.lift 1 c t) := by
  intro cs
  exact h (c :: cs)

theorem LiftablePayload.liftStacked {u : AST} {t : LF.Term}
    (h : LiftablePayload u t) : ∀ cs : List Nat,
      LiftablePayload (liftStack cs u) (lfLiftStack cs t)
  | [] => by
      simpa [liftStack, lfLiftStack] using h
  | c :: cs => by
      simpa [liftStack, lfLiftStack] using
        (LiftablePayload.liftStacked (h.lifted c) cs)

theorem liftable_of_stack_step {u v : AST} {t : LF.Term}
    (hstep : ∀ cs : List Nat, oneStep pTC (liftStack cs u) = some (liftStack cs v))
    (hv : LiftablePayload v t) : LiftablePayload u t := by
  intro cs
  rcases hv cs with ⟨w, N, henc, hN⟩
  refine ⟨w, 1 + N, henc, ?_⟩
  simp only [Nat.one_add, eval]
  rw [hstep cs]
  exact hN

theorem reducesToEncTyCore_refl {t : LF.Term} {u : AST}
    (h : encTyCore? t = some u) : ReducesToEncTyCore u t :=
  ⟨u, 0, h, rfl⟩

theorem liftablePayload_lift1 {u : AST} {t : LF.Term}
    (h : LiftablePayload u t) : LiftablePayload (liftT (S Z) Z u) (LFTyping.lift 1 0 t) := by
  simpa [peano] using h.lifted 0

theorem hcong_liftT_arg_tc (d c s : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c)
    (hb : baseReducts pTC (liftT d c s) = []) : ∀ s',
      oneStep pTC s = some s' -> oneStep pTC (liftT d c s) = some (liftT d c s') := by
  intro s' hstep
  simp only [IsNormal] at hd hc
  change (match baseReducts pTC (liftT d c s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "liftT") args')
        (oneStepList pTC [d, c, s])) = some (liftT d c s')
  rw [hb]
  simp only [oneStepList, hd, hc, hstep, Option.map_some, liftT]

theorem lift1Stack_descend_lift_step_tc (n : Nat) (d c : AST) {s s' : AST}
    (h : oneStep pTC (liftT d c s) = some s') :
    oneStep pTC (lift1Stack n (liftT d c s)) = some (lift1Stack n s') := by
  induction n generalizing d c s s' with
  | zero => exact h
  | succ n ih =>
      change oneStep pTC (lift1Stack n (liftT (S Z) Z (liftT d c s))) =
        some (lift1Stack n (liftT (S Z) Z s'))
      have hinner : oneStep pTC (liftT (S Z) Z (liftT d c s)) =
          some (liftT (S Z) Z s') := by
        exact hcong_liftT_arg_tc (S Z) Z (liftT d c s)
          (isnormal_peano_tc 1) (isnormal_peano_tc 0) rfl s' h
      exact ih (S Z) Z hinner

theorem liftStack_descend_lift_step_tc (cs : List Nat) (c : Nat) {s s' : AST}
    (h : oneStep pTC (liftT (S Z) (peano c) s) = some s') :
    oneStep pTC (liftStack cs (liftT (S Z) (peano c) s)) = some (liftStack cs s') := by
  induction cs generalizing c s s' with
  | nil => exact h
  | cons d ds ih =>
      change oneStep pTC (liftStack ds (liftT (S Z) (peano d)
          (liftT (S Z) (peano c) s))) =
        some (liftStack ds (liftT (S Z) (peano d) s'))
      have hinner : oneStep pTC (liftT (S Z) (peano d) (liftT (S Z) (peano c) s)) =
          some (liftT (S Z) (peano d) s') := by
        exact hcong_liftT_arg_tc (S Z) (peano d) (liftT (S Z) (peano c) s)
          (isnormal_peano_tc 1) (isnormal_peano_tc d) rfl s' h
      exact ih d hinner

theorem baseReducts_nfT_s_liftStack_liftT_tc :
    ∀ (cs : List Nat) (fuel : AST) (c : Nat) (u : AST),
      baseReducts pTC
        (nfT (S fuel) (liftStack cs (liftT (S Z) (peano c) u))) = [] := by
  intro cs
  induction cs with
  | nil =>
      intro fuel c u
      rfl
  | cons d ds ih =>
      intro fuel c u
      simpa [liftStack] using ih fuel d (liftT (S Z) (peano c) u)

theorem hcong_nfT_s_liftStack_liftT_arg_tc
    (cs : List Nat) (fuel : AST) (c : Nat) (u u' : AST)
    (hfuel : IsNormal pTC fuel)
    (h : oneStep pTC (liftT (S Z) (peano c) u) = some u') :
    oneStep pTC (nfT (S fuel) (liftStack cs (liftT (S Z) (peano c) u))) =
      some (nfT (S fuel) (liftStack cs u')) := by
  exact hcong_nfT_s_arg_tc fuel
    (liftStack cs (liftT (S Z) (peano c) u)) (liftStack cs u') hfuel
    (baseReducts_nfT_s_liftStack_liftT_tc cs fuel c u)
    (liftStack_descend_lift_step_tc cs c h)

theorem hcong_liftVarT3_lt_tc (d c a b : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) : ∀ k k',
      oneStep pTC k = some k' ->
        oneStep pTC (liftVarT d c k (ltT a b)) = some (liftVarT d c k' (ltT a b)) := by
  intro k k' hstep
  have hb : baseReducts pTC (liftVarT d c k (ltT a b)) = [] := rfl
  simp only [IsNormal] at hd hc
  change (match baseReducts pTC (liftVarT d c k (ltT a b)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "liftVarT") args')
        (oneStepList pTC [d, c, k, ltT a b])) = some (liftVarT d c k' (ltT a b))
  rw [hb]
  simp only [oneStepList, hd, hc, hstep, Option.map_some, liftVarT]

theorem hcong_liftVarT4_lt_tc (d c k a b : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) (hk : IsNormal pTC k) : ∀ g',
      oneStep pTC (ltT a b) = some g' ->
        oneStep pTC (liftVarT d c k (ltT a b)) = some (liftVarT d c k g') := by
  intro g' hstep
  have hb : baseReducts pTC (liftVarT d c k (ltT a b)) = [] := rfl
  simp only [IsNormal] at hd hc hk
  change (match baseReducts pTC (liftVarT d c k (ltT a b)) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "liftVarT") args')
        (oneStepList pTC [d, c, k, ltT a b])) = some (liftVarT d c k g')
  rw [hb]
  simp only [oneStepList, hd, hc, hk, hstep, Option.map_some, liftVarT]

theorem lift1Stack_descend_liftVarT_step_tc (n : Nat) (d c k b s' : AST)
    (h : oneStep pTC (liftVarT d c k b) = some s') :
    oneStep pTC (lift1Stack n (liftVarT d c k b)) = some (lift1Stack n s') := by
  cases n with
  | zero => exact h
  | succ n =>
      change oneStep pTC (lift1Stack n (liftT (S Z) Z (liftVarT d c k b))) =
        some (lift1Stack n (liftT (S Z) Z s'))
      have hinner : oneStep pTC (liftT (S Z) Z (liftVarT d c k b)) =
          some (liftT (S Z) Z s') := by
        exact hcong_liftT_arg_tc (S Z) Z (liftVarT d c k b)
          (isnormal_peano_tc 1) (isnormal_peano_tc 0) rfl s' h
      exact lift1Stack_descend_lift_step_tc n (S Z) Z hinner

theorem liftStack_descend_liftVarT_step_tc (cs : List Nat) (d c k b s' : AST)
    (h : oneStep pTC (liftVarT d c k b) = some s') :
    oneStep pTC (liftStack cs (liftVarT d c k b)) = some (liftStack cs s') := by
  induction cs with
  | nil => exact h
  | cons e es _ =>
      change oneStep pTC (liftStack es (liftT (S Z) (peano e) (liftVarT d c k b))) =
        some (liftStack es (liftT (S Z) (peano e) s'))
      have hinner : oneStep pTC (liftT (S Z) (peano e) (liftVarT d c k b)) =
          some (liftT (S Z) (peano e) s') := by
        exact hcong_liftT_arg_tc (S Z) (peano e) (liftVarT d c k b)
          (isnormal_peano_tc 1) (isnormal_peano_tc e) rfl s' h
      exact liftStack_descend_lift_step_tc es e hinner

theorem baseReducts_nfT_s_liftStack_liftVarT_tc :
    ∀ (cs : List Nat) (fuel d c k b : AST),
      baseReducts pTC (nfT (S fuel) (liftStack cs (liftVarT d c k b))) = [] := by
  intro cs
  induction cs with
  | nil =>
      intro fuel d c k b
      rfl
  | cons e es ih =>
      intro fuel d c k b
      simpa [liftStack] using
        baseReducts_nfT_s_liftStack_liftT_tc es fuel e (liftVarT d c k b)

theorem hcong_nfT_s_liftStack_liftVarT_arg_tc
    (cs : List Nat) (fuel d c k b s' : AST)
    (hfuel : IsNormal pTC fuel)
    (h : oneStep pTC (liftVarT d c k b) = some s') :
    oneStep pTC (nfT (S fuel) (liftStack cs (liftVarT d c k b))) =
      some (nfT (S fuel) (liftStack cs s')) := by
  exact hcong_nfT_s_arg_tc fuel
    (liftStack cs (liftVarT d c k b)) (liftStack cs s') hfuel
    (baseReducts_nfT_s_liftStack_liftVarT_tc cs fuel d c k b)
    (liftStack_descend_liftVarT_step_tc cs d c k b s' h)

theorem liftStack_descend_substT_step_tc (cs : List Nat) (j s t s' : AST)
    (h : oneStep pTC (substT j s t) = some s') :
    oneStep pTC (liftStack cs (substT j s t)) = some (liftStack cs s') := by
  induction cs with
  | nil => exact h
  | cons e es _ =>
      change oneStep pTC (liftStack es (liftT (S Z) (peano e) (substT j s t))) =
        some (liftStack es (liftT (S Z) (peano e) s'))
      have hinner : oneStep pTC (liftT (S Z) (peano e) (substT j s t)) =
          some (liftT (S Z) (peano e) s') := by
        exact hcong_liftT_arg_tc (S Z) (peano e) (substT j s t)
          (isnormal_peano_tc 1) (isnormal_peano_tc e) rfl s' h
      exact liftStack_descend_lift_step_tc es e hinner

theorem baseReducts_nfT_s_liftStack_substT_tc :
    ∀ (cs : List Nat) (fuel j s t : AST),
      baseReducts pTC (nfT (S fuel) (liftStack cs (substT j s t))) = [] := by
  intro cs
  induction cs with
  | nil =>
      intro fuel j s t
      rfl
  | cons e es _ =>
      intro fuel j s t
      simpa [liftStack] using
        baseReducts_nfT_s_liftStack_liftT_tc es fuel e (substT j s t)

theorem hcong_nfT_s_liftStack_substT_arg_tc
    (cs : List Nat) (fuel j s t s' : AST)
    (hfuel : IsNormal pTC fuel)
    (h : oneStep pTC (substT j s t) = some s') :
    oneStep pTC (nfT (S fuel) (liftStack cs (substT j s t))) =
      some (nfT (S fuel) (liftStack cs s')) := by
  exact hcong_nfT_s_arg_tc fuel
    (liftStack cs (substT j s t)) (liftStack cs s') hfuel
    (baseReducts_nfT_s_liftStack_substT_tc cs fuel j s t)
    (liftStack_descend_substT_step_tc cs j s t s' h)

theorem liftStack_descend_substVarLT_step_tc (cs : List Nat) (j s k b s' : AST)
    (h : oneStep pTC (substVarLT j s k b) = some s') :
    oneStep pTC (liftStack cs (substVarLT j s k b)) = some (liftStack cs s') := by
  induction cs with
  | nil => exact h
  | cons e es _ =>
      change oneStep pTC (liftStack es (liftT (S Z) (peano e) (substVarLT j s k b))) =
        some (liftStack es (liftT (S Z) (peano e) s'))
      have hinner : oneStep pTC (liftT (S Z) (peano e) (substVarLT j s k b)) =
          some (liftT (S Z) (peano e) s') := by
        exact hcong_liftT_arg_tc (S Z) (peano e) (substVarLT j s k b)
          (isnormal_peano_tc 1) (isnormal_peano_tc e) rfl s' h
      exact liftStack_descend_lift_step_tc es e hinner

theorem baseReducts_nfT_s_liftStack_substVarLT_tc :
    ∀ (cs : List Nat) (fuel j s k b : AST),
      baseReducts pTC (nfT (S fuel) (liftStack cs (substVarLT j s k b))) = [] := by
  intro cs
  induction cs with
  | nil =>
      intro fuel j s k b
      rfl
  | cons e es _ =>
      intro fuel j s k b
      simpa [liftStack] using
        baseReducts_nfT_s_liftStack_liftT_tc es fuel e (substVarLT j s k b)

theorem hcong_nfT_s_liftStack_substVarLT_arg_tc
    (cs : List Nat) (fuel j s k b s' : AST)
    (hfuel : IsNormal pTC fuel)
    (h : oneStep pTC (substVarLT j s k b) = some s') :
    oneStep pTC (nfT (S fuel) (liftStack cs (substVarLT j s k b))) =
      some (nfT (S fuel) (liftStack cs s')) := by
  exact hcong_nfT_s_arg_tc fuel
    (liftStack cs (substVarLT j s k b)) (liftStack cs s') hfuel
    (baseReducts_nfT_s_liftStack_substVarLT_tc cs fuel j s k b)
    (liftStack_descend_substVarLT_step_tc cs j s k b s' h)

theorem hcong_nfT_s_liftStack_substVarLT2_lt_tc
    (cs : List Nat) (fuel j k a b : AST)
    (hfuel : IsNormal pTC fuel) (hj : IsNormal pTC j) : ∀ s s',
    oneStep pTC s = some s' ->
      oneStep pTC (nfT (S fuel) (liftStack cs (substVarLT j s k (ltT a b)))) =
        some (nfT (S fuel) (liftStack cs (substVarLT j s' k (ltT a b)))) := by
  intro s s' hstep
  exact hcong_nfT_s_liftStack_substVarLT_arg_tc cs fuel j s k (ltT a b)
    (substVarLT j s' k (ltT a b)) hfuel
    (hcong_substVarLT2_lt_tc j k a b hj s s' hstep)

theorem liftStack_hcong_liftVarT3_lt_tc (cs : List Nat) (d c a b : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) : ∀ k k',
      oneStep pTC k = some k' ->
        oneStep pTC (liftStack cs (liftVarT d c k (ltT a b))) =
          some (liftStack cs (liftVarT d c k' (ltT a b))) := by
  intro k k' hstep
  exact liftStack_descend_liftVarT_step_tc cs d c k (ltT a b)
    (liftVarT d c k' (ltT a b))
    (hcong_liftVarT3_lt_tc d c a b hd hc k k' hstep)

theorem liftStack_hcong_liftVarT4_lt_tc (cs : List Nat) (d c k a b g' : AST)
    (hd : IsNormal pTC d) (hc : IsNormal pTC c) (hk : IsNormal pTC k)
    (h : oneStep pTC (ltT a b) = some g') :
    oneStep pTC (liftStack cs (liftVarT d c k (ltT a b))) =
      some (liftStack cs (liftVarT d c k g')) := by
  exact liftStack_descend_liftVarT_step_tc cs d c k (ltT a b) (liftVarT d c k g')
    (hcong_liftVarT4_lt_tc d c k a b hd hc hk g' h)

theorem liftStack_hcong_substVarLT2_lt_tc (cs : List Nat) (j k a b : AST)
    (hj : IsNormal pTC j) : ∀ s s',
    oneStep pTC s = some s' ->
      oneStep pTC (liftStack cs (substVarLT j s k (ltT a b))) =
        some (liftStack cs (substVarLT j s' k (ltT a b))) := by
  intro s s' hstep
  exact liftStack_descend_substVarLT_step_tc cs j s k (ltT a b)
    (substVarLT j s' k (ltT a b))
    (hcong_substVarLT2_lt_tc j k a b hj s s' hstep)

theorem lift1Stack_liftVarT_lt_final_tc : ∀ (a b n : Nat) (d c k : AST),
    IsNormal pTC d -> IsNormal pTC c -> IsNormal pTC k ->
    ∃ N, eval pTC N (lift1Stack n (liftVarT d c k (ltT (peano a) (peano b)))) =
      lift1Stack n (if a < b then Var k else Var (addN k d)) := by
  intro a
  induction a with
  | zero =>
      intro b n d c k hd hc hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1step := lift1Stack_descend_liftVarT_step_tc n d c k (ltT Z Z)
            (liftVarT d c k (con0 "ff")) (os_liftVarT_lt_zz_tc d c k hd hc hk)
          have h1 : eval pTC 1 (lift1Stack n (liftVarT d c k (ltT (peano 0) (peano 0)))) =
              lift1Stack n (liftVarT d c k (con0 "ff")) := by
            simp only [peano, eval, h1step]
          have hff : oneStep pTC (liftVarT d c k (con0 "ff")) = some (Var (addN k d)) := by
            rfl
          have h2step := lift1Stack_descend_liftVarT_step_tc n d c k (con0 "ff")
            (Var (addN k d)) hff
          have h2 : eval pTC 1 (lift1Stack n (liftVarT d c k (con0 "ff"))) =
              lift1Stack n (Var (addN k d)) := by
            simp only [eval, h2step]
          have hlt : ¬ 0 < 0 := Nat.not_lt_zero 0
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          refine ⟨1 + 1, ?_⟩
          have h1step := lift1Stack_descend_liftVarT_step_tc n d c k (ltT Z (S (peano b')))
            (liftVarT d c k (con0 "tt")) (os_liftVarT_lt_zs_tc d c k (peano b') hd hc hk)
          have h1 : eval pTC 1
              (lift1Stack n (liftVarT d c k (ltT (peano 0) (peano (Nat.succ b'))))) =
              lift1Stack n (liftVarT d c k (con0 "tt")) := by
            simp only [peano, eval, h1step]
          have htt : oneStep pTC (liftVarT d c k (con0 "tt")) = some (Var k) := by
            rfl
          have h2step := lift1Stack_descend_liftVarT_step_tc n d c k (con0 "tt") (Var k) htt
          have h2 : eval pTC 1 (lift1Stack n (liftVarT d c k (con0 "tt"))) =
              lift1Stack n (Var k) := by
            simp only [eval, h2step]
          have hlt : 0 < Nat.succ b' := Nat.zero_lt_succ b'
          simpa only [hlt, if_true] using eval_trans_tc 1 1 _ _ _ h1 h2
  | succ a ih =>
      intro b n d c k hd hc hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1step := lift1Stack_descend_liftVarT_step_tc n d c k (ltT (S (peano a)) Z)
            (liftVarT d c k (con0 "ff")) (os_liftVarT_lt_sz_tc d c k (peano a) hd hc hk)
          have h1 : eval pTC 1
              (lift1Stack n (liftVarT d c k (ltT (peano (Nat.succ a)) (peano 0)))) =
              lift1Stack n (liftVarT d c k (con0 "ff")) := by
            simp only [peano, eval, h1step]
          have hff : oneStep pTC (liftVarT d c k (con0 "ff")) = some (Var (addN k d)) := by
            rfl
          have h2step := lift1Stack_descend_liftVarT_step_tc n d c k (con0 "ff")
            (Var (addN k d)) hff
          have h2 : eval pTC 1 (lift1Stack n (liftVarT d c k (con0 "ff"))) =
              lift1Stack n (Var (addN k d)) := by
            simp only [eval, h2step]
          have hlt : ¬ Nat.succ a < 0 := Nat.not_lt_zero (Nat.succ a)
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b' n d c k hd hc hk
          refine ⟨N + 1, ?_⟩
          have h1step := lift1Stack_descend_liftVarT_step_tc n d c k
            (ltT (S (peano a)) (S (peano b')))
            (liftVarT d c k (ltT (peano a) (peano b')))
            (os_liftVarT_lt_ss_tc d c k (peano a) (peano b') hd hc hk)
          simp only [peano, eval, h1step]
          rw [hN]
          simp only [if_succ_lt_succ_eq]

theorem liftStack_liftVarT_lt_final_tc : ∀ (a b : Nat) (cs : List Nat) (d c k : AST),
    IsNormal pTC d -> IsNormal pTC c -> IsNormal pTC k ->
    ∃ N, eval pTC N (liftStack cs (liftVarT d c k (ltT (peano a) (peano b)))) =
      liftStack cs (if a < b then Var k else Var (addN k d)) := by
  intro a
  induction a with
  | zero =>
      intro b cs d c k hd hc hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1step := liftStack_descend_liftVarT_step_tc cs d c k (ltT Z Z)
            (liftVarT d c k (con0 "ff")) (os_liftVarT_lt_zz_tc d c k hd hc hk)
          have h1 : eval pTC 1 (liftStack cs (liftVarT d c k (ltT (peano 0) (peano 0)))) =
              liftStack cs (liftVarT d c k (con0 "ff")) := by
            simp only [peano, eval, h1step]
          have hff : oneStep pTC (liftVarT d c k (con0 "ff")) = some (Var (addN k d)) := by
            rfl
          have h2step := liftStack_descend_liftVarT_step_tc cs d c k (con0 "ff")
            (Var (addN k d)) hff
          have h2 : eval pTC 1 (liftStack cs (liftVarT d c k (con0 "ff"))) =
              liftStack cs (Var (addN k d)) := by
            simp only [eval, h2step]
          have hlt : ¬ 0 < 0 := Nat.not_lt_zero 0
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          refine ⟨1 + 1, ?_⟩
          have h1step := liftStack_descend_liftVarT_step_tc cs d c k (ltT Z (S (peano b')))
            (liftVarT d c k (con0 "tt")) (os_liftVarT_lt_zs_tc d c k (peano b') hd hc hk)
          have h1 : eval pTC 1
              (liftStack cs (liftVarT d c k (ltT (peano 0) (peano (Nat.succ b'))))) =
              liftStack cs (liftVarT d c k (con0 "tt")) := by
            simp only [peano, eval, h1step]
          have htt : oneStep pTC (liftVarT d c k (con0 "tt")) = some (Var k) := by
            rfl
          have h2step := liftStack_descend_liftVarT_step_tc cs d c k (con0 "tt") (Var k) htt
          have h2 : eval pTC 1 (liftStack cs (liftVarT d c k (con0 "tt"))) =
              liftStack cs (Var k) := by
            simp only [eval, h2step]
          have hlt : 0 < Nat.succ b' := Nat.zero_lt_succ b'
          simpa only [hlt, if_true] using eval_trans_tc 1 1 _ _ _ h1 h2
  | succ a ih =>
      intro b cs d c k hd hc hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1step := liftStack_descend_liftVarT_step_tc cs d c k (ltT (S (peano a)) Z)
            (liftVarT d c k (con0 "ff")) (os_liftVarT_lt_sz_tc d c k (peano a) hd hc hk)
          have h1 : eval pTC 1
              (liftStack cs (liftVarT d c k (ltT (peano (Nat.succ a)) (peano 0)))) =
              liftStack cs (liftVarT d c k (con0 "ff")) := by
            simp only [peano, eval, h1step]
          have hff : oneStep pTC (liftVarT d c k (con0 "ff")) = some (Var (addN k d)) := by
            rfl
          have h2step := liftStack_descend_liftVarT_step_tc cs d c k (con0 "ff")
            (Var (addN k d)) hff
          have h2 : eval pTC 1 (liftStack cs (liftVarT d c k (con0 "ff"))) =
              liftStack cs (Var (addN k d)) := by
            simp only [eval, h2step]
          have hlt : ¬ Nat.succ a < 0 := Nat.not_lt_zero (Nat.succ a)
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b' cs d c k hd hc hk
          refine ⟨N + 1, ?_⟩
          have h1step := liftStack_descend_liftVarT_step_tc cs d c k
            (ltT (S (peano a)) (S (peano b')))
            (liftVarT d c k (ltT (peano a) (peano b')))
            (os_liftVarT_lt_ss_tc d c k (peano a) (peano b') hd hc hk)
          simp only [peano, eval, h1step]
          rw [hN]
          simp only [if_succ_lt_succ_eq]

theorem liftStack_substVarLT_lt_final_tc : ∀ (a b : Nat) (cs : List Nat) (j s k : AST),
    IsNormal pTC j -> IsNormal pTC s -> IsNormal pTC k ->
    ∃ N, eval pTC N (liftStack cs (substVarLT j s k (ltT (peano a) (peano b)))) =
      liftStack cs (if a < b then Var (predN k) else Var k) := by
  intro a
  induction a with
  | zero =>
      intro b cs j s k hj hs hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1step := liftStack_descend_substVarLT_step_tc cs j s k (ltT Z Z)
            (substVarLT j s k (con0 "ff")) (os_substVarLT_lt_zz_tc j s k hj hs hk)
          have h1 : eval pTC 1 (liftStack cs (substVarLT j s k (ltT (peano 0) (peano 0)))) =
              liftStack cs (substVarLT j s k (con0 "ff")) := by
            simp only [peano, eval, h1step]
          have hff : oneStep pTC (substVarLT j s k (con0 "ff")) = some (Var k) := by
            rfl
          have h2step := liftStack_descend_substVarLT_step_tc cs j s k (con0 "ff")
            (Var k) hff
          have h2 : eval pTC 1 (liftStack cs (substVarLT j s k (con0 "ff"))) =
              liftStack cs (Var k) := by
            simp only [eval, h2step]
          have hlt : ¬ 0 < 0 := Nat.not_lt_zero 0
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          refine ⟨1 + 1, ?_⟩
          have h1step := liftStack_descend_substVarLT_step_tc cs j s k (ltT Z (S (peano b')))
            (substVarLT j s k (con0 "tt")) (os_substVarLT_lt_zs_tc j s k (peano b') hj hs hk)
          have h1 : eval pTC 1
              (liftStack cs (substVarLT j s k (ltT (peano 0) (peano (Nat.succ b'))))) =
              liftStack cs (substVarLT j s k (con0 "tt")) := by
            simp only [peano, eval, h1step]
          have htt : oneStep pTC (substVarLT j s k (con0 "tt")) = some (Var (predN k)) := by
            rfl
          have h2step := liftStack_descend_substVarLT_step_tc cs j s k (con0 "tt")
            (Var (predN k)) htt
          have h2 : eval pTC 1 (liftStack cs (substVarLT j s k (con0 "tt"))) =
              liftStack cs (Var (predN k)) := by
            simp only [eval, h2step]
          have hlt : 0 < Nat.succ b' := Nat.zero_lt_succ b'
          simpa only [hlt, if_true] using eval_trans_tc 1 1 _ _ _ h1 h2
  | succ a ih =>
      intro b cs j s k hj hs hk
      cases b with
      | zero =>
          refine ⟨1 + 1, ?_⟩
          have h1step := liftStack_descend_substVarLT_step_tc cs j s k (ltT (S (peano a)) Z)
            (substVarLT j s k (con0 "ff")) (os_substVarLT_lt_sz_tc j s k (peano a) hj hs hk)
          have h1 : eval pTC 1
              (liftStack cs (substVarLT j s k (ltT (peano (Nat.succ a)) (peano 0)))) =
              liftStack cs (substVarLT j s k (con0 "ff")) := by
            simp only [peano, eval, h1step]
          have hff : oneStep pTC (substVarLT j s k (con0 "ff")) = some (Var k) := by
            rfl
          have h2step := liftStack_descend_substVarLT_step_tc cs j s k (con0 "ff")
            (Var k) hff
          have h2 : eval pTC 1 (liftStack cs (substVarLT j s k (con0 "ff"))) =
              liftStack cs (Var k) := by
            simp only [eval, h2step]
          have hlt : ¬ Nat.succ a < 0 := Nat.not_lt_zero (Nat.succ a)
          simpa only [hlt, if_false] using eval_trans_tc 1 1 _ _ _ h1 h2
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b' cs j s k hj hs hk
          refine ⟨N + 1, ?_⟩
          have h1step := liftStack_descend_substVarLT_step_tc cs j s k
            (ltT (S (peano a)) (S (peano b')))
            (substVarLT j s k (ltT (peano a) (peano b')))
            (os_substVarLT_lt_ss_tc j s k (peano a) (peano b') hj hs hk)
          simp only [peano, eval, h1step]
          rw [hN]
          simp only [if_succ_lt_succ_eq]

theorem liftStack_liftVarT_guard_addN_one_final_tc : ∀ (k b idx : Nat) (cs : List Nat)
    (cArg : AST), IsNormal pTC cArg ->
    ∃ N, eval pTC N (liftStack cs (liftVarT (S Z) cArg (peano idx)
      (ltT (addN (peano k) (S Z)) (peano b)))) =
      liftStack cs (if k + 1 < b then Var (peano idx) else Var (addN (peano idx) (S Z))) := by
  intro k
  induction k with
  | zero =>
      intro b idx cs cArg hcArg
      obtain ⟨Ntail, htail⟩ := liftStack_liftVarT_lt_final_tc 1 b cs (S Z) cArg (peano idx)
        (isnormal_peano_tc 1) hcArg (isnormal_peano_tc idx)
      refine ⟨1 + Ntail, ?_⟩
      have hguardStep : oneStep pTC (ltT (addN (peano 0) (S Z)) (peano b)) =
          some (ltT (S Z) (peano b)) := by
        have hadd : oneStep pTC (addN Z (S Z)) = some (S Z) := by rfl
        exact hcong_ltT1_tc (addN Z (S Z)) (peano b) (S Z) hadd rfl
      have hstep : eval pTC 1 (liftStack cs (liftVarT (S Z) cArg (peano idx)
          (ltT (addN (peano 0) (S Z)) (peano b)))) =
          liftStack cs (liftVarT (S Z) cArg (peano idx) (ltT (S Z) (peano b))) := by
        simp only [peano, eval,
          liftStack_hcong_liftVarT4_lt_tc cs (S Z) cArg (peano idx)
            (addN Z (S Z)) (peano b) (ltT (S Z) (peano b))
            (isnormal_peano_tc 1) hcArg (isnormal_peano_tc idx) hguardStep]
      exact eval_trans_tc 1 Ntail _ _ _ hstep htail
  | succ k ih =>
      intro b idx cs cArg hcArg
      cases b with
      | zero =>
          refine ⟨1 + (1 + 1), ?_⟩
          have hguardStep1 : oneStep pTC
              (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0)) =
              some (ltT (S (addN (peano k) (S Z))) Z) := by
            have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                some (S (addN (peano k) (S Z))) := by rfl
            exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) Z
              (S (addN (peano k) (S Z))) hadd rfl
          have hstep1 : eval pTC 1 (liftStack cs (liftVarT (S Z) cArg (peano idx)
              (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0)))) =
              liftStack cs (liftVarT (S Z) cArg (peano idx)
                (ltT (S (addN (peano k) (S Z))) Z)) := by
            simp only [peano, eval,
              liftStack_hcong_liftVarT4_lt_tc cs (S Z) cArg (peano idx)
                (addN (S (peano k)) (S Z)) Z (ltT (S (addN (peano k) (S Z))) Z)
                (isnormal_peano_tc 1) hcArg (isnormal_peano_tc idx) hguardStep1]
          have hstep2 : eval pTC 1 (liftStack cs (liftVarT (S Z) cArg (peano idx)
              (ltT (S (addN (peano k) (S Z))) Z))) =
              liftStack cs (liftVarT (S Z) cArg (peano idx) (con0 "ff")) := by
            have hs := liftStack_descend_liftVarT_step_tc cs (S Z) cArg (peano idx)
              (ltT (S (addN (peano k) (S Z))) Z)
              (liftVarT (S Z) cArg (peano idx) (con0 "ff"))
              (os_liftVarT_lt_sz_tc (S Z) cArg (peano idx) (addN (peano k) (S Z))
                (isnormal_peano_tc 1) hcArg (isnormal_peano_tc idx))
            simp only [eval, hs]
          have hstep3 : eval pTC 1 (liftStack cs (liftVarT (S Z) cArg (peano idx) (con0 "ff"))) =
              liftStack cs (Var (addN (peano idx) (S Z))) := by
            have hs := liftStack_descend_liftVarT_step_tc cs (S Z) cArg (peano idx) (con0 "ff")
              (Var (addN (peano idx) (S Z))) (by rfl)
            simp only [eval, hs]
          have htail := eval_trans_tc 1 1 _ _ _ hstep2 hstep3
          have htotal := eval_trans_tc 1 (1 + 1) _ _ _ hstep1 htail
          have hlt : ¬ Nat.succ k + 1 < 0 := Nat.not_lt_zero (Nat.succ k + 1)
          simpa only [hlt, if_false] using htotal
      | succ b' =>
          obtain ⟨Nrec, hrec⟩ := ih b' idx cs cArg hcArg
          refine ⟨1 + (1 + Nrec), ?_⟩
          have hguardStep1 : oneStep pTC
              (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))) =
              some (ltT (S (addN (peano k) (S Z))) (S (peano b'))) := by
            have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                some (S (addN (peano k) (S Z))) := by rfl
            exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) (S (peano b'))
              (S (addN (peano k) (S Z))) hadd rfl
          have hstep1 : eval pTC 1 (liftStack cs (liftVarT (S Z) cArg (peano idx)
              (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))))) =
              liftStack cs (liftVarT (S Z) cArg (peano idx)
                (ltT (S (addN (peano k) (S Z))) (S (peano b')))) := by
            simp only [peano, eval,
              liftStack_hcong_liftVarT4_lt_tc cs (S Z) cArg (peano idx)
                (addN (S (peano k)) (S Z)) (S (peano b'))
                (ltT (S (addN (peano k) (S Z))) (S (peano b')))
                (isnormal_peano_tc 1) hcArg (isnormal_peano_tc idx) hguardStep1]
          have hstep2 : eval pTC 1 (liftStack cs (liftVarT (S Z) cArg (peano idx)
              (ltT (S (addN (peano k) (S Z))) (S (peano b'))))) =
              liftStack cs (liftVarT (S Z) cArg (peano idx)
                (ltT (addN (peano k) (S Z)) (peano b'))) := by
            have hs := liftStack_descend_liftVarT_step_tc cs (S Z) cArg (peano idx)
              (ltT (S (addN (peano k) (S Z))) (S (peano b')))
              (liftVarT (S Z) cArg (peano idx)
                (ltT (addN (peano k) (S Z)) (peano b')))
              (os_liftVarT_lt_ss_tc (S Z) cArg (peano idx)
                (addN (peano k) (S Z)) (peano b')
                (isnormal_peano_tc 1) hcArg (isnormal_peano_tc idx))
            simp only [eval, hs]
          have htail := eval_trans_tc 1 Nrec _ _ _ hstep2 hrec
          have htotal := eval_trans_tc 1 (1 + Nrec) _ _ _ hstep1 htail
          simpa only [if_succ_add_one_lt_succ_eq] using htotal

theorem liftStack_liftVarT_addN_one_final_tc (k c : Nat) (cs : List Nat) :
    ∃ N, eval pTC N (liftStack cs (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
      (ltT (addN (peano k) (S Z)) (peano c)))) =
      liftStack cs (if k + 1 < c then Var (peano (k + 1))
        else Var (addN (peano (k + 1)) (S Z))) := by
  obtain ⟨Nidx, hidx⟩ := addN_sim_tc k 1
  have hidx' : eval pTC Nidx (addN (peano k) (S Z)) = peano (k + 1) := by
    simpa [peano] using hidx
  obtain ⟨Midx, hMidx⟩ :=
    cong_eval_tc
      (fun s => liftStack cs (liftVarT (S Z) (peano c) s
        (ltT (addN (peano k) (S Z)) (peano c))))
      (fun s s' hs => liftStack_hcong_liftVarT3_lt_tc cs (S Z) (peano c)
        (addN (peano k) (S Z)) (peano c)
        (isnormal_peano_tc 1) (isnormal_peano_tc c) s s' hs)
      Nidx hidx' (isnormal_peano_tc (k + 1))
  obtain ⟨Mguard, hMguard⟩ :=
    liftStack_liftVarT_guard_addN_one_final_tc k c (k + 1) cs (peano c)
      (isnormal_peano_tc c)
  refine ⟨Midx + Mguard, ?_⟩
  exact eval_trans_tc Midx Mguard _ _ _ hMidx hMguard

theorem liftable_var_pair_tc : ∀ cs : List Nat,
    (∀ k : Nat, ReducesToEncTyCore (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
    (∀ k : Nat, ReducesToEncTyCore (liftStack cs (Var (addN (peano k) (S Z))))
      (lfLiftStack cs (.var (k + 1)))) := by
  intro cs
  induction cs with
  | nil =>
      constructor
      · intro k
        exact reducesToEncTyCore_refl rfl
      · intro k
        obtain ⟨N, hN⟩ := var_addN_sim_tc k 1
        refine ⟨Var (peano (k + 1)), N, ?_, ?_⟩
        · rfl
        · simpa [peano, liftStack] using hN
  | cons c cs ih =>
      constructor
      · intro k
        have h0 : eval pTC 1 (liftStack (c :: cs) (Var (peano k))) =
            liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))) := by
          have hroot : oneStep pTC (liftT (S Z) (peano c) (Var (peano k))) =
              some (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))) := by rfl
          simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
        obtain ⟨Nguard, hguard⟩ := liftStack_liftVarT_lt_final_tc k c cs (S Z) (peano c) (peano k)
          (isnormal_peano_tc 1) (isnormal_peano_tc c) (isnormal_peano_tc k)
        by_cases hkc : k < c
        · rcases ih.1 k with ⟨v, Ntail, henc, htail⟩
          refine ⟨v, 1 + (Nguard + Ntail), ?_, ?_⟩
          · simpa [lfLiftStack, LFTyping.lift, hkc] using henc
          · have hguard' : eval pTC Nguard
                (liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c)))) =
                liftStack cs (Var (peano k)) := by
              simpa [hkc] using hguard
            have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
            exact eval_trans_tc 1 (Nguard + Ntail) _ _ _ h0 htail'
        · rcases ih.2 k with ⟨v, Ntail, henc, htail⟩
          refine ⟨v, 1 + (Nguard + Ntail), ?_, ?_⟩
          · simpa [lfLiftStack, LFTyping.lift, hkc] using henc
          · have hguard' : eval pTC Nguard
                (liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c)))) =
                liftStack cs (Var (addN (peano k) (S Z))) := by
              simpa [hkc] using hguard
            have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
            exact eval_trans_tc 1 (Nguard + Ntail) _ _ _ h0 htail'
      · intro k
        have h0 : eval pTC 1 (liftStack (c :: cs) (Var (addN (peano k) (S Z)))) =
            liftStack cs (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
              (ltT (addN (peano k) (S Z)) (peano c))) := by
          have hroot : oneStep pTC (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))) =
              some (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
                (ltT (addN (peano k) (S Z)) (peano c))) := by rfl
          simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
        obtain ⟨Nguard, hguard⟩ := liftStack_liftVarT_addN_one_final_tc k c cs
        by_cases hkc : k + 1 < c
        · rcases ih.1 (k + 1) with ⟨v, Ntail, henc, htail⟩
          refine ⟨v, 1 + (Nguard + Ntail), ?_, ?_⟩
          · simpa [lfLiftStack, LFTyping.lift, hkc] using henc
          · have hguard' : eval pTC Nguard
                (liftStack cs (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
                  (ltT (addN (peano k) (S Z)) (peano c)))) =
                liftStack cs (Var (peano (k + 1))) := by
              simpa [hkc] using hguard
            have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
            exact eval_trans_tc 1 (Nguard + Ntail) _ _ _ h0 htail'
        · rcases ih.2 (k + 1) with ⟨v, Ntail, henc, htail⟩
          refine ⟨v, 1 + (Nguard + Ntail), ?_, ?_⟩
          · simpa [lfLiftStack, LFTyping.lift, hkc] using henc
          · have hguard' : eval pTC Nguard
                (liftStack cs (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
                  (ltT (addN (peano k) (S Z)) (peano c)))) =
                liftStack cs (Var (addN (peano (k + 1)) (S Z))) := by
              simpa [hkc] using hguard
            have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
            exact eval_trans_tc 1 (Nguard + Ntail) _ _ _ h0 htail'

theorem liftable_liftVarT_peano_guard_tc (a b idx : Nat) :
    LiftablePayload
      (liftVarT (S Z) (peano b) (peano idx) (ltT (peano a) (peano b)))
      (if a < b then .var idx else .var (idx + 1)) := by
  intro cs
  obtain ⟨Nguard, hguard⟩ :=
    liftStack_liftVarT_lt_final_tc a b cs (S Z) (peano b) (peano idx)
      (isnormal_peano_tc 1) (isnormal_peano_tc b) (isnormal_peano_tc idx)
  by_cases hlt : a < b
  · rcases (liftable_var_pair_tc cs).1 idx with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano b) (peano idx) (ltT (peano a) (peano b)))) =
          liftStack cs (Var (peano idx)) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail
  · rcases (liftable_var_pair_tc cs).2 idx with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano b) (peano idx) (ltT (peano a) (peano b)))) =
          liftStack cs (Var (addN (peano idx) (S Z))) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail

theorem liftable_liftVarT_peano_guard_cutoff_tc (a b cutoff idx : Nat) :
    LiftablePayload
      (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano a) (peano b)))
      (if a < b then .var idx else .var (idx + 1)) := by
  intro cs
  obtain ⟨Nguard, hguard⟩ :=
    liftStack_liftVarT_lt_final_tc a b cs (S Z) (peano cutoff) (peano idx)
      (isnormal_peano_tc 1) (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)
  by_cases hlt : a < b
  · rcases (liftable_var_pair_tc cs).1 idx with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano a) (peano b)))) =
          liftStack cs (Var (peano idx)) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail
  · rcases (liftable_var_pair_tc cs).2 idx with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano a) (peano b)))) =
          liftStack cs (Var (addN (peano idx) (S Z))) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail

theorem liftable_liftVarT_guard_addN_one_tc (k b cutoff idx : Nat) :
    LiftablePayload
      (liftVarT (S Z) (peano cutoff) (peano idx)
        (ltT (addN (peano k) (S Z)) (peano b)))
      (if k + 1 < b then .var idx else .var (idx + 1)) := by
  intro cs
  obtain ⟨Nguard, hguard⟩ :=
    liftStack_liftVarT_guard_addN_one_final_tc k b idx cs (peano cutoff)
      (isnormal_peano_tc cutoff)
  by_cases hlt : k + 1 < b
  · rcases (liftable_var_pair_tc cs).1 idx with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (addN (peano k) (S Z)) (peano b)))) =
          liftStack cs (Var (peano idx)) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail
  · rcases (liftable_var_pair_tc cs).2 idx with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (addN (peano k) (S Z)) (peano b)))) =
          liftStack cs (Var (addN (peano idx) (S Z))) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail

theorem liftable_liftVarT_addN_one_guard_tc (k c : Nat) :
    LiftablePayload
      (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
        (ltT (addN (peano k) (S Z)) (peano c)))
      (if k + 1 < c then .var (k + 1) else .var (k + 2)) := by
  intro cs
  obtain ⟨Nguard, hguard⟩ := liftStack_liftVarT_addN_one_final_tc k c cs
  by_cases hlt : k + 1 < c
  · rcases (liftable_var_pair_tc cs).1 (k + 1) with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
              (ltT (addN (peano k) (S Z)) (peano c)))) =
          liftStack cs (Var (peano (k + 1))) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail
  · rcases (liftable_var_pair_tc cs).2 (k + 1) with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Nguard + Ntail, ?_, ?_⟩
    · simpa [hlt, Nat.add_assoc] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs
            (liftVarT (S Z) (peano c) (addN (peano k) (S Z))
              (ltT (addN (peano k) (S Z)) (peano c)))) =
          liftStack cs (Var (addN (peano (k + 1)) (S Z))) := by
        simpa [hlt] using hguard
      exact eval_trans_tc Nguard Ntail _ _ _ hguard' htail

theorem liftStack_var_predN_tc (cs : List Nat) (k : Nat) :
    ReducesToEncTyCore (liftStack cs (Var (predN (peano k))))
      (lfLiftStack cs (.var (k - 1))) := by
  cases cs with
  | nil =>
      obtain ⟨N, hN⟩ := var_predN_sim_tc k
      exact ⟨Var (peano (k - 1)), N, rfl, hN⟩
  | cons c cs =>
      have h0 : eval pTC 1 (liftStack (c :: cs) (Var (predN (peano k)))) =
          liftStack cs (liftVarT (S Z) (peano c) (predN (peano k))
            (ltT (predN (peano k)) (peano c))) := by
        have hroot : oneStep pTC (liftT (S Z) (peano c) (Var (predN (peano k)))) =
            some (liftVarT (S Z) (peano c) (predN (peano k))
              (ltT (predN (peano k)) (peano c))) := by rfl
        simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
      have hpred : oneStep pTC (predN (peano k)) = some (peano (k - 1)) :=
        os_predN_peano_tc k
      have hidx : eval pTC 1
          (liftStack cs (liftVarT (S Z) (peano c) (predN (peano k))
            (ltT (predN (peano k)) (peano c)))) =
          liftStack cs (liftVarT (S Z) (peano c) (peano (k - 1))
            (ltT (predN (peano k)) (peano c))) := by
        simp only [eval,
          liftStack_hcong_liftVarT3_lt_tc cs (S Z) (peano c)
            (predN (peano k)) (peano c)
            (isnormal_peano_tc 1) (isnormal_peano_tc c)
            (predN (peano k)) (peano (k - 1)) hpred]
      have hguardStep : oneStep pTC (ltT (predN (peano k)) (peano c)) =
          some (ltT (peano (k - 1)) (peano c)) := by
        exact hcong_ltT1_tc (predN (peano k)) (peano c) (peano (k - 1)) hpred rfl
      have hguardArg : eval pTC 1
          (liftStack cs (liftVarT (S Z) (peano c) (peano (k - 1))
            (ltT (predN (peano k)) (peano c)))) =
          liftStack cs (liftVarT (S Z) (peano c) (peano (k - 1))
            (ltT (peano (k - 1)) (peano c))) := by
        simp only [eval,
          liftStack_hcong_liftVarT4_lt_tc cs (S Z) (peano c) (peano (k - 1))
            (predN (peano k)) (peano c) (ltT (peano (k - 1)) (peano c))
            (isnormal_peano_tc 1) (isnormal_peano_tc c) (isnormal_peano_tc (k - 1))
            hguardStep]
      obtain ⟨Nguard, hguard⟩ :=
        liftStack_liftVarT_lt_final_tc (k - 1) c cs (S Z) (peano c) (peano (k - 1))
          (isnormal_peano_tc 1) (isnormal_peano_tc c) (isnormal_peano_tc (k - 1))
      by_cases hkc : k - 1 < c
      · rcases (liftable_var_pair_tc cs).1 (k - 1) with ⟨v, Ntail, henc, htail⟩
        refine ⟨v, (1 + 1 + 1) + (Nguard + Ntail), ?_, ?_⟩
        · simpa [lfLiftStack, LFTyping.lift, hkc] using henc
        · have hguard' : eval pTC Nguard
              (liftStack cs (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (peano (k - 1)) (peano c)))) =
              liftStack cs (Var (peano (k - 1))) := by
            simpa [hkc] using hguard
          have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
          have h01 := eval_trans_tc 1 1 _ _ _ h0 hidx
          have h012 := eval_trans_tc (1 + 1) 1 _ _ _ h01 hguardArg
          exact eval_trans_tc (1 + 1 + 1) (Nguard + Ntail) _ _ _ h012 htail'
      · rcases (liftable_var_pair_tc cs).2 (k - 1) with ⟨v, Ntail, henc, htail⟩
        refine ⟨v, (1 + 1 + 1) + (Nguard + Ntail), ?_, ?_⟩
        · simpa [lfLiftStack, LFTyping.lift, hkc] using henc
        · have hguard' : eval pTC Nguard
              (liftStack cs (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (peano (k - 1)) (peano c)))) =
              liftStack cs (Var (addN (peano (k - 1)) (S Z))) := by
            simpa [hkc] using hguard
          have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
          have h01 := eval_trans_tc 1 1 _ _ _ h0 hidx
          have h012 := eval_trans_tc (1 + 1) 1 _ _ _ h01 hguardArg
          exact eval_trans_tc (1 + 1 + 1) (Nguard + Ntail) _ _ _ h012 htail'

theorem liftable_var_tc (k : Nat) : LiftablePayload (Var (peano k)) (.var k) := by
  intro cs
  exact (liftable_var_pair_tc cs).1 k

theorem liftable_var_addN_one_tc (k : Nat) :
    LiftablePayload (Var (addN (peano k) (S Z))) (.var (k + 1)) := by
  intro cs
  exact (liftable_var_pair_tc cs).2 k

theorem liftable_var_predN_peano_tc (k : Nat) :
    LiftablePayload (Var (predN (peano k))) (.var (k - 1)) := by
  intro cs
  exact liftStack_var_predN_tc cs k

theorem liftable_srt_tc (s : LF.Srt) :
    LiftablePayload (Srt (match s with | .type => typeS | .kind => kindS)) (.srt s) := by
  intro cs
  induction cs with
  | nil =>
      cases s <;> exact reducesToEncTyCore_refl rfl
  | cons c cs ih =>
      cases s
      · rcases ih with ⟨v, N, henc, hN⟩
        refine ⟨v, 1 + N, ?_, ?_⟩
        · simpa [lfLiftStack, LFTyping.lift] using henc
        · have hroot : oneStep pTC (liftT (S Z) (peano c) (Srt typeS)) =
              some (Srt typeS) := by rfl
          have hstep : eval pTC 1 (liftStack (c :: cs) (Srt typeS)) =
              liftStack cs (Srt typeS) := by
            simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
          exact eval_trans_tc 1 N _ _ _ hstep hN
      · rcases ih with ⟨v, N, henc, hN⟩
        refine ⟨v, 1 + N, ?_, ?_⟩
        · simpa [lfLiftStack, LFTyping.lift] using henc
        · have hroot : oneStep pTC (liftT (S Z) (peano c) (Srt kindS)) =
              some (Srt kindS) := by rfl
          have hstep : eval pTC 1 (liftStack (c :: cs) (Srt kindS)) =
              liftStack cs (Srt kindS) := by
            simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
          exact eval_trans_tc 1 N _ _ _ hstep hN

theorem liftable_con_tc {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) : LiftablePayload u (.con x) := by
  unfold encTyCore? at h
  cases hx : encName? x with
  | none => simp [hx] at h
  | some k =>
      simp [hx] at h
      subst u
      have henc0 : encTyCore? (.con x) = some (Con k) := by
        unfold encTyCore?
        simp [hx]
      intro cs
      induction cs with
      | nil => exact reducesToEncTyCore_refl henc0
      | cons c cs ih =>
          rcases ih with ⟨v, N, henc, hN⟩
          refine ⟨v, 1 + N, ?_, ?_⟩
          · simpa [lfLiftStack, LFTyping.lift] using henc
          · have hroot : oneStep pTC (liftT (S Z) (peano c) (Con k)) = some (Con k) := by rfl
            have hstep : eval pTC 1 (liftStack (c :: cs) (Con k)) =
                liftStack cs (Con k) := by
              simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
            exact eval_trans_tc 1 N _ _ _ hstep hN

theorem liftT_var_peano_tc (d c k : Nat) :
    ∃ N, eval pTC N (liftT (peano d) (peano c) (Var (peano k))) =
      Var (peano (if k < c then k else k + d)) := by
  obtain ⟨Nguard, hguard⟩ :=
    liftVarT_lt_final_tc k c (peano d) (peano c) (peano k)
      (isnormal_peano_tc d) (isnormal_peano_tc c) (isnormal_peano_tc k)
  have hstep : eval pTC 1 (liftT (peano d) (peano c) (Var (peano k))) =
      liftVarT (peano d) (peano c) (peano k) (ltT (peano k) (peano c)) := by
    simp only [liftT_var_tc]
  by_cases hkc : k < c
  · refine ⟨1 + Nguard, ?_⟩
    have hguard' : eval pTC Nguard (liftVarT (peano d) (peano c) (peano k)
        (ltT (peano k) (peano c))) = Var (peano k) := by
      simpa [hkc] using hguard
    have htotal := eval_trans_tc 1 Nguard _ _ _ hstep hguard'
    simpa [hkc] using htotal
  · obtain ⟨M, hM⟩ := var_addN_sim_tc k d
    refine ⟨1 + (Nguard + M), ?_⟩
    have hguard' : eval pTC Nguard (liftVarT (peano d) (peano c) (peano k)
        (ltT (peano k) (peano c))) = Var (addN (peano k) (peano d)) := by
      simpa [hkc] using hguard
    have htail := eval_trans_tc Nguard M _ _ _ hguard' hM
    have htotal := eval_trans_tc 1 (Nguard + M) _ _ _ hstep htail
    simpa [hkc] using htotal

theorem isnormal_Var_tc (k : AST) (hk : IsNormal pTC k) : IsNormal pTC (Var k) :=
  isnormal_sexp1_tc (.id "Var") k rfl hk

theorem isnormal_Con_tc (x : AST) (hx : IsNormal pTC x) : IsNormal pTC (Con x) :=
  isnormal_sexp1_tc (.id "Con") x rfl hx

theorem isnormal_Srt_tc (s : AST) (hs : IsNormal pTC s) : IsNormal pTC (Srt s) :=
  isnormal_sexp1_tc (.id "Srt") s rfl hs

theorem isnormal_Pi_tc (A B : AST) (hA : IsNormal pTC A) (hB : IsNormal pTC B) :
    IsNormal pTC (Pi A B) :=
  isnormal_sexp2_tc (.id "Pi") A B rfl hA hB

theorem isnormal_Lam_tc (A b : AST) (hA : IsNormal pTC A) (hb : IsNormal pTC b) :
    IsNormal pTC (Lam A b) :=
  isnormal_sexp2_tc (.id "Lam") A b rfl hA hb

theorem isnormal_App_tc (f a : AST) (hf : IsNormal pTC f) (ha : IsNormal pTC a) :
    IsNormal pTC (App f a) :=
  isnormal_sexp2_tc (.id "App") f a rfl hf ha

theorem isnormal_encTerm_raw_tc : ∀ t : LF.Term, IsNormal pTC (encTerm t)
  | .srt s => by
      cases s <;> exact isnormal_Srt_tc _ (isnormal_con0_tc _)
  | .con x => isnormal_Con_tc (con0 x) (isnormal_con0_tc x)
  | .var k => isnormal_Var_tc (peano k) (isnormal_peano_tc k)
  | .pi A B =>
      isnormal_Pi_tc (encTerm A) (encTerm B)
        (isnormal_encTerm_raw_tc A) (isnormal_encTerm_raw_tc B)
  | .lam A b =>
      isnormal_Lam_tc (encTerm A) (encTerm b)
        (isnormal_encTerm_raw_tc A) (isnormal_encTerm_raw_tc b)
  | .app f a =>
      isnormal_App_tc (encTerm f) (encTerm a)
        (isnormal_encTerm_raw_tc f) (isnormal_encTerm_raw_tc a)

theorem isnormal_encTyCore?_tc : ∀ (t : LF.Term) (u : AST),
    encTyCore? t = some u -> IsNormal pTC u := by
  intro t
  induction t with
  | srt s =>
      intro u h
      cases s <;> cases h
      · exact isnormal_Srt_tc typeS (isnormal_con0_tc "type")
      · exact isnormal_Srt_tc kindS (isnormal_con0_tc "kind")
  | var k =>
      intro u h
      cases h
      exact isnormal_Var_tc (peano k) (isnormal_peano_tc k)
  | con x =>
      intro u h
      unfold encTyCore? at h
      unfold encName? at h
      cases hname : Mettapedia.GSLT.InternedNames.Table.intern? lfNameTable x with
      | none => simp [hname] at h
      | some k =>
          simp [hname] at h
          cases h
          exact isnormal_Con_tc (peano k) (isnormal_peano_tc k)
  | pi A B ihA ihB =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hB : encTyCore? B with
          | none => simp [hA, hB] at h
          | some B' =>
              simp [hA, hB] at h
              cases h
              exact isnormal_Pi_tc A' B' (ihA A' hA) (ihB B' hB)
  | lam A b ihA ihb =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hb : encTyCore? b with
          | none => simp [hA, hb] at h
          | some b' =>
              simp [hA, hb] at h
              cases h
              exact isnormal_Lam_tc A' b' (ihA A' hA) (ihb b' hb)
  | app f a ihf iha =>
      intro u h
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              cases h
              exact isnormal_App_tc f' a' (ihf f' hf) (iha a' ha)

theorem reduces_pi_tc {u v : AST} {A B : LF.Term}
    (hu : ReducesToEncTyCore u A) (hv : ReducesToEncTyCore v B) :
    ReducesToEncTyCore (Pi u v) (.pi A B) := by
  rcases hu with ⟨Au, NA, hAu, hAe⟩
  rcases hv with ⟨Bv, NB, hBv, hBe⟩
  have hAnorm : IsNormal pTC Au := isnormal_encTyCore?_tc A Au hAu
  have hBnorm : IsNormal pTC Bv := isnormal_encTyCore?_tc B Bv hBv
  obtain ⟨MA, hMA⟩ :=
    cong_eval_tc (fun s => Pi s v) (hcong_Pi1_tc v) NA hAe hAnorm
  obtain ⟨MB, hMB⟩ :=
    cong_eval_tc (fun s => Pi Au s) (hcong_Pi2_tc Au hAnorm) NB hBe hBnorm
  refine ⟨Pi Au Bv, MA + MB, ?_, ?_⟩
  · simp [encTyCore?, hAu, hBv]
  · exact eval_trans_tc MA MB _ _ _ hMA hMB

theorem reduces_lam_tc {u v : AST} {A b : LF.Term}
    (hu : ReducesToEncTyCore u A) (hv : ReducesToEncTyCore v b) :
    ReducesToEncTyCore (Lam u v) (.lam A b) := by
  rcases hu with ⟨Au, NA, hAu, hAe⟩
  rcases hv with ⟨bv, NB, hbv, hbe⟩
  have hAnorm : IsNormal pTC Au := isnormal_encTyCore?_tc A Au hAu
  have hbnorm : IsNormal pTC bv := isnormal_encTyCore?_tc b bv hbv
  obtain ⟨MA, hMA⟩ :=
    cong_eval_tc (fun s => Lam s v) (hcong_Lam1_tc v) NA hAe hAnorm
  obtain ⟨MB, hMB⟩ :=
    cong_eval_tc (fun s => Lam Au s) (hcong_Lam2_tc Au hAnorm) NB hbe hbnorm
  refine ⟨Lam Au bv, MA + MB, ?_, ?_⟩
  · simp [encTyCore?, hAu, hbv]
  · exact eval_trans_tc MA MB _ _ _ hMA hMB

theorem reduces_app_tc {u v : AST} {f a : LF.Term}
    (hu : ReducesToEncTyCore u f) (hv : ReducesToEncTyCore v a) :
    ReducesToEncTyCore (App u v) (.app f a) := by
  rcases hu with ⟨fu, NF, hfu, hfe⟩
  rcases hv with ⟨av, NA, hav, hae⟩
  have hfnorm : IsNormal pTC fu := isnormal_encTyCore?_tc f fu hfu
  have hanorm : IsNormal pTC av := isnormal_encTyCore?_tc a av hav
  obtain ⟨MF, hMF⟩ :=
    cong_eval_tc (fun s => App s v) (hcong_App1_tc v) NF hfe hfnorm
  obtain ⟨MA, hMA⟩ :=
    cong_eval_tc (fun s => App fu s) (hcong_App2_tc fu hfnorm) NA hae hanorm
  refine ⟨App fu av, MF + MA, ?_, ?_⟩
  · simp [encTyCore?, hfu, hav]
  · exact eval_trans_tc MF MA _ _ _ hMF hMA

theorem liftable_app_stack_tc : ∀ (cs : List Nat) {u v : AST} {f a : LF.Term},
    LiftablePayload u f -> LiftablePayload v a ->
    ReducesToEncTyCore (liftStack cs (App u v)) (lfLiftStack cs (.app f a)) := by
  intro cs
  induction cs with
  | nil =>
      intro u v f a hu hv
      exact reduces_app_tc hu.reduces hv.reduces
  | cons c cs ih =>
      intro u v f a hu hv
      have hroot : oneStep pTC (liftT (S Z) (peano c) (App u v)) =
          some (App (liftT (S Z) (peano c) u) (liftT (S Z) (peano c) v)) := by rfl
      have hstep : eval pTC 1 (liftStack (c :: cs) (App u v)) =
          liftStack cs (App (liftT (S Z) (peano c) u) (liftT (S Z) (peano c) v)) := by
        simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
      have htail : ReducesToEncTyCore
          (liftStack cs (App (liftT (S Z) (peano c) u) (liftT (S Z) (peano c) v)))
          (lfLiftStack cs (.app (LFTyping.lift 1 c f) (LFTyping.lift 1 c a))) :=
        ih (hu.lifted c) (hv.lifted c)
      rcases htail with ⟨w, N, henc, hN⟩
      refine ⟨w, 1 + N, ?_, ?_⟩
      · simpa [lfLiftStack, LFTyping.lift] using henc
      · exact eval_trans_tc 1 N _ _ _ hstep hN

theorem liftable_app_tc {u v : AST} {f a : LF.Term}
    (hu : LiftablePayload u f) (hv : LiftablePayload v a) :
    LiftablePayload (App u v) (.app f a) := by
  intro cs
  exact liftable_app_stack_tc cs hu hv

theorem liftable_pi_stack_tc : ∀ (cs : List Nat) {u v : AST} {A B : LF.Term},
    LiftablePayload u A -> LiftablePayload v B ->
    ReducesToEncTyCore (liftStack cs (Pi u v)) (lfLiftStack cs (.pi A B)) := by
  intro cs
  induction cs with
  | nil =>
      intro u v A B hu hv
      exact reduces_pi_tc hu.reduces hv.reduces
  | cons c cs ih =>
      intro u v A B hu hv
      have hroot : oneStep pTC (liftT (S Z) (peano c) (Pi u v)) =
          some (Pi (liftT (S Z) (peano c) u) (liftT (S Z) (S (peano c)) v)) := by rfl
      have hstep : eval pTC 1 (liftStack (c :: cs) (Pi u v)) =
          liftStack cs (Pi (liftT (S Z) (peano c) u) (liftT (S Z) (S (peano c)) v)) := by
        simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
      have htail : ReducesToEncTyCore
          (liftStack cs (Pi (liftT (S Z) (peano c) u) (liftT (S Z) (S (peano c)) v)))
          (lfLiftStack cs (.pi (LFTyping.lift 1 c A) (LFTyping.lift 1 (c + 1) B))) := by
        simpa [peano] using ih (hu.lifted c) (hv.lifted (c + 1))
      rcases htail with ⟨w, N, henc, hN⟩
      refine ⟨w, 1 + N, ?_, ?_⟩
      · simpa [lfLiftStack, LFTyping.lift] using henc
      · exact eval_trans_tc 1 N _ _ _ hstep hN

theorem liftable_pi_tc {u v : AST} {A B : LF.Term}
    (hu : LiftablePayload u A) (hv : LiftablePayload v B) :
    LiftablePayload (Pi u v) (.pi A B) := by
  intro cs
  exact liftable_pi_stack_tc cs hu hv

theorem liftable_lam_stack_tc : ∀ (cs : List Nat) {u v : AST} {A b : LF.Term},
    LiftablePayload u A -> LiftablePayload v b ->
    ReducesToEncTyCore (liftStack cs (Lam u v)) (lfLiftStack cs (.lam A b)) := by
  intro cs
  induction cs with
  | nil =>
      intro u v A b hu hv
      exact reduces_lam_tc hu.reduces hv.reduces
  | cons c cs ih =>
      intro u v A b hu hv
      have hroot : oneStep pTC (liftT (S Z) (peano c) (Lam u v)) =
          some (Lam (liftT (S Z) (peano c) u) (liftT (S Z) (S (peano c)) v)) := by rfl
      have hstep : eval pTC 1 (liftStack (c :: cs) (Lam u v)) =
          liftStack cs (Lam (liftT (S Z) (peano c) u) (liftT (S Z) (S (peano c)) v)) := by
        simp only [liftStack, eval, liftStack_descend_lift_step_tc cs c hroot]
      have htail : ReducesToEncTyCore
          (liftStack cs (Lam (liftT (S Z) (peano c) u) (liftT (S Z) (S (peano c)) v)))
          (lfLiftStack cs (.lam (LFTyping.lift 1 c A) (LFTyping.lift 1 (c + 1) b))) := by
        simpa [peano] using ih (hu.lifted c) (hv.lifted (c + 1))
      rcases htail with ⟨w, N, henc, hN⟩
      refine ⟨w, 1 + N, ?_, ?_⟩
      · simpa [lfLiftStack, LFTyping.lift] using henc
      · exact eval_trans_tc 1 N _ _ _ hstep hN

theorem liftable_lam_tc {u v : AST} {A b : LF.Term}
    (hu : LiftablePayload u A) (hv : LiftablePayload v b) :
    LiftablePayload (Lam u v) (.lam A b) := by
  intro cs
  exact liftable_lam_stack_tc cs hu hv

theorem liftable_encTyCore?_tc : ∀ (t : LF.Term) (u : AST),
    encTyCore? t = some u -> LiftablePayload u t := by
  intro t
  induction t with
  | srt s =>
      intro u h
      cases s <;> cases h
      · exact liftable_srt_tc .type
      · exact liftable_srt_tc .kind
  | var k =>
      intro u h
      cases h
      exact liftable_var_tc k
  | con x =>
      intro u h
      exact liftable_con_tc h
  | pi A B ihA ihB =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hB : encTyCore? B with
          | none => simp [hA, hB] at h
          | some B' =>
              simp [hA, hB] at h
              cases h
              exact liftable_pi_tc (ihA A' hA) (ihB B' hB)
  | lam A b ihA ihb =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hb : encTyCore? b with
          | none => simp [hA, hb] at h
          | some b' =>
              simp [hA, hb] at h
              cases h
              exact liftable_lam_tc (ihA A' hA) (ihb b' hb)
  | app f a ihf iha =>
      intro u h
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              cases h
              exact liftable_app_tc (ihf f' hf) (iha a' ha)

theorem liftable_substT_srt_type_tc (j sAst : AST) :
    LiftablePayload (substT j sAst (Srt typeS)) (.srt .type) := by
  exact liftable_of_stack_step
    (u := substT j sAst (Srt typeS)) (v := Srt typeS) (t := .srt .type)
    (by
      intro cs
      exact liftStack_descend_substT_step_tc cs j sAst (Srt typeS) (Srt typeS) rfl)
    (liftable_srt_tc .type)

theorem liftable_substT_srt_kind_tc (j sAst : AST) :
    LiftablePayload (substT j sAst (Srt kindS)) (.srt .kind) := by
  exact liftable_of_stack_step
    (u := substT j sAst (Srt kindS)) (v := Srt kindS) (t := .srt .kind)
    (by
      intro cs
      exact liftStack_descend_substT_step_tc cs j sAst (Srt kindS) (Srt kindS) rfl)
    (liftable_srt_tc .kind)

theorem liftable_substT_con_tc {j sAst u : AST} {x : String}
    (henc : encTyCore? (.con x) = some u) :
    LiftablePayload (substT j sAst u) (.con x) := by
  unfold encTyCore? at henc
  cases hx : encName? x with
  | none => simp [hx] at henc
  | some k =>
      simp [hx] at henc
      subst u
      have henc' : encTyCore? (.con x) = some (Con k) := by
        unfold encTyCore?
        simp [hx]
      exact liftable_of_stack_step
        (u := substT j sAst (Con k)) (v := Con k) (t := .con x)
        (by
          intro cs
          exact liftStack_descend_substT_step_tc cs j sAst (Con k) (Con k) rfl)
        (liftable_con_tc henc')

theorem liftable_substT_var_self_tc (j : Nat) {sAst : AST} {sTerm : LF.Term}
    (hs : LiftablePayload sAst sTerm) :
    LiftablePayload (substT (peano j) sAst (Var (peano j))) sTerm := by
  exact liftable_of_stack_step
    (u := substT (peano j) sAst (Var (peano j))) (v := sAst) (t := sTerm)
    (by
      intro cs
      exact liftStack_descend_substT_step_tc cs (peano j) sAst (Var (peano j)) sAst
        (os_substT_var_self_tc (peano j) sAst))
    hs

theorem liftable_substVarLT_payload_peano_tc (j k : Nat)
    {sAst : AST} {sTerm : LF.Term} (hs : LiftablePayload sAst sTerm) :
    LiftablePayload (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
      (if j < k then .var (k - 1) else .var k) := by
  intro cs
  rcases hs.reduces with ⟨sVal, Ns, hsEnc, hsEval⟩
  have hsNorm : IsNormal pTC sVal := isnormal_encTyCore?_tc sTerm sVal hsEnc
  obtain ⟨Mpayload, hMpayload⟩ :=
    cong_eval_tc
      (fun s => liftStack cs (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k))))
      (fun s s' hstep =>
        liftStack_hcong_substVarLT2_lt_tc cs (peano j) (peano k) (peano j) (peano k)
          (isnormal_peano_tc j) s s' hstep)
      Ns hsEval hsNorm
  obtain ⟨Nguard, hguard⟩ :=
    liftStack_substVarLT_lt_final_tc j k cs (peano j) sVal (peano k)
      (isnormal_peano_tc j) hsNorm (isnormal_peano_tc k)
  by_cases hlt : j < k
  · rcases liftStack_var_predN_tc cs k with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Mpayload + (Nguard + Ntail), ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs (substVarLT (peano j) sVal (peano k) (ltT (peano j) (peano k)))) =
          liftStack cs (Var (predN (peano k))) := by
        simpa [hlt] using hguard
      have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
      exact eval_trans_tc Mpayload (Nguard + Ntail) _ _ _ hMpayload htail'
  · rcases (liftable_var_pair_tc cs).1 k with ⟨v, Ntail, henc, htail⟩
    refine ⟨v, Mpayload + (Nguard + Ntail), ?_, ?_⟩
    · simpa [hlt] using henc
    · have hguard' : eval pTC Nguard
          (liftStack cs (substVarLT (peano j) sVal (peano k) (ltT (peano j) (peano k)))) =
          liftStack cs (Var (peano k)) := by
        simpa [hlt] using hguard
      have htail' := eval_trans_tc Nguard Ntail _ _ _ hguard' htail
      exact eval_trans_tc Mpayload (Nguard + Ntail) _ _ _ hMpayload htail'

theorem liftable_substT_var_miss_tc (j k : Nat) {sAst : AST} {sTerm : LF.Term}
    (h : k ≠ j) (hs : LiftablePayload sAst sTerm) :
    LiftablePayload (substT (peano j) sAst (Var (peano k)))
      (if j < k then .var (k - 1) else .var k) := by
  have hneq : j ≠ k := by
    intro hjk
    exact h hjk.symm
  exact liftable_of_stack_step
    (u := substT (peano j) sAst (Var (peano k)))
    (v := substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
    (t := if j < k then .var (k - 1) else .var k)
    (by
      intro cs
      exact liftStack_descend_substT_step_tc cs (peano j) sAst (Var (peano k))
        (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
        (os_substT_var_miss_tc j k sAst hneq))
    (liftable_substVarLT_payload_peano_tc j k hs)

theorem liftable_substT_pi_tc {j sAst A B : AST} {ATerm BTerm : LF.Term}
    (hA : LiftablePayload (substT j sAst A) ATerm)
    (hB : LiftablePayload (substT (S j) (liftT (S Z) Z sAst) B) BTerm) :
    LiftablePayload (substT j sAst (Pi A B)) (.pi ATerm BTerm) := by
  exact liftable_of_stack_step
    (u := substT j sAst (Pi A B))
    (v := Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B))
    (t := .pi ATerm BTerm)
    (by
      intro cs
      exact liftStack_descend_substT_step_tc cs j sAst (Pi A B)
        (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B)) rfl)
    (liftable_pi_tc hA hB)

theorem liftable_substT_lam_tc {j sAst A b : AST} {ATerm bTerm : LF.Term}
    (hA : LiftablePayload (substT j sAst A) ATerm)
    (hb : LiftablePayload (substT (S j) (liftT (S Z) Z sAst) b) bTerm) :
    LiftablePayload (substT j sAst (Lam A b)) (.lam ATerm bTerm) := by
  exact liftable_of_stack_step
    (u := substT j sAst (Lam A b))
    (v := Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b))
    (t := .lam ATerm bTerm)
    (by
      intro cs
      exact liftStack_descend_substT_step_tc cs j sAst (Lam A b)
        (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b)) rfl)
    (liftable_lam_tc hA hb)

theorem liftable_substT_app_tc {j sAst f a : AST} {fTerm aTerm : LF.Term}
    (hf : LiftablePayload (substT j sAst f) fTerm)
    (ha : LiftablePayload (substT j sAst a) aTerm) :
    LiftablePayload (substT j sAst (App f a)) (.app fTerm aTerm) := by
  exact liftable_of_stack_step
    (u := substT j sAst (App f a))
    (v := App (substT j sAst f) (substT j sAst a))
    (t := .app fTerm aTerm)
    (by
      intro cs
      exact liftStack_descend_substT_step_tc cs j sAst (App f a)
        (App (substT j sAst f) (substT j sAst a)) rfl)
    (liftable_app_tc hf ha)

theorem liftable_substT_encTyCore_tc :
    ∀ (body : LF.Term) (bodyAst : AST) (j : Nat) (sAst : AST) (sTerm : LF.Term),
      encTyCore? body = some bodyAst -> LiftablePayload sAst sTerm ->
        LiftablePayload (substT (peano j) sAst bodyAst) (LFTyping.subst j sTerm body) := by
  intro body
  induction body with
  | srt sort =>
      intro bodyAst j sAst sTerm h hs
      cases sort <;> simp [encTyCore?] at h <;> subst bodyAst
      · simpa [LFTyping.subst] using liftable_substT_srt_type_tc (peano j) sAst
      · simpa [LFTyping.subst] using liftable_substT_srt_kind_tc (peano j) sAst
  | var k =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      subst bodyAst
      by_cases hkj : k = j
      · subst k
        simpa [LFTyping.subst] using liftable_substT_var_self_tc j hs
      · simpa [LFTyping.subst, hkj] using liftable_substT_var_miss_tc j k hkj hs
  | con x =>
      intro bodyAst j sAst sTerm h hs
      simpa [LFTyping.subst] using
        liftable_substT_con_tc (j := peano j) (sAst := sAst) (u := bodyAst) (x := x) h
  | pi A B ihA ihB =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hB : encTyCore? B with
          | none => simp [hA, hB] at h
          | some B' =>
              simp [hA, hB] at h
              subst bodyAst
              have hAlift : LiftablePayload (substT (peano j) sAst A')
                  (LFTyping.subst j sTerm A) :=
                ihA A' j sAst sTerm hA hs
              have hBlift : LiftablePayload (substT (S (peano j)) (liftT (S Z) Z sAst) B')
                  (LFTyping.subst (j + 1) (LFTyping.lift 1 0 sTerm) B) := by
                simpa [peano] using
                  ihB B' (j + 1) (liftT (S Z) Z sAst)
                    (LFTyping.lift 1 0 sTerm) hB (liftablePayload_lift1 hs)
              simpa [LFTyping.subst] using liftable_substT_pi_tc hAlift hBlift
  | lam A b ihA ihb =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hb : encTyCore? b with
          | none => simp [hA, hb] at h
          | some b' =>
              simp [hA, hb] at h
              subst bodyAst
              have hAlift : LiftablePayload (substT (peano j) sAst A')
                  (LFTyping.subst j sTerm A) :=
                ihA A' j sAst sTerm hA hs
              have hblift : LiftablePayload (substT (S (peano j)) (liftT (S Z) Z sAst) b')
                  (LFTyping.subst (j + 1) (LFTyping.lift 1 0 sTerm) b) := by
                simpa [peano] using
                  ihb b' (j + 1) (liftT (S Z) Z sAst)
                    (LFTyping.lift 1 0 sTerm) hb (liftablePayload_lift1 hs)
              simpa [LFTyping.subst] using liftable_substT_lam_tc hAlift hblift
  | app f a ihf iha =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              subst bodyAst
              have hflift : LiftablePayload (substT (peano j) sAst f')
                  (LFTyping.subst j sTerm f) :=
                ihf f' j sAst sTerm hf hs
              have halift : LiftablePayload (substT (peano j) sAst a')
                  (LFTyping.subst j sTerm a) :=
                iha a' j sAst sTerm ha hs
              simpa [LFTyping.subst] using liftable_substT_app_tc hflift halift

inductive FirstLiftableNF (t : LF.Term) (u : AST) (call : AST) : Prop where
  | intro {payload : AST} {N M : Nat} :
      encTyCore? t = some u ->
      eval pTC N call = someT payload ->
      (∀ k, k < N -> NFActiveShape (eval pTC k call)) ->
      LiftablePayload payload t ->
      eval pTC M payload = u ->
      FirstLiftableNF t u call

inductive FirstStrongNF (t : LF.Term) (u : AST) (call : AST) : Prop where
  | intro {payload : AST} {N M : Nat} :
      encTyCore? t = some u ->
      eval pTC N call = someT payload ->
      (∀ k, k < N -> NFActiveShape (eval pTC k call)) ->
      LiftablePayload payload t ->
      LiftablePayload u t ->
      eval pTC M payload = u ->
      FirstStrongNF t u call

theorem FirstStrongNF.toFirstLiftable {t : LF.Term} {u call : AST}
    (h : FirstStrongNF t u call) : FirstLiftableNF t u call := by
  cases h with
  | @intro payload N M henc hmatch hguard hpayload _ heval =>
      exact FirstLiftableNF.intro (payload := payload) (N := N) (M := M)
        henc hmatch hguard hpayload heval

theorem FirstStrongNF.finalLiftable {t : LF.Term} {u call : AST}
    (h : FirstStrongNF t u call) : LiftablePayload u t := by
  cases h with
  | @intro _ _ _ _ _ _ _ hfinal _ => exact hfinal

theorem FirstStrongNF.enc {t : LF.Term} {u call : AST}
    (h : FirstStrongNF t u call) : encTyCore? t = some u := by
  cases h with
  | @intro _ _ _ henc _ _ _ _ _ => exact henc

def ReplayablePayload (u : AST) (t : LF.Term) : Prop :=
  LiftablePayload u t ∧
    ∀ fuelNat : Nat, ∃ v,
      FirstStrongNF (LFTyping.nf LFTyping.corpusSig fuelNat t) v
        (nfT (peano fuelNat) u)

def StackReplayablePayload (u : AST) (t : LF.Term) : Prop :=
  ∀ cs : List Nat, ReplayablePayload (liftStack cs u) (lfLiftStack cs t)

theorem StackReplayablePayload.replay {u : AST} {t : LF.Term}
    (h : StackReplayablePayload u t) : ReplayablePayload u t := by
  exact h []

theorem StackReplayablePayload.lifted {u : AST} {t : LF.Term}
    (h : StackReplayablePayload u t) (c : Nat) :
    StackReplayablePayload (liftT (S Z) (peano c) u) (LFTyping.lift 1 c t) := by
  intro cs
  exact h (c :: cs)

inductive FirstReplayNF (t : LF.Term) (u : AST) (call : AST) : Prop where
  | intro {payload : AST} {N M : Nat} :
      encTyCore? t = some u ->
      eval pTC N call = someT payload ->
      (∀ k, k < N -> NFActiveShape (eval pTC k call)) ->
      LiftablePayload payload t ->
      StackReplayablePayload payload t ->
      LiftablePayload u t ->
      StackReplayablePayload u t ->
      eval pTC M payload = u ->
      FirstReplayNF t u call

theorem FirstReplayNF.toStrong {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) : FirstStrongNF t u call := by
  cases h with
  | @intro payload N M henc hmatch hguard hpayload _ hfinal _ heval =>
      exact FirstStrongNF.intro (payload := payload) (N := N) (M := M)
        henc hmatch hguard hpayload hfinal heval

theorem FirstReplayNF.toFirstLiftable {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) : FirstLiftableNF t u call :=
  h.toStrong.toFirstLiftable

theorem FirstReplayNF.payloadReplay {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) :
    ∃ payload, StackReplayablePayload payload t ∧ ∃ N, eval pTC N call = someT payload := by
  cases h with
  | @intro payload N _ _ hmatch _ _ hpayloadReplay _ _ _ =>
      exact ⟨payload, hpayloadReplay, N, hmatch⟩

theorem FirstReplayNF.finalReplay {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) : StackReplayablePayload u t := by
  cases h with
  | @intro _ _ _ _ _ _ _ _ _ hfinalReplay _ => exact hfinalReplay

theorem FirstReplayNF.payloadLiftable {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) :
    ∃ payload, LiftablePayload payload t ∧ StackReplayablePayload payload t ∧
      ∃ N, eval pTC N call = someT payload := by
  cases h with
  | @intro payload N _ _ hmatch _ hpayload hpayloadReplay _ _ _ =>
      exact ⟨payload, hpayload, hpayloadReplay, N, hmatch⟩

theorem FirstReplayNF.finalLiftable {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) : LiftablePayload u t := by
  cases h with
  | @intro _ _ _ _ _ _ _ _ hfinal _ _ => exact hfinal

theorem FirstReplayNF.payloadEvalFinal {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) :
    ∃ payload, StackReplayablePayload payload t ∧
      ∃ N M, eval pTC N call = someT payload ∧ eval pTC M payload = u := by
  cases h with
  | @intro payload N M _ hmatch _ _ hpayloadReplay _ _ heval =>
      exact ⟨payload, hpayloadReplay, N, M, hmatch, heval⟩

theorem FirstReplayNF.enc {t : LF.Term} {u call : AST}
    (h : FirstReplayNF t u call) : encTyCore? t = some u := by
  cases h with
  | @intro _ _ _ henc _ _ _ _ _ _ _ => exact henc

theorem FirstLiftableNF.toStrong {t : LF.Term} {u call : AST}
    (h : FirstLiftableNF t u call) : FirstStrongNF t u call := by
  cases h with
  | @intro payload N M henc hmatch hguard hpayload heval =>
      exact FirstStrongNF.intro (payload := payload) (N := N) (M := M)
        henc hmatch hguard hpayload (liftable_encTyCore?_tc t u henc) heval

theorem first_strong_nf_prepend {t : LF.Term} {u call next : AST}
    (hstep : eval pTC 1 call = next) (hactive : NFActiveShape call)
    (hnext : FirstStrongNF t u next) : FirstStrongNF t u call := by
  cases hnext with
  | @intro payload N M henc hmatch hguard hpayload hfinal heval =>
      refine FirstStrongNF.intro (payload := payload) (N := 1 + N) (M := M)
        henc ?_ ?_ hpayload hfinal heval
      · have htotal : eval pTC (1 + N) call = eval pTC N next :=
          eval_trans_tc 1 N call next (eval pTC N next) hstep rfl
        rw [htotal]
        exact hmatch
      · intro k hk
        cases k with
        | zero =>
            simpa only [eval] using hactive
        | succ k =>
            have hk' : Nat.succ k < Nat.succ N := by
              simpa only [Nat.one_add] using hk
            have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
            have htotal : eval pTC (Nat.succ k) call = eval pTC k next := by
              have h := eval_trans_tc 1 k call next (eval pTC k next) hstep rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [htotal]
            exact hguard k hkN

theorem first_strong_nf_prefix {t : LF.Term} {u call next : AST}
    {M : Nat} (hctx : eval pTC M call = next)
    (hctxGuard : ∀ k, k < M -> NFActiveShape (eval pTC k call))
    (hnext : FirstStrongNF t u next) : FirstStrongNF t u call := by
  cases hnext with
  | @intro payload N MP henc hmatch hguard hpayload hfinal heval =>
      refine FirstStrongNF.intro (payload := payload) (N := M + N) (M := MP)
        henc ?_ ?_ hpayload hfinal heval
      · exact eval_trans_tc M N call next (someT payload) hctx hmatch
      · intro k hk
        by_cases hkM : k < M
        · exact hctxGuard k hkM
        · have hge : M ≤ k := Nat.le_of_not_gt hkM
          have hkN : k - M < N := by omega
          have hdecomp : k = M + (k - M) := by omega
          rw [hdecomp]
          have htotal : eval pTC (M + (k - M)) call =
              eval pTC (k - M) next := by
            exact eval_trans_tc M (k - M) call next
              (eval pTC (k - M) next) hctx rfl
          rw [htotal]
          exact hguard (k - M) hkN

theorem first_replay_nf_prepend {t : LF.Term} {u call next : AST}
    (hstep : eval pTC 1 call = next) (hactive : NFActiveShape call)
    (hnext : FirstReplayNF t u next) : FirstReplayNF t u call := by
  cases hnext with
  | @intro payload N M henc hmatch hguard hpayload hpayloadReplay hfinal hfinalReplay heval =>
      refine FirstReplayNF.intro (payload := payload) (N := 1 + N) (M := M)
        henc ?_ ?_ hpayload hpayloadReplay hfinal hfinalReplay heval
      · have htotal : eval pTC (1 + N) call = eval pTC N next :=
          eval_trans_tc 1 N call next (eval pTC N next) hstep rfl
        rw [htotal]
        exact hmatch
      · intro k hk
        cases k with
        | zero =>
            simpa only [eval] using hactive
        | succ k =>
            have hk' : Nat.succ k < Nat.succ N := by
              simpa only [Nat.one_add] using hk
            have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
            have htotal : eval pTC (Nat.succ k) call = eval pTC k next := by
              have h := eval_trans_tc 1 k call next (eval pTC k next) hstep rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [htotal]
            exact hguard k hkN

theorem first_replay_nf_prefix {t : LF.Term} {u call next : AST}
    {M : Nat} (hctx : eval pTC M call = next)
    (hctxGuard : ∀ k, k < M -> NFActiveShape (eval pTC k call))
    (hnext : FirstReplayNF t u next) : FirstReplayNF t u call := by
  cases hnext with
  | @intro payload N MP henc hmatch hguard hpayload hpayloadReplay hfinal hfinalReplay heval =>
      refine FirstReplayNF.intro (payload := payload) (N := M + N) (M := MP)
        henc ?_ ?_ hpayload hpayloadReplay hfinal hfinalReplay heval
      · exact eval_trans_tc M N call next (someT payload) hctx hmatch
      · intro k hk
        by_cases hkM : k < M
        · exact hctxGuard k hkM
        · have hge : M ≤ k := Nat.le_of_not_gt hkM
          have hkN : k - M < N := by omega
          have hdecomp : k = M + (k - M) := by omega
          rw [hdecomp]
          have htotal : eval pTC (M + (k - M)) call =
              eval pTC (k - M) next := by
            exact eval_trans_tc M (k - M) call next
              (eval pTC (k - M) next) hctx rfl
          rw [htotal]
          exact hguard (k - M) hkN

theorem FirstLiftableNF.toPayload {t : LF.Term} {u call : AST}
    (h : FirstLiftableNF t u call) : FirstPayloadNF u call := by
  cases h with
  | @intro payload N M _ hmatch hguard _ hpayload =>
      exact FirstPayloadNF.intro (payload := payload) (N := N) (M := M)
        hmatch hguard hpayload

theorem FirstLiftableNF.toEval {t : LF.Term} {u call : AST}
    (h : FirstLiftableNF t u call) :
    ∃ N, eval pTC N call = someT u := by
  have hpayloadFirst : FirstPayloadNF u call := FirstLiftableNF.toPayload h
  cases h with
  | @intro _ _ _ henc _ _ _ _ =>
      exact first_payload_nf_to_eval hpayloadFirst (isnormal_encTyCore?_tc t u henc)

theorem FirstLiftableNF.enc {t : LF.Term} {u call : AST}
    (h : FirstLiftableNF t u call) : encTyCore? t = some u := by
  cases h with
  | @intro _ _ _ henc _ _ _ _ => exact henc

theorem first_liftable_nf_prepend {t : LF.Term} {u call next : AST}
    (hstep : eval pTC 1 call = next) (hactive : NFActiveShape call)
    (hnext : FirstLiftableNF t u next) : FirstLiftableNF t u call := by
  cases hnext with
  | @intro payload N M henc hmatch hguard hlift hpayload =>
      refine FirstLiftableNF.intro (payload := payload) (N := 1 + N) (M := M)
        henc ?_ ?_ hlift hpayload
      · have htotal : eval pTC (1 + N) call = eval pTC N next :=
          eval_trans_tc 1 N call next (eval pTC N next) hstep rfl
        rw [htotal]
        exact hmatch
      · intro k hk
        cases k with
        | zero =>
            simpa only [eval] using hactive
        | succ k =>
            have hk' : Nat.succ k < Nat.succ N := by
              simpa only [Nat.one_add] using hk
            have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
            have htotal : eval pTC (Nat.succ k) call = eval pTC k next := by
              have h := eval_trans_tc 1 k call next (eval pTC k next) hstep rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [htotal]
            exact hguard k hkN

theorem nfT_z_first_liftable {t : LF.Term} {u call : AST}
    (henc : encTyCore? t = some u)
    (hlift : LiftablePayload call t)
    (hpayload : ∃ M, eval pTC M call = u) :
    FirstLiftableNF t u (nfT Z call) := by
  obtain ⟨M, hM⟩ := hpayload
  exact FirstLiftableNF.intro (payload := call) (N := 1) (M := M)
    henc (nfT_z_tc call)
    (by
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
      subst k
      exact NFActiveShape.nf Z call)
    hlift hM

theorem nfT_z_first_strong {t : LF.Term} {u call : AST}
    (henc : encTyCore? t = some u)
    (hcall : LiftablePayload call t)
    (hfinal : LiftablePayload u t)
    (hpayload : ∃ M, eval pTC M call = u) :
    FirstStrongNF t u (nfT Z call) := by
  obtain ⟨M, hM⟩ := hpayload
  exact FirstStrongNF.intro (payload := call) (N := 1) (M := M)
    henc (nfT_z_tc call)
    (by
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
      subst k
      exact NFActiveShape.nf Z call)
    hcall hfinal hM

theorem nfT_z_first_replay {t : LF.Term} {u call : AST}
    (henc : encTyCore? t = some u)
    (hcall : LiftablePayload call t)
    (hcallReplay : StackReplayablePayload call t)
    (hfinal : LiftablePayload u t)
    (hfinalReplay : StackReplayablePayload u t)
    (hpayload : ∃ M, eval pTC M call = u) :
    FirstReplayNF t u (nfT Z call) := by
  obtain ⟨M, hM⟩ := hpayload
  exact FirstReplayNF.intro (payload := call) (N := 1) (M := M)
    henc (nfT_z_tc call)
    (by
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
      subst k
      exact NFActiveShape.nf Z call)
    hcall hcallReplay hfinal hfinalReplay hM

theorem replayablePayload_prepend_nfT_arg {u v : AST} {t : LF.Term}
    (hu : LiftablePayload u t)
    (hstep : ∀ fuelNat : Nat,
      oneStep pTC (nfT (peano (Nat.succ fuelNat)) u) =
        some (nfT (peano (Nat.succ fuelNat)) v))
    (hv : ReplayablePayload v t) : ReplayablePayload u t := by
  constructor
  · exact hu
  · intro fuelNat
    cases fuelNat with
    | zero =>
        rcases hu.reduces with ⟨w, N, henc, hN⟩
        refine ⟨w, ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_z_first_strong henc hu (liftable_encTyCore?_tc t w henc) ⟨N, hN⟩)
    | succ fuelPred =>
        obtain ⟨w, hw⟩ := hv.2 (Nat.succ fuelPred)
        refine ⟨w, ?_⟩
        have h1 : eval pTC 1 (nfT (peano (Nat.succ fuelPred)) u) =
            nfT (peano (Nat.succ fuelPred)) v := by
          simp only [eval, hstep fuelPred]
        exact first_strong_nf_prepend h1
          (NFActiveShape.nf (peano (Nat.succ fuelPred)) u) hw

theorem replayablePayload_prefix_nfT_arg {u v : AST} {t : LF.Term}
    (hu : LiftablePayload u t)
    (hctx : ∀ fuelNat : Nat, ∃ M,
      eval pTC M (nfT (peano (Nat.succ fuelNat)) u) =
        nfT (peano (Nat.succ fuelNat)) v ∧
      ∀ k, k < M -> NFActiveShape (eval pTC k (nfT (peano (Nat.succ fuelNat)) u)))
    (hv : ReplayablePayload v t) : ReplayablePayload u t := by
  constructor
  · exact hu
  · intro fuelNat
    cases fuelNat with
    | zero =>
        rcases hu.reduces with ⟨w, N, henc, hN⟩
        refine ⟨w, ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_z_first_strong henc hu (liftable_encTyCore?_tc t w henc) ⟨N, hN⟩)
    | succ fuelPred =>
        obtain ⟨w, hw⟩ := hv.2 (Nat.succ fuelPred)
        obtain ⟨M, hM, hMguard⟩ := hctx fuelPred
        refine ⟨w, ?_⟩
        exact first_strong_nf_prefix hM hMguard hw

theorem stackReplayablePayload_of_step {u v : AST} {t : LF.Term}
    (hstep : ∀ cs : List Nat,
      oneStep pTC (liftStack cs u) = some (liftStack cs v))
    (hnfstep : ∀ (cs : List Nat) (fuelNat : Nat),
      oneStep pTC (nfT (peano (Nat.succ fuelNat)) (liftStack cs u)) =
        some (nfT (peano (Nat.succ fuelNat)) (liftStack cs v)))
    (hv : StackReplayablePayload v t) : StackReplayablePayload u t := by
  intro cs
  exact replayablePayload_prepend_nfT_arg
    (u := liftStack cs u) (v := liftStack cs v) (t := lfLiftStack cs t)
    (liftable_of_stack_step
      (u := liftStack cs u) (v := liftStack cs v) (t := lfLiftStack cs t)
      (by
        intro ds
        calc
          oneStep pTC (liftStack ds (liftStack cs u)) =
              oneStep pTC (liftStack (cs ++ ds) u) := by
            rw [liftStack_append cs ds u]
          _ = some (liftStack (cs ++ ds) v) := hstep (cs ++ ds)
          _ = some (liftStack ds (liftStack cs v)) := by
            rw [liftStack_append cs ds v])
      (hv cs).1)
    (by
      intro fuelNat
      exact hnfstep cs fuelNat)
    (hv cs)

theorem stackReplayablePayload_lift_step_tc (c : Nat) {u v : AST} {t : LF.Term}
    (h : oneStep pTC (liftT (S Z) (peano c) u) = some v)
    (hv : StackReplayablePayload v t) :
    StackReplayablePayload (liftT (S Z) (peano c) u) t := by
  apply stackReplayablePayload_of_step
  · intro cs
    exact liftStack_descend_lift_step_tc cs c h
  · intro cs fuelNat
    simpa [peano] using
      hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c u v
        (isnormal_peano_tc fuelNat) h
  · exact hv

theorem stackReplayablePayload_substT_var_self_tc (j : Nat)
    {sAst : AST} {sTerm : LF.Term}
    (hs : StackReplayablePayload sAst sTerm) :
    StackReplayablePayload (substT (peano j) sAst (Var (peano j))) sTerm := by
  apply stackReplayablePayload_of_step
  · intro cs
    exact liftStack_descend_substT_step_tc cs (peano j) sAst (Var (peano j)) sAst
      (os_substT_var_self_tc (peano j) sAst)
  · intro cs fuelNat
    simpa [peano] using
      hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat)
        (peano j) sAst (Var (peano j)) sAst
        (isnormal_peano_tc fuelNat) (os_substT_var_self_tc (peano j) sAst)
  · exact hs

theorem stackReplayablePayload_substT_pi_step_tc
    {j sAst A B : AST} {ATerm BTerm : LF.Term}
    (hnext : StackReplayablePayload
      (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B))
      (.pi ATerm BTerm)) :
    StackReplayablePayload (substT j sAst (Pi A B)) (.pi ATerm BTerm) := by
  apply stackReplayablePayload_of_step
  · intro cs
    exact liftStack_descend_substT_step_tc cs j sAst (Pi A B)
      (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B)) rfl
  · intro cs fuelNat
    simpa [peano] using
      hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat) j sAst (Pi A B)
        (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B))
        (isnormal_peano_tc fuelNat) rfl
  · exact hnext

theorem stackReplayablePayload_substT_lam_step_tc
    {j sAst A b : AST} {ATerm bTerm : LF.Term}
    (hnext : StackReplayablePayload
      (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b))
      (.lam ATerm bTerm)) :
    StackReplayablePayload (substT j sAst (Lam A b)) (.lam ATerm bTerm) := by
  apply stackReplayablePayload_of_step
  · intro cs
    exact liftStack_descend_substT_step_tc cs j sAst (Lam A b)
      (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b)) rfl
  · intro cs fuelNat
    simpa [peano] using
      hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat) j sAst (Lam A b)
        (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b))
        (isnormal_peano_tc fuelNat) rfl
  · exact hnext

theorem stackReplayablePayload_substT_app_step_tc
    {j sAst f a : AST} {fTerm aTerm : LF.Term}
    (hnext : StackReplayablePayload (App (substT j sAst f) (substT j sAst a))
      (.app fTerm aTerm)) :
    StackReplayablePayload (substT j sAst (App f a)) (.app fTerm aTerm) := by
  apply stackReplayablePayload_of_step
  · intro cs
    exact liftStack_descend_substT_step_tc cs j sAst (App f a)
      (App (substT j sAst f) (substT j sAst a)) rfl
  · intro cs fuelNat
    simpa [peano] using
      hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat) j sAst (App f a)
        (App (substT j sAst f) (substT j sAst a))
        (isnormal_peano_tc fuelNat) rfl
  · exact hnext

theorem nfT_z_first_liftable_of_reduces {t : LF.Term} {call : AST}
    (hlift : LiftablePayload call t) :
    ∃ u, FirstLiftableNF t u (nfT Z call) := by
  rcases hlift.reduces with ⟨u, M, henc, hM⟩
  exact ⟨u, nfT_z_first_liftable henc hlift ⟨M, hM⟩⟩

theorem nfT_srt_first_liftable (fuel : AST) (s : LF.Srt) :
    FirstLiftableNF (.srt s) (Srt (match s with | .type => typeS | .kind => kindS))
      (nfT (S fuel) (Srt (match s with | .type => typeS | .kind => kindS))) := by
  cases s
  · exact FirstLiftableNF.intro (payload := Srt typeS) (N := 1) (M := 0)
      rfl (nfT_srt_tc fuel typeS)
      (by
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        subst k
        exact NFActiveShape.nf (S fuel) (Srt typeS))
      (liftable_srt_tc .type) rfl
  · exact FirstLiftableNF.intro (payload := Srt kindS) (N := 1) (M := 0)
      rfl (nfT_srt_tc fuel kindS)
      (by
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        subst k
        exact NFActiveShape.nf (S fuel) (Srt kindS))
      (liftable_srt_tc .kind) rfl

theorem nfT_srt_first_strong (fuel : AST) (s : LF.Srt) :
    FirstStrongNF (.srt s) (Srt (match s with | .type => typeS | .kind => kindS))
      (nfT (S fuel) (Srt (match s with | .type => typeS | .kind => kindS))) := by
  cases s
  · exact FirstStrongNF.intro (payload := Srt typeS) (N := 1) (M := 0)
      rfl (nfT_srt_tc fuel typeS)
      (by
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        subst k
        exact NFActiveShape.nf (S fuel) (Srt typeS))
      (liftable_srt_tc .type) (liftable_srt_tc .type) rfl
  · exact FirstStrongNF.intro (payload := Srt kindS) (N := 1) (M := 0)
      rfl (nfT_srt_tc fuel kindS)
      (by
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        subst k
        exact NFActiveShape.nf (S fuel) (Srt kindS))
      (liftable_srt_tc .kind) (liftable_srt_tc .kind) rfl

theorem stackReplayablePayload_srt_atom_tc (s : LF.Srt) (u : AST)
    (henc : encTyCore? (.srt s) = some u)
    (hroot : ∀ c : Nat, oneStep pTC (liftT (S Z) (peano c) u) = some u)
    (hnf : ∀ fuel : AST, FirstStrongNF (.srt s) u (nfT (S fuel) u)) :
    StackReplayablePayload u (.srt s) := by
  intro cs
  induction cs with
  | nil =>
      constructor
      · exact liftable_encTyCore?_tc (.srt s) u henc
      · intro fuelNat
        cases fuelNat with
        | zero =>
            refine ⟨u, ?_⟩
            simpa [peano, LFTyping.nf, liftStack, lfLiftStack] using
              (nfT_z_first_strong (t := .srt s)
                (u := u) (call := u)
                henc (liftable_encTyCore?_tc (.srt s) u henc)
                (liftable_encTyCore?_tc (.srt s) u henc) ⟨0, rfl⟩)
        | succ fuelPred =>
            refine ⟨u, ?_⟩
            simpa [peano, LFTyping.nf, liftStack, lfLiftStack] using hnf (peano fuelPred)
  | cons c cs ih =>
      have hnext : ReplayablePayload (liftStack cs u) (lfLiftStack cs (.srt s)) := ih
      have hthis : ReplayablePayload
          (liftStack cs (liftT (S Z) (peano c) u))
          (lfLiftStack cs (.srt s)) := by
        exact replayablePayload_prepend_nfT_arg
          (u := liftStack cs (liftT (S Z) (peano c) u))
          (v := liftStack cs u)
          (t := lfLiftStack cs (.srt s))
          (liftable_of_stack_step
            (u := liftStack cs (liftT (S Z) (peano c) u))
            (v := liftStack cs u)
            (t := lfLiftStack cs (.srt s))
            (by
              intro ds
              calc
                oneStep pTC
                    (liftStack ds (liftStack cs (liftT (S Z) (peano c) u))) =
                    oneStep pTC (liftStack (cs ++ ds) (liftT (S Z) (peano c) u)) := by
                  rw [liftStack_append cs ds]
                _ = some (liftStack (cs ++ ds) u) :=
                  liftStack_descend_lift_step_tc (cs ++ ds) c (hroot c)
                _ = some (liftStack ds (liftStack cs u)) := by
                  rw [liftStack_append cs ds])
            hnext.1)
          (by
            intro fuelNat
            simpa [peano] using
              hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c u u
                (isnormal_peano_tc fuelNat) (hroot c))
          hnext
      simpa [liftStack, lfLiftStack, LFTyping.lift] using hthis

theorem stackReplayablePayload_srt_tc (s : LF.Srt) :
    StackReplayablePayload
      (Srt (match s with | .type => typeS | .kind => kindS)) (.srt s) := by
  cases s
  · exact stackReplayablePayload_srt_atom_tc .type (Srt typeS) rfl
      (by intro c; rfl)
      (by intro fuel; exact nfT_srt_first_strong fuel .type)
  · exact stackReplayablePayload_srt_atom_tc .kind (Srt kindS) rfl
      (by intro c; rfl)
      (by intro fuel; exact nfT_srt_first_strong fuel .kind)

theorem stackReplayablePayload_substT_srt_tc (j sAst : AST) (s : LF.Srt) :
    StackReplayablePayload
      (substT j sAst (Srt (match s with | .type => typeS | .kind => kindS))) (.srt s) := by
  cases s
  · apply stackReplayablePayload_of_step
    · intro cs
      exact liftStack_descend_substT_step_tc cs j sAst (Srt typeS) (Srt typeS) rfl
    · intro cs fuelNat
      simpa [peano] using
        hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat)
          j sAst (Srt typeS) (Srt typeS) (isnormal_peano_tc fuelNat) rfl
    · exact stackReplayablePayload_srt_tc .type
  · apply stackReplayablePayload_of_step
    · intro cs
      exact liftStack_descend_substT_step_tc cs j sAst (Srt kindS) (Srt kindS) rfl
    · intro cs fuelNat
      simpa [peano] using
        hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat)
          j sAst (Srt kindS) (Srt kindS) (isnormal_peano_tc fuelNat) rfl
    · exact stackReplayablePayload_srt_tc .kind

theorem nfT_srt_first_replay (fuel : AST) (s : LF.Srt) :
    FirstReplayNF (.srt s) (Srt (match s with | .type => typeS | .kind => kindS))
      (nfT (S fuel) (Srt (match s with | .type => typeS | .kind => kindS))) := by
  cases s
  · have hrep := stackReplayablePayload_srt_tc .type
    exact FirstReplayNF.intro (payload := Srt typeS) (N := 1) (M := 0)
      rfl (nfT_srt_tc fuel typeS)
      (by
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        subst k
        exact NFActiveShape.nf (S fuel) (Srt typeS))
      (liftable_srt_tc .type) hrep (liftable_srt_tc .type) hrep rfl
  · have hrep := stackReplayablePayload_srt_tc .kind
    exact FirstReplayNF.intro (payload := Srt kindS) (N := 1) (M := 0)
      rfl (nfT_srt_tc fuel kindS)
      (by
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        subst k
        exact NFActiveShape.nf (S fuel) (Srt kindS))
      (liftable_srt_tc .kind) hrep (liftable_srt_tc .kind) hrep rfl

theorem nfT_substT_srt_first_replay (fuel j sAst : AST) (s : LF.Srt)
    (hfuel : IsNormal pTC fuel) :
    FirstReplayNF (.srt s) (Srt (match s with | .type => typeS | .kind => kindS))
      (nfT (S fuel)
        (substT j sAst (Srt (match s with | .type => typeS | .kind => kindS)))) := by
  cases s
  · have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (Srt typeS))) =
        nfT (S fuel) (Srt typeS) := by
      simp only [eval,
        hcong_nfT_s_substT_arg_tc fuel j sAst (Srt typeS) (Srt typeS)
          hfuel rfl]
    exact first_replay_nf_prepend hstep
      (NFActiveShape.nf (S fuel) (substT j sAst (Srt typeS)))
      (nfT_srt_first_replay fuel .type)
  · have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (Srt kindS))) =
        nfT (S fuel) (Srt kindS) := by
      simp only [eval,
        hcong_nfT_s_substT_arg_tc fuel j sAst (Srt kindS) (Srt kindS)
          hfuel rfl]
    exact first_replay_nf_prepend hstep
      (NFActiveShape.nf (S fuel) (substT j sAst (Srt kindS)))
      (nfT_srt_first_replay fuel .kind)

theorem nfT_substT_srt_payload_first_replay (fuelNat j : Nat)
    (s : LF.Srt) {sAst : AST} {sTerm : LF.Term} :
    ∃ v,
      FirstReplayNF (LFTyping.nf LFTyping.corpusSig fuelNat
        (LFTyping.subst j sTerm (.srt s))) v
        (nfT (peano fuelNat)
          (substT (peano j) sAst
            (Srt (match s with | .type => typeS | .kind => kindS)))) := by
  cases s
  · cases fuelNat with
    | zero =>
        refine ⟨Srt typeS, ?_⟩
        have hpayload : ∃ M, eval pTC M (substT (peano j) sAst (Srt typeS)) =
            Srt typeS := ⟨1, rfl⟩
        simpa [peano, LFTyping.nf, LFTyping.subst] using
          (nfT_z_first_replay (t := .srt .type) (u := Srt typeS)
            (call := substT (peano j) sAst (Srt typeS)) rfl
            (stackReplayablePayload_substT_srt_tc (peano j) sAst .type).replay.1
            (stackReplayablePayload_substT_srt_tc (peano j) sAst .type)
            (liftable_srt_tc .type) (stackReplayablePayload_srt_tc .type) hpayload)
    | succ fuelPred =>
        refine ⟨Srt typeS, ?_⟩
        simpa [peano, LFTyping.nf, LFTyping.subst] using
          nfT_substT_srt_first_replay (peano fuelPred) (peano j) sAst .type
            (isnormal_peano_tc fuelPred)
  · cases fuelNat with
    | zero =>
        refine ⟨Srt kindS, ?_⟩
        have hpayload : ∃ M, eval pTC M (substT (peano j) sAst (Srt kindS)) =
            Srt kindS := ⟨1, rfl⟩
        simpa [peano, LFTyping.nf, LFTyping.subst] using
          (nfT_z_first_replay (t := .srt .kind) (u := Srt kindS)
            (call := substT (peano j) sAst (Srt kindS)) rfl
            (stackReplayablePayload_substT_srt_tc (peano j) sAst .kind).replay.1
            (stackReplayablePayload_substT_srt_tc (peano j) sAst .kind)
            (liftable_srt_tc .kind) (stackReplayablePayload_srt_tc .kind) hpayload)
    | succ fuelPred =>
        refine ⟨Srt kindS, ?_⟩
        simpa [peano, LFTyping.nf, LFTyping.subst] using
          nfT_substT_srt_first_replay (peano fuelPred) (peano j) sAst .kind
            (isnormal_peano_tc fuelPred)

theorem nfT_var_first_liftable (fuel : AST) (k : Nat) :
    FirstLiftableNF (.var k) (Var (peano k)) (nfT (S fuel) (Var (peano k))) := by
  exact FirstLiftableNF.intro (payload := Var (peano k)) (N := 1) (M := 0)
    rfl (nfT_var_tc fuel (peano k))
    (by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst j
      exact NFActiveShape.nf (S fuel) (Var (peano k)))
    (liftable_var_tc k) rfl

theorem nfT_var_first_strong (fuel : AST) (k : Nat) :
    FirstStrongNF (.var k) (Var (peano k)) (nfT (S fuel) (Var (peano k))) := by
  exact FirstStrongNF.intro (payload := Var (peano k)) (N := 1) (M := 0)
    rfl (nfT_var_tc fuel (peano k))
    (by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst j
      exact NFActiveShape.nf (S fuel) (Var (peano k)))
    (liftable_var_tc k) (liftable_var_tc k) rfl

theorem nfT_var_predN_first_strong (fuel : AST) (k : Nat) :
    FirstStrongNF (.var (k - 1)) (Var (peano (k - 1)))
      (nfT (S fuel) (Var (predN (peano k)))) := by
  obtain ⟨M, hM⟩ := var_predN_sim_tc k
  exact FirstStrongNF.intro (payload := Var (predN (peano k))) (N := 1) (M := M)
    rfl (nfT_var_tc fuel (predN (peano k)))
    (by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst j
      exact NFActiveShape.nf (S fuel) (Var (predN (peano k))))
    (liftable_var_predN_peano_tc k) (liftable_var_tc (k - 1)) hM

theorem nfT_var_addN_one_first_strong (fuel : AST) (k : Nat) :
    FirstStrongNF (.var (k + 1)) (Var (peano (k + 1)))
      (nfT (S fuel) (Var (addN (peano k) (S Z)))) := by
  obtain ⟨M, hM⟩ := var_addN_sim_tc k 1
  have hM' : eval pTC M (Var (addN (peano k) (S Z))) = Var (peano (k + 1)) := by
    simpa [peano] using hM
  exact FirstStrongNF.intro (payload := Var (addN (peano k) (S Z))) (N := 1) (M := M)
    rfl (nfT_var_tc fuel (addN (peano k) (S Z)))
    (by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst j
      exact NFActiveShape.nf (S fuel) (Var (addN (peano k) (S Z))))
    (liftable_var_addN_one_tc k) (liftable_var_tc (k + 1)) hM'

theorem replayablePayload_var_tc (k : Nat) :
    ReplayablePayload (Var (peano k)) (.var k) := by
  constructor
  · exact liftable_var_tc k
  · intro fuelNat
    cases fuelNat with
    | zero =>
        refine ⟨Var (peano k), ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_z_first_strong (t := .var k) (u := Var (peano k))
            (call := Var (peano k)) rfl (liftable_var_tc k) (liftable_var_tc k) ⟨0, rfl⟩)
    | succ fuelPred =>
        refine ⟨Var (peano k), ?_⟩
        simpa [peano, LFTyping.nf] using nfT_var_first_strong (peano fuelPred) k

theorem replayablePayload_var_addN_one_tc (k : Nat) :
    ReplayablePayload (Var (addN (peano k) (S Z))) (.var (k + 1)) := by
  constructor
  · exact liftable_var_addN_one_tc k
  · intro fuelNat
    cases fuelNat with
    | zero =>
        obtain ⟨M, hM⟩ := var_addN_sim_tc k 1
        have hM' : eval pTC M (Var (addN (peano k) (S Z))) = Var (peano (k + 1)) := by
          simpa [peano] using hM
        refine ⟨Var (peano (k + 1)), ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_z_first_strong (t := .var (k + 1)) (u := Var (peano (k + 1)))
            (call := Var (addN (peano k) (S Z))) rfl
            (liftable_var_addN_one_tc k) (liftable_var_tc (k + 1)) ⟨M, hM'⟩)
    | succ fuelPred =>
        refine ⟨Var (peano (k + 1)), ?_⟩
        simpa [peano, LFTyping.nf] using
          nfT_var_addN_one_first_strong (peano fuelPred) k

theorem replayablePayload_var_pair_nil_tc :
    (∀ k : Nat, ReplayablePayload (liftStack [] (Var (peano k))) (lfLiftStack [] (.var k))) ∧
    (∀ k : Nat, ReplayablePayload (liftStack [] (Var (addN (peano k) (S Z))))
      (lfLiftStack [] (.var (k + 1)))) := by
  constructor
  · intro k
    simpa [liftStack, lfLiftStack] using replayablePayload_var_tc k
  · intro k
    simpa [liftStack, lfLiftStack] using replayablePayload_var_addN_one_tc k

theorem replayablePayload_liftStack_liftVarT_tt_tc (cs : List Nat)
    (hpair :
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (addN (peano k) (S Z))))
        (lfLiftStack cs (.var (k + 1)))))
    (b idx : Nat) :
    ReplayablePayload
      (liftStack cs (liftVarT (S Z) (peano b) (peano idx) (con0 "tt")))
      (lfLiftStack cs (.var idx)) := by
  exact replayablePayload_prepend_nfT_arg
    (u := liftStack cs (liftVarT (S Z) (peano b) (peano idx) (con0 "tt")))
    (v := liftStack cs (Var (peano idx)))
    (t := lfLiftStack cs (.var idx))
    (liftable_of_stack_step
      (u := liftStack cs (liftVarT (S Z) (peano b) (peano idx) (con0 "tt")))
      (v := liftStack cs (Var (peano idx)))
      (t := lfLiftStack cs (.var idx))
      (by
        intro ds
        calc
          oneStep pTC (liftStack ds (liftStack cs
              (liftVarT (S Z) (peano b) (peano idx) (con0 "tt")))) =
              oneStep pTC (liftStack (cs ++ ds)
                (liftVarT (S Z) (peano b) (peano idx) (con0 "tt"))) := by
            rw [liftStack_append cs ds]
          _ = some (liftStack (cs ++ ds) (Var (peano idx))) := by
            exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano b)
              (peano idx) (con0 "tt") (Var (peano idx)) rfl
          _ = some (liftStack ds (liftStack cs (Var (peano idx)))) := by
            rw [liftStack_append cs ds])
      (hpair.1 idx).1)
    (by
      intro fuelNat
      simpa [peano] using
        hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
          (S Z) (peano b) (peano idx) (con0 "tt") (Var (peano idx))
          (isnormal_peano_tc fuelNat) rfl)
    (hpair.1 idx)

theorem replayablePayload_liftStack_liftVarT_ff_tc (cs : List Nat)
    (hpair :
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (addN (peano k) (S Z))))
        (lfLiftStack cs (.var (k + 1)))))
    (b idx : Nat) :
    ReplayablePayload
      (liftStack cs (liftVarT (S Z) (peano b) (peano idx) (con0 "ff")))
      (lfLiftStack cs (.var (idx + 1))) := by
  exact replayablePayload_prepend_nfT_arg
    (u := liftStack cs (liftVarT (S Z) (peano b) (peano idx) (con0 "ff")))
    (v := liftStack cs (Var (addN (peano idx) (S Z))))
    (t := lfLiftStack cs (.var (idx + 1)))
    (liftable_of_stack_step
      (u := liftStack cs (liftVarT (S Z) (peano b) (peano idx) (con0 "ff")))
      (v := liftStack cs (Var (addN (peano idx) (S Z))))
      (t := lfLiftStack cs (.var (idx + 1)))
      (by
        intro ds
        calc
          oneStep pTC (liftStack ds (liftStack cs
              (liftVarT (S Z) (peano b) (peano idx) (con0 "ff")))) =
              oneStep pTC (liftStack (cs ++ ds)
                (liftVarT (S Z) (peano b) (peano idx) (con0 "ff"))) := by
            rw [liftStack_append cs ds]
          _ = some (liftStack (cs ++ ds) (Var (addN (peano idx) (S Z)))) := by
            exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano b)
              (peano idx) (con0 "ff") (Var (addN (peano idx) (S Z))) rfl
          _ = some (liftStack ds (liftStack cs (Var (addN (peano idx) (S Z))))) := by
            rw [liftStack_append cs ds])
      (hpair.2 idx).1)
    (by
      intro fuelNat
      simpa [peano] using
        hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
          (S Z) (peano b) (peano idx) (con0 "ff")
          (Var (addN (peano idx) (S Z)))
          (isnormal_peano_tc fuelNat) rfl)
    (hpair.2 idx)

theorem replayablePayload_liftStack_liftVarT_peano_guard_tc (cs : List Nat)
    (hpair :
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (addN (peano k) (S Z))))
        (lfLiftStack cs (.var (k + 1))))) :
    ∀ (a b cutoff idx : Nat),
      ReplayablePayload
        (liftStack cs
          (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano a) (peano b))))
        (lfLiftStack cs (if a < b then .var idx else .var (idx + 1))) := by
  intro a
  induction a with
  | zero =>
      intro b cutoff idx
      cases b with
      | zero =>
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano 0) (peano 0))))
            (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))
            (t := lfLiftStack cs (.var (idx + 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano 0) (peano 0))))
              (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))
              (t := lfLiftStack cs (.var (idx + 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano 0) (peano 0))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano 0) (peano 0)))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                      (peano idx) (ltT (peano 0) (peano 0))
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                      (os_liftVarT_lt_zz_tc (S Z) (peano cutoff) (peano idx)
                        (isnormal_peano_tc 1) (isnormal_peano_tc cutoff) (isnormal_peano_tc idx))
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))) := by
                    rw [liftStack_append cs ds])
              (replayablePayload_liftStack_liftVarT_ff_tc cs hpair cutoff idx).1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx) (ltT (peano 0) (peano 0))
                  (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                  (isnormal_peano_tc fuelNat)
                  (os_liftVarT_lt_zz_tc (S Z) (peano cutoff) (peano idx)
                    (isnormal_peano_tc 1) (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
            (replayablePayload_liftStack_liftVarT_ff_tc cs hpair cutoff idx)
      | succ b' =>
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (peano 0) (peano (Nat.succ b')))))
            (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt")))
            (t := lfLiftStack cs (.var idx))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (peano 0) (peano (Nat.succ b')))))
              (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt")))
              (t := lfLiftStack cs (.var idx))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (peano 0) (peano (Nat.succ b')))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (peano 0) (peano (Nat.succ b'))))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt"))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                      (peano idx) (ltT (peano 0) (peano (Nat.succ b')))
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt"))
                      (os_liftVarT_lt_zs_tc (S Z) (peano cutoff) (peano idx)
                        (peano b') (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                        (isnormal_peano_tc idx))
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt")))) := by
                    rw [liftStack_append cs ds])
              (replayablePayload_liftStack_liftVarT_tt_tc cs hpair cutoff idx).1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx)
                  (ltT (peano 0) (peano (Nat.succ b')))
                  (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt"))
                  (isnormal_peano_tc fuelNat)
                  (os_liftVarT_lt_zs_tc (S Z) (peano cutoff) (peano idx)
                    (peano b') (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx)))
            (replayablePayload_liftStack_liftVarT_tt_tc cs hpair cutoff idx)
  | succ a ih =>
      intro b cutoff idx
      cases b with
      | zero =>
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (peano (Nat.succ a)) (peano 0))))
            (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))
            (t := lfLiftStack cs (.var (idx + 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (peano (Nat.succ a)) (peano 0))))
              (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))
              (t := lfLiftStack cs (.var (idx + 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (peano (Nat.succ a)) (peano 0))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (peano (Nat.succ a)) (peano 0)))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                      (peano idx) (ltT (peano (Nat.succ a)) (peano 0))
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                      (os_liftVarT_lt_sz_tc (S Z) (peano cutoff) (peano idx)
                        (peano a) (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                        (isnormal_peano_tc idx))
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))) := by
                    rw [liftStack_append cs ds])
              (replayablePayload_liftStack_liftVarT_ff_tc cs hpair cutoff idx).1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx)
                  (ltT (peano (Nat.succ a)) (peano 0))
                  (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                  (isnormal_peano_tc fuelNat)
                  (os_liftVarT_lt_sz_tc (S Z) (peano cutoff) (peano idx)
                    (peano a) (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx)))
            (replayablePayload_liftStack_liftVarT_ff_tc cs hpair cutoff idx)
      | succ b' =>
          have hnext := ih b' cutoff idx
          have hthis : ReplayablePayload
              (liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))))
              (lfLiftStack cs (if a < b' then .var idx else .var (idx + 1))) := by
            exact replayablePayload_prepend_nfT_arg
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))))
              (v := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (peano a) (peano b'))))
              (t := lfLiftStack cs (if a < b' then .var idx else .var (idx + 1)))
              (liftable_of_stack_step
                (u := liftStack cs
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))))
                (v := liftStack cs
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (peano a) (peano b'))))
                (t := lfLiftStack cs (if a < b' then .var idx else .var (idx + 1)))
                (by
                  intro ds
                  calc
                    oneStep pTC (liftStack ds (liftStack cs
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))))) =
                        oneStep pTC (liftStack (cs ++ ds)
                          (liftVarT (S Z) (peano cutoff) (peano idx)
                            (ltT (peano (Nat.succ a)) (peano (Nat.succ b'))))) := by
                      rw [liftStack_append cs ds]
                    _ = some (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (peano a) (peano b')))) := by
                      exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                        (peano idx) (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (peano a) (peano b')))
                        (os_liftVarT_lt_ss_tc (S Z) (peano cutoff) (peano idx)
                          (peano a) (peano b') (isnormal_peano_tc 1)
                          (isnormal_peano_tc cutoff) (isnormal_peano_tc idx))
                    _ = some (liftStack ds (liftStack cs
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (peano a) (peano b'))))) := by
                      rw [liftStack_append cs ds])
                hnext.1)
              (by
                intro fuelNat
                simpa [peano] using
                  hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                    (S Z) (peano cutoff) (peano idx)
                    (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))
                    (liftVarT (S Z) (peano cutoff) (peano idx)
                      (ltT (peano a) (peano b')))
                    (isnormal_peano_tc fuelNat)
                    (os_liftVarT_lt_ss_tc (S Z) (peano cutoff) (peano idx)
                      (peano a) (peano b') (isnormal_peano_tc 1)
                      (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
              hnext
          simpa only [if_succ_lt_succ_eq] using hthis

theorem replayablePayload_var_peano_cons_tc (c : Nat) (cs : List Nat)
    (hpair :
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (addN (peano k) (S Z))))
        (lfLiftStack cs (.var (k + 1)))))
    (k : Nat) :
    ReplayablePayload (liftStack (c :: cs) (Var (peano k)))
      (lfLiftStack (c :: cs) (.var k)) := by
  have hroot : oneStep pTC (liftT (S Z) (peano c) (Var (peano k))) =
      some (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))) := by rfl
  have hguard := replayablePayload_liftStack_liftVarT_peano_guard_tc cs hpair k c c k
  by_cases hkc : k < c
  · have hguard' : ReplayablePayload
        (liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))
        (lfLiftStack cs (.var k)) := by
      simpa [hkc] using hguard
    have hthis : ReplayablePayload
        (liftStack cs (liftT (S Z) (peano c) (Var (peano k))))
        (lfLiftStack cs (.var k)) := by
      exact replayablePayload_prepend_nfT_arg
        (u := liftStack cs (liftT (S Z) (peano c) (Var (peano k))))
        (v := liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))
        (t := lfLiftStack cs (.var k))
        (liftable_of_stack_step
          (u := liftStack cs (liftT (S Z) (peano c) (Var (peano k))))
          (v := liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))
          (t := lfLiftStack cs (.var k))
          (by
            intro ds
            calc
              oneStep pTC (liftStack ds (liftStack cs (liftT (S Z) (peano c) (Var (peano k))))) =
                  oneStep pTC (liftStack (cs ++ ds) (liftT (S Z) (peano c) (Var (peano k)))) := by
                rw [liftStack_append cs ds]
              _ = some (liftStack (cs ++ ds)
                  (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c)))) := by
                exact liftStack_descend_lift_step_tc (cs ++ ds) c hroot
              _ = some (liftStack ds (liftStack cs
                  (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))) := by
                rw [liftStack_append cs ds])
          hguard'.1)
        (by
          intro fuelNat
          simpa [peano] using
            hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c
              (Var (peano k))
              (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c)))
              (isnormal_peano_tc fuelNat) hroot)
        hguard'
    simpa [liftStack, lfLiftStack, LFTyping.lift, hkc] using hthis
  · have hguard' : ReplayablePayload
        (liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))
        (lfLiftStack cs (.var (k + 1))) := by
      simpa [hkc] using hguard
    have hthis : ReplayablePayload
        (liftStack cs (liftT (S Z) (peano c) (Var (peano k))))
        (lfLiftStack cs (.var (k + 1))) := by
      exact replayablePayload_prepend_nfT_arg
        (u := liftStack cs (liftT (S Z) (peano c) (Var (peano k))))
        (v := liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))
        (t := lfLiftStack cs (.var (k + 1)))
        (liftable_of_stack_step
          (u := liftStack cs (liftT (S Z) (peano c) (Var (peano k))))
          (v := liftStack cs (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))
          (t := lfLiftStack cs (.var (k + 1)))
          (by
            intro ds
            calc
              oneStep pTC (liftStack ds (liftStack cs (liftT (S Z) (peano c) (Var (peano k))))) =
                  oneStep pTC (liftStack (cs ++ ds) (liftT (S Z) (peano c) (Var (peano k)))) := by
                rw [liftStack_append cs ds]
              _ = some (liftStack (cs ++ ds)
                  (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c)))) := by
                exact liftStack_descend_lift_step_tc (cs ++ ds) c hroot
              _ = some (liftStack ds (liftStack cs
                  (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c))))) := by
                rw [liftStack_append cs ds])
          hguard'.1)
        (by
          intro fuelNat
          simpa [peano] using
            hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c
              (Var (peano k))
              (liftVarT (S Z) (peano c) (peano k) (ltT (peano k) (peano c)))
              (isnormal_peano_tc fuelNat) hroot)
        hguard'
    simpa [liftStack, lfLiftStack, LFTyping.lift, hkc] using hthis

theorem replayablePayload_liftStack_liftVarT_guard_addN_one_tc (cs : List Nat)
    (hpair :
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (addN (peano k) (S Z))))
        (lfLiftStack cs (.var (k + 1))))) :
    ∀ (k b cutoff idx : Nat),
      ReplayablePayload
        (liftStack cs
          (liftVarT (S Z) (peano cutoff) (peano idx)
            (ltT (addN (peano k) (S Z)) (peano b))))
        (lfLiftStack cs (if k + 1 < b then .var idx else .var (idx + 1))) := by
  intro k
  induction k with
  | zero =>
      intro b cutoff idx
      have hnext := replayablePayload_liftStack_liftVarT_peano_guard_tc cs hpair 1 b cutoff idx
      exact replayablePayload_prepend_nfT_arg
        (u := liftStack cs
          (liftVarT (S Z) (peano cutoff) (peano idx)
            (ltT (addN (peano 0) (S Z)) (peano b))))
        (v := liftStack cs
          (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano 1) (peano b))))
        (t := lfLiftStack cs (if 0 + 1 < b then .var idx else .var (idx + 1)))
        (liftable_of_stack_step
          (u := liftStack cs
            (liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (addN (peano 0) (S Z)) (peano b))))
          (v := liftStack cs
            (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano 1) (peano b))))
          (t := lfLiftStack cs (if 0 + 1 < b then .var idx else .var (idx + 1)))
          (by
            intro ds
            have hguardStep : oneStep pTC (ltT (addN (peano 0) (S Z)) (peano b)) =
                some (ltT (S Z) (peano b)) := by
              have hadd : oneStep pTC (addN Z (S Z)) = some (S Z) := by rfl
              exact hcong_ltT1_tc (addN Z (S Z)) (peano b) (S Z) hadd rfl
            calc
              oneStep pTC (liftStack ds (liftStack cs
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (addN (peano 0) (S Z)) (peano b))))) =
                  oneStep pTC (liftStack (cs ++ ds)
                    (liftVarT (S Z) (peano cutoff) (peano idx)
                      (ltT (addN (peano 0) (S Z)) (peano b)))) := by
                rw [liftStack_append cs ds]
              _ = some (liftStack (cs ++ ds)
                  (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (S Z) (peano b)))) := by
                exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                  (peano idx) (ltT (addN (peano 0) (S Z)) (peano b))
                  (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (S Z) (peano b)))
                  (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                    (addN (peano 0) (S Z)) (peano b)
                    (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx) (ltT (S Z) (peano b)) hguardStep)
              _ = some (liftStack ds (liftStack cs
                  (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (S Z) (peano b))))) := by
                rw [liftStack_append cs ds])
          (by simpa [peano] using hnext.1))
        (by
          intro fuelNat
          have hguardStep : oneStep pTC (ltT (addN (peano 0) (S Z)) (peano b)) =
              some (ltT (S Z) (peano b)) := by
            have hadd : oneStep pTC (addN Z (S Z)) = some (S Z) := by rfl
            exact hcong_ltT1_tc (addN Z (S Z)) (peano b) (S Z) hadd rfl
          simpa [peano] using
            hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
              (S Z) (peano cutoff) (peano idx)
              (ltT (addN (peano 0) (S Z)) (peano b))
              (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (S Z) (peano b)))
              (isnormal_peano_tc fuelNat)
              (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                (addN (peano 0) (S Z)) (peano b)
                (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                (isnormal_peano_tc idx) (ltT (S Z) (peano b)) hguardStep))
        (by simpa [peano] using hnext)
  | succ k ih =>
      intro b cutoff idx
      cases b with
      | zero =>
          have hmidReplay : ReplayablePayload
              (liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (S (addN (peano k) (S Z))) Z)))
              (lfLiftStack cs (.var (idx + 1))) := by
            exact replayablePayload_prepend_nfT_arg
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (S (addN (peano k) (S Z))) Z)))
              (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))
              (t := lfLiftStack cs (.var (idx + 1)))
              (liftable_of_stack_step
                (u := liftStack cs
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) Z)))
                (v := liftStack cs (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))
                (t := lfLiftStack cs (.var (idx + 1)))
                (by
                  intro ds
                  calc
                    oneStep pTC (liftStack ds (liftStack cs
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (S (addN (peano k) (S Z))) Z)))) =
                        oneStep pTC (liftStack (cs ++ ds)
                          (liftVarT (S Z) (peano cutoff) (peano idx)
                            (ltT (S (addN (peano k) (S Z))) Z))) := by
                      rw [liftStack_append cs ds]
                    _ = some (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))) := by
                      exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                        (peano idx) (ltT (S (addN (peano k) (S Z))) Z)
                        (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                        (os_liftVarT_lt_sz_tc (S Z) (peano cutoff) (peano idx)
                          (addN (peano k) (S Z)) (isnormal_peano_tc 1)
                          (isnormal_peano_tc cutoff) (isnormal_peano_tc idx))
                    _ = some (liftStack ds (liftStack cs
                        (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff")))) := by
                      rw [liftStack_append cs ds])
                (replayablePayload_liftStack_liftVarT_ff_tc cs hpair cutoff idx).1)
              (by
                intro fuelNat
                simpa [peano] using
                  hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                    (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) Z)
                    (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                    (isnormal_peano_tc fuelNat)
                    (os_liftVarT_lt_sz_tc (S Z) (peano cutoff) (peano idx)
                      (addN (peano k) (S Z)) (isnormal_peano_tc 1)
                      (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
              (replayablePayload_liftStack_liftVarT_ff_tc cs hpair cutoff idx)
          have hpre := replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0))))
            (v := liftStack cs
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) Z)))
            (t := lfLiftStack cs (.var (idx + 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0))))
              (v := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (S (addN (peano k) (S Z))) Z)))
              (t := lfLiftStack cs (.var (idx + 1)))
              (by
                intro ds
                have hguardStep : oneStep pTC
                    (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0)) =
                    some (ltT (S (addN (peano k) (S Z))) Z) := by
                  have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                      some (S (addN (peano k) (S Z))) := by rfl
                  exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) Z
                    (S (addN (peano k) (S Z))) hadd rfl
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0)))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (S (addN (peano k) (S Z))) Z))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                      (peano idx) (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0))
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (S (addN (peano k) (S Z))) Z))
                      (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                        (addN (peano (Nat.succ k)) (S Z)) (peano 0)
                        (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                        (isnormal_peano_tc idx)
                        (ltT (S (addN (peano k) (S Z))) Z) hguardStep)
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (S (addN (peano k) (S Z))) Z)))) := by
                    rw [liftStack_append cs ds])
              hmidReplay.1)
            (by
              intro fuelNat
              have hguardStep : oneStep pTC
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0)) =
                  some (ltT (S (addN (peano k) (S Z))) Z) := by
                have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                    some (S (addN (peano k) (S Z))) := by rfl
                exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) Z
                  (S (addN (peano k) (S Z))) hadd rfl
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0))
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) Z))
                  (isnormal_peano_tc fuelNat)
                  (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                    (addN (peano (Nat.succ k)) (S Z)) (peano 0)
                    (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx)
                    (ltT (S (addN (peano k) (S Z))) Z) hguardStep))
            hmidReplay
          simpa using hpre
      | succ b' =>
          have hmidReplay : ReplayablePayload
              (liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (S (addN (peano k) (S Z))) (S (peano b')))))
              (lfLiftStack cs (if k + 1 < b' then .var idx else .var (idx + 1))) := by
            exact replayablePayload_prepend_nfT_arg
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (S (addN (peano k) (S Z))) (S (peano b')))))
              (v := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano k) (S Z)) (peano b'))))
              (t := lfLiftStack cs (if k + 1 < b' then .var idx else .var (idx + 1)))
              (liftable_of_stack_step
                (u := liftStack cs
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) (S (peano b')))))
                (v := liftStack cs
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (addN (peano k) (S Z)) (peano b'))))
                (t := lfLiftStack cs (if k + 1 < b' then .var idx else .var (idx + 1)))
                (by
                  intro ds
                  calc
                    oneStep pTC (liftStack ds (liftStack cs
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (S (addN (peano k) (S Z))) (S (peano b')))))) =
                        oneStep pTC (liftStack (cs ++ ds)
                          (liftVarT (S Z) (peano cutoff) (peano idx)
                            (ltT (S (addN (peano k) (S Z))) (S (peano b'))))) := by
                      rw [liftStack_append cs ds]
                    _ = some (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (addN (peano k) (S Z)) (peano b')))) := by
                      exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                        (peano idx) (ltT (S (addN (peano k) (S Z))) (S (peano b')))
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (addN (peano k) (S Z)) (peano b')))
                        (os_liftVarT_lt_ss_tc (S Z) (peano cutoff) (peano idx)
                          (addN (peano k) (S Z)) (peano b') (isnormal_peano_tc 1)
                          (isnormal_peano_tc cutoff) (isnormal_peano_tc idx))
                    _ = some (liftStack ds (liftStack cs
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (addN (peano k) (S Z)) (peano b'))))) := by
                      rw [liftStack_append cs ds])
                (ih b' cutoff idx).1)
              (by
                intro fuelNat
                simpa [peano] using
                  hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                    (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) (S (peano b')))
                    (liftVarT (S Z) (peano cutoff) (peano idx)
                      (ltT (addN (peano k) (S Z)) (peano b')))
                    (isnormal_peano_tc fuelNat)
                    (os_liftVarT_lt_ss_tc (S Z) (peano cutoff) (peano idx)
                      (addN (peano k) (S Z)) (peano b') (isnormal_peano_tc 1)
                      (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
              (ih b' cutoff idx)
          have hpre := replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b')))))
            (v := liftStack cs
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) (S (peano b')))))
            (t := lfLiftStack cs (if k + 1 < b' then .var idx else .var (idx + 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b')))))
              (v := liftStack cs
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (S (addN (peano k) (S Z))) (S (peano b')))))
              (t := lfLiftStack cs (if k + 1 < b' then .var idx else .var (idx + 1)))
              (by
                intro ds
                have hguardStep : oneStep pTC
                    (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))) =
                    some (ltT (S (addN (peano k) (S Z))) (S (peano b'))) := by
                  have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                      some (S (addN (peano k) (S Z))) := by rfl
                  exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) (S (peano b'))
                    (S (addN (peano k) (S Z))) hadd rfl
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b')))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano cutoff) (peano idx)
                          (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (S (addN (peano k) (S Z))) (S (peano b'))))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds) (S Z) (peano cutoff)
                      (peano idx) (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b')))
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (S (addN (peano k) (S Z))) (S (peano b'))))
                      (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                        (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))
                        (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                        (isnormal_peano_tc idx)
                        (ltT (S (addN (peano k) (S Z))) (S (peano b'))) hguardStep)
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano cutoff) (peano idx)
                        (ltT (S (addN (peano k) (S Z))) (S (peano b')))))) := by
                    rw [liftStack_append cs ds])
              hmidReplay.1)
            (by
              intro fuelNat
              have hguardStep : oneStep pTC
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))) =
                  some (ltT (S (addN (peano k) (S Z))) (S (peano b'))) := by
                have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                    some (S (addN (peano k) (S Z))) := by rfl
                exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) (S (peano b'))
                  (S (addN (peano k) (S Z))) hadd rfl
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b')))
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) (S (peano b'))))
                  (isnormal_peano_tc fuelNat)
                  (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                    (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))
                    (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx)
                    (ltT (S (addN (peano k) (S Z))) (S (peano b'))) hguardStep))
            hmidReplay
          simpa only [if_succ_add_one_lt_succ_eq] using hpre

theorem replayablePayload_var_addN_one_cons_tc (c : Nat) (cs : List Nat)
    (hpair :
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
      (∀ k : Nat, ReplayablePayload (liftStack cs (Var (addN (peano k) (S Z))))
        (lfLiftStack cs (.var (k + 1)))))
    (k : Nat) :
    ReplayablePayload (liftStack (c :: cs) (Var (addN (peano k) (S Z))))
      (lfLiftStack (c :: cs) (.var (k + 1))) := by
  let root := liftVarT (S Z) (peano c) (addN (peano k) (S Z))
    (ltT (addN (peano k) (S Z)) (peano c))
  let norm := liftVarT (S Z) (peano c) (peano (k + 1))
    (ltT (addN (peano k) (S Z)) (peano c))
  let target := if k + 1 < c then LF.Term.var (k + 1) else LF.Term.var (k + 2)
  have hnorm : ReplayablePayload (liftStack cs norm) (lfLiftStack cs target) := by
    simpa [norm, target] using
      replayablePayload_liftStack_liftVarT_guard_addN_one_tc cs hpair k c c (k + 1)
  have hrootLift : LiftablePayload (liftStack cs root) (lfLiftStack cs target) := by
    intro ds
    simpa [root, target, liftStack_append, lfLiftStack_append] using
      (liftable_liftVarT_addN_one_guard_tc k c (cs ++ ds))
  have hidxReplay : ReplayablePayload (liftStack cs root) (lfLiftStack cs target) := by
    exact replayablePayload_prefix_nfT_arg
      (u := liftStack cs root) (v := liftStack cs norm) (t := lfLiftStack cs target)
      hrootLift
      (by
        intro fuelNat
        obtain ⟨Nidx, hidx⟩ := addN_sim_tc k 1
        have hidx' : eval pTC Nidx (addN (peano k) (S Z)) = peano (k + 1) := by
          simpa [peano] using hidx
        simpa [root, norm, peano] using
          cong_eval_nf_wrapper_with_guard
            (fun s => nfT (peano (Nat.succ fuelNat))
              (liftStack cs (liftVarT (S Z) (peano c) s
                (ltT (addN (peano k) (S Z)) (peano c)))))
            (by
              intro s
              exact NFActiveShape.nf (peano (Nat.succ fuelNat))
                (liftStack cs (liftVarT (S Z) (peano c) s
                  (ltT (addN (peano k) (S Z)) (peano c)))))
            (by
              intro s s' hs
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano c) s (ltT (addN (peano k) (S Z)) (peano c))
                  (liftVarT (S Z) (peano c) s'
                    (ltT (addN (peano k) (S Z)) (peano c)))
                  (isnormal_peano_tc fuelNat)
                  (hcong_liftVarT3_lt_tc (S Z) (peano c)
                    (addN (peano k) (S Z)) (peano c)
                    (isnormal_peano_tc 1) (isnormal_peano_tc c) s s' hs))
            Nidx hidx' (isnormal_peano_tc (k + 1)))
      hnorm
  have houter : ReplayablePayload
      (liftStack cs (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))))
      (lfLiftStack cs target) := by
    have hrootStep : oneStep pTC (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))) =
        some root := by
      rfl
    exact replayablePayload_prepend_nfT_arg
      (u := liftStack cs (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))))
      (v := liftStack cs root)
      (t := lfLiftStack cs target)
      (liftable_of_stack_step
        (u := liftStack cs (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))))
        (v := liftStack cs root)
        (t := lfLiftStack cs target)
        (by
          intro ds
          calc
            oneStep pTC (liftStack ds (liftStack cs
                (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))))) =
                oneStep pTC (liftStack (cs ++ ds)
                  (liftT (S Z) (peano c) (Var (addN (peano k) (S Z))))) := by
              rw [liftStack_append cs ds]
            _ = some (liftStack (cs ++ ds) root) := by
              exact liftStack_descend_lift_step_tc (cs ++ ds) c hrootStep
            _ = some (liftStack ds (liftStack cs root)) := by
              rw [liftStack_append cs ds])
        hidxReplay.1)
      (by
        intro fuelNat
        simpa [root, peano] using
          hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c
            (Var (addN (peano k) (S Z))) root
            (isnormal_peano_tc fuelNat) hrootStep)
      hidxReplay
  by_cases hkc : k + 1 < c
  · have houter' : ReplayablePayload
        (liftStack cs (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))))
        (lfLiftStack cs (.var (k + 1))) := by
      simpa [target, hkc] using houter
    simpa [liftStack, lfLiftStack, LFTyping.lift, hkc] using houter'
  · have houter' : ReplayablePayload
        (liftStack cs (liftT (S Z) (peano c) (Var (addN (peano k) (S Z)))))
        (lfLiftStack cs (.var (k + 2))) := by
      simpa [target, hkc] using houter
    simpa [liftStack, lfLiftStack, LFTyping.lift, hkc, Nat.add_assoc] using houter'

theorem replayablePayload_var_pair_tc : ∀ cs : List Nat,
    (∀ k : Nat, ReplayablePayload (liftStack cs (Var (peano k))) (lfLiftStack cs (.var k))) ∧
    (∀ k : Nat, ReplayablePayload (liftStack cs (Var (addN (peano k) (S Z))))
      (lfLiftStack cs (.var (k + 1)))) := by
  intro cs
  induction cs with
  | nil =>
      exact replayablePayload_var_pair_nil_tc
  | cons c cs ih =>
      constructor
      · intro k
        exact replayablePayload_var_peano_cons_tc c cs ih k
      · intro k
        exact replayablePayload_var_addN_one_cons_tc c cs ih k

theorem stackReplayablePayload_var_tc (k : Nat) :
    StackReplayablePayload (Var (peano k)) (.var k) := by
  intro cs
  exact (replayablePayload_var_pair_tc cs).1 k

theorem stackReplayablePayload_var_addN_one_tc (k : Nat) :
    StackReplayablePayload (Var (addN (peano k) (S Z))) (.var (k + 1)) := by
  intro cs
  exact (replayablePayload_var_pair_tc cs).2 k

theorem replayablePayload_var_predN_peano_tc (cs : List Nat) (k : Nat) :
    ReplayablePayload (liftStack cs (Var (predN (peano k))))
      (lfLiftStack cs (.var (k - 1))) := by
  cases cs with
  | nil =>
      constructor
      · simpa [liftStack, lfLiftStack] using liftable_var_predN_peano_tc k
      · intro fuelNat
        cases fuelNat with
        | zero =>
            obtain ⟨M, hM⟩ := var_predN_sim_tc k
            refine ⟨Var (peano (k - 1)), ?_⟩
            simpa [liftStack, lfLiftStack, peano, LFTyping.nf] using
              (nfT_z_first_strong (t := .var (k - 1)) (u := Var (peano (k - 1)))
                (call := Var (predN (peano k))) rfl
                (liftable_var_predN_peano_tc k) (liftable_var_tc (k - 1)) ⟨M, hM⟩)
        | succ fuelPred =>
            refine ⟨Var (peano (k - 1)), ?_⟩
            simpa [liftStack, lfLiftStack, peano, LFTyping.nf] using
              nfT_var_predN_first_strong (peano fuelPred) k
  | cons c cs =>
      have hroot : oneStep pTC (liftT (S Z) (peano c) (Var (predN (peano k)))) =
          some (liftVarT (S Z) (peano c) (predN (peano k))
            (ltT (predN (peano k)) (peano c))) := by
        rfl
      have hpred : oneStep pTC (predN (peano k)) = some (peano (k - 1)) :=
        os_predN_peano_tc k
      have hidx : oneStep pTC
          (liftVarT (S Z) (peano c) (predN (peano k))
            (ltT (predN (peano k)) (peano c))) =
          some (liftVarT (S Z) (peano c) (peano (k - 1))
            (ltT (predN (peano k)) (peano c))) := by
        exact hcong_liftVarT3_lt_tc (S Z) (peano c)
          (predN (peano k)) (peano c)
          (isnormal_peano_tc 1) (isnormal_peano_tc c)
          (predN (peano k)) (peano (k - 1)) hpred
      have hguardStep : oneStep pTC (ltT (predN (peano k)) (peano c)) =
          some (ltT (peano (k - 1)) (peano c)) := by
        exact hcong_ltT1_tc (predN (peano k)) (peano c)
          (peano (k - 1)) hpred rfl
      have hguardArg : oneStep pTC
          (liftVarT (S Z) (peano c) (peano (k - 1))
            (ltT (predN (peano k)) (peano c))) =
          some (liftVarT (S Z) (peano c) (peano (k - 1))
            (ltT (peano (k - 1)) (peano c))) := by
        exact hcong_liftVarT4_lt_tc (S Z) (peano c) (peano (k - 1))
          (predN (peano k)) (peano c)
          (isnormal_peano_tc 1) (isnormal_peano_tc c) (isnormal_peano_tc (k - 1))
          (ltT (peano (k - 1)) (peano c)) hguardStep
      have hguard :=
        replayablePayload_liftStack_liftVarT_peano_guard_tc cs
          (replayablePayload_var_pair_tc cs) (k - 1) c c (k - 1)
      by_cases hkc : k - 1 < c
      · have hguard' : ReplayablePayload
            (liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (peano (k - 1)) (peano c))))
            (lfLiftStack cs (.var (k - 1))) := by
          simpa [hkc] using hguard
        have hguardArgReplay : ReplayablePayload
            (liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (predN (peano k)) (peano c))))
            (lfLiftStack cs (.var (k - 1))) := by
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (predN (peano k)) (peano c))))
            (v := liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (peano (k - 1)) (peano c))))
            (t := lfLiftStack cs (.var (k - 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano c) (peano (k - 1))
                  (ltT (predN (peano k)) (peano c))))
              (v := liftStack cs
                (liftVarT (S Z) (peano c) (peano (k - 1))
                  (ltT (peano (k - 1)) (peano c))))
              (t := lfLiftStack cs (.var (k - 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano c) (peano (k - 1))
                          (ltT (predN (peano k)) (peano c)))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (peano (k - 1)) (peano c)))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds)
                      (S Z) (peano c) (peano (k - 1))
                      (ltT (predN (peano k)) (peano c))
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (peano (k - 1)) (peano c))) hguardArg
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (peano (k - 1)) (peano c))))) := by
                    rw [liftStack_append cs ds])
              hguard'.1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano c) (peano (k - 1))
                  (ltT (predN (peano k)) (peano c))
                  (liftVarT (S Z) (peano c) (peano (k - 1))
                    (ltT (peano (k - 1)) (peano c)))
                  (isnormal_peano_tc fuelNat) hguardArg)
            hguard'
        have hidxReplay : ReplayablePayload
            (liftStack cs
              (liftVarT (S Z) (peano c) (predN (peano k))
                (ltT (predN (peano k)) (peano c))))
            (lfLiftStack cs (.var (k - 1))) := by
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano c) (predN (peano k))
                (ltT (predN (peano k)) (peano c))))
            (v := liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (predN (peano k)) (peano c))))
            (t := lfLiftStack cs (.var (k - 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano c) (predN (peano k))
                  (ltT (predN (peano k)) (peano c))))
              (v := liftStack cs
                (liftVarT (S Z) (peano c) (peano (k - 1))
                  (ltT (predN (peano k)) (peano c))))
              (t := lfLiftStack cs (.var (k - 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (predN (peano k))
                        (ltT (predN (peano k)) (peano c))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano c) (predN (peano k))
                          (ltT (predN (peano k)) (peano c)))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c)))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds)
                      (S Z) (peano c) (predN (peano k))
                      (ltT (predN (peano k)) (peano c))
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c))) hidx
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c))))) := by
                    rw [liftStack_append cs ds])
              hguardArgReplay.1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano c) (predN (peano k))
                  (ltT (predN (peano k)) (peano c))
                  (liftVarT (S Z) (peano c) (peano (k - 1))
                    (ltT (predN (peano k)) (peano c)))
                  (isnormal_peano_tc fuelNat) hidx)
            hguardArgReplay
        have hrootReplay : ReplayablePayload
            (liftStack cs (liftT (S Z) (peano c) (Var (predN (peano k)))))
            (lfLiftStack cs (.var (k - 1))) := by
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs (liftT (S Z) (peano c) (Var (predN (peano k)))))
            (v := liftStack cs
              (liftVarT (S Z) (peano c) (predN (peano k))
                (ltT (predN (peano k)) (peano c))))
            (t := lfLiftStack cs (.var (k - 1)))
            (liftable_of_stack_step
              (u := liftStack cs (liftT (S Z) (peano c) (Var (predN (peano k)))))
              (v := liftStack cs
                (liftVarT (S Z) (peano c) (predN (peano k))
                  (ltT (predN (peano k)) (peano c))))
              (t := lfLiftStack cs (.var (k - 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftT (S Z) (peano c) (Var (predN (peano k)))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftT (S Z) (peano c) (Var (predN (peano k))))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano c) (predN (peano k))
                        (ltT (predN (peano k)) (peano c)))) := by
                    exact liftStack_descend_lift_step_tc (cs ++ ds) c hroot
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (predN (peano k))
                        (ltT (predN (peano k)) (peano c))))) := by
                    rw [liftStack_append cs ds])
              hidxReplay.1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c
                  (Var (predN (peano k)))
                  (liftVarT (S Z) (peano c) (predN (peano k))
                    (ltT (predN (peano k)) (peano c)))
                  (isnormal_peano_tc fuelNat) hroot)
            hidxReplay
        simpa [liftStack, lfLiftStack, LFTyping.lift, hkc] using hrootReplay
      · have hguard' : ReplayablePayload
            (liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (peano (k - 1)) (peano c))))
            (lfLiftStack cs (.var ((k - 1) + 1))) := by
          simpa [hkc] using hguard
        have hguardArgReplay : ReplayablePayload
            (liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (predN (peano k)) (peano c))))
            (lfLiftStack cs (.var ((k - 1) + 1))) := by
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (predN (peano k)) (peano c))))
            (v := liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (peano (k - 1)) (peano c))))
            (t := lfLiftStack cs (.var ((k - 1) + 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano c) (peano (k - 1))
                  (ltT (predN (peano k)) (peano c))))
              (v := liftStack cs
                (liftVarT (S Z) (peano c) (peano (k - 1))
                  (ltT (peano (k - 1)) (peano c))))
              (t := lfLiftStack cs (.var ((k - 1) + 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano c) (peano (k - 1))
                          (ltT (predN (peano k)) (peano c)))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (peano (k - 1)) (peano c)))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds)
                      (S Z) (peano c) (peano (k - 1))
                      (ltT (predN (peano k)) (peano c))
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (peano (k - 1)) (peano c))) hguardArg
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (peano (k - 1)) (peano c))))) := by
                    rw [liftStack_append cs ds])
              hguard'.1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano c) (peano (k - 1))
                  (ltT (predN (peano k)) (peano c))
                  (liftVarT (S Z) (peano c) (peano (k - 1))
                    (ltT (peano (k - 1)) (peano c)))
                  (isnormal_peano_tc fuelNat) hguardArg)
            hguard'
        have hidxReplay : ReplayablePayload
            (liftStack cs
              (liftVarT (S Z) (peano c) (predN (peano k))
                (ltT (predN (peano k)) (peano c))))
            (lfLiftStack cs (.var ((k - 1) + 1))) := by
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs
              (liftVarT (S Z) (peano c) (predN (peano k))
                (ltT (predN (peano k)) (peano c))))
            (v := liftStack cs
              (liftVarT (S Z) (peano c) (peano (k - 1))
                (ltT (predN (peano k)) (peano c))))
            (t := lfLiftStack cs (.var ((k - 1) + 1)))
            (liftable_of_stack_step
              (u := liftStack cs
                (liftVarT (S Z) (peano c) (predN (peano k))
                  (ltT (predN (peano k)) (peano c))))
              (v := liftStack cs
                (liftVarT (S Z) (peano c) (peano (k - 1))
                  (ltT (predN (peano k)) (peano c))))
              (t := lfLiftStack cs (.var ((k - 1) + 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (predN (peano k))
                        (ltT (predN (peano k)) (peano c))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftVarT (S Z) (peano c) (predN (peano k))
                          (ltT (predN (peano k)) (peano c)))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c)))) := by
                    exact liftStack_descend_liftVarT_step_tc (cs ++ ds)
                      (S Z) (peano c) (predN (peano k))
                      (ltT (predN (peano k)) (peano c))
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c))) hidx
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (peano (k - 1))
                        (ltT (predN (peano k)) (peano c))))) := by
                    rw [liftStack_append cs ds])
              hguardArgReplay.1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc cs (peano fuelNat)
                  (S Z) (peano c) (predN (peano k))
                  (ltT (predN (peano k)) (peano c))
                  (liftVarT (S Z) (peano c) (peano (k - 1))
                    (ltT (predN (peano k)) (peano c)))
                  (isnormal_peano_tc fuelNat) hidx)
            hguardArgReplay
        have hrootReplay : ReplayablePayload
            (liftStack cs (liftT (S Z) (peano c) (Var (predN (peano k)))))
            (lfLiftStack cs (.var ((k - 1) + 1))) := by
          exact replayablePayload_prepend_nfT_arg
            (u := liftStack cs (liftT (S Z) (peano c) (Var (predN (peano k)))))
            (v := liftStack cs
              (liftVarT (S Z) (peano c) (predN (peano k))
                (ltT (predN (peano k)) (peano c))))
            (t := lfLiftStack cs (.var ((k - 1) + 1)))
            (liftable_of_stack_step
              (u := liftStack cs (liftT (S Z) (peano c) (Var (predN (peano k)))))
              (v := liftStack cs
                (liftVarT (S Z) (peano c) (predN (peano k))
                  (ltT (predN (peano k)) (peano c))))
              (t := lfLiftStack cs (.var ((k - 1) + 1)))
              (by
                intro ds
                calc
                  oneStep pTC (liftStack ds (liftStack cs
                      (liftT (S Z) (peano c) (Var (predN (peano k)))))) =
                      oneStep pTC (liftStack (cs ++ ds)
                        (liftT (S Z) (peano c) (Var (predN (peano k))))) := by
                    rw [liftStack_append cs ds]
                  _ = some (liftStack (cs ++ ds)
                      (liftVarT (S Z) (peano c) (predN (peano k))
                        (ltT (predN (peano k)) (peano c)))) := by
                    exact liftStack_descend_lift_step_tc (cs ++ ds) c hroot
                  _ = some (liftStack ds (liftStack cs
                      (liftVarT (S Z) (peano c) (predN (peano k))
                        (ltT (predN (peano k)) (peano c))))) := by
                    rw [liftStack_append cs ds])
              hidxReplay.1)
            (by
              intro fuelNat
              simpa [peano] using
                hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c
                  (Var (predN (peano k)))
                  (liftVarT (S Z) (peano c) (predN (peano k))
                    (ltT (predN (peano k)) (peano c)))
                  (isnormal_peano_tc fuelNat) hroot)
            hidxReplay
        simpa [liftStack, lfLiftStack, LFTyping.lift, hkc] using hrootReplay

theorem stackReplayablePayload_var_predN_peano_tc (k : Nat) :
    StackReplayablePayload (Var (predN (peano k))) (.var (k - 1)) := by
  intro cs
  exact replayablePayload_var_predN_peano_tc cs k

theorem replayablePayload_prepend_liftStack_substVarLT_step
    {target : LF.Term} (cs : List Nat) (j s k b next : AST)
    (h : oneStep pTC (substVarLT j s k b) = some next)
    (hv : ReplayablePayload (liftStack cs next) target) :
    ReplayablePayload (liftStack cs (substVarLT j s k b)) target := by
  exact replayablePayload_prepend_nfT_arg
    (u := liftStack cs (substVarLT j s k b))
    (v := liftStack cs next)
    (t := target)
    (liftable_of_stack_step
      (u := liftStack cs (substVarLT j s k b))
      (v := liftStack cs next)
      (t := target)
      (by
        intro ds
        calc
          oneStep pTC (liftStack ds (liftStack cs (substVarLT j s k b))) =
              oneStep pTC (liftStack (cs ++ ds) (substVarLT j s k b)) := by
            rw [liftStack_append cs ds]
          _ = some (liftStack (cs ++ ds) next) := by
            exact liftStack_descend_substVarLT_step_tc (cs ++ ds) j s k b next h
          _ = some (liftStack ds (liftStack cs next)) := by
            rw [liftStack_append cs ds])
      hv.1)
    (by
      intro fuelNat
      simpa [peano] using
        hcong_nfT_s_liftStack_substVarLT_arg_tc cs (peano fuelNat)
          j s k b next (isnormal_peano_tc fuelNat) h)
    hv

theorem replayablePayload_liftStack_substVarLT_tt_tc
    (cs : List Nat) (j s : AST) (k : Nat) :
    ReplayablePayload (liftStack cs (substVarLT j s (peano k) (con0 "tt")))
      (lfLiftStack cs (.var (k - 1))) := by
  exact replayablePayload_prepend_nfT_arg
    (u := liftStack cs (substVarLT j s (peano k) (con0 "tt")))
    (v := liftStack cs (Var (predN (peano k))))
    (t := lfLiftStack cs (.var (k - 1)))
    (liftable_of_stack_step
      (u := liftStack cs (substVarLT j s (peano k) (con0 "tt")))
      (v := liftStack cs (Var (predN (peano k))))
      (t := lfLiftStack cs (.var (k - 1)))
      (by
        intro ds
        calc
          oneStep pTC (liftStack ds (liftStack cs
              (substVarLT j s (peano k) (con0 "tt")))) =
              oneStep pTC (liftStack (cs ++ ds)
                (substVarLT j s (peano k) (con0 "tt"))) := by
            rw [liftStack_append cs ds]
          _ = some (liftStack (cs ++ ds) (Var (predN (peano k)))) := by
            exact liftStack_descend_substVarLT_step_tc (cs ++ ds)
              j s (peano k) (con0 "tt") (Var (predN (peano k))) rfl
          _ = some (liftStack ds (liftStack cs (Var (predN (peano k))))) := by
            rw [liftStack_append cs ds])
      (replayablePayload_var_predN_peano_tc cs k).1)
    (by
      intro fuelNat
      simpa [peano] using
        hcong_nfT_s_liftStack_substVarLT_arg_tc cs (peano fuelNat)
          j s (peano k) (con0 "tt") (Var (predN (peano k)))
          (isnormal_peano_tc fuelNat) rfl)
    (replayablePayload_var_predN_peano_tc cs k)

theorem replayablePayload_liftStack_substVarLT_ff_tc
    (cs : List Nat) (j s : AST) (k : Nat) :
    ReplayablePayload (liftStack cs (substVarLT j s (peano k) (con0 "ff")))
      (lfLiftStack cs (.var k)) := by
  exact replayablePayload_prepend_nfT_arg
    (u := liftStack cs (substVarLT j s (peano k) (con0 "ff")))
    (v := liftStack cs (Var (peano k)))
    (t := lfLiftStack cs (.var k))
    (liftable_of_stack_step
      (u := liftStack cs (substVarLT j s (peano k) (con0 "ff")))
      (v := liftStack cs (Var (peano k)))
      (t := lfLiftStack cs (.var k))
      (by
        intro ds
        calc
          oneStep pTC (liftStack ds (liftStack cs
              (substVarLT j s (peano k) (con0 "ff")))) =
              oneStep pTC (liftStack (cs ++ ds)
                (substVarLT j s (peano k) (con0 "ff"))) := by
            rw [liftStack_append cs ds]
          _ = some (liftStack (cs ++ ds) (Var (peano k))) := by
            exact liftStack_descend_substVarLT_step_tc (cs ++ ds)
              j s (peano k) (con0 "ff") (Var (peano k)) rfl
          _ = some (liftStack ds (liftStack cs (Var (peano k)))) := by
            rw [liftStack_append cs ds])
      ((replayablePayload_var_pair_tc cs).1 k).1)
    (by
      intro fuelNat
      simpa [peano] using
        hcong_nfT_s_liftStack_substVarLT_arg_tc cs (peano fuelNat)
          j s (peano k) (con0 "ff") (Var (peano k))
          (isnormal_peano_tc fuelNat) rfl)
    ((replayablePayload_var_pair_tc cs).1 k)

theorem replayablePayload_liftStack_substVarLT_peano_guard_tc
    (cs : List Nat) (j s : AST) (k : Nat)
    (hj : IsNormal pTC j) (hs : IsNormal pTC s) :
    ∀ (a b : Nat),
      ReplayablePayload
        (liftStack cs (substVarLT j s (peano k) (ltT (peano a) (peano b))))
        (lfLiftStack cs (if a < b then .var (k - 1) else .var k)) := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b with
      | zero =>
          exact replayablePayload_prepend_liftStack_substVarLT_step
            (target := lfLiftStack cs (.var k)) cs j s (peano k)
            (ltT (peano 0) (peano 0))
            (substVarLT j s (peano k) (con0 "ff"))
            (os_substVarLT_lt_zz_tc j s (peano k) hj hs (isnormal_peano_tc k))
            (replayablePayload_liftStack_substVarLT_ff_tc cs j s k)
      | succ b' =>
          exact replayablePayload_prepend_liftStack_substVarLT_step
            (target := lfLiftStack cs (.var (k - 1))) cs j s (peano k)
            (ltT (peano 0) (peano (Nat.succ b')))
            (substVarLT j s (peano k) (con0 "tt"))
            (os_substVarLT_lt_zs_tc j s (peano k) (peano b')
              hj hs (isnormal_peano_tc k))
            (replayablePayload_liftStack_substVarLT_tt_tc cs j s k)
  | succ a ih =>
      intro b
      cases b with
      | zero =>
          exact replayablePayload_prepend_liftStack_substVarLT_step
            (target := lfLiftStack cs (.var k)) cs j s (peano k)
            (ltT (peano (Nat.succ a)) (peano 0))
            (substVarLT j s (peano k) (con0 "ff"))
            (os_substVarLT_lt_sz_tc j s (peano k) (peano a)
              hj hs (isnormal_peano_tc k))
            (replayablePayload_liftStack_substVarLT_ff_tc cs j s k)
      | succ b' =>
          have hnext := ih b'
          have hthis : ReplayablePayload
              (liftStack cs
                (substVarLT j s (peano k)
                  (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))))
              (lfLiftStack cs (if a < b' then .var (k - 1) else .var k)) := by
            exact replayablePayload_prepend_liftStack_substVarLT_step
              (target := lfLiftStack cs (if a < b' then .var (k - 1) else .var k))
              cs j s (peano k)
              (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))
              (substVarLT j s (peano k) (ltT (peano a) (peano b')))
              (os_substVarLT_lt_ss_tc j s (peano k) (peano a) (peano b')
                hj hs (isnormal_peano_tc k))
              hnext
          simpa only [if_succ_lt_succ_eq] using hthis

theorem replayablePayload_liftStack_substVarLT_peano_payload_tc
    (cs : List Nat) (j k : Nat) {sAst : AST} {sTerm : LF.Term}
    (hs : StackReplayablePayload sAst sTerm) :
    ReplayablePayload
      (liftStack cs
        (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k))))
      (lfLiftStack cs (if j < k then .var (k - 1) else .var k)) := by
  rcases hs.replay.1.reduces with ⟨sVal, Ns, hsEnc, hsEval⟩
  have hsNorm : IsNormal pTC sVal := isnormal_encTyCore?_tc sTerm sVal hsEnc
  have hcall : LiftablePayload
      (liftStack cs
        (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k))))
      (lfLiftStack cs (if j < k then .var (k - 1) else .var k)) := by
    exact LiftablePayload.liftStacked
      (liftable_substVarLT_payload_peano_tc j k hs.replay.1) cs
  have hnext : ReplayablePayload
      (liftStack cs
        (substVarLT (peano j) sVal (peano k) (ltT (peano j) (peano k))))
      (lfLiftStack cs (if j < k then .var (k - 1) else .var k)) := by
    exact replayablePayload_liftStack_substVarLT_peano_guard_tc cs
      (peano j) sVal k (isnormal_peano_tc j) hsNorm j k
  exact replayablePayload_prefix_nfT_arg
    (u := liftStack cs
      (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k))))
    (v := liftStack cs
      (substVarLT (peano j) sVal (peano k) (ltT (peano j) (peano k))))
    (t := lfLiftStack cs (if j < k then .var (k - 1) else .var k))
    hcall
    (by
      intro fuelNat
      simpa [peano] using
        cong_eval_nf_wrapper_with_guard
          (fun s => nfT (peano (Nat.succ fuelNat))
            (liftStack cs
              (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k)))))
          (fun s => NFActiveShape.nf (peano (Nat.succ fuelNat))
            (liftStack cs
              (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k)))))
          (fun s s' hstep =>
            hcong_nfT_s_liftStack_substVarLT2_lt_tc cs (peano fuelNat)
              (peano j) (peano k) (peano j) (peano k)
              (isnormal_peano_tc fuelNat) (isnormal_peano_tc j) s s' hstep)
          Ns hsEval hsNorm)
    hnext

theorem stackReplayablePayload_substVarLT_peano_payload_tc
    (j k : Nat) {sAst : AST} {sTerm : LF.Term}
    (hs : StackReplayablePayload sAst sTerm) :
    StackReplayablePayload
      (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
      (if j < k then .var (k - 1) else .var k) := by
  intro cs
  exact replayablePayload_liftStack_substVarLT_peano_payload_tc cs j k hs

theorem stackReplayablePayload_substT_var_miss_tc (j k : Nat)
    {sAst : AST} {sTerm : LF.Term}
    (h : k ≠ j) (hs : StackReplayablePayload sAst sTerm) :
    StackReplayablePayload (substT (peano j) sAst (Var (peano k)))
      (if j < k then .var (k - 1) else .var k) := by
  have hneq : j ≠ k := by
    intro hjk
    exact h hjk.symm
  apply stackReplayablePayload_of_step
  · intro cs
    exact liftStack_descend_substT_step_tc cs (peano j) sAst (Var (peano k))
      (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
      (os_substT_var_miss_tc j k sAst hneq)
  · intro cs fuelNat
    simpa [peano] using
      hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat)
        (peano j) sAst (Var (peano k))
        (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
        (isnormal_peano_tc fuelNat) (os_substT_var_miss_tc j k sAst hneq)
  · exact stackReplayablePayload_substVarLT_peano_payload_tc j k hs

theorem nfT_var_first_replay (fuel : AST) (k : Nat) :
    FirstReplayNF (.var k) (Var (peano k)) (nfT (S fuel) (Var (peano k))) := by
  exact FirstReplayNF.intro (payload := Var (peano k)) (N := 1) (M := 0)
    rfl (nfT_var_tc fuel (peano k))
    (by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst j
      exact NFActiveShape.nf (S fuel) (Var (peano k)))
    (liftable_var_tc k) (stackReplayablePayload_var_tc k)
    (liftable_var_tc k) (stackReplayablePayload_var_tc k) rfl

theorem nfT_var_addN_one_first_replay (fuel : AST) (k : Nat) :
    FirstReplayNF (.var (k + 1)) (Var (peano (k + 1)))
      (nfT (S fuel) (Var (addN (peano k) (S Z)))) := by
  obtain ⟨M, hM⟩ := var_addN_sim_tc k 1
  have hM' : eval pTC M (Var (addN (peano k) (S Z))) = Var (peano (k + 1)) := by
    simpa [peano] using hM
  exact FirstReplayNF.intro (payload := Var (addN (peano k) (S Z))) (N := 1) (M := M)
    rfl (nfT_var_tc fuel (addN (peano k) (S Z)))
    (by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst j
      exact NFActiveShape.nf (S fuel) (Var (addN (peano k) (S Z))))
    (liftable_var_addN_one_tc k) (stackReplayablePayload_var_addN_one_tc k)
    (liftable_var_tc (k + 1)) (stackReplayablePayload_var_tc (k + 1)) hM'

theorem nfT_var_predN_first_replay (fuel : AST) (k : Nat) :
    FirstReplayNF (.var (k - 1)) (Var (peano (k - 1)))
      (nfT (S fuel) (Var (predN (peano k)))) := by
  obtain ⟨M, hM⟩ := var_predN_sim_tc k
  exact FirstReplayNF.intro (payload := Var (predN (peano k))) (N := 1) (M := M)
    rfl (nfT_var_tc fuel (predN (peano k)))
    (by
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst j
      exact NFActiveShape.nf (S fuel) (Var (predN (peano k))))
    (liftable_var_predN_peano_tc k) (stackReplayablePayload_var_predN_peano_tc k)
    (liftable_var_tc (k - 1)) (stackReplayablePayload_var_tc (k - 1)) hM

theorem nfT_substVarLT_tt_first_replay
    (fuel j s : AST) (k : Nat) (hfuel : IsNormal pTC fuel) :
    FirstReplayNF (.var (k - 1)) (Var (peano (k - 1)))
      (nfT (S fuel) (substVarLT j s (peano k) (con0 "tt"))) := by
  have hstep : eval pTC 1
      (nfT (S fuel) (substVarLT j s (peano k) (con0 "tt"))) =
      nfT (S fuel) (Var (predN (peano k))) := by
    simp only [eval,
      hcong_nfT_s_substVarLT_arg_tc fuel j s (peano k) (con0 "tt")
        (Var (predN (peano k))) hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substVarLT j s (peano k) (con0 "tt")))
    (nfT_var_predN_first_replay fuel k)

theorem nfT_substVarLT_ff_first_replay
    (fuel j s : AST) (k : Nat) (hfuel : IsNormal pTC fuel) :
    FirstReplayNF (.var k) (Var (peano k))
      (nfT (S fuel) (substVarLT j s (peano k) (con0 "ff"))) := by
  have hstep : eval pTC 1
      (nfT (S fuel) (substVarLT j s (peano k) (con0 "ff"))) =
      nfT (S fuel) (Var (peano k)) := by
    simp only [eval,
      hcong_nfT_s_substVarLT_arg_tc fuel j s (peano k) (con0 "ff")
        (Var (peano k)) hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substVarLT j s (peano k) (con0 "ff")))
    (nfT_var_first_replay fuel k)

theorem nfT_substVarLT_guard_normal_first_replay :
    ∀ (a b k : Nat) (fuel j s : AST),
      IsNormal pTC fuel -> IsNormal pTC j -> IsNormal pTC s ->
        ∃ v,
          FirstReplayNF (if a < b then .var (k - 1) else .var k) v
            (nfT (S fuel) (substVarLT j s (peano k) (ltT (peano a) (peano b)))) := by
  intro a
  induction a with
  | zero =>
      intro b k fuel j s hfuel hj hs
      cases b with
      | zero =>
          refine ⟨Var (peano k), ?_⟩
          have hstep : eval pTC 1
              (nfT (S fuel) (substVarLT j s (peano k) (ltT (peano 0) (peano 0)))) =
              nfT (S fuel) (substVarLT j s (peano k) (con0 "ff")) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel j s (peano k)
                (ltT Z Z) (substVarLT j s (peano k) (con0 "ff")) hfuel
                (os_substVarLT_lt_zz_tc j s (peano k) hj hs (isnormal_peano_tc k))]
          have hlt : ¬ 0 < 0 := Nat.not_lt_zero 0
          simpa only [hlt, if_false] using
            first_replay_nf_prepend hstep
              (NFActiveShape.nf (S fuel)
                (substVarLT j s (peano k) (ltT (peano 0) (peano 0))))
              (nfT_substVarLT_ff_first_replay fuel j s k hfuel)
      | succ b' =>
          refine ⟨Var (peano (k - 1)), ?_⟩
          have hstep : eval pTC 1
              (nfT (S fuel)
                (substVarLT j s (peano k) (ltT (peano 0) (peano (Nat.succ b'))))) =
              nfT (S fuel) (substVarLT j s (peano k) (con0 "tt")) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel j s (peano k)
                (ltT Z (S (peano b'))) (substVarLT j s (peano k) (con0 "tt")) hfuel
                (os_substVarLT_lt_zs_tc j s (peano k) (peano b') hj hs
                  (isnormal_peano_tc k))]
          have hlt : 0 < Nat.succ b' := Nat.zero_lt_succ b'
          simpa only [hlt, if_true] using
            first_replay_nf_prepend hstep
              (NFActiveShape.nf (S fuel)
                (substVarLT j s (peano k) (ltT (peano 0) (peano (Nat.succ b')))))
              (nfT_substVarLT_tt_first_replay fuel j s k hfuel)
  | succ a ih =>
      intro b k fuel j s hfuel hj hs
      cases b with
      | zero =>
          refine ⟨Var (peano k), ?_⟩
          have hstep : eval pTC 1
              (nfT (S fuel)
                (substVarLT j s (peano k) (ltT (peano (Nat.succ a)) (peano 0)))) =
              nfT (S fuel) (substVarLT j s (peano k) (con0 "ff")) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel j s (peano k)
                (ltT (S (peano a)) Z) (substVarLT j s (peano k) (con0 "ff")) hfuel
                (os_substVarLT_lt_sz_tc j s (peano k) (peano a) hj hs
                  (isnormal_peano_tc k))]
          have hlt : ¬ Nat.succ a < 0 := Nat.not_lt_zero (Nat.succ a)
          simpa only [hlt, if_false] using
            first_replay_nf_prepend hstep
              (NFActiveShape.nf (S fuel)
                (substVarLT j s (peano k) (ltT (peano (Nat.succ a)) (peano 0))))
              (nfT_substVarLT_ff_first_replay fuel j s k hfuel)
      | succ b' =>
          obtain ⟨v, hnext⟩ := ih b' k fuel j s hfuel hj hs
          refine ⟨v, ?_⟩
          have hstep : eval pTC 1
              (nfT (S fuel)
                (substVarLT j s (peano k)
                  (ltT (peano (Nat.succ a)) (peano (Nat.succ b'))))) =
              nfT (S fuel) (substVarLT j s (peano k) (ltT (peano a) (peano b'))) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel j s (peano k)
                (ltT (S (peano a)) (S (peano b')))
                (substVarLT j s (peano k) (ltT (peano a) (peano b'))) hfuel
                (os_substVarLT_lt_ss_tc j s (peano k) (peano a) (peano b') hj hs
                  (isnormal_peano_tc k))]
          simpa only [if_succ_lt_succ_eq] using
            first_replay_nf_prepend hstep
              (NFActiveShape.nf (S fuel)
                (substVarLT j s (peano k)
                  (ltT (peano (Nat.succ a)) (peano (Nat.succ b')))))
              hnext

theorem nfT_substVarLT_peano_payload_first_replay (fuel : AST) (j k : Nat)
    {sAst : AST} {sTerm : LF.Term}
    (hfuel : IsNormal pTC fuel) (hs : StackReplayablePayload sAst sTerm) :
    ∃ v,
      FirstReplayNF (if j < k then .var (k - 1) else .var k) v
        (nfT (S fuel)
          (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))) := by
  rcases hs.replay.1.reduces with ⟨sVal, Ns, hsEnc, hsEval⟩
  have hsNorm : IsNormal pTC sVal := isnormal_encTyCore?_tc sTerm sVal hsEnc
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun s => nfT (S fuel)
        (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k))))
      (fun s => NFActiveShape.nf (S fuel)
        (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k))))
      (fun s s' hstep =>
        hcong_nfT_s_substVarLT2_lt_tc fuel (peano j) (peano k) (peano j) (peano k)
          hfuel (isnormal_peano_tc j) s s' hstep)
      Ns hsEval hsNorm
  obtain ⟨v, hnext⟩ :=
    nfT_substVarLT_guard_normal_first_replay j k k fuel (peano j) sVal
      hfuel (isnormal_peano_tc j) hsNorm
  exact ⟨v, first_replay_nf_prefix hMctx hMguard hnext⟩

theorem liftable_liftVarT_tt_tc (b idx : Nat) :
    LiftablePayload (liftVarT (S Z) (peano b) (peano idx) (con0 "tt")) (.var idx) := by
  apply liftable_of_stack_step
  · intro cs
    exact liftStack_descend_liftVarT_step_tc cs (S Z) (peano b) (peano idx)
      (con0 "tt") (Var (peano idx)) rfl
  · exact liftable_var_tc idx

theorem liftable_liftVarT_ff_tc (b idx : Nat) :
    LiftablePayload (liftVarT (S Z) (peano b) (peano idx) (con0 "ff"))
      (.var (idx + 1)) := by
  apply liftable_of_stack_step
  · intro cs
    exact liftStack_descend_liftVarT_step_tc cs (S Z) (peano b) (peano idx)
      (con0 "ff") (Var (addN (peano idx) (S Z))) rfl
  · exact liftable_var_addN_one_tc idx

theorem replayablePayload_liftVarT_tt_tc (b idx : Nat) :
    ReplayablePayload (liftVarT (S Z) (peano b) (peano idx) (con0 "tt"))
      (.var idx) := by
  exact replayablePayload_prepend_nfT_arg
    (u := liftVarT (S Z) (peano b) (peano idx) (con0 "tt"))
    (v := Var (peano idx)) (t := .var idx)
    (liftable_liftVarT_tt_tc b idx)
    (by
      intro fuelNat
      simpa [peano, liftStack] using
        hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
          (S Z) (peano b) (peano idx) (con0 "tt") (Var (peano idx))
          (isnormal_peano_tc fuelNat) rfl)
    (replayablePayload_var_tc idx)

theorem replayablePayload_liftVarT_ff_tc (b idx : Nat) :
    ReplayablePayload (liftVarT (S Z) (peano b) (peano idx) (con0 "ff"))
      (.var (idx + 1)) := by
  exact replayablePayload_prepend_nfT_arg
    (u := liftVarT (S Z) (peano b) (peano idx) (con0 "ff"))
    (v := Var (addN (peano idx) (S Z))) (t := .var (idx + 1))
    (liftable_liftVarT_ff_tc b idx)
    (by
      intro fuelNat
      simpa [peano, liftStack] using
        hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
          (S Z) (peano b) (peano idx) (con0 "ff")
          (Var (addN (peano idx) (S Z)))
          (isnormal_peano_tc fuelNat) rfl)
    (replayablePayload_var_addN_one_tc idx)

theorem replayablePayload_liftVarT_peano_guard_succ_tc (a b cutoff idx : Nat)
    (hnext : ReplayablePayload
      (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano a) (peano b)))
      (if a < b then .var idx else .var (idx + 1))) :
    ReplayablePayload
      (liftVarT (S Z) (peano cutoff) (peano idx)
        (ltT (peano (Nat.succ a)) (peano (Nat.succ b))))
      (if Nat.succ a < Nat.succ b then .var idx else .var (idx + 1)) := by
  rw [if_succ_lt_succ_eq]
  have hlift0 :=
    liftable_liftVarT_peano_guard_cutoff_tc (Nat.succ a) (Nat.succ b) cutoff idx
  rw [if_succ_lt_succ_eq] at hlift0
  exact replayablePayload_prepend_nfT_arg
    (u := liftVarT (S Z) (peano cutoff) (peano idx)
      (ltT (peano (Nat.succ a)) (peano (Nat.succ b))))
    (v := liftVarT (S Z) (peano cutoff) (peano idx)
      (ltT (peano a) (peano b)))
    (t := if a < b then .var idx else .var (idx + 1))
    hlift0
    (by
      intro fuelNat
      simpa [peano, liftStack] using
        hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
          (S Z) (peano cutoff) (peano idx)
          (ltT (peano (Nat.succ a)) (peano (Nat.succ b)))
          (liftVarT (S Z) (peano cutoff) (peano idx)
            (ltT (peano a) (peano b)))
          (isnormal_peano_tc fuelNat)
          (os_liftVarT_lt_ss_tc (S Z) (peano cutoff) (peano idx)
            (peano a) (peano b) (isnormal_peano_tc 1)
            (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
    hnext

theorem replayablePayload_liftVarT_peano_guard_zero_succ_tc (b cutoff idx : Nat) :
    ReplayablePayload
      (liftVarT (S Z) (peano cutoff) (peano idx)
        (ltT (peano 0) (peano (Nat.succ b))))
      (if 0 < Nat.succ b then .var idx else .var (idx + 1)) := by
  have hlt : 0 < Nat.succ b := Nat.succ_pos b
  rw [if_pos hlt]
  have hlift0 := liftable_liftVarT_peano_guard_cutoff_tc 0 (Nat.succ b) cutoff idx
  rw [if_pos hlt] at hlift0
  exact replayablePayload_prepend_nfT_arg
    (u := liftVarT (S Z) (peano cutoff) (peano idx)
      (ltT (peano 0) (peano (Nat.succ b))))
    (v := liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt"))
    (t := .var idx)
    hlift0
    (by
      intro fuelNat
      simpa [peano, liftStack] using
        hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
          (S Z) (peano cutoff) (peano idx)
          (ltT (peano 0) (peano (Nat.succ b)))
          (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "tt"))
          (isnormal_peano_tc fuelNat)
          (os_liftVarT_lt_zs_tc (S Z) (peano cutoff) (peano idx)
            (peano b) (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
            (isnormal_peano_tc idx)))
    (replayablePayload_liftVarT_tt_tc cutoff idx)

theorem replayablePayload_liftVarT_peano_guard_tc :
    ∀ (a b cutoff idx : Nat),
      ReplayablePayload
        (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano a) (peano b)))
        (if a < b then .var idx else .var (idx + 1)) := by
  intro a
  induction a with
  | zero =>
      intro b cutoff idx
      cases b with
      | zero =>
          exact replayablePayload_prepend_nfT_arg
            (u := liftVarT (S Z) (peano cutoff) (peano idx) (ltT (peano 0) (peano 0)))
            (v := liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
            (t := .var (idx + 1))
            (by simpa using liftable_liftVarT_peano_guard_cutoff_tc 0 0 cutoff idx)
            (by
              intro fuelNat
              simpa [peano, liftStack] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx) (ltT (peano 0) (peano 0))
                  (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                  (isnormal_peano_tc fuelNat)
                  (os_liftVarT_lt_zz_tc (S Z) (peano cutoff) (peano idx)
                    (isnormal_peano_tc 1) (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
            (by simpa using replayablePayload_liftVarT_ff_tc cutoff idx)
      | succ b' =>
          exact replayablePayload_liftVarT_peano_guard_zero_succ_tc b' cutoff idx
  | succ a ih =>
      intro b cutoff idx
      cases b with
      | zero =>
          exact replayablePayload_prepend_nfT_arg
            (u := liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (peano (Nat.succ a)) (peano 0)))
            (v := liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
            (t := .var (idx + 1))
            (by simpa using liftable_liftVarT_peano_guard_cutoff_tc (Nat.succ a) 0 cutoff idx)
            (by
              intro fuelNat
              simpa [peano, liftStack] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx)
                  (ltT (peano (Nat.succ a)) (peano 0))
                  (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                  (isnormal_peano_tc fuelNat)
                  (os_liftVarT_lt_sz_tc (S Z) (peano cutoff) (peano idx)
                    (peano a) (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx)))
            (by simpa using replayablePayload_liftVarT_ff_tc cutoff idx)
      | succ b' =>
          exact replayablePayload_liftVarT_peano_guard_succ_tc a b' cutoff idx
            (ih b' cutoff idx)

theorem replayablePayload_liftVarT_guard_addN_one_tc :
    ∀ (k b cutoff idx : Nat),
      ReplayablePayload
        (liftVarT (S Z) (peano cutoff) (peano idx)
          (ltT (addN (peano k) (S Z)) (peano b)))
        (if k + 1 < b then .var idx else .var (idx + 1)) := by
  intro k
  induction k with
  | zero =>
      intro b cutoff idx
      exact replayablePayload_prepend_nfT_arg
        (u := liftVarT (S Z) (peano cutoff) (peano idx)
          (ltT (addN (peano 0) (S Z)) (peano b)))
        (v := liftVarT (S Z) (peano cutoff) (peano idx)
          (ltT (peano 1) (peano b)))
        (t := if 0 + 1 < b then .var idx else .var (idx + 1))
        (liftable_liftVarT_guard_addN_one_tc 0 b cutoff idx)
        (by
          intro fuelNat
          have hguardStep : oneStep pTC (ltT (addN (peano 0) (S Z)) (peano b)) =
              some (ltT (S Z) (peano b)) := by
            have hadd : oneStep pTC (addN Z (S Z)) = some (S Z) := by rfl
            exact hcong_ltT1_tc (addN Z (S Z)) (peano b) (S Z) hadd rfl
          simpa [peano, liftStack] using
            hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
              (S Z) (peano cutoff) (peano idx)
              (ltT (addN (peano 0) (S Z)) (peano b))
              (liftVarT (S Z) (peano cutoff) (peano idx) (ltT (S Z) (peano b)))
              (isnormal_peano_tc fuelNat)
              (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                (addN (peano 0) (S Z)) (peano b)
                (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                (isnormal_peano_tc idx) (ltT (S Z) (peano b)) hguardStep))
        (by simpa [peano] using replayablePayload_liftVarT_peano_guard_tc 1 b cutoff idx)
  | succ k ih =>
      intro b cutoff idx
      cases b with
      | zero =>
          have hmidLift : LiftablePayload
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) Z))
              (.var (idx + 1)) := by
            apply liftable_of_stack_step
            · intro cs
              exact liftStack_descend_liftVarT_step_tc cs (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) Z)
                (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                (os_liftVarT_lt_sz_tc (S Z) (peano cutoff) (peano idx)
                  (addN (peano k) (S Z)) (isnormal_peano_tc 1)
                  (isnormal_peano_tc cutoff) (isnormal_peano_tc idx))
            · exact liftable_liftVarT_ff_tc cutoff idx
          have hmidReplay : ReplayablePayload
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) Z))
              (.var (idx + 1)) := by
            exact replayablePayload_prepend_nfT_arg
              (u := liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) Z))
              (v := liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
              (t := .var (idx + 1))
              hmidLift
              (by
                intro fuelNat
                simpa [peano, liftStack] using
                  hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
                    (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) Z)
                    (liftVarT (S Z) (peano cutoff) (peano idx) (con0 "ff"))
                    (isnormal_peano_tc fuelNat)
                    (os_liftVarT_lt_sz_tc (S Z) (peano cutoff) (peano idx)
                      (addN (peano k) (S Z)) (isnormal_peano_tc 1)
                      (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
              (replayablePayload_liftVarT_ff_tc cutoff idx)
          have hpre := replayablePayload_prepend_nfT_arg
            (u := liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0)))
            (v := liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (S (addN (peano k) (S Z))) Z))
            (t := .var (idx + 1))
            (by simpa using liftable_liftVarT_guard_addN_one_tc (Nat.succ k) 0 cutoff idx)
            (by
              intro fuelNat
              have hguardStep : oneStep pTC
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0)) =
                  some (ltT (S (addN (peano k) (S Z))) Z) := by
                have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                    some (S (addN (peano k) (S Z))) := by rfl
                exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) Z
                  (S (addN (peano k) (S Z))) hadd rfl
              simpa [peano, liftStack] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano 0))
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) Z))
                  (isnormal_peano_tc fuelNat)
                  (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                    (addN (peano (Nat.succ k)) (S Z)) (peano 0)
                    (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx)
                    (ltT (S (addN (peano k) (S Z))) Z) hguardStep))
            hmidReplay
          simpa using hpre
      | succ b' =>
          have hmidLift : LiftablePayload
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) (S (peano b'))))
              (if k + 1 < b' then .var idx else .var (idx + 1)) := by
            apply liftable_of_stack_step
            · intro cs
              exact liftStack_descend_liftVarT_step_tc cs (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) (S (peano b')))
                (liftVarT (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano k) (S Z)) (peano b')))
                (os_liftVarT_lt_ss_tc (S Z) (peano cutoff) (peano idx)
                  (addN (peano k) (S Z)) (peano b') (isnormal_peano_tc 1)
                  (isnormal_peano_tc cutoff) (isnormal_peano_tc idx))
            · exact liftable_liftVarT_guard_addN_one_tc k b' cutoff idx
          have hmidReplay : ReplayablePayload
              (liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) (S (peano b'))))
              (if k + 1 < b' then .var idx else .var (idx + 1)) := by
            exact replayablePayload_prepend_nfT_arg
              (u := liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (S (addN (peano k) (S Z))) (S (peano b'))))
              (v := liftVarT (S Z) (peano cutoff) (peano idx)
                (ltT (addN (peano k) (S Z)) (peano b')))
              (t := if k + 1 < b' then .var idx else .var (idx + 1))
              hmidLift
              (by
                intro fuelNat
                simpa [peano, liftStack] using
                  hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
                    (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) (S (peano b')))
                    (liftVarT (S Z) (peano cutoff) (peano idx)
                      (ltT (addN (peano k) (S Z)) (peano b')))
                    (isnormal_peano_tc fuelNat)
                    (os_liftVarT_lt_ss_tc (S Z) (peano cutoff) (peano idx)
                      (addN (peano k) (S Z)) (peano b') (isnormal_peano_tc 1)
                      (isnormal_peano_tc cutoff) (isnormal_peano_tc idx)))
              (ih b' cutoff idx)
          have hpre := replayablePayload_prepend_nfT_arg
            (u := liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))))
            (v := liftVarT (S Z) (peano cutoff) (peano idx)
              (ltT (S (addN (peano k) (S Z))) (S (peano b'))))
            (t := if k + 1 < b' then .var idx else .var (idx + 1))
            (by
              simpa only [if_succ_add_one_lt_succ_eq] using
                liftable_liftVarT_guard_addN_one_tc (Nat.succ k) (Nat.succ b') cutoff idx)
            (by
              intro fuelNat
              have hguardStep : oneStep pTC
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))) =
                  some (ltT (S (addN (peano k) (S Z))) (S (peano b'))) := by
                have hadd : oneStep pTC (addN (S (peano k)) (S Z)) =
                    some (S (addN (peano k) (S Z))) := by rfl
                exact hcong_ltT1_tc (addN (S (peano k)) (S Z)) (S (peano b'))
                  (S (addN (peano k) (S Z))) hadd rfl
              simpa [peano, liftStack] using
                hcong_nfT_s_liftStack_liftVarT_arg_tc [] (peano fuelNat)
                  (S Z) (peano cutoff) (peano idx)
                  (ltT (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b')))
                  (liftVarT (S Z) (peano cutoff) (peano idx)
                    (ltT (S (addN (peano k) (S Z))) (S (peano b'))))
                  (isnormal_peano_tc fuelNat)
                  (hcong_liftVarT4_lt_tc (S Z) (peano cutoff) (peano idx)
                    (addN (peano (Nat.succ k)) (S Z)) (peano (Nat.succ b'))
                    (isnormal_peano_tc 1) (isnormal_peano_tc cutoff)
                    (isnormal_peano_tc idx)
                    (ltT (S (addN (peano k) (S Z))) (S (peano b'))) hguardStep))
            hmidReplay
          simpa only [if_succ_add_one_lt_succ_eq] using hpre

theorem nfT_substVarLT_tt_first_strong (fuel jAst sVal : AST) (k : Nat)
    (hfuel : IsNormal pTC fuel) :
    FirstStrongNF (.var (k - 1)) (Var (peano (k - 1)))
      (nfT (S fuel) (substVarLT jAst sVal (peano k) (con0 "tt"))) := by
  exact first_strong_nf_prepend
    (by
      simp only [eval, hcong_nfT_s_substVarLT_arg_tc fuel jAst sVal (peano k)
        (con0 "tt") (Var (predN (peano k))) hfuel rfl])
    (NFActiveShape.nf (S fuel) (substVarLT jAst sVal (peano k) (con0 "tt")))
    (nfT_var_predN_first_strong fuel k)

theorem nfT_substVarLT_ff_first_strong (fuel jAst sVal : AST) (k : Nat)
    (hfuel : IsNormal pTC fuel) :
    FirstStrongNF (.var k) (Var (peano k))
      (nfT (S fuel) (substVarLT jAst sVal (peano k) (con0 "ff"))) := by
  exact first_strong_nf_prepend
    (by
      simp only [eval, hcong_nfT_s_substVarLT_arg_tc fuel jAst sVal (peano k)
        (con0 "ff") (Var (peano k)) hfuel rfl])
    (NFActiveShape.nf (S fuel) (substVarLT jAst sVal (peano k) (con0 "ff")))
    (nfT_var_first_strong fuel k)

theorem nfT_substVarLT_guard_normal_first_strong :
    ∀ (a b k : Nat) (fuel jAst sVal : AST),
    IsNormal pTC fuel -> IsNormal pTC jAst -> IsNormal pTC sVal ->
    FirstStrongNF (if a < b then .var (k - 1) else .var k)
      (if a < b then Var (peano (k - 1)) else Var (peano k))
      (nfT (S fuel) (substVarLT jAst sVal (peano k) (ltT (peano a) (peano b)))) := by
  intro a
  induction a with
  | zero =>
      intro b k fuel jAst sVal hfuel hj hsVal
      cases b with
      | zero =>
          have hstep : eval pTC 1
              (nfT (S fuel) (substVarLT jAst sVal (peano k) (ltT (peano 0) (peano 0)))) =
              nfT (S fuel) (substVarLT jAst sVal (peano k) (con0 "ff")) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel jAst sVal (peano k) (ltT Z Z)
                (substVarLT jAst sVal (peano k) (con0 "ff")) hfuel
                (os_substVarLT_lt_zz_tc jAst sVal (peano k) hj hsVal (isnormal_peano_tc k))]
          have hnext := nfT_substVarLT_ff_first_strong fuel jAst sVal k hfuel
          have hlt : ¬ 0 < 0 := Nat.not_lt_zero 0
          simpa only [hlt, if_false] using first_strong_nf_prepend hstep
            (NFActiveShape.nf (S fuel) (substVarLT jAst sVal (peano k)
              (ltT (peano 0) (peano 0)))) hnext
      | succ b' =>
          have hstep : eval pTC 1
              (nfT (S fuel) (substVarLT jAst sVal (peano k)
                (ltT (peano 0) (peano (Nat.succ b'))))) =
              nfT (S fuel) (substVarLT jAst sVal (peano k) (con0 "tt")) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel jAst sVal (peano k)
                (ltT Z (S (peano b'))) (substVarLT jAst sVal (peano k) (con0 "tt")) hfuel
                (os_substVarLT_lt_zs_tc jAst sVal (peano k) (peano b') hj hsVal
                  (isnormal_peano_tc k))]
          have hnext := nfT_substVarLT_tt_first_strong fuel jAst sVal k hfuel
          have hlt : 0 < Nat.succ b' := Nat.zero_lt_succ b'
          simpa only [hlt, if_true] using first_strong_nf_prepend hstep
            (NFActiveShape.nf (S fuel) (substVarLT jAst sVal (peano k)
              (ltT (peano 0) (peano (Nat.succ b'))))) hnext
  | succ a ih =>
      intro b k fuel jAst sVal hfuel hj hsVal
      cases b with
      | zero =>
          have hstep : eval pTC 1
              (nfT (S fuel) (substVarLT jAst sVal (peano k)
                (ltT (peano (Nat.succ a)) (peano 0)))) =
              nfT (S fuel) (substVarLT jAst sVal (peano k) (con0 "ff")) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel jAst sVal (peano k)
                (ltT (S (peano a)) Z) (substVarLT jAst sVal (peano k) (con0 "ff")) hfuel
                (os_substVarLT_lt_sz_tc jAst sVal (peano k) (peano a) hj hsVal
                  (isnormal_peano_tc k))]
          have hnext := nfT_substVarLT_ff_first_strong fuel jAst sVal k hfuel
          have hlt : ¬ Nat.succ a < 0 := Nat.not_lt_zero (Nat.succ a)
          simpa only [hlt, if_false] using first_strong_nf_prepend hstep
            (NFActiveShape.nf (S fuel) (substVarLT jAst sVal (peano k)
              (ltT (peano (Nat.succ a)) (peano 0)))) hnext
      | succ b' =>
          have hstep : eval pTC 1
              (nfT (S fuel) (substVarLT jAst sVal (peano k)
                (ltT (peano (Nat.succ a)) (peano (Nat.succ b'))))) =
              nfT (S fuel) (substVarLT jAst sVal (peano k) (ltT (peano a) (peano b'))) := by
            simp only [peano, eval,
              hcong_nfT_s_substVarLT_arg_tc fuel jAst sVal (peano k)
                (ltT (S (peano a)) (S (peano b')))
                (substVarLT jAst sVal (peano k) (ltT (peano a) (peano b'))) hfuel
                (os_substVarLT_lt_ss_tc jAst sVal (peano k) (peano a) (peano b') hj hsVal
                  (isnormal_peano_tc k))]
          have hnext := ih b' k fuel jAst sVal hfuel hj hsVal
          simpa only [if_succ_lt_succ_eq] using first_strong_nf_prepend hstep
            (NFActiveShape.nf (S fuel) (substVarLT jAst sVal (peano k)
              (ltT (peano (Nat.succ a)) (peano (Nat.succ b'))))) hnext

theorem nfT_substVarLT_peano_payload_first_strong (fuel : AST) (j k : Nat)
    {sAst : AST} {sTerm : LF.Term}
    (hfuel : IsNormal pTC fuel) (hs : LiftablePayload sAst sTerm) :
    FirstStrongNF (if j < k then .var (k - 1) else .var k)
      (if j < k then Var (peano (k - 1)) else Var (peano k))
      (nfT (S fuel) (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))) := by
  rcases hs.reduces with ⟨sVal, Ns, hsEnc, hsEval⟩
  have hsNorm : IsNormal pTC sVal := isnormal_encTyCore?_tc sTerm sVal hsEnc
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun s => nfT (S fuel) (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k))))
      (fun s => NFActiveShape.nf (S fuel)
        (substVarLT (peano j) s (peano k) (ltT (peano j) (peano k))))
      (fun s s' hstep =>
        hcong_nfT_s_substVarLT2_lt_tc fuel (peano j) (peano k) (peano j) (peano k)
          hfuel (isnormal_peano_tc j) s s' hstep)
      Ns hsEval hsNorm
  have hnext := nfT_substVarLT_guard_normal_first_strong j k k fuel (peano j) sVal
    hfuel (isnormal_peano_tc j) hsNorm
  exact first_strong_nf_prefix hMctx hMguard hnext

theorem nfT_substT_var_payload_first_strong (fuelNat j k : Nat)
    {sAst : AST} {sTerm : LF.Term}
    (hs : ReplayablePayload sAst sTerm) :
    ∃ v,
      FirstStrongNF (LFTyping.nf LFTyping.corpusSig fuelNat
        (LFTyping.subst j sTerm (.var k))) v
        (nfT (peano fuelNat) (substT (peano j) sAst (Var (peano k)))) := by
  cases fuelNat with
  | zero =>
      have hcall : LiftablePayload (substT (peano j) sAst (Var (peano k)))
          (LFTyping.subst j sTerm (.var k)) := by
        exact liftable_substT_encTyCore_tc (.var k) (Var (peano k)) j sAst sTerm rfl hs.1
      rcases hcall.reduces with ⟨u, N, henc, hEval⟩
      refine ⟨u, ?_⟩
      change FirstStrongNF (LFTyping.subst j sTerm (.var k)) u
        (nfT Z (substT (peano j) sAst (Var (peano k))))
      simpa [LFTyping.nf] using
        (nfT_z_first_strong henc hcall (liftable_encTyCore?_tc _ _ henc) ⟨N, hEval⟩)
  | succ fuelPred =>
      by_cases hkj : k = j
      · subst k
        obtain ⟨v, hnext⟩ := hs.2 (Nat.succ fuelPred)
        refine ⟨v, ?_⟩
        have hstep : eval pTC 1
            (nfT (peano (Nat.succ fuelPred)) (substT (peano j) sAst (Var (peano j)))) =
            nfT (peano (Nat.succ fuelPred)) sAst := by
          simp only [peano, eval,
            hcong_nfT_s_substT_arg_tc (peano fuelPred) (peano j) sAst (Var (peano j)) sAst
              (isnormal_peano_tc fuelPred) (os_substT_var_self_tc (peano j) sAst)]
        simpa [LFTyping.subst] using
          first_strong_nf_prepend hstep
            (NFActiveShape.nf (peano (Nat.succ fuelPred))
              (substT (peano j) sAst (Var (peano j))))
            hnext
      · have hneq : j ≠ k := by
          intro hjk
          exact hkj hjk.symm
        refine ⟨if j < k then Var (peano (k - 1)) else Var (peano k), ?_⟩
        have hstep : eval pTC 1
            (nfT (peano (Nat.succ fuelPred)) (substT (peano j) sAst (Var (peano k)))) =
            nfT (peano (Nat.succ fuelPred))
              (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k))) := by
          simp only [peano, eval,
            hcong_nfT_s_substT_arg_tc (peano fuelPred) (peano j) sAst (Var (peano k))
              (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
              (isnormal_peano_tc fuelPred) (os_substT_var_miss_tc j k sAst hneq)]
        have hnext := nfT_substVarLT_peano_payload_first_strong (peano fuelPred) j k
          (isnormal_peano_tc fuelPred) hs.1
        by_cases hlt : j < k
        · simpa [LFTyping.subst, LFTyping.nf, hkj, hlt] using
            first_strong_nf_prepend hstep
              (NFActiveShape.nf (peano (Nat.succ fuelPred))
                (substT (peano j) sAst (Var (peano k))))
              hnext
        · simpa [LFTyping.subst, LFTyping.nf, hkj, hlt] using
            first_strong_nf_prepend hstep
              (NFActiveShape.nf (peano (Nat.succ fuelPred))
                (substT (peano j) sAst (Var (peano k))))
              hnext

theorem nfT_substT_var_payload_first_replay (fuelNat j k : Nat)
    {sAst sVal : AST} {sTerm : LF.Term}
    (hs : StackReplayablePayload sAst sTerm)
    (hsEnc : encTyCore? sTerm = some sVal)
    (hsEval : ∃ M, eval pTC M sAst = sVal)
    (hsFinal : StackReplayablePayload sVal sTerm)
    (hsNF : ∀ fuelNat : Nat,
      ∃ v, FirstReplayNF (LFTyping.nf LFTyping.corpusSig fuelNat sTerm) v
        (nfT (peano fuelNat) sAst)) :
    ∃ v,
      FirstReplayNF (LFTyping.nf LFTyping.corpusSig fuelNat
        (LFTyping.subst j sTerm (.var k))) v
        (nfT (peano fuelNat) (substT (peano j) sAst (Var (peano k)))) := by
  cases fuelNat with
  | zero =>
      by_cases hkj : k = j
      · subst k
        refine ⟨sVal, ?_⟩
        have hcallLift : LiftablePayload
            (substT (peano j) sAst (Var (peano j))) sTerm := by
          exact liftable_substT_var_self_tc j hs.replay.1
        have hcallReplay : StackReplayablePayload
            (substT (peano j) sAst (Var (peano j))) sTerm := by
          exact stackReplayablePayload_substT_var_self_tc j hs
        have hpayload : ∃ M,
            eval pTC M (substT (peano j) sAst (Var (peano j))) = sVal := by
          obtain ⟨M, hM⟩ := hsEval
          refine ⟨1 + M, ?_⟩
          have hstep : eval pTC 1 (substT (peano j) sAst (Var (peano j))) = sAst := by
            simp only [eval, os_substT_var_self_tc (peano j) sAst]
          exact eval_trans_tc 1 M _ _ _ hstep hM
        simpa [LFTyping.nf, LFTyping.subst, peano] using
          (nfT_z_first_replay hsEnc hcallLift hcallReplay
            (liftable_encTyCore?_tc sTerm sVal hsEnc) hsFinal hpayload)
      · have hcallLift : LiftablePayload
            (substT (peano j) sAst (Var (peano k)))
            (if j < k then .var (k - 1) else .var k) := by
          exact liftable_substT_var_miss_tc j k hkj hs.replay.1
        have hcallReplay : StackReplayablePayload
            (substT (peano j) sAst (Var (peano k)))
            (if j < k then .var (k - 1) else .var k) := by
          exact stackReplayablePayload_substT_var_miss_tc j k hkj hs
        by_cases hlt : j < k
        · refine ⟨Var (peano (k - 1)), ?_⟩
          have hsNorm : IsNormal pTC sVal := isnormal_encTyCore?_tc sTerm sVal hsEnc
          obtain ⟨N, hN⟩ := substT_var_payload_peano_tc j k sAst sVal hsNorm hsEval
          have hpayload : ∃ M,
              eval pTC M (substT (peano j) sAst (Var (peano k))) =
                Var (peano (k - 1)) := by
            refine ⟨N, ?_⟩
            simpa [hkj, hlt] using hN
          have henc' : encTyCore? (.var (k - 1)) = some (Var (peano (k - 1))) := rfl
          have hcallLift' : LiftablePayload
              (substT (peano j) sAst (Var (peano k))) (.var (k - 1)) := by
            simpa [hlt] using hcallLift
          have hcallReplay' : StackReplayablePayload
              (substT (peano j) sAst (Var (peano k))) (.var (k - 1)) := by
            simpa [hlt] using hcallReplay
          simpa [LFTyping.nf, LFTyping.subst, hkj, hlt, peano] using
            (nfT_z_first_replay henc' hcallLift' hcallReplay'
              (liftable_var_tc (k - 1)) (stackReplayablePayload_var_tc (k - 1))
              hpayload)
        · refine ⟨Var (peano k), ?_⟩
          have hsNorm : IsNormal pTC sVal := isnormal_encTyCore?_tc sTerm sVal hsEnc
          obtain ⟨N, hN⟩ := substT_var_payload_peano_tc j k sAst sVal hsNorm hsEval
          have hpayload : ∃ M,
              eval pTC M (substT (peano j) sAst (Var (peano k))) =
                Var (peano k) := by
            refine ⟨N, ?_⟩
            simpa [hkj, hlt] using hN
          have henc' : encTyCore? (.var k) = some (Var (peano k)) := rfl
          have hcallLift' : LiftablePayload
              (substT (peano j) sAst (Var (peano k))) (.var k) := by
            simpa [hlt] using hcallLift
          have hcallReplay' : StackReplayablePayload
              (substT (peano j) sAst (Var (peano k))) (.var k) := by
            simpa [hlt] using hcallReplay
          simpa [LFTyping.nf, LFTyping.subst, hkj, hlt, peano] using
            (nfT_z_first_replay henc' hcallLift' hcallReplay'
              (liftable_var_tc k) (stackReplayablePayload_var_tc k) hpayload)
  | succ fuelPred =>
      by_cases hkj : k = j
      · subst k
        obtain ⟨v, hnext⟩ := hsNF (Nat.succ fuelPred)
        refine ⟨v, ?_⟩
        have hstep : eval pTC 1
            (nfT (peano (Nat.succ fuelPred)) (substT (peano j) sAst (Var (peano j)))) =
            nfT (peano (Nat.succ fuelPred)) sAst := by
          simp only [peano, eval,
            hcong_nfT_s_substT_arg_tc (peano fuelPred) (peano j) sAst
              (Var (peano j)) sAst (isnormal_peano_tc fuelPred)
              (os_substT_var_self_tc (peano j) sAst)]
        simpa [LFTyping.subst] using
          first_replay_nf_prepend hstep
            (NFActiveShape.nf (peano (Nat.succ fuelPred))
              (substT (peano j) sAst (Var (peano j))))
            hnext
      · have hneq : j ≠ k := by
          intro hjk
          exact hkj hjk.symm
        obtain ⟨v, hnext⟩ :=
          nfT_substVarLT_peano_payload_first_replay (peano fuelPred) j k
            (isnormal_peano_tc fuelPred) hs
        refine ⟨v, ?_⟩
        have hstep : eval pTC 1
            (nfT (peano (Nat.succ fuelPred)) (substT (peano j) sAst (Var (peano k)))) =
            nfT (peano (Nat.succ fuelPred))
              (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k))) := by
          simp only [peano, eval,
            hcong_nfT_s_substT_arg_tc (peano fuelPred) (peano j) sAst (Var (peano k))
              (substVarLT (peano j) sAst (peano k) (ltT (peano j) (peano k)))
              (isnormal_peano_tc fuelPred) (os_substT_var_miss_tc j k sAst hneq)]
        by_cases hlt : j < k
        · simpa [LFTyping.subst, LFTyping.nf, hkj, hlt] using
            first_replay_nf_prepend hstep
              (NFActiveShape.nf (peano (Nat.succ fuelPred))
                (substT (peano j) sAst (Var (peano k))))
              hnext
        · simpa [LFTyping.subst, LFTyping.nf, hkj, hlt] using
            first_replay_nf_prepend hstep
              (NFActiveShape.nf (peano (Nat.succ fuelPred))
                (substT (peano j) sAst (Var (peano k))))
              hnext

theorem lookupBody_corpusSig_none (x : String) :
    LFTyping.lookupBody LFTyping.corpusSig x = none := by
  simp [LFTyping.lookupBody, LFTyping.corpusSig]

theorem nfT_con_first_liftable {fuel : AST} {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) :
    FirstLiftableNF (.con x) u (nfT (S fuel) u) := by
  unfold encTyCore? at h
  cases hx : encName? x with
  | none => simp [hx] at h
  | some k =>
      simp [hx] at h
      subst u
      exact FirstLiftableNF.intro (payload := Con k) (N := 1) (M := 0)
        (by
          unfold encTyCore?
          simp [hx])
        (by
          simpa [lookupBody_corpusSig_none] using nfT_con_tc fuel k)
        (by
          intro j hj
          have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
          subst j
          exact NFActiveShape.nf (S fuel) (Con k))
        (liftable_con_tc (by
          unfold encTyCore?
          simp [hx]))
        rfl

theorem nfT_con_first_strong {fuel : AST} {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) :
    FirstStrongNF (.con x) u (nfT (S fuel) u) := by
  unfold encTyCore? at h
  cases hx : encName? x with
  | none => simp [hx] at h
  | some k =>
      simp [hx] at h
      subst u
      have henc : encTyCore? (.con x) = some (Con k) := by
        unfold encTyCore?
        simp [hx]
      exact FirstStrongNF.intro (payload := Con k) (N := 1) (M := 0)
        henc
        (by simpa [lookupBody_corpusSig_none] using nfT_con_tc fuel k)
        (by
          intro j hj
          have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
          subst j
          exact NFActiveShape.nf (S fuel) (Con k))
        (liftable_con_tc henc) (liftable_con_tc henc) rfl

theorem stackReplayablePayload_con_tc {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) :
    StackReplayablePayload u (.con x) := by
  unfold encTyCore? at h
  cases hx : encName? x with
  | none => simp [hx] at h
  | some k =>
      simp [hx] at h
      subst u
      have henc : encTyCore? (.con x) = some (Con k) := by
        unfold encTyCore?
        simp [hx]
      intro cs
      induction cs with
      | nil =>
          constructor
          · exact liftable_con_tc henc
          · intro fuelNat
            cases fuelNat with
            | zero =>
                refine ⟨Con k, ?_⟩
                simpa [peano, LFTyping.nf, liftStack, lfLiftStack] using
                  (nfT_z_first_strong (t := .con x) (u := Con k) (call := Con k)
                    henc (liftable_con_tc henc) (liftable_con_tc henc) ⟨0, rfl⟩)
            | succ fuelPred =>
                refine ⟨Con k, ?_⟩
                simpa [peano, LFTyping.nf, lookupBody_corpusSig_none, liftStack, lfLiftStack] using
                  (nfT_con_first_strong (fuel := peano fuelPred) henc)
      | cons c cs ih =>
          have hroot : oneStep pTC (liftT (S Z) (peano c) (Con k)) = some (Con k) := by
            rfl
          have hnext : ReplayablePayload (liftStack cs (Con k)) (lfLiftStack cs (.con x)) := ih
          have hthis : ReplayablePayload
              (liftStack cs (liftT (S Z) (peano c) (Con k)))
              (lfLiftStack cs (.con x)) := by
            exact replayablePayload_prepend_nfT_arg
              (u := liftStack cs (liftT (S Z) (peano c) (Con k)))
              (v := liftStack cs (Con k))
              (t := lfLiftStack cs (.con x))
              (liftable_of_stack_step
                (u := liftStack cs (liftT (S Z) (peano c) (Con k)))
                (v := liftStack cs (Con k))
                (t := lfLiftStack cs (.con x))
                (by
                  intro ds
                  calc
                    oneStep pTC (liftStack ds (liftStack cs (liftT (S Z) (peano c) (Con k)))) =
                        oneStep pTC (liftStack (cs ++ ds) (liftT (S Z) (peano c) (Con k))) := by
                      rw [liftStack_append cs ds]
                    _ = some (liftStack (cs ++ ds) (Con k)) :=
                      liftStack_descend_lift_step_tc (cs ++ ds) c hroot
                    _ = some (liftStack ds (liftStack cs (Con k))) := by
                      rw [liftStack_append cs ds])
                hnext.1)
              (by
                intro fuelNat
                simpa [peano] using
                  hcong_nfT_s_liftStack_liftT_arg_tc cs (peano fuelNat) c
                    (Con k) (Con k) (isnormal_peano_tc fuelNat) hroot)
              hnext
          simpa [liftStack, lfLiftStack, LFTyping.lift] using hthis

theorem stackReplayablePayload_substT_con_tc {j sAst u : AST} {x : String}
    (henc : encTyCore? (.con x) = some u) :
    StackReplayablePayload (substT j sAst u) (.con x) := by
  unfold encTyCore? at henc
  cases hx : encName? x with
  | none => simp [hx] at henc
  | some k =>
      simp [hx] at henc
      subst u
      have henc' : encTyCore? (.con x) = some (Con k) := by
        unfold encTyCore?
        simp [hx]
      apply stackReplayablePayload_of_step
      · intro cs
        exact liftStack_descend_substT_step_tc cs j sAst (Con k) (Con k) rfl
      · intro cs fuelNat
        simpa [peano] using
          hcong_nfT_s_liftStack_substT_arg_tc cs (peano fuelNat)
            j sAst (Con k) (Con k) (isnormal_peano_tc fuelNat) rfl
      · exact stackReplayablePayload_con_tc henc'

theorem nfT_con_first_replay {fuel : AST} {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) :
    FirstReplayNF (.con x) u (nfT (S fuel) u) := by
  unfold encTyCore? at h
  cases hx : encName? x with
  | none => simp [hx] at h
  | some k =>
      simp [hx] at h
      subst u
      have henc : encTyCore? (.con x) = some (Con k) := by
        unfold encTyCore?
        simp [hx]
      have hrep := stackReplayablePayload_con_tc henc
      exact FirstReplayNF.intro (payload := Con k) (N := 1) (M := 0)
        henc
        (by simpa [lookupBody_corpusSig_none] using nfT_con_tc fuel k)
        (by
          intro j hj
          have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
          subst j
          exact NFActiveShape.nf (S fuel) (Con k))
        (liftable_con_tc henc) hrep (liftable_con_tc henc) hrep rfl

theorem nfT_substT_con_first_replay {fuel j sAst u : AST} {x : String}
    (henc : encTyCore? (.con x) = some u) (hfuel : IsNormal pTC fuel) :
    FirstReplayNF (.con x) u (nfT (S fuel) (substT j sAst u)) := by
  unfold encTyCore? at henc
  cases hx : encName? x with
  | none => simp [hx] at henc
  | some k =>
      simp [hx] at henc
      subst u
      have henc' : encTyCore? (.con x) = some (Con k) := by
        unfold encTyCore?
        simp [hx]
      have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (Con k))) =
          nfT (S fuel) (Con k) := by
        simp only [eval,
          hcong_nfT_s_substT_arg_tc fuel j sAst (Con k) (Con k) hfuel rfl]
      exact first_replay_nf_prepend hstep
        (NFActiveShape.nf (S fuel) (substT j sAst (Con k)))
        (nfT_con_first_replay (fuel := fuel) henc')

theorem nfT_substT_con_payload_first_replay (fuelNat j : Nat)
    {sAst : AST} {sTerm : LF.Term} {x : String} {u : AST}
    (henc : encTyCore? (.con x) = some u) :
    ∃ v,
      FirstReplayNF (LFTyping.nf LFTyping.corpusSig fuelNat
        (LFTyping.subst j sTerm (.con x))) v
        (nfT (peano fuelNat) (substT (peano j) sAst u)) := by
  cases fuelNat with
  | zero =>
      refine ⟨u, ?_⟩
      have hpayload : ∃ M, eval pTC M (substT (peano j) sAst u) = u := by
        unfold encTyCore? at henc
        cases hx : encName? x with
        | none => simp [hx] at henc
        | some k =>
            simp [hx] at henc
            subst u
            exact ⟨1, rfl⟩
      simpa [peano, LFTyping.nf, LFTyping.subst] using
        (nfT_z_first_replay henc
          (stackReplayablePayload_substT_con_tc (j := peano j) (sAst := sAst) henc).replay.1
          (stackReplayablePayload_substT_con_tc (j := peano j) (sAst := sAst) henc)
          (liftable_con_tc henc) (stackReplayablePayload_con_tc henc) hpayload)
  | succ fuelPred =>
      refine ⟨u, ?_⟩
      simpa [peano, LFTyping.nf, LFTyping.subst, lookupBody_corpusSig_none] using
        nfT_substT_con_first_replay (fuel := peano fuelPred) (j := peano j)
          (sAst := sAst) henc (isnormal_peano_tc fuelPred)

theorem nfPi2_nfT_first_liftable
    {ATerm BTerm : LF.Term} {Aval Bval fuel B Apre : AST}
    (hAenc : encTyCore? ATerm = some Aval)
    (hAeval : ∃ M, eval pTC M Apre = Aval)
    (hB : FirstLiftableNF BTerm Bval (nfT fuel B)) :
    FirstLiftableNF (.pi ATerm BTerm) (Pi Aval Bval) (nfPi2 Apre (nfT fuel B)) := by
  have hAnorm : IsNormal pTC Aval := isnormal_encTyCore?_tc ATerm Aval hAenc
  obtain ⟨NA, hNA⟩ := hAeval
  obtain ⟨MA, hMA, hMAguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun A => nfPi2 A (nfT fuel B))
      (fun A => NFActiveShape.pi2 A (nfT fuel B))
      (hcong_nfPi2_arg_nfT_tc fuel B) NA hNA hAnorm
  cases hB with
  | @intro Bpre NB MB hBenc hBmatch hBguard hBLift hBpayload =>
      have hBnorm : IsNormal pTC Bval := isnormal_encTyCore?_tc BTerm Bval hBenc
      obtain ⟨MBctx, hMBctx, hMBguard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfPi2 Aval s)
          (fun s _ => NFActiveShape.pi2 Aval s)
          (hcong_nfPi2_active_tc Aval hAnorm) NB hBmatch hBguard
      obtain ⟨MPayload, hMPayload⟩ :=
        cong_eval_tc (fun s => Pi Aval s) (hcong_Pi2_tc Aval hAnorm) MB hBpayload hBnorm
      refine FirstLiftableNF.intro (payload := Pi Aval Bpre) (N := MA + (MBctx + 1))
        (M := MPayload) ?_ ?_ ?_ ?_ hMPayload
      · simp [encTyCore?, hAenc, hBenc]
      · have hafterB : eval pTC (MA + MBctx) (nfPi2 Apre (nfT fuel B)) =
            nfPi2 Aval (someT Bpre) := by
          exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
        have hroot : eval pTC 1 (nfPi2 Aval (someT Bpre)) = someT (Pi Aval Bpre) :=
          nfPi2_ok_tc Aval Bpre
        have htotal := eval_trans_tc (MA + MBctx) 1 _ _ _ hafterB hroot
        simpa [Nat.add_assoc] using htotal
      · intro k hk
        by_cases hkA : k < MA
        · exact hMAguard k hkA
        · have hgeA : MA ≤ k := Nat.le_of_not_gt hkA
          by_cases hkB : k < MA + MBctx
          · let j := k - MA
            have hjlt : j < MBctx := by
              exact Nat.sub_lt_left_of_lt_add hgeA hkB
            have hkdecomp : k = MA + j := by
              exact (Nat.add_sub_of_le hgeA).symm
            subst j
            rw [hkdecomp]
            have htotal : eval pTC (MA + (k - MA)) (nfPi2 Apre (nfT fuel B)) =
                eval pTC (k - MA) (nfPi2 Aval (nfT fuel B)) :=
              eval_trans_tc MA (k - MA) _ _ _ hMA rfl
            rw [htotal]
            exact hMBguard (k - MA) hjlt
          · have hkEq : k = MA + MBctx := by omega
            subst k
            have htotal : eval pTC (MA + MBctx) (nfPi2 Apre (nfT fuel B)) =
                nfPi2 Aval (someT Bpre) := by
              exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
            rw [htotal]
            exact NFActiveShape.pi2 Aval (someT Bpre)
      · exact liftable_pi_tc (liftable_encTyCore?_tc ATerm Aval hAenc) hBLift

theorem nfPi2_nfT_first_replay
    {ATerm BTerm : LF.Term} {Aval Bval fuel B Apre : AST}
    (hAenc : encTyCore? ATerm = some Aval)
    (hAeval : ∃ M, eval pTC M Apre = Aval)
    (hB : FirstReplayNF BTerm Bval (nfT fuel B))
    (hPayloadReplay : ∀ {Bpre : AST}, LiftablePayload Bpre BTerm ->
      (∃ M, eval pTC M Bpre = Bval) -> StackReplayablePayload Bpre BTerm ->
        StackReplayablePayload (Pi Aval Bpre) (.pi ATerm BTerm))
    (hFinalReplay : StackReplayablePayload (Pi Aval Bval) (.pi ATerm BTerm)) :
    FirstReplayNF (.pi ATerm BTerm) (Pi Aval Bval) (nfPi2 Apre (nfT fuel B)) := by
  have hAnorm : IsNormal pTC Aval := isnormal_encTyCore?_tc ATerm Aval hAenc
  obtain ⟨NA, hNA⟩ := hAeval
  obtain ⟨MA, hMA, hMAguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun A => nfPi2 A (nfT fuel B))
      (fun A => NFActiveShape.pi2 A (nfT fuel B))
      (hcong_nfPi2_arg_nfT_tc fuel B) NA hNA hAnorm
  cases hB with
  | @intro Bpre NB MB hBenc hBmatch hBguard hBLift hBReplay hBFinal hBFinalReplay hBpayload =>
      have hBnorm : IsNormal pTC Bval := isnormal_encTyCore?_tc BTerm Bval hBenc
      obtain ⟨MBctx, hMBctx, hMBguard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfPi2 Aval s)
          (fun s _ => NFActiveShape.pi2 Aval s)
          (hcong_nfPi2_active_tc Aval hAnorm) NB hBmatch hBguard
      obtain ⟨MPayload, hMPayload⟩ :=
        cong_eval_tc (fun s => Pi Aval s) (hcong_Pi2_tc Aval hAnorm) MB hBpayload hBnorm
      refine FirstReplayNF.intro (payload := Pi Aval Bpre) (N := MA + (MBctx + 1))
        (M := MPayload) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hMPayload
      · simp [encTyCore?, hAenc, hBenc]
      · have hafterB : eval pTC (MA + MBctx) (nfPi2 Apre (nfT fuel B)) =
            nfPi2 Aval (someT Bpre) := by
          exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
        have hroot : eval pTC 1 (nfPi2 Aval (someT Bpre)) = someT (Pi Aval Bpre) :=
          nfPi2_ok_tc Aval Bpre
        have htotal := eval_trans_tc (MA + MBctx) 1 _ _ _ hafterB hroot
        simpa [Nat.add_assoc] using htotal
      · intro k hk
        by_cases hkA : k < MA
        · exact hMAguard k hkA
        · have hgeA : MA ≤ k := Nat.le_of_not_gt hkA
          by_cases hkB : k < MA + MBctx
          · let j := k - MA
            have hjlt : j < MBctx := by
              exact Nat.sub_lt_left_of_lt_add hgeA hkB
            have hkdecomp : k = MA + j := by
              exact (Nat.add_sub_of_le hgeA).symm
            subst j
            rw [hkdecomp]
            have htotal : eval pTC (MA + (k - MA)) (nfPi2 Apre (nfT fuel B)) =
                eval pTC (k - MA) (nfPi2 Aval (nfT fuel B)) :=
              eval_trans_tc MA (k - MA) _ _ _ hMA rfl
            rw [htotal]
            exact hMBguard (k - MA) hjlt
          · have hkEq : k = MA + MBctx := by omega
            subst k
            have htotal : eval pTC (MA + MBctx) (nfPi2 Apre (nfT fuel B)) =
                nfPi2 Aval (someT Bpre) := by
              exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
            rw [htotal]
            exact NFActiveShape.pi2 Aval (someT Bpre)
      · exact liftable_pi_tc (liftable_encTyCore?_tc ATerm Aval hAenc) hBLift
      · exact hPayloadReplay hBLift ⟨MB, hBpayload⟩ hBReplay
      · exact liftable_pi_tc (liftable_encTyCore?_tc ATerm Aval hAenc) hBFinal
      · exact hFinalReplay

theorem nfPi1_nfT_first_liftable
    {ATerm BTerm : LF.Term} {Aval Bval fuel B Acall : AST}
    (hfuel : IsNormal pTC fuel) (hBraw : IsNormal pTC B)
    (hA : FirstLiftableNF ATerm Aval Acall)
    (hB : FirstLiftableNF BTerm Bval (nfT fuel B)) :
    FirstLiftableNF (.pi ATerm BTerm) (Pi Aval Bval) (nfPi1 fuel B Acall) := by
  cases hA with
  | @intro Apre NA MA hAenc hAmatch hAguard _ hApayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfPi1 fuel B s)
          (fun s _ => NFActiveShape.pi1 fuel B s)
          (hcong_nfPi1_active_tc fuel B hfuel hBraw) NA hAmatch hAguard
      have htail := nfPi2_nfT_first_liftable (ATerm := ATerm) (BTerm := BTerm)
        (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := B) (Apre := Apre)
        hAenc ⟨MA, hApayload⟩ hB
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard hTailLift hTailPayload =>
          refine FirstLiftableNF.intro (payload := payloadTail) (N := MActx + (1 + NTail))
            (M := MTail) hTailEnc ?_ ?_ hTailLift hTailPayload
          · have hroot : eval pTC 1 (nfPi1 fuel B (someT Apre)) = nfPi2 Apre (nfT fuel B) :=
              nfPi1_ok_tc fuel B Apre
            have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
            have htotal := eval_trans_tc (MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkA : k < MActx
            · exact hMActxGuard k hkA
            · by_cases hkRoot : k = MActx
              · subst k
                rw [hMActx]
                exact NFActiveShape.pi1 fuel B (someT Apre)
              · let j := k - (MActx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MActx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfPi1 fuel B (someT Apre)) =
                    nfPi2 Apre (nfT fuel B) :=
                  nfPi1_ok_tc fuel B Apre
                have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
                have htotal : eval pTC (MActx + 1 + (k - (MActx + 1))) (nfPi1 fuel B Acall) =
                    eval pTC (k - (MActx + 1)) (nfPi2 Apre (nfT fuel B)) :=
                  eval_trans_tc (MActx + 1) (k - (MActx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MActx + 1)) hjlt

theorem nfPi1_nfT_first_replay
    {ATerm BTerm : LF.Term} {Aval Bval fuel B Acall : AST}
    (hfuel : IsNormal pTC fuel) (hBraw : IsNormal pTC B)
    (hA : FirstReplayNF ATerm Aval Acall)
    (hB : FirstReplayNF BTerm Bval (nfT fuel B))
    (hPayloadReplay : ∀ {Bpre : AST}, LiftablePayload Bpre BTerm ->
      (∃ M, eval pTC M Bpre = Bval) -> StackReplayablePayload Bpre BTerm ->
        StackReplayablePayload (Pi Aval Bpre) (.pi ATerm BTerm))
    (hFinalReplay : StackReplayablePayload (Pi Aval Bval) (.pi ATerm BTerm)) :
    FirstReplayNF (.pi ATerm BTerm) (Pi Aval Bval) (nfPi1 fuel B Acall) := by
  cases hA with
  | @intro Apre NA MA hAenc hAmatch hAguard _ _ _ _ hApayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfPi1 fuel B s)
          (fun s _ => NFActiveShape.pi1 fuel B s)
          (hcong_nfPi1_active_tc fuel B hfuel hBraw) NA hAmatch hAguard
      have htail := nfPi2_nfT_first_replay (ATerm := ATerm) (BTerm := BTerm)
        (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := B) (Apre := Apre)
        hAenc ⟨MA, hApayload⟩ hB hPayloadReplay hFinalReplay
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard
          hTailLift hTailReplay hTailFinal hTailFinalReplay hTailPayload =>
          refine FirstReplayNF.intro (payload := payloadTail) (N := MActx + (1 + NTail))
            (M := MTail) hTailEnc ?_ ?_ hTailLift hTailReplay hTailFinal
            hTailFinalReplay hTailPayload
          · have hroot : eval pTC 1 (nfPi1 fuel B (someT Apre)) = nfPi2 Apre (nfT fuel B) :=
              nfPi1_ok_tc fuel B Apre
            have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
            have htotal := eval_trans_tc (MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkA : k < MActx
            · exact hMActxGuard k hkA
            · by_cases hkRoot : k = MActx
              · subst k
                rw [hMActx]
                exact NFActiveShape.pi1 fuel B (someT Apre)
              · let j := k - (MActx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MActx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfPi1 fuel B (someT Apre)) =
                    nfPi2 Apre (nfT fuel B) :=
                  nfPi1_ok_tc fuel B Apre
                have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
                have htotal : eval pTC (MActx + 1 + (k - (MActx + 1))) (nfPi1 fuel B Acall) =
                    eval pTC (k - (MActx + 1)) (nfPi2 Apre (nfT fuel B)) :=
                  eval_trans_tc (MActx + 1) (k - (MActx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MActx + 1)) hjlt

theorem nfLam2_nfT_first_liftable
    {ATerm bTerm : LF.Term} {Aval bval fuel b Apre : AST}
    (hAenc : encTyCore? ATerm = some Aval)
    (hAeval : ∃ M, eval pTC M Apre = Aval)
    (hb : FirstLiftableNF bTerm bval (nfT fuel b)) :
    FirstLiftableNF (.lam ATerm bTerm) (Lam Aval bval) (nfLam2 Apre (nfT fuel b)) := by
  have hAnorm : IsNormal pTC Aval := isnormal_encTyCore?_tc ATerm Aval hAenc
  obtain ⟨NA, hNA⟩ := hAeval
  obtain ⟨MA, hMA, hMAguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun A => nfLam2 A (nfT fuel b))
      (fun A => NFActiveShape.lam2 A (nfT fuel b))
      (hcong_nfLam2_arg_nfT_tc fuel b) NA hNA hAnorm
  cases hb with
  | @intro bpre NB MB hbenc hbmatch hbguard hbLift hbpayload =>
      have hbnorm : IsNormal pTC bval := isnormal_encTyCore?_tc bTerm bval hbenc
      obtain ⟨MBctx, hMBctx, hMBguard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfLam2 Aval s)
          (fun s _ => NFActiveShape.lam2 Aval s)
          (hcong_nfLam2_active_tc Aval hAnorm) NB hbmatch hbguard
      obtain ⟨MPayload, hMPayload⟩ :=
        cong_eval_tc (fun s => Lam Aval s) (hcong_Lam2_tc Aval hAnorm) MB hbpayload hbnorm
      refine FirstLiftableNF.intro (payload := Lam Aval bpre) (N := MA + (MBctx + 1))
        (M := MPayload) ?_ ?_ ?_ ?_ hMPayload
      · simp [encTyCore?, hAenc, hbenc]
      · have hafterB : eval pTC (MA + MBctx) (nfLam2 Apre (nfT fuel b)) =
            nfLam2 Aval (someT bpre) := by
          exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
        have hroot : eval pTC 1 (nfLam2 Aval (someT bpre)) = someT (Lam Aval bpre) :=
          nfLam2_ok_tc Aval bpre
        have htotal := eval_trans_tc (MA + MBctx) 1 _ _ _ hafterB hroot
        simpa [Nat.add_assoc] using htotal
      · intro k hk
        by_cases hkA : k < MA
        · exact hMAguard k hkA
        · have hgeA : MA ≤ k := Nat.le_of_not_gt hkA
          by_cases hkB : k < MA + MBctx
          · let j := k - MA
            have hjlt : j < MBctx := by
              exact Nat.sub_lt_left_of_lt_add hgeA hkB
            have hkdecomp : k = MA + j := by
              exact (Nat.add_sub_of_le hgeA).symm
            subst j
            rw [hkdecomp]
            have htotal : eval pTC (MA + (k - MA)) (nfLam2 Apre (nfT fuel b)) =
                eval pTC (k - MA) (nfLam2 Aval (nfT fuel b)) :=
              eval_trans_tc MA (k - MA) _ _ _ hMA rfl
            rw [htotal]
            exact hMBguard (k - MA) hjlt
          · have hkEq : k = MA + MBctx := by omega
            subst k
            have htotal : eval pTC (MA + MBctx) (nfLam2 Apre (nfT fuel b)) =
                nfLam2 Aval (someT bpre) := by
              exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
            rw [htotal]
            exact NFActiveShape.lam2 Aval (someT bpre)
      · exact liftable_lam_tc (liftable_encTyCore?_tc ATerm Aval hAenc) hbLift

theorem nfLam2_nfT_first_replay
    {ATerm bTerm : LF.Term} {Aval bval fuel b Apre : AST}
    (hAenc : encTyCore? ATerm = some Aval)
    (hAeval : ∃ M, eval pTC M Apre = Aval)
    (hb : FirstReplayNF bTerm bval (nfT fuel b))
    (hPayloadReplay : ∀ {bpre : AST}, LiftablePayload bpre bTerm ->
      (∃ M, eval pTC M bpre = bval) -> StackReplayablePayload bpre bTerm ->
        StackReplayablePayload (Lam Aval bpre) (.lam ATerm bTerm))
    (hFinalReplay : StackReplayablePayload (Lam Aval bval) (.lam ATerm bTerm)) :
    FirstReplayNF (.lam ATerm bTerm) (Lam Aval bval) (nfLam2 Apre (nfT fuel b)) := by
  have hAnorm : IsNormal pTC Aval := isnormal_encTyCore?_tc ATerm Aval hAenc
  obtain ⟨NA, hNA⟩ := hAeval
  obtain ⟨MA, hMA, hMAguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun A => nfLam2 A (nfT fuel b))
      (fun A => NFActiveShape.lam2 A (nfT fuel b))
      (hcong_nfLam2_arg_nfT_tc fuel b) NA hNA hAnorm
  cases hb with
  | @intro bpre NB MB hbenc hbmatch hbguard hbLift hbReplay hbFinal hbFinalReplay hbpayload =>
      have hbnorm : IsNormal pTC bval := isnormal_encTyCore?_tc bTerm bval hbenc
      obtain ⟨MBctx, hMBctx, hMBguard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfLam2 Aval s)
          (fun s _ => NFActiveShape.lam2 Aval s)
          (hcong_nfLam2_active_tc Aval hAnorm) NB hbmatch hbguard
      obtain ⟨MPayload, hMPayload⟩ :=
        cong_eval_tc (fun s => Lam Aval s) (hcong_Lam2_tc Aval hAnorm) MB hbpayload hbnorm
      refine FirstReplayNF.intro (payload := Lam Aval bpre) (N := MA + (MBctx + 1))
        (M := MPayload) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hMPayload
      · simp [encTyCore?, hAenc, hbenc]
      · have hafterB : eval pTC (MA + MBctx) (nfLam2 Apre (nfT fuel b)) =
            nfLam2 Aval (someT bpre) := by
          exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
        have hroot : eval pTC 1 (nfLam2 Aval (someT bpre)) = someT (Lam Aval bpre) :=
          nfLam2_ok_tc Aval bpre
        have htotal := eval_trans_tc (MA + MBctx) 1 _ _ _ hafterB hroot
        simpa [Nat.add_assoc] using htotal
      · intro k hk
        by_cases hkA : k < MA
        · exact hMAguard k hkA
        · have hgeA : MA ≤ k := Nat.le_of_not_gt hkA
          by_cases hkB : k < MA + MBctx
          · let j := k - MA
            have hjlt : j < MBctx := by
              exact Nat.sub_lt_left_of_lt_add hgeA hkB
            have hkdecomp : k = MA + j := by
              exact (Nat.add_sub_of_le hgeA).symm
            subst j
            rw [hkdecomp]
            have htotal : eval pTC (MA + (k - MA)) (nfLam2 Apre (nfT fuel b)) =
                eval pTC (k - MA) (nfLam2 Aval (nfT fuel b)) :=
              eval_trans_tc MA (k - MA) _ _ _ hMA rfl
            rw [htotal]
            exact hMBguard (k - MA) hjlt
          · have hkEq : k = MA + MBctx := by omega
            subst k
            have htotal : eval pTC (MA + MBctx) (nfLam2 Apre (nfT fuel b)) =
                nfLam2 Aval (someT bpre) := by
              exact eval_trans_tc MA MBctx _ _ _ hMA hMBctx
            rw [htotal]
            exact NFActiveShape.lam2 Aval (someT bpre)
      · exact liftable_lam_tc (liftable_encTyCore?_tc ATerm Aval hAenc) hbLift
      · exact hPayloadReplay hbLift ⟨MB, hbpayload⟩ hbReplay
      · exact liftable_lam_tc (liftable_encTyCore?_tc ATerm Aval hAenc) hbFinal
      · exact hFinalReplay

theorem nfLam1_nfT_first_liftable
    {ATerm bTerm : LF.Term} {Aval bval fuel b Acall : AST}
    (hfuel : IsNormal pTC fuel) (hbraw : IsNormal pTC b)
    (hA : FirstLiftableNF ATerm Aval Acall)
    (hb : FirstLiftableNF bTerm bval (nfT fuel b)) :
    FirstLiftableNF (.lam ATerm bTerm) (Lam Aval bval) (nfLam1 fuel b Acall) := by
  cases hA with
  | @intro Apre NA MA hAenc hAmatch hAguard _ hApayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfLam1 fuel b s)
          (fun s _ => NFActiveShape.lam1 fuel b s)
          (hcong_nfLam1_active_tc fuel b hfuel hbraw) NA hAmatch hAguard
      have htail := nfLam2_nfT_first_liftable (ATerm := ATerm) (bTerm := bTerm)
        (Aval := Aval) (bval := bval) (fuel := fuel) (b := b) (Apre := Apre)
        hAenc ⟨MA, hApayload⟩ hb
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard hTailLift hTailPayload =>
          refine FirstLiftableNF.intro (payload := payloadTail) (N := MActx + (1 + NTail))
            (M := MTail) hTailEnc ?_ ?_ hTailLift hTailPayload
          · have hroot : eval pTC 1 (nfLam1 fuel b (someT Apre)) = nfLam2 Apre (nfT fuel b) :=
              nfLam1_ok_tc fuel b Apre
            have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
            have htotal := eval_trans_tc (MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkA : k < MActx
            · exact hMActxGuard k hkA
            · by_cases hkRoot : k = MActx
              · subst k
                rw [hMActx]
                exact NFActiveShape.lam1 fuel b (someT Apre)
              · let j := k - (MActx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MActx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfLam1 fuel b (someT Apre)) =
                    nfLam2 Apre (nfT fuel b) :=
                  nfLam1_ok_tc fuel b Apre
                have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
                have htotal : eval pTC (MActx + 1 + (k - (MActx + 1))) (nfLam1 fuel b Acall) =
                    eval pTC (k - (MActx + 1)) (nfLam2 Apre (nfT fuel b)) :=
                  eval_trans_tc (MActx + 1) (k - (MActx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MActx + 1)) hjlt

theorem nfLam1_nfT_first_replay
    {ATerm bTerm : LF.Term} {Aval bval fuel b Acall : AST}
    (hfuel : IsNormal pTC fuel) (hbraw : IsNormal pTC b)
    (hA : FirstReplayNF ATerm Aval Acall)
    (hb : FirstReplayNF bTerm bval (nfT fuel b))
    (hPayloadReplay : ∀ {bpre : AST}, LiftablePayload bpre bTerm ->
      (∃ M, eval pTC M bpre = bval) -> StackReplayablePayload bpre bTerm ->
        StackReplayablePayload (Lam Aval bpre) (.lam ATerm bTerm))
    (hFinalReplay : StackReplayablePayload (Lam Aval bval) (.lam ATerm bTerm)) :
    FirstReplayNF (.lam ATerm bTerm) (Lam Aval bval) (nfLam1 fuel b Acall) := by
  cases hA with
  | @intro Apre NA MA hAenc hAmatch hAguard _ _ _ _ hApayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfLam1 fuel b s)
          (fun s _ => NFActiveShape.lam1 fuel b s)
          (hcong_nfLam1_active_tc fuel b hfuel hbraw) NA hAmatch hAguard
      have htail := nfLam2_nfT_first_replay (ATerm := ATerm) (bTerm := bTerm)
        (Aval := Aval) (bval := bval) (fuel := fuel) (b := b) (Apre := Apre)
        hAenc ⟨MA, hApayload⟩ hb hPayloadReplay hFinalReplay
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard
          hTailLift hTailReplay hTailFinal hTailFinalReplay hTailPayload =>
          refine FirstReplayNF.intro (payload := payloadTail) (N := MActx + (1 + NTail))
            (M := MTail) hTailEnc ?_ ?_ hTailLift hTailReplay hTailFinal
            hTailFinalReplay hTailPayload
          · have hroot : eval pTC 1 (nfLam1 fuel b (someT Apre)) = nfLam2 Apre (nfT fuel b) :=
              nfLam1_ok_tc fuel b Apre
            have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
            have htotal := eval_trans_tc (MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkA : k < MActx
            · exact hMActxGuard k hkA
            · by_cases hkRoot : k = MActx
              · subst k
                rw [hMActx]
                exact NFActiveShape.lam1 fuel b (someT Apre)
              · let j := k - (MActx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MActx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfLam1 fuel b (someT Apre)) =
                    nfLam2 Apre (nfT fuel b) :=
                  nfLam1_ok_tc fuel b Apre
                have hafterRoot := eval_trans_tc MActx 1 _ _ _ hMActx hroot
                have htotal : eval pTC (MActx + 1 + (k - (MActx + 1))) (nfLam1 fuel b Acall) =
                    eval pTC (k - (MActx + 1)) (nfLam2 Apre (nfT fuel b)) :=
                  eval_trans_tc (MActx + 1) (k - (MActx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MActx + 1)) hjlt

theorem nfT_pi_first_liftable
    {ATerm BTerm : LF.Term} {Aval Bval fuel A B : AST}
    (hfuel : IsNormal pTC fuel) (hBraw : IsNormal pTC B)
    (hA : FirstLiftableNF ATerm Aval (nfT fuel A))
    (hB : FirstLiftableNF BTerm Bval (nfT fuel B)) :
    FirstLiftableNF (.pi ATerm BTerm) (Pi Aval Bval) (nfT (S fuel) (Pi A B)) := by
  exact first_liftable_nf_prepend (nfT_pi_tc fuel A B) (NFActiveShape.nf (S fuel) (Pi A B))
    (nfPi1_nfT_first_liftable (ATerm := ATerm) (BTerm := BTerm)
      (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := B) (Acall := nfT fuel A)
      hfuel hBraw hA hB)

theorem nfT_lam_first_liftable
    {ATerm bTerm : LF.Term} {Aval bval fuel A b : AST}
    (hfuel : IsNormal pTC fuel) (hbraw : IsNormal pTC b)
    (hA : FirstLiftableNF ATerm Aval (nfT fuel A))
    (hb : FirstLiftableNF bTerm bval (nfT fuel b)) :
    FirstLiftableNF (.lam ATerm bTerm) (Lam Aval bval) (nfT (S fuel) (Lam A b)) := by
  exact first_liftable_nf_prepend (nfT_lam_tc fuel A b) (NFActiveShape.nf (S fuel) (Lam A b))
    (nfLam1_nfT_first_liftable (ATerm := ATerm) (bTerm := bTerm)
      (Aval := Aval) (bval := bval) (fuel := fuel) (b := b) (Acall := nfT fuel A)
      hfuel hbraw hA hb)

theorem nfT_pi_first_strong
    {ATerm BTerm : LF.Term} {Aval Bval fuel A B : AST}
    (hfuel : IsNormal pTC fuel) (hBraw : IsNormal pTC B)
    (hA : FirstStrongNF ATerm Aval (nfT fuel A))
    (hB : FirstStrongNF BTerm Bval (nfT fuel B)) :
    FirstStrongNF (.pi ATerm BTerm) (Pi Aval Bval) (nfT (S fuel) (Pi A B)) := by
  exact FirstLiftableNF.toStrong
    (nfT_pi_first_liftable (ATerm := ATerm) (BTerm := BTerm)
      (Aval := Aval) (Bval := Bval) (fuel := fuel) (A := A) (B := B)
      hfuel hBraw (FirstStrongNF.toFirstLiftable hA) (FirstStrongNF.toFirstLiftable hB))

theorem nfT_lam_first_strong
    {ATerm bTerm : LF.Term} {Aval bval fuel A b : AST}
    (hfuel : IsNormal pTC fuel) (hbraw : IsNormal pTC b)
    (hA : FirstStrongNF ATerm Aval (nfT fuel A))
    (hb : FirstStrongNF bTerm bval (nfT fuel b)) :
    FirstStrongNF (.lam ATerm bTerm) (Lam Aval bval) (nfT (S fuel) (Lam A b)) := by
  exact FirstLiftableNF.toStrong
    (nfT_lam_first_liftable (ATerm := ATerm) (bTerm := bTerm)
      (Aval := Aval) (bval := bval) (fuel := fuel) (A := A) (b := b)
      hfuel hbraw (FirstStrongNF.toFirstLiftable hA) (FirstStrongNF.toFirstLiftable hb))

theorem nfT_pi_first_replay
    {ATerm BTerm : LF.Term} {Aval Bval fuel A B : AST}
    (hfuel : IsNormal pTC fuel) (hBraw : IsNormal pTC B)
    (hA : FirstReplayNF ATerm Aval (nfT fuel A))
    (hB : FirstReplayNF BTerm Bval (nfT fuel B))
    (hPayloadReplay : ∀ {Bpre : AST}, LiftablePayload Bpre BTerm ->
      (∃ M, eval pTC M Bpre = Bval) -> StackReplayablePayload Bpre BTerm ->
        StackReplayablePayload (Pi Aval Bpre) (.pi ATerm BTerm))
    (hFinalReplay : StackReplayablePayload (Pi Aval Bval) (.pi ATerm BTerm)) :
    FirstReplayNF (.pi ATerm BTerm) (Pi Aval Bval) (nfT (S fuel) (Pi A B)) := by
  exact first_replay_nf_prepend (nfT_pi_tc fuel A B) (NFActiveShape.nf (S fuel) (Pi A B))
    (nfPi1_nfT_first_replay (ATerm := ATerm) (BTerm := BTerm)
      (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := B) (Acall := nfT fuel A)
      hfuel hBraw hA hB hPayloadReplay hFinalReplay)

theorem nfT_lam_first_replay
    {ATerm bTerm : LF.Term} {Aval bval fuel A b : AST}
    (hfuel : IsNormal pTC fuel) (hbraw : IsNormal pTC b)
    (hA : FirstReplayNF ATerm Aval (nfT fuel A))
    (hb : FirstReplayNF bTerm bval (nfT fuel b))
    (hPayloadReplay : ∀ {bpre : AST}, LiftablePayload bpre bTerm ->
      (∃ M, eval pTC M bpre = bval) -> StackReplayablePayload bpre bTerm ->
        StackReplayablePayload (Lam Aval bpre) (.lam ATerm bTerm))
    (hFinalReplay : StackReplayablePayload (Lam Aval bval) (.lam ATerm bTerm)) :
    FirstReplayNF (.lam ATerm bTerm) (Lam Aval bval) (nfT (S fuel) (Lam A b)) := by
  exact first_replay_nf_prepend (nfT_lam_tc fuel A b) (NFActiveShape.nf (S fuel) (Lam A b))
    (nfLam1_nfT_first_replay (ATerm := ATerm) (bTerm := bTerm)
      (Aval := Aval) (bval := bval) (fuel := fuel) (b := b) (Acall := nfT fuel A)
      hfuel hbraw hA hb hPayloadReplay hFinalReplay)

theorem nfAppT_wrap_first_liftable {fuel fVal aPre : AST}
    {fTerm aTerm : LF.Term} {aVal : AST}
    (hroot : eval pTC 1 (nfAppT fuel fVal aPre) = someT (App fVal aPre))
    (hfenc : encTyCore? fTerm = some fVal) (hflift : LiftablePayload fVal fTerm)
    (haenc : encTyCore? aTerm = some aVal) (halift : LiftablePayload aPre aTerm)
    (haeval : ∃ M, eval pTC M aPre = aVal) :
    FirstLiftableNF (.app fTerm aTerm) (App fVal aVal) (nfAppT fuel fVal aPre) := by
  have hfnorm : IsNormal pTC fVal := isnormal_encTyCore?_tc fTerm fVal hfenc
  obtain ⟨MA, hMA⟩ := haeval
  have hanorm : IsNormal pTC aVal := isnormal_encTyCore?_tc aTerm aVal haenc
  obtain ⟨MPayload, hMPayload⟩ :=
    cong_eval_tc (fun s => App fVal s) (hcong_App2_tc fVal hfnorm) MA hMA hanorm
  refine FirstLiftableNF.intro (payload := App fVal aPre) (N := 1) (M := MPayload)
    ?_ hroot ?_ ?_ hMPayload
  · simp [encTyCore?, hfenc, haenc]
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    exact NFActiveShape.appT fuel fVal aPre
  · exact liftable_app_tc hflift halift

theorem nfAppT_wrap_first_replay {fuel fVal aPre : AST}
    {fTerm aTerm : LF.Term} {aVal : AST}
    (hroot : eval pTC 1 (nfAppT fuel fVal aPre) = someT (App fVal aPre))
    (hfenc : encTyCore? fTerm = some fVal) (hflift : LiftablePayload fVal fTerm)
    (haenc : encTyCore? aTerm = some aVal) (halift : LiftablePayload aPre aTerm)
    (haeval : ∃ M, eval pTC M aPre = aVal)
    (hPayloadReplay : StackReplayablePayload (App fVal aPre) (.app fTerm aTerm))
    (hFinalReplay : StackReplayablePayload (App fVal aVal) (.app fTerm aTerm)) :
    FirstReplayNF (.app fTerm aTerm) (App fVal aVal) (nfAppT fuel fVal aPre) := by
  have hfnorm : IsNormal pTC fVal := isnormal_encTyCore?_tc fTerm fVal hfenc
  obtain ⟨MA, hMA⟩ := haeval
  have hanorm : IsNormal pTC aVal := isnormal_encTyCore?_tc aTerm aVal haenc
  obtain ⟨MPayload, hMPayload⟩ :=
    cong_eval_tc (fun s => App fVal s) (hcong_App2_tc fVal hfnorm) MA hMA hanorm
  refine FirstReplayNF.intro (payload := App fVal aPre) (N := 1) (M := MPayload)
    ?_ hroot ?_ ?_ hPayloadReplay ?_ hFinalReplay hMPayload
  · simp [encTyCore?, hfenc, haenc]
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    exact NFActiveShape.appT fuel fVal aPre
  · exact liftable_app_tc hflift halift
  · exact liftable_app_tc hflift (liftable_encTyCore?_tc aTerm aVal haenc)

theorem nfAppT_z_first_liftable {fVal aPre : AST}
    {fTerm aTerm : LF.Term} {aVal : AST}
    (hfenc : encTyCore? fTerm = some fVal) (hflift : LiftablePayload fVal fTerm)
    (haenc : encTyCore? aTerm = some aVal) (halift : LiftablePayload aPre aTerm)
    (haeval : ∃ M, eval pTC M aPre = aVal) :
    FirstLiftableNF (.app fTerm aTerm) (App fVal aVal) (nfAppT Z fVal aPre) := by
  exact nfAppT_wrap_first_liftable (nfAppT_z_tc fVal aPre) hfenc hflift haenc halift haeval

theorem nfAppT_beta_prepend_first_liftable {t : LF.Term}
    {u fuel A body aPre : AST}
    (hnext : FirstLiftableNF t u (nfT fuel (substT Z aPre body))) :
    FirstLiftableNF t u (nfAppT (S fuel) (Lam A body) aPre) := by
  exact first_liftable_nf_prepend (nfAppT_beta_tc fuel A body aPre)
    (NFActiveShape.appT (S fuel) (Lam A body) aPre) hnext

theorem nfAppT_beta_prepend_first_replay {t : LF.Term}
    {u fuel A body aPre : AST}
    (hnext : FirstReplayNF t u (nfT fuel (substT Z aPre body))) :
    FirstReplayNF t u (nfAppT (S fuel) (Lam A body) aPre) := by
  exact first_replay_nf_prepend (nfAppT_beta_tc fuel A body aPre)
    (NFActiveShape.appT (S fuel) (Lam A body) aPre) hnext

theorem nfApp2_nfT_first_liftable
    {aTerm resTerm : LF.Term} {aVal resVal fuel fPre fVal aAst : AST}
    (hfuel : IsNormal pTC fuel) (hfnorm : IsNormal pTC fVal)
    (hfpreEval : ∃ M, eval pTC M fPre = fVal)
    (hA : FirstLiftableNF aTerm aVal (nfT fuel aAst))
    (hTail : ∀ {aPre : AST}, LiftablePayload aPre aTerm ->
      (∃ M, eval pTC M aPre = aVal) ->
        FirstLiftableNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstLiftableNF resTerm resVal (nfApp2 fuel fPre (nfT fuel aAst)) := by
  obtain ⟨MF, hMF⟩ := hfpreEval
  obtain ⟨MFctx, hMFctx, hMFguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun f => nfApp2 fuel f (nfT fuel aAst))
      (fun f => NFActiveShape.app2 fuel f (nfT fuel aAst))
      (hcong_nfApp2_fun_nfT_tc fuel aAst hfuel) MF hMF hfnorm
  cases hA with
  | @intro aPre NA MA haenc hAmatch hAguard haLift haPayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfApp2 fuel fVal s)
          (fun s _ => NFActiveShape.app2 fuel fVal s)
          (hcong_nfApp2_active_tc fuel fVal hfuel hfnorm) NA hAmatch hAguard
      have htail := hTail haLift ⟨MA, haPayload⟩
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard hTailLift hTailPayload =>
          refine FirstLiftableNF.intro (payload := payloadTail)
            (N := MFctx + (MActx + (1 + NTail))) (M := MTail)
            hTailEnc ?_ ?_ hTailLift hTailPayload
          · have hafterA : eval pTC (MFctx + MActx) (nfApp2 fuel fPre (nfT fuel aAst)) =
                nfApp2 fuel fVal (someT aPre) := by
              exact eval_trans_tc MFctx MActx _ _ _ hMFctx hMActx
            have hroot : eval pTC 1 (nfApp2 fuel fVal (someT aPre)) = nfAppT fuel fVal aPre :=
              nfApp2_ok_tc fuel fVal aPre
            have hafterRoot := eval_trans_tc (MFctx + MActx) 1 _ _ _ hafterA hroot
            have htotal := eval_trans_tc (MFctx + MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkF : k < MFctx
            · exact hMFguard k hkF
            · have hgeF : MFctx ≤ k := Nat.le_of_not_gt hkF
              by_cases hkA : k < MFctx + MActx
              · let j := k - MFctx
                have hjlt : j < MActx := by
                  exact Nat.sub_lt_left_of_lt_add hgeF hkA
                have hkdecomp : k = MFctx + j := by
                  exact (Nat.add_sub_of_le hgeF).symm
                subst j
                rw [hkdecomp]
                have htotal : eval pTC (MFctx + (k - MFctx)) (nfApp2 fuel fPre (nfT fuel aAst)) =
                    eval pTC (k - MFctx) (nfApp2 fuel fVal (nfT fuel aAst)) :=
                  eval_trans_tc MFctx (k - MFctx) _ _ _ hMFctx rfl
                rw [htotal]
                exact hMActxGuard (k - MFctx) hjlt
              · by_cases hkRoot : k = MFctx + MActx
                · subst k
                  have hafterA : eval pTC (MFctx + MActx) (nfApp2 fuel fPre (nfT fuel aAst)) =
                      nfApp2 fuel fVal (someT aPre) := by
                    exact eval_trans_tc MFctx MActx _ _ _ hMFctx hMActx
                  rw [hafterA]
                  exact NFActiveShape.app2 fuel fVal (someT aPre)
                · let j := k - (MFctx + MActx + 1)
                  have hjlt : j < NTail := by omega
                  have hkdecomp : k = MFctx + MActx + 1 + j := by omega
                  subst j
                  rw [hkdecomp]
                  have hafterA : eval pTC (MFctx + MActx) (nfApp2 fuel fPre (nfT fuel aAst)) =
                      nfApp2 fuel fVal (someT aPre) := by
                    exact eval_trans_tc MFctx MActx _ _ _ hMFctx hMActx
                  have hroot : eval pTC 1 (nfApp2 fuel fVal (someT aPre)) = nfAppT fuel fVal aPre :=
                    nfApp2_ok_tc fuel fVal aPre
                  have hafterRoot := eval_trans_tc (MFctx + MActx) 1 _ _ _ hafterA hroot
                  have htotal : eval pTC (MFctx + MActx + 1 + (k - (MFctx + MActx + 1)))
                        (nfApp2 fuel fPre (nfT fuel aAst)) =
                      eval pTC (k - (MFctx + MActx + 1)) (nfAppT fuel fVal aPre) :=
                    eval_trans_tc (MFctx + MActx + 1) (k - (MFctx + MActx + 1))
                      _ _ _ hafterRoot rfl
                  rw [htotal]
                  exact hTailGuard (k - (MFctx + MActx + 1)) hjlt

theorem nfApp2_nfT_first_replay
    {aTerm resTerm : LF.Term} {aVal resVal fuel fPre fVal aAst : AST}
    (hfuel : IsNormal pTC fuel) (hfnorm : IsNormal pTC fVal)
    (hfpreEval : ∃ M, eval pTC M fPre = fVal)
    (hA : FirstReplayNF aTerm aVal (nfT fuel aAst))
    (hTail : ∀ {aPre : AST}, LiftablePayload aPre aTerm ->
      (∃ M, eval pTC M aPre = aVal) -> StackReplayablePayload aPre aTerm ->
        FirstReplayNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstReplayNF resTerm resVal (nfApp2 fuel fPre (nfT fuel aAst)) := by
  obtain ⟨MF, hMF⟩ := hfpreEval
  obtain ⟨MFctx, hMFctx, hMFguard⟩ :=
    cong_eval_nf_wrapper_with_guard (fun f => nfApp2 fuel f (nfT fuel aAst))
      (fun f => NFActiveShape.app2 fuel f (nfT fuel aAst))
      (hcong_nfApp2_fun_nfT_tc fuel aAst hfuel) MF hMF hfnorm
  cases hA with
  | @intro aPre NA MA haenc hAmatch hAguard haLift haReplay _ _ haPayload =>
      obtain ⟨MActx, hMActx, hMActxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfApp2 fuel fVal s)
          (fun s _ => NFActiveShape.app2 fuel fVal s)
          (hcong_nfApp2_active_tc fuel fVal hfuel hfnorm) NA hAmatch hAguard
      have htail := hTail haLift ⟨MA, haPayload⟩ haReplay
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard
          hTailLift hTailReplay hTailFinal hTailFinalReplay hTailPayload =>
          refine FirstReplayNF.intro (payload := payloadTail)
            (N := MFctx + (MActx + (1 + NTail))) (M := MTail)
            hTailEnc ?_ ?_ hTailLift hTailReplay hTailFinal hTailFinalReplay hTailPayload
          · have hafterA : eval pTC (MFctx + MActx) (nfApp2 fuel fPre (nfT fuel aAst)) =
                nfApp2 fuel fVal (someT aPre) := by
              exact eval_trans_tc MFctx MActx _ _ _ hMFctx hMActx
            have hroot : eval pTC 1 (nfApp2 fuel fVal (someT aPre)) = nfAppT fuel fVal aPre :=
              nfApp2_ok_tc fuel fVal aPre
            have hafterRoot := eval_trans_tc (MFctx + MActx) 1 _ _ _ hafterA hroot
            have htotal := eval_trans_tc (MFctx + MActx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkF : k < MFctx
            · exact hMFguard k hkF
            · have hgeF : MFctx ≤ k := Nat.le_of_not_gt hkF
              by_cases hkA : k < MFctx + MActx
              · let j := k - MFctx
                have hjlt : j < MActx := by
                  exact Nat.sub_lt_left_of_lt_add hgeF hkA
                have hkdecomp : k = MFctx + j := by
                  exact (Nat.add_sub_of_le hgeF).symm
                subst j
                rw [hkdecomp]
                have htotal : eval pTC (MFctx + (k - MFctx)) (nfApp2 fuel fPre (nfT fuel aAst)) =
                    eval pTC (k - MFctx) (nfApp2 fuel fVal (nfT fuel aAst)) :=
                  eval_trans_tc MFctx (k - MFctx) _ _ _ hMFctx rfl
                rw [htotal]
                exact hMActxGuard (k - MFctx) hjlt
              · by_cases hkRoot : k = MFctx + MActx
                · subst k
                  have hafterA : eval pTC (MFctx + MActx) (nfApp2 fuel fPre (nfT fuel aAst)) =
                      nfApp2 fuel fVal (someT aPre) := by
                    exact eval_trans_tc MFctx MActx _ _ _ hMFctx hMActx
                  rw [hafterA]
                  exact NFActiveShape.app2 fuel fVal (someT aPre)
                · let j := k - (MFctx + MActx + 1)
                  have hjlt : j < NTail := by omega
                  have hkdecomp : k = MFctx + MActx + 1 + j := by omega
                  subst j
                  rw [hkdecomp]
                  have hafterA : eval pTC (MFctx + MActx) (nfApp2 fuel fPre (nfT fuel aAst)) =
                      nfApp2 fuel fVal (someT aPre) := by
                    exact eval_trans_tc MFctx MActx _ _ _ hMFctx hMActx
                  have hroot : eval pTC 1 (nfApp2 fuel fVal (someT aPre)) = nfAppT fuel fVal aPre :=
                    nfApp2_ok_tc fuel fVal aPre
                  have hafterRoot := eval_trans_tc (MFctx + MActx) 1 _ _ _ hafterA hroot
                  have htotal : eval pTC (MFctx + MActx + 1 + (k - (MFctx + MActx + 1)))
                        (nfApp2 fuel fPre (nfT fuel aAst)) =
                      eval pTC (k - (MFctx + MActx + 1)) (nfAppT fuel fVal aPre) :=
                    eval_trans_tc (MFctx + MActx + 1) (k - (MFctx + MActx + 1))
                      _ _ _ hafterRoot rfl
                  rw [htotal]
                  exact hTailGuard (k - (MFctx + MActx + 1)) hjlt

theorem nfApp1_nfT_first_liftable
    {fTerm resTerm : LF.Term} {fVal resVal fuel aAst fCall : AST}
    (hfuel : IsNormal pTC fuel) (haRaw : IsNormal pTC aAst)
    (hF : FirstLiftableNF fTerm fVal fCall)
    (hTail : ∀ {fPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) ->
        FirstLiftableNF resTerm resVal (nfApp2 fuel fPre (nfT fuel aAst))) :
    FirstLiftableNF resTerm resVal (nfApp1 fuel aAst fCall) := by
  cases hF with
  | @intro fPre NF MF hfenc hFmatch hFguard hfLift hfPayload =>
      obtain ⟨MFctx, hMFctx, hMFctxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfApp1 fuel aAst s)
          (fun s _ => NFActiveShape.app1 fuel aAst s)
          (hcong_nfApp1_active_tc fuel aAst hfuel haRaw) NF hFmatch hFguard
      have htail := hTail hfLift ⟨MF, hfPayload⟩
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard hTailLift hTailPayload =>
          refine FirstLiftableNF.intro (payload := payloadTail)
            (N := MFctx + (1 + NTail)) (M := MTail) hTailEnc ?_ ?_ hTailLift hTailPayload
          · have hroot : eval pTC 1 (nfApp1 fuel aAst (someT fPre)) =
                nfApp2 fuel fPre (nfT fuel aAst) :=
              nfApp1_ok_tc fuel aAst fPre
            have hafterRoot := eval_trans_tc MFctx 1 _ _ _ hMFctx hroot
            have htotal := eval_trans_tc (MFctx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkF : k < MFctx
            · exact hMFctxGuard k hkF
            · by_cases hkRoot : k = MFctx
              · subst k
                rw [hMFctx]
                exact NFActiveShape.app1 fuel aAst (someT fPre)
              · let j := k - (MFctx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MFctx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfApp1 fuel aAst (someT fPre)) =
                    nfApp2 fuel fPre (nfT fuel aAst) :=
                  nfApp1_ok_tc fuel aAst fPre
                have hafterRoot := eval_trans_tc MFctx 1 _ _ _ hMFctx hroot
                have htotal : eval pTC (MFctx + 1 + (k - (MFctx + 1))) (nfApp1 fuel aAst fCall) =
                    eval pTC (k - (MFctx + 1)) (nfApp2 fuel fPre (nfT fuel aAst)) :=
                  eval_trans_tc (MFctx + 1) (k - (MFctx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MFctx + 1)) hjlt

theorem nfApp1_nfT_first_replay
    {fTerm resTerm : LF.Term} {fVal resVal fuel aAst fCall : AST}
    (hfuel : IsNormal pTC fuel) (haRaw : IsNormal pTC aAst)
    (hF : FirstReplayNF fTerm fVal fCall)
    (hTail : ∀ {fPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> StackReplayablePayload fPre fTerm ->
        FirstReplayNF resTerm resVal (nfApp2 fuel fPre (nfT fuel aAst))) :
    FirstReplayNF resTerm resVal (nfApp1 fuel aAst fCall) := by
  cases hF with
  | @intro fPre NF MF hfenc hFmatch hFguard hfLift hfReplay _ _ hfPayload =>
      obtain ⟨MFctx, hMFctx, hMFctxGuard⟩ :=
        cong_eval_nf_active_with_guard (fun s => nfApp1 fuel aAst s)
          (fun s _ => NFActiveShape.app1 fuel aAst s)
          (hcong_nfApp1_active_tc fuel aAst hfuel haRaw) NF hFmatch hFguard
      have htail := hTail hfLift ⟨MF, hfPayload⟩ hfReplay
      cases htail with
      | @intro payloadTail NTail MTail hTailEnc hTailMatch hTailGuard
          hTailLift hTailReplay hTailFinal hTailFinalReplay hTailPayload =>
          refine FirstReplayNF.intro (payload := payloadTail)
            (N := MFctx + (1 + NTail)) (M := MTail) hTailEnc ?_ ?_
            hTailLift hTailReplay hTailFinal hTailFinalReplay hTailPayload
          · have hroot : eval pTC 1 (nfApp1 fuel aAst (someT fPre)) =
                nfApp2 fuel fPre (nfT fuel aAst) :=
              nfApp1_ok_tc fuel aAst fPre
            have hafterRoot := eval_trans_tc MFctx 1 _ _ _ hMFctx hroot
            have htotal := eval_trans_tc (MFctx + 1) NTail _ _ _ hafterRoot hTailMatch
            simpa [Nat.add_assoc] using htotal
          · intro k hk
            by_cases hkF : k < MFctx
            · exact hMFctxGuard k hkF
            · by_cases hkRoot : k = MFctx
              · subst k
                rw [hMFctx]
                exact NFActiveShape.app1 fuel aAst (someT fPre)
              · let j := k - (MFctx + 1)
                have hjlt : j < NTail := by omega
                have hkdecomp : k = MFctx + 1 + j := by omega
                subst j
                rw [hkdecomp]
                have hroot : eval pTC 1 (nfApp1 fuel aAst (someT fPre)) =
                    nfApp2 fuel fPre (nfT fuel aAst) :=
                  nfApp1_ok_tc fuel aAst fPre
                have hafterRoot := eval_trans_tc MFctx 1 _ _ _ hMFctx hroot
                have htotal : eval pTC (MFctx + 1 + (k - (MFctx + 1))) (nfApp1 fuel aAst fCall) =
                    eval pTC (k - (MFctx + 1)) (nfApp2 fuel fPre (nfT fuel aAst)) :=
                  eval_trans_tc (MFctx + 1) (k - (MFctx + 1)) _ _ _ hafterRoot rfl
                rw [htotal]
                exact hTailGuard (k - (MFctx + 1)) hjlt

theorem nfT_app_first_liftable
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel fAst aAst : AST}
    (hfuel : IsNormal pTC fuel) (haRaw : IsNormal pTC aAst)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstLiftableNF fTerm fVal (nfT fuel fAst))
    (hA : FirstLiftableNF aTerm aVal (nfT fuel aAst))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> LiftablePayload aPre aTerm ->
        (∃ M, eval pTC M aPre = aVal) ->
          FirstLiftableNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstLiftableNF resTerm resVal (nfT (S fuel) (App fAst aAst)) := by
  exact first_liftable_nf_prepend (nfT_app_tc fuel fAst aAst)
    (NFActiveShape.nf (S fuel) (App fAst aAst))
    (nfApp1_nfT_first_liftable (fTerm := fTerm) (resTerm := resTerm)
      (fVal := fVal) (resVal := resVal) (fuel := fuel) (aAst := aAst)
      (fCall := nfT fuel fAst) hfuel haRaw hF
      (by
        intro fPre hfLift hfEval
        exact nfApp2_nfT_first_liftable (aTerm := aTerm) (resTerm := resTerm)
          (aVal := aVal) (resVal := resVal) (fuel := fuel) (fPre := fPre)
          (fVal := fVal) (aAst := aAst) hfuel hfnorm hfEval hA
          (by
            intro aPre haLift haEval
            exact hTail hfLift hfEval haLift haEval)))

theorem nfT_app_first_strong
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel fAst aAst : AST}
    (hfuel : IsNormal pTC fuel) (haRaw : IsNormal pTC aAst)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstStrongNF fTerm fVal (nfT fuel fAst))
    (hA : FirstStrongNF aTerm aVal (nfT fuel aAst))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> LiftablePayload aPre aTerm ->
        (∃ M, eval pTC M aPre = aVal) ->
          FirstStrongNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstStrongNF resTerm resVal (nfT (S fuel) (App fAst aAst)) := by
  exact FirstLiftableNF.toStrong
    (nfT_app_first_liftable (fTerm := fTerm) (aTerm := aTerm) (resTerm := resTerm)
      (fVal := fVal) (aVal := aVal) (resVal := resVal) (fuel := fuel)
      (fAst := fAst) (aAst := aAst) hfuel haRaw hfnorm
      (FirstStrongNF.toFirstLiftable hF) (FirstStrongNF.toFirstLiftable hA)
      (by
        intro fPre aPre hfLift hfEval haLift haEval
        exact FirstStrongNF.toFirstLiftable (hTail hfLift hfEval haLift haEval)))

theorem nfT_app_first_strong_replay
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel fAst aAst : AST}
    (hfuel : IsNormal pTC fuel) (haRaw : IsNormal pTC aAst)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstStrongNF fTerm fVal (nfT fuel fAst))
    (hA : FirstStrongNF aTerm aVal (nfT fuel aAst))
    (hAReplay : ∀ {aPre : AST}, LiftablePayload aPre aTerm ->
      (∃ M, eval pTC M aPre = aVal) -> StackReplayablePayload aPre aTerm)
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> LiftablePayload aPre aTerm ->
        (∃ M, eval pTC M aPre = aVal) -> StackReplayablePayload aPre aTerm ->
          FirstStrongNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstStrongNF resTerm resVal (nfT (S fuel) (App fAst aAst)) := by
  exact nfT_app_first_strong (fTerm := fTerm) (aTerm := aTerm) (resTerm := resTerm)
    (fVal := fVal) (aVal := aVal) (resVal := resVal) (fuel := fuel)
    (fAst := fAst) (aAst := aAst) hfuel haRaw hfnorm hF hA
    (by
      intro fPre aPre hfLift hfEval haLift haEval
      exact hTail hfLift hfEval haLift haEval (hAReplay haLift haEval))

theorem nfT_app_first_replay
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel fAst aAst : AST}
    (hfuel : IsNormal pTC fuel) (haRaw : IsNormal pTC aAst)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstReplayNF fTerm fVal (nfT fuel fAst))
    (hA : FirstReplayNF aTerm aVal (nfT fuel aAst))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> StackReplayablePayload fPre fTerm ->
        LiftablePayload aPre aTerm -> (∃ M, eval pTC M aPre = aVal) ->
          StackReplayablePayload aPre aTerm ->
            FirstReplayNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstReplayNF resTerm resVal (nfT (S fuel) (App fAst aAst)) := by
  exact first_replay_nf_prepend (nfT_app_tc fuel fAst aAst)
    (NFActiveShape.nf (S fuel) (App fAst aAst))
    (nfApp1_nfT_first_replay (fTerm := fTerm) (resTerm := resTerm)
      (fVal := fVal) (resVal := resVal) (fuel := fuel) (aAst := aAst)
      (fCall := nfT fuel fAst) hfuel haRaw hF
      (by
        intro fPre hfLift hfEval hfReplay
        exact nfApp2_nfT_first_replay (aTerm := aTerm) (resTerm := resTerm)
          (aVal := aVal) (resVal := resVal) (fuel := fuel) (fPre := fPre)
          (fVal := fVal) (aAst := aAst) hfuel hfnorm hfEval hA
          (by
            intro aPre haLift haEval haReplay
            exact hTail hfLift hfEval hfReplay haLift haEval haReplay)))

theorem nfT_pi_raw_second_first_strong
    {ATerm BTerm : LF.Term} {Aval Bval fuel Araw Braw Benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hBenc : encTyCore? BTerm = some Benc)
    (hBeval : ∃ M, eval pTC M Braw = Benc)
    (hA : FirstStrongNF ATerm Aval (nfT fuel Araw))
    (hB : FirstStrongNF BTerm Bval (nfT fuel Benc)) :
    FirstStrongNF (.pi ATerm BTerm) (Pi Aval Bval) (nfT (S fuel) (Pi Araw Braw)) := by
  have hBnorm : IsNormal pTC Benc := isnormal_encTyCore?_tc BTerm Benc hBenc
  obtain ⟨MB, hMB⟩ := hBeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun B => nfPi1 fuel B (nfT fuel Araw))
      (fun B => NFActiveShape.pi1 fuel B (nfT fuel Araw))
      (fun B B' hstep => hcong_nfPi1_raw_nfT_arg_tc fuel B Araw hfuel B' hstep)
      MB hMB hBnorm
  have hnext : FirstStrongNF (.pi ATerm BTerm) (Pi Aval Bval)
      (nfPi1 fuel Benc (nfT fuel Araw)) := by
    exact FirstLiftableNF.toStrong
      (nfPi1_nfT_first_liftable (ATerm := ATerm) (BTerm := BTerm)
        (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := Benc)
        (Acall := nfT fuel Araw) hfuel hBnorm
        (FirstStrongNF.toFirstLiftable hA) (FirstStrongNF.toFirstLiftable hB))
  have htail := first_strong_nf_prefix hMctx hMguard hnext
  exact first_strong_nf_prepend (nfT_pi_tc fuel Araw Braw)
    (NFActiveShape.nf (S fuel) (Pi Araw Braw)) htail

theorem nfT_pi_raw_second_first_strong_split
    {ATerm BRawTerm BNormTerm : LF.Term} {Aval Bval fuel Araw Braw Benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hBrawEnc : encTyCore? BRawTerm = some Benc)
    (hBeval : ∃ M, eval pTC M Braw = Benc)
    (hA : FirstStrongNF ATerm Aval (nfT fuel Araw))
    (hB : FirstStrongNF BNormTerm Bval (nfT fuel Benc)) :
    FirstStrongNF (.pi ATerm BNormTerm) (Pi Aval Bval) (nfT (S fuel) (Pi Araw Braw)) := by
  have hBrawNorm : IsNormal pTC Benc := isnormal_encTyCore?_tc BRawTerm Benc hBrawEnc
  obtain ⟨MB, hMB⟩ := hBeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun B => nfPi1 fuel B (nfT fuel Araw))
      (fun B => NFActiveShape.pi1 fuel B (nfT fuel Araw))
      (fun B B' hstep => hcong_nfPi1_raw_nfT_arg_tc fuel B Araw hfuel B' hstep)
      MB hMB hBrawNorm
  have hnext : FirstStrongNF (.pi ATerm BNormTerm) (Pi Aval Bval)
      (nfPi1 fuel Benc (nfT fuel Araw)) := by
    exact FirstLiftableNF.toStrong
      (nfPi1_nfT_first_liftable (ATerm := ATerm) (BTerm := BNormTerm)
        (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := Benc)
        (Acall := nfT fuel Araw) hfuel hBrawNorm
        (FirstStrongNF.toFirstLiftable hA) (FirstStrongNF.toFirstLiftable hB))
  have htail := first_strong_nf_prefix hMctx hMguard hnext
  exact first_strong_nf_prepend (nfT_pi_tc fuel Araw Braw)
    (NFActiveShape.nf (S fuel) (Pi Araw Braw)) htail

theorem replayablePayload_pi_payload_tc {Aval Bpre Bval : AST} {ATerm BTerm : LF.Term}
    (hA : ReplayablePayload Aval ATerm)
    (hBpre : LiftablePayload Bpre BTerm)
    (hBenc : encTyCore? BTerm = some Bval)
    (hBeval : ∃ M, eval pTC M Bpre = Bval)
    (hBfinal : ReplayablePayload Bval BTerm) :
    ReplayablePayload (Pi Aval Bpre) (.pi ATerm BTerm) := by
  constructor
  · exact liftable_pi_tc hA.1 hBpre
  · intro fuelNat
    cases fuelNat with
    | zero =>
        have hcall : LiftablePayload (Pi Aval Bpre) (.pi ATerm BTerm) :=
          liftable_pi_tc hA.1 hBpre
        rcases hcall.reduces with ⟨u, N, henc, hN⟩
        refine ⟨u, ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_z_first_strong henc hcall (liftable_encTyCore?_tc _ _ henc) ⟨N, hN⟩)
    | succ fuelPred =>
        obtain ⟨AvalNF, hANF⟩ := hA.2 fuelPred
        obtain ⟨BvalNF, hBNF⟩ := hBfinal.2 fuelPred
        refine ⟨Pi AvalNF BvalNF, ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_pi_raw_second_first_strong_split
            (ATerm := LFTyping.nf LFTyping.corpusSig fuelPred ATerm)
            (BRawTerm := BTerm)
            (BNormTerm := LFTyping.nf LFTyping.corpusSig fuelPred BTerm)
            (Aval := AvalNF) (Bval := BvalNF) (fuel := peano fuelPred)
            (Araw := Aval) (Braw := Bpre) (Benc := Bval)
            (isnormal_peano_tc fuelPred) hBenc hBeval hANF hBNF)

theorem nfT_pi_raw_second_first_replay
    {ATerm BTerm : LF.Term} {Aval Bval fuel Araw Braw Benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hBenc : encTyCore? BTerm = some Benc)
    (hBeval : ∃ M, eval pTC M Braw = Benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel Araw))
    (hB : FirstReplayNF BTerm Bval (nfT fuel Benc))
    (hPayloadReplay : ∀ {Bpre : AST}, LiftablePayload Bpre BTerm ->
      (∃ M, eval pTC M Bpre = Bval) -> StackReplayablePayload Bpre BTerm ->
        StackReplayablePayload (Pi Aval Bpre) (.pi ATerm BTerm))
    (hFinalReplay : StackReplayablePayload (Pi Aval Bval) (.pi ATerm BTerm)) :
    FirstReplayNF (.pi ATerm BTerm) (Pi Aval Bval) (nfT (S fuel) (Pi Araw Braw)) := by
  have hBnorm : IsNormal pTC Benc := isnormal_encTyCore?_tc BTerm Benc hBenc
  obtain ⟨MB, hMB⟩ := hBeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun B => nfPi1 fuel B (nfT fuel Araw))
      (fun B => NFActiveShape.pi1 fuel B (nfT fuel Araw))
      (fun B B' hstep => hcong_nfPi1_raw_nfT_arg_tc fuel B Araw hfuel B' hstep)
      MB hMB hBnorm
  have hnext : FirstReplayNF (.pi ATerm BTerm) (Pi Aval Bval)
      (nfPi1 fuel Benc (nfT fuel Araw)) := by
    exact nfPi1_nfT_first_replay (ATerm := ATerm) (BTerm := BTerm)
      (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := Benc)
      (Acall := nfT fuel Araw) hfuel hBnorm hA hB hPayloadReplay hFinalReplay
  have htail := first_replay_nf_prefix hMctx hMguard hnext
  exact first_replay_nf_prepend (nfT_pi_tc fuel Araw Braw)
    (NFActiveShape.nf (S fuel) (Pi Araw Braw)) htail

theorem nfT_pi_raw_second_first_replay_split
    {ATerm BRawTerm BNormTerm : LF.Term} {Aval Bval fuel Araw Braw Benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hBrawEnc : encTyCore? BRawTerm = some Benc)
    (hBeval : ∃ M, eval pTC M Braw = Benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel Araw))
    (hB : FirstReplayNF BNormTerm Bval (nfT fuel Benc))
    (hPayloadReplay : ∀ {Bpre : AST}, LiftablePayload Bpre BNormTerm ->
      (∃ M, eval pTC M Bpre = Bval) -> StackReplayablePayload Bpre BNormTerm ->
        StackReplayablePayload (Pi Aval Bpre) (.pi ATerm BNormTerm))
    (hFinalReplay : StackReplayablePayload (Pi Aval Bval) (.pi ATerm BNormTerm)) :
    FirstReplayNF (.pi ATerm BNormTerm) (Pi Aval Bval) (nfT (S fuel) (Pi Araw Braw)) := by
  have hBrawNorm : IsNormal pTC Benc := isnormal_encTyCore?_tc BRawTerm Benc hBrawEnc
  obtain ⟨MB, hMB⟩ := hBeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun B => nfPi1 fuel B (nfT fuel Araw))
      (fun B => NFActiveShape.pi1 fuel B (nfT fuel Araw))
      (fun B B' hstep => hcong_nfPi1_raw_nfT_arg_tc fuel B Araw hfuel B' hstep)
      MB hMB hBrawNorm
  have hnext : FirstReplayNF (.pi ATerm BNormTerm) (Pi Aval Bval)
      (nfPi1 fuel Benc (nfT fuel Araw)) := by
    exact nfPi1_nfT_first_replay (ATerm := ATerm) (BTerm := BNormTerm)
      (Aval := Aval) (Bval := Bval) (fuel := fuel) (B := Benc)
      (Acall := nfT fuel Araw) hfuel hBrawNorm hA hB hPayloadReplay hFinalReplay
  have htail := first_replay_nf_prefix hMctx hMguard hnext
  exact first_replay_nf_prepend (nfT_pi_tc fuel Araw Braw)
    (NFActiveShape.nf (S fuel) (Pi Araw Braw)) htail

theorem nfT_lam_raw_body_first_strong
    {ATerm bTerm : LF.Term} {Aval bval fuel Araw braw benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hbenc : encTyCore? bTerm = some benc)
    (hbeval : ∃ M, eval pTC M braw = benc)
    (hA : FirstStrongNF ATerm Aval (nfT fuel Araw))
    (hb : FirstStrongNF bTerm bval (nfT fuel benc)) :
    FirstStrongNF (.lam ATerm bTerm) (Lam Aval bval) (nfT (S fuel) (Lam Araw braw)) := by
  have hbnorm : IsNormal pTC benc := isnormal_encTyCore?_tc bTerm benc hbenc
  obtain ⟨MB, hMB⟩ := hbeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun b => nfLam1 fuel b (nfT fuel Araw))
      (fun b => NFActiveShape.lam1 fuel b (nfT fuel Araw))
      (fun b b' hstep => hcong_nfLam1_raw_nfT_arg_tc fuel b Araw hfuel b' hstep)
      MB hMB hbnorm
  have hnext : FirstStrongNF (.lam ATerm bTerm) (Lam Aval bval)
      (nfLam1 fuel benc (nfT fuel Araw)) := by
    exact FirstLiftableNF.toStrong
      (nfLam1_nfT_first_liftable (ATerm := ATerm) (bTerm := bTerm)
        (Aval := Aval) (bval := bval) (fuel := fuel) (b := benc)
        (Acall := nfT fuel Araw) hfuel hbnorm
        (FirstStrongNF.toFirstLiftable hA) (FirstStrongNF.toFirstLiftable hb))
  have htail := first_strong_nf_prefix hMctx hMguard hnext
  exact first_strong_nf_prepend (nfT_lam_tc fuel Araw braw)
    (NFActiveShape.nf (S fuel) (Lam Araw braw)) htail

theorem nfT_lam_raw_body_first_strong_split
    {ATerm bRawTerm bNormTerm : LF.Term} {Aval bval fuel Araw braw benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hbrawEnc : encTyCore? bRawTerm = some benc)
    (hbeval : ∃ M, eval pTC M braw = benc)
    (hA : FirstStrongNF ATerm Aval (nfT fuel Araw))
    (hb : FirstStrongNF bNormTerm bval (nfT fuel benc)) :
    FirstStrongNF (.lam ATerm bNormTerm) (Lam Aval bval) (nfT (S fuel) (Lam Araw braw)) := by
  have hbrawNorm : IsNormal pTC benc := isnormal_encTyCore?_tc bRawTerm benc hbrawEnc
  obtain ⟨MB, hMB⟩ := hbeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun b => nfLam1 fuel b (nfT fuel Araw))
      (fun b => NFActiveShape.lam1 fuel b (nfT fuel Araw))
      (fun b b' hstep => hcong_nfLam1_raw_nfT_arg_tc fuel b Araw hfuel b' hstep)
      MB hMB hbrawNorm
  have hnext : FirstStrongNF (.lam ATerm bNormTerm) (Lam Aval bval)
      (nfLam1 fuel benc (nfT fuel Araw)) := by
    exact FirstLiftableNF.toStrong
      (nfLam1_nfT_first_liftable (ATerm := ATerm) (bTerm := bNormTerm)
        (Aval := Aval) (bval := bval) (fuel := fuel) (b := benc)
        (Acall := nfT fuel Araw) hfuel hbrawNorm
        (FirstStrongNF.toFirstLiftable hA) (FirstStrongNF.toFirstLiftable hb))
  have htail := first_strong_nf_prefix hMctx hMguard hnext
  exact first_strong_nf_prepend (nfT_lam_tc fuel Araw braw)
    (NFActiveShape.nf (S fuel) (Lam Araw braw)) htail

theorem replayablePayload_lam_payload_tc {Aval bpre bval : AST} {ATerm bTerm : LF.Term}
    (hA : ReplayablePayload Aval ATerm)
    (hbpre : LiftablePayload bpre bTerm)
    (hbenc : encTyCore? bTerm = some bval)
    (hbeval : ∃ M, eval pTC M bpre = bval)
    (hbfinal : ReplayablePayload bval bTerm) :
    ReplayablePayload (Lam Aval bpre) (.lam ATerm bTerm) := by
  constructor
  · exact liftable_lam_tc hA.1 hbpre
  · intro fuelNat
    cases fuelNat with
    | zero =>
        have hcall : LiftablePayload (Lam Aval bpre) (.lam ATerm bTerm) :=
          liftable_lam_tc hA.1 hbpre
        rcases hcall.reduces with ⟨u, N, henc, hN⟩
        refine ⟨u, ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_z_first_strong henc hcall (liftable_encTyCore?_tc _ _ henc) ⟨N, hN⟩)
    | succ fuelPred =>
        obtain ⟨AvalNF, hANF⟩ := hA.2 fuelPred
        obtain ⟨bvalNF, hbNF⟩ := hbfinal.2 fuelPred
        refine ⟨Lam AvalNF bvalNF, ?_⟩
        simpa [peano, LFTyping.nf] using
          (nfT_lam_raw_body_first_strong_split
            (ATerm := LFTyping.nf LFTyping.corpusSig fuelPred ATerm)
            (bRawTerm := bTerm)
            (bNormTerm := LFTyping.nf LFTyping.corpusSig fuelPred bTerm)
            (Aval := AvalNF) (bval := bvalNF) (fuel := peano fuelPred)
            (Araw := Aval) (braw := bpre) (benc := bval)
            (isnormal_peano_tc fuelPred) hbenc hbeval hANF hbNF)

theorem nfT_lam_raw_body_first_replay
    {ATerm bTerm : LF.Term} {Aval bval fuel Araw braw benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hbenc : encTyCore? bTerm = some benc)
    (hbeval : ∃ M, eval pTC M braw = benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel Araw))
    (hb : FirstReplayNF bTerm bval (nfT fuel benc))
    (hPayloadReplay : ∀ {bpre : AST}, LiftablePayload bpre bTerm ->
      (∃ M, eval pTC M bpre = bval) -> StackReplayablePayload bpre bTerm ->
        StackReplayablePayload (Lam Aval bpre) (.lam ATerm bTerm))
    (hFinalReplay : StackReplayablePayload (Lam Aval bval) (.lam ATerm bTerm)) :
    FirstReplayNF (.lam ATerm bTerm) (Lam Aval bval) (nfT (S fuel) (Lam Araw braw)) := by
  have hbnorm : IsNormal pTC benc := isnormal_encTyCore?_tc bTerm benc hbenc
  obtain ⟨MB, hMB⟩ := hbeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun b => nfLam1 fuel b (nfT fuel Araw))
      (fun b => NFActiveShape.lam1 fuel b (nfT fuel Araw))
      (fun b b' hstep => hcong_nfLam1_raw_nfT_arg_tc fuel b Araw hfuel b' hstep)
      MB hMB hbnorm
  have hnext : FirstReplayNF (.lam ATerm bTerm) (Lam Aval bval)
      (nfLam1 fuel benc (nfT fuel Araw)) := by
    exact nfLam1_nfT_first_replay (ATerm := ATerm) (bTerm := bTerm)
      (Aval := Aval) (bval := bval) (fuel := fuel) (b := benc)
      (Acall := nfT fuel Araw) hfuel hbnorm hA hb hPayloadReplay hFinalReplay
  have htail := first_replay_nf_prefix hMctx hMguard hnext
  exact first_replay_nf_prepend (nfT_lam_tc fuel Araw braw)
    (NFActiveShape.nf (S fuel) (Lam Araw braw)) htail

theorem nfT_lam_raw_body_first_replay_split
    {ATerm bRawTerm bNormTerm : LF.Term} {Aval bval fuel Araw braw benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hbrawEnc : encTyCore? bRawTerm = some benc)
    (hbeval : ∃ M, eval pTC M braw = benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel Araw))
    (hb : FirstReplayNF bNormTerm bval (nfT fuel benc))
    (hPayloadReplay : ∀ {bpre : AST}, LiftablePayload bpre bNormTerm ->
      (∃ M, eval pTC M bpre = bval) -> StackReplayablePayload bpre bNormTerm ->
        StackReplayablePayload (Lam Aval bpre) (.lam ATerm bNormTerm))
    (hFinalReplay : StackReplayablePayload (Lam Aval bval) (.lam ATerm bNormTerm)) :
    FirstReplayNF (.lam ATerm bNormTerm) (Lam Aval bval) (nfT (S fuel) (Lam Araw braw)) := by
  have hbrawNorm : IsNormal pTC benc := isnormal_encTyCore?_tc bRawTerm benc hbrawEnc
  obtain ⟨MB, hMB⟩ := hbeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun b => nfLam1 fuel b (nfT fuel Araw))
      (fun b => NFActiveShape.lam1 fuel b (nfT fuel Araw))
      (fun b b' hstep => hcong_nfLam1_raw_nfT_arg_tc fuel b Araw hfuel b' hstep)
      MB hMB hbrawNorm
  have hnext : FirstReplayNF (.lam ATerm bNormTerm) (Lam Aval bval)
      (nfLam1 fuel benc (nfT fuel Araw)) := by
    exact nfLam1_nfT_first_replay (ATerm := ATerm) (bTerm := bNormTerm)
      (Aval := Aval) (bval := bval) (fuel := fuel) (b := benc)
      (Acall := nfT fuel Araw) hfuel hbrawNorm hA hb hPayloadReplay hFinalReplay
  have htail := first_replay_nf_prefix hMctx hMguard hnext
  exact first_replay_nf_prepend (nfT_lam_tc fuel Araw braw)
    (NFActiveShape.nf (S fuel) (Lam Araw braw)) htail

theorem nfT_substT_pi_raw_second_first_replay
    {ATerm BTerm : LF.Term} {Aval Bval fuel j sAst A B Benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hBenc : encTyCore? BTerm = some Benc)
    (hBeval : ∃ M, eval pTC M (substT (S j) (liftT (S Z) Z sAst) B) = Benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel (substT j sAst A)))
    (hB : FirstReplayNF BTerm Bval (nfT fuel Benc))
    (hPayloadReplay : ∀ {Bpre : AST}, LiftablePayload Bpre BTerm ->
      (∃ M, eval pTC M Bpre = Bval) -> StackReplayablePayload Bpre BTerm ->
        StackReplayablePayload (Pi Aval Bpre) (.pi ATerm BTerm))
    (hFinalReplay : StackReplayablePayload (Pi Aval Bval) (.pi ATerm BTerm)) :
    FirstReplayNF (.pi ATerm BTerm) (Pi Aval Bval)
      (nfT (S fuel) (substT j sAst (Pi A B))) := by
  have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (Pi A B))) =
      nfT (S fuel)
        (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B)) := by
    simp only [eval,
      hcong_nfT_s_substT_arg_tc fuel j sAst (Pi A B)
        (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B))
        hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substT j sAst (Pi A B)))
    (nfT_pi_raw_second_first_replay (ATerm := ATerm) (BTerm := BTerm)
      (Aval := Aval) (Bval := Bval) (fuel := fuel)
      (Araw := substT j sAst A)
      (Braw := substT (S j) (liftT (S Z) Z sAst) B)
      (Benc := Benc) hfuel hBenc hBeval hA hB hPayloadReplay hFinalReplay)

theorem nfT_substT_pi_raw_second_first_replay_split
    {ATerm BRawTerm BNormTerm : LF.Term} {Aval Bval fuel j sAst A B Benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hBrawEnc : encTyCore? BRawTerm = some Benc)
    (hBeval : ∃ M, eval pTC M (substT (S j) (liftT (S Z) Z sAst) B) = Benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel (substT j sAst A)))
    (hB : FirstReplayNF BNormTerm Bval (nfT fuel Benc))
    (hPayloadReplay : ∀ {Bpre : AST}, LiftablePayload Bpre BNormTerm ->
      (∃ M, eval pTC M Bpre = Bval) -> StackReplayablePayload Bpre BNormTerm ->
        StackReplayablePayload (Pi Aval Bpre) (.pi ATerm BNormTerm))
    (hFinalReplay : StackReplayablePayload (Pi Aval Bval) (.pi ATerm BNormTerm)) :
    FirstReplayNF (.pi ATerm BNormTerm) (Pi Aval Bval)
      (nfT (S fuel) (substT j sAst (Pi A B))) := by
  have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (Pi A B))) =
      nfT (S fuel)
        (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B)) := by
    simp only [eval,
      hcong_nfT_s_substT_arg_tc fuel j sAst (Pi A B)
        (Pi (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) B))
        hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substT j sAst (Pi A B)))
    (nfT_pi_raw_second_first_replay_split (ATerm := ATerm) (BRawTerm := BRawTerm)
      (BNormTerm := BNormTerm) (Aval := Aval) (Bval := Bval) (fuel := fuel)
      (Araw := substT j sAst A)
      (Braw := substT (S j) (liftT (S Z) Z sAst) B)
      (Benc := Benc) hfuel hBrawEnc hBeval hA hB hPayloadReplay hFinalReplay)

theorem nfT_substT_lam_raw_body_first_replay
    {ATerm bTerm : LF.Term} {Aval bval fuel j sAst A b benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hbenc : encTyCore? bTerm = some benc)
    (hbeval : ∃ M, eval pTC M (substT (S j) (liftT (S Z) Z sAst) b) = benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel (substT j sAst A)))
    (hb : FirstReplayNF bTerm bval (nfT fuel benc))
    (hPayloadReplay : ∀ {bpre : AST}, LiftablePayload bpre bTerm ->
      (∃ M, eval pTC M bpre = bval) -> StackReplayablePayload bpre bTerm ->
        StackReplayablePayload (Lam Aval bpre) (.lam ATerm bTerm))
    (hFinalReplay : StackReplayablePayload (Lam Aval bval) (.lam ATerm bTerm)) :
    FirstReplayNF (.lam ATerm bTerm) (Lam Aval bval)
      (nfT (S fuel) (substT j sAst (Lam A b))) := by
  have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (Lam A b))) =
      nfT (S fuel)
        (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b)) := by
    simp only [eval,
      hcong_nfT_s_substT_arg_tc fuel j sAst (Lam A b)
        (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b))
        hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substT j sAst (Lam A b)))
    (nfT_lam_raw_body_first_replay (ATerm := ATerm) (bTerm := bTerm)
      (Aval := Aval) (bval := bval) (fuel := fuel)
      (Araw := substT j sAst A)
      (braw := substT (S j) (liftT (S Z) Z sAst) b)
      (benc := benc) hfuel hbenc hbeval hA hb hPayloadReplay hFinalReplay)

theorem nfT_substT_lam_raw_body_first_replay_split
    {ATerm bRawTerm bNormTerm : LF.Term} {Aval bval fuel j sAst A b benc : AST}
    (hfuel : IsNormal pTC fuel)
    (hbrawEnc : encTyCore? bRawTerm = some benc)
    (hbeval : ∃ M, eval pTC M (substT (S j) (liftT (S Z) Z sAst) b) = benc)
    (hA : FirstReplayNF ATerm Aval (nfT fuel (substT j sAst A)))
    (hb : FirstReplayNF bNormTerm bval (nfT fuel benc))
    (hPayloadReplay : ∀ {bpre : AST}, LiftablePayload bpre bNormTerm ->
      (∃ M, eval pTC M bpre = bval) -> StackReplayablePayload bpre bNormTerm ->
        StackReplayablePayload (Lam Aval bpre) (.lam ATerm bNormTerm))
    (hFinalReplay : StackReplayablePayload (Lam Aval bval) (.lam ATerm bNormTerm)) :
    FirstReplayNF (.lam ATerm bNormTerm) (Lam Aval bval)
      (nfT (S fuel) (substT j sAst (Lam A b))) := by
  have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (Lam A b))) =
      nfT (S fuel)
        (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b)) := by
    simp only [eval,
      hcong_nfT_s_substT_arg_tc fuel j sAst (Lam A b)
        (Lam (substT j sAst A) (substT (S j) (liftT (S Z) Z sAst) b))
        hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substT j sAst (Lam A b)))
    (nfT_lam_raw_body_first_replay_split (ATerm := ATerm) (bRawTerm := bRawTerm)
      (bNormTerm := bNormTerm) (Aval := Aval) (bval := bval) (fuel := fuel)
      (Araw := substT j sAst A)
      (braw := substT (S j) (liftT (S Z) Z sAst) b)
      (benc := benc) hfuel hbrawEnc hbeval hA hb hPayloadReplay hFinalReplay)

theorem nfT_app_raw_arg_first_strong
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel fraw araw aenc : AST}
    (hfuel : IsNormal pTC fuel)
    (haenc : encTyCore? aTerm = some aenc)
    (haeval : ∃ M, eval pTC M araw = aenc)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstStrongNF fTerm fVal (nfT fuel fraw))
    (hA : FirstStrongNF aTerm aVal (nfT fuel aenc))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> LiftablePayload aPre aTerm ->
        (∃ M, eval pTC M aPre = aVal) ->
          FirstStrongNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstStrongNF resTerm resVal (nfT (S fuel) (App fraw araw)) := by
  have hanorm : IsNormal pTC aenc := isnormal_encTyCore?_tc aTerm aenc haenc
  obtain ⟨MA, hMA⟩ := haeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun a => nfApp1 fuel a (nfT fuel fraw))
      (fun a => NFActiveShape.app1 fuel a (nfT fuel fraw))
      (fun a a' hstep => hcong_nfApp1_raw_nfT_arg_tc fuel a fraw hfuel a' hstep)
      MA hMA hanorm
  have hnext : FirstStrongNF resTerm resVal (nfApp1 fuel aenc (nfT fuel fraw)) := by
    exact FirstLiftableNF.toStrong
      (nfApp1_nfT_first_liftable (fTerm := fTerm) (resTerm := resTerm)
        (fVal := fVal) (resVal := resVal) (fuel := fuel) (aAst := aenc)
        (fCall := nfT fuel fraw) hfuel hanorm (FirstStrongNF.toFirstLiftable hF)
        (by
          intro fPre hfLift hfEval
          exact nfApp2_nfT_first_liftable (aTerm := aTerm) (resTerm := resTerm)
            (aVal := aVal) (resVal := resVal) (fuel := fuel) (fPre := fPre)
            (fVal := fVal) (aAst := aenc) hfuel hfnorm hfEval
            (FirstStrongNF.toFirstLiftable hA)
            (by
              intro aPre haLift haEval
              exact FirstStrongNF.toFirstLiftable (hTail hfLift hfEval haLift haEval))))
  have htail := first_strong_nf_prefix hMctx hMguard hnext
  exact first_strong_nf_prepend (nfT_app_tc fuel fraw araw)
    (NFActiveShape.nf (S fuel) (App fraw araw)) htail

theorem nfT_app_raw_arg_first_strong_split
    {fTerm aRawTerm aNormTerm resTerm : LF.Term} {fVal aVal resVal fuel fraw araw aenc : AST}
    (hfuel : IsNormal pTC fuel)
    (haRawEnc : encTyCore? aRawTerm = some aenc)
    (haeval : ∃ M, eval pTC M araw = aenc)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstStrongNF fTerm fVal (nfT fuel fraw))
    (hA : FirstStrongNF aNormTerm aVal (nfT fuel aenc))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> LiftablePayload aPre aNormTerm ->
        (∃ M, eval pTC M aPre = aVal) ->
          FirstStrongNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstStrongNF resTerm resVal (nfT (S fuel) (App fraw araw)) := by
  have hanorm : IsNormal pTC aenc := isnormal_encTyCore?_tc aRawTerm aenc haRawEnc
  obtain ⟨MA, hMA⟩ := haeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun a => nfApp1 fuel a (nfT fuel fraw))
      (fun a => NFActiveShape.app1 fuel a (nfT fuel fraw))
      (fun a a' hstep => hcong_nfApp1_raw_nfT_arg_tc fuel a fraw hfuel a' hstep)
      MA hMA hanorm
  have hnext : FirstStrongNF resTerm resVal (nfApp1 fuel aenc (nfT fuel fraw)) := by
    exact FirstLiftableNF.toStrong
      (nfApp1_nfT_first_liftable (fTerm := fTerm) (resTerm := resTerm)
        (fVal := fVal) (resVal := resVal) (fuel := fuel) (aAst := aenc)
        (fCall := nfT fuel fraw) hfuel hanorm (FirstStrongNF.toFirstLiftable hF)
        (by
          intro fPre hfLift hfEval
          exact nfApp2_nfT_first_liftable (aTerm := aNormTerm) (resTerm := resTerm)
            (aVal := aVal) (resVal := resVal) (fuel := fuel) (fPre := fPre)
            (fVal := fVal) (aAst := aenc) hfuel hfnorm hfEval
            (FirstStrongNF.toFirstLiftable hA)
            (by
              intro aPre haLift haEval
              exact FirstStrongNF.toFirstLiftable (hTail hfLift hfEval haLift haEval))))
  have htail := first_strong_nf_prefix hMctx hMguard hnext
  exact first_strong_nf_prepend (nfT_app_tc fuel fraw araw)
    (NFActiveShape.nf (S fuel) (App fraw araw)) htail

theorem nfT_app_raw_arg_first_strong_replay
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel fraw araw aenc : AST}
    (hfuel : IsNormal pTC fuel)
    (haenc : encTyCore? aTerm = some aenc)
    (haeval : ∃ M, eval pTC M araw = aenc)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstStrongNF fTerm fVal (nfT fuel fraw))
    (hA : FirstStrongNF aTerm aVal (nfT fuel aenc))
    (hAReplay : ∀ {aPre : AST}, LiftablePayload aPre aTerm ->
      (∃ M, eval pTC M aPre = aVal) -> StackReplayablePayload aPre aTerm)
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> LiftablePayload aPre aTerm ->
        (∃ M, eval pTC M aPre = aVal) -> StackReplayablePayload aPre aTerm ->
          FirstStrongNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstStrongNF resTerm resVal (nfT (S fuel) (App fraw araw)) := by
  exact nfT_app_raw_arg_first_strong (fTerm := fTerm) (aTerm := aTerm)
    (resTerm := resTerm) (fVal := fVal) (aVal := aVal) (resVal := resVal)
    (fuel := fuel) (fraw := fraw) (araw := araw) (aenc := aenc)
    hfuel haenc haeval hfnorm hF hA
    (by
      intro fPre aPre hfLift hfEval haLift haEval
      exact hTail hfLift hfEval haLift haEval (hAReplay haLift haEval))

theorem nfT_app_raw_arg_first_replay
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel fraw araw aenc : AST}
    (hfuel : IsNormal pTC fuel)
    (haenc : encTyCore? aTerm = some aenc)
    (haeval : ∃ M, eval pTC M araw = aenc)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstReplayNF fTerm fVal (nfT fuel fraw))
    (hA : FirstReplayNF aTerm aVal (nfT fuel aenc))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> StackReplayablePayload fPre fTerm ->
        LiftablePayload aPre aTerm -> (∃ M, eval pTC M aPre = aVal) ->
          StackReplayablePayload aPre aTerm ->
            FirstReplayNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstReplayNF resTerm resVal (nfT (S fuel) (App fraw araw)) := by
  have hanorm : IsNormal pTC aenc := isnormal_encTyCore?_tc aTerm aenc haenc
  obtain ⟨MA, hMA⟩ := haeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun a => nfApp1 fuel a (nfT fuel fraw))
      (fun a => NFActiveShape.app1 fuel a (nfT fuel fraw))
      (fun a a' hstep => hcong_nfApp1_raw_nfT_arg_tc fuel a fraw hfuel a' hstep)
      MA hMA hanorm
  have hnext : FirstReplayNF resTerm resVal (nfApp1 fuel aenc (nfT fuel fraw)) := by
    exact nfApp1_nfT_first_replay (fTerm := fTerm) (resTerm := resTerm)
      (fVal := fVal) (resVal := resVal) (fuel := fuel) (aAst := aenc)
      (fCall := nfT fuel fraw) hfuel hanorm hF
      (by
        intro fPre hfLift hfEval hfReplay
        exact nfApp2_nfT_first_replay (aTerm := aTerm) (resTerm := resTerm)
          (aVal := aVal) (resVal := resVal) (fuel := fuel) (fPre := fPre)
          (fVal := fVal) (aAst := aenc) hfuel hfnorm hfEval hA
          (by
            intro aPre haLift haEval haReplay
            exact hTail hfLift hfEval hfReplay haLift haEval haReplay))
  have htail := first_replay_nf_prefix hMctx hMguard hnext
  exact first_replay_nf_prepend (nfT_app_tc fuel fraw araw)
    (NFActiveShape.nf (S fuel) (App fraw araw)) htail

theorem nfT_app_raw_arg_first_replay_split
    {fTerm aRawTerm aNormTerm resTerm : LF.Term} {fVal aVal resVal fuel fraw araw aenc : AST}
    (hfuel : IsNormal pTC fuel)
    (haRawEnc : encTyCore? aRawTerm = some aenc)
    (haeval : ∃ M, eval pTC M araw = aenc)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstReplayNF fTerm fVal (nfT fuel fraw))
    (hA : FirstReplayNF aNormTerm aVal (nfT fuel aenc))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> StackReplayablePayload fPre fTerm ->
        LiftablePayload aPre aNormTerm -> (∃ M, eval pTC M aPre = aVal) ->
          StackReplayablePayload aPre aNormTerm ->
            FirstReplayNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstReplayNF resTerm resVal (nfT (S fuel) (App fraw araw)) := by
  have hanorm : IsNormal pTC aenc := isnormal_encTyCore?_tc aRawTerm aenc haRawEnc
  obtain ⟨MA, hMA⟩ := haeval
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_nf_wrapper_with_guard
      (fun a => nfApp1 fuel a (nfT fuel fraw))
      (fun a => NFActiveShape.app1 fuel a (nfT fuel fraw))
      (fun a a' hstep => hcong_nfApp1_raw_nfT_arg_tc fuel a fraw hfuel a' hstep)
      MA hMA hanorm
  have hnext : FirstReplayNF resTerm resVal (nfApp1 fuel aenc (nfT fuel fraw)) := by
    exact nfApp1_nfT_first_replay (fTerm := fTerm) (resTerm := resTerm)
      (fVal := fVal) (resVal := resVal) (fuel := fuel) (aAst := aenc)
      (fCall := nfT fuel fraw) hfuel hanorm hF
      (by
        intro fPre hfLift hfEval hfReplay
        exact nfApp2_nfT_first_replay (aTerm := aNormTerm) (resTerm := resTerm)
          (aVal := aVal) (resVal := resVal) (fuel := fuel) (fPre := fPre)
          (fVal := fVal) (aAst := aenc) hfuel hfnorm hfEval hA
          (by
            intro aPre haLift haEval haReplay
            exact hTail hfLift hfEval hfReplay haLift haEval haReplay))
  have htail := first_replay_nf_prefix hMctx hMguard hnext
  exact first_replay_nf_prepend (nfT_app_tc fuel fraw araw)
    (NFActiveShape.nf (S fuel) (App fraw araw)) htail

theorem nfT_substT_app_raw_arg_first_replay
    {fTerm aTerm resTerm : LF.Term} {fVal aVal resVal fuel j sAst f a aenc : AST}
    (hfuel : IsNormal pTC fuel)
    (haenc : encTyCore? aTerm = some aenc)
    (haeval : ∃ M, eval pTC M (substT j sAst a) = aenc)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstReplayNF fTerm fVal (nfT fuel (substT j sAst f)))
    (hA : FirstReplayNF aTerm aVal (nfT fuel aenc))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> StackReplayablePayload fPre fTerm ->
        LiftablePayload aPre aTerm -> (∃ M, eval pTC M aPre = aVal) ->
          StackReplayablePayload aPre aTerm ->
            FirstReplayNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstReplayNF resTerm resVal
      (nfT (S fuel) (substT j sAst (App f a))) := by
  have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (App f a))) =
      nfT (S fuel) (App (substT j sAst f) (substT j sAst a)) := by
    simp only [eval,
      hcong_nfT_s_substT_arg_tc fuel j sAst (App f a)
        (App (substT j sAst f) (substT j sAst a)) hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substT j sAst (App f a)))
    (nfT_app_raw_arg_first_replay (fTerm := fTerm) (aTerm := aTerm)
      (resTerm := resTerm) (fVal := fVal) (aVal := aVal) (resVal := resVal)
      (fuel := fuel) (fraw := substT j sAst f) (araw := substT j sAst a)
      (aenc := aenc) hfuel haenc haeval hfnorm hF hA hTail)

theorem nfT_substT_app_raw_arg_first_replay_split
    {fTerm aRawTerm aNormTerm resTerm : LF.Term} {fVal aVal resVal fuel j sAst f a aenc : AST}
    (hfuel : IsNormal pTC fuel)
    (haRawEnc : encTyCore? aRawTerm = some aenc)
    (haeval : ∃ M, eval pTC M (substT j sAst a) = aenc)
    (hfnorm : IsNormal pTC fVal)
    (hF : FirstReplayNF fTerm fVal (nfT fuel (substT j sAst f)))
    (hA : FirstReplayNF aNormTerm aVal (nfT fuel aenc))
    (hTail : ∀ {fPre aPre : AST}, LiftablePayload fPre fTerm ->
      (∃ M, eval pTC M fPre = fVal) -> StackReplayablePayload fPre fTerm ->
        LiftablePayload aPre aNormTerm -> (∃ M, eval pTC M aPre = aVal) ->
          StackReplayablePayload aPre aNormTerm ->
            FirstReplayNF resTerm resVal (nfAppT fuel fVal aPre)) :
    FirstReplayNF resTerm resVal
      (nfT (S fuel) (substT j sAst (App f a))) := by
  have hstep : eval pTC 1 (nfT (S fuel) (substT j sAst (App f a))) =
      nfT (S fuel) (App (substT j sAst f) (substT j sAst a)) := by
    simp only [eval,
      hcong_nfT_s_substT_arg_tc fuel j sAst (App f a)
        (App (substT j sAst f) (substT j sAst a))
        hfuel rfl]
  exact first_replay_nf_prepend hstep
    (NFActiveShape.nf (S fuel) (substT j sAst (App f a)))
    (nfT_app_raw_arg_first_replay_split (fTerm := fTerm) (aRawTerm := aRawTerm)
      (aNormTerm := aNormTerm) (resTerm := resTerm)
      (fVal := fVal) (aVal := aVal) (resVal := resVal)
      (fuel := fuel) (fraw := substT j sAst f) (araw := substT j sAst a)
      (aenc := aenc) hfuel haRawEnc haeval hfnorm hF hA hTail)

theorem nfAppT_nfApp_first_liftable
    (fuelNat : Nat) (fNF aNF : LF.Term) (fVal aPre aVal : AST)
    (hfenc : encTyCore? fNF = some fVal)
    (hflift : LiftablePayload fVal fNF)
    (haenc : encTyCore? aNF = some aVal)
    (halift : LiftablePayload aPre aNF)
    (haeval : ∃ M, eval pTC M aPre = aVal)
    (hBeta : ∀ {fuelPred : Nat} {A body : LF.Term} {AAst bodyAst : AST},
      fuelNat = fuelPred + 1 ->
        fNF = .lam A body ->
          encTyCore? A = some AAst ->
            encTyCore? body = some bodyAst ->
              ∃ resVal,
                FirstLiftableNF
                  (LFTyping.nf LFTyping.corpusSig fuelPred (LFTyping.subst0 aNF body))
                  resVal (nfT (peano fuelPred) (substT Z aPre bodyAst))) :
    ∃ resVal,
      FirstLiftableNF (LFTyping.nfApp LFTyping.corpusSig fuelNat fNF aNF)
        resVal (nfAppT (peano fuelNat) fVal aPre) := by
  cases fuelNat with
  | zero =>
      refine ⟨App fVal aVal, ?_⟩
      simpa [peano, LFTyping.nfApp] using
        (nfAppT_z_first_liftable (fVal := fVal) (aPre := aPre)
          (fTerm := fNF) (aTerm := aNF) (aVal := aVal)
          hfenc hflift haenc halift haeval)
  | succ fuelPred =>
      cases fNF with
      | srt s =>
          cases s <;> simp [encTyCore?] at hfenc <;> subst fVal
          · refine ⟨App (Srt typeS) aVal, ?_⟩
            simpa [peano, LFTyping.nfApp] using
              (nfAppT_wrap_first_liftable
                (hroot := nfAppT_srt_fall_tc (peano fuelPred) typeS aPre)
                (fTerm := LF.Term.srt .type) (aTerm := aNF) (aVal := aVal)
                rfl hflift haenc halift haeval)
          · refine ⟨App (Srt kindS) aVal, ?_⟩
            simpa [peano, LFTyping.nfApp] using
              (nfAppT_wrap_first_liftable
                (hroot := nfAppT_srt_fall_tc (peano fuelPred) kindS aPre)
                (fTerm := LF.Term.srt .kind) (aTerm := aNF) (aVal := aVal)
                rfl hflift haenc halift haeval)
      | var k =>
          simp [encTyCore?] at hfenc
          subst fVal
          refine ⟨App (Var (peano k)) aVal, ?_⟩
          simpa [peano, LFTyping.nfApp] using
            (nfAppT_wrap_first_liftable
              (hroot := nfAppT_var_fall_tc (peano fuelPred) (peano k) aPre)
              (fTerm := LF.Term.var k) (aTerm := aNF) (aVal := aVal)
              rfl hflift haenc halift haeval)
      | con x =>
          unfold encTyCore? at hfenc
          cases hx : encName? x with
          | none => simp [hx] at hfenc
          | some k =>
              simp [hx] at hfenc
              subst fVal
              refine ⟨App (Con k) aVal, ?_⟩
              have hfenc' : encTyCore? (.con x) = some (Con k) := by
                unfold encTyCore?
                simp [hx]
              simpa [peano, LFTyping.nfApp] using
                (nfAppT_wrap_first_liftable
                  (hroot := nfAppT_con_fall_tc (peano fuelPred) k aPre)
                  (fTerm := LF.Term.con x) (aTerm := aNF) (aVal := aVal)
                  hfenc' hflift haenc halift haeval)
      | pi A B =>
          simp [encTyCore?] at hfenc
          cases hA : encTyCore? A with
          | none => simp [hA] at hfenc
          | some AAst =>
              cases hB : encTyCore? B with
              | none => simp [hA, hB] at hfenc
              | some BAst =>
                  simp [hA, hB] at hfenc
                  subst fVal
                  refine ⟨App (Pi AAst BAst) aVal, ?_⟩
                  have hfenc' : encTyCore? (.pi A B) = some (Pi AAst BAst) := by
                    simp [encTyCore?, hA, hB]
                  simpa [peano, LFTyping.nfApp] using
                    (nfAppT_wrap_first_liftable
                      (hroot := nfAppT_pi_fall_tc (peano fuelPred) AAst BAst aPre)
                      (fTerm := LF.Term.pi A B) (aTerm := aNF) (aVal := aVal)
                      hfenc' hflift haenc halift haeval)
      | lam A body =>
          simp [encTyCore?] at hfenc
          cases hA : encTyCore? A with
          | none => simp [hA] at hfenc
          | some AAst =>
              cases hbody : encTyCore? body with
              | none => simp [hA, hbody] at hfenc
              | some bodyAst =>
                  simp [hA, hbody] at hfenc
                  subst fVal
                  obtain ⟨resVal, hnext⟩ :=
                    hBeta (fuelPred := fuelPred) (A := A) (body := body)
                      (AAst := AAst) (bodyAst := bodyAst) rfl rfl hA hbody
                  refine ⟨resVal, ?_⟩
                  simpa [peano, LFTyping.nfApp, LFTyping.subst0] using
                    (nfAppT_beta_prepend_first_liftable
                      (fuel := peano fuelPred) (A := AAst) (body := bodyAst)
                      (aPre := aPre) hnext)
      | app f a =>
          simp [encTyCore?] at hfenc
          cases hf : encTyCore? f with
          | none => simp [hf] at hfenc
          | some fAst =>
              cases ha : encTyCore? a with
              | none => simp [hf, ha] at hfenc
              | some aAst =>
                  simp [hf, ha] at hfenc
                  subst fVal
                  refine ⟨App (App fAst aAst) aVal, ?_⟩
                  have hfenc' : encTyCore? (.app f a) = some (App fAst aAst) := by
                    simp [encTyCore?, hf, ha]
                  simpa [peano, LFTyping.nfApp] using
                    (nfAppT_wrap_first_liftable
                      (hroot := nfAppT_app_fall_tc (peano fuelPred) fAst aAst aPre)
                      (fTerm := LF.Term.app f a) (aTerm := aNF) (aVal := aVal)
                      hfenc' hflift haenc halift haeval)

theorem nfAppT_nfApp_first_strong
    (fuelNat : Nat) (fNF aNF : LF.Term) (fVal aPre aVal : AST)
    (hfenc : encTyCore? fNF = some fVal)
    (hflift : LiftablePayload fVal fNF)
    (haenc : encTyCore? aNF = some aVal)
    (halift : LiftablePayload aPre aNF)
    (haeval : ∃ M, eval pTC M aPre = aVal)
    (hBeta : ∀ {fuelPred : Nat} {A body : LF.Term} {AAst bodyAst : AST},
      fuelNat = fuelPred + 1 ->
        fNF = .lam A body ->
          encTyCore? A = some AAst ->
            encTyCore? body = some bodyAst ->
              ∃ resVal,
                FirstStrongNF
                  (LFTyping.nf LFTyping.corpusSig fuelPred (LFTyping.subst0 aNF body))
                  resVal (nfT (peano fuelPred) (substT Z aPre bodyAst))) :
    ∃ resVal,
      FirstStrongNF (LFTyping.nfApp LFTyping.corpusSig fuelNat fNF aNF)
        resVal (nfAppT (peano fuelNat) fVal aPre) := by
  obtain ⟨resVal, hres⟩ :=
    nfAppT_nfApp_first_liftable fuelNat fNF aNF fVal aPre aVal
      hfenc hflift haenc halift haeval
      (by
        intro fuelPred A body AAst bodyAst hfuel hshape hA hbody
        obtain ⟨resVal, hstrong⟩ :=
          hBeta hfuel hshape hA hbody
        exact ⟨resVal, FirstStrongNF.toFirstLiftable hstrong⟩)
  exact ⟨resVal, FirstLiftableNF.toStrong hres⟩

theorem nfAppT_nfApp_first_strong_replay
    (fuelNat : Nat) (fNF aNF : LF.Term) (fVal aPre aVal : AST)
    (hfenc : encTyCore? fNF = some fVal)
    (hflift : LiftablePayload fVal fNF)
    (haenc : encTyCore? aNF = some aVal)
    (halift : LiftablePayload aPre aNF)
    (haeval : ∃ M, eval pTC M aPre = aVal)
    (haReplay : StackReplayablePayload aPre aNF)
    (hBeta : ∀ {fuelPred : Nat} {A body : LF.Term} {AAst bodyAst : AST},
      fuelNat = fuelPred + 1 ->
        fNF = .lam A body ->
          encTyCore? A = some AAst ->
            encTyCore? body = some bodyAst ->
              StackReplayablePayload aPre aNF ->
                ∃ resVal,
                  FirstStrongNF
                    (LFTyping.nf LFTyping.corpusSig fuelPred (LFTyping.subst0 aNF body))
                    resVal (nfT (peano fuelPred) (substT Z aPre bodyAst))) :
    ∃ resVal,
      FirstStrongNF (LFTyping.nfApp LFTyping.corpusSig fuelNat fNF aNF)
        resVal (nfAppT (peano fuelNat) fVal aPre) := by
  exact nfAppT_nfApp_first_strong fuelNat fNF aNF fVal aPre aVal
    hfenc hflift haenc halift haeval
    (by
      intro fuelPred A body AAst bodyAst hfuel hshape hA hbody
      exact hBeta hfuel hshape hA hbody haReplay)

theorem nfAppT_nfApp_first_replay
    (fuelNat : Nat) (fNF aNF : LF.Term) (fVal aPre aVal : AST)
    (hfenc : encTyCore? fNF = some fVal)
    (hflift : LiftablePayload fVal fNF)
    (haenc : encTyCore? aNF = some aVal)
    (halift : LiftablePayload aPre aNF)
    (haeval : ∃ M, eval pTC M aPre = aVal)
    (haReplay : StackReplayablePayload aPre aNF)
    (hWrapReplay : ∀ {fTerm : LF.Term} {fAst : AST},
      encTyCore? fTerm = some fAst ->
        StackReplayablePayload (App fAst aPre) (.app fTerm aNF) ∧
          StackReplayablePayload (App fAst aVal) (.app fTerm aNF))
    (hBeta : ∀ {fuelPred : Nat} {A body : LF.Term} {AAst bodyAst : AST},
      fuelNat = fuelPred + 1 ->
        fNF = .lam A body ->
          encTyCore? A = some AAst ->
            encTyCore? body = some bodyAst ->
              StackReplayablePayload aPre aNF ->
                ∃ resVal,
                  FirstReplayNF
                    (LFTyping.nf LFTyping.corpusSig fuelPred (LFTyping.subst0 aNF body))
                    resVal (nfT (peano fuelPred) (substT Z aPre bodyAst))) :
    ∃ resVal,
      FirstReplayNF (LFTyping.nfApp LFTyping.corpusSig fuelNat fNF aNF)
        resVal (nfAppT (peano fuelNat) fVal aPre) := by
  cases fuelNat with
  | zero =>
      obtain ⟨hPayloadReplay, hFinalReplay⟩ := hWrapReplay hfenc
      refine ⟨App fVal aVal, ?_⟩
      simpa [peano, LFTyping.nfApp] using
        (nfAppT_wrap_first_replay
          (hroot := nfAppT_z_tc fVal aPre)
          (fTerm := fNF) (aTerm := aNF) (aVal := aVal)
          hfenc hflift haenc halift haeval hPayloadReplay hFinalReplay)
  | succ fuelPred =>
      cases fNF with
      | srt s =>
          cases s <;> simp [encTyCore?] at hfenc <;> subst fVal
          · refine ⟨App (Srt typeS) aVal, ?_⟩
            obtain ⟨hPayloadReplay, hFinalReplay⟩ :=
              hWrapReplay (fTerm := LF.Term.srt .type) (fAst := Srt typeS) rfl
            simpa [peano, LFTyping.nfApp] using
              (nfAppT_wrap_first_replay
                (hroot := nfAppT_srt_fall_tc (peano fuelPred) typeS aPre)
                (fTerm := LF.Term.srt .type) (aTerm := aNF) (aVal := aVal)
                rfl hflift haenc halift haeval hPayloadReplay hFinalReplay)
          · refine ⟨App (Srt kindS) aVal, ?_⟩
            obtain ⟨hPayloadReplay, hFinalReplay⟩ :=
              hWrapReplay (fTerm := LF.Term.srt .kind) (fAst := Srt kindS) rfl
            simpa [peano, LFTyping.nfApp] using
              (nfAppT_wrap_first_replay
                (hroot := nfAppT_srt_fall_tc (peano fuelPred) kindS aPre)
                (fTerm := LF.Term.srt .kind) (aTerm := aNF) (aVal := aVal)
                rfl hflift haenc halift haeval hPayloadReplay hFinalReplay)
      | var k =>
          simp [encTyCore?] at hfenc
          subst fVal
          refine ⟨App (Var (peano k)) aVal, ?_⟩
          obtain ⟨hPayloadReplay, hFinalReplay⟩ :=
            hWrapReplay (fTerm := LF.Term.var k) (fAst := Var (peano k)) rfl
          simpa [peano, LFTyping.nfApp] using
            (nfAppT_wrap_first_replay
              (hroot := nfAppT_var_fall_tc (peano fuelPred) (peano k) aPre)
              (fTerm := LF.Term.var k) (aTerm := aNF) (aVal := aVal)
              rfl hflift haenc halift haeval hPayloadReplay hFinalReplay)
      | con x =>
          unfold encTyCore? at hfenc
          cases hx : encName? x with
          | none => simp [hx] at hfenc
          | some k =>
              simp [hx] at hfenc
              subst fVal
              refine ⟨App (Con k) aVal, ?_⟩
              have hfenc' : encTyCore? (.con x) = some (Con k) := by
                unfold encTyCore?
                simp [hx]
              obtain ⟨hPayloadReplay, hFinalReplay⟩ :=
                hWrapReplay (fTerm := LF.Term.con x) (fAst := Con k) hfenc'
              simpa [peano, LFTyping.nfApp] using
                (nfAppT_wrap_first_replay
                  (hroot := nfAppT_con_fall_tc (peano fuelPred) k aPre)
                  (fTerm := LF.Term.con x) (aTerm := aNF) (aVal := aVal)
                  hfenc' hflift haenc halift haeval hPayloadReplay hFinalReplay)
      | pi A B =>
          simp [encTyCore?] at hfenc
          cases hA : encTyCore? A with
          | none => simp [hA] at hfenc
          | some AAst =>
              cases hB : encTyCore? B with
              | none => simp [hA, hB] at hfenc
              | some BAst =>
                  simp [hA, hB] at hfenc
                  subst fVal
                  refine ⟨App (Pi AAst BAst) aVal, ?_⟩
                  have hfenc' : encTyCore? (.pi A B) = some (Pi AAst BAst) := by
                    simp [encTyCore?, hA, hB]
                  obtain ⟨hPayloadReplay, hFinalReplay⟩ :=
                    hWrapReplay (fTerm := LF.Term.pi A B) (fAst := Pi AAst BAst) hfenc'
                  simpa [peano, LFTyping.nfApp] using
                    (nfAppT_wrap_first_replay
                      (hroot := nfAppT_pi_fall_tc (peano fuelPred) AAst BAst aPre)
                      (fTerm := LF.Term.pi A B) (aTerm := aNF) (aVal := aVal)
                      hfenc' hflift haenc halift haeval hPayloadReplay hFinalReplay)
      | lam A body =>
          simp [encTyCore?] at hfenc
          cases hA : encTyCore? A with
          | none => simp [hA] at hfenc
          | some AAst =>
              cases hbody : encTyCore? body with
              | none => simp [hA, hbody] at hfenc
              | some bodyAst =>
                  simp [hA, hbody] at hfenc
                  subst fVal
                  obtain ⟨resVal, hnext⟩ :=
                    hBeta (fuelPred := fuelPred) (A := A) (body := body)
                      (AAst := AAst) (bodyAst := bodyAst) rfl rfl hA hbody haReplay
                  refine ⟨resVal, ?_⟩
                  simpa [peano, LFTyping.nfApp, LFTyping.subst0] using
                    (nfAppT_beta_prepend_first_replay
                      (fuel := peano fuelPred) (A := AAst) (body := bodyAst)
                      (aPre := aPre) hnext)
      | app f a =>
          simp [encTyCore?] at hfenc
          cases hf : encTyCore? f with
          | none => simp [hf] at hfenc
          | some fAst =>
              cases ha : encTyCore? a with
              | none => simp [hf, ha] at hfenc
              | some aAst =>
                  simp [hf, ha] at hfenc
                  subst fVal
                  refine ⟨App (App fAst aAst) aVal, ?_⟩
                  have hfenc' : encTyCore? (.app f a) = some (App fAst aAst) := by
                    simp [encTyCore?, hf, ha]
                  obtain ⟨hPayloadReplay, hFinalReplay⟩ :=
                    hWrapReplay (fTerm := LF.Term.app f a) (fAst := App fAst aAst) hfenc'
                  simpa [peano, LFTyping.nfApp] using
                    (nfAppT_wrap_first_replay
                      (hroot := nfAppT_app_fall_tc (peano fuelPred) fAst aAst aPre)
                      (fTerm := LF.Term.app f a) (aTerm := aNF) (aVal := aVal)
                      hfenc' hflift haenc halift haeval hPayloadReplay hFinalReplay)

theorem substT_encTyCore_sim_tc :
    ∀ (body : LF.Term) (bodyAst : AST) (j : Nat) (sAst : AST) (sTerm : LF.Term),
      encTyCore? body = some bodyAst -> LiftablePayload sAst sTerm ->
        ∃ v N, encTyCore? (LFTyping.subst j sTerm body) = some v ∧
          eval pTC N (substT (peano j) sAst bodyAst) = v := by
  intro body
  induction body with
  | srt sort =>
      intro bodyAst j sAst sTerm h hs
      cases sort <;> simp [encTyCore?] at h <;> subst bodyAst
      · refine ⟨Srt typeS, 1, ?_, ?_⟩
        · simp [LFTyping.subst, encTyCore?]
        · exact substT_srt_tc (peano j) sAst typeS
      · refine ⟨Srt kindS, 1, ?_, ?_⟩
        · simp [LFTyping.subst, encTyCore?]
        · exact substT_srt_tc (peano j) sAst kindS
  | var k =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      subst bodyAst
      rcases hs.reduces with ⟨sVal, Ns, hsEnc, hsEval⟩
      have hsNorm : IsNormal pTC sVal := isnormal_encTyCore?_tc sTerm sVal hsEnc
      obtain ⟨Nsubst, hsubst⟩ := substT_var_payload_peano_tc j k sAst sVal hsNorm ⟨Ns, hsEval⟩
      by_cases hkj : k = j
      · refine ⟨sVal, Nsubst, ?_, ?_⟩
        · simpa [LFTyping.subst, hkj] using hsEnc
        · simpa [hkj] using hsubst
      · by_cases hlt : j < k
        · refine ⟨Var (peano (k - 1)), Nsubst, ?_, ?_⟩
          · simp [LFTyping.subst, encTyCore?, hkj, hlt]
          · simpa [hkj, hlt] using hsubst
        · refine ⟨Var (peano k), Nsubst, ?_, ?_⟩
          · simp [LFTyping.subst, encTyCore?, hkj, hlt]
          · simpa [hkj, hlt] using hsubst
  | con x =>
      intro bodyAst j sAst sTerm h hs
      unfold encTyCore? at h
      cases hx : encName? x with
      | none => simp [hx] at h
      | some k =>
          simp [hx] at h
          subst bodyAst
          refine ⟨Con k, 1, ?_, ?_⟩
          · simp [LFTyping.subst, encTyCore?, hx]
          · exact substT_con_tc (peano j) sAst k
  | pi A B ihA ihB =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hB : encTyCore? B with
          | none => simp [hA, hB] at h
          | some B' =>
              simp [hA, hB] at h
              subst bodyAst
              obtain ⟨Av, NA, hAenc, hAe⟩ := ihA A' j sAst sTerm hA hs
              obtain ⟨Bv, NB, hBenc, hBe⟩ := ihB B' (j + 1) (liftT (S Z) Z sAst)
                (LFTyping.lift 1 0 sTerm) hB (liftablePayload_lift1 hs)
              have hBcall : eval pTC NB
                  (substT (S (peano j)) (liftT (S Z) Z sAst) B') = Bv := by
                simpa [peano] using hBe
              have hBenc' : encTyCore? (LFTyping.subst (j + 1) (LFTyping.lift 1 0 sTerm) B) =
                  some Bv := hBenc
              have htail : ReducesToEncTyCore
                  (Pi (substT (peano j) sAst A') (substT (S (peano j)) (liftT (S Z) Z sAst) B'))
                  (.pi (LFTyping.subst j sTerm A)
                    (LFTyping.subst (j + 1) (LFTyping.lift 1 0 sTerm) B)) :=
                reduces_pi_tc ⟨Av, NA, hAenc, hAe⟩ ⟨Bv, NB, hBenc', hBcall⟩
              rcases htail with ⟨v, Ntail, henc, htailEval⟩
              refine ⟨v, 1 + Ntail, ?_, ?_⟩
              · simpa [LFTyping.subst, encTyCore?] using henc
              · have hstep : eval pTC 1 (substT (peano j) sAst (Pi A' B')) =
                    Pi (substT (peano j) sAst A')
                      (substT (S (peano j)) (liftT (S Z) Z sAst) B') := by
                  exact substT_pi_tc (peano j) sAst A' B'
                exact eval_trans_tc 1 Ntail _ _ _ hstep htailEval
  | lam A b ihA ihb =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hb : encTyCore? b with
          | none => simp [hA, hb] at h
          | some b' =>
              simp [hA, hb] at h
              subst bodyAst
              obtain ⟨Av, NA, hAenc, hAe⟩ := ihA A' j sAst sTerm hA hs
              obtain ⟨bv, NB, hbenc, hbe⟩ := ihb b' (j + 1) (liftT (S Z) Z sAst)
                (LFTyping.lift 1 0 sTerm) hb (liftablePayload_lift1 hs)
              have hbcall : eval pTC NB
                  (substT (S (peano j)) (liftT (S Z) Z sAst) b') = bv := by
                simpa [peano] using hbe
              have hbenc' : encTyCore? (LFTyping.subst (j + 1) (LFTyping.lift 1 0 sTerm) b) =
                  some bv := hbenc
              have htail : ReducesToEncTyCore
                  (Lam (substT (peano j) sAst A') (substT (S (peano j)) (liftT (S Z) Z sAst) b'))
                  (.lam (LFTyping.subst j sTerm A)
                    (LFTyping.subst (j + 1) (LFTyping.lift 1 0 sTerm) b)) :=
                reduces_lam_tc ⟨Av, NA, hAenc, hAe⟩ ⟨bv, NB, hbenc', hbcall⟩
              rcases htail with ⟨v, Ntail, henc, htailEval⟩
              refine ⟨v, 1 + Ntail, ?_, ?_⟩
              · simpa [LFTyping.subst, encTyCore?] using henc
              · have hstep : eval pTC 1 (substT (peano j) sAst (Lam A' b')) =
                    Lam (substT (peano j) sAst A')
                      (substT (S (peano j)) (liftT (S Z) Z sAst) b') := by
                  exact substT_lam_tc (peano j) sAst A' b'
                exact eval_trans_tc 1 Ntail _ _ _ hstep htailEval
  | app f a ihf iha =>
      intro bodyAst j sAst sTerm h hs
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              subst bodyAst
              obtain ⟨fv, NF, hfenc, hfe⟩ := ihf f' j sAst sTerm hf hs
              obtain ⟨av, NA, haenc, hae⟩ := iha a' j sAst sTerm ha hs
              have htail : ReducesToEncTyCore
                  (App (substT (peano j) sAst f') (substT (peano j) sAst a'))
                  (.app (LFTyping.subst j sTerm f) (LFTyping.subst j sTerm a)) :=
                reduces_app_tc ⟨fv, NF, hfenc, hfe⟩ ⟨av, NA, haenc, hae⟩
              rcases htail with ⟨v, Ntail, henc, htailEval⟩
              refine ⟨v, 1 + Ntail, ?_, ?_⟩
              · simpa [LFTyping.subst, encTyCore?] using henc
              · have hstep : eval pTC 1 (substT (peano j) sAst (App f' a')) =
                    App (substT (peano j) sAst f') (substT (peano j) sAst a') := by
                  exact substT_app_tc (peano j) sAst f' a'
                exact eval_trans_tc 1 Ntail _ _ _ hstep htailEval

theorem isnormal_encTy_tc (t : LF.Term) : IsNormal pTC (encTy t) := by
  unfold encTy encTy?
  cases h : encTyCore? (LFTyping.nf LFTyping.corpusSig checkerFuel t) with
  | none =>
      rfl
  | some u =>
      exact isnormal_encTyCore?_tc _ u h

theorem liftT_encTyCore_sim_tc :
    ∀ (t : LF.Term) (u : AST) (d c : Nat),
      encTyCore? t = some u ->
        ∃ v N, encTyCore? (LFTyping.lift d c t) = some v ∧
          eval pTC N (liftT (peano d) (peano c) u) = v := by
  intro t
  induction t with
  | srt sort =>
      intro u d c h
      cases sort <;> simp [encTyCore?] at h <;> subst u
      · exact ⟨Srt typeS, 1, rfl, liftT_srt_tc (peano d) (peano c) typeS⟩
      · exact ⟨Srt kindS, 1, rfl, liftT_srt_tc (peano d) (peano c) kindS⟩
  | var k =>
      intro u d c h
      simp [encTyCore?] at h
      subst u
      obtain ⟨N, hN⟩ := liftT_var_peano_tc d c k
      refine ⟨Var (peano (if k < c then k else k + d)), N, ?_, hN⟩
      simp [LFTyping.lift, encTyCore?]
  | con x =>
      intro u d c h
      unfold encTyCore? at h
      cases hx : encName? x with
      | none => simp [hx] at h
      | some k =>
          simp [hx] at h
          subst u
          refine ⟨Con k, 1, ?_, ?_⟩
          · simp [LFTyping.lift, encTyCore?, hx]
          · exact liftT_con_tc (peano d) (peano c) k
  | pi A B ihA ihB =>
      intro u d c h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hB : encTyCore? B with
          | none => simp [hA, hB] at h
          | some B' =>
              simp [hA, hB] at h
              subst u
              obtain ⟨Av, NA, hAlift, hAe⟩ := ihA A' d c hA
              obtain ⟨Bv, NB, hBlift, hBe⟩ := ihB B' d (Nat.succ c) hB
              have hBlift' : encTyCore? (LFTyping.lift d (c + 1) B) = some Bv := by
                rw [Nat.add_one]
                exact hBlift
              have hAnorm : IsNormal pTC Av :=
                isnormal_encTyCore?_tc (LFTyping.lift d c A) Av hAlift
              have hBnorm : IsNormal pTC Bv :=
                isnormal_encTyCore?_tc (LFTyping.lift d (c + 1) B) Bv hBlift'
              obtain ⟨MA, hMA⟩ :=
                cong_eval_tc (fun s => Pi s (liftT (peano d) (S (peano c)) B'))
                  (hcong_Pi1_tc (liftT (peano d) (S (peano c)) B')) NA hAe hAnorm
              obtain ⟨MB, hMB⟩ :=
                cong_eval_tc (fun s => Pi Av s) (hcong_Pi2_tc Av hAnorm) NB hBe hBnorm
              refine ⟨Pi Av Bv, (1 + MA) + MB, ?_, ?_⟩
              · change encTyCore? (.pi (LFTyping.lift d c A) (LFTyping.lift d (c + 1) B)) =
                  some (Pi Av Bv)
                simp only [encTyCore?, hAlift, hBlift']
              · have hstep : eval pTC 1 (liftT (peano d) (peano c) (Pi A' B')) =
                    Pi (liftT (peano d) (peano c) A') (liftT (peano d) (S (peano c)) B') := by
                  exact liftT_pi_tc (peano d) (peano c) A' B'
                have hleft := eval_trans_tc 1 MA _ _ _ hstep hMA
                exact eval_trans_tc (1 + MA) MB _ _ _ hleft hMB
  | lam A b ihA ihb =>
      intro u d c h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hb : encTyCore? b with
          | none => simp [hA, hb] at h
          | some b' =>
              simp [hA, hb] at h
              subst u
              obtain ⟨Av, NA, hAlift, hAe⟩ := ihA A' d c hA
              obtain ⟨bv, NB, hblift, hbe⟩ := ihb b' d (Nat.succ c) hb
              have hblift' : encTyCore? (LFTyping.lift d (c + 1) b) = some bv := by
                rw [Nat.add_one]
                exact hblift
              have hAnorm : IsNormal pTC Av :=
                isnormal_encTyCore?_tc (LFTyping.lift d c A) Av hAlift
              have hbnorm : IsNormal pTC bv :=
                isnormal_encTyCore?_tc (LFTyping.lift d (c + 1) b) bv hblift'
              obtain ⟨MA, hMA⟩ :=
                cong_eval_tc (fun s => Lam s (liftT (peano d) (S (peano c)) b'))
                  (hcong_Lam1_tc (liftT (peano d) (S (peano c)) b')) NA hAe hAnorm
              obtain ⟨MB, hMB⟩ :=
                cong_eval_tc (fun s => Lam Av s) (hcong_Lam2_tc Av hAnorm) NB hbe hbnorm
              refine ⟨Lam Av bv, (1 + MA) + MB, ?_, ?_⟩
              · change encTyCore? (.lam (LFTyping.lift d c A) (LFTyping.lift d (c + 1) b)) =
                  some (Lam Av bv)
                simp only [encTyCore?, hAlift, hblift']
              · have hstep : eval pTC 1 (liftT (peano d) (peano c) (Lam A' b')) =
                    Lam (liftT (peano d) (peano c) A') (liftT (peano d) (S (peano c)) b') := by
                  exact liftT_lam_tc (peano d) (peano c) A' b'
                have hleft := eval_trans_tc 1 MA _ _ _ hstep hMA
                exact eval_trans_tc (1 + MA) MB _ _ _ hleft hMB
  | app f a ihf iha =>
      intro u d c h
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              subst u
              obtain ⟨fv, NF, hflift, hfe⟩ := ihf f' d c hf
              obtain ⟨av, NA, halift, hae⟩ := iha a' d c ha
              have hfnorm : IsNormal pTC fv :=
                isnormal_encTyCore?_tc (LFTyping.lift d c f) fv hflift
              have hanorm : IsNormal pTC av :=
                isnormal_encTyCore?_tc (LFTyping.lift d c a) av halift
              obtain ⟨MF, hMF⟩ :=
                cong_eval_tc (fun s => App s (liftT (peano d) (peano c) a'))
                  (hcong_App1_tc (liftT (peano d) (peano c) a')) NF hfe hfnorm
              obtain ⟨MA, hMA⟩ :=
                cong_eval_tc (fun s => App fv s) (hcong_App2_tc fv hfnorm) NA hae hanorm
              refine ⟨App fv av, (1 + MF) + MA, ?_, ?_⟩
              · change encTyCore? (.app (LFTyping.lift d c f) (LFTyping.lift d c a)) =
                  some (App fv av)
                simp only [encTyCore?, hflift, halift]
              · have hstep : eval pTC 1 (liftT (peano d) (peano c) (App f' a')) =
                    App (liftT (peano d) (peano c) f') (liftT (peano d) (peano c) a') := by
                  exact liftT_app_tc (peano d) (peano c) f' a'
                have hleft := eval_trans_tc 1 MF _ _ _ hstep hMF
                exact eval_trans_tc (1 + MF) MA _ _ _ hleft hMA

/-! ## Interning simulation leaves. -/

inductive InternActiveShape : AST -> Prop where
  | term (t : AST) : InternActiveShape (internTerm t)
  | pi1 (B s : AST) : InternActiveShape (internPi1 B s)
  | pi2 (A s : AST) : InternActiveShape (internPi2 A s)
  | lam1 (b s : AST) : InternActiveShape (internLam1 b s)
  | lam2 (A s : AST) : InternActiveShape (internLam2 A s)
  | app1 (a s : AST) : InternActiveShape (internApp1 a s)
  | app2 (f s : AST) : InternActiveShape (internApp2 f s)

inductive MatchesIntern : Option AST -> AST -> Prop where
  | success {u v : AST} : v = someT u -> MatchesIntern (some u) v
  | failure {v : AST} : v = checkBad -> MatchesIntern none v

inductive FirstActiveIntern (r : Option AST) (call : AST) : Prop where
  | intro {N : Nat} :
      MatchesIntern r (eval pTC N call) ->
      (∀ k, k < N -> InternActiveShape (eval pTC k call)) ->
      FirstActiveIntern r call

theorem intern_con_success_sim {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) :
    ∃ N, eval pTC N (internTerm (Con (con0 x))) = someT u := by
  by_cases h0 : x = "prop"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h1 : x = "nat"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h2 : x = "A"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h3 : x = "B"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h4 : x = "z"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h5 : x = "prf"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h6 : x = "imp"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h7 : x = "eqn"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h8 : x = "rfl"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h9 : x = "hImpAB"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h10 : x = "hA"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  by_cases h11 : x = "mpAB"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact ⟨1, rfl⟩
  simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
    Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at h

theorem isnormal_raw_con_success_tc {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) :
    IsNormal pTC (Con (con0 x)) := by
  by_cases h0 : x = "prop"
  · subst x
    exact isnormal_Con_tc (con0 "prop") (isnormal_con0_tc "prop")
  by_cases h1 : x = "nat"
  · subst x
    exact isnormal_Con_tc (con0 "nat") (isnormal_con0_tc "nat")
  by_cases h2 : x = "A"
  · subst x
    exact isnormal_Con_tc (con0 "A") (isnormal_con0_tc "A")
  by_cases h3 : x = "B"
  · subst x
    exact isnormal_Con_tc (con0 "B") (isnormal_con0_tc "B")
  by_cases h4 : x = "z"
  · subst x
    exact isnormal_Con_tc (con0 "z") (isnormal_con0_tc "z")
  by_cases h5 : x = "prf"
  · subst x
    exact isnormal_Con_tc (con0 "prf") (isnormal_con0_tc "prf")
  by_cases h6 : x = "imp"
  · subst x
    exact isnormal_Con_tc (con0 "imp") (isnormal_con0_tc "imp")
  by_cases h7 : x = "eqn"
  · subst x
    exact isnormal_Con_tc (con0 "eqn") (isnormal_con0_tc "eqn")
  by_cases h8 : x = "rfl"
  · subst x
    exact isnormal_Con_tc (con0 "rfl") (isnormal_con0_tc "rfl")
  by_cases h9 : x = "hImpAB"
  · subst x
    exact isnormal_Con_tc (con0 "hImpAB") (isnormal_con0_tc "hImpAB")
  by_cases h10 : x = "hA"
  · subst x
    exact isnormal_Con_tc (con0 "hA") (isnormal_con0_tc "hA")
  by_cases h11 : x = "mpAB"
  · subst x
    exact isnormal_Con_tc (con0 "mpAB") (isnormal_con0_tc "mpAB")
  simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
    Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at h

theorem isnormal_encTerm_success_tc : ∀ (t : LF.Term) (u : AST),
    encTyCore? t = some u -> IsNormal pTC (encTerm t) := by
  intro t
  induction t with
  | srt s =>
      intro _ _
      cases s <;> exact isnormal_Srt_tc _ (isnormal_con0_tc _)
  | var k =>
      intro _ _
      exact isnormal_Var_tc (peano k) (isnormal_peano_tc k)
  | con x =>
      intro u h
      exact isnormal_raw_con_success_tc h
  | pi A B ihA ihB =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hB : encTyCore? B with
          | none => simp [hA, hB] at h
          | some B' =>
              exact isnormal_Pi_tc (encTerm A) (encTerm B) (ihA A' hA) (ihB B' hB)
  | lam A b ihA ihb =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hb : encTyCore? b with
          | none => simp [hA, hb] at h
          | some b' =>
              exact isnormal_Lam_tc (encTerm A) (encTerm b) (ihA A' hA) (ihb b' hb)
  | app f a ihf iha =>
      intro u h
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              exact isnormal_App_tc (encTerm f) (encTerm a) (ihf f' hf) (iha a' ha)

theorem hcong_internPi1_active_tc (B : AST) (hB : IsNormal pTC B) :
    ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (internPi1 B s) = some (internPi1 B s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (internPi1 B s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hB
  change (match baseReducts pTC (internPi1 B s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "internPi1") args') (oneStepList pTC [B, s])) =
      some (internPi1 B s')
  rw [hb]
  simp only [oneStepList, hB, hstep, Option.map_some, internPi1]

theorem hcong_internPi2_active_tc (A : AST) (hA : IsNormal pTC A) :
    ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (internPi2 A s) = some (internPi2 A s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (internPi2 A s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hA
  change (match baseReducts pTC (internPi2 A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "internPi2") args') (oneStepList pTC [A, s])) =
      some (internPi2 A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, internPi2]

theorem hcong_internLam1_active_tc (b : AST) (hb' : IsNormal pTC b) :
    ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (internLam1 b s) = some (internLam1 b s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (internLam1 b s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hb'
  change (match baseReducts pTC (internLam1 b s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "internLam1") args') (oneStepList pTC [b, s])) =
      some (internLam1 b s')
  rw [hb]
  simp only [oneStepList, hb', hstep, Option.map_some, internLam1]

theorem hcong_internLam2_active_tc (A : AST) (hA : IsNormal pTC A) :
    ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (internLam2 A s) = some (internLam2 A s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (internLam2 A s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hA
  change (match baseReducts pTC (internLam2 A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "internLam2") args') (oneStepList pTC [A, s])) =
      some (internLam2 A s')
  rw [hb]
  simp only [oneStepList, hA, hstep, Option.map_some, internLam2]

theorem hcong_internApp1_active_tc (a : AST) (ha : IsNormal pTC a) :
    ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (internApp1 a s) = some (internApp1 a s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (internApp1 a s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at ha
  change (match baseReducts pTC (internApp1 a s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "internApp1") args') (oneStepList pTC [a, s])) =
      some (internApp1 a s')
  rw [hb]
  simp only [oneStepList, ha, hstep, Option.map_some, internApp1]

theorem hcong_internApp2_active_tc (f : AST) (hf : IsNormal pTC f) :
    ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (internApp2 f s) = some (internApp2 f s') := by
  intro s s' hs hstep
  have hb : baseReducts pTC (internApp2 f s) = [] := by
    cases hs <;> rfl
  simp only [IsNormal] at hf
  change (match baseReducts pTC (internApp2 f s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "internApp2") args') (oneStepList pTC [f, s])) =
      some (internApp2 f s')
  rw [hb]
  simp only [oneStepList, hf, hstep, Option.map_some, internApp2]

theorem cong_eval_intern_active (F : AST -> AST)
    (hcong : ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pTC N s = v ->
      (∀ k, k < N -> InternActiveShape (eval pTC k s)) ->
        ∃ M, eval pTC M (F s) = F v := by
  intro N
  induction N with
  | zero =>
      intro s v h _
      simp only [eval] at h
      subst h
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro s v h hguard
      simp only [eval] at h
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at h
          have hsactive : InternActiveShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguard' : ∀ k, k < n -> InternActiveShape (eval pTC k s') := by
            intro k hk
            have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
            simpa only [eval, hstep] using hguard (k + 1) hk'
          obtain ⟨M, hM⟩ := ih h hguard'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsactive hstep]
          exact hM

theorem cong_eval_intern_active_with_guard (F : AST -> AST)
    (hwrap : ∀ s, InternActiveShape s -> InternActiveShape (F s))
    (hcong : ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pTC N s = v ->
      (∀ k, k < N -> InternActiveShape (eval pTC k s)) ->
        ∃ M, eval pTC M (F s) = F v ∧
          ∀ k, k < M -> InternActiveShape (eval pTC k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v h _
      simp only [eval] at h
      subst h
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v h hguard
      simp only [eval] at h
      cases hstep : oneStep pTC s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at h
          have hsactive : InternActiveShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguard' : ∀ k, k < n -> InternActiveShape (eval pTC k s') := by
            intro k hk
            have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
            simpa only [eval, hstep] using hguard (k + 1) hk'
          obtain ⟨M, hM, hMguard⟩ := ih h hguard'
          refine ⟨M + 1, ?_, ?_⟩
          · simp only [eval, hcong s s' hsactive hstep]
            exact hM
          · intro k hk
            cases k with
            | zero =>
                simpa only [eval] using hwrap s hsactive
            | succ k =>
                have hkM : k < M := by
                  exact Nat.succ_lt_succ_iff.mp (by
                    simpa only [Nat.add_one] using hk)
                have htotal : eval pTC (Nat.succ k) (F s) = eval pTC k (F s') := by
                  simp only [eval, hcong s s' hsactive hstep]
                rw [htotal]
                exact hMguard k hkM

theorem first_active_intern_prepend {r : Option AST} {call next : AST}
    (hstep : eval pTC 1 call = next) (hactive : InternActiveShape call)
    (hnext : FirstActiveIntern r next) : FirstActiveIntern r call := by
  cases hnext with
  | intro hmatch hguard =>
      rename_i N
      refine FirstActiveIntern.intro (N := 1 + N) ?_ ?_
      · have htotal : eval pTC (1 + N) call = eval pTC N next :=
          eval_trans_tc 1 N call next (eval pTC N next) hstep rfl
        rw [htotal]
        exact hmatch
      · intro k hk
        cases k with
        | zero =>
            simpa only [eval] using hactive
        | succ k =>
            have hk' : Nat.succ k < Nat.succ N := by
              simpa only [Nat.one_add] using hk
            have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
            have htotal : eval pTC (Nat.succ k) call = eval pTC k next := by
              have h := eval_trans_tc 1 k call next (eval pTC k next) hstep rfl
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            rw [htotal]
            exact hguard k hkN

theorem first_active_intern_bind_active {r q : Option AST} {call : AST}
    (F : AST -> AST)
    (hwrap : ∀ s, InternActiveShape s -> InternActiveShape (F s))
    (hcong : ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (F s) = some (F s'))
    (hfirst : FirstActiveIntern r call)
    (hend : ∀ {v : AST}, MatchesIntern r v -> FirstActiveIntern q (F v)) :
    FirstActiveIntern q (F call) := by
  cases hfirst with
  | intro hchild hguard =>
      rename_i Nchild
      obtain ⟨Mctx, hMctx, hMguard⟩ :=
        cong_eval_intern_active_with_guard F hwrap hcong Nchild rfl hguard
      have hend' := hend hchild
      cases hend' with
      | intro hendMatch hendGuard =>
          rename_i Nend
          refine FirstActiveIntern.intro (N := Mctx + Nend) ?_ ?_
          · have htotal : eval pTC (Mctx + Nend) (F call)
                = eval pTC Nend (F (eval pTC Nchild call)) :=
              eval_trans_tc Mctx Nend _ _ _ hMctx rfl
            rw [htotal]
            exact hendMatch
          · intro k hk
            by_cases hkctx : k < Mctx
            · exact hMguard k hkctx
            · have hge : Mctx ≤ k := Nat.le_of_not_gt hkctx
              let j := k - Mctx
              have hjlt : j < Nend := by
                exact Nat.sub_lt_left_of_lt_add hge hk
              have hkdecomp : k = Mctx + j := by
                exact (Nat.add_sub_of_le hge).symm
              subst j
              rw [hkdecomp]
              have htotal : eval pTC (Mctx + (k - Mctx)) (F call)
                    = eval pTC (k - Mctx) (F (eval pTC Nchild call)) :=
                eval_trans_tc Mctx (k - Mctx) _ _ _ hMctx rfl
              rw [htotal]
              exact hendGuard (k - Mctx) hjlt

theorem first_active_intern_one_success {call u : AST}
    (hstep : eval pTC 1 call = someT u) (hactive : InternActiveShape call) :
    FirstActiveIntern (some u) call := by
  refine FirstActiveIntern.intro (N := 1) ?_ ?_
  · rw [hstep]
    exact MatchesIntern.success rfl
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simpa only [eval] using hactive

theorem intern_con_success_first_active {x : String} {u : AST}
    (h : encTyCore? (.con x) = some u) :
    FirstActiveIntern (some u) (internTerm (Con (con0 x))) := by
  by_cases h0 : x = "prop"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "prop")))
  by_cases h1 : x = "nat"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "nat")))
  by_cases h2 : x = "A"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "A")))
  by_cases h3 : x = "B"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "B")))
  by_cases h4 : x = "z"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "z")))
  by_cases h5 : x = "prf"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "prf")))
  by_cases h6 : x = "imp"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "imp")))
  by_cases h7 : x = "eqn"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "eqn")))
  by_cases h8 : x = "rfl"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "rfl")))
  by_cases h9 : x = "hImpAB"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "hImpAB")))
  by_cases h10 : x = "hA"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "hA")))
  by_cases h11 : x = "mpAB"
  · subst x
    simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
      Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable] at h
    subst u
    exact first_active_intern_one_success rfl (InternActiveShape.term (Con (con0 "mpAB")))
  simp [encTyCore?, encName?, Mettapedia.GSLT.InternedNames.Table.intern?,
    Mettapedia.GSLT.InternedNames.Table.internAux, lfNameTable,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at h

theorem internTerm_success_first_active : ∀ (t : LF.Term) (u : AST),
    encTyCore? t = some u -> FirstActiveIntern (some u) (internTerm (encTerm t)) := by
  intro t
  induction t with
  | srt s =>
      intro u h
      cases s <;> simp [encTyCore?] at h <;> subst u
      · exact first_active_intern_one_success rfl (InternActiveShape.term (Srt typeS))
      · exact first_active_intern_one_success rfl (InternActiveShape.term (Srt kindS))
  | var k =>
      intro u h
      simp [encTyCore?] at h
      subst u
      exact first_active_intern_one_success rfl (InternActiveShape.term (Var (peano k)))
  | con x =>
      intro u h
      exact intern_con_success_first_active h
  | pi A B ihA ihB =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hB : encTyCore? B with
          | none => simp [hA, hB] at h
          | some B' =>
              simp [hA, hB] at h
              subst u
              have hfirstA := ihA A' hA
              have hfirstB := ihB B' hB
              have hBraw : IsNormal pTC (encTerm B) := isnormal_encTerm_success_tc B B' hB
              have hAnorm : IsNormal pTC A' := isnormal_encTyCore?_tc A A' hA
              exact first_active_intern_prepend
                (call := internTerm (Pi (encTerm A) (encTerm B)))
                (next := internPi1 (encTerm B) (internTerm (encTerm A)))
                rfl (InternActiveShape.term (Pi (encTerm A) (encTerm B)))
                (first_active_intern_bind_active
                  (fun s => internPi1 (encTerm B) s)
                  (fun s _ => InternActiveShape.pi1 (encTerm B) s)
                  (hcong_internPi1_active_tc (encTerm B) hBraw)
                  hfirstA
                  (by
                    intro v hv
                    cases hv with
                    | success hv =>
                        subst v
                        have hwrappedB := first_active_intern_bind_active
                          (fun s => internPi2 A' s)
                          (fun s _ => InternActiveShape.pi2 A' s)
                          (hcong_internPi2_active_tc A' hAnorm)
                          hfirstB
                          (by
                            intro v hv
                            cases hv with
                            | success hv =>
                                subst v
                                exact first_active_intern_one_success rfl
                                  (InternActiveShape.pi2 A' (someT B')))
                        exact first_active_intern_prepend rfl
                          (InternActiveShape.pi1 (encTerm B) (someT A')) hwrappedB))
  | lam A b ihA ihb =>
      intro u h
      simp [encTyCore?] at h
      cases hA : encTyCore? A with
      | none => simp [hA] at h
      | some A' =>
          cases hb : encTyCore? b with
          | none => simp [hA, hb] at h
          | some b' =>
              simp [hA, hb] at h
              subst u
              have hfirstA := ihA A' hA
              have hfirstb := ihb b' hb
              have hbraw : IsNormal pTC (encTerm b) := isnormal_encTerm_success_tc b b' hb
              have hAnorm : IsNormal pTC A' := isnormal_encTyCore?_tc A A' hA
              exact first_active_intern_prepend
                (call := internTerm (Lam (encTerm A) (encTerm b)))
                (next := internLam1 (encTerm b) (internTerm (encTerm A)))
                rfl (InternActiveShape.term (Lam (encTerm A) (encTerm b)))
                (first_active_intern_bind_active
                  (fun s => internLam1 (encTerm b) s)
                  (fun s _ => InternActiveShape.lam1 (encTerm b) s)
                  (hcong_internLam1_active_tc (encTerm b) hbraw)
                  hfirstA
                  (by
                    intro v hv
                    cases hv with
                    | success hv =>
                        subst v
                        have hwrappedb := first_active_intern_bind_active
                          (fun s => internLam2 A' s)
                          (fun s _ => InternActiveShape.lam2 A' s)
                          (hcong_internLam2_active_tc A' hAnorm)
                          hfirstb
                          (by
                            intro v hv
                            cases hv with
                            | success hv =>
                                subst v
                                exact first_active_intern_one_success rfl
                                  (InternActiveShape.lam2 A' (someT b')))
                        exact first_active_intern_prepend rfl
                          (InternActiveShape.lam1 (encTerm b) (someT A')) hwrappedb))
  | app f a ihf iha =>
      intro u h
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              subst u
              have hfirstf := ihf f' hf
              have hfirsta := iha a' ha
              have haraw : IsNormal pTC (encTerm a) := isnormal_encTerm_success_tc a a' ha
              have hfnorm : IsNormal pTC f' := isnormal_encTyCore?_tc f f' hf
              exact first_active_intern_prepend
                (call := internTerm (App (encTerm f) (encTerm a)))
                (next := internApp1 (encTerm a) (internTerm (encTerm f)))
                rfl (InternActiveShape.term (App (encTerm f) (encTerm a)))
                (first_active_intern_bind_active
                  (fun s => internApp1 (encTerm a) s)
                  (fun s _ => InternActiveShape.app1 (encTerm a) s)
                  (hcong_internApp1_active_tc (encTerm a) haraw)
                  hfirstf
                  (by
                    intro v hv
                    cases hv with
                    | success hv =>
                        subst v
                        have hwrappeda := first_active_intern_bind_active
                          (fun s => internApp2 f' s)
                          (fun s _ => InternActiveShape.app2 f' s)
                          (hcong_internApp2_active_tc f' hfnorm)
                          hfirsta
                          (by
                            intro v hv
                            cases hv with
                            | success hv =>
                                subst v
                                exact first_active_intern_one_success rfl
                                  (InternActiveShape.app2 f' (someT a')))
                        exact first_active_intern_prepend rfl
                          (InternActiveShape.app1 (encTerm a) (someT f')) hwrappeda))

theorem internTerm_success_sim {t : LF.Term} {u : AST}
    (h : encTyCore? t = some u) :
    ∃ N, eval pTC N (internTerm (encTerm t)) = someT u := by
  have hfirst := internTerm_success_first_active t u h
  cases hfirst with
  | intro hmatch hguard =>
      rename_i N
      refine ⟨N, ?_⟩
      cases hmatch with
      | success hv => exact hv

theorem baseReducts_lfcheckI_enc_active_tc : ∀ (Araw : LF.Term) (A s : AST),
    encTyCore? Araw = some A -> InternActiveShape s ->
      baseReducts pTC (lfcheckI A s) = [] := by
  intro Araw
  induction Araw with
  | srt sort =>
      intro A s h hs
      cases sort <;> simp [encTyCore?] at h <;> subst A <;> cases hs <;> rfl
  | var k =>
      intro A s h hs
      simp [encTyCore?] at h
      subst A
      cases hs <;> rfl
  | con x =>
      intro A s h hs
      unfold encTyCore? encName? at h
      cases hname : Mettapedia.GSLT.InternedNames.Table.intern? lfNameTable x with
      | none => simp [hname] at h
      | some k =>
          simp [hname] at h
          subst A
          cases hs <;> rfl
  | pi T U ihT ihU =>
      intro A s h hs
      simp [encTyCore?] at h
      cases hT : encTyCore? T with
      | none => simp [hT] at h
      | some T' =>
          cases hU : encTyCore? U with
          | none => simp [hT, hU] at h
          | some U' =>
              simp [hT, hU] at h
              subst A
              cases hs <;> rfl
  | lam T b ihT ihb =>
      intro A s h hs
      simp [encTyCore?] at h
      cases hT : encTyCore? T with
      | none => simp [hT] at h
      | some T' =>
          cases hb : encTyCore? b with
          | none => simp [hT, hb] at h
          | some b' =>
              simp [hT, hb] at h
              subst A
              cases hs <;> rfl
  | app f a ihf iha =>
      intro A s h hs
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              subst A
              cases hs <;> rfl

theorem hcong_lfcheckI_enc_active_tc {Araw : LF.Term} {A : AST}
    (hA : encTyCore? Araw = some A) :
    ∀ s s', InternActiveShape s -> oneStep pTC s = some s' ->
      oneStep pTC (lfcheckI A s) = some (lfcheckI A s') := by
  intro s s' hs hstep
  have hb := baseReducts_lfcheckI_enc_active_tc Araw A s hA hs
  have hAnorm : IsNormal pTC A := isnormal_encTyCore?_tc Araw A hA
  simp only [IsNormal] at hAnorm
  change (match baseReducts pTC (lfcheckI A s) with
    | r :: _ => some r
    | [] => Option.map (fun args' => AST.sexp (.id "lfcheckI") args') (oneStepList pTC [A, s])) =
      some (lfcheckI A s')
  rw [hb]
  simp only [oneStepList, hAnorm, hstep, Option.map_some, lfcheckI]

theorem lfcheckI_ok_enc_tc : ∀ (Araw : LF.Term) (A t : AST),
    encTyCore? Araw = some A ->
      eval pTC 1 (lfcheckI A (someT t)) = verdict (checkT checkerFuelA Nil t A) := by
  intro Araw
  induction Araw with
  | srt sort =>
      intro A t h
      cases sort <;> simp [encTyCore?] at h <;> subst A <;> rfl
  | var k =>
      intro A t h
      simp [encTyCore?] at h
      subst A
      rfl
  | con x =>
      intro A t h
      unfold encTyCore? encName? at h
      cases hname : Mettapedia.GSLT.InternedNames.Table.intern? lfNameTable x with
      | none => simp [hname] at h
      | some k =>
          simp [hname] at h
          subst A
          rfl
  | pi T U ihT ihU =>
      intro A t h
      simp [encTyCore?] at h
      cases hT : encTyCore? T with
      | none => simp [hT] at h
      | some T' =>
          cases hU : encTyCore? U with
          | none => simp [hT, hU] at h
          | some U' =>
              simp [hT, hU] at h
              subst A
              rfl
  | lam T b ihT ihb =>
      intro A t h
      simp [encTyCore?] at h
      cases hT : encTyCore? T with
      | none => simp [hT] at h
      | some T' =>
          cases hb : encTyCore? b with
          | none => simp [hT, hb] at h
          | some b' =>
              simp [hT, hb] at h
              subst A
              rfl
  | app f a ihf iha =>
      intro A t h
      simp [encTyCore?] at h
      cases hf : encTyCore? f with
      | none => simp [hf] at h
      | some f' =>
          cases ha : encTyCore? a with
          | none => simp [hf, ha] at h
          | some a' =>
              simp [hf, ha] at h
              subst A
              rfl

theorem lfcheckI_intern_success_to_checkT {Araw : LF.Term} {A raw t : AST}
    (hA : encTyCore? Araw = some A)
    (hfirst : FirstActiveIntern (some t) (internTerm raw)) :
    ∃ N, eval pTC N (lfcheckI A (internTerm raw)) = verdict (checkT checkerFuelA Nil t A) := by
  cases hfirst with
  | intro hmatch hguard =>
      rename_i Nchild
      obtain ⟨Mctx, hMctx⟩ :=
        cong_eval_intern_active (fun s => lfcheckI A s)
          (hcong_lfcheckI_enc_active_tc hA) Nchild rfl hguard
      cases hmatch with
      | success hv =>
          have hMctx' : eval pTC Mctx (lfcheckI A (internTerm raw)) = lfcheckI A (someT t) := by
            rw [hMctx, hv]
          have hstep : eval pTC 1 (lfcheckI A (someT t)) = verdict (checkT checkerFuelA Nil t A) :=
            lfcheckI_ok_enc_tc Araw A t hA
          refine ⟨Mctx + 1, ?_⟩
          exact eval_trans_tc Mctx 1 _ _ _ hMctx' hstep

theorem lfcheckI_encTerms_to_checkT {Araw traw : LF.Term} {A t : AST}
    (hA : encTyCore? Araw = some A) (ht : encTyCore? traw = some t) :
    ∃ N, eval pTC N (lfcheckI A (internTerm (encTerm traw))) =
      verdict (checkT checkerFuelA Nil t A) := by
  exact lfcheckI_intern_success_to_checkT hA (internTerm_success_first_active traw t ht)

theorem lfcheckK_ok_encTerms_to_checkT {Araw traw : LF.Term} {A t : AST}
    (hA : encTyCore? Araw = some A) (ht : encTyCore? traw = some t) :
    ∃ N, eval pTC N (lfcheckK A (Ok (encTerm traw))) =
      verdict (checkT checkerFuelA Nil t A) := by
  obtain ⟨N, hN⟩ := lfcheckI_encTerms_to_checkT hA ht
  refine ⟨1 + N, ?_⟩
  have hstep : eval pTC 1 (lfcheckK A (Ok (encTerm traw))) =
      lfcheckI A (internTerm (encTerm traw)) := by
    rfl
  exact eval_trans_tc 1 N _ _ _ hstep hN

/-! ## End-to-end assembly statements. -/

def PipelineSimStatement : Prop :=
  ∀ toks A_spec, ∃ N,
    MatchesCheckVerdict (referencePipeline toks A_spec)
      (eval pTC N
        (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks) (encTy A_spec)))

def LFCheckKPipelineInterface : Prop :=
  ∀ toks A_spec, ∃ N,
    MatchesCheckVerdict (referencePipeline toks A_spec)
      (eval pTC N
        (lfcheckK (encTy A_spec)
          (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))))

def LFRecParserTCInterface : Prop :=
  ∀ toks, ∃ N,
    (match LF.recognize 64 toks with
    | none =>
        ∃ e, eval pTC N
          (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)) = Err e
    | some t =>
        eval pTC N
          (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)) = Ok (encTerm t)) ∧
      ∀ k, k < N ->
        LFCheckKChildOpenShape
          (eval pTC k (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)))

def LFRecRawParserTCInterface : Prop :=
  ∀ toks, ∃ N,
    (match LF.pTerm 64 [] toks with
    | none =>
        ∃ e, eval pTC N
          (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)) = Err e
    | some (t, rest) =>
        match rest with
        | [] =>
            ∃ raw,
              Mettapedia.GSLT.LanguageDef.LFParserSim.ShiftablePayload raw t ∧
                eval pTC N
                  (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)) = Ok raw
        | _ :: _ =>
            ∃ e, eval pTC N
              (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)) = Err e) ∧
      ∀ k, k < N ->
        LFCheckKChildOpenShape
          (eval pTC k (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)))

def FirstActiveMatchesParseShiftableTC (r : Option (LF.Term × List LF.Tok))
    (call : AST) : Prop :=
  ∃ N,
    Mettapedia.GSLT.LanguageDef.LFParserSim.MatchesParseShiftable r (eval pTC N call) ∧
      ∀ k, k < N ->
        Mettapedia.GSLT.LanguageDef.LFParserSim.ParserActiveShape (eval pTC k call)

def LFParserTermFirstActiveShiftableTCInterface : Prop :=
  ∀ toks,
    FirstActiveMatchesParseShiftableTC (LF.pTerm 64 [] toks)
      (tm (peano 64) Nil (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))

theorem lfrec_raw_parser_tc_of_first_active_shiftable_tc
    (hparser : LFParserTermFirstActiveShiftableTCInterface) :
    LFRecRawParserTCInterface := by
  intro toks
  let toksAst := Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks
  let call := tm (peano 64) Nil toksAst
  obtain ⟨Nchild, hchild, hchildGuard⟩ := hparser toks
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_recK_active_with_guard Nchild (s := call) (v := eval pTC Nchild call)
      rfl hchildGuard
  have hlfstep : eval pTC 1 (lfrec toksAst) = recK call := by
    rfl
  have hlfGuard :
      ∀ k, k < 1 + (Mctx + 1) ->
        LFCheckKChildOpenShape (eval pTC k (lfrec toksAst)) := by
    intro k hk
    cases k with
    | zero =>
        simpa only [eval] using LFCheckKChildOpenShape.recCall toksAst
    | succ k =>
        have hkBound : k < Mctx + 1 := by
          exact Nat.succ_lt_succ_iff.mp (by simpa only [Nat.one_add] using hk)
        have hshift : eval pTC (Nat.succ k) (lfrec toksAst) =
            eval pTC k (recK call) := by
          have h := eval_trans_tc 1 k (lfrec toksAst) (recK call)
            (eval pTC k (recK call)) hlfstep rfl
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
        rw [hshift]
        by_cases hkM : k < Mctx
        · exact hMguard k hkM
        · have hge : Mctx ≤ k := Nat.le_of_not_gt hkM
          have hle : k ≤ Mctx := Nat.le_of_lt_succ hkBound
          have hkEq : k = Mctx := Nat.le_antisymm hle hge
          subst k
          rw [hMctx]
          exact LFCheckKChildOpenShape.recKCall (eval pTC Nchild call)
  cases hterm : LF.pTerm 64 [] toks with
  | none =>
      simp [Mettapedia.GSLT.LanguageDef.LFParserSim.MatchesParseShiftable, hterm] at hchild
      obtain ⟨e, hv⟩ := hchild
      refine ⟨1 + (Mctx + 1), ?_, hlfGuard⟩
      refine ⟨e, ?_⟩
      have hend : eval pTC 1 (recK (eval pTC Nchild call)) = Err e := by
        rw [hv]
        rfl
      have hrecK :
          eval pTC (Mctx + 1) (recK call) = Err e :=
        eval_trans_tc Mctx 1 _ _ _ hMctx hend
      exact eval_trans_tc 1 (Mctx + 1) _ _ _ hlfstep hrecK
  | some pr =>
      rcases pr with ⟨t, rest⟩
      cases rest with
      | nil =>
          simp [Mettapedia.GSLT.LanguageDef.LFParserSim.MatchesParseShiftable, hterm] at hchild
          obtain ⟨raw, hv, hraw⟩ := hchild
          refine ⟨1 + (Mctx + 1), ?_, hlfGuard⟩
          refine ⟨raw, hraw, ?_⟩
          have hend : eval pTC 1 (recK (eval pTC Nchild call)) = Ok raw := by
            rw [hv]
            rfl
          have hrecK :
              eval pTC (Mctx + 1) (recK call) = Ok raw :=
            eval_trans_tc Mctx 1 _ _ _ hMctx hend
          exact eval_trans_tc 1 (Mctx + 1) _ _ _ hlfstep hrecK
      | cons tok restTail =>
          simp [Mettapedia.GSLT.LanguageDef.LFParserSim.MatchesParseShiftable, hterm] at hchild
          obtain ⟨raw, hv, _hraw⟩ := hchild
          let err := extraToks
            (Cons (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encTok tok)
              (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks restTail))
          refine ⟨1 + (Mctx + 1), ?_, hlfGuard⟩
          refine ⟨err, ?_⟩
          have hend : eval pTC 1 (recK (eval pTC Nchild call)) = Err err := by
            rw [hv]
            rfl
          have hrecK :
              eval pTC (Mctx + 1) (recK call) = Err err :=
            eval_trans_tc Mctx 1 _ _ _ hMctx hend
          exact eval_trans_tc 1 (Mctx + 1) _ _ _ hlfstep hrecK

def LFCheckKParserContextInterface : Prop :=
  ∀ toks A, IsNormal pTC A -> ∃ N,
    match LF.recognize 64 toks with
    | none =>
        ∃ e, eval pTC N
          (lfcheckK A (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
            lfcheckK A (Err e)
    | some t =>
        eval pTC N
          (lfcheckK A (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
            lfcheckK A (Ok (encTerm t))

def LFCheckKRawParserContextInterface : Prop :=
  ∀ toks A, IsNormal pTC A -> ∃ N,
    match LF.pTerm 64 [] toks with
    | none =>
        ∃ e, eval pTC N
          (lfcheckK A (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
            lfcheckK A (Err e)
    | some (t, rest) =>
        match rest with
        | [] =>
            ∃ raw,
              Mettapedia.GSLT.LanguageDef.LFParserSim.ShiftablePayload raw t ∧
                eval pTC N
                  (lfcheckK A
                    (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
                  lfcheckK A (Ok raw)
        | _ :: _ =>
            ∃ e, eval pTC N
              (lfcheckK A (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
                lfcheckK A (Err e)

theorem lfcheckK_parser_context_of_lfrec_tc
    (hrec : LFRecParserTCInterface) : LFCheckKParserContextInterface := by
  intro toks A hA
  obtain ⟨Nrec, hrecMatch, hrecGuard⟩ := hrec toks
  cases hparse : LF.recognize 64 toks with
  | none =>
      simp [hparse] at hrecMatch
      obtain ⟨e, hrecEval⟩ := hrecMatch
      obtain ⟨M, hM⟩ :=
        cong_eval_lfcheckK_child_open_with_guard A hA Nrec hrecEval hrecGuard
      refine ⟨M, ?_⟩
      simp
      exact ⟨e, hM⟩
  | some t =>
      simp [hparse] at hrecMatch
      obtain ⟨M, hM⟩ :=
        cong_eval_lfcheckK_child_open_with_guard A hA Nrec hrecMatch hrecGuard
      refine ⟨M, ?_⟩
      simp
      exact hM

theorem lfcheckK_raw_parser_context_of_lfrec_raw_tc
    (hrec : LFRecRawParserTCInterface) : LFCheckKRawParserContextInterface := by
  intro toks A hA
  obtain ⟨Nrec, hrecMatch, hrecGuard⟩ := hrec toks
  cases hterm : LF.pTerm 64 [] toks with
  | none =>
      simp [hterm] at hrecMatch
      obtain ⟨e, hrecEval⟩ := hrecMatch
      obtain ⟨M, hM⟩ :=
        cong_eval_lfcheckK_child_open_with_guard A hA Nrec hrecEval hrecGuard
      refine ⟨M, ?_⟩
      simp
      exact ⟨e, hM⟩
  | some pr =>
      rcases pr with ⟨t, rest⟩
      cases rest with
      | nil =>
          simp [hterm] at hrecMatch
          obtain ⟨raw, hraw, hrecEval⟩ := hrecMatch
          obtain ⟨M, hM⟩ :=
            cong_eval_lfcheckK_child_open_with_guard A hA Nrec hrecEval hrecGuard
          refine ⟨M, ?_⟩
          simp
          exact ⟨raw, hraw, hM⟩
      | cons tok restTail =>
          simp [hterm] at hrecMatch
          obtain ⟨e, hrecEval⟩ := hrecMatch
          obtain ⟨M, hM⟩ :=
            cong_eval_lfcheckK_child_open_with_guard A hA Nrec hrecEval hrecGuard
          refine ⟨M, ?_⟩
          simp
          exact ⟨e, hM⟩

def LFCheckKSuccessInterface : Prop :=
  ∀ t A_spec, ∃ N,
    MatchesCheckVerdict (some (LFTyping.check checkerFuel LFTyping.corpusSig [] t A_spec))
      (eval pTC N (lfcheckK (encTy A_spec) (Ok (encTerm t))))

def LFCheckKRawSuccessInterface : Prop :=
  ∀ t A_spec raw,
    Mettapedia.GSLT.LanguageDef.LFParserSim.ShiftablePayload raw t ->
      ∃ N,
        MatchesCheckVerdict (some (LFTyping.check checkerFuel LFTyping.corpusSig [] t A_spec))
          (eval pTC N (lfcheckK (encTy A_spec) (Ok raw)))

def LFCheckIRawSuccessInterface : Prop :=
  ∀ t A_spec raw,
    Mettapedia.GSLT.LanguageDef.LFParserSim.ShiftablePayload raw t ->
      ∃ N,
        MatchesCheckVerdict (some (LFTyping.check checkerFuel LFTyping.corpusSig [] t A_spec))
          (eval pTC N (lfcheckI (encTy A_spec) (internTerm raw)))

theorem lfcheckK_raw_success_of_lfcheckI_raw_success
    (hcheckI : LFCheckIRawSuccessInterface) : LFCheckKRawSuccessInterface := by
  intro t A_spec raw hraw
  obtain ⟨N, hN⟩ := hcheckI t A_spec raw hraw
  refine ⟨1 + N, ?_⟩
  have hstep :
      eval pTC 1 (lfcheckK (encTy A_spec) (Ok raw)) =
        lfcheckI (encTy A_spec) (internTerm raw) := by
    rfl
  have htotal :
      eval pTC (1 + N) (lfcheckK (encTy A_spec) (Ok raw)) =
        eval pTC N (lfcheckI (encTy A_spec) (internTerm raw)) := by
    exact eval_trans_tc 1 N _ _ _ hstep rfl
  rw [htotal]
  exact hN

theorem lfcheckK_pipeline_interface_of_parser_and_checker
    (hparser : LFCheckKParserContextInterface)
    (hcheck : LFCheckKSuccessInterface) : LFCheckKPipelineInterface := by
  intro toks A_spec
  obtain ⟨Nparser, hparserN⟩ := hparser toks (encTy A_spec) (isnormal_encTy_tc A_spec)
  cases hrec : LF.recognize 64 toks with
  | none =>
      simp [hrec] at hparserN
      obtain ⟨e, hparserEval⟩ := hparserN
      refine ⟨Nparser + 1, ?_⟩
      have herr :
          eval pTC 1 (lfcheckK (encTy A_spec) (Err e)) = checkErr e := by
        rfl
      have htotal :
          eval pTC (Nparser + 1)
              (lfcheckK (encTy A_spec)
                (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
            checkErr e := by
        exact eval_trans_tc Nparser 1 _ _ _ hparserEval herr
      unfold referencePipeline
      simp [hrec, htotal]
      exact MatchesCheckVerdict.rejectParse rfl
  | some t =>
      simp [hrec] at hparserN
      obtain ⟨Ncheck, hcheckN⟩ := hcheck t A_spec
      refine ⟨Nparser + Ncheck, ?_⟩
      have htotal :
          eval pTC (Nparser + Ncheck)
              (lfcheckK (encTy A_spec)
                (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
            eval pTC Ncheck (lfcheckK (encTy A_spec) (Ok (encTerm t))) := by
        exact eval_trans_tc Nparser Ncheck _ _ _ hparserN rfl
      unfold referencePipeline
      simp [hrec]
      rw [htotal]
      exact hcheckN

theorem lfcheckK_pipeline_interface_of_raw_parser_and_checker
    (hparser : LFCheckKRawParserContextInterface)
    (hcheck : LFCheckKRawSuccessInterface) : LFCheckKPipelineInterface := by
  intro toks A_spec
  obtain ⟨Nparser, hparserN⟩ := hparser toks (encTy A_spec) (isnormal_encTy_tc A_spec)
  cases hterm : LF.pTerm 64 [] toks with
  | none =>
      simp [hterm] at hparserN
      obtain ⟨e, hparserEval⟩ := hparserN
      refine ⟨Nparser + 1, ?_⟩
      have herr :
          eval pTC 1 (lfcheckK (encTy A_spec) (Err e)) = checkErr e := by
        rfl
      have htotal :
          eval pTC (Nparser + 1)
              (lfcheckK (encTy A_spec)
                (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
            checkErr e := by
        exact eval_trans_tc Nparser 1 _ _ _ hparserEval herr
      unfold referencePipeline
      simp [LF.recognize, hterm, htotal]
      exact MatchesCheckVerdict.rejectParse rfl
  | some pr =>
      rcases pr with ⟨t, rest⟩
      cases rest with
      | nil =>
          simp [hterm] at hparserN
          obtain ⟨raw, hraw, hparserEval⟩ := hparserN
          obtain ⟨Ncheck, hcheckN⟩ := hcheck t A_spec raw hraw
          refine ⟨Nparser + Ncheck, ?_⟩
          have htotal :
              eval pTC (Nparser + Ncheck)
                  (lfcheckK (encTy A_spec)
                    (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
                eval pTC Ncheck (lfcheckK (encTy A_spec) (Ok raw)) := by
            exact eval_trans_tc Nparser Ncheck _ _ _ hparserEval rfl
          unfold referencePipeline
          simp [LF.recognize, hterm]
          rw [htotal]
          exact hcheckN
      | cons tok restTail =>
          simp [hterm] at hparserN
          obtain ⟨e, hparserEval⟩ := hparserN
          refine ⟨Nparser + 1, ?_⟩
          have herr :
              eval pTC 1 (lfcheckK (encTy A_spec) (Err e)) = checkErr e := by
            rfl
          have htotal :
              eval pTC (Nparser + 1)
                  (lfcheckK (encTy A_spec)
                    (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) =
                checkErr e := by
            exact eval_trans_tc Nparser 1 _ _ _ hparserEval herr
          unfold referencePipeline
          simp [LF.recognize, hterm, htotal]
          exact MatchesCheckVerdict.rejectParse rfl

theorem pipeline_sim_from_lfcheckK_interface
    (hK : LFCheckKPipelineInterface) : PipelineSimStatement := by
  intro toks A_spec
  obtain ⟨N, hN⟩ := hK toks A_spec
  refine ⟨1 + N, ?_⟩
  have hstep :
      eval pTC 1
          (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks) (encTy A_spec)) =
        lfcheckK (encTy A_spec)
          (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks)) := by
    rfl
  have htotal :
      eval pTC (1 + N)
          (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks) (encTy A_spec)) =
        eval pTC N
          (lfcheckK (encTy A_spec)
            (lfrec (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks))) := by
    exact eval_trans_tc 1 N _ _ _ hstep rfl
  rw [htotal]
  exact hN

theorem pipeline_sim_from_parser_and_checker_interfaces
    (hparser : LFCheckKParserContextInterface)
    (hcheck : LFCheckKSuccessInterface) : PipelineSimStatement :=
  pipeline_sim_from_lfcheckK_interface
    (lfcheckK_pipeline_interface_of_parser_and_checker hparser hcheck)

theorem pipeline_sim_from_raw_parser_and_checker_interfaces
    (hparser : LFCheckKRawParserContextInterface)
    (hcheck : LFCheckKRawSuccessInterface) : PipelineSimStatement :=
  pipeline_sim_from_lfcheckK_interface
    (lfcheckK_pipeline_interface_of_raw_parser_and_checker hparser hcheck)

theorem pipeline_sim_from_raw_parser_and_lfcheckI_interfaces
    (hparser : LFCheckKRawParserContextInterface)
    (hcheckI : LFCheckIRawSuccessInterface) : PipelineSimStatement :=
  pipeline_sim_from_raw_parser_and_checker_interfaces hparser
    (lfcheckK_raw_success_of_lfcheckI_raw_success hcheckI)

theorem pipeline_sim_from_lfrec_raw_and_lfcheckI_interfaces
    (hrec : LFRecRawParserTCInterface)
    (hcheckI : LFCheckIRawSuccessInterface) : PipelineSimStatement :=
  pipeline_sim_from_raw_parser_and_lfcheckI_interfaces
    (lfcheckK_raw_parser_context_of_lfrec_raw_tc hrec) hcheckI

theorem pipeline_sim_from_parser_first_active_and_lfcheckI_interfaces
    (hparser : LFParserTermFirstActiveShiftableTCInterface)
    (hcheckI : LFCheckIRawSuccessInterface) : PipelineSimStatement :=
  pipeline_sim_from_lfrec_raw_and_lfcheckI_interfaces
    (lfrec_raw_parser_tc_of_first_active_shiftable_tc hparser) hcheckI

theorem pipeline_sim
    (hparser : LFParserTermFirstActiveShiftableTCInterface)
    (hcheckI : LFCheckIRawSuccessInterface) :
    ∀ toks A_spec, ∃ N,
      MatchesCheckVerdict (referencePipeline toks A_spec)
        (eval pTC N
          (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks toks) (encTy A_spec))) :=
  pipeline_sim_from_parser_first_active_and_lfcheckI_interfaces hparser hcheckI

def AcceptedIsDerivableStatement : Prop :=
  ∀ toks A_spec, EngineAccepts toks A_spec ->
    ∃ t, LFTyping.HasType LFTyping.corpusSig [] t A_spec

def EngineAcceptsReferenceSound : Prop :=
  ∀ toks A_spec, EngineAccepts toks A_spec -> referencePipeline toks A_spec = some true

theorem engine_accepts_reference_sound_from_pipeline
    (hpipeline : PipelineSimStatement) : EngineAcceptsReferenceSound := by
  intro toks A_spec hacc
  cases hacc with
  | intro haccept =>
      obtain ⟨_, hpipe⟩ := hpipeline toks A_spec
      cases href : referencePipeline toks A_spec with
      | none =>
          rw [href] at hpipe
          cases hpipe with
          | rejectParse hreject =>
              exact False.elim (eval_reject_accept_false_tc haccept hreject)
      | some b =>
          cases b with
          | false =>
              rw [href] at hpipe
              cases hpipe with
              | rejectFalse hreject =>
                  exact False.elim (eval_reject_accept_false_tc haccept hreject)
          | true =>
              rfl

theorem accepted_is_derivable_from_reference_sound
    (hsound : EngineAcceptsReferenceSound) : AcceptedIsDerivableStatement := by
  intro toks A_spec hacc
  have href := hsound toks A_spec hacc
  unfold referencePipeline at href
  cases hrec : LF.recognize 64 toks with
  | none =>
      simp [hrec] at href
  | some t =>
      simp [hrec] at href
      exact ⟨t, LFTyping.S1 (fuel := checkerFuel) href⟩

theorem accepted_is_derivable_from_pipeline
    (hpipeline : PipelineSimStatement) : AcceptedIsDerivableStatement :=
  accepted_is_derivable_from_reference_sound
    (engine_accepts_reference_sound_from_pipeline hpipeline)

theorem accepted_is_derivable
    (hparser : LFParserTermFirstActiveShiftableTCInterface)
    (hcheckI : LFCheckIRawSuccessInterface) :
    ∀ toks A_spec, EngineAccepts toks A_spec ->
      ∃ t, LFTyping.HasType LFTyping.corpusSig [] t A_spec :=
  accepted_is_derivable_from_pipeline (pipeline_sim hparser hcheckI)

/-! ## Positive and negative corpus instances through the composed pipeline. -/

def idProofToksLF : List LF.Tok :=
  [.lam, .id "h", .colon, .id "prf", .id "A", .dot, .id "h"]

theorem idProof_parse :
    LF.recognize 64 idProofToksLF = some LFTyping.idProof := by
  decide

def mpProofToksLF : List LF.Tok :=
  [.id "mpAB", .id "hImpAB", .id "hA"]

theorem mpProof_parse :
    LF.recognize 64 mpProofToksLF = some LFTyping.mpProof := by
  decide

theorem corpus_rfl_pipeline_matches :
    MatchesCheckVerdict (referencePipeline LF.cToks1 LFTyping.rflZTy)
      (eval pTC 1000
        (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks LF.cToks1)
          (encTy LFTyping.rflZTy))) := by
  simp [referencePipeline, checkerFuel, LF.corr1]
  exact MatchesCheckVerdict.accept lfcheck_rflZ_engine

theorem corpus_id_pipeline_matches :
    MatchesCheckVerdict (referencePipeline idProofToksLF LFTyping.idProofTy)
      (eval pTC 2500
        (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks idProofToksLF)
          (encTy LFTyping.idProofTy))) := by
  simp [referencePipeline, checkerFuel, idProof_parse]
  apply MatchesCheckVerdict.accept
  change eval pTC 2500 (lfcheck idProofToks (encTy LFTyping.idProofTy)) = checkOk
  exact lfcheck_id_engine

theorem corpus_mp_pipeline_matches :
    MatchesCheckVerdict (referencePipeline mpProofToksLF LFTyping.mpProofTy)
      (eval pTC 2500
        (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks mpProofToksLF)
          (encTy LFTyping.mpProofTy))) := by
  simp [referencePipeline, checkerFuel, mpProof_parse]
  apply MatchesCheckVerdict.accept
  change eval pTC 2500 (lfcheck mpProofToks (encTy LFTyping.mpProofTy)) = checkOk
  exact lfcheck_mp_engine

theorem corpus_bad_rfl_pipeline_matches :
    MatchesCheckVerdict (referencePipeline LF.cToks1 LFTyping.badRflTy)
      (eval pTC 1000
        (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks LF.cToks1)
          (encTy LFTyping.badRflTy))) := by
  simp [referencePipeline, checkerFuel, LF.corr1]
  exact MatchesCheckVerdict.rejectFalse lfcheck_bad_rfl_engine

theorem corpus_bad_parse_pipeline_matches :
    MatchesCheckVerdict (referencePipeline LF.cToks8 LFTyping.rflZTy)
      (eval pTC 1000
        (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks LF.cToks8)
          (encTy LFTyping.rflZTy))) := by
  rw [referencePipeline, LF.corr8]
  exact MatchesCheckVerdict.rejectParse lfcheck_bad_parse_engine

theorem corpus_rfl_accepted_is_derivable :
    EngineAccepts LF.cToks1 LFTyping.rflZTy ->
      ∃ t, LFTyping.HasType LFTyping.corpusSig [] t LFTyping.rflZTy := by
  intro _
  exact ⟨LFTyping.rflZ, LFTyping.corpus_rfl_sound⟩

theorem corpus_id_accepted_is_derivable :
    EngineAccepts idProofToksLF LFTyping.idProofTy ->
      ∃ t, LFTyping.HasType LFTyping.corpusSig [] t LFTyping.idProofTy := by
  intro _
  exact ⟨LFTyping.idProof, LFTyping.corpus_id_sound⟩

theorem corpus_mp_accepted_is_derivable :
    EngineAccepts mpProofToksLF LFTyping.mpProofTy ->
      ∃ t, LFTyping.HasType LFTyping.corpusSig [] t LFTyping.mpProofTy := by
  intro _
  exact ⟨LFTyping.mpProof, LFTyping.corpus_mp_sound⟩

/-! ## Boundary/reference normalization regression. -/

def typeOnlyToksLF : List LF.Tok := [.type]

def betaDiscardUnknownTy : LF.Term :=
  .app (.lam (.srt .type) (.srt .kind)) (.con "unknown")

theorem regression_reference_accepts_beta_discard_unknown :
    referencePipeline typeOnlyToksLF betaDiscardUnknownTy = some true := by
  rfl

theorem regression_encTy_beta_discard_unknown :
    encTy betaDiscardUnknownTy = Srt kindS := by
  rfl

theorem regression_engine_accepts_beta_discard_unknown :
    eval pTC 1000
      (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks typeOnlyToksLF)
        (encTy betaDiscardUnknownTy)) = checkOk := by
  rfl

theorem regression_beta_discard_pipeline_matches :
    MatchesCheckVerdict (referencePipeline typeOnlyToksLF betaDiscardUnknownTy)
      (eval pTC 1000
        (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks typeOnlyToksLF)
          (encTy betaDiscardUnknownTy))) := by
  rw [regression_reference_accepts_beta_discard_unknown]
  exact MatchesCheckVerdict.accept regression_engine_accepts_beta_discard_unknown

theorem regression_beta_discard_accepted_is_derivable :
    EngineAccepts typeOnlyToksLF betaDiscardUnknownTy ->
      ∃ t, LFTyping.HasType LFTyping.corpusSig [] t betaDiscardUnknownTy := by
  intro _
  exact ⟨.srt .type, LFTyping.S1 (fuel := checkerFuel) (by rfl)⟩

#print axioms pipeline_sim_from_lfcheckK_interface
#print axioms hcong_Ok_tc
#print axioms isnormal_encTerm_raw_tc
#print axioms cong_eval_recK_active_with_guard
#print axioms cong_eval_lfcheckK_child_open_with_guard
#print axioms lfrec_raw_parser_tc_of_first_active_shiftable_tc
#print axioms lfcheckK_parser_context_of_lfrec_tc
#print axioms lfcheckK_raw_parser_context_of_lfrec_raw_tc
#print axioms lfcheckK_pipeline_interface_of_parser_and_checker
#print axioms pipeline_sim_from_parser_and_checker_interfaces
#print axioms lfcheckK_raw_success_of_lfcheckI_raw_success
#print axioms lfcheckK_pipeline_interface_of_raw_parser_and_checker
#print axioms pipeline_sim_from_raw_parser_and_checker_interfaces
#print axioms pipeline_sim_from_raw_parser_and_lfcheckI_interfaces
#print axioms pipeline_sim_from_lfrec_raw_and_lfcheckI_interfaces
#print axioms pipeline_sim_from_parser_first_active_and_lfcheckI_interfaces
#print axioms pipeline_sim
#print axioms engine_accepts_reference_sound_from_pipeline
#print axioms accepted_is_derivable_from_reference_sound
#print axioms accepted_is_derivable_from_pipeline
#print axioms accepted_is_derivable
#print axioms corpus_mp_pipeline_matches
#print axioms regression_reference_accepts_beta_discard_unknown
#print axioms regression_engine_accepts_beta_discard_unknown
#print axioms regression_beta_discard_pipeline_matches
#print axioms regression_beta_discard_accepted_is_derivable

end Mettapedia.GSLT.LanguageDef.LFCheckerSim
