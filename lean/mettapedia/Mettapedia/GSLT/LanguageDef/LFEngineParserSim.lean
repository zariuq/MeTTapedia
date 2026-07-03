/-
# E2b-universal — parser-result bricks for the LF recognizer simulation

This file starts the parser layer above `shift_sim` / `resolve_sim`.  It lands reusable
normal-form and context-congruence lemmas for encoded tokens and parser result shapes, plus the
first leaf simulations for `lf-atom` (`id`, `Type`, and no-fuel).  These are the bottom parser
bricks needed by the eventual mutual `parser_sim` / `lfrec_sim` theorem.

Integrity: 0 sorry / 0 native_decide.
-/
import Mettapedia.GSLT.LanguageDef.LFEngineResolveSim

namespace Mettapedia.GSLT.LanguageDef.LFParserSim

open MeTTaIL Mettapedia.GSLT.LanguageDef.LFEnc Mettapedia.GSLT.LanguageDef.LFUniv
open Mettapedia.GSLT.LanguageDef.LFEngineCorr (encSrt encTok encToks encTerm MatchesVerdict)
open Mettapedia.GSLT.LanguageDef.LFResolveSim
  (encCtx resolve_sim ctxidx_sim encIdx isnormal_encIdx Good good_cong_eval hdesc_resolveK)
open Mettapedia.GSLT.LanguageDef.LFShiftSim
  (eval_trans cong_eval isnormal_con0 isnormal_peano isnormal_encTerm isnormal_sexp1
    isnormal_sexp2 hcong_pi1 hcong_pi2 hcong_lam1 hcong_lam2 hcong_app1 hcong_app2
    shift_sim os_sh_srt os_sh_con os_sh_var os_sh_pi os_sh_lam os_sh_app
    os_shv_lt_ss os_shv_lt_zs os_shv_lt_zz os_shv_lt_sz os_shv_tt os_shv_ff)

set_option maxRecDepth 8000

/-! ## Parser-result correspondence relation -/

/-- Engine parser result `v` agrees with a Lean `Option (Term × rest)` result. -/
def MatchesParse : Option (LF.Term × List LF.Tok) → AST → Prop
  | some (t, rest), v => v = Pp (encTerm t) (encToks rest)
  | none, v => ∃ e, v = PErr e

theorem matches_parse_some (t : LF.Term) (rest : List LF.Tok) :
    MatchesParse (some (t, rest)) (Pp (encTerm t) (encToks rest)) := rfl

theorem matches_parse_none (e : AST) : MatchesParse none (PErr e) := ⟨e, rfl⟩

/-! ## Raw parser-result correspondence

The parser continuations are intentionally call-by-name in their term payloads: for example
`at-id` emits `(P (resolve ctx s) rest)`, and `apmK-p` may consume that `P` before `resolve`
normalizes.  The raw relation records exactly that operational state; a boundary lemma below
normalizes the payload under `P` when an exact `MatchesParse` fact is needed.
-/

def ReducesToEncTerm (u : AST) (t : LF.Term) : Prop :=
  ∃ N, eval pLF N u = encTerm t

def MatchesParseRaw : Option (LF.Term × List LF.Tok) → AST → Prop
  | some (t, rest), v => ∃ u, v = Pp u (encToks rest) ∧ ReducesToEncTerm u t
  | none, v => ∃ e, v = PErr e

def ParserResultShape : AST → Prop
  | .sexp (.id "P") [_, _] => True
  | .sexp (.id "PErr") [_] => True
  | _ => False

def FirstMatchesParseRaw (r : Option (LF.Term × List LF.Tok)) (call : AST) : Prop :=
  ∃ N, MatchesParseRaw r (eval pLF N call) ∧
    ∀ k, k < N → ¬ ParserResultShape (eval pLF k call)

inductive ParserActiveShape : AST → Prop where
  | tm (f ctx toks : AST) : ParserActiveShape (tm f ctx toks)
  | ar (f ctx toks : AST) : ParserActiveShape (ar f ctx toks)
  | ap (f ctx toks : AST) : ParserActiveShape (ap f ctx toks)
  | apm (f ctx acc toks : AST) : ParserActiveShape (apm f ctx acc toks)
  | atom (f ctx toks : AST) : ParserActiveShape (at' f ctx toks)
  | tmPi1 (f ctx x r : AST) : ParserActiveShape (tmPi1 f ctx x r)
  | tmPi2 (A r : AST) : ParserActiveShape (tmPi2 A r)
  | tmLam1 (f ctx x r : AST) : ParserActiveShape (tmLam1 f ctx x r)
  | tmLam2 (A r : AST) : ParserActiveShape (tmLam2 A r)
  | arK (f ctx r : AST) : ParserActiveShape (arK f ctx r)
  | arK2 (a r : AST) : ParserActiveShape (arK2 a r)
  | apK (f ctx r : AST) : ParserActiveShape (apK f ctx r)
  | apmK (f ctx acc toks r : AST) : ParserActiveShape (apmK f ctx acc toks r)
  | atLPk (f ctx r : AST) : ParserActiveShape (atLPk f ctx r)

def FirstActiveMatchesParseRaw (r : Option (LF.Term × List LF.Tok)) (call : AST) : Prop :=
  ∃ N, MatchesParseRaw r (eval pLF N call) ∧
    ∀ k, k < N → ParserActiveShape (eval pLF k call)

theorem first_matches_to_raw {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (h : FirstMatchesParseRaw r call) :
    ∃ N, MatchesParseRaw r (eval pLF N call) := by
  rcases h with ⟨N, hN, _⟩
  exact ⟨N, hN⟩

theorem first_active_to_raw {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (h : FirstActiveMatchesParseRaw r call) :
    ∃ N, MatchesParseRaw r (eval pLF N call) := by
  rcases h with ⟨N, hN, _⟩
  exact ⟨N, hN⟩

theorem first_matches_zero {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (h : MatchesParseRaw r call) : FirstMatchesParseRaw r call := by
  refine ⟨0, ?_, ?_⟩
  · simpa only [eval] using h
  · intro k hk
    exact False.elim (Nat.not_lt_zero k hk)

theorem first_matches_one {r : Option (LF.Term × List LF.Tok)} {call v : AST}
    (hstep : eval pLF 1 call = v) (h : MatchesParseRaw r v)
    (hnot : ¬ ParserResultShape call) : FirstMatchesParseRaw r call := by
  refine ⟨1, ?_, ?_⟩
  · rw [hstep]
    exact h
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simpa only [eval] using hnot

theorem first_matches_prepend {r : Option (LF.Term × List LF.Tok)} {call next : AST}
    (hstep : eval pLF 1 call = next) (hnot : ¬ ParserResultShape call)
    (hnext : FirstMatchesParseRaw r next) : FirstMatchesParseRaw r call := by
  rcases hnext with ⟨N, hN, hguard⟩
  refine ⟨1 + N, ?_, ?_⟩
  · have htotal : eval pLF (1 + N) call = eval pLF N next :=
      eval_trans pLF 1 N call next (eval pLF N next) hstep rfl
    rw [htotal]
    exact hN
  · intro k hk
    cases k with
    | zero =>
        simpa only [eval] using hnot
    | succ k =>
        have hk' : Nat.succ k < Nat.succ N := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using hk
        have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
        have htotal : eval pLF (Nat.succ k) call = eval pLF k next := by
          have h := eval_trans pLF 1 k call next (eval pLF k next) hstep rfl
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
        rw [htotal]
        exact hguard k hkN

theorem first_active_zero {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (h : MatchesParseRaw r call) : FirstActiveMatchesParseRaw r call := by
  refine ⟨0, ?_, ?_⟩
  · simpa only [eval] using h
  · intro k hk
    exact False.elim (Nat.not_lt_zero k hk)

theorem first_active_one {r : Option (LF.Term × List LF.Tok)} {call v : AST}
    (hstep : eval pLF 1 call = v) (h : MatchesParseRaw r v)
    (hactive : ParserActiveShape call) : FirstActiveMatchesParseRaw r call := by
  refine ⟨1, ?_, ?_⟩
  · rw [hstep]
    exact h
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simpa only [eval] using hactive

theorem first_active_prepend {r : Option (LF.Term × List LF.Tok)} {call next : AST}
    (hstep : eval pLF 1 call = next) (hactive : ParserActiveShape call)
    (hnext : FirstActiveMatchesParseRaw r next) : FirstActiveMatchesParseRaw r call := by
  rcases hnext with ⟨N, hN, hguard⟩
  refine ⟨1 + N, ?_, ?_⟩
  · have htotal : eval pLF (1 + N) call = eval pLF N next :=
      eval_trans pLF 1 N call next (eval pLF N next) hstep rfl
    rw [htotal]
    exact hN
  · intro k hk
    cases k with
    | zero =>
        simpa only [eval] using hactive
    | succ k =>
        have hk' : Nat.succ k < Nat.succ N := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using hk
        have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
        have htotal : eval pLF (Nat.succ k) call = eval pLF k next := by
          have h := eval_trans pLF 1 k call next (eval pLF k next) hstep rfl
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
        rw [htotal]
        exact hguard k hkN

theorem first_active_prepend_eval {r : Option (LF.Term × List LF.Tok)} {call next : AST}
    {M : Nat} (hstep : eval pLF M call = next)
    (hguard : ∀ k, k < M → ParserActiveShape (eval pLF k call))
    (hnext : FirstActiveMatchesParseRaw r next) : FirstActiveMatchesParseRaw r call := by
  rcases hnext with ⟨N, hN, hnextGuard⟩
  refine ⟨M + N, ?_, ?_⟩
  · have htotal : eval pLF (M + N) call = eval pLF N next :=
      eval_trans pLF M N call next (eval pLF N next) hstep rfl
    rw [htotal]
    exact hN
  · intro k hk
    by_cases hkM : k < M
    · exact hguard k hkM
    · have hge : M ≤ k := Nat.le_of_not_gt hkM
      let j := k - M
      have hjN : j < N := by
        omega
      have hk_eq : k = M + j := by
        omega
      have hshift : eval pLF k call = eval pLF j next := by
        have htotal : eval pLF (M + j) call = eval pLF j next :=
          eval_trans pLF M j call next (eval pLF j next) hstep rfl
        simpa [hk_eq] using htotal
      rw [hshift]
      exact hnextGuard j hjN

theorem not_result_tm (f ctx toks : AST) : ¬ ParserResultShape (tm f ctx toks) := by
  intro h
  exact h

theorem not_result_ar (f ctx toks : AST) : ¬ ParserResultShape (ar f ctx toks) := by
  intro h
  exact h

theorem not_result_ap (f ctx toks : AST) : ¬ ParserResultShape (ap f ctx toks) := by
  intro h
  exact h

theorem not_result_apm (f ctx acc toks : AST) : ¬ ParserResultShape (apm f ctx acc toks) := by
  intro h
  exact h

theorem not_result_at (f ctx toks : AST) : ¬ ParserResultShape (at' f ctx toks) := by
  intro h
  exact h

theorem not_result_tmPi1 (f ctx x r : AST) : ¬ ParserResultShape (tmPi1 f ctx x r) := by
  intro h
  exact h

theorem not_result_tmPi2 (A r : AST) : ¬ ParserResultShape (tmPi2 A r) := by
  intro h
  exact h

theorem not_result_tmLam1 (f ctx x r : AST) : ¬ ParserResultShape (tmLam1 f ctx x r) := by
  intro h
  exact h

theorem not_result_tmLam2 (A r : AST) : ¬ ParserResultShape (tmLam2 A r) := by
  intro h
  exact h

theorem not_result_arK (f ctx r : AST) : ¬ ParserResultShape (arK f ctx r) := by
  intro h
  exact h

theorem not_result_arK2 (a r : AST) : ¬ ParserResultShape (arK2 a r) := by
  intro h
  exact h

theorem not_result_apK (f ctx r : AST) : ¬ ParserResultShape (apK f ctx r) := by
  intro h
  exact h

theorem not_result_apmK (f ctx acc toks r : AST) :
    ¬ ParserResultShape (apmK f ctx acc toks r) := by
  intro h
  exact h

theorem not_result_atLPk (f ctx r : AST) : ¬ ParserResultShape (atLPk f ctx r) := by
  intro h
  exact h

theorem parser_active_not_result {s : AST} (h : ParserActiveShape s) :
    ¬ ParserResultShape s := by
  cases h with
  | tm f ctx toks => exact not_result_tm f ctx toks
  | ar f ctx toks => exact not_result_ar f ctx toks
  | ap f ctx toks => exact not_result_ap f ctx toks
  | apm f ctx acc toks => exact not_result_apm f ctx acc toks
  | atom f ctx toks => exact not_result_at f ctx toks
  | tmPi1 f ctx x r => exact not_result_tmPi1 f ctx x r
  | tmPi2 A r => exact not_result_tmPi2 A r
  | tmLam1 f ctx x r => exact not_result_tmLam1 f ctx x r
  | tmLam2 A r => exact not_result_tmLam2 A r
  | arK f ctx r => exact not_result_arK f ctx r
  | arK2 a r => exact not_result_arK2 a r
  | apK f ctx r => exact not_result_apK f ctx r
  | apmK f ctx acc toks r => exact not_result_apmK f ctx acc toks r
  | atLPk f ctx r => exact not_result_atLPk f ctx r

theorem first_active_to_first {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (h : FirstActiveMatchesParseRaw r call) :
    FirstMatchesParseRaw r call := by
  rcases h with ⟨N, hN, hactive⟩
  exact ⟨N, hN, fun k hk => parser_active_not_result (hactive k hk)⟩

theorem reduces_encTerm_refl (t : LF.Term) : ReducesToEncTerm (encTerm t) t := ⟨0, rfl⟩

theorem matches_parse_raw_some (t : LF.Term) (rest : List LF.Tok) :
    MatchesParseRaw (some (t, rest)) (Pp (encTerm t) (encToks rest)) :=
  ⟨encTerm t, rfl, reduces_encTerm_refl t⟩

theorem matches_parse_raw_some_of_reduces {u : AST} {t : LF.Term} (rest : List LF.Tok)
    (hu : ReducesToEncTerm u t) : MatchesParseRaw (some (t, rest)) (Pp u (encToks rest)) :=
  ⟨u, rfl, hu⟩

theorem matches_parse_raw_none (e : AST) : MatchesParseRaw none (PErr e) := ⟨e, rfl⟩

/-- A syntactic side condition for parser fragments that do not need the parenthesized-term branch. -/
def NoLPar : List LF.Tok → Prop
  | [] => True
  | .lpar :: _ => False
  | _ :: rest => NoLPar rest

theorem matches_parse_to_raw {r : Option (LF.Term × List LF.Tok)} {v : AST}
    (h : MatchesParse r v) : MatchesParseRaw r v := by
  cases r with
  | none => exact h
  | some pr =>
      rcases pr with ⟨t, rest⟩
      exact ⟨encTerm t, h, reduces_encTerm_refl t⟩

theorem reduces_app {u v : AST} {f a : LF.Term}
    (hu : ReducesToEncTerm u f) (hv : ReducesToEncTerm v a) :
    ReducesToEncTerm (App u v) (.app f a) := by
  rcases hu with ⟨Nu, hNu⟩
  rcases hv with ⟨Nv, hNv⟩
  obtain ⟨M1, hM1⟩ := cong_eval (fun s => App s v)
    (hcong_app1 v) Nu hNu (isnormal_encTerm f)
  obtain ⟨M2, hM2⟩ := cong_eval (fun s => App (encTerm f) s)
    (hcong_app2 (encTerm f) (isnormal_encTerm f)) Nv hNv (isnormal_encTerm a)
  refine ⟨M1 + M2, ?_⟩
  change eval pLF (M1 + M2) (App u v) = App (encTerm f) (encTerm a)
  exact eval_trans pLF M1 M2 _ _ _ hM1 hM2

theorem reduces_pi {u v : AST} {A B : LF.Term}
    (hu : ReducesToEncTerm u A) (hv : ReducesToEncTerm v B) :
    ReducesToEncTerm (Pi u v) (.pi A B) := by
  rcases hu with ⟨Nu, hNu⟩
  rcases hv with ⟨Nv, hNv⟩
  obtain ⟨M1, hM1⟩ := cong_eval (fun s => Pi s v)
    (hcong_pi1 v) Nu hNu (isnormal_encTerm A)
  obtain ⟨M2, hM2⟩ := cong_eval (fun s => Pi (encTerm A) s)
    (hcong_pi2 (encTerm A) (isnormal_encTerm A)) Nv hNv (isnormal_encTerm B)
  refine ⟨M1 + M2, ?_⟩
  change eval pLF (M1 + M2) (Pi u v) = Pi (encTerm A) (encTerm B)
  exact eval_trans pLF M1 M2 _ _ _ hM1 hM2

theorem reduces_lam {u v : AST} {A b : LF.Term}
    (hu : ReducesToEncTerm u A) (hv : ReducesToEncTerm v b) :
    ReducesToEncTerm (Lam u v) (.lam A b) := by
  rcases hu with ⟨Nu, hNu⟩
  rcases hv with ⟨Nv, hNv⟩
  obtain ⟨M1, hM1⟩ := cong_eval (fun s => Lam s v)
    (hcong_lam1 v) Nu hNu (isnormal_encTerm A)
  obtain ⟨M2, hM2⟩ := cong_eval (fun s => Lam (encTerm A) s)
    (hcong_lam2 (encTerm A) (isnormal_encTerm A)) Nv hNv (isnormal_encTerm b)
  refine ⟨M1 + M2, ?_⟩
  change eval pLF (M1 + M2) (Lam u v) = Lam (encTerm A) (encTerm b)
  exact eval_trans pLF M1 M2 _ _ _ hM1 hM2

def shiftStack : List Nat → AST → AST
  | [], u => u
  | c :: cs, u => shiftStack cs (shift (peano c) u)

def lfShiftStack : List Nat → LF.Term → LF.Term
  | [], t => t
  | c :: cs, t => lfShiftStack cs (LF.shift c t)

def ShiftablePayload (u : AST) (t : LF.Term) : Prop :=
  ∀ cs : List Nat, ReducesToEncTerm (shiftStack cs u) (lfShiftStack cs t)

theorem ShiftablePayload.reduces {u : AST} {t : LF.Term}
    (h : ShiftablePayload u t) : ReducesToEncTerm u t := by
  exact h []

theorem ShiftablePayload.shifted {u : AST} {t : LF.Term}
    (h : ShiftablePayload u t) (c : Nat) :
    ShiftablePayload (shift (peano c) u) (LF.shift c t) := by
  intro cs
  exact h (c :: cs)

theorem ShiftablePayload.shift_zero {u : AST} {t : LF.Term}
    (h : ShiftablePayload u t) : ReducesToEncTerm (shift Z u) (LF.shift 0 t) := by
  exact h [0]

theorem shiftable_payload_shift (c : Nat) {u : AST} {t : LF.Term}
    (h : ShiftablePayload u t) :
    ShiftablePayload (shift (peano c) u) (LF.shift c t) :=
  h.shifted c

theorem shiftable_payload_shift_zero {u : AST} {t : LF.Term}
    (h : ShiftablePayload u t) :
    ShiftablePayload (shift Z u) (LF.shift 0 t) := by
  simpa [peano] using h.shifted 0

theorem hcong_shift_arg (c s : AST)
    (hc : oneStep pLF c = none) (hb : baseReducts pLF (shift c s) = []) :
    ∀ t, oneStep pLF s = some t → oneStep pLF (shift c s) = some (shift c t) := by
  intro t h
  have hb' : baseReducts pLF (AST.sexp (Label.id "shift") [c, s]) = [] := hb
  show oneStep pLF (AST.sexp (Label.id "shift") [c, s]) = _
  simp only [oneStep, hb', oneStepList, hc, h, Option.map_some, shift]

theorem shiftStack_descend_shift_step (cs : List Nat) (c : Nat) {s s' : AST}
    (h : oneStep pLF (shift (peano c) s) = some s') :
    oneStep pLF (shiftStack cs (shift (peano c) s)) = some (shiftStack cs s') := by
  induction cs generalizing c s s' with
  | nil => exact h
  | cons d ds ih =>
      change oneStep pLF (shiftStack ds (shift (peano d) (shift (peano c) s))) =
        some (shiftStack ds (shift (peano d) s'))
      have hinner : oneStep pLF (shift (peano d) (shift (peano c) s)) =
          some (shift (peano d) s') := by
        exact hcong_shift_arg (peano d) (shift (peano c) s)
          (isnormal_peano d) rfl s' h
      exact ih d hinner

theorem shiftStack_descend_shiftVar_step (cs : List Nat) (c k b s' : AST)
    (h : oneStep pLF (shiftVar c k b) = some s') :
    oneStep pLF (shiftStack cs (shiftVar c k b)) = some (shiftStack cs s') := by
  induction cs with
  | nil => exact h
  | cons d ds _ =>
      change oneStep pLF (shiftStack ds (shift (peano d) (shiftVar c k b))) =
        some (shiftStack ds (shift (peano d) s'))
      have hinner : oneStep pLF (shift (peano d) (shiftVar c k b)) =
          some (shift (peano d) s') := by
        exact hcong_shift_arg (peano d) (shiftVar c k b)
          (isnormal_peano d) rfl s' h
      exact shiftStack_descend_shift_step ds d hinner

theorem stack_shiftVar_lt_final : ∀ (a b : Nat) (cs : List Nat) (c k : AST),
    oneStep pLF c = none → oneStep pLF k = none →
    ∃ N, eval pLF N (shiftStack cs (shiftVar c k (ltT (peano a) (peano b))))
      = shiftStack cs (if a < b then Var k else Var (S k)) := by
  intro a
  induction a with
  | zero =>
      intro b cs c k hc hk
      cases b with
      | zero =>
          refine ⟨2, ?_⟩
          have h1 := shiftStack_descend_shiftVar_step cs c k (ltT Z Z)
            (shiftVar c k (con0 "ff")) (os_shv_lt_zz c k hc hk)
          have h2 := shiftStack_descend_shiftVar_step cs c k (con0 "ff")
            (Var (S k)) (os_shv_ff c k)
          simp only [peano, eval, h1, h2]
          simp
      | succ b' =>
          refine ⟨2, ?_⟩
          have h1 := shiftStack_descend_shiftVar_step cs c k (ltT Z (S (peano b')))
            (shiftVar c k (con0 "tt")) (os_shv_lt_zs c k (peano b') hc hk)
          have h2 := shiftStack_descend_shiftVar_step cs c k (con0 "tt")
            (Var k) (os_shv_tt c k)
          simp only [peano, eval, h1, h2]
          simp [Nat.zero_lt_succ]
  | succ a' ih =>
      intro b cs c k hc hk
      cases b with
      | zero =>
          refine ⟨2, ?_⟩
          have h1 := shiftStack_descend_shiftVar_step cs c k (ltT (S (peano a')) Z)
            (shiftVar c k (con0 "ff")) (os_shv_lt_sz c k (peano a') hc hk)
          have h2 := shiftStack_descend_shiftVar_step cs c k (con0 "ff")
            (Var (S k)) (os_shv_ff c k)
          simp only [peano, eval, h1, h2]
          simp
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b' cs c k hc hk
          refine ⟨N + 1, ?_⟩
          have h1 := shiftStack_descend_shiftVar_step cs c k
            (ltT (S (peano a')) (S (peano b')))
            (shiftVar c k (ltT (peano a') (peano b')))
            (os_shv_lt_ss c k (peano a') (peano b') hc hk)
          simp only [peano, eval, h1]
          rw [hN]
          simp [Nat.succ_lt_succ_iff]

theorem shiftable_srt (s : LF.Srt) : ShiftablePayload (Srt (encSrt s)) (.srt s) := by
  intro cs
  induction cs with
  | nil => exact reduces_encTerm_refl (.srt s)
  | cons c cs ih =>
      have hone := shiftStack_descend_shift_step cs c (os_sh_srt (peano c) (encSrt s))
      have hstep : eval pLF 1 (shiftStack (c :: cs) (Srt (encSrt s))) =
          shiftStack cs (Srt (encSrt s)) := by
        simp only [shiftStack, eval, hone]
      rcases ih with ⟨N, hN⟩
      refine ⟨1 + N, ?_⟩
      refine eval_trans pLF 1 N _ _ _ hstep ?_
      simpa [lfShiftStack, LF.shift] using hN

theorem shiftable_con (x : String) : ShiftablePayload (Con (con0 x)) (.con x) := by
  intro cs
  induction cs with
  | nil => exact reduces_encTerm_refl (.con x)
  | cons c cs ih =>
      have hone := shiftStack_descend_shift_step cs c (os_sh_con (peano c) (con0 x))
      have hstep : eval pLF 1 (shiftStack (c :: cs) (Con (con0 x))) =
          shiftStack cs (Con (con0 x)) := by
        simp only [shiftStack, eval, hone]
      rcases ih with ⟨N, hN⟩
      refine ⟨1 + N, ?_⟩
      refine eval_trans pLF 1 N _ _ _ hstep ?_
      simpa [lfShiftStack, LF.shift] using hN

theorem shiftable_var (k : Nat) : ShiftablePayload (Var (peano k)) (.var k) := by
  intro cs
  induction cs generalizing k with
  | nil => exact reduces_encTerm_refl (.var k)
  | cons c cs ih =>
      have h0 : eval pLF 1 (shiftStack (c :: cs) (Var (peano k))) =
          shiftStack cs (shiftVar (peano c) (peano k) (ltT (peano k) (peano c))) := by
        have hone := shiftStack_descend_shift_step cs c (os_sh_var (peano c) (peano k))
        simp only [shiftStack, eval, hone]
      obtain ⟨Nguard, hguard⟩ := stack_shiftVar_lt_final k c cs (peano c) (peano k)
        (isnormal_peano c) (isnormal_peano k)
      have htail : ReducesToEncTerm (shiftStack cs (encTerm (LF.shift c (.var k))))
          (lfShiftStack cs (LF.shift c (.var k))) := ih (if k < c then k else k + 1)
      rcases htail with ⟨Ntail, htail⟩
      refine ⟨1 + (Nguard + Ntail), ?_⟩
      refine eval_trans pLF 1 (Nguard + Ntail) _ _ _ h0 ?_
      have hguard' : eval pLF Nguard
          (shiftStack cs (shiftVar (peano c) (peano k) (ltT (peano k) (peano c)))) =
          shiftStack cs (encTerm (LF.shift c (.var k))) := by
        rw [hguard]
        by_cases hkc : k < c
        · simp [LF.shift, hkc, encTerm]
        · simp [LF.shift, hkc, encTerm, peano]
      exact eval_trans pLF Nguard Ntail _ _ _ hguard' htail

theorem shiftable_app_stack : ∀ (cs : List Nat) {u v : AST} {f a : LF.Term},
    ShiftablePayload u f → ShiftablePayload v a →
    ReducesToEncTerm (shiftStack cs (App u v)) (lfShiftStack cs (.app f a)) := by
  intro cs
  induction cs with
  | nil =>
      intro u v f a hu hv
      exact reduces_app hu.reduces hv.reduces
  | cons c cs ih =>
      intro u v f a hu hv
      have hone := shiftStack_descend_shift_step cs c (os_sh_app (peano c) u v)
      have hstep : eval pLF 1 (shiftStack (c :: cs) (App u v)) =
          shiftStack cs (App (shift (peano c) u) (shift (peano c) v)) := by
        simp only [shiftStack, eval, hone]
      have htail : ReducesToEncTerm
          (shiftStack cs (App (shift (peano c) u) (shift (peano c) v)))
          (lfShiftStack cs (.app (LF.shift c f) (LF.shift c a))) :=
        ih (hu.shifted c) (hv.shifted c)
      rcases htail with ⟨N, hN⟩
      refine ⟨1 + N, ?_⟩
      exact eval_trans pLF 1 N _ _ _ hstep hN

theorem shiftable_app {u v : AST} {f a : LF.Term}
    (hu : ShiftablePayload u f) (hv : ShiftablePayload v a) :
    ShiftablePayload (App u v) (.app f a) := by
  intro cs
  exact shiftable_app_stack cs hu hv

theorem shiftable_pi_stack : ∀ (cs : List Nat) {u v : AST} {A B : LF.Term},
    ShiftablePayload u A → ShiftablePayload v B →
    ReducesToEncTerm (shiftStack cs (Pi u v)) (lfShiftStack cs (.pi A B)) := by
  intro cs
  induction cs with
  | nil =>
      intro u v A B hu hv
      exact reduces_pi hu.reduces hv.reduces
  | cons c cs ih =>
      intro u v A B hu hv
      have hone := shiftStack_descend_shift_step cs c (os_sh_pi (peano c) u v)
      have hstep : eval pLF 1 (shiftStack (c :: cs) (Pi u v)) =
          shiftStack cs (Pi (shift (peano c) u) (shift (S (peano c)) v)) := by
        simp only [shiftStack, eval, hone]
      have htail : ReducesToEncTerm
          (shiftStack cs (Pi (shift (peano c) u) (shift (S (peano c)) v)))
          (lfShiftStack cs (.pi (LF.shift c A) (LF.shift (c + 1) B))) := by
        simpa [peano] using ih (hu.shifted c) (hv.shifted (c + 1))
      rcases htail with ⟨N, hN⟩
      refine ⟨1 + N, ?_⟩
      exact eval_trans pLF 1 N _ _ _ hstep hN

theorem shiftable_pi {u v : AST} {A B : LF.Term}
    (hu : ShiftablePayload u A) (hv : ShiftablePayload v B) :
    ShiftablePayload (Pi u v) (.pi A B) := by
  intro cs
  exact shiftable_pi_stack cs hu hv

theorem shiftable_lam_stack : ∀ (cs : List Nat) {u v : AST} {A b : LF.Term},
    ShiftablePayload u A → ShiftablePayload v b →
    ReducesToEncTerm (shiftStack cs (Lam u v)) (lfShiftStack cs (.lam A b)) := by
  intro cs
  induction cs with
  | nil =>
      intro u v A b hu hv
      exact reduces_lam hu.reduces hv.reduces
  | cons c cs ih =>
      intro u v A b hu hv
      have hone := shiftStack_descend_shift_step cs c (os_sh_lam (peano c) u v)
      have hstep : eval pLF 1 (shiftStack (c :: cs) (Lam u v)) =
          shiftStack cs (Lam (shift (peano c) u) (shift (S (peano c)) v)) := by
        simp only [shiftStack, eval, hone]
      have htail : ReducesToEncTerm
          (shiftStack cs (Lam (shift (peano c) u) (shift (S (peano c)) v)))
          (lfShiftStack cs (.lam (LF.shift c A) (LF.shift (c + 1) b))) := by
        simpa [peano] using ih (hu.shifted c) (hv.shifted (c + 1))
      rcases htail with ⟨N, hN⟩
      refine ⟨1 + N, ?_⟩
      exact eval_trans pLF 1 N _ _ _ hstep hN

theorem shiftable_lam {u v : AST} {A b : LF.Term}
    (hu : ShiftablePayload u A) (hv : ShiftablePayload v b) :
    ShiftablePayload (Lam u v) (.lam A b) := by
  intro cs
  exact shiftable_lam_stack cs hu hv

theorem shiftable_encTerm (t : LF.Term) : ShiftablePayload (encTerm t) t := by
  induction t with
  | srt s => exact shiftable_srt s
  | con x => exact shiftable_con x
  | var k => exact shiftable_var k
  | pi A B ihA ihB => exact shiftable_pi ihA ihB
  | lam A b ihA ihb => exact shiftable_lam ihA ihb
  | app f a ihf iha => exact shiftable_app ihf iha

theorem hdesc_shiftStack_shift_resolveK (cs : List Nat) (c : Nat) (s0 : String) :
    ∀ {a a' : AST}, Good a → oneStep pLF a = some a' →
      oneStep pLF (shiftStack cs (shift (peano c) (resolveK (con0 s0) a))) =
        some (shiftStack cs (shift (peano c) (resolveK (con0 s0) a'))) := by
  intro a a' hgood hstep
  have hres := hdesc_resolveK s0 hgood hstep
  have hinner : oneStep pLF (shift (peano c) (resolveK (con0 s0) a)) =
      some (shift (peano c) (resolveK (con0 s0) a')) := by
    exact hcong_shift_arg (peano c) (resolveK (con0 s0) a)
      (isnormal_peano c) rfl _ hres
  exact shiftStack_descend_shift_step cs c hinner

theorem shiftStack_shift_resolve_step (cs : List Nat) (c : Nat)
    (ctx : List String) (s : String) :
    eval pLF 1 (shiftStack cs (shift (peano c) (resolve (encCtx ctx) (con0 s)))) =
      shiftStack cs (shift (peano c)
        (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)))) := by
  have hinner : oneStep pLF (shift (peano c) (resolve (encCtx ctx) (con0 s))) =
      some (shift (peano c) (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)))) := by
    exact hcong_shift_arg (peano c) (resolve (encCtx ctx) (con0 s))
      (isnormal_peano c) rfl _ (by rfl)
  have hone := shiftStack_descend_shift_step cs c hinner
  simp only [eval, hone]

theorem shiftStack_shift_resolveK_nf_step (cs : List Nat) (c : Nat) (s : String) :
    eval pLF 1 (shiftStack cs (shift (peano c) (resolveK (con0 s) NF))) =
      shiftStack cs (shift (peano c) (Con (con0 s))) := by
  have hinner : oneStep pLF (shift (peano c) (resolveK (con0 s) NF)) =
      some (shift (peano c) (Con (con0 s))) := by
    exact hcong_shift_arg (peano c) (resolveK (con0 s) NF)
      (isnormal_peano c) rfl _ (by rfl)
  have hone := shiftStack_descend_shift_step cs c hinner
  simp only [eval, hone]

theorem shiftStack_shift_resolveK_idx_step (cs : List Nat) (c i : Nat) (s : String) :
    eval pLF 1 (shiftStack cs (shift (peano c) (resolveK (con0 s) (Idx (peano i))))) =
      shiftStack cs (shift (peano c) (Var (peano i))) := by
  have hinner : oneStep pLF (shift (peano c) (resolveK (con0 s) (Idx (peano i)))) =
      some (shift (peano c) (Var (peano i))) := by
    exact hcong_shift_arg (peano c) (resolveK (con0 s) (Idx (peano i)))
      (isnormal_peano c) rfl _ (by rfl)
  have hone := shiftStack_descend_shift_step cs c hinner
  simp only [eval, hone]

theorem shiftable_resolve (ctx : List String) (s : String) :
    ShiftablePayload (resolve (encCtx ctx) (con0 s)) (LF.resolve ctx s) := by
  intro cs
  cases cs with
  | nil => exact resolve_sim ctx s
  | cons c cs =>
      obtain ⟨Nctx, hctx⟩ := ctxidx_sim ctx s
      obtain ⟨Mctx, hMctx⟩ :=
        good_cong_eval
          (fun r => shiftStack cs (shift (peano c) (resolveK (con0 s) r)))
          (hdesc_shiftStack_shift_resolveK cs c s)
          Nctx (Good.seed ctx s) hctx (isnormal_encIdx _)
      have hstep0 : eval pLF 1
          (shiftStack (c :: cs) (resolve (encCtx ctx) (con0 s))) =
          shiftStack cs (shift (peano c)
            (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)))) := by
        simpa [shiftStack] using shiftStack_shift_resolve_step cs c ctx s
      cases hr : LF.ctxIdx ctx s with
      | none =>
          obtain ⟨K, hK⟩ := (shiftable_con s) (c :: cs)
          have hMctx' : eval pLF Mctx
              (shiftStack cs (shift (peano c)
                (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s))))) =
              shiftStack cs (shift (peano c) (resolveK (con0 s) (encIdx none))) := by
            simpa [hr] using hMctx
          refine ⟨1 + (Mctx + (1 + K)), ?_⟩
          refine eval_trans pLF 1 (Mctx + (1 + K)) _ _ _ hstep0 ?_
          refine eval_trans pLF Mctx (1 + K) _ _ _ hMctx' ?_
          have hcollapse : eval pLF 1
              (shiftStack cs (shift (peano c) (resolveK (con0 s) (encIdx none)))) =
              shiftStack cs (shift (peano c) (Con (con0 s))) := by
            simp only [encIdx, shiftStack_shift_resolveK_nf_step]
          refine eval_trans pLF 1 K _ _ _ hcollapse ?_
          simpa [shiftStack, lfShiftStack, LF.resolve, hr] using hK
      | some i =>
          obtain ⟨K, hK⟩ := (shiftable_var i) (c :: cs)
          have hMctx' : eval pLF Mctx
              (shiftStack cs (shift (peano c)
                (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s))))) =
              shiftStack cs (shift (peano c) (resolveK (con0 s) (encIdx (some i)))) := by
            simpa [hr] using hMctx
          refine ⟨1 + (Mctx + (1 + K)), ?_⟩
          refine eval_trans pLF 1 (Mctx + (1 + K)) _ _ _ hstep0 ?_
          refine eval_trans pLF Mctx (1 + K) _ _ _ hMctx' ?_
          have hcollapse : eval pLF 1
              (shiftStack cs (shift (peano c) (resolveK (con0 s) (encIdx (some i))))) =
              shiftStack cs (shift (peano c) (Var (peano i))) := by
            simp only [encIdx, shiftStack_shift_resolveK_idx_step]
          refine eval_trans pLF 1 K _ _ _ hcollapse ?_
          simpa [shiftStack, lfShiftStack, LF.resolve, hr] using hK

theorem nested_shift_srt_reduces (c d : Nat) (s : LF.Srt) :
    ReducesToEncTerm (shift (peano c) (shift (peano d) (encTerm (.srt s))))
      (LF.shift c (LF.shift d (.srt s))) := by
  cases s
  · refine ⟨2, ?_⟩
    have h1 : oneStep pLF
        (shift (peano c) (shift (peano d) (Srt (encSrt LF.Srt.type))))
        = some (shift (peano c) (Srt (encSrt LF.Srt.type))) := by
      exact hcong_shift_arg (peano c)
        (shift (peano d) (Srt (encSrt LF.Srt.type)))
        (isnormal_peano c) rfl (Srt (encSrt LF.Srt.type))
        (os_sh_srt (peano d) (encSrt LF.Srt.type))
    simp only [encTerm, eval, h1, os_sh_srt, LF.shift]
  · refine ⟨2, ?_⟩
    have h1 : oneStep pLF
        (shift (peano c) (shift (peano d) (Srt (encSrt LF.Srt.kind))))
        = some (shift (peano c) (Srt (encSrt LF.Srt.kind))) := by
      exact hcong_shift_arg (peano c)
        (shift (peano d) (Srt (encSrt LF.Srt.kind)))
        (isnormal_peano c) rfl (Srt (encSrt LF.Srt.kind))
        (os_sh_srt (peano d) (encSrt LF.Srt.kind))
    simp only [encTerm, eval, h1, os_sh_srt, LF.shift]

theorem nested_shift_con_reduces (c d : Nat) (x : String) :
    ReducesToEncTerm (shift (peano c) (shift (peano d) (encTerm (.con x))))
      (LF.shift c (LF.shift d (.con x))) := by
  refine ⟨2, ?_⟩
  have h1 : oneStep pLF
      (shift (peano c) (shift (peano d) (Con (con0 x))))
      = some (shift (peano c) (Con (con0 x))) := by
    exact hcong_shift_arg (peano c)
      (shift (peano d) (Con (con0 x)))
      (isnormal_peano c) rfl (Con (con0 x))
      (os_sh_con (peano d) (con0 x))
  simp only [encTerm, eval, h1, os_sh_con, LF.shift]

theorem shift_shiftVar_lt_final : ∀ (a b outer : Nat) (c k : AST),
    oneStep pLF c = none → oneStep pLF k = none →
    ∃ N, eval pLF N (shift (peano outer) (shiftVar c k (ltT (peano a) (peano b))))
      = shift (peano outer) (if a < b then Var k else Var (S k)) := by
  intro a
  induction a with
  | zero =>
      intro b outer c k hc hk
      cases b with
      | zero =>
          refine ⟨2, ?_⟩
          have h1 : oneStep pLF (shift (peano outer) (shiftVar c k (ltT Z Z)))
              = some (shift (peano outer) (shiftVar c k (con0 "ff"))) := by
            exact hcong_shift_arg (peano outer) (shiftVar c k (ltT Z Z))
              (isnormal_peano outer) rfl (shiftVar c k (con0 "ff"))
              (os_shv_lt_zz c k hc hk)
          have h2 : oneStep pLF (shift (peano outer) (shiftVar c k (con0 "ff")))
              = some (shift (peano outer) (Var (S k))) := by
            exact hcong_shift_arg (peano outer) (shiftVar c k (con0 "ff"))
              (isnormal_peano outer) rfl (Var (S k))
              (os_shv_ff c k)
          simp only [peano, eval, h1, h2]
          simp
      | succ b' =>
          refine ⟨2, ?_⟩
          have h1 : oneStep pLF (shift (peano outer) (shiftVar c k (ltT Z (S (peano b')))))
              = some (shift (peano outer) (shiftVar c k (con0 "tt"))) := by
            exact hcong_shift_arg (peano outer) (shiftVar c k (ltT Z (S (peano b'))))
              (isnormal_peano outer) rfl (shiftVar c k (con0 "tt"))
              (os_shv_lt_zs c k (peano b') hc hk)
          have h2 : oneStep pLF (shift (peano outer) (shiftVar c k (con0 "tt")))
              = some (shift (peano outer) (Var k)) := by
            exact hcong_shift_arg (peano outer) (shiftVar c k (con0 "tt"))
              (isnormal_peano outer) rfl (Var k)
              (os_shv_tt c k)
          simp only [peano, eval, h1, h2]
          simp [Nat.zero_lt_succ]
  | succ a' ih =>
      intro b outer c k hc hk
      cases b with
      | zero =>
          refine ⟨2, ?_⟩
          have h1 : oneStep pLF (shift (peano outer) (shiftVar c k (ltT (S (peano a')) Z)))
              = some (shift (peano outer) (shiftVar c k (con0 "ff"))) := by
            exact hcong_shift_arg (peano outer) (shiftVar c k (ltT (S (peano a')) Z))
              (isnormal_peano outer) rfl (shiftVar c k (con0 "ff"))
              (os_shv_lt_sz c k (peano a') hc hk)
          have h2 : oneStep pLF (shift (peano outer) (shiftVar c k (con0 "ff")))
              = some (shift (peano outer) (Var (S k))) := by
            exact hcong_shift_arg (peano outer) (shiftVar c k (con0 "ff"))
              (isnormal_peano outer) rfl (Var (S k))
              (os_shv_ff c k)
          simp only [peano, eval, h1, h2]
          simp
      | succ b' =>
          obtain ⟨N, hN⟩ := ih b' outer c k hc hk
          refine ⟨N + 1, ?_⟩
          have h1 : oneStep pLF
              (shift (peano outer) (shiftVar c k (ltT (S (peano a')) (S (peano b')))))
              = some (shift (peano outer) (shiftVar c k (ltT (peano a') (peano b')))) := by
            exact hcong_shift_arg (peano outer)
              (shiftVar c k (ltT (S (peano a')) (S (peano b'))))
              (isnormal_peano outer) rfl (shiftVar c k (ltT (peano a') (peano b')))
              (os_shv_lt_ss c k (peano a') (peano b') hc hk)
          simp only [peano, eval, h1]
          rw [hN]
          simp [Nat.succ_lt_succ_iff]

theorem nested_shift_var_reduces (c d k : Nat) :
    ReducesToEncTerm (shift (peano c) (shift (peano d) (encTerm (.var k))))
      (LF.shift c (LF.shift d (.var k))) := by
  obtain ⟨Nguard, hguard⟩ := shift_shiftVar_lt_final k d c (peano d) (peano k)
    (isnormal_peano d) (isnormal_peano k)
  obtain ⟨K, hK⟩ := shift_sim c (LF.shift d (.var k))
  refine ⟨1 + (Nguard + K), ?_⟩
  have h0 : eval pLF 1 (shift (peano c) (shift (peano d) (encTerm (.var k))))
      = shift (peano c) (shiftVar (peano d) (peano k) (ltT (peano k) (peano d))) := by
    have hstep : oneStep pLF (shift (peano c) (shift (peano d) (Var (peano k))))
        = some (shift (peano c) (shiftVar (peano d) (peano k) (ltT (peano k) (peano d)))) := by
      exact hcong_shift_arg (peano c) (shift (peano d) (Var (peano k)))
        (isnormal_peano c) rfl
        (shiftVar (peano d) (peano k) (ltT (peano k) (peano d)))
        (os_sh_var (peano d) (peano k))
    simp only [encTerm, eval, hstep]
  have hguard' : eval pLF Nguard
      (shift (peano c) (shiftVar (peano d) (peano k) (ltT (peano k) (peano d))))
      = shift (peano c) (encTerm (LF.shift d (.var k))) := by
    rw [hguard]
    by_cases hkd : k < d
    · simp [LF.shift, hkd, encTerm]
    · simp [LF.shift, hkd, encTerm, peano]
  refine eval_trans pLF 1 (Nguard + K) _ _ _ h0 ?_
  refine eval_trans pLF Nguard K _ _ _ hguard' hK

theorem nested_shift_app_reduces {u v : AST} {f a : LF.Term} (c d : Nat)
    (hu : ReducesToEncTerm (shift (peano c) (shift (peano d) u))
      (LF.shift c (LF.shift d f)))
    (hv : ReducesToEncTerm (shift (peano c) (shift (peano d) v))
      (LF.shift c (LF.shift d a))) :
    ReducesToEncTerm (shift (peano c) (shift (peano d) (App u v)))
      (LF.shift c (LF.shift d (.app f a))) := by
  rcases reduces_app hu hv with ⟨Ntail, htail⟩
  have h1 : eval pLF 1 (shift (peano c) (shift (peano d) (App u v)))
      = shift (peano c) (App (shift (peano d) u) (shift (peano d) v)) := by
    have hstep : oneStep pLF (shift (peano c) (shift (peano d) (App u v)))
        = some (shift (peano c) (App (shift (peano d) u) (shift (peano d) v))) := by
      exact hcong_shift_arg (peano c) (shift (peano d) (App u v))
        (isnormal_peano c) rfl
        (App (shift (peano d) u) (shift (peano d) v))
        (os_sh_app (peano d) u v)
    simp only [eval, hstep]
  have h2 : eval pLF 1
      (shift (peano c) (App (shift (peano d) u) (shift (peano d) v)))
      = App (shift (peano c) (shift (peano d) u))
          (shift (peano c) (shift (peano d) v)) := by
    simp only [eval, os_sh_app]
  refine ⟨1 + (1 + Ntail), ?_⟩
  refine eval_trans pLF 1 (1 + Ntail) _ _ _ h1 ?_
  refine eval_trans pLF 1 Ntail _ _ _ h2 ?_
  simpa [LF.shift] using htail

theorem nested_shift_pi_reduces {u v : AST} {A B : LF.Term} (c d : Nat)
    (hu : ReducesToEncTerm (shift (peano c) (shift (peano d) u))
      (LF.shift c (LF.shift d A)))
    (hv : ReducesToEncTerm (shift (S (peano c)) (shift (S (peano d)) v))
      (LF.shift (c + 1) (LF.shift (d + 1) B))) :
    ReducesToEncTerm (shift (peano c) (shift (peano d) (Pi u v)))
      (LF.shift c (LF.shift d (.pi A B))) := by
  rcases reduces_pi hu hv with ⟨Ntail, htail⟩
  have h1 : eval pLF 1 (shift (peano c) (shift (peano d) (Pi u v)))
      = shift (peano c) (Pi (shift (peano d) u) (shift (S (peano d)) v)) := by
    have hstep : oneStep pLF (shift (peano c) (shift (peano d) (Pi u v)))
        = some (shift (peano c)
          (Pi (shift (peano d) u) (shift (S (peano d)) v))) := by
      exact hcong_shift_arg (peano c) (shift (peano d) (Pi u v))
        (isnormal_peano c) rfl
        (Pi (shift (peano d) u) (shift (S (peano d)) v))
        (os_sh_pi (peano d) u v)
    simp only [eval, hstep]
  have h2 : eval pLF 1
      (shift (peano c) (Pi (shift (peano d) u) (shift (S (peano d)) v)))
      = Pi (shift (peano c) (shift (peano d) u))
          (shift (S (peano c)) (shift (S (peano d)) v)) := by
    simp only [eval, os_sh_pi]
  refine ⟨1 + (1 + Ntail), ?_⟩
  refine eval_trans pLF 1 (1 + Ntail) _ _ _ h1 ?_
  refine eval_trans pLF 1 Ntail _ _ _ h2 ?_
  simpa [LF.shift] using htail

theorem nested_shift_lam_reduces {u v : AST} {A b : LF.Term} (c d : Nat)
    (hu : ReducesToEncTerm (shift (peano c) (shift (peano d) u))
      (LF.shift c (LF.shift d A)))
    (hv : ReducesToEncTerm (shift (S (peano c)) (shift (S (peano d)) v))
      (LF.shift (c + 1) (LF.shift (d + 1) b))) :
    ReducesToEncTerm (shift (peano c) (shift (peano d) (Lam u v)))
      (LF.shift c (LF.shift d (.lam A b))) := by
  rcases reduces_lam hu hv with ⟨Ntail, htail⟩
  have h1 : eval pLF 1 (shift (peano c) (shift (peano d) (Lam u v)))
      = shift (peano c) (Lam (shift (peano d) u) (shift (S (peano d)) v)) := by
    have hstep : oneStep pLF (shift (peano c) (shift (peano d) (Lam u v)))
        = some (shift (peano c)
          (Lam (shift (peano d) u) (shift (S (peano d)) v))) := by
      exact hcong_shift_arg (peano c) (shift (peano d) (Lam u v))
        (isnormal_peano c) rfl
        (Lam (shift (peano d) u) (shift (S (peano d)) v))
        (os_sh_lam (peano d) u v)
    simp only [eval, hstep]
  have h2 : eval pLF 1
      (shift (peano c) (Lam (shift (peano d) u) (shift (S (peano d)) v)))
      = Lam (shift (peano c) (shift (peano d) u))
          (shift (S (peano c)) (shift (S (peano d)) v)) := by
    simp only [eval, os_sh_lam]
  refine ⟨1 + (1 + Ntail), ?_⟩
  refine eval_trans pLF 1 (1 + Ntail) _ _ _ h1 ?_
  refine eval_trans pLF 1 Ntail _ _ _ h2 ?_
  simpa [LF.shift] using htail

theorem nested_shift_encTerm_reduces : ∀ (t : LF.Term) (c d : Nat),
    ReducesToEncTerm (shift (peano c) (shift (peano d) (encTerm t)))
      (LF.shift c (LF.shift d t)) := by
  intro t
  induction t with
  | srt s =>
      intro c d
      exact nested_shift_srt_reduces c d s
  | con x =>
      intro c d
      exact nested_shift_con_reduces c d x
  | var k =>
      intro c d
      exact nested_shift_var_reduces c d k
  | pi A B ihA ihB =>
      intro c d
      exact nested_shift_pi_reduces c d (ihA c d) (by
        simpa [peano] using ihB (c + 1) (d + 1))
  | lam A b ihA ihb =>
      intro c d
      exact nested_shift_lam_reduces c d (ihA c d) (by
        simpa [peano] using ihb (c + 1) (d + 1))
  | app f a ihf iha =>
      intro c d
      exact nested_shift_app_reduces c d (ihf c d) (iha c d)

theorem hdesc_nested_shift_resolveK (c d : Nat) (s0 : String) : ∀ {a a' : AST},
    Good a → oneStep pLF a = some a' →
      oneStep pLF (shift (peano c) (shift (peano d) (resolveK (con0 s0) a)))
        = some (shift (peano c) (shift (peano d) (resolveK (con0 s0) a'))) := by
  intro a a' hgood hstep
  have hres := hdesc_resolveK s0 hgood hstep
  have hinner : oneStep pLF (shift (peano d) (resolveK (con0 s0) a))
      = some (shift (peano d) (resolveK (con0 s0) a')) := by
    exact hcong_shift_arg (peano d) (resolveK (con0 s0) a)
      (isnormal_peano d) rfl (resolveK (con0 s0) a') hres
  exact hcong_shift_arg (peano c) (shift (peano d) (resolveK (con0 s0) a))
    (isnormal_peano c) rfl (shift (peano d) (resolveK (con0 s0) a')) hinner

theorem nested_shift_resolve_step (c d : Nat) (ctx : List String) (s : String) :
    eval pLF 1 (shift (peano c) (shift (peano d) (resolve (encCtx ctx) (con0 s))))
      = shift (peano c) (shift (peano d)
          (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)))) := by
  have hresolve : oneStep pLF (resolve (encCtx ctx) (con0 s))
      = some (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s))) := by
    rfl
  have hinner : oneStep pLF (shift (peano d) (resolve (encCtx ctx) (con0 s)))
      = some (shift (peano d)
          (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)))) := by
    exact hcong_shift_arg (peano d) (resolve (encCtx ctx) (con0 s))
      (isnormal_peano d) rfl
      (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s))) hresolve
  have houter : oneStep pLF (shift (peano c) (shift (peano d) (resolve (encCtx ctx) (con0 s))))
      = some (shift (peano c) (shift (peano d)
          (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s))))) := by
    exact hcong_shift_arg (peano c) (shift (peano d) (resolve (encCtx ctx) (con0 s)))
      (isnormal_peano c) rfl
      (shift (peano d) (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)))) hinner
  simp only [eval, houter]

theorem nested_shift_resolveK_nf_step (c d : Nat) (s : String) :
    eval pLF 1 (shift (peano c) (shift (peano d) (resolveK (con0 s) NF)))
      = shift (peano c) (shift (peano d) (Con (con0 s))) := by
  have hres : oneStep pLF (resolveK (con0 s) NF) = some (Con (con0 s)) := by
    rfl
  have hinner : oneStep pLF (shift (peano d) (resolveK (con0 s) NF))
      = some (shift (peano d) (Con (con0 s))) := by
    exact hcong_shift_arg (peano d) (resolveK (con0 s) NF)
      (isnormal_peano d) rfl (Con (con0 s)) hres
  have houter : oneStep pLF (shift (peano c) (shift (peano d) (resolveK (con0 s) NF)))
      = some (shift (peano c) (shift (peano d) (Con (con0 s)))) := by
    exact hcong_shift_arg (peano c) (shift (peano d) (resolveK (con0 s) NF))
      (isnormal_peano c) rfl (shift (peano d) (Con (con0 s))) hinner
  simp only [eval, houter]

theorem nested_shift_resolveK_idx_step (c d i : Nat) (s : String) :
    eval pLF 1 (shift (peano c) (shift (peano d) (resolveK (con0 s) (Idx (peano i)))))
      = shift (peano c) (shift (peano d) (Var (peano i))) := by
  have hres : oneStep pLF (resolveK (con0 s) (Idx (peano i)))
      = some (Var (peano i)) := by
    rfl
  have hinner : oneStep pLF (shift (peano d) (resolveK (con0 s) (Idx (peano i))))
      = some (shift (peano d) (Var (peano i))) := by
    exact hcong_shift_arg (peano d) (resolveK (con0 s) (Idx (peano i)))
      (isnormal_peano d) rfl (Var (peano i)) hres
  have houter : oneStep pLF
      (shift (peano c) (shift (peano d) (resolveK (con0 s) (Idx (peano i)))))
      = some (shift (peano c) (shift (peano d) (Var (peano i)))) := by
    exact hcong_shift_arg (peano c)
      (shift (peano d) (resolveK (con0 s) (Idx (peano i))))
      (isnormal_peano c) rfl (shift (peano d) (Var (peano i))) hinner
  simp only [eval, houter]

theorem nested_shift_resolve (ctx : List String) (s : String) (c d : Nat) :
    ReducesToEncTerm (shift (peano c) (shift (peano d) (resolve (encCtx ctx) (con0 s))))
      (LF.shift c (LF.shift d (LF.resolve ctx s))) := by
  obtain ⟨Nctx, hctx⟩ := ctxidx_sim ctx s
  obtain ⟨Mctx, hMctx⟩ :=
    good_cong_eval
      (fun r => shift (peano c) (shift (peano d) (resolveK (con0 s) r)))
      (hdesc_nested_shift_resolveK c d s)
      Nctx (Good.seed ctx s) hctx (isnormal_encIdx _)
  obtain ⟨K, hK⟩ := nested_shift_encTerm_reduces (LF.resolve ctx s) c d
  refine ⟨1 + (Mctx + (1 + K)), ?_⟩
  have hstep0 : eval pLF 1
      (shift (peano c) (shift (peano d) (resolve (encCtx ctx) (con0 s))))
      = shift (peano c) (shift (peano d)
          (resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)))) :=
    nested_shift_resolve_step c d ctx s
  refine eval_trans pLF 1 (Mctx + (1 + K)) _ _ _ hstep0 ?_
  refine eval_trans pLF Mctx (1 + K) _ _ _ hMctx ?_
  cases hr : LF.ctxIdx ctx s with
  | none =>
      have hcollapse : eval pLF 1
          (shift (peano c) (shift (peano d) (resolveK (con0 s) (encIdx none))))
          = shift (peano c) (shift (peano d) (encTerm (LF.resolve ctx s))) := by
        rw [show LF.resolve ctx s = .con s from by simp [LF.resolve, hr]]
        simp only [encIdx, encTerm, nested_shift_resolveK_nf_step]
      exact eval_trans pLF 1 K _ _ _ hcollapse hK
  | some i =>
      have hcollapse : eval pLF 1
          (shift (peano c) (shift (peano d) (resolveK (con0 s) (encIdx (some i)))))
          = shift (peano c) (shift (peano d) (encTerm (LF.resolve ctx s))) := by
        rw [show LF.resolve ctx s = .var i from by simp [LF.resolve, hr]]
        simp only [encIdx, encTerm, nested_shift_resolveK_idx_step]
      exact eval_trans pLF 1 K _ _ _ hcollapse hK

def MatchesParseShiftable : Option (LF.Term × List LF.Tok) → AST → Prop
  | some (t, rest), v => ∃ u, v = Pp u (encToks rest) ∧ ShiftablePayload u t
  | none, v => ∃ e, v = PErr e

def FirstActiveMatchesParseShiftable (r : Option (LF.Term × List LF.Tok)) (call : AST) : Prop :=
  ∃ N, MatchesParseShiftable r (eval pLF N call) ∧
    ∀ k, k < N → ParserActiveShape (eval pLF k call)

theorem matches_parse_raw_of_shiftable {r : Option (LF.Term × List LF.Tok)} {v : AST}
    (h : MatchesParseShiftable r v) : MatchesParseRaw r v := by
  cases r with
  | none => exact h
  | some pr =>
      rcases pr with ⟨t, rest⟩
      rcases h with ⟨u, rfl, hu⟩
      exact ⟨u, rfl, hu.reduces⟩

theorem first_active_raw_of_shiftable {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (h : FirstActiveMatchesParseShiftable r call) :
    FirstActiveMatchesParseRaw r call := by
  rcases h with ⟨N, hN, hguard⟩
  exact ⟨N, matches_parse_raw_of_shiftable hN, hguard⟩

theorem matches_parse_shiftable_some_of_payload {t : LF.Term} {rest : List LF.Tok} {u : AST}
    (hu : ShiftablePayload u t) :
    MatchesParseShiftable (some (t, rest)) (Pp u (encToks rest)) :=
  ⟨u, rfl, hu⟩

theorem matches_parse_shiftable_none (e : AST) : MatchesParseShiftable none (PErr e) :=
  ⟨e, rfl⟩

theorem matches_parse_shiftable_exact (t : LF.Term) (rest : List LF.Tok) :
    MatchesParseShiftable (some (t, rest)) (Pp (encTerm t) (encToks rest)) :=
  matches_parse_shiftable_some_of_payload (shiftable_encTerm t)

theorem first_active_shiftable_zero {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (h : MatchesParseShiftable r call) : FirstActiveMatchesParseShiftable r call := by
  refine ⟨0, ?_, ?_⟩
  · simpa only [eval] using h
  · intro k hk
    exact False.elim (Nat.not_lt_zero k hk)

theorem first_active_shiftable_one {r : Option (LF.Term × List LF.Tok)} {call v : AST}
    (hstep : eval pLF 1 call = v) (h : MatchesParseShiftable r v)
    (hactive : ParserActiveShape call) : FirstActiveMatchesParseShiftable r call := by
  refine ⟨1, ?_, ?_⟩
  · rw [hstep]
    exact h
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simpa only [eval] using hactive

theorem first_active_shiftable_prepend {r : Option (LF.Term × List LF.Tok)} {call next : AST}
    (hstep : eval pLF 1 call = next) (hactive : ParserActiveShape call)
    (hnext : FirstActiveMatchesParseShiftable r next) :
    FirstActiveMatchesParseShiftable r call := by
  rcases hnext with ⟨N, hN, hguard⟩
  refine ⟨1 + N, ?_, ?_⟩
  · have htotal : eval pLF (1 + N) call = eval pLF N next :=
      eval_trans pLF 1 N call next (eval pLF N next) hstep rfl
    rw [htotal]
    exact hN
  · intro k hk
    cases k with
    | zero => simpa only [eval] using hactive
    | succ k =>
        have hk' : Nat.succ k < Nat.succ N := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using hk
        have hkN : k < N := Nat.succ_lt_succ_iff.mp hk'
        have htotal : eval pLF (Nat.succ k) call = eval pLF k next := by
          have h := eval_trans pLF 1 k call next (eval pLF k next) hstep rfl
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
        rw [htotal]
        exact hguard k hkN

theorem first_active_shiftable_prepend_eval {r : Option (LF.Term × List LF.Tok)}
    {call next : AST} {M : Nat} (hstep : eval pLF M call = next)
    (hguard : ∀ k, k < M → ParserActiveShape (eval pLF k call))
    (hnext : FirstActiveMatchesParseShiftable r next) :
    FirstActiveMatchesParseShiftable r call := by
  rcases hnext with ⟨N, hN, hNguard⟩
  refine ⟨M + N, ?_, ?_⟩
  · have htotal : eval pLF (M + N) call = eval pLF N next :=
      eval_trans pLF M N call next (eval pLF N next) hstep rfl
    rw [htotal]
    exact hN
  · intro k hk
    by_cases hkM : k < M
    · exact hguard k hkM
    · have hge : M ≤ k := Nat.le_of_not_gt hkM
      let j := k - M
      have hjlt : j < N := by omega
      have hk_eq : k = M + j := by omega
      have hshift : eval pLF k call = eval pLF j next := by
        have htotal : eval pLF (M + j) call = eval pLF j next :=
          eval_trans pLF M j call next (eval pLF j next) hstep rfl
        simpa [hk_eq] using htotal
      rw [hshift]
      exact hNguard j hjlt

/-! ## Normal forms for encoded tokens, token streams, and parser result shapes -/

theorem isnormal_encTok : ∀ t : LF.Tok, IsNormal pLF (encTok t)
  | .pi => isnormal_con0 "PI"
  | .lam => isnormal_con0 "LAM"
  | .arr => isnormal_con0 "ARR"
  | .colon => isnormal_con0 "COLON"
  | .dot => isnormal_con0 "DOT"
  | .lpar => isnormal_con0 "LP"
  | .rpar => isnormal_con0 "RP"
  | .type => isnormal_con0 "TYPE"
  | .id s => isnormal_sexp1 (.id "Tid") (con0 s) rfl (isnormal_con0 s)

theorem isnormal_encToks : ∀ ts : List LF.Tok, IsNormal pLF (encToks ts)
  | [] => isnormal_con0 "Nil"
  | t :: ts =>
      isnormal_sexp2 (.id "Cons") (encTok t) (encToks ts) rfl
        (isnormal_encTok t) (isnormal_encToks ts)

theorem isnormal_encCtx : ∀ ctx : List String, IsNormal pLF (encCtx ctx)
  | [] => isnormal_con0 "Nil"
  | x :: xs =>
      isnormal_sexp2 (.id "Cons") (con0 x) (encCtx xs) rfl
        (isnormal_con0 x) (isnormal_encCtx xs)

theorem isnormal_Pp {t r : AST} (ht : IsNormal pLF t) (hr : IsNormal pLF r) :
    IsNormal pLF (Pp t r) :=
  isnormal_sexp2 (.id "P") t r rfl ht hr

theorem isnormal_PErr {e : AST} (he : IsNormal pLF e) : IsNormal pLF (PErr e) :=
  isnormal_sexp1 (.id "PErr") e rfl he

theorem isnormal_Ok {t : AST} (ht : IsNormal pLF t) : IsNormal pLF (Ok t) :=
  isnormal_sexp1 (.id "Ok") t rfl ht

theorem isnormal_Err {e : AST} (he : IsNormal pLF e) : IsNormal pLF (Err e) :=
  isnormal_sexp1 (.id "Err") e rfl he

theorem isnormal_extraToks {r : AST} (hr : IsNormal pLF r) : IsNormal pLF (extraToks r) :=
  isnormal_sexp1 (.id "extra-tokens") r rfl hr

/-! ## Context congruence for parser-result constructors -/

theorem hcong_Pp1 (r : AST) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Pp s r) = some (Pp s' r) := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "P") [s, r]) = [] := rfl
  show oneStep pLF (.sexp (.id "P") [s, r]) = _
  simp only [oneStep, hb, oneStepList, h, Option.map_some, Pp]

theorem hcong_Pp2 (t : AST) (ht : oneStep pLF t = none) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Pp t s) = some (Pp t s') := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "P") [t, s]) = [] := rfl
  show oneStep pLF (.sexp (.id "P") [t, s]) = _
  simp only [oneStep, hb, oneStepList, ht, h, Option.map_some, Pp]

theorem matches_parse_raw_to_exact {r : Option (LF.Term × List LF.Tok)} {v : AST}
    (h : MatchesParseRaw r v) : ∃ N, MatchesParse r (eval pLF N v) := by
  cases r with
  | none =>
      rcases h with ⟨e, rfl⟩
      exact ⟨0, matches_parse_none e⟩
  | some pr =>
      rcases pr with ⟨t, rest⟩
      rcases h with ⟨u, rfl, N, hN⟩
      obtain ⟨M, hM⟩ := cong_eval (fun s => Pp s (encToks rest))
        (hcong_Pp1 (encToks rest)) N hN (isnormal_encTerm t)
      refine ⟨M, ?_⟩
      rw [hM]
      exact matches_parse_some t rest

theorem matches_parse_exact_of_raw_eval {r : Option (LF.Term × List LF.Tok)}
    {call : AST} {N : Nat} (h : MatchesParseRaw r (eval pLF N call)) :
    ∃ M, MatchesParse r (eval pLF M call) := by
  obtain ⟨K, hK⟩ := matches_parse_raw_to_exact h
  refine ⟨N + K, ?_⟩
  have hcomp : eval pLF (N + K) call = eval pLF K (eval pLF N call) :=
    eval_trans pLF N K call (eval pLF N call) (eval pLF K (eval pLF N call)) rfl rfl
  rw [hcomp]
  exact hK

theorem matches_parse_exact_of_first_raw {r : Option (LF.Term × List LF.Tok)}
    {call : AST} (h : FirstMatchesParseRaw r call) :
    ∃ M, MatchesParse r (eval pLF M call) := by
  rcases first_matches_to_raw h with ⟨N, hN⟩
  exact matches_parse_exact_of_raw_eval hN

theorem cong_eval_raw_until_result (F : AST → AST)
    (hcong : ∀ s s', ¬ ParserResultShape s → oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pLF N s = v →
      (∀ k, k < N → ¬ ParserResultShape (eval pLF k s)) →
        ∃ M, eval pLF M (F s) = F v := by
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
      cases hstep : oneStep pLF s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at h
          have hsnot : ¬ ParserResultShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguard' : ∀ k, k < n → ¬ ParserResultShape (eval pLF k s') := by
            intro k hk
            have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
            simpa only [eval, hstep] using hguard (k + 1) hk'
          obtain ⟨M, hM⟩ := ih h hguard'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsnot hstep]
          exact hM

theorem first_matches_bind {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (F : AST → AST) (Goal : AST → Prop)
    (hcong : ∀ s s', ¬ ParserResultShape s → oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s'))
    (hfirst : FirstMatchesParseRaw r call)
    (hend : ∀ {v : AST}, MatchesParseRaw r v → ∃ K, Goal (eval pLF K (F v))) :
    ∃ N, Goal (eval pLF N (F call)) := by
  rcases hfirst with ⟨Nchild, hchild, hguard⟩
  obtain ⟨Mctx, hMctx⟩ := cong_eval_raw_until_result F hcong Nchild rfl hguard
  obtain ⟨Kend, hKend⟩ := hend hchild
  refine ⟨Mctx + Kend, ?_⟩
  have htotal : eval pLF (Mctx + Kend) (F call)
      = eval pLF Kend (F (eval pLF Nchild call)) :=
    eval_trans pLF Mctx Kend _ _ _ hMctx rfl
  rw [htotal]
  exact hKend

theorem cong_eval_active (F : AST → AST)
    (hcong : ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pLF N s = v →
      (∀ k, k < N → ParserActiveShape (eval pLF k s)) →
        ∃ M, eval pLF M (F s) = F v := by
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
      cases hstep : oneStep pLF s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl⟩
      | some s' =>
          rw [hstep] at h
          have hsactive : ParserActiveShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguard' : ∀ k, k < n → ParserActiveShape (eval pLF k s') := by
            intro k hk
            have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
            simpa only [eval, hstep] using hguard (k + 1) hk'
          obtain ⟨M, hM⟩ := ih h hguard'
          refine ⟨M + 1, ?_⟩
          simp only [eval, hcong s s' hsactive hstep]
          exact hM

theorem first_active_bind {r : Option (LF.Term × List LF.Tok)} {call : AST}
    (F : AST → AST) (Goal : AST → Prop)
    (hcong : ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s'))
    (hfirst : FirstActiveMatchesParseRaw r call)
    (hend : ∀ {v : AST}, MatchesParseRaw r v → ∃ K, Goal (eval pLF K (F v))) :
    ∃ N, Goal (eval pLF N (F call)) := by
  rcases hfirst with ⟨Nchild, hchild, hguard⟩
  obtain ⟨Mctx, hMctx⟩ := cong_eval_active F hcong Nchild rfl hguard
  obtain ⟨Kend, hKend⟩ := hend hchild
  refine ⟨Mctx + Kend, ?_⟩
  have htotal : eval pLF (Mctx + Kend) (F call)
      = eval pLF Kend (F (eval pLF Nchild call)) :=
    eval_trans pLF Mctx Kend _ _ _ hMctx rfl
  rw [htotal]
  exact hKend

theorem cong_eval_active_with_guard (F : AST → AST)
    (hwrap : ∀ s, ParserActiveShape s → ParserActiveShape (F s))
    (hcong : ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pLF N s = v →
      (∀ k, k < N → ParserActiveShape (eval pLF k s)) →
        ∃ M, eval pLF M (F s) = F v ∧
          ∀ k, k < M → ParserActiveShape (eval pLF k (F s)) := by
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
      cases hstep : oneStep pLF s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at h
          have hsactive : ParserActiveShape s := by
            simpa only [eval] using hguard 0 (Nat.zero_lt_succ n)
          have hguard' : ∀ k, k < n → ParserActiveShape (eval pLF k s') := by
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
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal : eval pLF (Nat.succ k) (F s) = eval pLF k (F s') := by
                  simp only [eval, hcong s s' hsactive hstep]
                rw [htotal]
                exact hMguard k hkM

theorem cong_eval_with_active_wrapper (F : AST → AST)
    (hwrap : ∀ s, ParserActiveShape (F s))
    (hcong : ∀ s s', oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pLF N s = v →
        ∃ M, eval pLF M (F s) = F v ∧
          ∀ k, k < M → ParserActiveShape (eval pLF k (F s)) := by
  intro N
  induction N with
  | zero =>
      intro s v h
      simp only [eval] at h
      subst h
      exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
      intro s v h
      simp only [eval] at h
      cases hstep : oneStep pLF s with
      | none =>
          rw [hstep] at h
          subst h
          exact ⟨0, rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      | some s' =>
          rw [hstep] at h
          obtain ⟨M, hM, hMguard⟩ := ih h
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
                    simpa [Nat.succ_eq_add_one] using hk)
                have htotal : eval pLF (Nat.succ k) (F s) = eval pLF k (F s') := by
                  simp only [eval, hcong s s' hstep]
                rw [htotal]
                exact hMguard k hkM

theorem first_active_bind_active {r q : Option (LF.Term × List LF.Tok)} {call : AST}
    (F : AST → AST)
    (hwrap : ∀ s, ParserActiveShape s → ParserActiveShape (F s))
    (hcong : ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s'))
    (hfirst : FirstActiveMatchesParseRaw r call)
    (hend : ∀ {v : AST}, MatchesParseRaw r v → FirstActiveMatchesParseRaw q (F v)) :
    FirstActiveMatchesParseRaw q (F call) := by
  rcases hfirst with ⟨Nchild, hchild, hguard⟩
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_active_with_guard F hwrap hcong Nchild rfl hguard
  rcases hend hchild with ⟨Nend, hendRaw, hendGuard⟩
  refine ⟨Mctx + Nend, ?_, ?_⟩
  · have htotal : eval pLF (Mctx + Nend) (F call)
        = eval pLF Nend (F (eval pLF Nchild call)) :=
      eval_trans pLF Mctx Nend _ _ _ hMctx rfl
    rw [htotal]
    exact hendRaw
  · intro k hk
    by_cases hkctx : k < Mctx
    · exact hMguard k hkctx
    · have hge : Mctx ≤ k := Nat.le_of_not_gt hkctx
      let j := k - Mctx
      have hjlt : j < Nend := by
        omega
      have hk_eq : k = Mctx + j := by
        omega
      have hshift : eval pLF k (F call) = eval pLF j (F (eval pLF Nchild call)) := by
        have htotal : eval pLF (Mctx + j) (F call)
            = eval pLF j (F (eval pLF Nchild call)) :=
          eval_trans pLF Mctx j _ _ _ hMctx rfl
        simpa [hk_eq] using htotal
      rw [hshift]
      exact hendGuard j hjlt

theorem first_active_shiftable_bind_active {r q : Option (LF.Term × List LF.Tok)} {call : AST}
    (F : AST → AST)
    (hwrap : ∀ s, ParserActiveShape s → ParserActiveShape (F s))
    (hcong : ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (F s) = some (F s'))
    (hfirst : FirstActiveMatchesParseShiftable r call)
    (hend : ∀ {v : AST}, MatchesParseShiftable r v → FirstActiveMatchesParseShiftable q (F v)) :
    FirstActiveMatchesParseShiftable q (F call) := by
  rcases hfirst with ⟨Nchild, hchild, hguard⟩
  obtain ⟨Mctx, hMctx, hMguard⟩ :=
    cong_eval_active_with_guard F hwrap hcong Nchild rfl hguard
  rcases hend hchild with ⟨Nend, hendRaw, hendGuard⟩
  refine ⟨Mctx + Nend, ?_, ?_⟩
  · have htotal : eval pLF (Mctx + Nend) (F call)
        = eval pLF Nend (F (eval pLF Nchild call)) :=
      eval_trans pLF Mctx Nend _ _ _ hMctx rfl
    rw [htotal]
    exact hendRaw
  · intro k hk
    by_cases hkctx : k < Mctx
    · exact hMguard k hkctx
    · have hge : Mctx ≤ k := Nat.le_of_not_gt hkctx
      let j := k - Mctx
      have hjlt : j < Nend := by omega
      have hk_eq : k = Mctx + j := by omega
      have hshift : eval pLF k (F call) = eval pLF j (F (eval pLF Nchild call)) := by
        have htotal : eval pLF (Mctx + j) (F call)
            = eval pLF j (F (eval pLF Nchild call)) :=
          eval_trans pLF Mctx j _ _ _ hMctx rfl
        simpa [hk_eq] using htotal
      rw [hshift]
      exact hendGuard j hjlt

theorem hcong_Ok : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Ok s) = some (Ok s') := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "Ok") [s]) = [] := rfl
  show oneStep pLF (.sexp (.id "Ok") [s]) = _
  simp only [oneStep, hb, oneStepList, h, Option.map_some, Ok]

theorem hcong_Err : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Err s) = some (Err s') := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "Err") [s]) = [] := rfl
  show oneStep pLF (.sexp (.id "Err") [s]) = _
  simp only [oneStep, hb, oneStepList, h, Option.map_some, Err]

theorem hcong_arK_arg (f ctx s : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hb : baseReducts pLF (arK f ctx s) = []) :
    ∀ s', oneStep pLF s = some s' → oneStep pLF (arK f ctx s) = some (arK f ctx s') := by
  intro s' h
  have hb' : baseReducts pLF (AST.sexp (Label.id "arK") [f, ctx, s]) = [] := hb
  show oneStep pLF (.sexp (.id "arK") [f, ctx, s]) = _
  simp only [oneStep, hb', oneStepList, hf, hctx, h, Option.map_some, arK]

theorem hcong_tmPi1_arg (f ctx x s : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none)
    (hb : baseReducts pLF (tmPi1 f ctx x s) = []) :
    ∀ s', oneStep pLF s = some s' →
      oneStep pLF (tmPi1 f ctx x s) = some (tmPi1 f ctx x s') := by
  intro s' h
  have hb' : baseReducts pLF (AST.sexp (Label.id "tmPi1") [f, ctx, x, s]) = [] := hb
  show oneStep pLF (.sexp (.id "tmPi1") [f, ctx, x, s]) = _
  simp only [oneStep, hb', oneStepList, hf, hctx, hx, h, Option.map_some, tmPi1]

theorem hcong_tmLam1_arg (f ctx x s : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none)
    (hb : baseReducts pLF (tmLam1 f ctx x s) = []) :
    ∀ s', oneStep pLF s = some s' →
      oneStep pLF (tmLam1 f ctx x s) = some (tmLam1 f ctx x s') := by
  intro s' h
  have hb' : baseReducts pLF (AST.sexp (Label.id "tmLam1") [f, ctx, x, s]) = [] := hb
  show oneStep pLF (.sexp (.id "tmLam1") [f, ctx, x, s]) = _
  simp only [oneStep, hb', oneStepList, hf, hctx, hx, h, Option.map_some, tmLam1]

theorem hcong_apK_arg (f ctx s : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hb : baseReducts pLF (apK f ctx s) = []) :
    ∀ s', oneStep pLF s = some s' → oneStep pLF (apK f ctx s) = some (apK f ctx s') := by
  intro s' h
  have hb' : baseReducts pLF (AST.sexp (Label.id "apK") [f, ctx, s]) = [] := hb
  show oneStep pLF (.sexp (.id "apK") [f, ctx, s]) = _
  simp only [oneStep, hb', oneStepList, hf, hctx, h, Option.map_some, apK]

theorem hcong_apmK_arg (f ctx acc toks s : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hacc : oneStep pLF acc = none) (htoks : oneStep pLF toks = none)
    (hb : baseReducts pLF (apmK f ctx acc toks s) = []) :
    ∀ s', oneStep pLF s = some s' →
      oneStep pLF (apmK f ctx acc toks s) = some (apmK f ctx acc toks s') := by
  intro s' h
  have hb' : baseReducts pLF (AST.sexp (Label.id "apmK") [f, ctx, acc, toks, s]) = [] := hb
  show oneStep pLF (.sexp (.id "apmK") [f, ctx, acc, toks, s]) = _
  simp only [oneStep, hb', oneStepList, hf, hctx, hacc, htoks, h, Option.map_some, apmK]

theorem hcong_atLPk_arg (f ctx s : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hb : baseReducts pLF (atLPk f ctx s) = []) :
    ∀ s', oneStep pLF s = some s' → oneStep pLF (atLPk f ctx s) = some (atLPk f ctx s') := by
  intro s' h
  have hb' : baseReducts pLF (AST.sexp (Label.id "atLPk") [f, ctx, s]) = [] := hb
  show oneStep pLF (.sexp (.id "atLPk") [f, ctx, s]) = _
  simp only [oneStep, hb', oneStepList, hf, hctx, h, Option.map_some, atLPk]

theorem hcong_arK2_left_active_child (r : AST) (hr : ParserActiveShape r) :
    ∀ a a', oneStep pLF a = some a' →
      oneStep pLF (arK2 a r) = some (arK2 a' r) := by
  intro a a' h
  have hb : baseReducts pLF (arK2 a r) = [] := by
    cases hr <;> rfl
  have hb' : baseReducts pLF (AST.sexp (Label.id "arK2") [a, r]) = [] := hb
  show oneStep pLF (.sexp (.id "arK2") [a, r]) = _
  simp only [oneStep, hb', oneStepList, h, Option.map_some, arK2]

theorem hcong_arK2_right_active (a : AST) (ha : oneStep pLF a = none) :
    ∀ r r', ParserActiveShape r → oneStep pLF r = some r' →
      oneStep pLF (arK2 a r) = some (arK2 a r') := by
  intro r r' hr h
  have hb : baseReducts pLF (arK2 a r) = [] := by
    cases hr <;> rfl
  have hb' : baseReducts pLF (AST.sexp (Label.id "arK2") [a, r]) = [] := hb
  show oneStep pLF (.sexp (.id "arK2") [a, r]) = _
  simp only [oneStep, hb', oneStepList, ha, h, Option.map_some, arK2]

theorem hcong_tmPi2_left_active_child (r : AST) (hr : ParserActiveShape r) :
    ∀ A A', oneStep pLF A = some A' →
      oneStep pLF (tmPi2 A r) = some (tmPi2 A' r) := by
  intro A A' h
  have hb : baseReducts pLF (tmPi2 A r) = [] := by
    cases hr <;> rfl
  have hb' : baseReducts pLF (AST.sexp (Label.id "tmPi2") [A, r]) = [] := hb
  show oneStep pLF (.sexp (.id "tmPi2") [A, r]) = _
  simp only [oneStep, hb', oneStepList, h, Option.map_some, tmPi2]

theorem hcong_tmPi2_right_active (A : AST) (hA : oneStep pLF A = none) :
    ∀ r r', ParserActiveShape r → oneStep pLF r = some r' →
      oneStep pLF (tmPi2 A r) = some (tmPi2 A r') := by
  intro r r' hr h
  have hb : baseReducts pLF (tmPi2 A r) = [] := by
    cases hr <;> rfl
  have hb' : baseReducts pLF (AST.sexp (Label.id "tmPi2") [A, r]) = [] := hb
  show oneStep pLF (.sexp (.id "tmPi2") [A, r]) = _
  simp only [oneStep, hb', oneStepList, hA, h, Option.map_some, tmPi2]

theorem hcong_tmLam2_left_active_child (r : AST) (hr : ParserActiveShape r) :
    ∀ A A', oneStep pLF A = some A' →
      oneStep pLF (tmLam2 A r) = some (tmLam2 A' r) := by
  intro A A' h
  have hb : baseReducts pLF (tmLam2 A r) = [] := by
    cases hr <;> rfl
  have hb' : baseReducts pLF (AST.sexp (Label.id "tmLam2") [A, r]) = [] := hb
  show oneStep pLF (.sexp (.id "tmLam2") [A, r]) = _
  simp only [oneStep, hb', oneStepList, h, Option.map_some, tmLam2]

theorem hcong_tmLam2_right_active (A : AST) (hA : oneStep pLF A = none) :
    ∀ r r', ParserActiveShape r → oneStep pLF r = some r' →
      oneStep pLF (tmLam2 A r) = some (tmLam2 A r') := by
  intro r r' hr h
  have hb : baseReducts pLF (tmLam2 A r) = [] := by
    cases hr <;> rfl
  have hb' : baseReducts pLF (AST.sexp (Label.id "tmLam2") [A, r]) = [] := hb
  show oneStep pLF (.sexp (.id "tmLam2") [A, r]) = _
  simp only [oneStep, hb', oneStepList, hA, h, Option.map_some, tmLam2]

theorem hcong_atLPk_ar (f ctx g c toks : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (ar g c toks) = some s' →
      oneStep pLF (atLPk f ctx (ar g c toks)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (ar g c toks) hf hctx rfl

theorem hcong_atLPk_ap (f ctx g c toks : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (ap g c toks) = some s' →
      oneStep pLF (atLPk f ctx (ap g c toks)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (ap g c toks) hf hctx rfl

theorem hcong_atLPk_apm (f ctx g c acc toks : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (apm g c acc toks) = some s' →
      oneStep pLF (atLPk f ctx (apm g c acc toks)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (apm g c acc toks) hf hctx rfl

theorem hcong_atLPk_at (f ctx g c toks : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (at' g c toks) = some s' →
      oneStep pLF (atLPk f ctx (at' g c toks)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (at' g c toks) hf hctx rfl

theorem hcong_atLPk_tmPi1 (f ctx g c x r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (tmPi1 g c x r) = some s' →
      oneStep pLF (atLPk f ctx (tmPi1 g c x r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (tmPi1 g c x r) hf hctx rfl

theorem hcong_atLPk_tmPi2 (f ctx A r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (tmPi2 A r) = some s' →
      oneStep pLF (atLPk f ctx (tmPi2 A r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (tmPi2 A r) hf hctx rfl

theorem hcong_atLPk_tmLam1 (f ctx g c x r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (tmLam1 g c x r) = some s' →
      oneStep pLF (atLPk f ctx (tmLam1 g c x r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (tmLam1 g c x r) hf hctx rfl

theorem hcong_atLPk_tmLam2 (f ctx A r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (tmLam2 A r) = some s' →
      oneStep pLF (atLPk f ctx (tmLam2 A r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (tmLam2 A r) hf hctx rfl

theorem hcong_atLPk_arK (f ctx g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (arK g c r) = some s' →
      oneStep pLF (atLPk f ctx (arK g c r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (arK g c r) hf hctx rfl

theorem hcong_atLPk_arK2 (f ctx a r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (arK2 a r) = some s' →
      oneStep pLF (atLPk f ctx (arK2 a r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (arK2 a r) hf hctx rfl

theorem hcong_atLPk_apK (f ctx g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (apK g c r) = some s' →
      oneStep pLF (atLPk f ctx (apK g c r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (apK g c r) hf hctx rfl

theorem hcong_atLPk_apmK (f ctx g c acc toks r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (apmK g c acc toks r) = some s' →
      oneStep pLF (atLPk f ctx (apmK g c acc toks r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (apmK g c acc toks r) hf hctx rfl

theorem hcong_recK_arg (s : AST) (hb : baseReducts pLF (recK s) = []) :
    ∀ s', oneStep pLF s = some s' → oneStep pLF (recK s) = some (recK s') := by
  intro s' h
  have hb' : baseReducts pLF (AST.sexp (Label.id "recK") [s]) = [] := hb
  show oneStep pLF (.sexp (.id "recK") [s]) = _
  simp only [oneStep, hb', oneStepList, h, Option.map_some, recK]

theorem hcong_recK_tm (f ctx toks : AST) :
    ∀ s', oneStep pLF (tm f ctx toks) = some s' →
      oneStep pLF (recK (tm f ctx toks)) = some (recK s') :=
  hcong_recK_arg (tm f ctx toks) rfl

theorem hcong_recK_ar (f ctx toks : AST) :
    ∀ s', oneStep pLF (ar f ctx toks) = some s' →
      oneStep pLF (recK (ar f ctx toks)) = some (recK s') :=
  hcong_recK_arg (ar f ctx toks) rfl

theorem hcong_recK_ap (f ctx toks : AST) :
    ∀ s', oneStep pLF (ap f ctx toks) = some s' →
      oneStep pLF (recK (ap f ctx toks)) = some (recK s') :=
  hcong_recK_arg (ap f ctx toks) rfl

theorem hcong_recK_apm (f ctx acc toks : AST) :
    ∀ s', oneStep pLF (apm f ctx acc toks) = some s' →
      oneStep pLF (recK (apm f ctx acc toks)) = some (recK s') :=
  hcong_recK_arg (apm f ctx acc toks) rfl

theorem hcong_recK_at (f ctx toks : AST) :
    ∀ s', oneStep pLF (at' f ctx toks) = some s' →
      oneStep pLF (recK (at' f ctx toks)) = some (recK s') :=
  hcong_recK_arg (at' f ctx toks) rfl

theorem hcong_recK_tmPi1 (f ctx x r : AST) :
    ∀ s', oneStep pLF (tmPi1 f ctx x r) = some s' →
      oneStep pLF (recK (tmPi1 f ctx x r)) = some (recK s') :=
  hcong_recK_arg (tmPi1 f ctx x r) rfl

theorem hcong_recK_tmPi2 (A r : AST) :
    ∀ s', oneStep pLF (tmPi2 A r) = some s' →
      oneStep pLF (recK (tmPi2 A r)) = some (recK s') :=
  hcong_recK_arg (tmPi2 A r) rfl

theorem hcong_recK_tmLam1 (f ctx x r : AST) :
    ∀ s', oneStep pLF (tmLam1 f ctx x r) = some s' →
      oneStep pLF (recK (tmLam1 f ctx x r)) = some (recK s') :=
  hcong_recK_arg (tmLam1 f ctx x r) rfl

theorem hcong_recK_tmLam2 (A r : AST) :
    ∀ s', oneStep pLF (tmLam2 A r) = some s' →
      oneStep pLF (recK (tmLam2 A r)) = some (recK s') :=
  hcong_recK_arg (tmLam2 A r) rfl

theorem hcong_recK_arK (f ctx r : AST) :
    ∀ s', oneStep pLF (arK f ctx r) = some s' →
      oneStep pLF (recK (arK f ctx r)) = some (recK s') :=
  hcong_recK_arg (arK f ctx r) rfl

theorem hcong_recK_arK2 (a r : AST) :
    ∀ s', oneStep pLF (arK2 a r) = some s' →
      oneStep pLF (recK (arK2 a r)) = some (recK s') :=
  hcong_recK_arg (arK2 a r) rfl

theorem hcong_recK_apK (f ctx r : AST) :
    ∀ s', oneStep pLF (apK f ctx r) = some s' →
      oneStep pLF (recK (apK f ctx r)) = some (recK s') :=
  hcong_recK_arg (apK f ctx r) rfl

theorem hcong_recK_apmK (f ctx acc toks r : AST) :
    ∀ s', oneStep pLF (apmK f ctx acc toks r) = some s' →
      oneStep pLF (recK (apmK f ctx acc toks r)) = some (recK s') :=
  hcong_recK_arg (apmK f ctx acc toks r) rfl

theorem hcong_recK_atLPk (f ctx r : AST) :
    ∀ s', oneStep pLF (atLPk f ctx r) = some s' →
      oneStep pLF (recK (atLPk f ctx r)) = some (recK s') :=
  hcong_recK_arg (atLPk f ctx r) rfl

theorem hcong_recK_active :
    ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (recK s) = some (recK s') := by
  intro s s' hactive hstep
  cases hactive with
  | tm f ctx toks => exact hcong_recK_tm f ctx toks s' hstep
  | ar f ctx toks => exact hcong_recK_ar f ctx toks s' hstep
  | ap f ctx toks => exact hcong_recK_ap f ctx toks s' hstep
  | apm f ctx acc toks => exact hcong_recK_apm f ctx acc toks s' hstep
  | atom f ctx toks => exact hcong_recK_at f ctx toks s' hstep
  | tmPi1 f ctx x r => exact hcong_recK_tmPi1 f ctx x r s' hstep
  | tmPi2 A r => exact hcong_recK_tmPi2 A r s' hstep
  | tmLam1 f ctx x r => exact hcong_recK_tmLam1 f ctx x r s' hstep
  | tmLam2 A r => exact hcong_recK_tmLam2 A r s' hstep
  | arK f ctx r => exact hcong_recK_arK f ctx r s' hstep
  | arK2 a r => exact hcong_recK_arK2 a r s' hstep
  | apK f ctx r => exact hcong_recK_apK f ctx r s' hstep
  | apmK f ctx acc toks r => exact hcong_recK_apmK f ctx acc toks r s' hstep
  | atLPk f ctx r => exact hcong_recK_atLPk f ctx r s' hstep

theorem hcong_apK_at (f ctx g c t : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (at' g c t) = some s' →
      oneStep pLF (apK f ctx (at' g c t)) = some (apK f ctx s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "apK") [f, ctx, at' g c t]) = [] := rfl
  show oneStep pLF (.sexp (.id "apK") [f, ctx, at' g c t]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, h, Option.map_some, apK]

theorem hcong_arK_ap (f ctx g c t : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (ap g c t) = some s' →
      oneStep pLF (arK f ctx (ap g c t)) = some (arK f ctx s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "arK") [f, ctx, ap g c t]) = [] := rfl
  show oneStep pLF (.sexp (.id "arK") [f, ctx, ap g c t]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, h, Option.map_some, arK]

theorem hcong_arK_apK (f ctx g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (apK g c r) = some s' →
      oneStep pLF (arK f ctx (apK g c r)) = some (arK f ctx s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "arK") [f, ctx, apK g c r]) = [] := rfl
  show oneStep pLF (.sexp (.id "arK") [f, ctx, apK g c r]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, h, Option.map_some, arK]

theorem hcong_arK_active (f ctx : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (arK f ctx s) = some (arK f ctx s') := by
  intro s s' hactive hstep
  cases hactive with
  | tm g c toks =>
      exact hcong_arK_arg f ctx (tm g c toks) hf hctx rfl s' hstep
  | ar g c toks =>
      exact hcong_arK_arg f ctx (ar g c toks) hf hctx rfl s' hstep
  | ap g c toks =>
      exact hcong_arK_ap f ctx g c toks hf hctx s' hstep
  | apm g c acc toks =>
      exact hcong_arK_arg f ctx (apm g c acc toks) hf hctx rfl s' hstep
  | atom g c toks =>
      exact hcong_arK_arg f ctx (at' g c toks) hf hctx rfl s' hstep
  | tmPi1 g c x r =>
      exact hcong_arK_arg f ctx (tmPi1 g c x r) hf hctx rfl s' hstep
  | tmPi2 A r =>
      exact hcong_arK_arg f ctx (tmPi2 A r) hf hctx rfl s' hstep
  | tmLam1 g c x r =>
      exact hcong_arK_arg f ctx (tmLam1 g c x r) hf hctx rfl s' hstep
  | tmLam2 A r =>
      exact hcong_arK_arg f ctx (tmLam2 A r) hf hctx rfl s' hstep
  | arK g c r =>
      exact hcong_arK_arg f ctx (arK g c r) hf hctx rfl s' hstep
  | arK2 a r =>
      exact hcong_arK_arg f ctx (arK2 a r) hf hctx rfl s' hstep
  | apK g c r =>
      exact hcong_arK_apK f ctx g c r hf hctx s' hstep
  | apmK g c acc toks r =>
      exact hcong_arK_arg f ctx (apmK g c acc toks r) hf hctx rfl s' hstep
  | atLPk g c r =>
      exact hcong_arK_arg f ctx (atLPk g c r) hf hctx rfl s' hstep

theorem hcong_tmPi1_ap (f ctx x g c t : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none) :
    ∀ s', oneStep pLF (ap g c t) = some s' →
      oneStep pLF (tmPi1 f ctx x (ap g c t)) = some (tmPi1 f ctx x s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "tmPi1") [f, ctx, x, ap g c t]) = [] := rfl
  show oneStep pLF (.sexp (.id "tmPi1") [f, ctx, x, ap g c t]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, hx, h, Option.map_some, tmPi1]

theorem hcong_tmPi1_apK (f ctx x g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none) :
    ∀ s', oneStep pLF (apK g c r) = some s' →
      oneStep pLF (tmPi1 f ctx x (apK g c r)) = some (tmPi1 f ctx x s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "tmPi1") [f, ctx, x, apK g c r]) = [] := rfl
  show oneStep pLF (.sexp (.id "tmPi1") [f, ctx, x, apK g c r]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, hx, h, Option.map_some, tmPi1]

theorem hcong_tmLam1_ap (f ctx x g c t : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none) :
    ∀ s', oneStep pLF (ap g c t) = some s' →
      oneStep pLF (tmLam1 f ctx x (ap g c t)) = some (tmLam1 f ctx x s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "tmLam1") [f, ctx, x, ap g c t]) = [] := rfl
  show oneStep pLF (.sexp (.id "tmLam1") [f, ctx, x, ap g c t]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, hx, h, Option.map_some, tmLam1]

theorem hcong_tmLam1_apK (f ctx x g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none) :
    ∀ s', oneStep pLF (apK g c r) = some s' →
      oneStep pLF (tmLam1 f ctx x (apK g c r)) = some (tmLam1 f ctx x s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "tmLam1") [f, ctx, x, apK g c r]) = [] := rfl
  show oneStep pLF (.sexp (.id "tmLam1") [f, ctx, x, apK g c r]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, hx, h, Option.map_some, tmLam1]

theorem hcong_tmPi1_active (f ctx x : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none) :
    ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (tmPi1 f ctx x s) = some (tmPi1 f ctx x s') := by
  intro s s' hactive hstep
  cases hactive with
  | tm g c toks =>
      exact hcong_tmPi1_arg f ctx x (tm g c toks) hf hctx hx rfl s' hstep
  | ar g c toks =>
      exact hcong_tmPi1_arg f ctx x (ar g c toks) hf hctx hx rfl s' hstep
  | ap g c toks =>
      exact hcong_tmPi1_ap f ctx x g c toks hf hctx hx s' hstep
  | apm g c acc toks =>
      exact hcong_tmPi1_arg f ctx x (apm g c acc toks) hf hctx hx rfl s' hstep
  | atom g c toks =>
      exact hcong_tmPi1_arg f ctx x (at' g c toks) hf hctx hx rfl s' hstep
  | tmPi1 g c y r =>
      exact hcong_tmPi1_arg f ctx x (tmPi1 g c y r) hf hctx hx rfl s' hstep
  | tmPi2 A r =>
      exact hcong_tmPi1_arg f ctx x (tmPi2 A r) hf hctx hx rfl s' hstep
  | tmLam1 g c y r =>
      exact hcong_tmPi1_arg f ctx x (tmLam1 g c y r) hf hctx hx rfl s' hstep
  | tmLam2 A r =>
      exact hcong_tmPi1_arg f ctx x (tmLam2 A r) hf hctx hx rfl s' hstep
  | arK g c r =>
      exact hcong_tmPi1_arg f ctx x (arK g c r) hf hctx hx rfl s' hstep
  | arK2 a r =>
      exact hcong_tmPi1_arg f ctx x (arK2 a r) hf hctx hx rfl s' hstep
  | apK g c r =>
      exact hcong_tmPi1_apK f ctx x g c r hf hctx hx s' hstep
  | apmK g c acc toks r =>
      exact hcong_tmPi1_arg f ctx x (apmK g c acc toks r) hf hctx hx rfl s' hstep
  | atLPk g c r =>
      exact hcong_tmPi1_arg f ctx x (atLPk g c r) hf hctx hx rfl s' hstep

theorem hcong_tmLam1_active (f ctx x : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hx : oneStep pLF x = none) :
    ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (tmLam1 f ctx x s) = some (tmLam1 f ctx x s') := by
  intro s s' hactive hstep
  cases hactive with
  | tm g c toks =>
      exact hcong_tmLam1_arg f ctx x (tm g c toks) hf hctx hx rfl s' hstep
  | ar g c toks =>
      exact hcong_tmLam1_arg f ctx x (ar g c toks) hf hctx hx rfl s' hstep
  | ap g c toks =>
      exact hcong_tmLam1_ap f ctx x g c toks hf hctx hx s' hstep
  | apm g c acc toks =>
      exact hcong_tmLam1_arg f ctx x (apm g c acc toks) hf hctx hx rfl s' hstep
  | atom g c toks =>
      exact hcong_tmLam1_arg f ctx x (at' g c toks) hf hctx hx rfl s' hstep
  | tmPi1 g c y r =>
      exact hcong_tmLam1_arg f ctx x (tmPi1 g c y r) hf hctx hx rfl s' hstep
  | tmPi2 A r =>
      exact hcong_tmLam1_arg f ctx x (tmPi2 A r) hf hctx hx rfl s' hstep
  | tmLam1 g c y r =>
      exact hcong_tmLam1_arg f ctx x (tmLam1 g c y r) hf hctx hx rfl s' hstep
  | tmLam2 A r =>
      exact hcong_tmLam1_arg f ctx x (tmLam2 A r) hf hctx hx rfl s' hstep
  | arK g c r =>
      exact hcong_tmLam1_arg f ctx x (arK g c r) hf hctx hx rfl s' hstep
  | arK2 a r =>
      exact hcong_tmLam1_arg f ctx x (arK2 a r) hf hctx hx rfl s' hstep
  | apK g c r =>
      exact hcong_tmLam1_apK f ctx x g c r hf hctx hx s' hstep
  | apmK g c acc toks r =>
      exact hcong_tmLam1_arg f ctx x (apmK g c acc toks r) hf hctx hx rfl s' hstep
  | atLPk g c r =>
      exact hcong_tmLam1_arg f ctx x (atLPk g c r) hf hctx hx rfl s' hstep

theorem hcong_atLPk_tm (f ctx g c t : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (tm g c t) = some s' →
      oneStep pLF (atLPk f ctx (tm g c t)) = some (atLPk f ctx s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "atLPk") [f, ctx, tm g c t]) = [] := rfl
  show oneStep pLF (.sexp (.id "atLPk") [f, ctx, tm g c t]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, h, Option.map_some, atLPk]

theorem hcong_atLPk_atLPk (f ctx g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (atLPk g c r) = some s' →
      oneStep pLF (atLPk f ctx (atLPk g c r)) = some (atLPk f ctx s') :=
  hcong_atLPk_arg f ctx (atLPk g c r) hf hctx rfl

theorem hcong_atLPk_active (f ctx : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (atLPk f ctx s) = some (atLPk f ctx s') := by
  intro s s' hactive hstep
  cases hactive with
  | tm g c toks => exact hcong_atLPk_tm f ctx g c toks hf hctx s' hstep
  | ar g c toks => exact hcong_atLPk_ar f ctx g c toks hf hctx s' hstep
  | ap g c toks => exact hcong_atLPk_ap f ctx g c toks hf hctx s' hstep
  | apm g c acc toks => exact hcong_atLPk_apm f ctx g c acc toks hf hctx s' hstep
  | atom g c toks => exact hcong_atLPk_at f ctx g c toks hf hctx s' hstep
  | tmPi1 g c x r => exact hcong_atLPk_tmPi1 f ctx g c x r hf hctx s' hstep
  | tmPi2 A r => exact hcong_atLPk_tmPi2 f ctx A r hf hctx s' hstep
  | tmLam1 g c x r => exact hcong_atLPk_tmLam1 f ctx g c x r hf hctx s' hstep
  | tmLam2 A r => exact hcong_atLPk_tmLam2 f ctx A r hf hctx s' hstep
  | arK g c r => exact hcong_atLPk_arK f ctx g c r hf hctx s' hstep
  | arK2 a r => exact hcong_atLPk_arK2 f ctx a r hf hctx s' hstep
  | apK g c r => exact hcong_atLPk_apK f ctx g c r hf hctx s' hstep
  | apmK g c acc toks r => exact hcong_atLPk_apmK f ctx g c acc toks r hf hctx s' hstep
  | atLPk g c r => exact hcong_atLPk_atLPk f ctx g c r hf hctx s' hstep

theorem hcong_apK_atLPk (f ctx g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s', oneStep pLF (atLPk g c r) = some s' →
      oneStep pLF (apK f ctx (atLPk g c r)) = some (apK f ctx s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "apK") [f, ctx, atLPk g c r]) = [] := rfl
  show oneStep pLF (.sexp (.id "apK") [f, ctx, atLPk g c r]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, h, Option.map_some, apK]

theorem hcong_apK_active (f ctx : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (apK f ctx s) = some (apK f ctx s') := by
  intro s s' hactive hstep
  cases hactive with
  | tm g c toks =>
      exact hcong_apK_arg f ctx (tm g c toks) hf hctx rfl s' hstep
  | ar g c toks =>
      exact hcong_apK_arg f ctx (ar g c toks) hf hctx rfl s' hstep
  | ap g c toks =>
      exact hcong_apK_arg f ctx (ap g c toks) hf hctx rfl s' hstep
  | apm g c acc toks =>
      exact hcong_apK_arg f ctx (apm g c acc toks) hf hctx rfl s' hstep
  | atom g c toks =>
      exact hcong_apK_at f ctx g c toks hf hctx s' hstep
  | tmPi1 g c x r =>
      exact hcong_apK_arg f ctx (tmPi1 g c x r) hf hctx rfl s' hstep
  | tmPi2 A r =>
      exact hcong_apK_arg f ctx (tmPi2 A r) hf hctx rfl s' hstep
  | tmLam1 g c x r =>
      exact hcong_apK_arg f ctx (tmLam1 g c x r) hf hctx rfl s' hstep
  | tmLam2 A r =>
      exact hcong_apK_arg f ctx (tmLam2 A r) hf hctx rfl s' hstep
  | arK g c r =>
      exact hcong_apK_arg f ctx (arK g c r) hf hctx rfl s' hstep
  | arK2 a r =>
      exact hcong_apK_arg f ctx (arK2 a r) hf hctx rfl s' hstep
  | apK g c r =>
      exact hcong_apK_arg f ctx (apK g c r) hf hctx rfl s' hstep
  | apmK g c acc toks r =>
      exact hcong_apK_arg f ctx (apmK g c acc toks r) hf hctx rfl s' hstep
  | atLPk g c r =>
      exact hcong_apK_atLPk f ctx g c r hf hctx s' hstep

theorem hcong_apmK_at (f ctx acc toks g c t : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hacc : oneStep pLF acc = none) (htoks : oneStep pLF toks = none) :
    ∀ s', oneStep pLF (at' g c t) = some s' →
      oneStep pLF (apmK f ctx acc toks (at' g c t)) = some (apmK f ctx acc toks s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "apmK") [f, ctx, acc, toks, at' g c t]) = [] := rfl
  show oneStep pLF (.sexp (.id "apmK") [f, ctx, acc, toks, at' g c t]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, hacc, htoks, h, Option.map_some, apmK]

theorem hcong_apmK_atLPk (f ctx acc toks g c r : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hacc : oneStep pLF acc = none) (htoks : oneStep pLF toks = none) :
    ∀ s', oneStep pLF (atLPk g c r) = some s' →
      oneStep pLF (apmK f ctx acc toks (atLPk g c r))
        = some (apmK f ctx acc toks s') := by
  intro s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "apmK") [f, ctx, acc, toks, atLPk g c r]) = [] := rfl
  show oneStep pLF (.sexp (.id "apmK") [f, ctx, acc, toks, atLPk g c r]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, hacc, htoks, h, Option.map_some, apmK]

theorem hcong_apmK_acc_at (f ctx toks g c t : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none) :
    ∀ s s', oneStep pLF s = some s' →
      oneStep pLF (apmK f ctx s toks (at' g c t))
        = some (apmK f ctx s' toks (at' g c t)) := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "apmK") [f, ctx, s, toks, at' g c t]) = [] := rfl
  show oneStep pLF (.sexp (.id "apmK") [f, ctx, s, toks, at' g c t]) = _
  simp only [oneStep, hb, oneStepList, hf, hctx, h, Option.map_some, apmK]

theorem hcong_apmK_active (f ctx acc toks : AST)
    (hf : oneStep pLF f = none) (hctx : oneStep pLF ctx = none)
    (hacc : oneStep pLF acc = none) (htoks : oneStep pLF toks = none) :
    ∀ s s', ParserActiveShape s → oneStep pLF s = some s' →
      oneStep pLF (apmK f ctx acc toks s) = some (apmK f ctx acc toks s') := by
  intro s s' hactive hstep
  cases hactive with
  | tm g c ts =>
      exact hcong_apmK_arg f ctx acc toks (tm g c ts) hf hctx hacc htoks rfl s' hstep
  | ar g c ts =>
      exact hcong_apmK_arg f ctx acc toks (ar g c ts) hf hctx hacc htoks rfl s' hstep
  | ap g c ts =>
      exact hcong_apmK_arg f ctx acc toks (ap g c ts) hf hctx hacc htoks rfl s' hstep
  | apm g c a ts =>
      exact hcong_apmK_arg f ctx acc toks (apm g c a ts) hf hctx hacc htoks rfl s' hstep
  | atom g c ts =>
      exact hcong_apmK_at f ctx acc toks g c ts hf hctx hacc htoks s' hstep
  | tmPi1 g c x r =>
      exact hcong_apmK_arg f ctx acc toks (tmPi1 g c x r) hf hctx hacc htoks rfl s' hstep
  | tmPi2 A r =>
      exact hcong_apmK_arg f ctx acc toks (tmPi2 A r) hf hctx hacc htoks rfl s' hstep
  | tmLam1 g c x r =>
      exact hcong_apmK_arg f ctx acc toks (tmLam1 g c x r) hf hctx hacc htoks rfl s' hstep
  | tmLam2 A r =>
      exact hcong_apmK_arg f ctx acc toks (tmLam2 A r) hf hctx hacc htoks rfl s' hstep
  | arK g c r =>
      exact hcong_apmK_arg f ctx acc toks (arK g c r) hf hctx hacc htoks rfl s' hstep
  | arK2 a r =>
      exact hcong_apmK_arg f ctx acc toks (arK2 a r) hf hctx hacc htoks rfl s' hstep
  | apK g c r =>
      exact hcong_apmK_arg f ctx acc toks (apK g c r) hf hctx hacc htoks rfl s' hstep
  | apmK g c a ts r =>
      exact hcong_apmK_arg f ctx acc toks (apmK g c a ts r) hf hctx hacc htoks rfl s' hstep
  | atLPk g c r =>
      exact hcong_apmK_atLPk f ctx acc toks g c r hf hctx hacc htoks s' hstep

/-! ## One-step dispatch facts for `lf-atom` leaves -/

theorem os_tm_z (ctx toks : AST) :
    oneStep pLF (tm Z ctx toks) = some (PErr (con0 "no-fuel")) := by rfl

theorem os_ar_z (ctx toks : AST) :
    oneStep pLF (ar Z ctx toks) = some (PErr (con0 "no-fuel")) := by rfl

theorem os_ap_z (ctx toks : AST) :
    oneStep pLF (ap Z ctx toks) = some (PErr (con0 "no-fuel")) := by rfl

theorem os_apm_z (ctx acc toks : AST) :
    oneStep pLF (apm Z ctx acc toks) = some (Pp acc toks) := by rfl

theorem os_at_z (ctx toks : AST) :
    oneStep pLF (at' Z ctx toks) = some (PErr (con0 "no-fuel")) := by rfl

theorem os_tm_pi (f ctx x rest : AST) :
    oneStep pLF (tm (S f) ctx (Cons tPI (Cons (tId x) (Cons tCOLON rest))))
      = some (tmPi1 f ctx x (ap f ctx rest)) := by
  rfl

theorem os_tm_lam (f ctx x rest : AST) :
    oneStep pLF (tm (S f) ctx (Cons tLAM (Cons (tId x) (Cons tCOLON rest))))
      = some (tmLam1 f ctx x (ap f ctx rest)) := by
  rfl

theorem os_tmPi1_dot (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tDOT rest)))
      = some (tmPi2 A (tm f (Cons x ctx) rest)) := by
  rfl

theorem os_tmPi1_pi (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tPI rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_lam (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tLAM rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_arr (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tARR rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_colon (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tCOLON rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_lp (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tLP rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_rp (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tRP rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_type (f ctx x A rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons tTYPE rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_id (f ctx x A s rest : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A (Cons (tId s) rest)))
      = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_nil (f ctx x A : AST) :
    oneStep pLF (tmPi1 f ctx x (Pp A Nil)) = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi1_err (f ctx x e : AST) :
    oneStep pLF (tmPi1 f ctx x (PErr e)) = some (PErr (con0 "pi-malformed")) := by
  rfl

theorem os_tmPi2_p (A B rest : AST) :
    oneStep pLF (tmPi2 A (Pp B rest)) = some (Pp (Pi A B) rest) := by
  rfl

theorem os_tmPi2_err (A e : AST) :
    oneStep pLF (tmPi2 A (PErr e)) = some (PErr e) := by
  rfl

theorem os_tmLam1_dot (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tDOT rest)))
      = some (tmLam2 A (tm f (Cons x ctx) rest)) := by
  rfl

theorem os_tmLam1_pi (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tPI rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_lam (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tLAM rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_arr (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tARR rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_colon (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tCOLON rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_lp (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tLP rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_rp (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tRP rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_type (f ctx x A rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons tTYPE rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_id (f ctx x A s rest : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A (Cons (tId s) rest)))
      = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_nil (f ctx x A : AST) :
    oneStep pLF (tmLam1 f ctx x (Pp A Nil)) = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam1_err (f ctx x e : AST) :
    oneStep pLF (tmLam1 f ctx x (PErr e)) = some (PErr (con0 "lam-malformed")) := by
  rfl

theorem os_tmLam2_p (A b rest : AST) :
    oneStep pLF (tmLam2 A (Pp b rest)) = some (Pp (Lam A b) rest) := by
  rfl

theorem os_tmLam2_err (A e : AST) :
    oneStep pLF (tmLam2 A (PErr e)) = some (PErr e) := by
  rfl

theorem os_ar_s (f ctx toks : AST) :
    oneStep pLF (ar (S f) ctx toks) = some (arK f ctx (ap f ctx toks)) := by
  rfl

theorem os_arK_arr (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tARR rest))) = some (arK2 a (tm f ctx rest)) := by
  rfl

theorem os_arK_pi (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tPI rest))) = some (Pp a (Cons tPI rest)) := by
  rfl

theorem os_arK_lam (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tLAM rest))) = some (Pp a (Cons tLAM rest)) := by
  rfl

theorem os_arK_colon (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tCOLON rest))) = some (Pp a (Cons tCOLON rest)) := by
  rfl

theorem os_arK_dot (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tDOT rest))) = some (Pp a (Cons tDOT rest)) := by
  rfl

theorem os_arK_lp (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tLP rest))) = some (Pp a (Cons tLP rest)) := by
  rfl

theorem os_arK_rp (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tRP rest))) = some (Pp a (Cons tRP rest)) := by
  rfl

theorem os_arK_type (f ctx a rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons tTYPE rest))) = some (Pp a (Cons tTYPE rest)) := by
  rfl

theorem os_arK_id (f ctx a s rest : AST) :
    oneStep pLF (arK f ctx (Pp a (Cons (tId s) rest))) = some (Pp a (Cons (tId s) rest)) := by
  rfl

theorem os_arK_nil (f ctx a : AST) :
    oneStep pLF (arK f ctx (Pp a Nil)) = some (Pp a Nil) := by
  rfl

theorem os_arK_err (f ctx e : AST) :
    oneStep pLF (arK f ctx (PErr e)) = some (PErr e) := by
  rfl

theorem os_arK2_p (a b rest : AST) :
    oneStep pLF (arK2 a (Pp b rest)) = some (Pp (Pi a (shift Z b)) rest) := by
  rfl

theorem os_arK2_err (a e : AST) :
    oneStep pLF (arK2 a (PErr e)) = some (PErr e) := by
  rfl

theorem os_ap_s (f ctx toks : AST) :
    oneStep pLF (ap (S f) ctx toks) = some (apK f ctx (at' f ctx toks)) := by
  rfl

theorem os_apK_p (f ctx a rest : AST) :
    oneStep pLF (apK f ctx (Pp a rest)) = some (apm f ctx a rest) := by
  rfl

theorem os_apK_err (f ctx e : AST) :
    oneStep pLF (apK f ctx (PErr e)) = some (PErr e) := by
  rfl

theorem os_apm_s (f ctx acc toks : AST) :
    oneStep pLF (apm (S f) ctx acc toks)
      = some (apmK f ctx acc toks (at' f ctx toks)) := by rfl

theorem os_apmK_err (f ctx acc toks e : AST) :
    oneStep pLF (apmK f ctx acc toks (PErr e)) = some (Pp acc toks) := by rfl

theorem os_apmK_p (f ctx acc toks a rest : AST) :
    oneStep pLF (apmK f ctx acc toks (Pp a rest)) = some (apm f ctx (App acc a) rest) := by
  rfl

theorem os_at_type (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tTYPE rest)) = some (Pp (Srt (con0 "type")) rest) := by
  rfl

theorem os_at_id (f ctx s rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons (tId s) rest)) = some (Pp (resolve ctx s) rest) := by
  rfl

theorem os_at_lp (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tLP rest)) = some (atLPk f ctx (tm f ctx rest)) := by
  rfl

theorem os_atLPk_rp (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tRP rest))) = some (Pp t rest) := by
  rfl

theorem os_atLPk_pi (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tPI rest))) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_lam (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tLAM rest))) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_arr (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tARR rest))) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_colon (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tCOLON rest))) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_dot (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tDOT rest))) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_lp (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tLP rest))) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_type (f ctx t rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons tTYPE rest))) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_id (f ctx t s rest : AST) :
    oneStep pLF (atLPk f ctx (Pp t (Cons (tId s) rest))) =
      some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_nil (f ctx t : AST) :
    oneStep pLF (atLPk f ctx (Pp t Nil)) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_atLPk_err (f ctx e : AST) :
    oneStep pLF (atLPk f ctx (PErr e)) = some (PErr (con0 "paren-malformed")) := by
  rfl

theorem os_at_err_nil (f ctx : AST) :
    oneStep pLF (at' (S f) ctx Nil) = some (PErr (con0 "atom-expected")) := by rfl

theorem os_at_err_pi (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tPI rest)) = some (PErr (con0 "atom-expected")) := by rfl

theorem os_at_err_lam (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tLAM rest)) = some (PErr (con0 "atom-expected")) := by rfl

theorem os_at_err_arr (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tARR rest)) = some (PErr (con0 "atom-expected")) := by rfl

theorem os_at_err_colon (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tCOLON rest)) = some (PErr (con0 "atom-expected")) := by rfl

theorem os_at_err_dot (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tDOT rest)) = some (PErr (con0 "atom-expected")) := by rfl

theorem os_at_err_rp (f ctx rest : AST) :
    oneStep pLF (at' (S f) ctx (Cons tRP rest)) = some (PErr (con0 "atom-expected")) := by rfl

theorem os_recK_p_nil (t : AST) :
    oneStep pLF (recK (Pp t Nil)) = some (Ok t) := by
  rfl

theorem os_recK_p_cons (t h r : AST) :
    oneStep pLF (recK (Pp t (Cons h r))) = some (Err (extraToks (Cons h r))) := by
  rfl

theorem os_recK_err (e : AST) :
    oneStep pLF (recK (PErr e)) = some (Err e) := by
  rfl

theorem os_lfrec (t : AST) :
    oneStep pLF (lfrec t) = some (recK (tm (peano 64) Nil t)) := by
  rfl

/-! ## Leaf simulations for `lf-atom` -/

theorem term_no_fuel_sim (ctx : List String) (toks : List LF.Tok) :
    eval pLF 1 (tm Z (encCtx ctx) (encToks toks)) = PErr (con0 "no-fuel") := by
  simp only [eval, os_tm_z]

theorem term_no_fuel_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pTerm 0 ctx toks)
      (eval pLF N (tm Z (encCtx ctx) (encToks toks))) := by
  refine ⟨1, ?_⟩
  rw [term_no_fuel_sim]
  exact matches_parse_none (con0 "no-fuel")

theorem term_no_fuel_first_raw (ctx : List String) (toks : List LF.Tok) :
    FirstMatchesParseRaw (LF.pTerm 0 ctx toks)
      (tm Z (encCtx ctx) (encToks toks)) := by
  exact first_matches_one (term_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (not_result_tm Z (encCtx ctx) (encToks toks))

theorem term_no_fuel_first_active (ctx : List String) (toks : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pTerm 0 ctx toks)
      (tm Z (encCtx ctx) (encToks toks)) := by
  exact first_active_one (term_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (ParserActiveShape.tm Z (encCtx ctx) (encToks toks))

theorem arrow_no_fuel_sim (ctx : List String) (toks : List LF.Tok) :
    eval pLF 1 (ar Z (encCtx ctx) (encToks toks)) = PErr (con0 "no-fuel") := by
  simp only [eval, os_ar_z]

theorem arrow_no_fuel_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pArrow 0 ctx toks)
      (eval pLF N (ar Z (encCtx ctx) (encToks toks))) := by
  refine ⟨1, ?_⟩
  rw [arrow_no_fuel_sim]
  exact matches_parse_none (con0 "no-fuel")

theorem arrow_no_fuel_first_raw (ctx : List String) (toks : List LF.Tok) :
    FirstMatchesParseRaw (LF.pArrow 0 ctx toks)
      (ar Z (encCtx ctx) (encToks toks)) := by
  exact first_matches_one (arrow_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (not_result_ar Z (encCtx ctx) (encToks toks))

theorem arrow_no_fuel_first_active (ctx : List String) (toks : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pArrow 0 ctx toks)
      (ar Z (encCtx ctx) (encToks toks)) := by
  exact first_active_one (arrow_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (ParserActiveShape.ar Z (encCtx ctx) (encToks toks))

theorem app_no_fuel_sim (ctx : List String) (toks : List LF.Tok) :
    eval pLF 1 (ap Z (encCtx ctx) (encToks toks)) = PErr (con0 "no-fuel") := by
  simp only [eval, os_ap_z]

theorem app_no_fuel_raw_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParseRaw (LF.pApp 0 ctx toks)
      (eval pLF N (ap Z (encCtx ctx) (encToks toks))) := by
  refine ⟨1, ?_⟩
  rw [app_no_fuel_sim]
  exact matches_parse_raw_none (con0 "no-fuel")

theorem app_no_fuel_first_raw (ctx : List String) (toks : List LF.Tok) :
    FirstMatchesParseRaw (LF.pApp 0 ctx toks)
      (ap Z (encCtx ctx) (encToks toks)) := by
  exact first_matches_one (app_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (not_result_ap Z (encCtx ctx) (encToks toks))

theorem app_no_fuel_first_active (ctx : List String) (toks : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pApp 0 ctx toks)
      (ap Z (encCtx ctx) (encToks toks)) := by
  exact first_active_one (app_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (ParserActiveShape.ap Z (encCtx ctx) (encToks toks))

theorem app_no_fuel_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pApp 0 ctx toks)
      (eval pLF N (ap Z (encCtx ctx) (encToks toks))) := by
  obtain ⟨N, hN⟩ := app_no_fuel_raw_matches ctx toks
  exact matches_parse_exact_of_raw_eval hN

theorem arrow_one_sim (ctx : List String) (toks : List LF.Tok) :
    eval pLF 3 (ar (peano (0 + 1)) (encCtx ctx) (encToks toks))
      = PErr (con0 "no-fuel") := by
  have hap : oneStep pLF (ap Z (encCtx ctx) (encToks toks)) = some (PErr (con0 "no-fuel")) := by
    simp only [os_ap_z]
  have hstep2 := hcong_arK_ap Z (encCtx ctx) Z (encCtx ctx) (encToks toks)
    (isnormal_peano 0) (isnormal_encCtx ctx) (PErr (con0 "no-fuel")) hap
  simp only [peano, eval, os_ar_s, hstep2, os_arK_err]

theorem arrow_one_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pArrow (0 + 1) ctx toks)
      (eval pLF N (ar (peano (0 + 1)) (encCtx ctx) (encToks toks))) := by
  refine ⟨3, ?_⟩
  rw [arrow_one_sim]
  exact matches_parse_none (con0 "no-fuel")

theorem arrow_two_sim (ctx : List String) (toks : List LF.Tok) :
    eval pLF 5 (ar (peano ((0 + 1) + 1)) (encCtx ctx) (encToks toks))
      = PErr (con0 "no-fuel") := by
  have hap_s : oneStep pLF (ap (S Z) (encCtx ctx) (encToks toks))
      = some (apK Z (encCtx ctx) (at' Z (encCtx ctx) (encToks toks))) := by
    simp only [os_ap_s]
  have hstep2 := hcong_arK_ap (S Z) (encCtx ctx) (S Z) (encCtx ctx) (encToks toks)
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx)
    (apK Z (encCtx ctx) (at' Z (encCtx ctx) (encToks toks))) hap_s
  have hat_z : oneStep pLF (at' Z (encCtx ctx) (encToks toks)) = some (PErr (con0 "no-fuel")) := by
    simp only [os_at_z]
  have hapK_step := hcong_apK_at Z (encCtx ctx) Z (encCtx ctx) (encToks toks)
    (isnormal_peano 0) (isnormal_encCtx ctx) (PErr (con0 "no-fuel")) hat_z
  have hstep3 := hcong_arK_apK (S Z) (encCtx ctx) Z (encCtx ctx)
    (at' Z (encCtx ctx) (encToks toks))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx)
    (apK Z (encCtx ctx) (PErr (con0 "no-fuel"))) hapK_step
  have hapK_err : oneStep pLF (apK Z (encCtx ctx) (PErr (con0 "no-fuel")))
      = some (PErr (con0 "no-fuel")) := by
    simp only [os_apK_err]
  have hstep4 := hcong_arK_apK (S Z) (encCtx ctx) Z (encCtx ctx) (PErr (con0 "no-fuel"))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (PErr (con0 "no-fuel")) hapK_err
  simp only [peano, eval, os_ar_s, hstep2, hstep3, hstep4, os_arK_err]

theorem arrow_two_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pArrow ((0 + 1) + 1) ctx toks)
      (eval pLF N (ar (peano ((0 + 1) + 1)) (encCtx ctx) (encToks toks))) := by
  refine ⟨5, ?_⟩
  rw [arrow_two_sim]
  exact matches_parse_none (con0 "no-fuel")

theorem term_one_pi_malformed_sim (ctx : List String) (x : String) (rest : List LF.Tok) :
    eval pLF 3 (tm (peano (0 + 1)) (encCtx ctx)
      (encToks (.pi :: .id x :: .colon :: rest)))
      = PErr (con0 "pi-malformed") := by
  have hap : oneStep pLF (ap Z (encCtx ctx) (encToks rest)) = some (PErr (con0 "no-fuel")) := by
    simp only [os_ap_z]
  have hstep2 := hcong_tmPi1_ap Z (encCtx ctx) (con0 x) Z (encCtx ctx) (encToks rest)
    (isnormal_peano 0) (isnormal_encCtx ctx) (isnormal_con0 x)
    (PErr (con0 "no-fuel")) hap
  simp only [peano, encToks, encTok, eval, os_tm_pi, hstep2, os_tmPi1_err]

theorem term_one_pi_malformed_matches (ctx : List String) (x : String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pTerm (0 + 1) ctx (.pi :: .id x :: .colon :: rest))
      (eval pLF N (tm (peano (0 + 1)) (encCtx ctx)
        (encToks (.pi :: .id x :: .colon :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [term_one_pi_malformed_sim]
  exact matches_parse_none (con0 "pi-malformed")

theorem term_one_lam_malformed_sim (ctx : List String) (x : String) (rest : List LF.Tok) :
    eval pLF 3 (tm (peano (0 + 1)) (encCtx ctx)
      (encToks (.lam :: .id x :: .colon :: rest)))
      = PErr (con0 "lam-malformed") := by
  have hap : oneStep pLF (ap Z (encCtx ctx) (encToks rest)) = some (PErr (con0 "no-fuel")) := by
    simp only [os_ap_z]
  have hstep2 := hcong_tmLam1_ap Z (encCtx ctx) (con0 x) Z (encCtx ctx) (encToks rest)
    (isnormal_peano 0) (isnormal_encCtx ctx) (isnormal_con0 x)
    (PErr (con0 "no-fuel")) hap
  simp only [peano, encToks, encTok, eval, os_tm_lam, hstep2, os_tmLam1_err]

theorem term_one_lam_malformed_matches (ctx : List String) (x : String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pTerm (0 + 1) ctx (.lam :: .id x :: .colon :: rest))
      (eval pLF N (tm (peano (0 + 1)) (encCtx ctx)
        (encToks (.lam :: .id x :: .colon :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [term_one_lam_malformed_sim]
  exact matches_parse_none (con0 "lam-malformed")

theorem term_two_pi_malformed_sim (ctx : List String) (x : String) (rest : List LF.Tok) :
    eval pLF 5 (tm (peano ((0 + 1) + 1)) (encCtx ctx)
      (encToks (.pi :: .id x :: .colon :: rest)))
      = PErr (con0 "pi-malformed") := by
  have hap_s : oneStep pLF (ap (S Z) (encCtx ctx) (encToks rest))
      = some (apK Z (encCtx ctx) (at' Z (encCtx ctx) (encToks rest))) := by
    simp only [os_ap_s]
  have hstep2 := hcong_tmPi1_ap (S Z) (encCtx ctx) (con0 x) (S Z) (encCtx ctx)
    (encToks rest) (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_con0 x)
    (apK Z (encCtx ctx) (at' Z (encCtx ctx) (encToks rest))) hap_s
  have hat_z : oneStep pLF (at' Z (encCtx ctx) (encToks rest))
      = some (PErr (con0 "no-fuel")) := by
    simp only [os_at_z]
  have hapK_at := hcong_apK_at Z (encCtx ctx) Z (encCtx ctx) (encToks rest)
    (isnormal_peano 0) (isnormal_encCtx ctx) (PErr (con0 "no-fuel")) hat_z
  have hstep3 := hcong_tmPi1_apK (S Z) (encCtx ctx) (con0 x) Z (encCtx ctx)
    (at' Z (encCtx ctx) (encToks rest))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_con0 x)
    (apK Z (encCtx ctx) (PErr (con0 "no-fuel"))) hapK_at
  have hapK_err : oneStep pLF (apK Z (encCtx ctx) (PErr (con0 "no-fuel")))
      = some (PErr (con0 "no-fuel")) := by
    simp only [os_apK_err]
  have hstep4 := hcong_tmPi1_apK (S Z) (encCtx ctx) (con0 x) Z (encCtx ctx)
    (PErr (con0 "no-fuel"))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_con0 x)
    (PErr (con0 "no-fuel")) hapK_err
  simp only [peano, encToks, encTok, eval, os_tm_pi, hstep2, hstep3, hstep4, os_tmPi1_err]

theorem term_two_pi_malformed_matches (ctx : List String) (x : String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pTerm ((0 + 1) + 1) ctx (.pi :: .id x :: .colon :: rest))
      (eval pLF N (tm (peano ((0 + 1) + 1)) (encCtx ctx)
        (encToks (.pi :: .id x :: .colon :: rest)))) := by
  refine ⟨5, ?_⟩
  rw [term_two_pi_malformed_sim]
  exact matches_parse_none (con0 "pi-malformed")

theorem term_two_lam_malformed_sim (ctx : List String) (x : String) (rest : List LF.Tok) :
    eval pLF 5 (tm (peano ((0 + 1) + 1)) (encCtx ctx)
      (encToks (.lam :: .id x :: .colon :: rest)))
      = PErr (con0 "lam-malformed") := by
  have hap_s : oneStep pLF (ap (S Z) (encCtx ctx) (encToks rest))
      = some (apK Z (encCtx ctx) (at' Z (encCtx ctx) (encToks rest))) := by
    simp only [os_ap_s]
  have hstep2 := hcong_tmLam1_ap (S Z) (encCtx ctx) (con0 x) (S Z) (encCtx ctx)
    (encToks rest) (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_con0 x)
    (apK Z (encCtx ctx) (at' Z (encCtx ctx) (encToks rest))) hap_s
  have hat_z : oneStep pLF (at' Z (encCtx ctx) (encToks rest))
      = some (PErr (con0 "no-fuel")) := by
    simp only [os_at_z]
  have hapK_at := hcong_apK_at Z (encCtx ctx) Z (encCtx ctx) (encToks rest)
    (isnormal_peano 0) (isnormal_encCtx ctx) (PErr (con0 "no-fuel")) hat_z
  have hstep3 := hcong_tmLam1_apK (S Z) (encCtx ctx) (con0 x) Z (encCtx ctx)
    (at' Z (encCtx ctx) (encToks rest))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_con0 x)
    (apK Z (encCtx ctx) (PErr (con0 "no-fuel"))) hapK_at
  have hapK_err : oneStep pLF (apK Z (encCtx ctx) (PErr (con0 "no-fuel")))
      = some (PErr (con0 "no-fuel")) := by
    simp only [os_apK_err]
  have hstep4 := hcong_tmLam1_apK (S Z) (encCtx ctx) (con0 x) Z (encCtx ctx)
    (PErr (con0 "no-fuel"))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_con0 x)
    (PErr (con0 "no-fuel")) hapK_err
  simp only [peano, encToks, encTok, eval, os_tm_lam, hstep2, hstep3, hstep4, os_tmLam1_err]

theorem term_two_lam_malformed_matches (ctx : List String) (x : String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pTerm ((0 + 1) + 1) ctx (.lam :: .id x :: .colon :: rest))
      (eval pLF N (tm (peano ((0 + 1) + 1)) (encCtx ctx)
        (encToks (.lam :: .id x :: .colon :: rest)))) := by
  refine ⟨5, ?_⟩
  rw [term_two_lam_malformed_sim]
  exact matches_parse_none (con0 "lam-malformed")

theorem tmPi2_matches_raw_of_term_result (fuel : Nat) (ctx : List String) (A : LF.Term)
    (Araw : AST) (hA : ReducesToEncTerm Araw A) (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    ∃ N, MatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (eval pLF N (tmPi2 Araw v)) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      simp only [eval, os_tmPi2_err]
      exact matches_parse_raw_none e
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      refine ⟨1, ?_⟩
      simp only [eval, os_tmPi2_p]
      exact matches_parse_raw_some_of_reduces rest (reduces_pi hA hB)

theorem tmPi2_matches_first_raw_of_term_result (fuel : Nat) (ctx : List String) (A : LF.Term)
    (Araw : AST) (hA : ReducesToEncTerm Araw A) (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    FirstMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (tmPi2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_matches_one (by simp only [eval, os_tmPi2_err])
        (matches_parse_raw_none e) (not_result_tmPi2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      exact first_matches_one (by simp only [eval, os_tmPi2_p])
        (matches_parse_raw_some_of_reduces rest (reduces_pi hA hB))
        (not_result_tmPi2 Araw (Pp Braw (encToks rest)))

theorem tmPi2_matches_first_active_of_term_result (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ReducesToEncTerm Araw A)
    (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (tmPi2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_active_one (by simp only [eval, os_tmPi2_err])
        (matches_parse_raw_none e)
        (ParserActiveShape.tmPi2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      exact first_active_one (by simp only [eval, os_tmPi2_p])
        (matches_parse_raw_some_of_reduces rest (reduces_pi hA hB))
        (ParserActiveShape.tmPi2 Araw (Pp Braw (encToks rest)))

theorem tmPi2_matches_first_active_of_term_first_active (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ReducesToEncTerm Araw A)
    (bodyToks : List LF.Tok)
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm fuel ctx bodyToks)
      (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) :
    FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (tmPi2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) := by
  let child := tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  rcases hA with ⟨NA, hNA⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => tmPi2 a child)
      (fun a => ParserActiveShape.tmPi2 a child)
      (hcong_tmPi2_left_active_child child hchildActive)
      NA hNA
  have htail : FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (tmPi2 (encTerm A) child) :=
    first_active_bind_active
      (fun s => tmPi2 (encTerm A) s)
      (fun s _ => ParserActiveShape.tmPi2 (encTerm A) s)
      (hcong_tmPi2_right_active (encTerm A) (isnormal_encTerm A))
      hfirst
      (fun {v} hv =>
        tmPi2_matches_first_active_of_term_result fuel ctx A (encTerm A)
          (reduces_encTerm_refl A) bodyToks hv)
  exact first_active_prepend_eval hMnorm hNormGuard htail

theorem tmLam2_matches_raw_of_term_result (fuel : Nat) (ctx : List String) (A : LF.Term)
    (Araw : AST) (hA : ReducesToEncTerm Araw A) (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    ∃ N, MatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (eval pLF N (tmLam2 Araw v)) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      simp only [eval, os_tmLam2_err]
      exact matches_parse_raw_none e
  | some pr =>
      rcases pr with ⟨b, rest⟩
      rw [hbody] at h
      rcases h with ⟨braw, rfl, hb⟩
      refine ⟨1, ?_⟩
      simp only [eval, os_tmLam2_p]
      exact matches_parse_raw_some_of_reduces rest (reduces_lam hA hb)

theorem tmLam2_matches_first_raw_of_term_result (fuel : Nat) (ctx : List String) (A : LF.Term)
    (Araw : AST) (hA : ReducesToEncTerm Araw A) (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    FirstMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (tmLam2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_matches_one (by simp only [eval, os_tmLam2_err])
        (matches_parse_raw_none e) (not_result_tmLam2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨b, rest⟩
      rw [hbody] at h
      rcases h with ⟨braw, rfl, hb⟩
      exact first_matches_one (by simp only [eval, os_tmLam2_p])
        (matches_parse_raw_some_of_reduces rest (reduces_lam hA hb))
        (not_result_tmLam2 Araw (Pp braw (encToks rest)))

theorem tmLam2_matches_first_active_of_term_result (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ReducesToEncTerm Araw A)
    (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (tmLam2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_active_one (by simp only [eval, os_tmLam2_err])
        (matches_parse_raw_none e)
        (ParserActiveShape.tmLam2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨b, rest⟩
      rw [hbody] at h
      rcases h with ⟨braw, rfl, hb⟩
      exact first_active_one (by simp only [eval, os_tmLam2_p])
        (matches_parse_raw_some_of_reduces rest (reduces_lam hA hb))
        (ParserActiveShape.tmLam2 Araw (Pp braw (encToks rest)))

theorem tmLam2_matches_first_active_of_term_first_active (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ReducesToEncTerm Araw A)
    (bodyToks : List LF.Tok)
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm fuel ctx bodyToks)
      (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) :
    FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (tmLam2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) := by
  let child := tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  rcases hA with ⟨NA, hNA⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => tmLam2 a child)
      (fun a => ParserActiveShape.tmLam2 a child)
      (hcong_tmLam2_left_active_child child hchildActive)
      NA hNA
  have htail : FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (tmLam2 (encTerm A) child) :=
    first_active_bind_active
      (fun s => tmLam2 (encTerm A) s)
      (fun s _ => ParserActiveShape.tmLam2 (encTerm A) s)
      (hcong_tmLam2_right_active (encTerm A) (isnormal_encTerm A))
      hfirst
      (fun {v} hv =>
        tmLam2_matches_first_active_of_term_result fuel ctx A (encTerm A)
          (reduces_encTerm_refl A) bodyToks hv)
  exact first_active_prepend_eval hMnorm hNormGuard htail

theorem tmPi2_matches_first_active_shiftable_of_term_result (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ShiftablePayload Araw A)
    (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseShiftable (LF.pTerm fuel ctx bodyToks) v) :
    FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (tmPi2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_active_shiftable_one (by simp only [eval, os_tmPi2_err])
        (matches_parse_shiftable_none e)
        (ParserActiveShape.tmPi2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      exact first_active_shiftable_one (by simp only [eval, os_tmPi2_p])
        (matches_parse_shiftable_some_of_payload (shiftable_pi hA hB))
        (ParserActiveShape.tmPi2 Araw (Pp Braw (encToks rest)))

theorem tmPi2_matches_first_active_shiftable_of_term_first_active (fuel : Nat)
    (ctx : List String) (A : LF.Term) (Araw : AST) (hA : ShiftablePayload Araw A)
    (bodyToks : List LF.Tok)
    (hfirst : FirstActiveMatchesParseShiftable (LF.pTerm fuel ctx bodyToks)
      (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) :
    FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (tmPi2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) := by
  let child := tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  rcases hA.reduces with ⟨NA, hNA⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => tmPi2 a child)
      (fun a => ParserActiveShape.tmPi2 a child)
      (hcong_tmPi2_left_active_child child hchildActive)
      NA hNA
  have htail : FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A B, rest)
       | none => none)
      (tmPi2 (encTerm A) child) :=
    first_active_shiftable_bind_active
      (fun s => tmPi2 (encTerm A) s)
      (fun s _ => ParserActiveShape.tmPi2 (encTerm A) s)
      (hcong_tmPi2_right_active (encTerm A) (isnormal_encTerm A))
      hfirst
      (fun {v} hv =>
        tmPi2_matches_first_active_shiftable_of_term_result fuel ctx A (encTerm A)
          (shiftable_encTerm A) bodyToks hv)
  exact first_active_shiftable_prepend_eval hMnorm hNormGuard htail

theorem tmLam2_matches_first_active_shiftable_of_term_result (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ShiftablePayload Araw A)
    (bodyToks : List LF.Tok) {v : AST}
    (h : MatchesParseShiftable (LF.pTerm fuel ctx bodyToks) v) :
    FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (tmLam2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_active_shiftable_one (by simp only [eval, os_tmLam2_err])
        (matches_parse_shiftable_none e)
        (ParserActiveShape.tmLam2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨b, rest⟩
      rw [hbody] at h
      rcases h with ⟨braw, rfl, hb⟩
      exact first_active_shiftable_one (by simp only [eval, os_tmLam2_p])
        (matches_parse_shiftable_some_of_payload (shiftable_lam hA hb))
        (ParserActiveShape.tmLam2 Araw (Pp braw (encToks rest)))

theorem tmLam2_matches_first_active_shiftable_of_term_first_active (fuel : Nat)
    (ctx : List String) (A : LF.Term) (Araw : AST) (hA : ShiftablePayload Araw A)
    (bodyToks : List LF.Tok)
    (hfirst : FirstActiveMatchesParseShiftable (LF.pTerm fuel ctx bodyToks)
      (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) :
    FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (tmLam2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) := by
  let child := tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  rcases hA.reduces with ⟨NA, hNA⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => tmLam2 a child)
      (fun a => ParserActiveShape.tmLam2 a child)
      (hcong_tmLam2_left_active_child child hchildActive)
      NA hNA
  have htail : FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (b, rest) => some (.lam A b, rest)
       | none => none)
      (tmLam2 (encTerm A) child) :=
    first_active_shiftable_bind_active
      (fun s => tmLam2 (encTerm A) s)
      (fun s _ => ParserActiveShape.tmLam2 (encTerm A) s)
      (hcong_tmLam2_right_active (encTerm A) (isnormal_encTerm A))
      hfirst
      (fun {v} hv =>
        tmLam2_matches_first_active_shiftable_of_term_result fuel ctx A (encTerm A)
          (shiftable_encTerm A) bodyToks hv)
  exact first_active_shiftable_prepend_eval hMnorm hNormGuard htail

theorem arK2_matches_raw_of_term_result (fuel : Nat) (ctx : List String) (A : LF.Term)
    (Araw : AST) (hA : ReducesToEncTerm Araw A) (bodyToks : List LF.Tok) {v : AST}
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B))
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    ∃ N, MatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (eval pLF N (arK2 Araw v)) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      simp only [eval, os_arK2_err]
      exact matches_parse_raw_none e
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      refine ⟨1, ?_⟩
      simp only [eval, os_arK2_p]
      exact matches_parse_raw_some_of_reduces rest (reduces_pi hA (hshift hB))

theorem arK2_matches_first_raw_of_term_result (fuel : Nat) (ctx : List String) (A : LF.Term)
    (Araw : AST) (hA : ReducesToEncTerm Araw A) (bodyToks : List LF.Tok) {v : AST}
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B))
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    FirstMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (arK2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_matches_one (by simp only [eval, os_arK2_err])
        (matches_parse_raw_none e) (not_result_arK2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      exact first_matches_one (by simp only [eval, os_arK2_p])
        (matches_parse_raw_some_of_reduces rest (reduces_pi hA (hshift hB)))
        (not_result_arK2 Araw (Pp Braw (encToks rest)))

theorem arK2_matches_first_active_of_term_result (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ReducesToEncTerm Araw A)
    (bodyToks : List LF.Tok) {v : AST}
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B))
    (h : MatchesParseRaw (LF.pTerm fuel ctx bodyToks) v) :
    FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (arK2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_active_one (by simp only [eval, os_arK2_err])
        (matches_parse_raw_none e)
        (ParserActiveShape.arK2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      exact first_active_one (by simp only [eval, os_arK2_p])
        (matches_parse_raw_some_of_reduces rest (reduces_pi hA (hshift hB)))
        (ParserActiveShape.arK2 Araw (Pp Braw (encToks rest)))

theorem arK2_matches_first_active_of_term_first_active (fuel : Nat) (ctx : List String)
    (A : LF.Term) (Araw : AST) (hA : ReducesToEncTerm Araw A)
    (bodyToks : List LF.Tok)
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B))
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm fuel ctx bodyToks)
      (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) :
    FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) := by
  let child := tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  rcases hA with ⟨NA, hNA⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => arK2 a child)
      (fun a => ParserActiveShape.arK2 a child)
      (hcong_arK2_left_active_child child hchildActive)
      NA hNA
  have htail : FirstActiveMatchesParseRaw
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (arK2 (encTerm A) child) :=
    first_active_bind_active
      (fun s => arK2 (encTerm A) s)
      (fun s _ => ParserActiveShape.arK2 (encTerm A) s)
      (hcong_arK2_right_active (encTerm A) (isnormal_encTerm A))
      hfirst
      (fun {v} hv =>
        arK2_matches_first_active_of_term_result fuel ctx A (encTerm A)
          (reduces_encTerm_refl A) bodyToks hshift hv)
  exact first_active_prepend_eval hMnorm hNormGuard htail

theorem arK2_matches_first_active_shiftable_of_term_result (fuel : Nat)
    (ctx : List String) (A : LF.Term) (Araw : AST) (hA : ShiftablePayload Araw A)
    (bodyToks : List LF.Tok) {v : AST}
    (hshiftPayload : ∀ {B : LF.Term} {Braw : AST}, ShiftablePayload Braw B →
      ShiftablePayload (shift Z Braw) (LF.shift 0 B))
    (h : MatchesParseShiftable (LF.pTerm fuel ctx bodyToks) v) :
    FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (arK2 Araw v) := by
  cases hbody : LF.pTerm fuel ctx bodyToks with
  | none =>
      rw [hbody] at h
      rcases h with ⟨e, rfl⟩
      exact first_active_shiftable_one (by simp only [eval, os_arK2_err])
        (matches_parse_shiftable_none e)
        (ParserActiveShape.arK2 Araw (PErr e))
  | some pr =>
      rcases pr with ⟨B, rest⟩
      rw [hbody] at h
      rcases h with ⟨Braw, rfl, hB⟩
      exact first_active_shiftable_one (by simp only [eval, os_arK2_p])
        (matches_parse_shiftable_some_of_payload
          (shiftable_pi hA (hshiftPayload hB)))
        (ParserActiveShape.arK2 Araw (Pp Braw (encToks rest)))

theorem arK2_matches_first_active_shiftable_of_term_first_active (fuel : Nat)
    (ctx : List String) (A : LF.Term) (Araw : AST) (hA : ShiftablePayload Araw A)
    (bodyToks : List LF.Tok)
    (hshiftPayload : ∀ {B : LF.Term} {Braw : AST}, ShiftablePayload Braw B →
      ShiftablePayload (shift Z Braw) (LF.shift 0 B))
    (hfirst : FirstActiveMatchesParseShiftable (LF.pTerm fuel ctx bodyToks)
      (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) :
    FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks))) := by
  let child := tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.tm (peano fuel) (encCtx ctx) (encToks bodyToks)
  rcases hA.reduces with ⟨NA, hNA⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => arK2 a child)
      (fun a => ParserActiveShape.arK2 a child)
      (hcong_arK2_left_active_child child hchildActive)
      NA hNA
  have htail : FirstActiveMatchesParseShiftable
      (match LF.pTerm fuel ctx bodyToks with
       | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
       | none => none)
      (arK2 (encTerm A) child) :=
    first_active_shiftable_bind_active
      (fun s => arK2 (encTerm A) s)
      (fun s _ => ParserActiveShape.arK2 (encTerm A) s)
      (hcong_arK2_right_active (encTerm A) (isnormal_encTerm A))
      hfirst
      (fun {v} hv =>
        arK2_matches_first_active_shiftable_of_term_result fuel ctx A (encTerm A)
          (shiftable_encTerm A) bodyToks hshiftPayload hv)
  exact first_active_shiftable_prepend_eval hMnorm hNormGuard htail

theorem tmPi1_matches_raw_of_app_result (fuel : Nat) (ctx : List String) (x : String)
    (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        ∃ N, MatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (B, rest) => some (.pi A B, rest)
           | none => none)
          (eval pLF N
            (tmPi2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks))))) :
    ∃ N, MatchesParseRaw (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks))
      (eval pLF N (tmPi1 (peano fuel) (encCtx ctx) (con0 x) v)) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      simp only [eval, os_tmPi1_err]
      exact matches_parse_raw_none (con0 "pi-malformed")
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          refine ⟨1, ?_⟩
          rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          simp only [eval, encToks, os_tmPi1_nil]
          exact matches_parse_raw_none (con0 "pi-malformed")
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain ⟨Ntail, htail⟩ := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmPi2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmPi1_dot]
              have htotal := eval_trans pLF 1 Ntail _ _ _ hstep rfl
              refine ⟨1 + Ntail, ?_⟩
              rw [htotal]
              rw [show
                LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (B, rest) => some (.pi A B, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact htail
          | pi =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_pi]
              exact matches_parse_raw_none (con0 "pi-malformed")
          | lam =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_lam]
              exact matches_parse_raw_none (con0 "pi-malformed")
          | arr =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_arr]
              exact matches_parse_raw_none (con0 "pi-malformed")
          | colon =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_colon]
              exact matches_parse_raw_none (con0 "pi-malformed")
          | lpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_lp]
              exact matches_parse_raw_none (con0 "pi-malformed")
          | rpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_rp]
              exact matches_parse_raw_none (con0 "pi-malformed")
          | type =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_type]
              exact matches_parse_raw_none (con0 "pi-malformed")
          | id s =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmPi1_id]
              exact matches_parse_raw_none (con0 "pi-malformed")

theorem tmLam1_matches_raw_of_app_result (fuel : Nat) (ctx : List String) (x : String)
    (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        ∃ N, MatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (b, rest) => some (.lam A b, rest)
           | none => none)
          (eval pLF N
            (tmLam2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks))))) :
    ∃ N, MatchesParseRaw (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks))
      (eval pLF N (tmLam1 (peano fuel) (encCtx ctx) (con0 x) v)) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      simp only [eval, os_tmLam1_err]
      exact matches_parse_raw_none (con0 "lam-malformed")
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          refine ⟨1, ?_⟩
          rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          simp only [eval, encToks, os_tmLam1_nil]
          exact matches_parse_raw_none (con0 "lam-malformed")
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain ⟨Ntail, htail⟩ := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmLam2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmLam1_dot]
              have htotal := eval_trans pLF 1 Ntail _ _ _ hstep rfl
              refine ⟨1 + Ntail, ?_⟩
              rw [htotal]
              rw [show
                LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (b, rest) => some (.lam A b, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact htail
          | pi =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_pi]
              exact matches_parse_raw_none (con0 "lam-malformed")
          | lam =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_lam]
              exact matches_parse_raw_none (con0 "lam-malformed")
          | arr =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_arr]
              exact matches_parse_raw_none (con0 "lam-malformed")
          | colon =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_colon]
              exact matches_parse_raw_none (con0 "lam-malformed")
          | lpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_lp]
              exact matches_parse_raw_none (con0 "lam-malformed")
          | rpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_rp]
              exact matches_parse_raw_none (con0 "lam-malformed")
          | type =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_type]
              exact matches_parse_raw_none (con0 "lam-malformed")
          | id s =>
              refine ⟨1, ?_⟩
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              simp only [eval, encToks, encTok, os_tmLam1_id]
              exact matches_parse_raw_none (con0 "lam-malformed")

theorem tmPi1_matches_first_raw_of_app_result (fuel : Nat) (ctx : List String) (x : String)
    (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        FirstMatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (B, rest) => some (.pi A B, rest)
           | none => none)
          (tmPi2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks))
      (tmPi1 (peano fuel) (encCtx ctx) (con0 x) v) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      exact first_matches_one (by simp only [eval, os_tmPi1_err])
        (matches_parse_raw_none (con0 "pi-malformed"))
        (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          exact first_matches_one (by simp only [eval, encToks, os_tmPi1_nil])
            (matches_parse_raw_none (con0 "pi-malformed"))
            (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmPi2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmPi1_dot]
              rw [show
                LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (B, rest) => some (.pi A B, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact first_matches_prepend hstep
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.dot :: bodyToks)))) htail
          | pi =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_pi])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_lam])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | arr =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_arr])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.arr :: bodyToks))))
          | colon =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_colon])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | lpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_lp])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_rp])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_type])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmPi1_id])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (not_result_tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem tmPi1_matches_first_active_of_app_result (fuel : Nat) (ctx : List String)
    (x : String) (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        FirstActiveMatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (B, rest) => some (.pi A B, rest)
           | none => none)
          (tmPi2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks))
      (tmPi1 (peano fuel) (encCtx ctx) (con0 x) v) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      exact first_active_one (by simp only [eval, os_tmPi1_err])
        (matches_parse_raw_none (con0 "pi-malformed"))
        (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          exact first_active_one (by simp only [eval, encToks, os_tmPi1_nil])
            (matches_parse_raw_none (con0 "pi-malformed"))
            (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmPi2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmPi1_dot]
              rw [show
                LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (B, rest) => some (.pi A B, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact first_active_prepend hstep
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.dot :: bodyToks)))) htail
          | pi =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_pi])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_lam])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | arr =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_arr])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.arr :: bodyToks))))
          | colon =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_colon])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | lpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_lp])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_rp])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_type])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmPi1_id])
                (matches_parse_raw_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem tmPi1_matches_first_active_of_app_first_active (fuel : Nat) (ctx : List String)
    (x : String) (argToks : List LF.Tok)
    (happ : FirstActiveMatchesParseRaw (LF.pApp fuel ctx argToks)
      (ap (peano fuel) (encCtx ctx) (encToks argToks)))
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        FirstActiveMatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (B, rest) => some (.pi A B, rest)
           | none => none)
          (tmPi2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks))
      (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
        (ap (peano fuel) (encCtx ctx) (encToks argToks))) := by
  exact first_active_bind_active
    (fun s => tmPi1 (peano fuel) (encCtx ctx) (con0 x) s)
    (fun s _ => ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x) s)
    (hcong_tmPi1_active (peano fuel) (encCtx ctx) (con0 x)
      (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_con0 x))
    happ
    (fun {v} hv => tmPi1_matches_first_active_of_app_result fuel ctx x argToks hv tail)

theorem tmLam1_matches_first_raw_of_app_result (fuel : Nat) (ctx : List String) (x : String)
    (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        FirstMatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (b, rest) => some (.lam A b, rest)
           | none => none)
          (tmLam2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks))
      (tmLam1 (peano fuel) (encCtx ctx) (con0 x) v) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      exact first_matches_one (by simp only [eval, os_tmLam1_err])
        (matches_parse_raw_none (con0 "lam-malformed"))
        (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          exact first_matches_one (by simp only [eval, encToks, os_tmLam1_nil])
            (matches_parse_raw_none (con0 "lam-malformed"))
            (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmLam2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmLam1_dot]
              rw [show
                LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (b, rest) => some (.lam A b, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact first_matches_prepend hstep
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.dot :: bodyToks)))) htail
          | pi =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_pi])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_lam])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | arr =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_arr])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.arr :: bodyToks))))
          | colon =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_colon])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | lpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_lp])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_rp])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_type])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_tmLam1_id])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (not_result_tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem tmLam1_matches_first_active_of_app_result (fuel : Nat) (ctx : List String)
    (x : String) (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        FirstActiveMatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (b, rest) => some (.lam A b, rest)
           | none => none)
          (tmLam2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks))
      (tmLam1 (peano fuel) (encCtx ctx) (con0 x) v) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      exact first_active_one (by simp only [eval, os_tmLam1_err])
        (matches_parse_raw_none (con0 "lam-malformed"))
        (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          exact first_active_one (by simp only [eval, encToks, os_tmLam1_nil])
            (matches_parse_raw_none (con0 "lam-malformed"))
            (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmLam2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmLam1_dot]
              rw [show
                LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (b, rest) => some (.lam A b, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact first_active_prepend hstep
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.dot :: bodyToks)))) htail
          | pi =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_pi])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_lam])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | arr =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_arr])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.arr :: bodyToks))))
          | colon =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_colon])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | lpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_lp])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_rp])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_type])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_tmLam1_id])
                (matches_parse_raw_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem tmLam1_matches_first_active_of_app_first_active (fuel : Nat) (ctx : List String)
    (x : String) (argToks : List LF.Tok)
    (happ : FirstActiveMatchesParseRaw (LF.pApp fuel ctx argToks)
      (ap (peano fuel) (encCtx ctx) (encToks argToks)))
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ReducesToEncTerm Araw A →
        FirstActiveMatchesParseRaw
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (b, rest) => some (.lam A b, rest)
           | none => none)
          (tmLam2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks))
      (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
        (ap (peano fuel) (encCtx ctx) (encToks argToks))) := by
  exact first_active_bind_active
    (fun s => tmLam1 (peano fuel) (encCtx ctx) (con0 x) s)
    (fun s _ => ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x) s)
    (hcong_tmLam1_active (peano fuel) (encCtx ctx) (con0 x)
      (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_con0 x))
    happ
    (fun {v} hv => tmLam1_matches_first_active_of_app_result fuel ctx x argToks hv tail)

theorem tmPi1_matches_first_active_shiftable_of_app_result (fuel : Nat) (ctx : List String)
    (x : String) (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseShiftable (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ShiftablePayload Araw A →
        FirstActiveMatchesParseShiftable
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (B, rest) => some (.pi A B, rest)
           | none => none)
          (tmPi2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseShiftable (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks))
      (tmPi1 (peano fuel) (encCtx ctx) (con0 x) v) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      exact first_active_shiftable_one (by simp only [eval, os_tmPi1_err])
        (matches_parse_shiftable_none (con0 "pi-malformed"))
        (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          exact first_active_shiftable_one (by simp only [eval, encToks, os_tmPi1_nil])
            (matches_parse_shiftable_none (con0 "pi-malformed"))
            (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmPi2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmPi1_dot]
              rw [show
                LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (B, rest) => some (.pi A B, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact first_active_shiftable_prepend hstep
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.dot :: bodyToks)))) htail
          | pi =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_pi])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_lam])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | arr =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_arr])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.arr :: bodyToks))))
          | colon =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_colon])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | lpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_lp])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_rp])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_type])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmPi1_id])
                (matches_parse_shiftable_none (con0 "pi-malformed"))
                (ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem tmPi1_matches_first_active_shiftable_of_app_first_active (fuel : Nat)
    (ctx : List String) (x : String) (argToks : List LF.Tok)
    (happ : FirstActiveMatchesParseShiftable (LF.pApp fuel ctx argToks)
      (ap (peano fuel) (encCtx ctx) (encToks argToks)))
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ShiftablePayload Araw A →
        FirstActiveMatchesParseShiftable
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (B, rest) => some (.pi A B, rest)
           | none => none)
          (tmPi2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseShiftable (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: argToks))
      (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
        (ap (peano fuel) (encCtx ctx) (encToks argToks))) := by
  exact first_active_shiftable_bind_active
    (fun s => tmPi1 (peano fuel) (encCtx ctx) (con0 x) s)
    (fun s _ => ParserActiveShape.tmPi1 (peano fuel) (encCtx ctx) (con0 x) s)
    (hcong_tmPi1_active (peano fuel) (encCtx ctx) (con0 x)
      (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_con0 x))
    happ
    (fun {v} hv =>
      tmPi1_matches_first_active_shiftable_of_app_result fuel ctx x argToks hv tail)

theorem tmLam1_matches_first_active_shiftable_of_app_result (fuel : Nat) (ctx : List String)
    (x : String) (argToks : List LF.Tok) {v : AST}
    (h : MatchesParseShiftable (LF.pApp fuel ctx argToks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ShiftablePayload Araw A →
        FirstActiveMatchesParseShiftable
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (b, rest) => some (.lam A b, rest)
           | none => none)
          (tmLam2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseShiftable (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks))
      (tmLam1 (peano fuel) (encCtx ctx) (con0 x) v) := by
  cases happ : LF.pApp fuel ctx argToks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
        simp [LF.pTerm, happ]]
      exact first_active_shiftable_one (by simp only [eval, os_tmLam1_err])
        (matches_parse_shiftable_none (con0 "lam-malformed"))
        (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
            simp [LF.pTerm, happ]]
          exact first_active_shiftable_one (by simp only [eval, encToks, os_tmLam1_nil])
            (matches_parse_shiftable_none (con0 "lam-malformed"))
            (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | dot =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                    (Pp Araw (encToks (.dot :: bodyToks))))
                  = tmLam2 Araw
                    (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)) := by
                rw [show encCtx (x :: ctx) = Cons (con0 x) (encCtx ctx) from rfl]
                simp only [eval, encToks, encTok, os_tmLam1_dot]
              rw [show
                LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks)
                  =
                    (match LF.pTerm fuel (x :: ctx) bodyToks with
                     | some (b, rest) => some (.lam A b, rest)
                     | none => none) by
                simp [LF.pTerm, happ]
                rfl]
              exact first_active_shiftable_prepend hstep
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.dot :: bodyToks)))) htail
          | pi =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_pi])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_lam])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | arr =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_arr])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.arr :: bodyToks))))
          | colon =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_colon])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | lpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_lp])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_rp])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_type])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks) = none by
                simp [LF.pTerm, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_tmLam1_id])
                (matches_parse_shiftable_none (con0 "lam-malformed"))
                (ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem tmLam1_matches_first_active_shiftable_of_app_first_active (fuel : Nat)
    (ctx : List String) (x : String) (argToks : List LF.Tok)
    (happ : FirstActiveMatchesParseShiftable (LF.pApp fuel ctx argToks)
      (ap (peano fuel) (encCtx ctx) (encToks argToks)))
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx argToks = some (A, .dot :: bodyToks) → ShiftablePayload Araw A →
        FirstActiveMatchesParseShiftable
          (match LF.pTerm fuel (x :: ctx) bodyToks with
           | some (b, rest) => some (.lam A b, rest)
           | none => none)
          (tmLam2 Araw (tm (peano fuel) (encCtx (x :: ctx)) (encToks bodyToks)))) :
    FirstActiveMatchesParseShiftable (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: argToks))
      (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
        (ap (peano fuel) (encCtx ctx) (encToks argToks))) := by
  exact first_active_shiftable_bind_active
    (fun s => tmLam1 (peano fuel) (encCtx ctx) (con0 x) s)
    (fun s _ => ParserActiveShape.tmLam1 (peano fuel) (encCtx ctx) (con0 x) s)
    (hcong_tmLam1_active (peano fuel) (encCtx ctx) (con0 x)
      (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_con0 x))
    happ
    (fun {v} hv =>
      tmLam1_matches_first_active_shiftable_of_app_result fuel ctx x argToks hv tail)

theorem arK_matches_raw_of_app_result (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx toks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx toks = some (A, .arr :: bodyToks) → ReducesToEncTerm Araw A →
        ∃ N, MatchesParseRaw
          (match LF.pTerm fuel ctx bodyToks with
           | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
           | none => none)
          (eval pLF N (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks))))) :
    ∃ N, MatchesParseRaw (LF.pArrow (fuel + 1) ctx toks)
      (eval pLF N (arK (peano fuel) (encCtx ctx) v)) := by
  cases happ : LF.pApp fuel ctx toks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      rw [show LF.pArrow (fuel + 1) ctx toks = none by simp [LF.pArrow, happ]]
      simp only [eval, os_arK_err]
      exact matches_parse_raw_none e
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          refine ⟨1, ?_⟩
          rw [show LF.pArrow (fuel + 1) ctx toks = some (A, []) by simp [LF.pArrow, happ]]
          simp only [eval, encToks, os_arK_nil]
          exact matches_parse_raw_some_of_reduces [] hA
      | cons tok bodyToks =>
          cases tok with
          | arr =>
              obtain ⟨Ntail, htail⟩ := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (arK (peano fuel) (encCtx ctx) (Pp Araw (encToks (.arr :: bodyToks))))
                  = arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)) := by
                simp only [eval, encToks, encTok, os_arK_arr]
              have htotal := eval_trans pLF 1 Ntail _ _ _ hstep rfl
              refine ⟨1 + Ntail, ?_⟩
              rw [htotal]
              rw [show
                LF.pArrow (fuel + 1) ctx toks
                  =
                    (match LF.pTerm fuel ctx bodyToks with
                     | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
                     | none => none) by
                simp [LF.pArrow, happ]
                rfl]
              exact htail
          | pi =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .pi :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_pi]
              exact matches_parse_raw_some_of_reduces (.pi :: bodyToks) hA
          | lam =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lam :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_lam]
              exact matches_parse_raw_some_of_reduces (.lam :: bodyToks) hA
          | colon =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .colon :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_colon]
              exact matches_parse_raw_some_of_reduces (.colon :: bodyToks) hA
          | dot =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .dot :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_dot]
              exact matches_parse_raw_some_of_reduces (.dot :: bodyToks) hA
          | lpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_lp]
              exact matches_parse_raw_some_of_reduces (.lpar :: bodyToks) hA
          | rpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .rpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_rp]
              exact matches_parse_raw_some_of_reduces (.rpar :: bodyToks) hA
          | type =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .type :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_type]
              exact matches_parse_raw_some_of_reduces (.type :: bodyToks) hA
          | id s =>
              refine ⟨1, ?_⟩
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .id s :: bodyToks) by
                simp [LF.pArrow, happ]]
              simp only [eval, encToks, encTok, os_arK_id]
              exact matches_parse_raw_some_of_reduces (.id s :: bodyToks) hA

theorem arK_matches_first_raw_of_app_result (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx toks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx toks = some (A, .arr :: bodyToks) → ReducesToEncTerm Araw A →
        FirstMatchesParseRaw
          (match LF.pTerm fuel ctx bodyToks with
           | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
           | none => none)
          (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)))) :
    FirstMatchesParseRaw (LF.pArrow (fuel + 1) ctx toks)
      (arK (peano fuel) (encCtx ctx) v) := by
  cases happ : LF.pApp fuel ctx toks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pArrow (fuel + 1) ctx toks = none by simp [LF.pArrow, happ]]
      exact first_matches_one (by simp only [eval, os_arK_err])
        (matches_parse_raw_none e)
        (not_result_arK (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pArrow (fuel + 1) ctx toks = some (A, []) by simp [LF.pArrow, happ]]
          exact first_matches_one (by simp only [eval, encToks, os_arK_nil])
            (matches_parse_raw_some_of_reduces [] hA)
            (not_result_arK (peano fuel) (encCtx ctx) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | arr =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (arK (peano fuel) (encCtx ctx) (Pp Araw (encToks (.arr :: bodyToks))))
                  = arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)) := by
                simp only [eval, encToks, encTok, os_arK_arr]
              rw [show
                LF.pArrow (fuel + 1) ctx toks
                  =
                    (match LF.pTerm fuel ctx bodyToks with
                     | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
                     | none => none) by
                simp [LF.pArrow, happ]
                rfl]
              exact first_matches_prepend hstep
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.arr :: bodyToks)))) htail
          | pi =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .pi :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_pi])
                (matches_parse_raw_some_of_reduces (.pi :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lam :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_lam])
                (matches_parse_raw_some_of_reduces (.lam :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | colon =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .colon :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_colon])
                (matches_parse_raw_some_of_reduces (.colon :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | dot =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .dot :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_dot])
                (matches_parse_raw_some_of_reduces (.dot :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.dot :: bodyToks))))
          | lpar =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_lp])
                (matches_parse_raw_some_of_reduces (.lpar :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .rpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_rp])
                (matches_parse_raw_some_of_reduces (.rpar :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .type :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_type])
                (matches_parse_raw_some_of_reduces (.type :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .id s :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_arK_id])
                (matches_parse_raw_some_of_reduces (.id s :: bodyToks) hA)
                (not_result_arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem arK_matches_first_active_of_app_result (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pApp fuel ctx toks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx toks = some (A, .arr :: bodyToks) → ReducesToEncTerm Araw A →
        FirstActiveMatchesParseRaw
          (match LF.pTerm fuel ctx bodyToks with
           | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
           | none => none)
          (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)))) :
    FirstActiveMatchesParseRaw (LF.pArrow (fuel + 1) ctx toks)
      (arK (peano fuel) (encCtx ctx) v) := by
  cases happ : LF.pApp fuel ctx toks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pArrow (fuel + 1) ctx toks = none by simp [LF.pArrow, happ]]
      exact first_active_one (by simp only [eval, os_arK_err])
        (matches_parse_raw_none e)
        (ParserActiveShape.arK (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pArrow (fuel + 1) ctx toks = some (A, []) by simp [LF.pArrow, happ]]
          exact first_active_one (by simp only [eval, encToks, os_arK_nil])
            (matches_parse_raw_some_of_reduces [] hA)
            (ParserActiveShape.arK (peano fuel) (encCtx ctx) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | arr =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (arK (peano fuel) (encCtx ctx) (Pp Araw (encToks (.arr :: bodyToks))))
                  = arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)) := by
                simp only [eval, encToks, encTok, os_arK_arr]
              rw [show
                LF.pArrow (fuel + 1) ctx toks
                  =
                    (match LF.pTerm fuel ctx bodyToks with
                     | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
                     | none => none) by
                simp [LF.pArrow, happ]
                rfl]
              exact first_active_prepend hstep
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.arr :: bodyToks)))) htail
          | pi =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .pi :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_pi])
                (matches_parse_raw_some_of_reduces (.pi :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lam :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_lam])
                (matches_parse_raw_some_of_reduces (.lam :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | colon =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .colon :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_colon])
                (matches_parse_raw_some_of_reduces (.colon :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | dot =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .dot :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_dot])
                (matches_parse_raw_some_of_reduces (.dot :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.dot :: bodyToks))))
          | lpar =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_lp])
                (matches_parse_raw_some_of_reduces (.lpar :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .rpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_rp])
                (matches_parse_raw_some_of_reduces (.rpar :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .type :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_type])
                (matches_parse_raw_some_of_reduces (.type :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .id s :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_arK_id])
                (matches_parse_raw_some_of_reduces (.id s :: bodyToks) hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem arrow_succ_first_active_of_app_term (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok)
    (happ : FirstActiveMatchesParseRaw (LF.pApp fuel ctx toks)
      (ap (peano fuel) (encCtx ctx) (encToks toks)))
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx toks = some (A, .arr :: bodyToks) → ReducesToEncTerm Araw A →
        FirstActiveMatchesParseRaw
          (match LF.pTerm fuel ctx bodyToks with
           | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
           | none => none)
          (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)))) :
    FirstActiveMatchesParseRaw (LF.pArrow (fuel + 1) ctx toks)
      (ar (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  have hinner : FirstActiveMatchesParseRaw (LF.pArrow (fuel + 1) ctx toks)
      (arK (peano fuel) (encCtx ctx)
        (ap (peano fuel) (encCtx ctx) (encToks toks))) :=
    first_active_bind_active
      (fun s => arK (peano fuel) (encCtx ctx) s)
      (fun s _ => ParserActiveShape.arK (peano fuel) (encCtx ctx) s)
      (hcong_arK_active (peano fuel) (encCtx ctx)
        (isnormal_peano fuel) (isnormal_encCtx ctx))
      happ
      (fun {v} hv => arK_matches_first_active_of_app_result fuel ctx toks hv tail)
  have har : eval pLF 1 (ar (peano (fuel + 1)) (encCtx ctx) (encToks toks))
      = arK (peano fuel) (encCtx ctx)
          (ap (peano fuel) (encCtx ctx) (encToks toks)) := by
    simp only [peano, eval, os_ar_s]
  exact first_active_prepend har
    (ParserActiveShape.ar (peano (fuel + 1)) (encCtx ctx) (encToks toks)) hinner

theorem arK_matches_first_active_shiftable_of_app_result (fuel : Nat)
    (ctx : List String) (toks : List LF.Tok) {v : AST}
    (h : MatchesParseShiftable (LF.pApp fuel ctx toks) v)
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx toks = some (A, .arr :: bodyToks) → ShiftablePayload Araw A →
        FirstActiveMatchesParseShiftable
          (match LF.pTerm fuel ctx bodyToks with
           | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
           | none => none)
          (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)))) :
    FirstActiveMatchesParseShiftable (LF.pArrow (fuel + 1) ctx toks)
      (arK (peano fuel) (encCtx ctx) v) := by
  cases happ : LF.pApp fuel ctx toks with
  | none =>
      rw [happ] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pArrow (fuel + 1) ctx toks = none by simp [LF.pArrow, happ]]
      exact first_active_shiftable_one (by simp only [eval, os_arK_err])
        (matches_parse_shiftable_none e)
        (ParserActiveShape.arK (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨A, restAfterA⟩
      rw [happ] at h
      rcases h with ⟨Araw, rfl, hA⟩
      cases restAfterA with
      | nil =>
          rw [show LF.pArrow (fuel + 1) ctx toks = some (A, []) by simp [LF.pArrow, happ]]
          exact first_active_shiftable_one (by simp only [eval, encToks, os_arK_nil])
            (matches_parse_shiftable_some_of_payload hA)
            (ParserActiveShape.arK (peano fuel) (encCtx ctx) (Pp Araw Nil))
      | cons tok bodyToks =>
          cases tok with
          | arr =>
              obtain htail := tail A bodyToks Araw happ hA
              have hstep : eval pLF 1
                  (arK (peano fuel) (encCtx ctx) (Pp Araw (encToks (.arr :: bodyToks))))
                  = arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)) := by
                simp only [eval, encToks, encTok, os_arK_arr]
              rw [show
                LF.pArrow (fuel + 1) ctx toks
                  =
                    (match LF.pTerm fuel ctx bodyToks with
                     | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
                     | none => none) by
                simp [LF.pArrow, happ]
                rfl]
              exact first_active_shiftable_prepend hstep
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.arr :: bodyToks)))) htail
          | pi =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .pi :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_pi])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.pi :: bodyToks))))
          | lam =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lam :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_lam])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.lam :: bodyToks))))
          | colon =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .colon :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_colon])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.colon :: bodyToks))))
          | dot =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .dot :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_dot])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.dot :: bodyToks))))
          | lpar =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .lpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_lp])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.lpar :: bodyToks))))
          | rpar =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .rpar :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_rp])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.rpar :: bodyToks))))
          | type =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .type :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_type])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.type :: bodyToks))))
          | id s =>
              rw [show LF.pArrow (fuel + 1) ctx toks = some (A, .id s :: bodyToks) by
                simp [LF.pArrow, happ]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_arK_id])
                (matches_parse_shiftable_some_of_payload hA)
                (ParserActiveShape.arK (peano fuel) (encCtx ctx)
                  (Pp Araw (encToks (.id s :: bodyToks))))

theorem arrow_succ_first_active_shiftable_of_app_term (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok)
    (happ : FirstActiveMatchesParseShiftable (LF.pApp fuel ctx toks)
      (ap (peano fuel) (encCtx ctx) (encToks toks)))
    (tail : ∀ (A : LF.Term) (bodyToks : List LF.Tok) (Araw : AST),
      LF.pApp fuel ctx toks = some (A, .arr :: bodyToks) → ShiftablePayload Araw A →
        FirstActiveMatchesParseShiftable
          (match LF.pTerm fuel ctx bodyToks with
           | some (B, rest) => some (.pi A (LF.shift 0 B), rest)
           | none => none)
          (arK2 Araw (tm (peano fuel) (encCtx ctx) (encToks bodyToks)))) :
    FirstActiveMatchesParseShiftable (LF.pArrow (fuel + 1) ctx toks)
      (ar (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  have hinner : FirstActiveMatchesParseShiftable (LF.pArrow (fuel + 1) ctx toks)
      (arK (peano fuel) (encCtx ctx)
        (ap (peano fuel) (encCtx ctx) (encToks toks))) :=
    first_active_shiftable_bind_active
      (fun s => arK (peano fuel) (encCtx ctx) s)
      (fun s _ => ParserActiveShape.arK (peano fuel) (encCtx ctx) s)
      (hcong_arK_active (peano fuel) (encCtx ctx)
        (isnormal_peano fuel) (isnormal_encCtx ctx))
      happ
      (fun {v} hv => arK_matches_first_active_shiftable_of_app_result fuel ctx toks hv tail)
  have har : eval pLF 1 (ar (peano (fuel + 1)) (encCtx ctx) (encToks toks))
      = arK (peano fuel) (encCtx ctx)
          (ap (peano fuel) (encCtx ctx) (encToks toks)) := by
    simp only [peano, eval, os_ar_s]
  exact first_active_shiftable_prepend har
    (ParserActiveShape.ar (peano (fuel + 1)) (encCtx ctx) (encToks toks)) hinner

theorem term_one_fall_matches_of_step (ctx : List String) (toks : List LF.Tok)
    (hstep : oneStep pLF (tm (peano (0 + 1)) (encCtx ctx) (encToks toks))
      = some (ar (peano 0) (encCtx ctx) (encToks toks)))
    (hparse : LF.pTerm (0 + 1) ctx toks = none) :
    ∃ N, MatchesParse (LF.pTerm (0 + 1) ctx toks)
      (eval pLF N (tm (peano (0 + 1)) (encCtx ctx) (encToks toks))) := by
  have hstep1 : eval pLF 1 (tm (peano (0 + 1)) (encCtx ctx) (encToks toks))
      = ar (peano 0) (encCtx ctx) (encToks toks) := by
    simp only [eval, hstep]
  have har := arrow_no_fuel_sim ctx toks
  have htotal := eval_trans pLF 1 1 _ _ _ hstep1 har
  refine ⟨1 + 1, ?_⟩
  rw [htotal, hparse]
  exact matches_parse_none (con0 "no-fuel")

theorem term_one_matches (ctx : List String) :
    ∀ toks : List LF.Tok, ∃ N, MatchesParse (LF.pTerm (0 + 1) ctx toks)
      (eval pLF N (tm (peano (0 + 1)) (encCtx ctx) (encToks toks)))
  | [] => term_one_fall_matches_of_step ctx [] (by simp only [peano, encToks]; rfl) (by rfl)
  | .pi :: [] => term_one_fall_matches_of_step ctx (.pi :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .pi :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .lam :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .arr :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .colon :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .colon :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .dot :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .lpar :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .rpar :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .type :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: [] =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .pi :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .lam :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .arr :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .colon :: rest =>
      term_one_pi_malformed_matches ctx x rest
  | .pi :: .id x :: .dot :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .lpar :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .rpar :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .type :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .id y :: rest =>
      term_one_fall_matches_of_step ctx (.pi :: .id x :: .id y :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: [] => term_one_fall_matches_of_step ctx (.lam :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .pi :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .lam :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .arr :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .colon :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .colon :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .dot :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .lpar :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .rpar :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .type :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: [] =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .pi :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .lam :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .arr :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .colon :: rest =>
      term_one_lam_malformed_matches ctx x rest
  | .lam :: .id x :: .dot :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .lpar :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .rpar :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .type :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .id y :: rest =>
      term_one_fall_matches_of_step ctx (.lam :: .id x :: .id y :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .arr :: rest =>
      term_one_fall_matches_of_step ctx (.arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .colon :: rest =>
      term_one_fall_matches_of_step ctx (.colon :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .dot :: rest =>
      term_one_fall_matches_of_step ctx (.dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lpar :: rest =>
      term_one_fall_matches_of_step ctx (.lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .rpar :: rest =>
      term_one_fall_matches_of_step ctx (.rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .type :: rest =>
      term_one_fall_matches_of_step ctx (.type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .id x :: rest =>
      term_one_fall_matches_of_step ctx (.id x :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)

theorem term_two_fall_matches_of_step (ctx : List String) (toks : List LF.Tok)
    (hstep : oneStep pLF (tm (peano ((0 + 1) + 1)) (encCtx ctx) (encToks toks))
      = some (ar (peano (0 + 1)) (encCtx ctx) (encToks toks)))
    (hparse : LF.pTerm ((0 + 1) + 1) ctx toks = none) :
    ∃ N, MatchesParse (LF.pTerm ((0 + 1) + 1) ctx toks)
      (eval pLF N (tm (peano ((0 + 1) + 1)) (encCtx ctx) (encToks toks))) := by
  have hstep1 : eval pLF 1 (tm (peano ((0 + 1) + 1)) (encCtx ctx) (encToks toks))
      = ar (peano (0 + 1)) (encCtx ctx) (encToks toks) := by
    simp only [eval, hstep]
  have har := arrow_one_sim ctx toks
  have htotal := eval_trans pLF 1 3 _ _ _ hstep1 har
  refine ⟨1 + 3, ?_⟩
  rw [htotal, hparse]
  exact matches_parse_none (con0 "no-fuel")

theorem term_two_matches (ctx : List String) :
    ∀ toks : List LF.Tok, ∃ N, MatchesParse (LF.pTerm ((0 + 1) + 1) ctx toks)
      (eval pLF N (tm (peano ((0 + 1) + 1)) (encCtx ctx) (encToks toks)))
  | [] => term_two_fall_matches_of_step ctx [] (by simp only [peano, encToks]; rfl) (by rfl)
  | .pi :: [] => term_two_fall_matches_of_step ctx (.pi :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .pi :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .lam :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .arr :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .colon :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .colon :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .dot :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .lpar :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .rpar :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .type :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: [] =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .pi :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .lam :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .arr :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .colon :: rest =>
      term_two_pi_malformed_matches ctx x rest
  | .pi :: .id x :: .dot :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .lpar :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .rpar :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .type :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .pi :: .id x :: .id y :: rest =>
      term_two_fall_matches_of_step ctx (.pi :: .id x :: .id y :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: [] => term_two_fall_matches_of_step ctx (.lam :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .pi :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .lam :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .arr :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .colon :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .colon :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .dot :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .lpar :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .rpar :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .type :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: [] =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: []) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .pi :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .pi :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .lam :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .lam :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .arr :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .colon :: rest =>
      term_two_lam_malformed_matches ctx x rest
  | .lam :: .id x :: .dot :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .lpar :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .rpar :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .type :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lam :: .id x :: .id y :: rest =>
      term_two_fall_matches_of_step ctx (.lam :: .id x :: .id y :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .arr :: rest =>
      term_two_fall_matches_of_step ctx (.arr :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .colon :: rest =>
      term_two_fall_matches_of_step ctx (.colon :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .dot :: rest =>
      term_two_fall_matches_of_step ctx (.dot :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .lpar :: rest =>
      term_two_fall_matches_of_step ctx (.lpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .rpar :: rest =>
      term_two_fall_matches_of_step ctx (.rpar :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .type :: rest =>
      term_two_fall_matches_of_step ctx (.type :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)
  | .id x :: rest =>
      term_two_fall_matches_of_step ctx (.id x :: rest) (by simp only [peano, encToks, encTok]; rfl) (by rfl)

theorem atom_no_fuel_sim (ctx : List String) (toks : List LF.Tok) :
    eval pLF 1 (at' Z (encCtx ctx) (encToks toks)) = PErr (con0 "no-fuel") := by
  simp only [eval, os_at_z]

theorem atom_no_fuel_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom 0 ctx toks) (eval pLF N (at' Z (encCtx ctx) (encToks toks))) := by
  refine ⟨1, ?_⟩
  rw [atom_no_fuel_sim]
  exact matches_parse_none (con0 "no-fuel")

theorem atom_lpar_no_fuel_sim (ctx : List String) (rest : List LF.Tok) :
    eval pLF 3 (at' (peano (0 + 1)) (encCtx ctx) (encToks (.lpar :: rest)))
      = PErr (con0 "paren-malformed") := by
  have hstep2 := hcong_atLPk_tm Z (encCtx ctx) Z (encCtx ctx) (encToks rest)
    (isnormal_peano 0) (isnormal_encCtx ctx) (PErr (con0 "no-fuel"))
    (by simp only [os_tm_z])
  simp only [peano, encToks, encTok, eval, os_at_lp, hstep2, os_atLPk_err]

theorem atom_lpar_no_fuel_matches (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (0 + 1) ctx (.lpar :: rest))
      (eval pLF N (at' (peano (0 + 1)) (encCtx ctx) (encToks (.lpar :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [atom_lpar_no_fuel_sim]
  exact matches_parse_none (con0 "paren-malformed")

theorem atom_lpar_no_fuel_raw_matches (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParseRaw (LF.pAtom (0 + 1) ctx (.lpar :: rest))
      (eval pLF N (at' (peano (0 + 1)) (encCtx ctx) (encToks (.lpar :: rest)))) := by
  obtain ⟨N, hN⟩ := atom_lpar_no_fuel_matches ctx rest
  exact ⟨N, matches_parse_to_raw hN⟩

theorem atLPk_matches_raw_of_term_result (fuel : Nat) (ctx : List String) (rest : List LF.Tok)
    {v : AST} (h : MatchesParseRaw (LF.pTerm fuel ctx rest) v) :
    ∃ N, MatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (eval pLF N (atLPk (peano fuel) (encCtx ctx) v)) := by
  cases hterm : LF.pTerm fuel ctx rest with
  | none =>
      rw [hterm] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
      simp only [eval, os_atLPk_err]
      exact matches_parse_raw_none (con0 "paren-malformed")
  | some pr =>
      rcases pr with ⟨t, rest'⟩
      rw [hterm] at h
      rcases h with ⟨u, rfl, hu⟩
      cases rest' with
      | nil =>
          refine ⟨1, ?_⟩
          rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
          simp only [eval, encToks, os_atLPk_nil]
          exact matches_parse_raw_none (con0 "paren-malformed")
      | cons tok rest2 =>
          cases tok with
          | rpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = some (t, rest2) by
                simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_rp]
              exact matches_parse_raw_some_of_reduces rest2 hu
          | pi =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_pi]
              exact matches_parse_raw_none (con0 "paren-malformed")
          | lam =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_lam]
              exact matches_parse_raw_none (con0 "paren-malformed")
          | arr =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_arr]
              exact matches_parse_raw_none (con0 "paren-malformed")
          | colon =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_colon]
              exact matches_parse_raw_none (con0 "paren-malformed")
          | dot =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_dot]
              exact matches_parse_raw_none (con0 "paren-malformed")
          | lpar =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_lp]
              exact matches_parse_raw_none (con0 "paren-malformed")
          | type =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_type]
              exact matches_parse_raw_none (con0 "paren-malformed")
          | id s =>
              refine ⟨1, ?_⟩
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              simp only [eval, encToks, encTok, os_atLPk_id]
              exact matches_parse_raw_none (con0 "paren-malformed")

theorem atLPk_matches_raw_of_term_first_active (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok)
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm fuel ctx rest)
      (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    ∃ N, MatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (eval pLF N (atLPk (peano fuel) (encCtx ctx)
        (tm (peano fuel) (encCtx ctx) (encToks rest)))) := by
  exact first_active_bind
    (fun s => atLPk (peano fuel) (encCtx ctx) s)
    (fun w => MatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest)) w)
    (hcong_atLPk_active (peano fuel) (encCtx ctx)
      (isnormal_peano fuel) (isnormal_encCtx ctx))
    hfirst
    (fun {v} hv => atLPk_matches_raw_of_term_result fuel ctx rest hv)

theorem atom_lpar_raw_of_term_first_active (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok)
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm fuel ctx rest)
      (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    ∃ N, MatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest)))) := by
  obtain ⟨Ntail, htail⟩ := atLPk_matches_raw_of_term_first_active fuel ctx rest hfirst
  have hstep : eval pLF 1
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest)))
      = atLPk (peano fuel) (encCtx ctx)
          (tm (peano fuel) (encCtx ctx) (encToks rest)) := by
    simp only [peano, encToks, encTok, eval, os_at_lp]
  refine ⟨1 + Ntail, ?_⟩
  have htotal := eval_trans pLF 1 Ntail _ _ _ hstep rfl
  rw [htotal]
  exact htail

theorem atLPk_matches_first_raw_of_term_result (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) {v : AST} (h : MatchesParseRaw (LF.pTerm fuel ctx rest) v) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (atLPk (peano fuel) (encCtx ctx) v) := by
  cases hterm : LF.pTerm fuel ctx rest with
  | none =>
      rw [hterm] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
      exact first_matches_one (by simp only [eval, os_atLPk_err])
        (matches_parse_raw_none (con0 "paren-malformed"))
        (not_result_atLPk (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨t, rest'⟩
      rw [hterm] at h
      rcases h with ⟨u, rfl, hu⟩
      cases rest' with
      | nil =>
          rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
          exact first_matches_one (by simp only [eval, encToks, os_atLPk_nil])
            (matches_parse_raw_none (con0 "paren-malformed"))
            (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u Nil))
      | cons tok rest2 =>
          cases tok with
          | rpar =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = some (t, rest2) by
                simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_rp])
                (matches_parse_raw_some_of_reduces rest2 hu)
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.rpar :: rest2))))
          | pi =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_pi])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.pi :: rest2))))
          | lam =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_lam])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.lam :: rest2))))
          | arr =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_arr])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.arr :: rest2))))
          | colon =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_colon])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.colon :: rest2))))
          | dot =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_dot])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.dot :: rest2))))
          | lpar =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_lp])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.lpar :: rest2))))
          | type =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_type])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.type :: rest2))))
          | id s =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_matches_one (by simp only [eval, encToks, encTok, os_atLPk_id])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (not_result_atLPk (peano fuel) (encCtx ctx) (Pp u (encToks (.id s :: rest2))))

theorem atLPk_matches_first_active_of_term_result (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) {v : AST} (h : MatchesParseRaw (LF.pTerm fuel ctx rest) v) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (atLPk (peano fuel) (encCtx ctx) v) := by
  cases hterm : LF.pTerm fuel ctx rest with
  | none =>
      rw [hterm] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
      exact first_active_one (by simp only [eval, os_atLPk_err])
        (matches_parse_raw_none (con0 "paren-malformed"))
        (ParserActiveShape.atLPk (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨t, rest'⟩
      rw [hterm] at h
      rcases h with ⟨u, rfl, hu⟩
      cases rest' with
      | nil =>
          rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
          exact first_active_one (by simp only [eval, encToks, os_atLPk_nil])
            (matches_parse_raw_none (con0 "paren-malformed"))
            (ParserActiveShape.atLPk (peano fuel) (encCtx ctx) (Pp u Nil))
      | cons tok rest2 =>
          cases tok with
          | rpar =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = some (t, rest2) by
                simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_rp])
                (matches_parse_raw_some_of_reduces rest2 hu)
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.rpar :: rest2))))
          | pi =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_pi])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.pi :: rest2))))
          | lam =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_lam])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.lam :: rest2))))
          | arr =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_arr])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.arr :: rest2))))
          | colon =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_colon])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.colon :: rest2))))
          | dot =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_dot])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.dot :: rest2))))
          | lpar =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_lp])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.lpar :: rest2))))
          | type =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_type])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.type :: rest2))))
          | id s =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_one (by simp only [eval, encToks, encTok, os_atLPk_id])
                (matches_parse_raw_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.id s :: rest2))))

theorem atLPk_matches_first_active_of_term_first_active (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok)
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm fuel ctx rest)
      (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (atLPk (peano fuel) (encCtx ctx)
        (tm (peano fuel) (encCtx ctx) (encToks rest))) := by
  exact first_active_bind_active
    (fun s => atLPk (peano fuel) (encCtx ctx) s)
    (fun s _ => ParserActiveShape.atLPk (peano fuel) (encCtx ctx) s)
    (hcong_atLPk_active (peano fuel) (encCtx ctx)
      (isnormal_peano fuel) (isnormal_encCtx ctx))
    hfirst
    (fun {v} hv => atLPk_matches_first_active_of_term_result fuel ctx rest hv)

theorem atom_lpar_first_active_of_term_first_active (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok)
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm fuel ctx rest)
      (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest))) := by
  have htail := atLPk_matches_first_active_of_term_first_active fuel ctx rest hfirst
  have hstep : eval pLF 1
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest)))
      = atLPk (peano fuel) (encCtx ctx)
          (tm (peano fuel) (encCtx ctx) (encToks rest)) := by
    simp only [peano, encToks, encTok, eval, os_at_lp]
  exact first_active_prepend hstep
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest))) htail

theorem atom_type_sim (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)))
      = Pp (Srt (con0 "type")) (encToks rest) := by
  simp only [peano, encToks, encTok, eval, os_at_type]

theorem atom_type_matches (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.type :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)))) := by
  refine ⟨1, ?_⟩
  rw [atom_type_sim]
  exact matches_parse_some (.srt .type) rest

theorem atom_empty_sim (fuel : Nat) (ctx : List String) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks []))
      = PErr (con0 "atom-expected") := by
  simp only [peano, encToks, eval, os_at_err_nil]

theorem atom_empty_matches (fuel : Nat) (ctx : List String) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx [])
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks []))) := by
  refine ⟨1, ?_⟩
  rw [atom_empty_sim]
  exact matches_parse_none (con0 "atom-expected")

theorem atom_pi_expected_sim (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest)))
      = PErr (con0 "atom-expected") := by
  simp only [peano, encToks, encTok, eval, os_at_err_pi]

theorem atom_pi_expected_matches (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.pi :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest)))) := by
  refine ⟨1, ?_⟩
  rw [atom_pi_expected_sim]
  exact matches_parse_none (con0 "atom-expected")

theorem atom_lam_expected_sim (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest)))
      = PErr (con0 "atom-expected") := by
  simp only [peano, encToks, encTok, eval, os_at_err_lam]

theorem atom_lam_expected_matches (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.lam :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest)))) := by
  refine ⟨1, ?_⟩
  rw [atom_lam_expected_sim]
  exact matches_parse_none (con0 "atom-expected")

theorem atom_arr_expected_sim (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest)))
      = PErr (con0 "atom-expected") := by
  simp only [peano, encToks, encTok, eval, os_at_err_arr]

theorem atom_arr_expected_matches (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.arr :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest)))) := by
  refine ⟨1, ?_⟩
  rw [atom_arr_expected_sim]
  exact matches_parse_none (con0 "atom-expected")

theorem atom_colon_expected_sim (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest)))
      = PErr (con0 "atom-expected") := by
  simp only [peano, encToks, encTok, eval, os_at_err_colon]

theorem atom_colon_expected_matches (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.colon :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest)))) := by
  refine ⟨1, ?_⟩
  rw [atom_colon_expected_sim]
  exact matches_parse_none (con0 "atom-expected")

theorem atom_dot_expected_sim (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest)))
      = PErr (con0 "atom-expected") := by
  simp only [peano, encToks, encTok, eval, os_at_err_dot]

theorem atom_dot_expected_matches (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.dot :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest)))) := by
  refine ⟨1, ?_⟩
  rw [atom_dot_expected_sim]
  exact matches_parse_none (con0 "atom-expected")

theorem atom_rpar_expected_sim (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest)))
      = PErr (con0 "atom-expected") := by
  simp only [peano, encToks, encTok, eval, os_at_err_rp]

theorem atom_rpar_expected_matches (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.rpar :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest)))) := by
  refine ⟨1, ?_⟩
  rw [atom_rpar_expected_sim]
  exact matches_parse_none (con0 "atom-expected")

/-- Identifier atoms first take the `at-id` rule, then normalize the emitted `resolve` payload under
    the parser-result constructor. -/
theorem atom_id_sim (fuel : Nat) (ctx : List String) (s : String) (rest : List LF.Tok) :
    ∃ N, eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = Pp (encTerm (LF.resolve ctx s)) (encToks rest) := by
  obtain ⟨N, hN⟩ := resolve_sim ctx s
  obtain ⟨M, hM⟩ := cong_eval (fun u => Pp u (encToks rest))
    (hcong_Pp1 (encToks rest)) N hN (isnormal_encTerm _)
  refine ⟨1 + M, ?_⟩
  have hstep : eval pLF 1 (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = Pp (resolve (encCtx ctx) (con0 s)) (encToks rest) := by
    simp only [peano, encToks, encTok, eval, os_at_id]
  exact eval_trans pLF 1 M _ _ _ hstep hM

theorem atom_id_matches (fuel : Nat) (ctx : List String) (s : String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (fuel + 1) ctx (.id s :: rest))
      (eval pLF N (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))) := by
  obtain ⟨N, hN⟩ := atom_id_sim fuel ctx s rest
  refine ⟨N, ?_⟩
  rw [hN]
  exact matches_parse_some (LF.resolve ctx s) rest

/-- All `lf-atom` cases except parenthesized terms: these are the leaf cases of the parser
    simulation.  The lone excluded case is where the proof must call the `pTerm` simulation. -/
theorem atom_non_lpar_matches (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    (hnot : ∀ rest, toks ≠ .lpar :: rest) :
    ∃ N, MatchesParse (LF.pAtom fuel ctx toks)
      (eval pLF N (at' (peano fuel) (encCtx ctx) (encToks toks))) := by
  cases fuel with
  | zero => exact atom_no_fuel_matches ctx toks
  | succ fuel =>
    cases toks with
    | nil => exact atom_empty_matches fuel ctx
    | cons tok rest =>
      cases tok with
      | pi => exact atom_pi_expected_matches fuel ctx rest
      | lam => exact atom_lam_expected_matches fuel ctx rest
      | arr => exact atom_arr_expected_matches fuel ctx rest
      | colon => exact atom_colon_expected_matches fuel ctx rest
      | dot => exact atom_dot_expected_matches fuel ctx rest
      | lpar => exact False.elim (hnot rest rfl)
      | rpar => exact atom_rpar_expected_matches fuel ctx rest
      | type => exact atom_type_matches fuel ctx rest
      | id s => exact atom_id_matches fuel ctx s rest

theorem atom_non_lpar_raw_matches (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    (hnot : ∀ rest, toks ≠ .lpar :: rest) :
    ∃ N, MatchesParseRaw (LF.pAtom fuel ctx toks)
      (eval pLF N (at' (peano fuel) (encCtx ctx) (encToks toks))) := by
  obtain ⟨N, hN⟩ := atom_non_lpar_matches fuel ctx toks hnot
  exact ⟨N, matches_parse_to_raw hN⟩

theorem atom_no_fuel_first_raw (ctx : List String) (toks : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom 0 ctx toks)
      (at' Z (encCtx ctx) (encToks toks)) := by
  exact first_matches_one (atom_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (not_result_at Z (encCtx ctx) (encToks toks))

theorem atom_type_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.type :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))) := by
  exact first_matches_one (atom_type_sim fuel ctx rest)
    (matches_parse_raw_some (.srt .type) rest)
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)))

theorem atom_id_first_raw (fuel : Nat) (ctx : List String) (s : String)
    (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.id s :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))) := by
  have hstep : eval pLF 1
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = Pp (resolve (encCtx ctx) (con0 s)) (encToks rest) := by
    simp only [peano, encToks, encTok, eval, os_at_id]
  obtain ⟨Nres, hNres⟩ := resolve_sim ctx s
  have hres : ReducesToEncTerm (resolve (encCtx ctx) (con0 s)) (LF.resolve ctx s) :=
    ⟨Nres, hNres⟩
  exact first_matches_one hstep
    (matches_parse_raw_some_of_reduces rest hres)
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))

theorem atom_empty_first_raw (fuel : Nat) (ctx : List String) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx [])
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks [])) := by
  exact first_matches_one (atom_empty_sim fuel ctx)
    (matches_parse_raw_none (con0 "atom-expected"))
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks []))

theorem atom_pi_expected_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.pi :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest))) := by
  exact first_matches_one (atom_pi_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest)))

theorem atom_lam_expected_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lam :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest))) := by
  exact first_matches_one (atom_lam_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest)))

theorem atom_arr_expected_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.arr :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest))) := by
  exact first_matches_one (atom_arr_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest)))

theorem atom_colon_expected_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.colon :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest))) := by
  exact first_matches_one (atom_colon_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest)))

theorem atom_dot_expected_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.dot :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest))) := by
  exact first_matches_one (atom_dot_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest)))

theorem atom_rpar_expected_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.rpar :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest))) := by
  exact first_matches_one (atom_rpar_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (not_result_at (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest)))

theorem atom_non_lpar_first_raw (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    (hnot : ∀ rest, toks ≠ .lpar :: rest) :
    FirstMatchesParseRaw (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)) := by
  cases fuel with
  | zero => exact atom_no_fuel_first_raw ctx toks
  | succ fuel =>
      cases toks with
      | nil => exact atom_empty_first_raw fuel ctx
      | cons tok rest =>
          cases tok with
          | pi => exact atom_pi_expected_first_raw fuel ctx rest
          | lam => exact atom_lam_expected_first_raw fuel ctx rest
          | arr => exact atom_arr_expected_first_raw fuel ctx rest
          | colon => exact atom_colon_expected_first_raw fuel ctx rest
          | dot => exact atom_dot_expected_first_raw fuel ctx rest
          | lpar => exact False.elim (hnot rest rfl)
          | rpar => exact atom_rpar_expected_first_raw fuel ctx rest
          | type => exact atom_type_first_raw fuel ctx rest
          | id s => exact atom_id_first_raw fuel ctx s rest

theorem atom_no_fuel_first_active (ctx : List String) (toks : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom 0 ctx toks)
      (at' Z (encCtx ctx) (encToks toks)) := by
  exact first_active_one (atom_no_fuel_sim ctx toks)
    (matches_parse_raw_none (con0 "no-fuel"))
    (ParserActiveShape.atom Z (encCtx ctx) (encToks toks))

theorem atom_type_first_active (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.type :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))) := by
  exact first_active_one (atom_type_sim fuel ctx rest)
    (matches_parse_raw_some (.srt .type) rest)
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)))

theorem atom_id_first_active (fuel : Nat) (ctx : List String) (s : String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.id s :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))) := by
  have hstep : eval pLF 1
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = Pp (resolve (encCtx ctx) (con0 s)) (encToks rest) := by
    simp only [peano, encToks, encTok, eval, os_at_id]
  obtain ⟨Nres, hNres⟩ := resolve_sim ctx s
  have hres : ReducesToEncTerm (resolve (encCtx ctx) (con0 s)) (LF.resolve ctx s) :=
    ⟨Nres, hNres⟩
  exact first_active_one hstep
    (matches_parse_raw_some_of_reduces rest hres)
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))

theorem atom_empty_first_active (fuel : Nat) (ctx : List String) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx [])
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks [])) := by
  exact first_active_one (atom_empty_sim fuel ctx)
    (matches_parse_raw_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks []))

theorem atom_pi_expected_first_active (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.pi :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest))) := by
  exact first_active_one (atom_pi_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest)))

theorem atom_lam_expected_first_active (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.lam :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest))) := by
  exact first_active_one (atom_lam_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest)))

theorem atom_arr_expected_first_active (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.arr :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest))) := by
  exact first_active_one (atom_arr_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest)))

theorem atom_colon_expected_first_active (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.colon :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest))) := by
  exact first_active_one (atom_colon_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest)))

theorem atom_dot_expected_first_active (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.dot :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest))) := by
  exact first_active_one (atom_dot_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest)))

theorem atom_rpar_expected_first_active (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx (.rpar :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest))) := by
  exact first_active_one (atom_rpar_expected_sim fuel ctx rest)
    (matches_parse_raw_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest)))

theorem atom_non_lpar_first_active (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    (hnot : ∀ rest, toks ≠ .lpar :: rest) :
    FirstActiveMatchesParseRaw (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)) := by
  cases fuel with
  | zero => exact atom_no_fuel_first_active ctx toks
  | succ fuel =>
      cases toks with
      | nil => exact atom_empty_first_active fuel ctx
      | cons tok rest =>
          cases tok with
          | pi => exact atom_pi_expected_first_active fuel ctx rest
          | lam => exact atom_lam_expected_first_active fuel ctx rest
          | arr => exact atom_arr_expected_first_active fuel ctx rest
          | colon => exact atom_colon_expected_first_active fuel ctx rest
          | dot => exact atom_dot_expected_first_active fuel ctx rest
          | lpar => exact False.elim (hnot rest rfl)
          | rpar => exact atom_rpar_expected_first_active fuel ctx rest
          | type => exact atom_type_first_active fuel ctx rest
          | id s => exact atom_id_first_active fuel ctx s rest

theorem atom_succ_first_active_of_lpar_term (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok)
    (hlpar : ∀ rest, toks = .lpar :: rest →
      FirstActiveMatchesParseRaw (LF.pTerm fuel ctx rest)
        (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx toks)
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  cases toks with
  | nil =>
      exact atom_non_lpar_first_active (fuel + 1) ctx [] (by intro rest h; cases h)
  | cons tok rest =>
      cases tok with
      | pi =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.pi :: rest)
            (by intro r h; cases h)
      | lam =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.lam :: rest)
            (by intro r h; cases h)
      | arr =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.arr :: rest)
            (by intro r h; cases h)
      | colon =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.colon :: rest)
            (by intro r h; cases h)
      | dot =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.dot :: rest)
            (by intro r h; cases h)
      | lpar =>
          exact atom_lpar_first_active_of_term_first_active fuel ctx rest (hlpar rest rfl)
      | rpar =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.rpar :: rest)
            (by intro r h; cases h)
      | type =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.type :: rest)
            (by intro r h; cases h)
      | id s =>
          exact atom_non_lpar_first_active (fuel + 1) ctx (.id s :: rest)
            (by intro r h; cases h)

theorem atLPk_matches_first_active_shiftable_of_term_result (fuel : Nat)
    (ctx : List String) (rest : List LF.Tok) {v : AST}
    (h : MatchesParseShiftable (LF.pTerm fuel ctx rest) v) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (atLPk (peano fuel) (encCtx ctx) v) := by
  cases hterm : LF.pTerm fuel ctx rest with
  | none =>
      rw [hterm] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
      exact first_active_shiftable_one (by simp only [eval, os_atLPk_err])
        (matches_parse_shiftable_none (con0 "paren-malformed"))
        (ParserActiveShape.atLPk (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨t, rest'⟩
      rw [hterm] at h
      rcases h with ⟨u, rfl, hu⟩
      cases rest' with
      | nil =>
          rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
          exact first_active_shiftable_one (by simp only [eval, encToks, os_atLPk_nil])
            (matches_parse_shiftable_none (con0 "paren-malformed"))
            (ParserActiveShape.atLPk (peano fuel) (encCtx ctx) (Pp u Nil))
      | cons tok rest2 =>
          cases tok with
          | rpar =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = some (t, rest2) by
                simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_rp])
                (matches_parse_shiftable_some_of_payload hu)
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.rpar :: rest2))))
          | pi =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_pi])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.pi :: rest2))))
          | lam =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_lam])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.lam :: rest2))))
          | arr =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_arr])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.arr :: rest2))))
          | colon =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_colon])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.colon :: rest2))))
          | dot =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_dot])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.dot :: rest2))))
          | lpar =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_lp])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.lpar :: rest2))))
          | type =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_type])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.type :: rest2))))
          | id s =>
              rw [show LF.pAtom (fuel + 1) ctx (.lpar :: rest) = none by simp [LF.pAtom, hterm]]
              exact first_active_shiftable_one (by simp only [eval, encToks, encTok, os_atLPk_id])
                (matches_parse_shiftable_none (con0 "paren-malformed"))
                (ParserActiveShape.atLPk (peano fuel) (encCtx ctx)
                  (Pp u (encToks (.id s :: rest2))))

theorem atLPk_matches_first_active_shiftable_of_term_first_active (fuel : Nat)
    (ctx : List String) (rest : List LF.Tok)
    (hfirst : FirstActiveMatchesParseShiftable (LF.pTerm fuel ctx rest)
      (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (atLPk (peano fuel) (encCtx ctx)
        (tm (peano fuel) (encCtx ctx) (encToks rest))) := by
  exact first_active_shiftable_bind_active
    (fun s => atLPk (peano fuel) (encCtx ctx) s)
    (fun s _ => ParserActiveShape.atLPk (peano fuel) (encCtx ctx) s)
    (hcong_atLPk_active (peano fuel) (encCtx ctx)
      (isnormal_peano fuel) (isnormal_encCtx ctx))
    hfirst
    (fun {v} hv => atLPk_matches_first_active_shiftable_of_term_result fuel ctx rest hv)

theorem atom_lpar_first_active_shiftable_of_term_first_active (fuel : Nat)
    (ctx : List String) (rest : List LF.Tok)
    (hfirst : FirstActiveMatchesParseShiftable (LF.pTerm fuel ctx rest)
      (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.lpar :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest))) := by
  have htail := atLPk_matches_first_active_shiftable_of_term_first_active fuel ctx rest hfirst
  have hstep : eval pLF 1
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest)))
      = atLPk (peano fuel) (encCtx ctx)
          (tm (peano fuel) (encCtx ctx) (encToks rest)) := by
    simp only [peano, encToks, encTok, eval, os_at_lp]
  exact first_active_shiftable_prepend hstep
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.lpar :: rest))) htail

theorem atom_no_fuel_first_active_shiftable (ctx : List String) (toks : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom 0 ctx toks)
      (at' Z (encCtx ctx) (encToks toks)) := by
  exact first_active_shiftable_one (atom_no_fuel_sim ctx toks)
    (matches_parse_shiftable_none (con0 "no-fuel"))
    (ParserActiveShape.atom Z (encCtx ctx) (encToks toks))

theorem atom_type_first_active_shiftable (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.type :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))) := by
  exact first_active_shiftable_one (atom_type_sim fuel ctx rest)
    (matches_parse_shiftable_some_of_payload (shiftable_encTerm (.srt .type)))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)))

theorem atom_id_first_active_shiftable (fuel : Nat) (ctx : List String) (s : String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.id s :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))) := by
  have hstep : eval pLF 1
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = Pp (resolve (encCtx ctx) (con0 s)) (encToks rest) := by
    simp only [peano, encToks, encTok, eval, os_at_id]
  exact first_active_shiftable_one hstep
    (matches_parse_shiftable_some_of_payload (shiftable_resolve ctx s))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))

theorem atom_empty_first_active_shiftable (fuel : Nat) (ctx : List String) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx [])
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks [])) := by
  exact first_active_shiftable_one (atom_empty_sim fuel ctx)
    (matches_parse_shiftable_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks []))

theorem atom_pi_expected_first_active_shiftable (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.pi :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest))) := by
  exact first_active_shiftable_one (atom_pi_expected_sim fuel ctx rest)
    (matches_parse_shiftable_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: rest)))

theorem atom_lam_expected_first_active_shiftable (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.lam :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest))) := by
  exact first_active_shiftable_one (atom_lam_expected_sim fuel ctx rest)
    (matches_parse_shiftable_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: rest)))

theorem atom_arr_expected_first_active_shiftable (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.arr :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest))) := by
  exact first_active_shiftable_one (atom_arr_expected_sim fuel ctx rest)
    (matches_parse_shiftable_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.arr :: rest)))

theorem atom_colon_expected_first_active_shiftable (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.colon :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest))) := by
  exact first_active_shiftable_one (atom_colon_expected_sim fuel ctx rest)
    (matches_parse_shiftable_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.colon :: rest)))

theorem atom_dot_expected_first_active_shiftable (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.dot :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest))) := by
  exact first_active_shiftable_one (atom_dot_expected_sim fuel ctx rest)
    (matches_parse_shiftable_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.dot :: rest)))

theorem atom_rpar_expected_first_active_shiftable (fuel : Nat) (ctx : List String)
    (rest : List LF.Tok) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx (.rpar :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest))) := by
  exact first_active_shiftable_one (atom_rpar_expected_sim fuel ctx rest)
    (matches_parse_shiftable_none (con0 "atom-expected"))
    (ParserActiveShape.atom (peano (fuel + 1)) (encCtx ctx) (encToks (.rpar :: rest)))

theorem atom_non_lpar_first_active_shiftable (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok) (hnot : ∀ rest, toks ≠ .lpar :: rest) :
    FirstActiveMatchesParseShiftable (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)) := by
  cases fuel with
  | zero => exact atom_no_fuel_first_active_shiftable ctx toks
  | succ fuel =>
      cases toks with
      | nil => exact atom_empty_first_active_shiftable fuel ctx
      | cons tok rest =>
          cases tok with
          | pi => exact atom_pi_expected_first_active_shiftable fuel ctx rest
          | lam => exact atom_lam_expected_first_active_shiftable fuel ctx rest
          | arr => exact atom_arr_expected_first_active_shiftable fuel ctx rest
          | colon => exact atom_colon_expected_first_active_shiftable fuel ctx rest
          | dot => exact atom_dot_expected_first_active_shiftable fuel ctx rest
          | lpar => exact False.elim (hnot rest rfl)
          | rpar => exact atom_rpar_expected_first_active_shiftable fuel ctx rest
          | type => exact atom_type_first_active_shiftable fuel ctx rest
          | id s => exact atom_id_first_active_shiftable fuel ctx s rest

theorem atom_succ_first_active_shiftable_of_lpar_term (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok)
    (hlpar : ∀ rest, toks = .lpar :: rest →
      FirstActiveMatchesParseShiftable (LF.pTerm fuel ctx rest)
        (tm (peano fuel) (encCtx ctx) (encToks rest))) :
    FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx toks)
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  cases toks with
  | nil =>
      exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx [] (by intro rest h; cases h)
  | cons tok rest =>
      cases tok with
      | pi =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.pi :: rest)
            (by intro r h; cases h)
      | lam =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.lam :: rest)
            (by intro r h; cases h)
      | arr =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.arr :: rest)
            (by intro r h; cases h)
      | colon =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.colon :: rest)
            (by intro r h; cases h)
      | dot =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.dot :: rest)
            (by intro r h; cases h)
      | lpar =>
          exact atom_lpar_first_active_shiftable_of_term_first_active fuel ctx rest (hlpar rest rfl)
      | rpar =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.rpar :: rest)
            (by intro r h; cases h)
      | type =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.type :: rest)
            (by intro r h; cases h)
      | id s =>
          exact atom_non_lpar_first_active_shiftable (fuel + 1) ctx (.id s :: rest)
            (by intro r h; cases h)

theorem atom_one_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pAtom (0 + 1) ctx toks)
      (eval pLF N (at' (peano (0 + 1)) (encCtx ctx) (encToks toks))) := by
  cases toks with
  | nil =>
      exact atom_non_lpar_matches (0 + 1) ctx [] (by intro rest h; cases h)
  | cons tok rest =>
      cases tok with
      | lpar => exact atom_lpar_no_fuel_matches ctx rest
      | pi =>
          exact atom_non_lpar_matches (0 + 1) ctx (.pi :: rest) (by intro r h; cases h)
      | lam =>
          exact atom_non_lpar_matches (0 + 1) ctx (.lam :: rest) (by intro r h; cases h)
      | arr =>
          exact atom_non_lpar_matches (0 + 1) ctx (.arr :: rest) (by intro r h; cases h)
      | colon =>
          exact atom_non_lpar_matches (0 + 1) ctx (.colon :: rest) (by intro r h; cases h)
      | dot =>
          exact atom_non_lpar_matches (0 + 1) ctx (.dot :: rest) (by intro r h; cases h)
      | rpar =>
          exact atom_non_lpar_matches (0 + 1) ctx (.rpar :: rest) (by intro r h; cases h)
      | type =>
          exact atom_non_lpar_matches (0 + 1) ctx (.type :: rest) (by intro r h; cases h)
      | id s =>
          exact atom_non_lpar_matches (0 + 1) ctx (.id s :: rest) (by intro r h; cases h)

theorem pApp_fail_no_fuel (ctx : List String) (toks : List LF.Tok) :
    LF.pApp (0 + 1) ctx toks = none := by
  rfl

theorem pApp_fail_empty (fuel : Nat) (ctx : List String) :
    LF.pApp ((fuel + 1) + 1) ctx [] = none := by
  rfl

theorem pApp_fail_pi (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.pi :: rest) = none := by
  rfl

theorem pApp_fail_lam (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.lam :: rest) = none := by
  rfl

theorem pApp_fail_arr (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.arr :: rest) = none := by
  rfl

theorem pApp_fail_colon (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.colon :: rest) = none := by
  rfl

theorem pApp_fail_dot (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.dot :: rest) = none := by
  rfl

theorem pApp_fail_rpar (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.rpar :: rest) = none := by
  rfl

theorem pApp_type_eq (fuel : Nat) (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.type :: rest)
      = some (LF.pAppMore (fuel + 1) ctx (.srt .type) rest) := by
  rfl

theorem pApp_id_eq (fuel : Nat) (ctx : List String) (s : String) (rest : List LF.Tok) :
    LF.pApp ((fuel + 1) + 1) ctx (.id s :: rest)
      = some (LF.pAppMore (fuel + 1) ctx (LF.resolve ctx s) rest) := by
  rfl

theorem pApp_fail_lpar_no_fuel (ctx : List String) (rest : List LF.Tok) :
    LF.pApp ((0 + 1) + 1) ctx (.lpar :: rest) = none := by
  rfl

theorem app_fail_of_atom_error_raw (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    (e : AST)
    (hat : oneStep pLF (at' (peano fuel) (encCtx ctx) (encToks toks)) = some (PErr e))
    (hparse : LF.pApp (fuel + 1) ctx toks = none) :
    ∃ N, MatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
      (eval pLF N (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks))) := by
  have hstep2 := hcong_apK_at (peano fuel) (encCtx ctx) (peano fuel) (encCtx ctx)
    (encToks toks) (isnormal_peano fuel) (isnormal_encCtx ctx) (PErr e) hat
  refine ⟨3, ?_⟩
  simp only [peano, eval, os_ap_s, hstep2, os_apK_err]
  rw [hparse]
  exact matches_parse_raw_none e

theorem app_fail_of_atom_error_first_raw (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    (e : AST)
    (hat : oneStep pLF (at' (peano fuel) (encCtx ctx) (encToks toks)) = some (PErr e))
    (hparse : LF.pApp (fuel + 1) ctx toks = none) :
    FirstMatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
      (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  have hapK_at : eval pLF 1
      (apK (peano fuel) (encCtx ctx) (at' (peano fuel) (encCtx ctx) (encToks toks)))
      = apK (peano fuel) (encCtx ctx) (PErr e) := by
    have hstep := hcong_apK_at (peano fuel) (encCtx ctx) (peano fuel) (encCtx ctx)
      (encToks toks) (isnormal_peano fuel) (isnormal_encCtx ctx) (PErr e) hat
    simp only [eval, hstep]
  have hapK_err : FirstMatchesParseRaw none (apK (peano fuel) (encCtx ctx) (PErr e)) :=
    first_matches_one (by simp only [eval, os_apK_err])
      (matches_parse_raw_none e)
      (not_result_apK (peano fuel) (encCtx ctx) (PErr e))
  have hinner := first_matches_prepend hapK_at
    (not_result_apK (peano fuel) (encCtx ctx)
      (at' (peano fuel) (encCtx ctx) (encToks toks))) hapK_err
  have hap : eval pLF 1 (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks))
      = apK (peano fuel) (encCtx ctx) (at' (peano fuel) (encCtx ctx) (encToks toks)) := by
    simp only [peano, eval, os_ap_s]
  rw [hparse]
  exact first_matches_prepend hap
    (not_result_ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) hinner

theorem apK_matches_raw_of_atom_result (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    {v : AST} (h : MatchesParseRaw (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        ∃ N, MatchesParseRaw (some (LF.pAppMore fuel ctx a rest))
          (eval pLF N (apm (peano fuel) (encCtx ctx) u (encToks rest)))) :
    ∃ N, MatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
      (eval pLF N (apK (peano fuel) (encCtx ctx) v)) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      rw [show LF.pApp (fuel + 1) ctx toks = none by simp [LF.pApp, hatom]]
      simp only [eval, os_apK_err]
      exact matches_parse_raw_none e
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      obtain ⟨Ntail, htail⟩ := tail a rest u hatom hu
      have hstep : eval pLF 1 (apK (peano fuel) (encCtx ctx) (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) u (encToks rest) := by
        simp only [eval, os_apK_p]
      have htotal := eval_trans pLF 1 Ntail _ _ _ hstep rfl
      refine ⟨1 + Ntail, ?_⟩
      rw [htotal]
      rw [show LF.pApp (fuel + 1) ctx toks = some (LF.pAppMore fuel ctx a rest) by
        simp [LF.pApp, hatom]]
      exact htail

theorem apK_matches_first_raw_of_atom_result (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    {v : AST} (h : MatchesParseRaw (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        FirstMatchesParseRaw (some (LF.pAppMore fuel ctx a rest))
          (apm (peano fuel) (encCtx ctx) u (encToks rest))) :
    FirstMatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
      (apK (peano fuel) (encCtx ctx) v) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pApp (fuel + 1) ctx toks = none by simp [LF.pApp, hatom]]
      exact first_matches_one (by simp only [eval, os_apK_err])
        (matches_parse_raw_none e)
        (not_result_apK (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      have hstep : eval pLF 1 (apK (peano fuel) (encCtx ctx) (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) u (encToks rest) := by
        simp only [eval, os_apK_p]
      obtain htail := tail a rest u hatom hu
      rw [show LF.pApp (fuel + 1) ctx toks = some (LF.pAppMore fuel ctx a rest) by
        simp [LF.pApp, hatom]]
      exact first_matches_prepend hstep
        (not_result_apK (peano fuel) (encCtx ctx) (Pp u (encToks rest))) htail

theorem apK_matches_first_active_of_atom_result (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok)
    {v : AST} (h : MatchesParseRaw (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        FirstActiveMatchesParseRaw (some (LF.pAppMore fuel ctx a rest))
          (apm (peano fuel) (encCtx ctx) u (encToks rest))) :
    FirstActiveMatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
      (apK (peano fuel) (encCtx ctx) v) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pApp (fuel + 1) ctx toks = none by simp [LF.pApp, hatom]]
      exact first_active_one (by simp only [eval, os_apK_err])
        (matches_parse_raw_none e)
        (ParserActiveShape.apK (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      have hstep : eval pLF 1 (apK (peano fuel) (encCtx ctx) (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) u (encToks rest) := by
        simp only [eval, os_apK_p]
      obtain htail := tail a rest u hatom hu
      rw [show LF.pApp (fuel + 1) ctx toks = some (LF.pAppMore fuel ctx a rest) by
        simp [LF.pApp, hatom]]
      exact first_active_prepend hstep
        (ParserActiveShape.apK (peano fuel) (encCtx ctx) (Pp u (encToks rest))) htail

theorem app_succ_first_active_of_atom_appmore (fuel : Nat) (ctx : List String)
    (toks : List LF.Tok)
    (hatom : FirstActiveMatchesParseRaw (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)))
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        FirstActiveMatchesParseRaw (some (LF.pAppMore fuel ctx a rest))
          (apm (peano fuel) (encCtx ctx) u (encToks rest))) :
    FirstActiveMatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
      (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  have hinner : FirstActiveMatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
      (apK (peano fuel) (encCtx ctx)
        (at' (peano fuel) (encCtx ctx) (encToks toks))) :=
    first_active_bind_active
      (fun s => apK (peano fuel) (encCtx ctx) s)
      (fun s _ => ParserActiveShape.apK (peano fuel) (encCtx ctx) s)
      (hcong_apK_active (peano fuel) (encCtx ctx)
        (isnormal_peano fuel) (isnormal_encCtx ctx))
      hatom
      (fun {v} hv => apK_matches_first_active_of_atom_result fuel ctx toks hv tail)
  have hap : eval pLF 1 (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks))
      = apK (peano fuel) (encCtx ctx)
          (at' (peano fuel) (encCtx ctx) (encToks toks)) := by
    simp only [peano, eval, os_ap_s]
  exact first_active_prepend hap
    (ParserActiveShape.ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) hinner

theorem apK_matches_first_active_shiftable_of_atom_result (fuel : Nat)
    (ctx : List String) (toks : List LF.Tok)
    {v : AST} (h : MatchesParseShiftable (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ShiftablePayload u a →
        FirstActiveMatchesParseShiftable (some (LF.pAppMore fuel ctx a rest))
          (apm (peano fuel) (encCtx ctx) u (encToks rest))) :
    FirstActiveMatchesParseShiftable (LF.pApp (fuel + 1) ctx toks)
      (apK (peano fuel) (encCtx ctx) v) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pApp (fuel + 1) ctx toks = none by simp [LF.pApp, hatom]]
      exact first_active_shiftable_one (by simp only [eval, os_apK_err])
        (matches_parse_shiftable_none e)
        (ParserActiveShape.apK (peano fuel) (encCtx ctx) (PErr e))
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      have hstep : eval pLF 1 (apK (peano fuel) (encCtx ctx) (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) u (encToks rest) := by
        simp only [eval, os_apK_p]
      obtain htail := tail a rest u hatom hu
      rw [show LF.pApp (fuel + 1) ctx toks = some (LF.pAppMore fuel ctx a rest) by
        simp [LF.pApp, hatom]]
      exact first_active_shiftable_prepend hstep
        (ParserActiveShape.apK (peano fuel) (encCtx ctx) (Pp u (encToks rest))) htail

theorem app_succ_first_active_shiftable_of_atom_appmore (fuel : Nat)
    (ctx : List String) (toks : List LF.Tok)
    (hatom : FirstActiveMatchesParseShiftable (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)))
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ShiftablePayload u a →
        FirstActiveMatchesParseShiftable (some (LF.pAppMore fuel ctx a rest))
          (apm (peano fuel) (encCtx ctx) u (encToks rest))) :
    FirstActiveMatchesParseShiftable (LF.pApp (fuel + 1) ctx toks)
      (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  have hinner : FirstActiveMatchesParseShiftable (LF.pApp (fuel + 1) ctx toks)
      (apK (peano fuel) (encCtx ctx)
        (at' (peano fuel) (encCtx ctx) (encToks toks))) :=
    first_active_shiftable_bind_active
      (fun s => apK (peano fuel) (encCtx ctx) s)
      (fun s _ => ParserActiveShape.apK (peano fuel) (encCtx ctx) s)
      (hcong_apK_active (peano fuel) (encCtx ctx)
        (isnormal_peano fuel) (isnormal_encCtx ctx))
      hatom
      (fun {v} hv => apK_matches_first_active_shiftable_of_atom_result fuel ctx toks hv tail)
  have hap : eval pLF 1 (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks))
      = apK (peano fuel) (encCtx ctx)
          (at' (peano fuel) (encCtx ctx) (encToks toks)) := by
    simp only [peano, eval, os_ap_s]
  exact first_active_shiftable_prepend hap
    (ParserActiveShape.ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) hinner

theorem app_one_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pApp (0 + 1) ctx toks)
      (eval pLF N (ap (peano (0 + 1)) (encCtx ctx) (encToks toks))) := by
  obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw 0 ctx toks (con0 "no-fuel")
    (by simp only [peano, os_at_z]) (pApp_fail_no_fuel ctx toks)
  exact matches_parse_exact_of_raw_eval hN


theorem app_success_type_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok)
    (tail : ∃ N, MatchesParseRaw
      (some (LF.pAppMore (fuel + 1) ctx (.srt .type) rest))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx)
        (Srt (con0 "type")) (encToks rest)))) :
    ∃ N, MatchesParseRaw (LF.pApp ((fuel + 1) + 1) ctx (.type :: rest))
      (eval pLF N (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.type :: rest)))) := by
  obtain ⟨Ntail, htail⟩ := tail
  have hstep2 := hcong_apK_at (peano (fuel + 1)) (encCtx ctx) (peano (fuel + 1))
    (encCtx ctx) (encToks (.type :: rest))
    (isnormal_peano (fuel + 1)) (isnormal_encCtx ctx)
    (Pp (Srt (con0 "type")) (encToks rest))
    (by simp only [peano, encToks, encTok, os_at_type])
  have hstep2' : oneStep pLF
      (apK (S (peano fuel)) (encCtx ctx)
        (at' (S (peano fuel)) (encCtx ctx) (encToks (.type :: rest))))
      = some (apK (S (peano fuel)) (encCtx ctx) (Pp (Srt (con0 "type")) (encToks rest))) := by
    simpa only [peano] using hstep2
  have hpre : eval pLF 3 (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.type :: rest)))
      = apm (peano (fuel + 1)) (encCtx ctx) (Srt (con0 "type")) (encToks rest) := by
    simp only [peano, eval, os_ap_s, hstep2', os_apK_p]
  refine ⟨3 + Ntail, ?_⟩
  have htotal := eval_trans pLF 3 Ntail _ _ _ hpre rfl
  rw [htotal, pApp_type_eq]
  exact htail

theorem app_success_id_raw (fuel : Nat) (ctx : List String) (s : String) (rest : List LF.Tok)
    (tail : ∃ N, MatchesParseRaw
      (some (LF.pAppMore (fuel + 1) ctx (LF.resolve ctx s) rest))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx)
        (resolve (encCtx ctx) (con0 s)) (encToks rest)))) :
    ∃ N, MatchesParseRaw (LF.pApp ((fuel + 1) + 1) ctx (.id s :: rest))
      (eval pLF N (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.id s :: rest)))) := by
  obtain ⟨Ntail, htail⟩ := tail
  have hstep2 := hcong_apK_at (peano (fuel + 1)) (encCtx ctx) (peano (fuel + 1))
    (encCtx ctx) (encToks (.id s :: rest))
    (isnormal_peano (fuel + 1)) (isnormal_encCtx ctx)
    (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest))
    (by simp only [peano, encToks, encTok, os_at_id])
  have hstep2' : oneStep pLF
      (apK (S (peano fuel)) (encCtx ctx)
        (at' (S (peano fuel)) (encCtx ctx) (encToks (.id s :: rest))))
      = some (apK (S (peano fuel)) (encCtx ctx)
        (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest))) := by
    simpa only [peano] using hstep2
  have hpre : eval pLF 3 (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = apm (peano (fuel + 1)) (encCtx ctx) (resolve (encCtx ctx) (con0 s)) (encToks rest) := by
    simp only [peano, eval, os_ap_s, hstep2', os_apK_p]
  refine ⟨3 + Ntail, ?_⟩
  have htotal := eval_trans pLF 3 Ntail _ _ _ hpre rfl
  rw [htotal, pApp_id_eq]
  exact htail

theorem app_success_type_first_raw (fuel : Nat) (ctx : List String) (rest : List LF.Tok)
    (tail : FirstMatchesParseRaw
      (some (LF.pAppMore (fuel + 1) ctx (.srt .type) rest))
      (apm (peano (fuel + 1)) (encCtx ctx) (Srt (con0 "type")) (encToks rest))) :
    FirstMatchesParseRaw (LF.pApp ((fuel + 1) + 1) ctx (.type :: rest))
      (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.type :: rest))) := by
  have hat : oneStep pLF
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)))
      = some (Pp (Srt (con0 "type")) (encToks rest)) := by
    simp only [peano, encToks, encTok, os_at_type]
  have hapK_at : eval pLF 1
      (apK (peano (fuel + 1)) (encCtx ctx)
        (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))))
      = apK (peano (fuel + 1)) (encCtx ctx) (Pp (Srt (con0 "type")) (encToks rest)) := by
    have hstep := hcong_apK_at (peano (fuel + 1)) (encCtx ctx) (peano (fuel + 1))
      (encCtx ctx) (encToks (.type :: rest))
      (isnormal_peano (fuel + 1)) (isnormal_encCtx ctx)
      (Pp (Srt (con0 "type")) (encToks rest))
      hat
    simp only [eval, hstep]
  have hapK_p : eval pLF 1
      (apK (peano (fuel + 1)) (encCtx ctx) (Pp (Srt (con0 "type")) (encToks rest)))
      = apm (peano (fuel + 1)) (encCtx ctx) (Srt (con0 "type")) (encToks rest) := by
    simp only [eval, os_apK_p]
  have hmid := first_matches_prepend hapK_p
    (not_result_apK (peano (fuel + 1)) (encCtx ctx)
      (Pp (Srt (con0 "type")) (encToks rest))) tail
  have hinner := first_matches_prepend hapK_at
    (not_result_apK (peano (fuel + 1)) (encCtx ctx)
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)))) hmid
  have hap : eval pLF 1
      (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.type :: rest)))
      = apK (peano (fuel + 1)) (encCtx ctx)
        (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))) := by
    simp only [peano, eval, os_ap_s]
  rw [pApp_type_eq]
  exact first_matches_prepend hap
    (not_result_ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.type :: rest))) hinner

theorem app_success_id_first_raw (fuel : Nat) (ctx : List String) (s : String)
    (rest : List LF.Tok)
    (tail : FirstMatchesParseRaw
      (some (LF.pAppMore (fuel + 1) ctx (LF.resolve ctx s) rest))
      (apm (peano (fuel + 1)) (encCtx ctx) (resolve (encCtx ctx) (con0 s)) (encToks rest))) :
    FirstMatchesParseRaw (LF.pApp ((fuel + 1) + 1) ctx (.id s :: rest))
      (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.id s :: rest))) := by
  have hat : oneStep pLF
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = some (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest)) := by
    simp only [peano, encToks, encTok, os_at_id]
  have hapK_at : eval pLF 1
      (apK (peano (fuel + 1)) (encCtx ctx)
        (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))))
      = apK (peano (fuel + 1)) (encCtx ctx)
        (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest)) := by
    have hstep := hcong_apK_at (peano (fuel + 1)) (encCtx ctx) (peano (fuel + 1))
      (encCtx ctx) (encToks (.id s :: rest))
      (isnormal_peano (fuel + 1)) (isnormal_encCtx ctx)
      (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest))
      hat
    simp only [eval, hstep]
  have hapK_p : eval pLF 1
      (apK (peano (fuel + 1)) (encCtx ctx)
        (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest)))
      = apm (peano (fuel + 1)) (encCtx ctx)
        (resolve (encCtx ctx) (con0 s)) (encToks rest) := by
    simp only [eval, os_apK_p]
  have hmid := first_matches_prepend hapK_p
    (not_result_apK (peano (fuel + 1)) (encCtx ctx)
      (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest))) tail
  have hinner := first_matches_prepend hapK_at
    (not_result_apK (peano (fuel + 1)) (encCtx ctx)
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)))) hmid
  have hap : eval pLF 1
      (ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.id s :: rest)))
      = apK (peano (fuel + 1)) (encCtx ctx)
        (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))) := by
    simp only [peano, eval, os_ap_s]
  rw [pApp_id_eq]
  exact first_matches_prepend hap
    (not_result_ap (peano ((fuel + 1) + 1)) (encCtx ctx) (encToks (.id s :: rest))) hinner

theorem app_lpar_no_fuel_sim (ctx : List String) (rest : List LF.Tok) :
    eval pLF 5 (ap (peano ((0 + 1) + 1)) (encCtx ctx) (encToks (.lpar :: rest)))
      = PErr (con0 "paren-malformed") := by
  have h_at_lp : oneStep pLF
      (at' (peano (0 + 1)) (encCtx ctx) (encToks (.lpar :: rest)))
      = some (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest))) := by
    simp only [peano, encToks, encTok, os_at_lp]
  have hstep2 := hcong_apK_at (peano (0 + 1)) (encCtx ctx) (peano (0 + 1))
    (encCtx ctx) (encToks (.lpar :: rest))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx)
    (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest))) h_at_lp
  have hstep2' : oneStep pLF
      (apK (S Z) (encCtx ctx) (at' (S Z) (encCtx ctx) (encToks (.lpar :: rest))))
      = some (apK (S Z) (encCtx ctx)
        (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest)))) := by
    simpa only [peano] using hstep2
  have h_tm : oneStep pLF (tm Z (encCtx ctx) (encToks rest)) = some (PErr (con0 "no-fuel")) := by
    simp only [os_tm_z]
  have h_atLPk_tm := hcong_atLPk_tm Z (encCtx ctx) Z (encCtx ctx) (encToks rest)
    (isnormal_peano 0) (isnormal_encCtx ctx) (PErr (con0 "no-fuel")) h_tm
  have hstep3 := hcong_apK_atLPk (peano (0 + 1)) (encCtx ctx) Z (encCtx ctx)
    (tm Z (encCtx ctx) (encToks rest))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx)
    (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel"))) h_atLPk_tm
  have hstep3' : oneStep pLF
      (apK (S Z) (encCtx ctx)
        (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest))))
      = some (apK (S Z) (encCtx ctx) (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel")))) := by
    simpa only [peano] using hstep3
  have h_atLPk_err :
      oneStep pLF (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel")))
        = some (PErr (con0 "paren-malformed")) := by
    simp only [os_atLPk_err]
  have hstep4 := hcong_apK_atLPk (peano (0 + 1)) (encCtx ctx) Z (encCtx ctx)
    (PErr (con0 "no-fuel"))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx)
    (PErr (con0 "paren-malformed")) h_atLPk_err
  have hstep4' : oneStep pLF
      (apK (S Z) (encCtx ctx) (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel"))))
      = some (apK (S Z) (encCtx ctx) (PErr (con0 "paren-malformed"))) := by
    simpa only [peano] using hstep4
  simp only [peano, eval, os_ap_s, hstep2', hstep3', hstep4', os_apK_err]

theorem app_lpar_no_fuel_matches (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParse (LF.pApp ((0 + 1) + 1) ctx (.lpar :: rest))
      (eval pLF N (ap (peano ((0 + 1) + 1)) (encCtx ctx) (encToks (.lpar :: rest)))) := by
  refine ⟨5, ?_⟩
  rw [app_lpar_no_fuel_sim, pApp_fail_lpar_no_fuel]
  exact matches_parse_none (con0 "paren-malformed")

theorem app_lpar_no_fuel_raw_matches (ctx : List String) (rest : List LF.Tok) :
    ∃ N, MatchesParseRaw (LF.pApp ((0 + 1) + 1) ctx (.lpar :: rest))
      (eval pLF N (ap (peano ((0 + 1) + 1)) (encCtx ctx) (encToks (.lpar :: rest)))) := by
  obtain ⟨N, hN⟩ := app_lpar_no_fuel_matches ctx rest
  exact ⟨N, matches_parse_to_raw hN⟩

theorem appmore_zero_sim (ctx : List String) (acc : LF.Term) (toks : List LF.Tok) :
    eval pLF 1 (apm Z (encCtx ctx) (encTerm acc) (encToks toks))
      = Pp (encTerm acc) (encToks toks) := by
  simp only [eval, os_apm_z]

theorem appmore_zero_matches (ctx : List String) (acc : LF.Term) (toks : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore 0 ctx acc toks))
      (eval pLF N (apm Z (encCtx ctx) (encTerm acc) (encToks toks))) := by
  refine ⟨1, ?_⟩
  rw [appmore_zero_sim]
  exact matches_parse_some acc toks

theorem appmore_zero_raw_matches (ctx : List String) (acc : LF.Term) (toks : List LF.Tok)
    (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore 0 ctx acc toks))
      (eval pLF N (apm Z (encCtx ctx) accAst (encToks toks))) := by
  refine ⟨1, ?_⟩
  simp only [LF.pAppMore, eval, os_apm_z]
  exact matches_parse_raw_some_of_reduces toks hacc

theorem appmore_zero_first_raw (ctx : List String) (acc : LF.Term) (toks : List LF.Tok)
    (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    FirstMatchesParseRaw (some (LF.pAppMore 0 ctx acc toks))
      (apm Z (encCtx ctx) accAst (encToks toks)) := by
  have hstep : eval pLF 1 (apm Z (encCtx ctx) accAst (encToks toks))
      = Pp accAst (encToks toks) := by
    simp only [eval, os_apm_z]
  exact first_matches_one hstep
    (matches_parse_raw_some_of_reduces toks hacc)
    (not_result_apm Z (encCtx ctx) accAst (encToks toks))

theorem appmore_zero_first_active (ctx : List String) (acc : LF.Term) (toks : List LF.Tok)
    (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    FirstActiveMatchesParseRaw (some (LF.pAppMore 0 ctx acc toks))
      (apm Z (encCtx ctx) accAst (encToks toks)) := by
  have hstep : eval pLF 1 (apm Z (encCtx ctx) accAst (encToks toks))
      = Pp accAst (encToks toks) := by
    simp only [eval, os_apm_z]
  exact first_active_one hstep
    (matches_parse_raw_some_of_reduces toks hacc)
    (ParserActiveShape.apm Z (encCtx ctx) accAst (encToks toks))

theorem pAppMore_stop_no_fuel (ctx : List String) (acc : LF.Term) (toks : List LF.Tok) :
    LF.pAppMore (0 + 1) ctx acc toks = (acc, toks) := by
  rfl

theorem apmK_normalize_acc (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (accAst g c t : AST)
    (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, eval pLF N (apmK (peano fuel) (encCtx ctx) accAst (encToks toks) (at' g c t))
      = apmK (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks) (at' g c t) := by
  rcases hacc with ⟨N, hN⟩
  exact cong_eval (fun s => apmK (peano fuel) (encCtx ctx) s (encToks toks) (at' g c t))
    (hcong_apmK_acc_at (peano fuel) (encCtx ctx) (encToks toks) g c t
      (isnormal_peano fuel) (isnormal_encCtx ctx))
    N hN (isnormal_encTerm acc)

theorem appmore_stopK_of_atom_error (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (e : AST)
    (hat : oneStep pLF (at' (peano fuel) (encCtx ctx) (encToks toks)) = some (PErr e)) :
    eval pLF 2 (apmK (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)))
      = Pp (encTerm acc) (encToks toks) := by
  have hstep := hcong_apmK_at (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks)
    (peano fuel) (encCtx ctx) (encToks toks)
    (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_encTerm acc) (isnormal_encToks toks)
    (PErr e) hat
  simp only [eval, hstep, os_apmK_err]

theorem appmore_stop_of_atom_error_raw (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (accAst e : AST)
    (hacc : ReducesToEncTerm accAst acc)
    (hat : oneStep pLF (at' (peano fuel) (encCtx ctx) (encToks toks)) = some (PErr e))
    (hparse : LF.pAppMore (fuel + 1) ctx acc toks = (acc, toks)) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks))) := by
  obtain ⟨Macc, hMacc⟩ := apmK_normalize_acc fuel ctx acc toks accAst
    (peano fuel) (encCtx ctx) (encToks toks) hacc
  have hstep : eval pLF 1 (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks))
      = apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
          (at' (peano fuel) (encCtx ctx) (encToks toks)) := by
    simp only [peano, eval, os_apm_s]
  have hstop := appmore_stopK_of_atom_error fuel ctx acc toks e hat
  have htail := eval_trans pLF Macc 2 _ _ _ hMacc hstop
  refine ⟨1 + (Macc + 2), ?_⟩
  have htotal := eval_trans pLF 1 (Macc + 2) _ _ _ hstep htail
  rw [htotal, hparse]
  exact matches_parse_raw_some acc toks

theorem apmK_matches_raw_of_atom_result (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc)
    {v : AST} (h : MatchesParseRaw (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        ∃ N, MatchesParseRaw (some (LF.pAppMore fuel ctx (.app acc a) rest))
          (eval pLF N (apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest)))) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (eval pLF N (apmK (peano fuel) (encCtx ctx) accAst (encToks toks) v)) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = (acc, toks) by simp [LF.pAppMore, hatom]]
      simp only [eval, os_apmK_err]
      exact matches_parse_raw_some_of_reduces toks hacc
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      obtain ⟨Ntail, htail⟩ := tail a rest u hatom hu
      have hstep : eval pLF 1 (apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
            (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest) := by
        simp only [eval, os_apmK_p]
      have htotal := eval_trans pLF 1 Ntail _ _ _ hstep rfl
      refine ⟨1 + Ntail, ?_⟩
      rw [htotal]
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = LF.pAppMore fuel ctx (.app acc a) rest by
        simp [LF.pAppMore, hatom]]
      exact htail

theorem apmK_matches_first_raw_of_atom_result (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc)
    {v : AST} (h : MatchesParseRaw (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        FirstMatchesParseRaw (some (LF.pAppMore fuel ctx (.app acc a) rest))
          (apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest))) :
    FirstMatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apmK (peano fuel) (encCtx ctx) accAst (encToks toks) v) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = (acc, toks) by
        simp [LF.pAppMore, hatom]]
      exact first_matches_one (by simp only [eval, os_apmK_err])
        (matches_parse_raw_some_of_reduces toks hacc)
        (not_result_apmK (peano fuel) (encCtx ctx) accAst (encToks toks) (PErr e))
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      have hstep : eval pLF 1 (apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
            (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest) := by
        simp only [eval, os_apmK_p]
      obtain htail := tail a rest u hatom hu
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = LF.pAppMore fuel ctx (.app acc a) rest by
        simp [LF.pAppMore, hatom]]
      exact first_matches_prepend hstep
        (not_result_apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
          (Pp u (encToks rest))) htail

theorem apmK_matches_first_active_of_atom_result (fuel : Nat) (ctx : List String)
    (acc : LF.Term) (toks : List LF.Tok) (accAst : AST)
    (hacc : ReducesToEncTerm accAst acc)
    {v : AST} (h : MatchesParseRaw (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        FirstActiveMatchesParseRaw (some (LF.pAppMore fuel ctx (.app acc a) rest))
          (apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest))) :
    FirstActiveMatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apmK (peano fuel) (encCtx ctx) accAst (encToks toks) v) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = (acc, toks) by
        simp [LF.pAppMore, hatom]]
      exact first_active_one (by simp only [eval, os_apmK_err])
        (matches_parse_raw_some_of_reduces toks hacc)
        (ParserActiveShape.apmK (peano fuel) (encCtx ctx) accAst (encToks toks) (PErr e))
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      have hstep : eval pLF 1 (apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
            (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest) := by
        simp only [eval, os_apmK_p]
      obtain htail := tail a rest u hatom hu
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = LF.pAppMore fuel ctx (.app acc a) rest by
        simp [LF.pAppMore, hatom]]
      exact first_active_prepend hstep
        (ParserActiveShape.apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
          (Pp u (encToks rest))) htail

theorem appmore_succ_first_active_of_atom_appmore (fuel : Nat) (ctx : List String)
    (acc : LF.Term) (toks : List LF.Tok) (accAst : AST)
    (hacc : ReducesToEncTerm accAst acc)
    (hatom : FirstActiveMatchesParseRaw (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)))
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ReducesToEncTerm u a →
        FirstActiveMatchesParseRaw (some (LF.pAppMore fuel ctx (.app acc a) rest))
          (apm (peano fuel) (encCtx ctx) (App (encTerm acc) u) (encToks rest))) :
    FirstActiveMatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks)) := by
  let child := at' (peano fuel) (encCtx ctx) (encToks toks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.atom (peano fuel) (encCtx ctx) (encToks toks)
  rcases hacc with ⟨Nacc, hNacc⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => apmK (peano fuel) (encCtx ctx) a (encToks toks) child)
      (fun a => ParserActiveShape.apmK (peano fuel) (encCtx ctx) a (encToks toks) child)
      (hcong_apmK_acc_at (peano fuel) (encCtx ctx) (encToks toks)
        (peano fuel) (encCtx ctx) (encToks toks)
        (isnormal_peano fuel) (isnormal_encCtx ctx))
      Nacc hNacc
  have htail : FirstActiveMatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apmK (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks) child) :=
    first_active_bind_active
      (fun s => apmK (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks) s)
      (fun s _ => ParserActiveShape.apmK (peano fuel) (encCtx ctx)
        (encTerm acc) (encToks toks) s)
      (hcong_apmK_active (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks)
        (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_encTerm acc)
        (isnormal_encToks toks))
      hatom
      (fun {v} hv =>
        apmK_matches_first_active_of_atom_result fuel ctx acc toks (encTerm acc)
          (reduces_encTerm_refl acc) hv tail)
  have hafterNorm : FirstActiveMatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apmK (peano fuel) (encCtx ctx) accAst (encToks toks) child) :=
    first_active_prepend_eval hMnorm hNormGuard htail
  have hstep : eval pLF 1 (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks))
      = apmK (peano fuel) (encCtx ctx) accAst (encToks toks) child := by
    unfold child
    simp only [peano, eval, os_apm_s]
  exact first_active_prepend hstep
    (ParserActiveShape.apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks))
    hafterNorm

theorem apmK_matches_first_active_shiftable_of_atom_result (fuel : Nat)
    (ctx : List String) (acc : LF.Term) (toks : List LF.Tok) (accAst : AST)
    (hacc : ShiftablePayload accAst acc)
    {v : AST} (h : MatchesParseShiftable (LF.pAtom fuel ctx toks) v)
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ShiftablePayload u a →
        FirstActiveMatchesParseShiftable (some (LF.pAppMore fuel ctx (.app acc a) rest))
          (apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest))) :
    FirstActiveMatchesParseShiftable (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apmK (peano fuel) (encCtx ctx) accAst (encToks toks) v) := by
  cases hatom : LF.pAtom fuel ctx toks with
  | none =>
      rw [hatom] at h
      rcases h with ⟨e, rfl⟩
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = (acc, toks) by
        simp [LF.pAppMore, hatom]]
      exact first_active_shiftable_one (by simp only [eval, os_apmK_err])
        (matches_parse_shiftable_some_of_payload hacc)
        (ParserActiveShape.apmK (peano fuel) (encCtx ctx) accAst (encToks toks) (PErr e))
  | some pr =>
      rcases pr with ⟨a, rest⟩
      rw [hatom] at h
      rcases h with ⟨u, rfl, hu⟩
      have hstep : eval pLF 1 (apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
            (Pp u (encToks rest)))
          = apm (peano fuel) (encCtx ctx) (App accAst u) (encToks rest) := by
        simp only [eval, os_apmK_p]
      obtain htail := tail a rest u hatom hu
      rw [show LF.pAppMore (fuel + 1) ctx acc toks = LF.pAppMore fuel ctx (.app acc a) rest by
        simp [LF.pAppMore, hatom]]
      exact first_active_shiftable_prepend hstep
        (ParserActiveShape.apmK (peano fuel) (encCtx ctx) accAst (encToks toks)
          (Pp u (encToks rest))) htail

theorem appmore_succ_first_active_shiftable_of_atom_appmore (fuel : Nat)
    (ctx : List String) (acc : LF.Term) (toks : List LF.Tok) (accAst : AST)
    (hacc : ShiftablePayload accAst acc)
    (hatom : FirstActiveMatchesParseShiftable (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)))
    (tail : ∀ (a : LF.Term) (rest : List LF.Tok) (u : AST),
      LF.pAtom fuel ctx toks = some (a, rest) → ShiftablePayload u a →
        FirstActiveMatchesParseShiftable (some (LF.pAppMore fuel ctx (.app acc a) rest))
          (apm (peano fuel) (encCtx ctx) (App (encTerm acc) u) (encToks rest))) :
    FirstActiveMatchesParseShiftable (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks)) := by
  let child := at' (peano fuel) (encCtx ctx) (encToks toks)
  have hchildActive : ParserActiveShape child :=
    ParserActiveShape.atom (peano fuel) (encCtx ctx) (encToks toks)
  rcases hacc.reduces with ⟨Nacc, hNacc⟩
  obtain ⟨Mnorm, hMnorm, hNormGuard⟩ :=
    cong_eval_with_active_wrapper
      (fun a => apmK (peano fuel) (encCtx ctx) a (encToks toks) child)
      (fun a => ParserActiveShape.apmK (peano fuel) (encCtx ctx) a (encToks toks) child)
      (hcong_apmK_acc_at (peano fuel) (encCtx ctx) (encToks toks)
        (peano fuel) (encCtx ctx) (encToks toks)
        (isnormal_peano fuel) (isnormal_encCtx ctx))
      Nacc hNacc
  have htail : FirstActiveMatchesParseShiftable (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apmK (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks) child) :=
    first_active_shiftable_bind_active
      (fun s => apmK (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks) s)
      (fun s _ => ParserActiveShape.apmK (peano fuel) (encCtx ctx)
        (encTerm acc) (encToks toks) s)
      (hcong_apmK_active (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks)
        (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_encTerm acc)
        (isnormal_encToks toks))
      hatom
      (fun {v} hv =>
        apmK_matches_first_active_shiftable_of_atom_result fuel ctx acc toks (encTerm acc)
          (shiftable_encTerm acc) hv tail)
  have hafterNorm : FirstActiveMatchesParseShiftable (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apmK (peano fuel) (encCtx ctx) accAst (encToks toks) child) :=
    first_active_shiftable_prepend_eval hMnorm hNormGuard htail
  have hstep : eval pLF 1 (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks))
      = apmK (peano fuel) (encCtx ctx) accAst (encToks toks) child := by
    unfold child
    simp only [peano, eval, os_apm_s]
  exact first_active_shiftable_prepend hstep
    (ParserActiveShape.apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks))
    hafterNorm

theorem appmore_stop_no_fuel_raw_matches (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (0 + 1) ctx acc toks))
      (eval pLF N (apm (peano (0 + 1)) (encCtx ctx) accAst (encToks toks))) :=
  appmore_stop_of_atom_error_raw 0 ctx acc toks accAst (con0 "no-fuel") hacc
    (by simp only [peano, os_at_z]) (pAppMore_stop_no_fuel ctx acc toks)

theorem appmore_one_matches (ctx : List String) (acc : LF.Term) (toks : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore (0 + 1) ctx acc toks))
      (eval pLF N (apm (peano (0 + 1)) (encCtx ctx) (encTerm acc) (encToks toks))) := by
  obtain ⟨N, hN⟩ := appmore_stop_no_fuel_raw_matches ctx acc toks (encTerm acc)
    (reduces_encTerm_refl acc)
  exact matches_parse_exact_of_raw_eval hN

theorem pAppMore_stop_lpar_no_fuel (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    LF.pAppMore ((0 + 1) + 1) ctx acc (.lpar :: rest) = (acc, .lpar :: rest) := by
  rfl

theorem appmore_stop_lpar_no_fuel_sim (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    eval pLF 5 (apm (peano ((0 + 1) + 1)) (encCtx ctx) (encTerm acc)
      (encToks (.lpar :: rest)))
      = Pp (encTerm acc) (encToks (.lpar :: rest)) := by
  have h_at_lp : oneStep pLF
      (at' (peano (0 + 1)) (encCtx ctx) (encToks (.lpar :: rest)))
      = some (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest))) := by
    simp only [peano, encToks, encTok, os_at_lp]
  have hstep2 := hcong_apmK_at (peano (0 + 1)) (encCtx ctx) (encTerm acc)
    (encToks (.lpar :: rest)) (peano (0 + 1)) (encCtx ctx) (encToks (.lpar :: rest))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_encTerm acc)
    (isnormal_encToks (.lpar :: rest))
    (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest))) h_at_lp
  have hstep2' : oneStep pLF
      (apmK (S Z) (encCtx ctx) (encTerm acc) (encToks (.lpar :: rest))
        (at' (S Z) (encCtx ctx) (encToks (.lpar :: rest))))
      = some (apmK (S Z) (encCtx ctx) (encTerm acc) (encToks (.lpar :: rest))
        (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest)))) := by
    simpa only [peano] using hstep2
  have h_tm : oneStep pLF (tm Z (encCtx ctx) (encToks rest)) = some (PErr (con0 "no-fuel")) := by
    simp only [os_tm_z]
  have h_atLPk_tm := hcong_atLPk_tm Z (encCtx ctx) Z (encCtx ctx) (encToks rest)
    (isnormal_peano 0) (isnormal_encCtx ctx) (PErr (con0 "no-fuel")) h_tm
  have hstep3 := hcong_apmK_atLPk (peano (0 + 1)) (encCtx ctx) (encTerm acc)
    (encToks (.lpar :: rest)) Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_encTerm acc)
    (isnormal_encToks (.lpar :: rest))
    (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel"))) h_atLPk_tm
  have hstep3' : oneStep pLF
      (apmK (S Z) (encCtx ctx) (encTerm acc) (encToks (.lpar :: rest))
        (atLPk Z (encCtx ctx) (tm Z (encCtx ctx) (encToks rest))))
      = some (apmK (S Z) (encCtx ctx) (encTerm acc) (encToks (.lpar :: rest))
        (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel")))) := by
    simpa only [peano] using hstep3
  have h_atLPk_err :
      oneStep pLF (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel")))
        = some (PErr (con0 "paren-malformed")) := by
    simp only [os_atLPk_err]
  have hstep4 := hcong_apmK_atLPk (peano (0 + 1)) (encCtx ctx) (encTerm acc)
    (encToks (.lpar :: rest)) Z (encCtx ctx) (PErr (con0 "no-fuel"))
    (isnormal_peano (0 + 1)) (isnormal_encCtx ctx) (isnormal_encTerm acc)
    (isnormal_encToks (.lpar :: rest))
    (PErr (con0 "paren-malformed")) h_atLPk_err
  have hstep4' : oneStep pLF
      (apmK (S Z) (encCtx ctx) (encTerm acc) (encToks (.lpar :: rest))
        (atLPk Z (encCtx ctx) (PErr (con0 "no-fuel"))))
      = some (apmK (S Z) (encCtx ctx) (encTerm acc) (encToks (.lpar :: rest))
        (PErr (con0 "paren-malformed"))) := by
    simpa only [peano] using hstep4
  simp only [peano, eval, os_apm_s, hstep2', hstep3', hstep4', os_apmK_err]

theorem appmore_stop_lpar_no_fuel_matches (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore ((0 + 1) + 1) ctx acc (.lpar :: rest)))
      (eval pLF N (apm (peano ((0 + 1) + 1)) (encCtx ctx) (encTerm acc)
        (encToks (.lpar :: rest)))) := by
  refine ⟨5, ?_⟩
  rw [appmore_stop_lpar_no_fuel_sim, pAppMore_stop_lpar_no_fuel]
  exact matches_parse_some acc (.lpar :: rest)

theorem appmore_type_headK (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) :
    eval pLF 2 (apmK (peano (fuel + 1)) (encCtx ctx) (encTerm acc)
      (encToks (.type :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))))
      = apm (peano (fuel + 1)) (encCtx ctx)
          (App (encTerm acc) (Srt (con0 "type"))) (encToks rest) := by
  have hstep := hcong_apmK_at (peano (fuel + 1)) (encCtx ctx) (encTerm acc)
    (encToks (.type :: rest)) (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))
    (isnormal_peano (fuel + 1)) (isnormal_encCtx ctx) (isnormal_encTerm acc)
    (isnormal_encToks (.type :: rest)) (Pp (Srt (con0 "type")) (encToks rest))
    (by simp only [peano, encToks, encTok, os_at_type])
  simp only [eval, hstep, os_apmK_p]

theorem appmore_type_head_raw (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc)
    (tail : ∃ N, MatchesParseRaw
      (some (LF.pAppMore (fuel + 1) ctx (.app acc (.srt .type)) rest))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx)
        (App (encTerm acc) (Srt (con0 "type"))) (encToks rest)))) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore ((fuel + 1) + 1) ctx acc (.type :: rest)))
      (eval pLF N (apm (peano ((fuel + 1) + 1)) (encCtx ctx) accAst
        (encToks (.type :: rest)))) := by
  obtain ⟨Macc, hMacc⟩ := apmK_normalize_acc (fuel + 1) ctx acc (.type :: rest) accAst
    (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest)) hacc
  obtain ⟨Ntail, htail⟩ := tail
  have hstep : eval pLF 1 (apm (peano ((fuel + 1) + 1)) (encCtx ctx) accAst
      (encToks (.type :: rest)))
      = apmK (peano (fuel + 1)) (encCtx ctx) accAst (encToks (.type :: rest))
          (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.type :: rest))) := by
    simp only [peano, eval, os_apm_s]
  have hhead := appmore_type_headK fuel ctx acc rest
  have htail0 := eval_trans pLF Macc 2 _ _ _ hMacc hhead
  have hpre := eval_trans pLF 1 (Macc + 2) _ _ _ hstep htail0
  refine ⟨(1 + (Macc + 2)) + Ntail, ?_⟩
  have htotal := eval_trans pLF (1 + (Macc + 2)) Ntail _ _ _ hpre rfl
  rw [htotal]
  change MatchesParseRaw
    (some (LF.pAppMore (fuel + 1) ctx (.app acc (.srt .type)) rest))
    (eval pLF Ntail (apm (peano (fuel + 1)) (encCtx ctx)
      (App (encTerm acc) (Srt (con0 "type"))) (encToks rest)))
  exact htail

theorem appmore_id_headK (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (s : String) (rest : List LF.Tok) :
    eval pLF 2 (apmK (peano (fuel + 1)) (encCtx ctx) (encTerm acc)
      (encToks (.id s :: rest))
      (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))))
      = apm (peano (fuel + 1)) (encCtx ctx)
          (App (encTerm acc) (resolve (encCtx ctx) (con0 s))) (encToks rest) := by
  have hstep := hcong_apmK_at (peano (fuel + 1)) (encCtx ctx) (encTerm acc)
    (encToks (.id s :: rest)) (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))
    (isnormal_peano (fuel + 1)) (isnormal_encCtx ctx) (isnormal_encTerm acc)
    (isnormal_encToks (.id s :: rest))
    (Pp (resolve (encCtx ctx) (con0 s)) (encToks rest))
    (by simp only [peano, encToks, encTok, os_at_id])
  simp only [eval, hstep, os_apmK_p]

theorem appmore_id_head_raw (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (s : String) (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc)
    (tail : ∃ N, MatchesParseRaw
      (some (LF.pAppMore (fuel + 1) ctx (.app acc (LF.resolve ctx s)) rest))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx)
        (App (encTerm acc) (resolve (encCtx ctx) (con0 s))) (encToks rest)))) :
    ∃ N, MatchesParseRaw
      (some (LF.pAppMore ((fuel + 1) + 1) ctx acc (.id s :: rest)))
      (eval pLF N (apm (peano ((fuel + 1) + 1)) (encCtx ctx) accAst
        (encToks (.id s :: rest)))) := by
  obtain ⟨Macc, hMacc⟩ := apmK_normalize_acc (fuel + 1) ctx acc (.id s :: rest) accAst
    (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest)) hacc
  obtain ⟨Ntail, htail⟩ := tail
  have hstep : eval pLF 1 (apm (peano ((fuel + 1) + 1)) (encCtx ctx) accAst
      (encToks (.id s :: rest)))
      = apmK (peano (fuel + 1)) (encCtx ctx) accAst (encToks (.id s :: rest))
          (at' (peano (fuel + 1)) (encCtx ctx) (encToks (.id s :: rest))) := by
    simp only [peano, eval, os_apm_s]
  have hhead := appmore_id_headK fuel ctx acc s rest
  have htail0 := eval_trans pLF Macc 2 _ _ _ hMacc hhead
  have hpre := eval_trans pLF 1 (Macc + 2) _ _ _ hstep htail0
  refine ⟨(1 + (Macc + 2)) + Ntail, ?_⟩
  have htotal := eval_trans pLF (1 + (Macc + 2)) Ntail _ _ _ hpre rfl
  rw [htotal]
  change MatchesParseRaw
    (some (LF.pAppMore (fuel + 1) ctx (.app acc (LF.resolve ctx s)) rest))
    (eval pLF Ntail (apm (peano (fuel + 1)) (encCtx ctx)
      (App (encTerm acc) (resolve (encCtx ctx) (con0 s))) (encToks rest)))
  exact htail

theorem appmore_stop_of_atom_error (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (e : AST)
    (hat : oneStep pLF (at' (peano fuel) (encCtx ctx) (encToks toks)) = some (PErr e)) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks toks))
      = Pp (encTerm acc) (encToks toks) := by
  have hstep2 := hcong_apmK_at (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks)
    (peano fuel) (encCtx ctx) (encToks toks)
    (isnormal_peano fuel) (isnormal_encCtx ctx) (isnormal_encTerm acc) (isnormal_encToks toks)
    (PErr e) hat
  simp only [peano, eval, os_apm_s, hstep2, os_apmK_err]

theorem appmore_stop_empty_sim (fuel : Nat) (ctx : List String) (acc : LF.Term) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks []))
      = Pp (encTerm acc) (encToks []) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error 0 ctx acc [] (con0 "no-fuel") (by simp only [peano, encToks, os_at_z])
  | succ fuel =>
      exact appmore_stop_of_atom_error (fuel + 1) ctx acc [] (con0 "atom-expected")
        (by simp only [peano, encToks, os_at_err_nil])

theorem pAppMore_stop_empty (fuel : Nat) (ctx : List String) (acc : LF.Term) :
    LF.pAppMore (fuel + 1) ctx acc [] = (acc, []) := by
  cases fuel <;> rfl

theorem appmore_stop_empty_matches (fuel : Nat) (ctx : List String) (acc : LF.Term) :
    ∃ N, MatchesParse (some (LF.pAppMore (fuel + 1) ctx acc []))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks []))) := by
  refine ⟨3, ?_⟩
  rw [appmore_stop_empty_sim, pAppMore_stop_empty]
  exact matches_parse_some acc []

theorem appmore_stop_empty_raw_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc []))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks []))) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error_raw 0 ctx acc [] accAst (con0 "no-fuel") hacc
        (by simp only [peano, encToks, os_at_z]) (pAppMore_stop_empty 0 ctx acc)
  | succ fuel =>
      exact appmore_stop_of_atom_error_raw (fuel + 1) ctx acc [] accAst (con0 "atom-expected") hacc
        (by simp only [peano, encToks, os_at_err_nil]) (pAppMore_stop_empty (fuel + 1) ctx acc)

theorem appmore_stop_pi_sim (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.pi :: rest)))
      = Pp (encTerm acc) (encToks (.pi :: rest)) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error 0 ctx acc (.pi :: rest) (con0 "no-fuel")
        (by simp only [peano, encToks, encTok, os_at_z])
  | succ fuel =>
      exact appmore_stop_of_atom_error (fuel + 1) ctx acc (.pi :: rest) (con0 "atom-expected")
        (by simp only [peano, encToks, encTok, os_at_err_pi])

theorem pAppMore_stop_pi (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    LF.pAppMore (fuel + 1) ctx acc (.pi :: rest) = (acc, .pi :: rest) := by
  cases fuel <;> rfl

theorem appmore_stop_pi_matches (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore (fuel + 1) ctx acc (.pi :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.pi :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [appmore_stop_pi_sim, pAppMore_stop_pi]
  exact matches_parse_some acc (.pi :: rest)

theorem appmore_stop_pi_raw_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc (.pi :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks (.pi :: rest)))) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error_raw 0 ctx acc (.pi :: rest) accAst (con0 "no-fuel") hacc
        (by simp only [peano, encToks, encTok, os_at_z]) (pAppMore_stop_pi 0 ctx acc rest)
  | succ fuel =>
      exact appmore_stop_of_atom_error_raw (fuel + 1) ctx acc (.pi :: rest) accAst
        (con0 "atom-expected") hacc
        (by simp only [peano, encToks, encTok, os_at_err_pi])
        (pAppMore_stop_pi (fuel + 1) ctx acc rest)

theorem appmore_stop_lam_sim (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.lam :: rest)))
      = Pp (encTerm acc) (encToks (.lam :: rest)) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error 0 ctx acc (.lam :: rest) (con0 "no-fuel")
        (by simp only [peano, encToks, encTok, os_at_z])
  | succ fuel =>
      exact appmore_stop_of_atom_error (fuel + 1) ctx acc (.lam :: rest) (con0 "atom-expected")
        (by simp only [peano, encToks, encTok, os_at_err_lam])

theorem pAppMore_stop_lam (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    LF.pAppMore (fuel + 1) ctx acc (.lam :: rest) = (acc, .lam :: rest) := by
  cases fuel <;> rfl

theorem appmore_stop_lam_matches (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore (fuel + 1) ctx acc (.lam :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.lam :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [appmore_stop_lam_sim, pAppMore_stop_lam]
  exact matches_parse_some acc (.lam :: rest)

theorem appmore_stop_lam_raw_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc (.lam :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks (.lam :: rest)))) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error_raw 0 ctx acc (.lam :: rest) accAst (con0 "no-fuel") hacc
        (by simp only [peano, encToks, encTok, os_at_z]) (pAppMore_stop_lam 0 ctx acc rest)
  | succ fuel =>
      exact appmore_stop_of_atom_error_raw (fuel + 1) ctx acc (.lam :: rest) accAst
        (con0 "atom-expected") hacc
        (by simp only [peano, encToks, encTok, os_at_err_lam])
        (pAppMore_stop_lam (fuel + 1) ctx acc rest)

theorem appmore_stop_arr_sim (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.arr :: rest)))
      = Pp (encTerm acc) (encToks (.arr :: rest)) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error 0 ctx acc (.arr :: rest) (con0 "no-fuel")
        (by simp only [peano, encToks, encTok, os_at_z])
  | succ fuel =>
      exact appmore_stop_of_atom_error (fuel + 1) ctx acc (.arr :: rest) (con0 "atom-expected")
        (by simp only [peano, encToks, encTok, os_at_err_arr])

theorem pAppMore_stop_arr (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    LF.pAppMore (fuel + 1) ctx acc (.arr :: rest) = (acc, .arr :: rest) := by
  cases fuel <;> rfl

theorem appmore_stop_arr_matches (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore (fuel + 1) ctx acc (.arr :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.arr :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [appmore_stop_arr_sim, pAppMore_stop_arr]
  exact matches_parse_some acc (.arr :: rest)

theorem appmore_stop_arr_raw_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc (.arr :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks (.arr :: rest)))) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error_raw 0 ctx acc (.arr :: rest) accAst (con0 "no-fuel") hacc
        (by simp only [peano, encToks, encTok, os_at_z]) (pAppMore_stop_arr 0 ctx acc rest)
  | succ fuel =>
      exact appmore_stop_of_atom_error_raw (fuel + 1) ctx acc (.arr :: rest) accAst
        (con0 "atom-expected") hacc
        (by simp only [peano, encToks, encTok, os_at_err_arr])
        (pAppMore_stop_arr (fuel + 1) ctx acc rest)

theorem appmore_stop_colon_sim (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.colon :: rest)))
      = Pp (encTerm acc) (encToks (.colon :: rest)) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error 0 ctx acc (.colon :: rest) (con0 "no-fuel")
        (by simp only [peano, encToks, encTok, os_at_z])
  | succ fuel =>
      exact appmore_stop_of_atom_error (fuel + 1) ctx acc (.colon :: rest) (con0 "atom-expected")
        (by simp only [peano, encToks, encTok, os_at_err_colon])

theorem pAppMore_stop_colon (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) :
    LF.pAppMore (fuel + 1) ctx acc (.colon :: rest) = (acc, .colon :: rest) := by
  cases fuel <;> rfl

theorem appmore_stop_colon_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore (fuel + 1) ctx acc (.colon :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc)
        (encToks (.colon :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [appmore_stop_colon_sim, pAppMore_stop_colon]
  exact matches_parse_some acc (.colon :: rest)

theorem appmore_stop_colon_raw_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc (.colon :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst
        (encToks (.colon :: rest)))) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error_raw 0 ctx acc (.colon :: rest) accAst (con0 "no-fuel") hacc
        (by simp only [peano, encToks, encTok, os_at_z]) (pAppMore_stop_colon 0 ctx acc rest)
  | succ fuel =>
      exact appmore_stop_of_atom_error_raw (fuel + 1) ctx acc (.colon :: rest) accAst
        (con0 "atom-expected") hacc
        (by simp only [peano, encToks, encTok, os_at_err_colon])
        (pAppMore_stop_colon (fuel + 1) ctx acc rest)

theorem appmore_stop_dot_sim (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.dot :: rest)))
      = Pp (encTerm acc) (encToks (.dot :: rest)) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error 0 ctx acc (.dot :: rest) (con0 "no-fuel")
        (by simp only [peano, encToks, encTok, os_at_z])
  | succ fuel =>
      exact appmore_stop_of_atom_error (fuel + 1) ctx acc (.dot :: rest) (con0 "atom-expected")
        (by simp only [peano, encToks, encTok, os_at_err_dot])

theorem pAppMore_stop_dot (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    LF.pAppMore (fuel + 1) ctx acc (.dot :: rest) = (acc, .dot :: rest) := by
  cases fuel <;> rfl

theorem appmore_stop_dot_matches (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore (fuel + 1) ctx acc (.dot :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.dot :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [appmore_stop_dot_sim, pAppMore_stop_dot]
  exact matches_parse_some acc (.dot :: rest)

theorem appmore_stop_dot_raw_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc (.dot :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks (.dot :: rest)))) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error_raw 0 ctx acc (.dot :: rest) accAst (con0 "no-fuel") hacc
        (by simp only [peano, encToks, encTok, os_at_z]) (pAppMore_stop_dot 0 ctx acc rest)
  | succ fuel =>
      exact appmore_stop_of_atom_error_raw (fuel + 1) ctx acc (.dot :: rest) accAst
        (con0 "atom-expected") hacc
        (by simp only [peano, encToks, encTok, os_at_err_dot])
        (pAppMore_stop_dot (fuel + 1) ctx acc rest)

theorem appmore_stop_rpar_sim (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    eval pLF 3 (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.rpar :: rest)))
      = Pp (encTerm acc) (encToks (.rpar :: rest)) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error 0 ctx acc (.rpar :: rest) (con0 "no-fuel")
        (by simp only [peano, encToks, encTok, os_at_z])
  | succ fuel =>
      exact appmore_stop_of_atom_error (fuel + 1) ctx acc (.rpar :: rest) (con0 "atom-expected")
        (by simp only [peano, encToks, encTok, os_at_err_rp])

theorem pAppMore_stop_rpar (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    LF.pAppMore (fuel + 1) ctx acc (.rpar :: rest) = (acc, .rpar :: rest) := by
  cases fuel <;> rfl

theorem appmore_stop_rpar_matches (fuel : Nat) (ctx : List String) (acc : LF.Term) (rest : List LF.Tok) :
    ∃ N, MatchesParse (some (LF.pAppMore (fuel + 1) ctx acc (.rpar :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) (encTerm acc) (encToks (.rpar :: rest)))) := by
  refine ⟨3, ?_⟩
  rw [appmore_stop_rpar_sim, pAppMore_stop_rpar]
  exact matches_parse_some acc (.rpar :: rest)

theorem appmore_stop_rpar_raw_matches (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (rest : List LF.Tok) (accAst : AST) (hacc : ReducesToEncTerm accAst acc) :
    ∃ N, MatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc (.rpar :: rest)))
      (eval pLF N (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks (.rpar :: rest)))) := by
  cases fuel with
  | zero =>
      exact appmore_stop_of_atom_error_raw 0 ctx acc (.rpar :: rest) accAst (con0 "no-fuel") hacc
        (by simp only [peano, encToks, encTok, os_at_z]) (pAppMore_stop_rpar 0 ctx acc rest)
  | succ fuel =>
      exact appmore_stop_of_atom_error_raw (fuel + 1) ctx acc (.rpar :: rest) accAst
        (con0 "atom-expected") hacc
        (by simp only [peano, encToks, encTok, os_at_err_rp])
        (pAppMore_stop_rpar (fuel + 1) ctx acc rest)

theorem appmore_raw_matches_no_lpar :
    ∀ (fuel : Nat) (ctx : List String) (acc : LF.Term) (toks : List LF.Tok)
      (accAst : AST), NoLPar toks → ReducesToEncTerm accAst acc →
        ∃ N, MatchesParseRaw (some (LF.pAppMore fuel ctx acc toks))
          (eval pLF N (apm (peano fuel) (encCtx ctx) accAst (encToks toks))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ctx acc toks accAst _ hacc
      exact appmore_zero_raw_matches ctx acc toks accAst hacc
  | succ fuel ih =>
      intro ctx acc toks accAst hno hacc
      cases fuel with
      | zero =>
          exact appmore_stop_no_fuel_raw_matches ctx acc toks accAst hacc
      | succ fuel =>
          cases toks with
          | nil =>
              exact appmore_stop_empty_raw_matches (fuel + 1) ctx acc accAst hacc
          | cons tok rest =>
              cases tok with
              | pi =>
                  exact appmore_stop_pi_raw_matches (fuel + 1) ctx acc rest accAst hacc
              | lam =>
                  exact appmore_stop_lam_raw_matches (fuel + 1) ctx acc rest accAst hacc
              | arr =>
                  exact appmore_stop_arr_raw_matches (fuel + 1) ctx acc rest accAst hacc
              | colon =>
                  exact appmore_stop_colon_raw_matches (fuel + 1) ctx acc rest accAst hacc
              | dot =>
                  exact appmore_stop_dot_raw_matches (fuel + 1) ctx acc rest accAst hacc
              | lpar =>
                  exact False.elim hno
              | rpar =>
                  exact appmore_stop_rpar_raw_matches (fuel + 1) ctx acc rest accAst hacc
              | type =>
                  have hrest : NoLPar rest := by
                    simpa [NoLPar] using hno
                  have htail := ih ctx (.app acc (.srt .type)) rest
                    (App (encTerm acc) (Srt (con0 "type"))) hrest
                    (reduces_encTerm_refl (.app acc (.srt .type)))
                  exact appmore_type_head_raw fuel ctx acc rest accAst hacc htail
              | id s =>
                  have hrest : NoLPar rest := by
                    simpa [NoLPar] using hno
                  have hres : ReducesToEncTerm (resolve (encCtx ctx) (con0 s)) (LF.resolve ctx s) :=
                    resolve_sim ctx s
                  have htail := ih ctx (.app acc (LF.resolve ctx s)) rest
                    (App (encTerm acc) (resolve (encCtx ctx) (con0 s))) hrest
                    (reduces_app (reduces_encTerm_refl acc) hres)
                  exact appmore_id_head_raw fuel ctx acc s rest accAst hacc htail

theorem appmore_matches_no_lpar (fuel : Nat) (ctx : List String) (acc : LF.Term)
    (toks : List LF.Tok) (hno : NoLPar toks) :
    ∃ N, MatchesParse (some (LF.pAppMore fuel ctx acc toks))
      (eval pLF N (apm (peano fuel) (encCtx ctx) (encTerm acc) (encToks toks))) := by
  obtain ⟨N, hN⟩ := appmore_raw_matches_no_lpar fuel ctx acc toks (encTerm acc) hno
    (reduces_encTerm_refl acc)
  exact matches_parse_exact_of_raw_eval hN

theorem app_raw_matches_no_lpar :
    ∀ (fuel : Nat) (ctx : List String) (toks : List LF.Tok), NoLPar toks →
      ∃ N, MatchesParseRaw (LF.pApp fuel ctx toks)
        (eval pLF N (ap (peano fuel) (encCtx ctx) (encToks toks))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ctx toks _
      exact app_no_fuel_raw_matches ctx toks
  | succ fuel _ =>
      intro ctx toks hno
      cases fuel with
      | zero =>
          exact app_fail_of_atom_error_raw 0 ctx toks (con0 "no-fuel")
            (by simp only [peano, os_at_z]) (pApp_fail_no_fuel ctx toks)
      | succ fuel =>
          cases toks with
          | nil =>
              exact app_fail_of_atom_error_raw (fuel + 1) ctx [] (con0 "atom-expected")
                (by simp only [peano, encToks, os_at_err_nil]) (pApp_fail_empty fuel ctx)
          | cons tok rest =>
              cases tok with
              | pi =>
                  exact app_fail_of_atom_error_raw (fuel + 1) ctx (.pi :: rest)
                    (con0 "atom-expected")
                    (by simp only [peano, encToks, encTok, os_at_err_pi])
                    (pApp_fail_pi fuel ctx rest)
              | lam =>
                  exact app_fail_of_atom_error_raw (fuel + 1) ctx (.lam :: rest)
                    (con0 "atom-expected")
                    (by simp only [peano, encToks, encTok, os_at_err_lam])
                    (pApp_fail_lam fuel ctx rest)
              | arr =>
                  exact app_fail_of_atom_error_raw (fuel + 1) ctx (.arr :: rest)
                    (con0 "atom-expected")
                    (by simp only [peano, encToks, encTok, os_at_err_arr])
                    (pApp_fail_arr fuel ctx rest)
              | colon =>
                  exact app_fail_of_atom_error_raw (fuel + 1) ctx (.colon :: rest)
                    (con0 "atom-expected")
                    (by simp only [peano, encToks, encTok, os_at_err_colon])
                    (pApp_fail_colon fuel ctx rest)
              | dot =>
                  exact app_fail_of_atom_error_raw (fuel + 1) ctx (.dot :: rest)
                    (con0 "atom-expected")
                    (by simp only [peano, encToks, encTok, os_at_err_dot])
                    (pApp_fail_dot fuel ctx rest)
              | lpar =>
                  exact False.elim hno
              | rpar =>
                  exact app_fail_of_atom_error_raw (fuel + 1) ctx (.rpar :: rest)
                    (con0 "atom-expected")
                    (by simp only [peano, encToks, encTok, os_at_err_rp])
                    (pApp_fail_rpar fuel ctx rest)
              | type =>
                  have hrest : NoLPar rest := by
                    simpa [NoLPar] using hno
                  have htail := appmore_raw_matches_no_lpar (fuel + 1) ctx (.srt .type) rest
                    (Srt (con0 "type")) hrest (reduces_encTerm_refl (.srt .type))
                  exact app_success_type_raw fuel ctx rest htail
              | id s =>
                  have hrest : NoLPar rest := by
                    simpa [NoLPar] using hno
                  have hres : ReducesToEncTerm (resolve (encCtx ctx) (con0 s)) (LF.resolve ctx s) :=
                    resolve_sim ctx s
                  have htail := appmore_raw_matches_no_lpar (fuel + 1) ctx (LF.resolve ctx s) rest
                    (resolve (encCtx ctx) (con0 s)) hrest hres
                  exact app_success_id_raw fuel ctx s rest htail

theorem app_matches_no_lpar (fuel : Nat) (ctx : List String) (toks : List LF.Tok)
    (hno : NoLPar toks) :
    ∃ N, MatchesParse (LF.pApp fuel ctx toks)
      (eval pLF N (ap (peano fuel) (encCtx ctx) (encToks toks))) := by
  obtain ⟨N, hN⟩ := app_raw_matches_no_lpar fuel ctx toks hno
  exact matches_parse_exact_of_raw_eval hN

def ParserSimMutual (fuel : Nat) : Prop :=
  (∀ ctx toks,
    FirstActiveMatchesParseRaw (LF.pTerm fuel ctx toks)
      (tm (peano fuel) (encCtx ctx) (encToks toks))) ∧
  (∀ ctx toks,
    FirstActiveMatchesParseRaw (LF.pArrow fuel ctx toks)
      (ar (peano fuel) (encCtx ctx) (encToks toks))) ∧
  (∀ ctx toks,
    FirstActiveMatchesParseRaw (LF.pApp fuel ctx toks)
      (ap (peano fuel) (encCtx ctx) (encToks toks))) ∧
  (∀ ctx acc toks t rest accAst,
    ReducesToEncTerm accAst acc →
      LF.pAppMore fuel ctx acc toks = (t, rest) →
        FirstActiveMatchesParseRaw (some (t, rest))
          (apm (peano fuel) (encCtx ctx) accAst (encToks toks))) ∧
  (∀ ctx toks,
    FirstActiveMatchesParseRaw (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)))

theorem parser_sim_mutual_zero : ParserSimMutual 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ctx toks
    exact term_no_fuel_first_active ctx toks
  · intro ctx toks
    exact arrow_no_fuel_first_active ctx toks
  · intro ctx toks
    exact app_no_fuel_first_active ctx toks
  · intro ctx acc toks t rest accAst hacc hparse
    simp only [LF.pAppMore, Prod.mk.injEq] at hparse
    rcases hparse with ⟨rfl, rfl⟩
    exact appmore_zero_first_active ctx acc toks accAst hacc
  · intro ctx toks
    exact atom_no_fuel_first_active ctx toks

theorem parser_sim_mutual_succ_appmore (fuel : Nat) (ih : ParserSimMutual fuel) :
    ∀ ctx acc toks t rest accAst,
      ReducesToEncTerm accAst acc →
        LF.pAppMore (fuel + 1) ctx acc toks = (t, rest) →
          FirstActiveMatchesParseRaw (some (t, rest))
            (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks)) := by
  rcases ih with ⟨_, _, _, ihAppMore, ihAtom⟩
  intro ctx acc toks t rest accAst hacc hparse
  have hsim : FirstActiveMatchesParseRaw (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks)) :=
    appmore_succ_first_active_of_atom_appmore fuel ctx acc toks accAst hacc
      (ihAtom ctx toks)
      (fun a rest' u _ hu => by
        cases htail : LF.pAppMore fuel ctx (.app acc a) rest' with
        | mk t' rest'' =>
            exact ihAppMore ctx (.app acc a) rest' t' rest''
              (App (encTerm acc) u) (reduces_app (reduces_encTerm_refl acc) hu) htail)
  simpa [hparse] using hsim

theorem parser_sim_mutual_succ_app (fuel : Nat) (ih : ParserSimMutual fuel) :
    ∀ ctx toks,
      FirstActiveMatchesParseRaw (LF.pApp (fuel + 1) ctx toks)
        (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨_, _, _, ihAppMore, ihAtom⟩
  intro ctx toks
  exact app_succ_first_active_of_atom_appmore fuel ctx toks
    (ihAtom ctx toks)
    (fun a rest u _ hu => by
      cases htail : LF.pAppMore fuel ctx a rest with
      | mk t' rest' =>
          exact ihAppMore ctx a rest t' rest' u hu htail)

theorem parser_sim_mutual_succ_arrow_of_shift (fuel : Nat) (ih : ParserSimMutual fuel)
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B)) :
    ∀ ctx toks,
      FirstActiveMatchesParseRaw (LF.pArrow (fuel + 1) ctx toks)
        (ar (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨ihTerm, _, ihApp, _, _⟩
  intro ctx toks
  exact arrow_succ_first_active_of_app_term fuel ctx toks
    (ihApp ctx toks)
    (fun A bodyToks Araw _ hA =>
      arK2_matches_first_active_of_term_first_active fuel ctx A Araw hA bodyToks hshift
        (ihTerm ctx bodyToks))

theorem parser_sim_mutual_succ_atom (fuel : Nat) (ih : ParserSimMutual fuel) :
    ∀ ctx toks,
      FirstActiveMatchesParseRaw (LF.pAtom (fuel + 1) ctx toks)
        (at' (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨ihTerm, _, _, _, _⟩
  intro ctx toks
  exact atom_succ_first_active_of_lpar_term fuel ctx toks
    (fun rest h => by
      subst h
      exact ihTerm ctx rest)

theorem parser_sim_mutual_succ_term (fuel : Nat) (ih : ParserSimMutual fuel) :
    ∀ ctx toks,
      FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx toks)
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨ihTerm, ihArrow, ihApp, _, _⟩
  intro ctx toks
  have hfallback : ∀ toks,
      eval pLF 1 (tm (peano (fuel + 1)) (encCtx ctx) (encToks toks))
        = ar (peano fuel) (encCtx ctx) (encToks toks) →
      LF.pTerm (fuel + 1) ctx toks = LF.pArrow fuel ctx toks →
      FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx toks)
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
    intro toks hstep hparse
    rw [hparse]
    exact first_active_prepend hstep
      (ParserActiveShape.tm (peano (fuel + 1)) (encCtx ctx) (encToks toks))
      (ihArrow ctx toks)
  have hpi : ∀ x rest,
      FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: rest))
        (tm (peano (fuel + 1)) (encCtx ctx)
          (encToks (.pi :: .id x :: .colon :: rest))) := by
    intro x rest
    have hinner : FirstActiveMatchesParseRaw
        (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: rest))
        (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest))) :=
      tmPi1_matches_first_active_of_app_first_active fuel ctx x rest
        (ihApp ctx rest)
        (fun A bodyToks Araw happ hA =>
          tmPi2_matches_first_active_of_term_first_active fuel (x :: ctx) A Araw hA
            bodyToks (ihTerm (x :: ctx) bodyToks))
    have hstep : eval pLF 1
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: .id x :: .colon :: rest)))
        = tmPi1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest)) := by
      simp only [peano, encToks, encTok, eval, os_tm_pi]
    exact first_active_prepend hstep
      (ParserActiveShape.tm (peano (fuel + 1)) (encCtx ctx)
        (encToks (.pi :: .id x :: .colon :: rest))) hinner
  have hlam : ∀ x rest,
      FirstActiveMatchesParseRaw (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: rest))
        (tm (peano (fuel + 1)) (encCtx ctx)
          (encToks (.lam :: .id x :: .colon :: rest))) := by
    intro x rest
    have hinner : FirstActiveMatchesParseRaw
        (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: rest))
        (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest))) :=
      tmLam1_matches_first_active_of_app_first_active fuel ctx x rest
        (ihApp ctx rest)
        (fun A bodyToks Araw happ hA =>
          tmLam2_matches_first_active_of_term_first_active fuel (x :: ctx) A Araw hA
            bodyToks (ihTerm (x :: ctx) bodyToks))
    have hstep : eval pLF 1
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: .id x :: .colon :: rest)))
        = tmLam1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest)) := by
      simp only [peano, encToks, encTok, eval, os_tm_lam]
    exact first_active_prepend hstep
      (ParserActiveShape.tm (peano (fuel + 1)) (encCtx ctx)
        (encToks (.lam :: .id x :: .colon :: rest))) hinner
  cases toks with
  | nil =>
      exact hfallback [] (by simp only [peano, encToks, eval]; rfl) (by rfl)
  | cons tok rest =>
      cases tok with
      | pi =>
          cases rest with
          | nil => exact hfallback [.pi] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
          | cons tok2 rest2 =>
              cases tok2 with
              | id x =>
                  cases rest2 with
                  | nil => exact hfallback [.pi, .id x] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                  | cons tok3 rest3 =>
                      cases tok3 with
                      | colon => exact hpi x rest3
                      | pi => exact hfallback (.pi :: .id x :: .pi :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lam => exact hfallback (.pi :: .id x :: .lam :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | arr => exact hfallback (.pi :: .id x :: .arr :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | dot => exact hfallback (.pi :: .id x :: .dot :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lpar => exact hfallback (.pi :: .id x :: .lpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | rpar => exact hfallback (.pi :: .id x :: .rpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | type => exact hfallback (.pi :: .id x :: .type :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | id y => exact hfallback (.pi :: .id x :: .id y :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | pi => exact hfallback (.pi :: .pi :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lam => exact hfallback (.pi :: .lam :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | arr => exact hfallback (.pi :: .arr :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | colon => exact hfallback (.pi :: .colon :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | dot => exact hfallback (.pi :: .dot :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lpar => exact hfallback (.pi :: .lpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | rpar => exact hfallback (.pi :: .rpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | type => exact hfallback (.pi :: .type :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | lam =>
          cases rest with
          | nil => exact hfallback [.lam] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
          | cons tok2 rest2 =>
              cases tok2 with
              | id x =>
                  cases rest2 with
                  | nil => exact hfallback [.lam, .id x] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                  | cons tok3 rest3 =>
                      cases tok3 with
                      | colon => exact hlam x rest3
                      | pi => exact hfallback (.lam :: .id x :: .pi :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lam => exact hfallback (.lam :: .id x :: .lam :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | arr => exact hfallback (.lam :: .id x :: .arr :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | dot => exact hfallback (.lam :: .id x :: .dot :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lpar => exact hfallback (.lam :: .id x :: .lpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | rpar => exact hfallback (.lam :: .id x :: .rpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | type => exact hfallback (.lam :: .id x :: .type :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | id y => exact hfallback (.lam :: .id x :: .id y :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | pi => exact hfallback (.lam :: .pi :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lam => exact hfallback (.lam :: .lam :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | arr => exact hfallback (.lam :: .arr :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | colon => exact hfallback (.lam :: .colon :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | dot => exact hfallback (.lam :: .dot :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lpar => exact hfallback (.lam :: .lpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | rpar => exact hfallback (.lam :: .rpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | type => exact hfallback (.lam :: .type :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | arr => exact hfallback (.arr :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | colon => exact hfallback (.colon :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | dot => exact hfallback (.dot :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | lpar => exact hfallback (.lpar :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | rpar => exact hfallback (.rpar :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | type => exact hfallback (.type :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | id x => exact hfallback (.id x :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)

theorem parser_sim_mutual_succ_of_shift (fuel : Nat) (ih : ParserSimMutual fuel)
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B)) :
    ParserSimMutual (fuel + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact parser_sim_mutual_succ_term fuel ih
  · exact parser_sim_mutual_succ_arrow_of_shift fuel ih hshift
  · exact parser_sim_mutual_succ_app fuel ih
  · exact parser_sim_mutual_succ_appmore fuel ih
  · exact parser_sim_mutual_succ_atom fuel ih

theorem parser_sim_mutual_of_shift
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B)) :
    ∀ fuel, ParserSimMutual fuel := by
  intro fuel
  induction fuel with
  | zero => exact parser_sim_mutual_zero
  | succ fuel ih => exact parser_sim_mutual_succ_of_shift fuel ih hshift

def ParserSimMutualShiftable (fuel : Nat) : Prop :=
  (∀ ctx toks,
    FirstActiveMatchesParseShiftable (LF.pTerm fuel ctx toks)
      (tm (peano fuel) (encCtx ctx) (encToks toks))) ∧
  (∀ ctx toks,
    FirstActiveMatchesParseShiftable (LF.pArrow fuel ctx toks)
      (ar (peano fuel) (encCtx ctx) (encToks toks))) ∧
  (∀ ctx toks,
    FirstActiveMatchesParseShiftable (LF.pApp fuel ctx toks)
      (ap (peano fuel) (encCtx ctx) (encToks toks))) ∧
  (∀ ctx acc toks t rest accAst,
    ShiftablePayload accAst acc →
      LF.pAppMore fuel ctx acc toks = (t, rest) →
        FirstActiveMatchesParseShiftable (some (t, rest))
          (apm (peano fuel) (encCtx ctx) accAst (encToks toks))) ∧
  (∀ ctx toks,
    FirstActiveMatchesParseShiftable (LF.pAtom fuel ctx toks)
      (at' (peano fuel) (encCtx ctx) (encToks toks)))

theorem parser_sim_mutual_shiftable_zero : ParserSimMutualShiftable 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ctx toks
    exact first_active_shiftable_one (term_no_fuel_sim ctx toks)
      (matches_parse_shiftable_none (con0 "no-fuel"))
      (ParserActiveShape.tm Z (encCtx ctx) (encToks toks))
  · intro ctx toks
    exact first_active_shiftable_one (arrow_no_fuel_sim ctx toks)
      (matches_parse_shiftable_none (con0 "no-fuel"))
      (ParserActiveShape.ar Z (encCtx ctx) (encToks toks))
  · intro ctx toks
    exact first_active_shiftable_one (app_no_fuel_sim ctx toks)
      (matches_parse_shiftable_none (con0 "no-fuel"))
      (ParserActiveShape.ap Z (encCtx ctx) (encToks toks))
  · intro ctx acc toks t rest accAst hacc hparse
    simp only [LF.pAppMore, Prod.mk.injEq] at hparse
    rcases hparse with ⟨rfl, rfl⟩
    exact first_active_shiftable_one (by simp only [peano, eval, os_apm_z])
      (matches_parse_shiftable_some_of_payload hacc)
      (ParserActiveShape.apm Z (encCtx ctx) accAst (encToks toks))
  · intro ctx toks
    exact atom_no_fuel_first_active_shiftable ctx toks

theorem parser_sim_mutual_shiftable_succ_appmore (fuel : Nat)
    (ih : ParserSimMutualShiftable fuel) :
    ∀ ctx acc toks t rest accAst,
      ShiftablePayload accAst acc →
        LF.pAppMore (fuel + 1) ctx acc toks = (t, rest) →
          FirstActiveMatchesParseShiftable (some (t, rest))
            (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks)) := by
  rcases ih with ⟨_, _, _, ihAppMore, ihAtom⟩
  intro ctx acc toks t rest accAst hacc hparse
  have hsim : FirstActiveMatchesParseShiftable (some (LF.pAppMore (fuel + 1) ctx acc toks))
      (apm (peano (fuel + 1)) (encCtx ctx) accAst (encToks toks)) :=
    appmore_succ_first_active_shiftable_of_atom_appmore fuel ctx acc toks accAst hacc
      (ihAtom ctx toks)
      (fun a rest' u _ hu => by
        cases htail : LF.pAppMore fuel ctx (.app acc a) rest' with
        | mk t' rest'' =>
            exact ihAppMore ctx (.app acc a) rest' t' rest''
              (App (encTerm acc) u) (shiftable_app (shiftable_encTerm acc) hu) htail)
  simpa [hparse] using hsim

theorem parser_sim_mutual_shiftable_succ_app (fuel : Nat)
    (ih : ParserSimMutualShiftable fuel) :
    ∀ ctx toks,
      FirstActiveMatchesParseShiftable (LF.pApp (fuel + 1) ctx toks)
        (ap (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨_, _, _, ihAppMore, ihAtom⟩
  intro ctx toks
  exact app_succ_first_active_shiftable_of_atom_appmore fuel ctx toks
    (ihAtom ctx toks)
    (fun a rest u _ hu => by
      cases htail : LF.pAppMore fuel ctx a rest with
      | mk t' rest' =>
          exact ihAppMore ctx a rest t' rest' u hu htail)

theorem parser_sim_mutual_shiftable_succ_arrow_of_shift_payload (fuel : Nat)
    (ih : ParserSimMutualShiftable fuel)
    (hshiftPayload : ∀ {B : LF.Term} {Braw : AST}, ShiftablePayload Braw B →
      ShiftablePayload (shift Z Braw) (LF.shift 0 B)) :
    ∀ ctx toks,
      FirstActiveMatchesParseShiftable (LF.pArrow (fuel + 1) ctx toks)
        (ar (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨ihTerm, _, ihApp, _, _⟩
  intro ctx toks
  exact arrow_succ_first_active_shiftable_of_app_term fuel ctx toks
    (ihApp ctx toks)
    (fun A bodyToks Araw _ hA =>
      arK2_matches_first_active_shiftable_of_term_first_active fuel ctx A Araw hA
        bodyToks hshiftPayload (ihTerm ctx bodyToks))

theorem parser_sim_mutual_shiftable_succ_atom (fuel : Nat)
    (ih : ParserSimMutualShiftable fuel) :
    ∀ ctx toks,
      FirstActiveMatchesParseShiftable (LF.pAtom (fuel + 1) ctx toks)
        (at' (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨ihTerm, _, _, _, _⟩
  intro ctx toks
  exact atom_succ_first_active_shiftable_of_lpar_term fuel ctx toks
    (fun rest h => by
      subst h
      exact ihTerm ctx rest)

theorem parser_sim_mutual_shiftable_succ_term (fuel : Nat)
    (ih : ParserSimMutualShiftable fuel) :
    ∀ ctx toks,
      FirstActiveMatchesParseShiftable (LF.pTerm (fuel + 1) ctx toks)
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
  rcases ih with ⟨ihTerm, ihArrow, ihApp, _, _⟩
  intro ctx toks
  have hfallback : ∀ toks,
      eval pLF 1 (tm (peano (fuel + 1)) (encCtx ctx) (encToks toks))
        = ar (peano fuel) (encCtx ctx) (encToks toks) →
      LF.pTerm (fuel + 1) ctx toks = LF.pArrow fuel ctx toks →
      FirstActiveMatchesParseShiftable (LF.pTerm (fuel + 1) ctx toks)
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks toks)) := by
    intro toks hstep hparse
    rw [hparse]
    exact first_active_shiftable_prepend hstep
      (ParserActiveShape.tm (peano (fuel + 1)) (encCtx ctx) (encToks toks))
      (ihArrow ctx toks)
  have hpi : ∀ x rest,
      FirstActiveMatchesParseShiftable
        (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: rest))
        (tm (peano (fuel + 1)) (encCtx ctx)
          (encToks (.pi :: .id x :: .colon :: rest))) := by
    intro x rest
    have hinner : FirstActiveMatchesParseShiftable
        (LF.pTerm (fuel + 1) ctx (.pi :: .id x :: .colon :: rest))
        (tmPi1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest))) :=
      tmPi1_matches_first_active_shiftable_of_app_first_active fuel ctx x rest
        (ihApp ctx rest)
        (fun A bodyToks Araw _ hA =>
          tmPi2_matches_first_active_shiftable_of_term_first_active fuel (x :: ctx) A Araw hA
            bodyToks (ihTerm (x :: ctx) bodyToks))
    have hstep : eval pLF 1
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks (.pi :: .id x :: .colon :: rest)))
        = tmPi1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest)) := by
      simp only [peano, encToks, encTok, eval, os_tm_pi]
    exact first_active_shiftable_prepend hstep
      (ParserActiveShape.tm (peano (fuel + 1)) (encCtx ctx)
        (encToks (.pi :: .id x :: .colon :: rest))) hinner
  have hlam : ∀ x rest,
      FirstActiveMatchesParseShiftable
        (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: rest))
        (tm (peano (fuel + 1)) (encCtx ctx)
          (encToks (.lam :: .id x :: .colon :: rest))) := by
    intro x rest
    have hinner : FirstActiveMatchesParseShiftable
        (LF.pTerm (fuel + 1) ctx (.lam :: .id x :: .colon :: rest))
        (tmLam1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest))) :=
      tmLam1_matches_first_active_shiftable_of_app_first_active fuel ctx x rest
        (ihApp ctx rest)
        (fun A bodyToks Araw _ hA =>
          tmLam2_matches_first_active_shiftable_of_term_first_active fuel (x :: ctx) A Araw hA
            bodyToks (ihTerm (x :: ctx) bodyToks))
    have hstep : eval pLF 1
        (tm (peano (fuel + 1)) (encCtx ctx) (encToks (.lam :: .id x :: .colon :: rest)))
        = tmLam1 (peano fuel) (encCtx ctx) (con0 x)
          (ap (peano fuel) (encCtx ctx) (encToks rest)) := by
      simp only [peano, encToks, encTok, eval, os_tm_lam]
    exact first_active_shiftable_prepend hstep
      (ParserActiveShape.tm (peano (fuel + 1)) (encCtx ctx)
        (encToks (.lam :: .id x :: .colon :: rest))) hinner
  cases toks with
  | nil =>
      exact hfallback [] (by simp only [peano, encToks, eval]; rfl) (by rfl)
  | cons tok rest =>
      cases tok with
      | pi =>
          cases rest with
          | nil => exact hfallback [.pi] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
          | cons tok2 rest2 =>
              cases tok2 with
              | id x =>
                  cases rest2 with
                  | nil => exact hfallback [.pi, .id x] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                  | cons tok3 rest3 =>
                      cases tok3 with
                      | colon => exact hpi x rest3
                      | pi => exact hfallback (.pi :: .id x :: .pi :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lam => exact hfallback (.pi :: .id x :: .lam :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | arr => exact hfallback (.pi :: .id x :: .arr :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | dot => exact hfallback (.pi :: .id x :: .dot :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lpar => exact hfallback (.pi :: .id x :: .lpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | rpar => exact hfallback (.pi :: .id x :: .rpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | type => exact hfallback (.pi :: .id x :: .type :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | id y => exact hfallback (.pi :: .id x :: .id y :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | pi => exact hfallback (.pi :: .pi :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lam => exact hfallback (.pi :: .lam :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | arr => exact hfallback (.pi :: .arr :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | colon => exact hfallback (.pi :: .colon :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | dot => exact hfallback (.pi :: .dot :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lpar => exact hfallback (.pi :: .lpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | rpar => exact hfallback (.pi :: .rpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | type => exact hfallback (.pi :: .type :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | lam =>
          cases rest with
          | nil => exact hfallback [.lam] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
          | cons tok2 rest2 =>
              cases tok2 with
              | id x =>
                  cases rest2 with
                  | nil => exact hfallback [.lam, .id x] (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                  | cons tok3 rest3 =>
                      cases tok3 with
                      | colon => exact hlam x rest3
                      | pi => exact hfallback (.lam :: .id x :: .pi :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lam => exact hfallback (.lam :: .id x :: .lam :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | arr => exact hfallback (.lam :: .id x :: .arr :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | dot => exact hfallback (.lam :: .id x :: .dot :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | lpar => exact hfallback (.lam :: .id x :: .lpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | rpar => exact hfallback (.lam :: .id x :: .rpar :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | type => exact hfallback (.lam :: .id x :: .type :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
                      | id y => exact hfallback (.lam :: .id x :: .id y :: rest3) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | pi => exact hfallback (.lam :: .pi :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lam => exact hfallback (.lam :: .lam :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | arr => exact hfallback (.lam :: .arr :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | colon => exact hfallback (.lam :: .colon :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | dot => exact hfallback (.lam :: .dot :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | lpar => exact hfallback (.lam :: .lpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | rpar => exact hfallback (.lam :: .rpar :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
              | type => exact hfallback (.lam :: .type :: rest2) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | arr => exact hfallback (.arr :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | colon => exact hfallback (.colon :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | dot => exact hfallback (.dot :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | lpar => exact hfallback (.lpar :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | rpar => exact hfallback (.rpar :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | type => exact hfallback (.type :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)
      | id x => exact hfallback (.id x :: rest) (by simp only [peano, encToks, encTok, eval]; rfl) (by rfl)

theorem parser_sim_mutual_shiftable_succ_of_shift_payload (fuel : Nat)
    (ih : ParserSimMutualShiftable fuel)
    (hshiftPayload : ∀ {B : LF.Term} {Braw : AST}, ShiftablePayload Braw B →
      ShiftablePayload (shift Z Braw) (LF.shift 0 B)) :
    ParserSimMutualShiftable (fuel + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact parser_sim_mutual_shiftable_succ_term fuel ih
  · exact parser_sim_mutual_shiftable_succ_arrow_of_shift_payload fuel ih hshiftPayload
  · exact parser_sim_mutual_shiftable_succ_app fuel ih
  · exact parser_sim_mutual_shiftable_succ_appmore fuel ih
  · exact parser_sim_mutual_shiftable_succ_atom fuel ih

theorem parser_sim_mutual_shiftable_of_shift_payload
    (hshiftPayload : ∀ {B : LF.Term} {Braw : AST}, ShiftablePayload Braw B →
      ShiftablePayload (shift Z Braw) (LF.shift 0 B)) :
    ∀ fuel, ParserSimMutualShiftable fuel := by
  intro fuel
  induction fuel with
  | zero => exact parser_sim_mutual_shiftable_zero
  | succ fuel ih =>
      exact parser_sim_mutual_shiftable_succ_of_shift_payload fuel ih hshiftPayload

theorem app_two_matches (ctx : List String) (toks : List LF.Tok) :
    ∃ N, MatchesParse (LF.pApp ((0 + 1) + 1) ctx toks)
      (eval pLF N (ap (peano ((0 + 1) + 1)) (encCtx ctx) (encToks toks))) := by
  cases toks with
  | nil =>
      obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw (0 + 1) ctx [] (con0 "atom-expected")
        (by simp only [peano, encToks, os_at_err_nil]) (pApp_fail_empty 0 ctx)
      exact matches_parse_exact_of_raw_eval hN
  | cons tok rest =>
      cases tok with
      | lpar => exact app_lpar_no_fuel_matches ctx rest
      | pi =>
          obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw (0 + 1) ctx (.pi :: rest)
            (con0 "atom-expected")
            (by simp only [peano, encToks, encTok, os_at_err_pi]) (pApp_fail_pi 0 ctx rest)
          exact matches_parse_exact_of_raw_eval hN
      | lam =>
          obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw (0 + 1) ctx (.lam :: rest)
            (con0 "atom-expected")
            (by simp only [peano, encToks, encTok, os_at_err_lam]) (pApp_fail_lam 0 ctx rest)
          exact matches_parse_exact_of_raw_eval hN
      | arr =>
          obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw (0 + 1) ctx (.arr :: rest)
            (con0 "atom-expected")
            (by simp only [peano, encToks, encTok, os_at_err_arr]) (pApp_fail_arr 0 ctx rest)
          exact matches_parse_exact_of_raw_eval hN
      | colon =>
          obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw (0 + 1) ctx (.colon :: rest)
            (con0 "atom-expected")
            (by simp only [peano, encToks, encTok, os_at_err_colon]) (pApp_fail_colon 0 ctx rest)
          exact matches_parse_exact_of_raw_eval hN
      | dot =>
          obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw (0 + 1) ctx (.dot :: rest)
            (con0 "atom-expected")
            (by simp only [peano, encToks, encTok, os_at_err_dot]) (pApp_fail_dot 0 ctx rest)
          exact matches_parse_exact_of_raw_eval hN
      | rpar =>
          obtain ⟨N, hN⟩ := app_fail_of_atom_error_raw (0 + 1) ctx (.rpar :: rest)
            (con0 "atom-expected")
            (by simp only [peano, encToks, encTok, os_at_err_rp]) (pApp_fail_rpar 0 ctx rest)
          exact matches_parse_exact_of_raw_eval hN
      | type =>
          have htail := appmore_stop_no_fuel_raw_matches ctx (.srt .type) rest
            (Srt (con0 "type")) (reduces_encTerm_refl (.srt .type))
          obtain ⟨N, hN⟩ := app_success_type_raw 0 ctx rest htail
          exact matches_parse_exact_of_raw_eval hN
      | id s =>
          have htail := appmore_stop_no_fuel_raw_matches ctx (LF.resolve ctx s) rest
            (resolve (encCtx ctx) (con0 s)) (resolve_sim ctx s)
          obtain ⟨N, hN⟩ := app_success_id_raw 0 ctx s rest htail
          exact matches_parse_exact_of_raw_eval hN

theorem recK_matches_raw (toks : List LF.Tok) {v : AST}
    (h : MatchesParseRaw (LF.pTerm 64 [] toks) v) :
    ∃ N, MatchesVerdict (LF.recognize 64 toks) (eval pLF N (recK v)) := by
  unfold LF.recognize
  cases hparse : LF.pTerm 64 [] toks with
  | none =>
      rw [hparse] at h
      rcases h with ⟨e, rfl⟩
      refine ⟨1, ?_⟩
      simp only [eval, os_recK_err]
      exact ⟨e, rfl⟩
  | some pr =>
      rcases pr with ⟨t, rest⟩
      rw [hparse] at h
      rcases h with ⟨u, rfl, hu⟩
      cases rest with
      | nil =>
          rcases hu with ⟨Nu, hNu⟩
          obtain ⟨M, hM⟩ := cong_eval (fun s => Ok s) hcong_Ok Nu hNu (isnormal_encTerm t)
          have hstep : eval pLF 1 (recK (Pp u Nil)) = Ok u := by
            simp only [eval, os_recK_p_nil]
          have htotal := eval_trans pLF 1 M _ _ _ hstep hM
          refine ⟨1 + M, ?_⟩
          change MatchesVerdict (some t) (eval pLF (1 + M) (recK (Pp u Nil)))
          rw [htotal]
          rfl
      | cons tok rest =>
          refine ⟨1, ?_⟩
          change MatchesVerdict none (eval pLF 1 (recK (Pp u (encToks (tok :: rest)))))
          simp only [eval, encToks, os_recK_p_cons]
          exact ⟨extraToks (Cons (encTok tok) (encToks rest)), rfl⟩

theorem recK_matches_first_active_raw (toks : List LF.Tok) {call : AST}
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm 64 [] toks) call) :
    ∃ N, MatchesVerdict (LF.recognize 64 toks) (eval pLF N (recK call)) := by
  exact first_active_bind (fun s => recK s)
    (fun v => MatchesVerdict (LF.recognize 64 toks) v)
    hcong_recK_active hfirst
    (fun {v} hv => recK_matches_raw toks hv)

theorem lfrec_sim_of_parser_first_active (toks : List LF.Tok)
    (hfirst : FirstActiveMatchesParseRaw (LF.pTerm 64 [] toks)
      (tm (peano 64) (encCtx []) (encToks toks))) :
    ∃ N, MatchesVerdict (LF.recognize 64 toks) (eval pLF N (lfrec (encToks toks))) := by
  obtain ⟨N, hN⟩ := recK_matches_first_active_raw toks hfirst
  refine ⟨1 + N, ?_⟩
  have hstep : eval pLF 1 (lfrec (encToks toks))
      = recK (tm (peano 64) Nil (encToks toks)) := by
    simp only [eval, os_lfrec]
  have htotal : eval pLF (1 + N) (lfrec (encToks toks))
      = eval pLF N (recK (tm (peano 64) Nil (encToks toks))) :=
    eval_trans pLF 1 N _ _ _ hstep rfl
  rw [htotal]
  simpa only [encCtx] using hN

theorem lfrec_sim_of_shift
    (hshift : ∀ {B : LF.Term} {Braw : AST}, ReducesToEncTerm Braw B →
      ReducesToEncTerm (shift Z Braw) (LF.shift 0 B)) :
    ∀ toks, ∃ N, MatchesVerdict (LF.recognize 64 toks)
      (eval pLF N (lfrec (encToks toks))) := by
  intro toks
  have hparser := (parser_sim_mutual_of_shift hshift 64).1 [] toks
  exact lfrec_sim_of_parser_first_active toks hparser

theorem parser_term_first_active_raw_of_shift_payload
    (hshiftPayload : ∀ {B : LF.Term} {Braw : AST}, ShiftablePayload Braw B →
      ShiftablePayload (shift Z Braw) (LF.shift 0 B)) :
    ∀ fuel ctx toks,
      FirstActiveMatchesParseRaw (LF.pTerm fuel ctx toks)
        (tm (peano fuel) (encCtx ctx) (encToks toks)) := by
  intro fuel ctx toks
  exact first_active_raw_of_shiftable
    ((parser_sim_mutual_shiftable_of_shift_payload hshiftPayload fuel).1 ctx toks)

theorem lfrec_sim_of_shift_payload
    (hshiftPayload : ∀ {B : LF.Term} {Braw : AST}, ShiftablePayload Braw B →
      ShiftablePayload (shift Z Braw) (LF.shift 0 B)) :
    ∀ toks, ∃ N, MatchesVerdict (LF.recognize 64 toks)
      (eval pLF N (lfrec (encToks toks))) := by
  intro toks
  have hparser := parser_term_first_active_raw_of_shift_payload hshiftPayload 64 [] toks
  exact lfrec_sim_of_parser_first_active toks hparser

theorem parser_sim_mutual_shiftable : ∀ fuel, ParserSimMutualShiftable fuel :=
  parser_sim_mutual_shiftable_of_shift_payload
    (fun {_B Braw} h => shiftable_payload_shift_zero (u := Braw) h)

theorem parser_term_first_active_raw :
    ∀ fuel ctx toks,
      FirstActiveMatchesParseRaw (LF.pTerm fuel ctx toks)
        (tm (peano fuel) (encCtx ctx) (encToks toks)) := by
  intro fuel ctx toks
  exact first_active_raw_of_shiftable
    ((parser_sim_mutual_shiftable fuel).1 ctx toks)

theorem lfrec_sim :
    ∀ toks, ∃ N, MatchesVerdict (LF.recognize 64 toks)
      (eval pLF N (lfrec (encToks toks))) := by
  intro toks
  exact lfrec_sim_of_parser_first_active toks (parser_term_first_active_raw 64 [] toks)

end Mettapedia.GSLT.LanguageDef.LFParserSim
