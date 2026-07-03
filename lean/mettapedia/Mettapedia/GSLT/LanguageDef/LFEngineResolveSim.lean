/-
# E2b-universal — `eval pLF` simulates named→de-Bruijn `ctxidx` / `resolve`  (2026-07-03)

Mirrors `LFEngineShiftSim.shift_sim`: the certified normalizer `MeTTaIL.eval` computes the
recognizer's scope resolution (`ctxIdx` / `resolve`) exactly as the Lean spec `LF.ctxIdx` / `LF.resolve`,
on *every* context and identifier.

The new subtlety versus `shift_sim`: the `ctx-hit` rule uses MeTTaIL's repeated-pattern-variable
matching to test identifier equality, so the simulation must case-split on `x = s` (decidable) and,
in the `x ≠ s` branch, show the repeated-variable match *fails* (`AST.beq (con0 x) (con0 s) = false`).
The recursive `ctxidx`/`resolve` continuations descend through the `ctxK` / `resolveK` contexts, whose
rules match only the normal shapes `NF` / `Idx k`; a bespoke `Good` invariant (below) certifies that
while the inner call is still reducing it is `ctxidx`/`ctxK`-headed, so no root continuation rule
fires prematurely — the analogue of `shv_lt_final`'s fixed-head guard.

Integrity: 0 sorry / 0 native_decide; `#print axioms` clean.
-/
import Mettapedia.GSLT.LanguageDef.LFEngineShiftSim

namespace Mettapedia.GSLT.LanguageDef.LFResolveSim

open MeTTaIL Mettapedia.GSLT.LanguageDef.LFEnc Mettapedia.GSLT.LanguageDef.LFUniv
open Mettapedia.GSLT.LanguageDef.LFEngineCorr (encTerm)
open Mettapedia.GSLT.LanguageDef.LFShiftSim
  (eval_trans cong_eval isnormal_con0 isnormal_peano isnormal_sexp1)

set_option maxRecDepth 8000

/-! ## Encodings: name context → `Cons`-list, `ctxidx` result → `NF` / `Idx`. -/

/-- Encode a name context as a `Cons`-list of nullary identifier constructors (head = innermost). -/
def encCtx : List String → AST
  | []      => LFEnc.Nil
  | x :: xs => LFEnc.Cons (LFEnc.con0 x) (encCtx xs)

/-- Encode the `ctxidx` continuation result: `none ↦ NF`, `some i ↦ Idx (peano i)`. -/
def encIdx : Option Nat → AST
  | none   => LFEnc.NF
  | some i => LFEnc.Idx (LFEnc.peano i)

/-! ## String / `con0` beq facts — the identifier-equality test underlying `ctx-hit`. -/

/-- The derived `Label` beq on identifiers bottoms out at `String` beq. -/
@[simp] theorem label_id_beq (a b : String) : (Label.id a == Label.id b) = (a == b) := rfl

/-- `con0`-equality reflects String-equality: the constructor comparison bottoms out at `s == s'`. -/
theorem beq_con0 (x s : String) : (LFEnc.con0 x == LFEnc.con0 s) = (x == s) := by
  simp only [con0, BEq.beq, AST.beq, AST.beqList, Bool.and_true]; rfl

/-- Reflexivity of `BEq` for any `LawfulBEq` type, proved without `Classical.choice`
    (the library `beq_self_eq_true` pulls it in). -/
theorem beq_selfT {α : Type} [BEq α] [LawfulBEq α] (a : α) : (a == a) = true :=
  beq_iff_eq.mpr rfl

/-- On identical identifiers the repeated-variable check succeeds. -/
theorem beq_con0_self (s : String) : (LFEnc.con0 s == LFEnc.con0 s) = true := by
  rw [beq_con0]; exact beq_iff_eq.mpr rfl

/-- On distinct identifiers the repeated-variable check fails — the `x ≠ s` non-match. -/
theorem beq_con0_ne {x s : String} (h : x ≠ s) : (LFEnc.con0 x == LFEnc.con0 s) = false := by
  simp only [beq_con0]
  exact beq_eq_false_iff_ne.mpr h

/-! ## Easy one-step dispatch facts (each `rfl`). -/

theorem os_ctx_nil (s : AST) : oneStep pLF (ctxidx Nil s) = some NF := by rfl
theorem os_ctxK_nf : oneStep pLF (ctxK NF) = some NF := by rfl
theorem os_ctxK_idx (k : AST) : oneStep pLF (ctxK (Idx k)) = some (Idx (S k)) := by rfl
theorem os_res (ctx s : AST) : oneStep pLF (resolve ctx s) = some (resolveK s (ctxidx ctx s)) := by
  rfl
theorem os_resK_idx (s k : AST) : oneStep pLF (resolveK s (Idx k)) = some (Var k) := by rfl
theorem os_resK_nf (s : AST) : oneStep pLF (resolveK s NF) = some (Con s) := by rfl

/-- `ctx-hit`: when the list head equals the query, the repeated-variable match fires. -/
theorem os_ctx_hit (s : String) (t : AST) :
    oneStep pLF (ctxidx (Cons (con0 s) t) (con0 s)) = some (Idx Z) := by
  have e1 : (("lt" : String) == "ctxidx") = false := by decide
  have e2 : (("shift" : String) == "ctxidx") = false := by decide
  have e3 : (("shiftVar" : String) == "ctxidx") = false := by decide
  have e4 : (("Nil" : String) == "Cons") = false := by decide
  have e5 : (("t" : String) == "h") = false := by decide
  have e6 : (("h" : String) == "t") = false := by decide
  have e7 : (AST.sexp (Label.id s) [] == AST.sexp (Label.id s) []) = true := beq_con0_self s
  simp only [oneStep, baseReducts, pLF, Presentation.rewrites, shiftRules, ltRules, resolveRules,
    ctxidxRules, parserRules, applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    List.filterMap_cons, List.filterMap_nil, List.nil_append, List.cons_append,
    Option.map_some, Option.map_none, Option.bind_some, Option.bind_none,
    ctxidx, Cons, con0, Nil, NF, Idx, Z, S, Var, Con, ltT, shift, shiftVar, pv,
    AST.matchPat, AST.matchPatList, AST.inst, AST.instList,
    List.find?_cons, List.find?_nil, label_id_beq, beq_selfT,
    reduceCtorEq, if_false, if_true, e1, e2, e3, e4, e5, e6, e7]

/-- `ctx-miss`: when the list head differs from the query, `ctx-hit`'s repeated-variable match FAILS
    (`beq_con0_ne`), so the general miss rule fires and recurses under `ctxK`. This is the crux of the
    `x ≠ s` non-match. -/
theorem os_ctx_miss {x s : String} (xs : AST) (hxs : x ≠ s) :
    oneStep pLF (ctxidx (Cons (con0 x) xs) (con0 s)) = some (ctxK (ctxidx xs (con0 s))) := by
  have e1 : (("lt" : String) == "ctxidx") = false := by decide
  have e2 : (("shift" : String) == "ctxidx") = false := by decide
  have e3 : (("shiftVar" : String) == "ctxidx") = false := by decide
  have e4 : (("Nil" : String) == "Cons") = false := by decide
  have e5 : (("t" : String) == "h") = false := by decide
  have e6 : (("h" : String) == "t") = false := by decide
  have e8 : (("t" : String) == "s") = false := by decide
  have e9 : (("h" : String) == "s") = false := by decide
  have e10 : (("s" : String) == "t") = false := by decide
  have e7 : (AST.sexp (Label.id x) [] == AST.sexp (Label.id s) []) = false := beq_con0_ne hxs
  simp only [oneStep, baseReducts, pLF, Presentation.rewrites, shiftRules, ltRules, resolveRules,
    ctxidxRules, parserRules, applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    List.filterMap_cons, List.filterMap_nil, List.nil_append, List.cons_append,
    Option.map_some, Option.map_none, Option.bind_some, Option.bind_none,
    ctxidx, Cons, con0, ctxK, Nil, NF, Idx, Z, S, Var, Con, ltT, shift, shiftVar, pv,
    AST.matchPat, AST.matchPatList, AST.inst, AST.instList,
    List.find?_cons, List.find?_nil, label_id_beq, beq_selfT,
    reduceCtorEq, if_false, if_true, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

/-! ## The `Good` invariant.

While the inner `ctxidx` call reduces, every reachable term is headed by `ctxidx` or `ctxK`, or is a
normal `NF` / `Idx (peano i)`.  Reducible `Good` terms are therefore never `Idx`-headed with a
reducible payload, so wrapping in a `ctxK` / `resolveK` context never triggers a root continuation
rule prematurely — the analogue of `shv_lt_final`'s fixed-head guard, here made a bona fide invariant.
-/

inductive Good : AST → Prop
  | seed (ctx : List String) (q : String) : Good (ctxidx (encCtx ctx) (con0 q))
  | ctxK {a : AST} : Good a → Good (ctxK a)
  | nf : Good NF
  | idx (i : Nat) : Good (Idx (peano i))

/-- `ctxK` of a `ctxidx`-headed term has no root reduct (concrete head mismatch on every rule). -/
theorem baseReducts_ctxK_ctxidx (a q : AST) : baseReducts pLF (ctxK (ctxidx a q)) = [] := by rfl

/-- `ctxK` of a `ctxK`-headed term has no root reduct. -/
theorem baseReducts_ctxK_ctxK (a : AST) : baseReducts pLF (ctxK (ctxK a)) = [] := by rfl

/-- Descent through `ctxK` when its argument is not root-matchable. -/
theorem ctxK_step {b b' : AST} (hb : baseReducts pLF (ctxK b) = [])
    (h : oneStep pLF b = some b') : oneStep pLF (ctxK b) = some (ctxK b') := by
  have hb' : baseReducts pLF (AST.sexp (Label.id "ctxK") [b]) = [] := hb
  show oneStep pLF (AST.sexp (Label.id "ctxK") [b]) = _
  simp only [oneStep, hb', oneStepList, h, Option.map_some, ctxK]

/-- Inverse: a step of `ctxK b` (with `b` not root-matchable) is a descent into `b`. -/
theorem ctxK_descend_inv {b a' : AST} (hb : baseReducts pLF (ctxK b) = [])
    (h : oneStep pLF (ctxK b) = some a') : ∃ b', oneStep pLF b = some b' ∧ a' = ctxK b' := by
  have hb' : baseReducts pLF (AST.sexp (Label.id "ctxK") [b]) = [] := hb
  have hos : oneStep pLF (ctxK b)
      = (oneStepList pLF [b]).map (fun args => AST.sexp (Label.id "ctxK") args) := by
    show oneStep pLF (AST.sexp (Label.id "ctxK") [b]) = _
    simp only [oneStep, hb']
  rw [hos] at h
  cases hb2 : oneStep pLF b with
  | none => simp only [oneStepList, hb2, Option.map_none, reduceCtorEq] at h
  | some b' =>
    refine ⟨b', rfl, ?_⟩
    simp only [oneStepList, hb2, Option.map_some] at h
    injection h with h; rw [← h]; rfl

/-- Every seed `ctxidx (encCtx ctx) (con0 q)` takes a step. -/
theorem good_seed_reduces (ctx : List String) (q : String) :
    ∃ a', oneStep pLF (ctxidx (encCtx ctx) (con0 q)) = some a' := by
  cases ctx with
  | nil => exact ⟨NF, by rw [show encCtx [] = Nil from rfl, os_ctx_nil]⟩
  | cons y ys =>
    rw [show encCtx (y :: ys) = Cons (con0 y) (encCtx ys) from rfl]
    cases hd : y == q with
    | true => obtain rfl := eq_of_beq hd; exact ⟨Idx Z, os_ctx_hit y (encCtx ys)⟩
    | false =>
      have hyq : y ≠ q := beq_eq_false_iff_ne.mp hd
      exact ⟨ctxK (ctxidx (encCtx ys) (con0 q)), os_ctx_miss (encCtx ys) hyq⟩

/-- Every `ctxK`-wrapped `Good` term takes a step (root reduction if the payload is normal, else a
    descent). -/
theorem good_ctxK_reduces : ∀ {c : AST}, Good c → ∃ a', oneStep pLF (ctxK c) = some a' := by
  intro c hc
  induction hc with
  | seed ctx q =>
    obtain ⟨b', hb'⟩ := good_seed_reduces ctx q
    exact ⟨ctxK b', ctxK_step (baseReducts_ctxK_ctxidx _ _) hb'⟩
  | @ctxK d _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨ctxK e, ctxK_step (baseReducts_ctxK_ctxK d) he⟩
  | nf => exact ⟨NF, os_ctxK_nf⟩
  | idx i => exact ⟨Idx (S (peano i)), os_ctxK_idx (peano i)⟩

/-- **Preservation.** `oneStep` maps `Good` terms to `Good` terms. -/
theorem good_step : ∀ {a : AST}, Good a → ∀ {a' : AST}, oneStep pLF a = some a' → Good a' := by
  intro a ha
  induction ha with
  | seed ctx q =>
    intro a' h
    cases ctx with
    | nil =>
      rw [show encCtx [] = Nil from rfl, os_ctx_nil] at h
      injection h with h; rw [← h]; exact Good.nf
    | cons y ys =>
      rw [show encCtx (y :: ys) = Cons (con0 y) (encCtx ys) from rfl] at h
      cases hd : y == q with
      | true =>
        obtain rfl := eq_of_beq hd; rw [os_ctx_hit y (encCtx ys)] at h
        injection h with h; rw [← h]; exact Good.idx 0
      | false =>
        have hyq : y ≠ q := beq_eq_false_iff_ne.mp hd
        rw [os_ctx_miss (encCtx ys) hyq] at h
        injection h with h; rw [← h]; exact Good.ctxK (Good.seed ys q)
  | @ctxK a₀ bgood ih =>
    intro a' h
    cases bgood with
    | nf => rw [os_ctxK_nf] at h; injection h with h; rw [← h]; exact Good.nf
    | idx i =>
      rw [os_ctxK_idx (peano i)] at h; injection h with h; rw [← h]; exact Good.idx (i + 1)
    | seed ctx q =>
      obtain ⟨b', hb'⟩ := good_seed_reduces ctx q
      rw [ctxK_step (baseReducts_ctxK_ctxidx _ _) hb'] at h
      injection h with h; rw [← h]; exact Good.ctxK (ih hb')
    | @ctxK c cgood =>
      obtain ⟨b', hb'⟩ := good_ctxK_reduces cgood
      rw [ctxK_step (baseReducts_ctxK_ctxK _) hb'] at h
      injection h with h; rw [← h]; exact Good.ctxK (ih hb')
  | nf =>
    intro a' h
    have hn : oneStep pLF NF = none := isnormal_con0 "NF"
    rw [hn] at h; exact absurd h (by simp)
  | idx i =>
    intro a' h
    have hn : oneStep pLF (Idx (peano i)) = none :=
      isnormal_sexp1 (.id "Idx") (peano i) rfl (isnormal_peano i)
    rw [hn] at h; exact absurd h (by simp)

/-- Encoded `ctxidx` results are normal. -/
theorem isnormal_encIdx (r : Option Nat) : IsNormal pLF (encIdx r) := by
  cases r with
  | none => exact isnormal_con0 "NF"
  | some i => exact isnormal_sexp1 (.id "Idx") (peano i) rfl (isnormal_peano i)

/-! ## Context congruence over `eval` for the `Good`-guarded continuations `ctxK` / `resolveK`. -/

/-- **`Good`-guarded context congruence.** If a one-hole context `F` lifts every one-step reduction of
    a `Good` hole, then reducing a `Good` hole to a normal value lifts through `F`. -/
theorem good_cong_eval (F : AST → AST)
    (hdesc : ∀ {a a' : AST}, Good a → oneStep pLF a = some a' → oneStep pLF (F a) = some (F a')) :
    ∀ (N : Nat) {Y V : AST}, Good Y → eval pLF N Y = V → IsNormal pLF V →
      ∃ M, eval pLF M (F Y) = F V := by
  intro N
  induction N with
  | zero =>
    intro Y V _ hY _
    simp only [eval] at hY; subst hY; exact ⟨0, rfl⟩
  | succ n ih =>
    intro Y V hgood hY hV
    simp only [eval] at hY
    cases hstep : oneStep pLF Y with
    | none => rw [hstep] at hY; subst hY; exact ⟨0, rfl⟩
    | some Y' =>
      rw [hstep] at hY
      obtain ⟨M, hM⟩ := ih (good_step hgood hstep) hY hV
      exact ⟨M + 1, by simp only [eval, hdesc hgood hstep]; exact hM⟩

/-- The `ctxK` descent congruence, valid on `Good` holes. -/
theorem hdesc_ctxK : ∀ {a a' : AST},
    Good a → oneStep pLF a = some a' → oneStep pLF (ctxK a) = some (ctxK a') := by
  intro a a' hgood h
  cases hgood with
  | nf => rw [show oneStep pLF NF = none from isnormal_con0 "NF"] at h; simp at h
  | idx i =>
    rw [show oneStep pLF (Idx (peano i)) = none from
      isnormal_sexp1 (.id "Idx") (peano i) rfl (isnormal_peano i)] at h; simp at h
  | seed ctx q => exact ctxK_step (baseReducts_ctxK_ctxidx _ _) h
  | ctxK c => exact ctxK_step (baseReducts_ctxK_ctxK _) h

/-- One `ctxK`-collapse step: `ctxK (encIdx r)` reduces to `encIdx (r.map (·+1))`. -/
theorem ctxK_collapse : ∀ (r : Option Nat),
    eval pLF 1 (ctxK (encIdx r)) = encIdx (r.map (· + 1))
  | none => by simp only [encIdx, eval, os_ctxK_nf, Option.map_none]
  | some i => by simp only [encIdx, eval, os_ctxK_idx, Option.map_some]; rfl

/-- **`ctxidx`-correctness (simulation).** For every name context and identifier, the certified
    normalizer computes `LF.ctxIdx` exactly (encoded). -/
theorem ctxidx_sim : ∀ (ctx : List String) (s : String),
    ∃ N, eval pLF N (LFEnc.ctxidx (encCtx ctx) (LFEnc.con0 s)) = encIdx (LF.ctxIdx ctx s) := by
  intro ctx
  induction ctx with
  | nil =>
    intro s
    refine ⟨1, ?_⟩
    rw [show encCtx [] = Nil from rfl]
    simp only [LF.ctxIdx, encIdx, eval, os_ctx_nil]
  | cons x xs ih =>
    intro s
    rw [show encCtx (x :: xs) = Cons (con0 x) (encCtx xs) from rfl]
    cases hd : x == s with
    | true =>
      obtain rfl := eq_of_beq hd
      refine ⟨1, ?_⟩
      rw [show LF.ctxIdx (x :: xs) x = some 0 from by simp [LF.ctxIdx]]
      simp only [eval, os_ctx_hit, encIdx, peano]
    | false =>
      have hxs : x ≠ s := beq_eq_false_iff_ne.mp hd
      obtain ⟨N, hN⟩ := ih s
      obtain ⟨M, hM⟩ := good_cong_eval ctxK hdesc_ctxK N (Good.seed xs s) hN (isnormal_encIdx _)
      rw [show LF.ctxIdx (x :: xs) s = (LF.ctxIdx xs s).map (· + 1) from by simp [LF.ctxIdx, hxs]]
      refine ⟨1 + (M + 1), ?_⟩
      have hstep1 : eval pLF 1 (ctxidx (Cons (con0 x) (encCtx xs)) (con0 s))
          = ctxK (ctxidx (encCtx xs) (con0 s)) := by
        simp only [eval, os_ctx_miss (encCtx xs) hxs]
      refine eval_trans pLF 1 (M + 1) _ _ _ hstep1 ?_
      refine eval_trans pLF M 1 _ _ _ hM ?_
      exact ctxK_collapse (LF.ctxIdx xs s)

/-! ## `resolve` — one `res` step, then reduce the inner `ctxidx` under `resolveK`, then collapse. -/

theorem baseReducts_resolveK_ctxidx (s0 : String) (a q : AST) :
    baseReducts pLF (resolveK (con0 s0) (ctxidx a q)) = [] := by rfl

theorem baseReducts_resolveK_ctxK (s0 : String) (a : AST) :
    baseReducts pLF (resolveK (con0 s0) (ctxK a)) = [] := by rfl

/-- Descent through `resolveK (con0 s0) □` when the payload is not root-matchable. -/
theorem resolveK_step {s0 : String} {b b' : AST} (hb : baseReducts pLF (resolveK (con0 s0) b) = [])
    (h : oneStep pLF b = some b') :
    oneStep pLF (resolveK (con0 s0) b) = some (resolveK (con0 s0) b') := by
  have hb' : baseReducts pLF (AST.sexp (Label.id "resolveK") [con0 s0, b]) = [] := hb
  have hc : oneStep pLF (con0 s0) = none := isnormal_con0 s0
  show oneStep pLF (AST.sexp (Label.id "resolveK") [con0 s0, b]) = _
  simp only [oneStep, hb', oneStepList, hc, h, Option.map_some, resolveK]

/-- The `resolveK` descent congruence, valid on `Good` holes. -/
theorem hdesc_resolveK (s0 : String) : ∀ {a a' : AST},
    Good a → oneStep pLF a = some a' → oneStep pLF (resolveK (con0 s0) a) = some (resolveK (con0 s0) a') := by
  intro a a' hgood h
  cases hgood with
  | nf => rw [show oneStep pLF NF = none from isnormal_con0 "NF"] at h; simp at h
  | idx i =>
    rw [show oneStep pLF (Idx (peano i)) = none from
      isnormal_sexp1 (.id "Idx") (peano i) rfl (isnormal_peano i)] at h; simp at h
  | seed ctx q => exact resolveK_step (baseReducts_resolveK_ctxidx _ _ _) h
  | ctxK c => exact resolveK_step (baseReducts_resolveK_ctxK _ _) h

/-- **`resolve`-correctness (simulation).** The certified normalizer reduces the encoded
    `resolve (encCtx ctx) (con0 s)` to the encoding of Lean's `LF.resolve ctx s`. -/
theorem resolve_sim : ∀ (ctx : List String) (s : String),
    ∃ N, eval pLF N (LFEnc.resolve (encCtx ctx) (LFEnc.con0 s))
      = LFEngineCorr.encTerm (LF.resolve ctx s) := by
  intro ctx s
  obtain ⟨N, hN⟩ := ctxidx_sim ctx s
  obtain ⟨M, hM⟩ :=
    good_cong_eval (resolveK (con0 s)) (hdesc_resolveK s) N (Good.seed ctx s) hN (isnormal_encIdx _)
  refine ⟨1 + (M + 1), ?_⟩
  have hstep1 : eval pLF 1 (resolve (encCtx ctx) (con0 s))
      = resolveK (con0 s) (ctxidx (encCtx ctx) (con0 s)) := by
    simp only [eval, os_res]
  refine eval_trans pLF 1 (M + 1) _ _ _ hstep1 ?_
  refine eval_trans pLF M 1 _ _ _ hM ?_
  cases hr : LF.ctxIdx ctx s with
  | none =>
    rw [show LF.resolve ctx s = .con s from by simp [LF.resolve, hr]]
    simp only [encIdx, eval, os_resK_nf, encTerm]
  | some i =>
    rw [show LF.resolve ctx s = .var i from by simp [LF.resolve, hr]]
    simp only [encIdx, eval, os_resK_idx, encTerm]

end Mettapedia.GSLT.LanguageDef.LFResolveSim
