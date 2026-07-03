/-
# HOL/STT languageDef — `hol-core-g` as a scoped GSLT surface

This module verifies a recursive-descent recognizer for the `hol-core-g` parser-lane grammar.
It reuses the LF kernel term carrier (`Srt` / `Con` / `Var` / `Pi` / `Lam` / `App`) so the
recognized HOL/STT surface lowers directly to the imported kernel AST shape used by
`kernel_signature_lf_v0.metta`.

Grounding:
  * `hol-core-g` (`tests/support/lib_parse_gslt_core_grammars.metta`) gives the concrete
    precedence ladder: binders, `HIFF`, `HIMP`, `HOR`, `HAND`, `HEQ`, `HNOT`, application,
    atoms.
  * `kernel_signature_lf_v0.metta` supplies the checked HOL implication fragment:
    `o`, `prf`, `imp`, `impI`, `impE`.
  * Harper/PFPL STT supplies the binder/application reading; this M2 file proves parser
    scope soundness, while the M3 bridge delegates acceptance to the imported kernel.
-/
import Mettapedia.GSLT.LanguageDef.LF

namespace Mettapedia.GSLT.LanguageDef.HOL

abbrev Term := Mettapedia.GSLT.LanguageDef.LF.Term
abbrev WellScoped := Mettapedia.GSLT.LanguageDef.LF.WellScoped
abbrev shift := Mettapedia.GSLT.LanguageDef.LF.shift

namespace WellScoped

/-- Depth monotonicity for the reused kernel AST. -/
theorem mono {t : Term} {n : Nat} (h : WellScoped n t) :
    ∀ {m : Nat}, n ≤ m → WellScoped m t :=
  Mettapedia.GSLT.LanguageDef.LF.WellScoped.mono h

/-- Kernel shift preserves well-scopedness, inherited from the LF carrier proof. -/
theorem shift {t : Term} {n : Nat} (h : WellScoped n t) :
    ∀ c : Nat, WellScoped (n + 1) (shift c t) :=
  Mettapedia.GSLT.LanguageDef.LF.WellScoped.shift h

end WellScoped

/-! ## Surface tokens and kernel-AST lowering choices -/

/-- Surface tokens of `hol-core-g`. -/
inductive Tok where
  | hall | hex | hlam | hdot | hiff | himp | hor | hand | heq | hnot | lpar | rpar
  | id : String → Tok
  deriving DecidableEq, Repr

/-- de Bruijn index of the innermost binding of `s` in `ctx` (head = innermost). -/
def ctxIdx : List String → String → Option Nat
  | [], _ => none
  | h :: t, s => if h = s then some 0 else (ctxIdx t s).map (· + 1)

/-- Resolve an identifier against the name context: bound → `var i`, free → `con s`. -/
def resolve (ctx : List String) (s : String) : Term :=
  match ctxIdx ctx s with
  | some i => .var i
  | none   => .con s

/-- The unannotated `hol-core-g` binder token is lowered at the syntax layer with the
    proposition type constant from the checked HOL fragment. Kernel acceptance is still
    determined only by `kernel-check` in the bridge. -/
def binderTy : Term := .con "o"

def mkUnary (name : String) (t : Term) : Term :=
  .app (.con name) t

def mkBinary (name : String) (a b : Term) : Term :=
  .app (.app (.con name) a) b

def mkAll (body : Term) : Term :=
  .app (.con "all") (.lam binderTy body)

def mkEx (body : Term) : Term :=
  .app (.con "ex") (.lam binderTy body)

def mkLam (body : Term) : Term :=
  .lam binderTy body

def mkIff : Term → Term → Term := mkBinary "iff"
def mkImp : Term → Term → Term := mkBinary "imp"
def mkOr  : Term → Term → Term := mkBinary "or"
def mkAnd : Term → Term → Term := mkBinary "and"
def mkEq  : Term → Term → Term := mkBinary "eq"
def mkNot : Term → Term := mkUnary "not"

theorem wsUnary {name : String} {n : Nat} {t : Term}
    (ht : WellScoped n t) : WellScoped n (mkUnary name t) :=
  .app .con ht

theorem wsBinary {name : String} {n : Nat} {a b : Term}
    (ha : WellScoped n a) (hb : WellScoped n b) : WellScoped n (mkBinary name a b) :=
  .app (.app .con ha) hb

theorem wsAll {n : Nat} {body : Term}
    (hbody : WellScoped (n + 1) body) : WellScoped n (mkAll body) :=
  .app .con (.lam .con hbody)

theorem wsEx {n : Nat} {body : Term}
    (hbody : WellScoped (n + 1) body) : WellScoped n (mkEx body) :=
  .app .con (.lam .con hbody)

theorem wsLam {n : Nat} {body : Term}
    (hbody : WellScoped (n + 1) body) : WellScoped n (mkLam body) :=
  .lam .con hbody

theorem wsIff {n : Nat} {a b : Term}
    (ha : WellScoped n a) (hb : WellScoped n b) : WellScoped n (mkIff a b) :=
  wsBinary ha hb

theorem wsImp {n : Nat} {a b : Term}
    (ha : WellScoped n a) (hb : WellScoped n b) : WellScoped n (mkImp a b) :=
  wsBinary ha hb

theorem wsOr {n : Nat} {a b : Term}
    (ha : WellScoped n a) (hb : WellScoped n b) : WellScoped n (mkOr a b) :=
  wsBinary ha hb

theorem wsAnd {n : Nat} {a b : Term}
    (ha : WellScoped n a) (hb : WellScoped n b) : WellScoped n (mkAnd a b) :=
  wsBinary ha hb

theorem wsEq {n : Nat} {a b : Term}
    (ha : WellScoped n a) (hb : WellScoped n b) : WellScoped n (mkEq a b) :=
  wsBinary ha hb

theorem wsNot {n : Nat} {t : Term}
    (ht : WellScoped n t) : WellScoped n (mkNot t) :=
  wsUnary ht

mutual
/-- `Term → Bind | Iff`, with binders taking a greedy `Term` body. -/
def pTerm : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match toks with
    | .hall :: .id x :: .hdot :: rest =>
      match pTerm fuel (x :: ctx) rest with
      | some (body, r) => some (mkAll body, r)
      | none => none
    | .hex :: .id x :: .hdot :: rest =>
      match pTerm fuel (x :: ctx) rest with
      | some (body, r) => some (mkEx body, r)
      | none => none
    | .hlam :: .id x :: .hdot :: rest =>
      match pTerm fuel (x :: ctx) rest with
      | some (body, r) => some (mkLam body, r)
      | none => none
    | _ => pIff fuel ctx toks
/-- `Iff → Imp HIFF Iff | Imp` (right associative). -/
def pIff : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match pImp fuel ctx toks with
    | some (a, .hiff :: rest) =>
      match pIff fuel ctx rest with
      | some (b, r) => some (mkIff a b, r)
      | none => none
    | some (a, rest) => some (a, rest)
    | none => none
/-- `Imp → Disj HIMP Imp | Disj` (right associative). -/
def pImp : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match pDisj fuel ctx toks with
    | some (a, .himp :: rest) =>
      match pImp fuel ctx rest with
      | some (b, r) => some (mkImp a b, r)
      | none => none
    | some (a, rest) => some (a, rest)
    | none => none
/-- `Disj → Conj HOR Disj | Conj` (right associative). -/
def pDisj : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match pConj fuel ctx toks with
    | some (a, .hor :: rest) =>
      match pDisj fuel ctx rest with
      | some (b, r) => some (mkOr a b, r)
      | none => none
    | some (a, rest) => some (a, rest)
    | none => none
/-- `Conj → Eq HAND Conj | Eq` (right associative). -/
def pConj : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match pEq fuel ctx toks with
    | some (a, .hand :: rest) =>
      match pConj fuel ctx rest with
      | some (b, r) => some (mkAnd a b, r)
      | none => none
    | some (a, rest) => some (a, rest)
    | none => none
/-- `Eq → Neg HEQ Eq | Neg` (right associative, matching `hol-core-g`). -/
def pEq : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match pNeg fuel ctx toks with
    | some (a, .heq :: rest) =>
      match pEq fuel ctx rest with
      | some (b, r) => some (mkEq a b, r)
      | none => none
    | some (a, rest) => some (a, rest)
    | none => none
/-- `Neg → HNOT Neg | App`. -/
def pNeg : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match toks with
    | .hnot :: rest =>
      match pNeg fuel ctx rest with
      | some (t, r) => some (mkNot t, r)
      | none => none
    | _ => pApp fuel ctx toks
/-- `App → App Atom | Atom` (left associative). -/
def pApp : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match pAtom fuel ctx toks with
    | some (a0, r0) => some (pAppMore fuel ctx a0 r0)
    | none => none
/-- Left-fold trailing atoms into an application spine. -/
def pAppMore : Nat → List String → Term → List Tok → (Term × List Tok)
  | 0, _, acc, toks => (acc, toks)
  | fuel + 1, ctx, acc, toks =>
    match pAtom fuel ctx toks with
    | some (a, rest) => pAppMore fuel ctx (.app acc a) rest
    | none => (acc, toks)
/-- `Atom → ( Term ) | id`. -/
def pAtom : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match toks with
    | .lpar :: rest =>
      match pTerm fuel ctx rest with
      | some (t, .rpar :: r2) => some (t, r2)
      | _ => none
    | .id s :: rest => some (resolve ctx s, rest)
    | _ => none
end

/-- Top-level recognizer: parse a closed `Term`, requiring all tokens consumed. -/
def recognize (fuel : Nat) (toks : List Tok) : Option Term :=
  match pTerm fuel [] toks with
  | some (t, []) => some t
  | _ => none

/-! ## Soundness — the recognizer produces only well-scoped kernel ASTs -/

/-- A resolved de Bruijn index is in range of the name context. -/
theorem ctxIdx_lt : ∀ {ctx : List String} {s : String} {i : Nat},
    ctxIdx ctx s = some i → i < ctx.length := by
  intro ctx
  induction ctx with
  | nil => intro s i h; simp [ctxIdx] at h
  | cons hd tl ih =>
    intro s i h
    simp only [ctxIdx] at h
    simp only [List.length_cons]
    by_cases he : hd = s
    · rw [if_pos he] at h
      simp only [Option.some.injEq] at h
      omega
    · rw [if_neg he] at h
      cases hj : ctxIdx tl s with
      | none =>
        rw [hj] at h
        simp at h
      | some j =>
        rw [hj] at h
        simp at h
        have := ih hj
        omega

/-- Resolving any identifier against `ctx` yields a term well-scoped at depth `ctx.length`. -/
theorem resolve_wellScoped (ctx : List String) (s : String) :
    WellScoped ctx.length (resolve ctx s) := by
  unfold resolve
  cases hj : ctxIdx ctx s with
  | none => exact .con
  | some i => exact .var (ctxIdx_lt hj)

/-- **Soundness (mutual, by fuel induction).** Whenever a parser returns a kernel AST, that
    AST is well-scoped at the current name-context depth. -/
theorem sound_all : ∀ (fuel : Nat),
    (∀ ctx toks t rest, pTerm fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pIff fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pImp fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pDisj fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pConj fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pEq fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pNeg fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pApp fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx acc toks t rest, WellScoped ctx.length acc →
        pAppMore fuel ctx acc toks = (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pAtom fuel ctx toks = some (t, rest) → WellScoped ctx.length t) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx toks t rest h; simp [pTerm] at h
    · intro ctx toks t rest h; simp [pIff] at h
    · intro ctx toks t rest h; simp [pImp] at h
    · intro ctx toks t rest h; simp [pDisj] at h
    · intro ctx toks t rest h; simp [pConj] at h
    · intro ctx toks t rest h; simp [pEq] at h
    · intro ctx toks t rest h; simp [pNeg] at h
    · intro ctx toks t rest h; simp [pApp] at h
    · intro ctx acc toks t rest hacc h
      simp only [pAppMore, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hacc
    · intro ctx toks t rest h; simp [pAtom] at h
  | succ fuel ih =>
    obtain ⟨ihTerm, ihIff, ihImp, ihDisj, ihConj, ihEq, ihNeg, ihApp, ihAppMore, ihAtom⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- pTerm: binders or Iff
      intro ctx toks t rest h
      simp only [pTerm] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsAll (ihTerm (_ :: ctx) _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsEx (ihTerm (_ :: ctx) _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsLam (ihTerm (_ :: ctx) _ _ _ (by assumption)))
        | exact ihIff _ _ _ _ h
        | simp_all)
    · -- pIff: right-associated HIFF
      intro ctx toks t rest h
      simp only [pIff] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsIff (ihImp ctx _ _ _ (by assumption)) (ihIff ctx _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact ihImp ctx _ _ _ (by assumption))
        | simp_all)
    · -- pImp: right-associated HIMP
      intro ctx toks t rest h
      simp only [pImp] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsImp (ihDisj ctx _ _ _ (by assumption)) (ihImp ctx _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact ihDisj ctx _ _ _ (by assumption))
        | simp_all)
    · -- pDisj: right-associated HOR
      intro ctx toks t rest h
      simp only [pDisj] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsOr (ihConj ctx _ _ _ (by assumption)) (ihDisj ctx _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact ihConj ctx _ _ _ (by assumption))
        | simp_all)
    · -- pConj: right-associated HAND
      intro ctx toks t rest h
      simp only [pConj] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsAnd (ihEq ctx _ _ _ (by assumption)) (ihConj ctx _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact ihEq ctx _ _ _ (by assumption))
        | simp_all)
    · -- pEq: right-associated HEQ
      intro ctx toks t rest h
      simp only [pEq] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsEq (ihNeg ctx _ _ _ (by assumption)) (ihEq ctx _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact ihNeg ctx _ _ _ (by assumption))
        | simp_all)
    · -- pNeg: HNOT or App
      intro ctx toks t rest h
      simp only [pNeg] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact wsNot (ihNeg ctx _ _ _ (by assumption)))
        | exact ihApp _ _ _ _ h
        | simp_all)
    · -- pApp: atom then fold trailing atoms
      intro ctx toks t rest h
      simp only [pApp] at h
      split at h
      · simp only [Option.some.injEq] at h
        exact ihAppMore _ _ _ _ _ (ihAtom ctx _ _ _ (by assumption)) h
      · simp_all
    · -- pAppMore: left-fold spine
      intro ctx acc toks t rest hacc h
      simp only [pAppMore] at h
      split at h
      · exact ihAppMore _ _ _ _ _ (.app hacc (ihAtom ctx _ _ _ (by assumption))) h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact hacc
    · -- pAtom: parenthesized Term or identifier
      intro ctx toks t rest h
      simp only [pAtom] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact ihTerm ctx _ _ _ (by assumption))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, _⟩ := h
           exact resolve_wellScoped _ _)
        | simp_all)

/-- **Recognizer soundness (the M2 capstone).** A fully-consumed `hol-core-g` parse yields a
    closed (`WellScoped 0`) kernel AST. -/
theorem recognize_sound {fuel : Nat} {toks : List Tok} {t : Term}
    (h : recognize fuel toks = some t) : WellScoped 0 t := by
  unfold recognize at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact (sound_all fuel).1 _ _ _ _ (by assumption)
  · simp_all

/-! ## Finite parse-lane corpus (matching the green `hol-core-g` examples) -/

/-- `! x . p ==> q` -/
def cToks1 : List Tok := [.hall, .id "x", .hdot, .id "p", .himp, .id "q"]
/-- `p /\ q \/ r` -/
def cToks2 : List Tok := [.id "p", .hand, .id "q", .hor, .id "r"]
/-- `! x . ! y . p` -/
def cToks3 : List Tok := [.hall, .id "x", .hdot, .hall, .id "y", .hdot, .id "p"]
/-- `\ x . f x` -/
def cToks4 : List Tok := [.hlam, .id "x", .hdot, .id "f", .id "x"]

theorem corr1 : recognize 64 cToks1 =
    some (mkAll (mkImp (.con "p") (.con "q"))) := by decide

theorem corr2 : recognize 64 cToks2 =
    some (mkOr (mkAnd (.con "p") (.con "q")) (.con "r")) := by decide

theorem corr3 : recognize 64 cToks3 =
    some (mkAll (mkAll (.con "p"))) := by decide

theorem corr4 : recognize 64 cToks4 =
    some (mkLam (.app (.con "f") (.var 0))) := by decide

theorem ws1 : WellScoped 0 (mkAll (mkImp (.con "p") (.con "q"))) :=
  recognize_sound corr1

theorem ws2 : WellScoped 0 (mkOr (mkAnd (.con "p") (.con "q")) (.con "r")) :=
  recognize_sound corr2

theorem ws3 : WellScoped 0 (mkAll (mkAll (.con "p"))) :=
  recognize_sound corr3

theorem ws4 : WellScoped 0 (mkLam (.app (.con "f") (.var 0))) :=
  recognize_sound corr4

end Mettapedia.GSLT.LanguageDef.HOL
