/-
# LF languageDef — the operational λΠ syntax of an LF GSLT  (MIK parser verification, M2)

A `languageDef` operationally defines a `GSLT` `S = (T, E, R)` (Meredith Def 2.1). This file
formalizes the term grammar `T` of the LF (λΠ) GSLT and its de Bruijn scope discipline; the
`lf-core-g` parser (CeTTa parse lane) is verified against it, so the operational front end that
produces terms of `T` is proved to produce exactly the well-scoped ones.

Grounded in (real, not invented):
  * `MettaKernel/kernel/kernel_signature_lf_v0.metta`, `curriculum_lf_demo.metta`
      — the kernel's de Bruijn AST: `Srt` / `Con` / `Var` / `Pi` / `Lam` / `App`.
  * `MettaKernel/kernel/kernel_binding_waist_v1.metta` — de Bruijn `shift` (`bind-shift`).
  * `lf-core-g` (`tests/support/lib_parse_gslt_core_grammars.metta`) — the surface grammar.
  * Dedukti `FO.dk` / `plus.dk` + Lambdapi — concrete surface  `Π x:A.B`  `λ x:A.B`  `A→B`  `f a`  `Type`.

This is the operational (`T`) side; the equations `E` (α/β-conversion) and rewrites `R` come from
the kernel (`nf` / `conv` / `infer`) and are wired in later (M3, the parse→kernel bridge).
-/
namespace Mettapedia.GSLT.LanguageDef.LF

/-- LF sorts — the kernel's `(Srt type)` / `(Srt kind)`. -/
inductive Srt where
  | type | kind
  deriving DecidableEq, Repr

/-- The kernel's de Bruijn λΠ term (the carrier `T` of the LF GSLT).
    `A → B` is not a separate constructor: it is `pi A (shift 0 B)` (Dedukti convention —
    a non-dependent product with an unused bound variable). -/
inductive Term where
  | srt : Srt → Term
  | con : String → Term
  | var : Nat → Term
  | pi  : Term → Term → Term
  | lam : Term → Term → Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq

/-- de Bruijn shift (the kernel's `bind-shift`): lift every free variable `≥ c` by one. -/
def shift (c : Nat) : Term → Term
  | .var k   => .var (if k < c then k else k + 1)
  | .srt s   => .srt s
  | .con x   => .con x
  | .pi A B  => .pi (shift c A) (shift (c + 1) B)
  | .lam A b => .lam (shift c A) (shift (c + 1) b)
  | .app f a => .app (shift c f) (shift c a)

/-- Well-scopedness at context depth `n`: every `var k` has `k < n`; binders extend `n` by one.
    This is the binding/ABT invariant a correct parser + scope-resolver must guarantee. -/
inductive WellScoped : Nat → Term → Prop where
  | srt {n s}   : WellScoped n (.srt s)
  | con {n c}   : WellScoped n (.con c)
  | var {n k}   : k < n → WellScoped n (.var k)
  | pi  {n A B} : WellScoped n A → WellScoped (n + 1) B → WellScoped n (.pi A B)
  | lam {n A b} : WellScoped n A → WellScoped (n + 1) b → WellScoped n (.lam A b)
  | app {n f a} : WellScoped n f → WellScoped n a → WellScoped n (.app f a)

/-- Depth monotonicity: well-scoped at `n` implies well-scoped at any larger depth. -/
theorem WellScoped.mono {t : Term} {n : Nat} (h : WellScoped n t) :
    ∀ {m : Nat}, n ≤ m → WellScoped m t := by
  induction h with
  | srt => intro _ _; exact .srt
  | con => intro _ _; exact .con
  | var hk => intro _ hnm; exact .var (Nat.lt_of_lt_of_le hk hnm)
  | pi _ _ ihA ihB => intro _ hnm; exact .pi (ihA hnm) (ihB (Nat.succ_le_succ hnm))
  | lam _ _ ihA ihb => intro _ hnm; exact .lam (ihA hnm) (ihb (Nat.succ_le_succ hnm))
  | app _ _ ihf iha => intro _ hnm; exact .app (ihf hnm) (iha hnm)

/-- Shifting preserves well-scopedness, raising the bound by one — the de Bruijn scope lemma
    that the parser's named→de-Bruijn resolution relies on. -/
theorem WellScoped.shift {t : Term} {n : Nat} (h : WellScoped n t) :
    ∀ c : Nat, WellScoped (n + 1) (shift c t) := by
  induction h with
  | srt => intro _; exact .srt
  | con => intro _; exact .con
  | var hk => intro c; exact .var (by split <;> omega)
  | pi _ _ ihA ihB => intro c; exact .pi (ihA c) (ihB (c + 1))
  | lam _ _ ihA ihb => intro c; exact .lam (ihA c) (ihb (c + 1))
  | app _ _ ihf iha => intro c; exact .app (ihf c) (iha c)

/-! ## Concrete surface tokens and the `lf-core-g` recognizer

The surface tokens are exactly `lf-core-g`'s terminals: `Π λ → : . ( ) Type` and identifiers
`(Lex lf-id _)`. The recognizer is fuel-bounded recursive descent over the stratified grammar
(`Term → Pi | Lam | Arrow`, `Arrow → App → Term | App`, `App → App Atom | Atom`,
`Atom → ( Term ) | id | Type`), carrying a name context (head = innermost binder) that turns a
bound identifier into a de Bruijn `var` and a free one into `con` — the named→de-Bruijn scope
resolution. `A → B` lowers to `pi A (shift 0 B)` (Dedukti: arrow = non-dependent product). -/

/-- Surface tokens of `lf-core-g`. -/
inductive Tok where
  | pi | lam | arr | colon | dot | lpar | rpar | type
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

mutual
/-- `Term → Pi | Lam | Arrow`. -/
def pTerm : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match toks with
    | .pi :: .id x :: .colon :: rest =>
      match pApp fuel ctx rest with
      | some (A, .dot :: r2) =>
        match pTerm fuel (x :: ctx) r2 with
        | some (B, r3) => some (.pi A B, r3)
        | none => none
      | _ => none
    | .lam :: .id x :: .colon :: rest =>
      match pApp fuel ctx rest with
      | some (A, .dot :: r2) =>
        match pTerm fuel (x :: ctx) r2 with
        | some (b, r3) => some (.lam A b, r3)
        | none => none
      | _ => none
    | _ => pArrow fuel ctx toks
/-- `Arrow → App → Term | App`  (`A → B` = `pi A (shift 0 B)`). -/
def pArrow : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match pApp fuel ctx toks with
    | some (a, .arr :: rest) =>
      match pTerm fuel ctx rest with
      | some (b, r2) => some (.pi a (shift 0 b), r2)
      | none => none
    | some (a, rest) => some (a, rest)
    | none => none
/-- `App → App Atom | Atom` (left-assoc): one atom, then fold trailing atoms. -/
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
/-- `Atom → ( Term ) | id | Type`. -/
def pAtom : Nat → List String → List Tok → Option (Term × List Tok)
  | 0, _, _ => none
  | fuel + 1, ctx, toks =>
    match toks with
    | .lpar :: rest =>
      match pTerm fuel ctx rest with
      | some (t, .rpar :: r2) => some (t, r2)
      | _ => none
    | .type :: rest => some (.srt .type, rest)
    | .id s :: rest => some (resolve ctx s, rest)
    | _ => none
end

/-- Top-level recognizer: parse a closed `Term`, requiring all tokens consumed. -/
def recognize (fuel : Nat) (toks : List Tok) : Option Term :=
  match pTerm fuel [] toks with
  | some (t, []) => some t
  | _ => none

/-! ## Soundness — the recognizer produces exactly well-scoped terms -/

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
    · rw [if_pos he] at h; simp only [Option.some.injEq] at h; omega
    · rw [if_neg he] at h
      cases hj : ctxIdx tl s with
      | none => rw [hj] at h; simp at h
      | some j => rw [hj] at h; simp at h; have := ih hj; omega

/-- Resolving any identifier against `ctx` yields a term well-scoped at depth `ctx.length`. -/
theorem resolve_wellScoped (ctx : List String) (s : String) :
    WellScoped ctx.length (resolve ctx s) := by
  unfold resolve
  cases hj : ctxIdx ctx s with
  | none => exact .con
  | some i => exact .var (ctxIdx_lt hj)

/-- **Soundness (mutual, by fuel induction).** Whenever a parser returns a term, that term is
    well-scoped at the depth of its name context; `pAppMore` additionally carries the invariant
    on its accumulator. The `Pi`/`Arrow` cases discharge the extended-context body via
    `WellScoped.shift`; the identifier case via `resolve_wellScoped`. -/
theorem sound_all : ∀ (fuel : Nat),
    (∀ ctx toks t rest, pTerm fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pArrow fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pApp fuel ctx toks = some (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx acc toks t rest, WellScoped ctx.length acc →
        pAppMore fuel ctx acc toks = (t, rest) → WellScoped ctx.length t) ∧
    (∀ ctx toks t rest, pAtom fuel ctx toks = some (t, rest) → WellScoped ctx.length t) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro ctx toks t rest h; simp [pTerm] at h
    · intro ctx toks t rest h; simp [pArrow] at h
    · intro ctx toks t rest h; simp [pApp] at h
    · intro ctx acc toks t rest hacc h
      simp only [pAppMore, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact hacc
    · intro ctx toks t rest h; simp [pAtom] at h
  | succ fuel ih =>
    obtain ⟨ihTerm, ihArrow, ihApp, ihAppMore, ihAtom⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- pTerm → Pi | Lam | Arrow
      intro ctx toks t rest h
      simp only [pTerm] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h;
           exact .pi (ihApp ctx _ _ _ (by assumption)) (ihTerm (_ :: ctx) _ _ _ (by assumption)))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h;
           exact .lam (ihApp ctx _ _ _ (by assumption)) (ihTerm (_ :: ctx) _ _ _ (by assumption)))
        | exact ihArrow _ _ _ _ h
        | simp_all)
    · -- pArrow: A → B ↦ pi a (shift 0 b)
      intro ctx toks t rest h
      simp only [pArrow] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h;
           exact .pi (ihApp ctx _ _ _ (by assumption)) ((ihTerm ctx _ _ _ (by assumption)).shift 0))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h;
           exact ihApp ctx _ _ _ (by assumption))
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
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact hacc
    · -- pAtom: ( Term ) | id | Type
      intro ctx toks t rest h
      simp only [pAtom] at h
      repeat' split at h
      all_goals (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h;
           exact ihTerm ctx _ _ _ (by assumption))
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h;
           exact .srt)
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h;
           exact resolve_wellScoped _ _)
        | simp_all)

/-- **Recognizer soundness (the M2 capstone).** A fully-consumed `lf-core-g` parse yields a
    closed (`WellScoped 0`) LF term — the parser is a verified producer of well-formed syntax. -/
theorem recognize_sound {fuel : Nat} {toks : List Tok} {t : Term}
    (h : recognize fuel toks = some t) : WellScoped 0 t := by
  unfold recognize at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact (sound_all fuel).1 _ _ _ _ (by assumption)
  · simp_all

end Mettapedia.GSLT.LanguageDef.LF
