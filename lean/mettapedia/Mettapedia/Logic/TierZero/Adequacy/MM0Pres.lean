import Mettapedia.Logic.TierZero.Kernel2.Spaces
import Mettapedia.Languages.MM0.Kernel.Proof

/-!
# MM0 as a tier-0 presentation

The presentation of an MM0 environment (Mettapedia's MM0 kernel: `TermSignature`,
`Definition.Signature`, `TheoremSignature`) as rules of the tier-0 kernel.

**Encoding** (`enc Γ`), relative to the claim's context `Γ`:

* a bound variable `i` is the **name** `fv i` (a scope variable, as the kernel freshens it);
* a regular variable `i` with dependencies `D` is the **name `fv i` over the names of `D`**;
* a term symbol `c` is the constant `c`, and an application is `(F A)`.

So **the names in an encoded term are its MM0 support**: the name of the bound variable `j` occurs
in `enc Γ e` exactly when `e` depends on `j` (`occursIn_enc`, MM0's `HasVar`), which is what
`absent-from` checks (`absentOk_enc`). Example: in `Γ = [x : bound s, φ : regular t {0}]`, `φ` is
`(fv1 fv0)`, which mentions `x`; `(all x φ)` mentions `x` too.

**Judgments.** `(bv s X)`: `X` is a bound variable of sort `s`; `(ty s E)`: `E` has sort `s`
(saturated); `(cv s E F)`: `E` and `F` are convertible at sort `s`; `(pf E)`: `E` is proved.

**Rules** (`rules E`, rule names `Name`):

* `con c`: each argument fits its binder (`bv` for a bound slot, `ty` for a regular one) ⊢ the
  application has the result sort;
* `thm t`: each argument fits its binder, each hypothesis is proved, and the **independence
  conditions** hold: for each bound formal `p` and each formal `q` whose binder does not depend on
  `p`, `(absent-from p q)` ⊢ the conclusion is proved (MM0's admissible substitution);
* `cvRefl s`, `cvSymm`, `cvTrans`, `cvCong c`, `unfold c` (its dummies bound variables of the
  declared sorts, each fresh for the arguments and the earlier dummies, by `absent-from`), and `conv`
  (MM0's conversion of a proved statement).

At tier 0 a conversion is a **proof node**: MM0's conversion witnesses become nodes of these rules.

This file builds the encoding, the rules, and the bridging lemmas: the encoding commutes with MM0's
simultaneous substitution (`inst_patOf`), it is injective (`dec_enc`), and support is the
occurrence of names (`occursIn_enc`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.MM0.Kernel

/-! ## Encoding -/

/-- The dependencies of a regular variable, in order. -/
def depList (D : Finset ℕ) : List ℕ := D.sort (· ≤ ·)

/-- A variable of the context. -/
def encVar (Γ : Context) (i : ℕ) : Tm :=
  match Γ[i]? with
  | some (.bound _) => fvar i
  | some (.regular _ D) => fvar i (depList D)
  | none => fvar i []

/-- **The encoding of an MM0 preterm** in the context `Γ`. -/
def enc (Γ : Context) : Preterm → Tm
  | .var i => encVar Γ i
  | .term c => num c
  | .app f a => ex [enc Γ f, enc Γ a]

/-- A preterm over a declaration's formals as a pattern: variable `k` is formal `k`. -/
def patOf : Preterm → Pat
  | .var k => .mvar k
  | .term c => pnum c
  | .app f a => pex [patOf f, patOf a]

/-- Read a preterm back. -/
def dec : Tm → Option Preterm
  | .node (.fv i) _ => some (.var i)
  | .node (.num c) .nil => some (.term c)
  | .node .expr (.cons 0 f (.cons 0 a .nil)) =>
      match dec f, dec a with
      | some f', some a' => some (.app f' a')
      | _, _ => none
  | _ => none

theorem dec_enc (Γ : Context) : ∀ e : Preterm, dec (enc Γ e) = some e
  | .var i => by
      simp only [enc, encVar]
      cases Γ[i]? with
      | none => rfl
      | some b => cases b <;> rfl
  | .term c => rfl
  | .app f a => by
      simp only [enc, ex, flds, dec, dec_enc Γ f, dec_enc Γ a]

/-- **The encoding is injective.** -/
theorem enc_inj {Γ : Context} {e e' : Preterm} (h : enc Γ e = enc Γ e') : e = e' := by
  have := dec_enc Γ e
  rw [h, dec_enc Γ e'] at this
  exact (Option.some.inj this).symm

/-! ## The encoding commutes with simultaneous substitution -/

theorem inst_pex2 (σ : Subst ℕ Tm) (p q : Pat) :
    (pex [p, q]).inst σ = match p.inst σ, q.inst σ with
      | some x, some y => some (ex [x, y])
      | _, _ => none := by
  simp only [pex, pflds, TreePat.inst, TreePatFields.inst]
  cases p.inst σ <;> cases q.inst σ <;> rfl

/-- **Instantiating a statement's pattern with encoded arguments is encoding its MM0
substitution.** -/
theorem inst_patOf (Γ : Context) (vals : List Preterm) : ∀ p : Preterm,
    (patOf p).inst (substOf (vals.map (enc Γ))) =
      (Preterm.substitute (Substitution.ofList vals) p).map (enc Γ)
  | .var k => by
      simp [patOf, TreePat.inst, substOf, Preterm.substitute, Substitution.ofList]
  | .term c => by
      simp [patOf, pnum, TreePat.inst, TreePatFields.inst, Preterm.substitute, enc, num]
  | .app f a => by
      rw [patOf, inst_pex2, inst_patOf Γ vals f, inst_patOf Γ vals a]
      simp only [Preterm.substitute, Option.bind_eq_bind, Option.pure_def]
      cases Preterm.substitute (Substitution.ofList vals) f <;>
        cases Preterm.substitute (Substitution.ofList vals) a <;> simp [enc]

/-! ## Support is occurrence of names -/

theorem lift_fvar (j d : ℕ) : Term.lift 0 d (fvar j) = fvar j := by
  simp [fvar, flds, Term.lift, Term.Fields.lift]

/-- A name occurs in a name over names exactly when it is that name, plain, or one of the names it
is over. -/
theorem occursAt_fvar_fvar (j k d : ℕ) :
    ∀ ds : List ℕ, occursAt (fvar j) d (fvar k ds) = true ↔ (k = j ∧ ds = []) ∨ j ∈ ds := by
  intro ds
  have one : ∀ (e x : ℕ), occursAt (fvar j) e (.node (.fv x) .nil) = true ↔ j = x := by
    intro e x
    rw [occursAt, lift_fvar]
    simp [fvar, flds, occursFields]
  have fields : ∀ (e : ℕ) (L : List ℕ),
      occursFields (fvar j) e (flds (L.map fun d => .node (.fv d) .nil)) = true ↔ j ∈ L := by
    intro e L
    induction L with
    | nil => simp [flds, occursFields]
    | cons x L ih =>
        simp only [List.map_cons, flds, occursFields, Bool.or_eq_true, ih, List.mem_cons, Nat.add_zero,
          one]
  have top : Term.lift 0 d (fvar j) = fvar k ds ↔ (k = j ∧ ds = []) := by
    rw [lift_fvar]
    constructor
    · intro e
      simp only [fvar, Term.node.injEq, Head.fv.injEq] at e
      obtain ⟨rfl, e⟩ := e
      refine ⟨rfl, ?_⟩
      cases ds with
      | nil => rfl
      | cons _ _ => simp [flds] at e
    · rintro ⟨rfl, rfl⟩; rfl
  have unfold1 : occursAt (fvar j) d (fvar k ds) =
      (decide (Term.lift 0 d (fvar j) = fvar k ds) ||
        occursFields (fvar j) d (flds (ds.map fun d => .node (.fv d) .nil))) := by
    conv_lhs => rw [show fvar k ds = .node (.fv k) (flds (ds.map fun d => .node (.fv d) .nil)) from rfl]
    rw [occursAt]
    rfl
  rw [unfold1, Bool.or_eq_true, decide_eq_true_eq, top, fields]

/-- **The support of an encoded term is its MM0 support**: the name of the bound variable `j`
occurs in it exactly when the term depends on `j`. -/
theorem occursIn_enc (Γ : Context) {j s : ℕ} (hj : Γ[j]? = some (.bound s)) :
    ∀ e : Preterm, occursIn (fvar j) (enc Γ e) = true ↔ Preterm.HasVar Γ j e
  | .var i => by
      rw [Preterm.hasVar_var_iff]
      simp only [enc, encVar, occursIn]
      cases h : Γ[i]? with
      | none =>
          rw [occursAt_fvar_fvar]
          constructor
          · rintro (⟨rfl, -⟩ | m)
            · rw [hj] at h; cases h
            · simp at m
          · rintro (⟨_, e, -⟩ | ⟨_, _, e, -⟩) <;> cases e
      | some b =>
          cases b with
          | bound s' =>
              rw [occursAt_fvar_fvar]
              simp only [and_true, List.not_mem_nil, or_false, Option.some.injEq, reduceCtorEq,
                false_and, exists_false]
              constructor
              · intro e; exact ⟨s', rfl, e.symm⟩
              · rintro ⟨_, _, e⟩; exact e.symm
          | regular s' D =>
              rw [occursAt_fvar_fvar]
              constructor
              · rintro (⟨rfl, -⟩ | m)
                · rw [hj] at h; cases h
                · exact Or.inr ⟨s', D, rfl, by simpa [depList] using m⟩
              · rintro (⟨_, e, -⟩ | ⟨_, _, e, m⟩)
                · cases e
                · cases e; exact Or.inr (by simpa [depList] using m)
  | .term c => by
      constructor
      · intro h
        simp only [enc, num, occursIn] at h
        rw [occursAt, lift_fvar] at h
        simp [fvar, flds, occursFields] at h
      · intro h; cases h
  | .app f a => by
      rw [Preterm.hasVar_app_iff, ← occursIn_enc Γ hj f, ← occursIn_enc Γ hj a]
      simp only [enc, ex, flds, occursIn, occursAt, occursFields, Nat.add_zero, lift_fvar,
        Bool.or_eq_true, Bool.or_false]
      simp [fvar, flds]

/-- `absent-from` on encodings is MM0's independence. -/
theorem absentOk_enc (Γ : Context) {i s : ℕ} (hb : Γ[i]? = some (.bound s)) (e : Preterm) :
    absentOk (enc Γ (.var i)) (enc Γ e) = true ↔ ¬ Preterm.HasVar Γ i e := by
  have v : enc Γ (.var i) = fvar i := by simp [enc, encVar, hb]
  rw [v, absentOk, ← occursIn_enc Γ hb e]
  simp

/-! ## Judgments -/

def bvP (s : ℕ) (x : Pat) : Pat := pjd "bv" [pnum s, x]
def tyP (s : Pat) (x : Pat) : Pat := pjd "ty" [s, x]
def cvP (s x y : Pat) : Pat := pjd "cv" [s, x, y]
def pfP (x : Pat) : Pat := pjd "pf" [x]

def bvJ (s : ℕ) (x : Tm) : Tm := jd "bv" [num s, x]
def tyJ (s : ℕ) (x : Tm) : Tm := jd "ty" [num s, x]
def cvJ (s : ℕ) (x y : Tm) : Tm := jd "cv" [num s, x, y]
def pfJ (x : Tm) : Tm := jd "pf" [x]

/-- The judgment a binder asks of formal `k`. -/
def fitPat (b : Binder) (k : ℕ) : Pat :=
  match b with
  | .bound s => bvP s (pv k)
  | .regular s _ => tyP (pnum s) (pv k)

/-- The judgment a binder asks of a term. -/
def fitJ (b : Binder) (x : Tm) : Tm :=
  match b with
  | .bound s => bvJ s x
  | .regular s _ => tyJ s x

/-! ## Rules -/

/-- The fit premises of a context's binders: binder `k` asks formal `off + k`. -/
def fits (off : ℕ) (Φ : Context) : List Premise := (Φ.zipIdx off).map fun x => .judg (fitPat x.1 x.2)

/-- The formals `off … off + n - 1` as MM0 variables. -/
def varsP (off n : ℕ) : List Preterm := (List.range' off n).map Preterm.var

/-- The independence conditions of a formal context: for each bound formal `p` and each formal
`q` whose binder does not depend on `p`, `(absent-from p q)`. -/
def indep (Φ : Context) : List Premise :=
  Φ.zipIdx.flatMap fun x => match x.1 with
    | .bound _ => Φ.zipIdx.filterMap fun y =>
        if y.1.DependsOn y.2 x.2 then none else some (.absent (pv x.2) (pv y.2))
    | .regular _ _ => []

/-- The freshness conditions of an unfolding: dummy `j` (formal `n + j`) is fresh for the
arguments and the earlier dummies. -/
def fresh (n m : ℕ) : List Premise :=
  (List.range m).flatMap fun j => (List.range (n + j)).map fun k => .absent (pv (n + j)) (pv k)

/-- The dummies' premises: dummy `j` is a bound variable of its sort. -/
def dummyFits (n : ℕ) (ds : List ℕ) : List Premise := (ds.zipIdx n).map fun x => .judg (bvP x.1 (pv x.2))

/-- `con c`: the arguments fit ⊢ the application has the result sort. -/
def conRule (c : ℕ) (d : TermDecl) : Rule :=
  ⟨d.arguments.length, fits 0 d.arguments,
    tyP (pnum d.resultSort) (patOf (Preterm.applyArgs (.term c) (varsP 0 d.arguments.length)))⟩

/-- `thm t`: the arguments fit, the hypotheses are proved, the independence conditions hold ⊢ the
conclusion is proved. -/
def thmRule (d : TheoremDecl) : Rule :=
  ⟨d.arguments.length,
    fits 0 d.arguments ++ d.hypotheses.map (fun h => .judg (pfP (patOf h))) ++ indep d.arguments,
    pfP (patOf d.conclusion)⟩

def cvReflRule (s : ℕ) : Rule := ⟨1, [.judg (tyP (pnum s) (pv 0))], cvP (pnum s) (pv 0) (pv 0)⟩

def cvSymmRule : Rule := ⟨3, [.judg (cvP (pv 0) (pv 1) (pv 2))], cvP (pv 0) (pv 2) (pv 1)⟩

def cvTransRule : Rule :=
  ⟨4, [.judg (cvP (pv 0) (pv 1) (pv 2)), .judg (cvP (pv 0) (pv 2) (pv 3))], cvP (pv 0) (pv 1) (pv 3)⟩

/-- `cvCong c`: left arguments `0 … n-1`, right arguments `n … 2n-1`. -/
def cvCongRule (c : ℕ) (d : TermDecl) : Rule :=
  let n := d.arguments.length
  ⟨n + n,
    fits 0 d.arguments ++ fits n d.arguments ++
      d.arguments.zipIdx.map (fun x => .judg (cvP (pnum x.1.sort) (pv x.2) (pv (n + x.2)))),
    cvP (pnum d.resultSort) (patOf (Preterm.applyArgs (.term c) (varsP 0 n)))
      (patOf (Preterm.applyArgs (.term c) (varsP n n)))⟩

/-- `unfold c`: arguments `0 … n-1`, dummies `n … n+m-1`. -/
def unfoldRule (c : ℕ) (d : TermDecl) (b : Definition.Body) : Rule :=
  let n := d.arguments.length
  ⟨n + b.dummies.length,
    fits 0 d.arguments ++ dummyFits n b.dummies ++
      [.judg (tyP (pnum d.resultSort) (patOf b.expression))] ++ fresh n b.dummies.length,
    cvP (pnum d.resultSort) (patOf (Preterm.applyArgs (.term c) (varsP 0 n))) (patOf b.expression)⟩

def convRule : Rule := ⟨3, [.judg (cvP (pv 0) (pv 1) (pv 2)), .judg (pfP (pv 1))], pfP (pv 2)⟩

/-- An MM0 environment. -/
structure MM0Env where
  sig : TermSignature
  defs : Definition.Signature
  thms : TheoremSignature

/-- Rule names. -/
inductive Name where
  | con (c : ℕ)
  | thm (t : ℕ)
  | cvRefl (s : ℕ)
  | cvSymm
  | cvTrans
  | cvCong (c : ℕ)
  | unfold (c : ℕ)
  | conv
  deriving DecidableEq, Repr

/-- **The rules of an MM0 environment.** -/
def rules (E : MM0Env) : Kernel2.Env Name
  | .con c => (E.sig c).map (conRule c)
  | .thm t => (E.thms t).map thmRule
  | .cvRefl s => some (cvReflRule s)
  | .cvSymm => some cvSymmRule
  | .cvTrans => some cvTransRule
  | .cvCong c => (E.sig c).map (cvCongRule c)
  | .unfold c =>
      match E.sig c, E.defs c with
      | some d, some b => some (unfoldRule c d b)
      | _, _ => none
  | .conv => some convRule

/-- The hypotheses the context gives: each bound variable's `bv` and `ty`, each regular
variable's `ty`. -/
def ctxHyps (Γ : Context) : List Tm :=
  Γ.zipIdx.flatMap fun x => match x.1 with
    | .bound s => [bvJ s (fvar x.2), tyJ s (fvar x.2)]
    | .regular s D => [tyJ s (fvar x.2 (depList D))]

end Mettapedia.Logic.TierZero.Adequacy.MM0
