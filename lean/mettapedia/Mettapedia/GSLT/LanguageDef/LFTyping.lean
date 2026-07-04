/-
# E2c-1: LF typing reference twin

This file is the Lean-side reference twin for the runnable lambda-Pi kernel's
typing fragment.  It keeps the E2c-1 boundary deliberately small:

* HHP-style LF rules: Type/Kind, Var, Con, App, Lam, Pi, and conversion.
* Explicit finite signatures, matching the executable kernel's finite lookup discipline.
* A fuel-bounded infer/check procedure mirroring the executable kernel shape.
* Soundness S1: if the checker accepts, the declarative relation has a derivation.

Reuse audit before implementation:
* The existing `LF*.lean` files in this directory prove parser/scope and engine
  correspondence facts, not lambda-Pi typing soundness.
* Dedukti is present as an OCaml/.dk checker and source comparison point, not a Lean proof.
* MetaCoq/MetaRocq provides a Coq/Rocq PCUIC verified checker, too large and not Lean-adaptable here.
* LeaTTa/Metatheory provide beta-reduction and confluence infrastructure, but E2c-1 avoids SN/confluence.
-/
import Mettapedia.GSLT.LanguageDef.LF

namespace Mettapedia.GSLT.LanguageDef.LFTyping

open Mettapedia.GSLT.LanguageDef.LF

abbrev Ctx := List Term

/-- Signature declarations: constants and transparent definitions. -/
inductive Decl where
  | const : String -> Term -> Decl
  | defn : String -> Term -> Term -> Decl
  deriving Repr, DecidableEq

abbrev Sig := List Decl

/-- HHP finite signature lookup: declaration type by first matching name. -/
def lookupType : Sig -> String -> Option Term
  | [], _ => none
  | .const n A :: rest, x => if x = n then some A else lookupType rest x
  | .defn n A _ :: rest, x => if x = n then some A else lookupType rest x

/-- Lean-side mirror of the executable MeTTa `(sigT c)` finite type map. -/
def sigT (sig : Sig) (x : String) : Option Term := lookupType sig x

/-- Transparent definition body lookup, used by fuel-bounded delta reduction. -/
def lookupBody : Sig -> String -> Option Term
  | [], _ => none
  | .const _ _ :: rest, x => lookupBody rest x
  | .defn n _ body :: rest, x => if x = n then some body else lookupBody rest x

/-- General de Bruijn lift: add `d` to every free index at or above cutoff `c`. -/
def lift (d c : Nat) : Term -> Term
  | .var k => .var (if k < c then k else k + d)
  | .srt s => .srt s
  | .con x => .con x
  | .pi A B => .pi (lift d c A) (lift d (c + 1) B)
  | .lam A b => .lam (lift d c A) (lift d (c + 1) b)
  | .app f a => .app (lift d c f) (lift d c a)

/-- Capture-avoiding de Bruijn substitution. -/
def subst (j : Nat) (s : Term) : Term -> Term
  | .var k =>
      if k = j then
        s
      else if j < k then
        .var (k - 1)
      else
        .var k
  | .srt u => .srt u
  | .con x => .con x
  | .pi A B => .pi (subst j s A) (subst (j + 1) (lift 1 0 s) B)
  | .lam A b => .lam (subst j s A) (subst (j + 1) (lift 1 0 s) b)
  | .app f a => .app (subst j s f) (subst j s a)

/-- Substitute an argument for the innermost variable in a dependent result type. -/
def subst0 (a body : Term) : Term := subst 0 a body

/-- Kernel-style context lookup: crossing binders lifts older declarations. -/
def ctxLookupAux : Nat -> Ctx -> Nat -> Option Term
  | _, [], _ => none
  | depth, A :: _, 0 => some (lift (depth + 1) 0 A)
  | depth, _ :: rest, i + 1 => ctxLookupAux (depth + 1) rest i

/-- Type of de Bruijn variable `i` in context `Gamma`, if present. -/
def ctxLookup (Gamma : Ctx) (i : Nat) : Option Term := ctxLookupAux 0 Gamma i

mutual
/-- Fuel-bounded normalizer: beta + transparent delta + structural descent. -/
def nf (sig : Sig) : Nat -> Term -> Term
  | 0, t => t
  | _fuel + 1, .srt s => .srt s
  | _fuel + 1, .var k => .var k
  | fuel + 1, .con x =>
      match lookupBody sig x with
      | some body => nf sig fuel body
      | none => .con x
  | fuel + 1, .pi A B => .pi (nf sig fuel A) (nf sig fuel B)
  | fuel + 1, .lam A b => .lam (nf sig fuel A) (nf sig fuel b)
  | fuel + 1, .app f a => nfApp sig fuel (nf sig fuel f) (nf sig fuel a)

/-- One normalized application step. -/
def nfApp (sig : Sig) : Nat -> Term -> Term -> Term
  | 0, f, a => .app f a
  | fuel + 1, .lam _ body, a => nf sig fuel (subst0 a body)
  | _, f, a => .app f a
end

/-- The checker's conversion test: bounded normalization followed by syntactic equality. -/
def convBool (sig : Sig) (fuel : Nat) (A B : Term) : Bool := nf sig fuel A == nf sig fuel B

mutual
/-- Algorithmic inference, fuel-bounded and Bad-as-`none`. -/
def infer : Nat -> Sig -> Ctx -> Term -> Option Term
  | 0, _, _, _ => none
  | _fuel + 1, _sig, _Gamma, .srt .type => some (.srt .kind)
  | _fuel + 1, _, _, .srt .kind => none
  | _fuel + 1, sig, _, .con x => sigT sig x
  | _fuel + 1, _, Gamma, .var i => ctxLookup Gamma i
  | fuel + 1, sig, Gamma, .pi A B =>
      match infer fuel sig Gamma A with
      | some (.srt .type) =>
          match infer fuel sig (A :: Gamma) B with
          | some (.srt s) => some (.srt s)
          | _ => none
      | _ => none
  | fuel + 1, sig, Gamma, .lam A body =>
      match infer fuel sig Gamma A with
      | some (.srt .type) =>
          match infer fuel sig (A :: Gamma) body with
          | some B => some (.pi A B)
          | none => none
      | _ => none
  | fuel + 1, sig, Gamma, .app f a =>
      match infer fuel sig Gamma f with
      | some (.pi A B) =>
          if check fuel sig Gamma a A then some (subst0 a B) else none
      | _ => none

/-- Algorithmic checking: infer, then bounded conversion. -/
def check : Nat -> Sig -> Ctx -> Term -> Term -> Bool
  | 0, _, _, _, _ => false
  | fuel + 1, sig, Gamma, t, A =>
      match infer fuel sig Gamma t with
      | some B => convBool sig fuel B A
      | none => false
end

/-- Common-reduct conversion induced by beta/delta reduction. -/
inductive Reduces (sig : Sig) : Term -> Term -> Prop where
  | refl {t} : Reduces sig t t
  | beta {A body a} : Reduces sig (.app (.lam A body) a) (subst0 a body)
  | delta {x body} : lookupBody sig x = some body -> Reduces sig (.con x) body
  | app {f f' a a'} :
      Reduces sig f f' -> Reduces sig a a' -> Reduces sig (.app f a) (.app f' a')
  | pi {A A' B B'} :
      Reduces sig A A' -> Reduces sig B B' -> Reduces sig (.pi A B) (.pi A' B')
  | lam {A A' b b'} :
      Reduces sig A A' -> Reduces sig b b' -> Reduces sig (.lam A b) (.lam A' b')
  | trans {a b c} : Reduces sig a b -> Reduces sig b c -> Reduces sig a c

/-- HHP-style beta conversion: two terms reduce to a common reduct. -/
inductive Conv (sig : Sig) : Term -> Term -> Prop where
  | common {A B C} : Reduces sig A C -> Reduces sig B C -> Conv sig A B

/-- Declarative LF typing relation.  Rule comments name the HHP-style rule family. -/
inductive HasType (sig : Sig) : Ctx -> Term -> Term -> Prop where
  /-- HHP Type/Kind sort rule. -/
  | srtType {Gamma} : HasType sig Gamma (.srt .type) (.srt .kind)
  /-- HHP Var rule. -/
  | var {Gamma i A} : ctxLookup Gamma i = some A -> HasType sig Gamma (.var i) A
  /-- HHP Con rule over an explicit finite signature. -/
  | con {Gamma x A} : sigT sig x = some A -> HasType sig Gamma (.con x) A
  /-- HHP Pi formation rule. -/
  | pi {Gamma A B s} :
      HasType sig Gamma A (.srt .type) ->
      HasType sig (A :: Gamma) B (.srt s) ->
      HasType sig Gamma (.pi A B) (.srt s)
  /-- HHP Lam introduction/checking rule. -/
  | lam {Gamma A body B} :
      HasType sig Gamma A (.srt .type) ->
      HasType sig (A :: Gamma) body B ->
      HasType sig Gamma (.lam A body) (.pi A B)
  /-- HHP App elimination rule. -/
  | app {Gamma f a A B} :
      HasType sig Gamma f (.pi A B) ->
      HasType sig Gamma a A ->
      HasType sig Gamma (.app f a) (subst0 a B)
  /-- HHP Conv rule, with conversion witnessed by a common beta/delta reduct. -/
  | conv {Gamma t A B} :
      HasType sig Gamma t A ->
      Conv sig A B ->
      HasType sig Gamma t B

theorem nf_nfApp_sound (sig : Sig) : ∀ fuel,
    (∀ t, Reduces sig t (nf sig fuel t)) ∧
    (∀ f a, Reduces sig (.app f a) (nfApp sig fuel f a)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro t
        simp [nf]
        exact Reduces.refl
      · intro f a
        simp [nfApp]
        exact Reduces.refl
  | succ fuel ih =>
      constructor
      · intro t
        cases t with
        | srt s =>
            cases s <;> simp [nf] <;> exact Reduces.refl
        | var k =>
            simp [nf]
            exact Reduces.refl
        | con x =>
            cases h : lookupBody sig x with
            | none =>
                simp [nf, h]
                exact Reduces.refl
            | some body =>
                simp [nf, h]
                exact Reduces.trans (Reduces.delta h) (ih.1 body)
        | pi A B =>
            simp [nf]
            exact Reduces.pi (ih.1 A) (ih.1 B)
        | lam A body =>
            simp [nf]
            exact Reduces.lam (ih.1 A) (ih.1 body)
        | app f a =>
            simp [nf]
            exact Reduces.trans
              (Reduces.app (ih.1 f) (ih.1 a))
              (ih.2 (nf sig fuel f) (nf sig fuel a))
      · intro f a
        cases f with
        | lam A body =>
            simp [nfApp]
            exact Reduces.trans Reduces.beta (ih.1 (subst0 a body))
        | srt s =>
            cases s <;> simp [nfApp] <;> exact Reduces.refl
        | con x =>
            simp [nfApp]
            exact Reduces.refl
        | var k =>
            simp [nfApp]
            exact Reduces.refl
        | pi A B =>
            simp [nfApp]
            exact Reduces.refl
        | app g b =>
            simp [nfApp]
            exact Reduces.refl

theorem nf_sound (sig : Sig) (fuel : Nat) (t : Term) : Reduces sig t (nf sig fuel t) :=
  (nf_nfApp_sound sig fuel).1 t

theorem nfApp_sound (sig : Sig) (fuel : Nat) (f a : Term) :
    Reduces sig (.app f a) (nfApp sig fuel f a) :=
  (nf_nfApp_sound sig fuel).2 f a

theorem convBool_sound {sig : Sig} {fuel : Nat} {A B : Term} :
    convBool sig fuel A B = true -> Conv sig A B := by
  intro h
  unfold convBool at h
  by_cases heq : nf sig fuel A = nf sig fuel B
  · apply Conv.common (nf_sound sig fuel A)
    rw [heq]
    exact nf_sound sig fuel B
  · simp [heq] at h

theorem infer_check_sound : ∀ fuel,
    (∀ sig Gamma t A, infer fuel sig Gamma t = some A -> HasType sig Gamma t A) ∧
    (∀ sig Gamma t A, check fuel sig Gamma t A = true -> HasType sig Gamma t A) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro sig Gamma t A h
        simp [infer] at h
      · intro sig Gamma t A h
        simp [check] at h
  | succ fuel ih =>
      constructor
      · intro sig Gamma t A h
        cases t with
        | srt s =>
            cases s
            · simp [infer] at h
              exact h ▸ HasType.srtType
            · simp [infer] at h
        | con x =>
            simp [infer] at h
            exact HasType.con h
        | var i =>
            simp [infer] at h
            exact HasType.var h
        | pi A0 B0 =>
            simp [infer] at h
            split at h <;> try contradiction
            rename_i hA
            split at h <;> try contradiction
            rename_i s hB
            cases h
            exact HasType.pi ((ih.1 sig Gamma A0 (.srt .type)) hA) ((ih.1 sig (A0 :: Gamma) B0 (.srt s)) hB)
        | lam A0 body =>
            simp [infer] at h
            split at h <;> try contradiction
            rename_i hA
            split at h <;> try contradiction
            rename_i B hB
            cases h
            exact HasType.lam ((ih.1 sig Gamma A0 (.srt .type)) hA) ((ih.1 sig (A0 :: Gamma) body B) hB)
        | app f a =>
            simp [infer] at h
            split at h <;> try contradiction
            rename_i A0 B hF
            split at h <;> try contradiction
            rename_i hArg
            cases h
            exact HasType.app ((ih.1 sig Gamma f (.pi A0 B)) hF) ((ih.2 sig Gamma a A0) hArg)
      · intro sig Gamma t A h
        simp [check] at h
        split at h <;> try contradiction
        rename_i B hInf
        exact HasType.conv ((ih.1 sig Gamma t B) hInf) (convBool_sound h)

/-- **S1 soundness.** If the fuel-bounded checker accepts, the declarative LF relation derives it. -/
theorem S1 {fuel : Nat} {sig : Sig} {Gamma : Ctx} {t A : Term} :
    check fuel sig Gamma t A = true -> HasType sig Gamma t A :=
  (infer_check_sound fuel).2 sig Gamma t A

/-! ## Corpus: small LF encodings used by the runnable kernel curriculum. -/

def cProp : Term := .con "prop"
def cNat : Term := .con "nat"
def cA : Term := .con "A"
def cB : Term := .con "B"
def cZ : Term := .con "z"

def prf (P : Term) : Term := .app (.con "prf") P
def imp (P Q : Term) : Term := .app (.app (.con "imp") P) Q
def eqn (x y : Term) : Term := .app (.app (.con "eqn") x) y

def impAB : Term := imp cA cB
def hImpAB : Term := .con "hImpAB"
def hA : Term := .con "hA"

def corpusSig : Sig :=
  [ .const "prop" (.srt .type)
  , .const "nat" (.srt .type)
  , .const "A" cProp
  , .const "B" cProp
  , .const "z" cNat
  , .const "prf" (.pi cProp (.srt .type))
  , .const "imp" (.pi cProp (.pi cProp cProp))
  , .const "eqn" (.pi cNat (.pi cNat (.srt .type)))
  , .const "rfl" (.pi cNat (eqn (.var 0) (.var 0)))
  , .const "hImpAB" (prf impAB)
  , .const "hA" (prf cA)
  , .const "mpAB" (.pi (prf impAB) (.pi (prf cA) (prf cB)))
  ]

/-- Corpus positive: LF lambda proof of `A -> A`, as `lambda h : prf A. h`. -/
def idProof : Term := .lam (prf cA) (.var 0)
def idProofTy : Term := .pi (prf cA) (prf cA)

/-- Corpus positive: modus ponens over explicit proof constants. -/
def mpProof : Term := .app (.app (.con "mpAB") hImpAB) hA
def mpProofTy : Term := prf cB

/-- Corpus positive: `rfl z : eqn z z`. -/
def rflZ : Term := .app (.con "rfl") cZ
def rflZTy : Term := eqn cZ cZ

/-- Corpus negative: `rfl z` does not prove the mismatched equality `eqn z A`. -/
def badRflTy : Term := eqn cZ cA

theorem corpus_id_check : check 32 corpusSig [] idProof idProofTy = true := by decide
theorem corpus_mp_check : check 32 corpusSig [] mpProof mpProofTy = true := by decide
theorem corpus_rfl_check : check 32 corpusSig [] rflZ rflZTy = true := by decide
theorem corpus_bad_rfl_rejects : check 32 corpusSig [] rflZ badRflTy = false := by decide

theorem corpus_id_sound : HasType corpusSig [] idProof idProofTy := S1 corpus_id_check
theorem corpus_mp_sound : HasType corpusSig [] mpProof mpProofTy := S1 corpus_mp_check
theorem corpus_rfl_sound : HasType corpusSig [] rflZ rflZTy := S1 corpus_rfl_check

#print axioms S1

end Mettapedia.GSLT.LanguageDef.LFTyping
