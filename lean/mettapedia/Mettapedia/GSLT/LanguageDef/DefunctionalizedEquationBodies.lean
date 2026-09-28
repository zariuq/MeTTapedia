import Mettapedia.GSLT.LanguageDef.ContinuationArenaBridge

/-!
# Equation bodies compiled to first-order resume frames

`CompiledContinuationAnswerProducer.Expr.lower` is a continuation-passing
lowering whose continuations are host functions, and `ContinuationArenaBridge`
executes the lowered bodies with those functions as return frames.  A native
engine cannot store a host function.  This module defunctionalizes the lowering
for first-order equation bodies (Reynolds; Danvy and Nielsen): every non-tail
call site of a body becomes a *resume site*, and a return frame is the site's
code together with the activation slots that code reads.

The source language is first-order and slot-addressed:

* an equation has `slots` activation slots; activation allocates a fresh
  logical variable for each slot in the branch store (`StoreAlgebra.fresh`);
* a body in administrative normal form returns a value, fails, binds the answer
  of a call or primitive to a pattern by unification, branches on a test, or
  ends in a last call;
* templates are open terms over the slots; instantiation reads only a
  template's support (`TemplateLanguage.inst_congr`).

A slot holds a term that may contain logical variables of the branch store, so
a captured slot is a reference whose meaning is supplied by the store the
resumed computation runs in: captured branch-store references are executable
here, not merely representable.

The meaning of a body is given in the existing source calculus
(`meaning` into `CompiledContinuationAnswerProducer.Expr`), and the compiled
machine is an instance of the generic shared-continuation `Program`.  The
central laws are:

* `decode_inspect`: decoding a first-order control is the source lowering of its
  code, instruction by instruction; a return frame decodes to the host
  continuation the lowering would have built (`decodeFrame`);
* `balance_compiledStep`: every compiled step conserves the delivered answers
  followed by the source denotation of the entire residual frontier;
* `compiled_prefix`: at every step the delivered answers are a prefix of the
  source denotation of the query, so the compiled machine never invents an
  answer, even before it finishes; `compiled_completed` gives the whole
  denotation once the frontier is exhausted.

Further results:

* `resumeTable` is generated from the program's bodies (one entry per non-tail
  call site, in program order; finite by construction), and
  `reachable_frames_in_table` shows every return frame of every reachable
  state is one of its sites, capturing exactly that site's support
  (`inspect_call_site`);
* `norm_eval` normalizes nested source bodies (`let` over calls, conditionals
  and other `let`s) into this form, keeping every answer in order and with
  multiplicity; `source_compiled_exact` states the prefix and completion laws
  against the nested source program's own semantics;
* `closeOver_exact`: a return frame is closure conversion of its
  continuation, exact because captures are the code's support;
  `reconstruct_dropped` shows a slot outside the captures is not recovered;
* `compiled_arena_prefix`: the shared-arena realization of `SharedContinuation`
  inherits the prefix law.

The results are generic in the unifier, fresh-variable supply, primitives and
tests, so HE and PeTTa policies are distinct instantiations of one theorem.

Boundaries.  The theorems start at slot-addressed source bodies over abstract
templates.  A front end that turns calls nested inside data (for example an
arithmetic operand inside a constructor) into temporary slots produces answers
that agree after resolution through the store; that step, and the lexer,
parser and ABT lowering of textual MeTTa, are not covered here.  A source
meaning is any solution of the unfolding equations (`Denotation`,
`SProgram.Solves`), as in the continuation-body calculus.  Duplicating a
continuation over a conditional (`normBind`) costs code size, not meaning; a
native compiler would share it through a join point.  This is a model of the
compiler and machine, not a verified translation of CeTTa's C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies

open CompiledContinuationAnswerProducer
open Mettapedia.Machines.SharedContinuation

/-- Open code over `k` activation slots whose instantiation reads only its
support. -/
structure TemplateLanguage (Term : Type) where
  Tmpl : Nat → Type
  inst : {k : Nat} → Tmpl k → (Fin k → Term) → Term
  support : {k : Nat} → Tmpl k → Finset (Fin k)
  inst_congr : ∀ {k : Nat} (t : Tmpl k) (frame frame' : Fin k → Term),
    (∀ i ∈ support t, frame i = frame' i) → inst t frame = inst t frame'

/-- The branch store: unification, fresh activation slots, deterministic
primitives and tests.  `none` from a primitive or a test is failure. -/
structure StoreAlgebra (Term Store Op : Type) where
  unify : Term → Term → Store → Option Store
  fresh : Store → (k : Nat) → (Fin k → Term) × Store
  prim : Op → List Term → Store → Option Term
  test : Op → List Term → Store → Option Bool

variable {Term Store Rel Op : Type}

/-- First-order equation bodies in administrative normal form. -/
inductive Code (L : TemplateLanguage Term) (Rel Op : Type) (k : Nat) : Type where
  | ret (value : L.Tmpl k)
  | fail
  | letCall (pattern : L.Tmpl k) (rel : Rel) (args : List (L.Tmpl k))
      (body : Code L Rel Op k)
  | letPrim (pattern : L.Tmpl k) (op : Op) (args : List (L.Tmpl k))
      (body : Code L Rel Op k)
  | bind (pattern value : L.Tmpl k) (body : Code L Rel Op k)
  | ite (op : Op) (args : List (L.Tmpl k)) (yes no : Code L Rel Op k)
  | tail (rel : Rel) (args : List (L.Tmpl k))

section Support

variable (L : TemplateLanguage Term)

def argsSupport {k : Nat} : List (L.Tmpl k) → Finset (Fin k)
  | [] => ∅
  | t :: rest => L.support t ∪ argsSupport rest

def instArgs {k : Nat} (args : List (L.Tmpl k)) (frame : Fin k → Term) : List Term :=
  args.map fun t => L.inst t frame

theorem instArgs_congr {k : Nat} (args : List (L.Tmpl k)) (frame frame' : Fin k → Term)
    (agree : ∀ i ∈ argsSupport L args, frame i = frame' i) :
    instArgs L args frame = instArgs L args frame' := by
  induction args with
  | nil => rfl
  | cons t rest ih =>
      simp only [instArgs, List.map_cons, List.cons.injEq]
      exact ⟨L.inst_congr t frame frame' fun i hi =>
          agree i (by simp [argsSupport, hi]),
        ih fun i hi => agree i (by simp [argsSupport, hi])⟩

/-- The slots a body reads. -/
def Code.support {k : Nat} : Code L Rel Op k → Finset (Fin k)
  | .ret t => L.support t
  | .fail => ∅
  | .letCall p _ args body => L.support p ∪ argsSupport L args ∪ body.support
  | .letPrim p _ args body => L.support p ∪ argsSupport L args ∪ body.support
  | .bind p v body => L.support p ∪ L.support v ∪ body.support
  | .ite _ args yes no => argsSupport L args ∪ yes.support ∪ no.support
  | .tail _ args => argsSupport L args

/-- The slots a return frame must keep: its pattern and its continuation. -/
def frameSupport {k : Nat} (pattern : L.Tmpl k) (body : Code L Rel Op k) : Finset (Fin k) :=
  L.support pattern ∪ body.support

end Support

abbrev Call (Term Store Rel : Type) := Rel × List Term × Store
abbrev Answer (Term Store : Type) := Term × Store

section Meaning

variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op) [Inhabited Term]

/-- The source meaning of a body under an activation frame and branch store, in
the existing continuation-body source calculus.  A call's operand is the empty
computation `value (default, σ)`; its state ignores it. -/
def meaning {k : Nat} (frame : Fin k → Term) :
    Store → Code L Rel Op k → Expr (Call Term Store Rel) (Answer Term Store)
  | σ, .ret t => .value (L.inst t frame, σ)
  | _, .fail => .zero
  | σ, .letCall p rel args body =>
      .bind (.call (.value (default, σ)) fun _ => (rel, instArgs L args frame, σ))
        (fun a => (S.unify (L.inst p frame) a.1 a.2).isSome)
        (fun a => match S.unify (L.inst p frame) a.1 a.2 with
          | some σ' => meaning frame σ' body
          | none => .zero)
  | σ, .letPrim p op args body =>
      match S.prim op (instArgs L args frame) σ with
      | none => .zero
      | some v =>
          match S.unify (L.inst p frame) v σ with
          | some σ' => meaning frame σ' body
          | none => .zero
  | σ, .bind p v body =>
      match S.unify (L.inst p frame) (L.inst v frame) σ with
      | some σ' => meaning frame σ' body
      | none => .zero
  | σ, .ite op args yes no =>
      match S.test op (instArgs L args frame) σ with
      | some true => meaning frame σ yes
      | some false => meaning frame σ no
      | none => .zero
  | σ, .tail rel args => .call (.value (default, σ)) fun _ => (rel, instArgs L args frame, σ)

theorem meaning_congr {k : Nat} (code : Code L Rel Op k) (frame frame' : Fin k → Term)
    (agree : ∀ i ∈ code.support L, frame i = frame' i) (σ : Store) :
    meaning L S frame σ code = meaning L S frame' σ code := by
  induction code generalizing σ with
  | ret t =>
      simp only [meaning, L.inst_congr t frame frame' agree]
  | fail => rfl
  | letCall p rel args body ih =>
      have hp : L.inst p frame = L.inst p frame' :=
        L.inst_congr p frame frame' fun i hi => agree i (by simp [Code.support, hi])
      have ha : instArgs L args frame = instArgs L args frame' :=
        instArgs_congr L args frame frame' fun i hi => agree i (by simp [Code.support, hi])
      have hb : ∀ σ', meaning L S frame σ' body = meaning L S frame' σ' body :=
        ih (fun i hi => agree i (by simp [Code.support, hi]))
      simp only [meaning, hp, ha, hb]
  | letPrim p op args body ih =>
      have hp : L.inst p frame = L.inst p frame' :=
        L.inst_congr p frame frame' fun i hi => agree i (by simp [Code.support, hi])
      have ha : instArgs L args frame = instArgs L args frame' :=
        instArgs_congr L args frame frame' fun i hi => agree i (by simp [Code.support, hi])
      have hb : ∀ σ', meaning L S frame σ' body = meaning L S frame' σ' body :=
        ih (fun i hi => agree i (by simp [Code.support, hi]))
      simp only [meaning, hp, ha, hb]
  | bind p v body ih =>
      have hp : L.inst p frame = L.inst p frame' :=
        L.inst_congr p frame frame' fun i hi => agree i (by simp [Code.support, hi])
      have hv : L.inst v frame = L.inst v frame' :=
        L.inst_congr v frame frame' fun i hi => agree i (by simp [Code.support, hi])
      have hb : ∀ σ', meaning L S frame σ' body = meaning L S frame' σ' body :=
        ih (fun i hi => agree i (by simp [Code.support, hi]))
      simp only [meaning, hp, hv, hb]
  | ite op args yes no ihYes ihNo =>
      have ha : instArgs L args frame = instArgs L args frame' :=
        instArgs_congr L args frame frame' fun i hi => agree i (by simp [Code.support, hi])
      have hy : ∀ σ', meaning L S frame σ' yes = meaning L S frame' σ' yes :=
        ihYes (fun i hi => agree i (by simp [Code.support, hi]))
      have hn : ∀ σ', meaning L S frame σ' no = meaning L S frame' σ' no :=
        ihNo (fun i hi => agree i (by simp [Code.support, hi]))
      simp only [meaning, ha, hy, hn]
  | tail rel args =>
      have ha : instArgs L args frame = instArgs L args frame' :=
        instArgs_congr L args frame frame' fun i hi => agree i (by simp [Code.support, hi])
      simp only [meaning, ha]

end Meaning

/-! ### Source bodies with nested `let`, and their normalization -/

/-- Source bodies: `let` may bind the answers of any body, including another
`let` or a conditional.  Calls in tail position are last calls.  A primitive
is bound by a pattern (a tail primitive is written as a binding of a slot). -/
inductive Source (L : TemplateLanguage Term) (Rel Op : Type) (k : Nat) : Type where
  | ret (value : L.Tmpl k)
  | fail
  | call (rel : Rel) (args : List (L.Tmpl k))
  | letPrim (pattern : L.Tmpl k) (op : Op) (args : List (L.Tmpl k)) (body : Source L Rel Op k)
  | ite (op : Op) (args : List (L.Tmpl k)) (yes no : Source L Rel Op k)
  | letE (pattern : L.Tmpl k) (bound body : Source L Rel Op k)

section Normalization

variable (L : TemplateLanguage Term)

/-- Bind the answers of a source body to a pattern, then continue with code.
Nested `let`s flatten (associativity of sequencing); a conditional distributes
the continuation over its branches (the continuation is duplicated, a code-size
cost, not a semantic one); calls become resume sites.  All variables are frame
slots, so flattening needs no renaming. -/
def normBind {k : Nat} : Source L Rel Op k → L.Tmpl k → Code L Rel Op k → Code L Rel Op k
  | .ret t, p, c => .bind p t c
  | .fail, _, _ => .fail
  | .call rel args, p, c => .letCall p rel args c
  | .letPrim q op args b, p, c => .letPrim q op args (normBind b p c)
  | .ite op args yes no, p, c => .ite op args (normBind yes p c) (normBind no p c)
  | .letE q bound body, p, c => normBind bound q (normBind body p c)

/-- Normalize a source body into administrative normal form. -/
def norm {k : Nat} : Source L Rel Op k → Code L Rel Op k
  | .ret t => .ret t
  | .fail => .fail
  | .call rel args => .tail rel args
  | .letPrim q op args b => .letPrim q op args (norm b)
  | .ite op args yes no => .ite op args (norm yes) (norm no)
  | .letE q bound body => normBind L bound q (norm body)

variable (S : StoreAlgebra Term Store Op) [Inhabited Term]

/-- The source meaning of a nested body in the existing source calculus. -/
def smeaning {k : Nat} (frame : Fin k → Term) :
    Store → Source L Rel Op k → Expr (Call Term Store Rel) (Answer Term Store)
  | σ, .ret t => .value (L.inst t frame, σ)
  | _, .fail => .zero
  | σ, .call rel args => .call (.value (default, σ)) fun _ => (rel, instArgs L args frame, σ)
  | σ, .letPrim p op args body =>
      match S.prim op (instArgs L args frame) σ with
      | none => .zero
      | some v =>
          match S.unify (L.inst p frame) v σ with
          | some σ' => smeaning frame σ' body
          | none => .zero
  | σ, .ite op args yes no =>
      match S.test op (instArgs L args frame) σ with
      | some true => smeaning frame σ yes
      | some false => smeaning frame σ no
      | none => .zero
  | σ, .letE p bound body =>
      .bind (smeaning frame σ bound)
        (fun a => (S.unify (L.inst p frame) a.1 a.2).isSome)
        (fun a => match S.unify (L.inst p frame) a.1 a.2 with
          | some σ' => smeaning frame σ' body
          | none => .zero)

/-- Binding the answers of a normalized body is sequencing in the source
calculus: answers, their order and multiplicity are kept. -/
theorem normBind_eval {k : Nat} (value : Call Term Store Rel → List (Answer Term Store))
    (frame : Fin k → Term) (s : Source L Rel Op k) (p : L.Tmpl k) (c : Code L Rel Op k)
    (σ : Store) :
    (meaning L S frame σ (normBind L s p c)).eval value =
      ((smeaning L S frame σ s).eval value).flatMap fun a =>
        match S.unify (L.inst p frame) a.1 a.2 with
        | some σ' => (meaning L S frame σ' c).eval value
        | none => [] := by
  induction s generalizing σ p c with
  | ret t =>
      simp only [normBind, meaning, smeaning, Expr.eval, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      cases hu : S.unify (L.inst p frame) (L.inst t frame) σ <;> simp [Expr.eval]
  | fail => simp [normBind, meaning, smeaning, Expr.eval]
  | call rel args =>
      simp only [normBind, meaning, smeaning, Expr.eval, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      congr 1
      funext a
      cases hu : S.unify (L.inst p frame) a.1 a.2 <;> simp
  | letPrim q op args b ih =>
      simp only [normBind, meaning, smeaning]
      cases hv : S.prim op (instArgs L args frame) σ with
      | none => simp [Expr.eval]
      | some v =>
          cases hu : S.unify (L.inst q frame) v σ with
          | none => simp [hu, Expr.eval]
          | some σ' => simpa only [hu] using ih p c σ'
  | ite op args yes no ihYes ihNo =>
      simp only [normBind, meaning, smeaning]
      cases ht : S.test op (instArgs L args frame) σ with
      | none => simp [Expr.eval]
      | some b =>
          cases b with
          | true => simpa only [ht] using ihYes p c σ
          | false => simpa only [ht] using ihNo p c σ
  | letE q bound body ihBound ihBody =>
      simp only [normBind, smeaning, Expr.eval]
      rw [ihBound q (normBind L body p c) σ, List.flatMap_assoc]
      congr 1
      funext a
      cases hu : S.unify (L.inst q frame) a.1 a.2 with
      | none => simp
      | some σ' => simp [ihBody p c σ']

/-- Normalization preserves every answer of a source body, in order and with
multiplicity. -/
theorem norm_eval {k : Nat} (value : Call Term Store Rel → List (Answer Term Store))
    (frame : Fin k → Term) (s : Source L Rel Op k) (σ : Store) :
    (meaning L S frame σ (norm L s)).eval value = (smeaning L S frame σ s).eval value := by
  induction s generalizing σ with
  | ret t => rfl
  | fail => rfl
  | call rel args => rfl
  | letPrim q op args b ih =>
      simp only [norm, meaning, smeaning]
      cases hv : S.prim op (instArgs L args frame) σ with
      | none => rfl
      | some v =>
          cases hu : S.unify (L.inst q frame) v σ with
          | none => simp [hu]
          | some σ' => simpa only [hu] using ih σ'
  | ite op args yes no ihYes ihNo =>
      simp only [norm, meaning, smeaning]
      cases ht : S.test op (instArgs L args frame) σ with
      | none => simp
      | some b => cases b with
        | true => simpa only [ht] using ihYes σ
        | false => simpa only [ht] using ihNo σ
  | letE q bound body ihBound ihBody =>
      simp only [norm, smeaning, Expr.eval]
      rw [normBind_eval]
      congr 1
      funext a
      cases hu : S.unify (L.inst q frame) a.1 a.2 with
      | none => simp
      | some σ' => simp [ihBody σ']

end Normalization

/-- A source equation: its slot count, head parameters and body. -/
structure Equation (L : TemplateLanguage Term) (Rel Op : Type) where
  slots : Nat
  params : List (L.Tmpl slots)
  rhs : Code L Rel Op slots

/-- A source program: its equations in authored order. -/
abbrev EqProgram (L : TemplateLanguage Term) (Rel Op : Type) := List (Rel × Equation L Rel Op)

/-- A relation's equations, in authored order. -/
def EqProgram.equations [DecidableEq Rel] {L : TemplateLanguage Term}
    (P : EqProgram L Rel Op) (rel : Rel) : List (Equation L Rel Op) :=
  (P.filter fun entry => entry.1 = rel).map Prod.snd

section Machines

variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)

def unifyAll : List Term → List Term → Store → Option Store
  | [], [], σ => some σ
  | p :: ps, a :: as, σ => (S.unify p a σ).bind (unifyAll ps as)
  | _, _, _ => none

/-- A successful activation of an equation: its fresh frame, the store after
head unification, and its body. -/
structure Activation (L : TemplateLanguage Term) (Rel Op Store : Type) where
  slots : Nat
  frame : Fin slots → Term
  store : Store
  code : Code L Rel Op slots

/-- Every equation of the called relation, tried in authored order; those whose
head unifies with the call's arguments become activations. -/
def activate [DecidableEq Rel] (P : EqProgram L Rel Op) :
    Call Term Store Rel → List (Activation L Rel Op Store)
  | (rel, args, σ) =>
      (P.equations rel).filterMap fun e =>
        let fresh := S.fresh σ e.slots
        (unifyAll S (instArgs L e.params fresh.1) args fresh.2).map fun σ' =>
          ⟨e.slots, fresh.1, σ', e.rhs⟩

variable [Inhabited Term] [DecidableEq Rel]

/-- The source machine: each call's alternatives are its activations' bodies,
lowered by the existing continuation-passing lowering. -/
def sourceMachine (P : EqProgram L Rel Op) :
    Machine (Call Term Store Rel) (Answer Term Store) where
  branches c := (activate L S P c).map fun a =>
    (meaning L S a.frame a.store a.code).lower .answer

/-! ### The compiled, first-order machine -/

/-- A first-order control: code, the activation frame it reads, and the branch
store it runs in. -/
structure Control (L : TemplateLanguage Term) (Rel Op Store : Type) where
  slots : Nat
  code : Code L Rel Op slots
  frame : Fin slots → Term
  store : Store

/-- A first-order return frame: a resume site (the pattern the callee's answer
must match and the code that continues) and the captured slots.  `captured` is
defined exactly on the site's support; it holds no host continuation. -/
structure ReturnFrame (L : TemplateLanguage Term) (Rel Op : Type) where
  slots : Nat
  pattern : L.Tmpl slots
  body : Code L Rel Op slots
  captured : Fin slots → Option Term

def capture {k : Nat} (frame : Fin k → Term) (keep : Finset (Fin k)) : Fin k → Option Term :=
  fun i => if i ∈ keep then some (frame i) else none

def reconstruct {k : Nat} (captured : Fin k → Option Term) : Fin k → Term :=
  fun i => (captured i).getD default

theorem reconstruct_capture {k : Nat} (frame : Fin k → Term) (keep : Finset (Fin k))
    (i : Fin k) (kept : i ∈ keep) : reconstruct (capture frame keep) i = frame i := by
  simp [reconstruct, capture, kept]

/-- The next control boundary of a first-order control.  Deterministic local
work (primitives, pattern binding of their results, tests) runs here. -/
def inspectCode {k : Nat} (frame : Fin k → Term) :
    Store → Code L Rel Op k →
      Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)
  | σ, .ret t => .ret (L.inst t frame, σ)
  | _, .fail => .fail
  | σ, .letCall p rel args body =>
      .call (rel, instArgs L args frame, σ)
        ⟨k, p, body, capture frame (frameSupport L p body)⟩
  | σ, .letPrim p op args body =>
      match S.prim op (instArgs L args frame) σ with
      | none => .fail
      | some v =>
          match S.unify (L.inst p frame) v σ with
          | some σ' => inspectCode frame σ' body
          | none => .fail
  | σ, .bind p v body =>
      match S.unify (L.inst p frame) (L.inst v frame) σ with
      | some σ' => inspectCode frame σ' body
      | none => .fail
  | σ, .ite op args yes no =>
      match S.test op (instArgs L args frame) σ with
      | some true => inspectCode frame σ yes
      | some false => inspectCode frame σ no
      | none => .fail
  | σ, .tail rel args => .tail (rel, instArgs L args frame, σ)

/-- Resuming a return frame with a callee answer: rebuild the frame from the
captured slots, bind the pattern in the answer's store, continue. -/
def resumeControl (f : ReturnFrame L Rel Op) (a : Answer Term Store) :
    Control L Rel Op Store :=
  match S.unify (L.inst f.pattern (reconstruct f.captured)) a.1 a.2 with
  | some σ' => ⟨f.slots, f.body, reconstruct f.captured, σ'⟩
  | none => ⟨f.slots, .fail, reconstruct f.captured, a.2⟩

/-- The compiled machine, as an instance of the generic shared-continuation
program. -/
def compiled (P : EqProgram L Rel Op) :
    Program Unit (Control L Rel Op Store) (Call Term Store Rel)
      (ReturnFrame L Rel Op) (Answer Term Store) where
  inspect c := inspectCode L S c.frame c.store c.code
  branches _ c := (activate L S P c).map fun a => ((), ⟨a.slots, a.code, a.frame, a.store⟩)
  resume _ f a := ((), resumeControl L S f a)

/-! ### Decoding into the source lowering -/

def decodeControl (c : Control L Rel Op Store) :
    Body (Call Term Store Rel) (Answer Term Store) :=
  (meaning L S c.frame c.store c.code).lower .answer

/-- A return frame denotes the host continuation the lowering would build. -/
def decodeFrame (f : ReturnFrame L Rel Op) :
    Answer Term Store → Body (Call Term Store Rel) (Answer Term Store) :=
  fun a => decodeControl L S (resumeControl L S f a)

def instructionBody :
    Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store) →
      Body (Call Term Store Rel) (Answer Term Store)
  | .ret a => .answer a
  | .fail => .fail
  | .call c f => .call c (decodeFrame L S f)
  | .tail c => .call c .answer

omit [DecidableEq Rel] in
/-- Decoding a first-order control is the source lowering of its code, and the
compiled frame decodes to the continuation the lowering builds. -/
theorem decode_inspect {k : Nat} (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    decodeControl L S ⟨k, code, frame, σ⟩ = instructionBody L S (inspectCode L S frame σ code) := by
  induction code generalizing σ with
  | ret t => simp [decodeControl, meaning, inspectCode, instructionBody, Expr.lower]
  | fail => simp [decodeControl, meaning, inspectCode, instructionBody, Expr.lower]
  | letCall p rel args body ih =>
      simp only [decodeControl, meaning, inspectCode, instructionBody, Expr.lower]
      congr 1
      funext a
      have hp : L.inst p (reconstruct (capture frame (frameSupport L p body))) = L.inst p frame :=
        L.inst_congr p _ _ fun i hi =>
          reconstruct_capture frame _ i (by simp [frameSupport, hi])
      have hb : ∀ σ', meaning L S (reconstruct (capture frame (frameSupport L p body))) σ' body =
          meaning L S frame σ' body :=
        meaning_congr L S body _ _ fun i hi =>
          reconstruct_capture frame _ i (by simp [frameSupport, hi])
      simp only [decodeFrame, resumeControl, hp]
      cases h : S.unify (L.inst p frame) a.1 a.2 with
      | none => simp [decodeControl, meaning, Expr.lower]
      | some σ' => simp [decodeControl, hb]
  | letPrim p op args body ih =>
      simp only [decodeControl, meaning, inspectCode]
      cases hv : S.prim op (instArgs L args frame) σ with
      | none => simp [Expr.lower, instructionBody]
      | some v =>
          cases hu : S.unify (L.inst p frame) v σ with
          | none => simp [hu, Expr.lower, instructionBody]
          | some σ' =>
              simp only [hu]
              simpa [decodeControl] using ih σ'
  | bind p v body ih =>
      simp only [decodeControl, meaning, inspectCode]
      cases hu : S.unify (L.inst p frame) (L.inst v frame) σ with
      | none => simp [Expr.lower, instructionBody]
      | some σ' => simpa [decodeControl] using ih σ'
  | ite op args yes no ihYes ihNo =>
      simp only [decodeControl, meaning, inspectCode]
      cases ht : S.test op (instArgs L args frame) σ with
      | none => simp [Expr.lower, instructionBody]
      | some b =>
          cases b with
          | true => simpa [decodeControl] using ihYes σ
          | false => simpa [decodeControl] using ihNo σ
  | tail rel args => simp [decodeControl, meaning, inspectCode, instructionBody, Expr.lower]

def decodeTask (t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)) :
    Task Unit (Body (Call Term Store Rel) (Answer Term Store))
      (Answer Term Store → Body (Call Term Store Rel) (Answer Term Store)) :=
  ⟨(), decodeControl L S t.control, t.returns.map (decodeFrame L S)⟩

def decodeState (s : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)) :
    ContinuationArenaBridge.Reference (Call Term Store Rel) (Answer Term Store) :=
  ⟨s.frontier.map (decodeTask L S), s.emitted⟩

/-! ### Conservation and no invented answers -/

omit [Inhabited Term] [DecidableEq Rel] in
theorem frontierValue_map_run {α : Type} (value : Call Term Store Rel → List (Answer Term Store))
    (xs : List α) (h : α → Body (Call Term Store Rel) (Answer Term Store))
    (pending : List (Answer Term Store → Body (Call Term Store Rel) (Answer Term Store))) :
    frontierValue value (xs.map fun a => .run (h a) pending) =
      xs.flatMap fun a => ((h a).answers value).flatMap (pendingAnswers value pending) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [frontierValue, ih]

open ContinuationArenaBridge in
theorem balance_compiledStep (P : EqProgram L Rel Op)
    (denotation : Denotation (sourceMachine L S P))
    (s : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)) :
    balance denotation.value (decodeState L S (step (compiled L S P) s)) =
      balance denotation.value (decodeState L S s) := by
  rcases s with ⟨frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      rcases task with ⟨context, control, returns⟩
      rcases control with ⟨k, code, frame, σ⟩
      have hdec := decode_inspect L S code frame σ
      cases instr : inspectCode L S frame σ code with
      | ret a =>
          rw [instr] at hdec
          cases returns with
          | nil =>
              simp [step, compiled, instr, decodeState, decodeTask, balance, residuals,
                frontierValue, hdec, instructionBody, Body.answers, pendingAnswers,
                List.append_assoc]
          | cons f pending =>
              simp [step, compiled, instr, decodeState, decodeTask, balance, residuals,
                frontierValue, hdec, instructionBody, Body.answers, pendingAnswers, decodeFrame]
      | fail =>
          rw [instr] at hdec
          simp [step, compiled, instr, decodeState, decodeTask, balance, residuals,
            frontierValue, hdec, instructionBody, Body.answers]
      | call c f =>
          rw [instr] at hdec
          simp only [step, compiled, instr, decodeState, decodeTask, balance, residuals,
            List.map_cons, List.map_append, List.map_map, Function.comp_def]
          rw [hdec, frontierValue_append, frontierValue_map_run]
          simp [frontierValue, instructionBody, Body.answers, denotation.unfold c,
            sourceMachine, List.flatMap_assoc, pendingAnswers, List.flatMap_map, decodeControl]
      | tail c =>
          rw [instr] at hdec
          simp only [step, compiled, instr, decodeState, decodeTask, balance, residuals,
            List.map_cons, List.map_append, List.map_map, Function.comp_def]
          rw [hdec, frontierValue_append, frontierValue_map_run]
          simp [frontierValue, instructionBody, Body.answers, denotation.unfold c,
            sourceMachine, List.flatMap_assoc, List.flatMap_map, decodeControl]

open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats) in
open ContinuationArenaBridge in
theorem balance_compiledSteps (P : EqProgram L Rel Op)
    (denotation : Denotation (sourceMachine L S P)) (count : Nat)
    (s : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)) :
    balance denotation.value (decodeState L S (repeats (step (compiled L S P)) count s)) =
      balance denotation.value (decodeState L S s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => rw [repeats, ih, balance_compiledStep]

/-- The initial state of a query: a last call. -/
def initial (P : EqProgram L Rel Op) (c : Call Term Store Rel) :
    State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store) :=
  ⟨(activate L S P c).map fun a => ⟨(), ⟨a.slots, a.code, a.frame, a.store⟩, []⟩, []⟩

open ContinuationArenaBridge in
theorem balance_initial (P : EqProgram L Rel Op) (denotation : Denotation (sourceMachine L S P))
    (c : Call Term Store Rel) :
    balance denotation.value (decodeState L S (initial L S P c)) = denotation.value c := by
  simp only [initial, decodeState, decodeTask, balance, residuals, List.map_map,
    Function.comp_def, List.map_nil, List.nil_append]
  rw [frontierValue_map_run, denotation.unfold c]
  simp [sourceMachine, pendingAnswers, decodeControl, List.flatMap_map]

open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats) in
open ContinuationArenaBridge in
/-- At every step the delivered answers are followed by exactly the source
denotation of the residual frontier: together they are the query's denotation. -/
theorem compiled_conserves (P : EqProgram L Rel Op) (denotation : Denotation (sourceMachine L S P))
    (c : Call Term Store Rel) (count : Nat) :
    balance denotation.value (decodeState L S (repeats (step (compiled L S P)) count (initial L S P c))) =
      denotation.value c := by
  rw [balance_compiledSteps, balance_initial]

open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats) in
/-- No invented answers: at every step, including before completion, the
answers the compiled machine has delivered are a prefix of the source
denotation, in order and with multiplicity. -/
theorem compiled_prefix (P : EqProgram L Rel Op) (denotation : Denotation (sourceMachine L S P))
    (c : Call Term Store Rel) (count : Nat) :
    ((repeats (step (compiled L S P)) count (initial L S P c)).emitted.map Prod.snd) <+:
      denotation.value c := by
  have conserved := compiled_conserves L S P denotation c count
  simp only [ContinuationArenaBridge.balance, decodeState] at conserved
  exact ⟨_, conserved⟩

open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats) in
/-- Once the frontier is exhausted, the delivered answers are exactly the
source denotation.  Fuel exhaustion is not a premise. -/
theorem compiled_completed (P : EqProgram L Rel Op) (denotation : Denotation (sourceMachine L S P))
    (c : Call Term Store Rel) (count : Nat)
    (exhausted : (repeats (step (compiled L S P)) count (initial L S P c)).frontier = []) :
    (repeats (step (compiled L S P)) count (initial L S P c)).emitted.map Prod.snd =
      denotation.value c := by
  have conserved := compiled_conserves L S P denotation c count
  simpa [ContinuationArenaBridge.balance, decodeState, exhausted, ContinuationArenaBridge.residuals,
    frontierValue] using conserved

open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats) in
/-- The same guarantee for the shared-arena realization: return frames stored
once in an arena, roots on the frontier, decoded only for observation. -/
theorem compiled_arena_prefix (P : EqProgram L Rel Op) (denotation : Denotation (sourceMachine L S P))
    (c : Call Term Store Rel) (count : Nat) :
    ((repeats (checkedStep (compiled L S P)) count (encode (initial L S P c))).1.decode.emitted.map
        Prod.snd) <+: denotation.value c := by
  rw [Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching.decode_steps, decode_encode]
  exact compiled_prefix L S P denotation c count

/-! ### Closures -/

/-- A closure: code together with only the frame slots it reads.  A return
frame is the closure of a continuation; a first-class function value would be
the closure of its body. -/
structure Closure (L : TemplateLanguage Term) (Rel Op : Type) where
  slots : Nat
  code : Code L Rel Op slots
  captured : Fin slots → Option Term

def closeOver {k : Nat} (code : Code L Rel Op k) (frame : Fin k → Term) : Closure L Rel Op :=
  ⟨k, code, capture frame (code.support L)⟩

omit [DecidableEq Rel] in
/-- Closure conversion restricted to the support is exact: the closure's
rebuilt frame gives the code the same meaning as the full activation frame,
in every store.  Slots outside the support are neither kept nor needed. -/
theorem closeOver_exact {k : Nat} (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    meaning L S (reconstruct (closeOver L code frame).captured) σ code = meaning L S frame σ code :=
  meaning_congr L S code _ _ (fun i hi => reconstruct_capture frame _ i hi) σ

omit [DecidableEq Rel] in
/-- Keeping fewer slots than the support is not closure conversion: a slot the
code reads is rebuilt from the default value. -/
theorem reconstruct_dropped {k : Nat} (frame : Fin k → Term) (keep : Finset (Fin k))
    (i : Fin k) (dropped : i ∉ keep) : reconstruct (capture frame keep) i = default := by
  simp [reconstruct, capture, dropped]

/-! ### From nested source programs -/

/-- A source equation whose body may nest `let`s. -/
structure SEquation (L : TemplateLanguage Term) (Rel Op : Type) where
  slots : Nat
  params : List (L.Tmpl slots)
  rhs : Source L Rel Op slots

abbrev SProgram (L : TemplateLanguage Term) (Rel Op : Type) := List (Rel × SEquation L Rel Op)

/-- Normalize every equation body; heads are unchanged. -/
def SProgram.normalize (P : SProgram L Rel Op) : EqProgram L Rel Op :=
  P.map fun e => (e.1, ⟨e.2.slots, e.2.params, norm L e.2.rhs⟩)

/-- A source activation: fresh frame, store after head unification, source body. -/
structure SActivation (L : TemplateLanguage Term) (Rel Op Store : Type) where
  slots : Nat
  frame : Fin slots → Term
  store : Store
  code : Source L Rel Op slots

def activateS (P : SProgram L Rel Op) : Call Term Store Rel → List (SActivation L Rel Op Store)
  | (rel, args, σ) =>
      ((P.filter fun entry => entry.1 = rel).map Prod.snd).filterMap fun e =>
        let fresh := S.fresh σ e.slots
        (unifyAll S (instArgs L e.params fresh.1) args fresh.2).map fun σ' =>
          ⟨e.slots, fresh.1, σ', e.rhs⟩

omit [Inhabited Term] in
theorem activate_normalize (P : SProgram L Rel Op) (c : Call Term Store Rel) :
    activate L S P.normalize c =
      (activateS L S P c).map fun a => ⟨a.slots, a.frame, a.store, norm L a.code⟩ := by
  rcases c with ⟨rel, args, σ⟩
  simp only [activate, activateS, EqProgram.equations, SProgram.normalize, List.filter_map,
    List.map_map, List.map_filterMap]
  induction P with
  | nil => rfl
  | cons e rest ih =>
      by_cases h : e.1 = rel
      · simp only [List.filter_cons, Function.comp_apply, h, decide_true, ↓reduceIte,
          List.map_cons, List.filterMap_cons]
        cases hu : unifyAll S (instArgs L e.2.params (S.fresh σ e.2.slots).1) args
            (S.fresh σ e.2.slots).2 with
        | none => simpa [hu] using ih
        | some σ' => simpa [hu] using ih
      · simp only [List.filter_cons, Function.comp_apply, h, decide_false]
        simpa using ih

/-- The source semantics: `value` solves the source program's unfolding
equations when every call's answers are its activations' source answers. -/
def SProgram.Solves (P : SProgram L Rel Op)
    (value : Call Term Store Rel → List (Answer Term Store)) : Prop :=
  ∀ c, value c = (activateS L S P c).flatMap fun a =>
    (smeaning L S a.frame a.store a.code).eval value

/-- A solution of the source equations is a denotation of the normalized
program's machine. -/
def denotationOfSource (P : SProgram L Rel Op) (value : Call Term Store Rel → List (Answer Term Store))
    (solves : P.Solves L S value) : Denotation (sourceMachine L S P.normalize) where
  value := value
  unfold c := by
    rw [solves c]
    simp only [sourceMachine, activate_normalize, List.map_map, List.flatMap_map, Function.comp_def]
    congr 1
    funext a
    rw [Expr.lower_answer, norm_eval]

open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats) in
/-- End to end: for a nested source program, the compiled first-order machine
of its normalization never delivers an answer outside the source semantics,
and delivers exactly the source answers, in order, once exhausted. -/
theorem source_compiled_exact (P : SProgram L Rel Op)
    (value : Call Term Store Rel → List (Answer Term Store)) (solves : P.Solves L S value)
    (c : Call Term Store Rel) (count : Nat) :
    ((repeats (step (compiled L S P.normalize)) count (initial L S P.normalize c)).emitted.map
        Prod.snd <+: value c) ∧
    ((repeats (step (compiled L S P.normalize)) count (initial L S P.normalize c)).frontier = [] →
      (repeats (step (compiled L S P.normalize)) count (initial L S P.normalize c)).emitted.map
        Prod.snd = value c) :=
  ⟨compiled_prefix L S P.normalize (denotationOfSource L S P value solves) c count,
   compiled_completed L S P.normalize (denotationOfSource L S P value solves) c count⟩

end Machines

/-! ### The resume table -/

section ResumeTable

variable {L : TemplateLanguage Term}

/-- The resume sites of a body: every non-tail call, in body order, as its
pattern and the code that continues after it. -/
def Code.sites {k : Nat} : Code L Rel Op k → List (L.Tmpl k × Code L Rel Op k)
  | .ret _ => []
  | .fail => []
  | .tail _ _ => []
  | .letCall p _ _ body => (p, body) :: body.sites
  | .letPrim _ _ _ body => body.sites
  | .bind _ _ body => body.sites
  | .ite _ _ yes no => yes.sites ++ no.sites

/-- The bodies execution can enter: the body itself and every continuation or
branch below it. -/
def Code.entries {k : Nat} : Code L Rel Op k → List (Code L Rel Op k)
  | .letCall p rel args body => .letCall p rel args body :: body.entries
  | .letPrim p op args body => .letPrim p op args body :: body.entries
  | .bind p v body => .bind p v body :: body.entries
  | .ite op args yes no => .ite op args yes no :: (yes.entries ++ no.entries)
  | code => [code]

theorem Code.self_mem_entries {k : Nat} (code : Code L Rel Op k) : code ∈ code.entries := by
  cases code <;> simp [Code.entries]

/-- A site's continuation is an entry of the body that owns it. -/
theorem Code.site_body_mem_entries {k : Nat} (code : Code L Rel Op k)
    {p : L.Tmpl k} {body : Code L Rel Op k} (site : (p, body) ∈ code.sites) :
    body ∈ code.entries := by
  induction code with
  | ret => simp [Code.sites] at site
  | fail => simp [Code.sites] at site
  | tail => simp [Code.sites] at site
  | letCall p' rel args body' ih =>
      simp only [Code.sites, List.mem_cons, Prod.mk.injEq] at site
      rcases site with ⟨-, rfl⟩ | site
      · simp [Code.entries, Code.self_mem_entries]
      · simp [Code.entries, ih site]
  | letPrim p' op args body' ih =>
      simp [Code.sites] at site
      simp [Code.entries, ih site]
  | bind p' v body' ih =>
      simp [Code.sites] at site
      simp [Code.entries, ih site]
  | ite op args yes no ihYes ihNo =>
      simp only [Code.sites, List.mem_append] at site
      rcases site with site | site
      · simp [Code.entries, ihYes site]
      · simp [Code.entries, ihNo site]

/-- Entries of an entry are entries. -/
theorem Code.entries_trans {k : Nat} (code : Code L Rel Op k) {inner : Code L Rel Op k}
    (mem : inner ∈ code.entries) : inner.sites ⊆ code.sites := by
  induction code with
  | ret => simp [Code.entries] at mem; subst mem; exact fun _ h => h
  | fail => simp [Code.entries] at mem; subst mem; exact fun _ h => h
  | tail => simp [Code.entries] at mem; subst mem; exact fun _ h => h
  | letCall p rel args body ih =>
      simp only [Code.entries, List.mem_cons] at mem
      rcases mem with rfl | mem
      · exact fun _ h => h
      · exact fun x h => by simp [Code.sites, ih mem h]
  | letPrim p op args body ih =>
      simp only [Code.entries, List.mem_cons] at mem
      rcases mem with rfl | mem
      · exact fun _ h => h
      · exact fun x h => by simp [Code.sites, ih mem h]
  | bind p v body ih =>
      simp only [Code.entries, List.mem_cons] at mem
      rcases mem with rfl | mem
      · exact fun _ h => h
      · exact fun x h => by simp [Code.sites, ih mem h]
  | ite op args yes no ihYes ihNo =>
      simp only [Code.entries, List.mem_cons, List.mem_append] at mem
      rcases mem with rfl | mem | mem
      · exact fun _ h => h
      · exact fun x h => by simp [Code.sites, ihYes mem h]
      · exact fun x h => by simp [Code.sites, ihNo mem h]

/-- A resume site with its slot count. -/
abbrev Site (L : TemplateLanguage Term) (Rel Op : Type) := Σ k, L.Tmpl k × Code L Rel Op k

/-- The program's resume table: every site of every equation, in program
order.  It is generated from the source bodies and finite by construction;
its index is the resume label. -/
def resumeTable (P : EqProgram L Rel Op) : List (Site L Rel Op) :=
  P.flatMap fun e => e.2.rhs.sites.map fun s => ⟨e.2.slots, s⟩

def ReturnFrame.site (f : ReturnFrame L Rel Op) : Site L Rel Op := ⟨f.slots, f.pattern, f.body⟩

variable (L) (S : StoreAlgebra Term Store Op) [Inhabited Term]

omit [Inhabited Term] in
/-- A frame built by the compiled machine belongs to a site of the code it
was built from, and captures exactly that site's support. -/
theorem inspect_call_site {k : Nat} (frame : Fin k → Term) (σ : Store) (code : Code L Rel Op k)
    {c : Call Term Store Rel} {f : ReturnFrame L Rel Op}
    (h : inspectCode L S frame σ code = .call c f) :
    f.site ∈ code.sites.map (fun s => (⟨k, s⟩ : Site L Rel Op)) ∧
      ∀ i : Fin f.slots, (f.captured i).isSome ↔ i ∈ frameSupport L f.pattern f.body := by
  induction code generalizing σ with
  | ret => simp [inspectCode] at h
  | fail => simp [inspectCode] at h
  | tail => simp [inspectCode] at h
  | letCall p rel args body ih =>
      simp only [inspectCode, Instruction.call.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨by simp [Code.sites, ReturnFrame.site], fun i => ?_⟩
      by_cases hi : i ∈ frameSupport L p body <;> simp [capture, hi]
  | letPrim p op args body ih =>
      simp only [inspectCode] at h
      cases hv : S.prim op (instArgs L args frame) σ with
      | none => simp [hv] at h
      | some v =>
          cases hu : S.unify (L.inst p frame) v σ with
          | none => simp [hv, hu] at h
          | some σ' =>
              simp only [hv, hu] at h
              obtain ⟨mem, dom⟩ := ih σ' h
              exact ⟨by simpa [Code.sites] using mem, dom⟩
  | bind p v body ih =>
      simp only [inspectCode] at h
      cases hu : S.unify (L.inst p frame) (L.inst v frame) σ with
      | none => simp [hu] at h
      | some σ' =>
          simp only [hu] at h
          obtain ⟨mem, dom⟩ := ih σ' h
          exact ⟨by simpa [Code.sites] using mem, dom⟩
  | ite op args yes no ihYes ihNo =>
      simp only [inspectCode] at h
      cases ht : S.test op (instArgs L args frame) σ with
      | none => simp [ht] at h
      | some b =>
          cases b with
          | true =>
              simp only [ht] at h
              obtain ⟨mem, dom⟩ := ihYes σ h
              exact ⟨by simp only [Code.sites, List.map_append, List.mem_append]; exact .inl mem, dom⟩
          | false =>
              simp only [ht] at h
              obtain ⟨mem, dom⟩ := ihNo σ h
              exact ⟨by simp only [Code.sites, List.map_append, List.mem_append]; exact .inr mem, dom⟩

/-- Every body execution can enter, across the program, with its slot count. -/
def codeEntries (P : EqProgram L Rel Op) : List (Σ k, Code L Rel Op k) :=
  P.flatMap fun e => e.2.rhs.entries.map fun c => ⟨e.2.slots, c⟩

omit [Inhabited Term] in
theorem site_of_entry (P : EqProgram L Rel Op) {k : Nat} {code : Code L Rel Op k}
    (entry : (⟨k, code⟩ : Σ k, Code L Rel Op k) ∈ codeEntries L P) {site : Site L Rel Op}
    (mem : site ∈ code.sites.map (fun s => (⟨k, s⟩ : Site L Rel Op))) :
    site ∈ resumeTable P := by
  simp only [codeEntries, List.mem_flatMap, List.mem_map] at entry
  obtain ⟨⟨rel, ⟨slots, params, rhs⟩⟩, inP, inner, innerMem, same⟩ := entry
  simp only [Sigma.mk.inj_iff] at same
  obtain ⟨rfl, same⟩ := same
  cases same
  simp only [List.mem_map] at mem
  obtain ⟨s', s'mem, rfl⟩ := mem
  simp only [resumeTable, List.mem_flatMap, List.mem_map]
  exact ⟨_, inP, s', Code.entries_trans rhs innerMem s'mem, rfl⟩

omit [Inhabited Term] in
theorem entry_of_site (P : EqProgram L Rel Op) {f : ReturnFrame L Rel Op}
    (mem : f.site ∈ resumeTable P) :
    (⟨f.slots, f.body⟩ : Σ k, Code L Rel Op k) ∈ codeEntries L P := by
  rcases f with ⟨slots, pattern, body, captured⟩
  simp only [resumeTable, ReturnFrame.site, List.mem_flatMap, List.mem_map] at mem
  obtain ⟨⟨rel, ⟨slots', params, rhs⟩⟩, inP, ⟨p', b'⟩, siteMem, same⟩ := mem
  simp only [Sigma.mk.inj_iff] at same
  obtain ⟨rfl, same⟩ := same
  simp only [heq_eq_eq, Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  simp only [codeEntries, List.mem_flatMap, List.mem_map]
  exact ⟨_, inP, b', Code.site_body_mem_entries rhs siteMem, rfl⟩

variable [DecidableEq Rel]

omit [Inhabited Term] in
theorem activate_entry (P : EqProgram L Rel Op) (c : Call Term Store Rel)
    {a : Activation L Rel Op Store} (mem : a ∈ activate L S P c) :
    (⟨a.slots, a.code⟩ : Σ k, Code L Rel Op k) ∈ codeEntries L P := by
  rcases c with ⟨rel, args, σ⟩
  simp only [activate, List.mem_filterMap, Option.map_eq_some_iff] at mem
  obtain ⟨e, eMem, σ', -, rfl⟩ := mem
  simp only [EqProgram.equations, List.mem_map, List.mem_filter] at eMem
  obtain ⟨⟨rel', e'⟩, ⟨inP, -⟩, rfl⟩ := eMem
  simp only [codeEntries, List.mem_flatMap, List.mem_map]
  exact ⟨_, inP, e'.rhs, Code.self_mem_entries _, rfl⟩

/-- A frame's captures are exactly its site's support. -/
def CapturesSupport (f : ReturnFrame L Rel Op) : Prop :=
  ∀ i, (f.captured i).isSome ↔ i ∈ frameSupport L f.pattern f.body

/-- A control's code is an entry of the program or failure; every pending frame
is a site of the resume table and captures exactly that site's support. -/
def Covered (P : EqProgram L Rel Op)
    (s : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)) : Prop :=
  ∀ t ∈ s.frontier,
    ((⟨t.control.slots, t.control.code⟩ : Σ k, Code L Rel Op k) ∈ codeEntries L P ∨
      t.control.code = .fail) ∧
    ∀ f ∈ t.returns, f.site ∈ resumeTable P ∧ CapturesSupport L f

omit [Inhabited Term] in
theorem covered_initial (P : EqProgram L Rel Op) (c : Call Term Store Rel) :
    Covered L P (initial L S P c) := by
  intro t mem
  simp only [initial, List.mem_map] at mem
  obtain ⟨a, aMem, rfl⟩ := mem
  exact ⟨.inl (activate_entry L S P c aMem), by simp⟩

/-- Coverage is invariant: the compiled machine only ever builds return frames
from the generated resume table. -/
theorem covered_step (P : EqProgram L Rel Op)
    (s : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store))
    (covered : Covered L P s) : Covered L P (step (compiled L S P) s) := by
  rcases s with ⟨frontier, emitted⟩
  cases frontier with
  | nil => exact covered
  | cons task rest =>
      have restCovered : ∀ t ∈ rest, _ := fun t mem => covered t (by simp [mem])
      obtain ⟨codeOk, framesOk⟩ := covered task (by simp)
      rcases task with ⟨context, ⟨k, code, frame, σ⟩, returns⟩
      cases instr : inspectCode L S frame σ code with
      | ret a =>
          cases returns with
          | nil =>
              intro t mem
              simp only [step, compiled, instr] at mem
              exact restCovered t mem
          | cons f pending =>
              intro t mem
              simp only [step, compiled, instr, List.mem_cons] at mem
              rcases mem with rfl | mem
              · have fMem := (framesOk f (by simp)).1
                refine ⟨?_, fun g gMem => framesOk g (by simp [gMem])⟩
                simp only [resumeControl]
                split
                · exact .inl (entry_of_site L P fMem)
                · exact .inr rfl
              · exact restCovered t mem
      | fail =>
          intro t mem
          simp only [step, compiled, instr] at mem
          exact restCovered t mem
      | call c f =>
          intro t mem
          simp only [step, compiled, instr, List.mem_append, List.mem_map] at mem
          rcases mem with ⟨_, ⟨a, aMem, rfl⟩, rfl⟩ | mem
          · refine ⟨.inl (activate_entry L S P c aMem), fun g gMem => ?_⟩
            simp only [List.mem_cons] at gMem
            rcases gMem with rfl | gMem
            · obtain ⟨siteMem, domain⟩ := inspect_call_site L S frame σ code instr
              rcases codeOk with entry | isFail
              · exact ⟨site_of_entry L P entry siteMem, domain⟩
              · have hf : code = .fail := isFail
                rw [hf] at instr
                simp [inspectCode] at instr
            · exact framesOk g gMem
          · exact restCovered t mem
      | tail c =>
          intro t mem
          simp only [step, compiled, instr, List.mem_append, List.mem_map] at mem
          rcases mem with ⟨_, ⟨a, aMem, rfl⟩, rfl⟩ | mem
          · exact ⟨.inl (activate_entry L S P c aMem), framesOk⟩
          · exact restCovered t mem

open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats) in
/-- Every return frame of every reachable state is a site of the finite,
generated resume table, and captures exactly that site's support. -/
theorem reachable_frames_in_table (P : EqProgram L Rel Op) (c : Call Term Store Rel) (count : Nat) :
    Covered L P (repeats (step (compiled L S P)) count (initial L S P c)) := by
  suffices ∀ s, Covered L P s → Covered L P (repeats (step (compiled L S P)) count s) from
    this _ (covered_initial L S P c)
  induction count with
  | zero => exact fun s h => h
  | succ count ih => exact fun s h => ih _ (covered_step L S P s h)

end ResumeTable

end Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
