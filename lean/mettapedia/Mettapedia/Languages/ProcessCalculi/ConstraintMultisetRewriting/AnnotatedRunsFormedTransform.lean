import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormedEvidence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsTensor
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower
import Mettapedia.Logic.LP.UnificationMGU
import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.Logic.LP.TermEquality

/-!
# The represented program: a term language for transforms, its values, and its checker

## Terms

Transform terms are first-order terms over a fixed signature (`signature`): the Flower's
constants, application, pairs and second projection, an `evaluate` symbol for pending
computations (`evaluate t r`: the value of `t` is to be told to `r`), and named operation symbols
for compiled programs. Variables below the arity of the formed context are the context's
variables, shared with the caller; the others belong to the transform.

## Values

A theory's **value discipline** (`ValueDiscipline`) is a table of canonical constants
(constructors and type formers) such that every root rule's left side is headed by a constant
outside the table. **Values** (`IsValue`) are built from variables and canonical constants by
application and pairing: their application spines are headed by a variable (neutral forms) or by
a canonical constant or a pair (canonical forms). A value has no step of the theory
(`IsValue.no_step`): no beta or projection redex, and no root redex at any position.

* `quoteValue` maps values to transform terms; `readback` maps transform terms back and is
  defined on values only. A pending `evaluate`, a compiled operation, a projection, a variable of
  the transform and a non-canonical constant (an eliminator, a declared definition) have no
  readback (`readback_evaluate`, `readback_second`, `readback_operation`, `readback_internal`,
  `readback_isValue`).
* Readback inverts quotation (`readback_quoteValue`) and commutes with substitution of values
  for context variables (`readback_applyTerm`).

## Denotation

`denote` reads every transform term without a pending computation as a Flower term, an
operation as its body applied to the denotations of its arguments. It commutes with substitution
(`denote_applyTerm`), and it agrees with readback on values (`denote_of_readback`).

## The declared observation and the independent result checker

The observation of a run is what its final store **entails** about a result variable: every
solution of the store gives it the answer's value (`Observes`). `checkResult` runs the existing
occurs-checked first-order unifier with fuel on the final store, reads the result variable
through the unifier's answer, accepts only when the readback is the claimed Flower term and the
answer leaves the caller's context variables unbound (`fixesContext`). Its soundness
(`checkResult_sound`) uses only the unifier's proved soundness, generality and idempotence. As a
four-outcome service (`resultService`) it declines when the unifier gives no answer, so exhausted
fuel grants no authority. The answer depends on the fuel: below the unifier's need the checker
declines.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed

open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
  (Tm DeclName Rules StepCore Sub subst subComp subst_subComp)
open AnnotatedRuns

/-! ## The term language -/

/-- The function symbols of transform terms. -/
inductive Symbol where
  | application
  | pair
  | second
  | evaluate
  | operation (name : DeclName) (arity : Nat)
  deriving DecidableEq

def Symbol.arity : Symbol → Nat
  | .application => 2
  | .pair => 2
  | .second => 1
  | .evaluate => 2
  | .operation _ arity => arity

/-- The transform signature: Flower constants, natural-number variables. -/
abbrev signature : LPSignature where
  constants := DeclName
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Symbol
  functionArity := Symbol.arity

/-- The substitution action of transform terms: the existing first-order unifier's. -/
abbrev action := FirstOrder.action signature

abbrev Pattern := Term signature

def ap (function argument : Pattern) : Pattern :=
  .app .application fun i => if i.val = 0 then function else argument

def pairP (first second : Pattern) : Pattern :=
  .app .pair fun i => if i.val = 0 then first else second

def secondP (pair : Pattern) : Pattern := .app .second fun _ => pair

/-- A pending computation: the value of the first argument is to be told to the second. -/
def evaluate (term result : Pattern) : Pattern :=
  .app .evaluate fun i => if i.val = 0 then term else result

/-- A compiled operation applied to its arguments, in call order. -/
def call (name : DeclName) (arity : Nat) (arguments : Fin arity → Pattern) : Pattern :=
  .app (.operation name arity) arguments

/-- A compiled operation applied to a list of arguments. -/
def operation (name : DeclName) (arguments : List Pattern) : Pattern :=
  call name arguments.length fun i => arguments.get i

/-! ## Values -/

section Values

variable {Head : Type}

/-- The head of an application spine. -/
def spineHead {n : Nat} : Tm Head n → Tm Head n
  | .app function _ => spineHead function
  | term => term

/-- **Values**: built from variables and canonical constants by application and pairing. -/
def IsValue (canonical : DeclName → Bool) {n : Nat} : Tm Head n → Prop
  | .var _ => True
  | .const name => canonical name = true
  | .app function argument => IsValue canonical function ∧ IsValue canonical argument
  | .pair first second => IsValue canonical first ∧ IsValue canonical second
  | _ => False

/-- **A value discipline for a theory**: a table of canonical constants, constructors and type
formers, such that every root rule's left side is headed by a constant outside the table. The
law is a field; each theory's instance proves it. -/
structure ValueDiscipline (R : Rules Head) where
  canonical : DeclName → Bool
  root_head : ∀ {n : Nat} {left right : Tm Head n}, R.computation.step left right →
    ∃ name, spineHead left = .const name ∧ canonical name = false

/-- The spine of a value is headed by a variable, a canonical constant or a pair. -/
theorem IsValue.spineHead_cases {canonical : DeclName → Bool} {n : Nat} :
    ∀ {term : Tm Head n}, IsValue canonical term →
      (∃ index, spineHead term = .var index) ∨
        (∃ name, spineHead term = .const name ∧ canonical name = true) ∨
          (∃ first second, spineHead term = .pair first second)
  | .var index, _ => .inl ⟨index, rfl⟩
  | .const name, value => .inr (.inl ⟨name, rfl, value⟩)
  | .app function _, value => IsValue.spineHead_cases (term := function) value.1
  | .pair first second, _ => .inr (.inr ⟨first, second, rfl⟩)
  | .head _, value => value.elim
  | .pi _ _, value => value.elim
  | .sigma _ _, value => value.elim
  | .id _ _ _, value => value.elim
  | .lam _, value => value.elim
  | .fst _, value => value.elim
  | .snd _, value => value.elim
  | .refl _, value => value.elim

/-- **A value has no step**: under a value discipline, no beta, projection or root rule applies
to a value at any position. Values are normal forms. -/
theorem IsValue.no_step {R : Rules Head} (discipline : ValueDiscipline R) {n : Nat}
    {term next : Tm Head n} (value : IsValue discipline.canonical term) :
    ¬ StepCore R.computation R.headEq term next := by
  intro step
  induction step with
  | betaPi body argument => exact value.1.elim
  | betaSigmaFst first second => exact value.elim
  | betaSigmaSnd first second => exact value.elim
  | head _ => exact value.elim
  | root root =>
      obtain ⟨name, headed, notCanonical⟩ := discipline.root_head root
      rcases IsValue.spineHead_cases value with ⟨index, same⟩ | ⟨other, same, canonical⟩ |
          ⟨first, second, same⟩
      · rw [headed] at same
        cases same
      · rw [headed] at same
        cases same
        rw [notCanonical] at canonical
        cases canonical
      · rw [headed] at same
        cases same
  | congPiDom _ _ => exact value.elim
  | congPiCod _ _ => exact value.elim
  | congSigmaDom _ _ => exact value.elim
  | congSigmaCod _ _ => exact value.elim
  | congIdTy _ _ => exact value.elim
  | congIdLeft _ _ => exact value.elim
  | congIdRight _ _ => exact value.elim
  | congLam _ _ => exact value.elim
  | congAppFun _ ih => exact ih value.1
  | congAppArg _ ih => exact ih value.2
  | congPairFst _ ih => exact ih value.1
  | congPairSnd _ ih => exact ih value.2
  | congFst _ _ => exact value.elim
  | congSnd _ _ => exact value.elim
  | congRefl _ _ => exact value.elim

end Values

/-! ## Quotation and readback of values -/

section Quotation

variable {Head : Type} (canonical : DeclName → Bool)

/-- **Quotation of values.** -/
def quoteValue {n : Nat} : Tm Head n → Option Pattern
  | .var index => some (.var index.val)
  | .const name => if canonical name then some (.const name) else none
  | .app function argument =>
      (quoteValue function).bind fun f => (quoteValue argument).map (ap f)
  | .pair first second =>
      (quoteValue first).bind fun a => (quoteValue second).map (pairP a)
  | _ => none

/-- **Readback of values.** Pending computations, operations, projections, the transform's own
variables and non-canonical constants have no readback. -/
def readback {n : Nat} : Pattern → Option (Tm Head n)
  | .var v => if h : v < n then some (.var ⟨v, h⟩) else none
  | .const name => if canonical name then some (.const name) else none
  | .app .application arguments =>
      (readback (arguments ⟨0, by decide⟩)).bind fun f =>
        (readback (arguments ⟨1, by decide⟩)).map (Tm.app f)
  | .app .pair arguments =>
      (readback (arguments ⟨0, by decide⟩)).bind fun a =>
        (readback (arguments ⟨1, by decide⟩)).map (Tm.pair a)
  | .app _ _ => none

@[simp] theorem readback_ap {n : Nat} (f a : Pattern) :
    (readback canonical (ap f a) : Option (Tm Head n)) =
      (readback canonical f).bind fun f' => (readback canonical a).map (Tm.app f') := rfl

@[simp] theorem readback_pairP {n : Nat} (a b : Pattern) :
    (readback canonical (pairP a b) : Option (Tm Head n)) =
      (readback canonical a).bind fun a' => (readback canonical b).map (Tm.pair a') := rfl

/-- A pending computation is not a value. -/
@[simp] theorem readback_evaluate {n : Nat} (t r : Pattern) :
    (readback canonical (evaluate t r) : Option (Tm Head n)) = none := rfl

/-- A projection is not a value. -/
@[simp] theorem readback_second {n : Nat} (p : Pattern) :
    (readback canonical (secondP p) : Option (Tm Head n)) = none := rfl

/-- A compiled operation applied to arguments is not a value. -/
@[simp] theorem readback_operation {n : Nat} (name : DeclName) (arguments : List Pattern) :
    (readback canonical (operation name arguments) : Option (Tm Head n)) = none := rfl

/-- A variable of the transform, beyond the context, has no readback. -/
theorem readback_internal {n v : Nat} (outside : n ≤ v) :
    (readback canonical (.var v) : Option (Tm Head n)) = none := by
  simp [readback, Nat.not_lt.mpr outside]

/-- A non-canonical constant, such as an eliminator or a declared definition, has no readback. -/
theorem readback_noncanonical {n : Nat} {name : DeclName} (outside : canonical name = false) :
    (readback canonical (.const name) : Option (Tm Head n)) = none := by
  simp [readback, outside]

/-- **Readback produces values only.** -/
theorem readback_isValue {n : Nat} :
    ∀ (p : Pattern) {t : Tm Head n}, readback canonical p = some t → IsValue canonical t
  | .var v, t, read => by
      unfold readback at read
      split at read
      · cases read
        trivial
      · cases read
  | .const name, t, read => by
      unfold readback at read
      split at read
      · rename_i isCanonical
        cases read
        exact isCanonical
      · cases read
  | .app .application arguments, t, read => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              simp only [readback, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at read
              subst read
              exact ⟨readback_isValue _ hf, readback_isValue _ ha⟩
  | .app .pair arguments, t, read => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              simp only [readback, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at read
              subst read
              exact ⟨readback_isValue _ hf, readback_isValue _ ha⟩
  | .app .second _, t, read => by simp [readback] at read
  | .app .evaluate _, t, read => by simp [readback] at read
  | .app (.operation _ _) _, t, read => by simp [readback] at read

/-- **Readback inverts quotation.** -/
theorem readback_quoteValue {n : Nat} :
    ∀ (t : Tm Head n) {p : Pattern}, quoteValue canonical t = some p → readback canonical p = some t
  | .var index, p, quoted => by
      simp only [quoteValue, Option.some.injEq] at quoted
      subst quoted
      simp [readback, index.isLt]
  | .const name, p, quoted => by
      unfold quoteValue at quoted
      split at quoted
      · rename_i isCanonical
        cases quoted
        simp [readback, isCanonical]
      · cases quoted
  | .app function argument, p, quoted => by
      cases hf : quoteValue canonical function with
      | none => simp [quoteValue, hf] at quoted
      | some f =>
          cases ha : quoteValue canonical argument with
          | none => simp [quoteValue, hf, ha] at quoted
          | some a =>
              simp only [quoteValue, hf, ha, Option.bind_some, Option.map_some,
                Option.some.injEq] at quoted
              subst quoted
              rw [readback_ap, readback_quoteValue function hf, readback_quoteValue argument ha]
              rfl
  | .pair first second, p, quoted => by
      cases hf : quoteValue canonical first with
      | none => simp [quoteValue, hf] at quoted
      | some f =>
          cases hs : quoteValue canonical second with
          | none => simp [quoteValue, hf, hs] at quoted
          | some s =>
              simp only [quoteValue, hf, hs, Option.bind_some, Option.map_some,
                Option.some.injEq] at quoted
              subst quoted
              rw [readback_pairP, readback_quoteValue first hf, readback_quoteValue second hs]
              rfl
  | .head _, p, quoted => by simp [quoteValue] at quoted
  | .pi _ _, p, quoted => by simp [quoteValue] at quoted
  | .sigma _ _, p, quoted => by simp [quoteValue] at quoted
  | .id _ _ _, p, quoted => by simp [quoteValue] at quoted
  | .lam _, p, quoted => by simp [quoteValue] at quoted
  | .fst _, p, quoted => by simp [quoteValue] at quoted
  | .snd _, p, quoted => by simp [quoteValue] at quoted
  | .refl _, p, quoted => by simp [quoteValue] at quoted

/-- Every value is quoted. -/
theorem quoteValue_of_isValue {n : Nat} :
    ∀ (t : Tm Head n), IsValue canonical t → ∃ p, quoteValue canonical t = some p
  | .var index, _ => ⟨_, rfl⟩
  | .const name, value => ⟨.const name, by simp [quoteValue, show canonical name = true from value]⟩
  | .app function argument, ⟨functionValue, argumentValue⟩ => by
      obtain ⟨f, hf⟩ := quoteValue_of_isValue function functionValue
      obtain ⟨a, ha⟩ := quoteValue_of_isValue argument argumentValue
      exact ⟨ap f a, by simp [quoteValue, hf, ha]⟩
  | .pair first second, ⟨firstValue, secondValue⟩ => by
      obtain ⟨f, hf⟩ := quoteValue_of_isValue first firstValue
      obtain ⟨s, hs⟩ := quoteValue_of_isValue second secondValue
      exact ⟨pairP f s, by simp [quoteValue, hf, hs]⟩
  | .head _, value => value.elim
  | .pi _ _, value => value.elim
  | .sigma _ _, value => value.elim
  | .id _ _ _, value => value.elim
  | .lam _, value => value.elim
  | .fst _, value => value.elim
  | .snd _, value => value.elim
  | .refl _, value => value.elim

/-- **Readback commutes with substitution on values**: substituting, for the context variables,
transform terms that read back as a substitution's images, then reading back, is reading back
and then substituting. -/
theorem readback_applyTerm {n m : Nat} (σ : Subst signature) (τ : Sub Head n m)
    (images : ∀ i : Fin n, readback canonical (σ i.val) = some (τ i)) :
    ∀ (p : Pattern) {t : Tm Head n}, readback canonical p = some t →
      readback canonical (σ.applyTerm p) = some (subst τ t)
  | .var v, t, read => by
      unfold readback at read
      split at read
      · rename_i inside
        cases read
        exact images ⟨v, inside⟩
      · cases read
  | .const name, t, read => by
      unfold readback at read
      split at read
      · rename_i isCanonical
        cases read
        simp [Subst.applyTerm, readback, isCanonical, subst]
      · cases read
  | .app .application arguments, t, read => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              simp only [readback, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at read
              subst read
              change (readback canonical (σ.applyTerm (arguments ⟨0, by decide⟩))).bind
                  (fun f' => (readback canonical (σ.applyTerm (arguments ⟨1, by decide⟩))).map
                    (Tm.app f')) = _
              rw [readback_applyTerm σ τ images _ hf, readback_applyTerm σ τ images _ ha]
              rfl
  | .app .pair arguments, t, read => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              simp only [readback, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at read
              subst read
              change (readback canonical (σ.applyTerm (arguments ⟨0, by decide⟩))).bind
                  (fun f' => (readback canonical (σ.applyTerm (arguments ⟨1, by decide⟩))).map
                    (Tm.pair f')) = _
              rw [readback_applyTerm σ τ images _ hf, readback_applyTerm σ τ images _ ha]
              rfl
  | .app .second _, t, read => by simp [readback] at read
  | .app .evaluate _, t, read => by simp [readback] at read
  | .app (.operation _ _) _, t, read => by simp [readback] at read

end Quotation

/-! ## Denotation -/

section Denotation

variable {Head : Type}

/-- An operation table: each compiled operation's body over its arguments. -/
abbrev Operations (Head : Type) := DeclName → (arity : Nat) → Option (Tm Head arity)

/-- All images defined, or none. -/
def collect {α : Type} : {k : Nat} → (Fin k → Option α) → Option (Fin k → α)
  | 0, _ => some Fin.elim0
  | _ + 1, f => (f 0).bind fun first => (collect fun i => f i.succ).map (Fin.cons first)

theorem collect_eq_some {α : Type} :
    ∀ {k : Nat} {f : Fin k → Option α} {g : Fin k → α}, collect f = some g → ∀ i, f i = some (g i)
  | 0, _, _, _, i => i.elim0
  | k + 1, f, g, collected, i => by
      cases first : f 0 with
      | none => simp [collect, first] at collected
      | some a =>
          cases rest : collect (fun i : Fin k => f i.succ) with
          | none => simp [collect, first, rest] at collected
          | some h =>
              simp only [collect, first, rest, Option.bind_some, Option.map_some,
                Option.some.injEq] at collected
              subst collected
              refine Fin.cases ?_ (fun j => ?_) i
              · simpa using first
              · simpa using collect_eq_some rest j

theorem collect_of_forall {α : Type} :
    ∀ {k : Nat} {f : Fin k → Option α} {g : Fin k → α}, (∀ i, f i = some (g i)) → collect f = some g
  | 0, _, g, _ => by
      simp only [collect, Option.some.injEq]
      funext i
      exact i.elim0
  | k + 1, f, g, every => by
      have rest : collect (fun i : Fin k => f i.succ) = some (fun i => g i.succ) :=
        collect_of_forall fun i => every i.succ
      simp only [collect, every 0, rest, Option.bind_some, Option.map_some, Option.some.injEq]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **Denotation** of transform terms without pending computations: an operation is its body
applied to the denotations of its arguments. -/
def denote (ops : Operations Head) {n : Nat} : Pattern → Option (Tm Head n)
  | .var v => if h : v < n then some (.var ⟨v, h⟩) else none
  | .const name => some (.const name)
  | .app .application arguments =>
      (denote ops (arguments ⟨0, by decide⟩)).bind fun f =>
        (denote ops (arguments ⟨1, by decide⟩)).map (Tm.app f)
  | .app .pair arguments =>
      (denote ops (arguments ⟨0, by decide⟩)).bind fun a =>
        (denote ops (arguments ⟨1, by decide⟩)).map (Tm.pair a)
  | .app .second arguments => (denote ops (arguments ⟨0, by decide⟩)).map Tm.snd
  | .app .evaluate _ => none
  | .app (.operation name arity) arguments =>
      (ops name arity).bind fun body =>
        (collect fun i => denote ops (arguments i)).map fun images =>
          subst (fun index => images index.rev) body

/-- **Denotation commutes with substitution.** -/
theorem denote_applyTerm (ops : Operations Head) {k n : Nat} (σ : Subst signature)
    (τ : Sub Head k n) (images : ∀ i : Fin k, denote ops (σ i.val) = some (τ i)) :
    ∀ (p : Pattern) {t : Tm Head k}, denote ops p = some t →
      denote ops (σ.applyTerm p) = some (subst τ t)
  | .var v, t, denoted => by
      unfold denote at denoted
      split at denoted
      · rename_i inside
        cases denoted
        exact images ⟨v, inside⟩
      · cases denoted
  | .const name, t, denoted => by
      simp only [denote, Option.some.injEq] at denoted
      subst denoted
      rfl
  | .app .application arguments, t, denoted => by
      cases hf : (denote ops (arguments ⟨0, by decide⟩) : Option (Tm Head k)) with
      | none => simp [denote, hf] at denoted
      | some f =>
          cases ha : (denote ops (arguments ⟨1, by decide⟩) : Option (Tm Head k)) with
          | none => simp [denote, hf, ha] at denoted
          | some a =>
              simp only [denote, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at denoted
              subst denoted
              change (denote ops (σ.applyTerm (arguments ⟨0, by decide⟩))).bind
                  (fun f' => (denote ops (σ.applyTerm (arguments ⟨1, by decide⟩))).map
                    (Tm.app f')) = _
              rw [denote_applyTerm ops σ τ images _ hf, denote_applyTerm ops σ τ images _ ha]
              rfl
  | .app .pair arguments, t, denoted => by
      cases hf : (denote ops (arguments ⟨0, by decide⟩) : Option (Tm Head k)) with
      | none => simp [denote, hf] at denoted
      | some f =>
          cases ha : (denote ops (arguments ⟨1, by decide⟩) : Option (Tm Head k)) with
          | none => simp [denote, hf, ha] at denoted
          | some a =>
              simp only [denote, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at denoted
              subst denoted
              change (denote ops (σ.applyTerm (arguments ⟨0, by decide⟩))).bind
                  (fun f' => (denote ops (σ.applyTerm (arguments ⟨1, by decide⟩))).map
                    (Tm.pair f')) = _
              rw [denote_applyTerm ops σ τ images _ hf, denote_applyTerm ops σ τ images _ ha]
              rfl
  | .app .second arguments, t, denoted => by
      cases hp : (denote ops (arguments ⟨0, by decide⟩) : Option (Tm Head k)) with
      | none => simp [denote, hp] at denoted
      | some p =>
          simp only [denote, hp, Option.map_some, Option.some.injEq] at denoted
          subst denoted
          change (denote ops (σ.applyTerm (arguments ⟨0, by decide⟩))).map Tm.snd = _
          rw [denote_applyTerm ops σ τ images _ hp]
          rfl
  | .app .evaluate _, t, denoted => by simp [denote] at denoted
  | .app (.operation name arity) arguments, t, denoted => by
      cases hb : ops name arity with
      | none => simp [denote, hb] at denoted
      | some body =>
          cases hc : collect (fun i => (denote ops (arguments i) : Option (Tm Head k))) with
          | none => simp [denote, hb, hc] at denoted
          | some values =>
              simp only [denote, hb, hc, Option.bind_some, Option.map_some,
                Option.some.injEq] at denoted
              subst denoted
              have substituted : collect (fun i => denote ops (σ.applyTerm (arguments i))) =
                  some (fun i => subst τ (values i)) :=
                collect_of_forall fun i =>
                  denote_applyTerm ops σ τ images (arguments i) (collect_eq_some hc i)
              change (ops name arity).bind (fun body =>
                (collect fun i => denote ops (σ.applyTerm (arguments i))).map fun images =>
                  subst (fun index => images index.rev) body) = _
              rw [hb, substituted]
              simp only [Option.bind_some, Option.map_some, Option.some.injEq]
              rw [subst_subComp]
              rfl

/-- **Denotation agrees with readback on values.** -/
theorem denote_of_readback (ops : Operations Head) (canonical : DeclName → Bool) {n : Nat} :
    ∀ (p : Pattern) {t : Tm Head n}, readback canonical p = some t → denote ops p = some t
  | .var v, t, read => by
      unfold readback at read
      unfold denote
      split at read
      · rename_i inside
        cases read
        simp [inside]
      · cases read
  | .const name, t, read => by
      unfold readback at read
      split at read
      · cases read
        rfl
      · cases read
  | .app .application arguments, t, read => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              simp only [readback, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at read
              subst read
              simp only [denote, denote_of_readback ops canonical _ hf,
                denote_of_readback ops canonical _ ha, Option.bind_some, Option.map_some]
  | .app .pair arguments, t, read => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              simp only [readback, hf, ha, Option.bind_some, Option.map_some, Option.some.injEq] at read
              subst read
              simp only [denote, denote_of_readback ops canonical _ hf,
                denote_of_readback ops canonical _ ha, Option.bind_some, Option.map_some]
  | .app .second _, t, read => by simp [readback] at read
  | .app .evaluate _, t, read => by simp [readback] at read
  | .app (.operation _ _) _, t, read => by simp [readback] at read

/-- A quoted value denotes itself. -/
theorem denote_quoteValue (ops : Operations Head) (canonical : DeclName → Bool) {n : Nat}
    (t : Tm Head n) {p : Pattern} (quoted : quoteValue canonical t = some p) :
    denote ops p = some t :=
  denote_of_readback ops canonical p (readback_quoteValue canonical t quoted)

end Denotation

/-! ## Substitution through the term builders -/

section Builders

variable (σ : Subst signature)

@[simp] theorem applyTerm_ap (f a : Pattern) :
    σ.applyTerm (ap f a) = ap (σ.applyTerm f) (σ.applyTerm a) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  by_cases h : i.val = 0 <;> simp [h]

@[simp] theorem applyTerm_pairP (a b : Pattern) :
    σ.applyTerm (pairP a b) = pairP (σ.applyTerm a) (σ.applyTerm b) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  by_cases h : i.val = 0 <;> simp [h]

@[simp] theorem applyTerm_secondP (p : Pattern) :
    σ.applyTerm (secondP p) = secondP (σ.applyTerm p) := rfl

@[simp] theorem applyTerm_evaluate (t r : Pattern) :
    σ.applyTerm (evaluate t r) = evaluate (σ.applyTerm t) (σ.applyTerm r) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  by_cases h : i.val = 0 <;> simp [h]

@[simp] theorem applyTerm_call (name : DeclName) (arity : Nat) (arguments : Fin arity → Pattern) :
    σ.applyTerm (call name arity arguments) = call name arity fun i => σ.applyTerm (arguments i) :=
  rfl

theorem ap_injective {f a f' a' : Pattern} (same : ap f a = ap f' a') : f = f' ∧ a = a' := by
  have fields := eq_of_heq (Term.app.inj same).2
  exact ⟨by simpa using congrFun fields ⟨0, by decide⟩, by simpa using congrFun fields ⟨1, by decide⟩⟩

theorem pairP_injective {a b a' b' : Pattern} (same : pairP a b = pairP a' b') : a = a' ∧ b = b' := by
  have fields := eq_of_heq (Term.app.inj same).2
  exact ⟨by simpa using congrFun fields ⟨0, by decide⟩, by simpa using congrFun fields ⟨1, by decide⟩⟩

theorem secondP_injective {p p' : Pattern} (same : secondP p = secondP p') : p = p' := by
  have fields := eq_of_heq (Term.app.inj same).2
  exact congrFun fields ⟨0, by decide⟩

theorem evaluate_injective {t r t' r' : Pattern} (same : evaluate t r = evaluate t' r') :
    t = t' ∧ r = r' := by
  have fields := eq_of_heq (Term.app.inj same).2
  exact ⟨by simpa using congrFun fields ⟨0, by decide⟩, by simpa using congrFun fields ⟨1, by decide⟩⟩

/-- **A quoted value is fixed by every substitution fixing the context's variables.** In
particular a quoted closed value is fixed by every substitution. -/
theorem applyTerm_quoteValue {Head : Type} (canonical : DeclName → Bool) :
    ∀ {n : Nat} (t : Tm Head n) {p : Pattern}, quoteValue canonical t = some p →
      ∀ σ : Subst signature, (∀ i : Fin n, σ i.val = .var i.val) → σ.applyTerm p = p
  | _, .var index, p, quoted, σ, fixed => by
      simp only [quoteValue, Option.some.injEq] at quoted
      subst quoted
      exact fixed index
  | _, .const name, p, quoted, σ, _ => by
      unfold quoteValue at quoted
      split at quoted
      · cases quoted
        rfl
      · cases quoted
  | _, .app function argument, p, quoted, σ, fixed => by
      cases hf : quoteValue canonical function with
      | none => simp [quoteValue, hf] at quoted
      | some f =>
          cases ha : quoteValue canonical argument with
          | none => simp [quoteValue, hf, ha] at quoted
          | some a =>
              simp only [quoteValue, hf, ha, Option.bind_some, Option.map_some,
                Option.some.injEq] at quoted
              subst quoted
              rw [applyTerm_ap, applyTerm_quoteValue canonical function hf σ fixed,
                applyTerm_quoteValue canonical argument ha σ fixed]
  | _, .pair first second, p, quoted, σ, fixed => by
      cases hf : quoteValue canonical first with
      | none => simp [quoteValue, hf] at quoted
      | some f =>
          cases hs : quoteValue canonical second with
          | none => simp [quoteValue, hf, hs] at quoted
          | some s =>
              simp only [quoteValue, hf, hs, Option.bind_some, Option.map_some,
                Option.some.injEq] at quoted
              subst quoted
              rw [applyTerm_pairP, applyTerm_quoteValue canonical first hf σ fixed,
                applyTerm_quoteValue canonical second hs σ fixed]
  | _, .head _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .pi _ _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .sigma _ _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .id _ _ _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .lam _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .fst _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .snd _, p, quoted, _, _ => by simp [quoteValue] at quoted
  | _, .refl _, p, quoted, _, _ => by simp [quoteValue] at quoted

end Builders

/-! ## Stores of runs -/

section Stores

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- The final store of a run is consistent. -/
theorem Executable.final_consistent (A : SubstitutionAction T S) (label : O → T)
    {C : Configuration T O} {w : List (Firing T S O)} (run : Executable A label C w) :
    A.Consistent (follow label C w).equations := by
  rw [follow_equations]
  exact Executable.joint A label run

/-- Every firing of a run is admitted at some cut. -/
theorem Executable.valid_of_mem (A : SubstitutionAction T S) (label : O → T) :
    ∀ {C : Configuration T O} {w : List (Firing T S O)}, Executable A label C w →
      ∀ f ∈ w, ∃ D : Configuration T O, f.Valid A label D
  | _, [], _, _, member => (List.not_mem_nil member).elim
  | C, g :: rest, run, f, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨C, run.1⟩
      · exact Executable.valid_of_mem A label run.2 f later

/-- **The declared observation**: every solution of the store gives `result` the value of
`answer`. -/
def Observes (A : SubstitutionAction T S) (store : EquationStore T) (result answer : T) : Prop :=
  A.Entails store fun σ => A.Solves σ (result, answer)

/-- A stronger store keeps every observation. -/
theorem Observes.of_refines {A : SubstitutionAction T S} {stronger weaker : EquationStore T}
    (refines : A.Refines stronger weaker) {result answer : T}
    (observed : Observes A weaker result answer) : Observes A stronger result answer :=
  A.entails_of_refines refines observed

end Stores

/-! ## The independent result checker -/

section Checker

variable {Head : Type} [DecidableEq Head] {n : Nat}

/-- An answer of the unifier is a solution: the store is consistent. -/
theorem consistent_of_unified {fuel : Nat} {store : EquationStore Pattern}
    (unified : (unifyFuel fuel store).isSome = true) : action.Consistent store := by
  cases accepted : unifyFuel fuel store with
  | none =>
      rw [accepted] at unified
      cases unified
  | some θ => exact ⟨θ, unifyFuel_sound fuel store θ accepted⟩

/-- The answer leaves every context variable unbound. -/
def fixesContext (n : Nat) (θ : Subst signature) : Bool :=
  (List.finRange n).all fun i => decide (θ i.val = .var i.val)

theorem fixesContext_spec {n : Nat} {θ : Subst signature} (fixes : fixesContext n θ = true) :
    ∀ i : Fin n, θ i.val = .var i.val := by
  intro i
  have every := List.all_eq_true.mp fixes i (List.mem_finRange i)
  exact of_decide_eq_true every

variable (canonical : DeclName → Bool)

/-- **The result checker**: solve the store with the existing unifier, read the result variable
through its answer, compare the readback with the claimed Flower term, and check that the
answer leaves the caller's context variables unbound. -/
def checkResult (fuel : Nat) (store : EquationStore Pattern) (result : Nat) (target : Tm Head n) :
    Bool :=
  match unifyFuel fuel store with
  | some θ => decide (readback canonical (θ result) = some target) && fixesContext n θ
  | none => false

variable {canonical}

/-- The unifier's answer behind an accepted check. -/
theorem checkResult_answer {fuel : Nat} {store : EquationStore Pattern} {result : Nat}
    {target : Tm Head n} (checked : checkResult canonical fuel store result target = true) :
    ∃ θ, unifyFuel fuel store = some θ ∧ readback canonical (θ result) = some target ∧
      ∀ i : Fin n, θ i.val = .var i.val := by
  unfold checkResult at checked
  split at checked
  · rename_i θ accepted
    obtain ⟨read, fixes⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨θ, accepted, of_decide_eq_true read, fixesContext_spec fixes⟩
  · cases checked

/-- **Soundness of the result checker**: an accepted check gives a consistent store and an
answer, read back as the claimed term, that the store observes for the result variable. Only the
unifier's soundness, generality and idempotence are used. -/
theorem checkResult_sound {fuel : Nat} {store : EquationStore Pattern} {result : Nat}
    {target : Tm Head n} (checked : checkResult canonical fuel store result target = true) :
    action.Consistent store ∧
      ∃ answer, readback canonical answer = some target ∧
        Observes action store (.var result) answer := by
  obtain ⟨θ, accepted, read, _⟩ := checkResult_answer checked
  refine ⟨⟨θ, unifyFuel_sound fuel store θ accepted⟩, θ result, read, ?_⟩
  intro δ solved
  obtain ⟨residual, factors⟩ :=
    FirstOrder.factors_on_terms (unifyFuel_mgu fuel store θ accepted δ solved)
  have fixed : θ.applyTerm (θ result) = θ result :=
    Subst.applyTerm_eq_self ((unifyFuel_relevantIdempotent fuel store θ accepted).unbound result)
  change δ.applyTerm (.var result) = δ.applyTerm (θ result)
  rw [factors, factors, Subst.applyTerm_comp, Subst.applyTerm_comp, fixed]
  rfl

open Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower

variable (canonical)

/-- **The result checker as a four-outcome service**: no unifier answer is a decline; a
different readback, or an answer that binds a context variable, a rejection. -/
def resultService (fuel : Nat) : Service (EquationStore Pattern × Nat × Tm Head n) Unit where
  run input :=
    match unifyFuel fuel input.1 with
    | none => .declined
    | some θ =>
        if readback canonical (θ input.2.1) = some input.2.2 ∧ fixesContext n θ = true then
          .accepted ()
        else .rejected

theorem resultService_accepts_iff (fuel : Nat) (store : EquationStore Pattern) (result : Nat)
    (target : Tm Head n) :
    (resultService canonical fuel).Accepts (store, result, target) () ↔
      checkResult canonical fuel store result target = true := by
  unfold Service.Accepts resultService checkResult
  cases accepted : unifyFuel fuel store with
  | none => simp [accepted]
  | some θ =>
      simp only [accepted]
      by_cases same : readback canonical (θ result) = some target ∧ fixesContext n θ = true
      · simp [same]
      · simp only [same, if_false]
        constructor
        · intro impossible
          cases impossible
        · intro both
          exact absurd ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp both).1,
            (Bool.and_eq_true_iff.mp both).2⟩ same

/-- Only acceptance carries authority, and it carries the observation. -/
theorem resultService_sound (fuel : Nat) :
    (resultService (Head := Head) (n := n) canonical fuel).Sound fun input _ =>
      action.Consistent input.1 ∧
        ∃ answer, readback canonical answer = some input.2.2 ∧
          Observes action input.1 (.var input.2.1) answer := by
  intro input output accepted
  obtain ⟨store, result, target⟩ := input
  exact checkResult_sound ((resultService_accepts_iff canonical fuel store result target).mp accepted)

/-- Without fuel the service declines every store, whatever it entails. -/
theorem resultService_declines_without_fuel (store : EquationStore Pattern) (result : Nat)
    (target : Tm Head n) : (resultService canonical 0).run (store, result, target) = .declined := by
  simp [resultService, unifyFuel]

end Checker

#print axioms IsValue.spineHead_cases
#print axioms IsValue.no_step
#print axioms readback_internal
#print axioms readback_noncanonical
#print axioms readback_isValue
#print axioms readback_quoteValue
#print axioms quoteValue_of_isValue
#print axioms readback_applyTerm
#print axioms collect_eq_some
#print axioms collect_of_forall
#print axioms denote_applyTerm
#print axioms denote_of_readback
#print axioms denote_quoteValue
#print axioms applyTerm_ap
#print axioms evaluate_injective
#print axioms applyTerm_quoteValue
#print axioms Executable.final_consistent
#print axioms Executable.valid_of_mem
#print axioms Observes.of_refines
#print axioms consistent_of_unified
#print axioms fixesContext_spec
#print axioms checkResult_answer
#print axioms checkResult_sound
#print axioms resultService_accepts_iff
#print axioms resultService_sound
#print axioms resultService_declines_without_fuel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
