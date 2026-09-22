import Mettapedia.OSLF.Syntax.PatternAsBindingSignature
import Mettapedia.OSLF.Syntax.StepRelationCaptureWitness

/-!
# A guard that fails loudly if substitution captures

The witnesses elsewhere record what the current operation does.  A record does
not protect anything: an implementation can be changed, agree with the record,
and still be wrong.  This module states the *correct* answer positively, on a
program whose meaning visibly depends on getting substitution right, so that any
implementation which captures fails a theorem rather than passing quietly.

The program is eta-expansion of the identity.  Eta-expanding `z` should give a
function that hands its argument to `z`:

    lambda z. eta(z)   ~>   lambda z. lambda x. app(z, x)

A capturing substitution instead produces

    lambda z. lambda x. app(x, x)

which is a different function, and visibly so: the correct one *uses* the value
supplied for `z`, and the captured one ignores it and applies its own bound
variable to itself.  The identity has become self-application.  Both theorems
are stated below, so the difference is a fact about the two terms rather than a
remark about indices.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Binding.PatternPresentation

set_option autoImplicit false

namespace SubstitutionGuard

/-- `eta(F)  ~>  lambda x. app(F, x)`.  The matched subterm moves one binder
deeper, which is the shape on which a depth-blind substitution is wrong. -/
def etaRule : RewriteRule where
  name := "eta-expand"
  typeContext := []
  premises := []
  left := .apply "eta" [.fvar "F"]
  right := .lambda (some "x") (.apply "app" [.fvar "F", .bvar 0])

def etaLang : LanguageDef where
  name := "eta"
  types := []
  terms := []
  equations := []
  rewrites := [etaRule]

/-- The redex, as it sits inside one enclosing binder. -/
def redex : Pattern := .apply "eta" [.bvar 0]

/-- What eta-expansion must produce: a function handing its argument to `z`. -/
def correctBody : Pattern :=
  .lambda (some "x") (.apply "app" [.bvar 1, .bvar 0])

/-- What a capturing substitution produces: self-application. -/
def capturedBody : Pattern :=
  .lambda (some "x") (.apply "app" [.bvar 0, .bvar 0])

/-- The whole program, closed. -/
def program : Pattern := .lambda (some "z") redex

def correctProgram : Pattern := .lambda (some "z") correctBody

def capturedProgram : Pattern := .lambda (some "z") capturedBody

/-! ## The guard

The first theorem is the one that protects the semantics: it names the answer
that a correct substitution must give.  It is proved through the binding
signature, where the metavariable's arity records its one-variable body
context. The schema explicitly applies it to the enclosing variable, and
instantiation performs the corresponding weakening rather than recovering a
permission context from a capture-depth traversal. -/

/-- The rule's metavariable, matched one binder deep. -/
abbrev etaMetas : List (MetaArity patSig) := [([PatSrt.pat], PatSrt.pat)]

abbrev etaSchemaSig : Signature := withMetas patSig etaMetas

/-- `lambda x. app(F[z], x)` -- `F` is applied to the *enclosing* binder. -/
def etaRhsSchema : Term etaSchemaSig [PatSrt.pat] PatSrt.pat :=
  Term.op (S := etaSchemaSig) (Sum.inl (PatOp.lamOp (some "x")))
    (.cons
      (Term.op (S := etaSchemaSig) (Sum.inl (PatOp.applyOp "app" 2))
        (.cons
          (Term.op (S := etaSchemaSig) (Sum.inr (MetaOp.mk ⟨0, by decide⟩))
            (.cons (Term.var (Var.succ Var.zero)) .nil))
          (.cons (Term.var Var.zero) .nil)))
      .nil)

/-- The matched value: the enclosing binder's own variable. -/
def etaBody : (i : Fin etaMetas.length) →
    Term patSig (etaMetas.get i).1 (etaMetas.get i).2
  | ⟨0, _⟩ => Term.var Var.zero
  | ⟨_ + 2, h⟩ => by simp [etaMetas] at h

/-- **THE GUARD.**  Eta-expansion of the identity is the identity,
eta-expanded.  Any substitution that captures fails this. -/
theorem eta_expansion_is_correct :
    erase (instantiate etaBody etaRhsSchema) = correctBody := rfl

/-- **And the engine produces it.**  This is the guard doing its job: before
rule firing shifted a matched value across the binders it is inserted under, the
engine produced `capturedBody` here, in which the eta-expanded identity had
become self-application. -/
theorem engine_is_correct : rewriteStep etaLang redex = [correctBody] := by
  decide +kernel

/-- The capturing answer is no longer produced. -/
theorem captured_ne_correct : capturedBody ≠ correctBody := by decide

/-- The capturing answer is no longer produced. -/
theorem engine_does_not_capture : rewriteStep etaLang redex ≠ [capturedBody] := by
  rw [engine_is_correct]
  intro h
  exact captured_ne_correct (by injection h with h1; exact h1.symm)

/-! ## Why the difference is semantic and not a matter of indices

Supply a value for the enclosing binder.  The correct reduct hands that value to
its argument; the captured one never looks at it. -/

def suppliedValue : Pattern := .apply "c" []

/-- **The correct function uses what it is given.** -/
theorem correct_uses_its_argument :
    instantiateBVar suppliedValue correctBody
      = .lambda (some "x") (.apply "app" [suppliedValue, .bvar 0]) := by
  decide +kernel

/-- **The captured function ignores it**, and applies its own bound variable to
itself: the identity has become self-application. -/
theorem captured_ignores_its_argument :
    instantiateBVar suppliedValue capturedBody
      = .lambda (some "x") (.apply "app" [.bvar 0, .bvar 0]) := by
  decide +kernel

/-- **And it ignores every value equally**, which is the precise sense in which
a function was replaced by a different one. -/
theorem captured_ignores_every_argument (v : Pattern) :
    instantiateBVar v capturedBody = capturedBody := by
  simp [instantiateBVar, instantiateBVarAt, capturedBody]

theorem captured_is_constant_in_its_argument (v w : Pattern) :
    instantiateBVar v capturedBody = instantiateBVar w capturedBody := by
  rw [captured_ignores_every_argument v, captured_ignores_every_argument w]

/-- Whereas the correct one is not. -/
theorem correct_is_not_constant :
    instantiateBVar (.apply "c" []) correctBody
      ≠ instantiateBVar (.apply "d" []) correctBody := by
  decide +kernel

/-! ## The guard at the level of whole programs -/

theorem programs_differ : correctProgram ≠ capturedProgram := by decide

theorem both_programs_closed :
    correctProgram.isWellScopedAt 0 = true ∧ capturedProgram.isWellScopedAt 0 = true := by
  constructor
  · decide +kernel
  · decide +kernel

/-! ## A guard the obvious repair also fails

The guard above is passed by a substitution that weakens a matched value by the
number of binders it has passed on the right-hand side, because this rule's
left-hand side binds nothing: the value is matched at the ambient depth and one
binder is introduced, so "weaken by the binders passed" happens to be right.

A congruence rule is not like that.  Congruence here is written per term former,
so eta-expanding *under an abstraction* is a rule a user writes, and its
left-hand side binds.  The value is then matched one binder deep and only one
binder is new, while two have been passed -- so the naive weakening is one too
many, and the naive non-weakening is one too few.  Only the amount the type
knows is right.

    lambda z. F   ~>   lambda z. lambda y. app(F, y)

    on  lambda z. z:

      correct                  lambda z. lambda y. app(z, y)
      no weakening             lambda z. lambda y. app(y, y)    captured
      weaken by binders passed lambda z. lambda y. app(?, y)    escapes
-/

namespace UnderBinder

/-- Eta-expansion of an abstraction's body, written as a congruence rule -- the
way congruence is expressed in this engine. -/
def lamEtaRule : RewriteRule where
  name := "eta-under-lambda"
  typeContext := []
  premises := []
  left := .lambda (some "z") (.fvar "F")
  right := .lambda (some "z") (.lambda (some "y") (.apply "app" [.fvar "F", .bvar 0]))

def lamEtaLang : LanguageDef where
  name := "eta-under-lambda"
  types := []
  terms := []
  equations := []
  rewrites := [lamEtaRule]

/-- The identity, closed. -/
def identity : Pattern := .lambda (some "z") (.bvar 0)

/-- What eta-expanding its body must give: still the identity. -/
def correctResult : Pattern :=
  .lambda (some "z") (.lambda (some "y") (.apply "app" [.bvar 1, .bvar 0]))

/-- What no weakening gives: the argument applied to itself. -/
def capturedResult : Pattern :=
  .lambda (some "z") (.lambda (some "y") (.apply "app" [.bvar 0, .bvar 0]))

/-- What weakening by the binders passed gives: an index with nothing to name. -/
def escapedResult : Pattern :=
  .lambda (some "z") (.lambda (some "y") (.apply "app" [.bvar 2, .bvar 0]))

abbrev metasF : List (MetaArity patSig) := [([PatSrt.pat], PatSrt.pat)]

abbrev schemaSigF : Signature := withMetas patSig metasF

/-- `lambda z. lambda y. app(F[z], y)`: `F` is applied to the binder it was
matched under, and to nothing else. -/
def lamEtaSchema : Term schemaSigF [] PatSrt.pat :=
  Term.op (S := schemaSigF) (Sum.inl (PatOp.lamOp (some "z")))
    (.cons
      (Term.op (S := schemaSigF) (Sum.inl (PatOp.lamOp (some "y")))
        (.cons
          (Term.op (S := schemaSigF) (Sum.inl (PatOp.applyOp "app" 2))
            (.cons
              (Term.op (S := schemaSigF) (Sum.inr (MetaOp.mk ⟨0, by decide⟩))
                (.cons (Term.var (Var.succ Var.zero)) .nil))
              (.cons (Term.var Var.zero) .nil)))
          .nil))
      .nil)

/-- The matched body of the identity: the binder's own variable. -/
def lamEtaBody : (i : Fin metasF.length) →
    Term patSig (metasF.get i).1 (metasF.get i).2
  | ⟨0, _⟩ => Term.var Var.zero
  | ⟨_ + 2, h⟩ => by simp [metasF] at h

/-- **THE GUARD.**  Eta-expanding the body of the identity leaves the
identity. -/
theorem eta_under_lambda_is_correct :
    erase (instantiate lamEtaBody lamEtaSchema) = correctResult := rfl

/-- **And the engine produces it**, at the depth that separates the two wrong
answers: the value was matched one binder deep and is used two deep, so the
shift is one, where leaving it alone captures and lifting by two escapes. -/
theorem engine_is_correct_under_binder :
    rewriteStep lamEtaLang identity = [correctResult] := by
  decide +kernel

/-- **All three are different**, so the guard separates the correct answer from
both wrong ones rather than only from the current one. -/
theorem three_way_separation :
    correctResult ≠ capturedResult ∧ correctResult ≠ escapedResult
      ∧ capturedResult ≠ escapedResult := by
  refine ⟨by decide, by decide, by decide⟩

/-- The answer that weakens by the binders passed is not even closed. -/
theorem escaped_is_open : escapedResult.isWellScopedAt 0 = false := by decide +kernel

theorem correct_is_closed : correctResult.isWellScopedAt 0 = true := by decide +kernel

/-! ### The semantic reading

Supply a value for `z`.  The correct answer hands it to its argument; the
captured answer never looks at it. -/

theorem correct_uses_z :
    instantiateBVar (.apply "c" []) (.lambda (some "y") (.apply "app" [.bvar 1, .bvar 0]))
      = .lambda (some "y") (.apply "app" [.apply "c" [], .bvar 0]) := by
  decide +kernel

theorem captured_ignores_z (v : Pattern) :
    instantiateBVar v (.lambda (some "y") (.apply "app" [.bvar 0, .bvar 0]))
      = .lambda (some "y") (.apply "app" [.bvar 0, .bvar 0]) := by
  simp [instantiateBVar, instantiateBVarAt]

end UnderBinder

end SubstitutionGuard

namespace ScopeIndexControls

/-- A sort-correct permutation can exchange an enclosing variable with a
newly bound variable of the same sort. It is a contextual renaming, not a
binder-preserving lift. -/
def swapSameSort {S : Signature} (s : S.Srt) : Ren S [s, s] [s, s]
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero

/-- The defined lift fixes the binder and retains the enclosing variable's
identity. -/
theorem correct_lift_preserves_ambient_identity {S : Signature} (s : S.Srt) :
    liftRen (fun _ v => v) [s] s
      (Var.succ (Var.zero : Var [s] s)) = Var.succ Var.zero := rfl

/-- Intrinsic scope indices alone do not uniquely determine the correct
lift: a well-typed map can instead point at the newly bound variable. -/
theorem scope_types_do_not_force_binder_preservation {S : Signature} (s : S.Srt) :
    ∃ typedMap : Ren S [s, s] [s, s],
      typedMap s (Var.succ Var.zero) = Var.zero ∧
        typedMap s (Var.succ Var.zero) ≠
          liftRen (fun _ v => v) [s] s (Var.succ Var.zero) := by
  refine ⟨swapSameSort s, rfl, ?_⟩
  intro equal
  change Var.zero = Var.succ Var.zero at equal
  cases equal

#print axioms correct_lift_preserves_ambient_identity
#print axioms scope_types_do_not_force_binder_preservation

end ScopeIndexControls

end Mettapedia.OSLF.Binding
