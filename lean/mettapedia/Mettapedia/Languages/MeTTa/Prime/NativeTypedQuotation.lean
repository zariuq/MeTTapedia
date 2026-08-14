import Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
import Std.Data.String.ToNat

/-!
# Proof-producing typed quotations for MeTTa Native

`metta%` already turns authored MeTTa expressions into kernel-checked
`Pattern` constructor trees.  This module adds a deliberately partial,
intrinsically scoped elaboration layer for the dependent fragment used by
Prime protocols.

The bridge is stage-uniform.  It does not check a term only at interpreter
stage zero and then assume that the result remains valid at other stages.
Instead, `NativeCode` is interpreted at every stage, and every successful
`Inferred` value contains a native typing derivation for every stage.  This
is exactly the evidence required by native application and let-elimination.

The supported authored forms are:

* `(native:u0)`;
* `(native:u1)`, which reports that the current hierarchy has no higher
  universe rather than fabricating one;
* `(native:var n)` for a scoped de Bruijn variable;
* `(native:pi A B)` and `(native:sigma A B)`;
* `(native:lam A body)` with an explicit domain annotation;
* `(native:app function argument)`;
* `(native:id A left right)` and `(native:refl term)`;
* `(native:let value body)`;
* `(native:superpose left right)`;
* `(native:pattern expression)` for a runtime MeTTa value.

Other MeTTa remains executable through the raw plan.  Rejection here means
only that this proof-producing accelerator does not certify the expression;
it never withdraws the raw execution path.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation

open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.NativeTypeTheory.NativeModalTyping
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev RuntimePattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-! ## Stage-neutral, intrinsically scoped native code -/

/-- The dependent protocol fragment before choosing an interpreter stage.

The domain annotation on `lam` is elaboration data.  Its interpretation is
the native lambda constructor, while its inferred type retains the domain in
the resulting dependent product. -/
inductive NativeCode : Nat → Type where
  | var {binders : Nat} : Fin binders → NativeCode binders
  | u0 {binders : Nat} : NativeCode binders
  | u1 {binders : Nat} : NativeCode binders
  | pi {binders : Nat} : NativeCode binders → NativeCode (binders + 1) →
      NativeCode binders
  | sigma {binders : Nat} : NativeCode binders → NativeCode (binders + 1) →
      NativeCode binders
  | lam {binders : Nat} : NativeCode binders → NativeCode (binders + 1) →
      NativeCode binders
  | app {binders : Nat} : NativeCode binders → NativeCode binders →
      NativeCode binders
  | id {binders : Nat} : NativeCode binders → NativeCode binders →
      NativeCode binders → NativeCode binders
  | refl {binders : Nat} : NativeCode binders → NativeCode binders
  | letE {binders : Nat} : NativeCode binders → NativeCode (binders + 1) →
      NativeCode binders
  | pattern {binders : Nat} : RuntimePattern → NativeCode binders
  | superpose {binders : Nat} : NativeCode binders → NativeCode binders →
      NativeCode binders
deriving Repr, DecidableEq

namespace NativeCode

/-- Interpret one code at an explicitly selected stage. -/
def interpret (stage : Nat) : NativeCode binders → NativeRawTm stage binders
  | .var index => .var index
  | .u0 => .u0
  | .u1 => .u1
  | .pi domain body => .pi (domain.interpret stage) (body.interpret stage)
  | .sigma domain body =>
      .sigma (domain.interpret stage) (body.interpret stage)
  | .lam _ body => .lam (body.interpret stage)
  | .app function argument =>
      .app (function.interpret stage) (argument.interpret stage)
  | .id type left right =>
      .id (type.interpret stage) (left.interpret stage)
        (right.interpret stage)
  | .refl term => .refl (term.interpret stage)
  | .letE value body => .letE (value.interpret stage) (body.interpret stage)
  | .pattern value => .pattern value
  | .superpose left right =>
      .superpose (left.interpret stage) (right.interpret stage)

/-- The coherent native term family denoted by one code. -/
def family (code : NativeCode binders) : TermFamily binders :=
  fun stage => code.interpret stage

abbrev Ren (source target : Nat) := Fin source → Fin target

def liftRen (rho : Ren source target) :
    Ren (source + 1) (target + 1) :=
  nativeLiftRen rho

theorem liftRen_eq_nativeLiftRen (rho : Ren source target) :
    liftRen rho = nativeLiftRen rho :=
  rfl

def rename (rho : Ren source target) :
    NativeCode source → NativeCode target
  | .var index => .var (rho index)
  | .u0 => .u0
  | .u1 => .u1
  | .pi domain body =>
      .pi (rename rho domain) (rename (liftRen rho) body)
  | .sigma domain body =>
      .sigma (rename rho domain) (rename (liftRen rho) body)
  | .lam domain body =>
      .lam (rename rho domain) (rename (liftRen rho) body)
  | .app function argument =>
      .app (rename rho function) (rename rho argument)
  | .id type left right =>
      .id (rename rho type) (rename rho left)
        (rename rho right)
  | .refl term => .refl (rename rho term)
  | .letE value body =>
      .letE (rename rho value) (rename (liftRen rho) body)
  | .pattern value => .pattern value
  | .superpose left right =>
      .superpose (rename rho left) (rename rho right)

theorem interpret_rename (rho : Ren source target)
    (code : NativeCode source) (stage : Nat) :
    (rename rho code).interpret stage =
      nativeRename rho (code.interpret stage) := by
  induction code generalizing target with
  | var index => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [rename, interpret, nativeRename]
      rw [domainIH, bodyIH]
      rw [liftRen_eq_nativeLiftRen]
  | sigma domain body domainIH bodyIH =>
      simp only [rename, interpret, nativeRename]
      rw [domainIH, bodyIH]
      rw [liftRen_eq_nativeLiftRen]
  | lam domain body domainIH bodyIH =>
      simp only [rename, interpret, nativeRename]
      rw [bodyIH]
      rw [liftRen_eq_nativeLiftRen]
  | app function argument functionIH argumentIH =>
      simp only [rename, interpret, nativeRename]
      rw [functionIH, argumentIH]
  | id type left right typeIH leftIH rightIH =>
      simp only [rename, interpret, nativeRename]
      rw [typeIH, leftIH, rightIH]
  | refl term termIH =>
      simp only [rename, interpret, nativeRename]
      rw [termIH]
  | letE value body valueIH bodyIH =>
      simp only [rename, interpret, nativeRename]
      rw [valueIH, bodyIH]
      rw [liftRen_eq_nativeLiftRen]
  | pattern value => rfl
  | superpose left right leftIH rightIH =>
      simp only [rename, interpret, nativeRename]
      rw [leftIH, rightIH]

abbrev Sub (source target : Nat) := Fin source → NativeCode target

def liftSub (substitution : Sub source target) :
    Sub (source + 1) (target + 1) :=
  Fin.cases (.var 0)
    (fun index => rename Fin.succ (substitution index))

def subst (substitution : Sub source target) :
    NativeCode source → NativeCode target
  | .var index => substitution index
  | .u0 => .u0
  | .u1 => .u1
  | .pi domain body =>
      .pi (subst substitution domain) (subst (liftSub substitution) body)
  | .sigma domain body =>
      .sigma (subst substitution domain) (subst (liftSub substitution) body)
  | .lam domain body =>
      .lam (subst substitution domain) (subst (liftSub substitution) body)
  | .app function argument =>
      .app (subst substitution function) (subst substitution argument)
  | .id type left right =>
      .id (subst substitution type) (subst substitution left)
        (subst substitution right)
  | .refl term => .refl (subst substitution term)
  | .letE value body =>
      .letE (subst substitution value) (subst (liftSub substitution) body)
  | .pattern value => .pattern value
  | .superpose left right =>
      .superpose (subst substitution left) (subst substitution right)

def interpretedSub (substitution : Sub source target) :
    NativeSub source target :=
  fun stage index => (substitution index).interpret stage

theorem interpretedSub_lift (substitution : Sub source target) :
    interpretedSub (liftSub substitution) =
      nativeLiftSub (interpretedSub substitution) := by
  funext stage index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    exact interpret_rename Fin.succ (substitution previous) stage

theorem interpret_subst (substitution : Sub source target)
    (code : NativeCode source) (stage : Nat) :
    (subst substitution code).interpret stage =
      nativeSubst (interpretedSub substitution) (code.interpret stage) := by
  induction code generalizing target with
  | var index => rfl
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp only [subst, interpret, nativeSubst]
      rw [domainIH, bodyIH, interpretedSub_lift]
  | sigma domain body domainIH bodyIH =>
      simp only [subst, interpret, nativeSubst]
      rw [domainIH, bodyIH, interpretedSub_lift]
  | lam domain body domainIH bodyIH =>
      simp only [subst, interpret, nativeSubst]
      rw [bodyIH, interpretedSub_lift]
  | app function argument functionIH argumentIH =>
      simp only [subst, interpret, nativeSubst]
      rw [functionIH, argumentIH]
  | id type left right typeIH leftIH rightIH =>
      simp only [subst, interpret, nativeSubst]
      rw [typeIH, leftIH, rightIH]
  | refl term termIH =>
      simp only [subst, interpret, nativeSubst]
      rw [termIH]
  | letE value body valueIH bodyIH =>
      simp only [subst, interpret, nativeSubst]
      rw [valueIH, bodyIH, interpretedSub_lift]
  | pattern value => rfl
  | superpose left right leftIH rightIH =>
      simp only [subst, interpret, nativeSubst]
      rw [leftIH, rightIH]

/-- Substitute the newest variable by a closed-over code family. -/
def inst0 (argument : NativeCode binders)
    (body : NativeCode (binders + 1)) : NativeCode binders :=
  subst (Fin.cases argument (fun index => .var index)) body

theorem interpret_inst0 (argument : NativeCode binders)
    (body : NativeCode (binders + 1)) (stage : Nat) :
    (inst0 argument body).interpret stage =
      NativeModalTyping.inst0 argument.family (body.interpret stage) := by
  rw [inst0, interpret_subst]
  apply congrArg (fun substitution =>
    nativeSubst substitution (body.interpret stage))
  funext current index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

end NativeCode

/-! ## Stage-uniform contexts and typing evidence -/

/-- A telescope whose entries use the same stage-neutral code. -/
inductive CodeContext : Nat → Type where
  | nil : CodeContext 0
  | snoc : CodeContext binders → NativeCode binders →
      CodeContext (binders + 1)

namespace CodeContext

def interpret : CodeContext binders → NativeModalTyping.Context binders
  | .nil => .nil
  | .snoc context type => .snoc context.interpret type.family

def lookup : CodeContext binders → Fin binders → NativeCode binders
  | .nil, index => nomatch index
  | .snoc context type, index =>
      Fin.cases (NativeCode.rename Fin.succ type)
        (fun previous => NativeCode.rename Fin.succ (context.lookup previous))
        index

theorem interpret_lookup (context : CodeContext binders)
    (index : Fin binders) (stage : Nat) :
    (context.lookup index).interpret stage =
      NativeModalTyping.Context.lookup context.interpret stage index := by
  induction context with
  | nil => exact Fin.elim0 index
  | @snoc binders context type contextIH =>
      refine Fin.cases ?_ ?_ index
      · exact NativeCode.interpret_rename Fin.succ type stage
      · intro previous
        change
          (NativeCode.rename Fin.succ
            (context.lookup previous)).interpret stage =
          nativeRename nativeWk
            (NativeModalTyping.Context.lookup context.interpret stage previous)
        rw [NativeCode.interpret_rename, contextIH]
        apply nativeRename_ext
        intro variableIndex
        change Fin.succ variableIndex = Fin.succ variableIndex
        rfl

end CodeContext

/-- Successful inference retains a native derivation at every stage. -/
structure Inferred (context : CodeContext binders)
    (term : NativeCode binders) where
  type : NativeCode binders
  typing : ∀ stage,
    NativeModalTyping.HasType syntacticConversion context.interpret
      (term.interpret stage) (type.interpret stage)

/-- A typing derivation repackaged in `Type`, so it may be returned by the
executable elaborator without erasing its proof field. -/
structure ExpectedTyping (context : CodeContext binders)
    (term expected : NativeCode binders) : Type where
  typing : ∀ stage,
    NativeModalTyping.HasType syntacticConversion context.interpret
      (term.interpret stage) (expected.interpret stage)

/-! ## Structured failures -/

/-- The reason attached to a precise child path in the authored expression. -/
inductive FailureReason where
  | unsupportedForm (head : String)
  | wrongArity (head : String) (expected actual : Nat)
  | invalidIndex (token : String)
  | variableOutOfScope (index binders : Nat)
  | expectedUniverse
  | expectedFunction
  | typeMismatch
  | topUniverseHasNoType
deriving Repr, DecidableEq

/-- Child indices are stored outermost first. -/
structure Failure where
  path : List Nat
  reason : FailureReason
deriving Repr, DecidableEq

namespace Failure

def FailureReason.render : FailureReason → String
  | .unsupportedForm head => s!"unsupportedForm({head})"
  | .wrongArity head expected actual =>
      s!"wrongArity({head}, expected {expected}, got {actual})"
  | .invalidIndex token => s!"invalidIndex({token})"
  | .variableOutOfScope index binders =>
      s!"variableOutOfScope({index}, binders {binders})"
  | .expectedUniverse => "expectedUniverse"
  | .expectedFunction => "expectedFunction"
  | .typeMismatch => "typeMismatch"
  | .topUniverseHasNoType => "topUniverseHasNoType"

def atChild (index : Nat) (failure : Failure) : Failure :=
  { failure with path := index :: failure.path }

def here (reason : FailureReason) : Failure := ⟨[], reason⟩

/-- Stable human-readable diagnostic used by the typed quotation elaborator. -/
def render (failure : Failure) : String :=
  s!"child path {failure.path}: {FailureReason.render failure.reason}"

end Failure

private def expectType {context : CodeContext binders}
    {term : NativeCode binders} (inferred : Inferred context term)
    (expected : NativeCode binders) :
    Except Failure (ExpectedTyping context term expected) :=
  if equal : inferred.type = expected then
    .ok ⟨equal ▸ inferred.typing⟩
  else
    .error (Failure.here .typeMismatch)

/-- Proof-producing inference for the supported dependent fragment. -/
def infer (context : CodeContext binders) :
    (term : NativeCode binders) → Except Failure (Inferred context term)
  | .var index => .ok
      { type := context.lookup index
        typing := fun stage => by
          change NativeModalTyping.HasType syntacticConversion
            context.interpret (.var index)
              ((context.lookup index).interpret stage)
          rw [CodeContext.interpret_lookup]
          exact NativeModalTyping.HasType.var index }
  | .u0 => .ok
      { type := .u1
        typing := fun _ => NativeModalTyping.HasType.u0_type context.interpret }
  | .u1 => .error (Failure.here .topUniverseHasNoType)
  | .pi domain body => do
      let domainInferred ←
        (infer context domain).mapError (Failure.atChild 0)
      let domainUniverse ←
        (expectType domainInferred (.u1 : NativeCode binders)).mapError
          (fun _ => Failure.atChild 0 (Failure.here .expectedUniverse))
      let bodyInferred ←
        (infer (.snoc context domain) body).mapError (Failure.atChild 1)
      let bodyUniverse ←
        (expectType bodyInferred (.u1 : NativeCode (binders + 1))).mapError
          (fun _ => Failure.atChild 1 (Failure.here .expectedUniverse))
      .ok
        { type := .u1
          typing := fun stage =>
            NativeModalTyping.HasType.pi_form
              (domain := domain.family) (domainUniverse.typing stage)
              (bodyUniverse.typing stage) }
  | .sigma domain body => do
      let domainInferred ←
        (infer context domain).mapError (Failure.atChild 0)
      let domainUniverse ←
        (expectType domainInferred (.u1 : NativeCode binders)).mapError
          (fun _ => Failure.atChild 0 (Failure.here .expectedUniverse))
      let bodyInferred ←
        (infer (.snoc context domain) body).mapError (Failure.atChild 1)
      let bodyUniverse ←
        (expectType bodyInferred (.u1 : NativeCode (binders + 1))).mapError
          (fun _ => Failure.atChild 1 (Failure.here .expectedUniverse))
      .ok
        { type := .u1
          typing := fun stage =>
            NativeModalTyping.HasType.sigma_form
              (domain := domain.family) (domainUniverse.typing stage)
              (bodyUniverse.typing stage) }
  | .lam domain body => do
      let domainInferred ←
        (infer context domain).mapError (Failure.atChild 0)
      let _domainUniverse ←
        (expectType domainInferred (.u1 : NativeCode binders)).mapError
          (fun _ => Failure.atChild 0 (Failure.here .expectedUniverse))
      let bodyInferred ←
        (infer (.snoc context domain) body).mapError (Failure.atChild 1)
      .ok
        { type := .pi domain bodyInferred.type
          typing := fun stage =>
            NativeModalTyping.HasType.lam_intro
              (domain := domain.family) (bodyInferred.typing stage) }
  | .app function argument => do
      let functionInferred ←
        (infer context function).mapError (Failure.atChild 0)
      match functionTypeEq : functionInferred.type with
      | .pi domain bodyType => do
          let argumentInferred ←
            (infer context argument).mapError (Failure.atChild 1)
          let argumentTyping ←
            (expectType argumentInferred domain).mapError
              (fun _ => Failure.atChild 1 (Failure.here .typeMismatch))
          .ok
            { type := NativeCode.inst0 argument bodyType
              typing := fun stage => by
                rw [NativeCode.interpret_inst0]
                have functionTyping := functionInferred.typing stage
                rw [functionTypeEq] at functionTyping
                exact NativeModalTyping.HasType.app_elim
                  (argument := argument.family) (domain := domain.family)
                  functionTyping
                  argumentTyping.typing }
      | _ => .error (Failure.atChild 0 (Failure.here .expectedFunction))
  | .id type left right => do
      let typeInferred ←
        (infer context type).mapError (Failure.atChild 0)
      let typeUniverse ←
        (expectType typeInferred (.u1 : NativeCode binders)).mapError
          (fun _ => Failure.atChild 0 (Failure.here .expectedUniverse))
      let leftInferred ←
        (infer context left).mapError (Failure.atChild 1)
      let leftTyping ←
        (expectType leftInferred type).mapError
          (fun _ => Failure.atChild 1 (Failure.here .typeMismatch))
      let rightInferred ←
        (infer context right).mapError (Failure.atChild 2)
      let rightTyping ←
        (expectType rightInferred type).mapError
          (fun _ => Failure.atChild 2 (Failure.here .typeMismatch))
      .ok
        { type := .u1
          typing := fun stage => NativeModalTyping.HasType.id_form
            (typeUniverse.typing stage) (leftTyping.typing stage)
            (rightTyping.typing stage) }
  | .refl term => do
      let termInferred ←
        (infer context term).mapError (Failure.atChild 0)
      .ok
        { type := .id termInferred.type term term
          typing := fun stage => NativeModalTyping.HasType.refl_intro
            (termInferred.typing stage) }
  | .letE value body => do
      let valueInferred ←
        (infer context value).mapError (Failure.atChild 0)
      let bodyInferred ←
        (infer (.snoc context valueInferred.type) body).mapError
          (Failure.atChild 1)
      .ok
        { type := NativeCode.inst0 value bodyInferred.type
          typing := fun stage => by
            rw [NativeCode.interpret_inst0]
            exact NativeModalTyping.HasType.let_intro
              (value := value.family) (valueType := valueInferred.type.family)
              valueInferred.typing (bodyInferred.typing stage) }
  | .pattern value => .ok
      { type := .u0
        typing := fun _ =>
          NativeModalTyping.HasType.pattern_intro context.interpret value }
  | .superpose left right => do
      let leftInferred ←
        (infer context left).mapError (Failure.atChild 0)
      let rightInferred ←
        (infer context right).mapError (Failure.atChild 1)
      let rightTyping ←
        (expectType rightInferred leftInferred.type).mapError
          (fun _ => Failure.atChild 1 (Failure.here .typeMismatch))
      .ok
        { type := leftInferred.type
          typing := fun stage => NativeModalTyping.HasType.superpose_intro
            (leftInferred.typing stage) (rightTyping.typing stage) }

/-! ## Pattern grammar -/

private def parseIndexToken : RuntimePattern → Option Nat
  | .apply "0" [] => some 0
  | .apply "1" [] => some 1
  | .apply "2" [] => some 2
  | .apply "3" [] => some 3
  | .apply "4" [] => some 4
  | .apply "5" [] => some 5
  | .apply "6" [] => some 6
  | .apply "7" [] => some 7
  | .apply "8" [] => some 8
  | .apply "9" [] => some 9
  | .fvar "0" => some 0
  | .fvar "1" => some 1
  | .fvar "2" => some 2
  | .fvar "3" => some 3
  | .fvar "4" => some 4
  | .fvar "5" => some 5
  | .fvar "6" => some 6
  | .fvar "7" => some 7
  | .fvar "8" => some 8
  | .fvar "9" => some 9
  | .apply token [] => token.toNat?
  | .fvar token => token.toNat?
  | _ => none

private theorem parseIndexToken_nat_repr (index : Nat) :
    parseIndexToken (.apply (Nat.repr index) []) = some index := by
  by_cases h0 : index = 0
  · subst index; rfl
  by_cases h1 : index = 1
  · subst index; rfl
  by_cases h2 : index = 2
  · subst index; rfl
  by_cases h3 : index = 3
  · subst index; rfl
  by_cases h4 : index = 4
  · subst index; rfl
  by_cases h5 : index = 5
  · subst index; rfl
  by_cases h6 : index = 6
  · subst index; rfl
  by_cases h7 : index = 7
  · subst index; rfl
  by_cases h8 : index = 8
  · subst index; rfl
  by_cases h9 : index = 9
  · subst index; rfl
  have hr0 : index.repr ≠ "0" :=
    fun equality => h0 (Nat.repr_injective equality)
  have hr1 : index.repr ≠ "1" :=
    fun equality => h1 (Nat.repr_injective equality)
  have hr2 : index.repr ≠ "2" :=
    fun equality => h2 (Nat.repr_injective equality)
  have hr3 : index.repr ≠ "3" :=
    fun equality => h3 (Nat.repr_injective equality)
  have hr4 : index.repr ≠ "4" :=
    fun equality => h4 (Nat.repr_injective equality)
  have hr5 : index.repr ≠ "5" :=
    fun equality => h5 (Nat.repr_injective equality)
  have hr6 : index.repr ≠ "6" :=
    fun equality => h6 (Nat.repr_injective equality)
  have hr7 : index.repr ≠ "7" :=
    fun equality => h7 (Nat.repr_injective equality)
  have hr8 : index.repr ≠ "8" :=
    fun equality => h8 (Nat.repr_injective equality)
  have hr9 : index.repr ≠ "9" :=
    fun equality => h9 (Nat.repr_injective equality)
  simp [parseIndexToken]

private def arityFailure (head : String) (expected : Nat)
    (arguments : List RuntimePattern) : Except Failure α :=
  .error (Failure.here (.wrongArity head expected arguments.length))

/-- Parse the explicit `native:*` grammar into an intrinsically scoped code.
Runtime payloads below `native:pattern` are retained as ordinary MeTTa
patterns rather than interpreted as type syntax. -/
def parseCode : (binders : Nat) → RuntimePattern →
    Except Failure (NativeCode binders)
  | _, .apply "native:u0" [] => .ok .u0
  | _, .apply "native:u0" arguments => arityFailure "native:u0" 0 arguments
  | _, .apply "native:u1" [] => .ok .u1
  | _, .apply "native:u1" arguments => arityFailure "native:u1" 0 arguments
  | binders, .apply "native:var" [token] =>
      match parseIndexToken token with
      | none => .error (Failure.atChild 0
          (Failure.here (.invalidIndex (toString (repr token)))))
      | some index =>
          if inScope : index < binders then .ok (.var ⟨index, inScope⟩)
          else .error (Failure.atChild 0
            (Failure.here (.variableOutOfScope index binders)))
  | _, .apply "native:var" arguments => arityFailure "native:var" 1 arguments
  | binders, .apply "native:pi" [domain, body] => do
      let domainCode ← (parseCode binders domain).mapError (Failure.atChild 0)
      let bodyCode ←
        (parseCode (binders + 1) body).mapError (Failure.atChild 1)
      .ok (.pi domainCode bodyCode)
  | _, .apply "native:pi" arguments => arityFailure "native:pi" 2 arguments
  | binders, .apply "native:sigma" [domain, body] => do
      let domainCode ← (parseCode binders domain).mapError (Failure.atChild 0)
      let bodyCode ←
        (parseCode (binders + 1) body).mapError (Failure.atChild 1)
      .ok (.sigma domainCode bodyCode)
  | _, .apply "native:sigma" arguments =>
      arityFailure "native:sigma" 2 arguments
  | binders, .apply "native:lam" [domain, body] => do
      let domainCode ← (parseCode binders domain).mapError (Failure.atChild 0)
      let bodyCode ←
        (parseCode (binders + 1) body).mapError (Failure.atChild 1)
      .ok (.lam domainCode bodyCode)
  | _, .apply "native:lam" arguments => arityFailure "native:lam" 2 arguments
  | binders, .apply "native:app" [function, argument] => do
      let functionCode ←
        (parseCode binders function).mapError (Failure.atChild 0)
      let argumentCode ←
        (parseCode binders argument).mapError (Failure.atChild 1)
      .ok (.app functionCode argumentCode)
  | _, .apply "native:app" arguments => arityFailure "native:app" 2 arguments
  | binders, .apply "native:id" [type, left, right] => do
      let typeCode ← (parseCode binders type).mapError (Failure.atChild 0)
      let leftCode ← (parseCode binders left).mapError (Failure.atChild 1)
      let rightCode ← (parseCode binders right).mapError (Failure.atChild 2)
      .ok (.id typeCode leftCode rightCode)
  | _, .apply "native:id" arguments => arityFailure "native:id" 3 arguments
  | binders, .apply "native:refl" [term] => do
      let termCode ← (parseCode binders term).mapError (Failure.atChild 0)
      .ok (.refl termCode)
  | _, .apply "native:refl" arguments =>
      arityFailure "native:refl" 1 arguments
  | binders, .apply "native:let" [value, body] => do
      let valueCode ← (parseCode binders value).mapError (Failure.atChild 0)
      let bodyCode ←
        (parseCode (binders + 1) body).mapError (Failure.atChild 1)
      .ok (.letE valueCode bodyCode)
  | _, .apply "native:let" arguments => arityFailure "native:let" 2 arguments
  | binders, .apply "native:superpose" [left, right] => do
      let leftCode ← (parseCode binders left).mapError (Failure.atChild 0)
      let rightCode ← (parseCode binders right).mapError (Failure.atChild 1)
      .ok (.superpose leftCode rightCode)
  | _, .apply "native:superpose" arguments =>
      arityFailure "native:superpose" 2 arguments
  | _, .apply "native:pattern" [value] => .ok (.pattern value)
  | _, .apply "native:pattern" arguments =>
      arityFailure "native:pattern" 1 arguments
  | _, .apply head _ => .error (Failure.here (.unsupportedForm head))
  | _, pattern =>
      .error (Failure.here (.unsupportedForm (toString (repr pattern))))

namespace NativeCode

/-- Render intrinsically scoped native code back to the exact runtime-pattern
grammar accepted by `parseCode`. Runtime data beneath `native:pattern` is
retained without attempting to reinterpret or print it. -/
def renderPattern : NativeCode binders → RuntimePattern
  | .var index =>
      .apply "native:var" [.apply (Nat.repr index.val) []]
  | .u0 => .apply "native:u0" []
  | .u1 => .apply "native:u1" []
  | .pi domain body =>
      .apply "native:pi" [domain.renderPattern, body.renderPattern]
  | .sigma domain body =>
      .apply "native:sigma" [domain.renderPattern, body.renderPattern]
  | .lam domain body =>
      .apply "native:lam" [domain.renderPattern, body.renderPattern]
  | .app function argument =>
      .apply "native:app" [function.renderPattern, argument.renderPattern]
  | .id type left right =>
      .apply "native:id"
        [type.renderPattern, left.renderPattern, right.renderPattern]
  | .refl term => .apply "native:refl" [term.renderPattern]
  | .letE value body =>
      .apply "native:let" [value.renderPattern, body.renderPattern]
  | .pattern value => .apply "native:pattern" [value]
  | .superpose left right =>
      .apply "native:superpose" [left.renderPattern, right.renderPattern]

/-- The native grammar parser is a left inverse of its AST renderer for every
intrinsically scoped code. This is the general parser/renderer adequacy
theorem; it is not a finite collection of examples. -/
theorem parseCode_renderPattern (code : NativeCode binders) :
    parseCode binders code.renderPattern = .ok code := by
  induction code with
  | var index =>
      simp [renderPattern, parseCode, parseIndexToken_nat_repr, index.isLt]
  | u0 => rfl
  | u1 => rfl
  | pi domain body domainIH bodyIH =>
      simp [renderPattern, parseCode, domainIH, bodyIH, Except.mapError]
      rfl
  | sigma domain body domainIH bodyIH =>
      simp [renderPattern, parseCode, domainIH, bodyIH, Except.mapError]
      rfl
  | lam domain body domainIH bodyIH =>
      simp [renderPattern, parseCode, domainIH, bodyIH, Except.mapError]
      rfl
  | app function argument functionIH argumentIH =>
      simp [renderPattern, parseCode, functionIH, argumentIH, Except.mapError]
      rfl
  | id type left right typeIH leftIH rightIH =>
      simp [renderPattern, parseCode, typeIH, leftIH, rightIH, Except.mapError]
      rfl
  | refl term termIH =>
      simp [renderPattern, parseCode, termIH, Except.mapError]
      rfl
  | letE value body valueIH bodyIH =>
      simp [renderPattern, parseCode, valueIH, bodyIH, Except.mapError]
      rfl
  | pattern value => rfl
  | superpose left right leftIH rightIH =>
      simp [renderPattern, parseCode, leftIH, rightIH, Except.mapError]
      rfl

end NativeCode

/-- The result requested by the typed quotation crown: a closed native term,
its inferred native type, and an actual native typing derivation. -/
structure ClosedTyping where
  term : NativeRawTm 0 0
  type : NativeRawTm 0 0
  typing : NativeCanary.ClosedNativeTyping term type

/-- Elaborate one parsed MeTTa pattern into a closed native typing package. -/
def elaborate (pattern : RuntimePattern) : Except Failure ClosedTyping := do
  let code ← parseCode 0 pattern
  let inferred ← infer .nil code
  .ok
    { term := code.interpret 0
      type := inferred.type.interpret 0
      typing := inferred.typing 0 }

/-- Extract a successful elaboration.  The equality proof is normally `rfl`
for a compile-time quotation, so failure can never be silently coerced into a
typed value. -/
def requireSuccess (result : Except Failure α) (success : result.isOk = true) :
    α :=
  match result with
  | .ok value => value
  | .error failure => by
      exact Bool.noConfusion success

/-! ## Compile-time checked quotation -/

open Lean Elab Term

/-- `native%` first runs the explicit-dialect MeTTa parser and then the
proof-producing native elaborator.  A successful expansion contains only the
quoted constructor tree and native typing constructors; the elaborator and
parser are normalized out of the returned term.  A failure stops Lean
elaboration at the authored string with its child path and named reason. -/
elab "native% " dialect:ident source:str : term => do
  let parsed ←
    match dialect.getId.toString with
    | "petta" =>
        match parsePeTTaPattern source.getString with
        | .ok pattern => pure pattern
        | .error error =>
            throwErrorAt source "PeTTa parse failed: {error.render}"
    | "he" =>
        match parseHEPattern source.getString with
        | .ok pattern => pure pattern
        | .error error =>
            throwErrorAt source "HE parse failed: {error.render}"
    | other =>
        throwErrorAt dialect
          "unknown MeTTa dialect '{other}'; expected explicit 'petta' or 'he'"
  match elaborate parsed with
  | .error failure =>
      throwErrorAt source "MeTTa Native typing failed: {failure.render}"
  | .ok _ =>
      let expansion ←
        match dialect.getId.toString with
        | "petta" =>
            `(requireSuccess (elaborate (metta% petta $source)) (by decide))
        | "he" =>
            `(requireSuccess (elaborate (metta% he $source)) (by decide))
        | _ => unreachable!
      let elaborated ← Term.elabTerm expansion none
      Meta.reduceAll elaborated

/-! ## Positive and negative controls -/

/-- A dependent protocol: for each runtime request `x`, return a proof of
`Id U0 x x`.  Both the binder and the proof term are authored in MeTTa. -/
def dependentReceiptSource : RuntimePattern :=
  metta% petta
    "(native:lam (native:u0) (native:refl (native:var 0)))"

/-- The authored dependent protocol elaborates with kernel typing evidence. -/
def dependentReceiptTyping : ClosedTyping := by
  exact native% petta
    "(native:lam (native:u0) (native:refl (native:var 0)))"

/-- Applying the protocol to an authored request infers the corresponding
request-indexed identity type. -/
def appliedReceiptSource : RuntimePattern :=
  metta% petta
    "(native:app
        (native:lam (native:u0) (native:refl (native:var 0)))
        (native:pattern (request ticket-7 (payload datum))))"

def appliedReceiptTyping : ClosedTyping := by
  exact native% petta
    "(native:app
        (native:lam (native:u0) (native:refl (native:var 0)))
        (native:pattern (request ticket-7 (payload datum))))"

/--
error: MeTTa Native typing failed: child path [0]: expectedFunction
-/
#guard_msgs in
def rejectedApplication : ClosedTyping :=
  native% petta
    "(native:app (native:pattern request) (native:pattern datum))"

theorem appliedReceipt_type_is_request_indexed :
    appliedReceiptTyping.type =
      .id .u0
        (.pattern (metta% petta "(request ticket-7 (payload datum))"))
        (.pattern (metta% petta "(request ticket-7 (payload datum))")) :=
  rfl

/-- Negative: the de Bruijn index is rejected at its exact argument path. -/
example :
    elaborate (metta% petta "(native:refl (native:var 0))") =
      (Except.error ⟨[0, 0], .variableOutOfScope 0 0⟩ :
        Except Failure ClosedTyping) :=
  rfl

/-- Negative: applying a runtime pattern as though it were a function has a
named function-shape failure. -/
example :
    elaborate
        (metta% petta
          "(native:app (native:pattern request) (native:pattern datum))") =
      (Except.error ⟨[0], .expectedFunction⟩ :
        Except Failure ClosedTyping) :=
  rfl

/-- Typed evidence is optional: the same request pattern remains available
as an unchecked raw plan with no certification premise. -/
def rawRequestStillRuns : RawPlan (NativeRawTm 0 0) :=
  ⟨.pattern (metta% petta "(request ticket-7 (payload datum))")⟩

end Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
