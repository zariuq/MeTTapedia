import Mettapedia.Languages.MeTTa.PureKernel.RegularBidirectional

/-!
# Prime open lambda-Pi correspondence

This module is the theorem-side specification of the executable Prime
`PSynth` / `PCheck` fragment.  Lambda domains remain explicit elaboration
annotations, while `erase` maps accepted programs into the regular Pure
kernel, where annotations are not runtime terms.

Successful synthesis and checking construct `RegularHasType` derivations.
Consequently the executable judgment is not a second type theory: it is a
proof-producing presentation of the regular kernel on the stable open
lambda-Pi fragment.
-/

namespace Mettapedia.Languages.MeTTa.Prime.OpenLambdaPiCorrespondence

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

/-- Intrinsically scoped syntax accepted by the stable Prime lambda-Pi
judgment.  The domain stored by `lam` is elaboration data. -/
inductive AnnotatedTm : Nat → Type where
  | var {binders : Nat} : Fin binders → AnnotatedTm binders
  | u0 {binders : Nat} : AnnotatedTm binders
  | u1 {binders : Nat} : AnnotatedTm binders
  | pi {binders : Nat} : AnnotatedTm binders →
      AnnotatedTm (binders + 1) → AnnotatedTm binders
  | lam {binders : Nat} : AnnotatedTm binders →
      AnnotatedTm (binders + 1) → AnnotatedTm binders
  | app {binders : Nat} : AnnotatedTm binders →
      AnnotatedTm binders → AnnotatedTm binders
deriving DecidableEq, Repr

namespace AnnotatedTm

/-- Forget only lambda annotations; all computational constructors are
preserved exactly. -/
def erase : AnnotatedTm binders → PureTm binders
  | .var index => .var index
  | .u0 => .u0
  | .u1 => .u1
  | .pi domain body => .pi domain.erase body.erase
  | .lam _ body => .lam body.erase
  | .app function argument => .app function.erase argument.erase

end AnnotatedTm

/-- A synthesized open term, its regular-kernel type, and the formation
classification needed by exact conversion. -/
structure Inferred {binders : Nat} {context : Ctx binders}
    (term : AnnotatedTm binders) where
  type : PureTm binders
  typing : RegularHasType context term.erase type
  status : RegularTypeStatus context type

/-- Successful checking constructs exactly the requested kernel judgment. -/
structure Checked {binders : Nat} {context : Ctx binders}
    (term : AnnotatedTm binders) (expected : PureTm binders) : Type where
  typing : RegularHasType context term.erase expected

namespace Inferred

/-- Reclassify a term whose synthesized result is convertible to the top
sort as an ordinary type. -/
def asFormedType {context : Ctx binders} {term : AnnotatedTm binders}
    (inferred : Inferred (context := context) term)
    (regular : RegularCtx context) :
    Except RegularCheckError
      (PLift (RegularHasType context term.erase .u1)) :=
  if accepted : decideRegularConversion regular inferred.status (.top rfl) = true then
    pure ⟨.conv_sort inferred.typing
      ((decideRegularConversion_correct regular inferred.status (.top rfl)).1
        accepted)⟩
  else
    throw .expectedFormedType

/-- Extract the formation premise attached to every non-top synthesis
result. -/
def resultFormed {context : Ctx binders} {term : AnnotatedTm binders}
    (inferred : Inferred (context := context) term) :
    Except RegularCheckError
      (PLift (RegularHasType context inferred.type .u1)) :=
  match inferred.status with
  | .formed formed => pure ⟨formed⟩
  | .top _ => throw .expectedFormedType

end Inferred

mutual

/-- Proof-producing synthesis for the stable annotated open lambda-Pi
fragment. -/
def infer : {binders : Nat} → {context : Ctx binders} →
    (regular : RegularCtx context) → (term : AnnotatedTm binders) →
    Except RegularCheckError (Inferred (context := context) term)
  | _, context, regular, .var index =>
      pure
        { type := lookup context index
          typing := .var index
          status := .formed (regular.lookup_formed index) }
  | _, context, _, .u0 =>
      pure
        { type := .u1
          typing := .u0_type context
          status := .top rfl }
  | _, _, _, .u1 => throw .upperSortHasNoType
  | _, context, regular, .pi domain body => do
      let domainInfo ← infer regular domain
      let domainFormed ← domainInfo.asFormedType regular
      let extended : RegularCtx (.snoc context domain.erase) :=
        .snoc regular domainFormed.down
      let bodyInfo ← infer extended body
      let bodyFormed ← bodyInfo.asFormedType extended
      pure
        { type := .u1
          typing := .pi_form domainFormed.down bodyFormed.down
          status := .top rfl }
  | _, context, regular, .lam domain body => do
      let domainInfo ← infer regular domain
      let domainFormed ← domainInfo.asFormedType regular
      let extended : RegularCtx (.snoc context domain.erase) :=
        .snoc regular domainFormed.down
      let bodyInfo ← infer extended body
      let bodyTypeFormed ← bodyInfo.resultFormed
      let functionTypeFormed :=
        RegularHasType.pi_form domainFormed.down bodyTypeFormed.down
      pure
        { type := .pi domain.erase bodyInfo.type
          typing := .lam_intro domainFormed.down bodyTypeFormed.down
            bodyInfo.typing
          status := .formed functionTypeFormed }
  | _, context, regular, .app function argument => do
      let functionInfo ← infer regular function
      match regularPiView? regular functionInfo.status with
      | none => throw .expectedFunctionType
      | some view =>
          let functionTyping := RegularHasType.conv_type
            functionInfo.typing (.pi_form view.domFormed view.codFormed)
            view.conversion
          let argumentChecked ←
            check regular argument view.dom view.domFormed
          let resultFormed := view.codFormed.instantiate
            argumentChecked.typing regular.constantFreeCtx
          pure
            { type := inst0 argument.erase view.cod
              typing := .app_elim view.domFormed functionTyping
                argumentChecked.typing view.codFormed
              status := .formed resultFormed }
termination_by _ _ _ term => 2 * sizeOf term
decreasing_by
  all_goals simp_wf <;> omega

/-- Check an annotated term against an already-formed ordinary type.  A
lambda annotation is itself required to be a formed type and exactly
convertible to the expected domain. -/
def check : {binders : Nat} → {context : Ctx binders} →
    (regular : RegularCtx context) → (term : AnnotatedTm binders) →
    (expected : PureTm binders) →
    (expectedFormed : RegularHasType context expected .u1) →
    Except RegularCheckError (Checked (context := context) term expected)
  | _, context, regular, .lam annotation body, expected, expectedFormed =>
      match regularPiView? regular (.formed expectedFormed) with
      | none => throw .lambdaNeedsFunctionType
      | some view => do
          let annotationInfo ← infer regular annotation
          let annotationFormed ← annotationInfo.asFormedType regular
          if _accepted : decideRegularConversion regular
              (.formed annotationFormed.down)
              (.formed view.domFormed) = true then
            let extended : RegularCtx (.snoc context view.dom) :=
              .snoc regular view.domFormed
            let bodyChecked ←
              check extended body view.cod view.codFormed
            let lambdaTyping := RegularHasType.lam_intro
              view.domFormed view.codFormed bodyChecked.typing
            pure
              { typing := RegularHasType.conv_type lambdaTyping
                  expectedFormed view.conversion.symm }
          else
            throw .typeMismatch
  | _, _, regular, term, expected, expectedFormed => do
      let inferred ← infer regular term
      if accepted : decideRegularConversion regular inferred.status
          (.formed expectedFormed) = true then
        let conversion :=
          (decideRegularConversion_correct regular inferred.status
            (.formed expectedFormed)).1 accepted
        pure
          { typing := .conv_type inferred.typing expectedFormed conversion }
      else
        throw .typeMismatch
termination_by _ _ _ term _ _ => 2 * sizeOf term + 1
decreasing_by
  all_goals simp_wf <;> omega

end

/-- Check against the distinguished top sort. -/
def checkTop {context : Ctx binders} (regular : RegularCtx context)
    (term : AnnotatedTm binders) :
    Except RegularCheckError (Checked (context := context) term .u1) := do
  let inferred ← infer regular term
  if accepted : decideRegularConversion regular inferred.status (.top rfl) = true then
    let conversion :=
      (decideRegularConversion_correct regular inferred.status (.top rfl)).1
        accepted
    pure { typing := .conv_sort inferred.typing conversion }
  else
    throw .typeMismatch

/-- Public checking first establishes the expected type.  The top sort keeps
its distinguished two-universe boundary. -/
def checkType {context : Ctx binders} (regular : RegularCtx context)
    (term : AnnotatedTm binders) (expected : PureTm binders) :
    Except RegularCheckError (Checked (context := context) term expected) :=
  if top : expected = .u1 then
    top ▸ checkTop regular term
  else do
    let expectedInfo ← inferRegularType regular expected
    let expectedFormed ← expectedInfo.asFormedType? regular
    check regular term expected expectedFormed.down

/-- Certificate-free publication bit for the annotated fragment. -/
def checkBool {context : Ctx binders} (regular : RegularCtx context)
    (term : AnnotatedTm binders) (expected : PureTm binders) : Bool :=
  (checkType regular term expected).isOk

/-- Certificate-free synthesis publication bit. -/
def inferBool {context : Ctx binders} (regular : RegularCtx context)
    (term : AnnotatedTm binders) : Bool :=
  (infer regular term).isOk

/-- The synthesis correspondence theorem: every successful Prime synthesis
is a regular-kernel typing derivation after annotation erasure. -/
theorem inferred_corresponds {context : Ctx binders}
    (term : AnnotatedTm binders)
    (inferred : Inferred (context := context) term) :
    RegularHasType context term.erase inferred.type := by
  exact inferred.typing

/-- The checking correspondence theorem. -/
theorem checked_corresponds {context : Ctx binders}
    (term : AnnotatedTm binders)
    (expected : PureTm binders)
    (checked : Checked (context := context) term expected) :
    RegularHasType context term.erase expected := by
  exact checked.typing

/-- A published synthesis result always has a regular-kernel type. -/
theorem inferBool_sound {context : Ctx binders}
    (regular : RegularCtx context) (term : AnnotatedTm binders)
    (accepted : inferBool regular term = true) :
    ∃ type, RegularHasType context term.erase type := by
  unfold inferBool at accepted
  cases computed : infer regular term with
  | error failure =>
      rw [computed] at accepted
      change false = true at accepted
      cases accepted
  | ok inferred => exact ⟨inferred.type, inferred.typing⟩

/-- The public Boolean cannot publish an untyped judgment. -/
theorem checkBool_sound {context : Ctx binders}
    (regular : RegularCtx context) (term : AnnotatedTm binders)
    (expected : PureTm binders)
    (accepted : checkBool regular term expected = true) :
    RegularHasType context term.erase expected := by
  unfold checkBool at accepted
  cases computed : checkType regular term expected with
  | error failure =>
      rw [computed] at accepted
      change false = true at accepted
      cases accepted
  | ok checked => exact checked.typing

/-! ## Kernel-checked canaries -/

/-- Positive: the explicitly annotated identity synthesizes a dependent
function type. -/
def identity : AnnotatedTm 0 := .lam .u0 (.var 0)

example : RegularHasType (.nil : Ctx 0) identity.erase
    (.pi .u0 .u0) := by
  exact .lam_intro (.u0_type _) (.u0_type _) (.var 0)

/-- Negative: the upper sort has no type in the stable two-universe
fragment. -/
example : infer RegularCtx.nil (.u1 : AnnotatedTm 0) =
    .error .upperSortHasNoType := by
  rw [infer.eq_3]
  rfl

/-- Negative: a lambda annotation must denote a formed type. -/
example : (infer RegularCtx.nil
    (.lam (.u1 : AnnotatedTm 0) (.var 0))).isOk = false := by
  rw [infer.eq_5, infer.eq_3]
  rfl

#print axioms inferBool_sound
#print axioms checkBool_sound

end Mettapedia.Languages.MeTTa.Prime.OpenLambdaPiCorrespondence
