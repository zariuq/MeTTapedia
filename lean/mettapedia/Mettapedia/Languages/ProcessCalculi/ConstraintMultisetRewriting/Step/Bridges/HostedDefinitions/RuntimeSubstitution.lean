import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleBuilder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ControlProtocol

/-!
# Finite source rules for raw shifting and substitution

The program consists of ordinary binder equations over literal data. It uses
unary naturals, explicit environments and private continuation frames. No
right-hand side invokes a native syntax algorithm or a host evaluator.

An entry wraps the external continuation in a bottom frame. Internal returns
inspect only helper frames. Removing that bottom frame produces the public
resume port, at which the helper has no rule. Additional source clauses must
respect the internal phases to preserve determinism and progress.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration
open RuleBuilder

abbrev Equation := ProgramBinders.Equation MSig [] ()

def encodeRawEnv : List (NativeSyntax.Raw Tower.Head) → MClosed
  | [] => nodeC "prime-list-nil" []
  | value :: rest => nodeC "prime-list-cons" [quoteRaw value, encodeRawEnv rest]

def shiftOp (amount cutoff : Nat) : MClosed :=
  nodeC "hd-helper-shift-op" [encodeNat amount, encodeNat cutoff]
def zeroOp (argument : NativeSyntax.Raw Tower.Head) (depth : Nat) : MClosed :=
  nodeC "hd-helper-zero-op" [quoteRaw argument, encodeNat depth]
def environmentOp (environment : List (NativeSyntax.Raw Tower.Head)) : MClosed :=
  nodeC "hd-helper-env-op" [encodeRawEnv environment]

def bottom (continuation : MClosed) : MClosed := nodeC "hd-helper-bottom" [continuation]
def returnC (value continuation : MClosed) : MClosed := activeC "hd-helper-return" [value, continuation]
def mapC (operation term continuation : MClosed) : MClosed :=
  activeC "hd-helper-map" [operation, term, continuation]
def boundFlag (binds : Bool) : MClosed :=
  nodeC (if binds then "hd-helper-bound" else "hd-helper-free") []
def visitC (binds : Bool) (operation term continuation : MClosed) : MClosed :=
  activeC "hd-helper-visit" [boundFlag binds, operation, term, continuation]
def liftC (operation continuation : MClosed) : MClosed := activeC "hd-helper-lift" [operation, continuation]
def lookupC (environment : List (NativeSyntax.Raw Tower.Head)) (index : Nat) (continuation : MClosed) : MClosed :=
  activeC "hd-helper-lookup" [encodeRawEnv environment, encodeNat index, continuation]
def liftEnvironmentC (environment : List (NativeSyntax.Raw Tower.Head)) (continuation : MClosed) : MClosed :=
  activeC "hd-helper-lift-environment" [encodeRawEnv environment, continuation]

def shiftIndexC (amount cutoff index original : Nat) (continuation : MClosed) : MClosed :=
  activeC "hd-helper-shift-index" [encodeNat amount, encodeNat cutoff, encodeNat index,
    encodeNat original, continuation]
def addIndexC (amount index : Nat) (continuation : MClosed) : MClosed :=
  activeC "hd-helper-add-index" [encodeNat amount, encodeNat index, continuation]
def zeroIndexC (argument : NativeSyntax.Raw Tower.Head) (depth index originalDepth originalIndex : Nat)
    (continuation : MClosed) : MClosed :=
  activeC "hd-helper-zero-index" [quoteRaw argument, encodeNat depth, encodeNat index,
    encodeNat originalDepth, encodeNat originalIndex, continuation]
def oneFrame (tag : String) (continuation : MClosed) : MClosed :=
  nodeC "hd-helper-one" [csym tag, continuation]
def twoFirstFrame (tag : String) (operation : MClosed) (binds : Bool) (second continuation : MClosed) : MClosed :=
  nodeC "hd-helper-two-first" [csym tag, operation, boundFlag binds, second, continuation]
def twoLastFrame (tag : String) (first continuation : MClosed) : MClosed :=
  nodeC "hd-helper-two-last" [csym tag, first, continuation]
def threeFirstFrame (tag : String) (operation : MClosed) (secondBinds : Bool) (second : MClosed)
    (thirdBinds : Bool) (third continuation : MClosed) : MClosed :=
  nodeC "hd-helper-three-first" [csym tag, operation, boundFlag secondBinds, second,
    boundFlag thirdBinds, third, continuation]
def threeSecondFrame (tag : String) (first operation : MClosed) (binds : Bool) (third continuation : MClosed) : MClosed :=
  nodeC "hd-helper-three-second" [csym tag, first, operation, boundFlag binds, third, continuation]
def threeLastFrame (tag : String) (first second continuation : MClosed) : MClosed :=
  nodeC "hd-helper-three-last" [csym tag, first, second, continuation]

theorem encodeRawEnv_environmentC (environment : List (NativeSyntax.Raw Tower.Head)) :
    encodeRawEnv environment = environmentC environment := by
  induction environment with
  | nil => rfl
  | cons value rest ih => exact congrArg (fun tail => nodeC "prime-list-cons" [quoteRaw value, tail]) ih

namespace Templates

def act {n : Nat} (phase : String) (fields : List (Template n)) : Template n :=
  node activeTag [node phase fields]
def ret {n : Nat} (value continuation : Template n) : Template n := act "hd-helper-return" [value, continuation]
def mapTerm {n : Nat} (operation term continuation : Template n) : Template n :=
  act "hd-helper-map" [operation, term, continuation]
def visit {n : Nat} (flag operation term continuation : Template n) : Template n :=
  act "hd-helper-visit" [flag, operation, term, continuation]
def ns {n : Nat} (predecessor : Template n) : Template n := node "prime-nat-succ" [predecessor]
def nz {n : Nat} : Template n := node "prime-nat-zero" []
def rawVar {n : Nat} (index : Template n) : Template n := node "prime-tm-var" [index]
def nilEnv {n : Nat} : Template n := node "prime-list-nil" []
def consEnv {n : Nat} (first rest : Template n) : Template n := node "prime-list-cons" [first, rest]
def tupleHead {n : Nat} (head : Template n) (fields : List (Template n)) : Template n :=
  SourceLanguage.Toolkit.tupleAt (head :: fields)

def rule1 (body : Template 1 → Template 1 × Template 1) : Equation :=
  let pair := body (slot ⟨0, by decide⟩)
  equation pair.1 pair.2
def rule2 (body : Template 2 → Template 2 → Template 2 × Template 2) : Equation :=
  let pair := body (slot ⟨0, by decide⟩) (slot ⟨1, by decide⟩)
  equation pair.1 pair.2
def rule3 (body : Template 3 → Template 3 → Template 3 → Template 3 × Template 3) : Equation :=
  let pair := body (slot ⟨0, by decide⟩) (slot ⟨1, by decide⟩) (slot ⟨2, by decide⟩)
  equation pair.1 pair.2
def rule4 (body : Template 4 → Template 4 → Template 4 → Template 4 → Template 4 × Template 4) : Equation :=
  let pair := body (slot ⟨0, by decide⟩) (slot ⟨1, by decide⟩) (slot ⟨2, by decide⟩) (slot ⟨3, by decide⟩)
  equation pair.1 pair.2
def rule5 (body : Template 5 → Template 5 → Template 5 → Template 5 → Template 5 →
    Template 5 × Template 5) : Equation :=
  let pair := body (slot ⟨0, by decide⟩) (slot ⟨1, by decide⟩) (slot ⟨2, by decide⟩) (slot ⟨3, by decide⟩)
    (slot ⟨4, by decide⟩)
  equation pair.1 pair.2
def rule6 (body : Template 6 → Template 6 → Template 6 → Template 6 → Template 6 → Template 6 →
    Template 6 × Template 6) : Equation :=
  let pair := body (slot ⟨0, by decide⟩) (slot ⟨1, by decide⟩) (slot ⟨2, by decide⟩) (slot ⟨3, by decide⟩)
    (slot ⟨4, by decide⟩) (slot ⟨5, by decide⟩)
  equation pair.1 pair.2
def rule7 (body : Template 7 → Template 7 → Template 7 → Template 7 → Template 7 → Template 7 →
    Template 7 → Template 7 × Template 7) : Equation :=
  let pair := body (slot ⟨0, by decide⟩) (slot ⟨1, by decide⟩) (slot ⟨2, by decide⟩) (slot ⟨3, by decide⟩)
    (slot ⟨4, by decide⟩) (slot ⟨5, by decide⟩) (slot ⟨6, by decide⟩)
  equation pair.1 pair.2
def rule8 (body : Template 8 → Template 8 → Template 8 → Template 8 → Template 8 → Template 8 →
    Template 8 → Template 8 → Template 8 × Template 8) : Equation :=
  let pair := body (slot ⟨0, by decide⟩) (slot ⟨1, by decide⟩) (slot ⟨2, by decide⟩) (slot ⟨3, by decide⟩)
    (slot ⟨4, by decide⟩) (slot ⟨5, by decide⟩) (slot ⟨6, by decide⟩) (slot ⟨7, by decide⟩)
  equation pair.1 pair.2

end Templates

open Templates

def enterShift : Equation := rule4 fun amount cutoff term continuation =>
  (act "hd-shift" [amount, cutoff, term, continuation],
    mapTerm (node "hd-helper-shift-op" [amount, cutoff]) term (node "hd-helper-bottom" [continuation]))
def enterZero : Equation := rule4 fun argument depth body continuation =>
  (act "hd-subst-zero" [argument, depth, body, continuation],
    mapTerm (node "hd-helper-zero-op" [argument, depth]) body (node "hd-helper-bottom" [continuation]))
def enterEnvironment : Equation := rule3 fun environment body continuation =>
  (act "hd-subst-env" [environment, body, continuation],
    mapTerm (node "hd-helper-env-op" [environment]) body (node "hd-helper-bottom" [continuation]))
def leave : Equation := rule2 fun value continuation =>
  (ret value (node "hd-helper-bottom" [continuation]), act "hd-resume" [value, continuation])

def mapConstant : Equation := rule3 fun operation name continuation =>
  (mapTerm operation (node "prime-tm-const" [name]) continuation,
    ret (node "prime-tm-const" [name]) continuation)
def mapHead : Equation := rule3 fun operation head continuation =>
  (mapTerm operation (node "prime-tm-head" [head]) continuation,
    ret (node "prime-tm-head" [head]) continuation)
def mapVariable : Equation := rule3 fun operation index continuation =>
  (mapTerm operation (rawVar index) continuation, act "hd-helper-variable" [operation, index, continuation])

def mapUnary (tag : String) (binds : Bool) : Equation := rule3 fun operation child continuation =>
  (mapTerm operation (node tag [child]) continuation,
    visit (literal (boundFlag binds)) operation child
      (node "hd-helper-one" [literal (csym tag), continuation]))
def mapBinary (tag : String) (firstBinds secondBinds : Bool) : Equation :=
  rule4 fun operation first second continuation =>
    (mapTerm operation (node tag [first, second]) continuation,
      visit (literal (boundFlag firstBinds)) operation first
        (node "hd-helper-two-first" [literal (csym tag), operation,
          literal (boundFlag secondBinds), second, continuation]))
def mapTernary (tag : String) (firstBinds secondBinds thirdBinds : Bool) : Equation :=
  rule5 fun operation first second third continuation =>
    (mapTerm operation (node tag [first, second, third]) continuation,
      visit (literal (boundFlag firstBinds)) operation first
        (node "hd-helper-three-first" [literal (csym tag), operation,
          literal (boundFlag secondBinds), second, literal (boundFlag thirdBinds), third, continuation]))

def visitFree : Equation := rule3 fun operation term continuation =>
  (visit (literal (boundFlag false)) operation term continuation, mapTerm operation term continuation)
def visitBound : Equation := rule3 fun operation term continuation =>
  (visit (literal (boundFlag true)) operation term continuation,
    act "hd-helper-lift" [operation, node "hd-helper-after-lift" [term, continuation]])
def afterLift : Equation := rule3 fun operation term continuation =>
  (ret operation (node "hd-helper-after-lift" [term, continuation]), mapTerm operation term continuation)

def returnOne : Equation := rule3 fun value tag continuation =>
  (ret value (node "hd-helper-one" [tag, continuation]), ret (tupleHead tag [value]) continuation)
def returnTwoFirst : Equation := rule6 fun value tag operation flag second continuation =>
  (ret value (node "hd-helper-two-first" [tag, operation, flag, second, continuation]),
    visit flag operation second (node "hd-helper-two-last" [tag, value, continuation]))
def returnTwoLast : Equation := rule4 fun value tag first continuation =>
  (ret value (node "hd-helper-two-last" [tag, first, continuation]), ret (tupleHead tag [first, value]) continuation)
def returnThreeFirst : Equation := rule8 fun value tag operation secondFlag second thirdFlag third continuation =>
  (ret value (node "hd-helper-three-first" [tag, operation, secondFlag, second, thirdFlag, third, continuation]),
    visit secondFlag operation second
      (node "hd-helper-three-second" [tag, value, operation, thirdFlag, third, continuation]))
def returnThreeSecond : Equation := rule7 fun value tag first operation thirdFlag third continuation =>
  (ret value (node "hd-helper-three-second" [tag, first, operation, thirdFlag, third, continuation]),
    visit thirdFlag operation third (node "hd-helper-three-last" [tag, first, value, continuation]))
def returnThreeLast : Equation := rule5 fun value tag first second continuation =>
  (ret value (node "hd-helper-three-last" [tag, first, second, continuation]),
    ret (tupleHead tag [first, second, value]) continuation)

def liftShift : Equation := rule3 fun amount cutoff continuation =>
  (act "hd-helper-lift" [node "hd-helper-shift-op" [amount, cutoff], continuation],
    ret (node "hd-helper-shift-op" [amount, ns cutoff]) continuation)
def liftZero : Equation := rule3 fun argument depth continuation =>
  (act "hd-helper-lift" [node "hd-helper-zero-op" [argument, depth], continuation],
    ret (node "hd-helper-zero-op" [argument, ns depth]) continuation)
def liftEnvironment : Equation := rule2 fun environment continuation =>
  (act "hd-helper-lift" [node "hd-helper-env-op" [environment], continuation],
    act "hd-helper-lift-environment" [environment, node "hd-helper-env-op-frame" [continuation]])
def environmentOperation : Equation := rule2 fun environment continuation =>
  (ret environment (node "hd-helper-env-op-frame" [continuation]),
    ret (node "hd-helper-env-op" [consEnv (rawVar nz) environment]) continuation)

def shiftVariable : Equation := rule4 fun amount cutoff index continuation =>
  (act "hd-helper-variable" [node "hd-helper-shift-op" [amount, cutoff], index, continuation],
    act "hd-helper-shift-index" [amount, cutoff, index, index, continuation])
def shiftIndexAtCutoff : Equation := rule4 fun amount remaining original continuation =>
  (act "hd-helper-shift-index" [amount, nz, remaining, original, continuation],
    act "hd-helper-add-index" [amount, original, continuation])
def shiftIndexBelow : Equation := rule4 fun amount cutoff original continuation =>
  (act "hd-helper-shift-index" [amount, ns cutoff, nz, original, continuation], ret (rawVar original) continuation)
def shiftIndexNext : Equation := rule5 fun amount cutoff index original continuation =>
  (act "hd-helper-shift-index" [amount, ns cutoff, ns index, original, continuation],
    act "hd-helper-shift-index" [amount, cutoff, index, original, continuation])
def addIndexZero : Equation := rule2 fun index continuation =>
  (act "hd-helper-add-index" [nz, index, continuation], ret (rawVar index) continuation)
def addIndexNext : Equation := rule3 fun amount index continuation =>
  (act "hd-helper-add-index" [ns amount, index, continuation],
    act "hd-helper-add-index" [amount, ns index, continuation])

def zeroVariable : Equation := rule4 fun argument depth index continuation =>
  (act "hd-helper-variable" [node "hd-helper-zero-op" [argument, depth], index, continuation],
    act "hd-helper-zero-index" [argument, depth, index, depth, index, continuation])
def zeroIndexEqual : Equation := rule4 fun argument depth original continuation =>
  (act "hd-helper-zero-index" [argument, nz, nz, depth, original, continuation],
    mapTerm (node "hd-helper-shift-op" [depth, nz]) argument continuation)
def zeroIndexAbove : Equation := rule5 fun argument index depth predecessor continuation =>
  (act "hd-helper-zero-index" [argument, nz, ns index, depth, ns predecessor, continuation],
    ret (rawVar predecessor) continuation)
def zeroIndexBelow : Equation := rule5 fun argument remaining depth original continuation =>
  (act "hd-helper-zero-index" [argument, ns remaining, nz, depth, original, continuation],
    ret (rawVar original) continuation)
def zeroIndexNext : Equation := rule6 fun argument remaining index depth original continuation =>
  (act "hd-helper-zero-index" [argument, ns remaining, ns index, depth, original, continuation],
    act "hd-helper-zero-index" [argument, remaining, index, depth, original, continuation])

def environmentVariable : Equation := rule3 fun environment index continuation =>
  (act "hd-helper-variable" [node "hd-helper-env-op" [environment], index, continuation],
    act "hd-helper-lookup" [environment, index, continuation])
def lookupEmpty : Equation := rule2 fun index continuation =>
  (act "hd-helper-lookup" [nilEnv, index, continuation],
    ret (literal (quoteRaw (.const .anonymous))) continuation)
def lookupZero : Equation := rule3 fun first rest continuation =>
  (act "hd-helper-lookup" [consEnv first rest, nz, continuation], ret first continuation)
def lookupNext : Equation := rule4 fun first rest index continuation =>
  (act "hd-helper-lookup" [consEnv first rest, ns index, continuation],
    act "hd-helper-lookup" [rest, index, continuation])

def liftEnvironmentEmpty : Equation := rule1 fun continuation =>
  (act "hd-helper-lift-environment" [nilEnv, continuation], ret nilEnv continuation)
def liftEnvironmentNext : Equation := rule3 fun first rest continuation =>
  (act "hd-helper-lift-environment" [consEnv first rest, continuation],
    mapTerm (node "hd-helper-shift-op" [ns nz, nz]) first
      (node "hd-helper-env-head" [rest, continuation]))
def liftEnvironmentHead : Equation := rule3 fun value rest continuation =>
  (ret value (node "hd-helper-env-head" [rest, continuation]),
    act "hd-helper-lift-environment" [rest, node "hd-helper-env-tail" [value, continuation]])
def liftEnvironmentTail : Equation := rule3 fun rest value continuation =>
  (ret rest (node "hd-helper-env-tail" [value, continuation]), ret (consEnv value rest) continuation)

def rules : List Equation :=
  [enterShift, enterZero, enterEnvironment, leave,
   mapConstant, mapHead, mapVariable,
   mapUnary "prime-tm-lam" true, mapUnary "prime-tm-fst" false,
   mapUnary "prime-tm-snd" false, mapUnary "prime-tm-refl" false,
   mapBinary "prime-tm-pi" false true, mapBinary "prime-tm-sigma" false true,
   mapBinary "prime-tm-lam-typed" false true,
   mapBinary "prime-tm-app" false false, mapBinary "prime-tm-pair" false false,
   mapTernary "prime-tm-id" false false false,
   visitFree, visitBound, afterLift,
   returnOne, returnTwoFirst, returnTwoLast, returnThreeFirst, returnThreeSecond, returnThreeLast,
   liftShift, liftZero, liftEnvironment, environmentOperation,
   shiftVariable, shiftIndexAtCutoff, shiftIndexBelow, shiftIndexNext, addIndexZero, addIndexNext,
   zeroVariable, zeroIndexEqual, zeroIndexAbove, zeroIndexBelow, zeroIndexNext,
   environmentVariable, lookupEmpty, lookupZero, lookupNext,
   liftEnvironmentEmpty, liftEnvironmentNext, liftEnvironmentHead, liftEnvironmentTail]

theorem rules_length : rules.length = 49 := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
