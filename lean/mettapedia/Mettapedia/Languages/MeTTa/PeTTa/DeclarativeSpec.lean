import Mettapedia.Languages.MeTTa.PeTTa.Effects
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.PeTTa.StdLib
import Mettapedia.Languages.MeTTa.PeTTa.TranslateExpr
import Mettapedia.Languages.MeTTa.ExecutionContract

/-!
# PeTTa Declarative Core Spec (Grammar-Style)

This module provides a **clear declarative spec layer** for PeTTa in a style
close to grammar-like operational rules:

- a pure judgment (`PureDecl`) for core expression semantics;
- a stateful core judgment (`CoreDecl`) for command semantics including
  `progn` and `prog1`.

The key point is that this is not a separate implementation:
we prove exact correspondence with existing formal kernels:

- `PureDecl ↔ PeTTaEval`
- `CoreDecl ↔ PeTTaCmd`

So this file is simultaneously:
1. a readable declarative specification artifact, and
2. a machine-checked bridge to the established formalization.

## 3-Layer PeTTa Spec Pack (Audit View)

1. **Pure declarative core**:
   `PureDecl` with bridge theorem `pureDecl_iff_pettaEval`.
2. **Stateful declarative core**:
   `CoreDecl` with bridge theorem `coreDecl_iff_pettaCmd`.
3. **Operational instruction layer**:
   `MeTTaStep` (in `MinimalInstructions.lean`) with bridge
   `evalStep_implies_pettaEval`.

Bridge theorem index in this module:
- `pureDecl_iff_pettaEval`
- `coreDecl_iff_pettaCmd`
- `PredicateControlDeclClause.translatePredicate_query_to_pettaEval_match`
- `PredicateControlDeclClause.catch_fallback_to_pettaEval`

- There is the intention fro this file to be similar to HE MeTTa specs: https://trueagi-io.github.io/hyperon-experimental/metta/

-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.ExecutionContract

/-! ## Numeric Result Shape

PeTTa inherits the observable integer-vs-float result distinction from the
actual Prolog implementation in `hyperon/PeTTa/src/metta.pl` together with
SWI-Prolog arithmetic behavior.

This belongs in the declarative spec surface because programs can observe it.

Positive examples:
- `(+ 2 3)` returns `5`, not `5.0`
- `(sqrt-math 9)` returns `3.0`, not `3`
- `(round-math 5.4)` returns `5`, not `5.0`

Negative example:
- numeric result shape is not just presentation sugar; it is observable
  evaluation behavior and therefore part of the language specification.
-/

/-- Operator-class component of PeTTa numeric result-shape semantics.

This captures the fixed operator-family part. Concrete evaluation still depends
on the dynamic numeric class of the arguments where noted. -/
def numericResultShapeOf : String → Option NumericResultShape
  | "+" => some .preserveIntegralIfExact
  | "-" => some .preserveIntegralIfExact
  | "*" => some .preserveIntegralIfExact
  | "/" => some .preserveIntegralIfExact
  | "pow-math" => some .preserveIntegralIfExact
  | "%" => some .alwaysInteger
  | "round-math" => some .alwaysInteger
  | "trunc-math" => some .alwaysInteger
  | "ceil-math" => some .alwaysInteger
  | "floor-math" => some .alwaysInteger
  | "sqrt-math" => some .alwaysFloat
  | "log-math" => some .alwaysFloat
  | "sin-math" => some .alwaysFloat
  | "asin-math" => some .alwaysFloat
  | "cos-math" => some .alwaysFloat
  | "acos-math" => some .alwaysFloat
  | "tan-math" => some .alwaysFloat
  | "atan-math" => some .alwaysFloat
  | "abs-math" => some .preserveInputNumericClass
  | _ => none

theorem numericResultShapeOf_add :
    numericResultShapeOf "+" = some .preserveIntegralIfExact := rfl

theorem numericResultShapeOf_round :
    numericResultShapeOf "round-math" = some .alwaysInteger := rfl

theorem numericResultShapeOf_sqrt :
    numericResultShapeOf "sqrt-math" = some .alwaysFloat := rfl

theorem numericResultShapeOf_abs :
    numericResultShapeOf "abs-math" = some .preserveInputNumericClass := rfl

/-! ## Pure Declarative Core -/

/-- Declarative pure core judgment (grammar-style).

`PureDecl s p answers` means: in space `s`, expression `p` produces
nondeterministic answers `answers`.
-/
inductive PureDecl (s : PeTTaSpace) : Pattern → Answers → Prop where
  | var (x : String) :
      PureDecl s (.fvar x) [.fvar x]
  | bvar (n : Nat) :
      PureDecl s (.bvar n) [.bvar n]
  | ground (c : String) :
      PureDecl s (.apply c []) [.apply c []]
  | ruleApp (r : RewriteRule) (bs : Bindings) (p q : Pattern)
      (hr : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm : bs ∈ matchPattern r.left p)
      (hq : applyBindings bs r.right = q) :
      PureDecl s p [q]
  | spaceQuery (pat tmpl : Pattern) (results : Answers)
      (hres : results = s.spaceMatch pat tmpl) :
      PureDecl s (.apply "match" [.apply "&self" [], pat, tmpl]) results
  | superpose (alts : List Pattern) :
      PureDecl s (.apply "superpose" [.collection .vec alts none]) alts
  | collapse (p : Pattern) (answers : Answers)
      (h : PureDecl s p answers) :
      PureDecl s (.apply "collapse" [p]) [.collection .vec answers none]

theorem PureDecl.toPeTTaEval {s : PeTTaSpace} {p : Pattern} {answers : Answers}
    (h : PureDecl s p answers) :
    PeTTaEval s p answers := by
  cases h with
  | var x => exact PeTTaEval.var x
  | bvar n => exact PeTTaEval.bvar n
  | ground c => exact PeTTaEval.ground c
  | ruleApp r bs p q hr hprem hm hq =>
      exact PeTTaEval.ruleApp r bs p q hr hprem hm hq
  | spaceQuery pat tmpl _ hres =>
      exact PeTTaEval.spaceQuery pat tmpl _ hres
  | superpose _ =>
      exact PeTTaEval.superpose _
  | collapse p answers h =>
      exact PeTTaEval.collapse p answers (PureDecl.toPeTTaEval h)

theorem PureDecl.ofPeTTaEval {s : PeTTaSpace} {p : Pattern} {answers : Answers}
    (h : PeTTaEval s p answers) :
    PureDecl s p answers := by
  cases h with
  | var x => exact PureDecl.var x
  | bvar n => exact PureDecl.bvar n
  | ground c => exact PureDecl.ground c
  | ruleApp r bs p q hr hprem hm hq =>
      exact PureDecl.ruleApp r bs p q hr hprem hm hq
  | spaceQuery pat tmpl _ hres =>
      exact PureDecl.spaceQuery pat tmpl _ hres
  | superpose _ =>
      exact PureDecl.superpose _
  | collapse p answers h =>
      exact PureDecl.collapse p answers (PureDecl.ofPeTTaEval h)

theorem pureDecl_iff_pettaEval (s : PeTTaSpace) (p : Pattern) (answers : Answers) :
    PureDecl s p answers ↔ PeTTaEval s p answers :=
  ⟨PureDecl.toPeTTaEval, PureDecl.ofPeTTaEval⟩

/-! ## Full Declarative Core Clauses (`MeTTaEval`) -/

namespace FullDeclClause

/-- Clause form: symbol pass-through (`metta(Symbol, ty, space, bs)`). -/
def symbolPassThrough (s : PeTTaSpace) (c : String) (ty : Pattern) (bs : Bindings) : Prop :=
  MeTTaEval s (.apply c []) ty bs [(.apply c [], bs)]

/-- Clause form: variable pass-through. -/
def varPassThrough (s : PeTTaSpace) (x : String) (ty : Pattern) (bs : Bindings) : Prop :=
  MeTTaEval s (.fvar x) ty bs [(.fvar x, bs)]

/-- Clause form: error pass-through. -/
def errorPassThrough (s : PeTTaSpace) (atom msg ty : Pattern) (bs : Bindings) : Prop :=
  MeTTaEval s (mkError atom msg) ty bs [(mkError atom msg, bs)]

/-- Clause form: rule application with binding threading. -/
def ruleApp (s : PeTTaSpace) (r : RewriteRule) (bsm : Bindings)
    (p q ty : Pattern) (input : Bindings) : Prop :=
  r ∈ s.rules ∧
  r.premises = [] ∧
  bsm ∈ matchPattern r.left p ∧
  applyBindings bsm r.right = q ∧
  MeTTaEval s p ty input [(q, bsm ++ input)]

/-- Clause form: `(match &self pat tmpl)`. -/
def spaceQuery (s : PeTTaSpace) (pat tmpl ty : Pattern) (bs : Bindings) (res : EvalResult) : Prop :=
  res = (s.spaceMatch pat tmpl).map (·, bs) ∧
  MeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) ty bs res

/-- Clause form: `superpose`. -/
def superpose (s : PeTTaSpace) (alts : List Pattern) (ty : Pattern) (bs : Bindings) : Prop :=
  MeTTaEval s (.apply "superpose" [.collection .vec alts none]) ty bs (alts.map (·, bs))

/-- Clause form: `collapse`. -/
def collapse (s : PeTTaSpace) (p ty : Pattern) (bs : Bindings) (inner : EvalResult) : Prop :=
  MeTTaEval s p ty bs inner ∧
  MeTTaEval s (.apply "collapse" [p]) ty bs [(.collection .vec (inner.map Prod.fst) none, bs)]

theorem symbolPassThrough_intro (s : PeTTaSpace) (c : String) (ty : Pattern) (bs : Bindings)
    (hty : isPassThroughType ty) :
    symbolPassThrough s c ty bs := by
  exact MeTTaEval.symbolPassThrough c ty bs hty

theorem varPassThrough_intro (s : PeTTaSpace) (x : String) (ty : Pattern) (bs : Bindings) :
    varPassThrough s x ty bs := by
  exact MeTTaEval.varPassThrough x ty bs

theorem errorPassThrough_intro (s : PeTTaSpace) (atom msg ty : Pattern) (bs : Bindings) :
    errorPassThrough s atom msg ty bs := by
  exact MeTTaEval.errorPassThrough atom msg ty bs

theorem ruleApp_intro (s : PeTTaSpace) (r : RewriteRule) (bsm : Bindings)
    (p q ty : Pattern) (input : Bindings)
    (hr : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm : bsm ∈ matchPattern r.left p)
    (hq : applyBindings bsm r.right = q) :
    ruleApp s r bsm p q ty input := by
  refine ⟨hr, hprem, hm, hq, ?_⟩
  exact MeTTaEval.ruleApp r bsm p q ty input hr hprem hm hq

theorem spaceQuery_intro (s : PeTTaSpace) (pat tmpl ty : Pattern) (bs : Bindings) (res : EvalResult)
    (hres : res = (s.spaceMatch pat tmpl).map (·, bs)) :
    spaceQuery s pat tmpl ty bs res := by
  refine ⟨hres, ?_⟩
  exact MeTTaEval.spaceQuery pat tmpl ty bs res hres

theorem superpose_intro (s : PeTTaSpace) (alts : List Pattern) (ty : Pattern) (bs : Bindings) :
    superpose s alts ty bs := by
  exact MeTTaEval.superpose alts ty bs

theorem collapse_intro (s : PeTTaSpace) (p ty : Pattern) (bs : Bindings) (inner : EvalResult)
    (h : MeTTaEval s p ty bs inner) :
    collapse s p ty bs inner := by
  refine ⟨h, ?_⟩
  exact MeTTaEval.collapse p ty bs inner h

/-- Declarative clause packaging for `collapse (match &self pat tmpl)`.

This is the clean composition theorem for the first nested certified query
family: the inner `match &self` query is certified already, and `collapse`
packages exactly its threaded answers into a singleton collection. -/
theorem collapse_spaceQuery_intro
    (s : PeTTaSpace) (pat tmpl ty : Pattern) (bs : Bindings) :
    collapse s
      (.apply "match" [.apply "&self" [], pat, tmpl])
      ty
      bs
      ((s.spaceMatch pat tmpl).map (·, bs)) := by
  exact collapse_intro _ _ _ _
    ((s.spaceMatch pat tmpl).map (·, bs))
    (MeTTaEval.spaceQuery pat tmpl ty bs _ rfl)

end FullDeclClause

/-! ## Declarative Control Clauses (`if`/`let`/`case`) -/

namespace ControlDeclClause

/-- Clause form: `(if True then else)` selects `then` when `ifTrueRule` is present. -/
def ifTrueBranch (s : PeTTaSpace) (thenB elseB : Pattern) : Prop :=
  ifTrueRule ∈ s.rules ∧
  PeTTaEval s (.apply "if" [.apply "True" [], thenB, elseB]) [thenB]

/-- Clause form: `(if False then else)` selects `else` when `ifFalseRule` is present. -/
def ifFalseBranch (s : PeTTaSpace) (thenB elseB : Pattern) : Prop :=
  ifFalseRule ∈ s.rules ∧
  PeTTaEval s (.apply "if" [.apply "False" [], thenB, elseB]) [elseB]

/-- Clause form: `(let var val body)` rewrites to `(chain val var body)` when `letRule` is present. -/
def letToChain (s : PeTTaSpace) (varP valP bodyP : Pattern) : Prop :=
  letRule ∈ s.rules ∧
  PeTTaEval s (.apply "let" [varP, valP, bodyP]) [.apply "chain" [valP, varP, bodyP]]

/-- Clause form: case-success one-step reduction through `unify`. -/
def caseSuccessStep (s : PeTTaSpace) (cond pat branch : Pattern) (bs : Bindings) : Prop :=
  bs ∈ matchPattern pat cond ∧
  MeTTaStep s
    (.apply "unify" [cond, pat, branch, .apply "empty" []])
    (applyBindings bs branch)

/-- Clause form: case-failure one-step reduction through `unify`. -/
def caseFailureStep (s : PeTTaSpace) (cond pat thenB elseB : Pattern) : Prop :=
  matchPattern pat cond = [] ∧
  MeTTaStep s (.apply "unify" [cond, pat, thenB, elseB]) elseB

theorem ifTrueBranch_intro (s : PeTTaSpace) (thenB elseB : Pattern)
    (hT : ifTrueRule ∈ s.rules) :
    ifTrueBranch s thenB elseB := by
  exact ⟨hT, if_true_reduces s thenB elseB hT⟩

theorem ifFalseBranch_intro (s : PeTTaSpace) (thenB elseB : Pattern)
    (hF : ifFalseRule ∈ s.rules) :
    ifFalseBranch s thenB elseB := by
  exact ⟨hF, if_false_reduces s thenB elseB hF⟩

theorem letToChain_intro (s : PeTTaSpace) (varP valP bodyP : Pattern)
    (hL : letRule ∈ s.rules) :
    letToChain s varP valP bodyP := by
  exact ⟨hL, let_to_chain s varP valP bodyP hL⟩

theorem caseSuccessStep_intro (s : PeTTaSpace) (cond pat branch : Pattern) (bs : Bindings)
    (hm : bs ∈ matchPattern pat cond) :
    caseSuccessStep s cond pat branch bs := by
  exact ⟨hm, case_single_branch_reduces s cond pat branch bs hm⟩

theorem caseFailureStep_intro (s : PeTTaSpace) (cond pat thenB elseB : Pattern)
    (hno : matchPattern pat cond = []) :
    caseFailureStep s cond pat thenB elseB := by
  exact ⟨hno, case_single_branch_failure s cond pat thenB elseB hno⟩

end ControlDeclClause

/-! ## Declarative Let* Clauses -/

namespace LetStarDeclClause

/-- Clause form: `(let* () body)` base case reduces to `body`. -/
def base (s : PeTTaSpace) (bodyP : Pattern) : Prop :=
  letStarBaseRule ∈ s.rules ∧
  PeTTaEval s (.apply "let*" [.collection .vec [] none, bodyP]) [bodyP]

/-- Clause form: recursive `let*` step reducing to nested `let`. -/
def recStep (s : PeTTaSpace) (varP valP bodyP restP : Pattern) : Prop :=
  letStarRecRule ∈ s.rules ∧
  [("var", varP), ("val", valP), ("rest", restP), ("body", bodyP)] ∈
    matchPattern letStarRecRule.left
      (.apply "let*"
        [ .collection .vec [.apply "pair" [varP, valP]] none
        , bodyP ]) ∧
  PeTTaEval s
    (.apply "let*" [.collection .vec [.apply "pair" [varP, valP]] none, bodyP])
    [.apply "let" [varP, valP, .apply "let*" [restP, bodyP]]]

theorem base_intro (s : PeTTaSpace) (bodyP : Pattern)
    (hr : letStarBaseRule ∈ s.rules) :
    base s bodyP := by
  exact ⟨hr, let_star_base_reduces s bodyP hr⟩

theorem recStep_intro (s : PeTTaSpace) (varP valP bodyP restP : Pattern)
    (hr : letStarRecRule ∈ s.rules)
    (hm : [("var", varP), ("val", valP), ("rest", restP), ("body", bodyP)] ∈
           matchPattern letStarRecRule.left
             (.apply "let*"
               [ .collection .vec [.apply "pair" [varP, valP]] none
               , bodyP ])) :
    recStep s varP valP bodyP restP := by
  exact ⟨hr, hm, let_star_rec_reduces s varP valP bodyP restP hr hm⟩

end LetStarDeclClause

/-! ## Predicate-Control Declarative Clauses (`translatePredicate`/`catch`/`progn`) -/

namespace PredicateControlDeclClause

/-- Whether a string begins with `&` (kernel-reducible, unlike `String.startsWith`). -/
private def startsWithAmp (s : String) : Bool :=
  match s.data with
  | '&' :: _ => true
  | _ => false

/-- Decode a predicate-like query into a match pattern over `&self`. -/
def decodePredicateQuery? : Pattern → Option Pattern
  | .apply "Predicate" [inner] =>
      decodePredicateQuery? inner
  | .apply "&self" (relHead :: args) =>
      match relHead with
      | .apply rel [] => some (.apply rel args)
      | _ => none
  | .apply rel args =>
      if startsWithAmp rel then none else some (.apply rel args)
  | _ => none

/-- Executable answer policy for predicate queries:
nonempty match bag is returned; empty match returns `fail`. -/
def evalPredicateQuery (s : PeTTaSpace) (pat : Pattern) : Answers :=
  let out := s.spaceMatch pat pat
  if out.isEmpty then [.apply "fail" []] else out

/-- First-class declarative semantics for predicate-control forms. -/
inductive PredicateControlEval (s : PeTTaSpace) : Pattern → Answers → Prop where
  | translatePredicateQuery (pred pat : Pattern)
      (hdecode : decodePredicateQuery? pred = some pat) :
      PredicateControlEval s (.apply "translatePredicate" [pred]) (evalPredicateQuery s pat)
  | translatePredicateNoDecode (pred : Pattern)
      (hdecode : decodePredicateQuery? pred = none) :
      PredicateControlEval s (.apply "translatePredicate" [pred]) [.apply "fail" []]
  | catchUnary (inner : Pattern) (ans : Answers)
      (hinner : PredicateControlEval s inner ans) :
      PredicateControlEval s (.apply "catch" [inner]) ans
  | catchTernarySuccess (pred handler fallback : Pattern) (ans : Answers)
      (hpred : PredicateControlEval s (.apply "translatePredicate" [pred]) ans)
      (hgood : ans ≠ [.apply "fail" []]) :
      PredicateControlEval s (.apply "catch" [.apply "translatePredicate" [pred], handler, fallback]) ans
  | catchTernaryFallback (pred handler fallback : Pattern) (fb : Answers)
      (hpredFail : PredicateControlEval s (.apply "translatePredicate" [pred]) [.apply "fail" []])
      (hfb : PeTTaEval s fallback fb) :
      PredicateControlEval s (.apply "catch" [.apply "translatePredicate" [pred], handler, fallback]) fb

/-- `progn` is stateful and represented directly in `PeTTaCmd`. -/
def prognStateful (s₀ s₁ s₂ : EvalState) (e₁ e₂ : Pattern) (ans₁ ans₂ : Answers) : Prop :=
  PeTTaCmd s₀ e₁ s₁ ans₁ ∧
  PeTTaCmd s₁ e₂ s₂ ans₂ ∧
  PeTTaCmd s₀ (.apply "progn" [e₁, e₂]) s₂ ans₂

theorem evalPredicateQuery_eq_when_nonempty (s : PeTTaSpace) (pat : Pattern)
    (hne : s.spaceMatch pat pat ≠ []) :
    evalPredicateQuery s pat = s.spaceMatch pat pat := by
  simp [evalPredicateQuery, hne]

theorem evalPredicateQuery_eq_fail_when_empty (s : PeTTaSpace) (pat : Pattern)
    (hempty : s.spaceMatch pat pat = []) :
    evalPredicateQuery s pat = [.apply "fail" []] := by
  simp [evalPredicateQuery, hempty]

theorem translatePredicate_query_intro (s : PeTTaSpace) (pred pat : Pattern)
    (hdecode : decodePredicateQuery? pred = some pat) :
    PredicateControlEval s (.apply "translatePredicate" [pred]) (evalPredicateQuery s pat) := by
  exact PredicateControlEval.translatePredicateQuery pred pat hdecode

theorem translatePredicate_noDecode_intro (s : PeTTaSpace) (pred : Pattern)
    (hdecode : decodePredicateQuery? pred = none) :
    PredicateControlEval s (.apply "translatePredicate" [pred]) [.apply "fail" []] := by
  exact PredicateControlEval.translatePredicateNoDecode pred hdecode

theorem catch_unary_intro (s : PeTTaSpace) (inner : Pattern) (ans : Answers)
    (hinner : PredicateControlEval s inner ans) :
    PredicateControlEval s (.apply "catch" [inner]) ans := by
  exact PredicateControlEval.catchUnary inner ans hinner

theorem catch_ternary_success_intro (s : PeTTaSpace)
    (pred handler fallback : Pattern) (ans : Answers)
    (hpred : PredicateControlEval s (.apply "translatePredicate" [pred]) ans)
    (hgood : ans ≠ [.apply "fail" []]) :
    PredicateControlEval s
      (.apply "catch" [.apply "translatePredicate" [pred], handler, fallback]) ans := by
  exact PredicateControlEval.catchTernarySuccess pred handler fallback ans hpred hgood

theorem catch_ternary_fallback_intro (s : PeTTaSpace)
    (pred handler fallback : Pattern) (fb : Answers)
    (hpredFail : PredicateControlEval s (.apply "translatePredicate" [pred]) [.apply "fail" []])
    (hfb : PeTTaEval s fallback fb) :
    PredicateControlEval s
      (.apply "catch" [.apply "translatePredicate" [pred], handler, fallback]) fb := by
  exact PredicateControlEval.catchTernaryFallback pred handler fallback fb hpredFail hfb

theorem translatePredicate_query_to_pettaEval_match
    (s : PeTTaSpace) (pred pat : Pattern)
    (hdecode : decodePredicateQuery? pred = some pat)
    (hne : s.spaceMatch pat pat ≠ []) :
    PredicateControlEval s (.apply "translatePredicate" [pred]) (s.spaceMatch pat pat) ∧
    PeTTaEval s (.apply "match" [.apply "&self" [], pat, pat]) (s.spaceMatch pat pat) := by
  refine ⟨?_, ?_⟩
  · rw [← evalPredicateQuery_eq_when_nonempty s pat hne]
    exact translatePredicate_query_intro s pred pat hdecode
  · exact PeTTaEval.spaceQuery pat pat (s.spaceMatch pat pat) rfl

theorem catch_fallback_to_pettaEval
    (s : PeTTaSpace) (pred handler fallback : Pattern) (fb : Answers)
    (hpredFail : PredicateControlEval s (.apply "translatePredicate" [pred]) [.apply "fail" []])
    (hfb : PeTTaEval s fallback fb) :
    PredicateControlEval s
      (.apply "catch" [.apply "translatePredicate" [pred], handler, fallback]) fb ∧
    PeTTaEval s fallback fb := by
  exact ⟨catch_ternary_fallback_intro s pred handler fallback fb hpredFail hfb, hfb⟩

theorem prognStateful_intro (s₀ s₁ s₂ : EvalState) (e₁ e₂ : Pattern) (ans₁ ans₂ : Answers)
    (h₁ : PeTTaCmd s₀ e₁ s₁ ans₁)
    (h₂ : PeTTaCmd s₁ e₂ s₂ ans₂) :
    prognStateful s₀ s₁ s₂ e₁ e₂ ans₁ ans₂ := by
  exact ⟨h₁, h₂, PeTTaCmd.prognCmd _ _ _ _ _ _ _ h₁ h₂⟩

end PredicateControlDeclClause

/-! ## Higher-Order Control Clauses (`forall`/`foldall`) -/

namespace HigherOrderDeclClause

/-- `forall` currently compiles through the conservative catch-all path. -/
def forallFallback (cond body : Pattern) : Prop :=
  compileExpr (.apply "forall" [cond, body]) =
    .reduceCall [.apply "forall" [cond, body]]

/-- `foldall` currently compiles through the conservative catch-all path. -/
def foldallFallback (cond init body : Pattern) : Prop :=
  compileExpr (.apply "foldall" [cond, init, body]) =
    .reduceCall [.apply "foldall" [cond, init, body]]

theorem forallFallback_intro (cond body : Pattern) :
    forallFallback cond body := by
  simp [forallFallback, compileExpr]

theorem foldallFallback_intro (cond init body : Pattern) :
    foldallFallback cond init body := by
  simp [foldallFallback, compileExpr]

end HigherOrderDeclClause

/-! ## Operator-to-Clause Index (Audit Table) -/

/-- Compact index mapping core heads to declarative clause anchors in this file. -/
def operatorClauseIndex : List (String × String) :=
  [ ("if", "ControlDeclClause.ifTrueBranch / ifFalseBranch")
  , ("let", "ControlDeclClause.letToChain")
  , ("let*", "LetStarDeclClause.base / recStep")
  , ("case", "ControlDeclClause.caseSuccessStep / caseFailureStep")
  , ("translatePredicate", "PredicateControlDeclClause.PredicateControlEval.translatePredicateQuery")
  , ("catch", "PredicateControlDeclClause.PredicateControlEval.catchUnary / catchTernary*")
  , ("forall", "HigherOrderDeclClause.forallFallback")
  , ("foldall", "HigherOrderDeclClause.foldallFallback")
  , ("progn", "PredicateControlDeclClause.prognStateful, CoreDecl.progn")
  , ("prog1", "CoreDecl.prog1")
  ]

theorem operatorClauseIndex_has_if :
    ("if", "ControlDeclClause.ifTrueBranch / ifFalseBranch") ∈ operatorClauseIndex := by
  decide

theorem operatorClauseIndex_has_translatePredicate :
    ("translatePredicate", "PredicateControlDeclClause.PredicateControlEval.translatePredicateQuery")
      ∈ operatorClauseIndex := by
  decide

theorem operatorClauseIndex_has_letStar :
    ("let*", "LetStarDeclClause.base / recStep") ∈ operatorClauseIndex := by
  decide

/-! ## Focused Positive / Negative Anchors -/

theorem control_if_true_positive :
    ControlDeclClause.ifTrueBranch
      { facts := [], rules := [ifTrueRule] }
      (.apply "then-branch" []) (.apply "else-branch" []) := by
  exact ControlDeclClause.ifTrueBranch_intro
    { facts := [], rules := [ifTrueRule] }
    (.apply "then-branch" []) (.apply "else-branch" []) (by simp)

theorem control_if_true_negative_empty_rules :
    ¬ ControlDeclClause.ifTrueBranch
      { facts := [], rules := [] }
      (.apply "then-branch" []) (.apply "else-branch" []) := by
  intro h
  simpa using h.1

theorem control_let_positive :
    ControlDeclClause.letToChain
      { facts := [], rules := [letRule] }
      (.apply "x" []) (.apply "v" []) (.apply "body" []) := by
  exact ControlDeclClause.letToChain_intro
    { facts := [], rules := [letRule] }
    (.apply "x" []) (.apply "v" []) (.apply "body" []) (by simp)

theorem control_let_negative_empty_rules :
    ¬ ControlDeclClause.letToChain
      { facts := [], rules := [] }
      (.apply "x" []) (.apply "v" []) (.apply "body" []) := by
  intro h
  simpa using h.1

theorem control_case_success_positive :
    ControlDeclClause.caseSuccessStep
      { facts := [], rules := [] }
      (.apply "a" []) (.fvar "x") (.apply "branch" []) [("x", .apply "a" [])] := by
  exact ControlDeclClause.caseSuccessStep_intro
    { facts := [], rules := [] }
    (.apply "a" []) (.fvar "x") (.apply "branch" []) [("x", .apply "a" [])]
    (by simp [matchPattern])

theorem control_case_failure_positive :
    ControlDeclClause.caseFailureStep
      { facts := [], rules := [] }
      (.apply "a" []) (.apply "b" []) (.apply "then-branch" []) (.apply "else-branch" []) := by
  exact ControlDeclClause.caseFailureStep_intro
    { facts := [], rules := [] }
    (.apply "a" []) (.apply "b" []) (.apply "then-branch" []) (.apply "else-branch" [])
    (by simp [matchPattern])

theorem predicate_translatePredicate_positive :
    PredicateControlDeclClause.PredicateControlEval
      { facts := [.apply "p" []], rules := [] }
      (.apply "translatePredicate" [.apply "Predicate" [.apply "p" []]])
      [.apply "p" []] := by
  have hdecode :
      PredicateControlDeclClause.decodePredicateQuery?
        (.apply "Predicate" [.apply "p" []]) = some (.apply "p" []) := by
    simp [PredicateControlDeclClause.decodePredicateQuery?,
          PredicateControlDeclClause.startsWithAmp]; rfl
  have hsm :
      ({ facts := [.apply "p" []], rules := [] } : PeTTaSpace).spaceMatch (.apply "p" []) (.apply "p" []) =
      [.apply "p" []] := by
    simp [PeTTaSpace.spaceMatch, PeTTaSpace.storedAtoms,
          PeTTaSpace.storedRuleAtoms,
          matchPattern, matchArgs, applyBindings]
  have hquery :
      PredicateControlDeclClause.PredicateControlEval
        ({ facts := [.apply "p" []], rules := [] } : PeTTaSpace)
        (.apply "translatePredicate" [.apply "Predicate" [.apply "p" []]])
        (PredicateControlDeclClause.evalPredicateQuery
          ({ facts := [.apply "p" []], rules := [] } : PeTTaSpace) (.apply "p" [])) := by
    exact PredicateControlDeclClause.translatePredicate_query_intro
      ({ facts := [.apply "p" []], rules := [] } : PeTTaSpace)
      (.apply "Predicate" [.apply "p" []]) (.apply "p" []) hdecode
  have heval :
      PredicateControlDeclClause.evalPredicateQuery
        ({ facts := [.apply "p" []], rules := [] } : PeTTaSpace) (.apply "p" []) =
      [.apply "p" []] := by
    simp [PredicateControlDeclClause.evalPredicateQuery, hsm]
  simpa [heval] using hquery

theorem predicate_translatePredicate_negative_not_spaceMatch :
    compileExpr (.apply "translatePredicate" [.apply "p" []]) ≠
      .spaceMatch (.apply "p" []) (.apply "p" []) := by
  simp [compileExpr]

theorem predicate_catch_positive :
    PredicateControlDeclClause.PredicateControlEval
      { facts := [], rules := [] }
      (.apply "catch"
        [ .apply "translatePredicate" [.apply "&unknown" []]
        , .apply "handler" []
        , .apply "fallback" [] ])
      [.apply "fallback" []] := by
  have hpredFail :
      PredicateControlDeclClause.PredicateControlEval
        ({ facts := [], rules := [] } : PeTTaSpace)
        (.apply "translatePredicate" [.apply "&unknown" []])
        [.apply "fail" []] := by
    exact PredicateControlDeclClause.translatePredicate_noDecode_intro
      ({ facts := [], rules := [] } : PeTTaSpace) (.apply "&unknown" [])
      (by simp [PredicateControlDeclClause.decodePredicateQuery?,
                PredicateControlDeclClause.startsWithAmp]; rfl)
  have hfb :
      PeTTaEval ({ facts := [], rules := [] } : PeTTaSpace)
        (.apply "fallback" []) [.apply "fallback" []] := by
    exact PeTTaEval.ground "fallback"
  exact PredicateControlDeclClause.catch_ternary_fallback_intro
    ({ facts := [], rules := [] } : PeTTaSpace)
    (.apply "&unknown" []) (.apply "handler" []) (.apply "fallback" [])
    [.apply "fallback" []] hpredFail hfb

theorem predicate_catch_negative_not_fail :
    compileExpr (.apply "catch" [.apply "x" []]) ≠ .fail := by
  simp [compileExpr]

/-! ## Stateful Declarative Core (Includes `progn`) -/

/-- Declarative stateful core judgment.

`CoreDecl s₀ expr s₁ answers` means:
evaluate `expr` from state `s₀` to state `s₁`, returning `answers`.
-/
inductive CoreDecl : EvalState → Pattern → EvalState → Answers → Prop where
  | addAtom (s : EvalState) (p : Pattern) :
      CoreDecl s
        (.apply "add-atom" [.apply "&self" [], p])
        (s.addAtom p)
        [unitAtom]
  | removeAtom (s : EvalState) (p : Pattern) :
      CoreDecl s
        (.apply "remove-atom" [.apply "&self" [], p])
        (s.removeAtom p)
        [unitAtom]
  | getAtoms (s : EvalState) :
      CoreDecl s
        (.apply "get-atoms" [.apply "&self" []])
        s
        s.space.storedAtoms
  | pure (s : EvalState) (p : Pattern) (answers : Answers)
      (h : PureDecl s.space p answers) :
      CoreDecl s p s answers
  | progn (s₀ s₁ s₂ : EvalState) (e₁ e₂ : Pattern) (ans₁ ans₂ : Answers)
      (h₁ : CoreDecl s₀ e₁ s₁ ans₁)
      (h₂ : CoreDecl s₁ e₂ s₂ ans₂) :
      CoreDecl s₀ (.apply "progn" [e₁, e₂]) s₂ ans₂
  | prog1 (s₀ s₁ s₂ : EvalState) (e₁ e₂ : Pattern) (ans₁ ans₂ : Answers)
      (h₁ : CoreDecl s₀ e₁ s₁ ans₁)
      (h₂ : CoreDecl s₁ e₂ s₂ ans₂) :
      CoreDecl s₀ (.apply "prog1" [e₁, e₂]) s₂ ans₁

theorem CoreDecl.toPeTTaCmd
    {s₀ s₁ : EvalState} {expr : Pattern} {answers : Answers}
    (h : CoreDecl s₀ expr s₁ answers) :
    PeTTaCmd s₀ expr s₁ answers := by
  cases h with
  | addAtom _ _ =>
      exact PeTTaCmd.addAtomCmd _ _
  | removeAtom _ _ =>
      exact PeTTaCmd.removeAtomCmd _ _
  | getAtoms _ =>
      exact PeTTaCmd.getAtomsCmd _
  | pure _ _ _ hPure =>
      exact PeTTaCmd.pureEval _ _ _ (PureDecl.toPeTTaEval hPure)
  | progn _ _ _ _ _ _ _ h₁ h₂ =>
      exact PeTTaCmd.prognCmd _ _ _ _ _ _ _
        (CoreDecl.toPeTTaCmd h₁) (CoreDecl.toPeTTaCmd h₂)
  | prog1 _ _ _ _ _ _ _ h₁ h₂ =>
      exact PeTTaCmd.prog1Cmd _ _ _ _ _ _ _
        (CoreDecl.toPeTTaCmd h₁) (CoreDecl.toPeTTaCmd h₂)

theorem CoreDecl.ofPeTTaCmd
    {s₀ s₁ : EvalState} {expr : Pattern} {answers : Answers}
    (h : PeTTaCmd s₀ expr s₁ answers) :
    CoreDecl s₀ expr s₁ answers := by
  cases h with
  | addAtomCmd _ _ =>
      exact CoreDecl.addAtom _ _
  | removeAtomCmd _ _ =>
      exact CoreDecl.removeAtom _ _
  | getAtomsCmd _ =>
      exact CoreDecl.getAtoms _
  | pureEval _ _ _ hPure =>
      exact CoreDecl.pure _ _ _ (PureDecl.ofPeTTaEval hPure)
  | prognCmd _ _ _ _ _ _ _ h₁ h₂ =>
      exact CoreDecl.progn _ _ _ _ _ _ _
        (CoreDecl.ofPeTTaCmd h₁) (CoreDecl.ofPeTTaCmd h₂)
  | prog1Cmd _ _ _ _ _ _ _ h₁ h₂ =>
      exact CoreDecl.prog1 _ _ _ _ _ _ _
        (CoreDecl.ofPeTTaCmd h₁) (CoreDecl.ofPeTTaCmd h₂)

theorem coreDecl_iff_pettaCmd
    (s₀ s₁ : EvalState) (expr : Pattern) (answers : Answers) :
    CoreDecl s₀ expr s₁ answers ↔ PeTTaCmd s₀ expr s₁ answers :=
  ⟨CoreDecl.toPeTTaCmd, CoreDecl.ofPeTTaCmd⟩

/-! ## Positive / Negative Shape Examples -/

theorem coreDecl_positive_example_progn :
    CoreDecl EvalState.empty
      (.apply "progn"
        [ .apply "add-atom" [.apply "&self" [], .apply "foo" []]
        , .apply "get-atoms" [.apply "&self" []] ])
      { space := { facts := [.apply "foo" []], rules := [] } }
      [.apply "foo" []] := by
  exact
    CoreDecl.progn _ _ _ _ _ _ _
      (CoreDecl.addAtom EvalState.empty (.apply "foo" []))
      (CoreDecl.getAtoms _)

theorem pureDecl_negative_example_var_not_empty
    (s : PeTTaSpace) (x : String) :
    ¬ PureDecl s (.fvar x) [] := by
  intro h
  cases h

end Mettapedia.Languages.MeTTa.PeTTa
