import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainDeclarationAdmission

/-!
# Source call closure for declaration-derived chain regions

Only `.self` and `.enter` consult the program oracle. Constructor names are
data and `.call` uses the environment's retained canonical implementation;
their argument expressions may still contain oracle calls. The finite
closure check follows all argument and branch subexpressions.

The proof reuses the existing `CallsTyped` structural predicate and sanitizer
lemmas with region membership as their Boolean predicate. No additional
evaluator is introduced. Only reached heads need supported metadata;
unrelated open or structural annotations remain in the declaration space.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegionSourceClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ChainRegion ChainDeclarationAdmission

mutual
def reachedCalls (self : String) : Expr → List String
  | .var _ | .const _ | .empty => []
  | .ctor _ args | .prim _ args | .call _ args => reachedCallsAll self args
  | .self args => self :: reachedCallsAll self args
  | .enter head args => head :: reachedCallsAll self args
  | .letE _ value body | .matchE value _ body => reachedCalls self value ++ reachedCalls self body
  | .ifE test yes no => reachedCalls self test ++ reachedCalls self yes ++ reachedCalls self no
  | .caseE key _ bodies => reachedCalls self key ++ reachedCallsAll self bodies

def reachedCallsAll (self : String) : List Expr → List String
  | [] => []
  | first :: rest => reachedCalls self first ++ reachedCallsAll self rest
end

def within (heads : List String) (head : String) : Bool := heads.contains head

mutual
theorem reachedCalls_checked (heads : List String) (self : String) : ∀ expression,
    (reachedCalls self expression).all (within heads) = true ↔
      CallsTyped (within heads) (within heads self) expression
  | .var _ => by simp [reachedCalls, CallsTyped]
  | .const _ => by simp [reachedCalls, CallsTyped]
  | .ctor _ args => reachedCallsAll_checked heads self args
  | .self args => by simp [reachedCalls, CallsTyped, reachedCallsAll_checked]
  | .prim _ args => reachedCallsAll_checked heads self args
  | .call _ args => reachedCallsAll_checked heads self args
  | .enter _ args => by simp [reachedCalls, CallsTyped, reachedCallsAll_checked]
  | .letE _ value body => by simp [reachedCalls, CallsTyped, reachedCalls_checked]
  | .ifE test yes no => by simp [reachedCalls, CallsTyped, reachedCalls_checked]
  | .empty => by simp [reachedCalls, CallsTyped]
  | .caseE key _ bodies => by
      simp [reachedCalls, CallsTyped, reachedCalls_checked, reachedCallsAll_checked]
  | .matchE source _ body => by simp [reachedCalls, CallsTyped, reachedCalls_checked]

theorem reachedCallsAll_checked (heads : List String) (self : String) : ∀ expressions,
    (reachedCallsAll self expressions).all (within heads) = true ↔
      CallsTypedAll (within heads) (within heads self) expressions
  | [] => by simp [reachedCallsAll, CallsTypedAll]
  | _ :: _ => by
      simp [reachedCallsAll, CallsTypedAll, reachedCalls_checked, reachedCallsAll_checked]
end

/-- Finite source closure: inspect every authored RHS at every region head.
No claim is made that constructor or retained-canonical names are dynamic
region calls. Calls inside their arguments are nevertheless included. -/
def closedEquationsCheck (heads : List String) (equations : String → List Equation) : Bool :=
  heads.all fun self => (equations self).all fun equation =>
    (reachedCalls self equation.rhs).all (within heads)

theorem closedEquations_rhs {heads : List String} {equations : String → List Equation}
    (closed : closedEquationsCheck heads equations = true) {self : String}
    (member : self ∈ heads) {equation : Equation} (present : equation ∈ equations self) :
    CallsTyped (within heads) (within heads self) equation.rhs := by
  exact (reachedCalls_checked heads self equation.rhs).mp
    (List.all_eq_true.mp (List.all_eq_true.mp closed self member) equation present)

theorem sanitized_oracles_eq (heads : List String) (self : String)
    (left right : String → List Atom → Multiset Atom)
    (agree : ∀ head ∈ heads, left head = right head) :
    sanitize (within heads) (within heads self) (oracleOf left self) =
      sanitize (within heads) (within heads self) (oracleOf right self) := by
  unfold sanitize oracleOf
  congr 1
  · funext args
    split_ifs with present
    · exact congrFun (agree self (by simpa [within] using present)) args
    · rfl
  · funext head args
    split_ifs with present
    · exact congrFun (agree head (by simpa [within] using present)) args
    · rfl

theorem eval_region_congr (environment : Env) (heads : List String) (self : String)
    (left right : String → List Atom → Multiset Atom)
    (agree : ∀ head ∈ heads, left head = right head) (expression : Expr)
    (closed : CallsTyped (within heads) (within heads self) expression)
    (bindings : List (String × Atom)) :
    Expr.eval environment (oracleOf left self) bindings expression =
      Expr.eval environment (oracleOf right self) bindings expression := by
  rw [eval_sanitize environment _ _ _ expression bindings closed,
    eval_sanitize environment _ _ (oracleOf right self) expression bindings closed,
    sanitized_oracles_eq heads self left right agree]

theorem evalAll_region_congr (environment : Env) (heads : List String) (self : String)
    (left right : String → List Atom → Multiset Atom)
    (agree : ∀ head ∈ heads, left head = right head) (expressions : List Expr)
    (closed : CallsTypedAll (within heads) (within heads self) expressions)
    (bindings : List (String × Atom)) :
    Expr.evalAll environment (oracleOf left self) bindings expressions =
      Expr.evalAll environment (oracleOf right self) bindings expressions := by
  rw [evalAll_sanitize environment _ _ _ expressions bindings closed,
    evalAll_sanitize environment _ _ (oracleOf right self) expressions bindings closed,
    sanitized_oracles_eq heads self left right agree]

mutual
theorem evalOut_region_congr (environment : Env) (heads : List String) (self : String)
    (left right : String → List Atom → Multiset Atom)
    (agree : ∀ head ∈ heads, left head = right head) :
    ∀ (expression : Expr) (bindings : List (String × Atom)),
    CallsTyped (within heads) (within heads self) expression →
    Expr.evalOut environment (oracleOf left self) self bindings expression =
      Expr.evalOut environment (oracleOf right self) self bindings expression
  | .var _, _, _ => rfl
  | .const _, _, _ => rfl
  | .ctor name args, bindings, closed => by
      simp only [Expr.evalOut]
      rw [eval_region_congr environment heads self left right agree (.ctor name args) closed bindings]
  | .self args, bindings, closed => by
      simp only [Expr.evalOut]
      rw [evalAll_region_congr environment heads self left right agree args closed.2 bindings]
  | .prim name args, bindings, closed => by
      simp only [Expr.evalOut]
      rw [eval_region_congr environment heads self left right agree (.prim name args) closed bindings]
  | .call name args, bindings, closed => by
      simp only [Expr.evalOut]
      rw [eval_region_congr environment heads self left right agree (.call name args) closed bindings]
  | .enter _ args, bindings, closed => by
      simp only [Expr.evalOut]
      rw [evalAll_region_congr environment heads self left right agree args closed.2 bindings]
  | .letE pattern value body, bindings, closed => by
      simp only [Expr.evalOut]
      rw [eval_region_congr environment heads self left right agree value closed.1 bindings]
      refine Multiset.bind_congr fun result _ => ?_
      cases Pat.matchUnder bindings pattern result with
      | none => rfl
      | some next => exact evalOut_region_congr environment heads self left right agree body next closed.2
  | .ifE test yes no, bindings, closed => by
      simp only [Expr.evalOut]
      rw [eval_region_congr environment heads self left right agree test closed.1 bindings,
        evalOut_region_congr environment heads self left right agree yes bindings closed.2.1,
        evalOut_region_congr environment heads self left right agree no bindings closed.2.2]
  | .empty, _, _ => rfl
  | .caseE key patterns bodies, bindings, closed => by
      simp only [Expr.evalOut]
      rw [eval_region_congr environment heads self left right agree key closed.1 bindings]
      exact Multiset.bind_congr fun result _ =>
        evalOutArms_region_congr environment heads self left right agree result patterns bodies bindings closed.2
  | .matchE source pattern body, bindings, closed => by
      simp only [Expr.evalOut]
      rw [eval_region_congr environment heads self left right agree (.matchE source pattern body) closed bindings]

theorem evalOutArms_region_congr (environment : Env) (heads : List String) (self : String)
    (left right : String → List Atom → Multiset Atom)
    (agree : ∀ head ∈ heads, left head = right head) (key : Atom) :
    ∀ (patterns : List Pat) (bodies : List Expr) (bindings : List (String × Atom)),
    CallsTypedAll (within heads) (within heads self) bodies →
    Expr.evalOutArms environment (oracleOf left self) self bindings key patterns bodies =
      Expr.evalOutArms environment (oracleOf right self) self bindings key patterns bodies
  | pattern :: patterns, body :: bodies, bindings, closed => by
      simp only [Expr.evalOutArms]
      cases Pat.matchUnder bindings pattern key with
      | some next => exact evalOut_region_congr environment heads self left right agree body next closed.1
      | none => exact evalOutArms_region_congr environment heads self left right agree key patterns bodies bindings closed.2
  | [], _, _, _ => by simp [Expr.evalOutArms]
  | _ :: _, [], _, _ => rfl
end

theorem stepsOf_region_congr (environment : Env) {heads : List String}
    {equations : String → List Equation} (closed : closedEquationsCheck heads equations = true)
    (left right : String → List Atom → Multiset Atom)
    (agree : ∀ head ∈ heads, left head = right head) {self : String}
    (member : self ∈ heads) (args : List Atom) :
    stepsOf environment equations self left args = stepsOf environment equations self right args := by
  unfold stepsOf
  refine Multiset.bind_congr fun equation present => ?_
  cases Pat.matchAll equation.pats args with
  | none => rfl
  | some bindings =>
      exact evalOut_region_congr environment heads self left right agree equation.rhs bindings
        (closedEquations_rhs closed member (by simpa using present))

/-- For interpreting tail outcomes, use the existing source/outcome algebra.
This includes tail re-entry without a second transition relation. -/
theorem stepsOf_answers_region_congr (environment : Env) {heads : List String}
    {equations : String → List Equation} (closed : closedEquationsCheck heads equations = true)
    (left right : String → List Atom → Multiset Atom)
    (agree : ∀ head ∈ heads, left head = right head) {self : String}
    (member : self ∈ heads) (args : List Atom) :
    (stepsOf environment equations self left args).bind (outcomeAnswers left) =
      (stepsOf environment equations self right args).bind (outcomeAnswers right) := by
  rw [stepsOf_answers, stepsOf_answers]
  unfold equationsBody
  refine Multiset.bind_congr fun equation present => ?_
  cases Pat.matchAll equation.pats args with
  | none => rfl
  | some bindings =>
      exact eval_region_congr environment heads self left right agree equation.rhs
        (closedEquations_rhs closed member (by simpa using present)) bindings

/-- Protocol signatures need agree only at the syntactically closed region.
The equality is exact at each source fuel, not merely at termination. -/
theorem protocol_signatures_congr (declarations : Decls) (grounded : String → Bool)
    (environment : Env) {heads : List String} {equations : String → List Equation}
    (closed : closedEquationsCheck heads equations = true)
    (left right : String → Option (Ty String))
    (agree : ∀ head ∈ heads, left head = right head) :
    ∀ fuel head, head ∈ heads → ∀ args,
    protocolRunS declarations grounded left (stepsOf environment equations) fuel head args =
      protocolRunS declarations grounded right (stepsOf environment equations) fuel head args
  | 0, _, _, _ => rfl
  | fuel + 1, head, member, args => by
      have oracleAgree : ∀ name ∈ heads,
          protocolRunS declarations grounded left (stepsOf environment equations) fuel name =
          protocolRunS declarations grounded right (stepsOf environment equations) fuel name := by
        intro name present
        funext values
        exact protocol_signatures_congr declarations grounded environment closed left right agree fuel name present values
      have bodyAgree := fun values => stepsOf_answers_region_congr environment closed _ _ oracleAgree member values
      simp only [protocolRunS, agree head member]
      cases right head with
      | none => exact bodyAgree args
      | some row =>
          dsimp only
          congr 1
          funext values
          exact bodyAgree values

/-- Metadata admission plus actual source-call closure replaces the former
whole-space closed-value restriction. Unrelated annotations still govern
typing in Γ; they are not erased or rewritten to untyped declarations. -/
theorem region_source_run_eq_protocol {source : Source} {heads : List String}
    (functional : functionalCheck source = true) (admitted : regionCheck source heads = true)
    (grounded : String → Bool) (environment : Env) (equations : String → List Equation)
    (closed : closedEquationsCheck heads equations = true)
    (fuel : Nat) (head : String) (member : head ∈ heads) (args : List Atom) :
    run (declarations source) grounded (generatedRows source) (stepsOf environment equations)
      fuel none head args =
    protocolRunS (declarations source) grounded (sourceSignature source) (stepsOf environment equations)
      fuel head args := by
  rw [program_run_eq_protocol _ _ (functional_of_check functional)]
  exact protocol_signatures_congr _ _ _ closed _ _
    (fun _ present => region_signature_exact admitted present) fuel head member args

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegionSourceClosure
