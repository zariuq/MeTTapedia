import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.PeTTa.StdLib

/-!
# Shared Let* Interface for MeTTa-Like Evaluators

Defines a typeclass `MeTTaLike` abstracting over evaluation relations that
support rewrite rule application, and proves `let*` unfolding theorems
generically.  Both PeTTa and HE MeTTa are instances.

## Architecture

1. `MeTTaLike Eval` — typeclass: any evaluator that can fire rewrite rules
2. `PeTTaEval` instance — direct
3. `HEEvalAnswers` — MeTTaEval projected to answer-level (erasing types/bindings)
4. `letStarExpand` — syntactic expansion of `let*` to nested `let`
5. `mkLetStar` — construct a `let*` pattern from binding pairs
6. Per-step unfolding theorems at the `MeTTaLike` level

## References

- StdLib.lean: `letRule`, `letStarBaseRule`, `letStarRecRule`
- MeTTaEval.lean: erasure theorems to `PeTTaEval`
-/

namespace Mettapedia.Logic.GovernanceReasoning.LetStarInterface

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.PeTTa

/-! ## §1 MeTTaLike Typeclass -/

/-- Any evaluation relation that supports rewrite rule application.

    Both PeTTa (type-free, binding-free) and HE MeTTa (with types/bindings)
    satisfy this at the answer-pattern level. -/
class MeTTaLike (Eval : PeTTaSpace → Pattern → List Pattern → Prop) where
  /-- Rewrite rule application: if rule `r` in space `s` matches pattern `p`
      with bindings `bs`, evaluation produces `[applyBindings bs r.right]`. -/
  ruleApp : ∀ {s : PeTTaSpace} {r : RewriteRule} {bs : Bindings} {p : Pattern},
    r ∈ s.rules → r.premises = [] → bs ∈ matchPattern r.left p →
    Eval s p [applyBindings bs r.right]

/-- PeTTaEval is a MeTTaLike evaluator. -/
instance : MeTTaLike PeTTaEval where
  ruleApp hr hp hm := PeTTaEval.ruleApp _ _ _ _ hr hp hm rfl

/-! ## §2 HE MeTTa Answer-Level Projection -/

/-- HE MeTTa evaluation projected to answer-level patterns.

    `HEEvalAnswers s p answers` holds iff there exist some type `ty` and
    input bindings `inputBs` and results `results` such that
    `MeTTaEval s p ty inputBs results` and the pattern components of
    `results` are exactly `answers`. -/
def HEEvalAnswers (s : PeTTaSpace) (p : Pattern) (answers : List Pattern) : Prop :=
  ∃ ty inputBs results,
    MeTTaEval s p ty inputBs results ∧ results.map Prod.fst = answers

/-- HEEvalAnswers is a MeTTaLike evaluator. -/
instance : MeTTaLike HEEvalAnswers where
  ruleApp {s r bs p} hr hp hm := by
    refine ⟨undefinedType, [], _, MeTTaEval.ruleApp r bs p _ undefinedType [] hr hp hm rfl, ?_⟩
    simp

/-! ## §3 Syntactic Helpers -/

/-- Construct a `let*` pattern from a list of `(variable, value)` pairs and a body.

    `mkLetStar [(v₁,e₁), (v₂,e₂)] body` = `(let* ((pair v₁ e₁) (pair v₂ e₂)) body)` -/
def mkLetStar (bindings : List (Pattern × Pattern)) (body : Pattern) : Pattern :=
  .apply "let*"
    [ .collection .vec (bindings.map fun (v, e) => .apply "pair" [v, e]) none
    , body ]

/-- Expand `let*` to nested `let` syntactically.

    `letStarExpand [(v₁,e₁), (v₂,e₂)] body`
      = `(let v₁ e₁ (let v₂ e₂ body))` -/
def letStarExpand : List (Pattern × Pattern) → Pattern → Pattern
  | [], body => body
  | (v, e) :: rest, body => .apply "let" [v, e, letStarExpand rest body]

@[simp]
theorem letStarExpand_nil (body : Pattern) : letStarExpand [] body = body := rfl

@[simp]
theorem letStarExpand_cons (v e : Pattern) (rest : List (Pattern × Pattern)) (body : Pattern) :
    letStarExpand ((v, e) :: rest) body =
      .apply "let" [v, e, letStarExpand rest body] := rfl

/-! ## §4 Let* Base Case

`(let* () body) → body` via `letStarBaseRule`. -/

/-- For any MeTTaLike evaluator, `(let* () body)` evaluates to `[body]`. -/
theorem letStar_base {Eval : PeTTaSpace → Pattern → List Pattern → Prop}
    [MeTTaLike Eval] (s : PeTTaSpace) (body : Pattern)
    (hr : letStarBaseRule ∈ s.rules) :
    Eval s (mkLetStar [] body) [body] := by
  have hm : [("body", body)] ∈ matchPattern letStarBaseRule.left (mkLetStar [] body) := by
    simp [letStarBaseRule, mkLetStar, matchPattern, matchArgs, matchBag, mergeBindings]
  have h := MeTTaLike.ruleApp (Eval := Eval) hr rfl hm
  -- h : Eval s _ [applyBindings [("body", body)] letStarBaseRule.right]
  -- Need: applyBindings [("body", body)] (.fvar "body") = body
  simp [letStarBaseRule, applyBindings, List.find?] at h
  exact h

/-! ## §5 Let* Recursive Case

`(let* ((v e) . rest) body) → (let v e (let* rest body))` via `letStarRecRule`.

The binding order from `matchPattern` (via `matchBag` with rest variable) is:
`[("body", body), ("rest", ...), ("val", e), ("var", v)]`.

The match proof uses `simp` on concrete patterns. -/

/-- For any MeTTaLike evaluator, `(let* ((v e)) body)` → `[(let v e (let* () body))]`.
    Single binding: rest binds to empty collection. -/
theorem letStar_unfold_1 {Eval : PeTTaSpace → Pattern → List Pattern → Prop}
    [MeTTaLike Eval] (s : PeTTaSpace) (v e body : Pattern)
    (hr : letStarRecRule ∈ s.rules) :
    Eval s (mkLetStar [(v, e)] body) [.apply "let" [v, e, mkLetStar [] body]] := by
  have hm : [("body", body), ("rest", .collection .vec [] none), ("val", e), ("var", v)] ∈
      matchPattern letStarRecRule.left (mkLetStar [(v, e)] body) := by
    simp [letStarRecRule, mkLetStar, matchPattern, matchArgs, matchBag, mergeBindings]
  have h := MeTTaLike.ruleApp (Eval := Eval) hr rfl hm
  simp [letStarRecRule, mkLetStar, applyBindings, List.find?] at h
  exact h

/-- For any MeTTaLike evaluator, `(let* ((v₁ e₁) (v₂ e₂)) body)` unfolds one step. -/
theorem letStar_unfold_2 {Eval : PeTTaSpace → Pattern → List Pattern → Prop}
    [MeTTaLike Eval] (s : PeTTaSpace) (v₁ e₁ v₂ e₂ body : Pattern)
    (hr : letStarRecRule ∈ s.rules) :
    Eval s (mkLetStar [(v₁, e₁), (v₂, e₂)] body)
           [.apply "let" [v₁, e₁, mkLetStar [(v₂, e₂)] body]] := by
  have hm : [("body", body),
    ("rest", .collection .vec [.apply "pair" [v₂, e₂]] none),
    ("val", e₁), ("var", v₁)] ∈
      matchPattern letStarRecRule.left (mkLetStar [(v₁, e₁), (v₂, e₂)] body) := by
    simp [letStarRecRule, mkLetStar, matchPattern, matchArgs, matchBag, mergeBindings]
  have h := MeTTaLike.ruleApp (Eval := Eval) hr rfl hm
  simp [letStarRecRule, mkLetStar, applyBindings, List.find?] at h
  exact h

/-- For any MeTTaLike evaluator, `(let* ((v₁ e₁) (v₂ e₂) (v₃ e₃)) body)` unfolds one step. -/
theorem letStar_unfold_3 {Eval : PeTTaSpace → Pattern → List Pattern → Prop}
    [MeTTaLike Eval] (s : PeTTaSpace) (v₁ e₁ v₂ e₂ v₃ e₃ body : Pattern)
    (hr : letStarRecRule ∈ s.rules) :
    Eval s (mkLetStar [(v₁, e₁), (v₂, e₂), (v₃, e₃)] body)
           [.apply "let" [v₁, e₁, mkLetStar [(v₂, e₂), (v₃, e₃)] body]] := by
  have hm : [("body", body),
    ("rest", .collection .vec [.apply "pair" [v₂, e₂], .apply "pair" [v₃, e₃]] none),
    ("val", e₁), ("var", v₁)] ∈
      matchPattern letStarRecRule.left (mkLetStar [(v₁, e₁), (v₂, e₂), (v₃, e₃)] body) := by
    simp [letStarRecRule, mkLetStar, matchPattern, matchArgs, matchBag, mergeBindings]
  have h := MeTTaLike.ruleApp (Eval := Eval) hr rfl hm
  simp [letStarRecRule, mkLetStar, applyBindings, List.find?] at h
  exact h

/-! ## §6 Full Unfolding Sequences -/

/-- Full unfolding of a 2-binding `let*`: two recursive steps + base case. -/
theorem letStar_full_2 {Eval : PeTTaSpace → Pattern → List Pattern → Prop}
    [MeTTaLike Eval] (s : PeTTaSpace) (v₁ e₁ v₂ e₂ body : Pattern)
    (hrRec : letStarRecRule ∈ s.rules) (hrBase : letStarBaseRule ∈ s.rules) :
    Eval s (mkLetStar [(v₁, e₁), (v₂, e₂)] body)
           [.apply "let" [v₁, e₁, mkLetStar [(v₂, e₂)] body]] ∧
    Eval s (mkLetStar [(v₂, e₂)] body)
           [.apply "let" [v₂, e₂, mkLetStar [] body]] ∧
    Eval s (mkLetStar [] body) [body] :=
  ⟨letStar_unfold_2 s v₁ e₁ v₂ e₂ body hrRec,
   letStar_unfold_1 s v₂ e₂ body hrRec,
   letStar_base s body hrBase⟩

/-- Full unfolding of a 3-binding `let*`. -/
theorem letStar_full_3 {Eval : PeTTaSpace → Pattern → List Pattern → Prop}
    [MeTTaLike Eval] (s : PeTTaSpace) (v₁ e₁ v₂ e₂ v₃ e₃ body : Pattern)
    (hrRec : letStarRecRule ∈ s.rules) (hrBase : letStarBaseRule ∈ s.rules) :
    Eval s (mkLetStar [(v₁, e₁), (v₂, e₂), (v₃, e₃)] body)
           [.apply "let" [v₁, e₁, mkLetStar [(v₂, e₂), (v₃, e₃)] body]] ∧
    Eval s (mkLetStar [(v₂, e₂), (v₃, e₃)] body)
           [.apply "let" [v₂, e₂, mkLetStar [(v₃, e₃)] body]] ∧
    Eval s (mkLetStar [(v₃, e₃)] body)
           [.apply "let" [v₃, e₃, mkLetStar [] body]] ∧
    Eval s (mkLetStar [] body) [body] :=
  ⟨letStar_unfold_3 s v₁ e₁ v₂ e₂ v₃ e₃ body hrRec,
   letStar_unfold_2 s v₂ e₂ v₃ e₃ body hrRec,
   letStar_unfold_1 s v₃ e₃ body hrRec,
   letStar_base s body hrBase⟩

/-! ## §7 HEEvalAnswers Lifting -/

/-- Any PeTTaEval judgment can be lifted to HEEvalAnswers. -/
theorem pettaEval_to_heEvalAnswers {s : PeTTaSpace} {p : Pattern} {answers : List Pattern}
    (h : PeTTaEval s p answers) :
    HEEvalAnswers s p answers := by
  induction h with
  | var x => exact ⟨undefinedType, [], _, MeTTaEval.varPassThrough x _ [], rfl⟩
  | bvar n => exact ⟨undefinedType, [], _, MeTTaEval.bvarPassThrough n _ [], rfl⟩
  | ground c =>
    exact ⟨undefinedType, [], _, MeTTaEval.symbolPassThrough c _ []
      isPassThroughType_undefined, rfl⟩
  | ruleApp r bs p q hr hp hm hq =>
    refine ⟨undefinedType, [], _, MeTTaEval.ruleApp r bs p q _ [] hr hp hm hq, ?_⟩
    simp
  | spaceQuery pat tmpl results hres =>
    refine ⟨undefinedType, [], (results.map (·, [])), MeTTaEval.spaceQuery pat tmpl _ [] _ ?_, ?_⟩
    · simp [hres]
    · simp only [List.map_map]; exact List.map_id results
  | superpose alts =>
    refine ⟨undefinedType, [], _, MeTTaEval.superpose alts _ [], ?_⟩
    simp only [List.map_map]; exact List.map_id alts
  | collapse p answers _ ih =>
    obtain ⟨ty, inputBs, results, heval, hmap⟩ := ih
    refine ⟨ty, inputBs, _, MeTTaEval.collapse p _ inputBs results heval, ?_⟩
    simp [hmap]

end Mettapedia.Logic.GovernanceReasoning.LetStarInterface
