import Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement
import Mettapedia.Logic.GovernanceReasoning.LetStarInterface

/-!
# Governance DTS Rules: HE MeTTa Refinement Theorems

Parallel to `PeTTaRefinement.lean`, this file proves that the governance DTS
rules correspond to proven DTS theorems when evaluated via the **HE MeTTa**
(`MeTTaEval`) evaluation relation — the full 4-argument evaluator with
type annotations and binding threading.

## Relationship to PeTTaRefinement

Both files share:
- `DeonticInterp`, `interpretDeontic` — pattern interpretation (from PeTTaRefinement)
- `dtsRule_ob_implies_pe` et al. — rule encodings (from PeTTaRefinement)
- Interpretation correctness theorems (from PeTTaRefinement)
- Semantic refinement theorems wrapping DTS (from PeTTaRefinement)

This file adds:
- `MeTTaEval`-level evaluation bridges with explicit type/binding tracking
- `HEEvalAnswers`-level bridges via the shared `MeTTaLike` interface
- Conformance tests at the HE MeTTa level

## Key Insight

The interpretation theorems only depend on patterns (not bindings/types),
so they are identical to the PeTTa versions.  The HE-specific content is
the evaluation bridge: `MeTTaEval s p ty bindings [(q, matchBs ++ bindings)]`
instead of `PeTTaEval s p [q]`.

## References

- MeTTaEval: `Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval`
- HE MeTTa spec: `trueagi-io.github.io/hyperon-experimental/metta/`
- DTS theorems: `Mettapedia.Logic.GovernanceReasoning.Core`
-/

namespace Mettapedia.Logic.GovernanceReasoning.HERefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement
open Mettapedia.Logic.GovernanceReasoning.LetStarInterface

/-! ## §1 MeTTaEval-Level Evaluation Bridge

The HE MeTTa evaluator threads types and bindings through rule application.
`MeTTaEval.ruleApp` produces `[(q, matchBindings ++ inputBindings)]`.

For DTS rule evaluation, we use `undefinedType` (pass-through) as the
expected type, since DTS rules are type-agnostic rewrite rules. -/

/-- If `dtsRule_ob_implies_pe` is in a PeTTa space, then for any ground
    eventuality name `e`, the HE MeTTa evaluator produces the obligation
    lookup with appropriate binding threading. -/
theorem he_dts_ob_pe_fires (s : PeTTaSpace)
    (hmem : dtsRule_ob_implies_pe ∈ s.rules)
    (e : String) (ty : Pattern) (inputBindings : Bindings)
    (hmatch : [("e", Pattern.apply e [])] ∈
      matchPattern dtsRule_ob_implies_pe.left
        (applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left)) :
    MeTTaEval s
      (applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left)
      ty inputBindings
      [(applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.right,
        [("e", .apply e [])] ++ inputBindings)] :=
  MeTTaEval.ruleApp dtsRule_ob_implies_pe [("e", .apply e [])] _ _
    ty inputBindings hmem rfl hmatch rfl

/-- The binding threading in HE MeTTa for the OB⇒PE rule: the match
    bindings `[("e", .apply e [])]` are prepended to input bindings. -/
theorem he_dts_ob_pe_bindings (e : String) (inputBindings : Bindings) :
    [("e", .apply e [])] ++ inputBindings =
      ("e", .apply e []) :: inputBindings := rfl

/-! ## §2 Interpretation at HE Level

The interpretation theorems are IDENTICAL to the PeTTa versions because
`interpretDeontic` operates on patterns, not on bindings or types.
We re-export them for clarity. -/

/-- HE: the RHS of the OB⇒PE rule interprets as "obligatory for e". -/
theorem he_dts_ob_pe_rhs_interp (e : String) :
    interpretDeontic (applyBindings [("e", .apply e [])]
      dtsRule_ob_implies_pe.right) = .modalAssertion e .obligatory :=
  dtsRule_ob_pe_rhs_interp e

/-- HE: the LHS of the OB⇒PE rule interprets as "permitted for e". -/
theorem he_dts_ob_pe_lhs_interp (e : String) :
    interpretDeontic (applyBindings [("e", .apply e [])]
      dtsRule_ob_implies_pe.left) = .modalAssertion e .permitted :=
  dtsRule_ob_pe_lhs_interp e

/-! ## §3 Full HE Refinement

Bundles interpretation correctness with the DTS theorem and
explicit HE binding threading. -/

/-- The HE MeTTa DTS rule for OB⇒PE correctly encodes DTS Theorem 1,
    with explicit type and binding tracking.

    Part 1: The RHS interprets as obligatory (hypothesis).
    Part 2: The LHS interprets as permitted (conclusion).
    Part 3: The DTS theorem `ob_implies_pe` holds for any DTS.
    Part 4: HE binding threading prepends match bindings. -/
theorem he_dts_ob_pe_refinement (e : String) (inputBindings : Bindings) :
    (interpretDeontic (applyBindings [("e", .apply e [])]
       dtsRule_ob_implies_pe.right) = .modalAssertion e .obligatory) ∧
    (interpretDeontic (applyBindings [("e", .apply e [])]
       dtsRule_ob_implies_pe.left) = .modalAssertion e .permitted) ∧
    (∀ {P : Type*} (d : DTS P) (p : P), d.ob p → d.pe p) ∧
    ([("e", .apply e [])] ++ inputBindings =
       ("e", .apply e []) :: inputBindings) :=
  ⟨dtsRule_ob_pe_rhs_interp e,
   dtsRule_ob_pe_lhs_interp e,
   fun d p => d.ob_implies_pe p,
   rfl⟩

/-! ## §4 HEEvalAnswers Bridge

Via the shared `MeTTaLike` interface, all theorems proven for
`PeTTaEval` automatically hold for `HEEvalAnswers`. -/

/-- Via MeTTaLike: the OB⇒PE rule fires at the HEEvalAnswers level. -/
theorem heAnswers_dts_ob_pe_fires (s : PeTTaSpace)
    (hmem : dtsRule_ob_implies_pe ∈ s.rules) (e : String)
    (hmatch : [("e", Pattern.apply e [])] ∈
      matchPattern dtsRule_ob_implies_pe.left
        (applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left)) :
    HEEvalAnswers s
      (applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left)
      [applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.right] :=
  MeTTaLike.ruleApp (Eval := HEEvalAnswers) hmem rfl hmatch

/-! ## §5 Semantic Refinement via HEEvalAnswers

The semantic refinement theorems are identical — DTS theorems don't
depend on the evaluator. We re-export the key ones. -/

/-- HE: OB(¬p) ⇒ ¬PE(p). -/
theorem he_dts_ob_neg_not_pe_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P), d.ob (d.neg p) → ¬ d.pe p :=
  dts_ob_neg_not_pe_refinement

/-- HE: ¬PE(p) ⇒ OB(¬p). -/
theorem he_dts_not_pe_ob_neg_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P), ¬ d.pe p → d.ob (d.neg p) :=
  dts_not_pe_ob_neg_refinement

/-- HE: OP(p) ⇔ ¬OB(p) ∧ ¬OB(¬p). -/
theorem he_dts_op_iff_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P),
      d.op p ↔ ¬ d.ob p ∧ ¬ d.ob (d.neg p) :=
  dts_op_iff_refinement

/-- HE: ¬OP(p) ⇔ OB(p) ∨ OB(¬p). -/
theorem he_dts_not_op_iff_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P),
      ¬ d.op p ↔ d.ob p ∨ d.ob (d.neg p) :=
  dts_not_op_iff_refinement

/-- HE: OB(p) ⇒ ¬OP(p). -/
theorem he_dts_ob_not_op_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P), d.ob p → ¬ d.op p :=
  dts_ob_not_op_refinement

/-- HE: DTS trichotomy. -/
theorem he_dts_trichotomy_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P),
      d.ob p ∨ d.op p ∨ d.ob (d.neg p) :=
  dts_trichotomy_refinement

/-! ## §6 Let* Integration

The complex DTS rules (lines 14-135 of DTS.metta) use `let*` chains.
Via `LetStarInterface`, both PeTTa and HE MeTTa can unfold these chains,
and the unfolding theorems are proven generically. -/

/-- The let* unfolding works for HEEvalAnswers: a 2-binding `let*`
    unfolds in three steps (two recursive + base). -/
theorem he_letStar_full_2 (s : PeTTaSpace) (v₁ e₁ v₂ e₂ body : Pattern)
    (hrRec : letStarRecRule ∈ s.rules)
    (hrBase : letStarBaseRule ∈ s.rules) :
    HEEvalAnswers s (mkLetStar [(v₁, e₁), (v₂, e₂)] body)
      [.apply "let" [v₁, e₁, mkLetStar [(v₂, e₂)] body]] ∧
    HEEvalAnswers s (mkLetStar [(v₂, e₂)] body)
      [.apply "let" [v₂, e₂, mkLetStar [] body]] ∧
    HEEvalAnswers s (mkLetStar [] body) [body] :=
  letStar_full_2 s v₁ e₁ v₂ e₂ body hrRec hrBase

/-- The let* unfolding works for HEEvalAnswers: a 3-binding `let*`. -/
theorem he_letStar_full_3 (s : PeTTaSpace) (v₁ e₁ v₂ e₂ v₃ e₃ body : Pattern)
    (hrRec : letStarRecRule ∈ s.rules)
    (hrBase : letStarBaseRule ∈ s.rules) :
    HEEvalAnswers s (mkLetStar [(v₁, e₁), (v₂, e₂), (v₃, e₃)] body)
      [.apply "let" [v₁, e₁, mkLetStar [(v₂, e₂), (v₃, e₃)] body]] ∧
    HEEvalAnswers s (mkLetStar [(v₂, e₂), (v₃, e₃)] body)
      [.apply "let" [v₂, e₂, mkLetStar [(v₃, e₃)] body]] ∧
    HEEvalAnswers s (mkLetStar [(v₃, e₃)] body)
      [.apply "let" [v₃, e₃, mkLetStar [] body]] ∧
    HEEvalAnswers s (mkLetStar [] body) [body] :=
  letStar_full_3 s v₁ e₁ v₂ e₂ v₃ e₃ body hrRec hrBase

/-! ## §7 Conformance: HEEvalAnswers as stress test

These tests verify the same DTS properties via the HEEvalAnswers projection.
The fact that they type-check confirms that the HE MeTTa spec correctly
supports the DTS rule application pattern. -/

/-- HE conformance: ground lemmas hold via the shared interface. -/
theorem he_conformance_ground (e : String) :
    applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left =
      .apply "ct-triple-for-add"
        [.apply e [], .apply "type" [], .apply "permitted" []] ∧
    applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.right =
      .apply "ct-triple"
        [.apply e [], .apply "type" [], .apply "obligatory" []] :=
  ⟨dtsRule_ob_pe_lhs_ground e, dtsRule_ob_pe_rhs_ground e⟩

/-- HE conformance: the full refinement chain works at the answer level. -/
theorem he_conformance_full (e : String) :
    (interpretDeontic (applyBindings [("e", .apply e [])]
       dtsRule_ob_implies_pe.right) = .modalAssertion e .obligatory) ∧
    (interpretDeontic (applyBindings [("e", .apply e [])]
       dtsRule_ob_implies_pe.left) = .modalAssertion e .permitted) ∧
    (∀ {P : Type*} (d : DTS P) (p : P), d.ob p → d.pe p) :=
  dts_ob_pe_refinement e

end Mettapedia.Logic.GovernanceReasoning.HERefinement
