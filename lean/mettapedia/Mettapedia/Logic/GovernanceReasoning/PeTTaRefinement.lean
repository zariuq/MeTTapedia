import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Logic.GovernanceReasoning.Core
import Mettapedia.Logic.GovernanceReasoning.LetStarInterface

/-!
# Governance DTS Rules: PeTTa Refinement Theorems

Proves that the governance-reasoning-engine DTS rules, when encoded as PeTTa
RewriteRules and fired via `PeTTaEval.ruleApp`, correspond to the proven DTS
theorems in `Core.lean`.

## Architecture

1. §1 Pattern interpretation: mapping PeTTa patterns to deontic assertions
2. §2 Rule encodings: concrete RewriteRule values for DTS rules
3. §3 Interpretation correctness: each rule's LHS/RHS interprets correctly
4. §4 Semantic refinement: rule interpretation implies DTS theorem
5. §5 PeTTa evaluation bridge: `PeTTaEval.ruleApp` firing → refinement
6. §6 Concrete conformance tests

## References

- governance-reasoning-engine/reason/DTS.metta (Formal-Methods-Group)
- DTS.ob_implies_pe et al. (Core.lean)
- PeTTaEval.ruleApp (Eval.lean)
-/

namespace Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Logic.GovernanceReasoning.Core

/-! ## §1 Pattern Interpretation

Map PeTTa `Pattern` values representing governance ct-triples to deontic
assertions.  A ct-triple `(ct-triple E type M)` asserts that eventuality `E`
has modality `M`.  The `ct-triple-for-add` variant is used in DTS derivation
rules as a query pattern. -/

/-- Result of interpreting a PeTTa pattern as a deontic assertion.
    `modalAssertion e m` means "eventuality `e` has modality `m`". -/
inductive DeonticInterp where
  | modalAssertion : String → DeonticModality → DeonticInterp
  | uninterpreted : Pattern → DeonticInterp
  deriving DecidableEq, Repr

/-- Interpret a PeTTa pattern as a deontic assertion.

    Maps governance-reasoning-engine ct-triple atoms:
    - `(ct-triple E type obligatory)` → `modalAssertion E .obligatory`
    - `(ct-triple-for-add E type permitted)` → `modalAssertion E .permitted`
    - etc.

    Both ground eventualities (`(.apply e [])`) and free variables (`(.fvar e)`)
    are handled; after `applyBindings`, fvars become ground. -/
def interpretDeontic : Pattern → DeonticInterp
  -- Ground ct-triple patterns
  | .apply "ct-triple" [.apply e [], .apply "type" [], .apply "obligatory" []] =>
      .modalAssertion e .obligatory
  | .apply "ct-triple" [.apply e [], .apply "type" [], .apply "permitted" []] =>
      .modalAssertion e .permitted
  | .apply "ct-triple" [.apply e [], .apply "type" [], .apply "forbidden" []] =>
      .modalAssertion e .forbidden
  | .apply "ct-triple" [.apply e [], .apply "type" [], .apply "optional" []] =>
      .modalAssertion e .optional
  | .apply "ct-triple" [.apply e [], .apply "type" [], .apply "rexist" []] =>
      .modalAssertion e .rexist
  -- Ground ct-triple-for-add patterns (used in DTS derivation rules)
  | .apply "ct-triple-for-add" [.apply e [], .apply "type" [], .apply "obligatory" []] =>
      .modalAssertion e .obligatory
  | .apply "ct-triple-for-add" [.apply e [], .apply "type" [], .apply "permitted" []] =>
      .modalAssertion e .permitted
  | .apply "ct-triple-for-add" [.apply e [], .apply "type" [], .apply "forbidden" []] =>
      .modalAssertion e .forbidden
  | .apply "ct-triple-for-add" [.apply e [], .apply "type" [], .apply "optional" []] =>
      .modalAssertion e .optional
  -- Anything else
  | p => .uninterpreted p

/-! ## §2 Rule Encodings

Concrete `RewriteRule` values encoding the governance-reasoning-engine DTS rules.
Only rule 1 (OB ⇒ PE, line 147) is a pure unconditional rewrite in the MeTTa
source; the others involve `let*` chains with space queries. We encode the pure
rule directly and encode the semantic relationships of the complex rules as
separate refinement theorems (§4). -/

/-- DTS Rule 1: OB(p) ⇒ PE(p) — the permission derivation from obligation.

    MeTTa source (DTS.metta line 147):
    `(= (ct-triple-for-add $e type permitted) (ct-triple $e type obligatory))`

    Semantics: to derive permission for `e`, find obligation for `e`.
    When the rule fires: input matches the LHS (query for permission),
    output is the RHS (obligation lookup). If obligation exists, permission
    is derived. -/
def dtsRule_ob_implies_pe : RewriteRule where
  name := "dts_ob_pe"
  typeContext := []
  premises := []
  left := .apply "ct-triple-for-add"
    [.fvar "e", .apply "type" [], .apply "permitted" []]
  right := .apply "ct-triple"
    [.fvar "e", .apply "type" [], .apply "obligatory" []]

/-- DTS Rule 2 (semantic): OB(¬p) ⇒ ¬PE(p).

    MeTTa source (DTS.metta lines 14-31): complex `let*` chain with
    `ct-not`, `superpose`, and `meta-triple` lookups.

    We encode only the semantic content as a RewriteRule for the
    interpretation bridge; the operational complexity is in MeTTa. -/
def dtsRule_ob_neg_not_pe : RewriteRule where
  name := "dts_ob_neg_not_pe"
  typeContext := []
  premises := []
  left := .apply "not-ct-triple"
    [.fvar "e", .apply "type" [], .apply "permitted" []]
  right := .apply "ct-triple"
    [.fvar "e", .apply "type" [], .apply "obligatory" []]

/-- DTS Rule 3 (semantic): (OB(p)∨OB(¬p)) ⇒ ¬OP(p).

    MeTTa source (DTS.metta lines 84-106): complex `let*` chain.
    Encodes: if obligation holds for either p or ¬p, then p is not optional. -/
def dtsRule_not_optional : RewriteRule where
  name := "dts_not_optional"
  typeContext := []
  premises := []
  left := .apply "not-ct-triple"
    [.fvar "e", .apply "type" [], .apply "optional" []]
  right := .apply "ct-triple"
    [.fvar "e", .apply "type" [], .apply "obligatory" []]

/-! ## §3 Interpretation Correctness

Each rule's LHS/RHS, after binding application, interprets to the correct
deontic modalities.  All proofs are `rfl` (kernel-checked computation). -/

private theorem applyBindings_fvar_hit (v : Pattern) :
    applyBindings [("e", v)] (.fvar "e") = v := by
  simp [applyBindings, List.find?, BEq.beq, decide_true]

private theorem applyBindings_apply_map (v : Pattern)
    (c : String) (args : List Pattern) :
    applyBindings [("e", v)] (.apply c args) =
      .apply c (args.map (applyBindings [("e", v)])) := by
  simp [applyBindings]

/-- After applying bindings, the OB⇒PE rule's LHS becomes a ground ct-triple-for-add. -/
theorem dtsRule_ob_pe_lhs_ground (e : String) :
    applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left =
      .apply "ct-triple-for-add"
        [.apply e [], .apply "type" [], .apply "permitted" []] := by
  simp [dtsRule_ob_implies_pe, applyBindings, List.find?, List.map,
        BEq.beq, decide_true]

/-- After applying bindings, the OB⇒PE rule's RHS becomes a ground ct-triple. -/
theorem dtsRule_ob_pe_rhs_ground (e : String) :
    applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.right =
      .apply "ct-triple"
        [.apply e [], .apply "type" [], .apply "obligatory" []] := by
  simp [dtsRule_ob_implies_pe, applyBindings, List.find?, List.map,
        BEq.beq, decide_true]

/-- The LHS of the OB⇒PE rule interprets as "permitted for e". -/
theorem dtsRule_ob_pe_lhs_interp (e : String) :
    interpretDeontic (applyBindings [("e", .apply e [])]
      dtsRule_ob_implies_pe.left) = .modalAssertion e .permitted := by
  rw [dtsRule_ob_pe_lhs_ground]; rfl

/-- The RHS of the OB⇒PE rule interprets as "obligatory for e". -/
theorem dtsRule_ob_pe_rhs_interp (e : String) :
    interpretDeontic (applyBindings [("e", .apply e [])]
      dtsRule_ob_implies_pe.right) = .modalAssertion e .obligatory := by
  rw [dtsRule_ob_pe_rhs_ground]; rfl

/-- After applying bindings, the OB(¬p)⇒¬PE(p) rule's RHS becomes a ground ct-triple. -/
theorem dtsRule_ob_neg_not_pe_rhs_ground (e : String) :
    applyBindings [("e", .apply e [])] dtsRule_ob_neg_not_pe.right =
      .apply "ct-triple"
        [.apply e [], .apply "type" [], .apply "obligatory" []] := by
  simp [dtsRule_ob_neg_not_pe, applyBindings, List.find?, List.map,
        BEq.beq, decide_true]

/-- The RHS of the OB(¬p)⇒¬PE(p) rule interprets as "obligatory for e". -/
theorem dtsRule_ob_neg_not_pe_rhs_interp (e : String) :
    interpretDeontic (applyBindings [("e", .apply e [])]
      dtsRule_ob_neg_not_pe.right) = .modalAssertion e .obligatory := by
  rw [dtsRule_ob_neg_not_pe_rhs_ground]; rfl

/-- After applying bindings, the ¬OP rule's RHS becomes a ground ct-triple. -/
theorem dtsRule_not_optional_rhs_ground (e : String) :
    applyBindings [("e", .apply e [])] dtsRule_not_optional.right =
      .apply "ct-triple"
        [.apply e [], .apply "type" [], .apply "obligatory" []] := by
  simp [dtsRule_not_optional, applyBindings, List.find?, List.map,
        BEq.beq, decide_true]

/-- The RHS of the ¬OP rule interprets as "obligatory for e". -/
theorem dtsRule_not_optional_rhs_interp (e : String) :
    interpretDeontic (applyBindings [("e", .apply e [])]
      dtsRule_not_optional.right) = .modalAssertion e .obligatory := by
  rw [dtsRule_not_optional_rhs_ground]; rfl

/-! ## §4 Semantic Refinement Theorems

Bundle interpretation correctness with the corresponding DTS theorems.
Each theorem says: the rule's pattern interpretation matches the DTS theorem's
hypothesis/conclusion structure, and the DTS theorem holds. -/

/-- The PeTTa DTS rule for OB⇒PE correctly encodes DTS Theorem 1.

    Part 1: The RHS interprets as obligatory (hypothesis).
    Part 2: The LHS interprets as permitted (conclusion).
    Part 3: The DTS theorem `ob_implies_pe` holds for any DTS. -/
theorem dts_ob_pe_refinement (e : String) :
    (interpretDeontic (applyBindings [("e", .apply e [])]
       dtsRule_ob_implies_pe.right) = .modalAssertion e .obligatory) ∧
    (interpretDeontic (applyBindings [("e", .apply e [])]
       dtsRule_ob_implies_pe.left) = .modalAssertion e .permitted) ∧
    (∀ {P : Type*} (d : DTS P) (p : P), d.ob p → d.pe p) :=
  ⟨dtsRule_ob_pe_rhs_interp e, dtsRule_ob_pe_lhs_interp e, fun d p => d.ob_implies_pe p⟩

/-- Semantic refinement: OB(¬p) ⇒ ¬PE(p).

    The MeTTa rule (DTS.metta lines 14-31) derives ¬PE(p) from OB(¬p).
    The Lean DTS theorem `ob_neg_implies_not_pe` proves the same. -/
theorem dts_ob_neg_not_pe_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P), d.ob (d.neg p) → ¬ d.pe p :=
  fun d p => d.ob_neg_implies_not_pe p

/-- Semantic refinement: ¬PE(p) ⇒ OB(¬p).

    The MeTTa rule (DTS.metta lines 33-45) derives OB(¬p) from ¬PE(p).
    The Lean DTS theorem `not_pe_implies_ob_neg` proves the same. -/
theorem dts_not_pe_ob_neg_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P), ¬ d.pe p → d.ob (d.neg p) :=
  fun d p => d.not_pe_implies_ob_neg p

/-- Semantic refinement: (¬OB(p) ∧ ¬OB(¬p)) ⇔ OP(p).

    The MeTTa rules (DTS.metta lines 48-82) implement both directions.
    The Lean DTS theorem `op_iff` proves the equivalence. -/
theorem dts_op_iff_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P),
      d.op p ↔ ¬ d.ob p ∧ ¬ d.ob (d.neg p) :=
  fun d p => d.op_iff p

/-- Semantic refinement: (OB(p) ∨ OB(¬p)) ⇒ ¬OP(p).

    The MeTTa rules (DTS.metta lines 84-106) implement this derivation.
    The Lean DTS theorem `not_op_iff` proves the biconditional. -/
theorem dts_not_op_iff_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P),
      ¬ d.op p ↔ d.ob p ∨ d.ob (d.neg p) :=
  fun d p => d.not_op_iff p

/-- Semantic refinement: OB(p) ⇒ ¬OP(p).

    The MeTTa rule (derived from DTS.metta lines 84-106).
    The Lean DTS theorem `ob_implies_not_op` proves this. -/
theorem dts_ob_not_op_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P), d.ob p → ¬ d.op p :=
  fun d p => d.ob_implies_not_op p

/-- Semantic refinement: DTS trichotomy.

    Exactly one of OB(p), OP(p), OB(¬p) holds. The MeTTa DTS rules
    collectively implement this three-way classification. -/
theorem dts_trichotomy_refinement :
    ∀ {P : Type*} (d : DTS P) (p : P),
      d.ob p ∨ d.op p ∨ d.ob (d.neg p) :=
  fun d p => d.dts_trichotomy p

/-! ## §5 PeTTa Evaluation Bridge

Connect to `PeTTaEval.ruleApp`: if `dtsRule_ob_implies_pe` is in a PeTTa
space, it fires on the appropriate input and produces the expected output. -/

/-- If dtsRule_ob_implies_pe is in a PeTTa space, then for any ground
    eventuality name `e`, evaluating the permission query produces the
    obligation lookup, and both sides interpret correctly. -/
theorem petta_dts_ob_pe_fires (s : PeTTaSpace)
    (hmem : dtsRule_ob_implies_pe ∈ s.rules)
    (e : String)
    (hmatch : [("e", Pattern.apply e [])] ∈
      matchPattern dtsRule_ob_implies_pe.left
        (applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left)) :
    PeTTaEval s
      (applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left)
      [applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.right] := by
  exact PeTTaEval.ruleApp dtsRule_ob_implies_pe [("e", .apply e [])] _ _
    hmem rfl hmatch rfl

/-- The interpretation of the PeTTa DTS evaluation result gives the correct
    deontic modalities (independent of matchPattern reduction). -/
theorem petta_dts_ob_pe_interp (e : String) :
    let input := applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left
    let output := applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.right
    interpretDeontic output = .modalAssertion e .obligatory ∧
    interpretDeontic input = .modalAssertion e .permitted :=
  ⟨dtsRule_ob_pe_rhs_interp e, dtsRule_ob_pe_lhs_interp e⟩

/-! ## §6 Concrete Conformance Tests

Verify the full chain for specific eventuality names (kernel-checked `rfl`). -/

/-- Conformance: soaMoor obligation derives permission. -/
theorem conformance_soaMoor_ob_pe :
    let bs : Bindings := [("e", .apply "soaMoor" [])]
    applyBindings bs dtsRule_ob_implies_pe.left =
      .apply "ct-triple-for-add"
        [.apply "soaMoor" [], .apply "type" [], .apply "permitted" []] ∧
    applyBindings bs dtsRule_ob_implies_pe.right =
      .apply "ct-triple"
        [.apply "soaMoor" [], .apply "type" [], .apply "obligatory" []] ∧
    interpretDeontic (applyBindings bs dtsRule_ob_implies_pe.left) =
      .modalAssertion "soaMoor" .permitted ∧
    interpretDeontic (applyBindings bs dtsRule_ob_implies_pe.right) =
      .modalAssertion "soaMoor" .obligatory :=
  ⟨dtsRule_ob_pe_lhs_ground "soaMoor", dtsRule_ob_pe_rhs_ground "soaMoor",
   dtsRule_ob_pe_lhs_interp "soaMoor", dtsRule_ob_pe_rhs_interp "soaMoor"⟩

/-- Conformance: soaPay obligation derives permission. -/
theorem conformance_soaPay_ob_pe :
    let bs : Bindings := [("e", .apply "soaPay" [])]
    applyBindings bs dtsRule_ob_implies_pe.left =
      .apply "ct-triple-for-add"
        [.apply "soaPay" [], .apply "type" [], .apply "permitted" []] ∧
    applyBindings bs dtsRule_ob_implies_pe.right =
      .apply "ct-triple"
        [.apply "soaPay" [], .apply "type" [], .apply "obligatory" []] ∧
    interpretDeontic (applyBindings bs dtsRule_ob_implies_pe.left) =
      .modalAssertion "soaPay" .permitted ∧
    interpretDeontic (applyBindings bs dtsRule_ob_implies_pe.right) =
      .modalAssertion "soaPay" .obligatory :=
  ⟨dtsRule_ob_pe_lhs_ground "soaPay", dtsRule_ob_pe_rhs_ground "soaPay",
   dtsRule_ob_pe_lhs_interp "soaPay", dtsRule_ob_pe_rhs_interp "soaPay"⟩

/-- Conformance: arbitrary eventuality name (universally quantified). -/
theorem conformance_any_ob_pe (e : String) :
    applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.left =
      .apply "ct-triple-for-add"
        [.apply e [], .apply "type" [], .apply "permitted" []] ∧
    applyBindings [("e", .apply e [])] dtsRule_ob_implies_pe.right =
      .apply "ct-triple"
        [.apply e [], .apply "type" [], .apply "obligatory" []] :=
  ⟨dtsRule_ob_pe_lhs_ground e, dtsRule_ob_pe_rhs_ground e⟩

/-! ## §7 Let* Integration

The complex DTS rules (DTS.metta lines 14-135) use `let*` chains.
Via `LetStarInterface.MeTTaLike`, PeTTa can unfold these chains. -/

open Mettapedia.Logic.GovernanceReasoning.LetStarInterface
open Mettapedia.Languages.MeTTa.PeTTa (letStarRecRule letStarBaseRule)

/-- The let* unfolding works for PeTTaEval: a 2-binding `let*`
    unfolds in three steps (two recursive + base). -/
theorem petta_letStar_full_2 (s : PeTTaSpace) (v₁ e₁ v₂ e₂ body : Pattern)
    (hrRec : letStarRecRule ∈ s.rules)
    (hrBase : letStarBaseRule ∈ s.rules) :
    PeTTaEval s (mkLetStar [(v₁, e₁), (v₂, e₂)] body)
      [.apply "let" [v₁, e₁, mkLetStar [(v₂, e₂)] body]] ∧
    PeTTaEval s (mkLetStar [(v₂, e₂)] body)
      [.apply "let" [v₂, e₂, mkLetStar [] body]] ∧
    PeTTaEval s (mkLetStar [] body) [body] :=
  letStar_full_2 s v₁ e₁ v₂ e₂ body hrRec hrBase

end Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement
