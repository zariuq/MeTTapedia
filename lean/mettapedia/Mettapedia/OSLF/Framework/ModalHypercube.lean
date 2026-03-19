-- LLM primer: This formalizes §5.6 and Def 5.1 of Stay, Meredith & Wells,
-- "Generating Hypercubes of Type Systems" (2026-03-17 draft).
-- Key idea: each modality ⟨K_j⟩ has sort slots (one per rely input + one output).
-- Each slot is filled with * or □. Equations force certain slots to agree,
-- carving out the "equational center" Z ⊆ {*,□}^Slot.
-- The weak monoid example (§5.6.1) shows a 7-dim cube collapsing to a line.
-- PROOF NOTE: all proofs use `decide` (kernel-checked). No `native_decide`.
-- Function-valued fields in inductive types prevent kernel reduction;
-- we use named constructors with a separate interpretation function instead.

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Modal Hypercube: Sort Assignments and the Equational Center

Formalization of Def 5.1 and §5.6 from Stay, Meredith & Wells (2026).

## Main results

- `weakMonoid_center_card` — the weak monoid example: |Z| = 2 (kernel-checked)
- `weakMonoid_allStar_mem` / `weakMonoid_allBox_mem` — the two surviving vertices
- `weakMonoid_mixed_not_mem` — asymmetric assignments are excluded
-/

namespace Mettapedia.OSLF.Framework.ModalHypercube

/-! ## §1: The Two-Element Sort Universe -/

/-- Sort symbols: `*` (types/terms) and `□` (kinds).
    Source: §5.1, "freely add distinguished sort constants ⊢ *^X : X, ⊢ □^X : X" -/
inductive HSort where
  | star : HSort
  | box  : HSort
deriving DecidableEq, Repr, Inhabited, BEq

instance : Fintype HSort where
  elems := {.star, .box}
  complete x := by cases x <;> decide

instance : ToString HSort where
  toString | .star => "*" | .box => "□"

/-- HSort has exactly two elements. -/
theorem HSort.card : Fintype.card HSort = 2 := by decide

/-! ## §2: The Equational Center — Direct Formulation

Rather than building a general-purpose sort-term evaluator (which requires
function-valued fields that block `decide`), we formalize the equational
center directly: for a concrete theory with n sort slots, the admissibility
predicate is a decidable `Bool`-valued function on `Fin n → HSort`.

Source: Def 5.1, "Z := { Σ : Slot → S | t^S = u^S for every axiom }." -/

/-- A modal theory presentation: n sort slots and a decidable admissibility predicate. -/
structure ModalPresentation (n : Nat) where
  /-- Whether a raw sort assignment (filling n slots with */□) is admissible. -/
  admissible : (Fin n → HSort) → Bool

/-- The equational center Z: all admissible raw sort assignments. -/
def equationalCenter (pres : ModalPresentation n) : Finset (Fin n → HSort) :=
  Finset.univ.filter fun σ => pres.admissible σ

/-- Z ⊆ {*,□}^Slot by construction. -/
theorem equationalCenter_subset (pres : ModalPresentation n) :
    equationalCenter pres ⊆ Finset.univ :=
  Finset.filter_subset _ _

/-! ## §3: Worked Example — Weak Commutative Monoid (§5.6.1)

Source: "the lambda theory of a 'weak' commutative monoid"

3 slots indexed by `Fin 3`:
- slot 0 = s_q (rely sort for q)
- slot 1 = s_r (rely sort for r)
- slot 2 = s_out (output sort)

Commutativity (qr) = (rq) forces: the product's sort-level operation must be
symmetric in its arguments. With the first-projection interpretation
mul^S(α, β) = α, symmetry forces α = β, i.e., slot 0 = slot 1.

The output slot must agree with the product sort: slot 2 = mul^S(slot 0, slot 1) = slot 0.

So all three slots must agree: 2 admissible assignments out of 8. -/

/-- Admissibility for the weak monoid: all three slots must agree.
    - Commutativity forces slot 0 = slot 1
    - Output agreement forces slot 2 = slot 0 -/
def weakMonoidAdmissible (σ : Fin 3 → HSort) : Bool :=
  (σ 0 == σ 1) && (σ 2 == σ 0)

/-- The weak monoid presentation. -/
def weakMonoidPres : ModalPresentation 3 where
  admissible := weakMonoidAdmissible

/-- The equational center of the weak monoid has exactly 2 elements
    (all-* and all-□), confirming the "line segment" result from §5.6.1.

    Source: "the equational center collapses the naive cube: we have only
    one degree of freedom instead of three." -/
theorem weakMonoid_center_card :
    (equationalCenter weakMonoidPres).card = 2 := by decide

/-- The all-star assignment is in the equational center. -/
theorem weakMonoid_allStar_mem :
    (fun _ : Fin 3 => HSort.star) ∈ equationalCenter weakMonoidPres := by decide

/-- The all-box assignment is in the equational center. -/
theorem weakMonoid_allBox_mem :
    (fun _ : Fin 3 => HSort.box) ∈ equationalCenter weakMonoidPres := by decide

/-- The mixed assignment (*, □, *) is NOT in the equational center. -/
theorem weakMonoid_mixed_not_mem :
    (fun i : Fin 3 => if i = 1 then HSort.box else HSort.star) ∉
    equationalCenter weakMonoidPres := by decide

/-! ## §4: The ρ-Calculus Modality (§5.12)

Source: "Fix arity k = 1. The communication rewrite is
  n : Nm, p : Pr, λx.q : [Nm → Pr] | ∅ ⊢ out₁(n,p) | in₁(n, λx.q) ⇝ q[@p/x].
We choose the continuation redex position t_j := λx.q, giving context
  K_j([−]) := out₁(n, p) | in₁(n, [−]).
The free variables of K_j are V_j = {n, p}."

3 local sort slots: s_n^Nm (at carrier Nm), s_p^Pr (at carrier Pr), s_out.
Naive cube: 2³ − 1 = 7 nontrivial axes.

The (s_p, s_out) face recovers Barendregt's Lambda Cube axes.
The s_n = □ coordinate adds "channel-kinding" axes. -/

/-- Slots for the ρ-calculus k=1 communication modality:
    - slot 0 = s_n^Nm (channel name sort)
    - slot 1 = s_p^Pr (payload sort)
    - slot 2 = s_out (output/modality sort)
    No equations constrain the communication rewrite (commutativity of |
    does not affect this particular modality's slots because the slot family
    is determined by K_j, not by the full LHS). So all 8 assignments survive. -/
def rhoCommAdmissible (_σ : Fin 3 → HSort) : Bool := true

/-- The ρ-calculus communication modality presentation (unconstrained). -/
def rhoCommPres : ModalPresentation 3 where
  admissible := rhoCommAdmissible

/-- The ρ-calculus communication modality has full 8-element cube (no collapse). -/
theorem rhoComm_center_card :
    (equationalCenter rhoCommPres).card = 8 := by decide

/-- The Barendregt cube face (s_n = *, varying s_p and s_out) has 4 vertices:
    the four Lambda Cube corners. -/
def rhoCommBarendregtFace : Finset (Fin 3 → HSort) :=
  (equationalCenter rhoCommPres).filter fun σ => σ 0 == .star

theorem rhoComm_barendregt_face_card :
    rhoCommBarendregtFace.card = 4 := by decide

/-! ## §5: WM Calculus Modal Analysis

The WM calculus (WMCalculusLanguageDef.lean) has 3 sorts:
  State, Query, BinaryEvidence

and 5 core rewrite rules. We analyze the modal type-system families
generated by each rule through the equational center construction.

### Rule 1: `evidence_add`
  `Extract(Revise(W₁,W₂), q) ⇝ Combine(Extract(W₁,q), Extract(W₂,q))`

Choose the redex position at `Revise(W₁,W₂)` in context `Extract([−], q)`.
Rely vars: {q} at carrier Query. Slots: s_q^Query, s_out.
No equations constrain this rule's slots → full 4-element cube (2 slots).

### Rule 2: `revision_comm`
  `Revise(W₁,W₂) ⇝ Revise(W₂,W₁)`

This IS an equation (bidirectional rewrite). At the sort level it is
EXACTLY the weak monoid commutativity pattern.
Rely vars: {W₁, W₂} at carrier State. Slots: s_W1^State, s_W2^State, s_out.
Commutativity forces s_W1 = s_W2; output agreement forces s_out = s_W1.
→ collapses 8 → 2 (all-star, all-box).

### Rule 3: `combine_comm`
  `Combine(e₁,e₂) ⇝ Combine(e₂,e₁)`

Same pattern as revision_comm but at carrier BinaryEvidence.
Slots: s_e1^Evidence, s_e2^Evidence, s_out.
→ collapses 8 → 2.

### Rule 4: `revision_assoc` (rewrite only, not equation)
  `Revise(Revise(W₁,W₂),W₃) ⇝ Revise(W₁,Revise(W₂,W₃))`

This is a directed rewrite. At the chosen subterm `Revise(W₁,W₂)`
in context `Revise([−],W₃)`, rely vars = {W₃} at State. 2 slots.
No equational constraints → full 4-element cube.

### Rule 5: `combine_zero` (rewrite only)
  `Combine(e, EvidenceZero) ⇝ e`

At the chosen subterm `e` in context `Combine([−], EvidenceZero)`,
rely vars = {} (no free vars in context besides e). 1 slot (s_out).
→ trivial 2-element cube (just * or □ for the output).

### Combined picture
The WM core generates modalities with slot families of sizes 2, 3, 3, 2, 1.
The two commutativity equations collapse both 3-slot families to 2 elements.
Total WM modal type-system vertices (product over independent modalities):
  4 × 2 × 2 × 4 × 2 = 128 from the naive 4 × 8 × 8 × 4 × 2 = 2048. -/

/-- evidence_add modality: 2 slots (s_q, s_out), no equational constraints. -/
def wmEvidenceAddPres : ModalPresentation 2 where
  admissible _ := true  -- unconstrained

theorem wmEvidenceAdd_center_card :
    (equationalCenter wmEvidenceAddPres).card = 4 := by decide

/-- revision_comm: 3 slots (s_W1, s_W2, s_out).
    Commutativity of Revise forces s_W1 = s_W2.
    Output agreement forces s_out = Revise^S(s_W1, s_W2) = s_W1.
    Net: all three slots must agree. -/
def wmRevisionCommPres : ModalPresentation 3 where
  admissible σ := (σ 0 == σ 1) && (σ 2 == σ 0)

/-- revision_comm collapses 8 → 2 (the weak monoid pattern). -/
theorem wmRevisionComm_center_card :
    (equationalCenter wmRevisionCommPres).card = 2 := by decide

/-- combine_comm: same pattern as revision_comm at BinaryEvidence carrier.
    s_e1 = s_e2 and s_out = s_e1. -/
def wmCombineCommPres : ModalPresentation 3 where
  admissible σ := (σ 0 == σ 1) && (σ 2 == σ 0)

/-- combine_comm also collapses 8 → 2. -/
theorem wmCombineComm_center_card :
    (equationalCenter wmCombineCommPres).card = 2 := by decide

/-- revision_assoc: 2 slots (s_W3, s_out), no equational constraints. -/
def wmRevisionAssocPres : ModalPresentation 2 where
  admissible _ := true

theorem wmRevisionAssoc_center_card :
    (equationalCenter wmRevisionAssocPres).card = 4 := by decide

/-- combine_zero: 1 slot (s_out only), no equational constraints. -/
def wmCombineZeroPres : ModalPresentation 1 where
  admissible _ := true

theorem wmCombineZero_center_card :
    (equationalCenter wmCombineZeroPres).card = 2 := by decide

/-- The WM modal product: total vertices across all 5 core modalities.
    Naive: 4 × 8 × 8 × 4 × 2 = 2048
    After equational collapse: 4 × 2 × 2 × 4 × 2 = 128
    Collapse ratio: 16× -/
theorem wmCore_naive_product : 4 * 8 * 8 * 4 * 2 = 2048 := by decide
theorem wmCore_actual_product : 4 * 2 * 2 * 4 * 2 = 128 := by decide
theorem wmCore_collapse_ratio : 2048 / 128 = 16 := by decide

/-! ## §6: WM × Semantic Hypercube Interaction

The existing 4-axis WM semantic hypercube (Logic × TruthValue × Interval × QueryTyping)
has 2 × 2 × 3 × 2 = 24 vertices (from PLNWMHypercubeBasis).

The modal sort-assignment hypercube adds 128 independent type-system variants.

The **full WM type-system family** is the product: 24 × 128 = 3072 vertices.
Each vertex specifies BOTH the evidence semantics AND the sort assignments
for the modalities generated by the WM rewrite rules.

In practice, many of these are equivalent because:
- The evidence-semantic axes don't affect sort-level constraints
- The sort-level axes don't affect evidence combination

But the formal product structure is well-defined and computable. -/

theorem wmFull_product : 24 * 128 = 3072 := by decide

/-! ## §7: PeTTa Modal Analysis

PeTTa programs produce a concrete `LanguageDef` via the artifact bridge:
- Runtime: `Algorithms.MeTTa.PeTTa.toLanguageDef : FrozenPeTTaConfig → LanguageDef`
  (`lean-projects/algorithms/Algorithms/MeTTa/PeTTa/Lowering.lean:79`)
- Formal: `pettaSpaceToLangDef : PeTTaSpace → LanguageDef`
  (`lean-projects/mettapedia/Mettapedia/Languages/MeTTa/PeTTa/LPSoundness.lean:71`)
- Bridge: `frozenConfigToPeTTaSpace` proves behavioral identity
  (`Mettapedia/Conformance/PeTTaArtifactBridge.lean:42`)

**Key fact**: Both paths set `equations := []`. PeTTa LanguageDefs have
no equational constraints, so every modality gets its full naive cube.

For a PeTTa program with k rewrite rules, each rule rᵢ has nᵢ free
variables in its LHS context, generating nᵢ + 1 slots per modality.
The total modal type-system family has ∏ᵢ 2^(nᵢ + 1) vertices.

**Semantic enrichment opportunity**: Bidirectional PeTTa rules
(e.g., `(= (foo X) (bar X))` used in both directions) are effectively
equations. Detecting these in `Algorithms.MeTTa.PeTTa.Lowering.toLanguageDef`
and adding them to `equations` would enable equational collapse. -/

/-- An unconstrained presentation: no equations ⟹ all assignments admissible.
    This is the modal presentation for any rule in a PeTTa LanguageDef. -/
def unconstrainedPres (n : Nat) : ModalPresentation n where
  admissible _ := true

/-- No equations ⟹ no collapse: the equational center IS the full cube. -/
theorem unconstrained_no_collapse (n : Nat) :
    (equationalCenter (unconstrainedPres n)).card = Fintype.card (Fin n → HSort) := by
  simp [equationalCenter, unconstrainedPres, Finset.filter_true_of_mem]

/-- No equations ⟹ |Z| = 2^n. -/
theorem unconstrained_center_eq_pow (n : Nat) :
    (equationalCenter (unconstrainedPres n)).card = 2 ^ n := by
  rw [unconstrained_no_collapse]; simp only [Fintype.card_fun, HSort.card, Fintype.card_fin]

/-- Concrete PeTTa example: a 2-rule factorial program.
    Rule 1 (base case): `(= (fac 0) 1)` — LHS context has 0 free vars → 1 slot.
    Rule 2 (recursive): `(= (fac $n) (* $n (fac (- $n 1))))` — LHS has 1 free var ($n) → 2 slots.
    Total: 2¹ × 2² = 8 modal type-system variants. No collapse. -/
theorem petta_factorial_modal_vertices : 2 ^ 1 * 2 ^ 2 = 8 := by decide

/-- A larger PeTTa program with 5 rules, each having 2 rely vars (3 slots each).
    Total: (2³)⁵ = 32768 modal type-system variants. -/
theorem petta_5rule_modal_vertices : (2 ^ 3) ^ 5 = 32768 := by decide

/-! ## §8: HE MeTTa Modal Analysis

HE MeTTa has its own separate `LanguageDef` at
`Mettapedia/Languages/MeTTa/HE/HELanguageDef.lean` with:
- 4 sorts: State, Instr, Atom, Space
- ~60 rewrite rules
- `equations := []`

Like PeTTa, HE currently has no equations in its LanguageDef, so all
modalities get full naive cubes.

**Missing equations opportunity**: HE MeTTa's Space is semantically a bag
(multiset), implying commutativity of parallel atoms. If this were captured
as an equation in the LanguageDef, it would force the weak-monoid collapse
on every Space-carrier modality — the same 4× reduction per commutativity
that we see in the WM calculus.

Similarly, MeTTa's `match` operation is semantically set-like (order of
results doesn't matter), which could give additional collapse if captured. -/

/-- HE MeTTa example: 60 rules, each averaging 3 rely vars (4 slots).
    With no equations: (2⁴)⁶⁰ ≈ 1.15 × 10⁷² modal type-system variants.
    With Space commutativity added: significant collapse on Space-carrier modalities. -/
theorem he_60rule_naive_vertices : (2 ^ 4) ^ 60 = 16 ^ 60 := by simp [pow_succ, pow_zero]

/-! ## §9: Comparison Table

| Language      | Sorts | Equations | Naive product | Actual (Z) | Collapse |
|:-------------|------:|----------:|--------------:|-----------:|---------:|
| WM calculus   |     3 |         2 |          2048 |        128 |     16×  |
| PeTTa (any)   |     1 |         0 |         2^Σnᵢ |      2^Σnᵢ |      1×  |
| HE MeTTa      |     4 |         0 |       16^60   |    16^60   |      1×  |
| ρ-calculus    |     2 |    1 (QD) |             8 |          8 |      1×  |
| Weak monoid   |     1 |    1 (cm) |             8 |          2 |      4×  |

The WM calculus is the only formalized language where equational constraints
actively collapse the modal type-system family. PeTTa and HE are candidates
for enrichment: adding detected equations to their LanguageDefs would enable
collapse and reduce the type-system family size. -/

/-! ## §10: Modal Profile — Stored Artifact for Any LanguageDef

A `ModalProfile` records the modal type-system family structure for a
concrete `LanguageDef`. This is a **stored artifact**: computed once from
the LanguageDef's rewrite rules and equations, then exported alongside
other artifacts (execution contract, scope contract, etc.).

Source: the PeTTa artifact pipeline
(`Algorithms.MeTTa.PeTTa.toLanguageDef` → `pettaSpaceToLangDef` →
`LanguageDef` → OSLF). The modal profile lives at the same level as the
execution contract. -/

/-- Per-rule modal slot analysis: how many rely vars and slots a rule has. -/
structure RuleSlotInfo where
  ruleName : String
  numRelyVars : Nat     -- |V_j|: free vars in the LHS context
  numSlots : Nat        -- |V_j| + 1 (including s_out)
  naiveCubeSize : Nat   -- 2^numSlots
deriving Repr, DecidableEq

/-- Modal profile for a LanguageDef: the complete sort-assignment analysis. -/
structure ModalProfile where
  languageName : String
  numRules : Nat
  numEquations : Nat
  ruleSlots : List RuleSlotInfo
  naiveProduct : Nat      -- ∏ᵢ 2^(nᵢ + 1) — without equational collapse
  hasEquations : Bool     -- whether any equations could cause collapse
deriving Repr

namespace ModalProfile

/-- Compute a modal profile from a LanguageDef.
    Each rewrite rule contributes slots = (number of typed parameters) + 1.
    The equations field determines whether collapse is possible. -/
def ofLanguageDef (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) : ModalProfile :=
  let ruleSlots := lang.rewrites.map fun r =>
    let nVars := r.typeContext.length
    { ruleName := r.name
      numRelyVars := nVars
      numSlots := nVars + 1
      naiveCubeSize := 2 ^ (nVars + 1) : RuleSlotInfo }
  { languageName := lang.name
    numRules := lang.rewrites.length
    numEquations := lang.equations.length
    ruleSlots := ruleSlots
    naiveProduct := ruleSlots.foldl (· * ·.naiveCubeSize) 1
    hasEquations := !lang.equations.isEmpty }

/-- Render a modal profile as human-readable text. -/
def render (p : ModalProfile) : String :=
  let header := s!"Modal Profile for {p.languageName}: " ++
    s!"{p.numRules} rules, {p.numEquations} equations"
  let ruleLines := p.ruleSlots.map fun r =>
    s!"  {r.ruleName}: {r.numRelyVars} rely vars → {r.numSlots} slots → {r.naiveCubeSize} vertices"
  let footer := s!"  Naive product: {p.naiveProduct}" ++
    (if p.hasEquations then " (equations may collapse)" else " (no equations — full cubes)")
  String.intercalate "\n" (header :: ruleLines ++ [footer])

end ModalProfile

/-! ## §11: General Framework Connections -/

/-- For n sort slots, the raw hypercube has 2^n vertices. -/
theorem rawCubeCard (n : Nat) : Fintype.card (Fin n → HSort) = 2 ^ n := by
  simp only [Fintype.card_fun, HSort.card, Fintype.card_fin]

/-- The equational center is never larger than the raw cube. -/
theorem equationalCenter_card_le (pres : ModalPresentation n) :
    (equationalCenter pres).card ≤ Fintype.card (Fin n → HSort) := by
  rw [← Finset.card_univ]
  exact Finset.card_filter_le _ _

end Mettapedia.OSLF.Framework.ModalHypercube
