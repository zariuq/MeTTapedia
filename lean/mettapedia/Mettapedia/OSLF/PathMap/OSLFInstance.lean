import Mettapedia.OSLF.PathMap.Core
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# PathMap OSLF Instance — Complete NTT Formalization

Instantiates the OSLF pipeline for the PathMap algebraic language, giving
**complete** NTT soundness theorems covering all three `AlgebraicResult` cases:

| Case | Rust | Covered by |
|------|------|------------|
| `Identity(SELF)` or `Identity(COUNTER)` | result = operand | `*_self` / `*_other` rule |
| `Element(v)` | genuinely new value | `*_element` rule |
| `None` | annihilates | **no rule fires** → diamond = `False` |

## Language Design

PathMap has four algebraic operations.  Each operation's rewrite rules are gated
by `relationQuery` premises encoding the algebraic condition:

| Premise name | Meaning |
|---|---|
| `"sub"  [x, y]` | `x ⊆ y` |
| `"nsub" [x, y]` | `¬(x ⊆ y)` |
| `"ndisj"[x, y]` | `x ∩ y ≠ ∅` |
| `"disj" [x, y]` | `x ∩ y = ∅` |

**None case = no rule fires**: when the None-producing condition holds (e.g. `pmeet`
with disjoint operands), none of the premises have nonempty tuple lists → diamond = `False`.

## NTT Theorems

All four `pathMap_*_complete` theorems are **exact biconditionals** parameterized
by a `relEnv : RelationEnv` encoding which conditions hold for the token pair.

## References

- Meredith & Stay, "Operational Semantics in Logical Form"
- Williams & Stay, "Native Type Theory" (ACT 2021)
- PathMap `ring.rs`: `/home/zar/claude/hyperon/PathMap/src/ring.rs`
-/

namespace Mettapedia.OSLF.PathMap.OSLFInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Language Definition -/

/-- PathMap algebraic language as a `LanguageDef`.

    **Types**: one sort `"V"` for PathMap node values.

    **Constructors**: four algebraic operations (`PJoin`, `PMeet`, `PSubtract`,
    `PRestrict`) plus four result constructors for the `Element` case
    (`PUnion`, `PIntersect`, `PDiff`, `PFilter`).

    **Rewrites** (10 conditional rules):

    - `PJoin`    (3 rules): self when b⊆a, other when a⊆b, PUnion when neither
    - `PMeet`    (3 rules): self when a⊆b & non-disjoint, other when b⊆a & nd, PIntersect
    - `PSubtract`(2 rules): self when disjoint, PDiff otherwise (None = a⊆b, no rule)
    - `PRestrict`(2 rules): self when a⊆b, PFilter otherwise (None = disjoint, no rule)

    All rules use `"sub"`, `"nsub"`, `"ndisj"`, `"disj"` `relationQuery` premises. -/
def pathMapLang : LanguageDef := {
  name := "PathMap",
  types := ["V"],
  terms := [
    -- Algebraic operations
    { label := "PJoin",      category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "⊔", .nonTerminal "b"] },
    { label := "PMeet",      category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "⊓", .nonTerminal "b"] },
    { label := "PSubtract",  category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "\\", .nonTerminal "b"] },
    { label := "PRestrict",  category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "|>", .nonTerminal "b"] },
    -- Element-case result constructors
    { label := "PUnion",     category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "∪", .nonTerminal "b"] },
    { label := "PIntersect", category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "∩", .nonTerminal "b"] },
    { label := "PDiff",      category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "∖", .nonTerminal "b"] },
    { label := "PFilter",    category := "V",
      params := [.simple "a" (.base "V"), .simple "b" (.base "V")],
      syntaxPattern := [.nonTerminal "a", .terminal "↾", .nonTerminal "b"] }
  ],
  equations := [],
  rewrites := [
    -- ── PJoin: never None ──────────────────────────────────────────────────
    -- b ⊆ a: Identity(SELF) → result = a
    { name := "PJoin_self",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "sub" [.fvar "b", .fvar "a"]],
      left  := .apply "PJoin" [.fvar "a", .fvar "b"],
      right := .fvar "a" },
    -- a ⊆ b: Identity(COUNTER) → result = b
    { name := "PJoin_other",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "sub" [.fvar "a", .fvar "b"]],
      left  := .apply "PJoin" [.fvar "a", .fvar "b"],
      right := .fvar "b" },
    -- neither subset: Element → result = a ∪ b
    { name := "PJoin_element",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "nsub" [.fvar "b", .fvar "a"],
                   .relationQuery "nsub" [.fvar "a", .fvar "b"]],
      left  := .apply "PJoin" [.fvar "a", .fvar "b"],
      right := .apply "PUnion" [.fvar "a", .fvar "b"] },
    -- ── PMeet: None when disjoint (no rule fires) ──────────────────────────
    -- a ⊆ b & non-disjoint: Identity(SELF) → result = a
    { name := "PMeet_self",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
                   .relationQuery "sub"   [.fvar "a", .fvar "b"]],
      left  := .apply "PMeet" [.fvar "a", .fvar "b"],
      right := .fvar "a" },
    -- b ⊆ a & non-disjoint: Identity(COUNTER) → result = b
    { name := "PMeet_other",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
                   .relationQuery "sub"   [.fvar "b", .fvar "a"]],
      left  := .apply "PMeet" [.fvar "a", .fvar "b"],
      right := .fvar "b" },
    -- non-disjoint & neither subset: Element → result = a ∩ b
    { name := "PMeet_element",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
                   .relationQuery "nsub"  [.fvar "a", .fvar "b"],
                   .relationQuery "nsub"  [.fvar "b", .fvar "a"]],
      left  := .apply "PMeet" [.fvar "a", .fvar "b"],
      right := .apply "PIntersect" [.fvar "a", .fvar "b"] },
    -- ── PSubtract: None when a ⊆ b (no rule fires) ────────────────────────
    -- disjoint: Identity(SELF) → result = a  (a \ b = a)
    { name := "PSub_self",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "disj" [.fvar "a", .fvar "b"]],
      left  := .apply "PSubtract" [.fvar "a", .fvar "b"],
      right := .fvar "a" },
    -- not(a⊆b) & non-disjoint: Element → result = a \ b
    { name := "PSub_element",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "nsub"  [.fvar "a", .fvar "b"],
                   .relationQuery "ndisj" [.fvar "a", .fvar "b"]],
      left  := .apply "PSubtract" [.fvar "a", .fvar "b"],
      right := .apply "PDiff" [.fvar "a", .fvar "b"] },
    -- ── PRestrict: None when ¬(a⊆b) ∧ disjoint (no rule fires) ───────────
    -- a ⊆ b: Identity(SELF) → result = a
    { name := "PRes_self",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "sub" [.fvar "a", .fvar "b"]],
      left  := .apply "PRestrict" [.fvar "a", .fvar "b"],
      right := .fvar "a" },
    -- not(a⊆b) & non-disjoint: Element → result = a ∩ b (prefix-filtered)
    { name := "PRes_element",
      typeContext := [("a", .base "V"), ("b", .base "V")],
      premises := [.relationQuery "nsub"  [.fvar "a", .fvar "b"],
                   .relationQuery "ndisj" [.fvar "a", .fvar "b"]],
      left  := .apply "PRestrict" [.fvar "a", .fvar "b"],
      right := .apply "PFilter" [.fvar "a", .fvar "b"] }
  ]
}

/-! ## OSLF Pipeline Instantiation -/

/-- The OSLF type system for the PathMap algebraic language.
    With a non-empty `RelationEnv`, the Galois connection ◇ ⊣ □ is automatic.
    With empty RelationEnv, all premises fail → diamond is vacuously `False`. -/
def pathMapOSLF := langOSLF pathMapLang "V"

/-- The Galois connection for PathMap: ◇ ⊣ □. -/
theorem pathMapGalois :
    GaloisConnection (langDiamond pathMapLang) (langBox pathMapLang) :=
  langGalois pathMapLang

/-! ## Section 1: Match Lemmas -/

/-- matchPattern for PJoin lhs against PJoin concrete pattern. -/
private theorem matchPattern_PJoin_eq (a b : String) :
    matchPattern (.apply "PJoin" [.fvar "a", .fvar "b"])
                 (.apply "PJoin" [.fvar a, .fvar b]) =
    [[("b", .fvar b), ("a", .fvar a)]] := by
  simp only [matchPattern, matchArgs, List.flatMap, List.filterMap, List.map,
    mergeBindings, List.foldlM,
    (by decide : (("PJoin" : String) == "PJoin") = true)]
  simp

private theorem matchPattern_PMeet_eq (a b : String) :
    matchPattern (.apply "PMeet" [.fvar "a", .fvar "b"])
                 (.apply "PMeet" [.fvar a, .fvar b]) =
    [[("b", .fvar b), ("a", .fvar a)]] := by
  simp only [matchPattern, matchArgs, List.flatMap, List.filterMap, List.map,
    mergeBindings, List.foldlM,
    (by decide : (("PMeet" : String) == "PMeet") = true)]
  simp

private theorem matchPattern_PSub_eq (a b : String) :
    matchPattern (.apply "PSubtract" [.fvar "a", .fvar "b"])
                 (.apply "PSubtract" [.fvar a, .fvar b]) =
    [[("b", .fvar b), ("a", .fvar a)]] := by
  simp only [matchPattern, matchArgs, List.flatMap, List.filterMap, List.map,
    mergeBindings, List.foldlM,
    (by decide : (("PSubtract" : String) == "PSubtract") = true)]
  simp

private theorem matchPattern_PRes_eq (a b : String) :
    matchPattern (.apply "PRestrict" [.fvar "a", .fvar "b"])
                 (.apply "PRestrict" [.fvar a, .fvar b]) =
    [[("b", .fvar b), ("a", .fvar a)]] := by
  simp only [matchPattern, matchArgs, List.flatMap, List.filterMap, List.map,
    mergeBindings, List.foldlM,
    (by decide : (("PRestrict" : String) == "PRestrict") = true)]
  simp

/-- Any non-matching constructor pair gives an empty match. -/
private theorem matchPattern_neq_apply_empty (c1 c2 : String) (args1 args2 : List Pattern)
    (hne : (c1 == c2) = false) : matchPattern (.apply c1 args1) (.apply c2 args2) = [] := by
  simp [matchPattern, hne]

/-! ## Section 2: Binding Helpers -/

private theorem applyBindings_a (a b : String) :
    applyBindings [("b", .fvar b), ("a", .fvar a)] (.fvar "a") = .fvar a := by
  simp only [applyBindings, List.find?,
    (by decide : (("b" : String) == "a") = false),
    (by decide : (("a" : String) == "a") = true)]

private theorem applyBindings_b (a b : String) :
    applyBindings [("b", .fvar b), ("a", .fvar a)] (.fvar "b") = .fvar b := by
  simp only [applyBindings, List.find?,
    (by decide : (("b" : String) == "b") = true)]

private theorem applyPremises_nil (env : RelationEnv) (lang : LanguageDef)
    (seed : Bindings) :
    applyPremisesWithEnv env lang [] seed = [seed] := by
  simp [applyPremisesWithEnv]

/-! ## Section 3: Binding Preservation Through Premise Evaluation

The central technical lemma: `mergeBindings` never removes an existing
key-value pair, so after any premise evaluation chain, the original
bindings for `"a"` and `"b"` are preserved. -/

/-- `mergeBindings existing new = some merged` implies `merged.find? (k==key) = existing.find? (k==key)`
    for any key that already appears in `existing`. -/
private lemma mergeBindings_find_preserved (key : String) (val : Pattern)
    {existing new merged : Bindings}
    (h_existing : existing.find? (fun kv => kv.1 == key) = some (key, val))
    (h_merge : mergeBindings existing new = some merged) :
    merged.find? (fun kv => kv.1 == key) = some (key, val) := by
  simp only [mergeBindings] at h_merge
  induction new generalizing existing merged with
  | nil =>
    simp only [List.foldlM] at h_merge
    obtain rfl : existing = merged := Option.some_inj.mp h_merge
    exact h_existing
  | cons head rest ih =>
    obtain ⟨k₁, v₁⟩ := head
    rw [List.foldlM_cons] at h_merge
    -- The step: look up k₁ in existing
    cases hfind : existing.find? (fun kv => kv.1 == k₁) with
    | none =>
      -- k₁ not in existing → prepend (k₁, v₁)
      simp only [hfind] at h_merge
      -- h_merge : rest.foldlM ... ((k₁,v₁) :: existing) = some merged
      apply ih (existing := (k₁, v₁) :: existing)
      · -- Show ((k₁,v₁)::existing).find? (k==key) = some (key, val)
        simp only [List.find?_cons]
        by_cases hk₁key : k₁ == key
        · -- k₁ = key: but hfind says key not found, while h_existing says it is. Contradiction.
          exfalso
          have hk₁eq : k₁ = key := beq_iff_eq.mp hk₁key
          rw [hk₁eq] at hfind
          exact absurd h_existing (by simp [hfind])
        · simp [hk₁key]
          exact h_existing
      · exact h_merge
    | some existing_val =>
      -- k₁ in existing: confirm or fail
      simp only [hfind] at h_merge
      split_ifs at h_merge with hveq
      · -- Confirmed: existing unchanged
        exact ih h_existing h_merge
      · -- Conflict: step returns none → h_merge is none = some merged, contradiction
        simp at h_merge

/-- Each single premise step preserves any existing binding in `acc`. -/
private lemma premiseStep_preserves_find (relEnv : RelationEnv) (lang : LanguageDef)
    (prem : Premise) (key : String) (val : Pattern)
    (acc : Bindings)
    (h_find : acc.find? (fun kv => kv.1 == key) = some (key, val))
    (bs : Bindings)
    (h_bs : bs ∈ premiseStepWithEnv relEnv lang acc prem) :
    bs.find? (fun kv => kv.1 == key) = some (key, val) := by
  cases prem with
  | freshness fc =>
    have := premiseStepWithEnv_freshness_mem h_bs
    subst this; exact h_find
  | congruence src tgt =>
    obtain ⟨bPrem, hmerge⟩ := premiseStepWithEnv_congruence_mem h_bs
    exact mergeBindings_find_preserved key val h_find hmerge
  | relationQuery rel args =>
    obtain ⟨bPrem, hmerge⟩ := premiseStepWithEnv_relationQuery_mem h_bs
    exact mergeBindings_find_preserved key val h_find hmerge

/-- The full foldl chain over premises preserves any initial binding. -/
private lemma foldl_premises_preserves_find
    (relEnv : RelationEnv) (lang : LanguageDef) (premises : List Premise)
    (key : String) (val : Pattern)
    (acc_list : List Bindings)
    (h_init : ∀ acc ∈ acc_list, acc.find? (fun kv => kv.1 == key) = some (key, val))
    (bs : Bindings)
    (h_bs : bs ∈ premises.foldl
        (fun accs prem => accs.flatMap fun a => premiseStepWithEnv relEnv lang a prem)
        acc_list) :
    bs.find? (fun kv => kv.1 == key) = some (key, val) := by
  induction premises generalizing acc_list with
  | nil =>
    simp only [List.foldl_nil] at h_bs
    exact h_init bs h_bs
  | cons prem rest ih =>
    simp only [List.foldl_cons] at h_bs
    apply ih (acc_list := acc_list.flatMap fun a => premiseStepWithEnv relEnv lang a prem)
    · intro bs_mid h_mid
      simp only [List.mem_flatMap] at h_mid
      obtain ⟨acc, h_acc, h_bs_mid⟩ := h_mid
      exact premiseStep_preserves_find relEnv lang prem key val acc (h_init acc h_acc) bs_mid h_bs_mid
    · exact h_bs

/-- `applyPremisesWithEnv` preserves the `"a"` binding from the seed
    `[("b", .fvar b), ("a", .fvar a)]` for any premise list and any `RelationEnv`. -/
private lemma premisesEval_preserves_a (relEnv : RelationEnv) (lang : LanguageDef)
    (premises : List Premise) (a b : String) (bs : Bindings)
    (h : bs ∈ applyPremisesWithEnv relEnv lang premises [("b", .fvar b), ("a", .fvar a)]) :
    applyBindings bs (.fvar "a") = .fvar a := by
  have h_find : bs.find? (fun kv => kv.1 == "a") = some ("a", .fvar a) := by
    simp only [applyPremisesWithEnv] at h
    apply foldl_premises_preserves_find relEnv lang premises "a" (.fvar a)
        [[("b", .fvar b), ("a", .fvar a)]]
    · intro acc h_acc
      simp only [List.mem_singleton] at h_acc; subst h_acc
      simp only [List.find?_cons,
        (by decide : (("b" : String) == "a") = false),
        (by decide : (("a" : String) == "a") = true)]
    · exact h
  simp [applyBindings, h_find]

/-- Corollary: the "b" binding is also preserved. -/
private lemma premisesEval_preserves_b (relEnv : RelationEnv) (lang : LanguageDef)
    (premises : List Premise) (a b : String) (bs : Bindings)
    (h : bs ∈ applyPremisesWithEnv relEnv lang premises [("b", .fvar b), ("a", .fvar a)]) :
    applyBindings bs (.fvar "b") = .fvar b := by
  have h_find : bs.find? (fun kv => kv.1 == "b") = some ("b", .fvar b) := by
    simp only [applyPremisesWithEnv] at h
    apply foldl_premises_preserves_find relEnv lang premises "b" (.fvar b)
        [[("b", .fvar b), ("a", .fvar a)]]
    · intro acc h_acc
      simp only [List.mem_singleton] at h_acc; subst h_acc
      simp only [List.find?_cons,
        (by decide : (("b" : String) == "b") = true)]
    · exact h
  simp [applyBindings, h_find]

/-! ## Section 4: Premise Condition Extraction -/

/-- The standard PJoin binding seed. -/
private abbrev pjoinSeed (a b : String) : Bindings := [("b", .fvar b), ("a", .fvar a)]

/-! ## Section 5: NTT Soundness Theorems

The four complete NTT theorems. Each is a biconditional parameterized by
`relEnv : RelationEnv` describing which algebraic conditions hold for the token pair.

The premise conditions `applyPremisesWithEnv relEnv pathMapLang [p] seed ≠ []`
capture exactly when the corresponding rule fires. -/

-- Shorthand for premise evaluation conditions
private abbrev condSubBA (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "sub" [.fvar "b", .fvar "a"]] (pjoinSeed a b) ≠ []

private abbrev condSubAB (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "sub" [.fvar "a", .fvar "b"]] (pjoinSeed a b) ≠ []

private abbrev condNSubBA (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "nsub" [.fvar "b", .fvar "a"]] (pjoinSeed a b) ≠ []

private abbrev condNSubAB (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "nsub" [.fvar "a", .fvar "b"]] (pjoinSeed a b) ≠ []

private abbrev condNDisj (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "ndisj" [.fvar "a", .fvar "b"]] (pjoinSeed a b) ≠ []

private abbrev condDisj (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "disj" [.fvar "a", .fvar "b"]] (pjoinSeed a b) ≠ []

-- Two-premise chain conditions
private abbrev condNDisjSubAB (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
     .relationQuery "sub"   [.fvar "a", .fvar "b"]] (pjoinSeed a b) ≠ []

private abbrev condNDisjSubBA (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
     .relationQuery "sub"   [.fvar "b", .fvar "a"]] (pjoinSeed a b) ≠ []

private abbrev condNSubABndisj (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "nsub"  [.fvar "a", .fvar "b"],
     .relationQuery "ndisj" [.fvar "a", .fvar "b"]] (pjoinSeed a b) ≠ []

-- Three-premise chain condition for PMeet element
private abbrev condNDisjNSubABNSubBA (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
     .relationQuery "nsub"  [.fvar "a", .fvar "b"],
     .relationQuery "nsub"  [.fvar "b", .fvar "a"]] (pjoinSeed a b) ≠ []

-- Two-premise chain for PJoin element
private abbrev condNSubBANSubAB (relEnv : RelationEnv) (a b : String) : Prop :=
  applyPremisesWithEnv relEnv pathMapLang
    [.relationQuery "nsub" [.fvar "b", .fvar "a"],
     .relationQuery "nsub" [.fvar "a", .fvar "b"]] (pjoinSeed a b) ≠ []


/-- NTT Soundness for PJoin — Complete, covering all AlgebraicResult cases.

    The diamond `◇φ(PJoin(a,b))` under `relEnv` is:
    - `condSubBA ∧ φ(a)`: when b⊆a, result = a  (Identity SELF)
    - `condSubAB ∧ φ(b)`: when a⊆b, result = b  (Identity COUNTER)
    - `condNSubBANSubAB ∧ φ(PUnion(a,b))`: neither, result = a∪b (Element)
    - No branch: diamond = False                                  (None — impossible for pjoin) -/
theorem pathMap_pjoin_complete (relEnv : RelationEnv) (a b : String) (φ : Pattern → Prop) :
    langDiamondUsing relEnv pathMapLang φ (.apply "PJoin" [.fvar a, .fvar b]) ↔
    (condSubBA relEnv a b ∧ φ (.fvar a)) ∨
    (condSubAB relEnv a b ∧ φ (.fvar b)) ∨
    (condNSubBANSubAB relEnv a b ∧ φ (.apply "PUnion" [.fvar a, .fvar b])) := by
  rw [langDiamondUsing_spec]
  constructor
  · -- Forward: if some reduct q satisfies φ, extract which rule fired
    rintro ⟨q, hq_red, hq_φ⟩
    rw [langReducesUsing] at hq_red
    cases hq_red with
    | topRule r hr bs0 hm bs hp hb =>
      simp only [pathMapLang, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- PJoin_self: b⊆a premise, q = fvar a
        rw [matchPattern_PJoin_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        rw [ha] at hb
        exact Or.inl ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩
      · -- PJoin_other: a⊆b premise, q = fvar b
        rw [matchPattern_PJoin_eq] at hm; simp at hm; subst hm
        have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hp
        rw [hb_bind] at hb
        exact Or.inr (Or.inl ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩)
      · -- PJoin_element: nsub×2 premises, q = PUnion(a,b)
        rw [matchPattern_PJoin_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hp
        simp only [applyBindings, List.map, ha, hb_bind] at hb
        exact Or.inr (Or.inr ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩)
      · -- PMeet_self: match against PJoin fails
        simp only [matchPattern_neq_apply_empty "PMeet" "PJoin" _ _
          (by decide : ("PMeet" == "PJoin") = false)] at hm
        simp at hm
      · -- PMeet_other
        simp only [matchPattern_neq_apply_empty "PMeet" "PJoin" _ _
          (by decide : ("PMeet" == "PJoin") = false)] at hm
        simp at hm
      · -- PMeet_element
        simp only [matchPattern_neq_apply_empty "PMeet" "PJoin" _ _
          (by decide : ("PMeet" == "PJoin") = false)] at hm
        simp at hm
      · -- PSub_self
        simp only [matchPattern_neq_apply_empty "PSubtract" "PJoin" _ _
          (by decide : ("PSubtract" == "PJoin") = false)] at hm
        simp at hm
      · -- PSub_element
        simp only [matchPattern_neq_apply_empty "PSubtract" "PJoin" _ _
          (by decide : ("PSubtract" == "PJoin") = false)] at hm
        simp at hm
      · -- PRes_self
        simp only [matchPattern_neq_apply_empty "PRestrict" "PJoin" _ _
          (by decide : ("PRestrict" == "PJoin") = false)] at hm
        simp at hm
      · -- PRes_element
        simp only [matchPattern_neq_apply_empty "PRestrict" "PJoin" _ _
          (by decide : ("PRestrict" == "PJoin") = false)] at hm
        simp at hm
  · -- Backward: construct witnesses
    rintro (⟨hcond, hφa⟩ | ⟨hcond, hφb⟩ | ⟨hcond, hφu⟩)
    · -- condSubBA: PJoin_self fires
      obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      exact ⟨.fvar a,
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PJoin_self",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "sub" [.fvar "b", .fvar "a"]],
                     left := .apply "PJoin" [.fvar "a", .fvar "b"],
                     right := .fvar "a" })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PJoin_eq]; simp)
             bs hbs
             (by exact ha),
        hφa⟩
    · -- condSubAB: PJoin_other fires
      obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hbs
      exact ⟨.fvar b,
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PJoin_other",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "sub" [.fvar "a", .fvar "b"]],
                     left := .apply "PJoin" [.fvar "a", .fvar "b"],
                     right := .fvar "b" })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PJoin_eq]; simp)
             bs hbs
             (by exact hb_bind),
        hφb⟩
    · -- condNSubBANSubAB: PJoin_element fires
      obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hbs
      exact ⟨.apply "PUnion" [.fvar a, .fvar b],
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PJoin_element",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "nsub" [.fvar "b", .fvar "a"],
                                  .relationQuery "nsub" [.fvar "a", .fvar "b"]],
                     left := .apply "PJoin" [.fvar "a", .fvar "b"],
                     right := .apply "PUnion" [.fvar "a", .fvar "b"] })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PJoin_eq]; simp)
             bs hbs
             (by simp only [applyBindings, List.map, ha, hb_bind]),
        hφu⟩

/-- NTT Soundness for PMeet — Complete.

    - `condNDisjSubAB ∧ φ(a)`: non-disjoint & a⊆b → result = a
    - `condNDisjSubBA ∧ φ(b)`: non-disjoint & b⊆a → result = b
    - `condNDisjNSubABNSubBA ∧ φ(PIntersect(a,b))`: non-disjoint & neither → result = a∩b
    - No branch (disjoint case): diamond = False  (None — explicit absence of firing) -/
theorem pathMap_pmeet_complete (relEnv : RelationEnv) (a b : String) (φ : Pattern → Prop) :
    langDiamondUsing relEnv pathMapLang φ (.apply "PMeet" [.fvar a, .fvar b]) ↔
    (condNDisjSubAB relEnv a b ∧ φ (.fvar a)) ∨
    (condNDisjSubBA relEnv a b ∧ φ (.fvar b)) ∨
    (condNDisjNSubABNSubBA relEnv a b ∧ φ (.apply "PIntersect" [.fvar a, .fvar b])) := by
  rw [langDiamondUsing_spec]
  constructor
  · rintro ⟨q, hq_red, hq_φ⟩
    rw [langReducesUsing] at hq_red
    cases hq_red with
    | topRule r hr bs0 hm bs hp hb =>
      simp only [pathMapLang, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- PJoin_self: match against PMeet fails
        simp only [matchPattern_neq_apply_empty "PJoin" "PMeet" _ _
          (by decide : ("PJoin" == "PMeet") = false)] at hm
        simp at hm
      · -- PJoin_other
        simp only [matchPattern_neq_apply_empty "PJoin" "PMeet" _ _
          (by decide : ("PJoin" == "PMeet") = false)] at hm
        simp at hm
      · -- PJoin_element
        simp only [matchPattern_neq_apply_empty "PJoin" "PMeet" _ _
          (by decide : ("PJoin" == "PMeet") = false)] at hm
        simp at hm
      · -- PMeet_self: ndisj+sub(a,b) premises, q = fvar a
        rw [matchPattern_PMeet_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        rw [ha] at hb
        exact Or.inl ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩
      · -- PMeet_other
        rw [matchPattern_PMeet_eq] at hm; simp at hm; subst hm
        have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hp
        rw [hb_bind] at hb
        exact Or.inr (Or.inl ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩)
      · -- PMeet_element
        rw [matchPattern_PMeet_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hp
        simp only [applyBindings, List.map, ha, hb_bind] at hb
        exact Or.inr (Or.inr ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩)
      · -- PSub_self: match against PMeet fails
        simp only [matchPattern_neq_apply_empty "PSubtract" "PMeet" _ _
          (by decide : ("PSubtract" == "PMeet") = false)] at hm
        simp at hm
      · -- PSub_element
        simp only [matchPattern_neq_apply_empty "PSubtract" "PMeet" _ _
          (by decide : ("PSubtract" == "PMeet") = false)] at hm
        simp at hm
      · -- PRes_self
        simp only [matchPattern_neq_apply_empty "PRestrict" "PMeet" _ _
          (by decide : ("PRestrict" == "PMeet") = false)] at hm
        simp at hm
      · -- PRes_element
        simp only [matchPattern_neq_apply_empty "PRestrict" "PMeet" _ _
          (by decide : ("PRestrict" == "PMeet") = false)] at hm
        simp at hm
  · rintro (⟨hcond, hφa⟩ | ⟨hcond, hφb⟩ | ⟨hcond, hφi⟩)
    · obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      exact ⟨.fvar a,
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PMeet_self",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
                                  .relationQuery "sub"   [.fvar "a", .fvar "b"]],
                     left := .apply "PMeet" [.fvar "a", .fvar "b"], right := .fvar "a" })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PMeet_eq]; simp)
             bs hbs (by exact ha),
        hφa⟩
    · obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hbs
      exact ⟨.fvar b,
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PMeet_other",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
                                  .relationQuery "sub"   [.fvar "b", .fvar "a"]],
                     left := .apply "PMeet" [.fvar "a", .fvar "b"], right := .fvar "b" })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PMeet_eq]; simp)
             bs hbs (by exact hb_bind),
        hφb⟩
    · obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hbs
      exact ⟨.apply "PIntersect" [.fvar a, .fvar b],
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PMeet_element",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "ndisj" [.fvar "a", .fvar "b"],
                                  .relationQuery "nsub"  [.fvar "a", .fvar "b"],
                                  .relationQuery "nsub"  [.fvar "b", .fvar "a"]],
                     left := .apply "PMeet" [.fvar "a", .fvar "b"],
                     right := .apply "PIntersect" [.fvar "a", .fvar "b"] })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PMeet_eq]; simp)
             bs hbs (by simp only [applyBindings, List.map, ha, hb_bind]),
        hφi⟩

/-- NTT Soundness for PSubtract — Complete.

    - `condDisj ∧ φ(a)`: disjoint → result = a         (Identity SELF)
    - `condNSubABndisj ∧ φ(PDiff(a,b))`: overlap → result = a∖b (Element)
    - No branch (a⊆b): diamond = False                  (None)         -/
theorem pathMap_psubtract_complete (relEnv : RelationEnv) (a b : String) (φ : Pattern → Prop) :
    langDiamondUsing relEnv pathMapLang φ (.apply "PSubtract" [.fvar a, .fvar b]) ↔
    (condDisj relEnv a b ∧ φ (.fvar a)) ∨
    (condNSubABndisj relEnv a b ∧ φ (.apply "PDiff" [.fvar a, .fvar b])) := by
  rw [langDiamondUsing_spec]
  constructor
  · rintro ⟨q, hq_red, hq_φ⟩
    rw [langReducesUsing] at hq_red
    cases hq_red with
    | topRule r hr bs0 hm bs hp hb =>
      simp only [pathMapLang, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- PJoin_self: match against PSubtract fails
        simp only [matchPattern_neq_apply_empty "PJoin" "PSubtract" _ _
          (by decide : ("PJoin" == "PSubtract") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PJoin" "PSubtract" _ _
          (by decide : ("PJoin" == "PSubtract") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PJoin" "PSubtract" _ _
          (by decide : ("PJoin" == "PSubtract") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PMeet" "PSubtract" _ _
          (by decide : ("PMeet" == "PSubtract") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PMeet" "PSubtract" _ _
          (by decide : ("PMeet" == "PSubtract") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PMeet" "PSubtract" _ _
          (by decide : ("PMeet" == "PSubtract") = false)] at hm
        simp at hm
      · -- PSub_self
        rw [matchPattern_PSub_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        rw [ha] at hb
        exact Or.inl ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩
      · -- PSub_element
        rw [matchPattern_PSub_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hp
        simp only [applyBindings, List.map, ha, hb_bind] at hb
        exact Or.inr ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩
      · simp only [matchPattern_neq_apply_empty "PRestrict" "PSubtract" _ _
          (by decide : ("PRestrict" == "PSubtract") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PRestrict" "PSubtract" _ _
          (by decide : ("PRestrict" == "PSubtract") = false)] at hm
        simp at hm
  · rintro (⟨hcond, hφa⟩ | ⟨hcond, hφd⟩)
    · obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      exact ⟨.fvar a,
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PSub_self",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "disj" [.fvar "a", .fvar "b"]],
                     left := .apply "PSubtract" [.fvar "a", .fvar "b"], right := .fvar "a" })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PSub_eq]; simp)
             bs hbs (by exact ha),
        hφa⟩
    · obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hbs
      exact ⟨.apply "PDiff" [.fvar a, .fvar b],
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PSub_element",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "nsub"  [.fvar "a", .fvar "b"],
                                  .relationQuery "ndisj" [.fvar "a", .fvar "b"]],
                     left := .apply "PSubtract" [.fvar "a", .fvar "b"],
                     right := .apply "PDiff" [.fvar "a", .fvar "b"] })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PSub_eq]; simp)
             bs hbs (by simp only [applyBindings, List.map, ha, hb_bind]),
        hφd⟩

/-- NTT Soundness for PRestrict — Complete.

    - `condSubAB ∧ φ(a)`: a⊆b → result = a              (Identity SELF)
    - `condNSubABndisj ∧ φ(PFilter(a,b))`: overlap → result = a∩b (Element)
    - No branch (¬(a⊆b) ∧ disjoint): diamond = False    (None)         -/
theorem pathMap_prestrict_complete (relEnv : RelationEnv) (a b : String) (φ : Pattern → Prop) :
    langDiamondUsing relEnv pathMapLang φ (.apply "PRestrict" [.fvar a, .fvar b]) ↔
    (condSubAB relEnv a b ∧ φ (.fvar a)) ∨
    (condNSubABndisj relEnv a b ∧ φ (.apply "PFilter" [.fvar a, .fvar b])) := by
  rw [langDiamondUsing_spec]
  constructor
  · rintro ⟨q, hq_red, hq_φ⟩
    rw [langReducesUsing] at hq_red
    cases hq_red with
    | topRule r hr bs0 hm bs hp hb =>
      simp only [pathMapLang, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [matchPattern_neq_apply_empty "PJoin" "PRestrict" _ _
          (by decide : ("PJoin" == "PRestrict") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PJoin" "PRestrict" _ _
          (by decide : ("PJoin" == "PRestrict") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PJoin" "PRestrict" _ _
          (by decide : ("PJoin" == "PRestrict") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PMeet" "PRestrict" _ _
          (by decide : ("PMeet" == "PRestrict") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PMeet" "PRestrict" _ _
          (by decide : ("PMeet" == "PRestrict") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PMeet" "PRestrict" _ _
          (by decide : ("PMeet" == "PRestrict") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PSubtract" "PRestrict" _ _
          (by decide : ("PSubtract" == "PRestrict") = false)] at hm
        simp at hm
      · simp only [matchPattern_neq_apply_empty "PSubtract" "PRestrict" _ _
          (by decide : ("PSubtract" == "PRestrict") = false)] at hm
        simp at hm
      · -- PRes_self
        rw [matchPattern_PRes_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        rw [ha] at hb
        exact Or.inl ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩
      · -- PRes_element
        rw [matchPattern_PRes_eq] at hm; simp at hm; subst hm
        have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hp
        have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hp
        simp only [applyBindings, List.map, ha, hb_bind] at hb
        exact Or.inr ⟨List.ne_nil_of_mem hp, hb ▸ hq_φ⟩
  · rintro (⟨hcond, hφa⟩ | ⟨hcond, hφf⟩)
    · obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      exact ⟨.fvar a,
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PRes_self",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "sub" [.fvar "a", .fvar "b"]],
                     left := .apply "PRestrict" [.fvar "a", .fvar "b"], right := .fvar "a" })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PRes_eq]; simp)
             bs hbs (by exact ha),
        hφa⟩
    · obtain ⟨bs, hbs⟩ := List.exists_mem_of_ne_nil _ hcond
      have ha := premisesEval_preserves_a relEnv pathMapLang _ a b bs hbs
      have hb_bind := premisesEval_preserves_b relEnv pathMapLang _ a b bs hbs
      exact ⟨.apply "PFilter" [.fvar a, .fvar b],
        by rw [langReducesUsing]
           exact DeclReducesWithPremises.topRule
             (r := { name := "PRes_element",
                     typeContext := [("a", .base "V"), ("b", .base "V")],
                     premises := [.relationQuery "nsub"  [.fvar "a", .fvar "b"],
                                  .relationQuery "ndisj" [.fvar "a", .fvar "b"]],
                     left := .apply "PRestrict" [.fvar "a", .fvar "b"],
                     right := .apply "PFilter" [.fvar "a", .fvar "b"] })
             (by simp [pathMapLang])
             (bs0 := [("b", .fvar b), ("a", .fvar a)])
             (by rw [matchPattern_PRes_eq]; simp)
             bs hbs (by simp only [applyBindings, List.map, ha, hb_bind]),
        hφf⟩

end Mettapedia.OSLF.PathMap.OSLFInstance
