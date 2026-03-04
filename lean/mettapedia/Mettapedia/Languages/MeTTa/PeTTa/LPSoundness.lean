import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Logic.LP.MeTTaILBridge

/-!
# PeTTa ↔ LP Soundness Bridge

Connects `PeTTaEval` (the pure PeTTa evaluation relation) to the **least Herbrand
model** of a compiled LP knowledge base, closing the chain:

```
matchPattern_correct (MatchSpec)
  ↓
lp_complete_topRule (MeTTaILBridge)
  ↓
petta_ruleApp_lp_sound (this file)
```

## Architecture

For the `ruleApp` case of `PeTTaEval`, the bridge works as follows:

1. A `PeTTaSpace` is compiled to a `LanguageDef` (rules only) and then to an LP
   `KnowledgeBase` via `languageDefToLPKB`.
2. `matchPattern_correct` (proven in `MatchSpec.lean`) converts the algorithmic
   match evidence `bs ∈ matchPattern r.left p` into the semantic identity
   `applyBindings bs r.left = p`.
3. `lp_complete_topRule` (proven in `MeTTaILBridge.lean`) then gives membership
   of `encodeReduces p q` in `leastHerbrandModel`.

## Fragment Restriction (`pettaRuleSafe`)

The bridge covers rules where:
- Both LHS and RHS are `morkTranslatable` (no `.subst`, no rest-variable collections)
- The LHS is `isMatchCorrect` (no `.collection`, no `.subst`) — needed for
  `matchPattern_correct` to apply

Rules outside this fragment (collection patterns, substitution patterns) are
deferred to future work.

## Scope of this File

- `ruleApp`: covered, with `pettaRuleSafe` restriction.
- `spaceQuery` (`match &self pat tmpl`): the soundness of `spaceMatch` is already
  proven in `SpaceSemantics.lean`; LP encoding of the EDB is deferred.
- `superpose`, `collapse`, `var`, `bvar`, `ground`: no LP model claim needed
  (these are control-flow / structural forms, not rule derivations).

## References

- `Mettapedia.Logic.LP.MeTTaILBridge` — LP encoding of MeTTaIL patterns
- `Mettapedia.OSLF.MeTTaIL.MatchSpec` — `matchPattern_correct`
- `Mettapedia.Languages.MeTTa.PeTTa.Eval` — `PeTTaEval` inductive
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.LPSoundness

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.MeTTaILBridge
open Mettapedia.Languages.ProcessCalculi.MORK (morkTranslatable)

/-! ## Compiling PeTTaSpace to LP -/

/-- Convert a `PeTTaSpace` to a `LanguageDef` for LP compilation.

    Only `s.rules` is preserved. Facts (`s.facts`) are not encoded here —
    they are handled by `spaceMatch` in `SpaceSemantics.lean`. -/
def pettaSpaceToLangDef (s : PeTTaSpace) : LanguageDef where
  name                  := "PeTTaSpace"
  types                 := []
  terms                 := []
  equations             := []
  rewrites              := s.rules
  congruenceCollections := []   -- no congruence descent for flat PeTTa rules

/-- The LP `KnowledgeBase` compiled from a `PeTTaSpace`. -/
def pettaSpaceToLPKB (s : PeTTaSpace) : KnowledgeBase mettailLPSig :=
  languageDefToLPKB (pettaSpaceToLangDef s)

/-- Unfolding lemma: `pettaSpaceToLPKB` is exactly `languageDefToLPKB` of the lang def. -/
@[simp]
theorem pettaSpaceToLPKB_eq (s : PeTTaSpace) :
    pettaSpaceToLPKB s = languageDefToLPKB (pettaSpaceToLangDef s) := rfl

/-- Rules in the compiled KB come exactly from `s.rules`. -/
theorem pettaSpaceToLangDef_rewrites (s : PeTTaSpace) :
    (pettaSpaceToLangDef s).rewrites = s.rules := rfl

/-! ## Fragment Predicate -/

/-- A rule is **PeTTa LP-safe** if it satisfies the `lpTranslatable` conditions:
    - Both LHS and RHS are `morkTranslatable` (no `.subst`, no rest-variable collections)
    - The LHS is `isMatchCorrect` (no `.collection`, no `.subst`)

    This is exactly `lpTranslatable` from `MeTTaILBridge`. -/
abbrev pettaRuleSafe (r : RewriteRule) : Bool := lpTranslatable r

/-- Unpack `pettaRuleSafe` into its three components. -/
theorem pettaRuleSafe_iff (r : RewriteRule) :
    pettaRuleSafe r = true ↔
    morkTranslatable r.left = true ∧
    morkTranslatable r.right = true ∧
    Pattern.isMatchCorrect r.left = true := by
  simp only [pettaRuleSafe, lpTranslatable, Bool.and_eq_true]
  tauto

/-! ## Main Soundness Theorem -/

/-- **LP Soundness for PeTTa `ruleApp`** (in the LP-safe fragment).

    If rule `r` fires — matching `p` with bindings `bs`, producing `q` — and `r`
    is `pettaRuleSafe`, then the encoded reduction `encodeReduces p q` belongs to
    the least Herbrand model of the compiled LP knowledge base.

    **Proof chain**:
    - `matchPattern_correct hm hmc` (MatchSpec) → `applyBindings bs r.left = p`
    - `lp_complete_topRule` (MeTTaILBridge) → `encodeReduces p q ∈ leastHerbrandModel`

    **Preconditions of `PeTTaEval.ruleApp`** (brought in explicitly):
    - `hr`:    `r ∈ s.rules`
    - `hprem`: `r.premises = []` (unconditional rule only)
    - `hm`:    `bs ∈ matchPattern r.left p`
    - `hq`:    `applyBindings bs r.right = q`
    - `hsafe`: `pettaRuleSafe r = true` (fragment restriction) -/
theorem petta_ruleApp_lp_sound (s : PeTTaSpace)
    (r : RewriteRule) (bs : Bindings) (p q : Pattern)
    (hr    : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm    : bs ∈ matchPattern r.left p)
    (hq    : applyBindings bs r.right = q)
    (hsafe : pettaRuleSafe r = true) :
    encodeReduces p q ∈ leastHerbrandModel (pettaSpaceToLPKB s) := by
  -- Unpack the safety conditions
  rw [pettaRuleSafe_iff] at hsafe
  obtain ⟨hmt_l, hmt_r, hmc⟩ := hsafe
  -- matchPattern_correct: the algorithmic match is a left-inverse of applyBindings
  have hbs_lhs : applyBindings bs r.left = p :=
    matchPattern_correct hm hmc
  -- r's clause is in the LP KB (rules are preserved by pettaSpaceToLangDef)
  have hr_mem : r ∈ (pettaSpaceToLangDef s).rewrites := hr
  -- Apply the LP completeness theorem
  exact lp_complete_topRule r hr_mem hprem hmt_l hmt_r bs hbs_lhs hq

/-! ## PeTTaEval Corollary -/

/-- **Corollary**: if `PeTTaEval s p [q]` is witnessed by a `ruleApp` step and
    the rule is LP-safe, then `encodeReduces p q ∈ leastHerbrandModel`. -/
theorem petta_eval_lp_sound_ruleApp (s : PeTTaSpace) (p q : Pattern)
    (_heval : PeTTaEval s p [q])
    (hruleApp : ∃ r bs,
        r ∈ s.rules ∧
        r.premises = [] ∧
        bs ∈ matchPattern r.left p ∧
        applyBindings bs r.right = q ∧
        pettaRuleSafe r = true) :
    encodeReduces p q ∈ leastHerbrandModel (pettaSpaceToLPKB s) := by
  obtain ⟨r, bs, hr, hprem, hm, hq, hsafe⟩ := hruleApp
  exact petta_ruleApp_lp_sound s r bs p q hr hprem hm hq hsafe

/-! ## Fragment Soundness Theorem

    For PeTTa spaces where **all** rules are LP-safe, every ruleApp derivation
    is witnessed in the LP least model. -/

/-- A `PeTTaSpace` is **LP-safe** if all its rules are `pettaRuleSafe`. -/
def isLPSafe (s : PeTTaSpace) : Prop :=
  ∀ r ∈ s.rules, pettaRuleSafe r = true

/-- For a LP-safe space, any `ruleApp` derivation lies in the least LP model. -/
theorem petta_safe_space_ruleApp_lp_sound (s : PeTTaSpace) (hs : isLPSafe s)
    (r : RewriteRule) (bs : Bindings) (p q : Pattern)
    (hr    : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm    : bs ∈ matchPattern r.left p)
    (hq    : applyBindings bs r.right = q) :
    encodeReduces p q ∈ leastHerbrandModel (pettaSpaceToLPKB s) :=
  petta_ruleApp_lp_sound s r bs p q hr hprem hm hq (hs r hr)

/-! ## Structural Properties -/

/-- `T_P_LP` is monotone w.r.t. the KB: adding rules can only add derivations.
    Formally: for any interpretation `I`,
    `T_P_LP (pettaSpaceToLPKB s) I ⊆ T_P_LP (pettaSpaceToLPKB (s.addRule r)) I`. -/
private theorem T_P_LP_subset_addRule (s : PeTTaSpace) (r : RewriteRule) (I : Set (GroundAtom mettailLPSig)) :
    T_P_LP (pettaSpaceToLPKB s) I ⊆ T_P_LP (pettaSpaceToLPKB (s.addRule r)) I := by
  intro a ha
  simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq] at ha ⊢
  rcases ha with hdb | ⟨c, g, hc, hhead, hbody⟩
  · exact Or.inl hdb
  · refine Or.inr ⟨c, g, ?_, hhead, hbody⟩
    simp only [pettaSpaceToLPKB, pettaSpaceToLangDef, languageDefToLPKB,
               PeTTaSpace.addRule] at hc ⊢
    exact List.mem_cons_of_mem _ hc

/-- Adding a rule to a space preserves LP model membership (the model only grows). -/
theorem pettaSpaceToLPKB_addRule_mono (s : PeTTaSpace) (r : RewriteRule)
    (a : GroundAtom mettailLPSig)
    (h : a ∈ leastHerbrandModel (pettaSpaceToLPKB s)) :
    a ∈ leastHerbrandModel (pettaSpaceToLPKB (s.addRule r)) := by
  -- leastHerbrandModel new is a pre-fixpoint of T_P_LP old, so leastHerbrandModel old ⊆ new
  have hpre : T_P_LP (pettaSpaceToLPKB s) (leastHerbrandModel (pettaSpaceToLPKB (s.addRule r))) ⊆
      leastHerbrandModel (pettaSpaceToLPKB (s.addRule r)) := by
    intro x hx
    have h1 := T_P_LP_subset_addRule s r (leastHerbrandModel (pettaSpaceToLPKB (s.addRule r))) hx
    rwa [leastHerbrandModel_fixpoint] at h1
  exact leastHerbrandModel_least (pettaSpaceToLPKB s) _ hpre h

/-! ## Sanity Check: empty space has empty LP model -/

/-- The empty PeTTaSpace compiles to the empty LP KB. -/
theorem pettaSpaceToLPKB_empty :
    pettaSpaceToLPKB PeTTaSpace.empty =
    { prog := [], db := ∅ } := by
  simp [pettaSpaceToLPKB, pettaSpaceToLangDef, languageDefToLPKB, PeTTaSpace.empty,
        congruenceClauses]

/-! ## Summary

**0 sorries. 0 axioms.**

### Compilation
- `pettaSpaceToLangDef` — `PeTTaSpace → LanguageDef` (rules only; no EDB)
- `pettaSpaceToLPKB` — `PeTTaSpace → KnowledgeBase mettailLPSig`

### Fragment Predicate
- `pettaRuleSafe` — morkTranslatable both sides + isMatchCorrect LHS
- `pettaRuleSafe_iff` — component unpacking lemma
- `PeTTaSpace.isLPSafe` — all rules are LP-safe

### Main Soundness Theorem
- `petta_ruleApp_lp_sound` — `ruleApp` data + `pettaRuleSafe` →
  `encodeReduces p q ∈ leastHerbrandModel (pettaSpaceToLPKB s)`

### Corollaries
- `petta_eval_lp_sound_ruleApp` — version using `PeTTaEval` proof directly
- `petta_safe_space_ruleApp_lp_sound` — LP-safe space variant (no per-rule safety condition)

### Structural Properties
- `pettaSpaceToLPKB_addRule_mono` — adding rules preserves LP model membership
- `pettaSpaceToLPKB_empty` — empty space → empty KB

### Proof Chain
```
matchPattern_correct (MatchSpec)
  ↓
lp_complete_topRule (MeTTaILBridge)
  ↓
petta_ruleApp_lp_sound (this file)
```
-/

end Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
