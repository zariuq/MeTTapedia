import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.FunctionFree
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Ground PeTTa ↔ Datalog (Function-Free LP) Bridge

Bridges **fully-ground PeTTa programs** (no free variables, no collection rest
variables, no explicit substitution nodes) to function-free LP (Datalog) semantics.

## Core Insight

When every rule in a `PeTTaSpace` is fully ground (`isFullyGround` on both sides),
evaluation degenerates to pure EDB lookup:

1. `matchPattern r.left p` for `isFullyGround r.left` can only succeed when `p = r.left`,
   producing empty bindings `[]`.
2. `applyBindings [] r.right = r.right` when `isFullyGround r.right`.
3. So `ruleApp` reduces to: "is there a ground rule `(= p q)` in the space?"

## LP Encoding

We use a **function-free LP signature** `pettaFFSig`:
- Constants: `Pattern` (patterns are ground constants)
- Functions: `Empty` (no function symbols — Datalog territory)
- Relations: `Unit` (a single binary predicate `reduces`)

The compiled KB has `prog = []` (empty program) and an EDB of ground reduction facts.
The least Herbrand model of an empty-program KB equals the EDB exactly.

## Fragment: `isFullyGround`

`isFullyGround p` holds when `p` has:
- No `.fvar` (no metavariables — bindings cannot change `p`)
- No `.subst` (explicit substitution nodes — `applyBindings` evaluates them)
- No `.collection` (multiset matching is non-deterministic; excluded for unique match)

Under `isFullyGround`:
- `applyBindings bs p = p` for any `bs`
- `matchPattern p q` is non-empty iff `q = p`, and the only match is `[]`

## Key Results

1. `leastHerbrandModel_empty_prog` — empty program → LHM = EDB
2. `applyBindings_fully_ground` — `applyBindings bs p = p` when `isFullyGround p`
3. `matchPattern_ground_self` — `[] ∈ matchPattern p p` when `isFullyGround p`
4. `matchPattern_ground_unique` — `bs ∈ matchPattern pat q` + `isFullyGround pat` → `q = pat ∧ bs = []`
5. `pettaEval_ground_iff_lhm` — main biconditional in ruleApp form

## Relation to `LPSoundness.lean`

`LPSoundness.lean` handles the general (non-ground) case via `matchPattern_correct`
and `lp_complete_topRule`. This file handles the degenerate ground case directly,
establishing the stronger `q = r.left` uniqueness and showing LHM = EDB.

## References

- van Emden & Kowalski, "Semantics of predicate logic as a programming language", 1976
- Lloyd, *Foundations of Logic Programming*, Ch. 2 (Datalog special case)
-/

namespace Mettapedia.Logic.LP.FunctionFreePeTTa

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Logic.LP

/-! ## Section 1: LP Signature -/

/-- The function-free LP signature for ground PeTTa reduction facts.
    - `constants = Pattern`: each pattern is a ground constant.
    - `functionSymbols = Empty`: no function symbols (Datalog territory).
    - `relationSymbols = Unit`: single binary predicate `reduces(·,·)`.
    - `relationArity () = 2`. -/
abbrev pettaFFSig : LPSignature where
  constants       := Pattern
  vars            := Empty
  relationSymbols := Unit
  relationArity   := fun _ => 2
  functionSymbols := Empty
  functionArity   := Empty.elim

instance : IsEmpty pettaFFSig.functionSymbols := inferInstance

/-! ## Section 2: Encoding -/

/-- Encode a PeTTa reduction pair `(p, q)` as the ground atom `reduces(p, q)`. -/
def encodeReducesFF (p q : Pattern) : GroundAtom pettaFFSig :=
  GroundAtom.ofFinArgs () (fun i : Fin 2 =>
    if i = ⟨0, by omega⟩ then p else q)

/-- Non-dependent argument accessor for `pettaFFSig` atoms.
    Since `pettaFFSig.relationArity` is `fun _ => 2` (definitionally), no cast is needed. -/
private def pettaArg (ga : GroundAtom pettaFFSig) (i : Fin 2) : GroundTerm pettaFFSig :=
  ga.args (i.cast rfl)

/-- `encodeReducesFF` is injective in both arguments. -/
theorem encodeReducesFF_inj {p q p' q' : Pattern}
    (h : encodeReducesFF p q = encodeReducesFF p' q') : p = p' ∧ q = q' := by
  -- `pettaArg` is non-dependent so `congrArg` applies cleanly.
  have h0 := congrArg (pettaArg · ⟨0, by decide⟩) h
  have h1 := congrArg (pettaArg · ⟨1, by decide⟩) h
  simp only [pettaArg, encodeReducesFF, GroundAtom.ofFinArgs, Fin.cast_mk,
             show (⟨0, by decide⟩ : Fin 2) = ⟨0, by decide⟩ from rfl, ↓reduceIte,
             show (⟨1, by decide⟩ : Fin 2) ≠ ⟨0, by decide⟩ from by decide] at h0 h1
  exact ⟨GroundTerm.const.inj h0, GroundTerm.const.inj h1⟩

/-! ## Section 3: Fully-Ground Fragment -/

/-- `isFullyGround p` characterizes patterns for which `matchPattern p·` is
    determinate and `applyBindings bs p = p` for any `bs`:
    - No `.fvar` nodes (bindings would change them)
    - No `.subst` nodes (`applyBindings` evaluates them via `openBVar`)
    - No `.collection` nodes (multiset matching `matchBag` is non-deterministic)

    The last restriction (no collection) is necessary for `matchPattern_ground_unique`. -/
def isFullyGround : Pattern → Prop
  | .bvar _           => True
  | .fvar _           => False
  | .apply _ args     => ∀ a ∈ args, isFullyGround a
  | .lambda body      => isFullyGround body
  | .multiLambda _ b  => isFullyGround b
  | .subst _ _        => False
  | .collection _ _ _ => False

private theorem isFullyGround_apply_iff {c args} :
    isFullyGround (.apply c args) ↔ ∀ a ∈ args, isFullyGround a := by
  simp [isFullyGround]

private theorem isFullyGround_lambda_iff {body} :
    isFullyGround (.lambda body) ↔ isFullyGround body := by
  simp [isFullyGround]

private theorem isFullyGround_multiLambda_iff {n body} :
    isFullyGround (.multiLambda n body) ↔ isFullyGround body := by
  simp [isFullyGround]

/-! ## Section 4: `applyBindings` is Identity on Fully-Ground Patterns -/

private theorem list_map_eq_self {α : Type*} {f : α → α} {l : List α}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons]
    rw [h a List.mem_cons_self]
    congr 1
    exact ih (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- `applyBindings bs p = p` for any binding set `bs` when `isFullyGround p`. -/
theorem applyBindings_fully_ground (bs : Bindings) (p : Pattern)
    (hg : isFullyGround p) : applyBindings bs p = p := by
  induction p using Pattern.inductionOn generalizing bs with
  | hbvar _ => simp [applyBindings]
  | hfvar _ => exact absurd hg (by simp [isFullyGround])
  | happly c args ih =>
    have hg' := isFullyGround_apply_iff.mp hg
    simp only [applyBindings]
    congr 1
    apply list_map_eq_self
    intro a ha
    exact ih a ha bs (hg' a ha)
  | hlambda body ih =>
    have hg' := isFullyGround_lambda_iff.mp hg
    simp only [applyBindings]
    exact congrArg Pattern.lambda (ih bs hg')
  | hmultiLambda n body ih =>
    have hg' := isFullyGround_multiLambda_iff.mp hg
    simp only [applyBindings]
    exact congrArg (Pattern.multiLambda n) (ih bs hg')
  | hsubst _ _ _ _ => exact absurd hg (by simp [isFullyGround])
  | hcollection _ _ _ _ => exact absurd hg (by simp [isFullyGround])

/-! ## Section 5: Datalog-Safe Predicate -/

/-- A `PeTTaSpace` is **Datalog-safe** if every rule is premise-free and
    both its LHS and RHS are fully ground. -/
def isDatalogSafe (s : PeTTaSpace) : Prop :=
  ∀ r ∈ s.rules, r.premises = [] ∧ isFullyGround r.left ∧ isFullyGround r.right

/-! ## Section 6: KB Compilation -/

/-- Compile a Datalog-safe `PeTTaSpace` to a function-free LP KB.
    The program is empty because all derivations reduce to EDB lookups. -/
noncomputable def pettaSpaceToFFKB (s : PeTTaSpace) : KnowledgeBase pettaFFSig where
  prog := []
  db   := { a | ∃ r ∈ s.rules, r.premises = [] ∧ a = encodeReducesFF r.left r.right }

/-! ## Section 7: Empty-Program LHM = EDB -/

/-- When `kb.prog = []`, `T_P_LP kb I = kb.db` for any interpretation `I`. -/
theorem T_P_LP_empty_prog {σ : LPSignature} (kb : KnowledgeBase σ)
    (hprog : kb.prog = []) (I : Interpretation σ) : T_P_LP kb I = kb.db := by
  simp only [T_P_LP, Set.ext_iff, Set.mem_union, Set.mem_setOf_eq]
  intro a
  constructor
  · rintro (ha | ⟨c, _g, hc, _⟩)
    · exact ha
    · simp [hprog] at hc
  · exact Or.inl

/-- For a KB with empty program, the least Herbrand model equals the EDB. -/
theorem leastHerbrandModel_empty_prog {σ : LPSignature} (kb : KnowledgeBase σ)
    (h : kb.prog = []) : leastHerbrandModel kb = kb.db := by
  apply Set.eq_of_subset_of_subset
  · apply leastHerbrandModel_least
    rw [T_P_LP_empty_prog kb h]
  · intro a ha; exact leastHerbrandModel_db kb a ha

/-! ## Section 8: EDB Membership Characterization -/

/-- LHM membership iff a matching unconditional rule exists in the space. -/
theorem encodeReducesFF_mem_lhm_iff (s : PeTTaSpace) (p q : Pattern) :
    encodeReducesFF p q ∈ leastHerbrandModel (pettaSpaceToFFKB s) ↔
    ∃ r ∈ s.rules, r.premises = [] ∧ r.left = p ∧ r.right = q := by
  rw [leastHerbrandModel_empty_prog (pettaSpaceToFFKB s) rfl]
  simp only [pettaSpaceToFFKB, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, hprem, henc⟩
    obtain ⟨hleft, hright⟩ := encodeReducesFF_inj henc
    exact ⟨r, hr, hprem, hleft.symm, hright.symm⟩
  · rintro ⟨r, hr, hprem, rfl, rfl⟩
    exact ⟨r, hr, hprem, rfl⟩

/-! ## Section 9: Ground Pattern Matching -/

-- Joint proof by strong induction on `sizeOf pat` (and `sizeOf pats` for lists).
-- `matchPattern_ground_self` needs `matchArgs_ground_self`, and vice versa.
-- `matchPattern_ground_unique` needs `matchArgs_ground_unique`, and vice versa.

private theorem sizeOf_args_lt_apply (c : String) (args : List Pattern) :
    sizeOf args < sizeOf (Pattern.apply c args) := by simp_wf

private theorem sizeOf_body_lt_lambda (body : Pattern) :
    sizeOf body < sizeOf (Pattern.lambda body) := by simp_wf

private theorem sizeOf_body_lt_multiLambda (n : Nat) (body : Pattern) :
    sizeOf body < sizeOf (Pattern.multiLambda n body) := by simp_wf

private theorem sizeOf_pattern_pos (p : Pattern) : 0 < sizeOf p := by
  cases p <;> simp [sizeOf, Pattern._sizeOf_1]

private theorem sizeOf_head_lt_cons (p : Pattern) (ps : List Pattern) :
    sizeOf p < sizeOf (p :: ps) := by simp_wf; omega

private theorem sizeOf_tail_lt_cons (p : Pattern) (ps : List Pattern) :
    sizeOf ps < sizeOf (p :: ps) := by simp_wf

/-- Joint self-match and uniqueness for `matchPattern`/`matchArgs` on ground patterns.
    Proved by strong induction on a size bound. -/
private theorem ground_match_joint (n : Nat) :
    (∀ (p : Pattern), sizeOf p ≤ n → isFullyGround p →
      ([] : Bindings) ∈ matchPattern p p) ∧
    (∀ (pats : List Pattern), sizeOf pats ≤ n → (∀ a ∈ pats, isFullyGround a) →
      ([] : Bindings) ∈ matchArgs pats pats) ∧
    (∀ (p q : Pattern) (bs : Bindings), sizeOf p ≤ n →
      isFullyGround p → bs ∈ matchPattern p q → q = p ∧ bs = []) ∧
    (∀ (pats qs : List Pattern) (bs : Bindings), sizeOf pats ≤ n →
      (∀ a ∈ pats, isFullyGround a) → bs ∈ matchArgs pats qs → qs = pats ∧ bs = []) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hle _; exact absurd hle (by have := sizeOf_pattern_pos p; omega)
    · intro pats hle hpats
      cases pats with
      | nil => simp [matchArgs]
      | cons _ _ => exact absurd hle (by simp [sizeOf, List._sizeOf_1])
    · intro p _ _ hle _; exact absurd hle (by have := sizeOf_pattern_pos p; omega)
    · intro pats qs bs hle hpats hm
      cases pats with
      | nil => cases qs with
        | nil => simp only [matchArgs, List.mem_cons, List.mem_nil_iff, or_false] at hm; exact ⟨rfl, hm⟩
        | cons h t => simp [matchArgs] at hm
      | cons _ _ => exact absurd hle (by simp [sizeOf, List._sizeOf_1])
  | succ m ih =>
    obtain ⟨ih_self_pat, ih_self_args, ih_uniq_pat, ih_uniq_args⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Self-match for patterns
      intro p hle hg
      cases p with
      | bvar n => simp [matchPattern]
      | fvar _ => exact absurd hg (by simp [isFullyGround])
      | apply c args =>
        have hg' := isFullyGround_apply_iff.mp hg
        simp only [matchPattern, beq_self_eq_true, Bool.true_and, ↓reduceIte]
        exact ih_self_args args (by have := sizeOf_args_lt_apply c args; omega) hg'
      | lambda body =>
        simp only [matchPattern]
        exact ih_self_pat body (by have := sizeOf_body_lt_lambda body; omega)
          (isFullyGround_lambda_iff.mp hg)
      | multiLambda n body =>
        simp only [matchPattern, beq_self_eq_true, ↓reduceIte]
        exact ih_self_pat body (by have := sizeOf_body_lt_multiLambda n body; omega)
          (isFullyGround_multiLambda_iff.mp hg)
      | subst _ _ => exact absurd hg (by simp [isFullyGround])
      | collection _ _ _ => exact absurd hg (by simp [isFullyGround])
    · -- Self-match for matchArgs
      intro pats hle hpats
      cases pats with
      | nil => simp [matchArgs]
      | cons a rest =>
        simp only [matchArgs, List.mem_flatMap, List.mem_filterMap]
        exact ⟨[], ih_self_pat a (by have := sizeOf_head_lt_cons a rest; omega)
                    (hpats a List.mem_cons_self),
               [], ih_self_args rest (by have := sizeOf_tail_lt_cons a rest; omega)
                    (fun b hb => hpats b (List.mem_cons_of_mem a hb)), rfl⟩
    · -- Uniqueness for matchPattern
      intro p q bs hle hg hm
      cases p with
      | bvar n =>
        cases q with
        | bvar mv =>
          simp only [matchPattern] at hm
          split at hm
          · next heq =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
            subst hm; exact ⟨by rw [beq_iff_eq.mp heq], rfl⟩
          · simp at hm
        | _ => simp [matchPattern] at hm
      | fvar _ => exact absurd hg (by simp [isFullyGround])
      | apply c args =>
        have hg' := isFullyGround_apply_iff.mp hg
        cases q with
        | apply c2 qs =>
          simp only [matchPattern] at hm
          split at hm
          · next hcond =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨hceq, _⟩ := hcond
            obtain ⟨rfl, rfl⟩ := ih_uniq_args args qs bs
              (by have := sizeOf_args_lt_apply c args; omega) hg' hm
            exact ⟨by rw [hceq], rfl⟩
          · simp at hm
        | _ => simp [matchPattern] at hm
      | lambda body =>
        have hg' := isFullyGround_lambda_iff.mp hg
        cases q with
        | lambda q' =>
          simp only [matchPattern] at hm
          obtain ⟨heq, hbs⟩ := ih_uniq_pat body q' bs
            (by have := sizeOf_body_lt_lambda body; omega) hg' hm
          exact ⟨by rw [heq], hbs⟩
        | _ => simp [matchPattern] at hm
      | multiLambda n body =>
        have hg' := isFullyGround_multiLambda_iff.mp hg
        cases q with
        | multiLambda m' q' =>
          simp only [matchPattern] at hm
          split at hm
          · next hneq =>
            obtain ⟨heq, hbs⟩ := ih_uniq_pat body q' bs
              (by have := sizeOf_body_lt_multiLambda n body; omega) hg' hm
            exact ⟨by rw [heq, beq_iff_eq.mp hneq], hbs⟩
          · simp at hm
        | _ => simp [matchPattern] at hm
      | subst _ _ => exact absurd hg (by simp [isFullyGround])
      | collection _ _ _ => exact absurd hg (by simp [isFullyGround])
    · -- Uniqueness for matchArgs
      intro pats qs bs hle hpats hm
      cases pats with
      | nil =>
        cases qs with
        | nil =>
          simp only [matchArgs, List.mem_cons, List.mem_nil_iff, or_false] at hm
          exact ⟨rfl, hm⟩
        | cons h t => simp [matchArgs] at hm
      | cons ahead atail =>
        cases qs with
        | nil => simp [matchArgs] at hm
        | cons q' qs' =>
          simp only [matchArgs, List.mem_flatMap, List.mem_filterMap] at hm
          obtain ⟨bh, hbh, bt, hbt, hmrg⟩ := hm
          have hheadsz : sizeOf ahead ≤ m := by
            have := sizeOf_head_lt_cons ahead atail; omega
          have htailsz : sizeOf atail ≤ m := by
            have := sizeOf_tail_lt_cons ahead atail; omega
          have hhead_g : isFullyGround ahead := hpats ahead List.mem_cons_self
          have htail_g : ∀ a' ∈ atail, isFullyGround a' :=
            fun a' ha' => hpats a' (List.mem_cons_of_mem ahead ha')
          obtain ⟨hq'eq, hbheq⟩ := ih_uniq_pat ahead q' bh hheadsz hhead_g hbh
          obtain ⟨hqs, hbt'⟩ := ih_uniq_args atail qs' bt htailsz htail_g hbt
          subst hq'eq; subst hbheq; subst hqs; subst hbt'
          simp only [mergeBindings, List.foldlM] at hmrg
          exact ⟨rfl, (Option.some.inj hmrg.symm)⟩

/-- A fully-ground pattern matches itself with the empty binding set. -/
theorem matchPattern_ground_self (p : Pattern) (hg : isFullyGround p) :
    ([] : Bindings) ∈ matchPattern p p :=
  (ground_match_joint (sizeOf p)).1 p (le_refl _) hg

/-- For fully-ground patterns, matching is unique: the match forces `q = pat`
    and the only possible binding is `[]`. -/
theorem matchPattern_ground_unique {pat q : Pattern} {bs : Bindings}
    (hg : isFullyGround pat)
    (hm : bs ∈ matchPattern pat q) : q = pat ∧ bs = [] :=
  (ground_match_joint (sizeOf pat)).2.2.1 pat q bs (le_refl _) hg hm

/-! ## Section 10: Main Bridge Theorems -/

/-- **Sound direction**: a ruleApp derivation in a Datalog-safe space
    is witnessed in the least Herbrand model of the compiled KB. -/
theorem pettaEval_ruleApp_sound (s : PeTTaSpace) (hs : isDatalogSafe s)
    (r : RewriteRule) (bs : Bindings) (p q : Pattern)
    (hr    : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm    : bs ∈ matchPattern r.left p)
    (hq    : applyBindings bs r.right = q) :
    encodeReducesFF p q ∈ leastHerbrandModel (pettaSpaceToFFKB s) := by
  obtain ⟨_, hfl, hfr⟩ := hs r hr
  obtain ⟨rfl, rfl⟩ := matchPattern_ground_unique hfl hm
  rw [applyBindings_fully_ground [] r.right hfr] at hq
  rw [← hq, encodeReducesFF_mem_lhm_iff]
  exact ⟨r, hr, hprem, rfl, rfl⟩

/-- **Complete direction**: LHM membership + Datalog-safety implies `PeTTaEval`. -/
theorem pettaEval_ruleApp_complete' (s : PeTTaSpace) (hs : isDatalogSafe s)
    (p q : Pattern)
    (h : encodeReducesFF p q ∈ leastHerbrandModel (pettaSpaceToFFKB s)) :
    PeTTaEval s p [q] := by
  rw [encodeReducesFF_mem_lhm_iff] at h
  obtain ⟨r, hr, hprem, rfl, rfl⟩ := h
  obtain ⟨_, hfl, hfr⟩ := hs r hr
  exact PeTTaEval.ruleApp r [] r.left r.right hr hprem
    (matchPattern_ground_self r.left hfl)
    (applyBindings_fully_ground [] r.right hfr)

/-- **Main biconditional** (ruleApp form): for a Datalog-safe space,
    `PeTTaEval` via `ruleApp` is equivalent to membership in the least Herbrand model. -/
theorem pettaEval_ground_iff_lhm (s : PeTTaSpace) (hs : isDatalogSafe s) (p q : Pattern) :
    (∃ (r : RewriteRule) (bs : Bindings),
        r ∈ s.rules ∧ r.premises = [] ∧
        bs ∈ matchPattern r.left p ∧
        applyBindings bs r.right = q) ↔
    encodeReducesFF p q ∈ leastHerbrandModel (pettaSpaceToFFKB s) := by
  constructor
  · rintro ⟨r, bs, hr, hprem, hm, hq⟩
    exact pettaEval_ruleApp_sound s hs r bs p q hr hprem hm hq
  · intro h
    rw [encodeReducesFF_mem_lhm_iff] at h
    obtain ⟨r, hr, hprem, rfl, rfl⟩ := h
    obtain ⟨_, hfl, hfr⟩ := hs r hr
    exact ⟨r, [], hr, hprem,
           matchPattern_ground_self r.left hfl,
           applyBindings_fully_ground [] r.right hfr⟩

/-! ## Summary

**0 sorries. 0 axioms beyond kernel.**

### Signature and Encoding
- `pettaFFSig` — function-free LP signature with `constants = Pattern`
- `encodeReducesFF` — encode `(p, q)` as a binary ground atom
- `encodeReducesFF_inj` — injectivity

### Ground Fragment
- `isFullyGround` — no `.fvar`, no `.subst`, no `.collection`
- `applyBindings_fully_ground` — `applyBindings bs p = p`

### Datalog-Safe Predicate
- `isDatalogSafe` — all rules ground and premise-free

### LP Compilation
- `pettaSpaceToFFKB` — compile to KB with `prog = []`
- `T_P_LP_empty_prog` — T_P with empty program equals EDB
- `leastHerbrandModel_empty_prog` — LHM = EDB
- `encodeReducesFF_mem_lhm_iff` — LHM membership ↔ rule existence

### Matching Lemmas
- `matchPattern_ground_self` — self-match for fully-ground patterns
- `matchPattern_ground_unique` — ground LHS match forces `q = pat` and `bs = []`

### Bridge Theorems
- `pettaEval_ruleApp_sound` — ruleApp derivation → LHM membership
- `pettaEval_ruleApp_complete'` — LHM membership + Datalog-safety → PeTTaEval
- `pettaEval_ground_iff_lhm` — main biconditional in ruleApp form
-/

end Mettapedia.Logic.LP.FunctionFreePeTTa
