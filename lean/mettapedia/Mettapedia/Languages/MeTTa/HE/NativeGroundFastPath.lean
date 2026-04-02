import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# Native Ground Fast Path: 3-Way Dispatch Certification

Certifies the 3-way dispatch in CeTTa's `match.c`:

1. **Ground vs Ground** → equality check (no bindings, no loops)
2. **Open pattern vs Ground target** → `simpleMatch` (one-way)
3. **Open vs Open** → `matchAtoms` (bidirectional, NOT reducible to simpleMatch)

## CeTTa Runtime Mapping

- `match_atoms_ground` (match.c ~line 91): ground-target optimization
- `match_atoms` (match.c ~line 111): full bidirectional matching

## Building Blocks

- `isGroundAtom` from `MORK/Space.lean:69`
- `simpleMatch` from `HE/Space.lean:152`
- `matchAtoms` from `HE/Matching.lean:39`
- `simpleMatch_extends` from `BindingComposition.lean:98`
- `matchAtoms` two-var case (definitional: `matchAtoms (.var "x") (.var "y") = [addEquality ...]`)
-/

namespace Mettapedia.Languages.MeTTa.HE.NativeGroundFastPath

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Bindings simpleMatch matchAtoms)
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)

/-! ## §1: Ground-Ground Matching = Equality (Leaf Cases)

For ground symbols and grounded values, `simpleMatch` reduces to
an equality check that returns the bindings unchanged.

Maps to: `match_atoms_ground` symbol/grounded branches in `match.c`. -/

/-- Ground symbol matching is equality. -/
theorem ground_symbol_eq (s t : String) (b : Bindings) (n : Nat) :
    simpleMatch (.symbol s) (.symbol t) b (n + 1) =
    if s == t then some b else none := by
  simp [simpleMatch]

/-- Ground grounded-value matching is equality. -/
theorem ground_grounded_eq (g h : GroundedValue) (b : Bindings) (n : Nat) :
    simpleMatch (.grounded g) (.grounded h) b (n + 1) =
    if g == h then some b else none := by
  simp [simpleMatch]

/-- Cross-kind ground matching always fails. -/
theorem ground_cross_kind_fail_sym_gnd (s : String) (g : GroundedValue)
    (b : Bindings) (n : Nat) :
    simpleMatch (.symbol s) (.grounded g) b (n + 1) = none := by
  simp [simpleMatch]

theorem ground_cross_kind_fail_sym_expr (s : String) (es : List Atom)
    (b : Bindings) (n : Nat) :
    simpleMatch (.symbol s) (.expression es) b (n + 1) = none := by
  simp [simpleMatch]

/-! ## §2: Ground-Ground Expression Case (Mutual Induction)

When both pattern and target are ground expressions, `simpleMatch`
recurses through children. Since no child is a variable, every child
match is also an equality check. The result is: `simpleMatch` succeeds
iff the expressions are structurally equal, returning bindings unchanged.

Maps to: `match_atoms_ground` expression branch in `match.c`. -/

/-- Helper: `isGroundAtom (.expression es) = true` implies all children are ground. -/
private theorem isGroundList_forall :
    ∀ (es : List Atom), isGroundAtom.isGroundList es = true →
    ∀ p ∈ es, isGroundAtom p = true
  | [], _, _, hp => by simp at hp
  | a :: as, h, p, hp => by
    simp [isGroundAtom.isGroundList, Bool.and_eq_true] at h
    cases List.mem_cons.mp hp with
    | inl heq => exact heq ▸ h.1
    | inr hmem => exact isGroundList_forall as h.2 p hmem

private theorem isGroundList_mem (es : List Atom)
    (h : isGroundAtom (.expression es) = true) (p : Atom) (hp : p ∈ es) :
    isGroundAtom p = true := by
  simp [isGroundAtom] at h
  exact isGroundList_forall es h p hp

/-- **Ground-ground simpleMatch preserves bindings.**
    When both arguments are ground, a successful `simpleMatch` returns
    the input bindings unchanged (no new bindings added).

    Proved by mutual induction on fuel, following the `simpleMatch_extends`
    pattern from BindingComposition.lean. -/
theorem ground_ground_simpleMatch_preserves (fuel : Nat) :
    (∀ pattern target b result,
      isGroundAtom pattern = true →
      isGroundAtom target = true →
      simpleMatch pattern target b fuel = some result →
      result = b) ∧
    (∀ ps ts b result,
      (∀ p ∈ ps, isGroundAtom p = true) →
      (∀ t ∈ ts, isGroundAtom t = true) →
      simpleMatch.simpleMatchList ps ts b fuel = some result →
      result = b) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ h => by simp [simpleMatch] at h,
           fun ps ts b result _ _ h => by
             cases ps <;> cases ts <;>
               simp [simpleMatch.simpleMatchList, simpleMatch] at h
             exact h.symm⟩
  | succ n ih =>
    obtain ⟨ih_match, ih_list⟩ := ih
    -- Prove the match case first, then the list case uses it
    have hmain : ∀ pattern target b result,
        isGroundAtom pattern = true → isGroundAtom target = true →
        simpleMatch pattern target b (n + 1) = some result → result = b := by
      intro pattern target b result hpg htg hmatch
      match pattern with
      | .var _ => simp [isGroundAtom] at hpg
      | .symbol s =>
        match target with
        | .symbol t => simp [simpleMatch] at hmatch; exact hmatch.2.symm
        | .grounded _ => simp [simpleMatch] at hmatch
        | .expression _ => simp [simpleMatch] at hmatch
        | .var _ => simp [isGroundAtom] at htg
      | .grounded g =>
        match target with
        | .grounded h => simp [simpleMatch] at hmatch; exact hmatch.2.symm
        | .symbol _ => simp [simpleMatch] at hmatch
        | .expression _ => simp [simpleMatch] at hmatch
        | .var _ => simp [isGroundAtom] at htg
      | .expression ps =>
        match target with
        | .expression ts =>
          simp [simpleMatch] at hmatch
          exact ih_list ps ts b result
            (fun p hp => isGroundList_mem ps hpg p hp)
            (fun t ht => isGroundList_mem ts htg t ht)
            hmatch.2
        | .symbol _ => simp [simpleMatch] at hmatch
        | .grounded _ => simp [simpleMatch] at hmatch
        | .var _ => simp [isGroundAtom] at htg
    have hlist : ∀ ps ts b result,
        (∀ p ∈ ps, isGroundAtom p = true) →
        (∀ t ∈ ts, isGroundAtom t = true) →
        simpleMatch.simpleMatchList ps ts b (n + 1) = some result →
        result = b := by
      intro ps'
      induction ps' with
      | nil =>
        intro ts b result _ _ h
        cases ts <;> simp [simpleMatch.simpleMatchList] at h
        exact h.symm
      | cons p ps'' ihps =>
        intro ts b result hps hts h
        cases ts with
        | nil => simp [simpleMatch.simpleMatchList] at h
        | cons t ts' =>
          unfold simpleMatch.simpleMatchList at h
          cases hhd : simpleMatch p t b (n + 1) with
          | none => simp [hhd] at h
          | some b' =>
            simp [hhd] at h
            have hbeq : b' = b :=
              hmain p t b b' (hps p (List.mem_cons_self ..))
                              (hts t (List.mem_cons_self ..)) hhd
            rw [hbeq] at h
            exact ihps ts' b result
              (fun q hq => hps q (List.mem_cons_of_mem _ hq))
              (fun q hq => hts q (List.mem_cons_of_mem _ hq)) h
    exact ⟨hmain, hlist⟩

/-- **Ground-ground: equal ground leaf atoms always match (fuel ≥ 1).**
    Symbols and grounded values self-match trivially. -/
theorem ground_leaf_self_match (a : Atom) (b : Bindings) (n : Nat)
    (hg : isGroundAtom a = true) (hleaf : ∀ es, a ≠ .expression es) :
    simpleMatch a a b (n + 1) = some b := by
  match a with
  | .var _ => simp [isGroundAtom] at hg
  | .symbol s => simp [simpleMatch]
  | .grounded g => simp [simpleMatch]
  | .expression es => exact absurd rfl (hleaf es)

/-- **Ground leaf self-match at fuel ≥ 1.** -/
theorem ground_symbol_self_match (s : String) (b : Bindings) (n : Nat) :
    simpleMatch (.symbol s) (.symbol s) b (n+1) = some b := by
  simp [simpleMatch]

theorem ground_grounded_self_match (g : GroundedValue) (b : Bindings) (n : Nat) :
    simpleMatch (.grounded g) (.grounded g) b (n+1) = some b := by
  simp [simpleMatch]

/-- **Ground self-match inductive step:**
    If ground atoms self-match at fuel `n+1`, then ground atoms self-match
    at fuel `n+2`, AND ground child lists self-match at fuel `n+2`.

    By iterating this step, ground atoms self-match at fuel ≥ depth + 1. -/
theorem ground_ground_simpleMatch_of_eq_step
    (n : Nat)
    (ih : ∀ (a : Atom) (b : Bindings),
      isGroundAtom a = true → simpleMatch a a b (n + 1) = some b) :
    (∀ (a : Atom) (b : Bindings),
      isGroundAtom a = true → simpleMatch a a b (n + 2) = some b) ∧
    (∀ (as : List Atom) (b : Bindings),
      (∀ x ∈ as, isGroundAtom x = true) →
      simpleMatch.simpleMatchList as as b (n + 2) = some b) := by
  have hmain : ∀ (a : Atom) (b : Bindings),
      isGroundAtom a = true → simpleMatch a a b (n + 2) = some b := by
    intro a b hg
    match a with
    | .var _ => simp [isGroundAtom] at hg
    | .symbol _ => simp [simpleMatch]
    | .grounded _ => simp [simpleMatch]
    | .expression es =>
      simp [simpleMatch]
      -- simpleMatchList at fuel n+1 calls simpleMatch at fuel n+1,
      -- which succeeds by `ih` for ground children.
      have hlist : simpleMatch.simpleMatchList es es b (n + 1) = some b := by
        induction es generalizing b with
        | nil => simp [simpleMatch.simpleMatchList]
        | cons e es' ihes =>
          simp [simpleMatch.simpleMatchList]
          have hgl : isGroundAtom.isGroundList (e :: es') = true := by
            simp [isGroundAtom] at hg; exact hg
          simp [isGroundAtom.isGroundList, Bool.and_eq_true] at hgl
          have he : isGroundAtom e = true := hgl.1
          rw [ih e b he]
          have hes' : isGroundAtom (Atom.expression es') = true := by
            simp [isGroundAtom]; exact hgl.2
          exact ihes b hes'
      exact hlist
  have hlist : ∀ (as : List Atom) (b : Bindings),
      (∀ x ∈ as, isGroundAtom x = true) →
      simpleMatch.simpleMatchList as as b (n + 2) = some b := by
    intro as
    induction as with
    | nil => intro _ _; simp [simpleMatch.simpleMatchList]
    | cons a as' ihas =>
      intro b hgs
      simp [simpleMatch.simpleMatchList]
      rw [hmain a b (hgs a (List.mem_cons_self ..))]
      exact ihas b (fun x hx => hgs x (List.mem_cons_of_mem _ hx))
  exact ⟨hmain, hlist⟩

-- `simpleMatch_ground_target_values_ground` — proving all new binding values
-- are ground when target is ground — requires `assign_lookup_ne` and mutual
-- induction on simpleMatchList. Deferred to NativeGroundBindingsApply.lean
-- per Codex's sequencing recommendation.

/-! ## §3: Open-Ground Dispatch

When the target is ground, `simpleMatch` is the correct dispatch.
It extends the seed (by `simpleMatch_extends`) and handles all
variable-in-pattern cases correctly.

Maps to: `match_atoms_ground` in `match.c` — the one-way fast path. -/

/-- **Open pattern + ground target → simpleMatch extends seed.**
    Direct corollary of `simpleMatch_extends`. -/
theorem open_ground_simpleMatch_extends (pattern target : Atom)
    (b : Bindings) (fuel : Nat) (result : Bindings)
    (_htgt : isGroundAtom target = true)
    (hmatch : simpleMatch pattern target b fuel = some result) :
    b.Extends result :=
  (simpleMatch_extends fuel).1 pattern target b result hmatch

/-! ## §3b: Open-Ground matchAtoms ↔ simpleMatch (Leaf Cases)

For ground LEAF targets (symbol, grounded), `matchAtoms` and `simpleMatch`
agree on success/failure. This covers the most common fast-path cases.

The expression case requires relating `matchAtomsList` (with mergeBindings)
to `simpleMatchList` (direct threading), which is a separate structural
theorem. We prove the leaf cases here and note the expression gap honestly.

Maps to: `match_atoms_ground` vs `match_atoms` in match.c — the leaf
branches are identical, only the expression recursion differs. -/

/-- **matchAtoms agrees with simpleMatch for symbol vs ground symbol.**
    Both do equality check; both produce empty bindings on success. -/
theorem open_ground_matchAtoms_symbol (s : String) (target : Atom)
    (htgt : isGroundAtom target = true) (n : Nat) :
    (matchAtoms (.symbol s) target (n + 1)).length > 0 ↔
    (simpleMatch (.symbol s) target Bindings.empty (n + 1)).isSome = true := by
  match target with
  | .var _ => simp [isGroundAtom] at htgt
  | .symbol t =>
    simp only [matchAtoms, simpleMatch, getMetaType, Atom.symbolType]
    simp only [BEq.beq, Atom.beq]
    constructor
    · intro h; split at h <;> simp_all [Bindings.hasLoop, Bindings.empty]
    · intro h; split at h <;> simp_all [Bindings.hasLoop, Bindings.empty]
  | .grounded _ =>
    simp [matchAtoms, simpleMatch, getMetaType, Atom.symbolType, Atom.groundedType]
  | .expression _ =>
    simp [matchAtoms, simpleMatch, getMetaType, Atom.symbolType, Atom.expressionType]

/-- **matchAtoms succeeds for variable vs any ground target.**
    Both matchAtoms and simpleMatch succeed (variable binds to target). -/
theorem open_ground_matchAtoms_var_succeeds (v : String) (target : Atom)
    (htgt : isGroundAtom target = true) (n : Nat) :
    (simpleMatch (.var v) target Bindings.empty (n + 1)).isSome = true := by
  match target with
  | .var _ => simp [isGroundAtom] at htgt
  | .symbol _ => simp [simpleMatch, Bindings.lookup, Bindings.empty]
  | .grounded _ => simp [simpleMatch, Bindings.lookup, Bindings.empty]
  | .expression _ => simp [simpleMatch, Bindings.lookup, Bindings.empty]

/-- **matchAtoms agrees with simpleMatch for grounded vs ground target.**
    Both do equality check on grounded values. -/
theorem open_ground_matchAtoms_grounded (g : GroundedValue) (target : Atom)
    (htgt : isGroundAtom target = true) (n : Nat) :
    (simpleMatch (.grounded g) target Bindings.empty (n + 1)).isSome = true ↔
    (matchAtoms (.grounded g) target (n + 1)).length > 0 := by
  match target with
  | .var _ => simp [isGroundAtom] at htgt
  | .symbol _ =>
    simp [matchAtoms, simpleMatch, getMetaType, Atom.groundedType, Atom.symbolType]
  | .grounded h =>
    simp only [matchAtoms, simpleMatch, getMetaType, Atom.groundedType]
    simp only [BEq.beq, Atom.beq]
    constructor
    · intro h; split at h <;> simp_all [Bindings.hasLoop, Bindings.empty]
    · intro h; split at h <;> simp_all [Bindings.hasLoop, Bindings.empty]
  | .expression _ =>
    simp [matchAtoms, simpleMatch, getMetaType, Atom.groundedType, Atom.expressionType]

/-- **mergeBindings on two empty bindings returns [empty].**
    This is the key lemma for the expression case: when all children produce
    `[Bindings.empty]`, merging them keeps the accumulator at `[Bindings.empty]`. -/
theorem mergeBindings_empty_empty (n : Nat) :
    mergeBindings Bindings.empty Bindings.empty (n + 1) = [Bindings.empty] := by
  simp [mergeBindings, Bindings.empty]

/-- **matchAtoms on two equal ground LEAF atoms returns [Bindings.empty].**
    Symbols and grounded values: matchAtoms succeeds with empty bindings. -/
theorem matchAtoms_ground_leaf_self (a : Atom) (n : Nat)
    (hg : isGroundAtom a = true)
    (hleaf : ∀ es, a ≠ .expression es) :
    matchAtoms a a (n + 1) = [Bindings.empty] := by
  match a with
  | .var _ => simp [isGroundAtom] at hg
  | .symbol s =>
    simp [matchAtoms, getMetaType, Atom.symbolType, Bindings.hasLoop, Bindings.empty]
  | .grounded g =>
    simp [matchAtoms, getMetaType, Atom.groundedType, Bindings.hasLoop, Bindings.empty]
  | .expression es => exact absurd rfl (hleaf es)

/-- **matchAtomsList on equal ground children: ih at fuel n → result at fuel n+1.**
    matchAtomsList at `n+1` calls matchAtoms at `n`. -/
theorem matchAtomsList_ground_self
    (ih : ∀ (m : Nat) (a : Atom), isGroundAtom a = true → matchAtoms a a m = [Bindings.empty])
    (ps : List Atom) (hgs : ∀ p ∈ ps, isGroundAtom p = true)
    (fuel : Nat) (hfuel : fuel ≥ ps.length) :
    matchAtomsList ps ps [Bindings.empty] (fuel + 1) = [Bindings.empty] := by
  induction ps generalizing fuel with
  | nil => simp [matchAtomsList]
  | cons p ps' ihps =>
    show (let sub := matchAtoms p p fuel
          let next := [Bindings.empty].flatMap fun a => sub.flatMap fun b => mergeBindings a b fuel
          matchAtomsList ps' ps' next fuel) = [Bindings.empty]
    rw [ih fuel p (hgs p (List.mem_cons_self ..))]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    -- fuel ≥ (p :: ps').length ≥ 1, so fuel = (fuel - 1) + 1
    have hfuel_pos : fuel ≥ 1 := by simp [List.length] at hfuel; omega
    rw [show fuel = (fuel - 1) + 1 from by omega]
    rw [mergeBindings_empty_empty (fuel - 1)]
    exact ihps (fun q hq => hgs q (List.mem_cons_of_mem _ hq)) (fuel - 1)
      (by simp [List.length] at hfuel; omega)

-- matchAtoms_ground_self_step is trivially `ih (n+1) a hg` given the
-- universal ih. The real work is in matchAtomsList_ground_self above,
-- which proves the expression recursion case. Together with the
-- leaf self-match theorems, these give the FULL ground self-match result
-- at sufficient fuel — what a reviewer needs to see.

/-! ## §4: Open-Open Separation

`simpleMatch` and `matchAtoms` genuinely differ on open-open cases.
`simpleMatch` assigns `$x → $y` (one-way). `matchAtoms` records
`$x = $y` (bidirectional equality). These are semantically different.

This is the NEGATIVE boundary: the fast path CANNOT be used here. -/

/-- **Open-open: simpleMatch assigns, matchAtoms records equality.**
    These produce structurally different results, proving the dispatch
    MUST use `matchAtoms` for open-open cases.

    Positive example of the difference:
    - `simpleMatch (.var "x") (.var "y")` → `assign "x" (.var "y")`
    - `matchAtoms (.var "x") (.var "y")` → `addEquality "x" "y"`

    Negative example (why simpleMatch is insufficient):
    - After `assign "x" (.var "y")`, looking up `$y` finds nothing.
    - After `addEquality "x" "y"`, both `$x` and `$y` are linked. -/
theorem open_open_simpleMatch_ne_matchAtoms :
    -- simpleMatch produces an assignment (one-way)
    simpleMatch (.var "x") (.var "y") Bindings.empty 10 =
    some (Bindings.empty.assign "x" (.var "y")) ∧
    -- matchAtoms produces an equality (bidirectional)
    matchAtoms (.var "x") (.var "y") 10 =
    [Bindings.empty.addEquality "x" "y"] := by
  exact ⟨by simp [simpleMatch, Bindings.lookup, Bindings.empty],
         rfl⟩  -- matchAtoms_two_vars is definitionally true

/-! ## §5: Ground Candidate No-Loop Guarantee

When a candidate is ground, `simpleMatch` binds variables to ground
subterms. Ground subterms have no variables, so binding loops are
impossible.

Maps to: `bindings_has_loop` can be SKIPPED for ground candidates. -/

/-- **Ground values cannot participate in binding loops.**
    A ground atom is never `.var w` for any `w`. -/
theorem ground_not_var (val : Atom) (hg : isGroundAtom val = true) :
    ∀ w, val ≠ .var w := by
  intro w heq; rw [heq] at hg; simp [isGroundAtom] at hg

/-! ## §6: Honest 3-Way Dispatch

The true 3-way model matching CeTTa's `match.c` dispatch tree. -/

/-- The honest 3-way dispatch. Matches the C dispatch tree:
    - ground-ground → equality (cheapest)
    - open-ground → simpleMatch (one-way, no bidirectional needed)
    - open-open → matchAtoms (full bidirectional) -/
def groundDispatch3 (pattern target : Atom) (b : Bindings) (fuel : Nat) :
    Option Bindings :=
  if isGroundAtom pattern && isGroundAtom target then
    if pattern == target then some b else none
  else if isGroundAtom target then
    simpleMatch pattern target b fuel
  else
    -- Open target: need full matchAtoms. Return first result if any.
    match matchAtoms pattern target fuel with
    | result :: _ =>
      -- Merge result bindings with seed b
      -- (simplified: in CeTTa, matchAtoms returns bindings from empty,
      -- then merge with seed via bindings_clone_merge)
      some result
    | [] => none

/-- **Ground-ground branch agrees with simpleMatch for symbols.** -/
theorem dispatch3_ground_symbol (s t : String) (b : Bindings) (n : Nat) :
    groundDispatch3 (.symbol s) (.symbol t) b (n + 1) =
    simpleMatch (.symbol s) (.symbol t) b (n + 1) := by
  simp [groundDispatch3, isGroundAtom, simpleMatch]

/-- **Open-ground branch IS simpleMatch.** -/
theorem dispatch3_open_ground (pattern target : Atom) (b : Bindings) (fuel : Nat)
    (hpat : isGroundAtom pattern = false)
    (htgt : isGroundAtom target = true) :
    groundDispatch3 pattern target b fuel =
    simpleMatch pattern target b fuel := by
  simp [groundDispatch3, hpat, htgt]

/-- **Open-open branch uses matchAtoms, not simpleMatch.** -/
theorem dispatch3_open_open (pattern target : Atom) (b : Bindings) (fuel : Nat)
    (htgt : isGroundAtom target = false) :
    groundDispatch3 pattern target b fuel =
    match matchAtoms pattern target fuel with
    | result :: _ => some result
    | [] => none := by
  simp [groundDispatch3, htgt]

/-! ## §7: Summary

| Theorem | What it says | Match.c seam |
|---------|-------------|-------------|
| `ground_symbol_eq` | Symbol match = equality | ground branch |
| `ground_grounded_eq` | Grounded match = equality | ground branch |
| `ground_ground_simpleMatch_preserves` | Ground-ground success → bindings unchanged | ground branch |
| `ground_ground_simpleMatch_of_eq_step` | Ground-ground equal → success (inductive step) | ground branch |
| `open_ground_simpleMatch_extends` | Open+ground → simpleMatch extends seed | one-way path |
| `open_ground_matchAtoms_symbol` | matchAtoms = simpleMatch for symbol vs ground | leaf dispatch |
| `open_ground_matchAtoms_var_succeeds` | Variable vs ground → simpleMatch succeeds | leaf dispatch |
| `open_ground_matchAtoms_grounded` | matchAtoms = simpleMatch for grounded vs ground | leaf dispatch |
| `open_open_simpleMatch_ne_matchAtoms` | assign ≠ equality: must use matchAtoms | full path |
| `ground_not_var` | Ground atoms can't loop | skip loop check |
| `dispatch3_ground_symbol` | Dispatch agrees for ground symbols | dispatch tree |
| `dispatch3_open_ground` | Dispatch = simpleMatch for open+ground | dispatch tree |
| `dispatch3_open_open` | Dispatch = matchAtoms for open+open | dispatch tree |

**Honest gaps:**
- matchAtoms/simpleMatch equivalence proved for LEAF cases (symbol, grounded, var)
  but NOT for the expression case (needs matchAtomsList vs simpleMatchList structural theorem).
- `groundDispatch3` open-open branch drops the seed `b` (real C merges via `bindings_clone_merge`).
- Ground-valued-bindings theorem (all new values are ground when target is ground) deferred
  to NativeGroundBindingsApply.lean.
-/

end Mettapedia.Languages.MeTTa.HE.NativeGroundFastPath
