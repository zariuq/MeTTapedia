import Mettapedia.OSLF.PathMap.CandidateArchitecture
import Mettapedia.Languages.MeTTa.HE.Matching

/-!
# PathMap Matcher Instance: Connecting HE matchAtoms to CandidateArchitecture

Instantiates the abstract `NativeMatcher` with HE's concrete `matchAtoms`.

## The Bridge

`matchAtoms` (from HE.Matching) has signature:
```
matchAtoms : Atom → Atom → Nat → List Bindings
```

`NativeMatcher` (from CandidateArchitecture) needs:
```
isMatch : Atom → Atom → Bool
```

The bridge: `matchAtoms query atom fuel` returns a non-empty list iff matching
succeeds. We wrap this as `(matchAtoms query atom fuel).length > 0`.

## Fuel Policy

HE's `matchAtoms` uses fuel for termination of the mutual recursion
(`matchAtoms`/`matchAtomsList`/`mergeBindings`/`addVarBinding`/`addVarEquality`).
The fuel parameter is a Lean formalization artifact — the actual HE interpreter
uses unbounded recursion. We parameterize the matcher instance by fuel, making
the fuel choice explicit rather than hiding a magic constant.

## CeTTa Implication

CeTTa's `match_atoms_epoch` in `space_match_backend.c` is the concrete
implementation of this matcher. The `twoPhase_eq_direct` theorem from
CandidateArchitecture then says:

  PathMap candidates + match_atoms_epoch filter = correct HE query

This file instantiates that abstract theorem with the real HE matcher.
-/

namespace Mettapedia.OSLF.PathMap.PathMapMatcherInstance

open Mettapedia.Languages.MeTTa.HE (matchAtoms Bindings BagSpace support getMetaType)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.PathMap.CandidateArchitecture

/-! ## §1: HE Matcher as NativeMatcher -/

/-- Boolean match predicate: does `matchAtoms` succeed (return ≥1 binding set)?

    Parameterized by fuel — the caller chooses how deep matching can recurse.
    For ground atoms (no nested expressions), fuel 1 suffices.
    For nested expressions of depth d, fuel d+1 suffices. -/
def heIsMatch (fuel : Nat) (query atom : Atom) : Bool :=
  (matchAtoms query atom fuel).length > 0

/-- The HE matcher wrapped as a `NativeMatcher`, parameterized by fuel. -/
def heNativeMatcher (fuel : Nat) : NativeMatcher :=
  ⟨heIsMatch fuel⟩

/-! ## §2: Concrete two-phase correctness -/

/-- **The concrete HE instantiation of two-phase correctness.**

    Given:
    - A fuel level for matching
    - A sound candidate selector for that fuel level
    - Candidates drawn from the space's support

    Then: two-phase query with HE matching = direct query.

    This is `twoPhase_eq_direct` specialized to `heNativeMatcher`. -/
theorem he_twoPhase_eq_direct (fuel : Nat) (sel : CandidateSelector)
    (space : BagSpace) (query : Atom)
    (hsound : sel.sound (heNativeMatcher fuel) space query)
    (hsubset : sel.candidates query ⊆ space.atomSupport) :
    twoPhaseQuery sel (heNativeMatcher fuel) query =
    directQuery (heNativeMatcher fuel) space query :=
  twoPhase_eq_direct sel (heNativeMatcher fuel) space query hsound hsubset

/-- **Match failure means exclusion from direct query.**

    If `matchAtoms` returns empty for a query-atom pair, that atom
    is not in the direct query result. -/
theorem not_match_not_in_direct (fuel : Nat) (space : BagSpace)
    (query atom : Atom)
    (hfail : matchAtoms query atom fuel = []) :
    atom ∉ directQuery (heNativeMatcher fuel) space query := by
  simp only [directQuery, Finset.mem_filter]
  intro ⟨_, hmatch⟩
  simp only [heNativeMatcher, heIsMatch, hfail] at hmatch
  exact absurd hmatch (by decide)

/-- **Match success means the atom passes the native filter.**

    If `matchAtoms` returns a non-empty list, the atom passes `heIsMatch`. -/
theorem match_success_passes_filter (fuel : Nat) (query atom : Atom)
    (bs : Bindings) (rest : List Bindings)
    (hsucc : matchAtoms query atom fuel = bs :: rest) :
    heIsMatch fuel query atom = true := by
  simp only [heIsMatch, hsucc, List.length_cons, decide_eq_true_eq]
  omega

/-! ## §3: Ground atom matching -/

/-- Helper: `Bindings.empty` has no loop. -/
private theorem bindings_empty_no_loop : Bindings.empty.hasLoop = false := by
  simp [Bindings.hasLoop, Bindings.empty]

/-- For identical ground atoms (no variables), `matchAtoms` with fuel ≥ 1
    returns `[Bindings.empty]`. This covers the common case in PathMap
    queries where the query skeleton exactly matches a stored atom.

    Note: this follows directly from `matchAtoms` definition — identical
    symbols produce `[Bindings.empty]`. -/
theorem matchAtoms_self_symbol (s : String) (n : Nat) :
    matchAtoms (.symbol s) (.symbol s) (n + 1) = [Bindings.empty] := by
  unfold matchAtoms
  simp only [getMetaType, Atom.symbolType, Atom.beq, BEq.beq,
             Bool.true_and, decide_true, ite_true]
  simp only [List.filter, bindings_empty_no_loop, Bool.not_false]

/-- Self-match means heIsMatch is true for identical symbols. -/
theorem heIsMatch_self_symbol (s : String) (n : Nat) :
    heIsMatch (n + 1) (.symbol s) (.symbol s) = true := by
  simp only [heIsMatch, matchAtoms_self_symbol, List.length_cons, List.length_nil]
  decide

/-! ## §4: Variable matching -/

/-- Helper: `Bindings.empty.assign v atom` has no loop when atom is not a
    variable named `v`. For non-variable atoms, this is trivially true. -/
private theorem assign_nonvar_no_loop (v : String) (atom : Atom)
    (hNotVar : ∀ w, atom ≠ .var w) :
    (Bindings.empty.assign v atom).hasLoop = false := by
  match atom with
  | .var w => exact absurd rfl (hNotVar w)
  | .symbol _ =>
    unfold Bindings.assign; simp only [Bindings.empty, Bindings.isBound, Bindings.lookup,
      List.lookup, Option.isSome, Bool.false_eq_true, ite_false, List.nil_append]
    unfold Bindings.hasLoop; simp only [List.any_cons, List.any_nil, Bool.or_false]
    unfold Bindings.hasLoop.hasLoopFrom
    simp only [Bindings.lookup, List.lookup, beq_self_eq_true]
  | .grounded _ =>
    unfold Bindings.assign; simp only [Bindings.empty, Bindings.isBound, Bindings.lookup,
      List.lookup, Option.isSome, Bool.false_eq_true, ite_false, List.nil_append]
    unfold Bindings.hasLoop; simp only [List.any_cons, List.any_nil, Bool.or_false]
    unfold Bindings.hasLoop.hasLoopFrom
    simp only [Bindings.lookup, List.lookup, beq_self_eq_true]
  | .expression _ =>
    unfold Bindings.assign; simp only [Bindings.empty, Bindings.isBound, Bindings.lookup,
      List.lookup, Option.isSome, Bool.false_eq_true, ite_false, List.nil_append]
    unfold Bindings.hasLoop; simp only [List.any_cons, List.any_nil, Bool.or_false]
    unfold Bindings.hasLoop.hasLoopFrom
    simp only [Bindings.lookup, List.lookup, beq_self_eq_true]

/-- A variable query matches any non-variable atom (with fuel ≥ 1).
    This is the HE spec: `$x` matches anything by binding `x` to the atom.

    Variables as queries are the MOST GENERAL pattern — they produce
    candidates = full support, which the two-phase architecture handles
    correctly (candidate selector may overapproximate, but native match
    filters precisely). -/
theorem matchAtoms_var_any (v : String) (atom : Atom) (n : Nat)
    (hNotVar : ∀ w, atom ≠ .var w) :
    matchAtoms (.var v) atom (n + 1) = [Bindings.empty.assign v atom] := by
  unfold matchAtoms
  simp only [getMetaType, Atom.variableType]
  match atom with
  | .symbol s =>
    simp [Atom.symbolType, Atom.beq, BEq.beq,
          List.filter, assign_nonvar_no_loop v (.symbol s) hNotVar]
  | .grounded g =>
    simp [Atom.groundedType, Atom.beq, BEq.beq,
          List.filter, assign_nonvar_no_loop v (.grounded g) hNotVar]
  | .expression es =>
    simp [Atom.expressionType, Atom.beq, BEq.beq,
          List.filter, assign_nonvar_no_loop v (.expression es) hNotVar]
  | .var w => exact absurd rfl (hNotVar w)

/-- Variable queries always pass heIsMatch (for non-variable atoms). -/
theorem heIsMatch_var_any (v : String) (atom : Atom) (n : Nat)
    (hNotVar : ∀ w, atom ≠ .var w) :
    heIsMatch (n + 1) (.var v) atom = true := by
  simp only [heIsMatch, matchAtoms_var_any v atom n hNotVar, List.length_cons,
             List.length_nil]
  decide

/-! ## §5: Summary

Key results:
- `heNativeMatcher` — HE's `matchAtoms` wrapped as `NativeMatcher`
- `he_twoPhase_eq_direct` — concrete instantiation of two-phase correctness
- `not_match_not_in_direct` — match failure ↔ exclusion from query results
- `match_success_passes_filter` — match success ↔ passes native filter
- `matchAtoms_self_symbol` — identical symbols always match
- `matchAtoms_var_any` — variable queries match any non-variable atom
- `heIsMatch_self_symbol` / `heIsMatch_var_any` — Bool-level consequences

Maps to CeTTa: `space_match_backend.c` `match_atoms_epoch` = `heNativeMatcher`
-/

end Mettapedia.OSLF.PathMap.PathMapMatcherInstance
