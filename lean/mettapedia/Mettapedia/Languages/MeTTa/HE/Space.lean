import Mettapedia.Languages.MeTTa.HE.Matching
import Provenance.Util.ValueTypeString

/-!
# HE MeTTa Space

Atomspace and grounded dispatch for the HE interpreter formalization.
Uses computable (List-based) representation to enable `decide` proofs.

## Source Precedence
1. `interpreter.rs` (ground truth)
2. `metta.md` (spec)

## Main Definitions
* `Space` - Computable atomspace (List-based)
* `getAtomTypes` - Get all types for an atom from space
* `getMetaType` - Intrinsic meta-type of an atom
* `queryEquations` - Query `(= pattern $X)` matching
* `GroundedResult` / `GroundedDispatch` - Grounded operation dispatch
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Space

A computable atomspace using `List Atom` (unlike MeTTaCore.Atomspace which uses
noncomputable `Multiset`). This enables kernel-checked conformance tests. -/

/-- Computable atomspace for HE interpreter.
    Ref: metta.md "Atomspace" concept. -/
structure Space where
  atoms : List Atom
  deriving Repr, Inhabited, DecidableEq

namespace Space

/-- Empty space. -/
def empty : Space := ⟨[]⟩

instance : EmptyCollection Space := ⟨empty⟩

/-- Add an atom. -/
def add (s : Space) (a : Atom) : Space :=
  ⟨a :: s.atoms⟩

/-- Remove first occurrence of an atom. -/
def remove (s : Space) (a : Atom) : Space :=
  ⟨s.atoms.erase a⟩

/-- Add multiple atoms. -/
def addMany (s : Space) (as : List Atom) : Space :=
  ⟨as ++ s.atoms⟩

/-- Create from a list of atoms. -/
def ofList (as : List Atom) : Space := ⟨as⟩

/-- Check if an atom is a type annotation `(: atom type)`. -/
def isTypeAnnotation : Atom → Bool
  | .expression [.symbol ":", _, _] => true
  | _ => false

/-- Get the annotated atom from `(: atom type)`. -/
def getAnnotatedAtom : Atom → Option Atom
  | .expression [.symbol ":", a, _] => some a
  | _ => none

/-- Get the type from `(: atom type)`. -/
def getAnnotationType : Atom → Option Atom
  | .expression [.symbol ":", _, ty] => some ty
  | _ => none

/-- Check if an atom is an equation `(= lhs rhs)`. -/
def isEquation : Atom → Bool
  | .expression [.symbol "=", _, _] => true
  | _ => false

/-- Get LHS of equation. -/
def getEquationLhs : Atom → Option Atom
  | .expression [.symbol "=", lhs, _] => some lhs
  | _ => none

/-- Get RHS of equation. -/
def getEquationRhs : Atom → Option Atom
  | .expression [.symbol "=", _, rhs] => some rhs
  | _ => none

end Space

/-! ## Type Queries

Ref: metta.md line 287 `<list of the types of the $atom from the $space>`.
Ref: `types.rs:get_atom_types` (ground truth).

Type resolution dispatches by atom kind:
1. **Variables** → no type (falls back to `%Undefined%`)
2. **Grounded atoms** → intrinsic type from `Grounded::type_()` trait
3. **Symbols** → explicit `(: atom type)` annotations in space
4. **Expressions** → space annotations (application type inference deferred)

If no type is found, returns `[%Undefined%]`.
-/

/-- Get the intrinsic HE type of a grounded value.
    Ref: `hyperon-atom/src/gnd/{number,bool,str}.rs` — `Grounded::type_()` impl.
    HE uses `Number` (not `Int`) for all numeric grounded values. -/
def getGroundedType : GroundedValue → Atom
  | .int _       => .symbol "Number"
  | .bool _      => .symbol "Bool"
  | .string _    => .symbol "String"
  | .custom t _  => .symbol t

/-- Collect explicit `(: atom type)` annotations for an atom from space.
    Ref: `types.rs:query_types`. -/
def getAnnotatedTypes (space : Space) (a : Atom) : List Atom :=
  space.atoms.filterMap fun atom =>
    match atom with
    | .expression [.symbol ":", a', ty] =>
      if a' == a then some ty else none
    | _ => none

/-- Get all types for an atom from the space.
    Ref: `types.rs:get_atom_types`, metta.md line 287.

    Dispatches by atom kind following the Rust implementation:
    - Variables: no type → `%Undefined%`
    - Grounded: intrinsic type from `Grounded::type_()`
    - Symbols: `(: atom type)` annotations in space
    - Expressions: space annotations (application type inference deferred) -/
def getAtomTypes (space : Space) (a : Atom) : List Atom :=
  let types := match a with
    | .var _ => []
    | .grounded g =>
      let ty := getGroundedType g
      if ty == Atom.undefinedType then [] else [ty]
    | .symbol _ => getAnnotatedTypes space a
    | .expression es =>
      if es.isEmpty then []
      else getAnnotatedTypes space a
  if types.isEmpty then [Atom.undefinedType]
  else types

/-! ## Equation Query

Ref: metta.md line 538 `query($space, (= $atom $X))`.
Matches equations `(= pattern rhs)` against the query atom. -/

/-- Collect all variable names occurring in an atom (with duplicates).
    Fuel-bounded with `where`-clause list traversal for kernel reduction
    (nested-inductive `Atom` requires explicit structural recursion). -/
def collectVars (a : Atom) (fuel : Nat := 100) : List String :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match a with
    | .var v => [v]
    | .expression es => collectVarsList es n
    | _ => []
where
  collectVarsList : List Atom → Nat → List String
    | [], _ => []
    | a :: as, fuel => collectVars a fuel ++ collectVarsList as fuel

/-- Rename variables in an atom according to a mapping.
    Fuel-bounded with `where`-clause list traversal for kernel reduction. -/
def renameVars (mapping : List (String × String)) (a : Atom) (fuel : Nat := 100) : Atom :=
  match fuel with
  | 0 => a
  | n + 1 =>
    match a with
    | .var v => .var (mapping.find? (fun p => p.1 == v) |>.map Prod.snd |>.getD v)
    | .expression es => .expression (renameVarsList mapping es n)
    | a => a
where
  renameVarsList (mapping : List (String × String)) : List Atom → Nat → List Atom
    | [], _ => []
    | a :: as, fuel => renameVars mapping a fuel :: renameVarsList mapping as fuel

/-- Build a fresh variable mapping for one equation's variables.
    Each distinct variable name gets a unique suffix `#counter`.
    Returns the mapping and the updated counter.
    Ref: Rust HE uses `CachingMapper` + `VariableAtom::make_unique()`. -/
def freshMapping (counter : Nat) (vars : List String) : List (String × String) × Nat :=
  vars.foldl (fun (acc, n) v =>
    if acc.any (fun p => p.1 == v) then (acc, n)
    else ((v, s!"{v}#{n}") :: acc, n + 1))
  ([], counter)

/-- Search forward from `counter` for the first visible spelling `base#n` that
    is not already present in `avoid`. The search window is bounded by the
    number of distinct visible names, which is enough to find a gap among the
    candidate spellings. -/
private def chooseFreshNameLoop (base : String) (avoid : List String) : Nat → Nat → String × Nat
  | 0, n => (s!"{base}#{n}", n + 1)
  | fuel + 1, n =>
      let cand := s!"{base}#{n}"
      if cand ∈ avoid then
        chooseFreshNameLoop base avoid fuel (n + 1)
      else
        (cand, n + 1)

/-- Choose a fresh name for `base`, starting at `counter`, while avoiding all
    externally visible names in `avoid`. The chosen spelling still follows the
    runtime-style `base#n` convention, but it skips any already-visible
    `base#n` names instead of merely incrementing blindly. -/
def chooseFreshName (base : String) (avoid : List String) (counter : Nat) : String × Nat :=
  chooseFreshNameLoop base avoid avoid.eraseDups.length counter

/-- Fresh-variable mapping that avoids an external visible-name set while still
    producing runtime-style `base#n` names. Previously generated fresh names
    are also included in the avoid set so distinct source variables cannot
    collapse onto the same visible spelling. -/
def freshMappingAgainst (counter : Nat) (avoid vars : List String) :
    List (String × String) × Nat :=
  vars.foldl (fun (acc, n) v =>
    if acc.any (fun p => p.1 == v) then (acc, n)
    else
      let used := avoid ++ acc.map Prod.snd
      let (fresh, n') := chooseFreshName v used n
      ((v, fresh) :: acc, n'))
  ([], counter)

private def freshMappingAgainstStep (avoid : List String) :
    (List (String × String) × Nat) → String → (List (String × String) × Nat)
  | (acc, n), v =>
      if acc.any (fun p => p.1 == v) then (acc, n)
      else
        let used := avoid ++ acc.map Prod.snd
        let (fresh, n') := chooseFreshName v used n
        ((v, fresh) :: acc, n')

private theorem chooseFreshNameLoop_hasCounterSuffix
    (base : String) (avoid : List String) :
    ∀ (fuel counter : Nat), ∃ k : Nat,
      (chooseFreshNameLoop base avoid fuel counter).1 = s!"{base}#{k}" := by
  intro fuel counter
  induction fuel generalizing counter with
  | zero =>
      exact ⟨counter, rfl⟩
  | succ fuel ih =>
      let cand := toString base ++ toString "#" ++ counter.repr
      unfold chooseFreshNameLoop
      by_cases h : cand ∈ avoid
      · simpa [cand, h] using (ih (counter + 1))
      · refine ⟨counter, ?_⟩
        simp [cand, h]

/-- The visible-avoid fresh-name chooser always returns the original base name
with a numeric `#counter` suffix; it only skips counters, never changes the
base variable name. This is the first structural fact the repaired bridge uses
when comparing HE and LeaTTa freshening disciplines. -/
theorem chooseFreshName_hasCounterSuffix
    (base : String) (avoid : List String) (counter : Nat) :
    ∃ k : Nat, (chooseFreshName base avoid counter).1 = s!"{base}#{k}" := by
  unfold chooseFreshName
  exact chooseFreshNameLoop_hasCounterSuffix base avoid _ counter

private def decodeFreshName (s : String) : String × Nat :=
  let rs := s.toList.reverse
  let revDigits := rs.takeWhile (fun c => c != '#')
  let rest := rs.dropWhile (fun c => c != '#')
  (String.ofList (rest.drop 1).reverse, natStringValue (String.ofList revDigits.reverse))

private theorem digit_not_hash_of_mem_toDigits (n : Nat) :
    ∀ a ∈ (Nat.toDigits 10 n).reverse, (a != '#') = true := by
  intro a ha
  have ha' : a ∈ Nat.toDigits 10 n := List.mem_reverse.mp ha
  have hdig : a.isDigit = true :=
    Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega) ha'
  have hneq : a ≠ '#' := by
    intro h
    simp [h] at hdig
  simp [hneq]

private theorem decodeFreshName_eq (v : String) (n : Nat) :
    decodeFreshName (v ++ "#" ++ toString n) = (v, n) := by
  unfold decodeFreshName
  rw [String.toList_append, String.toList_append, List.reverse_append, List.reverse_append]
  simp
  have htake :=
    List.takeWhile_append_of_pos
      (l₁ := (Nat.toDigits 10 n).reverse)
      (l₂ := '#' :: v.toList.reverse)
      (p := fun c => c != '#')
      (digit_not_hash_of_mem_toDigits n)
  have hdrop :=
    List.dropWhile_append_of_pos
      (l₁ := (Nat.toDigits 10 n).reverse)
      (l₂ := '#' :: v.toList.reverse)
      (p := fun c => c != '#')
      (digit_not_hash_of_mem_toDigits n)
  rw [htake, hdrop]
  have hnat : natStringValue (String.ofList (Nat.toDigits 10 n)) = n := by
    simpa [natStringValue, Nat.toList_repr] using natStringValue_repr n
  simp [hnat]

private theorem freshName_injective :
    Function.Injective (fun p : String × Nat => p.1 ++ "#" ++ toString p.2) := by
  intro p q h
  have hp : decodeFreshName (p.1 ++ "#" ++ toString p.2) =
      decodeFreshName (q.1 ++ "#" ++ toString q.2) := congrArg decodeFreshName h
  have hp' : decodeFreshName (p.1 ++ "#" ++ toString p.2) = p := by
    simpa using (decodeFreshName_eq p.1 p.2)
  have hq' : decodeFreshName (q.1 ++ "#" ++ toString q.2) = q := by
    simpa using (decodeFreshName_eq q.1 q.2)
  calc
    p = decodeFreshName (p.1 ++ "#" ++ toString p.2) := hp'.symm
    _ = decodeFreshName (q.1 ++ "#" ++ toString q.2) := hp
    _ = q := hq'

private def candidateWindow (base : String) : Nat → Nat → List String
  | 0, counter => [s!"{base}#{counter}"]
  | fuel + 1, counter => s!"{base}#{counter}" :: candidateWindow base fuel (counter + 1)

private theorem candidateWindow_length (base : String) :
    ∀ fuel counter, (candidateWindow base fuel counter).length = fuel + 1
  | 0, _ => by simp [candidateWindow]
  | fuel + 1, counter => by
      simp [candidateWindow, candidateWindow_length base fuel (counter + 1)]

private theorem freshName_sameBase_ne_of_ne
    (base : String) {m n : Nat} (h : m ≠ n) :
    s!"{base}#{m}" ≠ s!"{base}#{n}" := by
  intro hEq
  have hpairs : (base, m) = (base, n) := by
    apply freshName_injective
    simpa using hEq
  have hmn : m = n := by
    simpa using congrArg Prod.snd hpairs
  exact h hmn

private theorem freshName_not_mem_candidateWindow_from_lt
    (base : String) :
    ∀ fuel start counter,
      counter < start →
      s!"{base}#{counter}" ∉ candidateWindow base fuel start
  | 0, start, counter, hlt => by
      intro hs
      simp [candidateWindow] at hs
      have hs' : s!"{base}#{counter}" = s!"{base}#{start}" := by simpa using hs
      exact freshName_sameBase_ne_of_ne base (Nat.ne_of_lt hlt) hs'
  | fuel + 1, start, counter, hlt => by
      intro hs
      simp [candidateWindow] at hs
      rcases hs with hs | hs
      · have hs' : s!"{base}#{counter}" = s!"{base}#{start}" := by simpa using hs
        exact freshName_sameBase_ne_of_ne base (Nat.ne_of_lt hlt) hs'
      · exact
          freshName_not_mem_candidateWindow_from_lt
            base fuel (start + 1) counter (lt_trans hlt (Nat.lt_succ_self start)) hs

private theorem candidateWindow_nodup (base : String) :
    ∀ fuel counter, (candidateWindow base fuel counter).Nodup
  | 0, _ => by simp [candidateWindow]
  | fuel + 1, counter => by
      refine List.Nodup.cons ?_ (candidateWindow_nodup base fuel (counter + 1))
      exact freshName_not_mem_candidateWindow_from_lt base fuel (counter + 1) counter
        (Nat.lt_succ_self counter)

private theorem chooseFreshNameLoop_mem_candidateWindow
    (base : String) (avoid : List String) :
    ∀ fuel counter,
      (chooseFreshNameLoop base avoid fuel counter).1 ∈ candidateWindow base fuel counter
  | 0, counter => by
      simp [chooseFreshNameLoop, candidateWindow]
  | fuel + 1, counter => by
      let cand := toString base ++ toString "#" ++ counter.repr
      by_cases hcur : cand ∈ avoid
      · rw [show chooseFreshNameLoop base avoid (fuel + 1) counter =
            chooseFreshNameLoop base avoid fuel (counter + 1) by
              simp [chooseFreshNameLoop, cand, hcur]]
        simpa [candidateWindow, cand] using
          List.mem_cons_of_mem cand (chooseFreshNameLoop_mem_candidateWindow base avoid fuel (counter + 1))
      · rw [show chooseFreshNameLoop base avoid (fuel + 1) counter =
            (cand, counter + 1) by
              simp [chooseFreshNameLoop, cand, hcur]]
        simp [candidateWindow, cand]

private theorem chooseFreshNameLoop_all_candidates_mem_of_mem_avoid
    (base : String) (avoid : List String) :
    ∀ fuel counter,
      (chooseFreshNameLoop base avoid fuel counter).1 ∈ avoid →
      ∀ s ∈ candidateWindow base fuel counter, s ∈ avoid
  | 0, counter, hmem => by
      intro s hs
      simp [candidateWindow] at hs
      subst hs
      exact hmem
  | fuel + 1, counter, hmem => by
      let cand := toString base ++ toString "#" ++ counter.repr
      by_cases hcur : cand ∈ avoid
      · intro s hs
        have hmem' : (chooseFreshNameLoop base avoid fuel (counter + 1)).1 ∈ avoid := by
          simp [chooseFreshNameLoop, cand, hcur] at hmem
          exact hmem
        simp [candidateWindow] at hs
        rcases hs with rfl | hs
        · exact hcur
        · exact
            chooseFreshNameLoop_all_candidates_mem_of_mem_avoid
              base avoid fuel (counter + 1) hmem' s hs
      · exfalso
        have hmem' := hmem
        simp [chooseFreshNameLoop, cand, hcur] at hmem'

private theorem nodup_eraseDups : (xs : List String) → xs.eraseDups.Nodup
  | [] => by
      simp
  | x :: xs => by
      rw [List.eraseDups_cons]
      refine List.Nodup.cons ?_ (nodup_eraseDups _)
      intro hx
      have : x ∈ List.filter (fun b => !b == x) xs := List.mem_eraseDups.mp hx
      simp at this
termination_by xs => xs.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le (fun b => !b == x) xs)

/-- The repaired visible-avoid chooser really avoids the caller-supplied visible
names: the returned `base#k` spelling is never already present in `avoid`. -/
theorem chooseFreshName_not_mem_avoid
    (base : String) (avoid : List String) (counter : Nat) :
    (chooseFreshName base avoid counter).1 ∉ avoid := by
  intro hmem
  have hall :
      ∀ s ∈ candidateWindow base avoid.eraseDups.length counter, s ∈ avoid.eraseDups := by
    intro s hs
    apply List.mem_eraseDups.mpr
    exact
      chooseFreshNameLoop_all_candidates_mem_of_mem_avoid
        base avoid avoid.eraseDups.length counter
        (by simpa [chooseFreshName] using hmem) s hs
  have hsubset :
      (candidateWindow base avoid.eraseDups.length counter).toFinset ⊆ avoid.eraseDups.toFinset := by
    intro s hs
    exact List.mem_toFinset.mpr (hall s (List.mem_toFinset.mp hs))
  have hcard :=
    Finset.card_le_card hsubset
  have hleft :
      (candidateWindow base avoid.eraseDups.length counter).toFinset.card =
        (candidateWindow base avoid.eraseDups.length counter).length := by
    exact
      List.toFinset_card_of_nodup
        (candidateWindow_nodup base avoid.eraseDups.length counter)
  have hright :
      avoid.eraseDups.toFinset.card = avoid.eraseDups.length := by
    exact List.toFinset_card_of_nodup (nodup_eraseDups avoid)
  rw [hleft, hright, candidateWindow_length] at hcard
  omega

private theorem exists_pair_of_mem_map_fst
    {acc : List (String × String)} {v : String}
    (hmem : v ∈ acc.map Prod.fst) :
    ∃ fresh, (v, fresh) ∈ acc := by
  induction acc with
  | nil =>
      cases hmem
  | cons p ps ih =>
      rcases p with ⟨k, fresh⟩
      simp at hmem
      rcases hmem with h | h
      · exact ⟨fresh, by simp [h]⟩
      · rcases h with ⟨fresh', hmem'⟩
        exact ⟨fresh', List.mem_cons_of_mem _ hmem'⟩

private theorem any_key_eq_true_of_mem_map_fst
    {acc : List (String × String)} {v : String}
    (hmem : v ∈ acc.map Prod.fst) :
    acc.any (fun p => p.1 == v) = true := by
  rcases exists_pair_of_mem_map_fst hmem with ⟨fresh, hpair⟩
  exact (List.any_eq_true).2 ⟨(v, fresh), hpair, by simp⟩

private theorem freshMappingAgainstStep_pairs_haveCounterSuffix
    {avoid : List String} {acc : List (String × String)} {n : Nat} {v : String}
    (hacc : ∀ (p : String × String), p ∈ acc → ∃ k : Nat, p.2 = s!"{p.1}#{k}") :
    ∀ (p : String × String), p ∈ (freshMappingAgainstStep avoid (acc, n) v).1 →
      ∃ k : Nat, p.2 = s!"{p.1}#{k}" := by
  intro p hp
  by_cases hdup : acc.any (fun q => q.1 == v)
  · have hp' : p ∈ acc := by
      simpa [freshMappingAgainstStep, hdup] using hp
    exact hacc p hp'
  · have hp' :
        p ∈
          (v, (chooseFreshName v (avoid ++ acc.map Prod.snd) n).1) :: acc := by
      simpa [freshMappingAgainstStep, hdup] using hp
    rcases List.mem_cons.mp hp' with h | h
    · rcases h with ⟨rfl, rfl⟩
      rcases chooseFreshName_hasCounterSuffix v (avoid ++ acc.map Prod.snd) n with ⟨k, hk⟩
      exact ⟨k, hk⟩
    · exact hacc p h

private theorem freshMappingAgainst_pairs_haveCounterSuffix_aux
    (avoid : List String) :
    ∀ (vars : List String) (acc : List (String × String)) (n : Nat),
      (∀ (p : String × String), p ∈ acc → ∃ k : Nat, p.2 = s!"{p.1}#{k}") →
      ∀ (p : String × String), p ∈ (List.foldl (freshMappingAgainstStep avoid) (acc, n) vars).1 →
        ∃ k : Nat, p.2 = s!"{p.1}#{k}" := by
  intro vars
  induction vars with
  | nil =>
      intro acc n hacc p hp
      simpa using hacc p hp
  | cons v vs ih =>
      intro acc n hacc p hp
      let st := freshMappingAgainstStep avoid (acc, n) v
      have hst :
          ∀ (q : String × String), q ∈ st.1 → ∃ k : Nat, q.2 = s!"{q.1}#{k}" :=
        freshMappingAgainstStep_pairs_haveCounterSuffix hacc
      exact ih st.1 st.2 hst p hp

/-- Every fresh value produced by `freshMappingAgainst` keeps the same base
variable name and only changes the numeric suffix. This gives later repaired
bridge proofs a clean structural invariant without reopening the whole fold. -/
theorem freshMappingAgainst_pairs_haveCounterSuffix
    (counter : Nat) (avoid vars : List String) :
    ∀ (p : String × String), p ∈ (freshMappingAgainst counter avoid vars).1 →
      ∃ k : Nat, p.2 = s!"{p.1}#{k}" := by
  have hEq :
      freshMappingAgainst counter avoid vars =
        List.foldl (freshMappingAgainstStep avoid) ([], counter) vars := by
    rfl
  simpa [hEq] using
    freshMappingAgainst_pairs_haveCounterSuffix_aux avoid vars [] counter
      (by intro p hp; cases hp)

private theorem freshMappingAgainstStep_keysNodup
    {avoid : List String} {acc : List (String × String)} {n : Nat} {v : String}
    (hacc : (acc.map Prod.fst).Nodup) :
    ((freshMappingAgainstStep avoid (acc, n) v).1.map Prod.fst).Nodup := by
  unfold freshMappingAgainstStep
  by_cases hdup : acc.any (fun p => p.1 == v)
  · simpa [hdup] using hacc
  · have hnotmem : v ∉ acc.map Prod.fst := by
      intro hmem
      have : acc.any (fun p => p.1 == v) = true :=
        any_key_eq_true_of_mem_map_fst hmem
      rw [this] at hdup
      contradiction
    simpa [hdup] using List.Nodup.cons hnotmem hacc

private theorem freshMappingAgainst_keysNodup_aux
    (avoid : List String) :
    ∀ (vars : List String) (acc : List (String × String)) (n : Nat),
      (acc.map Prod.fst).Nodup →
      ((List.foldl (freshMappingAgainstStep avoid) (acc, n) vars).1.map Prod.fst).Nodup := by
  intro vars
  induction vars with
  | nil =>
      intro acc n hacc
      simpa using hacc
  | cons v vs ih =>
      intro acc n hacc
      let st := freshMappingAgainstStep avoid (acc, n) v
      have hst : (st.1.map Prod.fst).Nodup :=
        freshMappingAgainstStep_keysNodup hacc
      exact ih st.1 st.2 hst

/-- The repaired visible-avoid freshening map never duplicates source-variable
keys. This is the bookkeeping invariant the later bridge lemmas need when they
transport HE bindings onto LeaTTa matcher substitutions. -/
theorem freshMappingAgainst_keysNodup
    (counter : Nat) (avoid vars : List String) :
    ((freshMappingAgainst counter avoid vars).1.map Prod.fst).Nodup := by
  have hEq :
      freshMappingAgainst counter avoid vars =
        List.foldl (freshMappingAgainstStep avoid) ([], counter) vars := by
    rfl
  simpa [hEq] using
    freshMappingAgainst_keysNodup_aux avoid vars [] counter (by simp)

private theorem freshMappingAgainstStep_valuesNodup
    {avoid : List String} {acc : List (String × String)} {n : Nat} {v : String}
    (hacc : (acc.map Prod.snd).Nodup) :
    ((freshMappingAgainstStep avoid (acc, n) v).1.map Prod.snd).Nodup := by
  unfold freshMappingAgainstStep
  by_cases hdup : acc.any (fun p => p.1 == v)
  · simpa [hdup] using hacc
  · have hfresh :
        (chooseFreshName v (avoid ++ acc.map Prod.snd) n).1 ∉ acc.map Prod.snd := by
      intro hmem
      exact
        chooseFreshName_not_mem_avoid v (avoid ++ acc.map Prod.snd) n
          (List.mem_append.mpr (Or.inr hmem))
    simpa [hdup] using List.Nodup.cons hfresh hacc

private theorem freshMappingAgainst_valuesNodup_aux
    (avoid : List String) :
    ∀ (vars : List String) (acc : List (String × String)) (n : Nat),
      (acc.map Prod.snd).Nodup →
      ((List.foldl (freshMappingAgainstStep avoid) (acc, n) vars).1.map Prod.snd).Nodup := by
  intro vars
  induction vars with
  | nil =>
      intro acc n hacc
      simpa using hacc
  | cons v vs ih =>
      intro acc n hacc
      let st := freshMappingAgainstStep avoid (acc, n) v
      have hst : (st.1.map Prod.snd).Nodup :=
        freshMappingAgainstStep_valuesNodup hacc
      exact ih st.1 st.2 hst

/-- The repaired visible-avoid freshening map never reuses a generated visible
spelling: the fresh target names are pairwise distinct. Together with
`chooseFreshName_not_mem_avoid`, this is the key capture-safety invariant of
the avoid-aware HE freshening model. -/
theorem freshMappingAgainst_valuesNodup
    (counter : Nat) (avoid vars : List String) :
    ((freshMappingAgainst counter avoid vars).1.map Prod.snd).Nodup := by
  have hEq :
      freshMappingAgainst counter avoid vars =
        List.foldl (freshMappingAgainstStep avoid) ([], counter) vars := by
    rfl
  simpa [hEq] using
    freshMappingAgainst_valuesNodup_aux avoid vars [] counter (by simp)

/-- Alpha-rename equation-local variables while avoiding a visible-name set
    supplied by the caller, typically the query atom's currently visible
    variables. This models the stronger "standardize apart from the query"
    discipline that the concrete runtime enforces with epoch-tagged internal
    variable identities. -/
def freshenEquationAgainst (avoid : List String)
    (idx : Nat) (lhs rhs : Atom) (fuel : Nat := 100) : Atom × Atom :=
  let vars := (collectVars lhs fuel ++ collectVars rhs fuel).eraseDups
  let (mapping, _) := freshMappingAgainst idx avoid vars
  (renameVars mapping lhs fuel, renameVars mapping rhs fuel)

/-- Alpha-rename equation-local variables using the equation's index as a
    unique prefix. Returns `(renamed_lhs, renamed_rhs)`.
    Uses the same fuel as the parent query for kernel reduction. -/
def freshenEquation (idx : Nat) (lhs rhs : Atom) (fuel : Nat := 100) : Atom × Atom :=
  let vars := (collectVars lhs fuel ++ collectVars rhs fuel).eraseDups
  let (mapping, _) := freshMapping idx vars
  (renameVars mapping lhs fuel, renameVars mapping rhs fuel)

/-- Query equations `(= lhs rhs)` in space where `lhs` matches `atom`.
    Returns list of `(rhs, bindings)` pairs.
    Equation-local variables are alpha-renamed with unique suffixes to prevent
    collisions across recursive equation applications.
    Ref: metta.md line 538 `query($space, (= $atom $X))`.
    Ref: Rust HE `hyperon-space/src/index/trie.rs:261-359` (CachingMapper). -/
private def queryEquationsLegacy (space : Space) (atom : Atom) (fuel : Nat := 100) :
    List (Atom × Bindings) :=
  space.atoms.zipIdx.filterMap fun (eq, idx) =>
    match eq with
    | .expression [.symbol "=", lhs, rhs] =>
      let (lhs', rhs') := freshenEquation idx lhs rhs fuel
      match simpleMatch lhs' atom Bindings.empty fuel with
      | some b => some (rhs', b)
      | none => none
    | _ => none

/-- The faithful equation-query surface: alpha-freshen the rule, run the
official HE matcher `matchAtoms`, then replay the empty incoming seed via
`mergeBindings`.  This is the surface the declarative HE `equation_match`
rules should consume; the legacy `simpleMatch` path is kept only as a private
comparison helper for the bounded G3 agreement theorem. -/
def queryEquations (space : Space) (atom : Atom) (fuel : Nat := 100) : List (Atom × Bindings) :=
  match fuel with
  | 0 => []
  | _ =>
    space.atoms.zipIdx.flatMap fun (eq, idx) =>
      match eq with
      | .expression [.symbol "=", lhs, rhs] =>
        let (lhs', rhs') := freshenEquation idx lhs rhs fuel
        (matchAtoms atom lhs' fuel).flatMap fun qb =>
          (mergeBindings qb Bindings.empty fuel).filterMap fun merged =>
            if merged.hasLoop then none else some (rhs', merged)
      | _ => []

/-- Variant of `queryEquations` that standardizes equation-local variables apart
    from the query atom's currently visible variables before matching. This is a
    closer executable model of the concrete runtime's stronger freshness
    discipline, without yet replacing the legacy query surface. -/
private def queryEquationsAgainstVisibleLegacy
    (space : Space) (atom : Atom) (fuel : Nat := 100) : List (Atom × Bindings) :=
  let avoid := (collectVars atom fuel).eraseDups
  space.atoms.zipIdx.filterMap fun (eq, idx) =>
    match eq with
    | .expression [.symbol "=", lhs, rhs] =>
      let (lhs', rhs') := freshenEquationAgainst avoid idx lhs rhs fuel
      match simpleMatch lhs' atom Bindings.empty fuel with
      | some b => some (rhs', b)
      | none => none
    | _ => none

/-- Faithful visible-avoid equation query: standardize apart from the query's
currently visible variables, then use the official matcher/merge surface. -/
def queryEquationsAgainstVisible
    (space : Space) (atom : Atom) (fuel : Nat := 100) : List (Atom × Bindings) :=
  let avoid := (collectVars atom fuel).eraseDups
  match fuel with
  | 0 => []
  | _ =>
    space.atoms.zipIdx.flatMap fun (eq, idx) =>
      match eq with
      | .expression [.symbol "=", lhs, rhs] =>
        let (lhs', rhs') := freshenEquationAgainst avoid idx lhs rhs fuel
        (matchAtoms atom lhs' fuel).flatMap fun qb =>
          (mergeBindings qb Bindings.empty fuel).filterMap fun merged =>
            if merged.hasLoop then none else some (rhs', merged)
      | _ => []

/-! ## Grounded Dispatch

Ref: metta.md lines 527-536, `interpreter.rs` metta_call grounded branch.

The HE interpreter dispatches grounded operations via dynamic dispatch.
We parameterize over a `GroundedDispatch` structure. -/

/-- Result of executing a grounded operation.
    Ref: metta.md lines 529-536, `ExecError` in interpreter.rs. -/
inductive GroundedResult where
  | ok : ResultSet → GroundedResult
  | runtimeError : String → GroundedResult
  | noReduce : GroundedResult
  | incorrectArgument : GroundedResult
  deriving Repr, Inhabited, DecidableEq

/-- Grounded operation dispatch table.
    Ref: metta.md lines 527-536.

    - `isExecutable`: check if atom is an executable grounded atom
    - `execute`: call the grounded operation with arguments -/
structure GroundedDispatch where
  isExecutable : Atom → Bool
  execute : Atom → List Atom → GroundedResult
  deriving Inhabited

/-- Default dispatch with no grounded operations. -/
def GroundedDispatch.none : GroundedDispatch :=
  { isExecutable := fun _ => false
    execute := fun _ _ => .noReduce }

/-- Dispatch with standard arithmetic/boolean operations. -/
def GroundedDispatch.standard : GroundedDispatch :=
  { isExecutable := fun a => match a with
      | .grounded _ => true
      | _ => false
    execute := fun op _args => match op with
      | .grounded (.int _) => .noReduce  -- numbers are not callable
      | .grounded (.bool _) => .noReduce
      | .grounded (.string _) => .noReduce
      | _ => .noReduce }

/-! ## Unit Tests -/

section Tests

-- Space basics
example : Space.empty.atoms = [] := rfl
example : (Space.empty.add (.symbol "x")).atoms = [.symbol "x"] := rfl

-- Meta-type
example : getMetaType (.symbol "x") = .symbol "Symbol" := rfl
example : getMetaType (.var "x") = .symbol "Variable" := rfl

-- getAtomTypes
private def testSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "foo", .symbol "Int"],
    .expression [.symbol ":", .symbol "bar", .symbol "Bool"],
    .expression [.symbol "=", .symbol "foo", .grounded (.int 42)]
  ]

-- Symbol with annotation → annotated type
example : getAtomTypes testSpace (.symbol "foo") = [.symbol "Int"] := rfl
-- Symbol without annotation → %Undefined%
example : getAtomTypes testSpace (.symbol "baz") = [Atom.undefinedType] := rfl
-- Grounded int → Number (intrinsic, not from space)
example : getAtomTypes testSpace (.grounded (.int 42)) = [.symbol "Number"] := rfl
-- Grounded bool → Bool
example : getAtomTypes testSpace (.grounded (.bool true)) = [.symbol "Bool"] := rfl
-- Grounded string → String
example : getAtomTypes testSpace (.grounded (.string "hi")) = [.symbol "String"] := rfl
-- Variable → %Undefined%
example : getAtomTypes testSpace (.var "x") = [Atom.undefinedType] := rfl

-- queryEquations
example : queryEquations testSpace (.symbol "foo") =
    [(.grounded (.int 42), Bindings.empty)] := rfl

-- simpleMatch
example : simpleMatch (.var "x") (.symbol "hello") Bindings.empty 10 =
    some (Bindings.empty.assign "x" (.symbol "hello")) := rfl
example : simpleMatch (.symbol "a") (.symbol "a") Bindings.empty 10 =
    some Bindings.empty := rfl
example : simpleMatch (.symbol "a") (.symbol "b") Bindings.empty 10 =
    none := rfl

-- GroundedResult
example : GroundedResult.ok [] = GroundedResult.ok [] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
