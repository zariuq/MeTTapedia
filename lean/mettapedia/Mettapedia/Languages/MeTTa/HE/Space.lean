import Mettapedia.Languages.MeTTa.HE.Matching
import Provenance.Util.ValueTypeString

/-!
# A list representation of HE spaces

Atomspace and grounded dispatch for the HE interpreter formalization.
Uses computable (List-based) representation to enable `decide` proofs.

The list order is a representation and traversal profile. It does not specify
a language-level enumeration order. Independent type-occurrence contracts
and admissible enumeration policies are in `Spec.Type`; executable profiles
must be related to those contracts rather than supplying their authority.

## Main Definitions
* `Space` - Computable atomspace (List-based)
* `getAtomTypes` - Get all types for an atom from space
* `getMetaType` - Intrinsic meta-type of an atom
* `queryEquations` - Query `(= pattern $X)` matching
* `queryEquationsAvoiding` - The same query with rule instances fresh for a call scope
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
`types.rs:get_atom_types` motivates the executable profile below.

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

/-- With no visible names to avoid, the fresh-name chooser uses the current
counter immediately. -/
theorem chooseFreshName_nil (base : String) (counter : Nat) :
    chooseFreshName base [] counter = (s!"{base}#{counter}", counter + 1) := by
  simp [chooseFreshName, chooseFreshNameLoop]

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

/-- The faithful equation-query interface: alpha-freshen the rule, run the
official HE matcher `matchAtoms`, then replay the empty incoming seed via
`mergeBindings`.  This is the interface the declarative HE `equation_match`
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

/-- Every public equation-query hit comes from a concrete equation in the
space whose freshened left-hand side matched the query through the faithful
two-sided HE `matchAtoms` matcher.  The extra replay of the empty incoming seed
inside `queryEquations` is definitionally transparent here; this theorem is
the small audit hook that prevents the retired one-sided query path from
re-entering the public interface. -/
theorem queryEquations_matchAtoms_witness
    {space : Space} {atom : Atom} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (h : (rhs, qb) ∈ queryEquations space atom fuel) :
    ∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs = (freshenEquation idx lhs rhs0 fuel).2 ∧
      qb ∈ matchAtoms atom (freshenEquation idx lhs rhs0 fuel).1 fuel := by
  cases fuel with
  | zero =>
      simp [queryEquations] at h
  | succ n =>
      simp [queryEquations] at h
      rcases h with ⟨eq, idx, hmem, hhit⟩
      cases eq with
      | symbol s => simp at hhit
      | var v => simp at hhit
      | grounded g => simp at hhit
      | expression es =>
          cases es with
          | nil => simp at hhit
          | cons a rest =>
              cases a <;> try simp at hhit
              next s =>
                by_cases hs : s = "="
                · subst hs
                  cases rest with
                  | nil => simp at hhit
                  | cons lhs rest2 =>
                      cases rest2 with
                      | nil => simp at hhit
                      | cons rhs0 rest3 =>
                          cases rest3 with
                          | nil =>
                              simp at hhit
                              rcases hhit with ⟨mb, hmb, hmerge⟩
                              simp [mergeBindings, Bindings.empty] at hmerge
                              rcases hmerge with ⟨rfl, _hloop, hrhs⟩
                              exact ⟨lhs, rhs0, idx, by simpa using hmem, hrhs.symm, hmb⟩
                          | cons extra rest4 => simp at hhit
                · simp [hs] at hhit

/-- Variant of `queryEquations` that standardizes equation-local variables apart
    from the query atom's currently visible variables before matching. This is a
    closer executable model of the concrete runtime's stronger freshness
    discipline, without yet replacing the legacy query interface. -/
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
currently visible variables, then use the official matcher/merge interface. -/
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

/-- Visible-avoid analogue of `queryEquations_matchAtoms_witness`: every hit of
the repaired visible query interface is backed by the faithful HE matcher on the
freshened equation left-hand side, where freshening avoids the query atom's
currently visible variables. -/
theorem queryEquationsAgainstVisible_matchAtoms_witness
    {space : Space} {atom : Atom} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (h : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    ∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs =
        (freshenEquationAgainst (collectVars atom fuel).eraseDups idx lhs rhs0 fuel).2 ∧
      qb ∈ matchAtoms atom
        (freshenEquationAgainst (collectVars atom fuel).eraseDups idx lhs rhs0 fuel).1 fuel := by
  cases fuel with
  | zero =>
      simp [queryEquationsAgainstVisible] at h
  | succ n =>
      simp [queryEquationsAgainstVisible] at h
      rcases h with ⟨eq, idx, hmem, hhit⟩
      cases eq with
      | symbol s => simp at hhit
      | var v => simp at hhit
      | grounded g => simp at hhit
      | expression es =>
          cases es with
          | nil => simp at hhit
          | cons a rest =>
              cases a <;> try simp at hhit
              next s =>
                by_cases hs : s = "="
                · subst hs
                  cases rest with
                  | nil => simp at hhit
                  | cons lhs rest2 =>
                      cases rest2 with
                      | nil => simp at hhit
                      | cons rhs0 rest3 =>
                          cases rest3 with
                          | nil =>
                              simp at hhit
                              rcases hhit with ⟨mb, hmb, hmerge⟩
                              simp [mergeBindings, Bindings.empty] at hmerge
                              rcases hmerge with ⟨rfl, _hloop, hrhs⟩
                              exact ⟨lhs, rhs0, idx, by simpa using hmem, hrhs.symm, hmb⟩
                          | cons extra rest4 => simp at hhit
                · simp [hs] at hhit

/-! ## Scoped equation query

Rule variables are renamed apart from every name visible at the call: the
variables of the atoms its continuation retains, of the call and its expected
type, and of the incoming binding record. Every stored rule therefore yields a
fresh instance at each invocation, so nested and recursive calls of one rule do
not share variables. Without a collision the spelling is the original
`name#(index + position)`. -/

mutual
/-- Variable occurrences of an atom in order, by structural recursion. -/
def atomVariables : Atom → List String
  | .var name => [name]
  | .expression atoms => atomListVariables atoms
  | .symbol _ => []
  | .grounded _ => []
/-- Variable occurrences of an atom list in order. -/
def atomListVariables : List Atom → List String
  | [] => []
  | atom :: atoms => atomVariables atom ++ atomListVariables atoms
end

/-- Every variable found by a finite scan belongs to the total inventory.
Freshness conditions therefore cover arbitrary nesting without a fixed cap. -/
theorem collectVars_subset_atomVariables (atom : Atom) (fuel : Nat) :
    ∀ name ∈ collectVars atom fuel, name ∈ atomVariables atom := by
  induction fuel generalizing atom with
  | zero => simp [collectVars]
  | succ fuel ih =>
      cases atom with
      | var name => simp [collectVars,atomVariables]
      | symbol name => simp [collectVars,atomVariables]
      | grounded value => simp [collectVars,atomVariables]
      | expression atoms =>
          simp only [collectVars,atomVariables]
          have lists : ∀ atoms : List Atom, ∀ name ∈ collectVars.collectVarsList atoms fuel,
              name ∈ atomListVariables atoms := by
            intro atoms
            induction atoms with
            | nil => simp [collectVars.collectVarsList]
            | cons first rest more =>
                intro name member
                simp only [collectVars.collectVarsList,List.mem_append] at member
                rcases member with head | tail
                · exact List.mem_append_left _ (ih first name head)
                · exact List.mem_append_right _ (more name tail)
          exact lists atoms

/-- Variable inventories concatenate with their retained atom lists. -/
theorem atomListVariables_append (xs ys : List Atom) :
    atomListVariables (xs ++ ys) = atomListVariables xs ++ atomListVariables ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, atomListVariables, ih, List.append_assoc]

theorem atomListVariables_eq_nil_of_forall (xs : List Atom)
    (empty : ∀ x ∈ xs, atomVariables x = []) : atomListVariables xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [atomListVariables, empty x (List.mem_cons_self ..), List.nil_append]
      exact ih (fun a member => empty a (List.mem_cons_of_mem x member))

mutual
/-- Simultaneous renaming of every variable leaf, by structural recursion. -/
def renameAtom (rename : String → String) : Atom → Atom
  | .var name => .var (rename name)
  | .expression atoms => .expression (renameAtomList rename atoms)
  | .symbol name => .symbol name
  | .grounded value => .grounded value
/-- Simultaneous renaming of an atom list. -/
def renameAtomList (rename : String → String) : List Atom → List Atom
  | [] => []
  | atom :: atoms => renameAtom rename atom :: renameAtomList rename atoms
end

theorem renameAtomList_eq_map (rename : String → String) :
    ∀ atoms : List Atom, renameAtomList rename atoms = atoms.map (renameAtom rename)
  | [] => rfl
  | atom :: atoms => by simp [renameAtomList, renameAtomList_eq_map rename atoms]

theorem atomListVariables_eq_flatMap :
    ∀ atoms : List Atom, atomListVariables atoms = atoms.flatMap atomVariables
  | [] => rfl
  | atom :: atoms => by simp [atomListVariables, atomListVariables_eq_flatMap atoms]

/-- Names occurring in a binding record: assigned keys, ruleVariables of stored
values and both endpoints of every variable equality. -/
def Bindings.names (bindings : Bindings) : List String :=
  bindings.assignments.flatMap (fun entry => entry.1 :: atomVariables entry.2) ++
    bindings.equalities.flatMap (fun edge => [edge.1, edge.2])

/-- The spelling `name#index` used for equation-local variable instances. -/
def suffixName (name : String) (index : Nat) : String := name ++ "#" ++ toString index

/-- The spelling agrees with the interpolated `name#index` of the original
freshener. -/
theorem suffixName_eq_interpolated (name : String) (index : Nat) :
    suffixName name index = s!"{name}#{index}" := rfl

private theorem split_at_marker {marker : Char} :
    ∀ {left right left' right' : List Char},
      marker ∉ right → marker ∉ right' →
      left ++ marker :: right = left' ++ marker :: right' → left = left' ∧ right = right'
  | [], right, [], right', _, _, equal => by simpa using equal
  | [], right, c :: left', right', notRight, _, equal => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      exact absurd (by simp) notRight
  | c :: left, right, [], right', _, notRight', equal => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      exact absurd (by simp) notRight'
  | c :: left, right, c' :: left', right', notRight, notRight', equal => by
      simp only [List.cons_append, List.cons.injEq] at equal
      obtain ⟨rfl, rest⟩ := equal
      obtain ⟨rfl, rfl⟩ := split_at_marker notRight notRight' rest
      exact ⟨rfl, rfl⟩

private theorem marker_not_mem_digits (index : Nat) : '#' ∉ Nat.toDigits 10 index := by
  intro member
  simpa using Nat.isDigit_of_mem_toDigits (by decide) (by decide) member

/-- Distinct pairs of base name and index have distinct spellings: the index is
the digit block after the final marker. -/
theorem suffixName_inj {name name' : String} {index index' : Nat}
    (equal : suffixName name index = suffixName name' index') :
    name = name' ∧ index = index' := by
  have lists := congrArg String.toList equal
  have marker : ("#" : String).toList = ['#'] := rfl
  simp only [suffixName, String.toList_append, Nat.toString_eq_ofList_toDigits,
    String.toList_ofList, marker] at lists
  have lists' : name.toList ++ '#' :: Nat.toDigits 10 index =
      name'.toList ++ '#' :: Nat.toDigits 10 index' := by
    simpa [List.append_assoc] using lists
  obtain ⟨names, digits⟩ :=
    split_at_marker (marker_not_mem_digits index) (marker_not_mem_digits index') lists'
  refine ⟨String.ext names, ?_⟩
  have := congrArg (fun digits => Nat.ofDigitChars 10 digits 0) digits
  simpa using this

/-- First index from `index` whose spelling is not in `avoid`, searching at most
`budget` further candidates. -/
def freeSuffix (avoid : List String) (name : String) : Nat → Nat → Nat
  | 0, index => index
  | budget + 1, index =>
      if suffixName name index ∈ avoid then freeSuffix avoid name budget (index + 1) else index

private theorem freeSuffix_spec (avoid : List String) (name : String) :
    ∀ (budget index : Nat),
      suffixName name (freeSuffix avoid name budget index) ∉ avoid ∨
        (freeSuffix avoid name budget index = index + budget ∧
          ∀ offset < budget, suffixName name (index + offset) ∈ avoid)
  | 0, index => Or.inr ⟨rfl, fun _ bound => absurd bound (Nat.not_lt_zero _)⟩
  | budget + 1, index => by
      by_cases taken : suffixName name index ∈ avoid
      · simp only [freeSuffix, taken, if_true]
        rcases freeSuffix_spec avoid name budget (index + 1) with fresh | ⟨result, earlier⟩
        · exact Or.inl fresh
        · refine Or.inr ⟨by omega, fun offset bound => ?_⟩
          cases offset with
          | zero => simpa using taken
          | succ offset =>
              have := earlier offset (by omega)
              rwa [show index + 1 + offset = index + (offset + 1) by omega] at this
      · left
        simpa only [freeSuffix, taken, if_false] using taken

/-- With a budget equal to the length of `avoid`, the search always succeeds:
the candidates are pairwise distinct spellings, so they cannot all be avoided. -/
theorem freeSuffix_not_mem (avoid : List String) (name : String) (index : Nat) :
    suffixName name (freeSuffix avoid name avoid.length index) ∉ avoid := by
  rcases freeSuffix_spec avoid name avoid.length index with fresh | ⟨result, earlier⟩
  · exact fresh
  · rw [result]
    intro last
    let candidates := (List.range (avoid.length + 1)).map fun offset => suffixName name (index + offset)
    have nodup : candidates.Nodup := by
      refine List.Nodup.map (fun first second equal => ?_) List.nodup_range
      have := (suffixName_inj equal).2
      omega
    have covered : candidates ⊆ avoid := by
      intro candidate member
      simp only [candidates, List.mem_map, List.mem_range] at member
      obtain ⟨offset, bound, rfl⟩ := member
      by_cases final : offset = avoid.length
      · subst final
        exact last
      · exact earlier offset (by omega)
    have := (nodup.subperm covered).length_le
    simp [candidates] at this

/-- The instance spelling of one equation variable. Without a collision it is the
original `name#(counter + position)` spelling; otherwise the first later index
that avoids every visible name. -/
def instanceName (avoid ruleVariables : List String) (counter : Nat) (name : String) : String :=
  suffixName name (freeSuffix avoid name avoid.length (counter + ruleVariables.idxOf name))

theorem instanceName_injective (avoid ruleVariables : List String) (counter : Nat) :
    Function.Injective (instanceName avoid ruleVariables counter) :=
  fun _ _ equal => (suffixName_inj equal).1

theorem instanceName_not_mem (avoid ruleVariables : List String) (counter : Nat) (name : String) :
    instanceName avoid ruleVariables counter name ∉ avoid :=
  freeSuffix_not_mem avoid name _

/-- One call-site type instance uses a single injective map for its complete
signature. The caller supplies the protected logical scope. -/
def instantiateTypeSignature (scope : List String) (position : Nat) (signature : Atom) : Atom :=
  renameAtom (instanceName scope (atomVariables signature).eraseDups position) signature

/-- Preserve the physical type list while allocating later instances apart
from all preceding instantiated signatures and the original scope. -/
def instantiateTypeSignatures (scope : List String) (position : Nat) : List Atom → List Atom
  | [] => []
  | signature :: rest =>
      let instantiated := instantiateTypeSignature scope position signature
      instantiated :: instantiateTypeSignatures (atomVariables instantiated ++ scope) (position + 1) rest

theorem instantiateTypeSignatures_length (scope : List String) (position : Nat)
    (signatures : List Atom) :
    (instantiateTypeSignatures scope position signatures).length = signatures.length := by
  induction signatures generalizing scope position with
  | nil => rfl
  | cons signature rest ih => simp [instantiateTypeSignatures, ih]

/-- A declaration query remains raw; an invocation instantiates the resulting
signatures against the retained scope and the actual reached local operands. -/
def getAtomTypesScoped (scope : List String) (space : Space) (bindings : Bindings)
    (subject expected : Atom) : List Atom :=
  instantiateTypeSignatures
    (scope ++ bindings.names ++ atomVariables subject ++ atomVariables expected) 0
    (getAtomTypes space subject)

mutual
/-- Renaming leaves an atom without variable occurrences unchanged. -/
theorem renameAtom_of_atomVariables_eq_nil (rename : String → String) :
    ∀ atom : Atom, atomVariables atom = [] → renameAtom rename atom = atom
  | .var _, closed => by simp [atomVariables] at closed
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression atoms, closed => by
      simp only [atomVariables] at closed
      simp only [renameAtom]
      rw [renameAtomList_of_atomListVariables_eq_nil rename atoms closed]
/-- Renaming leaves a list without variable occurrences unchanged. -/
theorem renameAtomList_of_atomListVariables_eq_nil (rename : String → String) :
    ∀ atoms : List Atom, atomListVariables atoms = [] → renameAtomList rename atoms = atoms
  | [], _ => rfl
  | atom :: atoms, closed => by
      simp only [atomListVariables, List.append_eq_nil_iff] at closed
      simp only [renameAtomList]
      rw [renameAtom_of_atomVariables_eq_nil rename atom closed.1,
        renameAtomList_of_atomListVariables_eq_nil rename atoms closed.2]
end

theorem instantiateTypeSignature_closed (scope : List String) (position : Nat) {signature : Atom}
    (closed : atomVariables signature = []) :
    instantiateTypeSignature scope position signature = signature :=
  renameAtom_of_atomVariables_eq_nil _ signature closed

/-- Closed signatures are returned literally and leave the avoidance scope of
every later instance unchanged. -/
theorem instantiateTypeSignatures_closed_append (scope : List String) (position : Nat)
    (closedPrefix rest : List Atom)
    (closed : ∀ signature ∈ closedPrefix, atomVariables signature = []) :
    instantiateTypeSignatures scope position (closedPrefix ++ rest) =
      closedPrefix ++ instantiateTypeSignatures scope (position + closedPrefix.length) rest := by
  induction closedPrefix generalizing position with
  | nil => simp
  | cons signature more ih =>
      have head := closed signature (List.mem_cons_self ..)
      simp only [List.cons_append, instantiateTypeSignatures,
        instantiateTypeSignature_closed scope position head, head, List.nil_append,
        List.length_cons]
      rw [ih (position + 1) (fun other member => closed other (List.mem_cons_of_mem _ member)),
        show position + 1 + more.length = position + (more.length + 1) by omega]

theorem instantiateTypeSignatures_closed (scope : List String) (position : Nat)
    (signatures : List Atom) (closed : ∀ signature ∈ signatures, atomVariables signature = []) :
    instantiateTypeSignatures scope position signatures = signatures := by
  simpa [instantiateTypeSignatures] using
    instantiateTypeSignatures_closed_append scope position signatures [] closed

/-- A scoped invocation query agrees with the raw one on every closed prefix. -/
theorem getAtomTypesScoped_closed_append (scope : List String) (space : Space)
    (bindings : Bindings) (subject expected : Atom) {closedPrefix rest : List Atom}
    (types : getAtomTypes space subject = closedPrefix ++ rest)
    (closed : ∀ signature ∈ closedPrefix, atomVariables signature = []) :
    ∃ instances, getAtomTypesScoped scope space bindings subject expected =
      closedPrefix ++ instances ∧ instances.length = rest.length := by
  refine ⟨_, by rw [getAtomTypesScoped, types,
    instantiateTypeSignatures_closed_append _ _ _ _ closed], ?_⟩
  exact instantiateTypeSignatures_length _ _ rest

/-- Alpha-rename both sides of an equation apart from every name in `avoid`.
The renaming has no fuel bound and is injective on all names. -/
def freshenEquationAvoiding (avoid : List String) (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  let ruleVariables := (atomVariables lhs ++ atomVariables rhs).eraseDups
  (renameAtom (instanceName avoid ruleVariables counter) lhs,
    renameAtom (instanceName avoid ruleVariables counter) rhs)

/-- Equation query whose rule instances are fresh for `avoid`: each stored
equation is renamed apart from every name in `avoid`, matched with the official
`matchAtoms`, and replayed through the empty seed exactly as `queryEquations`
does. The caller merges the returned candidates with its incoming bindings once. -/
def queryEquationsAvoiding (avoid : List String) (space : Space) (atom : Atom)
    (fuel : Nat := 100) : List (Atom × Bindings) :=
  match fuel with
  | 0 => []
  | _ =>
    space.atoms.zipIdx.flatMap fun (eq, idx) =>
      match eq with
      | .expression [.symbol "=", lhs, rhs] =>
        let (lhs', rhs') := freshenEquationAvoiding avoid idx lhs rhs
        (matchAtoms atom lhs' fuel).flatMap fun qb =>
          (mergeBindings qb Bindings.empty fuel).filterMap fun merged =>
            if merged.hasLoop then none else some (rhs', merged)
      | _ => []

/-- Every hit of the scoped query comes from a stored equation at a physical
position whose renamed left-hand side matched through `matchAtoms`. -/
theorem queryEquationsAvoiding_matchAtoms_witness
    {avoid : List String} {space : Space} {atom : Atom} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (h : (rhs, qb) ∈ queryEquationsAvoiding avoid space atom fuel) :
    ∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs = (freshenEquationAvoiding avoid idx lhs rhs0).2 ∧
      qb ∈ matchAtoms atom (freshenEquationAvoiding avoid idx lhs rhs0).1 fuel ∧
      qb.hasLoop = false := by
  cases fuel with
  | zero => simp [queryEquationsAvoiding] at h
  | succ n =>
      simp [queryEquationsAvoiding] at h
      rcases h with ⟨eq, idx, hmem, hhit⟩
      cases eq with
      | symbol s => simp at hhit
      | var v => simp at hhit
      | grounded g => simp at hhit
      | expression es =>
          cases es with
          | nil => simp at hhit
          | cons a rest =>
              cases a <;> try simp at hhit
              next s =>
                by_cases hs : s = "="
                · subst hs
                  cases rest with
                  | nil => simp at hhit
                  | cons lhs rest2 =>
                      cases rest2 with
                      | nil => simp at hhit
                      | cons rhs0 rest3 =>
                          cases rest3 with
                          | nil =>
                              simp at hhit
                              rcases hhit with ⟨mb, hmb, hmerge⟩
                              simp [mergeBindings, Bindings.empty] at hmerge
                              rcases hmerge with ⟨rfl, hloop, hrhs⟩
                              exact ⟨lhs, rhs0, idx, by simpa using hmem, hrhs.symm, hmb, hloop⟩
                          | cons extra rest4 => simp at hhit
                · simp [hs] at hhit

/-- The names an equation instance must avoid at a call: variables of the
retained continuation atoms `live`, of the call, of its expected type and of
the incoming binding record. -/
def equationScope (live : List Atom) (atom type_ : Atom) (bindings : Bindings) : List String :=
  atomListVariables live ++ atomVariables atom ++ atomVariables type_ ++ bindings.names

/-- Scoped query hits carry loop-free bindings. -/
theorem queryEquationsAvoiding_hasLoop_false
    {avoid : List String} {space : Space} {atom : Atom} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (h : (rhs, qb) ∈ queryEquationsAvoiding avoid space atom fuel) : qb.hasLoop = false :=
  (queryEquationsAvoiding_matchAtoms_witness h).choose_spec.choose_spec.choose_spec.2.2.2

/-- An avoidance list covers a call when it contains every variable of the call
and every name of its incoming binding record. A rule instance renamed apart from
such a list cannot capture a caller variable. -/
def CoversCall (avoid : List String) (atom : Atom) (bindings : Bindings) : Prop :=
  ∀ name, name ∈ atomVariables atom ∨ name ∈ bindings.names → name ∈ avoid

theorem equationScope_covers (live : List Atom) (atom type_ : Atom) (bindings : Bindings) :
    CoversCall (equationScope live atom type_ bindings) atom bindings := by
  rintro name (member | member) <;> simp [equationScope, member]

/-- A call instance protects the complete retained computation, including the
expected type and atoms still held by its continuation. -/
def CoversEvaluation (avoid : List String) (live : List Atom)
    (atom type_ : Atom) (bindings : Bindings) : Prop :=
  ∀ name ∈ equationScope live atom type_ bindings, name ∈ avoid

theorem equationScope_coversEvaluation (live : List Atom) (atom type_ : Atom)
    (bindings : Bindings) :
    CoversEvaluation (equationScope live atom type_ bindings) live atom type_ bindings :=
  fun _ member => member

theorem CoversEvaluation.coversCall {avoid : List String} {live : List Atom}
    {atom type_ : Atom} {bindings : Bindings}
    (covered : CoversEvaluation avoid live atom type_ bindings) :
    CoversCall avoid atom bindings := by
  intro name member
  exact covered name (equationScope_covers live atom type_ bindings name member)

/-- No stored equation matches `atom` under any freshening of the rule variables. -/
def NoEquationMatch (space : Space) (atom : Atom) : Prop :=
  ∀ avoid fuel, queryEquationsAvoiding avoid space atom fuel = []

/-- A space without stored equations has no equation match. -/
theorem noEquationMatch_of_no_equations {space : Space} (atom : Atom)
    (h : ∀ lhs rhs, Atom.expression [.symbol "=", lhs, rhs] ∉ space.atoms) :
    NoEquationMatch space atom := by
  intro avoid fuel
  rcases hits : queryEquationsAvoiding avoid space atom fuel with _ | ⟨⟨rhs, qb⟩, rest⟩
  · rfl
  · obtain ⟨lhs, rhs0, idx, member, _⟩ :=
      queryEquationsAvoiding_matchAtoms_witness (hits ▸ List.mem_cons_self)
    rw [List.mem_zipIdx_iff_getElem?] at member
    exact (h lhs rhs0 (List.mem_of_getElem? member)).elim

/-! ## Grounded Dispatch

Ref: metta.md lines 527-536, `interpreter.rs` metta_call grounded branch.

The HE interpreter dispatches grounded operations via dynamic dispatch.
We parameterize over a `GroundedDispatch` structure. -/

/-- Result of executing a grounded operation.
    Ref: metta.md lines 529-536, `ExecError` in interpreter.rs. -/
inductive GroundedResult (Value : Type := Atom) where
  | ok : List (Value × Bindings) → GroundedResult Value
  | runtimeError : String → GroundedResult Value
  | noReduce : GroundedResult Value
  | incorrectArgument : GroundedResult Value
  deriving Repr, Inhabited, DecidableEq

/-- Change only the value representation. Binding records and host outcome
classes retain their original meaning and occurrence order. -/
def GroundedResult.map {Value Other : Type} (f : Value → Other) :
    GroundedResult Value → GroundedResult Other
  | .ok values => .ok (values.map fun row => (f row.1,row.2))
  | .runtimeError message => .runtimeError message
  | .noReduce => .noReduce
  | .incorrectArgument => .incorrectArgument

theorem GroundedResult.map_id {Value : Type} (result : GroundedResult Value) :
    result.map id = result := by
  cases result <;> simp [map]

theorem GroundedResult.map_comp {Value Middle Other : Type}
    (first : Value → Middle) (second : Middle → Other) (result : GroundedResult Value) :
    (result.map first).map second = result.map (second ∘ first) := by
  cases result <;> simp [map,List.map_map]

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
example : (GroundedResult.ok [] : GroundedResult) = GroundedResult.ok [] := rfl

end Tests


/-! ## Coverage of the scoped equation query -/

namespace EquationDepth

open Mettapedia.Machines.ReadOnlyQuery

def query (avoid : List String) (space : Space) (atom : Atom) :
    MatchDepth.Query (List (Atom × Bindings)) :=
  flatTraverse space.atoms.zipIdx fun (eq, idx) =>
    match eq with
    | .expression [.symbol "=", lhs, rhs] =>
        let (lhs', rhs') := freshenEquationAvoiding avoid idx lhs rhs
        .read (.atoms atom lhs') fun matched =>
          flatTraverse matched fun qb =>
            .read (.merge qb Bindings.empty) fun merged =>
              .pure (merged.filterMap fun bindings =>
                if bindings.hasLoop then none else some (rhs', bindings))
    | _ => .pure []

theorem run_query (depth : Nat) (avoid : List String) (space : Space) (atom : Atom) :
    (run (evalMatch (depth + 1)) (query avoid space atom)).answer =
      queryEquationsAvoiding avoid space atom (depth + 1) := by
  simp only [query, run_flatTraverse, queryEquationsAvoiding]
  congr 1
  funext entry
  rcases entry with ⟨eq, idx⟩
  split <;> simp [run, run_flatTraverse, evalMatch]

end EquationDepth

def queryEquationsCovered (avoid : List String) (space : Space) (atom : Atom) : Nat → Bool
  | 0 => false
  | depth + 1 => MatchDepth.queryCovered (depth + 1) (EquationDepth.query avoid space atom)

theorem queryEquationsCovered_stable (avoid : List String) (space : Space) (atom : Atom)
    (depth extra : Nat) (covered : queryEquationsCovered avoid space atom depth = true) :
    queryEquationsAvoiding avoid space atom (depth + extra) =
      queryEquationsAvoiding avoid space atom depth := by
  cases depth with
  | zero => simp [queryEquationsCovered] at covered
  | succ depth =>
      rw [Nat.succ_add, ← EquationDepth.run_query, ← EquationDepth.run_query]
      simpa only [Nat.succ_add] using
        congrArg Mettapedia.Machines.ReadOnlyQuery.Observation.answer
          (MatchDepth.queryCovered_stable (depth + 1) extra _ covered)

/-! ## Match queries on a captured view -/

namespace Space.MatchQuery

open Mettapedia.Machines.ReadOnlyQuery

/-- The atomic selector works in a fixed view and receives the earlier
branch's bindings for scoped row selection. A failed completion certificate
is not an empty completed selection. The selector owns freshening and
narrowing of open row locals. -/
abbrev AtomicRead := Bindings → Atom → Option (List Bindings)

inductive Read where
  | atoms (incoming : Bindings) (pattern : Atom)
  | merge (hit incoming : Bindings)

abbrev Query := Program Read (Option (List Bindings)) (List Bindings)

/-- Finish the join left to right: inside each branch apply its bindings
before making the next atomic request, then merge the hit with the incoming
record. No template is evaluated in this traversal. The atomic provider,
not the outer comma form, decides how to interpret a nested pattern. -/
def conjuncts : List Atom → List Bindings → Query
  | [], frontier => .pure frontier
  | pattern :: rest, frontier =>
      bind (flatTraverse frontier fun incoming =>
        .read (.atoms incoming (incoming.applyFull pattern (incoming.resolutionFuel pattern))) fun hits =>
          flatTraverse (hits.getD []) fun hit =>
            .read (.merge hit incoming) fun merged => .pure (merged.getD [])) (conjuncts rest)

def program : Atom → Query
  | .expression (.symbol "," :: legs) => conjuncts legs [Bindings.empty]
  | pattern => .read (.atoms Bindings.empty pattern) fun hits => .pure (hits.getD [])

def read (atomic : AtomicRead) (depth : Nat) : Read → Option (List Bindings)
  | .atoms incoming pattern => atomic incoming pattern
  | .merge hit incoming =>
      if matchCovered depth (.merge hit incoming) then
        some (mergeBindings hit incoming depth)
      else none

/-- Every attempted read must be complete, including an empty read. Using
the empty list to stop a blocked branch of the dependency program never
turns that branch's missing certificate into an answer. -/
def capture (atomic : AtomicRead) (depth : Nat) (pattern : Atom) : Option (List Bindings) :=
  let observed := run (read atomic depth) (program pattern)
  if observed.reads.all (fun sampled => sampled.2.isSome) then some observed.answer else none

/-- Only the visited atomic requests have to agree. The whole adaptive
read path and the capture agree, not just their supports. -/
theorem capture_eq_of_agrees {before after : AtomicRead} (depth : Nat) (pattern : Atom)
    (same : ∀ incoming atom value,
      (.atoms incoming atom, value) ∈ (run (read before depth) (program pattern)).reads →
      after incoming atom = value) :
    capture after depth pattern = capture before depth pattern := by
  have valid : Agrees (read after depth) (run (read before depth) (program pattern)).reads := by
    rintro ⟨request,value⟩ found
    cases request with
    | atoms incoming atom => exact same incoming atom value found
    | merge hit incoming => exact run_agrees (read before depth) (program pattern) _ found
  simp only [capture, run_eq_of_agrees (read before depth) (read after depth) (program pattern) valid]

/-- A finished capture is unchanged by a larger matcher depth and a provider
that preserves completed atomic replies. This includes zero answers and
does not require certification of requests behind a failed earlier leg. -/
theorem capture_stable {before after : AtomicRead} (depth extra : Nat) (pattern : Atom)
    {answers : List Bindings}
    (extend : ∀ incoming atom rows, before incoming atom = some rows →
      after incoming atom = some rows)
    (complete : capture before depth pattern = some answers) :
    capture after (depth + extra) pattern = some answers := by
  have closed : (run (read before depth) (program pattern)).reads.all
      (fun sampled => sampled.2.isSome) = true := by
    by_contra incomplete
    simp only [capture, if_neg incomplete] at complete
    cases complete
  have valid : Agrees (read after (depth + extra)) (run (read before depth) (program pattern)).reads := by
    rintro ⟨request,value⟩ found
    have available : value.isSome = true := List.all_eq_true.mp closed _ found
    have replied := run_agrees (read before depth) (program pattern) (request,value) found
    cases value with
    | none => simp at available
    | some rows =>
      cases request with
      | atoms incoming atom => exact extend incoming atom rows replied
      | merge hit incoming =>
        have known : matchCovered depth (.merge hit incoming) = true := by
          simp only [read] at replied
          split at replied
          · assumption
          · contradiction
        have later := matchCovered_mono depth extra (.merge hit incoming) known
        have answer := matchCovered_stable depth extra (.merge hit incoming) known
        change mergeBindings hit incoming (depth + extra) = mergeBindings hit incoming depth at answer
        rw [read, if_pos later, answer]
        simpa only [read, if_pos known] using replied
  have equal := run_eq_of_agrees (read before depth) (read after (depth + extra)) (program pattern) valid
  simpa only [capture, equal] using complete

end Space.MatchQuery

end Mettapedia.Languages.MeTTa.HE
