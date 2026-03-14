import Mettapedia.Languages.ProcessCalculi.MORK.Syntax
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# MORK: Space Semantics

A MORK `Space` is a finite set of ground atoms (a `PathMap<()>` in the Rust
implementation, but modelled here as `Finset Atom` for tractable formalization).

## Exec-rule firing

An exec rule fires in a space `s` when:
1. Every atom in the pattern, after variable binding, is present in `s`.
2. The template sinks add/remove atoms according to the substitution.

## Warning: Specification vs. Implementation

This formalization captures the *abstract behaviour* of MORK as documented in
`mork_backend.rs` and the MORK design notes. The Rust implementation is
authoritative; this file models the INTENDED semantics. Canary theorems in
`MORKCommBridge.lean` will flag divergences when the spec changes.

## Variable binding

We use first-order (non-unification) pattern matching:
- `Atom.var v` in a pattern position binds variable `v` to the corresponding
  ground atom found in the space.
- Ground atoms in the pattern must match exactly.

## Computability note

`matchOneInSpace` and `matchPattern` are `noncomputable` because they use
`Finset.toList` which has no kernel-computable code.  The `fireRule` function
is also `noncomputable`.  We reason about them abstractly.

## Canary note

Computational canary tests are not `rfl`-based here because:
- `String.BEq` is backed by a C++ native implementation and does not reduce
  definitionally in the kernel.
- Lean 4's well-founded recursion wrappers also prevent kernel reduction.
Type-level canaries (`#check`) confirm the API is correctly typed.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Space type -/

/-- A MORK space is a finite set of ground atoms.
    (PathMap<()> in Rust, modelled as Finset for tractable reasoning.) -/
abbrev Space := Finset Atom

/-! ## Variable substitution -/

/-- A substitution maps variable names to ground atoms. -/
abbrev Subst := List (String × Atom)

/-- Look up a variable in a substitution (first match wins). -/
def Subst.lookup (σ : Subst) (v : String) : Option Atom :=
  σ.find? (fun p => p.1 == v) |>.map Prod.snd

/-! ## Atom helpers -/

/-- Check if an atom is ground (contains no variables).
    Uses `where`-clause structural recursion (cf. `Atom.beq` in Atom.lean). -/
def isGroundAtom : Atom → Bool
  | .var _         => false
  | .symbol _      => true
  | .grounded _    => true
  | .expression es => isGroundList es
where
  isGroundList : List Atom → Bool
    | []      => true
    | a :: as => isGroundAtom a && isGroundList as

/-- Apply a substitution to an atom; replaces variables.
    Uses `where`-clause structural recursion (cf. `Atom.beq` in Atom.lean). -/
def applySubst (σ : Subst) : Atom → Atom
  | .var v         => (σ.lookup v).getD (.var v)
  | .symbol s      => .symbol s
  | .grounded g    => .grounded g
  | .expression es => .expression (applySubstList σ es)
where
  applySubstList (σ : Subst) : List Atom → List Atom
    | []      => []
    | a :: as => applySubst σ a :: applySubstList σ as

/-! ## Free variables and freshness -/

/-- Collect all variable names occurring in an atom. -/
def atomFreeVars : Atom → List String
  | .var x         => [x]
  | .symbol _      => []
  | .grounded _    => []
  | .expression es => atomFreeVarsList es
where
  atomFreeVarsList : List Atom → List String
    | []      => []
    | a :: as => atomFreeVars a ++ atomFreeVarsList as

/-- Check if variable `v` does NOT occur free in atom `a`. -/
def isAtomFresh (v : String) (a : Atom) : Bool :=
  !(atomFreeVars a).contains v

/-! ## Source guards -/

/-- Check a single guard against a substitution.
    Guards return `Bool` — they never modify the substitution.

    For `.freshness x pat`:
    1. Resolve `x` through the substitution (if bound to a `.var y`, use `y`;
       if bound to a non-variable, fail; if unbound, use `x` literally).
    2. Apply the substitution to `pat`.
    3. Check that the resolved variable name does not occur free in the result. -/
def matchSourceGuard (σ : Subst) : SourceGuard → Bool
  | .freshness x pat =>
    let resolvedX := match σ.lookup x with
      | some (.var y) => some y
      | some _        => none
      | none          => some x
    match resolvedX with
    | some v => isAtomFresh v (applySubst σ pat)
    | none   => false

/-- Check that all guards pass for a given substitution. -/
def matchSourceGuards (σ : Subst) (guards : List SourceGuard) : Bool :=
  guards.all (matchSourceGuard σ)

/-! ## Pattern matching -/

/-- Try to match a single pattern atom `pat` against a concrete atom `conc`,
    extending substitution `σ`.  Returns the extended substitution on success,
    `none` on failure.

    Handles all atom constructors including expression patterns (structural/nested
    atoms) via `where`-clause mutual recursion. -/
def matchAtom (σ : Subst) (pat conc : Atom) : Option Subst :=
  match pat, conc with
  | .var v, a =>
    match σ.lookup v with
    | some a' => if a == a' then some σ else none
    | none    => some ((v, a) :: σ)
  | .symbol s, .symbol t     => if s == t then some σ else none
  | .grounded g, .grounded h => if g == h then some σ else none
  | .expression ps, .expression cs => matchAtomList σ ps cs
  | _, _ => none
where
  matchAtomList (σ : Subst) : List Atom → List Atom → Option Subst
    | [], [] => some σ
    | p :: ps, c :: cs =>
      match matchAtom σ p c with
      | some σ' => matchAtomList σ' ps cs
      | none => none
    | _, _ => none

/-- Try to match a pattern atom against ANY atom in the space,
    returning all consistent (σ, concrete-atom) pairs. -/
noncomputable def matchOneInSpace (σ : Subst) (pat : Atom) (s : Space) :
    List (Subst × Atom) :=
  s.toList.filterMap fun a =>
    (matchAtom σ pat a).map (·, a)

/-- Try to match ALL pattern atoms simultaneously against the space.
    Returns list of (substitution, consumed-atoms) pairs. -/
noncomputable def matchPattern (σ : Subst) (s : Space) (p : Pattern) :
    List (Subst × Finset Atom) :=
  let rec go : List Atom → Subst → Finset Atom → List (Subst × Finset Atom)
    | [], σ', consumed => [(σ', consumed)]
    | pat :: rest, σ', consumed =>
        let available := s \ consumed
        (matchOneInSpace σ' pat available).flatMap fun (σ'', a) =>
          go rest σ'' (consumed ∪ {a})
  go p.atoms σ ∅

/-! ## Sink application -/

/-- Apply a single sink to a space under substitution `σ`. -/
def applySink (s : Space) (σ : Subst) (sink : Sink) : Space :=
  match sink with
  | .add a    =>
    let a' := applySubst σ a
    if isGroundAtom a' then s ∪ {a'} else s
  | .remove a =>
    s.erase (applySubst σ a)
  | .head a   =>
    -- Idempotent add: same as add in the Finset model (union is idempotent).
    -- The distinction matters in the computable evaluator (list-level).
    let a' := applySubst σ a
    if isGroundAtom a' then s ∪ {a'} else s

/-- Apply all sinks of a template to a space. -/
def applySinks (s : Space) (σ : Subst) (tmpl : Template) : Space :=
  tmpl.sinks.foldl (applySink · σ) s

/-! ## Rule firing -/

/-- All possible spaces that result from firing rule `r` in space `s`.
    Non-determinism arises from multiple matching positions in the space. -/
noncomputable def fireRule (s : Space) (r : ExecRule) : List Space :=
  (matchPattern [] s r.pat).map fun (σ, _consumed) =>
    applySinks s σ r.tmpl

/-! ## Source-aware matching -/

/-- Evaluate a single `SourceFactor` against a space.
    Returns list of (extended substitution, consumed atom) pairs.

    - `btm pat`: match `pat` against the available space (same as compat)
    - `eqConstraint pat witness`: substitute current bindings into `pat`,
      check if the result exists in the space, and if so match `witness`
      against the found atom (typically binding `witness` to it).
    - `neqConstraint pat witness`: substitute current bindings into `pat`,
      REMOVE the result from the space, then match `witness` against
      each remaining atom (inequality/exclusion filter). -/
noncomputable def matchSourceFactor (σ : Subst) (s : Space) (src : SourceFactor) :
    List (Subst × Atom) :=
  match src with
  | .btm pat => matchOneInSpace σ pat s
  | .eqConstraint pat witness =>
    let target := applySubst σ pat
    if target ∈ s then
      match matchAtom σ witness target with
      | some σ' => [(σ', target)]
      | none => []
    else []
  | .neqConstraint pat witness =>
    let target := applySubst σ pat
    let remaining := s.erase target
    matchOneInSpace σ witness remaining

/-- Match a list of explicit source factors against a space.
    Like `matchPattern`, threads substitution through factors and tracks
    consumed atoms to prevent double-matching. -/
noncomputable def matchSourceFactors (σ : Subst) (s : Space)
    (factors : List SourceFactor) : List (Subst × Finset Atom) :=
  let rec go : List SourceFactor → Subst → Finset Atom →
      List (Subst × Finset Atom)
    | [], σ', consumed => [(σ', consumed)]
    | src :: rest, σ', consumed =>
        let available := s \ consumed
        (matchSourceFactor σ' available src).flatMap fun (σ'', a) =>
          go rest σ'' (consumed ∪ {a})
  go factors σ ∅

/-- Match an `InputSpec` against a space.
    Dispatches to `matchPattern` for compat mode or
    `matchSourceFactors` for explicit mode. -/
noncomputable def matchInputSpec (σ : Subst) (s : Space)
    (input : InputSpec) : List (Subst × Finset Atom) :=
  match input with
  | .compat pat => matchPattern σ s pat
  | .explicit factors => matchSourceFactors σ s factors

/-- Fire a `SourceExecRule` in a space.
    After matching the input specification, any source guards are checked
    as substitution-level filters before applying sinks. -/
noncomputable def fireSourceRule (s : Space) (r : SourceExecRule) : List Space :=
  ((matchInputSpec [] s r.input).filter fun (σ, _) =>
    matchSourceGuards σ r.guards).map fun (σ, _consumed) =>
    applySinks s σ r.tmpl

/-- When a source rule has no guards, `fireSourceRule` is just
    `matchInputSpec` followed by `applySinks` (no filtering). -/
private theorem matchSourceGuards_nil (σ : Subst) : matchSourceGuards σ [] = true := by
  simp [matchSourceGuards, List.all_nil]

private theorem filter_matchSourceGuards_nil {l : List (Subst × Finset Atom)} :
    l.filter (fun (σ, _) => matchSourceGuards σ []) = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    rw [matchSourceGuards_nil]; simp [ih]

theorem fireSourceRule_no_guards (s : Space) (r : SourceExecRule)
    (hg : r.guards = []) :
    fireSourceRule s r =
      (matchInputSpec [] s r.input).map fun (σ, _consumed) =>
        applySinks s σ r.tmpl := by
  simp only [fireSourceRule, hg, filter_matchSourceGuards_nil]

/-- `fireSourceRule` on a compat-mode rule agrees with `fireRule`. -/
theorem fireSourceRule_compat (s : Space) (r : ExecRule) :
    fireSourceRule s r.toSourceRule = fireRule s r := by
  simp only [fireSourceRule, fireRule, ExecRule.toSourceRule, matchInputSpec,
    filter_matchSourceGuards_nil]

/-! ## Structural lemmas -/

/-- `applySink (.add a)` with a fully ground atom increases space by 1 (if absent). -/
theorem applySink_add_card (s : Space) (σ : Subst) (a : Atom)
    (hg : isGroundAtom (applySubst σ a) = true) (hna : applySubst σ a ∉ s) :
    Finset.card (applySink s σ (.add a)) = Finset.card s + 1 := by
  simp only [applySink, hg, ite_true]
  rw [Finset.card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left]; exact fun h => hna h

/-- `applySink (.remove a)` decreases space by 1 (if present). -/
theorem applySink_remove_card (s : Space) (σ : Subst) (a : Atom)
    (hm : applySubst σ a ∈ s) :
    Finset.card (applySink s σ (.remove a)) = Finset.card s - 1 := by
  simp only [applySink]
  exact Finset.card_erase_of_mem hm

/-- `applySinks` on empty template is identity. -/
theorem applySinks_empty (s : Space) (σ : Subst) :
    applySinks s σ ⟨[]⟩ = s := rfl

/-- Applying a template that only adds keeps original atoms. -/
theorem applySink_add_mem (s : Space) (σ : Subst) (a b : Atom)
    (hm : b ∈ s) :
    b ∈ applySink s σ (.add a) := by
  simp only [applySink]
  split_ifs with hg
  · exact Finset.mem_union_left _ hm
  · exact hm

/-- Applying a head-sink keeps original atoms (same as add in Finset model). -/
theorem applySink_head_mem (s : Space) (σ : Subst) (a b : Atom)
    (hm : b ∈ s) :
    b ∈ applySink s σ (.head a) := by
  simp only [applySink]
  split_ifs with hg
  · exact Finset.mem_union_left _ hm
  · exact hm

/-! ## Substitution extension -/

/-- `matchAtom` only extends the substitution: existing bindings are preserved.
    This is the key structural invariant of first-order pattern matching. -/
theorem matchAtom_extends (σ : Subst) (pat conc : Atom) (σ' : Subst)
    (h : matchAtom σ pat conc = some σ')
    (v : String) (a : Atom) (hva : (v, a) ∈ σ) :
    (v, a) ∈ σ' := by
  match pat, conc with
  | .var w, b =>
    simp only [matchAtom] at h
    cases heq : σ.lookup w with
    | some a' =>
      rw [heq] at h; simp only at h
      split_ifs at h; simp_all
    | none =>
      rw [heq] at h; simp only at h
      cases h; exact List.mem_cons_of_mem _ hva
  | .symbol s, .symbol t =>
    simp only [matchAtom] at h
    split_ifs at h; simp_all
  | .grounded g, .grounded k =>
    simp only [matchAtom] at h
    split_ifs at h; simp_all
  | .expression ps, .expression cs =>
    simp only [matchAtom] at h
    exact matchAtomList_extends σ ps cs σ' h v a hva
  | .symbol _, .var _ => simp [matchAtom] at h
  | .symbol _, .grounded _ => simp [matchAtom] at h
  | .symbol _, .expression _ => simp [matchAtom] at h
  | .grounded _, .var _ => simp [matchAtom] at h
  | .grounded _, .symbol _ => simp [matchAtom] at h
  | .grounded _, .expression _ => simp [matchAtom] at h
  | .expression _, .var _ => simp [matchAtom] at h
  | .expression _, .symbol _ => simp [matchAtom] at h
  | .expression _, .grounded _ => simp [matchAtom] at h
where
  matchAtomList_extends (σ : Subst) (pats concs : List Atom) (σ' : Subst)
      (h : matchAtom.matchAtomList σ pats concs = some σ')
      (v : String) (a : Atom) (hva : (v, a) ∈ σ) :
      (v, a) ∈ σ' := by
    match pats, concs with
    | [], [] => simp [matchAtom.matchAtomList] at h; rw [← h]; exact hva
    | [], _ :: _ => simp [matchAtom.matchAtomList] at h
    | _ :: _, [] => simp [matchAtom.matchAtomList] at h
    | p :: ps, c :: cs =>
      simp only [matchAtom.matchAtomList] at h
      cases heq : matchAtom σ p c with
      | none => rw [heq] at h; simp at h
      | some σ'' =>
        rw [heq] at h
        have hext := matchAtom_extends σ p c σ'' heq v a hva
        exact matchAtomList_extends σ'' ps cs σ' h v a hext

/-! ## matchOneInSpace membership -/

/-- If `a ∈ s` and `matchAtom σ pat a = some σ'`, then `(σ', a)` appears
    in `matchOneInSpace σ pat s`.  This is the key helper for proving
    forward soundness of `cmatchPattern` vs `matchPattern`. -/
theorem matchOneInSpace_mem (σ : Subst) (pat : Atom) (s : Space) (a : Atom)
    (ha : a ∈ s) (σ' : Subst) (hm : matchAtom σ pat a = some σ') :
    (σ', a) ∈ matchOneInSpace σ pat s := by
  unfold matchOneInSpace
  rw [List.mem_filterMap]
  exact ⟨a, Finset.mem_toList.mpr ha, by simp [hm]⟩

/-- If `(σ', a) ∈ matchOneInSpace σ pat s`, then `a ∈ s` and
    `matchAtom σ pat a = some σ'`.  Reverse of `matchOneInSpace_mem`. -/
theorem matchOneInSpace_spec (σ : Subst) (pat : Atom) (s : Space)
    (σ' : Subst) (a : Atom)
    (h : (σ', a) ∈ matchOneInSpace σ pat s) :
    a ∈ s ∧ matchAtom σ pat a = some σ' := by
  unfold matchOneInSpace at h
  rw [List.mem_filterMap] at h
  obtain ⟨b, hb_mem, hb_map⟩ := h
  simp only [Option.map_eq_some_iff] at hb_map
  obtain ⟨σ'', hm, heq⟩ := hb_map
  cases heq
  exact ⟨Finset.mem_toList.mp hb_mem, hm⟩

/-! ## Canary tests -/

section CanaryTests

-- API types typecheck
#check @matchAtom
#check @applySubst
#check @isGroundAtom
#check @matchPattern
#check @fireRule
#check @applySinks

-- Sink predicates (Syntax.lean)
example : (mkAdd (.symbol "x")).isAdd = true := rfl
example : (mkRemove (.symbol "x")).isRemove = true := rfl

-- applySinks_empty works
example (s : Space) (σ : Subst) : applySinks s σ ⟨[]⟩ = s := rfl

end CanaryTests

end Mettapedia.Languages.ProcessCalculi.MORK
