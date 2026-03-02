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

open Mettapedia.Languages.MeTTa.Core (Atom)

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

/-! ## Pattern matching -/

/-- Try to match a single pattern atom `pat` against a concrete atom `conc`,
    extending substitution `σ`.  Returns the extended substitution on success,
    `none` on failure.

    This is a SOUND-BUT-INCOMPLETE match function: it correctly handles variable
    binding, symbols, and grounded atoms.  Expression patterns (structural/nested
    atoms) are NOT matched here — they would require mutual/well-founded recursion
    and `sizeOf pat` termination which blocks definitional reducibility.  For MORK
    bridge-theorem purposes, flat patterns suffice.

    TODO: Full expression matching via `termination_by sizeOf pat` once Lean's
    kernel-level `decreasing_by` can prove `p ∈ ps → sizeOf p < sizeOf (.expression ps)`. -/
def matchAtom (σ : Subst) (pat conc : Atom) : Option Subst :=
  match pat, conc with
  | .var v, a =>
    match σ.lookup v with
    | some a' => if a == a' then some σ else none
    | none    => some ((v, a) :: σ)
  | .symbol s, .symbol t     => if s == t then some σ else none
  | .grounded g, .grounded h => if g == h then some σ else none
  | _, _ => none   -- expression patterns: see TODO above

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

/-- Apply all sinks of a template to a space. -/
def applySinks (s : Space) (σ : Subst) (tmpl : Template) : Space :=
  tmpl.sinks.foldl (applySink · σ) s

/-! ## Rule firing -/

/-- All possible spaces that result from firing rule `r` in space `s`.
    Non-determinism arises from multiple matching positions in the space. -/
noncomputable def fireRule (s : Space) (r : ExecRule) : List Space :=
  (matchPattern [] s r.pat).map fun (σ, _consumed) =>
    applySinks s σ r.tmpl

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
