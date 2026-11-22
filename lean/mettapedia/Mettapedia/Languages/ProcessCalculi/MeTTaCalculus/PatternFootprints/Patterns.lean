import Mettapedia.Logic.LP.UnificationRenaming
import Mettapedia.Logic.LP.Matching
import Mettapedia.Logic.LP.Semantics

/-!
# A pattern as a footprint

A location is a kind of atom in a space.  A pattern is a first-order term with
variables; a kind is a term without variables; a pattern **matches** a kind when
the kind is an instance of it (`Matches`).  The kinds a pattern matches (`kinds`)
are its footprint.  The set is usually infinite, and membership in it is decided
by the matcher of the logic-programming kernel (`decidableMatches`).

Whether two such footprints are disjoint is a question about two infinite sets.
It is answered by unification.

* `CommonInstance`: two patterns have a common instance when a substitution for
  each makes them one term.  The two substitutions are separate: a variable that
  both patterns use is not shared between them.
* `kinds_disjoint_of_not_commonInstance`: **patterns with no common instance
  match no kind in common.**  With one term without variables to put for what
  is left, the converse holds (`kinds_disjoint_iff_not_commonInstance`).
* `apart`: the test.  It renames the two patterns into two disjoint copies of
  the variables (`VariableSplit`) and asks the total unifier of the kernel.
  `apart_iff_not_commonInstance`: it answers exactly "no common instance", so it
  is sound for disjointness (`kinds_disjoint_of_apart`) and, with one term
  without variables, complete (`apart_iff_kinds_disjoint`).
* The renaming is needed.  `Controls.unify_without_renaming_unsound`: for
  `pair($x, a)` and `pair(b, $x)` the unifier asked without renaming finds no
  unifier, and both patterns match the kind `pair(b, a)`.
* An addition writes one kind.  Against it the test is matching:
  `singleton_disjoint_kinds_iff`.  Unification is needed between two patterns,
  that is, between a read of a pattern and the additions of a rule whose
  template still has variables.
* With several spaces a location is a kind in a space (`patternFootprint`), and
  two such footprints are disjoint when the spaces differ or the patterns are
  apart (`patternFootprint_disjoint_iff`).

Positive pair: `seen($x)` and `tried($x)` (`Controls.seen_tried_apart`).  Negative
pair: `seen($x)` and `seen(a)` (`Controls.seen_seenA_not_apart`).  A pair that no
comparison of heads separates and unification does: `pair($x, $x)` and
`pair(a, b)` (`Controls.diagonal_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming (rename)

variable {σ : LPSignature}

/-! ## The kinds a pattern matches -/

/-- A pattern **matches** a kind of atom when the kind is an instance of the
pattern. -/
def Matches (pattern : Term σ) (kind : GroundTerm σ) : Prop :=
  ∃ θ : Subst σ, θ.applyTerm pattern = kind.toTerm

/-- **The kinds a pattern matches**: its footprint, with a location a kind of
atom. -/
def kinds (pattern : Term σ) : Set (GroundTerm σ) :=
  {kind | Matches pattern kind}

/-- Whether a pattern matches a kind is decided by the matcher. -/
instance decidableMatches [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (pattern : Term σ) (kind : GroundTerm σ) :
    Decidable (Matches pattern kind) :=
  match result : matchTerm pattern kind with
  | .success answer => isTrue ⟨answer, matchTerm_sound pattern kind answer result⟩
  | .failure => isFalse fun ⟨θ, same⟩ => by
      obtain ⟨answer, accepted⟩ := matchTerm_complete pattern kind θ same
      rw [result] at accepted
      cases accepted

/-- So the footprint of a pattern is a set with decidable membership. -/
instance decidableMemKinds [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (pattern : Term σ) : DecidablePred (· ∈ kinds pattern) :=
  fun kind => decidableMatches pattern kind

/-- A substitution leaves a term without variables as it is. -/
theorem applyTerm_toTerm (θ : Subst σ) (kind : GroundTerm σ) :
    θ.applyTerm kind.toTerm = kind.toTerm := by
  induction kind with
  | const constant => rfl
  | app symbol arguments ih =>
      show Term.app symbol (fun position => θ.applyTerm (arguments position).toTerm) = _
      exact congrArg (Term.app symbol) (funext ih)

/-- A term without variables, as a pattern, matches itself and no other kind. -/
theorem kinds_toTerm (kind : GroundTerm σ) : kinds kind.toTerm = {kind} := by
  ext other
  constructor
  · rintro ⟨θ, same⟩
    rw [applyTerm_toTerm] at same
    exact (GroundTerm.toTerm_injective same).symm
  · rintro rfl
    exact ⟨Subst.id σ, applyTerm_toTerm _ _⟩

/-! ## Common instances -/

/-- Two patterns have a **common instance** when a substitution for each makes
them one term.  The substitutions are separate. -/
def CommonInstance (first second : Term σ) : Prop :=
  ∃ θ₁ θ₂ : Subst σ, θ₁.applyTerm first = θ₂.applyTerm second

/-- A kind that both patterns match is a common instance. -/
theorem commonInstance_of_mem_kinds {first second : Term σ} {kind : GroundTerm σ}
    (inFirst : kind ∈ kinds first) (inSecond : kind ∈ kinds second) :
    CommonInstance first second := by
  obtain ⟨θ₁, firstSame⟩ := inFirst
  obtain ⟨θ₂, secondSame⟩ := inSecond
  exact ⟨θ₁, θ₂, firstSame.trans secondSame.symm⟩

/-- **Patterns with no common instance match no kind in common.** -/
theorem kinds_disjoint_of_not_commonInstance {first second : Term σ}
    (none : ¬ CommonInstance first second) : Disjoint (kinds first) (kinds second) :=
  Set.disjoint_left.mpr fun _ inFirst inSecond =>
    none (commonInstance_of_mem_kinds inFirst inSecond)

/-- With one term without variables to put for the variables that are left, a
common instance gives a kind that both patterns match. -/
theorem exists_mem_kinds_of_commonInstance [Nonempty (GroundTerm σ)] {first second : Term σ}
    (common : CommonInstance first second) :
    ∃ kind, kind ∈ kinds first ∧ kind ∈ kinds second := by
  obtain ⟨θ₁, θ₂, same⟩ := common
  obtain ⟨filler⟩ := ‹Nonempty (GroundTerm σ)›
  let grounding : Grounding σ := fun _ => filler
  refine ⟨grounding.groundTerm (θ₁.applyTerm first), ⟨grounding.toSubst ∘ₛ θ₁, ?_⟩,
    ⟨grounding.toSubst ∘ₛ θ₂, ?_⟩⟩
  · rw [Subst.applyTerm_comp, Grounding.groundTerm_toTerm]
  · rw [Subst.applyTerm_comp, Grounding.groundTerm_toTerm, same]

/-- **Disjointness of two pattern footprints is the absence of a common
instance**, where there is a term without variables. -/
theorem kinds_disjoint_iff_not_commonInstance [Nonempty (GroundTerm σ)] {first second : Term σ} :
    Disjoint (kinds first) (kinds second) ↔ ¬ CommonInstance first second := by
  constructor
  · intro disjoint common
    obtain ⟨kind, inFirst, inSecond⟩ := exists_mem_kinds_of_commonInstance common
    exact Set.disjoint_left.mp disjoint inFirst inSecond
  · exact kinds_disjoint_of_not_commonInstance

/-- An addition of one kind against a read of a pattern: the two footprints are
disjoint exactly when the pattern does not match the kind. -/
theorem singleton_disjoint_kinds_iff {pattern : Term σ} {kind : GroundTerm σ} :
    Disjoint ({kind} : Set (GroundTerm σ)) (kinds pattern) ↔ ¬ Matches pattern kind :=
  Set.disjoint_singleton_left

/-! ## The test by unification -/

/-- **Two disjoint copies of the variables**, each with a way back. -/
structure VariableSplit (σ : LPSignature) where
  /-- The copy for the first pattern. -/
  left : σ.vars → σ.vars
  /-- The copy for the second pattern. -/
  right : σ.vars → σ.vars
  /-- Back from the first copy. -/
  leftBack : σ.vars → σ.vars
  /-- Back from the second copy. -/
  rightBack : σ.vars → σ.vars
  left_inverse : Function.LeftInverse leftBack left
  right_inverse : Function.LeftInverse rightBack right
  /-- The two copies share no variable. -/
  apart : ∀ first second, left first ≠ right second

/-- **Negative**: over one variable there are no two disjoint copies of the
variables. -/
theorem no_variableSplit_of_subsingleton [Subsingleton σ.vars] [Nonempty σ.vars] :
    IsEmpty (VariableSplit σ) :=
  ⟨fun split => by
    obtain ⟨name⟩ := ‹Nonempty σ.vars›
    exact split.apart name name (Subsingleton.elim _ _)⟩

/-- A substitution read through a renaming of the variables. -/
def renamed (θ : Subst σ) (relabel : σ.vars → σ.vars) : Subst σ :=
  fun name => θ (relabel name)

/-- A substitution applied to a renamed term is the substitution read through the
renaming, applied to the term. -/
theorem applyTerm_rename (θ : Subst σ) (relabel : σ.vars → σ.vars) (term : Term σ) :
    θ.applyTerm (rename relabel term) = (renamed θ relabel).applyTerm term :=
  (Subst.applyTerm_comp θ (fun name => .var (relabel name)) term).symm

/-- One substitution from two, along a split: the first on the first copy of the
variables, the second elsewhere. -/
def VariableSplit.join [DecidableEq σ.vars] (split : VariableSplit σ) (θ₁ θ₂ : Subst σ) :
    Subst σ :=
  fun name =>
    if split.left (split.leftBack name) = name then θ₁ (split.leftBack name)
    else θ₂ (split.rightBack name)

theorem VariableSplit.renamed_join_left [DecidableEq σ.vars] (split : VariableSplit σ)
    (θ₁ θ₂ : Subst σ) : renamed (split.join θ₁ θ₂) split.left = θ₁ := by
  funext name
  show (if split.left (split.leftBack (split.left name)) = split.left name then
    θ₁ (split.leftBack (split.left name)) else θ₂ (split.rightBack (split.left name))) = θ₁ name
  rw [split.left_inverse name, if_pos rfl]

theorem VariableSplit.renamed_join_right [DecidableEq σ.vars] (split : VariableSplit σ)
    (θ₁ θ₂ : Subst σ) : renamed (split.join θ₁ θ₂) split.right = θ₂ := by
  funext name
  show (if split.left (split.leftBack (split.right name)) = split.right name then
    θ₁ (split.leftBack (split.right name)) else θ₂ (split.rightBack (split.right name))) = θ₂ name
  rw [if_neg (split.apart _ _), split.right_inverse name]

/-- **A common instance is a unifier of the patterns renamed apart.** -/
theorem commonInstance_iff_unifiable [DecidableEq σ.vars] (split : VariableSplit σ)
    (first second : Term σ) :
    CommonInstance first second ↔
      ∃ θ : Subst σ, Unifies θ [(rename split.left first, rename split.right second)] := by
  constructor
  · rintro ⟨θ₁, θ₂, same⟩
    refine ⟨split.join θ₁ θ₂, fun pair member => ?_⟩
    rw [List.mem_singleton] at member
    subst member
    show (split.join θ₁ θ₂).applyTerm (rename split.left first) =
      (split.join θ₁ θ₂).applyTerm (rename split.right second)
    rw [applyTerm_rename, applyTerm_rename, split.renamed_join_left, split.renamed_join_right]
    exact same
  · rintro ⟨θ, unifies⟩
    have same := unifies _ (List.mem_singleton_self _)
    exact ⟨renamed θ split.left, renamed θ split.right, by
      rw [← applyTerm_rename, ← applyTerm_rename]
      exact same⟩

/-- **The test of disjointness.**  Rename the two patterns apart and ask the
total unifier; the patterns are apart when it finds no unifier. -/
def apart [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (split : VariableSplit σ) (first second : Term σ) : Bool :=
  (unifyTotal [(rename split.left first, rename split.right second)]).isNone

section Test

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- **The test answers exactly "no common instance".** -/
theorem apart_iff_not_commonInstance (split : VariableSplit σ) (first second : Term σ) :
    apart split first second = true ↔ ¬ CommonInstance first second := by
  rw [apart, Option.isNone_iff_eq_none, unifyTotal_none_iff_not_unifiable,
    commonInstance_iff_unifiable split]

/-- **The test is sound**: patterns it finds apart match no kind in common. -/
theorem kinds_disjoint_of_apart {split : VariableSplit σ} {first second : Term σ}
    (found : apart split first second = true) : Disjoint (kinds first) (kinds second) :=
  kinds_disjoint_of_not_commonInstance ((apart_iff_not_commonInstance split first second).mp found)

/-- **And complete**, where there is a term without variables: it finds apart
exactly the patterns that match no kind in common. -/
theorem apart_iff_kinds_disjoint [Nonempty (GroundTerm σ)] (split : VariableSplit σ)
    (first second : Term σ) :
    apart split first second = true ↔ Disjoint (kinds first) (kinds second) := by
  rw [apart_iff_not_commonInstance, kinds_disjoint_iff_not_commonInstance]

end Test

/-! ## A kind of atom in a space -/

/-- **The footprint of a pattern in a space**: the kinds it matches, there. -/
def patternFootprint {Space : Type*} (space : Space) (pattern : Term σ) :
    Set (Space × GroundTerm σ) :=
  {space} ×ˢ kinds pattern

/-- A kind in a space lies in the footprint when the space is that space and the
pattern matches the kind. -/
theorem mem_patternFootprint_iff {Space : Type*} {space other : Space} {pattern : Term σ}
    {kind : GroundTerm σ} :
    (other, kind) ∈ patternFootprint space pattern ↔ other = space ∧ Matches pattern kind :=
  Iff.rfl

/-- Two such footprints are disjoint when the spaces differ or the patterns
match no kind in common. -/
theorem patternFootprint_disjoint_iff {Space : Type*} {firstSpace secondSpace : Space}
    {first second : Term σ} :
    Disjoint (patternFootprint firstSpace first) (patternFootprint secondSpace second) ↔
      firstSpace ≠ secondSpace ∨ Disjoint (kinds first) (kinds second) := by
  unfold patternFootprint
  rw [Set.disjoint_prod, Set.disjoint_singleton]

/-! ## Controls -/

namespace Controls

/-- Two symbols. -/
inductive Symbol where
  | a
  | b
  deriving DecidableEq

/-- Three heads of atoms. -/
inductive Head where
  | seen
  | tried
  | pair
  deriving DecidableEq

/-- `seen` and `tried` take one argument, `pair` two. -/
def Head.arity : Head → ℕ
  | .seen => 1
  | .tried => 1
  | .pair => 2

/-- Atoms `seen(·)`, `tried(·)`, `pair(·, ·)` over two symbols, with variables
numbered. -/
abbrev atoms : LPSignature where
  constants := Symbol
  vars := ℕ
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Head
  functionArity := Head.arity

def seen (argument : Term atoms) : Term atoms := .app .seen ![argument]
def tried (argument : Term atoms) : Term atoms := .app .tried ![argument]
def pair (first second : Term atoms) : Term atoms := .app .pair ![first, second]

theorem apply_seen (θ : Subst atoms) (argument : Term atoms) :
    θ.applyTerm (seen argument) = seen (θ.applyTerm argument) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext position
  fin_cases position
  rfl

theorem apply_tried (θ : Subst atoms) (argument : Term atoms) :
    θ.applyTerm (tried argument) = tried (θ.applyTerm argument) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext position
  fin_cases position
  rfl

theorem apply_pair (θ : Subst atoms) (first second : Term atoms) :
    θ.applyTerm (pair first second) = pair (θ.applyTerm first) (θ.applyTerm second) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext position
  fin_cases position <;> rfl

theorem pair_injective {first second third fourth : Term atoms}
    (same : pair first second = pair third fourth) : first = third ∧ second = fourth := by
  have children : (![first, second] : Fin 2 → Term atoms) = ![third, fourth] := by
    injection same
  exact ⟨congrFun children 0, congrFun children 1⟩

/-- The kind `seen(a)`. -/
def seenA : GroundTerm atoms := .app .seen ![.const .a]

/-- The kind `pair(b, a)`. -/
def pairBA : GroundTerm atoms := .app .pair ![.const .b, .const .a]

instance : Nonempty (GroundTerm atoms) := ⟨.const .a⟩

theorem half_of_even (index : ℕ) : 2 * index / 2 = index := by omega

theorem half_of_odd (index : ℕ) : (2 * index + 1) / 2 = index := by omega

theorem even_ne_odd (first second : ℕ) : 2 * first ≠ 2 * second + 1 := by omega

/-- Even numbers for the first pattern, odd numbers for the second. -/
def evenOdd : VariableSplit atoms where
  left := fun index : ℕ => 2 * index
  right := fun index : ℕ => 2 * index + 1
  leftBack := fun index : ℕ => index / 2
  rightBack := fun index : ℕ => index / 2
  left_inverse := half_of_even
  right_inverse := half_of_odd
  apart := even_ne_odd

/-- The substitution that puts one symbol for every variable. -/
def always (symbol : Symbol) : Subst atoms :=
  fun _ => .const symbol

/-- **Positive, matching**: `seen($0)` matches `seen(a)`. -/
theorem seen_matches_seenA : Matches (seen (.var 0)) seenA := by
  refine ⟨always .a, ?_⟩
  rw [apply_seen]
  show Term.app _ _ = Term.app _ _
  congr 1
  funext position
  fin_cases position
  rfl

/-- **Negative, matching**: `tried($0)` does not. -/
theorem tried_not_matches_seenA : ¬ Matches (tried (.var 0)) seenA := by
  rintro ⟨θ, same⟩
  rw [apply_tried] at same
  have heads : Head.tried = Head.seen := by
    injection same
  cases heads

/-- The matcher decides both. -/
theorem matcher_decides :
    decide (Matches (seen (.var 0)) seenA) = true ∧
      decide (Matches (tried (.var 0)) seenA) = false :=
  ⟨decide_eq_true seen_matches_seenA, decide_eq_false tried_not_matches_seenA⟩

/-- **A positive pair**: `seen($0)` and `tried($0)` have no common instance; the
test finds them apart, and they match no kind in common. -/
theorem seen_tried_apart :
    ¬ CommonInstance (seen (.var 0)) (tried (.var 0)) ∧
      apart evenOdd (seen (.var 0)) (tried (.var 0)) = true ∧
      Disjoint (kinds (seen (.var 0))) (kinds (tried (.var 0))) := by
  have none : ¬ CommonInstance (seen (.var 0)) (tried (.var 0)) := by
    rintro ⟨θ₁, θ₂, same⟩
    rw [apply_seen, apply_tried] at same
    have heads : Head.seen = Head.tried := by
      injection same
    cases heads
  exact ⟨none, (apart_iff_not_commonInstance evenOdd _ _).mpr none,
    kinds_disjoint_of_not_commonInstance none⟩

/-- **A negative pair**: `seen($0)` and `seen(a)` both match the kind `seen(a)`;
they have a common instance, and the test does not find them apart. -/
theorem seen_seenA_not_apart :
    seenA ∈ kinds (seen (.var 0)) ∧ seenA ∈ kinds (seen (.const .a)) ∧
      CommonInstance (seen (.var 0)) (seen (.const .a)) ∧
      apart evenOdd (seen (.var 0)) (seen (.const .a)) = false := by
  have second : seenA ∈ kinds (seen (.const .a)) := by
    refine ⟨Subst.id atoms, ?_⟩
    rw [apply_seen]
    show Term.app _ _ = Term.app _ _
    congr 1
    funext position
    fin_cases position
    rfl
  refine ⟨seen_matches_seenA, second, commonInstance_of_mem_kinds seen_matches_seenA second, ?_⟩
  have notApart : ¬ apart evenOdd (seen (.var 0)) (seen (.const .a)) = true := fun found =>
    Set.disjoint_left.mp (kinds_disjoint_of_apart found) seen_matches_seenA second
  exact Bool.not_eq_true _ |>.mp notApart

/-- **A pair that the heads do not separate.**  `pair($0, $0)` and `pair(a, b)`
have the same head and the same number of arguments, and no common instance: the
one variable would be `a` and `b`. -/
theorem diagonal_apart :
    apart evenOdd (pair (.var 0) (.var 0)) (pair (.const .a) (.const .b)) = true ∧
      Disjoint (kinds (pair (.var 0) (.var 0))) (kinds (pair (.const .a) (.const .b))) := by
  have none : ¬ CommonInstance (pair (.var 0) (.var 0)) (pair (.const .a) (.const .b)) := by
    rintro ⟨θ₁, θ₂, same⟩
    rw [apply_pair, apply_pair] at same
    obtain ⟨first, second⟩ := pair_injective same
    have symbols : (Term.const Symbol.a : Term atoms) = Term.const Symbol.b :=
      first.symm.trans second
    have equal : Symbol.a = Symbol.b := by
      injection symbols
    cases equal
  exact ⟨(apart_iff_not_commonInstance evenOdd _ _).mpr none,
    kinds_disjoint_of_not_commonInstance none⟩

/-- **The renaming is needed.**  `pair($0, a)` and `pair(b, $0)` use one variable
name.  Asked without renaming, the unifier finds no unifier; and both patterns
match the kind `pair(b, a)`, so their footprints are not disjoint.  Renamed
apart, the test does not find them apart. -/
theorem unify_without_renaming_unsound :
    unifyTotal [(pair (.var 0) (.const .a), pair (.const .b) (.var 0))] = none ∧
      pairBA ∈ kinds (pair (.var 0) (.const .a)) ∧ pairBA ∈ kinds (pair (.const .b) (.var 0)) ∧
      apart evenOdd (pair (.var 0) (.const .a)) (pair (.const .b) (.var 0)) = false := by
  have first : pairBA ∈ kinds (pair (.var 0) (.const .a)) := by
    refine ⟨always .b, ?_⟩
    rw [apply_pair]
    show Term.app _ _ = Term.app _ _
    congr 1
    funext position
    fin_cases position <;> rfl
  have second : pairBA ∈ kinds (pair (.const .b) (.var 0)) := by
    refine ⟨always .a, ?_⟩
    rw [apply_pair]
    show Term.app _ _ = Term.app _ _
    congr 1
    funext position
    fin_cases position <;> rfl
  refine ⟨?_, first, second, ?_⟩
  · refine (unifyTotal_none_iff_not_unifiable (σ := atoms) _).mpr ?_
    rintro ⟨θ, solves⟩
    have same := solves _ (List.mem_singleton_self _)
    rw [apply_pair, apply_pair] at same
    obtain ⟨left, right⟩ := pair_injective same
    have symbols : (Term.const Symbol.b : Term atoms) = Term.const Symbol.a :=
      left.symm.trans right.symm
    have equal : Symbol.b = Symbol.a := by
      injection symbols
    cases equal
  · have notApart :
        ¬ apart evenOdd (pair (.var 0) (.const .a)) (pair (.const .b) (.var 0)) = true :=
      fun found => Set.disjoint_left.mp (kinds_disjoint_of_apart found) first second
    exact Bool.not_eq_true _ |>.mp notApart

/-- **Positive, the join of two substitutions**: read on the first copy of the
variables it is the first.  **Negative**: read on the second copy it is not; there
it is the second. -/
theorem join_instances :
    renamed (evenOdd.join (always .a) (always .b)) evenOdd.left = always .a ∧
      renamed (evenOdd.join (always .a) (always .b)) evenOdd.right ≠ always .a := by
  refine ⟨evenOdd.renamed_join_left _ _, ?_⟩
  rw [evenOdd.renamed_join_right]
  intro same
  have symbols : (Term.const Symbol.b : Term atoms) = Term.const Symbol.a :=
    congrFun same (0 : ℕ)
  have equal : Symbol.b = Symbol.a := by
    injection symbols
  cases equal

/-- **Positive, the footprint of a pattern in a space**: the kind `seen(a)` in
that space.  **Negative**: the same kind in another space. -/
theorem patternFootprint_instances :
    (true, seenA) ∈ patternFootprint true (seen (.var 0)) ∧
      (false, seenA) ∉ patternFootprint true (seen (.var 0)) :=
  ⟨mem_patternFootprint_iff.mpr ⟨rfl, seen_matches_seenA⟩,
    fun inside => absurd (mem_patternFootprint_iff.mp inside).1 (by decide)⟩

/-- **Positive, a kind in a space**: one pattern in two spaces has two disjoint
footprints. -/
theorem two_spaces_disjoint :
    Disjoint (patternFootprint true (seen (.var 0))) (patternFootprint false (seen (.var 0))) :=
  patternFootprint_disjoint_iff.mpr (Or.inl (by decide))

/-- **Negative, a kind in a space**: in one space the footprint is not disjoint
from itself. -/
theorem one_space_not_disjoint :
    ¬ Disjoint (patternFootprint true (seen (.var 0))) (patternFootprint true (seen (.var 0))) := by
  rw [patternFootprint_disjoint_iff]
  rintro (different | disjoint)
  · exact different rfl
  · exact Set.disjoint_left.mp disjoint seen_matches_seenA seen_matches_seenA

end Controls

#print axioms applyTerm_toTerm
#print axioms kinds_toTerm
#print axioms commonInstance_of_mem_kinds
#print axioms kinds_disjoint_of_not_commonInstance
#print axioms exists_mem_kinds_of_commonInstance
#print axioms kinds_disjoint_iff_not_commonInstance
#print axioms singleton_disjoint_kinds_iff
#print axioms commonInstance_iff_unifiable
#print axioms apart_iff_not_commonInstance
#print axioms kinds_disjoint_of_apart
#print axioms apart_iff_kinds_disjoint
#print axioms no_variableSplit_of_subsingleton
#print axioms mem_patternFootprint_iff
#print axioms patternFootprint_disjoint_iff
#print axioms Controls.join_instances
#print axioms Controls.patternFootprint_instances
#print axioms Controls.seen_matches_seenA
#print axioms Controls.tried_not_matches_seenA
#print axioms Controls.matcher_decides
#print axioms Controls.seen_tried_apart
#print axioms Controls.seen_seenA_not_apart
#print axioms Controls.diagonal_apart
#print axioms Controls.unify_without_renaming_unsound
#print axioms Controls.two_spaces_disjoint
#print axioms Controls.one_space_not_disjoint

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints
