import Mettapedia.Languages.MeTTa.HE.Types

/-!
# Human-grounded HE match and merge specification

This file formalizes the mutually recursive `match_atoms`, `merge_bindings`,
`add_var_binding`, and `add_var_equality` clauses from the published HE MeTTa
specification.  It is deliberately independent of both executable matchers:
none of the relations below mentions HE's `matchAtoms` / `mergeBindings` or
LeaTTa's matcher / merge functions.

The published text leaves two boundaries abstract:

* grounded atoms may provide a host-defined custom matcher;
* the final matcher filter rejects "variable loops" without defining that
  predicate.

`Parameters` exposes exactly those boundaries.  A conformance theorem must
select a concrete admissibility predicate and grounded-matcher interpretation;
they are not silently inherited from either implementation.

The text also says that a binding is a *set* of relations whose order does not
matter, while presenting merge as a fold.  `MergeRel` therefore quantifies over
every permutation of the right-hand constraints.  Concrete list chronology is
not part of the declarative judgment.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- The two host-defined boundaries left abstract by the human specification. -/
structure Parameters where
  /-- Whether this grounded value supplies the custom matcher tested by the
  ordered `elif` chain in `match_atoms`. -/
  hasCustomMatcher : GroundedValue → Prop
  /-- One possible result returned by that grounded value's custom matcher. -/
  customMatch : GroundedValue → Atom → Bindings → Prop
  /-- The human specification's final "doesn't have variable loops" filter. -/
  admissible : Bindings → Prop

/-- Is this atom a variable?  Kept local so the specification does not import
the previous hybrid declarative/executable matcher. -/
def isVariableB : Atom → Bool
  | .var _ => true
  | _ => false

/-- Does this atom carry the left-priority custom matcher from the human
`match_atoms` `elif` chain? -/
def Parameters.atomHasCustomMatcher (p : Parameters) : Atom → Prop
  | .grounded g => p.hasCustomMatcher g
  | _ => False

/-- Neutral syntax for the two relation forms in a human binding set. -/
inductive Constraint where
  | value (varName : String) (value : Atom)
  | equality (left right : String)
  deriving Repr, DecidableEq

/-- Expose a binding record as an unordered collection of human constraints.
The surrounding merge relation quotients the concrete concatenation order by
`List.Perm`. -/
def constraints (b : Bindings) : List Constraint :=
  (b.assignments.map
      (fun relation => Constraint.value relation.1 relation.2) ++
    b.equalities.map
      (fun relation => Constraint.equality relation.1 relation.2)).eraseDups

/-- All values in a nonempty list are syntactically equal to its head.  Unequal
values are not rejected: the recursive reconciliation rules match them. -/
def ValuesAgree : List Atom → Prop
  | [] => True
  | first :: rest => ∀ value ∈ rest, value = first

/-! ## Semantic loop boundary

The published text does not define "variable loop".  The relation below gives
it a representation-independent meaning: assignments induce directed
dependencies between equality classes, and a binding is admissible exactly
when that dependency graph is acyclic.  A bare assignment to a *different*
variable already in the same equality class is a redundant alias, not a
dependency; a direct self-assignment and every occurrence underneath an
expression remain genuine dependencies.
-/

/-- A variable occurs in an atom.  This is a relation rather than an executable
scan so it can be used directly in the declarative dependency graph. -/
inductive AtomOccurs : Atom → String → Prop where
  | var (name : String) : AtomOccurs (.var name) name
  | expression {atoms : List Atom} {atom : Atom} {name : String} :
      atom ∈ atoms → AtomOccurs atom name →
      AtomOccurs (.expression atoms) name

/-- One proper assignment dependency between equality classes. -/
def ClassDepends (bindings : Bindings) (source target : String) : Prop :=
  ∃ key value dependency,
    (key, value) ∈ bindings.assignments ∧
    source ∈ bindings.eqClass key ∧
    AtomOccurs value dependency ∧
    target ∈ bindings.eqClass dependency ∧
    ¬(value = .var dependency ∧ key ≠ dependency ∧
      dependency ∈ bindings.eqClass key)

/-- Human matcher admissibility: the class-level value-dependency graph has no
directed cycle. -/
def SemanticLoopFree (bindings : Bindings) : Prop :=
  ∀ name, ¬Relation.TransGen (ClassDepends bindings) name name

private theorem transGen_false_of_no_step {α : Type} {relation : α → α → Prop}
    (hstep : ∀ left right, ¬relation left right) :
    ∀ left right, ¬Relation.TransGen relation left right := by
  intro left right hreach
  induction hreach with
  | single h => exact hstep _ _ h
  | tail _ h ih => exact hstep _ _ h

/-- A binding record with no value assignments cannot contain a semantic value
dependency cycle; equality edges alone merely form classes. -/
theorem semanticLoopFree_of_assignments_nil {bindings : Bindings}
    (hassignments : bindings.assignments = []) :
    SemanticLoopFree bindings := by
  intro name
  apply transGen_false_of_no_step
  intro source target hdepends
  rcases hdepends with
    ⟨key, value, dependency, hmem, _, _, _, _⟩
  rw [hassignments] at hmem
  simp at hmem

@[simp] theorem semanticLoopFree_empty : SemanticLoopFree Bindings.empty :=
  semanticLoopFree_of_assignments_nil rfl

/-- A single value assignment is acyclic when its key does not occur in the
assigned atom.  Other variables in the value have no outgoing assignment edge
in this singleton record, so no longer cycle can arise. -/
theorem semanticLoopFree_single_assignment {key : String} {value : Atom}
    (hoccurs : ¬AtomOccurs value key) :
    SemanticLoopFree (Bindings.empty.assign key value) := by
  have hedge : ∀ source target,
      ClassDepends (Bindings.empty.assign key value) source target →
        source = key ∧ AtomOccurs value target := by
    intro source target hdepends
    rcases hdepends with
      ⟨storedKey, storedValue, dependency, hstored,
        hsource, hdependency, htarget, _⟩
    have hstoredEq : storedKey = key ∧ storedValue = value := by
      simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
        Bindings.lookup] using hstored
    rcases hstoredEq with ⟨hkey, hvalue⟩
    subst storedKey
    subst storedValue
    have hsourceEq : source = key := by
      simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
        Bindings.lookup, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.eqStep] using hsource
    have htargetEq : target = dependency := by
      simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
        Bindings.lookup, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.eqStep] using htarget
    exact ⟨hsourceEq, htargetEq ▸ hdependency⟩
  intro name hcycle
  have hreach : ∀ {source target},
      Relation.TransGen
          (ClassDepends (Bindings.empty.assign key value)) source target →
        source = key ∧ AtomOccurs value target := by
    intro source target hpath
    induction hpath with
    | single h => exact hedge _ _ h
    | tail _ h ih => exact ⟨ih.1, (hedge _ _ h).2⟩
  have hfinal := hreach hcycle
  rw [hfinal.1] at hfinal
  exact hoccurs hfinal.2

mutual

/-- A binding set is one result permitted by the human `match_atoms` relation.
Every constructor carries the final admissibility/loop-filter premise from the
published algorithm. -/
inductive MatchRel (p : Parameters) : Atom → Atom → Bindings → Prop where
  /-- Equal symbols match with empty bindings. -/
  | symSym (symbol : String)
      (hadmissible : p.admissible Bindings.empty) :
      MatchRel p (.symbol symbol) (.symbol symbol) Bindings.empty
  /-- Variable/variable matching records equality rather than an oriented
  assignment. -/
  | varVar (left right : String)
      (hadmissible : p.admissible
        (Bindings.empty.addEquality left right)) :
      MatchRel p (.var left) (.var right)
        (Bindings.empty.addEquality left right)
  /-- A left variable is assigned the non-variable atom. -/
  | varNonVar {varName : String} {value : Atom}
      (hnonvar : isVariableB value = false)
      (hadmissible : p.admissible (Bindings.empty.assign varName value)) :
      MatchRel p (.var varName) value
        (Bindings.empty.assign varName value)
  /-- Matching is two-sided: a right variable receives the left non-variable. -/
  | nonVarVar {value : Atom} {varName : String}
      (hnonvar : isVariableB value = false)
      (hadmissible : p.admissible (Bindings.empty.assign varName value)) :
      MatchRel p value (.var varName)
        (Bindings.empty.assign varName value)
  /-- Expressions match pointwise, threading the declarative merge relation. -/
  | expression {left right : List Atom} {out : Bindings}
      (hitems : MatchListAccRel p left right Bindings.empty out)
      (hadmissible : p.admissible out) :
      MatchRel p (.expression left) (.expression right) out
  /-- The left grounded custom matcher has priority after the variable and
  expression cases in the published `elif` chain. -/
  | groundedLeftCustom {grounded : GroundedValue} {right : Atom}
      {out : Bindings}
      (hright : isVariableB right = false)
      (hcustom : p.hasCustomMatcher grounded)
      (hmatch : p.customMatch grounded right out)
      (hadmissible : p.admissible out) :
      MatchRel p (.grounded grounded) right out
  /-- The right custom matcher is tried only when the left side did not already
  provide one. -/
  | groundedRightCustom {left : Atom} {grounded : GroundedValue}
      {out : Bindings}
      (hleft : isVariableB left = false)
      (hleftNoCustom : ¬p.atomHasCustomMatcher left)
      (hcustom : p.hasCustomMatcher grounded)
      (hmatch : p.customMatch grounded left out)
      (hadmissible : p.admissible out) :
      MatchRel p left (.grounded grounded) out
  /-- Published grounded/grounded fallback: if neither side supplies a custom
  matcher, the match succeeds with empty bindings.  This intentionally records
  the human clause rather than replacing it by an implementation equality test. -/
  | groundedFallback {left right : GroundedValue}
      (hleft : ¬p.hasCustomMatcher left)
      (hright : ¬p.hasCustomMatcher right)
      (hadmissible : p.admissible Bindings.empty) :
      MatchRel p (.grounded left) (.grounded right) Bindings.empty

/-- Pointwise expression matching with a live declarative binding accumulator. -/
inductive MatchListAccRel (p : Parameters) :
    List Atom → List Atom → Bindings → Bindings → Prop where
  | nil {seed : Bindings} : MatchListAccRel p [] [] seed seed
  | cons {left right : Atom} {lefts rights : List Atom}
      {seed matched next out : Bindings} :
      MatchRel p left right matched →
      MergeRel p seed matched next →
      MatchListAccRel p lefts rights next out →
      MatchListAccRel p (left :: lefts) (right :: rights) seed out

/-- Add one `$variable <- value` constraint.  A fresh class records the value;
a coherent valued class either changes nothing or recursively matches the new
value; an already-incoherent class reconciles every value together. -/
inductive AddVarBindingRel (p : Parameters) :
    Bindings → String → Atom → Bindings → Prop where
  | fresh {bindings : Bindings} {varName : String} {value : Atom}
      (hvalues : bindings.classValues varName = []) :
      AddVarBindingRel p bindings varName value
        (bindings.assign varName value)
  | same {bindings : Bindings} {varName : String} {value first : Atom}
      {rest : List Atom} :
      (hvalues : (first :: rest).Perm (bindings.classValues varName)) →
      ValuesAgree (first :: rest) →
      value = first →
      AddVarBindingRel p bindings varName value bindings
  | conflict {bindings : Bindings} {varName : String} {value first : Atom}
      {rest : List Atom} {matched out : Bindings} :
      (hvalues : (first :: rest).Perm (bindings.classValues varName)) →
      ValuesAgree (first :: rest) →
      value ≠ first →
      MatchRel p first value matched →
      MergeRel p bindings matched out →
      AddVarBindingRel p bindings varName value out
  | reconcile {bindings : Bindings} {varName : String} {value first : Atom}
      {rest : List Atom} {matched out : Bindings} :
      (hvalues : (first :: rest).Perm (bindings.classValues varName)) →
      ¬ValuesAgree (first :: rest) →
      MatchListAccRel p
        (List.replicate (rest.length + 1) first)
        (rest ++ [value]) Bindings.empty matched →
      MergeRel p bindings matched out →
      AddVarBindingRel p bindings varName value out

/-- Add `$left = $right`.  The equality is retained before reconciling class
values.  This repairs the literal conflict branch in the published pseudocode,
which otherwise merges a value unifier without recording the requested
variable equality and can therefore lose the advertised binding meaning. -/
inductive AddVarEqualityRel (p : Parameters) :
    Bindings → String → String → Bindings → Prop where
  | consistent {bindings : Bindings} {left right : String}
      {values : List Atom} :
      (hvalues : (bindings.addEquality left right).classValues left = values) →
      ValuesAgree values →
      AddVarEqualityRel p bindings left right
        (bindings.addEquality left right)
  | reconcile {bindings : Bindings} {left right : String}
      {first : Atom} {rest : List Atom} {matched out : Bindings} :
      (hvalues : (first :: rest).Perm
        ((bindings.addEquality left right).classValues left)) →
      ¬ValuesAgree (first :: rest) →
      MatchListAccRel p (List.replicate rest.length first) rest
        Bindings.empty matched →
      MergeRel p (bindings.addEquality left right) matched out →
      AddVarEqualityRel p bindings left right out

/-- Fold an explicitly chosen ordering of right-hand binding constraints. -/
inductive MergeConstraintsRel (p : Parameters) :
    Bindings → List Constraint → Bindings → Prop where
  | nil {seed : Bindings} : MergeConstraintsRel p seed [] seed
  | value {seed next out : Bindings} {varName : String} {value : Atom}
      {rest : List Constraint} :
      AddVarBindingRel p seed varName value next →
      MergeConstraintsRel p next rest out →
      MergeConstraintsRel p seed (.value varName value :: rest) out
  | equality {seed next out : Bindings} {left right : String}
      {rest : List Constraint} :
      AddVarEqualityRel p seed left right next →
      MergeConstraintsRel p next rest out →
      MergeConstraintsRel p seed (.equality left right :: rest) out

/-- Merge two binding sets.  Any permutation of the right-hand set is an
admissible fold order, making the human statement that relation order does not
matter part of the formal judgment rather than an informal comment. -/
inductive MergeRel (p : Parameters) : Bindings → Bindings → Bindings → Prop where
  | mk {left right out : Bindings} {order : List Constraint} :
      order.Perm (constraints right) →
      MergeConstraintsRel p left order out →
      MergeRel p left right out

end

/-- Public expression-list matching starts from empty bindings. -/
abbrev MatchListRel (p : Parameters) (left right : List Atom)
    (out : Bindings) : Prop :=
  MatchListAccRel p left right Bindings.empty out

/-- Changing only the concrete list presentation of the right binding set does
not change which declarative merges are admitted. -/
theorem mergeRel_iff_of_constraints_perm {p : Parameters}
    {left right₁ right₂ out : Bindings}
    (hperm : (constraints right₁).Perm (constraints right₂)) :
    MergeRel p left right₁ out ↔ MergeRel p left right₂ out := by
  constructor
  · rintro ⟨horder, hfold⟩
    exact ⟨horder.trans hperm, hfold⟩
  · rintro ⟨horder, hfold⟩
    exact ⟨horder.trans hperm.symm, hfold⟩

/-- Merging the empty human binding set is relationally the identity.  This is
the base case for direct LeaTTa completeness and does not appeal to either
executable merger. -/
theorem mergeRel_empty_right_eq {p : Parameters}
    {left out : Bindings}
    (hmerge : MergeRel p left Bindings.empty out) :
    out = left := by
  rcases hmerge with ⟨horder, hfold⟩
  have hnil : (constraints Bindings.empty) = [] := by
    rfl
  rw [hnil] at horder
  have horderNil : _ = [] := List.Perm.eq_nil horder
  subst horderNil
  cases hfold
  rfl

/-! ## Specification-boundary witnesses -/

/-- The human non-custom fragment with the semantic class-dependency loop
policy fixed above. -/
def noCustomSemantic : Parameters where
  hasCustomMatcher := fun _ => False
  customMatch := fun _ _ _ => False
  admissible := SemanticLoopFree

/-- Equality-based grounded callbacks instantiate the human custom-matcher
boundary for ordinary scalar payloads.  Because every payload supplies this
callback, the published no-custom fallback remains part of the general spec but
is unreachable in this particular profile. -/
def equalityGroundedSemantic : Parameters where
  hasCustomMatcher := fun _ => True
  customMatch := fun grounded atom out =>
    atom = .grounded grounded ∧ out = Bindings.empty
  admissible := SemanticLoopFree

/-- Positive: equal symbols match. -/
example : MatchRel noCustomSemantic (.symbol "a") (.symbol "a")
    Bindings.empty :=
  .symSym "a" semanticLoopFree_empty

/-- Positive: variable/variable matching records equality. -/
example : MatchRel noCustomSemantic (.var "x") (.var "y")
    (Bindings.empty.addEquality "x" "y") :=
  .varVar "x" "y" (semanticLoopFree_of_assignments_nil rfl)

/-- Positive human fallback: two grounded values without custom matchers match
even when their payloads differ.  This is the clause on which the published
text and the implementation-oriented model currently disagree. -/
example : MatchRel noCustomSemantic
    (.grounded (.int 1)) (.grounded (.int 2)) Bindings.empty :=
  .groundedFallback (by simp [noCustomSemantic])
    (by simp [noCustomSemantic]) semanticLoopFree_empty

/-- Positive equality-profile grounded callback. -/
example : MatchRel equalityGroundedSemantic
    (.grounded (.int 1)) (.grounded (.int 1)) Bindings.empty :=
  .groundedLeftCustom (by simp [isVariableB])
    (by simp [equalityGroundedSemantic])
    ⟨rfl, rfl⟩ semanticLoopFree_empty

/-- Negative equality-profile callback: distinct scalar payloads do not match. -/
theorem grounded_mismatch_not_match
    {left right : GroundedValue} (hne : left ≠ right) (out : Bindings) :
    ¬MatchRel equalityGroundedSemantic
      (.grounded left) (.grounded right) out := by
  intro hmatch
  cases hmatch with
  | groundedLeftCustom _ _ hcustom _ =>
      exact hne (Atom.grounded.inj hcustom.1.symm)
  | groundedRightCustom _ hleftNoCustom _ _ _ =>
      exact hleftNoCustom (by simp [Parameters.atomHasCustomMatcher,
        equalityGroundedSemantic])
  | groundedFallback hleft _ _ =>
      exact hleft (by simp [equalityGroundedSemantic])

/-- Negative: distinct symbols cannot be related by the human matcher. -/
theorem symbol_mismatch_not_match
    {p : Parameters} {left right : String}
    (hne : left ≠ right) (out : Bindings) :
    ¬MatchRel p (.symbol left) (.symbol right) out := by
  intro hmatch
  cases hmatch with
  | symSym => exact hne rfl

/-- Negative: the var/var clause cannot masquerade as an oriented assignment. -/
theorem varVar_assignment_not_match (left right : String) :
    ¬MatchRel noCustomSemantic (.var left) (.var right)
      (Bindings.empty.assign left (.var right)) := by
  intro hmatch
  cases hmatch with
  | varNonVar hnonvar => simp [isVariableB] at hnonvar
  | nonVarVar hnonvar => simp [isVariableB] at hnonvar

end Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec
