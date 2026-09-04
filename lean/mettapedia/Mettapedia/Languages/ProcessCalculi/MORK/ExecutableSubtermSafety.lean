import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchSafety

/-!
# Executable authority below atom roots

MM2 rows may carry dormant directives inside data structures.  A top-level
directive inventory therefore does not by itself describe every executable
value that a later matcher could expose.  This module computes the complete
nested directive inventory of an atom and supplies the hereditary invariant
needed by computable matching.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

mutual
  /-- Every scheduler-visible directive occurring at or below one atom. -/
  def rawExecSubterms : Atom → List RawExecFact
    | atom@(.expression children) =>
        (extractRawExecFact atom).toList ++ rawExecSubtermsList children
    | atom => (extractRawExecFact atom).toList

  /-- List companion of `rawExecSubterms`. -/
  def rawExecSubtermsList : List Atom → List RawExecFact
    | [] => []
    | atom :: atoms => rawExecSubterms atom ++ rawExecSubtermsList atoms
end

theorem rawExecSubtermsList_eq_flatMap (atoms : List Atom) :
    rawExecSubtermsList atoms = atoms.flatMap rawExecSubterms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      simp only [rawExecSubtermsList, List.flatMap_cons, induction]

/-- Every nested directive carried by `atom` belongs to a fixed inventory. -/
def ExecutableSubtermsWithin (allowed : List RawExecFact) (atom : Atom) : Prop :=
  ∀ raw ∈ rawExecSubterms atom, raw ∈ allowed

/-- List form of `ExecutableSubtermsWithin`. -/
def ExecutableSubtermListWithin (allowed : List RawExecFact)
    (atoms : List Atom) : Prop :=
  ∀ raw ∈ rawExecSubtermsList atoms, raw ∈ allowed

@[simp] theorem executableSubtermListWithin_nil (allowed : List RawExecFact) :
    ExecutableSubtermListWithin allowed [] := by
  intro raw member
  cases member

theorem executableSubtermListWithin_cons
    {allowed : List RawExecFact} {atom : Atom} {atoms : List Atom} :
    ExecutableSubtermListWithin allowed (atom :: atoms) ↔
      ExecutableSubtermsWithin allowed atom ∧
        ExecutableSubtermListWithin allowed atoms := by
  constructor
  · intro within
    constructor
    · intro raw member
      exact within raw (by simp [rawExecSubtermsList, member])
    · intro raw member
      exact within raw (by simp [rawExecSubtermsList, member])
  · intro within raw member
    simp only [rawExecSubtermsList, List.mem_append] at member
    rcases member with head | tail
    · exact within.1 raw head
    · exact within.2 raw tail

/-- The nested inventory includes a directive at the root when one is
present. -/
theorem extractRawExecFact_mem_rawExecSubterms
    {atom : Atom} {raw : RawExecFact}
    (extracted : extractRawExecFact atom = some raw) :
    raw ∈ rawExecSubterms atom := by
  cases atom <;> simp [rawExecSubterms, extracted]

private theorem rawExecFact_atom_eq_of_extract
    {atom : Atom} {raw : RawExecFact}
    (extracted : extractRawExecFact atom = some raw) :
    raw.atom = atom := by
  unfold extractRawExecFact at extracted
  split at extracted <;> try contradiction
  next equal =>
    injection extracted with rawEqual
    exact congrArg RawExecFact.atom rawEqual.symm

mutual
  /-- Nested executable inventory is transitively closed below every selected
  directive.  This keeps the authority test tied to syntax-tree containment,
  rather than to a separate hand-maintained rule list. -/
  theorem rawExecSubterms_transitive : ∀ parent raw nested,
      raw ∈ rawExecSubterms parent →
      nested ∈ rawExecSubterms raw.atom →
      nested ∈ rawExecSubterms parent
    | .symbol _, raw, nested, rawMember, _ => by
        simp [rawExecSubterms, extractRawExecFact] at rawMember
    | .var _, raw, nested, rawMember, _ => by
        simp [rawExecSubterms, extractRawExecFact] at rawMember
    | .grounded _, raw, nested, rawMember, _ => by
        simp [rawExecSubterms, extractRawExecFact] at rawMember
    | .expression children, raw, nested, rawMember, nestedMember => by
        simp only [rawExecSubterms, List.mem_append, Option.mem_toList] at rawMember
        rcases rawMember with rootMember | childMember
        · have extracted : extractRawExecFact (.expression children) = some raw := by
            simpa using rootMember
          have atomEqual := rawExecFact_atom_eq_of_extract extracted
          rw [atomEqual] at nestedMember
          exact nestedMember
        · simp only [rawExecSubterms, List.mem_append, Option.mem_toList]
          exact Or.inr (rawExecSubtermsList_transitive children raw nested
            childMember nestedMember)

  theorem rawExecSubtermsList_transitive : ∀ parents raw nested,
      raw ∈ rawExecSubtermsList parents →
      nested ∈ rawExecSubterms raw.atom →
      nested ∈ rawExecSubtermsList parents
    | [], raw, nested, rawMember, _ => by
        simp [rawExecSubtermsList] at rawMember
    | parent :: parents, raw, nested, rawMember, nestedMember => by
        simp only [rawExecSubtermsList, List.mem_append] at rawMember ⊢
        rcases rawMember with parentMember | parentsMember
        · exact Or.inl (rawExecSubterms_transitive parent raw nested
            parentMember nestedMember)
        · exact Or.inr (rawExecSubtermsList_transitive parents raw nested
            parentsMember nestedMember)
end

/-- A directive selected from an already authorized atom carries no hidden
directive outside that atom's fixed inventory. -/
theorem executableSubtermsWithin_rawExecFact
    {allowed : List RawExecFact} {atom : Atom} {raw : RawExecFact}
    (within : ExecutableSubtermsWithin allowed atom)
    (member : raw ∈ rawExecSubterms atom) :
    ExecutableSubtermsWithin allowed raw.atom := by
  intro nested nestedMember
  exact within nested
    (rawExecSubterms_transitive atom raw nested member nestedMember)

/-- Nested executable authority strengthens the existing root-only
authority predicate. -/
theorem executableSubtermsWithin_implies_rawExecAtomWithin
    {allowed : List RawExecFact} {atom : Atom}
    (within : ExecutableSubtermsWithin allowed atom) :
    RawExecAtomWithin allowed atom := by
  intro raw extracted
  exact within raw (extractRawExecFact_mem_rawExecSubterms extracted)

/-- The nested executable invariant descends through every expression edge,
which is exactly the hypothesis needed to transport it through matching. -/
theorem executableSubtermsWithin_hereditary (allowed : List RawExecFact) :
    AtomPropertyHereditary (ExecutableSubtermsWithin allowed) := by
  intro children parent child childMember raw rawMember
  apply parent raw
  simp only [rawExecSubterms, rawExecSubtermsList_eq_flatMap,
    List.mem_append, Option.mem_toList, List.mem_flatMap]
  exact Or.inr ⟨child, childMember, rawMember⟩

/-- Membership in a containing compiler-derived inventory establishes the
nested executable invariant without inspecting execution state. -/
theorem executableSubtermsWithin_of_subterms_subset
    {allowed : List RawExecFact} {atom : Atom}
    (subset : ∀ raw ∈ rawExecSubterms atom, raw ∈ allowed) :
    ExecutableSubtermsWithin allowed atom :=
  subset

/-- A directive excluded from a fixed inventory remains unauthorized when it
is hidden below an otherwise inert carrier. -/
theorem nested_directive_absent_from_inventory_is_rejected
    {allowed : List RawExecFact} {directive : Atom} {raw : RawExecFact}
    (extracted : extractRawExecFact directive = some raw)
    (absent : raw ∉ allowed) (carrier : Atom) :
    ¬ ExecutableSubtermsWithin allowed
      (.expression [carrier, directive]) := by
  intro within
  apply absent
  apply within raw
  simp only [rawExecSubterms, rawExecSubtermsList,
    List.mem_append, Option.mem_toList]
  exact Or.inr (Or.inr
    (Or.inl (extractRawExecFact_mem_rawExecSubterms extracted)))

/-! ## Controls -/

private def controlDirective : Atom :=
  .expression [.symbol "exec", .symbol "location",
    .expression [.symbol "I"], .expression [.symbol "O"]]

private def controlRawDirective : RawExecFact :=
  ⟨controlDirective, .symbol "location",
    .expression [.symbol "I"], .expression [.symbol "O"]⟩

/-- Positive control: a directive nested two expression levels below the
root is included in the recursive inventory. -/
theorem nested_directive_is_collected :
    controlRawDirective ∈ rawExecSubterms
      (.expression [.symbol "carrier", .expression [controlDirective]]) := by
  decide

/-- Negative control: root-only containment cannot certify a nested
directive that is absent from the declared inventory. -/
theorem root_only_authority_does_not_imply_nested_authority :
    RawExecAtomWithin []
        (.expression [.symbol "carrier", controlDirective]) ∧
      ¬ ExecutableSubtermsWithin []
        (.expression [.symbol "carrier", controlDirective]) := by
  constructor
  · intro raw extracted
    simp [extractRawExecFact] at extracted
  · intro within
    have impossible : controlRawDirective ∈ ([] : List RawExecFact) :=
      within controlRawDirective (by decide)
    simp at impossible

section AxiomAudit

#print axioms rawExecSubtermsList_eq_flatMap
#print axioms executableSubtermListWithin_cons
#print axioms extractRawExecFact_mem_rawExecSubterms
#print axioms rawExecSubterms_transitive
#print axioms rawExecSubtermsList_transitive
#print axioms executableSubtermsWithin_rawExecFact
#print axioms executableSubtermsWithin_implies_rawExecAtomWithin
#print axioms executableSubtermsWithin_hereditary
#print axioms executableSubtermsWithin_of_subterms_subset
#print axioms nested_directive_absent_from_inventory_is_rejected
#print axioms nested_directive_is_collected
#print axioms root_only_authority_does_not_imply_nested_authority

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
