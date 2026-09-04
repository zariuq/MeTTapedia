import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Hereditary safety for computable matching

A compatible match may bind a variable to any nested concrete atom reached by
its pattern.  This module isolates the generic condition needed to transport
an atom-local invariant into every value of the resulting substitution: the
invariant must pass from an expression to each of its immediate children.

The result is independent of executable syntax and can be reused for
capability origin, typing, provenance, and representation invariants.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Every value physically stored in a substitution satisfies `property`. -/
def SubstitutionValuesWithin (property : Atom → Prop)
    (substitution : Subst) : Prop :=
  ∀ entry ∈ substitution, property entry.2

/-- An atom-local property is hereditary when an authorized expression
authorizes each of its immediate children. -/
def AtomPropertyHereditary (property : Atom → Prop) : Prop :=
  ∀ children, property (.expression children) →
    ∀ child ∈ children, property child

@[simp] theorem substitutionValuesWithin_nil (property : Atom → Prop) :
    SubstitutionValuesWithin property [] := by
  intro entry member
  cases member

theorem substitutionValuesWithin_cons
    (property : Atom → Prop) {substitution : Subst}
    {name : String} {value : Atom}
    (before : SubstitutionValuesWithin property substitution)
    (valueWithin : property value) :
    SubstitutionValuesWithin property ((name, value) :: substitution) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | tail
  · exact valueWithin
  · exact before entry tail

/-- A value obtained by substitution lookup was physically present in the
substitution and therefore inherits its pointwise invariant. -/
theorem SubstitutionValuesWithin.lookup
    {property : Atom → Prop} {substitution : Subst}
    {name : String} {value : Atom}
    (within : SubstitutionValuesWithin property substitution)
    (found : substitution.lookup name = some value) :
    property value := by
  unfold Subst.lookup at found
  cases entry : substitution.find? (fun pair => pair.1 == name) with
  | none => simp [entry] at found
  | some pair =>
      rcases pair with ⟨key, stored⟩
      simp [entry] at found
      have pairMember : (key, stored) ∈ substitution :=
        List.mem_of_find?_eq_some entry
      exact found ▸ within (key, stored) pairMember

mutual
  /-- Matching one pattern cannot introduce an unsafe substitution value when
  the concrete atom is safe and safety descends through expressions. -/
  theorem cmatchAtom_substitutionValuesWithin
      (property : Atom → Prop)
      (hereditary : AtomPropertyHereditary property)
      (substitution : Subst) (pattern concrete : Atom) (result : Subst)
      (before : SubstitutionValuesWithin property substitution)
      (concreteWithin : property concrete)
      (matched : cmatchAtom substitution pattern concrete = some result) :
      SubstitutionValuesWithin property result := by
    cases pattern <;> cases concrete <;>
      simp only [cmatchAtom] at matched
    case var.var name concreteName =>
      cases lookup : Subst.lookup substitution name with
      | none =>
          simp only [lookup] at matched
          cases matched
          exact substitutionValuesWithin_cons property before concreteWithin
      | some value =>
          simp only [lookup] at matched
          split at matched
          · cases matched
            exact before
          · contradiction
    case var.symbol name concreteName =>
      cases lookup : Subst.lookup substitution name with
      | none =>
          simp only [lookup] at matched
          cases matched
          exact substitutionValuesWithin_cons property before concreteWithin
      | some value =>
          simp only [lookup] at matched
          split at matched
          · cases matched
            exact before
          · contradiction
    case var.grounded name concreteValue =>
      cases lookup : Subst.lookup substitution name with
      | none =>
          simp only [lookup] at matched
          cases matched
          exact substitutionValuesWithin_cons property before concreteWithin
      | some value =>
          simp only [lookup] at matched
          split at matched
          · cases matched
            exact before
          · contradiction
    case var.expression name concreteChildren =>
      cases lookup : Subst.lookup substitution name with
      | none =>
          simp only [lookup] at matched
          cases matched
          exact substitutionValuesWithin_cons property before concreteWithin
      | some value =>
          simp only [lookup] at matched
          split at matched
          · cases matched
            exact before
          · contradiction
    case symbol.symbol left right =>
      split at matched
      · cases matched
        exact before
      · contradiction
    case grounded.grounded left right =>
      split at matched
      · cases matched
        exact before
      · contradiction
    case expression.expression patterns concretes =>
      exact cmatchAtomList_substitutionValuesWithin property hereditary
        substitution patterns concretes result before
        (hereditary concretes concreteWithin) matched
    all_goals contradiction

  /-- List-matcher companion of
  `cmatchAtom_substitutionValuesWithin`. -/
  theorem cmatchAtomList_substitutionValuesWithin
      (property : Atom → Prop)
      (hereditary : AtomPropertyHereditary property)
      (substitution : Subst) (patterns concretes : List Atom)
      (result : Subst)
      (before : SubstitutionValuesWithin property substitution)
      (concretesWithin : ∀ concrete ∈ concretes, property concrete)
      (matched : cmatchAtomList substitution patterns concretes = some result) :
      SubstitutionValuesWithin property result := by
    cases patterns with
    | nil =>
        cases concretes with
        | nil =>
            simp only [cmatchAtomList] at matched
            cases matched
            exact before
        | cons concrete concretes => contradiction
    | cons pattern patterns =>
        cases concretes with
        | nil => contradiction
        | cons concrete concretes =>
            simp only [cmatchAtomList] at matched
            cases headMatch : cmatchAtom substitution pattern concrete with
            | none => simp [headMatch] at matched
            | some middle =>
                rw [headMatch] at matched
                exact cmatchAtomList_substitutionValuesWithin property
                  hereditary middle patterns concretes result
                  (cmatchAtom_substitutionValuesWithin property hereditary
                    substitution pattern concrete middle before
                    (concretesWithin concrete (by simp)) headMatch)
                  (fun candidate member =>
                    concretesWithin candidate (by simp [member]))
                  matched
end

/-- Every substitution returned by a positive compatible matcher contains
only values inherited from hereditary-safe input atoms. -/
theorem cmatchPattern_go_substitutionValuesWithin
    (property : Atom → Prop)
    (hereditary : AtomPropertyHereditary property)
    (space : CSpace) (spaceWithin : AtomsWithin property space) :
    ∀ patterns substitution witnesses result resultWitnesses,
      SubstitutionValuesWithin property substitution →
      (result, resultWitnesses) ∈
        cmatchPattern.go space patterns substitution witnesses →
      SubstitutionValuesWithin property result := by
  intro patterns
  induction patterns with
  | nil =>
      intro substitution witnesses result resultWitnesses before member
      simp only [cmatchPattern.go, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with ⟨rfl, _⟩
      exact before
  | cons pattern patterns induction =>
      intro substitution witnesses result resultWitnesses before member
      simp only [cmatchPattern.go, List.mem_flatMap] at member
      obtain ⟨⟨middle, concrete⟩, headMember, tailMember⟩ := member
      rw [List.mem_filterMap] at headMember
      obtain ⟨candidate, candidateMember, mapped⟩ := headMember
      simp only [Option.map_eq_some_iff] at mapped
      obtain ⟨matchedResult, matched, equal⟩ := mapped
      cases equal
      exact induction middle (concrete :: witnesses) result resultWitnesses
        (cmatchAtom_substitutionValuesWithin property hereditary substitution
          pattern concrete middle before
          (spaceWithin concrete candidateMember) matched)
        tailMember

/-- Input-spec specialization for ordinary compatible positive patterns. -/
theorem cmatchInputSpec_compat_substitutionValuesWithin
    (property : Atom → Prop)
    (hereditary : AtomPropertyHereditary property)
    (space : CSpace) (spaceWithin : AtomsWithin property space)
    (pattern : Pattern) {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] space (.compat pattern)).map Prod.fst) :
    SubstitutionValuesWithin property substitution := by
  rw [List.mem_map] at member
  obtain ⟨⟨result, witnesses⟩, resultMember, rfl⟩ := member
  exact cmatchPattern_go_substitutionValuesWithin property hereditary space
    spaceWithin pattern.atoms [] [] result witnesses
    (substitutionValuesWithin_nil property) resultMember

/-! ## Controls -/

private def forbidsUnsafeSymbol : Atom → Prop
  | .symbol "unsafe" => False
  | .expression children => ∀ child ∈ children, forbidsUnsafeSymbol child
  | _ => True

private theorem forbidsUnsafeSymbol_hereditary :
    AtomPropertyHereditary forbidsUnsafeSymbol := by
  intro children safe child member
  simp only [forbidsUnsafeSymbol] at safe
  exact safe child member

/-- Positive nested control: a variable bound below an expression constructor
inherits the hereditary invariant from the matched row. -/
theorem nested_match_preserves_hereditary_safety :
    SubstitutionValuesWithin forbidsUnsafeSymbol [("value", .symbol "safe")] := by
  have matched :
      cmatchAtom []
        (.expression [.symbol "box", .var "value"])
        (.expression [.symbol "box", .symbol "safe"]) =
          some [("value", .symbol "safe")] := by
    decide
  exact cmatchAtom_substitutionValuesWithin forbidsUnsafeSymbol
    forbidsUnsafeSymbol_hereditary [] _ _ _
    (substitutionValuesWithin_nil forbidsUnsafeSymbol)
    (by simp [forbidsUnsafeSymbol]) matched

private def rootOnlySafe : Atom → Prop
  | .symbol "unsafe" => False
  | _ => True

/-- Negative control: root-only safety is insufficient.  A safe expression
may expose an unsafe child to a nested pattern variable. -/
theorem root_only_safety_does_not_protect_nested_bindings :
    rootOnlySafe (.expression [.symbol "unsafe"]) ∧
      cmatchAtom [] (.expression [.var "value"])
        (.expression [.symbol "unsafe"]) =
          some [("value", .symbol "unsafe")] ∧
      ¬ SubstitutionValuesWithin rootOnlySafe
          [("value", .symbol "unsafe")] := by
  constructor
  · trivial
  constructor
  · decide
  · intro within
    exact within ("value", .symbol "unsafe") (by simp)

section AxiomAudit

#print axioms substitutionValuesWithin_cons
#print axioms SubstitutionValuesWithin.lookup
#print axioms cmatchAtom_substitutionValuesWithin
#print axioms cmatchAtomList_substitutionValuesWithin
#print axioms cmatchPattern_go_substitutionValuesWithin
#print axioms cmatchInputSpec_compat_substitutionValuesWithin
#print axioms nested_match_preserves_hereditary_safety
#print axioms root_only_safety_does_not_protect_nested_bindings

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
