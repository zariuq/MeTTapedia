import Mettapedia.Languages.MeTTa.SpaceTheory.Assignments
import Mettapedia.Languages.MeTTa.SpaceTheory.ConstructorSyntax
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Multiset.MapFold

/-!
# Symbol renaming of a space's static theory

A signature renaming maps symbols in the atoms, not their occurrence
identities, variables, or grounded payloads. It must fix the syntax of
type and subtype assignments. When it also transports the base typing
judgments, it preserves and reflects every assignment-generated type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.Renaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Atoms (Content)
open Assignments (TypeAssignment SubtypeAssignment Subtype HasType)
open Mettapedia.GSLT.LanguageDef (LanguageDefSymbolMap mapPattern mapPatternList)
open ConstructorSyntax (Variables term? terms?)

mutual
def atom (names : String → String) : Atom → Atom
  | .symbol s => .symbol (names s)
  | .var x => .var x
  | .grounded value => .grounded value
  | .expression children => .expression (childrenWith names children)

def childrenWith (names : String → String) : List Atom → List Atom
  | [] => []
  | first :: tail => atom names first :: childrenWith names tail
end

mutual
theorem atom_inverse (f g : String → String) (inverse : ∀ s, g (f s) = s) (a : Atom) :
    atom g (atom f a) = a := by
  cases a with
  | symbol s => simp [atom, inverse]
  | var | grounded => rfl
  | expression children => simp [atom, children_inverse f g inverse children]
termination_by sizeOf a

theorem children_inverse (f g : String → String) (inverse : ∀ s, g (f s) = s) (as : List Atom) :
    childrenWith g (childrenWith f as) = as := by
  cases as with
  | nil => rfl
  | cons first tail =>
    simp [childrenWith, atom_inverse f g inverse first, children_inverse f g inverse tail]
termination_by sizeOf as
end

def acts (names : Equiv.Perm String) : Atom ≃ Atom where
  toFun := atom names
  invFun := atom names.symm
  left_inv := atom_inverse _ _ names.symm_apply_apply
  right_inv := atom_inverse _ _ names.apply_symm_apply

/-- Constructor labels are user symbols. Rule and equation labels are
authored diagnostics, and premise operators belong to the base. -/
def termSymbols (names : String → String) : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with constructor := names }

mutual
/-- Renaming commutes with reading a constructor term. Failure is
preserved too; a singleton expression cannot become a symbol. -/
theorem term_rename (names : String → String) (vars : Variables) (a : Atom) :
    term? vars (atom names a) = (term? vars a).map (mapPattern (termSymbols names)) := by
  cases a with
  | symbol name => rfl
  | var name => cases vars <;> rfl
  | grounded value => rfl
  | expression children =>
    cases children with
    | nil => rfl
    | cons head children =>
      cases children with
      | nil => cases head <;> rfl
      | cons first tail =>
        cases head with
        | var | grounded | expression => rfl
        | symbol h =>
          simp only [atom, childrenWith, term?, term_rename names vars first, terms_rename names vars tail]
          cases term? vars first <;> cases terms? vars tail <;>
            simp [mapPattern, mapPatternList, termSymbols]
termination_by sizeOf a

theorem terms_rename (names : String → String) (vars : Variables) (as : List Atom) :
    terms? vars (childrenWith names as) = (terms? vars as).map (mapPatternList (termSymbols names)) := by
  cases as with
  | nil => rfl
  | cons first tail =>
    simp only [childrenWith, terms?, term_rename names vars first, terms_rename names vars tail]
    cases term? vars first <;> cases terms? vars tail <;>
      simp [mapPatternList]
termination_by sizeOf as
end

def renamed (names : Equiv.Perm String) (as : Multiset Atom) : Multiset Atom :=
  as.map (acts names)

private theorem renamed_mem (names : Equiv.Perm String) (as : Multiset Atom) (a : Atom) :
    acts names a ∈ renamed names as ↔ a ∈ as := by
  constructor
  · intro member
    obtain ⟨before, inside, equal⟩ := Multiset.mem_map.mp member
    exact (Equiv.injective (acts names) equal) ▸ inside
  · intro inside
    exact Multiset.mem_map.mpr ⟨a, inside, rfl⟩

/-- Preserving a constructor of declarations lets the corresponding
relation transport through the renamed multiset. -/
theorem type_assignment_iff (names : Equiv.Perm String) (fix : names ":" = ":")
    (as : Multiset Atom) (term type : Atom) :
    TypeAssignment (renamed names as) (acts names term) (acts names type) ↔
      TypeAssignment as term type := by
  have moved : acts names (Content.assignment term type).syntax =
      (Content.assignment (acts names term) (acts names type)).syntax := by
    change Atom.expression [.symbol (names ":"), acts names term, acts names type] = _
    rw [fix]
    rfl
  unfold TypeAssignment
  rw [← moved, renamed_mem]

theorem subtype_assignment_iff (names : Equiv.Perm String) (fix : names ":<" = ":<")
    (as : Multiset Atom) (s t : Atom) :
    SubtypeAssignment (renamed names as) (acts names s) (acts names t) ↔
      SubtypeAssignment as s t := by
  have moved : acts names (Content.subtype s t).syntax =
      (Content.subtype (acts names s) (acts names t)).syntax := by
    change Atom.expression [.symbol (names ":<"), acts names s, acts names t] = _
    rw [fix]
    rfl
  unfold SubtypeAssignment
  rw [← moved, renamed_mem]

def relation (e : Atom ≃ Atom) (base : Atom → Atom → Prop) : Atom → Atom → Prop :=
  fun a b => base (e.symm a) (e.symm b)

theorem subtype_iff (names : Equiv.Perm String) (fix : names ":<" = ":<")
    (base : Atom → Atom → Prop) (as : Multiset Atom) (s t : Atom) :
    Subtype (relation (acts names) base) (renamed names as) (acts names s) (acts names t) ↔
      Subtype base as s t := by
  let e := acts names
  constructor
  · intro proof
    have pulled := Assignments.subtype_least
      (target := fun a b => Subtype base as (e.symm a) (e.symm b))
      (fun _ => .refl) (fun _ _ _ h k => h.trans k) (fun _ _ h => .single (.inl h))
      (fun a b h => .single (.inr
        ((subtype_assignment_iff names fix as (e.symm a) (e.symm b)).mp
          (by simpa only [e, Equiv.apply_symm_apply] using h)))) proof
    simpa only [e, Equiv.symm_apply_apply] using pulled
  · intro proof
    exact Assignments.subtype_least
      (target := fun a b => Subtype (relation e base) (renamed names as) (e a) (e b))
      (fun _ => .refl) (fun _ _ _ h k => h.trans k)
      (fun _ _ h => .single (.inl (by simpa only [e, relation, Equiv.symm_apply_apply] using h)))
      (fun a b h => .single (.inr ((subtype_assignment_iff names fix as a b).mpr h))) proof

theorem typing_iff (names : Equiv.Perm String) (fixType : names ":" = ":")
    (fixSubtype : names ":<" = ":<") (baseType baseSubtype : Atom → Atom → Prop)
    (as : Multiset Atom) (term type : Atom) :
    HasType (relation (acts names) baseType) (relation (acts names) baseSubtype)
        (renamed names as) (acts names term) (acts names type) ↔
      HasType baseType baseSubtype as term type := by
  let e := acts names
  constructor
  · rintro ⟨first, assigned | assigned, path⟩
    · refine ⟨e.symm first, .inl ?_, (subtype_iff names fixSubtype baseSubtype as _ type).mp ?_⟩
      · simpa only [e, relation, Equiv.symm_apply_apply] using assigned
      · simpa only [e, Equiv.apply_symm_apply] using path
    · refine ⟨e.symm first, .inr ((type_assignment_iff names fixType as term _).mp ?_),
        (subtype_iff names fixSubtype baseSubtype as _ type).mp ?_⟩
      · simpa only [e, Equiv.apply_symm_apply] using assigned
      · simpa only [e, Equiv.apply_symm_apply] using path
  · rintro ⟨first, assigned | assigned, path⟩
    · refine ⟨e first, .inl ?_, (subtype_iff names fixSubtype baseSubtype as first type).mpr path⟩
      simpa only [e, relation, Equiv.symm_apply_apply] using assigned
    · exact ⟨e first, .inr ((type_assignment_iff names fixType as term first).mpr assigned),
        (subtype_iff names fixSubtype baseSubtype as first type).mpr path⟩

theorem renaming_a_reserved_symbol_can_create_a_declaration :
    let data : Atom := .expression [.symbol "tag", .symbol "Matcha", .symbol "Tea"]
    (Atoms.classify data).kind = .data ∧
      (Atoms.classify (acts (Equiv.swap "tag" ":") data)).kind = .typed := by
  decide +kernel

end Mettapedia.Languages.MeTTa.SpaceTheory.Renaming
