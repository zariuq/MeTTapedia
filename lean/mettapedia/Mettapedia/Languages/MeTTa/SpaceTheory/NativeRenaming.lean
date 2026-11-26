import Mettapedia.Languages.MeTTa.SpaceTheory.Renaming
import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Renaming the native equation theory

The atom action renames symbols, not variables or grounded values.
It transports the whole equation class, including equations inside an
expression. An authored firing judgment can be reindexed through that
signature action; a rename does not, by itself, evaluate a module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.NativeRenaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Atoms (Content Preference)
open Renaming (acts childrenWith atom_inverse relation)
open AtomEquations (Context)

theorem children_map (names : String → String) (children : List Atom) :
    childrenWith names children = children.map (Renaming.atom names) := by
  induction children with
  | nil => rfl
  | cons first rest ih => simp [childrenWith, ih]

def mapContext (names : String → String) : Context → Context
  | .hole => .hole
  | .child before inner after =>
    .child (before.map (Renaming.atom names)) (mapContext names inner) (after.map (Renaming.atom names))

theorem map_fill (names : String → String) (context : Context) (a : Atom) :
    Renaming.atom names (context.fill a) = (mapContext names context).fill (Renaming.atom names a) := by
  induction context with
  | hole => rfl
  | child before inner after ih =>
    simp [Context.fill, Renaming.atom, children_map, mapContext, ih]

def FixesEquations (names : String → String) : Prop :=
  ∀ preference : Preference, names preference.symbol = preference.symbol

theorem inverse_fixes (names : Equiv.Perm String) (tokens : FixesEquations names) : FixesEquations names.symm := by
  intro preference
  apply names.injective
  rw [names.apply_symm_apply, tokens preference]

theorem preserves_generator (names : String → String) (tokens : FixesEquations names)
    {atoms : List Atom} {first member : Atom} (declared : AtomEquations.Generator atoms first member) :
    AtomEquations.Generator (atoms.map (Renaming.atom names)) (Renaming.atom names first) (Renaming.atom names member) := by
  obtain ⟨pref, second, rest, written, one⟩ := declared
  refine ⟨pref, Renaming.atom names second, rest.map (Renaming.atom names), ?_, ?_⟩
  · refine List.mem_map.mpr ⟨_, written, ?_⟩
    simp [Content.syntax, Renaming.atom, children_map, tokens pref]
  · exact List.mem_map.mpr ⟨member, one, rfl⟩

theorem forward (names : String → String) (tokens : FixesEquations names)
    {atoms : List Atom} {a b : Atom} (same : AtomEquations.Equivalent atoms a b) :
    AtomEquations.Equivalent (atoms.map (Renaming.atom names)) (Renaming.atom names a) (Renaming.atom names b) := by
  induction same with
  | rel _ _ selected =>
    cases selected with
    | inside inner written =>
      rw [map_fill names inner, map_fill names inner]
      exact .rel _ _ (.inside (mapContext names inner) (preserves_generator names tokens written))
  | refl => exact .refl _
  | symm _ _ _ moved => exact .symm _ _ moved
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

theorem equivalent_iff (names : Equiv.Perm String) (tokens : FixesEquations names)
    (atoms : List Atom) (a b : Atom) :
    AtomEquations.Equivalent (atoms.map (Renaming.atom names)) (acts names a) (acts names b) ↔
      AtomEquations.Equivalent atoms a b := by
  constructor
  · intro moved
    change AtomEquations.Equivalent (atoms.map (Renaming.atom names))
      (Renaming.atom names a) (Renaming.atom names b) at moved
    have undone := forward names.symm (inverse_fixes names tokens) moved
    have original (source : List Atom) : (source.map (Renaming.atom names)).map (Renaming.atom names.symm) = source := by
      induction source with
      | nil => rfl
      | cons first rest ih => simp only [List.map_cons, atom_inverse names names.symm names.symm_apply_apply, ih]
    simpa only [original atoms, atom_inverse names names.symm names.symm_apply_apply] using undone
  · exact forward names tokens

theorem reindexed_steps_iff (names : Equiv.Perm String) (tokens : FixesEquations names)
    (atoms : List Atom) (firing : Atom → Atom → Prop) (a b : Atom) :
    (AtomEquations.theory (atoms.map (Renaming.atom names)) (relation (acts names) firing)).Step
        (acts names a) (acts names b) ↔ (AtomEquations.theory atoms firing).Step a b := by
  let rename := acts names
  constructor
  · rintro ⟨representative, result, into, writes, out⟩
    refine ⟨rename.symm representative, rename.symm result, ?_, writes, ?_⟩
    · apply (equivalent_iff names tokens atoms a (rename.symm representative)).mp
      change AtomEquations.Equivalent _ (rename a) (rename (rename.symm representative))
      rw [rename.apply_symm_apply]
      exact into
    · apply (equivalent_iff names tokens atoms (rename.symm result) b).mp
      change AtomEquations.Equivalent _ (rename (rename.symm result)) (rename b)
      rw [rename.apply_symm_apply]
      exact out
  · rintro ⟨representative, result, into, writes, out⟩
    refine ⟨rename representative, rename result, (equivalent_iff names tokens atoms _ _).mpr into, ?_,
      (equivalent_iff names tokens atoms _ _).mpr out⟩
    change firing (rename.symm (rename representative)) (rename.symm (rename result))
    simpa only [rename.symm_apply_apply] using writes

def operationMap (names : Equiv.Perm String) (tokens : FixesEquations names)
    (atoms : List Atom) (firing : Atom → Atom → Prop) :
    OperationalTranslation (AtomEquations.theory atoms firing)
      (AtomEquations.theory (atoms.map (Renaming.atom names)) (relation (acts names) firing)) where
  mapTerm := acts names
  mapEquiv := fun {a b} same => (equivalent_iff names tokens atoms a b).mpr same
  mapStep := fun {a b} step => (reindexed_steps_iff names tokens atoms firing a b).mpr step

section Controls

private def rename := Equiv.swap "A" "B"
private def stringA : Atom := .grounded (.string "A")
private def written : Atom := (Content.equation .rightward (.symbol "A") stringA []).syntax

theorem symbol_changes_but_grounded_literal_does_not :
    AtomEquations.Equivalent ([written].map (Renaming.atom rename)) (.symbol "B") stringA := by
  have tokens : FixesEquations rename := by intro p; cases p <;> decide +kernel
  have original : AtomEquations.Equivalent [written] (.symbol "A") stringA :=
    AtomEquations.authored ⟨.rightward, stringA, [], List.mem_cons_self, List.mem_cons_self⟩
  exact (equivalent_iff rename tokens [written] (.symbol "A") stringA).mpr original

private def notEquation : Atom := .expression [.symbol "marker", .symbol "A", .symbol "B"]
private def wrongRename := Equiv.swap "marker" "=e"

theorem changing_the_equation_token_changes_the_theory :
    ¬ AtomEquations.Equivalent [notEquation] (.symbol "A") (.symbol "B") ∧
      AtomEquations.Equivalent ([notEquation].map (Renaming.atom wrongRename)) (.symbol "A") (.symbol "B") := by
  constructor
  · have noGenerator (a b : Atom) : ¬ AtomEquations.Generator [notEquation] a b := by
      rintro ⟨pref, second, rest, listed, _⟩
      cases pref <;> simp [Content.syntax, Preference.symbol, notEquation] at listed
    intro joined
    have impossible := (AtomEquations.without_generators _ noGenerator _ _).mp joined
    exact (by decide : Atom.symbol "A" ≠ Atom.symbol "B") impossible
  · apply AtomEquations.authored
    exact ⟨.indifferent, .symbol "B", [], by decide +kernel, List.mem_cons_self⟩

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.NativeRenaming
