import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Stores

/-!
# Constructor definitions, with or without metavariables

This is the constructor vocabulary of a space presentation, not a new
MeTTa atom grammar. A source symbol and a singleton expression stay
distinct: the latter is outside this vocabulary. The ground restriction
is a choice about metavariables, not a separate presentation algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.ConstructorSyntax

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (binderFree binderFreeList)
open Mettapedia.GSLT.LanguageDef.DecidableRelations (FirstOrder)

inductive Variables where
  | literal | schematic
  deriving DecidableEq

mutual
  def term? (vars : Variables) : Atom → Option Pattern
    | .symbol h => some (.apply h [])
    | .var x => match vars with
      | .literal => none
      | .schematic => some (.fvar x)
    | .expression (.symbol h :: a :: tail) => do
      let first ← term? vars a
      let rest ← terms? vars tail
      return .apply h (first :: rest)
    | _ => none

  def terms? (vars : Variables) : List Atom → Option (List Pattern)
    | [] => some []
    | a :: tail => do
      let first ← term? vars a
      let rest ← terms? vars tail
      return first :: rest
end

mutual
theorem binderFree_term (vars : Variables) (atom : Atom) {p : Pattern}
    (read : term? vars atom = some p) : binderFree p = true := by
  unfold term? at read
  split at read
  · cases read; rfl
  · cases vars
    · cases read
    · cases read; rfl
  · rename_i head first tail
    obtain ⟨x, firstRead, tailAndResult⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨xs, restRead, result⟩ := Option.bind_eq_some_iff.mp tailAndResult
    cases result
    simp [binderFree, binderFreeList, binderFree_term vars first firstRead,
      binderFree_terms vars tail restRead]
  · contradiction
termination_by sizeOf atom

theorem binderFree_terms (vars : Variables) (atoms : List Atom) {ps : List Pattern}
    (read : terms? vars atoms = some ps) : binderFreeList ps = true := by
  cases atoms with
  | nil => cases read; rfl
  | cons first tail =>
    unfold terms? at read
    obtain ⟨x, firstRead, tailAndResult⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨xs, tailRead, result⟩ := Option.bind_eq_some_iff.mp tailAndResult
    cases result
    simp [binderFreeList, binderFree_term vars first firstRead,
      binderFree_terms vars tail tailRead]
termination_by sizeOf atoms
end

mutual
theorem ground_term (atom : Atom) {p : Pattern} (read : term? .literal atom = some p) :
    FirstOrder p := by
  unfold term? at read
  split at read
  · cases read; exact .apply (by simp)
  · cases read
  · rename_i head first tail
    obtain ⟨x, firstRead, tailAndResult⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨xs, restRead, result⟩ := Option.bind_eq_some_iff.mp tailAndResult
    cases result
    apply FirstOrder.apply
    intro t member
    rcases List.mem_cons.mp member with rfl | later
    · exact ground_term first firstRead
    · exact ground_terms tail restRead t later
  · contradiction
termination_by sizeOf atom

theorem ground_terms (atoms : List Atom) {ps : List Pattern} (read : terms? .literal atoms = some ps) :
    ∀ p ∈ ps, FirstOrder p := by
  cases atoms with
  | nil => cases read; simp
  | cons first tail =>
    unfold terms? at read
    obtain ⟨x, firstRead, tailAndResult⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨xs, tailRead, result⟩ := Option.bind_eq_some_iff.mp tailAndResult
    cases result
    intro t member
    rcases List.mem_cons.mp member with rfl | later
    · exact ground_term first firstRead
    · exact ground_terms tail tailRead t later
termination_by sizeOf atoms
end

end Mettapedia.Languages.MeTTa.SpaceTheory.ConstructorSyntax
