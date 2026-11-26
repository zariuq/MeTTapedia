import Mettapedia.Languages.MeTTa.HE.ModuleSpace
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mathlib.Data.Multiset.Bind

/-!
# Atom-local matching descends to a bag

An atom-local selection contributes its answer occurrences once per
stored occurrence. The resulting bag is independent of enumeration
order. This is the selection before its bodies execute: it does not
allow reordering effects or an ordered answer stream.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.BagMatching

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

def collect {A : Type} (answers : Atom → List A) (atoms : Multiset Atom) : Multiset A :=
  atoms.bind fun atom => (answers atom : Multiset A)

theorem collect_on_list {A : Type} (answers : Atom → List A) (atoms : List Atom) :
    collect answers (atoms : Multiset Atom) = (atoms.flatMap answers : Multiset A) :=
  Multiset.coe_bind atoms answers

theorem he_atom_local {A : Type} (answers : Atom → List A) (space : Space) :
    (space.queryWith answers : Multiset A) = collect answers space.atoms :=
  (collect_on_list answers space.atoms).symm

def pettaAt (bindings : Subst) (pattern body atom : Atom) : List Eval.Control :=
  ((SpaceSemantics.matchValue bindings pattern atom).map
    fun bound => Eval.Control.evaluate bound body).toList

theorem petta_selected_bag (bindings : Subst) (pattern body : Atom) (atoms : List Atom) :
    (Eval.queryBodies bindings atoms pattern body : Multiset Eval.Control) =
      collect (pettaAt bindings pattern body) atoms := by
  rw [collect_on_list]
  apply congrArg (fun alternatives : List Eval.Control => (alternatives : Multiset Eval.Control))
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    change List.filterMap _ (atom :: rest) = List.flatMap _ (atom :: rest)
    simp only [List.filterMap_cons, List.flatMap_cons, pettaAt]
    change Eval.queryBodies bindings rest pattern body = rest.flatMap (pettaAt bindings pattern body) at ih
    rw [← ih]
    cases SpaceSemantics.matchValue bindings pattern atom <;> rfl

theorem petta_named_space (state : Effects.State) (bindings : Subst) (space pattern body : Atom)
    (atoms : List Atom) (available : (Effects.readHandle space >>= state.read) = some atoms) :
    (Eval.queryAlternatives state bindings space pattern body : Multiset Eval.Control) =
      collect (pettaAt bindings pattern body) atoms := by
  rw [Eval.queryAlternatives, available]
  exact petta_selected_bag bindings pattern body atoms

/-- Neither definitions nor equations are erased from a raw read. Both
occurrences of the same written definition contribute to this query. -/
theorem petta_matches_repeated_written_definitions (name : String) (body : Atom) :
    let declaration := Atom.expression [.symbol "=", .symbol name, body]
    (Eval.queryBodies [] [declaration, declaration] (.var "written") (.var "written")).length = 2 := by
  simp [Eval.queryBodies, SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem a_set_can_lose_a_match :
    let atom := Atom.symbol "reading"
    let count (atoms : List Atom) :=
      (Eval.queryBodies [] atoms (.var "reading") (.var "reading")).length
    (∀ a, a ∈ [atom] ↔ a ∈ [atom, atom]) ∧ count [atom] ≠ count [atom, atom] := by
  dsimp only
  refine ⟨by simp, ?_⟩
  decide +kernel

end Mettapedia.Languages.MeTTa.SpaceTheory.BagMatching
