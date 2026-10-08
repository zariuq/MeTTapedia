import Mettapedia.GSLT.Logic.ProgrammableSpaceAtomCoding
import Mettapedia.GSLT.Logic.ProgrammableSpaceReadings
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Material observations of MM2 physical keys

The dictionary retains the tag between compact byte-path keys and abstract
host atoms. Its graph code is constructed from finite chains, ordered list
codes and the complete literal atom dictionary. The resulting material set
identifies stores exactly by physical-key membership.

Literal atom support remains a separate observation. In particular, physical
keys can identify two differently named source variables while literal source
consumers still distinguish their names.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ProgrammableSpaceMM2KeyReadings
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT

def naturalCoding : ArgumentCoding Nat where
  graph value := OutcomeLabels.chainGraph value
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph first) = HSet.mk (OutcomeLabels.chainGraph second) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact OutcomeLabels.chainValue_injective same

def keyGraph : MorkSupportKey → AccessiblePointedGraph
  | .compact bytes => ProgrammableSpaceAtomCoding.tagged 0 (naturalCoding.lists.graph bytes)
  | .abstract atom => ProgrammableSpaceAtomCoding.tagged 1 (ProgrammableSpaceAtomCoding.coding.graph atom)

theorem keyGraph_injective : Function.Injective (fun key => HSet.mk (keyGraph key)) := by
  intro first second same
  cases first <;> cases second <;>
    simp only [keyGraph, ProgrammableSpaceAtomCoding.tagged_equal_iff] at same
  · exact congrArg MorkSupportKey.compact (naturalCoding.lists.injective same.2)
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact congrArg MorkSupportKey.abstract (ProgrammableSpaceAtomCoding.coding.injective same.2)

def keyCoding : ArgumentCoding MorkSupportKey := ⟨keyGraph, keyGraph_injective⟩

def keySupport (atoms : List Atom) : HSet :=
  ProgrammableSpaceReadings.support keyCoding (atoms.map morkSupportKey)

theorem keySupport_eq_iff_support (first second : List Atom) :
    keySupport first = keySupport second ↔
      (first.map morkSupportKey).toFinset = (second.map morkSupportKey).toFinset := by
  rw [keySupport, keySupport, ProgrammableSpaceReadings.support_eq_iff]
  constructor
  · intro same
    ext key
    simpa using same key
  · intro same key
    have member := Finset.ext_iff.mp same key
    simpa using member

theorem variable_key_reading_identifies_names :
    keySupport [.var "x"] = keySupport [.var "y"] := by
  apply (keySupport_eq_iff_support _ _).mpr
  decide +kernel

theorem literal_reading_retains_names :
    ProgrammableSpaceReadings.support ProgrammableSpaceAtomCoding.coding [.var "x"] ≠
      ProgrammableSpaceReadings.support ProgrammableSpaceAtomCoding.coding [.var "y"] := by
  intro same
  have member := (ProgrammableSpaceReadings.support_eq_iff ProgrammableSpaceAtomCoding.coding _ _).mp same (.var "x")
  have positive : Atom.var "x" ∈ [Atom.var "x"] := List.mem_cons_self
  have negative : Atom.var "x" ∉ [Atom.var "y"] := by decide
  exact negative (member.mp positive)

end Mettapedia.GSLT.Logic.ProgrammableSpaceMM2KeyReadings
