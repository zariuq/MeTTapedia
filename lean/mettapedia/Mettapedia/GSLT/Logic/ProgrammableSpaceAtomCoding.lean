import Mettapedia.GSLT.Logic.DiscreteReadingCodings
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Faithful material labels for all native atom constructors

Finite chains label bytes and constructor tags. Ordered
material pairs retain each string's UTF-8 bytes, both custom-grounded fields, and
the complete ordered expression tree. No enumeration is selected from a
countability proposition, and no atom case is rejected by this construction.

This codes literal source identity. Compact-key alpha identification and
language-relative observation are separate readouts; a source variable is
not identified with a symbol or with another variable name here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ProgrammableSpaceAtomCoding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.TypeTheory.MaterialSets.Hypersets

def characters : ArgumentCoding Char where
  graph character := OutcomeLabels.chainGraph character.toNat
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph first.toNat) =
      HSet.mk (OutcomeLabels.chainGraph second.toNat) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact Char.toNat_inj.mp (OutcomeLabels.chainValue_injective same)

def bytes : ArgumentCoding UInt8 where
  graph byte := OutcomeLabels.chainGraph byte.toNat
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph first.toNat) =
      HSet.mk (OutcomeLabels.chainGraph second.toNat) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact UInt8.toNat_inj.mp (OutcomeLabels.chainValue_injective same)

def strings : ArgumentCoding String where
  graph value := (ArgumentCoding.lists bytes).graph value.toByteArray.data.toList
  injective := by
    intro first second same
    have listsSame := (ArgumentCoding.lists bytes).injective same
    have arraysSame := congrArg List.toArray listsSame
    have bytesSame : first.toByteArray = second.toByteArray :=
      ByteArray.ext (by simpa only [Array.toArray_toList] using arraysSame)
    exact String.toByteArray_inj.mp bytesSame

def booleans : ArgumentCoding Bool where
  graph value := OutcomeLabels.chainGraph (if value then 1 else 0)
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph _) = HSet.mk (OutcomeLabels.chainGraph _) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    have codes := OutcomeLabels.chainValue_injective same
    cases first <;> cases second <;> simp_all

def tagged (tag : Nat) (payload : AccessiblePointedGraph) : AccessiblePointedGraph :=
  AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph tag) payload

theorem tagged_equal_iff (firstTag secondTag : Nat)
    (first second : AccessiblePointedGraph) :
    HSet.mk (tagged firstTag first) = HSet.mk (tagged secondTag second) ↔
      firstTag = secondTag ∧ HSet.mk first = HSet.mk second := by
  simp only [tagged, AccessiblePointedGraph.mk_kpairGraph, HSet.kpair_inj,
    OutcomeLabels.mk_chainGraph]
  constructor
  · rintro ⟨tags, payloads⟩
    exact ⟨OutcomeLabels.chainValue_injective tags, payloads⟩
  · rintro ⟨rfl, payloads⟩
    exact ⟨rfl, payloads⟩

def groundedGraph : GroundedValue → AccessiblePointedGraph
  | .int value => tagged 0 (Mettapedia.GSLT.DiscreteReadingCodings.integers.graph value)
  | .string value => tagged 1 (strings.graph value)
  | .bool value => tagged 2 (booleans.graph value)
  | .custom typeName payload => tagged 3
      (AccessiblePointedGraph.kpairGraph (strings.graph typeName) (strings.graph payload))

theorem groundedGraph_injective : Function.Injective (fun value => HSet.mk (groundedGraph value)) := by
  intro first second same
  cases first <;> cases second <;> simp only [groundedGraph, tagged_equal_iff] at same
  all_goals try { obtain ⟨impossible, _⟩ := same; contradiction }
  · exact congrArg GroundedValue.int (Mettapedia.GSLT.DiscreteReadingCodings.integers.injective same.2)
  · exact congrArg GroundedValue.string (strings.injective same.2)
  · exact congrArg GroundedValue.bool (booleans.injective same.2)
  · have fields := same.2
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at fields
    exact congrArg₂ GroundedValue.custom (strings.injective (HSet.kpair_inj.mp fields).1)
      (strings.injective (HSet.kpair_inj.mp fields).2)

def grounded : ArgumentCoding GroundedValue := ⟨groundedGraph, groundedGraph_injective⟩

mutual
  def graph (atom : Atom) : AccessiblePointedGraph :=
    match atom with
    | .symbol name => tagged 0 (strings.graph name)
    | .var name => tagged 1 (strings.graph name)
    | .grounded value => tagged 2 (grounded.graph value)
    | .expression children => tagged 3 (listGraph children)
  termination_by structural atom

  def listGraph (atoms : List Atom) : AccessiblePointedGraph :=
    match atoms with
    | [] => AccessiblePointedGraph.empty
    | head :: tail => AccessiblePointedGraph.kpairGraph (graph head) (listGraph tail)
  termination_by structural atoms
end

theorem ordered_pair_not_empty (first second : HSet) : HSet.kpair first second ≠ ∅ := by
  intro same
  have member : ({first} : HSet) ∈ HSet.kpair first second := HSet.mem_pair.mpr (Or.inl rfl)
  rw [same] at member
  exact HSet.notMem_empty _ member

mutual
  theorem graph_injective (first second : Atom)
      (same : HSet.mk (graph first) = HSet.mk (graph second)) : first = second := by
    cases first <;> cases second <;> simp only [graph, tagged_equal_iff] at same
    all_goals try { obtain ⟨impossible, _⟩ := same; contradiction }
    · exact congrArg Atom.symbol (strings.injective same.2)
    · exact congrArg Atom.var (strings.injective same.2)
    · exact congrArg Atom.grounded (grounded.injective same.2)
    · exact congrArg Atom.expression (listGraph_injective _ _ same.2)
  termination_by structural first

  theorem listGraph_injective (first second : List Atom)
      (same : HSet.mk (listGraph first) = HSet.mk (listGraph second)) : first = second := by
    cases first with
    | nil =>
        cases second with
        | nil => rfl
        | cons head tail =>
            simp only [listGraph, HSet.mk_empty, AccessiblePointedGraph.mk_kpairGraph] at same
            exact (ordered_pair_not_empty _ _ same.symm).elim
    | cons head tail =>
        cases second with
        | nil =>
            simp only [listGraph, HSet.mk_empty, AccessiblePointedGraph.mk_kpairGraph] at same
            exact (ordered_pair_not_empty _ _ same).elim
        | cons next rest =>
            simp only [listGraph, AccessiblePointedGraph.mk_kpairGraph] at same
            have parts := HSet.kpair_inj.mp same
            exact congrArg₂ List.cons (graph_injective head next parts.1)
              (listGraph_injective tail rest parts.2)
  termination_by structural first
end

/-- A fully constructed coding of symbols, variables, every grounded case,
and arbitrary finite nested expressions. -/
def coding : ArgumentCoding Atom := ⟨graph, fun _ _ => graph_injective _ _⟩

theorem reading_equal_iff (first second : Atom) :
    coding.reading first = coding.reading second ↔ first = second :=
  ⟨fun same => coding.injective same, fun same => congrArg coding.reading same⟩

theorem symbol_variable_separated (name : String) :
    coding.reading (.symbol name) ≠ coding.reading (.var name) := by
  intro same
  cases coding.injective same

theorem symbol_grounded_separated (name : String) (value : GroundedValue) :
    coding.reading (.symbol name) ≠ coding.reading (.grounded value) := by
  intro same
  cases coding.injective same

theorem expressions_retain_order (first second : Atom) (different : first ≠ second) :
    coding.reading (.expression [first, second]) ≠
      coding.reading (.expression [second, first]) := by
  intro same
  have equal := Atom.expression.inj (coding.injective same)
  exact different (List.cons.inj equal).1

theorem expressions_retain_multiplicity (value : Atom) :
    coding.reading (.expression [value, value]) ≠ coding.reading (.expression [value]) := by
  intro same
  have equal := Atom.expression.inj (coding.injective same)
  have lengths := congrArg List.length equal
  exact Nat.noConfusion (Nat.succ.inj lengths)

theorem custom_type_names_retained (first second payload : String) (different : first ≠ second) :
    coding.reading (.grounded (.custom first payload)) ≠
      coding.reading (.grounded (.custom second payload)) := by
  intro same
  have equal := GroundedValue.custom.inj (Atom.grounded.inj (coding.injective same))
  exact different equal.1

end Mettapedia.GSLT.Logic.ProgrammableSpaceAtomCoding
