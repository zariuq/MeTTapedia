import Mettapedia.GSLT.Logic.ProgrammableSpaceAtomCoding
import Mettapedia.GSLT.Logic.ProgrammableSpaceReadings
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls

/-!
# Material readings of actual MM2 matcher rows

An MM2 row retains an ordered substitution and a stack of source witnesses.
The witness readout reverses the stack into authored premise order. Each
witness retains both its literal atom and its physical source position.
Ordered graph codings retain every field; unordered conclusion support is
an explicitly weaker readout.

The concrete instance uses the existing structural matcher on its actual
source, including the shared query occurrence and two distinct joining paths.
Counting those rows does not establish independence of their evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ProgrammableSpaceMM2EvidenceMaterial

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT.ProgrammableSpaceReadings
open Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2
open MM2MatchingCursor

universe u

def pairCoding {First Second : Type u}
    (first : ArgumentCoding First) (second : ArgumentCoding Second) :
    ArgumentCoding (First × Second) where
  graph value := AccessiblePointedGraph.kpairGraph (first.graph value.1) (second.graph value.2)
  injective := by
    intro left right same
    change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
      HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    exact Prod.ext (first.injective (HSet.kpair_inj.mp same).1)
      (second.injective (HSet.kpair_inj.mp same).2)

theorem pair_reading {First Second : Type u}
    (first : ArgumentCoding First) (second : ArgumentCoding Second) (value : First × Second) :
    (pairCoding first second).reading value =
      HSet.kpair (first.reading value.1) (second.reading value.2) :=
  AccessiblePointedGraph.mk_kpairGraph _ _

def positions : ArgumentCoding Nat where
  graph := OutcomeLabels.chainGraph
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph first) = HSet.mk (OutcomeLabels.chainGraph second) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact OutcomeLabels.chainValue_injective same

variable (atoms : ArgumentCoding Atom) (names : ArgumentCoding String)

def entries : ArgumentCoding Entry := pairCoding atoms positions

def bindings : ArgumentCoding (String × Atom) := pairCoding names atoms

def rowParts : ArgumentCoding Row := pairCoding (bindings atoms names).lists (entries atoms).lists

def sourceOrderedRow (row : Row) : Row := (row.1, row.2.reverse)

theorem sourceOrderedRow_injective : Function.Injective sourceOrderedRow := by
  intro first second same
  apply Prod.ext
  · have substitutions := congrArg Prod.fst same
    exact substitutions
  · have witnesses := congrArg Prod.snd same
    exact List.reverse_injective witnesses

def rows : ArgumentCoding Row where
  graph row := (rowParts atoms names).graph (sourceOrderedRow row)
  injective := fun _ _ same => sourceOrderedRow_injective ((rowParts atoms names).injective same)

theorem entry_reading_eq_iff (first second : Entry) :
    (entries atoms).reading first = (entries atoms).reading second ↔
      first.1 = second.1 ∧ first.2 = second.2 := by
  constructor
  · intro same
    have equal := (entries atoms).injective same
    exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩
  · rintro ⟨firstEqual, secondEqual⟩
    exact congrArg (entries atoms).reading (Prod.ext firstEqual secondEqual)

theorem different_origins_retained (atom : Atom) (first second : Nat) (different : first ≠ second) :
    (entries atoms).reading (atom, first) ≠ (entries atoms).reading (atom, second) := by
  intro same
  exact different ((entry_reading_eq_iff atoms _ _).mp same).2

theorem row_reading_eq_iff (first second : Row) :
    (rows atoms names).reading first = (rows atoms names).reading second ↔ first = second :=
  ⟨fun same => (rows atoms names).injective same, fun same => congrArg _ same⟩

theorem row_reading (row : Row) :
    (rows atoms names).reading row =
      HSet.kpair (occurrences (bindings atoms names) row.1)
        (occurrences (entries atoms) row.2.reverse) :=
  pair_reading (bindings atoms names).lists (entries atoms).lists (sourceOrderedRow row)

theorem row_kernel (first second : Row) :
    (rows atoms names).reading first = (rows atoms names).reading second ↔
      first.1 = second.1 ∧ first.2.reverse = second.2.reverse := by
  constructor
  · intro same
    have equal := (row_reading_eq_iff atoms names _ _).mp same
    exact ⟨congrArg Prod.fst equal, congrArg (fun row : Row => row.2.reverse) equal⟩
  · rintro ⟨substitution, witnesses⟩
    exact (row_reading_eq_iff atoms names _ _).mpr
      (Prod.ext substitution (List.reverse_injective witnesses))

def batch (values : List Row) : HSet := occurrences (rows atoms names) values

theorem batch_eq_iff (first second : List Row) :
    batch atoms names first = batch atoms names second ↔ first = second :=
  occurrences_eq_iff (rows atoms names) first second

def resultSupport (conclusion : Atom) (values : List Row) : HSet :=
  support atoms (values.map fun row => applySubst row.1 conclusion)

theorem result_member_iff (conclusion : Atom) (values : List Row) (atom : Atom) :
    atoms.reading atom ∈ resultSupport atoms conclusion values ↔
      ∃ row ∈ values, applySubst row.1 conclusion = atom := by
  rw [resultSupport, fact_member_iff]
  exact List.mem_map

theorem result_support_eq_iff (conclusion : Atom) (first second : List Row) :
    resultSupport atoms conclusion first = resultSupport atoms conclusion second ↔
      ∀ atom, (∃ row ∈ first, applySubst row.1 conclusion = atom) ↔
        ∃ row ∈ second, applySubst row.1 conclusion = atom := by
  rw [resultSupport, resultSupport, support_eq_iff]
  simp only [List.mem_map]

/-- This projection keeps the selected literal instruction, the entire ordered
source snapshot, and every ordered matcher row. Other request proof fields
are not declared as observations by this projection. -/
def receiptProjection (receipt : Receipt) : Atom × (List Atom × List Row) :=
  (receipt.request.directive.atom, receipt.before, receipt.rows)

def receiptParts : ArgumentCoding (Atom × (List Atom × List Row)) :=
  pairCoding atoms (pairCoding atoms.lists (rows atoms names).lists)

def receiptReading (receipt : Receipt) : HSet :=
  (receiptParts atoms names).reading (receiptProjection receipt)

theorem receipt_reading_eq_iff (first second : Receipt) :
    receiptReading atoms names first = receiptReading atoms names second ↔
      first.request.directive.atom = second.request.directive.atom ∧
        first.before = second.before ∧ first.rows = second.rows := by
  constructor
  · intro same
    have equal := (receiptParts atoms names).injective same
    exact ⟨congrArg Prod.fst equal, congrArg (fun value => value.2.1) equal,
      congrArg (fun value => value.2.2) equal⟩
  · rintro ⟨instruction, snapshot, matcherRows⟩
    exact congrArg (receiptParts atoms names).reading
      (Prod.ext instruction (Prod.ext snapshot matcherRows))

namespace ActualJoin

open Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls

def receipt : Receipt := ⟨joinRequest, joinSource, joinRows⟩

theorem row_count : joinRows.length = 2 := by
  simpa only [List.length_map] using two_paths_have_distinct_substitutions.1

def first : Row := joinRows.get ⟨0, by rw [row_count]; decide⟩
def second : Row := joinRows.get ⟨1, by rw [row_count]; decide⟩

theorem actual_rows : joinRows = [first, second] := by decide +kernel

theorem first_source_origins : first.2.reverse.map Prod.snd = [0, 1, 2] := by decide +kernel
theorem second_source_origins : second.2.reverse.map Prod.snd = [0, 3, 4] := by decide +kernel

theorem shared_query_occurrence :
    first.2.reverse.head? = some (context.head!, 0) ∧
      second.2.reverse.head? = some (context.head!, 0) := by decide +kernel

theorem both_emit_reachable :
    applySubst first.1 conclusion = reachable ∧ applySubst second.1 conclusion = reachable := by
  decide +kernel

theorem substitutions_differ : first.1 ≠ second.1 := by decide +kernel

theorem actual_material_rows_differ :
    (rows atoms names).reading first ≠ (rows atoms names).reading second := by
  intro same
  exact substitutions_differ (congrArg Prod.fst ((rows atoms names).injective same))

theorem both_origins_are_material_members :
    (entries atoms).reading (context.head!, 0) ∈ support (entries atoms) first.2.reverse ∧
      (entries atoms).reading (context.head!, 0) ∈ support (entries atoms) second.2.reverse := by
  constructor
  · rw [fact_member_iff]
    exact List.mem_of_mem_head? shared_query_occurrence.1
  · rw [fact_member_iff]
    exact List.mem_of_mem_head? shared_query_occurrence.2

theorem same_fact_support_two_material_rows :
    resultSupport atoms conclusion [first] = resultSupport atoms conclusion [second] ∧
      (rows atoms names).reading first ≠ (rows atoms names).reading second := by
  refine ⟨?_, actual_material_rows_differ atoms names⟩
  unfold resultSupport
  rw [List.map_singleton, List.map_singleton, both_emit_reachable.1, both_emit_reachable.2]

theorem published_support_is_single_result :
    resultSupport atoms conclusion joinRows = support atoms [reachable] := by
  unfold resultSupport
  rw [two_paths_emit_same_conclusion]
  exact duplicate_support atoms reachable

theorem material_batch_retains_two_rows :
    batch atoms names joinRows ≠ batch atoms names [first] := by
  intro same
  have equal := (batch_eq_iff atoms names _ _).mp same
  have lengths := congrArg List.length equal
  rw [row_count] at lengths
  exact (by decide : (2 : Nat) ≠ 1) lengths

theorem fact_support_cannot_recover_rows :
    ¬ ∃ recover : HSet → HSet,
      recover (resultSupport atoms conclusion [first]) = (rows atoms names).reading first ∧
        recover (resultSupport atoms conclusion [second]) = (rows atoms names).reading second := by
  rintro ⟨recover, left, right⟩
  have equal := congrArg recover (same_fact_support_two_material_rows atoms names).1
  rw [left, right] at equal
  exact actual_material_rows_differ atoms names equal

/-- Instantiate the constructed dictionaries on the native atoms and names. -/
theorem native_join_readouts :
    resultSupport ProgrammableSpaceAtomCoding.coding conclusion [first] =
      resultSupport ProgrammableSpaceAtomCoding.coding conclusion [second] ∧
        (rows ProgrammableSpaceAtomCoding.coding ProgrammableSpaceAtomCoding.strings).reading first ≠
          (rows ProgrammableSpaceAtomCoding.coding ProgrammableSpaceAtomCoding.strings).reading second :=
  same_fact_support_two_material_rows ProgrammableSpaceAtomCoding.coding ProgrammableSpaceAtomCoding.strings

end ActualJoin

end Mettapedia.GSLT.Logic.ProgrammableSpaceMM2EvidenceMaterial
