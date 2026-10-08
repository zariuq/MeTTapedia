import Mettapedia.GSLT.Logic.ProgrammableSpaceMM2EvidenceMaterial
import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceMaterial

/-!
# Typed proof receipts for actual MM2 ground matcher rows

Every matched row supplies a ground Horn instance. Its ordered premise list
is read from the retained witnesses, and each premise proof names its actual
position in the captured source snapshot. Lookup equality checks that position
before constructing the typed input proof. The original directive and ordered
substitution remain in the separate MM2 receipt readout.

This interprets completed rows as ground rule instances. It does not identify
ground-instance positions with the positions of uninstantiated MM2 templates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ProgrammableSpaceMM2EvidenceHorn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Mettapedia.GSLT.Core.AnnotatedHorn
open Mettapedia.GSLT.ProgrammableSpaceEvidence
open Mettapedia.TypeTheory.MaterialSets.Hypersets

def groundRule (conclusion : Atom) (row : Row) : DefiniteRule Atom :=
  ⟨row.2.reverse.map Prod.fst, applySubst row.1 conclusion⟩

/-- The retained ground premises agree with the authored templates under the
actual ordered substitution, rather than defining template matching by fiat. -/
def RowMatches (premises : List Atom) (row : Row) : Prop :=
  row.2.reverse.map Prod.fst = premises.map (applySubst row.1)

theorem ground_rule_matches (premises : List Atom) (conclusion : Atom) (row : Row)
    (agreement : RowMatches premises row) :
    groundRule conclusion row =
      ⟨premises.map (applySubst row.1), applySubst row.1 conclusion⟩ := by
  change (⟨_, _⟩ : DefiniteRule Atom) = ⟨_, _⟩
  rw [show row.2.reverse.map Prod.fst = premises.map (applySubst row.1) from agreement]

def templatesChecked (premises : List Atom) (rows : List Row) : Bool :=
  rows.all fun row => decide (row.2.reverse.map Prod.fst = premises.map (applySubst row.1))

theorem templatesChecked_iff (premises : List Atom) (rows : List Row) :
    templatesChecked premises rows = true ↔ ∀ row ∈ rows, RowMatches premises row := by
  simp only [templatesChecked, RowMatches, List.all_eq_true, decide_eq_true_eq]

def groundSource (snapshot : List Atom) (conclusion : Atom) (rows : List Row) :
    Source Atom (Fin snapshot.length) where
  input index := snapshot.get index
  rules := rows.map (groundRule conclusion)

def groundIndex (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (index : Fin rows.length) : (groundSource snapshot conclusion rows).RuleIndex :=
  ⟨index.val, by simpa only [groundSource, List.length_map] using index.isLt⟩

theorem rule_at (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (index : Fin rows.length) :
    (groundSource snapshot conclusion rows).rule (groundIndex snapshot conclusion rows index) =
      groundRule conclusion (rows.get index) := by
  simp only [Source.rule, groundSource, groundIndex, List.get_eq_getElem, List.getElem_map]

theorem premise_count (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (index : Fin rows.length) :
    ((groundSource snapshot conclusion rows).rule
      (groundIndex snapshot conclusion rows index)).body.length =
        (rows.get index).2.reverse.length :=
  (congrArg (fun rule : DefiniteRule Atom => rule.body.length)
    (rule_at snapshot conclusion rows index)).trans (List.length_map _)

theorem get_cast {A : Type} {first second : List A} (equal : first = second)
    (index : Fin first.length) :
    first.get index = second.get (Fin.cast (congrArg List.length equal) index) := by
  cases equal
  rfl

def witnessAt (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (index : Fin rows.length)
    (position : (groundSource snapshot conclusion rows).PremiseIndex
      (groundIndex snapshot conclusion rows index)) : Entry :=
  (rows.get index).2.reverse.get (Fin.cast (premise_count snapshot conclusion rows index) position)

theorem witness_is_premise (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (index : Fin rows.length)
    (position : (groundSource snapshot conclusion rows).PremiseIndex
      (groundIndex snapshot conclusion rows index)) :
    (witnessAt snapshot conclusion rows index position).1 =
      (groundSource snapshot conclusion rows).premise
        (groundIndex snapshot conclusion rows index) position := by
  have body : ((groundSource snapshot conclusion rows).rule
      (groundIndex snapshot conclusion rows index)).body =
      (rows.get index).2.reverse.map Prod.fst :=
    congrArg DefiniteRule.body (rule_at snapshot conclusion rows index)
  have converted := get_cast body position
  unfold Source.premise
  rw [converted]
  simp only [witnessAt, List.get_eq_getElem, Fin.val_cast, List.getElem_map]

/-- Source-relative physical positions are retained data, checked by lookup. -/
def WitnessesValid (snapshot : List Atom) (rows : List Row) : Prop :=
  ∀ row ∈ rows, ∀ entry ∈ row.2.reverse, snapshot[entry.2]? = some entry.1

def witnessesChecked (snapshot : List Atom) (rows : List Row) : Bool :=
  rows.all fun row => row.2.reverse.all fun entry => decide (snapshot[entry.2]? = some entry.1)

theorem witnessesChecked_iff (snapshot : List Atom) (rows : List Row) :
    witnessesChecked snapshot rows = true ↔ WitnessesValid snapshot rows := by
  simp only [witnessesChecked, WitnessesValid, List.all_eq_true, decide_eq_true_eq]

theorem witness_lookup (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length)
    (position : (groundSource snapshot conclusion rows).PremiseIndex
      (groundIndex snapshot conclusion rows index)) :
    snapshot[(witnessAt snapshot conclusion rows index position).2]? =
      some (witnessAt snapshot conclusion rows index position).1 :=
  valid _ (List.get_mem _ _) _ (List.get_mem _ _)

def physicalOrigin (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length)
    (position : (groundSource snapshot conclusion rows).PremiseIndex
      (groundIndex snapshot conclusion rows index)) : Fin snapshot.length :=
  ⟨(witnessAt snapshot conclusion rows index position).2, by
    obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp
      (witness_lookup snapshot conclusion rows valid index position)
    exact bounded⟩

theorem physicalOrigin_atom (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length)
    (position : (groundSource snapshot conclusion rows).PremiseIndex
      (groundIndex snapshot conclusion rows index)) :
    (groundSource snapshot conclusion rows).input
      (physicalOrigin snapshot conclusion rows valid index position) =
        (groundSource snapshot conclusion rows).premise
          (groundIndex snapshot conclusion rows index) position := by
  obtain ⟨_, equal⟩ := List.getElem?_eq_some_iff.mp
    (witness_lookup snapshot conclusion rows valid index position)
  exact equal.trans (witness_is_premise snapshot conclusion rows index position)

def premiseReceipt (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length)
    (position : (groundSource snapshot conclusion rows).PremiseIndex
      (groundIndex snapshot conclusion rows index)) :
    Derivation (groundSource snapshot conclusion rows)
      ((groundSource snapshot conclusion rows).premise
        (groundIndex snapshot conclusion rows index) position) :=
  (physicalOrigin_atom snapshot conclusion rows valid index position) ▸
    Derivation.input (physicalOrigin snapshot conclusion rows valid index position)

def rowReceipt (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length) :
    Receipt (groundSource snapshot conclusion rows) :=
  ⟨_, Derivation.rule (groundIndex snapshot conclusion rows index)
    (premiseReceipt snapshot conclusion rows valid index)⟩

theorem row_fact (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length) :
    (rowReceipt snapshot conclusion rows valid index).fact =
      applySubst (rows.get index).1 conclusion := by
  change ((groundSource snapshot conclusion rows).rule
    (groundIndex snapshot conclusion rows index)).head = _
  rw [rule_at]
  rfl

theorem row_root (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length) :
    (rowReceipt snapshot conclusion rows valid index).root =
      some (groundIndex snapshot conclusion rows index) := rfl

theorem origins_transport {SourceAtom SourceOrigin : Type} {source : Source SourceAtom SourceOrigin}
    {first second : SourceAtom} (equal : first = second) (proof : Derivation source first) :
    (equal ▸ proof).origins = proof.origins := by
  cases equal
  rfl

theorem premise_origin (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length)
    (position : (groundSource snapshot conclusion rows).PremiseIndex
      (groundIndex snapshot conclusion rows index)) :
    (premiseReceipt snapshot conclusion rows valid index position).origins =
      [physicalOrigin snapshot conclusion rows valid index position] :=
  origins_transport _ _

theorem flatten_ofFn_singletons {A : Type} {n : Nat} (values : Fin n → A) :
    (List.ofFn fun index => [values index]).flatten = List.ofFn values := by
  induction n with
  | zero => rfl
  | succ n induction =>
    rw [List.ofFn_succ, List.flatten_cons, induction, List.ofFn_succ]
    rfl

theorem row_origins (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (index : Fin rows.length) :
    (rowReceipt snapshot conclusion rows valid index).origins.map Fin.val =
      (rows.get index).2.reverse.map Prod.snd := by
  simp only [rowReceipt, Receipt.origins, Derivation.origins_rule, premise_origin,
    List.map_flatten, List.map_ofFn]
  change (List.ofFn fun position => [(witnessAt snapshot conclusion rows index position).2]).flatten = _
  rw [flatten_ofFn_singletons]
  rw [List.ofFn_congr (premise_count snapshot conclusion rows index)]
  simp only [witnessAt, Fin.cast_cast, Fin.cast_refl]
  change List.ofFn (Prod.snd ∘ (rows.get index).2.reverse.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem row_receipt_kernel (snapshot : List Atom) (conclusion : Atom) (rows : List Row)
    (valid : WitnessesValid snapshot rows) (first second : Fin rows.length) :
    rowReceipt snapshot conclusion rows valid first =
      rowReceipt snapshot conclusion rows valid second ↔ first = second := by
  constructor
  · intro same
    have roots := congrArg (fun receipt : Receipt (groundSource snapshot conclusion rows) => receipt.root) same
    rw [row_root, row_root] at roots
    have indices := Option.some.inj roots
    have offsets := congrArg Fin.val indices
    exact Fin.ext offsets
  · intro same
    cases same
    rfl

def sourcePositions (snapshot : List Atom) : ArgumentCoding (Fin snapshot.length) where
  graph index := ProgrammableSpaceMM2EvidenceMaterial.positions.graph index.val
  injective := fun _ _ same =>
    Fin.ext (ProgrammableSpaceMM2EvidenceMaterial.positions.injective same)

def typedReading (atoms : ArgumentCoding Atom) (snapshot : List Atom)
    (conclusion : Atom) (rows : List Row) (valid : WitnessesValid snapshot rows)
    (index : Fin rows.length) : HSet :=
  Material.reading atoms (sourcePositions snapshot) (rowReceipt snapshot conclusion rows valid index)

theorem typed_reading_kernel (atoms : ArgumentCoding Atom) (snapshot : List Atom)
    (conclusion : Atom) (rows : List Row) (valid : WitnessesValid snapshot rows)
    (first second : Fin rows.length) :
    typedReading atoms snapshot conclusion rows valid first =
      typedReading atoms snapshot conclusion rows valid second ↔ first = second :=
  (Material.reading_kernel atoms (sourcePositions snapshot) _ _).trans
    (row_receipt_kernel snapshot conclusion rows valid first second)

namespace ActualJoin

open Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls

theorem lookup_checked : witnessesChecked joinSource joinRows = true := by decide +kernel

theorem valid : WitnessesValid joinSource joinRows :=
  (witnessesChecked_iff joinSource joinRows).mp lookup_checked

theorem actual_template_matching :
    ∀ row ∈ joinRows, RowMatches inputs row :=
  (templatesChecked_iff inputs joinRows).mp (by decide +kernel)

theorem actual_ground_instance (index : Fin joinRows.length) :
    (groundSource joinSource conclusion joinRows).rule
      (groundIndex joinSource conclusion joinRows index) =
      ⟨inputs.map (applySubst (joinRows.get index).1),
        applySubst (joinRows.get index).1 conclusion⟩ :=
  (rule_at joinSource conclusion joinRows index).trans
    (ground_rule_matches inputs conclusion _ (actual_template_matching _ (List.get_mem _ _)))

def firstIndex : Fin joinRows.length :=
  ⟨0, by rw [ProgrammableSpaceMM2EvidenceMaterial.ActualJoin.row_count]; decide⟩
def secondIndex : Fin joinRows.length :=
  ⟨1, by rw [ProgrammableSpaceMM2EvidenceMaterial.ActualJoin.row_count]; decide⟩

def first : Receipt (groundSource joinSource conclusion joinRows) :=
  rowReceipt joinSource conclusion joinRows valid firstIndex

def second : Receipt (groundSource joinSource conclusion joinRows) :=
  rowReceipt joinSource conclusion joinRows valid secondIndex

theorem facts_equal : first.fact = reachable ∧ second.fact = reachable := by
  constructor
  · exact (row_fact joinSource conclusion joinRows valid firstIndex).trans
      ProgrammableSpaceMM2EvidenceMaterial.ActualJoin.both_emit_reachable.1
  · exact (row_fact joinSource conclusion joinRows valid secondIndex).trans
      ProgrammableSpaceMM2EvidenceMaterial.ActualJoin.both_emit_reachable.2

theorem actual_source_origins :
    first.origins.map Fin.val = [0, 1, 2] ∧ second.origins.map Fin.val = [0, 3, 4] :=
  ⟨(row_origins joinSource conclusion joinRows valid firstIndex).trans
      ProgrammableSpaceMM2EvidenceMaterial.ActualJoin.first_source_origins,
    (row_origins joinSource conclusion joinRows valid secondIndex).trans
      ProgrammableSpaceMM2EvidenceMaterial.ActualJoin.second_source_origins⟩

theorem different_roots : first.root ≠ second.root := by
  intro same
  change some (groundIndex joinSource conclusion joinRows firstIndex) =
    some (groundIndex joinSource conclusion joinRows secondIndex) at same
  have positions := congrArg Fin.val (Option.some.inj same)
  exact (by decide : (0 : Nat) ≠ 1) positions

theorem different_receipts : first ≠ second := by
  intro same
  exact different_roots (congrArg Receipt.root same)

def commonOrigin : Fin joinSource.length := ⟨0, by decide +kernel⟩

theorem shared_origin : commonOrigin ∈ first.origins ∧ commonOrigin ∈ second.origins := by
  constructor
  · have present : 0 ∈ first.origins.map Fin.val := by
      rw [actual_source_origins.1]
      exact List.mem_cons_self
    obtain ⟨origin, member, same⟩ := List.mem_map.mp present
    have equal : origin = commonOrigin := Fin.ext same
    exact equal ▸ member
  · have present : 0 ∈ second.origins.map Fin.val := by
      rw [actual_source_origins.2]
      exact List.mem_cons_self
    obtain ⟨origin, member, same⟩ := List.mem_map.mp present
    have equal : origin = commonOrigin := Fin.ext same
    exact equal ▸ member

theorem not_origin_separated : ¬ Receipt.OriginSeparated first second :=
  Receipt.not_originSeparated_of_shared first second commonOrigin shared_origin.1 shared_origin.2

theorem same_material_fact_distinct_proof (atoms : ArgumentCoding Atom) :
    atoms.reading first.fact = atoms.reading second.fact ∧
      Material.reading atoms (sourcePositions joinSource) first ≠
        Material.reading atoms (sourcePositions joinSource) second := by
  refine ⟨?_, ?_⟩
  · rw [facts_equal.1, facts_equal.2]
  · intro same
    exact different_receipts (Material.reading_injective atoms (sourcePositions joinSource) same)

theorem fact_cannot_recover_proof (atoms : ArgumentCoding Atom) :
    ¬ ∃ recover : HSet → HSet,
      recover (atoms.reading first.fact) = Material.reading atoms (sourcePositions joinSource) first ∧
        recover (atoms.reading second.fact) = Material.reading atoms (sourcePositions joinSource) second := by
  rintro ⟨recover, left, right⟩
  have same := congrArg recover (same_material_fact_distinct_proof atoms).1
  rw [left, right] at same
  exact (same_material_fact_distinct_proof atoms).2 same

def badRow : Row := ([], [(reachable, joinSource.length)])

theorem invalid_origin_refused : ¬ WitnessesValid joinSource [badRow] := by
  rw [← witnessesChecked_iff]
  decide +kernel

theorem native_typed_readouts :
    ProgrammableSpaceAtomCoding.coding.reading first.fact =
      ProgrammableSpaceAtomCoding.coding.reading second.fact ∧
        Material.reading ProgrammableSpaceAtomCoding.coding (sourcePositions joinSource) first ≠
          Material.reading ProgrammableSpaceAtomCoding.coding (sourcePositions joinSource) second :=
  same_material_fact_distinct_proof ProgrammableSpaceAtomCoding.coding

end ActualJoin

end Mettapedia.GSLT.Logic.ProgrammableSpaceMM2EvidenceHorn
