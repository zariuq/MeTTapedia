import Mettapedia.OSLF.Syntax.BindingWireData
import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Rules
import Mathlib.Data.List.FinRange

/-! # Verified append-only tables for generated rule certificates -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Shared

open Mettapedia.TypeTheory
universe u
variable {P : Presentation.{u}} [DecidableEq P.Judgment]

theorem decodeFrom?_append (table : List (Entry P)) (first second : List (Row P)) :
    decodeFrom? table (first ++ second) = (decodeFrom? table first).bind (fun next => decodeFrom? next second) := by
  induction first generalizing table with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.cons_append, decodeFrom?]
      cases selected : decodeRow? table row with
      | none => rfl
      | some entry =>
          exact ih (table ++ [entry])

theorem lookup?_exact (table : List (Entry P)) (position : Nat) (wanted : P.Judgment) :
    (lookup? table position wanted).isSome = true ↔
      (table[position]?).map Sigma.fst = some wanted := by
  unfold lookup?
  cases found : table[position]? with
  | none => simp
  | some entry =>
      rcases entry with ⟨actual, tree⟩
      split <;> simp_all

theorem lookup?_append (table extra : List (Entry P)) (position : Nat) (wanted : P.Judgment)
    (found : (lookup? table position wanted).isSome = true) :
    (lookup? (table ++ extra) position wanted).isSome = true := by
  apply (lookup?_exact _ _ _).mpr
  have pointed := (lookup?_exact _ _ _).mp found
  obtain ⟨entry, atEntry, _⟩ := Option.map_eq_some_iff.mp pointed
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp atEntry).1]
  exact pointed

theorem decodeRow?_exact (table : List (Entry P)) (row : Row P) :
    (decodeRow? table row).isSome = true ↔ ValidRow (table.map Sigma.fst) row := by
  let select := fun position : Fin (P.premises row.rule).length =>
    lookup? table (row.references position) ((P.premises row.rule).get position)
  have same : (decodeRow? table row).isSome =
      (allFin? (fun position => P.Derivation ((P.premises row.rule).get position)) select).isSome := by
    unfold decodeRow?
    cases got : allFin? (fun position => P.Derivation ((P.premises row.rule).get position)) select <;> rfl
  rw [same]
  constructor
  · intro accepted
    cases got : allFin? (fun position => P.Derivation ((P.premises row.rule).get position)) select with
    | none => rw [got] at accepted; cases accepted
    | some values =>
        intro position
        rw [List.getElem?_map]
        apply (lookup?_exact _ _ _).mp
        have picked := allFin?_some got position
        change (select position).isSome = true
        rw [picked]
        rfl
  · intro valid
    apply allFin?_complete
    intro position
    apply (lookup?_exact _ _ _).mpr
    simpa only [List.getElem?_map] using valid position

structure Cache (P : Presentation.{u}) [DecidableEq P.Judgment] where
  rows : List (Row P)
  table : List (Entry P)
  decoded : decodeFrom? [] rows = some table

structure Located (cache : Cache P) (judgment : P.Judgment) where
  position : Nat
  pointed : (lookup? cache.table position judgment).isSome = true

structure Result (cache : Cache P) (judgment : P.Judgment) where
  next : Cache P
  prefixTable : cache.table.IsPrefix next.table
  located : Located next judgment

def Located.lift {cache next : Cache P} {judgment : P.Judgment}
    (located : Located cache judgment) (extended : cache.table.IsPrefix next.table) : Located next judgment :=
  ⟨located.position, by
    obtain ⟨extra, equal⟩ := extended
    rw [← equal]
    exact lookup?_append _ _ _ _ located.pointed⟩

def emptyCache : Cache P := ⟨[], [], rfl⟩

def find? (cache : Cache P) (judgment : P.Judgment) : Option (Located cache judgment) :=
  match found : cache.table.findIdx? (fun entry => decide (entry.1 = judgment)) with
  | none => none
  | some position => some ⟨position, by
      apply (lookup?_exact _ _ _).mpr
      obtain ⟨bounded, same, _first⟩ := List.findIdx?_eq_some_iff_getElem.mp found
      have equal : cache.table[position].1 = judgment := of_decide_eq_true same
      simpa only [List.getElem?_eq_getElem bounded, Option.map_some] using congrArg some equal⟩

/-- Earlier references are checked by the ordinary row decoder before a row
is appended. The success branch retains its decoder equality. -/
def appendRow (cache : Cache P) (rule : P.Rule)
    (children : (position : Fin (P.premises rule).length) → Located cache ((P.premises rule).get position)) :
    Result cache (P.conclusion rule) := by
  let row : Row P := ⟨rule, fun position => (children position).position⟩
  have allPresent : (allFin? (fun position => P.Derivation ((P.premises rule).get position))
    (fun position => lookup? cache.table (row.references position) ((P.premises rule).get position))).isSome = true :=
    allFin?_complete (fun position => (children position).pointed)
  match got : allFin? (fun position => P.Derivation ((P.premises rule).get position))
      (fun position => lookup? cache.table (row.references position) ((P.premises rule).get position)) with
  | none => rw [got] at allPresent; cases allPresent
  | some values =>
      let entry : Entry P := ⟨P.conclusion rule, .node ⟨rule, rfl⟩ (fun position => values position.down)⟩
      have rowChecked : decodeRow? cache.table row = some entry := by
        unfold decodeRow?
        rw [got]
        rfl
      let next : Cache P := ⟨cache.rows ++ [row], cache.table ++ [entry], by
        rw [decodeFrom?_append, cache.decoded]
        change decodeFrom? cache.table [row] = some (cache.table ++ [entry])
        simp only [decodeFrom?, rowChecked]
        rfl⟩
      exact ⟨next, ⟨[entry], rfl⟩, ⟨cache.table.length, by
        apply (lookup?_exact _ _ _).mpr
        simp only [next, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.map_some, entry]⟩⟩

structure ForestResult (cache : Cache P) {n : Nat} (judgments : Fin n → P.Judgment) where
  next : Cache P
  prefixTable : cache.table.IsPrefix next.table
  located : (position : Fin n) → Located next (judgments position)

def sequence : {n : Nat} → (judgments : Fin n → P.Judgment) →
    ((position : Fin n) → (cache : Cache P) → Result cache (judgments position)) →
    (cache : Cache P) → ForestResult cache judgments
  | 0, _, _, cache => ⟨cache, ⟨[], List.append_nil _⟩, fun position => nomatch position⟩
  | n + 1, judgments, actions, cache =>
      let first := actions 0 cache
      let rest := sequence (fun position : Fin n => judgments position.succ)
        (fun position => actions position.succ) first.next
      ⟨rest.next, first.prefixTable.trans rest.prefixTable,
        Fin.cases (first.located.lift rest.prefixTable) rest.located⟩

/-! ## Exactness and work of direct judgment checking -/

theorem inspectPremises_exact (table : List P.Judgment) (row : Row P)
    (positions : List (Fin (P.premises row.rule).length)) :
    (inspectPremises table row positions).1 = true ↔
      ∀ position ∈ positions, table[row.references position]? = some ((P.premises row.rule).get position) := by
  induction positions with
  | nil => simp [inspectPremises]
  | cons position rest ih =>
      by_cases same : table[row.references position]? = some ((P.premises row.rule).get position)
      · rw [inspectPremises, if_pos same]
        change (inspectPremises table row rest).1 = true ↔ _
        rw [List.forall_mem_cons]
        exact ⟨fun accepted => ⟨same, ih.mp accepted⟩, fun both => ih.mpr both.2⟩
      · rw [inspectPremises, if_neg same]
        rw [List.forall_mem_cons]
        exact ⟨fun impossible => Bool.noConfusion impossible, fun both => (same both.1).elim⟩

theorem inspectPremises_checks_le (table : List P.Judgment) (row : Row P)
    (positions : List (Fin (P.premises row.rule).length)) :
    (inspectPremises table row positions).2 ≤ positions.length := by
  induction positions with
  | nil => simp [inspectPremises]
  | cons position rest ih =>
      simp only [inspectPremises]
      split
      · simpa only [Prod.snd, List.length_cons] using Nat.add_le_add_right ih 1
      · simp

theorem inspectPremises_checks_eq (table : List P.Judgment) (row : Row P)
    (positions : List (Fin (P.premises row.rule).length))
    (accepted : (inspectPremises table row positions).1 = true) :
    (inspectPremises table row positions).2 = positions.length := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      simp only [inspectPremises] at accepted ⊢
      split at accepted
      · rename_i same
        simp only [if_pos same, ih accepted, List.length_cons]
      · cases accepted

theorem inspectRow_exact (table : List P.Judgment) (row : Row P) :
    (inspectRow table row).1 = true ↔ ValidRow table row := by
  simpa only [inspectRow, ValidRow, List.mem_finRange, forall_const] using
    inspectPremises_exact table row (List.finRange (P.premises row.rule).length)

theorem inspectRow_checks_le (table : List P.Judgment) (row : Row P) :
    (inspectRow table row).2 ≤ (P.premises row.rule).length := by
  simpa only [inspectRow, List.length_finRange] using
    inspectPremises_checks_le table row (List.finRange (P.premises row.rule).length)

theorem inspectRow_checks_eq (table : List P.Judgment) (row : Row P)
    (accepted : (inspectRow table row).1 = true) :
    (inspectRow table row).2 = (P.premises row.rule).length := by
  simpa only [inspectRow, List.length_finRange] using
    inspectPremises_checks_eq table row (List.finRange (P.premises row.rule).length) accepted

theorem decodeRow?_conclusion (table : List (Entry P)) (row : Row P) (entry : Entry P)
    (decoded : decodeRow? table row = some entry) : entry.1 = P.conclusion row.rule := by
  unfold decodeRow? at decoded
  cases got : allFin? (fun position => P.Derivation ((P.premises row.rule).get position))
      (fun position => lookup? table (row.references position) ((P.premises row.rule).get position)) with
  | none => simp only [got, Bind.bind, Option.bind] at decoded; cases decoded
  | some children =>
      simp only [got, Bind.bind, Option.bind, pure, Option.some.injEq] at decoded
      cases decoded
      rfl

/-- Direct checking computes exactly the projection of the original
reconstruction table, including every refusal. -/
theorem inspectRows_projection (table : List (Entry P)) (rows : List (Row P)) :
    (inspectRows (table.map Sigma.fst) rows).table =
      (decodeFrom? table rows).map (List.map Sigma.fst) := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rest ih =>
      cases decoded : decodeRow? table row with
      | none =>
          have refused : (inspectRow (table.map Sigma.fst) row).1 = false := by
            apply Bool.eq_false_iff.mpr
            intro accepted
            have present := (decodeRow?_exact table row).mpr ((inspectRow_exact _ row).mp accepted)
            rw [decoded] at present
            cases present
          simp only [inspectRows, refused, Bool.false_eq_true, ↓reduceIte,
            decodeFrom?, decoded, Bind.bind, Option.bind, Option.map_none]
      | some entry =>
          have accepted : (inspectRow (table.map Sigma.fst) row).1 = true :=
            (inspectRow_exact _ row).mpr ((decodeRow?_exact table row).mp (by rw [decoded]; rfl))
          have conclusion := decodeRow?_conclusion table row entry decoded
          simp only [inspectRows, accepted, ↓reduceIte, decodeFrom?, decoded, Bind.bind, Option.bind]
          simpa only [List.map_append, List.map_cons, List.map_nil, conclusion] using ih (table ++ [entry])

/-- The reference/root checker compares complete literal judgments. -/
theorem judgmentLookup_eq (table : List (Entry P)) (position : Nat) (wanted : P.Judgment) :
    decide ((table.map Sigma.fst)[position]? = some wanted) = (lookup? table position wanted).isSome := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq, List.getElem?_map] using (lookup?_exact table position wanted).symm

/-- No certificate is accepted or refused differently by the direct
judgment table and the original derivation-reconstruction checker. -/
theorem checkJudgments_eq_check (certificate : Certificate P) (wanted : P.Judgment) :
    checkJudgments certificate wanted = check certificate wanted := by
  have projection := inspectRows_projection ([] : List (Entry P)) certificate.rows
  cases decoded : decodeFrom? [] certificate.rows with
  | none =>
      simp only [decoded, Option.map_none, List.map_nil] at projection
      simp only [checkJudgments, checkJudgmentsWithWork_eq_inspectRows, projection, check, reconstruct?,
        decoded, Bind.bind, Option.bind, Option.isSome_none]
  | some table =>
      simp only [decoded, Option.map_some, List.map_nil] at projection
      simp only [checkJudgments, checkJudgmentsWithWork_eq_inspectRows, projection, check, reconstruct?,
        decoded, Bind.bind, Option.bind]
      exact judgmentLookup_eq table certificate.root wanted

theorem checkJudgments_original (certificate : Certificate P) (wanted : P.Judgment)
    (accepted : checkJudgments certificate wanted = true) :
    ∃ derivation : P.Derivation wanted, reconstruct? certificate wanted = some derivation ∧
      Tree.check (Tree.erase derivation) wanted = true :=
  accepted_original certificate wanted ((checkJudgments_eq_check certificate wanted).symm.trans accepted)

theorem inspectRows_work_le (table : List P.Judgment) (rows : List (Row P)) :
    (inspectRows table rows).rows ≤ rows.length ∧
      (inspectRows table rows).premiseChecks ≤ premiseSlots rows := by
  induction rows generalizing table with
  | nil => simp [inspectRows, premiseSlots]
  | cons row rest ih =>
      have localBound := inspectRow_checks_le table row
      have laterBound := ih (table ++ [P.conclusion row.rule])
      simp only [inspectRows]
      split
      · simp only [List.length_cons, premiseSlots, List.map_cons, List.sum_cons] at *
        constructor <;> omega
      · simp only [List.length_cons, premiseSlots, List.map_cons, List.sum_cons]
        constructor <;> omega

/-- Success means every submitted row and every premise occurrence was
actually visited, including rows not used by the final root. -/
theorem inspectRows_work_eq (table : List P.Judgment) (rows : List (Row P))
    (accepted : (inspectRows table rows).table.isSome = true) :
    (inspectRows table rows).rows = rows.length ∧
      (inspectRows table rows).premiseChecks = premiseSlots rows := by
  induction rows generalizing table with
  | nil => simp [inspectRows, premiseSlots]
  | cons row rest ih =>
      simp only [inspectRows] at accepted ⊢
      split at accepted
      · rename_i valid
        have localExact := inspectRow_checks_eq table row valid
        have laterExact := ih (table ++ [P.conclusion row.rule]) accepted
        simp only [if_pos valid, List.length_cons, premiseSlots, List.map_cons, List.sum_cons] at *
        constructor <;> omega
      · cases accepted

/-- No expanded proof is retained: successful cache contents are exactly
the original table followed by each literal row conclusion, once. -/
theorem inspectRows_table (table : List P.Judgment) (rows : List (Row P))
    (result : List P.Judgment) (accepted : (inspectRows table rows).table = some result) :
    result = table ++ rows.map (fun row => P.conclusion row.rule) := by
  induction rows generalizing table with
  | nil => simpa only [inspectRows, Option.some.injEq, List.map_nil, List.append_nil] using accepted.symm
  | cons row rest ih =>
      simp only [inspectRows] at accepted
      split at accepted
      · have later := ih (table ++ [P.conclusion row.rule]) accepted
        simpa only [List.map_cons, List.append_assoc, List.singleton_append] using later
      · cases accepted

theorem inspectRows_table_length (table : List P.Judgment) (rows : List (Row P))
    (result : List P.Judgment) (accepted : (inspectRows table rows).table = some result) :
    result.length = table.length + rows.length := by
  rw [inspectRows_table table rows result accepted, List.length_append, List.length_map]

/-- These are bounds on the performed row/slot inspections. A bit-cost
reading additionally needs lookup, syntax equality, rule decoding and
payload-construction bounds for the actual selected representation. -/
theorem checkJudgments_work_le (certificate : Certificate P) (wanted : P.Judgment) :
    (checkJudgmentsWithWork certificate wanted).2.1 ≤ certificate.rows.length ∧
      (checkJudgmentsWithWork certificate wanted).2.2 ≤ premiseSlots certificate.rows + 1 := by
  have bounded := inspectRows_work_le ([] : List P.Judgment) certificate.rows
  cases selected : (inspectRows [] certificate.rows).table with
  | none =>
      simp only [checkJudgmentsWithWork_eq_inspectRows, selected]
      exact ⟨bounded.1, bounded.2.trans (Nat.le_add_right _ 1)⟩
  | some table =>
      simp only [checkJudgmentsWithWork_eq_inspectRows, selected]
      exact ⟨bounded.1, Nat.add_le_add_right bounded.2 1⟩

/-- An accepted graph checks every row, every premise slot, and its root. -/
theorem checkJudgments_work_eq (certificate : Certificate P) (wanted : P.Judgment)
    (accepted : checkJudgments certificate wanted = true) :
    (checkJudgmentsWithWork certificate wanted).2.1 = certificate.rows.length ∧
      (checkJudgmentsWithWork certificate wanted).2.2 = premiseSlots certificate.rows + 1 := by
  simp only [checkJudgments, checkJudgmentsWithWork_eq_inspectRows] at accepted
  cases selected : (inspectRows [] certificate.rows).table with
  | none => simp only [selected] at accepted; cases accepted
  | some table =>
      have exactWork := inspectRows_work_eq ([] : List P.Judgment) certificate.rows (by rw [selected]; rfl)
      simp only [checkJudgmentsWithWork_eq_inspectRows, selected]
      exact ⟨exactWork.1, congrArg (fun value => value + 1) exactWork.2⟩

end Mettapedia.OSLF.NativeTypes.Certificates.Shared

namespace Mettapedia.OSLF.NativeTypes.Certificates.Shared

open Mettapedia.TypeTheory
universe u
variable {source target : Presentation.{u}}

/-- Translate rule payloads while keeping each original reference ordinal. -/
def Row.map (translation : Presentation.Morphism source target) (row : Row source) : Row target where
  rule := translation.rule row.rule
  references position := row.references (translation.sourceIndex row.rule position)

def Certificate.map (translation : Presentation.Morphism source target)
    (certificate : Certificate source) : Certificate target where
  rows := certificate.rows.map (Row.map translation)
  root := certificate.root

theorem Row.map_reference (translation : Presentation.Morphism source target) (row : Row source)
    (position : Fin (source.premises row.rule).length) :
    (row.map translation).references (translation.targetIndex row.rule position) =
      row.references position := by
  simp only [Row.map, translation.source_target]

theorem Certificate.map_length (translation : Presentation.Morphism source target)
    (certificate : Certificate source) : (certificate.map translation).rows.length = certificate.rows.length :=
  List.length_map _

theorem Certificate.map_root (translation : Presentation.Morphism source target)
    (certificate : Certificate source) : (certificate.map translation).root = certificate.root := rfl

private theorem mapped_lookup_iff (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (table : List source.Judgment) (index : Nat) (wanted : source.Judgment) :
    (table.map translation.judgment)[index]? = some (translation.judgment wanted) ↔
      table[index]? = some wanted := by
  rw [List.getElem?_map]
  cases found : table[index]? with
  | none => simp
  | some actual =>
      simp only [Option.map_some, Option.some.injEq]
      exact injective.eq_iff

theorem validRow_map (translation : Presentation.Morphism source target)
    (table : List source.Judgment) (row : Row source) (valid : ValidRow table row) :
    ValidRow (table.map translation.judgment) (row.map translation) := by
  change ∀ position : Fin (target.premises (translation.rule row.rule)).length,
    (table.map translation.judgment)[row.references (translation.sourceIndex row.rule position)]? =
      some ((target.premises (translation.rule row.rule)).get position)
  intro position
  rw [translation.premise]
  rw [List.getElem?_map, valid]
  rfl

theorem validRow_map_iff (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (table : List source.Judgment) (row : Row source) :
    ValidRow (table.map translation.judgment) (row.map translation) ↔ ValidRow table row := by
  constructor
  · intro valid position
    have selected := valid (translation.targetIndex row.rule position)
    change (table.map translation.judgment)[row.references
      (translation.sourceIndex row.rule (translation.targetIndex row.rule position))]? =
        some ((target.premises (translation.rule row.rule)).get (translation.targetIndex row.rule position)) at selected
    rw [translation.premise] at selected
    rw [translation.source_target] at selected
    exact (mapped_lookup_iff translation injective table _ _).mp selected
  · exact validRow_map translation table row

section Checking
variable [DecidableEq source.Judgment] [DecidableEq target.Judgment]

/-- Every success and refusal visits the same premise positions on the image.
No judgment-equality or payload-construction time bound follows from this. -/
theorem inspectPremises_map (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (table : List source.Judgment) (row : Row source)
    (positions : List (Fin (target.premises (translation.rule row.rule)).length)) :
    inspectPremises (table.map translation.judgment) (row.map translation) positions =
      inspectPremises table row (positions.map (translation.sourceIndex row.rule)) := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      simp only [inspectPremises, List.map_cons, Row.map, translation.premise,
        mapped_lookup_iff translation injective]
      split
      · exact congrArg (fun later : Bool × Nat => (later.1, later.2 + 1)) ih
      · rfl

theorem inspectRow_map (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (table : List source.Judgment) (row : Row source) :
    inspectRow (table.map translation.judgment) (row.map translation) = inspectRow table row := by
  change inspectPremises (table.map translation.judgment) (row.map translation)
    (List.finRange (target.premises (translation.rule row.rule)).length) =
      inspectPremises table row (List.finRange (source.premises row.rule).length)
  rw [inspectPremises_map translation injective]
  have ordinals :
      (List.finRange (target.premises (translation.rule row.rule)).length).map
          (translation.sourceIndex row.rule) = List.finRange (source.premises row.rule).length := by
    calc
      _ = List.ofFn (translation.sourceIndex row.rule) := List.ofFn_eq_map.symm
      _ = List.ofFn (id : Fin (source.premises row.rule).length → _) :=
        translation.ofFn_sourceIndex row.rule id
      _ = _ := List.ofFn_id _
  rw [ordinals]

def JudgmentCheck.map (translation : Presentation.Morphism source target)
    (checked : JudgmentCheck source) : JudgmentCheck target where
  table := checked.table.map (List.map translation.judgment)
  rows := checked.rows
  premiseChecks := checked.premiseChecks

theorem inspectRows_map (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (table : List source.Judgment) (rows : List (Row source)) :
    inspectRows (table.map translation.judgment) (rows.map (Row.map translation)) =
      (inspectRows table rows).map translation := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.map_cons, inspectRows, inspectRow_map translation injective]
      split
      · rw [Row.map, translation.conclusion, ← List.map_singleton, ← List.map_append, ih]
        rfl
      · rfl

/-- Preservation of successful traversal needs no injectivity. -/
theorem inspectRows_map_of_success (translation : Presentation.Morphism source target)
    (table : List source.Judgment) (rows : List (Row source)) (result : List source.Judgment)
    (accepted : (inspectRows table rows).table = some result) :
    (inspectRows (table.map translation.judgment) (rows.map (Row.map translation))).table =
      some (result.map translation.judgment) := by
  induction rows generalizing table with
  | nil =>
      cases Option.some.inj accepted
      rfl
  | cons row rest ih =>
      by_cases valid : (inspectRow table row).1 = true
      · have tail : (inspectRows (table ++ [source.conclusion row.rule]) rest).table = some result := by
          simpa only [inspectRows, if_pos valid] using accepted
        have mappedValid : (inspectRow (table.map translation.judgment) (row.map translation)).1 = true :=
          (inspectRow_exact _ _).mpr (validRow_map translation table row ((inspectRow_exact _ _).mp valid))
        have mappedTail := ih (table ++ [source.conclusion row.rule]) tail
        simp only [List.map_cons, inspectRows, if_pos mappedValid]
        simpa only [Row.map, translation.conclusion, List.map_append, List.map_cons, List.map_nil]
          using mappedTail
      · simp only [inspectRows, if_neg valid] at accepted
        cases accepted

theorem checkJudgments_map (translation : Presentation.Morphism source target)
    (certificate : Certificate source) (wanted : source.Judgment)
    (accepted : checkJudgments certificate wanted = true) :
    checkJudgments (certificate.map translation) (translation.judgment wanted) = true := by
  cases original : (inspectRows [] certificate.rows).table with
  | none =>
      simp only [checkJudgments, checkJudgmentsWithWork_eq_inspectRows, original] at accepted
      cases accepted
  | some table =>
      have root : table[certificate.root]? = some wanted := by
        simpa only [checkJudgments, checkJudgmentsWithWork_eq_inspectRows, original, decide_eq_true_eq] using accepted
      have mapped :
          (inspectRows ([] : List target.Judgment) (certificate.rows.map (Row.map translation))).table =
            some (table.map translation.judgment) := by
        simpa only [List.map_nil] using inspectRows_map_of_success translation [] certificate.rows table original
      simp only [checkJudgments, checkJudgmentsWithWork_eq_inspectRows, Certificate.map, mapped,
        List.getElem?_map, root, Option.map_some, decide_true]

theorem checkJudgmentsWithWork_map (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (certificate : Certificate source) (wanted : source.Judgment) :
    checkJudgmentsWithWork (certificate.map translation) (translation.judgment wanted) =
      checkJudgmentsWithWork certificate wanted := by
  simp only [checkJudgmentsWithWork_eq_inspectRows, Certificate.map]
  rw [show ([] : List target.Judgment) = ([] : List source.Judgment).map translation.judgment from rfl,
    inspectRows_map translation injective]
  simp only [JudgmentCheck.map]
  cases found : (inspectRows [] certificate.rows).table with
  | none => rfl
  | some table =>
      simp only [Option.map_some, mapped_lookup_iff translation injective]

/-- Reflection concerns the actual translated graph, including invalid unused
rows. Extra target proofs remain outside this image theorem. -/
theorem checkJudgments_map_iff (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (certificate : Certificate source) (wanted : source.Judgment) :
    checkJudgments (certificate.map translation) (translation.judgment wanted) = true ↔
      checkJudgments certificate wanted = true := by
  rw [checkJudgments, checkJudgments, checkJudgmentsWithWork_map translation injective]

end Checking

theorem premiseSlots_map (translation : Presentation.Morphism source target) (rows : List (Row source)) :
    premiseSlots (rows.map (Row.map translation)) = premiseSlots rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [premiseSlots, List.map_cons, List.sum_cons] at ih ⊢
      rw [Row.map, translation.premises, List.length_map, ih]

@[simp] theorem Row.map_identity (row : Row source) :
    row.map (Presentation.Morphism.identity source) = row := by
  cases row
  rfl

theorem Row.map_comp {last : Presentation.{u}} (first : Presentation.Morphism source target)
    (second : Presentation.Morphism target last) (row : Row source) :
    (row.map first).map second = row.map (first.comp second) := by
  cases row
  rfl

@[simp] theorem Certificate.map_identity (certificate : Certificate source) :
    certificate.map (Presentation.Morphism.identity source) = certificate := by
  have identity : Row.map (Presentation.Morphism.identity source) = id := by
    funext row
    exact Row.map_identity row
  cases certificate with
  | mk rows root => simp only [Certificate.map, identity, List.map_id]

theorem Certificate.map_comp {last : Presentation.{u}} (first : Presentation.Morphism source target)
    (second : Presentation.Morphism target last) (certificate : Certificate source) :
    (certificate.map first).map second = certificate.map (first.comp second) := by
  have composition : Row.map second ∘ Row.map first = Row.map (first.comp second) := by
    funext row
    exact Row.map_comp first second row
  cases certificate with
  | mk rows root => simp only [Certificate.map, List.map_map, composition]

#print axioms checkJudgmentsWithWork_map
#print axioms checkJudgments_map_iff

end Mettapedia.OSLF.NativeTypes.Certificates.Shared



namespace Mettapedia.OSLF.NativeTypes.Certificates.Shared

universe u

namespace LiteralChecking

/-- The fixed literal representation used by the structural observer. Its
construction is separate from checking already materialized words. -/
structure Coding (α : Type u) where
  word : α → List Bool
  injective : Function.Injective word

abbrev Word := List Bool

/-- The count includes the final empty-list test. -/
def copy : Word → Word × Nat
  | [] => ([], 1)
  | bit :: rest =>
      let later := copy rest
      (bit :: later.1, later.2 + 1)

def equal : Word → Word → Bool × Nat
  | [], [] => (true, 1)
  | [], _ :: _ => (false, 1)
  | _ :: _, [] => (false, 1)
  | a :: as, b :: bs =>
      if a = b then
        let later := equal as bs
        (later.1, later.2 + 2)
      else (false, 2)

/-- Lookup pays for every visited table cell and copies the selected literal.
An out-of-bounds reference pays for the terminal empty cell. -/
def lookup : List Word → Nat → Option Word × Nat
  | [], _ => (none, 1)
  | word :: _, 0 =>
      let copied := copy word
      (some copied.1, copied.2 + 1)
  | _ :: rest, position + 1 =>
      let later := lookup rest position
      (later.1, later.2 + 1)

/-- Append copies the complete existing literal table, not only its spine. -/
def append : List Word → Word → List Word × Nat
  | [], word =>
      let copied := copy word
      ([copied.1], copied.2 + 1)
  | first :: rest, word =>
      let copied := copy first
      let later := append rest word
      (copied.1 :: later.1, copied.2 + later.2 + 1)

def compareAt (table : List Word) (position : Nat) (wanted : Word) : Bool × Nat :=
  let selected := lookup table position
  match selected.1 with
  | none => (false, selected.2 + 1)
  | some actual =>
      let expected := copy wanted
      let compared := equal actual expected.1
      (compared.1, selected.2 + expected.2 + compared.2 + 1)

def volume (table : List Word) : Nat := (table.map (fun word => word.length + 1)).sum

theorem member_volume {table : List Word} {actual : Word} (member : actual ∈ table) :
    actual.length + 1 ≤ volume table := by
  induction table with
  | nil => cases member
  | cons word rest ih =>
      rcases List.mem_cons.mp member with same | member
      · subst word; simp [volume]
      · have bound := ih member
        change actual.length + 1 ≤ (word.length + 1) + volume rest
        omega

@[simp] theorem copy_word (word : Word) : (copy word).1 = word := by
  induction word with
  | nil => rfl
  | cons bit rest ih => simp only [copy, ih]

@[simp] theorem copy_work (word : Word) : (copy word).2 = word.length + 1 := by
  induction word with
  | nil => rfl
  | cons bit rest ih => simp only [copy, ih, List.length_cons, Nat.add_assoc]

@[simp] theorem equal_result (first second : Word) :
    (equal first second).1 = decide (first = second) := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih =>
      cases second with
      | nil => rfl
      | cons other later =>
          by_cases same : bit = other
          · subst other
            simp only [equal, ↓reduceIte, ih, List.cons.injEq, true_and]
          · simp only [equal, same, ↓reduceIte, List.cons.injEq, false_and, decide_false]

theorem equal_work_le (first second : Word) :
    (equal first second).2 ≤ 2 * first.length + 1 := by
  induction first generalizing second with
  | nil => cases second <;> simp [equal]
  | cons bit rest ih =>
      cases second with
      | nil => simp [equal]
      | cons other later =>
          simp only [equal]
          split
          · have := ih later; simp only [List.length_cons]; omega
          · simp only [List.length_cons]; omega

@[simp] theorem lookup_result (table : List Word) (position : Nat) :
    (lookup table position).1 = table[position]? := by
  induction table generalizing position with
  | nil => rfl
  | cons word rest ih =>
      cases position with
      | zero => simp [lookup]
      | succ position => simpa only [lookup, List.getElem?_cons_succ] using ih position

@[simp] theorem append_result (table : List Word) (word : Word) :
    (append table word).1 = table ++ [word] := by
  induction table with
  | nil => simp [append]
  | cons first rest ih => simp only [append, copy_word, ih, List.cons_append]

@[simp] theorem append_work (table : List Word) (word : Word) :
    (append table word).2 = volume table + table.length + word.length + 2 := by
  induction table with
  | nil => simp [append, volume]
  | cons first rest ih =>
      simp only [append, copy_work, ih, volume, List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem lookup_work_le (table : List Word) (position : Nat) :
    (lookup table position).2 ≤ 2 * volume table + 1 := by
  induction table generalizing position with
  | nil => simp [lookup, volume]
  | cons word rest ih =>
      cases position with
      | zero =>
          simp only [lookup, copy_work, volume, List.map_cons, List.sum_cons]
          omega
      | succ position =>
          have := ih position
          simp only [lookup, volume, List.map_cons, List.sum_cons] at *
          omega

@[simp] theorem compareAt_result (table : List Word) (position : Nat) (wanted : Word) :
    (compareAt table position wanted).1 = decide (table[position]? = some wanted) := by
  unfold compareAt
  simp only [lookup_result]
  cases selected : table[position]? with
  | none => rfl
  | some actual => simp [copy_word, equal_result]

theorem compareAt_work_le (table : List Word) (position : Nat) (wanted : Word) :
    (compareAt table position wanted).2 ≤ 4 * volume table + wanted.length + 5 := by
  have lookupBound := lookup_work_le table position
  unfold compareAt
  simp only [lookup_result]
  cases selected : table[position]? with
  | none => simpa only [selected] using Nat.add_le_add_right lookupBound 1 |>.trans (by omega)
  | some actual =>
      have member : actual ∈ table := List.mem_of_getElem? selected
      have lengthBound := member_volume member
      have equalityBound := equal_work_le actual (copy wanted).1
      simp only [copy_work]
      omega

variable {P : Presentation.{u}} [DecidableEq P.Judgment]

def codeTable (coding : Coding P.Judgment) (table : List P.Judgment) : List Word :=
  table.map coding.word

structure Slots where
  accepted : Bool
  checks : Nat
  work : Nat

def inspectPremises (coding : Coding P.Judgment) (table : List Word) (row : Row P) :
    List (Fin (P.premises row.rule).length) → Slots
  | [] => ⟨true, 0, 1⟩
  | position :: rest =>
      let compared := compareAt table (row.references position)
        (coding.word ((P.premises row.rule).get position))
      if compared.1 then
        let later := inspectPremises coding table row rest
        ⟨later.accepted, later.checks + 1, compared.2 + later.work + 1⟩
      else ⟨false, 1, compared.2 + 1⟩

def inspectRow (coding : Coding P.Judgment) (table : List Word) (row : Row P) : Slots :=
  inspectPremises coding table row (List.finRange (P.premises row.rule).length)

structure Rows where
  table : Option (List Word)
  rows : Nat
  checks : Nat
  work : Nat

def inspectRows (coding : Coding P.Judgment) (table : List Word) : List (Row P) → Rows
  | [] => ⟨some table, 0, 0, 1⟩
  | row :: rest =>
      let inspected := inspectRow coding table row
      if inspected.accepted then
        let appended := append table (coding.word (P.conclusion row.rule))
        let later := inspectRows coding appended.1 rest
        ⟨later.table, later.rows + 1, inspected.checks + later.checks,
          inspected.work + appended.2 + later.work + 1⟩
      else ⟨none, 1, inspected.checks, inspected.work + 1⟩

structure Decision where
  accepted : Bool
  rows : Nat
  checks : Nat
  work : Nat

def check (coding : Coding P.Judgment) (certificate : Certificate P) (wanted : P.Judgment) : Decision :=
  let inspected := inspectRows coding [] certificate.rows
  match inspected.table with
  | none => ⟨false, inspected.rows, inspected.checks, inspected.work + 1⟩
  | some table =>
      let compared := compareAt table certificate.root (coding.word wanted)
      ⟨compared.1, inspected.rows, inspected.checks + 1, inspected.work + compared.2 + 1⟩

omit [DecidableEq P.Judgment] in
theorem codeTable_lookup (coding : Coding P.Judgment) (table : List P.Judgment)
    (position : Nat) (wanted : P.Judgment) :
    (codeTable coding table)[position]? = some (coding.word wanted) ↔
      table[position]? = some wanted := by
  simp only [codeTable, List.getElem?_map]
  cases selected : table[position]? with
  | none => simp
  | some actual => simp only [Option.map_some, Option.some.injEq, coding.injective.eq_iff]

theorem inspectPremises_projection (coding : Coding P.Judgment) (table : List P.Judgment)
    (row : Row P) (positions : List (Fin (P.premises row.rule).length)) :
    let paid := inspectPremises coding (codeTable coding table) row positions
    (paid.accepted, paid.checks) = Shared.inspectPremises table row positions := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      by_cases same : table[row.references position]? = some ((P.premises row.rule).get position)
      · simp only [inspectPremises, compareAt_result, codeTable_lookup, same, decide_true,
          ↓reduceIte, Shared.inspectPremises]
        exact congrArg (fun value : Bool × Nat => (value.1, value.2 + 1)) ih
      · simp only [inspectPremises, compareAt_result, codeTable_lookup, same, decide_false,
          Bool.false_eq_true, ↓reduceIte, Shared.inspectPremises]

theorem inspectRows_projection (coding : Coding P.Judgment) (table : List P.Judgment)
    (rows : List (Row P)) :
    let paid := inspectRows coding (codeTable coding table) rows
    let original := Shared.inspectRows table rows
    paid.table = original.table.map (codeTable coding) ∧
      paid.rows = original.rows ∧ paid.checks = original.premiseChecks := by
  induction rows generalizing table with
  | nil => simp [inspectRows, Shared.inspectRows]
  | cons row rest ih =>
      have localProjection := inspectPremises_projection coding table row
        (List.finRange (P.premises row.rule).length)
      have localAccepted := congrArg Prod.fst localProjection
      have localChecks := congrArg Prod.snd localProjection
      change (inspectRow coding (codeTable coding table) row).accepted =
        (Shared.inspectRow table row).1 at localAccepted
      change (inspectRow coding (codeTable coding table) row).checks =
        (Shared.inspectRow table row).2 at localChecks
      simp only [inspectRows, Shared.inspectRows, localAccepted]
      split
      · simp only [append_result]
        have next := ih (table ++ [P.conclusion row.rule])
        simp only [codeTable, List.map_append, List.map_cons, List.map_nil] at next
        exact ⟨next.1, congrArg (· + 1) next.2.1, by
          rw [localChecks]
          exact congrArg ((Shared.inspectRow table row).2 + ·) next.2.2⟩
      · simp only [localChecks, Option.map_none, and_self]

theorem check_projection (coding : Coding P.Judgment) (certificate : Certificate P)
    (wanted : P.Judgment) :
    let paid := check coding certificate wanted
    (paid.accepted, paid.rows, paid.checks) = checkJudgmentsWithWork certificate wanted := by
  have projection := inspectRows_projection coding [] certificate.rows
  simp only [check, checkJudgmentsWithWork_eq_inspectRows]
  simp only [codeTable, List.map_nil] at projection
  rw [projection.1, projection.2.1, projection.2.2]
  cases selected : (Shared.inspectRows [] certificate.rows).table with
  | none => rfl
  | some table => simp [compareAt_result, codeTable_lookup]

theorem check_exact (coding : Coding P.Judgment) (certificate : Certificate P)
    (wanted : P.Judgment) :
    (check coding certificate wanted).accepted = Shared.check certificate wanted := by
  have projected := congrArg Prod.fst (check_projection coding certificate wanted)
  exact projected.trans (checkJudgments_eq_check certificate wanted)

@[simp] theorem volume_append (table extra : List Word) :
    volume (table ++ extra) = volume table + volume extra := by
  simp [volume]

theorem length_le_volume (table : List Word) : table.length ≤ volume table := by
  induction table with
  | nil => rfl
  | cons word rest ih =>
      change rest.length + 1 ≤ (word.length + 1) + volume rest
      omega

def rowVolume (coding : Coding P.Judgment) (row : Row P) : Nat :=
  (coding.word (P.conclusion row.rule)).length + 1 +
    volume (codeTable coding (P.premises row.rule))

def articleVolume (coding : Coding P.Judgment) : List (Row P) → Nat
  | [] => 0
  | row :: rest => rowVolume coding row + articleVolume coding rest

omit [DecidableEq P.Judgment] in
theorem rowVolume_covers (coding : Coding P.Judgment) (row : Row P) :
    (coding.word (P.conclusion row.rule)).length + 1 ≤ rowVolume coding row ∧
      (P.premises row.rule).length + 1 ≤ rowVolume coding row ∧
      ∀ position : Fin (P.premises row.rule).length,
        (coding.word ((P.premises row.rule).get position)).length + 1 ≤ rowVolume coding row := by
  have lengthBound := length_le_volume (codeTable coding (P.premises row.rule))
  change (codeTable coding (P.premises row.rule)).length ≤ _ at lengthBound
  rw [show (codeTable coding (P.premises row.rule)).length = (P.premises row.rule).length by
    simp only [codeTable, List.length_map]] at lengthBound
  refine ⟨by unfold rowVolume; omega, by unfold rowVolume; omega, ?_⟩
  intro position
  have member : coding.word ((P.premises row.rule).get position) ∈
      codeTable coding (P.premises row.rule) :=
    List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
  have := member_volume member
  unfold rowVolume
  omega

omit [DecidableEq P.Judgment] in
theorem articleVolume_covers (coding : Coding P.Judgment) (rows : List (Row P)) :
    rows.length + premiseSlots rows ≤ articleVolume coding rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have := (rowVolume_covers coding row).2.1
      simp only [articleVolume, List.length_cons, premiseSlots, List.map_cons, List.sum_cons] at *
      omega

omit [DecidableEq P.Judgment] in
theorem inspectPremises_work_le (coding : Coding P.Judgment) (table : List Word)
    (row : Row P) (positions : List (Fin (P.premises row.rule).length)) (bound : Nat)
    (tableBound : volume table ≤ bound)
    (premiseBound : ∀ position ∈ positions,
      (coding.word ((P.premises row.rule).get position)).length ≤ bound) :
    (inspectPremises coding table row positions).work ≤ positions.length * (5 * bound + 6) + 1 := by
  induction positions with
  | nil => simp [inspectPremises]
  | cons position rest ih =>
      have compared := compareAt_work_le table (row.references position)
        (coding.word ((P.premises row.rule).get position))
      have wordBound := premiseBound position List.mem_cons_self
      have later := ih (fun p member => premiseBound p (List.mem_cons_of_mem _ member))
      simp only [inspectPremises]
      split
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        have nonnegative : 0 ≤ rest.length * (5 * bound + 6) := Nat.zero_le _
        omega

omit [DecidableEq P.Judgment] in
theorem inspectRow_work_le (coding : Coding P.Judgment) (table : List Word)
    (row : Row P) (bound : Nat) (tableBound : volume table ≤ bound)
    (rowBound : rowVolume coding row ≤ bound) :
    (inspectRow coding table row).work ≤
      (P.premises row.rule).length * (5 * bound + 6) + 1 := by
  have localBounds := rowVolume_covers coding row
  simpa only [inspectRow, List.length_finRange] using
    inspectPremises_work_le coding table row (List.finRange _) bound tableBound
      (fun position _ => by have := localBounds.2.2 position; omega)

omit [DecidableEq P.Judgment] in
theorem inspectRows_work_le (coding : Coding P.Judgment) (table : List Word)
    (rows : List (Row P)) (bound : Nat)
    (materialized : volume table + articleVolume coding rows ≤ bound) :
    (inspectRows coding table rows).work ≤
      (rows.length + premiseSlots rows + 1) * (5 * bound + 10) := by
  induction rows generalizing table with
  | nil => simp [inspectRows, premiseSlots]
  | cons row rest ih =>
      have whole : volume table + rowVolume coding row + articleVolume coding rest ≤ bound := by
        simpa only [articleVolume, Nat.add_assoc] using materialized
      have localBound := inspectRow_work_le coding table row bound (by omega) (by omega)
      have conclusionBound := (rowVolume_covers coding row).1
      have tableLength := length_le_volume table
      have appendBound : (append table (coding.word (P.conclusion row.rule))).2 ≤ 2 * bound + 2 := by
        rw [append_work]
        omega
      have laterMaterialized :
          volume (table ++ [coding.word (P.conclusion row.rule)]) + articleVolume coding rest ≤ bound := by
        rw [volume_append]
        change volume table + ((coding.word (P.conclusion row.rule)).length + 1) +
          articleVolume coding rest ≤ bound
        omega
      have later := ih (table ++ [coding.word (P.conclusion row.rule)]) laterMaterialized
      have rowCost : (inspectRow coding table row).work +
          (append table (coding.word (P.conclusion row.rule))).2 + 1 ≤
          ((P.premises row.rule).length + 1) * (5 * bound + 10) := by
        have compared : (P.premises row.rule).length * (5 * bound + 6) ≤
            (P.premises row.rule).length * (5 * bound + 10) :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simp only [inspectRows]
      split
      · simp only [append_result]
        have combined := Nat.add_le_add rowCost later
        simp only [List.length_cons, premiseSlots, List.map_cons, List.sum_cons] at *
        simp only [Nat.add_mul, Nat.one_mul] at combined ⊢
        omega
      · have extra : (P.premises row.rule).length + 1 ≤
            (row :: rest).length + premiseSlots (row :: rest) + 1 := by
          simp only [List.length_cons, premiseSlots, List.map_cons, List.sum_cons]
          omega
        exact (Nat.le_trans (by omega : (inspectRow coding table row).work + 1 ≤
          ((P.premises row.rule).length + 1) * (5 * bound + 10))
          (Nat.mul_le_mul_right _ extra))

/-- This size counts complete literal conclusions and every premise payload,
including unused rows and repeated premise occurrences. Numeric address
encoding, rule admission, and endpoint construction are separate costs. -/
def inputVolume (coding : Coding P.Judgment) (certificate : Certificate P)
    (wanted : P.Judgment) : Nat :=
  articleVolume coding certificate.rows + (coding.word wanted).length + 1

/-- The materialized-word checker has a quadratic structural account. This is
not a bound for its host implementation or a Turing-machine realization. -/
theorem check_work_le (coding : Coding P.Judgment) (certificate : Certificate P)
    (wanted : P.Judgment) :
    (check coding certificate wanted).work ≤
      (inputVolume coding certificate wanted + 2) * (5 * inputVolume coding certificate wanted + 10) := by
  let bound := inputVolume coding certificate wanted
  change (check coding certificate wanted).work ≤ (bound + 2) * (5 * bound + 10)
  have articleBound : articleVolume coding certificate.rows ≤ bound := by
    unfold bound inputVolume
    omega
  have countBound := articleVolume_covers coding certificate.rows
  have inspectedBound := inspectRows_work_le coding [] certificate.rows bound (by simpa [volume])
  have combinedBound : (inspectRows coding [] certificate.rows).work ≤
      (bound + 1) * (5 * bound + 10) :=
    inspectedBound.trans (Nat.mul_le_mul_right _ (by omega))
  have tableBound : ∀ table, (inspectRows coding [] certificate.rows).table = some table → volume table ≤ bound := by
    intro table successful
    have projection := inspectRows_projection coding [] certificate.rows
    simp only [codeTable, List.map_nil] at projection
    rw [successful] at projection
    obtain ⟨original, found, same⟩ := Option.map_eq_some_iff.mp projection.1.symm
    cases same
    have exactTable := inspectRows_table ([] : List P.Judgment) certificate.rows original found
    rw [exactTable]
    change volume (List.map coding.word (certificate.rows.map (fun row => P.conclusion row.rule))) ≤ bound
    have covers : volume (List.map coding.word (certificate.rows.map (fun row => P.conclusion row.rule))) ≤
        articleVolume coding certificate.rows := by
      induction certificate.rows with
      | nil => rfl
      | cons row rest ih =>
          have current := (rowVolume_covers coding row).1
          simp only [List.map_cons, volume, List.sum_cons, articleVolume]
          change (coding.word (P.conclusion row.rule)).length + 1 +
            volume (List.map coding.word (rest.map (fun row => P.conclusion row.rule))) ≤
              rowVolume coding row + articleVolume coding rest
          omega
    exact covers.trans articleBound
  unfold check
  dsimp only
  cases selected : (inspectRows coding [] certificate.rows).table with
  | none =>
      simp only
      simp only [Nat.add_mul, Nat.one_mul] at combinedBound ⊢
      omega
  | some table =>
      have tableVolume := tableBound table selected
      have compared := compareAt_work_le table certificate.root (coding.word wanted)
      have wantedBound : (coding.word wanted).length ≤ bound := by unfold bound inputVolume; omega
      simp only
      have last : (compareAt table certificate.root (coding.word wanted)).2 + 1 ≤ 5 * bound + 10 := by omega
      have added := Nat.add_le_add combinedBound last
      simp only [Nat.add_mul, Nat.one_mul] at *
      omega

end LiteralChecking

namespace Wire
open Mettapedia.OSLF.Binding.WireCodec

variable {P : Presentation}

/-- References are serialized in their declared slot order. Both missing and
extra references refuse before a row can enter the original checker. -/
def rowCodec (rules : Codec P.Rule) : Codec (Row P) where
  put row := .pair (rules.put row.rule) ((Codec.list Codec.nat).put (List.ofFn row.references))
  get
    | .pair code references => do
        let rule ← rules.get code
        let references ← (Codec.list Codec.nat).get references
        if length : references.length = (P.premises rule).length then
          pure ⟨rule, fun position => references[position.val]'(by rw [length]; exact position.isLt)⟩
        else none
    | _ => none
  get_put row := by
    simp only [rules.get_put, Codec.get_put, List.length_ofFn, ↓reduceDIte, Bind.bind, Option.bind]
    congr 2
    funext position
    exact List.getElem_ofFn _

def certificateCodec (rules : Codec P.Rule) : Codec (Certificate P) :=
  (Codec.prod (Codec.list (rowCodec rules)) Codec.nat).mapped
    (fun certificate => (certificate.rows, certificate.root))
    (fun fields => some ⟨fields.1, fields.2⟩) (fun _ => rfl)

/-- Canonical admission is distinct from validation of every graph row. -/
def read (rules : Codec P.Rule) : Data → Option (Certificate P) := (certificateCodec rules).canonicalGet

@[simp] theorem read_put (rules : Codec P.Rule) (certificate : Certificate P) :
    read rules ((certificateCodec rules).put certificate) = some certificate :=
  (certificateCodec rules).canonicalGet_put certificate

theorem put_of_read (rules : Codec P.Rule) (wire : Data) (certificate : Certificate P)
    (admitted : read rules wire = some certificate) : (certificateCodec rules).put certificate = wire :=
  (certificateCodec rules).put_of_canonicalGet wire certificate admitted

variable [DecidableEq P.Judgment]

def check (rules : Codec P.Rule) (wire : Data) (wanted : P.Judgment) : Bool :=
  match read rules wire with
  | none => false
  | some certificate => Shared.check certificate wanted

theorem check_exact (rules : Codec P.Rule) (wire : Data) (wanted : P.Judgment) :
    check rules wire wanted = true ↔
      ∃ certificate : Certificate P, (certificateCodec rules).put certificate = wire ∧
        Shared.check certificate wanted = true := by
  unfold check
  cases admitted : read rules wire with
  | none =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨certificate, same, _⟩
        rw [← same, read_put] at admitted
        cases admitted
  | some certificate =>
      constructor
      · intro accepted
        exact ⟨certificate, put_of_read rules wire certificate admitted, accepted⟩
      · rintro ⟨other, same, accepted⟩
        have reread := read_put rules other
        rw [same, admitted] at reread
        cases Option.some.inj reread
        exact accepted

end Wire

end Mettapedia.OSLF.NativeTypes.Certificates.Shared
