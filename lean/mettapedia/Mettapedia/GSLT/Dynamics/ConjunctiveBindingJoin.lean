import Mettapedia.GSLT.Dynamics.ConjunctiveRowMatching

/-!
# Sequential row binding and conjunctive provenance

The row-wise interpretation keeps the current binding frame and one physical
occurrence choice per factor. Projection to a complete assignment recovers
exactly the independently defined conjunctive witnesses, in authored order.
This is the composition edge between source-style nested matches and the
variable-at-a-time join semantics; it does not erase unused-variable or
finite-domain obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveBindingJoin

open ConjunctiveRegionProvenance GenericJoinRegions ConjunctiveRowMatching

variable {n : Nat} {Value Id : Type} [DecidableEq Value]

def extendsTo (before after : Environment n Value) : Bool :=
  (List.finRange n).all fun name => match before name with
    | none => true
    | some value => decide (after name = some value)

theorem extendsTo_iff (before after : Environment n Value) : extendsTo before after = true ↔ Extends before after := by
  simp only [extendsTo, List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro tested name value found
    simpa [found] using tested name
  · intro extended name
    cases found : before name with
    | none => rfl
    | some value => simp [extended name value found]

theorem bindFactor_extension_iff (before : Environment n Value) (assignment : Fin n → Value)
    (factor : Factor (Fin n) Value Id) (row : Id × (Fin factor.arity → Value)) :
    (∃ after, bindFactor before factor row = some after ∧ Extends after (fun name => some (assignment name))) ↔
      Extends before (fun name => some (assignment name)) ∧ factor.acceptsRow assignment row = true := by
  change (∃ after, bindValues before (List.ofFn factor.pattern) (List.ofFn row.2) = some after ∧ _) ↔ _
  rw [bindValues_extension_iff]
  apply and_congr_right
  intro _
  constructor
  · intro held
    obtain ⟨after, matched, _⟩ := bindValues_complete (Extends.refl (fun name => some (assignment name))) held
    change bindFactor (fun name => some (assignment name)) factor row = some after at matched
    rw [bindFactor_full] at matched
    split at matched
    next accepted => exact accepted
    next => cases matched
  · intro accepted
    have matched : bindValues (fun name => some (assignment name)) (List.ofFn factor.pattern) (List.ofFn row.2) =
        some (fun name => some (assignment name)) := by
      change bindFactor (fun name => some (assignment name)) factor row = _
      simp [bindFactor_full, accepted]
    exact (bindValues_sound matched).2

theorem bindFactor_compatible (before : Environment n Value) (assignment : Fin n → Value)
    (factor : Factor (Fin n) Value Id) (row : Id × (Fin factor.arity → Value)) :
    (bindFactor before factor row).any (fun after => extendsTo after (fun name => some (assignment name))) =
      (extendsTo before (fun name => some (assignment name)) && factor.acceptsRow assignment row) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Option.any_eq_true, Bool.and_eq_true, extendsTo_iff]
  exact bindFactor_extension_iff before assignment factor row

def run (before : Environment n Value) : List (Factor (Fin n) Value Id) → List (Environment n Value × List Id)
  | [] => [(before, [])]
  | factor :: factors => factor.rows.flatMap fun row =>
      (bindFactor before factor row).toList.flatMap fun after =>
        (run after factors).map fun result => (result.1, row.1 :: result.2)

def project (target : Environment n Value) (answers : List (Environment n Value × List Id)) : List (List Id) :=
  answers.filterMap fun answer => if extendsTo answer.1 target then some answer.2 else none

theorem project_flatMap {Row : Type} (target : Environment n Value)
    (rows : List Row) (answers : Row → List (Environment n Value × List Id)) :
    project target (rows.flatMap answers) = rows.flatMap (fun row => project target (answers row)) := by
  simp [project, List.filterMap_flatMap]

theorem project_prepend (target : Environment n Value) (occurrence : Id)
    (answers : List (Environment n Value × List Id)) :
    project target (answers.map fun result => (result.1, occurrence :: result.2)) =
      (project target answers).map (occurrence :: ·) := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      cases accepted : extendsTo answer.1 target with
      | false => simpa [project, accepted] using ih
      | true => simpa [project, accepted] using congrArg (List.cons (occurrence :: answer.2)) ih

theorem projected_witnesses_exact (before : Environment n Value) (assignment : Fin n → Value)
    (factors : List (Factor (Fin n) Value Id)) :
    project (fun name => some (assignment name)) (run before factors) =
      if extendsTo before (fun name => some (assignment name)) then witnesses assignment factors else [] := by
  induction factors generalizing before with
  | nil =>
      cases accepted : extendsTo before (fun name => some (assignment name)) <;>
        simp [run, project, witnesses, accepted]
  | cons factor factors ih =>
      have perRow (row : Id × (Fin factor.arity → Value)) :
          project (fun name => some (assignment name))
              ((bindFactor before factor row).toList.flatMap fun after =>
                (run after factors).map fun result => (result.1, row.1 :: result.2)) =
            if extendsTo before (fun name => some (assignment name)) && factor.acceptsRow assignment row then
              (witnesses assignment factors).map (row.1 :: ·) else [] := by
        rw [project_flatMap]
        simp only [project_prepend, ih]
        have compatible := bindFactor_compatible before assignment factor row
        cases matched : bindFactor before factor row with
        | none =>
            simp only [matched, Option.any_none] at compatible
            simp [← compatible]
        | some after =>
            simp only [matched, Option.any_some] at compatible
            simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
            rw [compatible]
            split <;> rfl
      simp only [run, project_flatMap, perRow]
      cases captured : extendsTo before (fun name => some (assignment name)) with
      | false => simp
      | true =>
          simp only [Bool.true_and, ↓reduceIte, witnesses, Factor.occurrences, List.flatMap_map]
          have filtered (rows : List (Id × (Fin factor.arity → Value))) :
              (rows.flatMap fun row => if factor.acceptsRow assignment row then
                (witnesses assignment factors).map (row.1 :: ·) else []) =
              (rows.filter (factor.acceptsRow assignment)).flatMap
                (fun row => (witnesses assignment factors).map (row.1 :: ·)) := by
            induction rows with
            | nil => rfl
            | cons row rows ih =>
                cases accepted : factor.acceptsRow assignment row <;> simp [accepted, ih]
          exact filtered factor.rows

namespace Controls

def duplicate : Factor (Fin 1) Nat Nat := ⟨1, fun _ => .variable 0, [(10, fun _ => 7), (11, fun _ => 7)]⟩

theorem repeated_read_positions_keep_four_witnesses :
    project (fun _ => some 7) (run (fun _ => none) [duplicate, duplicate]) =
      [[10, 10], [10, 11], [11, 10], [11, 11]] := by decide +kernel

theorem captured_conflict_does_not_create_a_branch :
    run (fun _ => some 8) [duplicate] = [] := by decide +kernel

theorem empty_conjunction_does_not_bind_a_free_variable :
    run (Id := Nat) (fun (_ : Fin 1) => (none : Option Nat)) [] = [(fun _ => none, [])] := rfl

end Controls

end Mettapedia.GSLT.Dynamics.ConjunctiveBindingJoin
