import Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPlan

/-!
# A packed projection at the pattern's observation demand

A query fixes its field order once. Every candidate row then
uses the same offsets regardless of the candidate's constructor
shape. Tags, presence, and term codes are separate observations.
The row directory is indexed by occurrence ordinal, so equal values
do not erase distinct occurrence identities.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.CandidateProjection

open Mettapedia.Logic.LP
open MatchPlan (Test Field Observation demand)
open NativeBinding (occupancy)
open PackedOccurrences (Codes)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def fields (tests : List (Test σ)) : List Field := (tests.flatMap Test.fields).eraseDups

theorem fields_exact (tests : List (Test σ)) (field : Field) :
    field ∈ fields tests ↔ field ∈ demand tests := by
  simp only [fields, List.mem_eraseDups, demand, List.mem_toFinset]

def column (tests : List (Test σ)) (field : Field) : ℕ := (fields tests).idxOf field

theorem column_bound {tests : List (Test σ)} {field : Field} (needed : field ∈ demand tests) :
    column tests field < (fields tests).length :=
  List.idxOf_lt_length_iff.mpr ((fields_exact tests field).mpr needed)

theorem field_at_column {tests : List (Test σ)} {field : Field} (needed : field ∈ demand tests) :
    (fields tests)[column tests field]? = some field := by
  rw [List.getElem?_eq_getElem (column_bound needed)]
  exact congrArg some (List.getElem_idxOf (column_bound needed))

theorem column_inj {tests : List (Test σ)} {left right : Field}
    (l : left ∈ demand tests) (r : right ∈ demand tests) :
    column tests left = column tests right → left = right := by
  intro same
  have keyed := field_at_column l
  rw [same, field_at_column r] at keyed
  exact (Option.some.inj keyed).symm

def wordFor (tags : Codes (Option (MatchPlan.Symbol σ))) (values : Codes (GroundTerm σ))
    (read : Observation σ) : Field → Option Word
  | .tag path => tags.encode ((read path).map MatchPlan.symbol)
  | .present path => some (occupancy (read path))
  | .value path =>
    match read path with
    | none => some 0
    | some candidate => values.encode candidate

private theorem mapM_entries {A B : Type*} (f : A → Option B) (input : List A)
    {output : List B} (done : input.mapM f = some output) :
    output.length = input.length ∧ ∀ i : ℕ, output[i]? = (input[i]?).bind f := by
  induction input generalizing output with
  | nil =>
    have empty : ([] : List B) = output := Option.some.inj done
    subst output
    exact ⟨rfl, fun i => by cases i <;> rfl⟩
  | cons first rest ih =>
    rw [List.mapM_cons] at done
    obtain ⟨head, encoded, remainder⟩ := Option.bind_eq_some_iff.mp done
    obtain ⟨tail, compiled, returned⟩ := Option.bind_eq_some_iff.mp remainder
    obtain rfl := (Option.some.inj returned).symm
    obtain ⟨length, atIndex⟩ := ih compiled
    refine ⟨congrArg Nat.succ length, ?_⟩
    intro i
    cases i with
    | zero => exact encoded.symm
    | succ i => exact atIndex i

def project (tags : Codes (Option (MatchPlan.Symbol σ))) (values : Codes (GroundTerm σ))
    (tests : List (Test σ)) (term : GroundTerm σ) : Option (Array Word) :=
  ((fields tests).mapM (wordFor tags values (MatchPlan.observe term))).map List.toArray

theorem project_shape (tags : Codes (Option (MatchPlan.Symbol σ))) (values : Codes (GroundTerm σ))
    {tests : List (Test σ)} {term : GroundTerm σ} {row : Array Word}
    (formed : project tags values tests term = some row) :
    row.size = (fields tests).length ∧
      ∀ field ∈ demand tests, row[column tests field]? = wordFor tags values (MatchPlan.observe term) field := by
  obtain ⟨words, mapped, rfl⟩ := Option.map_eq_some_iff.mp formed
  obtain ⟨width, atIndex⟩ := mapM_entries _ _ mapped
  refine ⟨width, ?_⟩
  intro field included
  simpa only [field_at_column included, Option.bind_some, List.getElem?_toArray] using atIndex (column tests field)

def prepare (tags : Codes (Option (MatchPlan.Symbol σ))) (values : Codes (GroundTerm σ))
    (tests : List (Test σ)) (packed : PackedOccurrences.Layout) : Option (Array (Array Word)) :=
  match PackedOccurrences.unpack values packed with
  | none => none
  | some decoded => (decoded.occurrences.mapM fun record => project tags values tests record.2).map List.toArray

/-- The indexed view corresponds to the term at the physical ordinal,
without changing the occurrence identity returned by the store. -/
theorem selected_projection (tags : Codes (Option (MatchPlan.Symbol σ))) (codes : Codes (GroundTerm σ))
    (tests : List (Test σ)) {store : Derivation.Store (GroundTerm σ)}
    {packed : PackedOccurrences.Layout} {directory : Array (Array Word)}
    (formed : PackedOccurrences.pack codes store = some packed)
    (projected : prepare tags codes tests packed = some directory) (index identity : ℕ) (term : GroundTerm σ)
    (selected : PackedOccurrences.at? codes packed index = some (identity, term)) :
    ∃ row, directory[index]? = some row ∧ project tags codes tests term = some row := by
  have read := (PackedOccurrences.pack_roundtrip codes formed).1
  rw [PackedOccurrences.at_exact codes formed] at selected
  unfold prepare at projected
  rw [read] at projected
  obtain ⟨rows, mapped, rfl⟩ := Option.map_eq_some_iff.mp projected
  have each := (mapM_entries _ _ mapped).2 index
  rw [selected] at each
  have within : index < rows.length := by
    have length := (mapM_entries _ _ mapped).1
    rw [length]
    exact (List.getElem?_eq_some_iff.mp selected).choose
  refine ⟨rows[index], ?_, ?_⟩
  · simpa only [List.getElem?_toArray] using List.getElem?_eq_getElem within
  · simpa only [Option.bind_some, List.getElem?_eq_getElem within] using each.symm

namespace Examples

private abbrev atoms : LPSignature where
  constants := Unit
  vars := Unit
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Empty
  functionArity := fun _ => 0

private def value : GroundTerm atoms := .const ()

private def atomCodes : Codes (GroundTerm atoms) where
  encode := fun _ => some 0
  decode := fun w => if w = 0 then some value else none
  reads := by
    intro v w wrote
    have same : (0 : Word) = w := Option.some.inj wrote
    subst w
    cases v with
    | const c => cases c; decide +kernel
    | app f _ => cases f

private def headCode : Option (MatchPlan.Symbol atoms) → Word
  | none => 0
  | some (.inl _) => 1
  | some (.inr f) => nomatch f

private def tags : Codes (Option (MatchPlan.Symbol atoms)) where
  encode := some ∘ headCode
  decode := fun w => if w = 0 then some none else if w = 1 then some (some (.inl ())) else none
  reads := by
    intro tag w wrote
    have same : headCode tag = w := Option.some.inj wrote
    subst w
    cases tag with
    | none => decide +kernel
    | some tag =>
      cases tag with
      | inl c => cases c; decide +kernel
      | inr f => cases f

private def tests : List (Test atoms) :=
  [.shape [] (.inl ()), .shape [] (.inl ()), .bind [] (), .bind [0] ()]

theorem repeat_test_reuses_column :
    fields tests = [.tag [], .present [], .value [], .present [0], .value [0]] := by decide +kernel

theorem present_zero_is_not_absent :
    project tags atomCodes tests value = some #[1, 1, 0, 0, 0] := by decide +kernel

private def duplicates : Derivation.Store (GroundTerm atoms) := ⟨[(2, value), (9, value)], 10⟩

theorem equal_projections_keep_occurrence_ordinals :
    ((PackedOccurrences.pack atomCodes duplicates).bind (prepare tags atomCodes tests)).map Array.size = some 2 := by
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.CandidateProjection
