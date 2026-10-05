import Mettapedia.Languages.VibeITP.Presentation.ProofProgram

/-!
# Actual ordered theory access

The same authored index computation selects an axiom or a complete definition
payload. It preserves list positions, duplicates and arbitrary natural indices.
Stored payloads are returned as data; selecting one does not execute a stored
expression or substitute a different theory entry.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs

open ComputationalData ComputationalShift ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "A" => proofEquations
local notation "H" => productDivisionHost

private theorem proof_view (values : List Term) :
    Applies P H "nik:list-view" [.list values] (listView values) := by
  apply Applies.primitive (by decide +kernel)
  change computationalHost.primitive "nik:list-view" [.list values] = .value (listView values)
  exact computationalHost_list_view values

private theorem proof_zero (value : Nat) :
    Applies P H "nik:nat-zero" [natural value] (boolean (decide (value = 0))) := by
  apply Applies.primitive (by decide +kernel)
  change computationalHost.primitive "nik:nat-zero" [natural value] = .value (boolean (decide (value = 0)))
  simpa only [boolean, decide_eq_true_eq] using computationalHost_zero value

private theorem proof_pred (value : Nat) :
    Applies P H "nik:nat-pred" [natural value] (natural (value - 1)) := by
  apply Applies.primitive (by decide +kernel)
  change computationalHost.primitive "nik:nat-pred" [natural value] = .value (natural (value - 1))
  exact computationalHost_pred value

private theorem proof_some (value : Term) :
    Applies P H "Some" [value] (encodeAccessResult (some value)) :=
  Applies.constructor (by decide +kernel) (by rfl)

private theorem access_start (values : List Term) (index : Nat) (result : Term)
    (next : Applies P H "vibe:proof-entry-view" [listView values, natural index] result) :
    Applies P H "vibe:proof-at" [.list values, natural index] result := by
  refine proof_equation (equation := A[0])
    (environment := [("entries", .list values), ("index", natural index)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (proof_view values)

theorem proofAt_computes {α : Type} (encode : α → Term) (entries : List α) (index : Nat) :
    Applies P H "vibe:proof-at" [.list (entries.map encode), natural index]
      (encodeAccessResult (entries[index]?.map encode)) := by
  induction entries generalizing index with
  | nil =>
      apply access_start
      exact ⟨1, by rw [proof_apply _ (by decide +kernel)]; rfl⟩
  | cons first rest ih =>
      apply access_start
      refine proof_equation (equation := A[2])
        (environment := [("first", encode first), ("rest", .list (rest.map encode)), ("index", natural index)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (index = 0)), encode first,
          .list (rest.map encode), natural index]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (proof_zero index)
      · cases index with
        | zero =>
            refine proof_equation (equation := A[3])
              (environment := [("first", encode first), ("rest", .list (rest.map encode)), ("index", natural 0)])
              (by decide +kernel) (by rfl) (by rfl) ?_
            exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (proof_some _)
        | succ index =>
            refine proof_equation (equation := A[4])
              (environment := [("first", encode first), ("rest", .list (rest.map encode)),
                ("index", natural (index + 1))]) (by decide +kernel) (by rfl) (by rfl) ?_
            exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (Evaluates.call (by simp [Special])
                (.cons (.variable (by rfl)) .nil) (proof_pred (index + 1))) .nil)) (ih index)

theorem axiomAt_computes (axioms : List Spec.Term) (index : Nat) :
    Applies P H "vibe:proof-at" [encodeAxioms axioms, natural index] (encodeResult axioms[index]?) := by
  have computed := proofAt_computes encode axioms index
  cases selected : axioms[index]? <;>
    simpa only [encodeAxioms, selected, Option.map_none, Option.map_some, encodeAccessResult, encodeResult] using computed

theorem definitionAt_computes (definitions : List Spec.Definition) (index : Nat) :
    Applies P H "vibe:proof-at" [encodeDefinitions definitions, natural index]
      (encodeAccessResult (definitions[index]?.map encodeDefinition)) :=
  proofAt_computes encodeDefinition definitions index

theorem proofAt_result_exact {α : Type} (encode : α → Term) (entries : List α) (index : Nat) (result : Term) :
    Applies P H "vibe:proof-at" [.list (entries.map encode), natural index] result ↔
      result = encodeAccessResult (entries[index]?.map encode) := by
  constructor
  · exact fun run => run.deterministic (proofAt_computes encode entries index)
  · rintro rfl
    exact proofAt_computes encode entries index

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs
