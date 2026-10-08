import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceMaterialControls

/-!
# Equal authored clauses and repeated premise occurrences

The first two source positions contain the same clause. Their derivations have
identical facts and leaf-origin traces, but remain distinct actual proofs.
A third clause uses the same input occurrence twice. Its two premise positions
remain present in the proof while origin support still contains only one item.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence.OccurrenceControls

attribute [local instance] Finite.membership

open Mettapedia.TypeTheory.MaterialSets.Hypersets

def source (n : Nat) : Source Nat Unit where
  input _ := n
  rules := [⟨[n], n+1⟩, ⟨[n], n+1⟩, ⟨[n,n], n+1⟩]

def first (n : Nat) : Receipt (source n) :=
  ⟨n+1, .rule ⟨0, by change 0 < 3; decide⟩
    (Fin.cases (Derivation.input (source := source n) ()) (fun i => Fin.elim0 i))⟩

def second (n : Nat) : Receipt (source n) :=
  ⟨n+1, .rule ⟨1, by change 1 < 3; decide⟩
    (Fin.cases (Derivation.input (source := source n) ()) (fun i => Fin.elim0 i))⟩

def repeated (n : Nat) : Receipt (source n) :=
  ⟨n+1, .rule ⟨2, by change 2 < 3; decide⟩
    (Fin.cases (Derivation.input (source := source n) ())
      (Fin.cases (Derivation.input (source := source n) ()) (fun i => Fin.elim0 i)))⟩

theorem authored_clauses_equal (n : Nat) :
    (source n).rule ⟨0, by change 0 < 3; decide⟩ =
      (source n).rule ⟨1, by change 1 < 3; decide⟩ := rfl

theorem literal_receipts_distinct (n : Nat) : first n ≠ second n := by
  intro same
  have roots := congrArg (fun receipt : Receipt (source n) => receipt.root.map Fin.val) same
  change some 0 = some 1 at roots
  cases roots

theorem leaf_trace_is_not_complete_evidence (n : Nat) :
    (first n).fact = (second n).fact ∧ (first n).origins = (second n).origins ∧
      first n ≠ second n := ⟨rfl, rfl, literal_receipts_distinct n⟩

theorem material_retains_authored_occurrences (n : Nat) :
    Material.reading (ArgumentCoding.ofEncodable Nat) (ArgumentCoding.ofEncodable Unit) (first n) ≠
      Material.reading (ArgumentCoding.ofEncodable Nat) (ArgumentCoding.ofEncodable Unit) (second n) :=
  fun same => literal_receipts_distinct n ((Material.reading_kernel _ _ _ _).mp same)

theorem repeated_use_is_one_origin (n : Nat) :
    (repeated n).origins = [(), ()] ∧ (repeated n).originSupport.card = 1 ∧
      (first n).originSupport = (repeated n).originSupport := by
  refine ⟨rfl, ?_, ?_⟩
  · change (Finite.support [(), ()] : Finset Unit).card = 1
    decide
  · change (Finite.support [()] : Finset Unit) = Finite.support [(), ()]
    rfl

theorem repeated_premise_positions_differ (n : Nat) :
    (⟨0, by change 0 < 2; decide⟩ : (source n).PremiseIndex ⟨2, by change 2 < 3; decide⟩) ≠
      ⟨1, by change 1 < 2; decide⟩ := by
  intro same
  have values := congrArg Fin.val same
  cases values

theorem repeated_fact_is_not_another_observation (n : Nat) :
    batchOriginSupport [first n, repeated n] = batchOriginSupport [first n] ∧
      [first n, repeated n] ≠ [first n] := by
  constructor
  · change (Finite.support [(), (), ()] : Finset Unit) = Finite.support [()]
    rfl
  · intro same
    have lengths := congrArg List.length same
    cases lengths

end Mettapedia.GSLT.ProgrammableSpaceEvidence.OccurrenceControls
