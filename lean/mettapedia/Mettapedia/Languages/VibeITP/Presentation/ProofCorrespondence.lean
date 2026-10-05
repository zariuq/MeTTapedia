import Mettapedia.Languages.VibeITP.Presentation.ProofExecution

/-!
# Complete static proof checking and actual theory binding

Every canonical finite supplied proof computes its independent result. Exact
acceptance and refusal preserve its particular witness, rather than searching
for unrelated derivability. A hosted theory has a finite complete allocation
table whose signature equals the actual signature everywhere. The transport
therefore imposes no hypothesis about intermediate proof results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs

open ComputationalData ComputationalShift ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "H" => productDivisionHost

theorem proofQuery_result_exact (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (result : Term) :
    Applies P H "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness] result ↔
      result = encodeResult (witness.result (theoryOf table axioms definitions)) := by
  constructor
  · exact fun run => run.deterministic (proofQuery_computes table axioms definitions witness)
  · rintro rfl
    exact proofQuery_computes table axioms definitions witness

theorem proofQuery_accepts_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness]
      (encodeResult (some claimed)) ↔ ProofWitness.Checks (theoryOf table axioms definitions) witness claimed := by
  constructor
  · intro run
    apply ProofWitness.result_sound
    exact (encodeResult_injective (run.deterministic (proofQuery_computes table axioms definitions witness))).symm
  · intro checked
    simpa only [checked.eval] using proofQuery_computes table axioms definitions witness

theorem proofQuery_refuses_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) :
    Applies P H "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness] (.sym "None") ↔
      ¬ ∃ statement, ProofWitness.Checks (theoryOf table axioms definitions) witness statement := by
  rw [← ProofWitness.result_none_iff]
  constructor
  · intro run
    have encoded : encodeResult none = encodeResult (witness.result (theoryOf table axioms definitions)) :=
      run.deterministic (proofQuery_computes table axioms definitions witness)
    exact (encodeResult_injective encoded).symm
  · intro refused
    simpa only [refused, encodeResult] using proofQuery_computes table axioms definitions witness

theorem proofQuery_completed_exact (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (fuel : Nat)
    (finished : apply P H fuel "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness] ≠ .exhausted) :
    apply P H fuel "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness] =
      .value (encodeResult (witness.result (theoryOf table axioms definitions))) :=
  (proofQuery_computes table axioms definitions witness).completed fuel finished

theorem checkProof_result_exact (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term) (result : Term) :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed] result ↔
      result = boolean (ProofWitness.check (theoryOf table axioms definitions) witness claimed) := by
  constructor
  · exact fun run => run.deterministic (checkProof_computes table axioms definitions witness claimed)
  · rintro rfl
    exact checkProof_computes table axioms definitions witness claimed

theorem checkProof_accepts_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (.sym "True") ↔ ProofWitness.Checks (theoryOf table axioms definitions) witness claimed := by
  rw [checkProof_result_exact, ← ProofWitness.check_iff]
  cases ProofWitness.check (theoryOf table axioms definitions) witness claimed <;> simp [boolean]

theorem checkProof_refuses_iff (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (.sym "False") ↔ ¬ ProofWitness.Checks (theoryOf table axioms definitions) witness claimed := by
  rw [checkProof_result_exact, ← ProofWitness.check_iff]
  cases ProofWitness.check (theoryOf table axioms definitions) witness claimed <;> simp [boolean]

theorem checkProof_completed_exact (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed] ≠ .exhausted) :
    apply P H fuel "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed] =
      .value (boolean (ProofWitness.check (theoryOf table axioms definitions) witness claimed)) :=
  (checkProof_computes table axioms definitions witness claimed).completed fuel finished

theorem checkProof_derived (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term)
    (accepted : Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (.sym "True")) : Spec.Derives (theoryOf table axioms definitions) claimed :=
  ((checkProof_accepts_iff table axioms definitions witness claimed).mp accepted).derives

def allocatedSymbols (allocated : Nat) : List Spec.SymId :=
  Spec.Builtin.all.map Spec.SymId.builtin ++ (List.range allocated).map Spec.SymId.fresh

def allocatedSnapshot (theory : Spec.Theory) (allocated : Nat) : SignatureTable :=
  tableFor theory.sig (allocatedSymbols allocated)

theorem allocatedSnapshot_signature {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated) :
    signatureOf (allocatedSnapshot theory allocated) = theory.sig := by
  funext symbol
  rw [allocatedSnapshot, tableFor_lookup]
  by_cases present : symbol ∈ allocatedSymbols allocated
  · simp only [present, ↓reduceIte]
  · simp only [present, ↓reduceIte]
    cases symbol with
    | builtin builtin =>
        have member : builtin ∈ Spec.Builtin.all := by cases builtin <;> simp [Spec.Builtin.all]
        exact False.elim (present (List.mem_append_left _ (List.mem_map.mpr ⟨builtin, member, rfl⟩)))
    | fresh index =>
        cases declared : theory.sig (.fresh index) with
        | none => rfl
        | some info =>
            have bounded : index < allocated := (hosted.fresh index).mp (by simp [declared])
            exact False.elim (present (List.mem_append_right _
              (List.mem_map.mpr ⟨index, List.mem_range.mpr bounded, rfl⟩)))

theorem theoryOf_allocatedSnapshot {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated) :
    theoryOf (allocatedSnapshot theory allocated) theory.axioms theory.definitions = theory := by
  unfold theoryOf
  rw [allocatedSnapshot_signature hosted]

theorem proofQuery_computes_for_theory {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (witness : ProofWitness) :
    Applies P H "vibe:proof-query"
      [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
        encodeDefinitions theory.definitions, encodeWitness witness]
      (encodeResult (witness.result theory)) := by
  simpa only [theoryOf_allocatedSnapshot hosted] using
    proofQuery_computes (allocatedSnapshot theory allocated) theory.axioms theory.definitions witness

theorem checkProof_computes_for_theory {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof"
      [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
        encodeDefinitions theory.definitions, encodeWitness witness, encode claimed]
      (boolean (ProofWitness.check theory witness claimed)) := by
  simpa only [theoryOf_allocatedSnapshot hosted] using
    checkProof_computes (allocatedSnapshot theory allocated) theory.axioms theory.definitions witness claimed

theorem checkProof_for_theory_iff {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof"
      [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
        encodeDefinitions theory.definitions, encodeWitness witness, encode claimed]
      (.sym "True") ↔ ProofWitness.Checks theory witness claimed := by
  rw [checkProof_accepts_iff, theoryOf_allocatedSnapshot hosted]

theorem checkProof_for_theory_refuses_iff {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-proof"
      [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
        encodeDefinitions theory.definitions, encodeWitness witness, encode claimed]
      (.sym "False") ↔ ¬ ProofWitness.Checks theory witness claimed := by
  rw [checkProof_refuses_iff, theoryOf_allocatedSnapshot hosted]

theorem checkProof_for_theory_derived {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (witness : ProofWitness) (claimed : Spec.Term)
    (accepted : Applies P H "vibe:check-proof"
      [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
        encodeDefinitions theory.definitions, encodeWitness witness, encode claimed] (.sym "True")) :
    Spec.Derives theory claimed := ((checkProof_for_theory_iff hosted witness claimed).mp accepted).derives

theorem proofWitness_exists {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    {statement : Spec.Term} (derived : Spec.Derives theory statement) :
    ∃ witness fuel, apply P H fuel "vibe:check-proof"
      [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
        encodeDefinitions theory.definitions, encodeWitness witness, encode statement] = .value (.sym "True") := by
  obtain ⟨witness, checked⟩ := certificate_exists hosted derived
  obtain ⟨fuel, executed⟩ := (checkProof_for_theory_iff hosted witness statement).mpr checked
  exact ⟨witness, fuel, executed⟩

theorem derives_iff_authored_check {theory : Spec.Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    (statement : Spec.Term) :
    Spec.Derives theory statement ↔ ∃ witness fuel, apply P H fuel "vibe:check-proof"
      [encodeTable (allocatedSnapshot theory allocated), encodeAxioms theory.axioms,
        encodeDefinitions theory.definitions, encodeWitness witness, encode statement] = .value (.sym "True") := by
  constructor
  · exact proofWitness_exists hosted
  · rintro ⟨witness, fuel, executed⟩
    exact checkProof_for_theory_derived hosted witness statement ⟨fuel, executed⟩

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs
