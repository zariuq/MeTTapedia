import Mettapedia.Languages.VibeITP.Presentation.AdmissionExecution
import Mettapedia.Languages.VibeITP.Presentation.AdmissionInvariant

/-!
# Exact sequential admission and proof use from the initial theory

The public entry starts from fixed builtins. Accepted declaration runs produce
an admitted actual theory, and the supplied proof is checked against that
result. Failed declarations cannot be replaced by unrelated derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission

open ComputationalData ComputationalShift ComputationalDefinitions ComputationalProofs
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissionProgram
local notation "H" => productDivisionHost

theorem encodeBinding_injective : Function.Injective encodeBinding := by
  intro first second same
  rcases first with ⟨firstSymbol, firstInfo⟩
  rcases second with ⟨secondSymbol, secondInfo⟩
  have fields := Term.expr.inj same
  simp only [List.cons.injEq, true_and, and_true] at fields
  have symbol : firstSymbol = secondSymbol := by
    have decoded := congrArg decodeSymbol fields.1
    simpa only [decode_encodeSymbol, Option.some.injEq] using decoded
  have info : firstInfo = secondInfo := encodeInfo_injective (by
    simp only [encodeInfo, fields.2.1, fields.2.2])
  cases symbol
  cases info
  rfl

theorem encodeTable_injective : Function.Injective encodeTable := by
  intro first second same
  exact List.map_injective_iff.mpr encodeBinding_injective (Term.list.inj same)

theorem encodeDefinition_injective : Function.Injective encodeDefinition := by
  intro first second same
  rcases first with ⟨firstSymbol, firstParameters, firstBody⟩
  rcases second with ⟨secondSymbol, secondParameters, secondBody⟩
  have fields := Term.list.inj same
  simp only [List.cons.injEq, and_true] at fields
  have symbol : firstSymbol = secondSymbol := by
    have decoded := congrArg decodeSymbol fields.1
    simpa only [decode_encodeSymbol, Option.some.injEq] using decoded
  have parameters : firstParameters = secondParameters :=
    List.map_injective_iff.mpr (fun _ _ same => by
      simpa only [decode_encodeSymbol, Option.some.injEq] using congrArg decodeSymbol same)
      (Term.list.inj fields.2.1)
  have body := encode_injective fields.2.2
  cases symbol
  cases parameters
  cases body
  rfl

theorem encodeDefinitions_injective : Function.Injective encodeDefinitions := by
  intro first second same
  exact List.map_injective_iff.mpr encodeDefinition_injective (Term.list.inj same)

theorem encodeAxioms_injective : Function.Injective encodeAxioms := by
  intro first second same
  exact List.map_injective_iff.mpr encode_injective (Term.list.inj same)

theorem encodeState_injective : Function.Injective encodeState := by
  intro first second same
  rcases first with ⟨firstPhase, firstIdentity, firstTable, firstAxioms, firstDefinitions⟩
  rcases second with ⟨secondPhase, secondIdentity, secondTable, secondAxioms, secondDefinitions⟩
  have fields := Term.list.inj same
  simp only [List.cons.injEq, true_and, and_true] at fields
  have phase : firstPhase = secondPhase := by
    cases firstPhase <;> cases secondPhase <;> simp_all [encodePhase]
  have identity := natural_injective fields.2.1
  have table := encodeTable_injective fields.2.2.1
  have axioms := encodeAxioms_injective fields.2.2.2.1
  have definitions := encodeDefinitions_injective fields.2.2.2.2
  cases phase
  cases identity
  cases table
  cases axioms
  cases definitions
  rfl

theorem encodeAdmissionResult_injective : Function.Injective encodeAdmissionResult := by
  intro first second same
  cases first with
  | none => cases second with
    | none => rfl
    | some _ => cases same
  | some first => cases second with
    | none => cases same
    | some second =>
        exact congrArg some (encodeState_injective (by simpa [encodeAdmissionResult] using same))

theorem admit_result_exact (state : AdmissionState) (declaration : Declaration) (result : Term) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration declaration] result ↔
      result = encodeAdmissionResult (admit state declaration) := by
  constructor
  · exact fun run => run.deterministic (admit_computes state declaration)
  · rintro rfl
    exact admit_computes state declaration

theorem admit_accepts_iff (state after : AdmissionState) (declaration : Declaration) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration declaration]
      (encodeAdmissionResult (some after)) ↔ Admits state declaration after := by
  rw [admit_result_exact, ← admit_eq_some_iff]
  exact ⟨fun same => (encodeAdmissionResult_injective same).symm, fun same => congrArg encodeAdmissionResult same.symm⟩

theorem admit_refuses_iff (state : AdmissionState) (declaration : Declaration) :
    Applies P H "vibe:admit" [encodeState state, encodeDeclaration declaration] (.sym "None") ↔
      ¬ ∃ after, Admits state declaration after := by
  rw [admit_result_exact]
  cases computed : admit state declaration with
  | none =>
      constructor
      · intro _ ⟨after, admitted⟩
        have result := (admit_eq_some_iff _ _ _).mpr admitted
        rw [computed] at result
        cases result
      · intro _; rfl
  | some after =>
      constructor
      · intro impossible; cases impossible
      · intro impossible
        exact False.elim (impossible ⟨after, (admit_eq_some_iff _ _ _).mp computed⟩)

theorem admitRun_result_exact (state : AdmissionState) (declarations : List Declaration) (result : Term) :
    Applies P H "vibe:admission-run" [encodeState state, encodeDeclarations declarations] result ↔
      result = encodeAdmissionResult (admitRun state declarations) := by
  constructor
  · exact fun run => run.deterministic (admitRun_computes state declarations)
  · rintro rfl
    exact admitRun_computes state declarations

theorem admitRun_accepts_iff (state after : AdmissionState) (declarations : List Declaration) :
    Applies P H "vibe:admission-run" [encodeState state, encodeDeclarations declarations]
      (encodeAdmissionResult (some after)) ↔ AdmissionRun state declarations after := by
  rw [admitRun_result_exact, ← admitRun_eq_some_iff]
  exact ⟨fun same => (encodeAdmissionResult_injective same).symm, fun same => congrArg encodeAdmissionResult same.symm⟩

theorem admitRun_refuses_iff (state : AdmissionState) (declarations : List Declaration) :
    Applies P H "vibe:admission-run" [encodeState state, encodeDeclarations declarations] (.sym "None") ↔
      ¬ ∃ after, AdmissionRun state declarations after := by
  rw [admitRun_result_exact]
  cases computed : admitRun state declarations with
  | none =>
      constructor
      · intro _ ⟨after, admitted⟩
        have result := (admitRun_eq_some_iff _ _ _).mpr admitted
        rw [computed] at result
        cases result
      · intro _; rfl
  | some after =>
      constructor
      · intro impossible; cases impossible
      · intro impossible
        exact False.elim (impossible ⟨after, (admitRun_eq_some_iff _ _ _).mp computed⟩)

theorem admissionStart_result_exact (declarations : List Declaration) (result : Term) :
    Applies P H "vibe:admission-start" [encodeDeclarations declarations] result ↔
      result = encodeAdmissionResult (admitRun initialAdmission declarations) := by
  constructor
  · exact fun run => run.deterministic (admissionStart_computes declarations)
  · rintro rfl
    exact admissionStart_computes declarations

theorem admissionStart_accepts_iff (declarations : List Declaration) (after : AdmissionState) :
    Applies P H "vibe:admission-start" [encodeDeclarations declarations] (encodeAdmissionResult (some after)) ↔
      AdmissionRun initialAdmission declarations after := by
  constructor
  · intro run
    apply (admitRun_eq_some_iff _ _ _).mp
    exact (encodeAdmissionResult_injective (run.deterministic (admissionStart_computes declarations))).symm
  · intro run
    simpa only [(admitRun_eq_some_iff _ _ _).mpr run] using admissionStart_computes declarations

theorem admissionStart_refuses_iff (declarations : List Declaration) :
    Applies P H "vibe:admission-start" [encodeDeclarations declarations] (.sym "None") ↔
      ¬ ∃ after, AdmissionRun initialAdmission declarations after := by
  exact ((admissionStart_result_exact declarations (.sym "None")).trans
    (admitRun_result_exact initialAdmission declarations (.sym "None")).symm).trans
      (admitRun_refuses_iff initialAdmission declarations)

theorem admissionStart_hosted {declarations : List Declaration} {after : AdmissionState}
    (run : Applies P H "vibe:admission-start" [encodeDeclarations declarations] (encodeAdmissionResult (some after))) :
    Hosted after.theory after.nextFresh :=
  ((admissionStart_accepts_iff _ _).mp run).hosted initialAdmission_hosted

theorem checkAdmitted_accepts_iff (state : AdmissionState) (declarations : List Declaration)
    (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-admitted" [encodeState state, encodeDeclarations declarations, encodeWitness witness, encode claimed]
      (.sym "True") ↔ ∃ after, AdmissionRun state declarations after ∧ ProofWitness.Checks after.theory witness claimed := by
  have reference : checkAdmitted state declarations witness claimed = true ↔
      ∃ after, AdmissionRun state declarations after ∧ ProofWitness.Checks after.theory witness claimed := by
    cases run : admitRun state declarations with
    | none =>
        simp only [checkAdmitted, run, Bool.false_eq_true]
        constructor
        · intro impossible; cases impossible
        · rintro ⟨after, admitted, _⟩
          have impossible := (admitRun_eq_some_iff _ _ _).mpr admitted
          rw [run] at impossible
          cases impossible
    | some after =>
        simp only [checkAdmitted, run, ProofWitness.check_iff]
        constructor
        · intro checked; exact ⟨after, (admitRun_eq_some_iff _ _ _).mp run, checked⟩
        · rintro ⟨other, admitted, checked⟩
          have same := (admitRun_eq_some_iff _ _ _).mpr admitted
          rw [run] at same
          cases Option.some.inj same
          exact checked
  constructor
  · intro accepted
    have same := accepted.deterministic (checkAdmitted_computes state declarations witness claimed)
    apply reference.mp
    cases checked : checkAdmitted state declarations witness claimed with
    | false =>
        simp only [checked, boolean] at same
        simp at same
    | true => rfl
  · intro checked
    have computed := checkAdmitted_computes state declarations witness claimed
    rw [reference.mpr checked] at computed
    exact computed

theorem checkStatic_result_exact (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term) (result : Term) :
    Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] result ↔
      result = boolean (checkStatic declarations witness claimed) := by
  constructor
  · exact fun run => run.deterministic (checkStatic_computes declarations witness claimed)
  · rintro rfl
    exact checkStatic_computes declarations witness claimed

theorem checkStatic_accepts_iff (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] (.sym "True") ↔
      ∃ after, AdmissionRun initialAdmission declarations after ∧ ProofWitness.Checks after.theory witness claimed := by
  have bound := checkAdmitted_accepts_iff initialAdmission declarations witness claimed
  have agrees : Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] (.sym "True") ↔
      Applies P H "vibe:check-admitted" [encodeState initialAdmission, encodeDeclarations declarations, encodeWitness witness, encode claimed] (.sym "True") := by
    constructor
    · intro accepted
      have same := accepted.deterministic (checkStatic_computes declarations witness claimed)
      rw [same]
      exact checkAdmitted_computes initialAdmission declarations witness claimed
    · intro accepted
      have same := accepted.deterministic (checkAdmitted_computes initialAdmission declarations witness claimed)
      rw [same]
      exact checkStatic_computes declarations witness claimed
  exact agrees.trans bound

theorem checkStatic_refuses_iff (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term) :
    Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] (.sym "False") ↔
      ¬ ∃ after, AdmissionRun initialAdmission declarations after ∧ ProofWitness.Checks after.theory witness claimed := by
  rw [← checkStatic_accepts_iff, checkStatic_result_exact, checkStatic_result_exact]
  cases checkStatic declarations witness claimed <;> simp [boolean]

theorem checkStatic_derived {declarations : List Declaration} {witness : ProofWitness} {claimed : Spec.Term}
    (accepted : Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] (.sym "True")) :
    ∃ after, AdmissionRun initialAdmission declarations after ∧ Hosted after.theory after.nextFresh ∧ Spec.Derives after.theory claimed := by
  obtain ⟨after, run, checked⟩ := (checkStatic_accepts_iff _ _ _).mp accepted
  exact ⟨after, run, run.hosted initialAdmission_hosted, checked.derives⟩

theorem checkStatic_certificate_exists {declarations : List Declaration} {after : AdmissionState}
    (run : admitRun initialAdmission declarations = some after) {claimed : Spec.Term} (derived : Spec.Derives after.theory claimed) :
    ∃ witness fuel, apply P H fuel "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] =
      .value (.sym "True") := by
  obtain ⟨witness, checked⟩ := certificate_exists (admitted_run_hosted run) derived
  obtain ⟨fuel, accepted⟩ := (checkStatic_accepts_iff _ _ _).mpr ⟨after, (admitRun_eq_some_iff _ _ _).mp run, checked⟩
  exact ⟨witness, fuel, accepted⟩

theorem checkStatic_completed_exact (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] ≠ .exhausted) :
    apply P H fuel "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed] =
      .value (boolean (checkStatic declarations witness claimed)) :=
  (checkStatic_computes declarations witness claimed).completed fuel finished

theorem admit_completed_exact (state : AdmissionState) (declaration : Declaration) (fuel : Nat)
    (finished : apply P H fuel "vibe:admit" [encodeState state, encodeDeclaration declaration] ≠ .exhausted) :
    apply P H fuel "vibe:admit" [encodeState state, encodeDeclaration declaration] =
      .value (encodeAdmissionResult (admit state declaration)) :=
  (admit_computes state declaration).completed fuel finished

theorem admitRun_completed_exact (state : AdmissionState) (declarations : List Declaration) (fuel : Nat)
    (finished : apply P H fuel "vibe:admission-run" [encodeState state, encodeDeclarations declarations] ≠ .exhausted) :
    apply P H fuel "vibe:admission-run" [encodeState state, encodeDeclarations declarations] =
      .value (encodeAdmissionResult (admitRun state declarations)) :=
  (admitRun_computes state declarations).completed fuel finished

theorem prior_derivation_preserved {before after : AdmissionState} {declarations : List Declaration}
    (run : AdmissionRun before declarations after) (hosted : Hosted before.theory before.nextFresh)
    {statement : Spec.Term} (derived : Spec.Derives before.theory statement) : Spec.Derives after.theory statement :=
  derives_theory_extension hosted (run.theory_extension hosted) derived

end Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission
