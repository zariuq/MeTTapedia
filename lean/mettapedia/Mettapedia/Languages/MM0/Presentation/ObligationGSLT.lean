import Mettapedia.Languages.MM0.Presentation.ObligationComputations
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Computational MM0 proof obligations as a GSLT

One transition resolves one independent rule constructor. Hypotheses are read
by position; theorem application reads the actual declaration and computes its
ordered instantiated premises; conversion checks a submitted conversion and
leaves its left endpoint as a proof obligation. The unchanged suffix retains
all outstanding occurrences. A transition never checks a complete proof.

The discharge theorem is proved against the independent `Derives` judgment.
Finite computations and finite derivations provide paths without prescribing
a terminating proof-search algorithm. The generated OSLF type uses this actual
local transition relation.

The equations on obligation lists are syntactic equality. MM0 definitional
conversion is retained as the explicit, typed conversion rule; it is not
silently imposed as equality of the obligation carrier.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalObligations

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open ComputationalProof ComputationalConversion ComputationalAdmission
open Mettapedia.GSLT Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

inductive Resolves (theory : Theory) (context : Context) (hypotheses : List Preterm) :
    List Preterm → List Preterm → Prop where
  | hypothesis {index : Nat} {claim : Preterm} {rest : List Preterm} :
      Applies admissionProgram dataEqualityHost "mm0:data-at" [encodeExpressions hypotheses, natural index]
        (encodeResult (some claim)) → Resolves theory context hypotheses (claim :: rest) rest
  | theoremApp {index : Nat} {declaration : TheoremDecl} {arguments : List Preterm}
      {instantiation : TheoremInstance} {rest : List Preterm} :
      Applies admissionProgram dataEqualityHost "nik:nat-table-get"
        [encodeTheorems theory.theorems, natural index] (encodeLookupResult (some (encodeTheorem declaration))) →
      Applies admissionProgram dataEqualityHost "mm0:instantiate-theorem"
        [encodeTable theory.terms, encodeContext context, encodeTheorem declaration, encodeExpressions arguments]
        (encodeInstance (some instantiation)) →
      Resolves theory context hypotheses (instantiation.conclusion :: rest) (instantiation.hypotheses ++ rest)
  | conversion {witness : ConvWitness} {left right : Preterm} {sort : Nat} {rest : List Preterm} :
      Applies admissionProgram dataEqualityHost "mm0:conversion"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext context,
          ComputationalConversion.encodeWitness witness] (encodeConversion (some ⟨left, right, sort⟩)) →
      Resolves theory context hypotheses (right :: rest) (left :: rest)

def obligationGSLT (theory : Theory) (context : Context) (hypotheses : List Preterm) : GSLT where
  Term := List Preterm
  equations := { r := Eq, iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := Resolves theory context hypotheses
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

theorem Resolves.append_right {theory : Theory} {context : Context} {hypotheses : List Preterm}
    {source target : List Preterm} (step : Resolves theory context hypotheses source target)
    (suffix : List Preterm) : Resolves theory context hypotheses (source ++ suffix) (target ++ suffix) := by
  cases step with
  | hypothesis computed => exact .hypothesis computed
  | theoremApp lookup instantiated =>
      simpa only [List.cons_append, List.append_assoc] using
        (Resolves.theoremApp (rest := _ ++ suffix) lookup instantiated)
  | conversion computed => exact .conversion computed

theorem Resolves.nonempty_source {theory : Theory} {context : Context} {hypotheses : List Preterm}
    {source target : List Preterm} (step : Resolves theory context hypotheses source target) : source ≠ [] := by
  cases step <;> simp

section Discharge

variable (theory : Theory) (context : Context) (hypotheses : List Preterm)

local notation "S" => obligationGSLT theory context hypotheses
local notation "D" => Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses
local notation "DL" => DerivesList theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses

theorem derivesList_append (first second : List Preterm) :
    DL (first ++ second) ↔ DL first ∧ DL second := by
  constructor
  · intro derived
    have pointwise := (derivesList_iff _ _ _ _ _ _).mp derived
    exact ⟨(derivesList_iff _ _ _ _ _ _).mpr (fun value member => pointwise value (List.mem_append_left _ member)),
      (derivesList_iff _ _ _ _ _ _).mpr (fun value member => pointwise value (List.mem_append_right _ member))⟩
  · rintro ⟨left, right⟩
    apply (derivesList_iff _ _ _ _ _ _).mpr
    intro value member
    rcases List.mem_append.mp member with firstMember | secondMember
    · exact (derivesList_iff _ _ _ _ _ _).mp left value firstMember
    · exact (derivesList_iff _ _ _ _ _ _).mp right value secondMember

theorem step_reflects {source target : List Preterm}
    (step : GSLT.Step S source target) (derived : DL target) : DL source := by
  cases step with
  | hypothesis computed =>
      exact .cons (.hypothesis (List.mem_of_getElem? ((hypothesis_query_exact _ _ _).mp computed))) derived
  | @theoremApp index declaration arguments instantiation rest lookup computed =>
      obtain ⟨premises, suffix⟩ := (derivesList_append theory context hypotheses _ _).mp derived
      exact .cons (.theoremApp ((theorem_query_exact _ _ _).mp lookup)
        ((instance_query_exact _ _ _ _ _).mp computed) premises) suffix
  | conversion computed =>
      cases derived with
      | cons left suffix =>
          exact .cons (.conversion ((conversion_query_exact _ _ _ _ _ _).mp computed).derives left) suffix

theorem discharge_reflects {goals : List Preterm} (path : GSLT.MultiStep S goals []) : DL goals := by
  have reflects {source target : List Preterm} (steps : GSLT.MultiStep S source target) : DL target → DL source := by
    let motive : ∀ first last : List Preterm, GSLT.MultiStep S first last → Prop :=
      fun first last _ => DL last → DL first
    exact @GSLT.MultiStep.rec (obligationGSLT theory context hypotheses) motive
      (fun _ derived => derived)
      (fun first _ ih derived => step_reflects theory context hypotheses first (ih derived)) source target steps
  exact reflects path .nil

theorem path_append {source target : List Preterm} (path : GSLT.MultiStep S source target) (suffix : List Preterm) :
    GSLT.MultiStep S (source ++ suffix) (target ++ suffix) := by
  let motive : ∀ first last : List Preterm, GSLT.MultiStep S first last → Prop :=
    fun first last _ => GSLT.MultiStep S (first ++ suffix) (last ++ suffix)
  exact @GSLT.MultiStep.rec (obligationGSLT theory context hypotheses) motive
    (fun (first : List Preterm) => @GSLT.MultiStep.refl S (first ++ suffix))
    (fun first _ ih => GSLT.MultiStep.step (Resolves.append_right first suffix) ih) source target path

theorem path_trans {first second third : List Preterm}
    (left : GSLT.MultiStep S first second) (right : GSLT.MultiStep S second third) : GSLT.MultiStep S first third := by
  let motive : ∀ first last : List Preterm, GSLT.MultiStep S first last → Prop :=
    fun first last _ => GSLT.MultiStep S last third → GSLT.MultiStep S first third
  exact @GSLT.MultiStep.rec (obligationGSLT theory context hypotheses) motive
    (fun _ suffix => suffix)
    (fun first _ ih suffix => GSLT.MultiStep.step first (ih suffix)) first second left right

theorem derivations_discharge {goals : List Preterm} (derived : DL goals) : GSLT.MultiStep S goals [] := by
  induction derived using DerivesList.rec
      (motive_1 := fun goal _ => GSLT.MultiStep S [goal] []) with
  | hypothesis member =>
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
      exact .step (.hypothesis ((hypothesis_query_exact _ _ _).mpr lookup)) (@GSLT.MultiStep.refl S [])
  | theoremApp lookup instantiated _ ih =>
      exact .step (.theoremApp ((theorem_query_exact _ _ _).mpr lookup)
        ((instance_query_exact _ _ _ _ _).mpr instantiated)) (by simpa only [List.append_nil] using ih)
  | conversion converted _ ih =>
      obtain ⟨witness, checked⟩ := converted.certificate_exists
      exact .step (.conversion ((conversion_query_exact _ _ witness _ _ _).mpr checked)) ih
  | nil => exact @GSLT.MultiStep.refl S []
  | @cons goal goals _ _ ihHead ihTail =>
      exact path_trans theory context hypotheses
        (by simpa only [List.singleton_append, List.nil_append] using path_append theory context hypotheses ihHead goals)
        ihTail

theorem discharge_iff_derivesList (goals : List Preterm) : GSLT.MultiStep S goals [] ↔ DL goals :=
  ⟨discharge_reflects theory context hypotheses, derivations_discharge theory context hypotheses⟩

theorem singleton_discharge_iff (goal : Preterm) : GSLT.MultiStep S [goal] [] ↔ D goal := by
  rw [discharge_iff_derivesList]
  constructor
  · intro derived
    cases derived with
    | cons head _ => exact head
  · intro derived
    exact .cons derived .nil

end Discharge

def derivableNativeType (theory : Theory) (context : Context) (hypotheses : List Preterm) :
    GSLTNativeType (obligationGSLT theory context hypotheses) where
  sort := ()
  pred := invariantPredicate (obligationGSLT theory context hypotheses)
    (fun goals => (obligationGSLT theory context hypotheses).MultiStep goals [])
    (by intro left right same; subst right; rfl)

theorem nativeType_iff_derivesList (theory : Theory) (context : Context) (hypotheses goals : List Preterm) :
    (gsltOSLF (obligationGSLT theory context hypotheses)).satisfies goals
      (derivableNativeType theory context hypotheses).pred ↔
      DerivesList theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses goals :=
  discharge_iff_derivesList theory context hypotheses goals

theorem nativeType_iff_derives (theory : Theory) (context : Context) (hypotheses : List Preterm) (goal : Preterm) :
    (gsltOSLF (obligationGSLT theory context hypotheses)).satisfies [goal]
      (derivableNativeType theory context hypotheses).pred ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses goal :=
  singleton_discharge_iff theory context hypotheses goal

theorem nativeType_iff_checked (theory : Theory) (context : Context) (hypotheses : List Preterm) (goal : Preterm) :
    (gsltOSLF (obligationGSLT theory context hypotheses)).satisfies [goal]
      (derivableNativeType theory context hypotheses).pred ↔
      ∃ proof, Applies admissionProgram dataEqualityHost "mm0:check-proof"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
          encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode goal] (.sym "True") :=
  (nativeType_iff_derives theory context hypotheses goal).trans
    (derives_iff_supplied_proof theory context hypotheses goal)

theorem accepted_proof_has_nativeType (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (goal : Preterm)
    (accepted : Applies admissionProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode goal] (.sym "True")) :
    (gsltOSLF (obligationGSLT theory context hypotheses)).satisfies [goal]
      (derivableNativeType theory context hypotheses).pred :=
  (nativeType_iff_checked theory context hypotheses goal).mpr ⟨proof, accepted⟩

theorem nativeType_has_finite_checked_execution (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (goal : Preterm)
    (inhabited : (gsltOSLF (obligationGSLT theory context hypotheses)).satisfies [goal]
      (derivableNativeType theory context hypotheses).pred) :
    ∃ proof fuel, apply admissionProgram dataEqualityHost fuel "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode goal] = .value (.sym "True") :=
  (nativeType_iff_checked theory context hypotheses goal).mp inhabited

end Mettapedia.Languages.MM0.Presentation.ComputationalObligations
