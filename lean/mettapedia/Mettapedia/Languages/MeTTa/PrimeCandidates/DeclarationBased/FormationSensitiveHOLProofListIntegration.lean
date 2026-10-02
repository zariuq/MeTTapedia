import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveNativeHOLMapExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizProofComparison

/-!
# Native HOL proof consumption and List computation in one environment

The unchanged implication/universal proof decoder and the existing native
List/relator declarations share a rules environment. Explicit morphisms
preserve the actual compiler judgments and native computation paths. This
is joint syntactic admission and computation, not a semantic model of the
whole extension or a native compilation of primitive HOL induction/equality.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveHOLProofListIntegration

open Presentation Presentation.Declaration Presentation.SchemaElaboration
open Mettapedia.Logic

namespace Execution
export FormationSensitiveNativeHOLMapExecution
  (nativeInstance holMorphism commonReduction CommonReduces)
end Execution

def rules : Rules Tower.Head :=
  extendRules Execution.nativeInstance.rules FormationSensitiveHOLProofFamily.declarations

abbrev Typing {n : Nat} (context : Tower.Ctx n) (term type : Tower.Tm n) :=
  FormationSensitive.Typing rules context term type

theorem executionMorphism :
    FormationSensitiveNativeHOLMapExecution.rules.Morphism rules (fun head => head) :=
  extensionMorphism Execution.nativeInstance.rules FormationSensitiveHOLProofFamily.extends_source

theorem proof_entry_fresh {name : DeclName} {entry : Entry Tower.Head}
    (known : FormationSensitiveHOLProofFamily.declarations.entries name = some entry) :
    NativeIndexedFamilies.IntrinsicRelator.rawSignature.typeOf? name = none := by
  by_cases equal : name = FormationSensitiveHOLProofFamily.proofName
  · subst name
    decide
  · have prior : FormationSensitiveHOLUniformList.declarations.entries name = some entry := by
      simpa [FormationSensitiveHOLProofFamily.declarations, Signature.insert, equal] using known
    exact (HOLNativeRelatorCompatibility.hol_entry_fresh prior).2

theorem proofMorphism :
    FormationSensitiveHOLProofFamily.rules.Morphism rules (fun head => head) where
  headTyping := fun h => h
  isUniverse := fun h => h
  join := fun h => h
  cumulative := fun h => h
  headEq := fun h => h
  constantType := by
    intro name type known
    have sourceKnown : FormationSensitiveHOLProofFamily.declarations.typeOf? name = some type := known
    obtain ⟨entry, entryKnown, _⟩ := Option.map_eq_some_iff.mp sourceKnown
    have fresh := proof_entry_fresh entryKnown
    apply combinedType_of_signature Execution.nativeInstance.rules
      FormationSensitiveHOLProofFamily.declarations
    · simp [LevelInstance.rules, extendRules, combinedType, LevelTower.rules,
        LevelInstance.signature, Signature.typeOf_instantiateLevels, fresh]
    · simpa only [Tm.mapHead_id] using sourceKnown
  computation := by
    intro n left right step
    simp only [Tm.mapHead_id]
    change RootStep Execution.nativeInstance.rules FormationSensitiveHOLProofFamily.declarations n left right
    cases step with
    | inherited impossible => exact impossible.elim
    | delta known => exact .delta known
    | declared decoder => exact .declared decoder

theorem proof_typed {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : FormationSensitive.Typing FormationSensitiveHOLProofFamily.rules context term type) :
    Typing context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead proofMorphism

theorem proof_context {n : Nat} {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation FormationSensitiveHOLProofFamily.rules context) :
    FormationSensitive.ContextFormation rules context := by
  simpa only [Ctx.mapHead_id] using formed.mapHead proofMorphism

theorem execution_typed {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : FormationSensitiveNativeHOLMapExecution.Typing context term type) :
    Typing context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead executionMorphism

theorem execution_context {n : Nat} {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation FormationSensitiveNativeHOLMapExecution.rules context) :
    FormationSensitive.ContextFormation rules context := by
  simpa only [Ctx.mapHead_id] using formed.mapHead executionMorphism

open HOLNaturalDeductionNativeTranslation

/-- Successful translation is the existing compiler's actual result. Its
complete judgment is included without replacing the compiler or decoder. -/
theorem compiler_judgment {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax HOL.UniformListInduction.Symbol delta phi)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (formed : FormationSensitive.ContextFormation FormationSensitiveHOLProofFamily.rules target)
    (objectTyped : NativeTyping.Objects target objects)
    (hypothesisTyped : NativeTyping.Hypotheses target objects hypotheses)
    (success : compile source objects hypotheses = some native) :
    ∃ code, represent phi = some code ∧
      FormationSensitive.Judgment rules target native
        (FormationSensitiveHOLProofFamily.proof (subst objects code)) := by
  obtain ⟨code, represented, admitted⟩ := NativeTyping.compile_judgment source
    formed objectTyped hypothesisTyped success
  exact ⟨code, represented, proof_context admitted.1, proof_typed admitted.2⟩

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def reduction (n : Nat) : Mettapedia.GSLT.GSLT :=
  equalityGSLT (Tower.Tm n) (StepCore rules.computation rules.headEq)

abbrev Reduces {n : Nat} (left right : Tower.Tm n) := (reduction n).MultiStep left right

theorem execution_step {n : Nat} {left right : Tower.Tm n}
    (step : StepCore FormationSensitiveNativeHOLMapExecution.rules.computation
      FormationSensitiveNativeHOLMapExecution.rules.headEq left right) :
    StepCore rules.computation rules.headEq left right := by
  simpa only [Tm.mapHead_id] using
    step.mapHead (targetEq := rules.headEq) (fun head => head)
      executionMorphism.headEq executionMorphism.computation

theorem execution_path {n : Nat} {left right : Tower.Tm n}
    (path : Execution.CommonReduces left right) : Reduces left right := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (Execution.commonReduction n)
    (fun left right _ => Reduces left right) (fun _ => .refl _)
    (fun {_ _ _} edge _ ih => .step (execution_step edge) ih) left right path

theorem execution_observation {n : Nat} {source : Tower.Tm n}
    {predicate : Tower.Tm n → Prop}
    (observed : gsltDiamond (Execution.commonReduction n).closure predicate source) :
    gsltDiamond (reduction n).closure predicate source := by
  obtain ⟨target, ⟨intermediate, path, equal⟩, accepted⟩ :=
    (gsltDiamond_spec (Execution.commonReduction n).closure predicate source).1 observed
  subst target
  exact (gsltDiamond_spec (reduction n).closure predicate source).2
    ⟨intermediate, ⟨intermediate, execution_path path, rfl⟩, accepted⟩

open NativeListHOLPredicateObservation IntrinsicNativeListMapComputation

/-- The previously connected HOL-proof refinement and native execution both
remain admitted after installing the existing proof decoder. This theorem
does not assert that the HOL induction proof has been compiled natively. -/
theorem fusion_joint_admitted_observed {gamma : HOL.Ctx HOL.UniformListInduction.BaseSort}
    (f g : Tower.Tm gamma.length) (fMeaning gMeaning : FunctionMeaning gamma)
    (fDenotes : NativeHOLFragmentDenotation.Denotes model
      (type := HOL.UniformListInduction.mapping) f fMeaning)
    (gDenotes : NativeHOLFragmentDenotation.Denotes model
      (type := HOL.UniformListInduction.mapping) g gMeaning)
    (heads : Heads gamma)
    (interpreted : ∀ head ∈ heads, NativeHOLFragmentDenotation.Denotes model
      (type := HOL.UniformListInduction.element) head.1 head.2)
    (rho : model.Valuation gamma) (property : List Bool → Prop)
    (accepted : property (((headValues heads rho).map (functionValue gMeaning rho)).map
      (functionValue fMeaning rho))) :
    FormationSensitive.Judgment rules
        (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma)
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) (heads.map Prod.fst)))
        (NativeIndexedFamilies.Intrinsic.listApp (elementCode gamma)) ∧
      gsltDiamond (reduction gamma.length).closure (observes rho property)
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) (heads.map Prod.fst))) := by
  have result := FormationSensitiveNativeHOLMapExecution.hol_fusion_admitted_observed
    f g fMeaning gMeaning fDenotes gDenotes heads interpreted rho property accepted
  exact ⟨⟨execution_context result.2.1.1, execution_typed result.2.1.2⟩,
    execution_observation result.2.2.2⟩

namespace Consumer

open HOL.UniformListInduction
open FormationSensitiveHOLProofFamily (proof)

abbrev gamma : SourceContext := [element, sequence, sequence, .arr sequence .prop]

def x : Expr gamma sequence := .var (.vs .vz)
def y : Expr gamma sequence := .var (.vs (.vs .vz))
def predicate : Expr gamma (.arr sequence .prop) := .var (.vs (.vs (.vs .vz)))

def assumptionCode : Tower.Tm gamma.length := .app (.var 3) (.var 1)
def relationCode : Tower.Tm gamma.length :=
  FormationSensitiveHOLUniformList.rawAll (.arr sequence .prop)
    (FormationSensitiveHOLUniformList.rawImp (.app (.var 0) (.var 2)) (.app (.var 0) (.var 3)))

theorem assumption_represented : represent (.app predicate x) = some assumptionCode := rfl
theorem relation_represented :
    represent (HOLLeibnizProofComparison.Source.leibniz x y) = some relationCode := rfl
theorem predicate_represented : represent predicate = some (.var 3) := rfl

def base : Tower.Ctx 4 :=
  FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma

def firstContext : Tower.Ctx 5 := .snoc base (proof assumptionCode)
def firstObjects : Sub Tower.Head 4 5 := fun i => rename wk (ids i)
def firstHypotheses : Fin 1 → Tower.Tm 5 :=
  Fin.cases (.var 0) (fun i : Fin 0 => rename wk (Fin.elim0 i : Tower.Tm 4))

def proofContext : Tower.Ctx 6 :=
  .snoc firstContext (proof (subst firstObjects relationCode))
def objects : Sub Tower.Head 4 6 := fun i => rename wk (firstObjects i)
def hypotheses : Fin 2 → Tower.Tm 6 :=
  Fin.cases (.var 0) (fun i => rename wk (firstHypotheses i))

theorem base_objects : NativeTyping.Objects (gamma := gamma) base ids := by
  intro i
  simpa only [subst_ids, ids, base] using
    (FormationSensitive.Typing.var (R := FormationSensitiveHOLProofFamily.rules) (Γ := base) i)

theorem first_objects : NativeTyping.Objects (gamma := gamma) firstContext firstObjects :=
  base_objects.weaken (proof assumptionCode)

theorem objects_typed : NativeTyping.Objects (gamma := gamma) proofContext objects :=
  first_objects.weaken (proof (subst firstObjects relationCode))

theorem first_hypotheses : NativeTyping.Hypotheses
    (delta := [.app predicate x]) firstContext firstObjects firstHypotheses := by
  intro index
  fin_cases index
  refine ⟨assumptionCode, assumption_represented, ?_⟩
  exact .var 0

theorem hypotheses_typed : NativeTyping.Hypotheses
    (delta := [HOLLeibnizProofComparison.Source.leibniz x y, .app predicate x])
    proofContext objects hypotheses :=
  first_hypotheses.prepend relation_represented

theorem context_formed :
    FormationSensitive.ContextFormation FormationSensitiveHOLProofFamily.rules proofContext := by
  have baseFormed := FormationSensitiveHOLProofFamily.include_context
    (FormationSensitiveHOLInterface.context_formed FormationSensitiveHOLUniformList.signature gamma)
  have firstFormed : FormationSensitive.ContextFormation
      FormationSensitiveHOLProofFamily.rules firstContext := by
    refine FormationSensitive.ContextFormation.snoc baseFormed ?_ (.sort Tower.zero)
    apply FormationSensitiveHOLProofFamily.proof_formed
    simpa only [subst_ids, FormationSensitiveHOLInterface.typeAt,
      FormationSensitiveHOLUniformList.types, liftClosed, rename] using
      NativeTyping.represented_typed assumption_represented base_objects
  exact .snoc firstFormed
    (FormationSensitiveHOLProofFamily.proof_formed
      (NativeTyping.represented_typed relation_represented first_objects)) (.sort Tower.zero)

def term : Tower.Tm 6 := .app (.app (hypotheses 0) (subst objects (.var 3))) (hypotheses 1)

theorem actual_compilation :
    compile (HOLLeibnizProofComparison.Native.predicateTransport x y predicate) objects hypotheses =
      some term :=
  HOLLeibnizProofComparison.Native.compile_predicateTransport x y predicate
    predicate_represented objects hypotheses

theorem admitted :
    ∃ conclusion, represent (.app predicate y) = some conclusion ∧
      FormationSensitive.Judgment rules proofContext term (proof (subst objects conclusion)) :=
  compiler_judgment (HOLLeibnizProofComparison.Native.predicateTransport x y predicate)
    context_formed objects_typed hypotheses_typed actual_compilation

open NativeIndexedFamilies IntrinsicNativeListMapComputation

def elementType {n : Nat} : Tower.Tm n := .const `HOLUniformList.element

theorem element_formed {n : Nat} (target : Tower.Ctx n) :
    FormationSensitiveNativeHOLMapExecution.Typing target elementType
      (sortTm Tower.zero) :=
  FormationSensitiveNativeHOLMapExecution.hol_typed
    (FormationSensitiveHOLUniformList.simple_type_formed element target)

/-- The added variable has a native inductive List type, not the abstract
HOL sequence type of the proof consumer's two source variables. -/
def jointContext : Tower.Ctx 7 := .snoc proofContext (Intrinsic.listApp elementType)

theorem joint_context_formed : FormationSensitive.ContextFormation rules jointContext :=
  .snoc (proof_context context_formed)
    (execution_typed (FormationSensitiveNativeHOLMapExecution.listApp_typed
      (element_formed proofContext))) (.sort Tower.zero)

def identityFunction : Tower.Tm 7 := .lam (.var 0)
def nativeInput : Tower.Tm 7 := encode elementType [.var 3]
def nativeProgram : Tower.Tm 7 := applyMap elementType elementType identityFunction nativeInput

theorem joint_actual_compilation :
    compile (HOLLeibnizProofComparison.Native.predicateTransport x y predicate)
      (fun i => rename wk (objects i)) (fun i => rename wk (hypotheses i)) =
      some (rename wk term) := by
  exact HOLLeibnizProofComparison.Native.compile_predicateTransport x y predicate
    predicate_represented (fun i => rename wk (objects i)) (fun i => rename wk (hypotheses i))

theorem identity_typed : FormationSensitiveNativeHOLMapExecution.Typing jointContext
    identityFunction (arrow elementType elementType) := by
  apply FormationSensitive.Typing.lamIntro
    (FormationSensitiveNativeHOLMapExecution.arrow_formed
      (element_formed jointContext) (element_formed jointContext)) (.sort Tower.zero)
  exact .var 0

theorem input_typed : FormationSensitiveNativeHOLMapExecution.Typing jointContext
    nativeInput (Intrinsic.listApp elementType) := by
  apply FormationSensitiveNativeHOLMapExecution.encode_typed (element_formed jointContext)
  intro value member
  have same : value = .var 3 := List.mem_singleton.mp member
  subst value
  exact .var 3

theorem program_typed : Typing jointContext nativeProgram (Intrinsic.listApp elementType) :=
  execution_typed (FormationSensitiveNativeHOLMapExecution.applyMap_typed
    (element_formed jointContext) (element_formed jointContext) identity_typed input_typed)

theorem native_computation : Reduces nativeProgram nativeInput := by
  apply execution_path
  apply FormationSensitiveNativeHOLMapExecution.computation_include
  have mapped := applyMap_encode Tower.zero elementType elementType identityFunction
    ([.var 3] : List (Tower.Tm 7))
  have heads := encode_pointwise Tower.zero (elementType : Tower.Tm 7)
    (fun value => .app identityFunction value) (fun value => value) [.var 3]
    (fun value _ => by
      exact .step (.betaPi (.var 0) value) (.refl _))
  exact mapped.trans heads

/-- The translated consumer and a nonempty native map calculation coexist
in one formed telescope with one authority. The proof assumptions concern
HOL sequence variables; no equality between those variables is inferred
from the separate native List calculation. -/
theorem joint_admission_and_computation :
    ∃ conclusion, represent (.app predicate y) = some conclusion ∧
      FormationSensitive.Judgment rules jointContext (rename wk term)
        (rename wk (proof (subst objects conclusion))) ∧
      FormationSensitive.Judgment rules jointContext nativeProgram
        (Intrinsic.listApp elementType) ∧
      FormationSensitive.Judgment rules jointContext nativeInput
        (Intrinsic.listApp elementType) ∧
      Reduces nativeProgram nativeInput := by
  obtain ⟨conclusion, represented, consumer⟩ := admitted
  exact ⟨conclusion, represented,
    ⟨joint_context_formed, consumer.2.weaken⟩,
    ⟨joint_context_formed, program_typed⟩,
    ⟨joint_context_formed, execution_typed input_typed⟩, native_computation⟩

end Consumer

namespace Controls

open NativeListHOLPredicateObservation.Controls

/-- Decoder installation does not turn the reversed-composition constructor
value into the proved value, even though that wrong output remains typed. -/
theorem wrong_composition_admitted_rejected :
    FormationSensitive.Judgment rules
        (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma)
        (encode (elementCode gamma) [.app g (.app f x)])
        (NativeIndexedFamilies.Intrinsic.listApp (elementCode gamma)) ∧
      ¬ observes rho (fun output => output = [true])
        (encode (elementCode gamma) [.app g (.app f x)]) := by
  have checked := FormationSensitiveNativeHOLMapExecution.Examples.wrong_composition_typed_rejected
  exact ⟨⟨execution_context checked.1.1, execution_typed checked.1.2⟩, checked.2⟩

/-- These are distinct native syntax types, not aliases made equal by the
construction. This is not a claim of non-convertibility under arbitrary extensions. -/
theorem sequence_and_list_distinct :
    NativeIndexedFamilies.Intrinsic.listApp (Consumer.elementType : Tower.Tm 0) ≠
      FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types 0
        HOL.UniformListInduction.sequence := by
  intro equal
  cases equal

end Controls

#print axioms executionMorphism
#print axioms proofMorphism
#print axioms compiler_judgment
#print axioms execution_path
#print axioms execution_observation
#print axioms fusion_joint_admitted_observed
#print axioms Consumer.context_formed
#print axioms Consumer.actual_compilation
#print axioms Consumer.joint_actual_compilation
#print axioms Consumer.admitted
#print axioms Consumer.joint_admission_and_computation
#print axioms Controls.wrong_composition_admitted_rejected
#print axioms Controls.sequence_and_list_distinct

end FormationSensitiveHOLProofListIntegration
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
