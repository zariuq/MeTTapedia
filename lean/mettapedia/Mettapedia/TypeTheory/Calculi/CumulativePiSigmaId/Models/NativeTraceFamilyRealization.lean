import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceLambdaSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLHenkinFamilySemantics
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding

/-!
# Membership-family realization of native trace-coded functions

A set code is interpreted by its actual membership fibre.  This keeps the
environment, variable projections and dependent context extension unchanged.
The native variable/lambda/application tree is also unchanged: its trace-coded
interpretation realizes the same section in the ordinary dependent-family
interpretation, using the proved product decoder at function boundaries.

The result is forward realization, not reflection or uniqueness of arbitrary
semantic conversions.  Product decoding is a semantic representation change;
it is not a computation rule for the native checker.  No interpretation of
HOL constants, admitted quantifiers or arbitrary HOTG axioms is inferred from
the lambda-fragment theorem.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceFamilyRealization

open Mettapedia.Logic
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension extensionSubstitution)
open HOLNativeGenericProofCompiler
open FormationSensitiveHOLInterface

universe u v

/-- Interpret a set family by actual membership, rather than choosing a
different carrier with the same cardinality. -/
def membershipFamily {Environment : Type (u + 1)}
    (family : SetFamily Environment) : HenkinFamilySemantics.Family Environment :=
  fun environment => Elements (family environment)

/-- Decode the families of a semantic telescope, retaining all its variables
and their actual projection sections. -/
def realizeContext {n : Nat} (context : NativeTraceLambdaSemantics.Context.{u} n) :
    HenkinFamilySemantics.SemanticContext.{u + 1} n where
  Environment := context.Environment
  family := fun index => membershipFamily (context.family index)
  projection := context.projection

@[simp] theorem realizeContext_snoc {n : Nat}
    (context : NativeTraceLambdaSemantics.Context.{u} n)
    (family : SetFamily context.Environment) :
    realizeContext (context.snoc family) =
      (realizeContext context).snoc (membershipFamily family) := by
  unfold realizeContext NativeTraceLambdaSemantics.Context.snoc
    HenkinFamilySemantics.SemanticContext.snoc
  congr 1
  · funext index environment
    refine Fin.cases ?_ (fun prior => ?_) index <;> rfl
  · apply Function.hfunext rfl
    intro index other same
    cases same
    refine Fin.cases ?_ (fun prior => ?_) index <;> rfl

/-- Membership interpretation commutes with arbitrary environment maps,
including noninjective maps. -/
@[simp] theorem membershipFamily_substitution
    {Environment Target : Type (u + 1)} (theta : Target → Environment)
    (family : SetFamily Environment) :
    membershipFamily (family ∘ theta) = membershipFamily family ∘ theta := rfl

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Recursively realize the SAME native term and section in ordinary dependent
families.  The Henkin model only supplies the signature of the ambient
interpretation; this fragment uses neither constants nor quantification. -/
theorem denotes_realization
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const)
    {n : Nat} {context : NativeTraceLambdaSemantics.Context.{u} n}
    {term : NativeTraceLambdaSemantics.Tm n}
    {family : SetFamily context.Environment} {value : Section family}
    (meaning : NativeTraceLambdaSemantics.Denotes context term family value) :
    HenkinFamilySemantics.Denotes signature model (realizeContext context)
      term.erase (membershipFamily family) value := by
  induction meaning with
  | var context index =>
      exact HenkinFamilySemantics.Denotes.var (realizeContext context) index
  | @lam n context domain codomain body bodyValue bodyMeaning bodyInduction =>
      have ordinaryBody : HenkinFamilySemantics.Denotes signature model
          ((realizeContext context).snoc (membershipFamily domain)) body.erase
          (membershipFamily codomain) bodyValue := by
        convert bodyInduction using 2
        apply Iff.of_eq
        congr 1
        exact (realizeContext_snoc context domain).symm
      exact HenkinFamilySemantics.Denotes.convert
        (HenkinFamilySemantics.Denotes.abstraction ordinaryBody)
        (fun environment => (ZFSetTraceContextual.piDecode domain codomain environment).symm)
  | @app n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      have ordinaryFunction := HenkinFamilySemantics.Denotes.convert
        functionInduction
        (fun environment => ZFSetTraceContextual.piDecode domain codomain environment)
      exact HenkinFamilySemantics.Denotes.application
        (codomain := membershipFamily codomain) ordinaryFunction argumentInduction

/-- The decoded function applies the actual set trace, rather than an
independently selected semantic function. -/
theorem decoded_application_value {Environment : Type (u + 1)}
    {domain : SetFamily Environment} {codomain : SetFamily (Extension domain)}
    (function : Section (ZFSetTraceContextual.piFamily domain codomain))
    (argument : Section domain) (environment : Environment) :
    ((ZFSetTraceContextual.piDecode domain codomain environment
      (function environment)) (argument environment)).1 =
      ZFSetTraceProducts.traceApp (function environment).1 (argument environment).1 :=
  ZFSetTraceContextual.piDecode_value domain codomain environment _ _

/-- Realization respects the actual native beta computation, including its
dependent result fibre. -/
theorem beta_realization
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const)
    {n : Nat} {context : NativeTraceLambdaSemantics.Context.{u} n}
    {domain : SetFamily context.Environment}
    {codomain : SetFamily (Extension domain)}
    {body : NativeTraceLambdaSemantics.Tm (n + 1)}
    {argument : NativeTraceLambdaSemantics.Tm n}
    {bodyValue : Section codomain} {argumentValue : Section domain}
    (bodyMeaning : NativeTraceLambdaSemantics.Denotes
      (context.snoc domain) body codomain bodyValue)
    (argumentMeaning : NativeTraceLambdaSemantics.Denotes
      context argument domain argumentValue) :
    HenkinFamilySemantics.Denotes signature model (realizeContext context)
      (.app (.lam body.erase) argument.erase)
      (membershipFamily (fun environment =>
        codomain ⟨environment, argumentValue environment⟩))
      (fun environment => bodyValue ⟨environment, argumentValue environment⟩) :=
  denotes_realization signature model
    (NativeTraceLambdaSemantics.beta bodyMeaning argumentMeaning)

/-- Actual membership in the separated proof set decodes to a proof of the
same proposition.  Neither direction extracts a source proof tree by choice. -/
noncomputable def truthMembershipEquiv (proposition : Prop) :
    Elements (ZFSetTraceProofDecoding.truthCode.{u} proposition) ≃
      ULift.{u + 1, 0} (PLift proposition) where
  toFun value := ULift.up (PLift.up
    ((ZFSetTraceProofDecoding.mem_truthCode proposition value.1).mp value.2).2)
  invFun proof := ⟨∅, (ZFSetTraceProofDecoding.mem_truthCode proposition ∅).mpr
    ⟨rfl, proof.down.down⟩⟩
  left_inv value := Subtype.ext
    (((ZFSetTraceProofDecoding.mem_truthCode proposition value.1).mp value.2).1).symm
  right_inv _ := rfl

/-- A native proof in the trace fragment realizes the ordinary proof family
of the same proposition, with the native term retained as its index. -/
theorem proof_realization
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const)
    {n : Nat} {context : NativeTraceLambdaSemantics.Context.{u} n}
    {term : NativeTraceLambdaSemantics.Tm n}
    {proposition : context.Environment → Prop}
    {value : Section (ZFSetTraceProofDecoding.truthFamily proposition)}
    (meaning : NativeTraceLambdaSemantics.Denotes context term
      (ZFSetTraceProofDecoding.truthFamily proposition) value) :
    HenkinFamilySemantics.Denotes signature model (realizeContext context) term.erase
      (HenkinFamilySemantics.truthFamily proposition)
      (fun environment => truthMembershipEquiv (proposition environment) (value environment)) :=
  HenkinFamilySemantics.Denotes.convert (denotes_realization signature model meaning)
    (fun environment => truthMembershipEquiv (proposition environment))

/-- The proof decoder is natural under the same environment map as the
function decoder, retaining the original section at the mapped point. -/
theorem proof_decode_substitution {Environment Target : Type (u + 1)}
    (theta : Target → Environment) (proposition : Environment → Prop)
    (value : Section (ZFSetTraceProofDecoding.truthFamily proposition)) :
    HenkinFamilySemantics.mapSection
        (fun target => truthMembershipEquiv (proposition (theta target)))
        (fun target => value (theta target)) =
      fun target => HenkinFamilySemantics.mapSection
        (fun environment => truthMembershipEquiv (proposition environment)) value
        (theta target) := rfl

/-- An actual environment is required: an empty telescope interpretation
must not validate a false closed proposition by having no inputs. -/
theorem false_proof_rejected {Environment : Type (u + 1)}
    (value : Section (ZFSetTraceProofDecoding.truthFamily (fun _ : Environment => False)))
    (environment : Environment) : False :=
  ((ZFSetTraceProofDecoding.mem_truthCode False (value environment).1).mp
    (value environment).2).2

namespace Controls

open ZFSetContextualInterpretation.Controls (domain codomain body zeroArgument oneArgument)

/-- A closed native identity lambda proves implication reflexivity.  The
proof section is obtained from its variable and abstraction interpretation,
then passed through the literal implication decoder and membership codec. -/
theorem identity_proof_realizes
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const) (proposition : Prop) :
    ∃ value : HenkinFamilySemantics.Section
        (HenkinFamilySemantics.truthFamily
          (fun _ : PUnit.{u + 2} => proposition → proposition)),
      HenkinFamilySemantics.Denotes signature model
        (realizeContext NativeTraceLambdaSemantics.Context.nil)
        (.lam (.var 0))
        (HenkinFamilySemantics.truthFamily (fun _ => proposition → proposition)) value := by
  let premise := fun _ : PUnit.{u + 2} => proposition
  have projectionMeaning := NativeTraceLambdaSemantics.Denotes.var
    (NativeTraceLambdaSemantics.Context.nil.snoc
      (ZFSetTraceProofDecoding.truthFamily premise)) 0
  have abstraction := NativeTraceLambdaSemantics.Denotes.lam projectionMeaning
  have decoded := abstraction.cast
    (ZFSetTraceProofDecoding.implication_decoder premise premise).symm
  exact ⟨_, proof_realization signature model decoded⟩

theorem closed_false_proof_rejected :
    ¬ ∃ (term : NativeTraceLambdaSemantics.Tm 0)
        (value : Section (ZFSetTraceProofDecoding.truthFamily
          (fun _ : PUnit.{u + 2} => False))),
      NativeTraceLambdaSemantics.Denotes NativeTraceLambdaSemantics.Context.nil
        term (ZFSetTraceProofDecoding.truthFamily (fun _ => False)) value := by
  rintro ⟨term, value, meaning⟩
  exact false_proof_rejected value PUnit.unit

/-- An input telescope supplies a real dependent function.  Its result fibre
is a singleton at zero and has two members at the other argument. -/
noncomputable def functionContext : NativeTraceLambdaSemantics.Context.{u} 1 where
  Environment := PUnit
  family := fun _ => ZFSetTraceContextual.piFamily domain codomain
  projection := fun _ => ZFSetTraceContextual.lam body

/-- The program calls its supplied function on its supplied argument. -/
def applicationProgram : NativeTraceLambdaSemantics.Tm 2 := .app (.var 1) (.var 0)

theorem application_denotes :
    NativeTraceLambdaSemantics.Denotes (functionContext.{u}.snoc domain)
      applicationProgram codomain body := by
  have functionMeaning := NativeTraceLambdaSemantics.Denotes.var
    (functionContext.{u}.snoc domain) (1 : Fin 2)
  have argumentMeaning := NativeTraceLambdaSemantics.Denotes.var
    (functionContext.{u}.snoc domain) (0 : Fin 2)
  have applied := NativeTraceLambdaSemantics.Denotes.app
    (context := functionContext.{u}.snoc domain)
    (a := domain ∘ Sigma.fst)
    (b := codomain ∘ extensionSubstitution Sigma.fst domain)
    (function := .var 1) (argument := .var 0)
    (functionValue := fun point => ZFSetTraceContextual.lam body point.1)
    (argumentValue := fun point => point.2)
    functionMeaning argumentMeaning
  have values : (fun point : Extension domain.{u} =>
      ZFSetTraceContextual.piDecode domain codomain point.1
        (ZFSetTraceContextual.lam body point.1) point.2) = body := by
    funext point
    exact congrFun ((ZFSetTraceContextual.piDecode domain codomain point.1).apply_symm_apply
      (fun argument => body ⟨point.1, argument⟩)) point.2
  change NativeTraceLambdaSemantics.Denotes (functionContext.{u}.snoc domain)
    applicationProgram codomain
    (fun point => ZFSetTraceContextual.piDecode domain codomain point.1
      (ZFSetTraceContextual.lam body point.1) point.2) at applied
  exact applied.change_value values

/-- Both models interpret the actual application tree, not just the product
decoder in isolation. -/
theorem application_realizes
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const) :
    HenkinFamilySemantics.Denotes signature model
      (realizeContext (functionContext.{u}.snoc domain)) applicationProgram.erase
      (membershipFamily codomain) body :=
  denotes_realization signature model application_denotes

theorem application_zero : (body.{u} ⟨PUnit.unit, zeroArgument PUnit.unit⟩).1 = ∅ := rfl

theorem application_one :
    (body.{u} ⟨PUnit.unit, oneArgument PUnit.unit⟩).1 = ZFSet.powerset ∅ := rfl

/-- A constant-empty implementation disagrees with the interpreted program
on a genuinely inhabited input fibre. -/
theorem wrong_constant_application :
    (body.{u} ⟨PUnit.unit, oneArgument PUnit.unit⟩).1 ≠ ∅ := by
  have wrong := ZFSetTraceContextual.Controls.wrong_constant_result.{u}
  rw [ZFSetTraceContextual.app_lam] at wrong
  exact wrong

theorem result_fibres_distinct :
    codomain.{u} ⟨PUnit.unit, zeroArgument PUnit.unit⟩ ≠
      codomain ⟨PUnit.unit, oneArgument PUnit.unit⟩ :=
  ZFSetDependentProducts.Controls.varying_fibres_distinct

end Controls

#print axioms denotes_realization
#print axioms decoded_application_value
#print axioms beta_realization
#print axioms truthMembershipEquiv
#print axioms proof_realization
#print axioms proof_decode_substitution
#print axioms false_proof_rejected
#print axioms Controls.application_denotes
#print axioms Controls.identity_proof_realizes
#print axioms Controls.closed_false_proof_rejected
#print axioms Controls.application_realizes
#print axioms Controls.wrong_constant_application
#print axioms Controls.result_fibres_distinct

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceFamilyRealization
