import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedEvidenceControls
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitutionCoherence

/-!
# Generated native functions under the actual compiler pullback

The bounded-natural interpretation lives on the compiler's own context
category. Its generated function is first pulled back to compiled programs
and then along the actual compiler map. Canonical native Pi comparisons
preserve abstraction, composition and dependent application in this same
presheaf topos. The supplied generated certificate and a returning rho
execution retain their separate mathematical roles.

These are native certificate calculations. They do not add natural-number
data or a dependent typing judgment to the compiled lambda language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafPiSubstitution
open DisplayedPresheafPiSubstitutionCoherence
open NamePassingDependentEvidence NamePassingGeneratedEvidenceControls
open Calculi.NativeDependent.ObjectInterpretation
open Calculi.NativeDependent.PresheafInterpretation
open Calculi.NativeDependent.Examples.BoundedNaturalModel

abbrev nativeBase := context nativeObjects 0
abbrev nativeDomain := objectFamily nativeObjects nativeBase
noncomputable abbrev nativeBody : DisplayedFamily (totalSpace nativeDomain) :=
  family nativeObjects nativeConstants nativePredicates input

/-- The unique map to the chosen empty native context in the same topos. -/
def compiledBase : compiledPrograms ⟶ nativeBase where
  app _ := TypeCat.ofHom fun _ => PUnit.unit
  naturality _ _ _ := by ext value; rfl

def sourceBase : sourcePrograms ⟶ nativeBase := compilerMap ≫ compiledBase

noncomputable def nativeFunction : (piDisplayed nativeDomain nativeBody).sections :=
  proof nativeObjects nativeConstants nativePredicates nativeDeclarations identityProof

noncomputable def compiledFunction :
    (piDisplayed (reindexDisplayed compiledBase nativeDomain)
      (reindexDisplayed (totalReindexMap compiledBase nativeDomain) nativeBody)).sections :=
  reindexFunction compiledBase nativeDomain nativeBody nativeFunction

noncomputable def sourceFunction :
    (piDisplayed (reindexDisplayed sourceBase nativeDomain)
      (reindexDisplayed (totalReindexMap sourceBase nativeDomain) nativeBody)).sections :=
  reindexFunction compilerMap (reindexDisplayed compiledBase nativeDomain)
    (reindexDisplayed (totalReindexMap compiledBase nativeDomain) nativeBody) compiledFunction

/-- Staged transport of this generated function agrees with the canonical
transport along the composite, on the entire natural function section. -/
theorem compiler_function_composition :
    sourceFunction = reindexFunction sourceBase nativeDomain nativeBody nativeFunction := by
  exact (reindexFunction_composition compilerMap compiledBase nativeDomain nativeBody
    nativeFunction).symm

/-- The generated abstraction is transported by the actual native product
comparison, rather than by evaluating it into a new chosen function. -/
theorem compiled_abstraction :
    compiledFunction = lamDisplayed
      (reindexDisplayedSection (totalReindexMap compiledBase nativeDomain) nativeBody
        (inputSection ContextCategory)) :=
  reindexFunction_lam compiledBase nativeDomain nativeBody (inputSection ContextCategory)

def nativeArgument (number : Nat) : nativeDomain.sections :=
  objectSection nativeObjects nativeConstants (.constant number)

noncomputable def nativeApplication (number : Nat) :=
  appDisplayed nativeFunction (nativeArgument number)

noncomputable def compiledApplication (number : Nat) :=
  appDisplayed compiledFunction
    (reindexDisplayedSection compiledBase nativeDomain (nativeArgument number))

noncomputable def sourceApplication (number : Nat) :=
  appDisplayed sourceFunction
    (reindexDisplayedSection sourceBase nativeDomain (nativeArgument number))

theorem native_application_computes (world : ContextCategoryᵒᵖ) (number : Nat) :
    HEq ((nativeApplication number).val (point ContextCategory world))
      (⟨number, Nat.lt_succ_self number⟩ : Fin (number + 1)) := by
  change HEq ((appDisplayed (lamDisplayed (inputSection ContextCategory))
    (nativeArgument number)).val _) _
  rw [pi_beta (inputSection ContextCategory) (nativeArgument number)]
  rfl

/-- Dependent application after pullback retains its supplied input and
the actual Fin (n + 1) witness at every compiled-program point. -/
theorem compiled_application_computes (position : compiledPrograms.Elements) (number : Nat) :
    HEq ((compiledApplication number).val position)
      (⟨number, Nat.lt_succ_self number⟩ : Fin (number + 1)) := by
  unfold compiledApplication compiledFunction
  rw [app_substitution compiledBase nativeDomain nativeBody nativeFunction (nativeArgument number)]
  exact (DisplayedPresheafCwf.reindexDependentSection_value_heq compiledBase nativeDomain
    nativeBody (nativeArgument number) (nativeApplication number) position).trans
      (native_application_computes position.1 number)

/-- The second pullback is the actual compiler map. Its application
comparison retains the same genuinely dependent output at every source
component, including the component with the supplied returning execution. -/
theorem compiler_application_computes (position : sourcePrograms.Elements) (number : Nat) :
    HEq ((sourceApplication number).val position)
      (⟨number, Nat.lt_succ_self number⟩ : Fin (number + 1)) := by
  unfold sourceApplication sourceFunction
  change HEq ((appDisplayed
    (reindexFunction compilerMap (reindexDisplayed compiledBase nativeDomain)
      (reindexDisplayed (totalReindexMap compiledBase nativeDomain) nativeBody) compiledFunction)
    (reindexDisplayedSection compilerMap (reindexDisplayed compiledBase nativeDomain)
      (reindexDisplayedSection compiledBase nativeDomain (nativeArgument number)))).val position) _
  rw [app_substitution]
  exact (DisplayedPresheafCwf.reindexDependentSection_value_heq compilerMap
    (reindexDisplayed compiledBase nativeDomain)
    (reindexDisplayed (totalReindexMap compiledBase nativeDomain) nativeBody)
    (reindexDisplayedSection compiledBase nativeDomain (nativeArgument number))
    (compiledApplication number) position).trans
      (compiled_application_computes (compilerMap.mapElements.obj position) number)

/-- The exact generated receipt readout and the function transported by
the actual compiler compute the same supplied dependent value. -/
theorem certificate_and_function_agree (number : Nat) :
    HEq ((sourceApplication number).val
      NamePassingDependentRuntimeControls.startPoint)
      (((NamePassingGeneratedEvidence.compiledReadout models _).app
        (compilerMap.mapElements.obj NamePassingDependentRuntimeControls.startPoint)
          ((carry (NamePassingGeneratedEvidence.certificates _)).app
            NamePassingDependentRuntimeControls.startPoint (applicationTree number))).val
              nativePoint) := by
  rw [NamePassingGeneratedEvidenceControls.compiled_application_computes]
  exact compiler_application_computes _ number

/-- One supplied returning execution retains its generated certificate,
whose native value agrees with actual compiler pullback of the function.
The endpoint is the observed rho endpoint, not a reconstructed endpoint. -/
theorem returning_execution_with_transported_function (number : Nat) :
    ∃ final, ∃ actual : Mettapedia.GSLT.IndexedOperational.ExecutionPath
        RhoUnaryReadback.Target (NamePassingSpineControls.process
          NamePassingCompilerReadback.Controls.start) final,
      ∃ receipt : NamePassingGeneratedEvidence.GeneratedReceipt models
          NamePassingDependentRuntimeControls.startPoint (applicationTree number)
          (NamePassingSpineControls.world NamePassingCompilerReadback.Controls.names)
          (NamePassingSpineControls.code NamePassingCompilerReadback.Controls.start) actual,
        receipt.history.2 = applicationTree number ∧
          HEq ((sourceApplication number).val
            NamePassingDependentRuntimeControls.startPoint)
            (receipt.specification.val nativePoint) ∧
          (RhoUnaryInputObservation.targetPredicate
            (NamePassingSpineControls.world NamePassingCompilerReadback.Controls.names) .zero).1
              final := by
  obtain ⟨final, actual, receipt, tree, computes, observed⟩ :=
    returning_execution_with_generated_certificate number
  refine ⟨final, actual, receipt, tree, ?_, observed⟩
  rw [computes]
  exact compiler_application_computes _ number

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionControls
