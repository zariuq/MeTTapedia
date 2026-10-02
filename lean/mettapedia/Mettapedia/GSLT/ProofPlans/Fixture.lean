import Mettapedia.GSLT.LanguageDef.CertificateGSLTInterpretation

/-!
# A proof-plan fixture calculus

The controls of the proof-plan modules run in one small validated proof
definition, the *kernel*, and in two method libraries over it.  Every judgment
is nullary, so each rule instance is its rule identifier.

| judgment | rules concluding it |
|---|---|
| `A` | `axA₁ : ⊢ A`, `axA₂ : ⊢ A` (two distinct derivations) |
| `B` | `ab : A ⊢ B`, `axB : ⊢ B` |
| `C` | `bc : B ⊢ C`, `xc : X ⊢ C` |
| `D` | `pair : A, A ⊢ D` |
| `E` | `both : A, B ⊢ E` |
| `L` | `loop : ⊢ L` |
| `W` | `weak : L ⊢ W` |
| `G` | `castCG : CastCG, C ⊢ G` |
| `CastAB` | `axCastAB : ⊢ CastAB` |
| `B` (again) | `castAB : CastAB, A ⊢ B` |
| `X`, `CastCG` | none |

The independent truth assignment `kernelTruth` makes `X`, `CastCG` and `G`
false and every other judgment true.  Every rule preserves it
(`kernelRules_preserve_truth`), so `X`, `CastCG` and `G` have no derivation
(`no_derivation_X`, `no_derivation_castCG`, `no_derivation_G`).

The method library has the macro rule `lib-ac : A ⊢ C` and its own axiom
`lib-axA : ⊢ A`; `elaborateLibrary` interprets them by the kernel
derivations `A ⊢ B ⊢ C` and `axA₁`.  The unsound library has the single rule
`lib-bogus : ⊢ G`, and admits no interpretation into the kernel
(`badLibrary_no_elaboration`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans.Fixture

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## Judgments -/

/-- A nullary judgment of the fixture. -/
def judgment (head : String) : Pattern := .apply head []

def A : Pattern := judgment "PP-A"
def B : Pattern := judgment "PP-B"
def C : Pattern := judgment "PP-C"
def D : Pattern := judgment "PP-D"
def E : Pattern := judgment "PP-E"
def X : Pattern := judgment "PP-X"
def L : Pattern := judgment "PP-L"
def W : Pattern := judgment "PP-W"
def G : Pattern := judgment "PP-G"
def CastCG : Pattern := judgment "PP-CastCG"
def CastAB : Pattern := judgment "PP-CastAB"

/-- A rule without metavariables or side conditions. -/
def groundRule (name : String) (premises : List Pattern) (conclusion : Pattern) :
    RuleSchema :=
  { id := ⟨name⟩
    metavariables := []
    premises := premises
    conclusion := conclusion
    sideConditions := [] }

/-! ## The kernel -/

def ruleAxA₁ : RuleSchema := groundRule "pp-axA1" [] A
def ruleAxA₂ : RuleSchema := groundRule "pp-axA2" [] A
def ruleAB : RuleSchema := groundRule "pp-ab" [A] B
def ruleAxB : RuleSchema := groundRule "pp-axB" [] B
def ruleBC : RuleSchema := groundRule "pp-bc" [B] C
def ruleXC : RuleSchema := groundRule "pp-xc" [X] C
def rulePair : RuleSchema := groundRule "pp-pair" [A, A] D
def ruleBoth : RuleSchema := groundRule "pp-both" [A, B] E
def ruleLoop : RuleSchema := groundRule "pp-loop" [] L
def ruleWeak : RuleSchema := groundRule "pp-weak" [L] W
def ruleCastCG : RuleSchema := groundRule "pp-castCG" [CastCG, C] G
def ruleCastAB : RuleSchema := groundRule "pp-castAB" [CastAB, A] B
def ruleAxCastAB : RuleSchema := groundRule "pp-axCastAB" [] CastAB

def kernelRules : List RuleSchema :=
  [ruleAxA₁, ruleAxA₂, ruleAB, ruleAxB, ruleBC, ruleXC, rulePair, ruleBoth,
    ruleLoop, ruleWeak, ruleCastCG, ruleCastAB, ruleAxCastAB]

def kernelJudgments : List JudgmentDecl :=
  [{ head := "PP-A", arity := 0 }, { head := "PP-B", arity := 0 },
    { head := "PP-C", arity := 0 }, { head := "PP-D", arity := 0 },
    { head := "PP-E", arity := 0 }, { head := "PP-X", arity := 0 },
    { head := "PP-L", arity := 0 }, { head := "PP-W", arity := 0 },
    { head := "PP-G", arity := 0 }, { head := "PP-CastCG", arity := 0 },
    { head := "PP-CastAB", arity := 0 }]

def kernelPresentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend (LanguageDef.empty "proof-plan-kernel")
    { judgments := kernelJudgments, rules := kernelRules }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

theorem kernelPresentation_valid : kernelPresentation.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [kernelPresentation, emptyLanguage_validate, kernelRules, kernelJudgments,
    ruleAxA₁, ruleAxA₂, ruleAB, ruleAxB, ruleBC, ruleXC, rulePair, ruleBoth,
    ruleLoop, ruleWeak, ruleCastCG, ruleCastAB, ruleAxCastAB, groundRule,
    A, B, C, D, E, X, L, W, G, CastCG, CastAB, judgment,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

/-- The validated kernel definition. -/
def kernelDefinition : ValidatedCalculusLanguageDef :=
  ⟨kernelPresentation, kernelPresentation_valid⟩

/-- The kernel as a proof-definition object. -/
abbrev kernel : Object := ⟨kernelDefinition⟩

/-! ## Rule instances and applications -/

/-- The unique instance of a ground rule. -/
def ruleInstance (rule : RuleSchema) : RuleInstance := ⟨rule.id, []⟩

/-- Every kernel rule instantiates to its own premises and conclusion. -/
theorem instantiate_kernel {rule : RuleSchema} (member : rule ∈ kernelRules) :
    instantiateRule? kernelDefinition (ruleInstance rule) =
      some (rule.premises, rule.conclusion) := by
  simp only [kernelRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp [instantiateRule?, kernelDefinition, kernelPresentation, kernelRules,
      ruleAxA₁, ruleAxA₂, ruleAB, ruleAxB, ruleBC, ruleXC, rulePair, ruleBoth,
      ruleLoop, ruleWeak, ruleCastCG, ruleCastAB, ruleAxCastAB, groundRule,
      ruleInstance, CalculusLanguageDef.lookupRule?, argumentsValidAt,
      RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, judgment,
      A, B, C, D, E, X, L, W, G, CastCG, CastAB]

/-- The typed application of a kernel rule. -/
theorem kernelApp {rule : RuleSchema} (member : rule ∈ kernelRules) :
    RuleApplication kernelDefinition (ruleInstance rule) rule.premises
      rule.conclusion :=
  instantiateRule?_eq_some_iff_application.mp (instantiate_kernel member)

/-- The premise/conclusion shapes of the kernel rules. -/
def kernelShapes : List (List Pattern × Pattern) :=
  kernelRules.map fun rule => (rule.premises, rule.conclusion)

/-- **Inversion.**  Every kernel rule application has the shape of a kernel
rule. -/
theorem kernel_application_shape {instance' : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication kernelDefinition instance' premises conclusion) :
    (premises, conclusion) ∈ kernelShapes := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  simp only [instantiateRule?] at executable
  cases lookup : kernelDefinition.1.lookupRule? instance'.ruleId with
  | none => simp [lookup] at executable
  | some rule =>
      simp only [lookup] at executable
      have member : rule ∈ kernelRules := by
        have found := List.mem_of_find?_eq_some lookup
        simpa [kernelDefinition, kernelPresentation] using found
      simp only [kernelRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;>
        simp [ruleAxA₁, ruleAxA₂, ruleAB, ruleAxB, ruleBC, ruleXC, rulePair,
          ruleBoth, ruleLoop, ruleWeak, ruleCastCG, ruleCastAB, ruleAxCastAB,
          groundRule, RuleSchema.sideConditionsHold, instantiateSchemas?,
          instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
          judgment, A, B, C, D, E, X, L, W, G, CastCG, CastAB] at executable <;>
        obtain ⟨-, rfl, rfl⟩ := executable <;>
        simp [kernelShapes, kernelRules, ruleAxA₁, ruleAxA₂, ruleAB, ruleAxB,
          ruleBC, ruleXC, rulePair, ruleBoth, ruleLoop, ruleWeak, ruleCastCG,
          ruleCastAB, ruleAxCastAB, groundRule, judgment,
          A, B, C, D, E, X, L, W, G, CastCG, CastAB]

/-! ## The independent truth assignment -/

/-- `X`, `CastCG` and `G` are false; every other judgment is true. -/
def kernelTruth (judgment : Pattern) : Prop :=
  judgment ≠ X ∧ judgment ≠ CastCG ∧ judgment ≠ G

instance (judgment : Pattern) : Decidable (kernelTruth judgment) := by
  unfold kernelTruth
  infer_instance

/-- Every kernel rule shape preserves the truth assignment. -/
theorem kernelShapes_sound :
    ∀ shape ∈ kernelShapes, (∀ premise ∈ shape.1, kernelTruth premise) →
      kernelTruth shape.2 := by
  decide

/-- **Every kernel rule preserves the truth assignment.** -/
theorem kernelRules_preserve_truth :
    ∀ (instance' : RuleInstance) (premises : List Pattern) (conclusion : Pattern),
      RuleApplication kernelDefinition instance' premises conclusion →
        (∀ premise ∈ premises, kernelTruth premise) → kernelTruth conclusion :=
  fun _ _ _ application => kernelShapes_sound _ (kernel_application_shape application)

/-- Every derivable kernel judgment is true. -/
theorem derivation_truth {goal : Pattern} (derivation : Derivation kernelDefinition goal) :
    kernelTruth goal :=
  Derivation.sound_of_ruleApplications kernelTruth kernelRules_preserve_truth derivation

theorem no_derivation_X : Derivation kernelDefinition X → False :=
  fun derivation => (derivation_truth derivation).1 rfl

theorem no_derivation_castCG : Derivation kernelDefinition CastCG → False :=
  fun derivation => (derivation_truth derivation).2.1 rfl

theorem no_derivation_G : Derivation kernelDefinition G → False :=
  fun derivation => (derivation_truth derivation).2.2 rfl

/-! ## Derivations -/

/-- The first axiom for `A`. -/
def dA₁ : Derivation kernelDefinition A :=
  .byRule _ (kernelApp (rule := ruleAxA₁) (by simp [kernelRules])) .nil

/-- The second axiom for `A`. -/
def dA₂ : Derivation kernelDefinition A :=
  .byRule _ (kernelApp (rule := ruleAxA₂) (by simp [kernelRules])) .nil

/-- The axiom for `B`. -/
def dB : Derivation kernelDefinition B :=
  .byRule _ (kernelApp (rule := ruleAxB) (by simp [kernelRules])) .nil

/-- `B` from the first axiom for `A`. -/
def dBA₁ : Derivation kernelDefinition B :=
  .byRule _ (kernelApp (rule := ruleAB) (by simp [kernelRules])) (.cons dA₁ .nil)

/-- `B` from the second axiom for `A`. -/
def dBA₂ : Derivation kernelDefinition B :=
  .byRule _ (kernelApp (rule := ruleAB) (by simp [kernelRules])) (.cons dA₂ .nil)

/-- `C` through `A ⊢ B ⊢ C`. -/
def dC : Derivation kernelDefinition C :=
  .byRule _ (kernelApp (rule := ruleBC) (by simp [kernelRules])) (.cons dBA₁ .nil)

/-- The axiom `⊢ L`. -/
def dL : Derivation kernelDefinition L :=
  .byRule _ (kernelApp (rule := ruleLoop) (by simp [kernelRules])) .nil

/-- The axiom `⊢ CastAB`. -/
def dCastAB : Derivation kernelDefinition CastAB :=
  .byRule _ (kernelApp (rule := ruleAxCastAB) (by simp [kernelRules])) .nil

/-! ## Plans

A plan is an open derivation; its ordered context lists the obligations. -/

/-- `ab(?A)`. -/
def planAB : OpenDerivation kernelDefinition [A] B :=
  .byRule _ (kernelApp (rule := ruleAB) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) .nil)

/-- `bc(ab(?A))`. -/
def planC : OpenDerivation kernelDefinition [A] C :=
  .byRule _ (kernelApp (rule := ruleBC) (by simp [kernelRules])) (.cons planAB .nil)

/-- `bc(?B)`: the method slot left by generalizing `planC`'s instances. -/
def planBC : OpenDerivation kernelDefinition [B] C :=
  .byRule _ (kernelApp (rule := ruleBC) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) .nil)

/-- `xc(?X)`: a plan for the derivable goal `C` whose obligation is false. -/
def planXC : OpenDerivation kernelDefinition [X] C :=
  .byRule _ (kernelApp (rule := ruleXC) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) .nil)

/-- `pair(?A₀, ?A₁)`: two distinct obligation occurrences of `A`. -/
def planPair : OpenDerivation kernelDefinition [A, A] D :=
  .byRule _ (kernelApp (rule := rulePair) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) (.cons (.assumption ⟨1, by simp⟩) .nil))

/-- `pair(?A, ?A)`: one obligation cited twice. -/
def planPairShared : OpenDerivation kernelDefinition [A] D :=
  .byRule _ (kernelApp (rule := rulePair) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) (.cons (.assumption ⟨0, by simp⟩) .nil))

/-- `both(?A, ab(axA₁))`: an obligation next to a determined sub-derivation. -/
def planBoth : OpenDerivation kernelDefinition [A] E :=
  .byRule _ (kernelApp (rule := ruleBoth) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) (.cons (OpenDerivation.ofClosed dBA₁) .nil))

/-- `weak(?L)`. -/
def planWeak : OpenDerivation kernelDefinition [L] W :=
  .byRule _ (kernelApp (rule := ruleWeak) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) .nil)

/-- The bypass of the established `C` towards the target `G`: a cast whose
obligation is `CastCG`. -/
def planBypass : OpenDerivation kernelDefinition [CastCG] G :=
  .byRule _ (kernelApp (rule := ruleCastCG) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) (.cons (OpenDerivation.ofClosed dC) .nil))

/-- A cast from `A` to `B` whose obligation `CastAB` is dischargeable. -/
def planCastAB : OpenDerivation kernelDefinition [CastAB] B :=
  .byRule _ (kernelApp (rule := ruleCastAB) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by simp⟩) (.cons (OpenDerivation.ofClosed dA₁) .nil))

/-! ## A method library and its elaboration into the kernel -/

/-- The macro rule `lib-ac : A ⊢ C`, a method schema. -/
def ruleLibAC : RuleSchema := groundRule "lib-ac" [A] C

/-- The library's own axiom `lib-axA : ⊢ A`. -/
def ruleLibAxA : RuleSchema := groundRule "lib-axA" [] A

def libraryRules : List RuleSchema := [ruleLibAC, ruleLibAxA]

def libraryPresentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend (LanguageDef.empty "proof-plan-library")
    { judgments := [{ head := "PP-A", arity := 0 }, { head := "PP-C", arity := 0 }]
      rules := libraryRules }

theorem libraryPresentation_valid : libraryPresentation.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [libraryPresentation, emptyLanguage_validate, libraryRules, ruleLibAC,
    ruleLibAxA, groundRule, A, C, judgment,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

def libraryDefinition : ValidatedCalculusLanguageDef :=
  ⟨libraryPresentation, libraryPresentation_valid⟩

/-- The method library as a proof-definition object. -/
abbrev library : Object := ⟨libraryDefinition⟩

theorem instantiate_library {rule : RuleSchema} (member : rule ∈ libraryRules) :
    instantiateRule? libraryDefinition (ruleInstance rule) =
      some (rule.premises, rule.conclusion) := by
  simp only [libraryRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [instantiateRule?, libraryDefinition, libraryPresentation, libraryRules,
      ruleLibAC, ruleLibAxA, groundRule, ruleInstance,
      CalculusLanguageDef.lookupRule?, argumentsValidAt,
      RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, judgment, A, C]

theorem libraryApp {rule : RuleSchema} (member : rule ∈ libraryRules) :
    RuleApplication libraryDefinition (ruleInstance rule) rule.premises
      rule.conclusion :=
  instantiateRule?_eq_some_iff_application.mp (instantiate_library member)

/-- Inversion for the library: its applications are `A ⊢ C` and `⊢ A`. -/
theorem library_application_shape {instance' : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication libraryDefinition instance' premises conclusion) :
    (premises = [A] ∧ conclusion = C) ∨ (premises = [] ∧ conclusion = A) := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  simp only [instantiateRule?] at executable
  cases lookup : libraryDefinition.1.lookupRule? instance'.ruleId with
  | none => simp [lookup] at executable
  | some rule =>
      simp only [lookup] at executable
      have member : rule ∈ libraryRules := by
        have found := List.mem_of_find?_eq_some lookup
        simpa [libraryDefinition, libraryPresentation] using found
      simp only [libraryRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [ruleLibAC, ruleLibAxA, groundRule, RuleSchema.sideConditionsHold,
          instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
          instantiateSchemaAt?, judgment, A, C] at executable <;>
        obtain ⟨-, rfl, rfl⟩ := executable
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩

/-- **The elaborator of the method library.**  The macro rule `A ⊢ C` is
implemented by the kernel plan `bc(ab(?A))`, and the library axiom by the
kernel axiom `axA₁`. -/
def elaborateLibrary : Interpretation library kernel where
  onRule := fun _ {premises} {conclusion} application =>
    if shapeAC : premises = [A] ∧ conclusion = C then by
      rw [shapeAC.1, shapeAC.2]
      exact planC
    else if shapeA : premises = [] ∧ conclusion = A then by
      rw [shapeA.1, shapeA.2]
      exact OpenDerivation.ofClosed dA₁
    else
      False.elim (by
        rcases library_application_shape application with shape | shape
        · exact shapeAC shape
        · exact shapeA shape)

/-- The library plan `lib-ac(?A)`. -/
def libraryPlan : OpenDerivation libraryDefinition [A] C :=
  .byRule _ (libraryApp (rule := ruleLibAC) (by simp [libraryRules]))
    (.cons (.assumption ⟨0, by simp⟩) .nil)

/-- The library derivation of `A`. -/
def libraryA : Derivation libraryDefinition A :=
  .byRule _ (libraryApp (rule := ruleLibAxA) (by simp [libraryRules])) .nil

/-! ## An unsound method library -/

/-- The unsound schema `lib-bogus : ⊢ G`. -/
def ruleBogus : RuleSchema := groundRule "lib-bogus" [] G

def badPresentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend (LanguageDef.empty "proof-plan-bad-library")
    { judgments := [{ head := "PP-G", arity := 0 }], rules := [ruleBogus] }

theorem badPresentation_valid : badPresentation.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [badPresentation, emptyLanguage_validate, ruleBogus, groundRule, G,
    judgment, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

def badDefinition : ValidatedCalculusLanguageDef :=
  ⟨badPresentation, badPresentation_valid⟩

/-- The library with the unsound schema. -/
abbrev badLibrary : Object := ⟨badDefinition⟩

theorem badApp : RuleApplication badDefinition (ruleInstance ruleBogus) [] G :=
  instantiateRule?_eq_some_iff_application.mp (by
    simp [instantiateRule?, badDefinition, badPresentation, ruleBogus, groundRule,
      ruleInstance, CalculusLanguageDef.lookupRule?, argumentsValidAt,
      RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, judgment, G])

/-- **An unsound method schema admits no elaboration.**  Any interpretation of
`⊢ G` into the kernel would be a kernel derivation of the false judgment
`G`. -/
theorem badLibrary_no_elaboration : IsEmpty (Interpretation badLibrary kernel) :=
  ⟨fun elaborator =>
    no_derivation_G (elaborator.onRule (ruleInstance ruleBogus) badApp).close⟩

/-! ## A calculus of equal and different bits

`Same(x, y)` is derivable exactly when `x = y`, and `Diff(x, y)` exactly when
`x ≠ y`.  The composition controls use it for plans whose obligations mention
shared role fillers. -/

/-- The bit constructors of the two-bit calculus. -/
def bit (value : Bool) : Pattern := .apply (if value then "sd-t" else "sd-f") []

/-- `Same(x, y)`. -/
def same (x y : Bool) : Pattern := .apply "SD-Same" [bit x, bit y]

/-- `Diff(x, y)`. -/
def diff (x y : Bool) : Pattern := .apply "SD-Diff" [bit x, bit y]

private def bitConstructor (label : String) : GrammarRule :=
  { label := label, category := "SDBit", params := [], syntaxPattern := [] }

def sameTT : RuleSchema := groundRule "sd-same-tt" [] (same true true)
def sameFF : RuleSchema := groundRule "sd-same-ff" [] (same false false)
def diffTF : RuleSchema := groundRule "sd-diff-tf" [] (diff true false)
def diffFT : RuleSchema := groundRule "sd-diff-ft" [] (diff false true)

def sameDiffRules : List RuleSchema := [sameTT, sameFF, diffTF, diffFT]

private def sameDiffLanguage : LanguageDef :=
  { name := "same-diff"
    types := [TypeDecl.plain "SDBit"]
    terms := [bitConstructor "sd-t", bitConstructor "sd-f"]
    equations := []
    rewrites := [] }

def sameDiffPresentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend sameDiffLanguage
    { judgments := [{ head := "SD-Same", arity := 2 }, { head := "SD-Diff", arity := 2 }]
      rules := sameDiffRules }

private theorem sameDiff_validate : sameDiffPresentation.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [sameDiffPresentation, sameDiffLanguage, bitConstructor,
      LanguageDef.typeNames, TermParam.typeExpr, TypeDecl.plain]

theorem sameDiffPresentation_valid : sameDiffPresentation.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [sameDiff_validate]
  simp [sameDiffPresentation, sameDiffLanguage, bitConstructor, sameDiffRules,
    sameTT, sameFF, diffTF, diffFT, groundRule, same, diff, bit,
    TypeDecl.plain, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    fixedConstructorsValid, languageHasConstructorArity,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

def sameDiffDefinition : ValidatedCalculusLanguageDef :=
  ⟨sameDiffPresentation, sameDiffPresentation_valid⟩

/-- The two-bit calculus as a proof-definition object. -/
abbrev sameDiff : Object := ⟨sameDiffDefinition⟩

theorem instantiate_sameDiff {rule : RuleSchema} (member : rule ∈ sameDiffRules) :
    instantiateRule? sameDiffDefinition (ruleInstance rule) =
      some (rule.premises, rule.conclusion) := by
  simp only [sameDiffRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [instantiateRule?, sameDiffDefinition, sameDiffPresentation, sameDiffRules,
      sameTT, sameFF, diffTF, diffFT, groundRule, ruleInstance,
      CalculusLanguageDef.lookupRule?, argumentsValidAt,
      RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, same, diff, bit]

theorem sameDiffApp {rule : RuleSchema} (member : rule ∈ sameDiffRules) :
    RuleApplication sameDiffDefinition (ruleInstance rule) rule.premises
      rule.conclusion :=
  instantiateRule?_eq_some_iff_application.mp (instantiate_sameDiff member)

/-- The four derivable judgments. -/
def sameDiffTrue : List Pattern :=
  [same true true, same false false, diff true false, diff false true]

theorem sameDiff_application_shape {instance' : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication sameDiffDefinition instance' premises conclusion) :
    premises = [] ∧ conclusion ∈ sameDiffTrue := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  simp only [instantiateRule?] at executable
  cases lookup : sameDiffDefinition.1.lookupRule? instance'.ruleId with
  | none => simp [lookup] at executable
  | some rule =>
      simp only [lookup] at executable
      have member : rule ∈ sameDiffRules := by
        have found := List.mem_of_find?_eq_some lookup
        simpa [sameDiffDefinition, sameDiffPresentation] using found
      simp only [sameDiffRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        simp [sameTT, sameFF, diffTF, diffFT, groundRule,
          RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
          instantiateSchemasAt?, instantiateSchemaAt?, same, diff, bit] at executable <;>
        obtain ⟨-, rfl, rfl⟩ := executable <;>
        simp [sameDiffTrue, same, diff, bit]

/-- Every derivable judgment of the two-bit calculus is one of the four. -/
theorem sameDiff_derivation_mem {goal : Pattern}
    (derivation : Derivation sameDiffDefinition goal) : goal ∈ sameDiffTrue :=
  Derivation.sound_of_ruleApplications (fun judgment => judgment ∈ sameDiffTrue)
    (fun _ _ _ application _ => (sameDiff_application_shape application).2) derivation

/-- The derivation of `Same(x, x)`. -/
def sameDerivation : (x : Bool) → Derivation sameDiffDefinition (same x x)
  | true => .byRule _ (sameDiffApp (rule := sameTT) (by simp [sameDiffRules])) .nil
  | false => .byRule _ (sameDiffApp (rule := sameFF) (by simp [sameDiffRules])) .nil

/-- The derivation of `Diff(x, !x)`. -/
def diffDerivation : (x : Bool) → Derivation sameDiffDefinition (diff x (!x))
  | true => .byRule _ (sameDiffApp (rule := diffTF) (by simp [sameDiffRules])) .nil
  | false => .byRule _ (sameDiffApp (rule := diffFT) (by simp [sameDiffRules])) .nil

/-- **`Same(x, y)` is derivable exactly when `x = y`.** -/
theorem same_derivable_iff (x y : Bool) :
    Nonempty (Derivation sameDiffDefinition (same x y)) ↔ x = y := by
  constructor
  · rintro ⟨derivation⟩
    have member := sameDiff_derivation_mem derivation
    cases x <;> cases y <;> simp_all [sameDiffTrue, same, diff, bit]
  · rintro rfl
    exact ⟨sameDerivation x⟩

/-- **`Diff(x, y)` is derivable exactly when `x ≠ y`.** -/
theorem diff_derivable_iff (x y : Bool) :
    Nonempty (Derivation sameDiffDefinition (diff x y)) ↔ x ≠ y := by
  constructor
  · rintro ⟨derivation⟩
    have member := sameDiff_derivation_mem derivation
    cases x <;> cases y <;> simp_all [sameDiffTrue, same, diff, bit]
  · intro different
    have equation : y = !x := by cases x <;> cases y <;> simp_all
    subst equation
    exact ⟨diffDerivation x⟩

/-- Every application of the two-bit calculus is the unique instance of one of
its rules. -/
theorem sameDiff_instance_of_application {instance' : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication sameDiffDefinition instance' premises conclusion) :
    ∃ rule ∈ sameDiffRules, instance' = ruleInstance rule ∧ conclusion = rule.conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  simp only [instantiateRule?] at executable
  cases lookup : sameDiffDefinition.1.lookupRule? instance'.ruleId with
  | none => simp [lookup] at executable
  | some rule =>
      simp only [lookup] at executable
      have found := List.find?_some lookup
      have sameId : rule.id = instance'.ruleId := of_decide_eq_true found
      have member : rule ∈ sameDiffRules := by
        have inList := List.mem_of_find?_eq_some lookup
        simpa [sameDiffDefinition, sameDiffPresentation] using inList
      refine ⟨rule, member, ?_⟩
      simp only [sameDiffRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases instance' with ⟨ruleId, arguments⟩
      simp only at sameId
      subst sameId
      rcases member with rfl | rfl | rfl | rfl <;>
        simp [sameTT, sameFF, diffTF, diffFT, groundRule,
          RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
          instantiateSchemasAt?, instantiateSchemaAt?, same, diff, bit] at executable <;>
        (cases arguments with
          | nil =>
              obtain ⟨-, -, rfl⟩ := executable
              exact ⟨rfl, rfl⟩
          | cons _ _ => simp [argumentsValidAt] at executable)

/-- **Derivations of the two-bit calculus are unique.** -/
theorem sameDiff_derivation_unique {goal : Pattern}
    (first second : Derivation sameDiffDefinition goal) : first = second := by
  cases first with
  | byRule instance₁ application₁ children₁ =>
      cases second with
      | byRule instance₂ application₂ children₂ =>
          obtain ⟨noPremises₁, -⟩ := sameDiff_application_shape application₁
          obtain ⟨noPremises₂, -⟩ := sameDiff_application_shape application₂
          subst noPremises₁
          subst noPremises₂
          cases children₁
          cases children₂
          obtain ⟨rule₁, member₁, rfl, conclusion₁⟩ :=
            sameDiff_instance_of_application application₁
          obtain ⟨rule₂, member₂, rfl, conclusion₂⟩ :=
            sameDiff_instance_of_application application₂
          have sameRule : rule₁ = rule₂ := by
            rw [conclusion₁] at conclusion₂
            simp only [sameDiffRules, List.mem_cons, List.not_mem_nil, or_false] at member₁ member₂
            rcases member₁ with rfl | rfl | rfl | rfl <;>
              rcases member₂ with rfl | rfl | rfl | rfl <;>
              first
                | rfl
                | simp [sameTT, sameFF, diffTF, diffFT, groundRule, same, diff, bit] at conclusion₂
          subst sameRule
          rfl

end Mettapedia.GSLT.ProofPlans.Fixture
