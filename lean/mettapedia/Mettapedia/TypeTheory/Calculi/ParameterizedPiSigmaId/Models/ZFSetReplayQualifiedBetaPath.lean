import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayQualifiedBetaPath
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayNeutralCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayTypingCoherence

/-!
# Interpreting finite qualified beta paths

Each actual retained contraction is semantically sound on valid context
environments because result-formation qualification derives membership of
its computed argument in the retained lambda domain. Independent accepted
paths ending at a common neutral term then agree, even if their intermediate
certificates and lambda domains differ.

This is a theorem about supplied finite paths, not normalization or
unrestricted certificate independence for the whole checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))
variable (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)

include universes successorQualified model constantModel

/-- Every step's output is the existing certificate-instantiation result.
Interpretation of the original accepted source agrees with interpretation of
the retained neutral endpoint on valid environments. -/
theorem QualifiedBetaPath.values
    {context : Ctx Head n} {displayed sourceTerm terminalTerm : Tm Head n}
    {sourceCode terminalCode : Code Head NoConversion n}
    (contextCode : ContextCode Head NoConversion n)
    (path : StructuralTypingReplay.QualifiedBetaPath R successor contextCode displayed
      sourceTerm sourceCode terminalTerm terminalCode)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (accepted : check R noConversionCheck context sourceTerm displayed sourceCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (sourceMeaning : Meaning.{u} n)
    (atSource : assemble heads constants sourceCode sourceTerm displayed = some sourceMeaning) :
    ∃ terminalMeaning,
      assemble heads constants terminalCode terminalTerm displayed = some terminalMeaning ∧
      ∀ env, valid env → sourceMeaning.value env = terminalMeaning.value env := by
  induction path generalizing sourceMeaning with
  | terminal =>
      exact ⟨sourceMeaning, atSource, fun _ _ => rfl⟩
  | contraction qualified computed rest ih =>
      obtain ⟨resultCode, resultMeaning, atContraction, resultChecked, atResult, stepValues⟩ :=
        qualified_contractBeta heads constants R successor universes successorQualified model
          constantModel contextCode _ sourceMeaning contextChecked accepted qualified atContext atSource
      rw [computed] at atContraction
      cases Option.some.inj atContraction
      obtain ⟨terminalMeaning, atTerminal, restValues⟩ :=
        ih resultChecked resultMeaning atResult
      exact ⟨terminalMeaning, atTerminal,
        fun env admitted => (stepValues env admitted).trans (restValues env admitted)⟩

/-- Two independently accepted finite paths with the same raw neutral
endpoint have the same source value on valid environments. Their source
terms and intermediate typing trees may differ. Terminal comparison uses
the existing neutral-elimination coherence theorem, not an assumed global
normalization or semantic-typing principle. -/
theorem qualified_paths_common_terminal_values
    {context : Ctx Head n} {displayed leftTerm rightTerm terminalTerm : Tm Head n}
    {leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n}
    (contextCode : ContextCode Head NoConversion n)
    (leftPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode displayed
      leftTerm leftCode terminalTerm leftTerminal)
    (rightPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode displayed
      rightTerm rightCode terminalTerm rightTerminal)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context leftTerm displayed leftCode = true)
    (rightChecked : check R noConversionCheck context rightTerm displayed rightCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (left right : Meaning.{u} n)
    (atLeft : assemble heads constants leftCode leftTerm displayed = some left)
    (atRight : assemble heads constants rightCode rightTerm displayed = some right)
    (env : Environment.{u} n) (admitted : valid env) :
    left.value env = right.value env := by
  obtain ⟨leftEnd, atLeftEnd, leftValues⟩ :=
    QualifiedBetaPath.values heads constants R successor universes successorQualified
      model constantModel contextCode leftPath contextChecked leftChecked atContext left atLeft
  obtain ⟨rightEnd, atRightEnd, rightValues⟩ :=
    QualifiedBetaPath.values heads constants R successor universes successorQualified
      model constantModel contextCode rightPath contextChecked rightChecked atContext right atRight
  have leftEndChecked := leftPath.terminal_checked R leftChecked
  have rightEndChecked := rightPath.terminal_checked R rightChecked
  have leftEndNeutral := leftPath.terminal_neutral
  have sameEnd := assemble_neutralEliminations_coherent heads constants R leftTerminal
    leftEndChecked leftEndNeutral atLeftEnd rightEndChecked atRightEnd (EqualOrHeads.refl _)
  calc
    left.value env = leftEnd.value env := leftValues env admitted
    _ = rightEnd.value env := congrArg (fun meaning => meaning.value env) sameEnd
    _ = right.value env := (rightValues env admitted).symm

/-- Independently checked finite beta paths can be compared even when their
displayed types differ. Both paths must reach the same raw terminal term,
whose structural interpretation fixes its value independently of the two
retained terminal certificates. No equality of intermediate Pi-domains or
terminal certificate trees is assumed. -/
theorem qualified_paths_supported_terminal_values
    {context : Ctx Head n}
    {leftDisplayed rightDisplayed leftTerm rightTerm terminalTerm : Tm Head n}
    {leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n}
    (contextCode : ContextCode Head NoConversion n)
    (leftPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode
      leftDisplayed leftTerm leftCode terminalTerm leftTerminal)
    (rightPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode
      rightDisplayed rightTerm rightCode terminalTerm rightTerminal)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context leftTerm leftDisplayed leftCode = true)
    (rightChecked : check R noConversionCheck context rightTerm rightDisplayed rightCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (left right : Meaning.{u} n)
    (atLeft : assemble heads constants leftCode leftTerm leftDisplayed = some left)
    (atRight : assemble heads constants rightCode rightTerm rightDisplayed = some right)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminalTerm = true)
    (env : Environment.{u} n) (admitted : valid env) :
    left.value env = right.value env := by
  obtain ⟨leftEnd, atLeftEnd, leftValues⟩ :=
    QualifiedBetaPath.values heads constants R successor universes successorQualified
      model constantModel contextCode leftPath contextChecked leftChecked atContext left atLeft
  obtain ⟨rightEnd, atRightEnd, rightValues⟩ :=
    QualifiedBetaPath.values heads constants R successor universes successorQualified
      model constantModel contextCode rightPath contextChecked rightChecked atContext right atRight
  have terminalValues := assemble_supported_values heads constants terminalSupported
    atLeftEnd atRightEnd
  calc
    left.value env = leftEnd.value env := leftValues env admitted
    _ = rightEnd.value env := congrFun terminalValues env
    _ = right.value env := (rightValues env admitted).symm

/-- The two actual checked routes for one substitution image. The source
expressions, displayed types and retained certificates may differ; their
finite paths end at one supported raw expression. -/
structure QualifiedImagePaths
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (R : Rules Head) (successor : Head → Head)
    [DecidableEq Head]
    [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
    [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
    {m : Nat} (context : Ctx Head m) (contextCode : ContextCode Head NoConversion m)
    (leftMeaning rightMeaning : Meaning.{u} m) where
  leftDisplayed : Tm Head m
  rightDisplayed : Tm Head m
  leftTerm : Tm Head m
  rightTerm : Tm Head m
  terminalTerm : Tm Head m
  leftCode : Code Head NoConversion m
  rightCode : Code Head NoConversion m
  leftTerminal : Code Head NoConversion m
  rightTerminal : Code Head NoConversion m
  leftPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode
    leftDisplayed leftTerm leftCode terminalTerm leftTerminal
  rightPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode
    rightDisplayed rightTerm rightCode terminalTerm rightTerminal
  leftChecked : check R noConversionCheck context leftTerm leftDisplayed leftCode = true
  rightChecked : check R noConversionCheck context rightTerm rightDisplayed rightCode = true
  atLeft : assemble heads constants leftCode leftTerm leftDisplayed = some leftMeaning
  atRight : assemble heads constants rightCode rightTerm rightDisplayed = some rightMeaning
  terminalSupported : ZFSetTypeExpressionInterpretation.supported terminalTerm = true

/-- A supported dependent expression has equal values after two independently
checked families of computed images. Finite path evidence is required only
for the outer variables the expression actually uses; all other images may
remain unrelated. This combines checked computation with semantic
substitution, without asserting normalization of every accepted term. -/
theorem qualified_image_paths_supported_expression_values
    {m k : Nat} {context : Ctx Head m}
    (contextCode : ContextCode Head NoConversion m)
    {valid : Environment.{u} m → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (expression : Tm Head k)
    (expressionSupported : ZFSetTypeExpressionInterpretation.supported expression = true)
    (leftImages rightImages : Fin k → Meaning.{u} m)
    (paths : ∀ index, index ∈ expression.freeVariables →
      QualifiedImagePaths heads constants R successor context contextCode
        (leftImages index) (rightImages index))
    (env : Environment.{u} m) (admitted : valid env) :
    ZFSetTypeExpressionInterpretation.interpret heads constants expression expressionSupported
      (imageEnvironment leftImages env) =
    ZFSetTypeExpressionInterpretation.interpret heads constants expression expressionSupported
      (imageEnvironment rightImages env) := by
  apply interpret_imageEnvironment_eq_of_freeVariables heads constants expression
    expressionSupported leftImages rightImages env
  intro index relevant
  let receipt := paths index relevant
  exact qualified_paths_supported_terminal_values heads constants R successor
    universes successorQualified model constantModel contextCode
    receipt.leftPath receipt.rightPath contextChecked receipt.leftChecked
    receipt.rightChecked atContext (leftImages index) (rightImages index)
    receipt.atLeft receipt.atRight receipt.terminalSupported env admitted

/-- An accepted source family can be instantiated with arbitrary checked
computed arguments in two independently retained ways. The same raw
substitution is used, but its two image-certificate families need not agree.
Qualified paths are needed only at variables free in the source expression.
Both transported codes are replayed, and their assembled values agree on
valid target environments. This does not compare arbitrary certificates
chosen after the substitution. -/
theorem qualified_image_paths_checked_substituted_family_values
    {k m : Nat} {sourceContext : Ctx Head k} {targetContext : Ctx Head m}
    (targetCode : ContextCode Head NoConversion m)
    {valid : Environment.{u} m → Prop}
    (targetChecked : checkContext R noConversionCheck targetContext targetCode = true)
    (atTarget : assembleContext heads constants targetCode targetContext = some valid)
    {sourceTerm sourceType : Tm Head k} (sourceCode : Code Head NoConversion k)
    (sourceSupported : ZFSetTypeExpressionInterpretation.supported sourceTerm = true)
    (sourceChecked : check R noConversionCheck sourceContext sourceTerm sourceType
      sourceCode = true)
    (sourceMeaning : Meaning.{u} k)
    (atSource : assemble heads constants sourceCode sourceTerm sourceType =
      some sourceMeaning)
    (σ : Sub Head k m)
    (leftCodes rightCodes : Fin k → Code Head NoConversion m)
    (leftImages rightImages : Fin k → Meaning.{u} m)
    (leftImageChecks : ∀ index, check R noConversionCheck targetContext (σ index)
      (subst σ (sourceContext.lookup index)) (leftCodes index) = true)
    (rightImageChecks : ∀ index, check R noConversionCheck targetContext (σ index)
      (subst σ (sourceContext.lookup index)) (rightCodes index) = true)
    (atLeftImages : ∀ index, assemble heads constants (leftCodes index) (σ index)
      (subst σ (sourceContext.lookup index)) = some (leftImages index))
    (atRightImages : ∀ index, assemble heads constants (rightCodes index) (σ index)
      (subst σ (sourceContext.lookup index)) = some (rightImages index))
    (paths : ∀ index, index ∈ sourceTerm.freeVariables →
      QualifiedImagePaths heads constants R successor targetContext targetCode
        (leftImages index) (rightImages index)) :
    check R noConversionCheck targetContext (subst σ sourceTerm) (subst σ sourceType)
      (sourceCode.substitute noConversionRename noConversionSubstitute σ leftCodes
        sourceTerm sourceType) = true ∧
    check R noConversionCheck targetContext (subst σ sourceTerm) (subst σ sourceType)
      (sourceCode.substitute noConversionRename noConversionSubstitute σ rightCodes
        sourceTerm sourceType) = true ∧
    ∃ left right,
      assemble heads constants
        (sourceCode.substitute noConversionRename noConversionSubstitute σ leftCodes
          sourceTerm sourceType) (subst σ sourceTerm) (subst σ sourceType) = some left ∧
      assemble heads constants
        (sourceCode.substitute noConversionRename noConversionSubstitute σ rightCodes
          sourceTerm sourceType) (subst σ sourceTerm) (subst σ sourceType) = some right ∧
      (∀ env, left.value env =
        ZFSetTypeExpressionInterpretation.interpret heads constants sourceTerm
          sourceSupported (imageEnvironment leftImages env)) ∧
      (∀ env, right.value env =
        ZFSetTypeExpressionInterpretation.interpret heads constants sourceTerm
          sourceSupported (imageEnvironment rightImages env)) ∧
      ∀ env, valid env → left.value env = right.value env := by
  have leftChecked := check_substitute noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) sourceCode sourceChecked σ leftCodes
    leftImageChecks
  have rightChecked := check_substitute noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) sourceCode sourceChecked σ rightCodes
    rightImageChecks
  obtain ⟨left, atLeft, leftValues, _⟩ :=
    assemble_substitute noConversionRename noConversionSubstitute heads constants R
      noConversionCheck sourceCode sourceMeaning sourceChecked atSource σ leftCodes
      leftImages atLeftImages
  obtain ⟨right, atRight, rightValues, _⟩ :=
    assemble_substitute noConversionRename noConversionSubstitute heads constants R
      noConversionCheck sourceCode sourceMeaning sourceChecked atSource σ rightCodes
      rightImages atRightImages
  refine ⟨leftChecked, rightChecked, left, right, atLeft, atRight, ?_, ?_, ?_⟩
  · intro env
    rw [leftValues]
    exact agrees_with_type_expressions heads constants sourceCode sourceTerm sourceType
      sourceMeaning sourceSupported atSource _
  · intro env
    rw [rightValues]
    exact agrees_with_type_expressions heads constants sourceCode sourceTerm sourceType
      sourceMeaning sourceSupported atSource _
  · intro env admitted
    rw [leftValues, rightValues]
    calc
      sourceMeaning.value (imageEnvironment leftImages env) =
          ZFSetTypeExpressionInterpretation.interpret heads constants sourceTerm
            sourceSupported (imageEnvironment leftImages env) :=
        agrees_with_type_expressions heads constants sourceCode sourceTerm sourceType
          sourceMeaning sourceSupported atSource _
      _ = ZFSetTypeExpressionInterpretation.interpret heads constants sourceTerm
            sourceSupported (imageEnvironment rightImages env) :=
        qualified_image_paths_supported_expression_values heads constants R successor
          universes successorQualified model constantModel targetCode targetChecked
          atTarget sourceTerm sourceSupported leftImages rightImages paths env admitted
      _ = sourceMeaning.value (imageEnvironment rightImages env) :=
        (agrees_with_type_expressions heads constants sourceCode sourceTerm sourceType
          sourceMeaning sourceSupported atSource _).symm

/-- Two retained paths for one computed term produce an actual checked
dependent equality witness. Semantic membership of the computed value in its
domain remains an explicit premise; the paths establish only the equality
between the two interpretations. -/
theorem qualified_paths_dependent_equality_witness
    {context : Ctx Head n} (contextCode : ContextCode Head NoConversion n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (level joined : Head) (isUniverse : R.isUniverse level)
    (joinedUniverse : R.isUniverse joined) (atJoin : R.join level level joined)
    (A subject terminal : Tm Head n)
    (domain first second firstTerminal secondTerminal : Code Head NoConversion n)
    (domainChecked : check R noConversionCheck context A (.head level) domain = true)
    (firstChecked : check R noConversionCheck context subject A first = true)
    (secondChecked : check R noConversionCheck context subject A second = true)
    (firstPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode A
      subject first terminal firstTerminal)
    (secondPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode A
      subject second terminal secondTerminal)
    (d a b : Meaning.{u} n)
    (atDomain : assemble heads constants domain A (.head level) = some d)
    (atFirst : assemble heads constants first subject A = some a)
    (atSecond : assemble heads constants second subject A = some b) :
    (CoherenceWitness.code level joined A domain first second).resultFormation
      noConversionRename noConversionSubstitute successor contextCode
      (CoherenceWitness.term subject) (CoherenceWitness.type A subject) =
        some (joined, CoherenceWitness.formation level domain first second) ∧
    checkJudgment R noConversionCheck context (CoherenceWitness.term subject)
      (CoherenceWitness.type A subject) contextCode
      (CoherenceWitness.code level joined A domain first second) = true ∧
    ∃ witness formed,
      assemble heads constants (CoherenceWitness.code level joined A domain first second)
        (CoherenceWitness.term subject) (CoherenceWitness.type A subject) = some witness ∧
      assemble heads constants (CoherenceWitness.formation level domain first second)
        (CoherenceWitness.type A subject) (.head joined) = some formed ∧
      ∀ env, valid env → a.value env ∈ d.value env →
        witness.value env ∈ formed.value env := by
  have witnessChecked := CoherenceWitness.checked R context level joined A subject
    domain first second isUniverse joinedUniverse atJoin domainChecked firstChecked
    secondChecked
  let witness := CoherenceWitness.termMeaning a
  let formed := CoherenceWitness.typeMeaning d a b
  have atWitness := CoherenceWitness.term_assembles heads constants level joined A subject
    domain first second a atFirst
  have atFormed := CoherenceWitness.formation_assembles heads constants level A subject
    domain first second d a b atDomain atFirst atSecond joined
  refine ⟨CoherenceWitness.resultFormation_exact successor contextCode level joined A subject
    domain first second, ?_, witness, formed, atWitness, atFormed, ?_⟩
  · simp only [checkJudgment, contextChecked, witnessChecked, Bool.and_self]
  intro env admitted inside
  apply (CoherenceWitness.membership_iff d a b env).mpr
  exact ⟨inside, qualified_paths_common_terminal_values heads constants R successor
    universes successorQualified model constantModel contextCode firstPath secondPath
    contextChecked firstChecked secondChecked atContext a b atFirst atSecond env admitted⟩

#print axioms QualifiedBetaPath.values
#print axioms qualified_paths_common_terminal_values
#print axioms qualified_paths_supported_terminal_values
#print axioms qualified_image_paths_supported_expression_values
#print axioms qualified_image_paths_checked_substituted_family_values
#print axioms qualified_paths_dependent_equality_witness

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
