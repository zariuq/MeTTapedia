import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveMILArgumentRecovery

/-!
# Native hypothesis computation preserves arbitrary admitted typings

Declaration-spine inversion recovers typed instances of the actual primitive
and chain schemas. Their independently checked reducts then replay the
source derivation's displayed-type adjustments. This discharges primitive
typing preservation for the native iota package under Pi conversion
qualification; contextual preservation additionally uses Sigma qualification.

The conversion boundaries remain explicit parameters in this module.
`FormationSensitiveMILQualification` independently discharges them for the
actual combined beta/iota package. Neither confluence nor normalization is
inferred from the typing result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveMILIotaPreservation

open Presentation Presentation.Declaration IntrinsicMILHypothesis
open FormationSensitiveMIL (Typing)
open FormationSensitiveMILArgumentRecovery

variable {n : Nat}

def primitiveSchemaSubstitution
    (sorts primitives motive primitiveCase chainCase source target symbol : Tower.Tm n) :
    Sub Tower.Head 8 n :=
  consSub symbol (consSub target (consSub source
    (parameterSubstitution sorts primitives motive primitiveCase chainCase)))

theorem primitiveSchema_typed {context : Tower.Ctx n}
    {sorts primitives motive primitiveCase chainCase source target symbol : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor rules contextSPMPrimitiveChain context
      (parameterSubstitution sorts primitives motive primitiveCase chainCase))
    (sourceTyped : Typing context source sorts) (targetTyped : Typing context target sorts)
    (symbolTyped : Typing context symbol (.app (.app primitives source) target)) :
    FormationSensitive.CtxMor rules contextSPMPCSourceTargetSymbol context
      (primitiveSchemaSubstitution sorts primitives motive primitiveCase chainCase source target symbol) := by
  have first : FormationSensitive.CtxMor rules contextSPMPCSource context
      (consSub source (parameterSubstitution sorts primitives motive primitiveCase chainCase)) :=
    parameters.extend sourceTyped
  have second : FormationSensitive.CtxMor rules contextSPMPCSourceTarget context
      (consSub target (consSub source
        (parameterSubstitution sorts primitives motive primitiveCase chainCase))) :=
    first.extend targetTyped
  exact second.extend symbolTyped

def chainSchemaSubstitution
    (sorts primitives motive primitiveCase chainCase source middle target earlier later : Tower.Tm n) :
    Sub Tower.Head 10 n :=
  consSub later (consSub earlier (consSub target (consSub middle (consSub source
    (parameterSubstitution sorts primitives motive primitiveCase chainCase)))))

theorem chainSchema_typed {context : Tower.Ctx n}
    {sorts primitives motive primitiveCase chainCase source middle target earlier later : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor rules contextSPMPrimitiveChain context
      (parameterSubstitution sorts primitives motive primitiveCase chainCase))
    (sourceTyped : Typing context source sorts) (middleTyped : Typing context middle sorts)
    (targetTyped : Typing context target sorts)
    (earlierTyped : Typing context earlier (hypothesisApp sorts primitives source middle))
    (laterTyped : Typing context later (hypothesisApp sorts primitives middle target)) :
    FormationSensitive.CtxMor rules contextSPMPCChainSourceMiddleTargetEarlierLater context
      (chainSchemaSubstitution sorts primitives motive primitiveCase chainCase
        source middle target earlier later) := by
  have first : FormationSensitive.CtxMor rules contextSPMPCChainSource context
      (consSub source (parameterSubstitution sorts primitives motive primitiveCase chainCase)) :=
    parameters.extend sourceTyped
  have second : FormationSensitive.CtxMor rules contextSPMPCChainSourceMiddle context
      (consSub middle (consSub source
        (parameterSubstitution sorts primitives motive primitiveCase chainCase))) :=
    first.extend middleTyped
  have third : FormationSensitive.CtxMor rules contextSPMPCChainSourceMiddleTarget context
      (consSub target (consSub middle (consSub source
        (parameterSubstitution sorts primitives motive primitiveCase chainCase)))) :=
    second.extend targetTyped
  have fourth : FormationSensitive.CtxMor rules contextSPMPCChainSourceMiddleTargetEarlier context
      (consSub earlier (consSub target (consSub middle (consSub source
        (parameterSubstitution sorts primitives motive primitiveCase chainCase))))) :=
    third.extend earlierTyped
  exact fourth.extend laterTyped

/-- Arbitrary refined primitive-redex typing determines a typed canonical
substitution; the reducer need not have received a quoted canonical input. -/
theorem primitive_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : FormationSensitive.ContextFormation rules context)
    {sorts primitives motive primitiveCase chainCase source target symbol displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp sorts primitives motive primitiveCase chainCase source target
        (primitiveApp sorts primitives source target symbol)) displayed) :
    Typing context (.app (.app (.app primitiveCase source) target) symbol) displayed := by
  obtain ⟨parameters, sourceTyped, targetTyped, hypothesisTyped, replay⟩ :=
    eliminateArguments boundary formed observed
  have symbolTyped := primitiveArgument boundary formed hypothesisTyped
  have typed := primitiveSchema_typed parameters sourceTyped targetTyped symbolTyped
  have reduct := (FormationSensitiveMILElimination.primitiveIota_substitute formed typed).2
  exact replay reduct.typing

/-- The chain redex retains both recursive calls and both constituent
receipts at the exact motive. All source type adjustments are replayed. -/
theorem chain_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : FormationSensitive.ContextFormation rules context)
    {sorts primitives motive primitiveCase chainCase source middle target earlier later displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp sorts primitives motive primitiveCase chainCase source target
        (chainApp sorts primitives source middle target earlier later)) displayed) :
    Typing context
      (.app (.app (.app (.app (.app (.app (.app chainCase source) middle) target) earlier) later)
        (eliminateApp sorts primitives motive primitiveCase chainCase source middle earlier))
        (eliminateApp sorts primitives motive primitiveCase chainCase middle target later)) displayed := by
  obtain ⟨parameters, sourceTyped, targetTyped, hypothesisTyped, replay⟩ :=
    eliminateArguments boundary formed observed
  obtain ⟨middleTyped, earlierTyped, laterTyped⟩ := chainArguments boundary formed hypothesisTyped
  have typed := chainSchema_typed parameters sourceTyped middleTyped targetTyped earlierTyped laterTyped
  have reduct := (FormationSensitiveMILElimination.chainIota_substitute formed typed).2
  exact replay reduct.typing

theorem iota_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : FormationSensitive.ContextFormation rules context)
    {source target displayed : Tower.Tm n} (evidence : IotaEvidence n source target)
    (observed : Typing context source displayed) : Typing context target displayed := by
  cases evidence with
  | primitive => exact primitive_preserves boundary formed observed
  | chain => exact chain_preserves boundary formed observed

/-- Every actual declared root is an iota rule: inherited roots are empty
and the four existing declarations are opaque. No root typing premise is
assumed in this instance. -/
theorem rootPreservation (boundary : PiConversionBoundary rules) :
    FormationSensitive.RootPreservation rules := by
  intro n context source target displayed formed observed root
  cases root with
  | inherited impossible => exact impossible.elim
  | delta lookup =>
      rw [rawSignature_valueOf_none] at lookup
      cases lookup
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      exact iota_preserves boundary formed evidence observed

/-- Arbitrary contextual finite runs of the native hypothesis package
preserve refined judgments once its conversion boundaries are qualified. -/
theorem steps_preserve (piBoundary : PiConversionBoundary rules)
    (sigmaBoundary : SigmaConversionBoundary rules)
    {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment rules context source displayed)
    (steps : ConversionCoherence.StepStar rules source target) :
    FormationSensitive.Judgment rules context target displayed :=
  judgment.steps_preserve universes piBoundary sigmaBoundary
    (FormationSensitive.towerHeadPreservation.includeSignature rawSignature)
    (rootPreservation piBoundary) steps

#print axioms primitiveSchema_typed
#print axioms chainSchema_typed
#print axioms primitive_preserves
#print axioms chain_preserves
#print axioms iota_preserves
#print axioms rootPreservation
#print axioms steps_preserve

end FormationSensitiveMILIotaPreservation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
