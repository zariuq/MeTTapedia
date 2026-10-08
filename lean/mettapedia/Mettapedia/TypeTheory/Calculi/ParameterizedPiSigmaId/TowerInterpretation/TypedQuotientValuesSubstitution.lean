import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.TypedQuotientValues
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotientSubstitution

/-!
# Admitted substitution of typed quotient values

The typed classes are substituted by the actual formation-sensitive
contextual arrow. Independently admitted annotated components evaluate to
the satisfying-environment map. The model value commutes with these two
actions by the earned simultaneous evaluator substitution theorem.

This comparison retains the supplied annotation telescopes and component
erasures. It does not assume that every arbitrary model admits every source
substitution, or identify a set model with a native presheaf model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace TypedQuotientValues

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization
open Presentation.FormationSensitiveContextual
open CategoryTheory
open UniverseLevel (LevelOrder)

universe u

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}
variable {P : ChurchRules S.R} {heads : Head → ZFSet.{u}} {constants : DeclName → ZFSet.{u}}
variable (q : FormationSensitiveTypedQuotient.Qualification S)
  (lifting : LiftingFacts P) (model : SetModel heads constants P)
variable {first last : Context S.R}
  {sourceContext : CCtx Head first.arity} {targetContext : CCtx Head last.arity}
  (sourceFormed : CCtxFormed P sourceContext) (sourceErases : sourceContext.erase = first.raw)
  (targetFormed : CCtxFormed P targetContext) (targetErases : targetContext.erase = last.raw)
  (arrow : first ⟶ last) {substitution : CSub Head last.arity first.arity}
  (typed : CSubstMor P targetContext sourceContext substitution)
  (componentsErase : ∀ index, (substitution index).erase = arrow.substitution index)
include componentsErase

/-- Full typed equality classes commute with the actual supplied contextual
substitution and its evaluated environment map. -/
theorem typeValue_reindex (type : FormationSensitiveTypedQuotient.QType q last)
    (environment : ConversionQuotient.Environment
      (heads := heads) (constants := constants) sourceContext) :
    typeValue q lifting model sourceFormed sourceErases (type.reindex arrow) environment =
      typeValue q lifting model targetFormed targetErases type
        (ConversionQuotient.substitutionEnvironment model typed environment) := by
  induction type using Quotient.inductionOn with
  | h type =>
      exact ConversionQuotient.typeValue_reindex model lifting q.forms q.roots q.heads q.church
        sourceFormed sourceErases targetFormed targetErases arrow typed componentsErase type environment

/-- Subject values, including typed beta/eta identifications, commute with
the same admitted substitution. -/
theorem termValue_reindex (term : FormationSensitiveTypedQuotient.QTerm q last)
    (environment : ConversionQuotient.Environment
      (heads := heads) (constants := constants) sourceContext) :
    termValue q lifting model sourceFormed sourceErases (term.reindex arrow) environment =
      termValue q lifting model targetFormed targetErases term
        (ConversionQuotient.substitutionEnvironment model typed environment) := by
  induction term using Quotient.inductionOn with
  | h pair =>
      exact ConversionQuotient.termValue_reindex model lifting q.forms q.roots q.heads q.church
        sourceFormed sourceErases targetFormed targetErases arrow typed componentsErase pair.2 environment

omit componentsErase
include q lifting sourceFormed sourceErases targetErases

/-- Independently admitted annotations of raw-converted substitutions give
the same actual environment map. Consequently the semantic action respects
the existing quotient of contextual arrows. -/
theorem substitutionEnvironment_converted {firstArrow secondArrow : first ⟶ last}
    (converted : homConversion S.R firstArrow secondArrow)
    {earlier later : CSub Head last.arity first.arity}
    (earlierTyped : CSubstMor P targetContext sourceContext earlier)
    (laterTyped : CSubstMor P targetContext sourceContext later)
    (earlierErases : ∀ index, (earlier index).erase = firstArrow.substitution index)
    (laterErases : ∀ index, (later index).erase = secondArrow.substitution index)
    (environment : ConversionQuotient.Environment
      (heads := heads) (constants := constants) sourceContext) :
    ConversionQuotient.substitutionEnvironment model earlierTyped environment =
      ConversionQuotient.substitutionEnvironment model laterTyped environment := by
  apply Subtype.ext
  funext index
  obtain ⟨level, universeWitness, entryFormed⟩ := last.formed.lookup_formed index
  let targetType : TypeOver last := ⟨Ctx.lookup last.raw index, level, universeWitness, entryFormed⟩
  let firstTerm : Term first (targetType.reindex firstArrow) :=
    ⟨firstArrow.substitution index, firstArrow.typed index⟩
  let secondTerm : Term first (targetType.reindex secondArrow) :=
    ⟨secondArrow.substitution index, secondArrow.typed index⟩
  have earlierTypeErases : ((targetContext.lookup index).subst earlier).erase =
      (targetType.reindex firstArrow).code := by
    rw [CTm.erase_subst, CCtx.erase_lookup, targetErases]
    exact Presentation.subst_ext earlierErases (Ctx.lookup last.raw index)
  have laterTypeErases : ((targetContext.lookup index).subst later).erase =
      (targetType.reindex secondArrow).code := by
    rw [CTm.erase_subst, CCtx.erase_lookup, targetErases]
    exact Presentation.subst_ext laterErases (Ctx.lookup last.raw index)
  have earlierComparison := ConversionQuotient.termValue_annotation lifting model
    q.forms q.roots q.heads q.church sourceFormed sourceErases
    firstTerm (earlierTyped index) (earlierErases index) earlierTypeErases
  have laterComparison := ConversionQuotient.termValue_annotation lifting model
    q.forms q.roots q.heads q.church sourceFormed sourceErases
    secondTerm (laterTyped index) (laterErases index) laterTypeErases
  have convertedValues := ConversionQuotient.termValue_conversion lifting model
    q.forms q.roots q.heads q.church sourceFormed sourceErases firstTerm secondTerm
    (Conv.substitutePointwise converted (Ctx.lookup last.raw index)) (converted index)
  exact congrFun (earlierComparison.symm.trans (convertedValues.trans laterComparison)) environment

end TypedQuotientValues
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
