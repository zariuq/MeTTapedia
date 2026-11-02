import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateContexts
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentReplay

/-!
# Guarded readings of the actual instantiated natural telescopes

The declared schema instance substitutes the motive universe by the maximum
of its two parameters. Its context therefore needs the corresponding lexical
head reading. A one-way lexical map transports the original predicate reading
without changing the source declaration, the HOL carriers or its guard terms.

Both original natural row contexts retain their dependent motive, base and
method guards. Source formation comes from the existing independent annotated
proofs. This is a fixed-carrier reading of those telescopes, not a general
universe model or a reflected typing theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.GuardedContexts
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open HOL.PredicateContexts
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

def levelMap : Tower.Head → Tower.Head := RussellTarski.substLevelsHead Programs.levels

def lexical (operations : Operations Base Const) : AnnotatedPredicateReading.LexicalReading Tower.Head Base Const where
  constCode? := (lexicalReading operations).constCode?
  headCode? := fun head => if head = levelMap (.sort motiveLevel) then
    some ⟨.arr (.arr operations.result .prop) .prop, HOL.PredicateProducts.full (.arr operations.result .prop)⟩
    else none

theorem lexical_map (operations : Operations Base Const) :
    AnnotatedPredicateReading.LexicalMap (lexicalReading operations) (lexical operations) levelMap := by
  constructor
  · intro name type code found
    exact found
  · intro head type code found
    dsimp only [lexicalReading] at found
    split at found
    · rename_i same
      subst head
      simpa [lexical] using found
    · cases found
  · intro operator result code found
    cases found

def parameters (operations : Operations Base Const) : Telescope Const operations.parameters :=
  .snoc (.snoc (.snoc .nil operations.motiveCode) operations.zeroCode) operations.stepCode

theorem original_reads (operations : Operations Base Const) :
    AnnotatedPredicateReading.ContextReads (lexicalReading operations)
      (Γ := operations.parameters) (liftCtx natContextPZS) (parameters operations) :=
  .snoc (.snoc (.snoc .nil
    (AnnotatedReads.of_lamFree operations.motiveCode_reads (by rfl)).toGeneric)
    (AnnotatedReads.of_lamFree operations.zeroCode_reads (by rfl)).toGeneric)
    (AnnotatedReads.of_lamFree operations.stepCode_reads (by rfl)).toGeneric

theorem zero_context_mapped (operations : Operations Base Const) :
    AnnotatedConversion.Row.zero.context operations = (liftCtx natContextPZS).mapHead levelMap := rfl

theorem zero_reads (operations : Operations Base Const) :
    AnnotatedPredicateReading.ContextReads (lexical operations)
      (Γ := operations.parameters) (AnnotatedConversion.Row.zero.context operations) (parameters operations) := by
  rw [zero_context_mapped]
  exact (original_reads operations).mapLexical (lexical_map operations)

def contextCode (operations : Operations Base Const) :
    (row : AnnotatedConversion.Row) → Telescope Const (row.parameters operations)
  | .zero => parameters operations
  | .successor => .snoc (parameters operations) (HOL.PredicateProducts.full operations.number)

theorem context_reads (operations : Operations Base Const) (row : AnnotatedConversion.Row) :
    AnnotatedPredicateReading.ContextReads (lexical operations) (row.context operations) (contextCode operations row) := by
  cases row with
  | zero => exact zero_reads operations
  | successor =>
      apply AnnotatedPredicateReading.ContextReads.snoc (zero_reads operations)
      exact (AnnotatedReads.natural (operations := operations) (Γ := operations.parameters)).toGeneric.mapLexical
        (lexical_map operations)

def admitted (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (row : AnnotatedConversion.Row) :
    AnnotatedPredicateReading.Reader.AdmittedContext (Programs.Annotated.church profile)
      (lexical operations) (row.parameters operations) (row.context operations) where
  code := contextCode operations row
  reading := context_reads operations row
  formed := by
    cases row with
    | zero => exact Programs.Annotated.context_formed profile ⟨0, by decide⟩
    | successor => exact Programs.Annotated.context_formed profile ⟨1, by decide⟩

theorem admission_available [DecidableEq Base] (operations : Operations Base Const)
    (profile : Programs.ComputationProfiles.Selection) (row : AnnotatedConversion.Row) :
    ∃ certificate,
      AnnotatedPredicateReading.Reader.admitContext? (Programs.Annotated.church profile) (lexical operations)
        (Programs.Annotated.JudgmentReplay.decoder profile) (row.parameters operations) (row.context operations)
        certificate = some (admitted operations profile row) :=
  AnnotatedPredicateReading.Reader.admitContext_complete _ _ _

def rootAssumptions (operations : Operations Base Const) : List (HOL.Formula Const operations.parameters) :=
  [HOL.SelectionProofs.principle (HOL.weakenCtx _ operations.selection),
   HOL.NaturalRecursionProofs.statement (HOL.weakenCtx _ operations.zero)
     (HOL.weakenCtx _ operations.successor) operations.result,
   HOL.NaturalRecursionProofs.inductionPrinciple (HOL.weakenCtx _ operations.zero)
     (HOL.weakenCtx _ operations.successor)]

def typingAssumptions (operations : Operations Base Const) :=
  rootAssumptions operations ++ (parameters operations).hypotheses

theorem base_guard (operations : Operations Base Const) :
    (parameters operations).guard (HOL.Var.vs HOL.Var.vz) =
      HOL.NaturalRecursionProofs.holds (.var (.vs (.vs .vz))) (HOL.weakenCtx _ operations.zero) (.var (.vs .vz)) := by
  simp [parameters, Telescope.guard, Telescope.domain, Operations.zeroCode, HOL.NaturalRecursionProofs.holds,
    HOL.weaken, HOL.rename, HOL.Rename.weaken]

theorem method_guard (operations : Operations Base Const) :
    (parameters operations).guard HOL.Var.vz =
      .app (operations.methodPredicate (.var (.vs (.vs .vz)))) (.var .vz) := by
  simp [parameters, Telescope.guard, Telescope.domain, Operations.stepCode, HOL.weaken,
    Operations.rename_methodPredicate, HOL.rename, HOL.Rename.weaken]

def baseMember (operations : Operations Base Const) : HOL.ProofSyntax Const (typingAssumptions operations)
    (HOL.NaturalRecursionProofs.holds (.var (.vs (.vs .vz))) (HOL.weakenCtx _ operations.zero) (.var (.vs .vz))) :=
  HOL.ProofSyntax.castIndices rfl (base_guard operations)
    (HOL.ProofSyntax.mono (HOL.ProofSyntax.OccurrenceMap.appendLeft _ _)
      ((parameters operations).variableProof (.vs .vz)))

def methodMember (operations : Operations Base Const) : HOL.ProofSyntax Const (typingAssumptions operations)
    (.app (operations.methodPredicate (.var (.vs (.vs .vz)))) (.var .vz)) :=
  HOL.ProofSyntax.castIndices rfl (method_guard operations)
    (HOL.ProofSyntax.mono (HOL.ProofSyntax.OccurrenceMap.appendLeft _ _)
      ((parameters operations).variableProof .vz))

/-- The open base and method premises come from their actual telescope
occurrences. Only the three primitive root facts remain additional premises. -/
def resultTyping (operations : Operations Base Const) : HOL.ProofSyntax Const (typingAssumptions operations)
    (.app (operations.resultPredicate (.var (.vs (.vs .vz)))) operations.atParameters) :=
  operations.result_typed (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)
    (.hyp ⟨0, by simp [typingAssumptions, rootAssumptions]⟩)
    (.hyp ⟨1, by simp [typingAssumptions, rootAssumptions]⟩)
    (.hyp ⟨2, by simp [typingAssumptions, rootAssumptions]⟩)
    (baseMember operations) (methodMember operations)

theorem resultTyping_free (operations : Operations Base Const) :
    (resultTyping operations).FunctionExtensionalityFree := by
  apply operations.result_typed_free
  all_goals simp [baseMember, methodMember, Telescope.variableProof, HOL.ProofSyntax.FunctionExtensionalityFree]

#print axioms lexical_map
#print axioms original_reads
#print axioms context_reads
#print axioms admission_available
#print axioms base_guard
#print axioms method_guard
#print axioms resultTyping_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.GuardedContexts
