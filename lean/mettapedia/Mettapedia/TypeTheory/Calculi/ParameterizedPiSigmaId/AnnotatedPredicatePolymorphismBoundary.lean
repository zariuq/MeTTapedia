import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Validity

/-!
# The fixed-carrier boundary of the lexical predicate reader

A single source function has one simple arrow type in this reader. Its
applications therefore cannot accept type codes with different simple
carriers. The source example uses one polymorphic variable at a type and at
that type's function space. Both source applications are well typed in the
same formed context. The obstruction concerns this exact shallow reading;
it does not exclude explicit specialization or a coded universe with its own
application operation.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v

namespace PolymorphismBoundary

private def typeDepth {Base : Type u} : HOL.Ty Base → Nat
  | .prop | .base _ => 0
  | .arr first second => 1 + typeDepth first + typeDepth second

theorem function_type_ne {Base : Type u} (carrier : HOL.Ty Base) :
    carrier ≠ .arr carrier carrier := by
  intro equal
  have depths := congrArg typeDepth equal
  simp only [typeDepth] at depths
  omega

variable {Head : Type} {Base : Type u} [DecidableEq Base] {Const : HOL.Ty Base → Type v}
  {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}

theorem application_carriers {function first second : CTm Head Γ.length}
    {leftDomain rightDomain leftResult rightResult : HOL.Ty Base}
    {firstCode : HOL.Term Const Γ leftDomain} {secondCode : HOL.Term Const Γ rightDomain}
    {leftCode : HOL.Term Const Γ leftResult} {rightCode : HOL.Term Const Γ rightResult}
    (firstRead : Reads lex first firstCode) (secondRead : Reads lex second secondCode)
    (leftRead : Reads lex (.app function first) leftCode)
    (rightRead : Reads lex (.app function second) rightCode) : leftDomain = rightDomain := by
  cases leftRead with
  | application leftFunction leftArgument =>
    cases rightRead with
    | application rightFunction rightArgument =>
      have domains := congrArg Sigma.fst (Reader.coherent leftFunction rightFunction)
      have firstSame := congrArg Sigma.fst (Reader.coherent firstRead leftArgument)
      have secondSame := congrArg Sigma.fst (Reader.coherent secondRead rightArgument)
      exact firstSame.trans ((HOL.Ty.arr.inj domains).1.trans secondSame.symm)

theorem type_and_function_type_cannot_both_apply
    {function : CTm Head Γ.length} (baseHead : Head)
    {carrier : HOL.Ty Base} (predicate : HOL.Term Const Γ (.arr carrier .prop))
    (baseRead : Reads lex (.head baseHead) predicate)
    (raisedRead : Reads lex (.head baseHead) (HOL.weaken (σ := carrier) predicate)) :
    ¬ ((∃ result, ∃ code : HOL.Term Const Γ result, Reads lex (.app function (.head baseHead)) code) ∧
      (∃ result, ∃ code : HOL.Term Const Γ result,
        Reads lex (.app function (.pi (.head baseHead) (.head baseHead))) code)) := by
  rintro ⟨⟨_,left,leftRead⟩,⟨_,right,rightRead⟩⟩
  have different := application_carriers baseRead (Reads.product baseRead raisedRead) leftRead rightRead
  have equal : carrier = .arr carrier carrier := (HOL.Ty.arr.inj different).1
  exact function_type_ne carrier equal

section Source
variable {R : Rules Head} (P : ChurchRules R) (baseHead universeHead upperHead : Head)
  (baseTyped : R.headTyping baseHead universeHead) (universeTyped : R.headTyping universeHead upperHead)
  (smallUniverse : R.isUniverse universeHead) (upper : R.isUniverse upperHead)
  (smallJoin : R.join universeHead universeHead universeHead)
  (largeJoin : R.join upperHead universeHead upperHead)

def polymorphicType : CTm Head 0 :=
  .pi (.head universeHead) (.pi (.var 0) (.var 1))
def sourceContext : CCtx Head 1 := .snoc .nil (polymorphicType universeHead)

include universeTyped smallUniverse upper smallJoin largeJoin in
theorem polymorphicType_formed :
    CTyped P .nil (polymorphicType universeHead) (.head upperHead) := by
  apply CDerivable.piForm (.headType universeTyped) upper ?_ smallUniverse largeJoin
  apply CDerivable.piForm (CDerivable.var 0) smallUniverse ?_ smallUniverse smallJoin
  exact CDerivable.var 1

include universeTyped smallUniverse upper smallJoin largeJoin in
theorem sourceContext_formed : CCtxFormed P (sourceContext universeHead) :=
  .snoc .nil ⟨upperHead,upper,polymorphicType_formed P universeHead upperHead universeTyped smallUniverse upper smallJoin largeJoin⟩

include baseTyped in
theorem at_base : CTyped P (sourceContext universeHead)
    (.app (.var 0) (.head baseHead))
    (CTm.inst0 (.head baseHead) (.pi (.var 0) (.var 1))) :=
  .appElim (show CTyped P (sourceContext universeHead) (.var 0)
      (.pi (.head universeHead) (.pi (.var 0) (.var 1))) from .var 0)
    (.headType baseTyped)

include baseTyped smallUniverse smallJoin in
theorem at_function_type : CTyped P (sourceContext universeHead)
    (.app (.var 0) (.pi (.head baseHead) (.head baseHead)))
    (CTm.inst0 (.pi (.head baseHead) (.head baseHead)) (.pi (.var 0) (.var 1))) :=
  .appElim (show CTyped P (sourceContext universeHead) (.var 0)
      (.pi (.head universeHead) (.pi (.var 0) (.var 1))) from .var 0)
    (.piForm (.headType baseTyped) smallUniverse (.headType baseTyped) smallUniverse smallJoin)

end Source

#print axioms application_carriers
#print axioms type_and_function_type_cannot_both_apply
#print axioms sourceContext_formed
#print axioms at_function_type
end PolymorphismBoundary
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
