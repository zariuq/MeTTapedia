import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

/-! # Instantiation shared by application and equality readings -/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}

namespace Reads

/-- Source opening and HOL instantiation use the same represented argument. -/
theorem instantiate {domain codomain : HOL.Ty Base}
    {body : CTm Head (domain :: Γ).length} {argument : CTm Head Γ.length}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain} {argumentCode : HOL.Term Const Γ domain}
    (bodyRead : Reads lex body bodyCode) (argumentRead : Reads lex argument argumentCode) :
    Reads lex (CTm.inst0 argument body) (HOL.instantiate argumentCode bodyCode) := by
  apply bodyRead.substitute (HOL.Subst.single argumentCode) (CTm.subst0 argument)
  intro type index
  cases index with
  | vz => exact argumentRead
  | vs prior => exact .var prior

end Reads
#print axioms Reads.instantiate
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
