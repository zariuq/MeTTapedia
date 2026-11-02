import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRealizability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FunctionArgumentAdapters

/-!
# Complete guarded application spines

Each supplied argument is an existing guarded realizer, retaining source
typing, exact readings and an actual membership proof. Applying the complete
spine derives the residual source type and retains the resulting proof data.
No whole-method closure or residual typing theorem is supplied as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
    {Γ : HOL.Ctx Base}

def instantiateProducts {n : Nat} : List (CTm Head n) → CTm Head n → Option (CTm Head n)
  | [], type => some type
  | argument :: rest, type => match type with
    | .pi _ body => instantiateProducts rest (CTm.inst0 argument body)
    | _ => none
termination_by structural arguments _ => arguments

inductive SuppliedArguments (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ) :
    List (CTm Head Γ.length) → CTm Head Γ.length → HOL.Ty Base → CTm Head Γ.length → HOL.Ty Base → Type (max u v) where
  | nil (type : CTm Head Γ.length) (carrier : HOL.Ty Base) :
      SuppliedArguments roots context [] type carrier type carrier
  | cons {argument : CTm Head Γ.length} {rest : List (CTm Head Γ.length)}
      {domain : CTm Head Γ.length} {body : CTm Head (Γ.length + 1)}
      {domainCarrier codomainCarrier finalCarrier : HOL.Ty Base} {target : CTm Head Γ.length}
      (value : GuardedRealizer roots context argument domain domainCarrier)
      (remaining : SuppliedArguments roots context rest (CTm.inst0 argument body) codomainCarrier target finalCarrier) :
      SuppliedArguments roots context (argument :: rest) (.pi domain body) (.arr domainCarrier codomainCarrier) target finalCarrier

namespace SuppliedArguments

variable {roots : List (HOL.ClosedFormula Const)} {context : GuardedContext P lex Γ}
    {arguments : List (CTm Head Γ.length)} {source target : CTm Head Γ.length}
    {carrier finalCarrier : HOL.Ty Base}

theorem instantiate (supplied : SuppliedArguments roots context arguments source carrier target finalCarrier) :
    instantiateProducts arguments source = some target := by
  induction supplied with
  | nil => rfl
  | cons _ _ previous => exact previous

/-- Supplying every queued argument leaves the declaration's result type.
The input type is compared by erasure, so source annotations remain intact. -/
theorem residual_of_curried
    (supplied : SuppliedArguments roots context arguments source carrier target finalCarrier)
    (domains : List (Tm Head Γ.length)) (result : Tm Head Γ.length)
    (original : source.erase = FunctionArgumentAdapters.curriedType domains result)
    (complete : arguments.length = domains.length) : target.erase = result := by
  induction supplied generalizing domains result with
  | nil type carrier =>
      cases domains with
      | nil => simpa only [FunctionArgumentAdapters.curriedType] using original
      | cons first rest => simp only [List.length_nil, List.length_cons] at complete; omega
  | cons value remaining previous =>
      cases domains with
      | nil => simp only [List.length_nil, List.length_cons] at complete; omega
      | cons first rest =>
          simp only [CTm.erase, FunctionArgumentAdapters.curriedType_cons,
            FunctionArgumentAdapters.arrow] at original
          have body := (Tm.pi.inj original).2
          apply previous rest result
          · simp only [CTm.erase_inst0, body, inst0_rename_wk]
          · simpa only [List.length_cons, Nat.add_right_cancel_iff] using complete

def apply [DecidableEq Base] :
    {arguments : List (CTm Head Γ.length)} → {source target : CTm Head Γ.length} →
    {carrier finalCarrier : HOL.Ty Base} →
    (supplied : SuppliedArguments roots context arguments source carrier target finalCarrier) →
    {function : CTm Head Γ.length} → GuardedRealizer roots context function source carrier →
    GuardedRealizer roots context (CTm.appSpine function arguments) target finalCarrier
  | _, _, _, _, _, .nil _ _, _, functionValue => functionValue
  | _, _, _, _, _, .cons value remaining, _, functionValue =>
      remaining.apply (GuardedRealizer.application functionValue value)

def Free : {arguments : List (CTm Head Γ.length)} → {source target : CTm Head Γ.length} →
    {carrier finalCarrier : HOL.Ty Base} →
    SuppliedArguments roots context arguments source carrier target finalCarrier → Prop
  | _, _, _, _, _, .nil _ _ => True
  | _, _, _, _, _, .cons value remaining => value.Free ∧ Free remaining

theorem apply_free [DecidableEq Base]
    (supplied : SuppliedArguments roots context arguments source carrier target finalCarrier)
    {function : CTm Head Γ.length} (functionValue : GuardedRealizer roots context function source carrier)
    (suppliedFree : supplied.Free) (functionFree : functionValue.Free) :
    (supplied.apply functionValue).Free := by
  induction supplied generalizing function with
  | nil => exact functionFree
  | cons value remaining previous =>
      apply previous
      · exact suppliedFree.2
      · exact GuardedRealizer.application_free functionValue value functionFree suppliedFree.1

end SuppliedArguments

#print axioms SuppliedArguments.instantiate
#print axioms SuppliedArguments.residual_of_curried
#print axioms SuppliedArguments.apply_free

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
