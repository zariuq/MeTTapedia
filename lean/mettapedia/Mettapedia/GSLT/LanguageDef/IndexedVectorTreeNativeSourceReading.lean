import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceFormation
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodReading

/-!
# Complete predicate readings of the parsed Vector-tree source contexts

The selected native profile reads the seven ambient binders and both complete
constructor field/IH contexts. The two source type parameters share the chosen
HOL carrier while retaining independent predicate variables. Constructor and
case-method slots remain distinct and retain their original source types.

Reading a requested complete context checks its length before interpreting
every original source binder. No least-family installation, semantic universe
model, represented source substitution or telescope realization follows from
readability alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceReading

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading IndexedContainerAnnotated
local infixr:60 " ⇒ " => HOL.Ty.arr

namespace Native
export IndexedContainerNativeVectorMethodReading
  (Base Const N E V W original pairs witness selection elementLevel resultLevel lex separated carriers)
end Native

abbrev solvedConstructorCarrier := Native.E ⇒ Native.E
abbrev branchConstructorCarrier := Native.N ⇒ Native.V ⇒ Native.E
abbrev motiveCarrier := Native.E ⇒ Native.W ⇒ .prop
abbrev solvedCaseCarrier := Native.E ⇒ Native.W
abbrev branchCaseCarrier := Native.N ⇒ Native.V ⇒ Native.W ⇒ Native.W

def theory := NativeVectorAll.Annotated.Profile.church Native.elementLevel Native.resultLevel (fun _ => false)

abbrev ambient : HOL.Ctx Native.Base :=
  [branchCaseCarrier, solvedCaseCarrier, branchConstructorCarrier, solvedConstructorCarrier,
    motiveCarrier, Native.E ⇒ .prop, Native.E ⇒ .prop]

def ambientSource : CCtx Tower.Head ambient.length :=
  IndexedVectorTreeNativeSourceFormation.context Native.elementLevel Native.resultLevel

theorem ambientSource_formed : CCtxFormed theory ambientSource :=
  IndexedVectorTreeNativeSourceFormation.context_formed Native.elementLevel Native.resultLevel (fun _ => false)

def ambientRead := Reader.readContext? Native.lex ambient ambientSource

theorem ambient_readable : ambientRead.isSome = true := by decide +kernel

def ambientContext : GuardedContext theory Native.lex ambient where
  source := ambientSource
  telescope := (ambientRead.get ambient_readable).val
  formed := ambientSource_formed
  reading := (ambientRead.get ambient_readable).property

def target (occurrence : Fin 2) : HOL.Ctx Native.Base :=
  Native.carriers.context (IndexedVectorTreeNativeSourceFormation.code occurrence) ambient []

theorem solved_target : target 0 = Native.E :: ambient := by decide +kernel

theorem branch_target : target 1 = Native.W :: Native.V :: Native.N :: ambient := by decide +kernel

def source (occurrence : Fin 2) :=
  IndexedVectorTreeNativeSourceFormation.completeContext Native.elementLevel Native.resultLevel occurrence

private theorem cast_formed {n m : Nat} (same : n = m) (context : CCtx Tower.Head n)
    (formed : CCtxFormed theory context) :
    CCtxFormed theory (cast (congrArg (CCtx Tower.Head) same) context) := by
  cases same
  exact formed

theorem source_target_size (occurrence : Fin 2) : (source occurrence).1 = (target occurrence).length := by
  fin_cases occurrence <;> decide +kernel

def checkedSource (occurrence : Fin 2) : CCtx Tower.Head (target occurrence).length :=
  cast (congrArg (CCtx Tower.Head) (source_target_size occurrence)) (source occurrence).2

theorem checkedSource_formed (occurrence : Fin 2) : CCtxFormed theory (checkedSource occurrence) :=
  cast_formed (source_target_size occurrence) (source occurrence).2
    (IndexedVectorTreeNativeSourceFormation.completeContext_formed Native.elementLevel Native.resultLevel
      (fun _ => false) occurrence)

def completeRead (occurrence : Fin 2) := Reader.readContext? Native.lex (target occurrence) (checkedSource occurrence)

theorem complete_readable (occurrence : Fin 2) : (completeRead occurrence).isSome = true := by
  fin_cases occurrence <;> decide +kernel

def context (occurrence : Fin 2) : GuardedContext theory Native.lex (target occurrence) where
  source := checkedSource occurrence
  telescope := ((completeRead occurrence).get (complete_readable occurrence)).val
  formed := checkedSource_formed occurrence
  reading := ((completeRead occurrence).get (complete_readable occurrence)).property

theorem full_source_retained (occurrence : Fin 2) : (context occurrence).source = checkedSource occurrence := rfl

/-- Interpret a carrier request against the complete original source. An
incomplete request is refused before any binder can be silently dropped. -/
def readComplete? (occurrence : Fin 2) (requested : HOL.Ctx Native.Base) :
    Option (GuardedContext theory Native.lex requested) :=
  if same : (source occurrence).1 = requested.length then
    let original := cast (congrArg (CCtx Tower.Head) same) (source occurrence).2
    (Reader.readContext? Native.lex requested original).map fun reading =>
      { source := original
        telescope := reading.val
        formed := cast_formed same (source occurrence).2
          (IndexedVectorTreeNativeSourceFormation.completeContext_formed Native.elementLevel Native.resultLevel
            (fun _ => false) occurrence)
        reading := reading.property }
  else none

theorem complete_request_readable (occurrence : Fin 2) : (readComplete? occurrence (target occurrence)).isSome = true := by
  fin_cases occurrence <;> decide +kernel

theorem readComplete?_source (occurrence : Fin 2) (requested : HOL.Ctx Native.Base)
    (output : GuardedContext theory Native.lex requested)
    (accepted : readComplete? occurrence requested = some output) :
    ∃ same : (source occurrence).1 = requested.length,
      output.source = cast (congrArg (CCtx Tower.Head) same) (source occurrence).2 := by
  unfold readComplete? at accepted
  split at accepted
  next same =>
    cases reading : Reader.readContext? Native.lex requested
        (cast (congrArg (CCtx Tower.Head) same) (source occurrence).2) with
    | none => simp only [reading, Option.map_none] at accepted; contradiction
    | some value =>
        simp only [reading, Option.map_some] at accepted
        cases Option.some.inj accepted
        exact ⟨same, rfl⟩
  next different => cases accepted

def familyPredicate : HOL.Term Native.Const ambient (Native.E ⇒ .prop) :=
  .var (.vs (.vs (.vs (.vs (.vs .vz)))))

def answerPredicate : HOL.Term Native.Const ambient (Native.E ⇒ .prop) :=
  .var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))

theorem family_parameter_read : Reads Native.lex (.var 5) familyPredicate := by
  exact Reads.var (Head := Tower.Head) (lex := Native.lex) (Γ := ambient)
    (.vs (.vs (.vs (.vs (.vs .vz)))))

theorem answer_parameter_read : Reads Native.lex (.var 6) answerPredicate := by
  exact Reads.var (Head := Tower.Head) (lex := Native.lex) (Γ := ambient)
    (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))

theorem independent_parameter_slots : familyPredicate ≠ answerPredicate := by
  intro same
  cases same

theorem distinct_constructor_carriers : solvedConstructorCarrier ≠ branchConstructorCarrier := by decide +kernel

theorem distinct_case_carriers : solvedCaseCarrier ≠ branchCaseCarrier := by decide +kernel

theorem missing_branch_hypothesis_refused : (readComplete? 1 (target 1).tail).isSome = false := by decide +kernel

def wrongBranchTarget : HOL.Ctx Native.Base := Native.N :: (target 1).tail

theorem changed_branch_hypothesis_carrier_refused : (readComplete? 1 wrongBranchTarget).isSome = false := by
  decide +kernel

def wrongConstructorAmbient : HOL.Ctx Native.Base :=
  [branchCaseCarrier, solvedCaseCarrier, branchConstructorCarrier, Native.N ⇒ Native.E,
    motiveCarrier, Native.E ⇒ .prop, Native.E ⇒ .prop]

theorem changed_constructor_carrier_refused :
    (Reader.readContext? Native.lex wrongConstructorAmbient ambientSource).isSome = false := by decide +kernel

def wrongCaseAmbient : HOL.Ctx Native.Base :=
  [solvedCaseCarrier, solvedCaseCarrier, branchConstructorCarrier, solvedConstructorCarrier,
    motiveCarrier, Native.E ⇒ .prop, Native.E ⇒ .prop]

theorem changed_case_carrier_refused :
    (Reader.readContext? Native.lex wrongCaseAmbient ambientSource).isSome = false := by decide +kernel

def withoutStructural : LexicalReading Tower.Head Native.Base Native.Const :=
  { Native.lex with structuralCode? := fun _ => none }

theorem missing_all_interpretation_refused :
    (Reader.readContext? withoutStructural ambient ambientSource).isSome = false := by decide +kernel

def collided := NativeVectorAll.Reading.lexical Native.original Native.pairs Native.witness Native.selection
  Native.elementLevel Native.elementLevel

def collidedSource : CCtx Tower.Head ambient.length :=
  IndexedVectorTreeNativeSourceFormation.context Native.elementLevel Native.elementLevel

theorem collidedSource_formed :
    CCtxFormed (NativeVectorAll.Annotated.Profile.church Native.elementLevel Native.elementLevel (fun _ => false))
      collidedSource :=
  IndexedVectorTreeNativeSourceFormation.context_formed Native.elementLevel Native.elementLevel (fun _ => false)

theorem colliding_universes_refused :
    (Reader.readContext? collided ambient collidedSource).isSome = false := by decide +kernel

#print axioms ambient_readable
#print axioms complete_readable
#print axioms readComplete?_source
#print axioms missing_branch_hypothesis_refused
#print axioms colliding_universes_refused

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceReading
