import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerGuardedMethodContexts
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllReading

/-!
# Reading every original mixed-constructor field and induction hypothesis

The formed source context is the registered native-Vector provider's actual
context, including the complete All programme. The existing context reader
checks all twelve binders. The selected profile gives the two source element
types the same HOL carrier, with distinct predicate guards. No closed datatype
case-function or generic universe interpretation is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodReading

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedContainerAnnotated
local infixr:60 " ⇒ " => HOL.Ty.arr

inductive Base where
  | number | element | vector | evidence
  deriving DecidableEq

inductive Const : HOL.Ty Base → Type where
  | parameter (name : Nat) (type : HOL.Ty Base) : Const type

abbrev N : HOL.Ty Base := .base .number
abbrev E : HOL.Ty Base := .base .element
abbrev V : HOL.Ty Base := .base .vector
abbrev W : HOL.Ty Base := .base .evidence

def parameter (name : Nat) (type : HOL.Ty Base) : HOL.ClosedTerm Const type := .const (.parameter name type)

def original : NativeVectorComputationRows.Operations Base Const where
  number := N
  element := E
  vector := V
  result := W
  zero := parameter 0 _
  successor := parameter 1 _
  nil := parameter 2 _
  cons := parameter 3 _
  head := parameter 4 _
  tail := parameter 5 _
  selection := parameter 6 _

def pairs : HOL.PredicateSigma.Operations Const W where
  pair := parameter 7 _
  first := parameter 8 _
  second := parameter 9 _

def witness : HOL.ClosedTerm Const W := parameter 10 _
def selection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection (N ⇒ V ⇒ W ⇒ .prop)) := parameter 11 _

def elementLevel : UniverseLevel.LevelExpr Nat := .param 0
def resultLevel : UniverseLevel.LevelExpr Nat := .param 2

def lex := NativeVectorAll.Reading.lexical original pairs witness selection elementLevel resultLevel

theorem separated : NativeVectorAll.Reading.ProfileLevels elementLevel resultLevel := by
  constructor <;> decide +kernel

abbrev constructorCarrier := N ⇒ E ⇒ E ⇒ V ⇒ E ⇒ E
abbrev motiveCarrier := E ⇒ W ⇒ .prop
abbrev ambient : HOL.Ctx Base := [constructorCarrier, motiveCarrier, E ⇒ .prop, E ⇒ .prop]

def carriers : MethodCarriers IndexedContainerNativeVectorMethodFormation.I
    IndexedContainerNativeVectorMethodFormation.registry Base where
  data
    | .length => N
    | .payload => E
  recursive := E
  nested _ _ _ := V
  directHypothesis := W
  nestedHypothesis _ _ _ := W

def source := IndexedContainerNativeVectorMethodFormation.completeContext elementLevel resultLevel
def target : HOL.Ctx Base := carriers.context IndexedContainerNativeVectorMethodFormation.code ambient []

theorem target_size : target.length = 12 := by decide +kernel

def checkedSource : CCtx Tower.Head target.length :=
  cast (congrArg (CCtx Tower.Head) (by decide +kernel : source.1 = target.length)) source.2

theorem checkedSource_formed :
    CCtxFormed (NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false)) checkedSource := by
  have transport {n m : Nat} (same : n = m) (context : CCtx Tower.Head n)
      (formed : CCtxFormed (NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false)) context) :
      CCtxFormed (NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false))
        (cast (congrArg (CCtx Tower.Head) same) context) := by
    cases same
    exact formed
  exact transport (by decide +kernel : source.1 = target.length) source.2
    (IndexedContainerNativeVectorMethodFormation.completeContext_formed elementLevel resultLevel (fun _ => false))

def reading := Reader.readContext? lex target checkedSource

theorem complete_context_readable : reading.isSome = true := by decide +kernel

def guarded : GuardedContext (NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false)) lex target :=
  { source := checkedSource
    telescope := (reading.get complete_context_readable).val
    formed := checkedSource_formed
    reading := (reading.get complete_context_readable).property }

/-- The returned source really is the provider's formed twelve-binder context;
there is no independently reconstructed or shortened source telescope. -/
theorem original_source_retained : guarded.source = checkedSource := rfl

def withoutStructural : LexicalReading Tower.Head Base Const :=
  { lex with structuralCode? := fun _ => none }

theorem missing_bundle_interpretation_refused :
    (Reader.readContext? withoutStructural target checkedSource).isSome = false := by decide +kernel

def wrongTarget : HOL.Ctx Base := N :: target.tail

def wrongSource : CCtx Tower.Head wrongTarget.length :=
  cast (congrArg (CCtx Tower.Head) (by decide +kernel : source.1 = wrongTarget.length)) source.2

theorem changed_hypothesis_carrier_refused :
    (Reader.readContext? lex wrongTarget wrongSource).isSome = false := by decide +kernel

def collided := NativeVectorAll.Reading.lexical original pairs witness selection elementLevel elementLevel

theorem colliding_universes_refuse_all :
    (Reader.infer? collided [V, N, E ⇒ W ⇒ .prop, E ⇒ .prop]
      (NativeVectorAll.Annotated.Formation.allType elementLevel (.var 3) (.var 2) (.var 1) (.var 0))).isSome = false := by
  decide +kernel

#print axioms complete_context_readable
#print axioms guarded
#print axioms missing_bundle_interpretation_refused

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodReading
