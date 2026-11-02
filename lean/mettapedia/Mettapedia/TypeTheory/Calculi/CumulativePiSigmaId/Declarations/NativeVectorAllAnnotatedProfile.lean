import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedAppend
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ElaborationHeadMap
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeFormationReadback

/-!
# Annotated Nat/Vector profiles for universe-valued elimination

Element and result levels are independent parameters. The existing annotated
Nat/Vector package transports through its actual level substitution, retaining
the selected root schemas and their mapped premises. Closed declaration proofs
then apply in arbitrary target contexts; caller terms need not be source images.

The recursor bound retains the explicit maximum of the element level and the
successor result level. This profile is not silently identified with a signature
whose universe expressions have different syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Profile

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated
open NativeNaturalVectorFamilies

def levels (element result : LevelExpr Nat) (parameter : Nat) : LevelExpr Nat :=
  if parameter = 0 then element else if parameter = 1 then .succ result else .param parameter

def heads (element result : LevelExpr Nat) : Tower.Head → Tower.Head :=
  RussellTarski.substLevelsHead (levels element result)

def rules (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) : Rules Tower.Head :=
  Rules.mapSchemas (heads element result) Tower.rules (Programs.ComputationProfiles.rules enabled)
    (Programs.Annotated.family enabled)

def church (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    ChurchRules (rules element result enabled) :=
  ChurchRules.mapSchemas (heads element result) Tower.rules (Programs.ComputationProfiles.rules enabled)
    (Programs.Annotated.family enabled)

theorem morphism (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    (Programs.Annotated.church enabled).Morphism (church element result enabled) (heads element result) :=
  ChurchRules.mapSchemas_morphism (heads element result) Tower.rules
    (Programs.ComputationProfiles.rules enabled) (Programs.Annotated.family enabled)
    (Programs.Annotated.presentation enabled)
    (RussellTarski.levelSubstMorphism (levels element result)).headTyping
    (RussellTarski.levelSubstMorphism (levels element result)).isUniverse
    (RussellTarski.levelSubstMorphism (levels element result)).join
    (RussellTarski.levelSubstMorphism (levels element result)).cumulative
    (RussellTarski.levelSubstMorphism (levels element result)).headEq

def levelModel (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    TypedEquality.Normalization.LevelModel (rules element result enabled) Nat :=
  { TypedEquality.Normalization.TowerModel.levels (fun _ => 0) with }

def recursorLevel (element result : LevelExpr Nat) : LevelExpr Nat := .max element (.succ result)

variable (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    {n : Nat} {ambient : CCtx Tower.Head n}

def elementSort : CTm Tower.Head n := .head (.sort element)
def motiveSort : CTm Tower.Head n := .head (.sort (recursorLevel element result))

private theorem transportClosed {term type : CTm Tower.Head 0}
    (typed : CTyped (Programs.Annotated.church enabled) .nil term type) :
    CTyped (church element result enabled) ambient ((term.mapHead (heads element result)).liftClosed)
      ((type.mapHead (heads element result)).liftClosed) :=
  CTyped.rename (typed.mapHead (morphism element result enabled)) (fun index => index.elim0)

theorem natural_typed : CTyped (church element result enabled) ambient (.const natName) (.head (.sort Tower.zero)) := by
  exact transportClosed element result enabled (Programs.Annotated.Functions.natural_typed enabled (Γ := .nil))

theorem zero_typed : CTyped (church element result enabled) ambient (.const zeroName) (.const natName) := by
  exact transportClosed element result enabled (Programs.Annotated.Functions.zero_typed enabled (Γ := .nil))

theorem successor_constant_typed : CTyped (church element result enabled) ambient (.const succName)
    (.pi (.const natName) (.const natName)) :=
  transportClosed element result enabled (Programs.Annotated.Functions.successor_constant_typed enabled (Γ := .nil))

theorem successor_typed {number : CTm Tower.Head n}
    (typed : CTyped (church element result enabled) ambient number (.const natName)) :
    CTyped (church element result enabled) ambient (Programs.Annotated.Functions.successor number) (.const natName) :=
  .appElim (successor_constant_typed element result enabled) typed

theorem vector_constant_typed : CTyped (church element result enabled) ambient (.const vecName)
    (.pi (elementSort element) (.pi (.const natName) (elementSort element))) := by
  exact transportClosed element result enabled (Programs.Annotated.Append.vector_constant_typed enabled (Γ := .nil))

theorem vector_typed {A length : CTm Tower.Head n}
    (elementTyped : CTyped (church element result enabled) ambient A (elementSort element))
    (lengthTyped : CTyped (church element result enabled) ambient length (.const natName)) :
    CTyped (church element result enabled) ambient (Programs.Annotated.Append.vector A length) (elementSort element) :=
  .appElim (.appElim (vector_constant_typed element result enabled) elementTyped) lengthTyped

theorem nil_constant_typed : CTyped (church element result enabled) ambient (.const vnilName)
    (.pi (elementSort element) (Programs.Annotated.Append.vector (.var 0) (.const zeroName))) := by
  exact transportClosed element result enabled (Programs.Annotated.Append.nil_constant_typed enabled (Γ := .nil))

theorem nil_typed {A : CTm Tower.Head n}
    (typed : CTyped (church element result enabled) ambient A (elementSort element)) :
    CTyped (church element result enabled) ambient (Programs.Annotated.Append.nil A)
      (Programs.Annotated.Append.vector A (.const zeroName)) :=
  .appElim (nil_constant_typed element result enabled) typed

def consEntry (scope : Nat) : Tower.Tm scope :=
  (Programs.Annotated.Append.consEntry scope).mapHead (heads element result)

def consContext : Tower.Ctx 4 := TypedEquality.Normalization.ofEntries (consEntry element result) 4

theorem cons_constant_typed : CTyped (church element result enabled) ambient (.const vconsName)
    (liftTm (TelescopeAbstraction.closeType (consContext element result) Programs.Annotated.Append.consResult)).liftClosed := by
  exact transportClosed element result enabled (Programs.Annotated.Append.cons_constant_typed enabled (Γ := .nil))

theorem cons_typed {A length head tail : CTm Tower.Head n}
    (elementTyped : CTyped (church element result enabled) ambient A (elementSort element))
    (lengthTyped : CTyped (church element result enabled) ambient length (.const natName))
    (headTyped : CTyped (church element result enabled) ambient head A)
    (tailTyped : CTyped (church element result enabled) ambient tail (Programs.Annotated.Append.vector A length)) :
    CTyped (church element result enabled) ambient (Programs.Annotated.Append.cons A length head tail)
      (Programs.Annotated.Append.vector A (Programs.Annotated.Functions.successor length)) := by
  have arguments : CSubstMor (church element result enabled) (liftCtx (consContext element result)) ambient
      (Programs.Annotated.Append.consArguments A length head tail) := by
    intro index
    exact Fin.cases tailTyped (Fin.cases headTyped (Fin.cases lengthTyped
      (Fin.cases elementTyped (fun impossible => Fin.elim0 impossible)))) index
  exact applyAlong_typed (Q := church element result enabled) (consEntry element result) 4
    Programs.Annotated.Append.consResult (Programs.Annotated.Append.consArguments A length head tail)
    arguments (cons_constant_typed element result enabled)

def recursorEntry (scope : Nat) : Tower.Tm scope :=
  (Programs.Annotated.Append.recursorEntry scope).mapHead (heads element result)

def recursorContext : Tower.Ctx 6 := TypedEquality.Normalization.ofEntries (recursorEntry element result) 6

theorem recursor_constant_typed : CTyped (church element result enabled) ambient (.const vecEliminateName)
    (liftTm (TelescopeAbstraction.closeType (recursorContext element result) Programs.Annotated.Append.recursorResult)).liftClosed := by
  exact transportClosed element result enabled (Programs.Annotated.Append.recursor_constant_typed enabled (Γ := .nil))

def familyType (A : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi (.const natName) (.pi (Programs.Annotated.Append.vector (A.rename wk) (.var 0)) (motiveSort element result))

theorem eliminate_typed {A family base method length value : CTm Tower.Head n}
    (elementTyped : CTyped (church element result enabled) ambient A (elementSort element))
    (familyTyped : CTyped (church element result enabled) ambient family (familyType element result A))
    (baseTyped : CTyped (church element result enabled) ambient base
      (.app (.app family (.const zeroName)) (Programs.Annotated.Append.nil A)))
    (methodTyped : CTyped (church element result enabled) ambient method (Programs.Annotated.Append.methodType A family))
    (lengthTyped : CTyped (church element result enabled) ambient length (.const natName))
    (valueTyped : CTyped (church element result enabled) ambient value (Programs.Annotated.Append.vector A length)) :
    CTyped (church element result enabled) ambient (Programs.Annotated.Append.eliminate A family base method length value)
      (.app (.app family length) value) := by
  have arguments : CSubstMor (church element result enabled) (liftCtx (recursorContext element result)) ambient
      (Programs.Annotated.Append.arguments A family base method length value) := by
    intro index
    fin_cases index
    · exact valueTyped
    · exact lengthTyped
    · exact methodTyped
    · exact baseTyped
    · simpa [recursorContext, recursorEntry, TypedEquality.Normalization.ofEntries,
        Programs.Annotated.Append.recursorEntry, Programs.Annotated.Append.arguments,
        liftCtx, liftTm, CTm.annotateWith, CCtx.lookup, CTm.rename, CTm.subst,
        CTm.liftSub, liftRen, wk, Fin.cases, Fin.induction, Fin.induction.go,
        RussellTarski.substLevelsTm, RussellTarski.substLevelsHead, Tm.mapHead,
        vecMotiveType, vecApp, natTm, motiveLevel, elementLevel, sortTm, familyType, Programs.levels,
        heads, levels, LevelExpr.subst, motiveSort, recursorLevel,
        Programs.Annotated.Append.vector] using familyTyped
    · exact elementTyped
  exact applyAlong_typed (Q := church element result enabled) (recursorEntry element result) 6
    Programs.Annotated.Append.recursorResult (Programs.Annotated.Append.arguments A family base method length value)
    arguments (recursor_constant_typed element result enabled)

#print axioms morphism
#print axioms eliminate_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Profile
