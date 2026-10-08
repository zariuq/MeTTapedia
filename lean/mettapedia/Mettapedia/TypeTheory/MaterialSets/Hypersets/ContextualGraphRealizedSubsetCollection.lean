import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedFullness

/-!
# Ordinary Subset Collection in the varying realized graph model

The independently stated first-order schema chooses a collecting family
before its relation parameter. Every implication and universal clause
ranges over all actual future arrows. The constructed receipt-function
catalogue validates this schema without a powerset or erased witness
selection principle.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSubsetCollection

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization
open GraphRealizedSetTheory (subsetPremiseIndices subsetForwardIndices subsetBackwardIndices subsetCollectionAxiom)
open ContextualMaterialLogic (substitute)
universe u
variable {D : Type u} [Category.{u} D] {point : D} {count : Nat}
variable (body : Formula (count+3))

def schemaPremise : Formula (count+4) :=
  .all (.imply (.member 0 4)
    (.exist (.both (.member 0 4) (substitute subsetPremiseIndices body))))

def schemaFirst : Formula (count+5) :=
  .all (.imply (.member 0 5)
    (.exist (.both (.member 0 2) (substitute subsetForwardIndices body))))

def schemaSecond : Formula (count+5) :=
  .all (.imply (.member 0 1)
    (.exist (.both (.member 0 6) (substitute subsetBackwardIndices body))))

theorem premiseEnvironment (environment : Environment D count point)
    (source target family parameter value result : Value D point) :
    extend D result (extend D value (extend D parameter (extend D family
      (extend D target (extend D source environment))))) ∘ subsetPremiseIndices =
        extend D result (extend D value (extend D parameter environment)) := by
  funext index
  exact Fin.cases rfl (fun second => Fin.cases rfl
    (fun third => Fin.cases rfl (fun _ => rfl) third) second) index

theorem forwardEnvironment (environment : Environment D count point)
    (source target family parameter collector value result : Value D point) :
    extend D result (extend D value (extend D collector (extend D parameter
      (extend D family (extend D target (extend D source environment)))))) ∘ subsetForwardIndices =
        extend D result (extend D value (extend D parameter environment)) := by
  funext index
  exact Fin.cases rfl (fun second => Fin.cases rfl
    (fun third => Fin.cases rfl (fun _ => rfl) third) second) index

theorem backwardEnvironment (environment : Environment D count point)
    (source target family parameter collector result value : Value D point) :
    extend D value (extend D result (extend D collector (extend D parameter
      (extend D family (extend D target (extend D source environment)))))) ∘ subsetBackwardIndices =
        extend D result (extend D value (extend D parameter environment)) := by
  funext index
  exact Fin.cases rfl (fun second => Fin.cases rfl
    (fun third => Fin.cases rfl (fun _ => rfl) third) second) index

def schemaInput (environment : Environment D count point)
    (source target family parameter : Value D point)
    (proof : realize D (schemaPremise body) point
      (extend D parameter (extend D family (extend D target (extend D source environment))))) :
    ContextualGraphRealizedFullness.Premise body (extend D parameter environment) source target := by
  intro future path value member
  have current := proof future path value future (𝟙 future)
  rw [moveEnvironment_identity] at current
  let selected : Σ result : Value D future,
      ULift (Member result (move D path target)) ×
        realize D (substitute subsetPremiseIndices body) future
          (extend D result (extend D value (moveEnvironment D path
            (extend D parameter (extend D family (extend D target (extend D source environment))))))) :=
    current ⟨member⟩
  refine ⟨selected.1, selected.2.1.down, ?_⟩
  have same : realize D (substitute subsetPremiseIndices body) future
      (extend D selected.1 (extend D value (moveEnvironment D path
        (extend D parameter (extend D family (extend D target (extend D source environment))))))) =
      realize D body future
        (extend D selected.1 (extend D value (moveEnvironment D path (extend D parameter environment)))) := by
    generalize selected.1 = result
    simp only [moveEnvironment_extend]
    rw [realize_substitution, premiseEnvironment]
  exact same ▸ selected.2.2

def firstClause (environment : Environment D count point)
    (source target family parameter : Value D point)
    (input : ContextualGraphRealizedFullness.Premise body (extend D parameter environment) source target) :
    realize D (schemaFirst body) point
      (extend D (ContextualGraphRealizedFullness.image source target
          (ContextualGraphRealizedFullness.selection body (extend D parameter environment) source target input))
        (extend D parameter (extend D family (extend D target (extend D source environment))))) := by
  let collector := ContextualGraphRealizedFullness.image source target
    (ContextualGraphRealizedFullness.selection body (extend D parameter environment) source target input)
  intro future path value later tail member
  let arrived := move D tail value
  let available := Member.transportParent (Equal.ofEq (move_composition D path tail source).symm) member.down
  let selected := ContextualGraphRealizedFullness.forward body (extend D parameter environment)
    source target input later (path ≫ tail) arrived available
  refine ⟨selected.1, ⟨⟨Member.transportParent
    (Equal.ofEq (move_composition D path tail collector)) selected.2.1⟩, ?_⟩⟩
  have same : realize D (substitute subsetForwardIndices body) later
      (extend D selected.1 (moveEnvironment D tail (extend D value (moveEnvironment D path
        (extend D collector (extend D parameter (extend D family (extend D target (extend D source environment))))))))) =
      realize D body later
        (extend D selected.1 (extend D arrived (moveEnvironment D (path ≫ tail) (extend D parameter environment)))) := by
    simp only [moveEnvironment_extend]
    rw [realize_substitution, forwardEnvironment, ← moveEnvironment_composition, ← move_composition]
  exact same.symm ▸ selected.2.2

def secondClause (environment : Environment D count point)
    (source target family parameter : Value D point)
    (input : ContextualGraphRealizedFullness.Premise body (extend D parameter environment) source target) :
    realize D (schemaSecond body) point
      (extend D (ContextualGraphRealizedFullness.image source target
          (ContextualGraphRealizedFullness.selection body (extend D parameter environment) source target input))
        (extend D parameter (extend D family (extend D target (extend D source environment))))) := by
  let collector := ContextualGraphRealizedFullness.image source target
    (ContextualGraphRealizedFullness.selection body (extend D parameter environment) source target input)
  intro future path result later tail member
  let arrived := move D tail result
  let available := Member.transportParent (Equal.ofEq (move_composition D path tail collector).symm) member.down
  let selected := ContextualGraphRealizedFullness.backward body (extend D parameter environment)
    source target input later (path ≫ tail) arrived available
  refine ⟨selected.1, ⟨⟨Member.transportParent
    (Equal.ofEq (move_composition D path tail source)) selected.2.1⟩, ?_⟩⟩
  have same : realize D (substitute subsetBackwardIndices body) later
      (extend D selected.1 (moveEnvironment D tail (extend D result (moveEnvironment D path
        (extend D collector (extend D parameter (extend D family (extend D target (extend D source environment))))))))) =
      realize D body later
        (extend D arrived (extend D selected.1 (moveEnvironment D (path ≫ tail) (extend D parameter environment)))) := by
    simp only [moveEnvironment_extend]
    rw [realize_substitution, backwardEnvironment, ← moveEnvironment_composition, ← move_composition]
  exact same.symm ▸ selected.2.2

theorem image_transport {first second nextFirst nextSecond : Value D point}
    (sourceSame : first = nextFirst) (targetSame : second = nextSecond)
    (picked : ContextualGraphRealizedFullness.ChoiceCarrier nextFirst nextSecond) :
    ContextualGraphRealizedFullness.image first second
      ((congrArg₂ ContextualGraphRealizedFullness.ChoiceCarrier sourceSame targetSame).symm ▸ picked) =
      ContextualGraphRealizedFullness.image nextFirst nextSecond picked := by
  subst nextFirst
  subst nextSecond
  rfl

/-- The collecting family is constructed before the parameter, and the
same ordinary Subset Collection schema holds at every future context. -/
def subsetCollectionLaw (environment : Environment D count point) :
    realize D (subsetCollectionAxiom body) point environment := by
  intro first firstPath source second secondPath target
  let previous := move D secondPath source
  let assignment := moveEnvironment D secondPath (moveEnvironment D firstPath environment)
  let family := ContextualGraphRealizedFullness.fullness previous target
  refine ⟨family, ?_⟩
  intro parameterStage parameterPath parameter later tail premise
  simp only [moveEnvironment_extend] at premise ⊢
  let path := parameterPath ≫ tail
  let currentSource := move D tail (move D parameterPath previous)
  let currentTarget := move D tail (move D parameterPath target)
  let currentFamily := move D tail (move D parameterPath family)
  let currentParameter := move D tail parameter
  let currentAssignment := moveEnvironment D tail (moveEnvironment D parameterPath assignment)
  let input := schemaInput body currentAssignment currentSource currentTarget currentFamily currentParameter premise
  let picked := ContextualGraphRealizedFullness.selection body
    (extend D currentParameter currentAssignment) currentSource currentTarget input
  let collector := ContextualGraphRealizedFullness.image currentSource currentTarget picked
  refine ⟨collector, ⟨?_, firstClause body currentAssignment currentSource currentTarget currentFamily currentParameter input,
    secondClause body currentAssignment currentSource currentTarget currentFamily currentParameter input⟩⟩
  have sourceSame : move D path previous = currentSource := move_composition D parameterPath tail previous
  have targetSame : move D path target = currentTarget := move_composition D parameterPath tail target
  let normalizedSelection : ContextualGraphRealizedFullness.ChoiceCarrier
      (move D path previous) (move D path target) :=
    (congrArg₂ ContextualGraphRealizedFullness.ChoiceCarrier sourceSame targetSame).symm ▸ picked
  have imageSame : ContextualGraphRealizedFullness.image
      (move D path previous) (move D path target) normalizedSelection = collector :=
    image_transport sourceSame targetSame picked
  let available := ContextualGraphRealizedFullness.imageInFullness previous target later path normalizedSelection
  exact ⟨Member.transportParent (Equal.ofEq (move_composition D parameterPath tail family))
    (Member.transportChild (Equal.ofEq imageSame) available)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSubsetCollection
