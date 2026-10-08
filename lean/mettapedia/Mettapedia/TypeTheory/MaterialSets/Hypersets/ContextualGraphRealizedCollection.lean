import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGenerators
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSetTheory

/-!
# Full Strong Collection in the varying realized graph model

The full-future totality realizer supplies one constructed witness for
each original-small source occurrence. The collector is an actual value
of the same untyped contextual graph universe. It retains all witness
origins and terminal arrows, so no coherent witness selection is needed.

Both first-order clauses hold at every future and actual context arrow.
Arbitrary formula bodies, including implication and unbounded quantifiers,
are transported using the realized logical persistence theorem. The
collector's node carrier stays in the original universe; its index never
ranges over all graph values or all full-formula realizers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedCollection

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization
universe u
variable {D : Type u} [Category.{u} D] {point : D} {count : Nat}
variable (body : Formula (count+2)) (environment : Environment D count point)
variable (parent : Value D point)

abbrev Witness (target : D) (assignment : Environment D count target) (value : Value D target) :
    Type (u+1) := Σ result : Value D target,
      realize D body target (extend D result (extend D value assignment))

abbrev Premise : Type (u+1) :=
  (target : D) → (arrival : point ⟶ target) → (value : Value D target) →
    Member value (move D arrival parent) →
      Witness body target (moveEnvironment D arrival environment) value

abbrev Origin : Type u := Σ target : D, Σ arrival : point ⟶ target,
  ContextualGraphDiagrams.Child D (move D arrival parent)

def source (origin : Origin parent) : D := origin.1
def arrival (origin : Origin parent) : point ⟶ source parent origin := origin.2.1

def sourceValue (origin : Origin parent) : Value D (source parent origin) :=
  childValue D (move D origin.2.1 parent) origin.2.2

variable (premise : Premise body environment parent)

def chosen (origin : Origin parent) :
    Witness body (source parent origin) (moveEnvironment D (arrival parent origin) environment)
      (sourceValue parent origin) :=
  premise (source parent origin) (arrival parent origin) (sourceValue parent origin)
    (Member.atChild (move D (arrival parent origin) parent) origin.2.2)

def witnessValue (origin : Origin parent) : Value D (source parent origin) :=
  (chosen body environment parent premise origin).1

def collector : Value D point :=
  ContextualGraphGenerators.root (source parent) (arrival parent)
    (witnessValue body environment parent premise) (𝟙 point)

def root (target : D) (path : point ⟶ target) : Value D target :=
  ContextualGraphGenerators.root (source parent) (arrival parent)
    (witnessValue body environment parent premise) path

theorem collector_move (target : D) (path : point ⟶ target) :
    move D path (collector body environment parent premise) =
      root body environment parent premise target path :=
  congrArg (fun pathValue => ContextualGraphGenerators.root (source parent) (arrival parent)
    (witnessValue body environment parent premise) pathValue) (Category.id_comp path)

def forwardRoot (target : D) (path : point ⟶ target) (value : Value D target)
    (member : Member value (move D path parent)) :
    Σ result : Value D target, Member result (root body environment parent premise target path) ×
      realize D body target (extend D result (extend D value (moveEnvironment D path environment))) :=
  let origin : Origin parent := ⟨target, path, member.1⟩
  let selected := chosen body environment parent premise origin
  let available := ContextualGraphGenerators.rootIntro (source parent) (arrival parent)
    (witnessValue body environment parent premise) path origin (𝟙 target) (Category.comp_id path)
  ⟨selected.1, Member.transportChild (Equal.ofEq (move_identity D target selected.1)) available,
    equalityTransport D body
      (extend D selected.1 (extend D (sourceValue parent origin) (moveEnvironment D path environment)))
      (extend D selected.1 (extend D value (moveEnvironment D path environment)))
      (Fin.cases (Equal.refl selected.1)
        (Fin.cases member.2.symm (fun index => Equal.refl (move D path (environment index))))) selected.2⟩

theorem transportedSource {target : D} (origin : Origin parent)
    (tail : source parent origin ⟶ target) (path : point ⟶ target)
    (same : arrival parent origin ≫ tail = path) :
    move D tail (move D (arrival parent origin) parent) = move D path parent :=
  (move_composition D (arrival parent origin) tail parent).symm.trans
    (congrArg (fun arrow => move D arrow parent) same)

def backwardRoot (target : D) (path : point ⟶ target) (result : Value D target)
    (member : Member result (root body environment parent premise target path)) :
    Σ value : Value D target, Member value (move D path parent) ×
      realize D body target (extend D result (extend D value (moveEnvironment D path environment))) := by
  let decoded := ContextualGraphGenerators.rootDecode (source parent) (arrival parent)
    (witnessValue body environment parent premise) path member.1
  let origin := decoded.1
  let tail := decoded.2.1
  have pathSame := decoded.2.2.1.down
  let selected := chosen body environment parent premise origin
  let value := move D tail (sourceValue parent origin)
  let sourceMember := Member.restrict tail
    (Member.atChild (move D (arrival parent origin) parent) origin.2.2)
  refine ⟨value, Member.transportParent
    (Equal.ofEq (transportedSource parent origin tail path pathSame)) sourceMember, ?_⟩
  have transported := persistence D body tail
    (extend D selected.1 (extend D (sourceValue parent origin)
      (moveEnvironment D (arrival parent origin) environment))) selected.2
  have assignmentSame :
      moveEnvironment D tail (extend D selected.1 (extend D (sourceValue parent origin)
        (moveEnvironment D (arrival parent origin) environment))) =
      extend D (move D tail selected.1) (extend D value (moveEnvironment D path environment)) := by
    rw [moveEnvironment_extend, moveEnvironment_extend, ← moveEnvironment_composition, pathSame]
  have normalized : realize D body target
      (extend D (move D tail selected.1) (extend D value (moveEnvironment D path environment))) :=
    assignmentSame ▸ transported
  have resultSame : Equal result (move D tail selected.1) := member.2.trans decoded.2.2.2
  exact equalityTransport D body
    (extend D (move D tail selected.1) (extend D value (moveEnvironment D path environment)))
    (extend D result (extend D value (moveEnvironment D path environment)))
    (Fin.cases resultSame.symm (fun index => Equal.refl (extend D value (moveEnvironment D path environment) index)))
    normalized

def forward (target : D) (path : point ⟶ target) (value : Value D target)
    (member : Member value (move D path parent)) :
    Σ result : Value D target, Member result (move D path (collector body environment parent premise)) ×
      realize D body target (extend D result (extend D value (moveEnvironment D path environment))) :=
  let selected := forwardRoot body environment parent premise target path value member
  ⟨selected.1, Member.transportParent
    (Equal.ofEq (collector_move body environment parent premise target path).symm) selected.2.1,
    selected.2.2⟩

def backward (target : D) (path : point ⟶ target) (result : Value D target)
    (member : Member result (move D path (collector body environment parent premise))) :
    Σ value : Value D target, Member value (move D path parent) ×
      realize D body target (extend D result (extend D value (moveEnvironment D path environment))) :=
  backwardRoot body environment parent premise target path result
    (Member.transportParent (Equal.ofEq (collector_move body environment parent premise target path)) member)

/-- The constructed object and both full-future Collection clauses. -/
def strongCollection :
    Σ collected : Value D point,
      ((target : D) → (path : point ⟶ target) → (value : Value D target) →
        Member value (move D path parent) →
          Σ result : Value D target, Member result (move D path collected) ×
            realize D body target (extend D result (extend D value (moveEnvironment D path environment)))) ×
      ((target : D) → (path : point ⟶ target) → (result : Value D target) →
        Member result (move D path collected) →
          Σ value : Value D target, Member value (move D path parent) ×
            realize D body target (extend D result (extend D value (moveEnvironment D path environment)))) :=
  ⟨collector body environment parent premise,
    forward body environment parent premise, backward body environment parent premise⟩

def fromFirstOrderPremise (parentIndex : Fin count)
    (proof : realize D (.all (.imply (.member 0 parentIndex.succ) (.exist body))) point environment) :
    Premise body environment (environment parentIndex) := by
  intro target path value member
  have current := proof target path value target (𝟙 target)
  rw [moveEnvironment_identity] at current
  exact current ⟨member⟩

theorem discardOne {target : D} (assignment : Environment D count target)
    (parent value result : Value D target) :
    extend D result (extend D value (extend D parent assignment)) ∘
      ContextualMaterialFormulaSemantics.behindTwoOne =
        extend D result (extend D value assignment) := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

theorem discardTwo {target : D} (assignment : Environment D count target)
    (parent collector value result : Value D target) :
    extend D result (extend D value (extend D collector (extend D parent assignment))) ∘
      ContextualMaterialFormulaSemantics.behindTwoTwo =
        extend D result (extend D value assignment) := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

theorem swappedDiscardTwo {target : D} (assignment : Environment D count target)
    (parent collector result value : Value D target) :
    extend D value (extend D result (extend D collector (extend D parent assignment))) ∘
      ContextualMaterialFormulaSemantics.swappedBehindTwoTwo =
        extend D result (extend D value assignment) := by
  funext index
  exact Fin.cases rfl (fun remaining => Fin.cases rfl (fun _ => rfl) remaining) index

def schemaInput {target : D} (assignment : Environment D count target) (parent : Value D target)
    (proof : realize D (ContextualMaterialSetTheory.collectionPremise body) target (extend D parent assignment)) :
    Premise body assignment parent := by
  intro future path value member
  have current := proof future path value future (𝟙 future)
  rw [moveEnvironment_identity] at current
  let selected : Σ result : Value D future,
      realize D (ContextualMaterialLogic.substitute ContextualMaterialFormulaSemantics.behindTwoOne body)
        future (extend D result (extend D value (moveEnvironment D path (extend D parent assignment)))) :=
    current ⟨member⟩
  refine ⟨selected.1, ?_⟩
  have same : realize D
      (ContextualMaterialLogic.substitute ContextualMaterialFormulaSemantics.behindTwoOne body) future
      (extend D selected.1 (extend D value (moveEnvironment D path (extend D parent assignment)))) =
      realize D body future (extend D selected.1 (extend D value (moveEnvironment D path assignment))) := by
    generalize selected.1 = result
    rw [moveEnvironment_extend, realize_substitution, discardOne]
  exact same ▸ selected.2

def schemaFirst {target : D} (assignment : Environment D count target) (parent : Value D target)
    (proof : Premise body assignment parent) :
    realize D (ContextualMaterialSetTheory.collectionFirst body) target
      (extend D (collector body assignment parent proof) (extend D parent assignment)) := by
  intro future path value later tail member
  let arrived := move D tail value
  have parentSame := (move_composition D path tail parent).symm
  let available := Member.transportParent (Equal.ofEq parentSame) member.down
  let selected := forward body assignment parent proof later (path ≫ tail) arrived available
  refine ⟨selected.1, ⟨⟨Member.transportParent
    (Equal.ofEq (move_composition D path tail (collector body assignment parent proof))) selected.2.1⟩, ?_⟩⟩
  have same : realize D
      (ContextualMaterialLogic.substitute ContextualMaterialFormulaSemantics.behindTwoTwo body) later
      (extend D selected.1 (moveEnvironment D tail (extend D value (moveEnvironment D path
        (extend D (collector body assignment parent proof) (extend D parent assignment)))))) =
      realize D body later (extend D selected.1 (extend D arrived (moveEnvironment D (path ≫ tail) assignment))) := by
    simp only [moveEnvironment_extend]
    rw [realize_substitution, discardTwo, ← moveEnvironment_composition]
  exact same.symm ▸ selected.2.2

def schemaSecond {target : D} (assignment : Environment D count target) (parent : Value D target)
    (proof : Premise body assignment parent) :
    realize D (ContextualMaterialSetTheory.collectionSecond body) target
      (extend D (collector body assignment parent proof) (extend D parent assignment)) := by
  intro future path result later tail member
  let arrived := move D tail result
  have collectorSame := (move_composition D path tail (collector body assignment parent proof)).symm
  let available := Member.transportParent (Equal.ofEq collectorSame) member.down
  let selected := backward body assignment parent proof later (path ≫ tail) arrived available
  refine ⟨selected.1, ⟨⟨Member.transportParent
    (Equal.ofEq (move_composition D path tail parent)) selected.2.1⟩, ?_⟩⟩
  have same : realize D
      (ContextualMaterialLogic.substitute ContextualMaterialFormulaSemantics.swappedBehindTwoTwo body) later
      (extend D selected.1 (moveEnvironment D tail (extend D result (moveEnvironment D path
        (extend D (collector body assignment parent proof) (extend D parent assignment)))))) =
      realize D body later (extend D arrived (extend D selected.1 (moveEnvironment D (path ≫ tail) assignment))) := by
    simp only [moveEnvironment_extend]
    rw [realize_substitution, swappedDiscardTwo, ← moveEnvironment_composition]
  exact same.symm ▸ selected.2.2

/-- The ordinary full first-order Strong Collection schema, validated in
the varying universe at every context and assignment. -/
def strongCollectionLaw :
    realize D (ContextualMaterialSetTheory.strongCollectionAxiom body) point environment := by
  intro source initialPath parent target path premise
  rw [moveEnvironment_extend] at premise ⊢
  let assignment := moveEnvironment D path (moveEnvironment D initialPath environment)
  let transportedParent := move D path parent
  let input := schemaInput body assignment transportedParent premise
  exact ⟨collector body assignment transportedParent input,
    schemaFirst body assignment transportedParent input, schemaSecond body assignment transportedParent input⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedCollection
