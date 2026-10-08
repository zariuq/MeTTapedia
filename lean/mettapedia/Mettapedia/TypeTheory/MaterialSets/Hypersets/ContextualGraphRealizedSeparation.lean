import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGenerators
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphBoundedRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSetTheory

/-!
# Constructed original-small bounded Separation

The separating diagram retains every past member occurrence together
with its original-small bounded realizer. Its root edges record the exact
arrival factorization. Bounded logical persistence carries the evidence
to later contexts; full future equality transports it to other member
presentations. Both directions are proved for the ordinary guarded
first-order Separation schema.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSeparation

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization (Environment extend moveEnvironment)
open GraphBoundedFormulaRealization (BoundedFormula toFormula)
universe u
variable {D : Type u} [Category.{u} D] {point : D} {count : Nat}
variable (body : BoundedFormula (count+1)) (environment : Environment D count point)
variable (parent : Value D point)

abbrev Origin : Type u :=
  Σ target : D, Σ path : point ⟶ target,
    Σ child : ContextualGraphDiagrams.Child D (move D path parent),
      ContextualGraphBoundedRealization.realize D body target
        (extend D (childValue D (move D path parent) child) (moveEnvironment D path environment))

def source (origin : Origin body environment parent) : D := origin.1
def arrival (origin : Origin body environment parent) : point ⟶ source body environment parent origin := origin.2.1
def witnessValue (origin : Origin body environment parent) : Value D (source body environment parent origin) :=
  childValue D (move D origin.2.1 parent) origin.2.2.1

def root (target : D) (path : point ⟶ target) : Value D target :=
  ContextualGraphGenerators.root (source body environment parent) (arrival body environment parent)
    (witnessValue body environment parent) path

def separated : Value D point := root body environment parent point (𝟙 point)

theorem separated_move (target : D) (path : point ⟶ target) :
    move D path (separated body environment parent) = root body environment parent target path :=
  congrArg (fun pathValue => root body environment parent target pathValue) (Category.id_comp path)

def forwardRoot (target : D) (path : point ⟶ target) (value : Value D target)
    (member : Member value (root body environment parent target path)) :
    Member value (move D path parent) ×
      ContextualGraphBoundedRealization.realize D body target
        (extend D value (moveEnvironment D path environment)) := by
  let decoded := ContextualGraphGenerators.rootDecode (source body environment parent)
    (arrival body environment parent) (witnessValue body environment parent) path member.1
  let origin := decoded.1
  let tail := decoded.2.1
  have pathSame := decoded.2.2.1.down
  let original := witnessValue body environment parent origin
  let transported := move D tail original
  have same : Equal value transported := member.2.trans decoded.2.2.2
  have parentSame : move D tail (move D origin.2.1 parent) = move D path parent :=
    (move_composition D origin.2.1 tail parent).symm.trans
      (congrArg (fun arrow => move D arrow parent) pathSame)
  let available := Member.transportParent (Equal.ofEq parentSame)
    (Member.restrict tail (Member.atChild (move D origin.2.1 parent) origin.2.2.1))
  refine ⟨Member.transportChild same.symm available, ?_⟩
  have evidence := ContextualGraphBoundedRealization.persistence D body tail
    (extend D original (moveEnvironment D origin.2.1 environment)) origin.2.2.2
  have assignmentSame :
      moveEnvironment D tail (extend D original (moveEnvironment D origin.2.1 environment)) =
      extend D transported (moveEnvironment D path environment) := by
    exact (ContextualGraphFormulaRealization.moveEnvironment_extend D tail original
      (moveEnvironment D origin.2.1 environment)).trans
      (congrArg (fun assignment => extend D transported assignment)
        ((ContextualGraphFormulaRealization.moveEnvironment_composition D origin.2.1 tail environment).symm.trans
          (congrArg (fun arrow => moveEnvironment D arrow environment) pathSame)))
  have normalized : ContextualGraphBoundedRealization.realize D body target
      (extend D transported (moveEnvironment D path environment)) := assignmentSame ▸ evidence
  exact ContextualGraphBoundedRealization.equalityTransport D body
    (extend D transported (moveEnvironment D path environment))
    (extend D value (moveEnvironment D path environment))
    (Fin.cases same.symm (fun index => Equal.refl (move D path (environment index)))) normalized

def backwardRoot (target : D) (path : point ⟶ target) (value : Value D target)
    (member : Member value (move D path parent))
    (proof : ContextualGraphBoundedRealization.realize D body target
      (extend D value (moveEnvironment D path environment))) :
    Member value (root body environment parent target path) :=
  let canonical := childValue D (move D path parent) member.1
  let retained := ContextualGraphBoundedRealization.equalityTransport D body
    (extend D value (moveEnvironment D path environment))
    (extend D canonical (moveEnvironment D path environment))
    (Fin.cases member.2 (fun index => Equal.refl (move D path (environment index)))) proof
  let origin : Origin body environment parent := ⟨target, path, member.1, retained⟩
  let available := ContextualGraphGenerators.rootIntro (source body environment parent)
    (arrival body environment parent) (witnessValue body environment parent)
    path origin (𝟙 target) (Category.comp_id path)
  Member.transportChild ((Equal.ofEq (move_identity D target canonical)).trans member.2.symm) available

def forward (target : D) (path : point ⟶ target) (value : Value D target)
    (member : Member value (move D path (separated body environment parent))) :
    Member value (move D path parent) ×
      ContextualGraphBoundedRealization.realize D body target
        (extend D value (moveEnvironment D path environment)) :=
  forwardRoot body environment parent target path value
    (Member.transportParent (Equal.ofEq (separated_move body environment parent target path)) member)

def backward (target : D) (path : point ⟶ target) (value : Value D target)
    (member : Member value (move D path parent))
    (proof : ContextualGraphBoundedRealization.realize D body target
      (extend D value (moveEnvironment D path environment))) :
    Member value (move D path (separated body environment parent)) :=
  Member.transportParent (Equal.ofEq (separated_move body environment parent target path).symm)
    (backwardRoot body environment parent target path value member proof)

theorem discardHeadTwo {target : D} (assignment : Environment D count target)
    (parent subset value : Value D target) :
    extend D value (extend D subset (extend D parent assignment)) ∘
      ContextualMaterialFormulaSemantics.behindHeadTwo = extend D value assignment := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

def separationLaw :
    ContextualGraphFormulaRealization.realize D (ContextualMaterialSetTheory.separationAxiom (toFormula body))
      point environment := by
  intro source initialPath parent
  let assignment := moveEnvironment D initialPath environment
  let subset := separated body assignment parent
  refine ⟨subset, ?_⟩
  intro future path value
  constructor
  · intro later tail member
    let arrived := move D tail value
    let available := Member.transportParent (Equal.ofEq (move_composition D path tail subset).symm) member.down
    let packet := forward body assignment parent later (path ≫ tail) arrived available
    refine ⟨⟨Member.transportParent (Equal.ofEq (move_composition D path tail parent)) packet.1⟩, ?_⟩
    have same : ContextualGraphFormulaRealization.realize D
        (ContextualMaterialLogic.substitute ContextualMaterialFormulaSemantics.behindHeadTwo (toFormula body)) later
        (moveEnvironment D tail (extend D value (moveEnvironment D path (extend D subset (extend D parent assignment))))) =
        ContextualGraphFormulaRealization.realize D (toFormula body) later
          (extend D arrived (moveEnvironment D (path ≫ tail) assignment)) := by
      simp only [ContextualGraphFormulaRealization.moveEnvironment_extend]
      rw [ContextualGraphFormulaRealization.realize_substitution, discardHeadTwo,
        ← ContextualGraphFormulaRealization.moveEnvironment_composition]
    exact same.symm ▸ ContextualGraphBoundedRealization.toFull D body later _ packet.2
  · intro later tail packet
    let arrived := move D tail value
    let available := Member.transportParent (Equal.ofEq (move_composition D path tail parent).symm) packet.1.down
    have same : ContextualGraphFormulaRealization.realize D
        (ContextualMaterialLogic.substitute ContextualMaterialFormulaSemantics.behindHeadTwo (toFormula body)) later
        (moveEnvironment D tail (extend D value (moveEnvironment D path (extend D subset (extend D parent assignment))))) =
        ContextualGraphFormulaRealization.realize D (toFormula body) later
          (extend D arrived (moveEnvironment D (path ≫ tail) assignment)) := by
      simp only [ContextualGraphFormulaRealization.moveEnvironment_extend]
      rw [ContextualGraphFormulaRealization.realize_substitution, discardHeadTwo,
        ← ContextualGraphFormulaRealization.moveEnvironment_composition]
    let bounded := ContextualGraphBoundedRealization.toFull.fromFull D body later _ (same ▸ packet.2)
    exact ⟨Member.transportParent (Equal.ofEq (move_composition D path tail subset))
      (backward body assignment parent later (path ≫ tail) arrived available bounded)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSeparation
