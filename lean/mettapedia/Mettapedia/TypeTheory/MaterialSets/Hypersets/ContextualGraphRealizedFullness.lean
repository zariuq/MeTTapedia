import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGenerators
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetTheory

/-!
# Constructed future Subset Collection at the original bound

Complete future receipt functions form an original-small carrier. Each
function generates an image diagram, retaining the context and receipt
where each selected witness originated. A second original-small diagram
collects these images at every future context, before the relation or
its parameter is specified. Actual totality realizers select one image;
logical persistence and matching transport establish both Collection
clauses in every future. No powerset of the untyped value universe is
used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedFullness

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization
open ContextualMaterialLogic (substitute)
universe u
variable {D : Type u} [Category.{u} D] {point : D}

abbrev ChoiceCarrier (source target : Value D point) : Type u :=
  (future : D) → (path : point ⟶ future) →
    Child D (move D path source) → Child D (move D path target)

abbrev ImageOrigin (source : Value D point) : Type u :=
  Σ future : D, Σ path : point ⟶ future, Child D (move D path source)

def imageSource (source : Value D point) (origin : ImageOrigin source) : D := origin.1
def imageArrival (source : Value D point) (origin : ImageOrigin source) :
    point ⟶ imageSource source origin := origin.2.1

def imageWitness (source target : Value D point) (selection : ChoiceCarrier source target)
    (origin : ImageOrigin source) : Value D (imageSource source origin) :=
  childValue D (move D origin.2.1 target) (selection origin.1 origin.2.1 origin.2.2)

def imageRoot (source target : Value D point) (selection : ChoiceCarrier source target)
    (future : D) (path : point ⟶ future) : Value D future :=
  ContextualGraphGenerators.root (imageSource source) (imageArrival source)
    (imageWitness source target selection) path

def image (source target : Value D point) (selection : ChoiceCarrier source target) : Value D point :=
  imageRoot source target selection point (𝟙 point)

theorem image_move (source target : Value D point) (selection : ChoiceCarrier source target)
    (future : D) (path : point ⟶ future) :
    move D path (image source target selection) = imageRoot source target selection future path :=
  congrArg (fun arrow => imageRoot source target selection future arrow) (Category.id_comp path)

def imageSubset (source target : Value D point) (selection : ChoiceCarrier source target)
    (future : D) (path : point ⟶ future) (value : Value D future)
    (member : Member value (imageRoot source target selection future path)) :
    Member value (move D path target) := by
  let decoded := ContextualGraphGenerators.rootDecode (imageSource source) (imageArrival source)
    (imageWitness source target selection) path member.1
  let origin := decoded.1
  let tail := decoded.2.1
  have same := decoded.2.2.1.down
  let available := Member.restrict tail
    (Member.atChild (move D origin.2.1 target) (selection origin.1 origin.2.1 origin.2.2))
  have parentSame : move D tail (move D origin.2.1 target) = move D path target :=
    (move_composition D origin.2.1 tail target).symm.trans
      (congrArg (fun arrow => move D arrow target) same)
  exact Member.transportParent (Equal.ofEq parentSame)
    (Member.transportChild (member.2.trans decoded.2.2.2).symm available)

abbrev FamilyOrigin (source target : Value D point) : Type u :=
  Σ future : D, Σ path : point ⟶ future,
    ChoiceCarrier (move D path source) (move D path target)

def familySource (source target : Value D point) (origin : FamilyOrigin source target) : D := origin.1
def familyArrival (source target : Value D point) (origin : FamilyOrigin source target) :
    point ⟶ familySource source target origin := origin.2.1
def familyWitness (source target : Value D point) (origin : FamilyOrigin source target) :
    Value D (familySource source target origin) :=
  image (move D origin.2.1 source) (move D origin.2.1 target) origin.2.2

def familyRoot (source target : Value D point) (future : D) (path : point ⟶ future) : Value D future :=
  ContextualGraphGenerators.root (familySource source target) (familyArrival source target)
    (familyWitness source target) path

def fullness (source target : Value D point) : Value D point :=
  familyRoot source target point (𝟙 point)

theorem fullness_move (source target : Value D point) (future : D) (path : point ⟶ future) :
    move D path (fullness source target) = familyRoot source target future path :=
  congrArg (fun arrow => familyRoot source target future arrow) (Category.id_comp path)

def imageInFullness (source target : Value D point) (future : D) (path : point ⟶ future)
    (selection : ChoiceCarrier (move D path source) (move D path target)) :
    Member (image (move D path source) (move D path target) selection)
      (move D path (fullness source target)) :=
  let origin : FamilyOrigin source target := ⟨future, path, selection⟩
  let available := ContextualGraphGenerators.rootIntro (familySource source target)
    (familyArrival source target) (familyWitness source target) path origin (𝟙 future)
    (Category.comp_id path)
  Member.transportParent (Equal.ofEq (fullness_move source target future path).symm)
    (Member.transportChild (Equal.ofEq (move_identity D future _)) available)

variable {count : Nat} (body : Formula (count+2)) (environment : Environment D count point)
variable (source target : Value D point)

abbrev Premise : Type (u+1) :=
  (future : D) → (path : point ⟶ future) → (value : Value D future) →
    Member value (move D path source) →
      Σ result : Value D future, Member result (move D path target) ×
        realize D body future (extend D result (extend D value (moveEnvironment D path environment)))

variable (premise : Premise body environment source target)

def witnessAt (origin : ImageOrigin source) :
    Σ result : Value D origin.1, Member result (move D origin.2.1 target) ×
      realize D body origin.1 (extend D result
        (extend D (childValue D (move D origin.2.1 source) origin.2.2)
          (moveEnvironment D origin.2.1 environment))) :=
  premise origin.1 origin.2.1 (childValue D (move D origin.2.1 source) origin.2.2)
    (Member.atChild (move D origin.2.1 source) origin.2.2)

def selection : ChoiceCarrier source target :=
  fun future path child => (witnessAt body environment source target premise ⟨future, path, child⟩).2.1.1

def normalized (origin : ImageOrigin source) :
    realize D body origin.1 (extend D (imageWitness source target
      (selection body environment source target premise) origin)
      (extend D (childValue D (move D origin.2.1 source) origin.2.2)
        (moveEnvironment D origin.2.1 environment))) :=
  let selected := witnessAt body environment source target premise origin
  equalityTransport D body
    (extend D selected.1 (extend D (childValue D (move D origin.2.1 source) origin.2.2)
      (moveEnvironment D origin.2.1 environment)))
    (extend D (childValue D (move D origin.2.1 target) selected.2.1.1)
      (extend D (childValue D (move D origin.2.1 source) origin.2.2)
        (moveEnvironment D origin.2.1 environment)))
    (Fin.cases selected.2.1.2 (Fin.cases (Equal.refl _)
      (fun index => Equal.refl (move D origin.2.1 (environment index))))) selected.2.2

def forwardRoot (future : D) (path : point ⟶ future) (value : Value D future)
    (member : Member value (move D path source)) :
    Σ result : Value D future, Member result (imageRoot source target
      (selection body environment source target premise) future path) ×
      realize D body future (extend D result (extend D value (moveEnvironment D path environment))) := by
  let origin : ImageOrigin source := ⟨future, path, member.1⟩
  let result := imageWitness source target (selection body environment source target premise) origin
  let available := ContextualGraphGenerators.rootIntro (imageSource source) (imageArrival source)
    (imageWitness source target (selection body environment source target premise)) path origin (𝟙 future)
    (Category.comp_id path)
  refine ⟨result, Member.transportChild (Equal.ofEq (move_identity D future result)) available, ?_⟩
  exact equalityTransport D body
    (extend D result (extend D (childValue D (move D path source) member.1) (moveEnvironment D path environment)))
    (extend D result (extend D value (moveEnvironment D path environment)))
    (Fin.cases (Equal.refl result) (Fin.cases member.2.symm
      (fun index => Equal.refl (move D path (environment index)))))
    (normalized body environment source target premise origin)

def backwardRoot (future : D) (path : point ⟶ future) (result : Value D future)
    (member : Member result (imageRoot source target
      (selection body environment source target premise) future path)) :
    Σ value : Value D future, Member value (move D path source) ×
      realize D body future (extend D result (extend D value (moveEnvironment D path environment))) := by
  let decoded := ContextualGraphGenerators.rootDecode (imageSource source) (imageArrival source)
    (imageWitness source target (selection body environment source target premise)) path member.1
  let origin := decoded.1
  let tail := decoded.2.1
  have pathSame := decoded.2.2.1.down
  let original := childValue D (move D origin.2.1 source) origin.2.2
  let value := move D tail original
  let selected := imageWitness source target (selection body environment source target premise) origin
  let transported := move D tail selected
  have same : Equal result transported := member.2.trans decoded.2.2.2
  have parentSame : move D tail (move D origin.2.1 source) = move D path source :=
    (move_composition D origin.2.1 tail source).symm.trans
      (congrArg (fun arrow => move D arrow source) pathSame)
  let available := Member.transportParent (Equal.ofEq parentSame)
    (Member.restrict tail (Member.atChild (move D origin.2.1 source) origin.2.2))
  refine ⟨value, available, ?_⟩
  have evidence := persistence D body tail
    (extend D selected (extend D original (moveEnvironment D origin.2.1 environment)))
    (normalized body environment source target premise origin)
  have assignmentSame :
      moveEnvironment D tail (extend D selected (extend D original (moveEnvironment D origin.2.1 environment))) =
      extend D transported (extend D value (moveEnvironment D path environment)) := by
    exact (moveEnvironment_extend D tail selected (extend D original (moveEnvironment D origin.2.1 environment))).trans
      (congrArg (extend D transported)
        ((moveEnvironment_extend D tail original (moveEnvironment D origin.2.1 environment)).trans
          (congrArg (extend D value)
            ((moveEnvironment_composition D origin.2.1 tail environment).symm.trans
              (congrArg (fun arrow => moveEnvironment D arrow environment) pathSame)))))
  have normalizedEvidence : realize D body future
      (extend D transported (extend D value (moveEnvironment D path environment))) := assignmentSame ▸ evidence
  exact equalityTransport D body
    (extend D transported (extend D value (moveEnvironment D path environment)))
    (extend D result (extend D value (moveEnvironment D path environment)))
    (Fin.cases same.symm (Fin.cases (Equal.refl value)
      (fun index => Equal.refl (move D path (environment index))))) normalizedEvidence

def forward (future : D) (path : point ⟶ future) (value : Value D future)
    (member : Member value (move D path source)) :
    Σ result : Value D future, Member result (move D path
      (image source target (selection body environment source target premise))) ×
      realize D body future (extend D result (extend D value (moveEnvironment D path environment))) :=
  let packet := forwardRoot body environment source target premise future path value member
  ⟨packet.1, Member.transportParent (Equal.ofEq (image_move source target
    (selection body environment source target premise) future path).symm) packet.2.1, packet.2.2⟩

def backward (future : D) (path : point ⟶ future) (result : Value D future)
    (member : Member result (move D path
      (image source target (selection body environment source target premise)))) :
    Σ value : Value D future, Member value (move D path source) ×
      realize D body future (extend D result (extend D value (moveEnvironment D path environment))) :=
  backwardRoot body environment source target premise future path result
    (Member.transportParent (Equal.ofEq (image_move source target
      (selection body environment source target premise) future path)) member)

def subsetCollection (future : D) (path : point ⟶ future)
    (input : Premise body (moveEnvironment D path environment)
      (move D path source) (move D path target)) :
    Σ collector : Value D future, Member collector (move D path (fullness source target)) ×
      ((later : D) → (tail : future ⟶ later) → (value : Value D later) →
        Member value (move D tail (move D path source)) →
          Σ result : Value D later, Member result (move D tail collector) ×
            realize D body later (extend D result
              (extend D value (moveEnvironment D tail (moveEnvironment D path environment))))) ×
      ((later : D) → (tail : future ⟶ later) → (result : Value D later) →
        Member result (move D tail collector) →
          Σ value : Value D later, Member value (move D tail (move D path source)) ×
            realize D body later (extend D result
              (extend D value (moveEnvironment D tail (moveEnvironment D path environment))))) ×
      ((later : D) → (tail : future ⟶ later) → (result : Value D later) →
        Member result (move D tail collector) → Member result (move D tail (move D path target))) :=
  let picked := selection body (moveEnvironment D path environment) (move D path source) (move D path target) input
  ⟨image (move D path source) (move D path target) picked,
    imageInFullness source target future path picked,
    forward body (moveEnvironment D path environment) (move D path source) (move D path target) input,
    backward body (moveEnvironment D path environment) (move D path source) (move D path target) input,
    fun later tail result member => imageSubset (move D path source) (move D path target) picked later tail result
      (Member.transportParent (Equal.ofEq (image_move (move D path source) (move D path target) picked later tail)) member)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedFullness
