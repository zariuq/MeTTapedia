import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedCollection

/-!
# Original-bound Subset Collection from receipt function spaces

For fixed sets `a` and `b`, the small carrier of functions from the root
children of `a` to the root children of `b` generates a set of witness
images. This set is independent of the relation formula and its parameters.
A realized total relation computes one such function from its actual
witnesses. Its image supplies both clauses of Strong Collection and stays
inside `b`. Duplicate source receipts are retained; no extensional choice
function on the material quotient is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedFullness

open GraphBisimulationRealizers GraphSetRealization GraphFormulaRealization

universe u

abbrev ChoiceCarrier (source target : Graph.{u}) : Type u :=
  Child source.edge source.point → Child target.edge target.point

def image (source target : Graph.{u}) (selection : ChoiceCarrier source target) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun child : Child source.edge source.point =>
    target.repoint (selection child).val)

/-- One original-small set of images works for every realized relation. -/
def fullness (source target : Graph.{u}) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun selection : ChoiceCarrier source target => image source target selection)

def imageInFullness (source target : Graph.{u}) (selection : ChoiceCarrier source target) :
    Member (image source target selection) (fullness source target) :=
  Sup.intro _ selection (Equal.refl _)

def imageSubset {source target : Graph.{u}} (selection : ChoiceCarrier source target)
    {value : Graph.{u}} (member : Member value (image source target selection)) : Member value target :=
  let decoded := Sup.eliminate _ member
  ⟨selection decoded.1, decoded.2⟩

variable {count : Nat} (body : Formula (count+2)) (environment : Environment.{u} count)
variable (source target : Graph.{u})

abbrev Premise : Type (u+1) :=
  (value : Graph.{u}) → Member value source →
    Σ result : Graph.{u}, Member result target × realize body (extend result (extend value environment))

variable (premise : Premise body environment source target)

def witnessAt (child : Child source.edge source.point) :
    Σ result : Graph.{u}, Member result target ×
      realize body (extend result (extend (source.repoint child.val) environment)) :=
  premise (source.repoint child.val) (Member.atChild source child)

def selection : ChoiceCarrier source target :=
  fun child => (witnessAt body environment source target premise child).2.1.1

def normalized (child : Child source.edge source.point) :
    realize body
      (extend (target.repoint (selection body environment source target premise child).val)
        (extend (source.repoint child.val) environment)) :=
  let witness := witnessAt body environment source target premise child
  GraphFormulaRealization.transport body (extend witness.1 (extend (source.repoint child.val) environment))
    (extend (target.repoint witness.2.1.1.val) (extend (source.repoint child.val) environment))
    (Fin.cases witness.2.1.2 (Fin.cases (Equal.refl _) (fun index => Equal.refl (environment index))))
    witness.2.2

def forward (value : Graph.{u}) (member : Member value source) :
    Σ result : Graph.{u},
      Member result (image source target (selection body environment source target premise)) ×
      realize body (extend result (extend value environment)) :=
  let result := target.repoint (selection body environment source target premise member.1).val
  ⟨result, Sup.intro _ member.1 (Equal.refl result),
    GraphFormulaRealization.transport body (extend result (extend (source.repoint member.1.val) environment))
      (extend result (extend value environment))
      (Fin.cases (Equal.refl result)
        (Fin.cases member.2.symm (fun index => Equal.refl (environment index))))
      (normalized body environment source target premise member.1)⟩

def backward (result : Graph.{u})
    (member : Member result (image source target (selection body environment source target premise))) :
    Σ value : Graph.{u}, Member value source × realize body (extend result (extend value environment)) :=
  let decoded := Sup.eliminate _ member
  ⟨source.repoint decoded.1.val, Member.atChild source decoded.1,
    GraphFormulaRealization.transport body
      (extend (target.repoint (selection body environment source target premise decoded.1).val)
        (extend (source.repoint decoded.1.val) environment))
      (extend result (extend (source.repoint decoded.1.val) environment))
      (Fin.cases decoded.2.symm
        (Fin.cases (Equal.refl _) (fun index => Equal.refl (environment index))))
      (normalized body environment source target premise decoded.1)⟩

/-- The image comes from one fixed small family, with both Collection
clauses and the explicit inclusion into the target set. -/
def subsetCollection :
    Σ collector : Graph.{u}, Member collector (fullness source target) ×
      ((value : Graph.{u}) → Member value source →
        Σ result : Graph.{u}, Member result collector × realize body (extend result (extend value environment))) ×
      ((result : Graph.{u}) → Member result collector →
        Σ value : Graph.{u}, Member value source × realize body (extend result (extend value environment))) ×
      ((result : Graph.{u}) → Member result collector → Member result target) :=
  ⟨image source target (selection body environment source target premise),
    imageInFullness source target (selection body environment source target premise),
    forward body environment source target premise,
    backward body environment source target premise,
    fun _ member => imageSubset (selection body environment source target premise) member⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedFullness
