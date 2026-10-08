import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphFormulaRealization

/-!
# Strong Collection from the actual realized logical premise

The premise is a realizer of `∀x (x ∈ a → ∃y φ(x,y))` in the ordinary
first-order syntax. The existential is interpreted by a dependent sum,
so this premise contains a graph witness and a formula realizer at every
actual member input. The collecting graph is the disjoint union of the
witness graphs for the original-small root-child carrier of `a`.

Both Collection clauses are constructed for arbitrary graph members.
Formula equality transport handles members represented by other graphs
and duplicate child receipts. The body may contain arbitrary unbounded
quantifiers; only the collected witness index, not its formula-realizer
type, must be original-small.

This theorem concerns Type-valued logical realization. It does not turn
an erased `∀x, Nonempty (...)` premise into dependent-sum witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedCollection

open GraphBisimulationRealizers GraphSetRealization GraphFormulaRealization

universe u

variable {count : Nat} (body : Formula (count+2)) (environment : Environment.{u} count)
variable (parent : Graph.{u})

abbrev Witness (value : Graph.{u}) : Type (u+1) :=
  Σ result : Graph.{u}, realize body (extend result (extend value environment))

variable (premise : ∀ value : Graph.{u}, Member value parent → Witness body environment value)

def childWitness (child : Child parent.edge parent.point) :
    Witness body environment (parent.repoint child.val) :=
  premise (parent.repoint child.val) (Member.atChild parent child)

/-- The collecting index is exactly the original child carrier. -/
def collected : Graph.{u} :=
  AccessiblePointedGraph.sup (fun child : Child parent.edge parent.point =>
    (childWitness body environment parent premise child).1)

def forward (value : Graph.{u}) (member : Member value parent) :
    Σ result : Graph.{u}, Member result (collected body environment parent premise) ×
      realize body (extend result (extend value environment)) :=
  let selected := childWitness body environment parent premise member.1
  ⟨selected.1, Sup.intro _ member.1 (Equal.refl selected.1),
    GraphFormulaRealization.transport body (extend selected.1 (extend (parent.repoint member.1.val) environment))
      (extend selected.1 (extend value environment))
      (Fin.cases (Equal.refl selected.1)
        (Fin.cases member.2.symm (fun index => Equal.refl (environment index)))) selected.2⟩

def backward (result : Graph.{u}) (member : Member result (collected body environment parent premise)) :
    Σ value : Graph.{u}, Member value parent × realize body (extend result (extend value environment)) :=
  let decoded := Sup.eliminate _ member
  let selected := childWitness body environment parent premise decoded.1
  ⟨parent.repoint decoded.1.val, Member.atChild parent decoded.1,
    GraphFormulaRealization.transport body (extend selected.1 (extend (parent.repoint decoded.1.val) environment))
      (extend result (extend (parent.repoint decoded.1.val) environment))
      (Fin.cases decoded.2.symm
        (Fin.cases (Equal.refl (parent.repoint decoded.1.val))
          (fun index => Equal.refl (environment index)))) selected.2⟩

/-- Strong Collection, with both clauses and no selected erased witnesses. -/
def strongCollection :
    Σ collector : Graph.{u},
      ((value : Graph.{u}) → Member value parent →
        Σ result : Graph.{u}, Member result collector ×
          realize body (extend result (extend value environment))) ×
      ((result : Graph.{u}) → Member result collector →
        Σ value : Graph.{u}, Member value parent ×
          realize body (extend result (extend value environment))) :=
  ⟨collected body environment parent premise,
    forward body environment parent premise, backward body environment parent premise⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedCollection

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedCollection

open GraphSetRealization GraphFormulaRealization

universe u

/-- The exact ordinary first-order premise uses a membership implication
and an unbounded existential. Its realizer supplies the witnesses used
by the original-bound construction above. -/
def fromFirstOrderPremise {count : Nat} (parent : Fin count) (body : Formula (count+2))
    (environment : Environment.{u} count)
    (premise : realize (.all (.imply (.member 0 parent.succ) (.exist body))) environment) :
    Σ collector : Graph.{u},
      ((value : Graph.{u}) → Member value (environment parent) →
        Σ result : Graph.{u}, Member result collector ×
          realize body (extend result (extend value environment))) ×
      ((result : Graph.{u}) → Member result collector →
        Σ value : Graph.{u}, Member value (environment parent) ×
          realize body (extend result (extend value environment))) :=
  strongCollection body environment (environment parent) (fun value member => premise value ⟨member⟩)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedCollection
