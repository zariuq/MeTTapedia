import Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWire
import Mettapedia.OSLF.Syntax.BindingWireData

/-! Structural transport of ordered proof wires using binary wire data.
No natural-number pairing expansion is needed for either labels or trees. -/

set_option autoImplicit false
namespace Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire
open Mettapedia.OSLF.Binding.WireCodec

variable {Label : Type} (labelCodec : Codec Label)

mutual
  def putWire : Wire Label → Data
    | .node label children => .pair (labelCodec.put label) (putChildren children)
  def putChildren : List (Wire Label) → Data
    | [] => .atom 0
    | head :: tail => .pair (putWire head) (putChildren tail)
end

mutual
  def getWire : Data → Option (Wire Label)
    | .pair label children => do return .node (← labelCodec.get label) (← getChildren children)
    | .atom _ => none
  def getChildren : Data → Option (List (Wire Label))
    | .atom 0 => some []
    | .pair head tail => do return (← getWire head) :: (← getChildren tail)
    | .atom (_ + 1) => none
end

mutual
  theorem get_putWire : ∀ wire : Wire Label,
      getWire labelCodec (putWire labelCodec wire) = some wire
    | .node label children => by
        simp only [putWire, getWire, labelCodec.get_put, get_putChildren children]
        rfl
  theorem get_putChildren : ∀ children : List (Wire Label),
      getChildren labelCodec (putChildren labelCodec children) = some children
    | [] => rfl
    | head :: tail => by
        simp only [putChildren, getChildren, get_putWire head, get_putChildren tail]
        rfl
end

def wireCodec : Codec (Wire Label) :=
  ⟨putWire labelCodec, getWire labelCodec, get_putWire labelCodec⟩

def dataLabelCodec : Codec Data := ⟨id, some, fun _ => rfl⟩
def dataWireCodec : Codec (Wire Data) := wireCodec dataLabelCodec

/-- For the actual identity Data label, accepted binary inputs are exact. -/
theorem data_inverse (data : Data) :
    (∀ wire, getWire dataLabelCodec data = some wire → putWire dataLabelCodec wire = data) ∧
    (∀ children, getChildren dataLabelCodec data = some children →
      putChildren dataLabelCodec children = data) := by
  induction data with
  | atom n =>
      constructor
      · intro wire accepted; cases accepted
      · intro children accepted
        cases n with
        | zero => cases accepted; rfl
        | succ n => cases accepted
  | pair first second ihFirst ihSecond =>
      constructor
      · intro wire accepted
        rw [getWire] at accepted
        change (getChildren dataLabelCodec second).bind (fun cs => some (Wire.node first cs)) = some wire at accepted
        cases children : getChildren dataLabelCodec second with
        | none => simp only [children, Option.bind_none] at accepted; cases accepted
        | some childrenValue =>
            simp only [children, Option.bind_some, Option.some.injEq] at accepted
            subst wire
            exact congrArg (Data.pair first) (ihSecond.2 childrenValue children)
      · intro children accepted
        cases head : getWire dataLabelCodec first with
        | none => simp only [getChildren, head, Bind.bind, Option.bind] at accepted; cases accepted
        | some headValue =>
            cases tail : getChildren dataLabelCodec second with
            | none => simp only [getChildren, head, tail, Bind.bind, Option.bind] at accepted; cases accepted
            | some tailValue =>
                simp only [getChildren, head, tail, Bind.bind, Option.bind, pure, Option.some.injEq] at accepted
                subst children
                exact congrArg₂ Data.pair (ihFirst.1 headValue head) (ihSecond.2 tailValue tail)

/-- The binary data transport used for native rule labels has no accepted aliases. -/
theorem put_of_dataWire_get {data : Data} {wire : Wire Data}
    (accepted : dataWireCodec.get data = some wire) : dataWireCodec.put wire = data :=
  (data_inverse data).1 wire accepted

#print axioms dataWireCodec

end Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire
