import Mettapedia.Logic.HOL.PairingReconstructionSchemas
import Mettapedia.Logic.HOL.ProofSyntaxInterpretation

/-!
# A schematic pairing signature with explicit membership evidence

The four objects and two operations are symbolic parameters. The retained
injectivity program uses the supplied membership schema; the signature
declares no axiom. An interpretation supplies actual typed operation terms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.PairingSchemaParameters
abbrev object : Ty Unit := .base ()
inductive Symbol : Ty Unit → Type where
  | membership : Symbol (object ⇒ object ⇒ .prop)
  | pairing : Symbol (object ⇒ object ⇒ object)
  | left : Symbol object
  | right : Symbol object
  | first : Symbol object
  | second : Symbol object

def membership : ClosedTerm Symbol (object ⇒ object ⇒ .prop) := .const .membership
def pairing : ClosedTerm Symbol (object ⇒ object ⇒ object) := .const .pairing
def schema : ClosedFormula Symbol := PairingReconstructionSchemas.membershipStatement membership pairing

def claim : ClosedFormula Symbol := .imp
  (.eq (PairingReconstruction.orderedBy (PairingReconstructionSchemas.pair pairing) (.const .left) (.const .right))
    (PairingReconstruction.orderedBy (PairingReconstructionSchemas.pair pairing) (.const .first) (.const .second)))
  (.and (.eq (.const .left) (.const .first)) (.eq (.const .right) (.const .second)))

def proof : ProofSyntax Symbol [schema] claim :=
  PairingReconstructionSchemas.injectivity membership pairing (.const .left) (.const .right)
    (.const .first) (.const .second) (ProofSyntax.castIndices rfl (weakenCtx_nil schema).symm (.hyp 0))

theorem proof_free : proof.FunctionExtensionalityFree :=
  PairingReconstructionSchemas.injectivity_free membership pairing _ _ _ _ _ trivial

universe v
def interpretation {Const : Ty Unit → Type v}
    (membership : ClosedTerm Const (object ⇒ object ⇒ .prop))
    (pairing : ClosedTerm Const (object ⇒ object ⇒ object))
    (left right first second : ClosedTerm Const object) : TermInterpretation Unit Symbol Unit Const where
  types := fun base => .base base
  constants := fun {_} symbol => match symbol with
    | .membership => membership
    | .pairing => pairing
    | .left => left
    | .right => right
    | .first => first
    | .second => second

theorem interpretation_schema {Const : Ty Unit → Type v}
    (membership : ClosedTerm Const (object ⇒ object ⇒ .prop))
    (pairing : ClosedTerm Const (object ⇒ object ⇒ object))
    (left right first second : ClosedTerm Const object) :
    (interpretation membership pairing left right first second).term schema =
      PairingReconstructionSchemas.membershipStatement membership pairing := rfl

theorem interpretation_claim {Const : Ty Unit → Type v}
    (membership : ClosedTerm Const (object ⇒ object ⇒ .prop))
    (pairing : ClosedTerm Const (object ⇒ object ⇒ object))
    (left right first second : ClosedTerm Const object) :
    (interpretation membership pairing left right first second).term claim =
      .imp
        (.eq (PairingReconstruction.orderedBy (PairingReconstructionSchemas.pair pairing) left right)
          (PairingReconstruction.orderedBy (PairingReconstructionSchemas.pair pairing) first second))
        (.and (.eq left first) (.eq right second)) := rfl

end Mettapedia.Logic.HOL.PairingSchemaParameters

