import Mettapedia.Logic.HOL.IndexedVectorPositionBounds
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# The positional bound retains its induction premise

A nonempty propositional carrier with identity successor supplies a lookup
whose position is not below its index. This is an explicit countermodel to
dropping natural induction, not a representation of natural numbers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPositionControls
open FiniteConstructorEncoding.Controls (Constants model values)

def ops : IndexedVectorPredicate.Signature Constants where
  number := .prop
  element := .prop
  vector := .prop
  zero := .bot
  successor := .lam (.var .vz)
  nil := .bot
  cons := .lam (.lam (.lam .top))

def present : ProofSyntax Constants [] (IndexedVectorPositions.lookup ops
    (.app ops.successor .top) (ops.consValue .top .top .bot) ops.zero .top) :=
  IndexedVectorPositions.here ops .top .top .bot

theorem present_free : present.FunctionExtensionalityFree := IndexedVectorPositions.here_free ops .top .top .bot

def bound : ClosedFormula Constants :=
  .app (.app (SuccessorOrder.less ops.successor) ops.zero) (.app ops.successor .top)

theorem bound_false : ¬ (model.denote bound @values).down := by
  change ¬ (model.denote (SuccessorOrder.less ops.successor) values (ULift.up False) (ULift.up True)).down
  intro holds
  have closure := (SuccessorOrder.less_denote model (HenkinModel.fullDomains_standard _ _)
    ops.successor values (ULift.up False) (ULift.up True)).mp holds
  have impossible := closure (fun point => ¬ point.down) (fun h => h) (fun _ h => h)
  exact impossible True.intro

theorem dropping_induction_refused : ¬ Nonempty (ProofSyntax Constants []
    (.imp (IndexedVectorPositions.lookup ops (.app ops.successor .top)
      (ops.consValue .top .top .bot) ops.zero .top) bound)) := by
  rintro ⟨claimed⟩
  have proof := ProofSyntax.impE claimed present
  exact bound_false (Soundness.extTheorem_sound proof.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)))

#print axioms present_free
#print axioms dropping_induction_refused
end Mettapedia.Logic.HOL.IndexedVectorPositionControls
