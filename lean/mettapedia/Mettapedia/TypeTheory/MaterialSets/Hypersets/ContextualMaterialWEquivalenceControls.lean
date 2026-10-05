import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialWEquivalence

/-!
# Material W signature controls on the infinite observed site

A nonidentity shape-coordinate map acts on independently constructed W
models while preserving their cyclic material payload. A second position
family changes from an inhabited identity fibre to an empty one at a later
observed point. The signature comparison covers that actual nonconstant
family as well. In contrast, a position at every root rules out all
well-founded trees, and its transported W carrier remains empty.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialWEquivalenceControls

open CategoryTheory ContextualGeneratedUniverse ContextualMaterialEquivalence

abbrev first := ContextualMaterialEquivalence.Controls.pairFamily
abbrev second := ContextualMaterialEquivalence.Controls.reversedDictionary
abbrev domain := ContextualMaterialEquivalence.Controls.coordinateEquivalence
abbrev arrows := Growing.arrowCoding
abbrev point := Growing.newPoint
abbrev shape := ContextualMaterialEquivalence.Controls.mixedPair

def terminal : MaterialFamily first.extension := MaterialFamily.empty first.extension
def transportedTerminal : MaterialFamily second.extension := domain.transportBody terminal
def terminalComparison : Equivalence terminal (transportedTerminal.reindex domain.comprehension) :=
  ofEquality (domain.transportBody_roundtrip terminal).symm

def leaf : (first.w terminal arrows).family.obj point :=
  ContextualWTypes.sup first.family (PowerClassPresheafProducts.indexedBody first.family terminal.family) shape
    (fun _ _ branch => Empty.elim branch.down)
    (fun _ _ _ _ branch => Empty.elim branch.down)

noncomputable def mappedLeaf : (second.w transportedTerminal arrows).family.obj point :=
  ContextualMaterialWEquivalence.naturalEquiv domain terminalComparison arrows point leaf

def rootLabel {D : Type} [Category.{0} D] {labels : D ⥤ Type}
    {positions : labels.Elements ⥤ Type} {X : D} : ContextualWTypes.RawTree labels positions X → labels.obj X
  | .sup label _ => label

theorem mapped_root_changes : rootLabel mappedLeaf.val ≠ rootLabel leaf.val :=
  ContextualMaterialEquivalence.Controls.coordinate_swap_changes_pair

theorem mapped_value : ((second.w transportedTerminal arrows).model point).value mappedLeaf =
    ((first.w terminal arrows).model point).value leaf :=
  (ContextualMaterialWEquivalence.w domain terminalComparison arrows).value point leaf

theorem cyclic_root_payload : HSet.snd ((first.model point).value shape) = HSet.quineAtom := by
  have pairValue : (first.model point).value shape = HSet.kpair
      ((Growing.input.model point).value (Growing.emptySection.val point))
      ((Growing.input.model point).value (Growing.positiveSection.val point)) :=
    PowerClassContextualMaterialization.sigmaModel_value _ _ _ _ _ _
  rw [pairValue, HSet.snd_kpair]
  exact Growing.positiveSection_value Growing.newRaw

theorem mapped_cyclic_root_payload :
    HSet.snd ((second.model point).value (rootLabel mappedLeaf.val)) = HSet.quineAtom :=
  (congrArg HSet.snd (domain.value point shape)).trans cyclic_root_payload

theorem mapped_leaf_member : ((second.w transportedTerminal arrows).model point).value mappedLeaf ∈
    ((second.w transportedTerminal arrows).model point).carrier :=
  ((second.w transportedTerminal arrows).model point).value_mem mappedLeaf

def varyingPositions : MaterialFamily first.extension :=
  (Growing.input.identity Growing.emptySection Growing.positiveSection).reindex
    (PowerClassPresheafProducts.projection first.family)

def transportedVaryingPositions : MaterialFamily second.extension := domain.transportBody varyingPositions
def varyingComparison : Equivalence varyingPositions (transportedVaryingPositions.reindex domain.comprehension) :=
  ofEquality (domain.transportBody_roundtrip varyingPositions).symm

noncomputable def varyingW : Equivalence (first.w varyingPositions arrows) (second.w transportedVaryingPositions arrows) :=
  ContextualMaterialWEquivalence.w domain varyingComparison arrows

def oldShape : first.family.obj Growing.old :=
  ⟨Growing.emptySection.val Growing.old, Growing.emptySection.val Growing.old⟩

def oldArgument : first.extension.base.Elements := ⟨Growing.old.1, ⟨Growing.old.2, oldShape⟩⟩
def newArgument : first.extension.base.Elements := ⟨point.1, ⟨point.2, shape⟩⟩

theorem old_position_carrier : (varyingPositions.model oldArgument).carrier = {∅} := Growing.identity_old_carrier
theorem new_position_carrier : (varyingPositions.model newArgument).carrier = ∅ := Growing.identity_new_carrier

theorem position_carriers_differ : (varyingPositions.model oldArgument).carrier ≠ (varyingPositions.model newArgument).carrier := by
  intro same
  exact HSet.empty_ne_singleton_empty (new_position_carrier.symm.trans (same.symm.trans old_position_carrier))

def unary : MaterialFamily first.extension := MaterialFamily.unit first.extension
def transportedUnary : MaterialFamily second.extension := domain.transportBody unary
def unaryComparison : Equivalence unary (transportedUnary.reindex domain.comprehension) :=
  ofEquality (domain.transportBody_roundtrip unary).symm

theorem unary_empty (atPoint : Growing.context.base.Elements) : ((first.w unary arrows).model atPoint).carrier = ∅ := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    let tree := ((first.w unary arrows).model atPoint).decode ⟨value, member⟩
    have impossible : ∀ {X}, (raw : ContextualWTypes.RawTree first.family
        (PowerClassPresheafProducts.indexedBody first.family unary.family) X) → False := by
      intro X raw
      induction raw with
      | @sup X _ _ ih => exact ih X (𝟙 X) (ULift.up PUnit.unit)
    exact (impossible tree.val).elim
  · intro member
    exact (HSet.notMem_empty value member).elim

theorem transported_unary_empty (atPoint : Growing.context.base.Elements) :
    ((second.w transportedUnary arrows).model atPoint).carrier = ∅ :=
  (ContextualMaterialWEquivalence.carrier domain unaryComparison arrows atPoint).symm.trans (unary_empty atPoint)

theorem leaf_not_unary : ¬ Nonempty ((first.w unary arrows).family.obj point) := by
  rintro ⟨tree⟩
  have belongs := ((first.w unary arrows).model point).value_mem tree
  rw [unary_empty] at belongs
  exact HSet.notMem_empty _ belongs

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialWEquivalenceControls
