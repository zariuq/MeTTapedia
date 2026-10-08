import Mettapedia.CategoryTheory.FiniteActionTreeCoiteration
import Mettapedia.CategoryTheory.FinitePowersetRelation
import Mettapedia.CategoryTheory.FinitePowersetWeakPullback

/-!
# Complete future assays and independently specified coloured bisimulation

The observer reads the supplied colour again at every reached state. A relation
must preserve that readout and match complete successor sets. The equality
kernel of the actual coloured coiteration is exactly this independently defined
bisimilarity. Complete relation spans earn the converse; no intersection of
independently chosen bisimulations is presumed to remain a bisimulation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTreeAssays

universe u v w t

variable {Actions : Type u} {First : Type v} {Second : Type w} {Colours : Type t}

def Admitted (before : First → Actions → Finset First)
    (after : Second → Actions → Finset Second)
    (firstReadout : First → Colours) (secondReadout : Second → Colours)
    (relation : First → Second → Prop) : Prop :=
  ∀ state other, relation state other →
    firstReadout state = secondReadout other ∧
      ∀ action, FinitePowerset.Related relation (before state action) (after other action)

def Bisimilar (before : First → Actions → Finset First)
    (after : Second → Actions → Finset Second)
    (firstReadout : First → Colours) (secondReadout : Second → Colours)
    (state : First) (other : Second) : Prop :=
  ∃ relation : First → Second → Prop,
    Admitted before after firstReadout secondReadout relation ∧ relation state other

def observe (successors : First → Actions → Finset First) (readout : First → Colours) :
    First → FiniteActionTree.Tree Actions Colours :=
  FiniteActionTree.Tree.coiterate successors readout

theorem kernel_admitted (before : First → Actions → Finset First)
    (after : Second → Actions → Finset Second)
    (firstReadout : First → Colours) (secondReadout : Second → Colours) :
    Admitted before after firstReadout secondReadout
      (fun state other => observe before firstReadout state = observe after secondReadout other) := by
  intro state other same
  constructor
  · have roots := congrArg FiniteActionTree.Tree.root same
    simpa only [observe, FiniteActionTree.Tree.root_coiterate] using roots
  · intro action
    apply (FinitePowersetWeakPullback.related_iff_matching
      (observe before firstReadout) (observe after secondReadout)
      (before state action) (after other action)).2
    have steps := congrArg (fun tree => FiniteActionTree.Tree.step tree action) same
    simpa only [observe, FiniteActionTree.Tree.step_coiterate] using steps

theorem observe_of_admitted (before : First → Actions → Finset First)
    (after : Second → Actions → Finset Second)
    (firstReadout : First → Colours) (secondReadout : Second → Colours)
    (relation : First → Second → Prop)
    (admitted : Admitted before after firstReadout secondReadout relation)
    {state : First} {other : Second} (held : relation state other) :
    observe before firstReadout state = observe after secondReadout other := by
  let pair : FinitePowersetRelation.Pair relation := ⟨(state, other), held⟩
  let joined : FinitePowersetRelation.Pair relation → Actions →
      Finset (FinitePowersetRelation.Pair relation) := fun pair action =>
    FinitePowersetRelation.matching relation (before pair.val.1 action) (after pair.val.2 action)
  have firstSquare : ∀ pair action,
      FinitePowerset.map (FinitePowersetRelation.first relation) (joined pair action) =
        before (FinitePowersetRelation.first relation pair) action := by
    intro pair action
    exact FinitePowersetRelation.matching_first relation _ _
      ((admitted _ _ pair.property).2 action)
  have secondSquare : ∀ pair action,
      FinitePowerset.map (FinitePowersetRelation.second relation) (joined pair action) =
        after (FinitePowersetRelation.second relation pair) action := by
    intro pair action
    exact FinitePowersetRelation.matching_second relation _ _
      ((admitted _ _ pair.property).2 action)
  have readouts : firstReadout ∘ FinitePowersetRelation.first relation =
      secondReadout ∘ FinitePowersetRelation.second relation := by
    funext pair
    exact (admitted _ _ pair.property).1
  have first := FiniteActionTree.Tree.coiterate_natural joined before
    (FinitePowersetRelation.first relation) firstSquare firstReadout pair
  have second := FiniteActionTree.Tree.coiterate_natural joined after
    (FinitePowersetRelation.second relation) secondSquare secondReadout pair
  rw [readouts] at first
  exact first.symm.trans second

theorem observation_eq_iff_bisimilar (before : First → Actions → Finset First)
    (after : Second → Actions → Finset Second)
    (firstReadout : First → Colours) (secondReadout : Second → Colours)
    (state : First) (other : Second) :
    observe before firstReadout state = observe after secondReadout other ↔
      Bisimilar before after firstReadout secondReadout state other := by
  constructor
  · intro same
    exact ⟨_, kernel_admitted before after firstReadout secondReadout, same⟩
  · rintro ⟨relation, admitted, held⟩
    exact observe_of_admitted before after firstReadout secondReadout relation admitted held

theorem readout_of_bisimilar (before : First → Actions → Finset First)
    (after : Second → Actions → Finset Second)
    (firstReadout : First → Colours) (secondReadout : Second → Colours)
    {state : First} {other : Second}
    (related : Bisimilar before after firstReadout secondReadout state other) :
    firstReadout state = secondReadout other := by
  obtain ⟨_, admitted, held⟩ := related
  exact (admitted state other held).1

theorem forgetting_assay (successors : First → Actions → Finset First)
    (readout : First → Colours) (state : First) :
    FiniteActionTree.Tree.map (fun _ : Colours => PUnit.unit)
      (observe successors readout state) =
        observe successors (fun _ => PUnit.unit) state :=
  FiniteActionTree.Tree.map_coiterate successors readout (fun _ => PUnit.unit) state

theorem weaken_assay {OtherColours : Type w}
    (successors : First → Actions → Finset First) (readout : First → Colours)
    (mapping : Colours → OtherColours) {first second : First}
    (related : Bisimilar successors successors readout readout first second) :
    Bisimilar successors successors (mapping ∘ readout) (mapping ∘ readout) first second := by
  obtain ⟨relation, admitted, held⟩ := related
  refine ⟨relation, ?_, held⟩
  intro state other related
  exact ⟨congrArg mapping ((admitted state other related).1),
    (admitted state other related).2⟩

end Mettapedia.CategoryTheory.FiniteActionTreeAssays
