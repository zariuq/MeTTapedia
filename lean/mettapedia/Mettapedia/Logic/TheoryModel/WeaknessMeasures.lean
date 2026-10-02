import Mettapedia.Logic.TheoryModel.Weakness
import Mettapedia.Logic.TheoryModel.Forgetting
import Mettapedia.GSLT.Meredith.WeaknessBridge
import Mettapedia.Enactive.Bennett2023
import Mettapedia.Enactive.CredalWeakness
import Mettapedia.UniversalAI.WeaknessPrior

/-!
# Weakness of theories in the existing weakness measures

Over a finite universe of structures with decidable satisfaction, a finite
theory has a finite model class. Its weakness can then be read in each of the
existing measures, and each reading is antitone in the theory:

* Michael Timothy Bennett's weakness: the number of admitted structures;
* quantale weakness of the diagonal event of the model class, for evidence
  over a finite universe of bisimulation classes as in the GSLT weakness
  bridge; the reading commutes with transport along quantale morphisms;
* robust lower and upper success probabilities over a credal family.

Bennett's extension of an aspect is the model class of its facts in the
completion relation, both in the abstract 2024 theory and in finite layers, so
his weakness and its antitonicity are instances; the 2023 Boolean-program
presentation agrees by characteristic sets, and a stronger statement has a
smaller normalized weakness prior.

Forgetting moves the two kinds of measure in opposite directions: coarsening
an observer enlarges the model class of the observed theory, so any monotone
measure of model classes grows, while the quantale weakness of the observer's
distinction event shrinks.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.WeaknessMeasures

open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.GSLT.Meredith.WeaknessBridge

universe uU uSent uQ uQ' uWorld uW

/-! ## Finite model classes -/

section Finite

variable {U : Type uU} [Fintype U] {Sent : Type uSent} (Sat : U → Sent → Prop)
  [∀ u φ, Decidable (Sat u φ)]

/-- The finite model class of a finite theory. -/
def modelFinset (T : Finset Sent) : Finset U :=
  Finset.univ.filter fun u => ∀ φ ∈ T, Sat u φ

theorem mem_modelFinset {T : Finset Sent} {u : U} :
    u ∈ modelFinset Sat T ↔ u ∈ models Sat (T : Set Sent) := by
  unfold modelFinset
  rw [Finset.mem_filter]
  exact ⟨fun member _ axiomMember => member.2 _ axiomMember,
    fun model => ⟨Finset.mem_univ u, fun _ axiomMember => model axiomMember⟩⟩

theorem coe_modelFinset (T : Finset Sent) :
    (modelFinset Sat T : Set U) = models Sat (T : Set Sent) :=
  Set.ext fun _ => mem_modelFinset Sat

variable {Sat}

theorem modelFinset_anti {T T' : Finset Sent} (included : T ⊆ T') :
    modelFinset Sat T' ⊆ modelFinset Sat T := fun _ member =>
  (mem_modelFinset Sat).mpr
    (models_anti (fun _ axiomMember => included axiomMember) ((mem_modelFinset Sat).mp member))

variable (Sat)

/-- Bennett's weakness of a finite theory: the number of admitted structures. -/
def theoryBennettWeakness (T : Finset Sent) : ℕ :=
  bennettWeakness (modelFinset Sat T)

variable {Sat}

/-- **Bennett weakness is antitone in the theory.** -/
theorem theoryBennettWeakness_anti {T T' : Finset Sent} (included : T ⊆ T') :
    theoryBennettWeakness Sat T' ≤ theoryBennettWeakness Sat T :=
  Finset.card_le_card (modelFinset_anti included)

/-- Bennett weakness is the cardinal weakness of the model class. -/
theorem theoryBennettWeakness_eq_encard (T : Finset Sent) :
    (theoryBennettWeakness Sat T : ℕ∞) = weaknessOf Sat Set.encard (T : Set Sent) := by
  unfold weaknessOf theoryBennettWeakness bennettWeakness
  rw [← coe_modelFinset, Set.encard_coe_eq_coe_finsetCard]

/-! ## Quantale weakness over GSLT evidence -/

section Quantale

variable {Q : Type uQ} [Monoid Q] [CompleteLattice Q]

variable (Sat)

/-- The quantale weakness of a finite theory: the weakness of the diagonal
event of its model class, for evidence over the universe of structures. -/
noncomputable def theoryWeakness (ev : GSLTEvidence U Q) (T : Finset Sent) : Q :=
  gsltWeakness ev (inducedDiagonalEvent (modelFinset Sat T))

variable {Sat}

/-- **Quantale weakness is antitone in the theory.** -/
theorem theoryWeakness_anti (ev : GSLTEvidence U Q) {T T' : Finset Sent} (included : T ⊆ T') :
    theoryWeakness Sat ev T' ≤ theoryWeakness Sat ev T :=
  weakness_mono _ _ _ (Finset.map_subset_map.mpr (modelFinset_anti included))

/-- The theory reading of quantale weakness commutes with transport along
quantale morphisms, as in the GSLT weakness bridge. -/
theorem theoryWeakness_transport [DecidableEq U] {Q' : Type uQ'} [Monoid Q'] [CompleteLattice Q']
    (ev : GSLTEvidence U Q) (g : QuantaleHom Q Q') (T : Finset Sent) :
    g (theoryWeakness Sat ev T) = theoryWeakness Sat (transportEvidence ev g) T :=
  transport_commutes ev g _

/-- On the diagonal event, pair-event cardinality is the Bennett weakness of the
theory. -/
theorem pairDistinctionWeakness_diagonal (T : Finset Sent) :
    pairDistinctionWeakness (inducedDiagonalEvent (modelFinset Sat T)) =
      theoryBennettWeakness Sat T :=
  pairDistinctionWeakness_inducedDiagonalEvent _

/-- **Coarsening an observer lowers the quantale weakness of its distinction
event**, for arbitrary evidence. -/
theorem distinctionWeakness_antitone (ev : GSLTEvidence U Q) {r₁ r₂ : Setoid U}
    [DecidableRel r₁.r] [DecidableRel r₂.r] (coarser : r₁ ≤ r₂) :
    gsltWeakness ev (setoidDistinctionSet r₂) ≤ gsltWeakness ev (setoidDistinctionSet r₁) :=
  weakness_mono _ _ _ (setoidDistinctionSet_mono coarser)

end Quantale

/-! ## Robust credal success -/

section Credal

variable [DecidableEq U]

variable (Sat)

/-- Finite theories as candidates, admitting their model classes. -/
def theoryCompletionSystem : Mettapedia.Enactive.CredalWeakness.CompletionSystem (Finset Sent) U :=
  ⟨modelFinset Sat⟩

variable {Sat}

open Mettapedia.Enactive.CredalWeakness.CompletionSystem in
/-- A stronger theory has lower robust success over every nonempty credal
family. -/
theorem theoryLowerScore_anti
    (credal : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite U)
    (nonempty : credal.Nonempty) {T T' : Finset Sent} (included : T ⊆ T') :
    lowerScore (theoryCompletionSystem Sat) credal T' ≤
      lowerScore (theoryCompletionSystem Sat) credal T :=
  lowerScore_mono_of_subset _ credal nonempty (modelFinset_anti included)

open Mettapedia.Enactive.CredalWeakness.CompletionSystem in
theorem theoryUpperScore_anti
    (credal : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite U)
    (nonempty : credal.Nonempty) {T T' : Finset Sent} (included : T ⊆ T') :
    upperScore (theoryCompletionSystem Sat) credal T' ≤
      upperScore (theoryCompletionSystem Sat) credal T :=
  upperScore_mono_of_subset _ credal nonempty (modelFinset_anti included)

end Credal

end Finite

/-! ## Forgetting: model-class weakness grows -/

section Forgetting

variable {Str : Type uU} {Sent : Type uSent} {Sat : Str → Sent → Prop}
  {W : Type uW} [Preorder W]

/-- Coarsening an observer raises the weakness of its observed theory under
every monotone measure of model classes. -/
theorem weaknessOf_observedTheory_mono {μ : Set Str → W} (monotone : MonotoneMeasure μ)
    {E E' : Setoid Str} (coarser : E ≤ E') (K : Set Str) :
    weaknessOf Sat μ (observedTheory Sat E K) ≤ weaknessOf Sat μ (observedTheory Sat E' K) :=
  monotone (models_observedTheory_mono coarser K)

end Forgetting

/-! ## Bennett's completion layers -/

section Bennett

/-- In the abstract theory, the extension of an aspect is the model class of its
facts, with completions as structures and facts as sentences. -/
theorem abstract_extension_eq_models {World : Type uWorld}
    {abstractLayer : Mettapedia.Enactive.AbstractionLayer World}
    (source : Mettapedia.Enactive.Aspect abstractLayer) :
    Mettapedia.Enactive.Completion.extension source =
      models (fun (target : Mettapedia.Enactive.Aspect abstractLayer) fact => fact ∈ target.facts)
        source.facts := by
  ext target
  rw [Mettapedia.Enactive.Completion.mem_extension]
  exact ⟨fun included _ member => included member, fun model _ member => model member⟩

open Mettapedia.Enactive.Finite

variable {World : Type uWorld} [Fintype World] [DecidableEq World] (layer : Layer World)

/-- Bennett's completion relation as satisfaction: a completion satisfies a
fact when it contains it. -/
def completionSat (target : layer.Statement) (fact : Finset World) : Prop :=
  fact ∈ target.val

instance (target : layer.Statement) (fact : Finset World) :
    Decidable (completionSat layer target fact) :=
  inferInstanceAs (Decidable (fact ∈ target.val))

/-- **Bennett's extension of a statement is the model class of its facts.** -/
theorem extension_eq_modelFinset (source : layer.Statement) :
    layer.extension source = modelFinset (completionSat layer) source.val := by
  ext target
  rw [Layer.mem_extension, mem_modelFinset]
  exact ⟨fun included _ member => included member, fun model _ member => model member⟩

/-- Bennett's weakness is the Bennett weakness of the statement read as a
theory. -/
theorem weakness_eq_theoryBennettWeakness (source : layer.Statement) :
    layer.weakness source = theoryBennettWeakness (completionSat layer) source.val := by
  unfold Layer.weakness theoryBennettWeakness bennettWeakness
  rw [extension_eq_modelFinset]

/-- Bennett's antitonicity of weakness, recovered from antitonicity of model
classes. -/
theorem weakness_antitone_of_models {left right : layer.Statement}
    (included : left.val ⊆ right.val) : layer.weakness right ≤ layer.weakness left := by
  rw [weakness_eq_theoryBennettWeakness, weakness_eq_theoryBennettWeakness]
  exact theoryBennettWeakness_anti included

/-- The 2023 Boolean-program presentation reads the same weakness. -/
theorem bennett2023_weakness_eq (layer : Mettapedia.Enactive.Bennett2023.Layer World)
    (source : layer.Statement) :
    layer.weakness source =
      theoryBennettWeakness (completionSat layer.toFinite)
        (Mettapedia.Enactive.Bennett2023.Layer.statementEquiv layer source).val := by
  rw [Mettapedia.Enactive.Bennett2023.Layer.weakness_agreement,
    weakness_eq_theoryBennettWeakness]

/-- A stronger statement has a smaller normalized weakness prior. -/
theorem normalizedWeaknessPrior_antitone [Nonempty World] {left right : layer.Statement}
    (included : left.val ⊆ right.val) :
    Mettapedia.UniversalAI.WeaknessPrior.Layer.normalizedWeaknessPrior layer right ≤
      Mettapedia.UniversalAI.WeaknessPrior.Layer.normalizedWeaknessPrior layer left :=
  (Mettapedia.UniversalAI.WeaknessPrior.Layer.normalizedWeaknessPrior_le_iff layer right left).mpr
    (weakness_antitone_of_models layer included)

end Bennett

/-! ## Controls -/

namespace Control

open Mettapedia.Logic.TheoryModel.Control (sat)

instance (m : Bool) (φ : Option Bool) : Decidable (sat m φ) := by
  cases φ with
  | none => exact isTrue trivial
  | some b => exact inferInstanceAs (Decidable (m = b))

/-- The empty theory admits both structures. -/
theorem weakness_empty : theoryBennettWeakness sat (∅ : Finset (Option Bool)) = 2 := by
  decide

/-- Adding an axiom lowers the weakness. -/
theorem weakness_some_true : theoryBennettWeakness sat {some true} = 1 := by
  decide

/-- The contradictory theory has weakness zero. -/
theorem weakness_contradiction : theoryBennettWeakness sat {some true, some false} = 0 := by
  decide

/-- Negative control: equal weakness does not identify the model classes. -/
theorem equal_weakness_different_models :
    theoryBennettWeakness sat {some true} = theoryBennettWeakness sat {some false} ∧
      modelFinset sat {some true} ≠ modelFinset sat {some false} := by
  decide

open Mettapedia.Enactive.Finite.Canary in
/-- Bennett's own canary read through the bridge: the unconstrained statement
has weakness six and the true-only statement weakness two. -/
theorem bennett_canary :
    theoryBennettWeakness (completionSat boolLayer) emptyStatement.val = 6 ∧
      theoryBennettWeakness (completionSat boolLayer) trueStatement.val = 2 :=
  ⟨(weakness_eq_theoryBennettWeakness boolLayer emptyStatement).symm.trans
      emptyStatement_weakness,
    (weakness_eq_theoryBennettWeakness boolLayer trueStatement).symm.trans
      trueStatement_weakness⟩

end Control

end Mettapedia.Logic.TheoryModel.WeaknessMeasures
