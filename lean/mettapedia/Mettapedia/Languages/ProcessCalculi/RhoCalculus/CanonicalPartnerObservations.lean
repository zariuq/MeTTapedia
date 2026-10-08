import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCoalgebra

/-!
# Whole partner observations and independently specified rho bisimilarity

The relation below matches independently authored canonical COMM reactions
under every supplied parallel partner. Its kernel theorem is earned from the
constructed final action-tree coalgebra. Coloured cofree observations retain
a supplied native readout at every reached state, with complete successor
sets and the actual coiteration universal property. The comparison to the
existing public partner system uses its operational arrows, not a definition
of success in terms of the new observations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerObservations

open _root_.CategoryTheory
open Mettapedia.CategoryTheory
open CanonicalBag CanonicalReaction CanonicalPartnerCoalgebra
open LanguageDefGSLT

/-- Two-sided matching of actual reactions, independently of all tree readouts. -/
def Admitted (relation : Bag → Bag → Prop) : Prop :=
  ∀ source other, relation source other → ∀ partner,
    (∀ target, Reaction (append source partner) target →
      ∃ matched, Reaction (append other partner) matched ∧ relation target matched) ∧
    (∀ target, Reaction (append other partner) target →
      ∃ matched, Reaction (append source partner) matched ∧ relation matched target)

def Bisimilar (source other : Bag) : Prop :=
  ∃ relation : Bag → Bag → Prop, Admitted relation ∧ relation source other

theorem admitted_iff_complete_matching (relation : Bag → Bag → Prop) :
    Admitted relation ↔
      ∀ source other, relation source other → ∀ partner,
        FinitePowerset.Related relation (successors source partner) (successors other partner) := by
  constructor
  · intro admitted source other held partner
    constructor
    · intro target member
      obtain ⟨matched, reaction, related⟩ := (admitted source other held partner).1 target
        ((mem_successors_iff_reaction source partner target).1 member)
      exact ⟨matched, (mem_successors_iff_reaction other partner matched).2 reaction, related⟩
    · intro target member
      obtain ⟨matched, reaction, related⟩ := (admitted source other held partner).2 target
        ((mem_successors_iff_reaction other partner target).1 member)
      exact ⟨matched, (mem_successors_iff_reaction source partner matched).2 reaction, related⟩
  · intro admitted source other held partner
    constructor
    · intro target reaction
      obtain ⟨matched, member, related⟩ := (admitted source other held partner).1 target
        ((mem_successors_iff_reaction source partner target).2 reaction)
      exact ⟨matched, (mem_successors_iff_reaction other partner matched).1 member, related⟩
    · intro target reaction
      obtain ⟨matched, member, related⟩ := (admitted source other held partner).2 target
        ((mem_successors_iff_reaction other partner target).2 reaction)
      exact ⟨matched, (mem_successors_iff_reaction source partner matched).1 member, related⟩

theorem generic_bisimilar_iff (source other : Bag) :
    FiniteActionTreeFinalSemantics.Bisimilar base index actions coalgebra coalgebra
      PUnit.unit PUnit.unit source other ↔ Bisimilar source other := by
  constructor
  · rintro ⟨relation, admitted, held⟩
    refine ⟨relation PUnit.unit PUnit.unit, ?_, held⟩
    apply (admitted_iff_complete_matching _).2
    exact admitted PUnit.unit PUnit.unit
  · rintro ⟨relation, admitted, held⟩
    refine ⟨fun _ _ => relation, ?_, held⟩
    intro _ _ source other related partner
    exact (admitted_iff_complete_matching relation).1 admitted source other related partner

/-- The actual unique arrow into the constructed uncoloured final coalgebra. -/
def observe (source : Bag) : FiniteActionTree.Tree Bag PUnit :=
  (FiniteActionTreeFinalSemantics.observe base index actions coalgebra).f
    PUnit.unit PUnit.unit source

theorem observe_successors (source partner : Bag) :
    FiniteActionTree.Tree.step (observe source) partner =
      FinitePowerset.map observe (successors source partner) :=
  FiniteActionTreeFinalSemantics.observe_step base index actions coalgebra
    PUnit.unit PUnit.unit source partner

theorem observation_eq_iff_bisimilar (source other : Bag) :
    observe source = observe other ↔ Bisimilar source other :=
  (FiniteActionTreeFinalSemantics.kernel_iff_bisimilar base index actions coalgebra coalgebra
    PUnit.unit PUnit.unit source other).trans (generic_bisimilar_iff source other)

theorem bisimilar_refl (source : Bag) : Bisimilar source source :=
  (observation_eq_iff_bisimilar source source).1 rfl

theorem bisimilar_symm {source other : Bag} (related : Bisimilar source other) :
    Bisimilar other source :=
  (observation_eq_iff_bisimilar other source).1
    ((observation_eq_iff_bisimilar source other).2 related).symm

theorem bisimilar_trans {source middle other : Bag}
    (first : Bisimilar source middle) (second : Bisimilar middle other) :
    Bisimilar source other :=
  (observation_eq_iff_bisimilar source other).1
    (((observation_eq_iff_bisimilar source middle).2 first).trans
      ((observation_eq_iff_bisimilar middle other).2 second))

/-- Actual coloured cofree extension, with the supplied state readout. -/
def certificateObservation (Colours : Type) (readout : Bag → Colours) (source : Bag) :
    FiniteActionTree.Tree Bag Colours :=
  (FiniteActionTreeCofree.extend base index actions coalgebra (fun _ _ => Colours)
    (fun _ _ => ↾readout)).f PUnit.unit PUnit.unit source

theorem certificate_root (Colours : Type) (readout : Bag → Colours) (source : Bag) :
    FiniteActionTree.Tree.root (certificateObservation Colours readout source) = readout source :=
  FiniteActionTree.Tree.root_coiterate successors readout source

theorem certificate_successors (Colours : Type) (readout : Bag → Colours)
    (source partner : Bag) :
    FiniteActionTree.Tree.step (certificateObservation Colours readout source) partner =
      FinitePowerset.map (certificateObservation Colours readout) (successors source partner) :=
  FiniteActionTree.Tree.step_coiterate successors readout source partner

theorem certificate_unique (Colours : Type) (readout : Bag → Colours)
    (candidate : Bag → FiniteActionTree.Tree Bag Colours)
    (roots : ∀ source, FiniteActionTree.Tree.root (candidate source) = readout source)
    (steps : ∀ source partner, FiniteActionTree.Tree.step (candidate source) partner =
      FinitePowerset.map candidate (successors source partner)) :
    candidate = certificateObservation Colours readout := by
  funext source
  exact FiniteActionTree.Tree.coiterate_unique successors readout candidate roots steps source

/-- Forgetting supplied colours is the unique final observation, not an origin decoder. -/
theorem forget_certificate (Colours : Type) (readout : Bag → Colours) (source : Bag) :
    FiniteActionTree.Tree.map (fun _ : Colours => PUnit.unit)
      (certificateObservation Colours readout source) = observe source :=
  FiniteActionTree.Tree.map_coiterate successors readout (fun _ : Colours => PUnit.unit) source

/-- Reaction bisimulation lifts to the already established public partner system. -/
theorem public_bisimilar_of_canonical {source other : RhoProcess}
    (related : Bisimilar (fromProcess source) (fromProcess other)) :
    (ParallelContextAdequacy.partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
      source other := by
  obtain ⟨relation, admitted, held⟩ := related
  refine ⟨fun first second => relation (fromProcess first) (fromProcess second),
    ⟨?_, ?_, ?_⟩, held⟩
  · intro first second related partner target step
    have reaction : Reaction (append (fromProcess first) (fromProcess partner))
        (fromProcess target) :=
      (mem_successors_iff_reaction _ _ _).1
        ((mem_successors_iff_public first partner target).2 step)
    obtain ⟨matched, matchedReaction, relatedTargets⟩ :=
      (admitted _ _ related (fromProcess partner)).1 _ reaction
    refine ⟨toProcess matched, ?_, ?_⟩
    · exact (mem_successors_iff_public second partner (toProcess matched)).1
        (by simpa only [fromProcess_toProcess] using
          (mem_successors_iff_reaction _ _ _).2 matchedReaction)
    · simpa only [fromProcess_toProcess] using relatedTargets
  · intro first second related partner target step
    have reaction : Reaction (append (fromProcess second) (fromProcess partner))
        (fromProcess target) :=
      (mem_successors_iff_reaction _ _ _).1
        ((mem_successors_iff_public second partner target).2 step)
    obtain ⟨matched, matchedReaction, relatedTargets⟩ :=
      (admitted _ _ related (fromProcess partner)).2 _ reaction
    refine ⟨toProcess matched, ?_, ?_⟩
    · exact (mem_successors_iff_public first partner (toProcess matched)).1
        (by simpa only [fromProcess_toProcess] using
          (mem_successors_iff_reaction _ _ _).2 matchedReaction)
    · simpa only [fromProcess_toProcess] using relatedTargets
  · intro _ _ _ atom
    exact atom.elim

/-- A public relation descends by retaining its raw origins until after matching. -/
theorem canonical_bisimilar_of_public {source other : RhoProcess}
    (related :
      (ParallelContextAdequacy.partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
        source other) : Bisimilar (fromProcess source) (fromProcess other) := by
  obtain ⟨relation, ⟨forward, backward, _⟩, held⟩ := related
  let descended : Bag → Bag → Prop := fun first second =>
    ∃ rawFirst rawSecond, relation rawFirst rawSecond ∧
      fromProcess rawFirst = first ∧ fromProcess rawSecond = second
  refine ⟨descended, ?_, source, other, held, rfl, rfl⟩
  rintro _ _ ⟨first, second, paired, rfl, rfl⟩ partner
  constructor
  · intro target reaction
    have step : rhoLanguageDefGSLT.Step
        (ParallelContextAdequacy.par first (toProcess partner)) (toProcess target) :=
      (mem_successors_iff_public first (toProcess partner) (toProcess target)).1
        (by simpa only [fromProcess_toProcess] using
          (mem_successors_iff_reaction _ _ _).2 reaction)
    obtain ⟨matched, matchedStep, matchedPair⟩ := forward paired (toProcess partner) step
    refine ⟨fromProcess matched, ?_, toProcess target, matched, matchedPair, ?_, rfl⟩
    · simpa only [fromProcess_toProcess] using
        (mem_successors_iff_reaction _ _ _).1
          ((mem_successors_iff_public second (toProcess partner) matched).2 matchedStep)
    · exact fromProcess_toProcess target
  · intro target reaction
    have step : rhoLanguageDefGSLT.Step
        (ParallelContextAdequacy.par second (toProcess partner)) (toProcess target) :=
      (mem_successors_iff_public second (toProcess partner) (toProcess target)).1
        (by simpa only [fromProcess_toProcess] using
          (mem_successors_iff_reaction _ _ _).2 reaction)
    obtain ⟨matched, matchedStep, matchedPair⟩ := backward paired (toProcess partner) step
    refine ⟨fromProcess matched, ?_, matched, toProcess target, matchedPair, rfl, ?_⟩
    · simpa only [fromProcess_toProcess] using
        (mem_successors_iff_reaction _ _ _).1
          ((mem_successors_iff_public first (toProcess partner) matched).2 matchedStep)
    · exact fromProcess_toProcess target

theorem public_bisimilar_iff_canonical (source other : RhoProcess) :
    (ParallelContextAdequacy.partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
        source other ↔ Bisimilar (fromProcess source) (fromProcess other) :=
  ⟨canonical_bisimilar_of_public, public_bisimilar_of_canonical⟩

theorem public_bisimilar_iff_final_observation (source other : RhoProcess) :
    (ParallelContextAdequacy.partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
        source other ↔ observe (fromProcess source) = observe (fromProcess other) :=
  (public_bisimilar_iff_canonical source other).trans
    (observation_eq_iff_bisimilar (fromProcess source) (fromProcess other)).symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerObservations
