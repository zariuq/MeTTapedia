import Mettapedia.GSLT.Logic.RedexRelativeCongruence
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Interface-changing IPO congruence in the category of types

Ordinary pushouts in `Type` discharge the RPO hypothesis for arbitrary
interfaces. The flip rule below has real transitions and two distinct
behaviorally related agents. Context filling changes the interface from
`Bool` to `Option Bool` and descends to their behavioral classes.

The separate terminal-redex control distinguishes an identity-labelled
reaction from one requiring interface collapse. It makes no claim that an
agent unable to take that label is globally unable to react.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RedexRelativeCongruence.TypeIPOContextCongruenceControls

open CategoryTheory CategoryTheory.Limits
open Mettapedia.GSLT.RelativePushout

universe u

/-- Every Type span has genuine relative pushouts, derived from its ordinary
pushout rather than a one-object context monoid. -/
theorem type_hasRelativePushouts {W X Y : Type u} (f : W ⟶ X) (g : W ⟶ Y) :
    HasRelativePushouts f g := hasRelativePushouts_of_hasPushout

/-- The RPO assumption in the generic contextual-congruence theorem is
discharged for every reactive rule family in `Type`, including interface-changing
contexts. Labels remain literal and there are no added observations. -/
theorem type_ipoBisimilar_comp {origin X Y : Type u}
    {rules : ReactionRule origin → Prop} {left right : origin ⟶ X}
    (related : IPOBisimilar rules left right) (context : X ⟶ Y) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => type_hasRelativePushouts agent rule.redex)
    related context

def flip : (Bool : Type) ⟶ Bool := TypeCat.ofHom Bool.not

@[simp] theorem flip_comp_flip : flip ≫ flip = 𝟙 (Bool : Type) := by
  ext value
  cases value <;> rfl

instance : IsIso flip := ⟨flip, flip_comp_flip, flip_comp_flip⟩

def flipRule : ReactionRule (Bool : Type) where
  codomain := Bool
  redex := 𝟙 Bool
  reactum := flip

def flipRules : ReactionRule (Bool : Type) → Prop := fun rule => rule = flipRule

private theorem identity_redex_ipo_iff {X Y : Type}
    (agent : (Bool : Type) ⟶ X) (label : X ⟶ Y)
    (square : agent ≫ label = 𝟙 (Bool : Type) ≫ (agent ≫ label)) :
    IsIdemPushout agent (𝟙 (Bool : Type)) label (agent ≫ label) square ↔ IsIso label := by
  constructor
  · intro ipo
    let smaller : Candidate agent (𝟙 (Bool : Type)) label (agent ≫ label) :=
      { apex := X
        inl := 𝟙 X
        inr := agent
        down := label
        comm := by simp
        fac_left := by simp
        fac_right := rfl }
    obtain ⟨inverse, ⟨left, -, down⟩, -⟩ := ipo smaller
    exact ⟨inverse, left, down⟩
  · intro invertible
    let : IsIso label := invertible
    exact isIdemPushout_of_isPushout (IsPushout.of_vert_isIso ⟨square⟩)

/-- For this actual rule, labels are precisely interface isomorphisms and
the returned agent is the input-dependent Boolean flip through that label. -/
theorem flip_step_iff {X Y : Type} (label : X ⟶ Y)
    (agent : (Bool : Type) ⟶ X) (target : (Bool : Type) ⟶ Y) :
    ActIPO flipRules label agent target ↔
      IsIso label ∧ target = flip ≫ agent ≫ label := by
  constructor
  · rintro ⟨rule, admitted, reaction, square, ipo, returned⟩
    change rule = flipRule at admitted
    subst rule
    have reactionEq : reaction = agent ≫ label := by
      exact (Category.id_comp reaction).symm.trans square.symm
    subst reaction
    exact ⟨(identity_redex_ipo_iff agent label square).mp ipo, returned⟩
  · rintro ⟨invertible, returned⟩
    have square : agent ≫ label = flipRule.redex ≫ (agent ≫ label) := by
      simp [flipRule]
    exact ⟨flipRule, rfl, agent ≫ label, square,
      (identity_redex_ipo_iff agent label square).mpr invertible, returned⟩

/-- Structural relation allowing exactly equality or a Boolean-origin swap,
not the indiscriminate universal relation. -/
def FlipRelated (X : Type) (left right : (Bool : Type) ⟶ X) : Prop :=
  right = left ∨ right = flip ≫ left

private theorem flipRelated_symm {X : Type} {left right : (Bool : Type) ⟶ X}
    (related : FlipRelated X left right) : FlipRelated X right left := by
  rcases related with equal | swapped
  · exact Or.inl equal.symm
  · exact Or.inr (by rw [swapped, ← Category.assoc, flip_comp_flip, Category.id_comp])

private theorem flipRelated_forward {X Y : Type} {left right : (Bool : Type) ⟶ X}
    (related : FlipRelated X left right) (label : X ⟶ Y) (next : (Bool : Type) ⟶ Y)
    (step : ActIPO flipRules label left next) :
    ∃ matched, ActIPO flipRules label right matched ∧ FlipRelated Y next matched := by
  obtain ⟨invertible, returned⟩ := (flip_step_iff label left next).mp step
  refine ⟨flip ≫ right ≫ label,
    (flip_step_iff label right _).mpr ⟨invertible, rfl⟩, ?_⟩
  rcases related with equal | swapped
  · exact Or.inl (by rw [equal, returned])
  · exact Or.inr (by rw [returned, swapped]; simp [← Category.assoc])

theorem flipRelated_is_bisimulation : IsIPOBisimulation flipRules FlipRelated := by
  intro interface left right related
  refine ⟨fun label next step => flipRelated_forward related label next step, ?_⟩
  intro nextInterface label next step
  obtain ⟨matched, matchedStep, matchedRelated⟩ :=
    flipRelated_forward (flipRelated_symm related) label next step
  exact ⟨matched, matchedStep, flipRelated_symm matchedRelated⟩

theorem distinct_agents_bisimilar : IPOBisimilar flipRules (𝟙 (Bool : Type)) flip :=
  ⟨FlipRelated, flipRelated_is_bisimulation, Or.inr (by simp)⟩

theorem agents_really_differ : (𝟙 (Bool : Type)) ≠ flip := by
  intro equal
  have atFalse := congrArg (fun arrow : (Bool : Type) ⟶ Bool => arrow false) equal
  change false = true at atFalse
  cases atFalse

theorem actual_flip_transition :
    ActIPO flipRules (𝟙 (Bool : Type)) (𝟙 (Bool : Type)) flip :=
  (flip_step_iff _ _ _).mpr ⟨inferInstance, by simp⟩

def grow : (Bool : Type) ⟶ Option Bool := TypeCat.ofHom Option.some

theorem context_changes_interface_and_retains_bisimilarity :
    IPOBisimilar flipRules ((𝟙 (Bool : Type)) ≫ grow) (flip ≫ grow) :=
  type_ipoBisimilar_comp distinct_agents_bisimilar grow

theorem filled_agents_really_differ : (𝟙 (Bool : Type)) ≫ grow ≠ flip ≫ grow := by
  intro equal
  have atFalse := congrArg
    (fun arrow : (Bool : Type) ⟶ Option Bool => arrow false) equal
  change some false = some true at atFalse
  cases atFalse

theorem filled_transition_changes_payload :
    ActIPO flipRules (𝟙 (Option Bool : Type)) grow (flip ≫ grow) ∧
      (flip ≫ grow) false = some true ∧ (flip ≫ grow) true = some false := by
  exact ⟨(flip_step_iff _ _ _).mpr ⟨inferInstance, by simp⟩, rfl, rfl⟩

theorem distinct_filled_agents_share_behavioral_class :
    toClass flipRules ((𝟙 (Bool : Type)) ≫ grow) = toClass flipRules (flip ≫ grow) :=
  (class_eq_iff _ _ _).mpr context_changes_interface_and_retains_bisimilarity

def terminal : (Bool : Type) ⟶ Unit := TypeCat.ofHom (fun _ => ())

def terminalRule : ReactionRule (Bool : Type) where
  codomain := Unit
  redex := terminal
  reactum := terminal

def terminalRules : ReactionRule (Bool : Type) → Prop := fun rule => rule = terminalRule

def constantFalse : (Bool : Type) ⟶ Bool := TypeCat.ofHom (fun _ => false)

/-- This redex reacts under the identity label without needing an interface
collapse: both maps out of its Boolean origin are already constant. -/
theorem constant_agent_has_identity_step :
    ActIPO terminalRules (𝟙 (Bool : Type)) constantFalse constantFalse := by
  let reaction : (Unit : Type) ⟶ Bool := TypeCat.ofHom (fun _ => false)
  have square : constantFalse ≫ 𝟙 Bool = terminal ≫ reaction := by
    ext value
    rfl
  refine ⟨terminalRule, rfl, reaction, square, ?_, ?_⟩
  · intro candidate
    refine ⟨candidate.inl, ⟨by simp [Candidate.self], ?_, candidate.fac_left⟩, ?_⟩
    · ext value
      cases value
      have comm := congrArg (fun arrow : (Bool : Type) ⟶ candidate.apex => arrow false)
        candidate.comm
      exact comm
    · rintro mediator ⟨left, -, -⟩
      exact (Category.id_comp mediator).symm.trans left
  · rfl

/-- An injective agent cannot match the same identity-labelled reaction.
Other labels may identify its two inputs, so this is deliberately label-specific. -/
theorem injective_agent_has_no_identity_step (next : (Bool : Type) ⟶ Bool) :
    ¬ ActIPO terminalRules (𝟙 (Bool : Type)) (𝟙 (Bool : Type)) next := by
  rintro ⟨rule, admitted, reaction, square, -, -⟩
  change rule = terminalRule at admitted
  subst rule
  have atFalse := congrArg (fun arrow : (Bool : Type) ⟶ Bool => arrow false) square
  have atTrue := congrArg (fun arrow : (Bool : Type) ⟶ Bool => arrow true) square
  change false = reaction () at atFalse
  change true = reaction () at atTrue
  exact Bool.noConfusion (atFalse.trans atTrue.symm)

/-- The same injective agent does react with a least interface-collapsing
label. Failure to take the identity label is therefore not global deadlock. -/
theorem injective_agent_reacts_after_interface_collapse :
    ActIPO terminalRules terminal (𝟙 (Bool : Type)) terminal := by
  have square : (𝟙 (Bool : Type)) ≫ terminal = terminal ≫ 𝟙 Unit := by simp
  exact ⟨terminalRule, rfl, 𝟙 Unit, square,
    isIdemPushout_of_isPushout (IsPushout.of_id_fst :
      IsPushout (𝟙 (Bool : Type)) terminal terminal (𝟙 Unit)), by simp [terminalRule]⟩

theorem constant_and_injective_agents_not_bisimilar :
    ¬ IPOBisimilar terminalRules constantFalse (𝟙 (Bool : Type)) := by
  intro related
  obtain ⟨matched, step, -⟩ :=
    ipoBisimilar_forward related constant_agent_has_identity_step
  exact injective_agent_has_no_identity_step matched step

#print axioms type_hasRelativePushouts
#print axioms hasRelativePushouts_of_isPushout
#print axioms hasRelativePushouts_of_hasPushout
#print axioms type_ipoBisimilar_comp
#print axioms flip_step_iff
#print axioms flipRelated_is_bisimulation
#print axioms context_changes_interface_and_retains_bisimilarity
#print axioms distinct_filled_agents_share_behavioral_class
#print axioms constant_and_injective_agents_not_bisimilar
#print axioms injective_agent_reacts_after_interface_collapse

end Mettapedia.GSLT.RedexRelativeCongruence.TypeIPOContextCongruenceControls
