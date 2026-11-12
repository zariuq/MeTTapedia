import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence

/-!
# Spatial guards under coexistence

Positive guards persist under growth without a blindness condition. Exact counts
persist precisely when the context contributes no new matching identity; a
matching identity already present may be shared. The quantified criterion is
needed only at solutions of the joint knowledge, not at all substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF

namespace Coexistence

abbrev SpatialGuard {Obj : Type uO} (Hom : Obj → Obj → Type uH)
    (O : Type uOcc) (a : Obj) := (b : Obj) → Hom a b → Finset O → Prop

namespace SpatialGuard

variable {Obj : Type uO} {Hom : Obj → Obj → Type uH} {O : Type uOcc} {a : Obj}

def Monotone (guard : SpatialGuard Hom O a) : Prop :=
  ∀ (b : Obj) (σ : Hom a b) {small big : Finset O},
    small ⊆ big → guard b σ small → guard b σ big

end SpatialGuard

section Matching

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {a b : Obj} (X : Frames Tm Hom)

noncomputable def matchedOccurrences (σ : Hom a b) (label : O → Tm a)
    (pattern : Tm a) (store : Finset O) : Finset O := by
  classical
  exact store.filter fun occurrence => X.E (X.act σ pattern) (X.act σ (label occurrence))

@[simp] theorem mem_matches (σ : Hom a b) (label : O → Tm a) (pattern : Tm a)
    (store : Finset O) (occurrence : O) : occurrence ∈ matchedOccurrences X σ label pattern store ↔
      occurrence ∈ store ∧ X.E (X.act σ pattern) (X.act σ (label occurrence)) := by
  classical
  exact Finset.mem_filter

theorem matches_mono (σ : Hom a b) (label : O → Tm a) (pattern : Tm a)
    {small big : Finset O} (inside : small ⊆ big) :
    matchedOccurrences X σ label pattern small ⊆ matchedOccurrences X σ label pattern big := by
  intro occurrence member
  obtain ⟨present, matched⟩ := (mem_matches X σ label pattern small occurrence).mp member
  exact (mem_matches X σ label pattern big occurrence).mpr ⟨inside present, matched⟩

noncomputable def hasMatch (label : O → Tm a) (pattern : Tm a) : SpatialGuard Hom O a :=
  fun _ σ store => (matchedOccurrences X σ label pattern store).Nonempty

noncomputable def atLeast (label : O → Tm a) (pattern : Tm a) (number : Nat) :
    SpatialGuard Hom O a := fun _ σ store => number ≤ (matchedOccurrences X σ label pattern store).card

theorem hasMatch_monotone (label : O → Tm a) (pattern : Tm a) :
    SpatialGuard.Monotone (hasMatch X label pattern) := by
  intro b σ small big inside witnessed
  obtain ⟨occurrence, member⟩ := witnessed
  exact ⟨occurrence, matches_mono X σ label pattern inside member⟩

theorem atLeast_monotone (label : O → Tm a) (pattern : Tm a) (number : Nat) :
    SpatialGuard.Monotone (atLeast X label pattern number) := by
  intro b σ small big inside enough
  exact enough.trans (Finset.card_le_card (matches_mono X σ label pattern inside))

def NoNewMatches (σ : Hom a b) (label : O → Tm a) (pattern : Tm a)
    (store context : Finset O) : Prop :=
  ∀ occurrence ∈ context, X.E (X.act σ pattern) (X.act σ (label occurrence)) → occurrence ∈ store

variable [DecidableEq O]

theorem matches_union (σ : Hom a b) (label : O → Tm a) (pattern : Tm a)
    (store context : Finset O) :
    matchedOccurrences X σ label pattern (store ∪ context) =
      matchedOccurrences X σ label pattern store ∪ matchedOccurrences X σ label pattern context := by
  ext occurrence
  simp only [mem_matches, Finset.mem_union]
  tauto

/-- An unconditional decomposition counts a shared matching identity once. -/
theorem count_union (σ : Hom a b) (label : O → Tm a) (pattern : Tm a)
    (store context : Finset O) :
    (matchedOccurrences X σ label pattern (store ∪ context)).card =
      (matchedOccurrences X σ label pattern store).card +
        (matchedOccurrences X σ label pattern context \ matchedOccurrences X σ label pattern store).card := by
  rw [matches_union]
  calc
    _ = (matchedOccurrences X σ label pattern context ∪ matchedOccurrences X σ label pattern store).card :=
      congrArg Finset.card (Finset.union_comm _ _)
    _ = (matchedOccurrences X σ label pattern context \ matchedOccurrences X σ label pattern store).card +
        (matchedOccurrences X σ label pattern store).card := (Finset.card_sdiff_add_card _ _).symm
    _ = _ := Nat.add_comm _ _

theorem count_unchanged_iff (σ : Hom a b) (label : O → Tm a) (pattern : Tm a)
    (store context : Finset O) :
    (matchedOccurrences X σ label pattern (store ∪ context)).card = (matchedOccurrences X σ label pattern store).card ↔
      NoNewMatches X σ label pattern store context := by
  have inside := matches_mono X σ label pattern
    (show store ⊆ store ∪ context from Finset.subset_union_left)
  constructor
  · intro counts occurrence inContext matched
    have sets := Finset.eq_of_subset_of_card_le inside counts.le
    have member : occurrence ∈ matchedOccurrences X σ label pattern (store ∪ context) :=
      (mem_matches X σ label pattern _ occurrence).mpr ⟨Finset.mem_union_right _ inContext, matched⟩
    rw [← sets] at member
    exact ((mem_matches X σ label pattern store occurrence).mp member).1
  · intro noNew
    have sets : matchedOccurrences X σ label pattern (store ∪ context) = matchedOccurrences X σ label pattern store := by
      ext occurrence
      simp only [mem_matches, Finset.mem_union]
      constructor
      · rintro ⟨present | inContext, matched⟩
        · exact ⟨present, matched⟩
        · exact ⟨noNew occurrence inContext matched, matched⟩
      · rintro ⟨present, matched⟩
        exact ⟨Or.inl present, matched⟩
    exact congrArg Finset.card sets

theorem absence_stable_iff (σ : Hom a b) (label : O → Tm a) (pattern : Tm a)
    (store context : Finset O) (absent : matchedOccurrences X σ label pattern store = ∅) :
    matchedOccurrences X σ label pattern (store ∪ context) = ∅ ↔ matchedOccurrences X σ label pattern context = ∅ := by
  rw [matches_union, absent, Finset.empty_union]

/-- The exact criterion is checked only at solutions of the joint knowledge. -/
theorem entails_count_iff (label : O → Tm a) (pattern : Tm a) (store context : Finset O)
    (joint : EquationStore (Tm a)) (number : Nat)
    (counted : X.Entails joint
      (fun _ σ => (matchedOccurrences X σ label pattern store).card = number)) :
    X.Entails joint (fun _ σ => (matchedOccurrences X σ label pattern (store ∪ context)).card = number) ↔
      X.Entails joint (fun _ σ => NoNewMatches X σ label pattern store context) := by
  constructor
  · intro jointCount b σ solved
    apply (count_unchanged_iff X σ label pattern store context).mp
    exact (jointCount b σ solved).trans (counted b σ solved).symm
  · intro noNew b σ solved
    exact ((count_unchanged_iff X σ label pattern store context).mpr
      (noNew b σ solved)).trans (counted b σ solved)

end Matching

namespace SpatialGuard

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {a : Obj} (X : Frames Tm Hom)

theorem entails_of_refinement (guard : SpatialGuard Hom O a) (monotone : guard.Monotone)
    {knowledge joint : EquationStore (Tm a)} {store larger : Finset O}
    (refines : ∀ (b : Obj) (σ : Hom a b), X.Models σ joint → X.Models σ knowledge)
    (inside : store ⊆ larger)
    (holds : X.Entails knowledge (fun b σ => guard b σ store)) :
    X.Entails joint (fun b σ => guard b σ larger) :=
  fun b σ solved => monotone b σ inside (holds b σ (refines b σ solved))

end SpatialGuard

end Coexistence

namespace EffectCore

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

/-- The general core's semantic refinement supplies the knowledge half of positive framing. -/
theorem information_preserves_monotone_guard (effect : EffectCore X O State Firing)
    {state : State} (firing : Firing state)
    (guard : Coexistence.SpatialGuard Hom O (effect.frame state))
    (monotone : guard.Monotone) {larger : Finset O} (inside : effect.present state ⊆ larger)
    (holds : X.Entails (effect.knowledge state) (fun b σ => guard b σ (effect.present state))) :
    X.Entails (effect.information firing)
      (fun b σ => guard b (X.comp σ (effect.extension firing)) larger) := by
  intro b σ solved
  exact monotone b (X.comp σ (effect.extension firing)) inside
    (holds b _ (effect.information_refines firing σ solved))

end EffectCore
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
