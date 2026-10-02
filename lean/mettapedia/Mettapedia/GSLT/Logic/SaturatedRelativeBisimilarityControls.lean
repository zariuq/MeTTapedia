import Mettapedia.GSLT.Logic.ObserverDetermination

/-!
# Controls for saturated relative bisimilarity and observer determination

Three small systems, each a negative control for one tempting claim.

* `TokenAbsorption`: **saturated bisimilarity is not contained in
  least-enabler bisimilarity.**  An absorbable token and nothing are equivalent
  under every context (`relEquiv_token_nothing`), yet the token has a
  transition whose least enabling context is a catalyst, and nothing has no
  transition with that label (`not_labelledBisimilar_token_nothing`).  The
  inclusion that holds is the other one (`labelledBisimilar_le_relEquiv`).

* `FrozenRelease`: **the contextual equivalence can be strictly coarser than
  the saturated one.**  Two processes are reduction bisimilar in every context
  (`contextualEquiv_start`), but after one step a freezing context, applied
  late, separates the residuals (`not_relEquiv_start`).  Applied early, it
  freezes the processes before they can step.

* `MixedVariance`: **determination is not monotone, and preservation is of
  mixed variance.**  A context can preserve a coarse relation and not a finer
  one (`collapse`), and another can preserve the finer relation and not the
  coarse one (`release`).  Consequently there are classes `A ≤ B` with
  `A.determined obs ≰ B.determined obs` (`determined_not_monotone`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.AdmissibleContextCongruence.SaturatedControls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass

/-! ## Minimal labels are strictly finer than saturated labels -/

namespace TokenAbsorption

/-- A configuration counts absorbable tokens and catalysts. -/
abbrev Config := ℕ × ℕ

/-- One token is absorbed in the presence of a catalyst. -/
def Absorbs (source target : Config) : Prop :=
  1 ≤ source.1 ∧ 1 ≤ source.2 ∧ target = (source.1 - 1, source.2)

/-- A configuration may stay put or absorb a token. -/
abbrev tokenGSLT : GSLT where
  Term := Config
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := target = source ∨ Absorbs source target
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- The two authored rules. -/
inductive TokenRule where
  | idle
  | absorb
  deriving DecidableEq

/-- Firing of each rule. -/
def tokenFires : TokenRule → Config → Config → Prop
  | .idle, source, target => target = source
  | .absorb, source, target => Absorbs source target

/-- Contexts add tokens and catalysts. -/
abbrev tokenRules : ContextualRules tokenGSLT where
  Context := Config
  identity := (0, 0)
  compose outer inner := outer + inner
  plug context term := context + term
  plug_identity term := Prod.ext (Nat.zero_add _) (Nat.zero_add _)
  plug_compose outer inner term := add_assoc outer inner term
  plug_resp context := by
    intro left right equal
    subst equal
    rfl
  Rule := TokenRule
  fires := tokenFires
  fires_resp_left := by
    intro rule left right target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro rule source target target' fires equal
    subst equal
    exact fires
  fires_step := by
    intro rule source target fires
    cases rule with
    | idle => exact Or.inl fires
    | absorb => exact Or.inr fires

/-- The only observation: a catalyst is present. -/
abbrev catalystPresent : ContextualRules.Observations tokenGSLT where
  Atom := Unit
  observes _ term := 1 ≤ term.2
  observes_resp := by
    intro _ left right equal
    subst equal
    exact Iff.rfl

/-- Nothing, and one absorbable token. -/
def nothing : Config := (0, 0)
def token : Config := (1, 0)

/-- Two configurations related when the right one carries one extra token. -/
def extraToken (left right : Config) : Prop :=
  right = left ∨ right = (left.1 + 1, left.2)

theorem extraToken_isReductionBisimulation :
    IsReductionBisimulation catalystPresent extraToken := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro left right related left' step
    rcases related with rfl | rfl
    · exact ⟨left', step, Or.inl rfl⟩
    · rcases step with equal | ⟨hasToken, hasCatalyst, equal⟩
      · subst left'
        exact ⟨(left.1 + 1, left.2), Or.inl rfl, Or.inr rfl⟩
      · subst left'
        refine ⟨(left.1, left.2), Or.inr ⟨by omega, hasCatalyst, ?_⟩, Or.inr ?_⟩
        · exact Prod.ext (Nat.add_sub_cancel left.1 1).symm rfl
        · exact Prod.ext (Nat.sub_add_cancel hasToken).symm rfl
  · intro left right related right' step
    rcases related with rfl | rfl
    · exact ⟨right', step, Or.inl rfl⟩
    · rcases step with rfl | ⟨_, hasCatalyst, rfl⟩
      · exact ⟨left, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨left, Or.inl rfl, Or.inl (Prod.ext (Nat.add_sub_cancel left.1 1) rfl)⟩
  · intro left right related _
    rcases related with rfl | rfl <;> exact Iff.rfl

theorem extraToken_closedUnder : (⊤ : AdmissibleClass tokenRules).ClosedUnder extraToken := by
  intro context left right _ related
  rcases related with rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr (Prod.ext ?_ ?_)
    · change context.1 + (left.1 + 1) = (context.1 + left.1) + 1
      omega
    · rfl

/-- **Saturated equivalence identifies nothing with a lone token.** -/
theorem relEquiv_token_nothing :
    (⊤ : AdmissibleClass tokenRules).RelEquiv catalystPresent nothing token :=
  (⊤ : AdmissibleClass tokenRules).relEquiv_of_isReductionBisimulation catalystPresent
    extraToken_isReductionBisimulation extraToken_closedUnder (Or.inr rfl)

/-- The catalyst is a least enabling context of absorption at a lone token. -/
theorem catalyst_isLeastEnabler :
    tokenRules.IsLeastEnabler (0, 1) token .absorb := by
  refine ⟨⟨(0, 1), by decide, by decide, rfl⟩, ?_⟩
  rintro other ⟨target, _, hasCatalyst, _⟩
  refine ⟨(other.1, other.2 - 1), fun term => ?_⟩
  change other + term = (other.1, other.2 - 1) + ((0, 1) + term)
  change 1 ≤ other.2 + 0 at hasCatalyst
  refine Prod.ext ?_ ?_
  · change other.1 + term.1 = other.1 + (0 + term.1)
    omega
  · change other.2 + term.2 = (other.2 - 1) + (1 + term.2)
    omega

/-- Nothing has no transition whose least enabling context is the catalyst. -/
theorem no_catalyst_transition_from_nothing (target : Config) :
    ¬ tokenRules.Act (0, 1) nothing target := by
  rintro ⟨rule, least, fires⟩
  cases rule with
  | idle =>
      obtain ⟨residual, factors⟩ := least.2 (0, 0) ⟨(0, 0), rfl⟩
      have atZero := congrArg Prod.snd (factors (0, 0))
      change 0 + 0 = residual.2 + (1 + 0) at atZero
      omega
  | absorb =>
      obtain ⟨hasToken, _, _⟩ := fires
      exact absurd hasToken (by decide)

/-- **Least-enabler bisimilarity separates them.** -/
theorem not_labelledBisimilar_token_nothing :
    ¬ ((⊤ : AdmissibleClass tokenRules).labelledSystem catalystPresent).Bisimilar nothing token := by
  intro bisimilar
  obtain ⟨_, step, _⟩ := AdmissibleContextCongruence.bisimilar_backward bisimilar
    ⟨(0, 1), top_admissible _⟩
    (⟨.absorb, catalyst_isLeastEnabler, by decide, by decide, rfl⟩ :
      tokenRules.Act (0, 1) token (0, 1))
  exact no_catalyst_transition_from_nothing _ step

/-- **The inclusion of saturated in least-enabler bisimilarity fails.** -/
theorem relEquiv_not_le_labelledBisimilar :
    ¬ ∀ left right : Config,
        (⊤ : AdmissibleClass tokenRules).RelEquiv catalystPresent left right →
          ((⊤ : AdmissibleClass tokenRules).labelledSystem catalystPresent).Bisimilar left right :=
  fun included => not_labelledBisimilar_token_nothing (included _ _ relEquiv_token_nothing)

end TokenAbsorption

/-! ## The contextual equivalence can be strictly coarser -/

namespace FrozenRelease

/-- The four stages of two processes. -/
inductive Stage where
  | start
  | startAlt
  | released
  | releasedAlt
  deriving DecidableEq

/-- A term is a stage together with a frozen flag. -/
abbrev FrozenTerm := Bool × Stage

/-- Only unfrozen starting processes step. -/
inductive Releases : FrozenTerm → FrozenTerm → Prop where
  | first : Releases (false, .start) (false, .released)
  | second : Releases (false, .startAlt) (false, .releasedAlt)

abbrev frozenGSLT : GSLT where
  Term := FrozenTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Releases
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- A context either leaves a term alone or freezes it. -/
abbrev frozenRules : ContextualRules frozenGSLT where
  Context := Bool
  identity := false
  compose outer inner := outer || inner
  plug context term := (context || term.1, term.2)
  plug_identity term := by cases term; rfl
  plug_compose outer inner term := by cases outer <;> cases inner <;> rfl
  plug_resp context := by
    intro left right equal
    subst equal
    rfl
  Rule := Unit
  fires _ := Releases
  fires_resp_left := by
    intro _ left right target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ source target target' fires equal
    subst equal
    exact fires
  fires_step := fun fires => fires

/-- The only observation: a released first process, frozen. -/
abbrev frozenRelease : ContextualRules.Observations frozenGSLT where
  Atom := Unit
  observes _ term := term = (true, .released)
  observes_resp := by
    intro _ left right equal
    subst equal
    exact Iff.rfl

/-- The pairs identified in every context. -/
def sameUpToAlt (left right : FrozenTerm) : Prop :=
  (left = (false, .start) ∧ right = (false, .startAlt)) ∨
    (left = (false, .released) ∧ right = (false, .releasedAlt)) ∨
    (left = (true, .start) ∧ right = (true, .startAlt))

theorem sameUpToAlt_isReductionBisimulation :
    IsReductionBisimulation frozenRelease sameUpToAlt := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro left right related left' step
    rcases related with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases step
    exact ⟨(false, .releasedAlt), .second, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · intro left right related right' step
    rcases related with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases step
    exact ⟨(false, .released), .first, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · intro left right related atom
    cases atom
    rcases related with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- **Contextually equivalent**: in each context the two starting processes are
reduction bisimilar. -/
theorem contextualEquiv_start :
    (⊤ : AdmissibleClass frozenRules).ContextualEquiv frozenRelease (false, .start)
      (false, .startAlt) := by
  intro context _
  refine ⟨sameUpToAlt, sameUpToAlt_isReductionBisimulation, ?_⟩
  cases context
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **Not saturated-equivalent**: freezing after the release step separates the
residuals. -/
theorem not_relEquiv_start :
    ¬ (⊤ : AdmissibleClass frozenRules).RelEquiv frozenRelease (false, .start)
      (false, .startAlt) := by
  intro related
  obtain ⟨residual, step, residualRelated⟩ :=
    AdmissibleContextCongruence.bisimilar_forward related ⟨false, top_admissible _⟩
      (Releases.first : frozenGSLT.Step (frozenRules.plug false (false, .start))
        (false, .released))
  cases step
  have agree := AdmissibleContextCongruence.bisimilar_observes residualRelated
    ((), ⟨true, top_admissible _⟩)
  have image : ((true, Stage.releasedAlt) : FrozenTerm) = (true, .released) := agree.mp rfl
  exact absurd image (by decide)

/-- The saturated equivalence is strictly finer than the contextual one. -/
theorem contextualEquiv_not_le_relEquiv :
    ¬ ∀ left right : FrozenTerm,
        (⊤ : AdmissibleClass frozenRules).ContextualEquiv frozenRelease left right →
          (⊤ : AdmissibleClass frozenRules).RelEquiv frozenRelease left right :=
  fun included => not_relEquiv_start (included _ _ contextualEquiv_start)

end FrozenRelease

/-! ## Preservation is of mixed variance; determination is not monotone -/

namespace MixedVariance

/-- Four inert points. -/
inductive Point where
  | a
  | b
  | c
  | d
  deriving DecidableEq

abbrev pointGSLT : GSLT where
  Term := Point
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

/-- Every function on points is a context. -/
abbrev pointRules : ContextualRules pointGSLT where
  Context := Point → Point
  identity := id
  compose outer inner := outer ∘ inner
  plug context term := context term
  plug_identity _ := rfl
  plug_compose _ _ _ := rfl
  plug_resp context := by
    intro left right equal
    subst equal
    rfl
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

/-- The only observation: membership in `{c, d}`. -/
def InCD (point : Point) : Prop := point = .c ∨ point = .d

instance : DecidablePred InCD := fun point => by unfold InCD; infer_instance

abbrev inCD : ContextualRules.Observations pointGSLT where
  Atom := Unit
  observes _ point := InCD point
  observes_resp := by
    intro _ left right equal
    subst equal
    exact Iff.rfl

/-- Merges `c` into `d`'s class by mapping everything into `{c, d}`. -/
def collapse : Point → Point
  | .a => .c
  | .b => .d
  | .c => .c
  | .d => .c

/-- Separates `c` from `d`, fixing `a` and `b`. -/
def split : Point → Point
  | .a => .a
  | .b => .b
  | .c => .c
  | .d => .a

/-- Sends `c` out of `{c, d}`, fixing `a` and `b`. -/
def release : Point → Point
  | .a => .a
  | .b => .b
  | .c => .a
  | .d => .c

/-- The class with no generators, whose contexts are identities. -/
abbrev bottom : AdmissibleClass pointRules := generatedBy ∅

/-- The class generated by `split`. -/
abbrev splitting : AdmissibleClass pointRules := generatedBy {split}

theorem bottom_le_splitting : bottom ≤ splitting :=
  generatedBy_le_iff.mpr (Set.empty_subset _)

/-- The class of identity contexts. -/
def identities : AdmissibleClass pointRules where
  Admissible context := context = id
  identity_mem := rfl
  compose_mem := by
    rintro _ _ rfl rfl
    rfl

/-- The class of contexts fixing `a` and `b`. -/
def fixingAB : AdmissibleClass pointRules where
  Admissible context := context .a = .a ∧ context .b = .b
  identity_mem := ⟨rfl, rfl⟩
  compose_mem := by
    rintro outer inner ⟨outerA, outerB⟩ ⟨innerA, innerB⟩
    refine ⟨?_, ?_⟩
    · change outer (inner .a) = .a
      rw [innerA, outerA]
    · change outer (inner .b) = .b
      rw [innerB, outerB]

theorem bottom_context_eq_id {context : Point → Point}
    (admissible : bottom.Admissible context) : context = id :=
  (generatedBy_le_iff.mpr (Set.empty_subset _) : bottom ≤ identities) context admissible

theorem splitting_fixes_ab {context : Point → Point}
    (admissible : splitting.Admissible context) : context .a = .a ∧ context .b = .b :=
  (generatedBy_le_iff.mpr (by rintro _ rfl; exact ⟨rfl, rfl⟩) : splitting ≤ fixingAB)
    context admissible

/-- The bottom equivalence is agreement on the observation. -/
theorem bottom_relEquiv_iff (left right : Point) :
    bottom.RelEquiv inCD left right ↔ (InCD left ↔ InCD right) := by
  constructor
  · intro related
    exact AdmissibleContextCongruence.bisimilar_observes related ((), ⟨id, bottom.identity_mem⟩)
  · intro agree
    refine ⟨fun first second => InCD first ↔ InCD second, ⟨?_, ?_, ?_⟩, agree⟩
    · intro _ _ _ _ _ impossible
      exact impossible.elim
    · intro _ _ _ _ _ impossible
      exact impossible.elim
    · intro first second held atom
      have identity := bottom_context_eq_id atom.2.2
      change InCD (atom.2.1 first) ↔ InCD (atom.2.1 second)
      rw [identity]
      exact held

/-- The splitting equivalence identifies `a` and `b`. -/
theorem splitting_relEquiv_a_b : splitting.RelEquiv inCD .a .b := by
  refine ⟨fun first second => first = .a ∧ second = .b, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · intro _ _ _ _ _ impossible
    exact impossible.elim
  · intro _ _ _ _ _ impossible
    exact impossible.elim
  · rintro first second ⟨rfl, rfl⟩ atom
    have fixes := splitting_fixes_ab atom.2.2
    change InCD (atom.2.1 .a) ↔ InCD (atom.2.1 .b)
    rw [fixes.1, fixes.2]
    decide

/-- The splitting equivalence separates `c` from `d`. -/
theorem not_splitting_relEquiv_c_d : ¬ splitting.RelEquiv inCD .c .d := by
  intro related
  have agree := AdmissibleContextCongruence.bisimilar_observes related
    ((), ⟨split, generator_mem rfl⟩)
  have image : InCD (split .d) := agree.mp (Or.inl rfl)
  exact absurd image (by decide)

/-- The splitting equivalence is equality up to swapping `a` and `b`. -/
theorem splitting_relEquiv_iff (left right : Point) :
    splitting.RelEquiv inCD left right ↔
      left = right ∨ (left = .a ∧ right = .b) ∨ (left = .b ∧ right = .a) := by
  constructor
  · intro related
    have base := AdmissibleContextCongruence.bisimilar_observes related
      ((), ⟨id, splitting.identity_mem⟩)
    have viaSplit := AdmissibleContextCongruence.bisimilar_observes related
      ((), ⟨split, generator_mem rfl⟩)
    change InCD left ↔ InCD right at base
    change InCD (split left) ↔ InCD (split right) at viaSplit
    cases left <;> cases right <;> simp_all [InCD, split]
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact splitting.relEquiv_refl inCD _
    · exact splitting_relEquiv_a_b
    · exact splitting.relEquiv_symm inCD splitting_relEquiv_a_b

/-- **`collapse` preserves the coarse relation and not the fine one.** -/
theorem collapse_preserves_bottom : Preserves (rules := pointRules) collapse (bottom.RelEquiv inCD) := by
  intro left right _
  rw [bottom_relEquiv_iff]
  cases left <;> cases right <;> decide

theorem collapse_not_preserves_splitting :
    ¬ Preserves (rules := pointRules) collapse (splitting.RelEquiv inCD) :=
  fun preserves => not_splitting_relEquiv_c_d (preserves splitting_relEquiv_a_b)

/-- **`release` preserves the fine relation and not the coarse one.** -/
theorem release_preserves_splitting :
    Preserves (rules := pointRules) release (splitting.RelEquiv inCD) := by
  intro left right related
  rw [splitting_relEquiv_iff] at related ⊢
  rcases related with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem release_not_preserves_bottom :
    ¬ Preserves (rules := pointRules) release (bottom.RelEquiv inCD) := by
  intro preserves
  have related : bottom.RelEquiv inCD .c .d := (bottom_relEquiv_iff _ _).mpr (by decide)
  have image := (bottom_relEquiv_iff _ _).mp (preserves related)
  exact absurd image (by decide)

/-- The fine relation is contained in the coarse one. -/
theorem splitting_le_bottom {left right : Point} (related : splitting.RelEquiv inCD left right) :
    bottom.RelEquiv inCD left right :=
  AdmissibleClass.relEquiv_antitone inCD bottom_le_splitting related

/-- **Preservation is neither monotone nor antitone in the relation.** -/
theorem preservation_mixed_variance :
    (∀ left right, splitting.RelEquiv inCD left right → bottom.RelEquiv inCD left right) ∧
      (Preserves (rules := pointRules) collapse (bottom.RelEquiv inCD) ∧
        ¬ Preserves (rules := pointRules) collapse (splitting.RelEquiv inCD)) ∧
      (Preserves (rules := pointRules) release (splitting.RelEquiv inCD) ∧
        ¬ Preserves (rules := pointRules) release (bottom.RelEquiv inCD)) :=
  ⟨fun _ _ => splitting_le_bottom, ⟨collapse_preserves_bottom, collapse_not_preserves_splitting⟩,
    ⟨release_preserves_splitting, release_not_preserves_bottom⟩⟩

/-- **Determination is not monotone.** -/
theorem determined_not_monotone :
    bottom ≤ splitting ∧ ¬ bottom.determined inCD ≤ splitting.determined inCD := by
  refine ⟨bottom_le_splitting, fun le => ?_⟩
  exact collapse_not_preserves_splitting (le collapse collapse_preserves_bottom)

end MixedVariance

end Mettapedia.GSLT.AdmissibleContextCongruence.SaturatedControls
