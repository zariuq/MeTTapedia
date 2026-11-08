import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RacePair

/-!
# The determinate fragment: where the spectrum collapses

Milner's determinacy theorem in the step. A program is **determinate** on a set of configurations
closed under its moves when any two successors under one label are bisimilar (`Determinate`). There,
**bisimilarity equals trace equivalence** (`bisimilar_iff_traceEquivalent`): the linear-time /
branching-time spectrum is a single point.

## The race-free, independent fragment (`Fragment`)

A program whose offered firings are ground, each offered under one label, and pairwise statically
independent when distinct. No two of its firings take a common occurrence (independent firings do
not clash), so it has no races. On configurations with reflexive knowledge it is determinate
(`Fragment.determinate`): two firings with one label commute, so firing either leaves the other
admitted, and every later firing is admitted after both (`enabled_of_fire`,
`MeTTaCalculus.OccurrenceCommits.enabled_fire_iff`, `MeTTaCalculus.OccurrenceCommits.fire_comm`).
Hence **in the fragment, bisimilarity is trace equivalence** (`Fragment.bisimilar_iff_traceEquivalent`).

## The race pair leaves the fragment (`Pair.not_determinate`, `Pair.not_fragment`)

`Q` has two firings under rule `A`, both admitted, both taking `a`: they race, they are not
independent, and their results are not bisimilar.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing StaticIndependent)
open MeTTaCalculus.OccurrenceCommits (Enabled fire Commit TraceIndependent)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

section Milner

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}

variable (A label offers) in
/-- **Determinacy** on a set of configurations: successors under one label are bisimilar. -/
def Determinate (good : Configuration T O → Prop) : Prop :=
  ∀ C, good C → ∀ ℓ C₁ C₂, Moves A label offers C ℓ C₁ → Moves A label offers C ℓ C₂ →
    Bisimilar A label offers C₁ C₂

/-- **Milner's determinacy theorem in the step**: on a determinate set closed under moves, trace
equivalence is a bisimulation. -/
theorem bisimilar_of_traceEquivalent {good : Configuration T O → Prop}
    (closed : ∀ C ℓ D, good C → Moves A label offers C ℓ D → good D)
    (determinate : Determinate A label offers good) {C D : Configuration T O} (goodC : good C)
    (goodD : good D) (traces : TraceEquivalent A label offers C D) : Bisimilar A label offers C D := by
  have step : ∀ X Y, good X → good Y → TraceEquivalent A label offers X Y →
      ∀ ℓ X', Moves A label offers X ℓ X' → ∃ Y', Moves A label offers Y ℓ Y' ∧
        good X' ∧ good Y' ∧ TraceEquivalent A label offers X' Y' := by
    intro X Y goodX goodY traces ℓ X' moved
    obtain ⟨Y', moved', _⟩ := hasTrace_cons.mp ((traces [ℓ]).mp
      (hasTrace_cons.mpr ⟨X', moved, hasTrace_nil _⟩))
    refine ⟨Y', moved', closed X ℓ X' goodX moved, closed Y ℓ Y' goodY moved', fun w => ⟨?_, ?_⟩⟩
    · intro traced
      obtain ⟨Y'', moved'', traced''⟩ := hasTrace_cons.mp ((traces (ℓ :: w)).mp
        (hasTrace_cons.mpr ⟨X', moved, traced⟩))
      exact (traceEquivalent_of_bisimilar (determinate Y goodY ℓ Y'' Y' moved'' moved') w).mp traced''
    · intro traced
      obtain ⟨X'', moved'', traced''⟩ := hasTrace_cons.mp ((traces (ℓ :: w)).mpr
        (hasTrace_cons.mpr ⟨Y', moved', traced⟩))
      exact (traceEquivalent_of_bisimilar (determinate X goodX ℓ X'' X' moved'' moved) w).mp traced''
  refine ⟨fun X Y => good X ∧ good Y ∧ TraceEquivalent A label offers X Y, ⟨?_, ?_, ?_⟩,
    goodC, goodD, traces⟩
  · rintro X Y ⟨goodX, goodY, traces⟩ ℓ X' moved
    obtain ⟨Y', moved', goodX', goodY', traces'⟩ := step X Y goodX goodY traces ℓ X' moved
    exact ⟨Y', moved', goodX', goodY', traces'⟩
  · rintro X Y ⟨goodX, goodY, traces⟩ ℓ Y' moved
    obtain ⟨X', moved', goodY', goodX', traces'⟩ :=
      step Y X goodY goodX (fun w => (traces w).symm) ℓ Y' moved
    exact ⟨X', moved', goodX', goodY', fun w => (traces' w).symm⟩
  · intro _ _ _ atom
    exact atom.elim

/-- **On a determinate set, bisimilarity is trace equivalence.** -/
theorem bisimilar_iff_traceEquivalent {good : Configuration T O → Prop}
    (closed : ∀ C ℓ D, good C → Moves A label offers C ℓ D → good D)
    (determinate : Determinate A label offers good) {C D : Configuration T O} (goodC : good C)
    (goodD : good D) : Bisimilar A label offers C D ↔ TraceEquivalent A label offers C D :=
  ⟨traceEquivalent_of_bisimilar, bisimilar_of_traceEquivalent closed determinate goodC goodD⟩

end Milner

/-! ## The race-free, independent fragment -/

section Fragment

/-- A commit stays enabled backwards: if `d` is enabled after `c`, and `c` makes nothing `d` uses
and `d` makes nothing `c` uses, then `d` was enabled before `c`. -/
theorem enabled_of_fire {label : O → T} {s : Finset O} {c d : Commit O T}
    (after : Enabled label (fire s c) d) (independent : TraceIndependent label c d)
    (noQueries : d.queries = []) : Enabled label s d := by
  have old : ∀ o ∈ d.taken ∪ d.kept, o ∈ s := by
    intro o used
    rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp
      ((Finset.mem_union.mp used).elim (fun t => after.taken_subset t) (fun k => after.kept_subset k))
      with ⟨inStore, _⟩ | made
    · exact inStore
    · exact absurd used (Finset.disjoint_left.mp independent.2.1 made)
  refine ⟨fun o taken => old o (Finset.mem_union_left _ taken),
    fun o kept => old o (Finset.mem_union_right _ kept), after.apart, ?_, ?_⟩
  · refine Finset.disjoint_left.mpr fun o made inStore => ?_
    have notAfter : o ∉ fire s c := fun inFire => Finset.disjoint_left.mp after.fresh made inFire
    have taken : o ∈ c.taken := by
      by_contra notTaken
      exact notAfter (MeTTaCalculus.OccurrenceCommits.mem_fire.mpr (.inl ⟨inStore, notTaken⟩))
    exact Finset.disjoint_left.mp independent.2.2 made (Finset.mem_union_left _ taken)
  · intro query member
    rw [noQueries] at member
    simp at member

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)

/-- **The race-free, independent fragment**: offered firings are ground, each under one label, and
distinct offered firings are statically independent. -/
structure Fragment : Prop where
  ground : ∀ ℓ f, offers ℓ f → Ground label f
  oneLabel : ∀ ℓ ℓ' f, offers ℓ f → offers ℓ' f → ℓ = ℓ'
  independent : ∀ ℓ ℓ' f g, offers ℓ f → offers ℓ' g → f ≠ g → StaticIndependent label f g

variable {A label offers}

theorem footprint_eq {f : Firing T S O} (noQueries : f.queries = []) (σ : S) :
    f.footprintAt σ = f.selection.commit (T := T) := by
  unfold Firing.footprintAt PredicateQueryAdmission.commit
  rw [noQueries]
  rfl

theorem Fragment.trace (fragment : Fragment label offers) (σ : S) {ℓ ℓ' : L} {f g : Firing T S O}
    (offeredF : offers ℓ f) (offeredG : offers ℓ' g) (apart : f ≠ g) :
    TraceIndependent label (f.selection.commit (T := T)) (g.selection.commit (T := T)) := by
  have := (fragment.independent ℓ ℓ' f g offeredF offeredG apart).2.2 σ
  rwa [footprint_eq (fragment.ground _ _ offeredF).queries,
    footprint_eq (fragment.ground _ _ offeredG).queries] at this

theorem Fragment.moves_iff (fragment : Fragment label offers) {C : Configuration T O}
    (refl : Reflexive C.equations) {ℓ : L} {D : Configuration T O} :
    Moves A label offers C ℓ D ↔
      ∃ f, offers ℓ f ∧ Enabled label C.present (f.selection.commit (T := T)) ∧ D = f.result label C := by
  constructor
  · rintro ⟨f, offered, valid, rfl⟩
    exact ⟨f, offered, ((fragment.ground _ _ offered).valid_iff A refl).mp valid, rfl⟩
  · rintro ⟨f, offered, enabled, rfl⟩
    exact ⟨f, offered, ((fragment.ground _ _ offered).valid_iff A refl).mpr enabled, rfl⟩

/-- The relation of the determinacy proof: same occurrences, or the two results of two
same-labelled firings enabled at one store. -/
def Twin (offers : L → Firing T S O → Prop) (X Y : Configuration T O) : Prop :=
  Reflexive X.equations ∧ Reflexive Y.equations ∧
    (X.present = Y.present ∨ ∃ (Z : Finset O) (ℓ : L) (f₁ f₂ : Firing T S O), offers ℓ f₁ ∧ offers ℓ f₂ ∧
      f₁ ≠ f₂ ∧ Enabled label Z (f₁.selection.commit (T := T)) ∧
      Enabled label Z (f₂.selection.commit (T := T)) ∧
      X.present = fire Z (f₁.selection.commit (T := T)) ∧ Y.present = fire Z (f₂.selection.commit (T := T)))

theorem twin_symm {X Y : Configuration T O} (twin : Twin (label := label) offers X Y) :
    Twin (label := label) offers Y X := by
  obtain ⟨reflX, reflY, same | ⟨Z, ℓ, f₁, f₂, o₁, o₂, apart, e₁, e₂, p₁, p₂⟩⟩ := twin
  · exact ⟨reflY, reflX, .inl same.symm⟩
  · exact ⟨reflY, reflX, .inr ⟨Z, ℓ, f₂, f₁, o₂, o₁, Ne.symm apart, e₂, e₁, p₂, p₁⟩⟩

theorem twin_forward (fragment : Fragment label offers) {X Y : Configuration T O}
    (twin : Twin (label := label) offers X Y) {ℓ' : L} {X' : Configuration T O}
    (moved : Moves A label offers X ℓ' X') :
    ∃ Y', Moves A label offers Y ℓ' Y' ∧ Twin (label := label) offers X' Y' := by
  obtain ⟨reflX, reflY, same | ⟨Z, ℓ, f₁, f₂, o₁, o₂, apart, e₁, e₂, p₁, p₂⟩⟩ := twin
  · obtain ⟨g, offered, enabled, rfl⟩ := (fragment.moves_iff reflX).mp moved
    refine ⟨g.result label Y, (fragment.moves_iff reflY).mpr ⟨g, offered, same ▸ enabled, rfl⟩,
      (fragment.ground _ _ offered).reflexive_result reflX,
      (fragment.ground _ _ offered).reflexive_result reflY, .inl ?_⟩
    show fire X.present _ = fire Y.present _
    rw [same]
  · obtain ⟨g, offered, enabled, rfl⟩ := (fragment.moves_iff reflX).mp moved
    have reflX' := (fragment.ground _ _ offered).reflexive_result (C := X) reflX
    by_cases isF₂ : g = f₂
    · subst isF₂
      obtain rfl := fragment.oneLabel ℓ ℓ' g o₂ offered
      have f₁After : Enabled label (fire Z (g.selection.commit (T := T))) (f₁.selection.commit (T := T)) :=
        (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff e₁ e₂).mpr
          ⟨fun clash => (fragment.trace A.identity o₁ o₂ apart).1.1 clash,
            (fragment.trace A.identity o₁ o₂ apart).1.2.2⟩
      refine ⟨f₁.result label Y, (fragment.moves_iff reflY).mpr ⟨f₁, o₁, p₂ ▸ f₁After, rfl⟩, reflX',
        (fragment.ground _ _ o₁).reflexive_result reflY, .inl ?_⟩
      show fire X.present _ = fire Y.present _
      rw [p₁, p₂]
      exact MeTTaCalculus.OccurrenceCommits.fire_comm e₁ e₂
    · have gAtZ : Enabled label Z (g.selection.commit (T := T)) := by
        by_cases isF₁ : g = f₁
        · subst isF₁
          exact e₁
        · exact enabled_of_fire (p₁ ▸ enabled) (fragment.trace A.identity o₁ offered (Ne.symm isF₁)) rfl
      have gAfterF₂ : Enabled label (fire Z (f₂.selection.commit (T := T))) (g.selection.commit (T := T)) :=
        (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff gAtZ e₂).mpr
          ⟨fun clash => (fragment.trace A.identity offered o₂ isF₂).1.1 clash,
            (fragment.trace A.identity offered o₂ isF₂).1.2.2⟩
      have f₁AfterG : Enabled label (fire Z (g.selection.commit (T := T))) (f₁.selection.commit (T := T)) := by
        by_cases isF₁ : g = f₁
        · subst isF₁
          exact p₁ ▸ enabled
        · exact (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff e₁ gAtZ).mpr
            ⟨fun clash => (fragment.trace A.identity o₁ offered (Ne.symm isF₁)).1.1 clash,
              (fragment.trace A.identity o₁ offered (Ne.symm isF₁)).1.2.2⟩
      have f₂AfterG : Enabled label (fire Z (g.selection.commit (T := T))) (f₂.selection.commit (T := T)) :=
        (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff e₂ gAtZ).mpr
          ⟨fun clash => (fragment.trace A.identity o₂ offered (Ne.symm isF₂)).1.1 clash,
            (fragment.trace A.identity o₂ offered (Ne.symm isF₂)).1.2.2⟩
      refine ⟨g.result label Y, (fragment.moves_iff reflY).mpr ⟨g, offered, p₂ ▸ gAfterF₂, rfl⟩, reflX',
        (fragment.ground _ _ offered).reflexive_result reflY,
        .inr ⟨fire Z (g.selection.commit (T := T)), ℓ, f₁, f₂, o₁, o₂, apart, f₁AfterG, f₂AfterG, ?_, ?_⟩⟩
      · show fire X.present _ = _
        rw [p₁]
        exact MeTTaCalculus.OccurrenceCommits.fire_comm e₁ gAtZ
      · show fire Y.present _ = _
        rw [p₂]
        exact MeTTaCalculus.OccurrenceCommits.fire_comm e₂ gAtZ

/-- **The fragment is determinate** on configurations with reflexive knowledge. -/
theorem Fragment.determinate (fragment : Fragment label offers) :
    Determinate A label offers (fun C => Reflexive C.equations) := by
  intro C refl ℓ C₁ C₂ moved₁ moved₂
  obtain ⟨f₁, o₁, e₁, rfl⟩ := (fragment.moves_iff refl).mp moved₁
  obtain ⟨f₂, o₂, e₂, rfl⟩ := (fragment.moves_iff refl).mp moved₂
  refine ⟨Twin (label := label) offers, ⟨fun X Y twin ℓ' X' moved => twin_forward fragment twin moved,
    fun X Y twin ℓ' Y' moved => ?_, fun _ _ _ atom => atom.elim⟩, ?_⟩
  · obtain ⟨X', moved', twin'⟩ := twin_forward fragment (twin_symm twin) moved
    exact ⟨X', moved', twin_symm twin'⟩
  · refine ⟨(fragment.ground _ _ o₁).reflexive_result refl,
      (fragment.ground _ _ o₂).reflexive_result refl, ?_⟩
    by_cases same : f₁ = f₂
    · subst same
      exact .inl rfl
    · exact .inr ⟨C.present, ℓ, f₁, f₂, o₁, o₂, same, e₁, e₂, rfl, rfl⟩

/-- **In the race-free, independent fragment, bisimilarity is trace equivalence.** -/
theorem Fragment.bisimilar_iff_traceEquivalent (fragment : Fragment label offers)
    {C D : Configuration T O} (reflC : Reflexive C.equations) (reflD : Reflexive D.equations) :
    Bisimilar A label offers C D ↔ TraceEquivalent A label offers C D :=
  Race.bisimilar_iff_traceEquivalent
    (fun C ℓ D refl moved => by
      obtain ⟨f, offered, _, rfl⟩ := (fragment.moves_iff refl).mp moved
      exact (fragment.ground _ _ offered).reflexive_result refl)
    fragment.determinate reflC reflD

end Fragment

/-! ## The race pair leaves the fragment -/

namespace Pair

variable (t : Tags T) (A : SubstitutionAction T S)

/-- **The race pair is not determinate**: the two `A`-successors of `Q` are not bisimilar. -/
theorem not_determinate (apart : t.b ≠ t.c) :
    ¬ Determinate A (label t) (offers t) (fun C => Reflexive C.equations) := by
  intro determinate
  have bisimilar := determinate Q reflexive_nil (ruleA t) (Kb t) (Kc t)
    ((moves_Q t A).mpr (.inl ⟨rfl, rfl⟩)) ((moves_Q t A).mpr (.inr ⟨rfl, rfl⟩))
  have traced := (traceEquivalent_of_bisimilar bisimilar [ruleB t]).mp
    ((hasTrace_Kb t A).mpr (.inr rfl))
  rcases (hasTrace_Kc t A).mp traced with empty | same
  · cases empty
  · exact ruleB_ne_ruleC t apart (List.cons.inj same).1

include A in
/-- **The race pair leaves the fragment**: the two `A`-firings of `Q` are distinct and not
independent. -/
theorem not_fragment : ¬ Fragment (S := S) (label t) (offers t) := by
  intro fragment
  have distinct : aQb (S := S) t ≠ aQc t := by
    intro same
    have := congrArg (fun f : AnnotatedRuns.Firing T S Site => f.selection.made) same
    simp [aQb, aQc] at this
  have independent := fragment.independent _ _ _ _ ⟨mem_aQb t, rfl⟩ ⟨mem_aQc t, rfl⟩ distinct
  have trace := independent.2.2 A.identity
  exact trace.1.1 (.inl (of_decide_eq_false rfl))

end Pair

#print axioms bisimilar_of_traceEquivalent
#print axioms bisimilar_iff_traceEquivalent
#print axioms enabled_of_fire
#print axioms Fragment.determinate
#print axioms Fragment.bisimilar_iff_traceEquivalent
#print axioms Pair.not_determinate
#print axioms Pair.not_fragment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
