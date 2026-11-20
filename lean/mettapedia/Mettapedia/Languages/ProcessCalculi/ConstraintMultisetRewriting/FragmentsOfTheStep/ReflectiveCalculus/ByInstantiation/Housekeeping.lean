import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Effects

/-!
# Housekeeping: heating and clearing keep the represented process and decrease the weight

* `heat_effect`, `clearBag_effect`, `clearZero_effect`: every admitted housekeeping firing keeps the
  represented process and strictly decreases the spine weight.
* `canonical_admits`: a rule of the program opened canonically, with a selection of the right
  shape, is admitted as soon as a grounding solves its information; `copair_solves` builds that
  grounding from a solution of the knowledge and an assignment of the rule's unknowns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

theorem similar_bag_bag {Γ : Ctx sig} {l l' : G Γ .ps} (similar : Similar (bagT l) (bagT l')) :
    Similar l l' := by
  cases similar with
  | bag inner => exact inner

theorem similar_pcons_pcons {Γ : Ctx sig} {p p' : G Γ .pr} {l l' : G Γ .ps}
    (similar : Similar (pconsT p l) (pconsT p' l')) : Similar p p' ∧ Similar l l' := by
  cases similar with
  | pcons head tail => exact ⟨head, tail⟩

theorem spine_bag_cons (a : G [] .pr) (r : G [] .ps) :
    spine (bagT (pconsT a r)) = spine a + spine r + 1 + 1 := rfl

theorem spine_bag (r : G [] .ps) : spine (bagT r) = spine r + 1 := rfl

/-- Closedness of the parts of a closed bag. -/
theorem closed_parts {a : G [] .pr} {r : G [] .ps} (closed : Closed (bagT (pconsT a r))) :
    Closed a ∧ Closed (bagT r) := by
  obtain ⟨elements, same⟩ := read_ps_ground r
  have unfolded : binderSafeAt "NQuote" 0 (consBag (read a) (read r)) = true := closed
  rw [same] at unfolded
  have parts : binderSafeAt "NQuote" 0 (read a) = true ∧
      binderSafeListAt "NQuote" 0 elements = true := by
    simpa [consBag, bagElements, binderSafeAt, binderSafeListAt] using unfolded
  refine ⟨parts.1, ?_⟩
  show binderSafeAt "NQuote" 0 (read r) = true
  rw [same]
  simpa [binderSafeAt] using parts.2

theorem primes_bag_parts (a : G [] .pr) (r : G [] .ps) :
    primes (read (bagT (pconsT a r))) = primes (read a) + primes (read (bagT r)) := by
  obtain ⟨elements, same⟩ := read_ps_ground r
  show primes (consBag (read a) (read r)) = primes (read a) + primes (read r)
  rw [same]
  exact primes_cons_bag (read a) elements

/-! ## Heating -/

/-- **What a heating firing does**: the represented process is kept and the weight decreases. -/
theorem heat_effect {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) (f : Firing s) (isHeat : f.rule = heatRule)
    (admitted : f.Admits knowledge s) :
    ∃ value' : ℕ → G [] .pr, RepresentsBy (f.result knowledge s) P value' ∧
      weightOf (f.result knowledge s).present value' < weightOf s.present value := by
  classical
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = heatRule at isHeat
  subst isHeat
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLen, readLen, produceLen, collectLen⟩, enabled, solvable,
    asks⟩ := admitted
  change 1 = taken.length at takeLen
  change 0 = readSel.length at readLen
  change 2 = made.length at produceLen
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero readLen.symm
  obtain ⟨o₄, o₅, rfl⟩ := List.length_eq_two.mp produceLen.symm
  let fir : Firing s := ⟨heatRule, member, ext, opening, ⟨[o], [], [o₄, o₅]⟩, seen⟩
  have shapes : fir.Shapes knowledge s :=
    ⟨fresh, takenNodup, madeNodup, takeLen, readLen, produceLen, collectLen⟩
  have distinct : o₄ ≠ o₅ := by simpa using madeNodup
  have present : o ∈ s.present := enabled.taken_subset (by simp [Selection.commit])
  have freshMade : Disjoint ({o₄, o₅} : Finset ℕ) s.present := by
    have apart := enabled.fresh
    simpa [Selection.commit] using apart
  have fresh₄ : o₄ ∉ s.present := fun inside => Finset.disjoint_left.mp freshMade (by simp) inside
  have fresh₅ : o₅ ∉ s.present := fun inside => Finset.disjoint_left.mp freshMade (by simp) inside
  have takes : ∀ g' : Grounding (target fir), GroundSolves g' (fir.information knowledge s) →
      Similar (bagT (pconsT ((Assignment.compose g' opening) .first)
        ((Assignment.compose g' opening) .rest))) (value o) := by
    intro g' solved
    obtain ⟨u, at', similar⟩ := represented.determined _ (ground_knowledge fir solved) o present
    have first := ground_take fir solved (p := obs heatBag) (o := o) (by
      simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])
    rw [at'] at first
    change ObsSimilar ⟨[], .pr, instantiate (Assignment.compose g' opening) heatBag⟩ _ at first
    rw [instantiate_heatBag] at first
    exact obs_closed_similar first similar
  obtain ⟨g₀, solved₀⟩ := (solvable_iff _).mp solvable
  obtain ⟨l, shapeBag, inner₀⟩ := similar_bag_inv (Γ := ([] : Ctx sig)) (takes g₀ solved₀)
  obtain ⟨a, r, shapeCons, _, _⟩ := similar_pcons_inv (Γ := ([] : Ctx sig)) inner₀
  have shape : value o = bagT (pconsT a r) := by rw [shapeBag, shapeCons]
  have closedParts := closed_parts (shape ▸ represented.closed o present)
  let value' : ℕ → G [] .pr := fun x => if x = o₄ then a else if x = o₅ then bagT r else value x
  have keep : ∀ x ∈ s.present, value' x = value x := by
    intro x member
    have not₄ : x ≠ o₄ := fun same => fresh₄ (same ▸ member)
    have not₅ : x ≠ o₅ := fun same => fresh₅ (same ▸ member)
    simp only [value', not₄, not₅, if_false]
  have at₄ : value' o₄ = a := by simp [value']
  have at₅ : value' o₅ = bagT r := by simp [value', distinct.symm]
  have resultPresent : (fir.result knowledge s).present = (s.present \ {o}) ∪ {o₄, o₅} := by
    rw [result_present_eq]
    simp [fir]
  have parts : ∀ g' : Grounding (target fir), GroundSolves g' (fir.information knowledge s) →
      Similar ((Assignment.compose g' opening) .first) a ∧
        Similar ((Assignment.compose g' opening) .rest) r := by
    intro g' solved
    have similar := takes g' solved
    rw [shape] at similar
    exact similar_pcons_pcons (similar_bag_bag similar)
  have apart : Disjoint (s.present \ {o}) {o₄, o₅} := by
    rw [Finset.disjoint_left]
    intro x inside made
    simp only [Finset.mem_insert, Finset.mem_singleton] at made
    rcases made with rfl | rfl
    · exact fresh₄ (Finset.mem_sdiff.mp inside).1
    · exact fresh₅ (Finset.mem_sdiff.mp inside).1
  have restPrimes : ∑ x ∈ s.present \ {o}, primes (read (value' x)) =
      ∑ x ∈ s.present \ {o}, primes (read (value x)) :=
    Finset.sum_congr rfl fun x member => by rw [keep x (Finset.mem_sdiff.mp member).1]
  have restSpine : ∑ x ∈ s.present \ {o}, spine (value' x) =
      ∑ x ∈ s.present \ {o}, spine (value x) :=
    Finset.sum_congr rfl fun x member => by rw [keep x (Finset.mem_sdiff.mp member).1]
  refine ⟨value', ⟨⟨g₀, solved₀⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro g' solved x member
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with kept | new
    · have keptOld := Finset.mem_sdiff.mp kept
      have not₄ : x ≠ o₄ := fun same => fresh₄ (same ▸ keptOld.1)
      have not₅ : x ≠ o₅ := fun same => fresh₅ (same ▸ keptOld.1)
      obtain ⟨u, at', similar⟩ := represented.determined _ (ground_knowledge fir solved) x keptOld.1
      refine ⟨u, (ground_kept fir g' (by simp [fir, not₄, not₅])).trans at', ?_⟩
      rw [keep x keptOld.1]
      exact similar
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      obtain ⟨firstSimilar, restSimilar⟩ := parts g' solved
      rcases new with rfl | rfl
      · refine ⟨(Assignment.compose g' opening) .first,
          (ground_made fir g' shapes (p := obs (generator heatArity .first)) (by
            simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])).trans ?_, ?_⟩
        · exact congrArg (fun t : G [] .pr => (⟨[], .pr, t⟩ : Observation sig noUnknowns))
            (instantiate_generator (Assignment.compose g' opening) HeatUnknown.first)
        · rw [at₄]
          exact firstSimilar
      · refine ⟨bagT ((Assignment.compose g' opening) .rest),
          (ground_made fir g' shapes (p := obs (bagT (generator heatArity .rest))) (by
            simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])).trans ?_, ?_⟩
        · exact congrArg (fun t : G [] .ps => (⟨[], .pr, bagT t⟩ : Observation sig noUnknowns))
            (instantiate_generator (Assignment.compose g' opening) HeatUnknown.rest)
        · rw [at₅]
          exact .bag restSimilar
  · intro x member
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with kept | new
    · rw [keep x (Finset.mem_sdiff.mp kept).1]
      exact represented.closed x (Finset.mem_sdiff.mp kept).1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [at₄]
        exact closedParts.1
      · rw [at₅]
        exact closedParts.2
  · rw [← represented.inventory_eq]
    unfold inventoryOf
    rw [resultPresent, Finset.sum_union apart, Finset.sum_pair distinct, at₄, at₅, restPrimes,
      ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present), Finset.sum_singleton, shape,
      primes_bag_parts]
  · unfold weightOf
    rw [resultPresent, Finset.sum_union apart, Finset.sum_pair distinct, at₄, at₅, restSpine,
      ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (f := fun x => spine (value x)),
      Finset.sum_singleton, shape, spine_bag_cons, spine_bag]
    omega

/-! ## Clearing -/

/-- **What a clearing firing of the empty bag does.** -/
theorem clearBag_effect {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) (f : Firing s) (isClear : f.rule = clearBagRule)
    (admitted : f.Admits knowledge s) :
    RepresentsBy (f.result knowledge s) P value ∧
      weightOf (f.result knowledge s).present value < weightOf s.present value := by
  classical
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = clearBagRule at isClear
  subst isClear
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLen, readLen, produceLen, collectLen⟩, enabled, solvable,
    asks⟩ := admitted
  change 1 = taken.length at takeLen
  change 0 = readSel.length at readLen
  change 0 = made.length at produceLen
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero readLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero produceLen.symm
  let fir : Firing s := ⟨clearBagRule, member, ext, opening, ⟨[o], [], []⟩, seen⟩
  have present : o ∈ s.present := enabled.taken_subset (by simp [Selection.commit])
  obtain ⟨g₀, solved₀⟩ := (solvable_iff _).mp solvable
  have shape : value o = bagT pnilT := by
    obtain ⟨u, at', similar⟩ := represented.determined _ (ground_knowledge fir solved₀) o present
    have first := ground_take fir solved₀ (p := obs (bagT pnilT)) (o := o) (by
      simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])
    rw [at'] at first
    have taken : Similar (bagT pnilT) (value o) := obs_closed_similar first similar
    obtain ⟨l, same, inner⟩ := similar_bag_inv taken
    rw [same, similar_pnil_inv inner]
  have resultPresent : (fir.result knowledge s).present = s.present \ {o} := by
    rw [result_present_eq]
    simp [fir]
  refine ⟨⟨⟨g₀, solved₀⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro g' solved x member
    rw [resultPresent] at member
    obtain ⟨u, at', similar⟩ :=
      represented.determined _ (ground_knowledge fir solved) x (Finset.mem_sdiff.mp member).1
    exact ⟨u, (ground_kept fir g' (by simp [fir])).trans at', similar⟩
  · intro x member
    rw [resultPresent] at member
    exact represented.closed x (Finset.mem_sdiff.mp member).1
  · rw [← represented.inventory_eq]
    unfold inventoryOf
    rw [resultPresent, ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present)
      (s₂ := s.present), Finset.sum_singleton, shape]
    show _ = _ + primes (.collection .hashBag [] none)
    rw [primes_empty_bag, add_zero]
  · unfold weightOf
    rw [resultPresent, ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present)
      (s₂ := s.present) (f := fun x => spine (value x)), Finset.sum_singleton, shape]
    show _ < _ + 1
    omega

/-- **What a clearing firing of the null process does.** -/
theorem clearZero_effect {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) (f : Firing s) (isClear : f.rule = clearZeroRule)
    (admitted : f.Admits knowledge s) :
    RepresentsBy (f.result knowledge s) P value ∧
      weightOf (f.result knowledge s).present value < weightOf s.present value := by
  classical
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = clearZeroRule at isClear
  subst isClear
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLen, readLen, produceLen, collectLen⟩, enabled, solvable,
    asks⟩ := admitted
  change 1 = taken.length at takeLen
  change 0 = readSel.length at readLen
  change 0 = made.length at produceLen
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero readLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero produceLen.symm
  let fir : Firing s := ⟨clearZeroRule, member, ext, opening, ⟨[o], [], []⟩, seen⟩
  have present : o ∈ s.present := enabled.taken_subset (by simp [Selection.commit])
  obtain ⟨g₀, solved₀⟩ := (solvable_iff _).mp solvable
  have shape : value o = zeroT := by
    obtain ⟨u, at', similar⟩ := represented.determined _ (ground_knowledge fir solved₀) o present
    have first := ground_take fir solved₀ (p := obs zeroT) (o := o) (by
      simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])
    rw [at'] at first
    exact similar_zero_inv (obs_closed_similar first similar)
  have resultPresent : (fir.result knowledge s).present = s.present \ {o} := by
    rw [result_present_eq]
    simp [fir]
  refine ⟨⟨⟨g₀, solved₀⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro g' solved x member
    rw [resultPresent] at member
    obtain ⟨u, at', similar⟩ :=
      represented.determined _ (ground_knowledge fir solved) x (Finset.mem_sdiff.mp member).1
    exact ⟨u, (ground_kept fir g' (by simp [fir])).trans at', similar⟩
  · intro x member
    rw [resultPresent] at member
    exact represented.closed x (Finset.mem_sdiff.mp member).1
  · rw [← represented.inventory_eq]
    unfold inventoryOf
    rw [resultPresent, ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present)
      (s₂ := s.present), Finset.sum_singleton, shape]
    show _ = _ + primes zeroPattern
    rw [primes_zero, add_zero]
  · unfold weightOf
    rw [resultPresent, ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present)
      (s₂ := s.present) (f := fun x => spine (value x)), Finset.sum_singleton, shape]
    show _ < _ + 1
    omega

#print axioms heat_effect
#print axioms clearBag_effect
#print axioms clearZero_effect

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
