import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.RuleLocality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition

/-!
# The positive single-firing profile for dynamically held rules

Check the specification selected for activation, not everything reachable
from its source or every code it installs. Equation checks and explicit
selections are allowed; complete row observations and unmatched-rule
queries are not. This restricts the existing step, preserving its effects.

For an allowed firing, admission at a fixed frame and knowledge depends
only on the present identities it selects or makes and on the held
identities it uses, removes or makes. The opening must still be fresh in
the full state. The small view is used for checking admission, not for
computing the result in place of the full store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z}

/-- A check with no region is precisely an equation check. -/
private theorem checkRegion_eq_none_iff {T : Type uT} (c : Check T) :
    checkRegion c = none ↔ ∃ l r, c = .equal l r := by
  cases c <;> simp [checkRegion]

/-- A store-independent check on the chosen specification. Terms, code
arguments and code values not being activated are not traversed. -/
def Spec.positiveCheck (sp : Spec Tm C Z) : Bool :=
  sp.body.checks.all (fun c => (checkRegion c).isNone) &&
    sp.collect.isEmpty && sp.unmatched.isEmpty

theorem Spec.positiveCheck_iff (sp : Spec Tm C Z) :
    sp.positiveCheck = true ↔ Scope.Positive sp.toRule ∧ sp.unmatched = [] := by
  simp only [positiveCheck, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none,
    checkRegion_eq_none_iff, List.isEmpty_iff, Scope.Positive, toRule]

variable (X : Frames Tm Hom) [DecidableEq O] [DecidableEq R]

/-- The ordinary single-firing step, restricted by a check at each
activation, including activation of received or newly installed code. -/
abbrev positiveStep (codes : Codes Tm C Z) (ambient : Set C) :=
  Spaces.restrict (rstep X O R E codes ambient).toStep
    (fun {_} f => f.spec.positiveCheck = true)

theorem positiveStep_admits_iff (ambient : Set C) {s : RState Tm O R C Z}
    (f : RFiring O R E codes s) :
    (positiveStep (O := O) (R := R) (E := E) X codes ambient).Admits f ↔
      f.Admits X ambient ∧ Scope.Positive f.spec.toRule ∧ f.spec.unmatched = [] := by
  change (f.Admits X ambient ∧ f.spec.positiveCheck = true) ↔ _
  rw [Spec.positiveCheck_iff]

theorem positiveStep_run_checks (ambient : Set C) {s : RState Tm O R C Z}
    (run : (positiveStep (O := O) (R := R) (E := E) X codes ambient).Run s) :
    ∀ event ∈ run.word, Scope.Positive event.2.spec.toRule ∧ event.2.spec.unmatched = [] := by
  intro event member
  exact (Spec.positiveCheck_iff _).mp (Spaces.run_allowed _ _ run event member)

section Footprint

variable {s : RState Tm O R C Z} (f : RFiring O R E codes s)

/-- The row identities used by admission apart from opening freshness:
taken and read identities, and the proposed new identities. -/
def RFiring.rowSupport : Finset O :=
  f.selection.taken.toFinset ∪ f.selection.read.toFinset ∪ f.selection.made.toFinset

/-- The registry part of the support. An ambient use contributes no
held identity; its availability remains checked against the ambient set. -/
def RFiring.ruleSupport : Finset R :=
  (match f.use with | .ambient _ => ∅ | .held ρ => {ρ}) ∪
    f.removedRules.toFinset ∪ f.madeRules.toFinset

/-- A view of the selected support, with the full frame, labels and
knowledge kept. In particular an already occupied output is not hidden. -/
abbrev RFiring.onSupport :=
  (f.atPresent (s.present ∩ f.rowSupport)).atRules (s.rules ∩ f.ruleSupport)

omit [DecidableEq O] [DecidableEq R] in
private theorem queryPatterns_nil (positive : Scope.Positive f.spec.toRule) :
    f.base.queryPatterns X = [] := by
  have checks : ((f.base.opened X).checks.filterMap checkRegion) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro check member
    obtain ⟨old, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨l, r, rfl⟩ := positive.1 old inside
    rfl
  have allRows : f.base.collectOpened X = [] := by
    change f.spec.collect.map _ = []
    have empty : f.spec.collect = [] := positive.2
    rw [empty]
    rfl
  simp [Firing.queryPatterns, checks, allRows]

omit [DecidableEq O] [DecidableEq R] in
private theorem atPresent_fresh_of_subset {W : Finset O} (inside : W ⊆ s.present)
    (fresh : f.Fresh X) : (f.atPresent W).Fresh X := by
  intro b g h
  obtain ⟨a, state, opened⟩ := fresh b g h
  refine ⟨a, ?_, opened⟩
  intro t member
  apply state t
  rcases member with (left | right | ⟨o, present, same⟩) | rules
  · exact Or.inl (Or.inl left)
  · exact Or.inl (Or.inr (Or.inl right))
  · exact Or.inl (Or.inr (Or.inr ⟨o, inside present, same⟩))
  · exact Or.inr rules

omit [DecidableEq O] [DecidableEq R] in
private theorem atRules_fresh_of_subset {W : Finset R} (inside : W ⊆ s.rules)
    (fresh : f.Fresh X) : (f.atRules W).Fresh X := by
  intro b g h
  obtain ⟨a, state, opened⟩ := fresh b g h
  refine ⟨a, ?_, opened⟩
  intro t member
  apply state t
  rcases member with rows | ⟨ρ, held, argument⟩
  · exact Or.inl rows
  · exact Or.inr ⟨ρ, inside held, argument⟩

omit [DecidableEq O] in
private theorem available_on_ruleSupport_iff (ambient : Set C) :
    (s.withRules (s.rules ∩ f.ruleSupport)).Available ambient f.use ↔
      s.Available ambient f.use := by
  cases h : f.use with
  | ambient c => simp only [RState.Available]
  | held ρ => simp [RState.Available, RState.withRules, RFiring.ruleSupport, h]

/-- The chosen rows, held rule and outputs are enough to validate an
already prepared positive firing. This is an equivalence of admission;
it does not erase the frame from the actual state update. -/
theorem RFiring.admits_onSupport_iff {ambient : Set C}
    (positive : f.spec.positiveCheck = true) (fresh : f.Fresh X) :
    f.onSupport.Admits X ambient ↔ f.Admits X ambient := by
  have ⟨basePositive, noRuleQueries⟩ := (Spec.positiveCheck_iff _).mp positive
  let W := s.present ∩ f.rowSupport
  let Q := s.rules ∩ f.ruleSupport
  have sameRows : ∀ o, (o ∈ f.selection.taken ∨ o ∈ f.selection.read ∨ o ∈ f.selection.made) →
      (o ∈ s.present ↔ o ∈ W) := by
    intro o touched
    have supported : o ∈ f.rowSupport := by
      simp only [RFiring.rowSupport, Finset.mem_union, List.mem_toFinset]
      tauto
    exact ⟨fun before => Finset.mem_inter.mpr ⟨before, supported⟩, fun after =>
      (Finset.mem_inter.mp after).1⟩
  have withoutRowQueries := queryPatterns_nil X f basePositive
  have rowFresh : (f.atPresent W).Fresh X :=
    atPresent_fresh_of_subset X f Finset.inter_subset_left fresh
  have bothFresh : f.onSupport.Fresh X :=
    atRules_fresh_of_subset X (f.atPresent W) Finset.inter_subset_left rowFresh
  constructor
  · intro admitted
    have rowsBack : (f.atPresent W).Admits X ambient := by
      apply f.onSupport.admits_of_outsideRules X admitted
      · refine ⟨?_, ?_, ?_, ?_⟩
        · exact (available_on_ruleSupport_iff f ambient).mp admitted.1.2.2.available
        · intro ρ made held
          change ρ ∈ f.madeRules at made
          have supported : ρ ∈ f.ruleSupport := by
            simp only [RFiring.ruleSupport, Finset.mem_union, List.mem_toFinset]
            exact Or.inr made
          exact admitted.1.2.2.madeNew ρ made (Finset.mem_inter.mpr ⟨held, supported⟩)
        · intro p removed
          exact (Finset.mem_inter.mp (admitted.1.2.2.removedHeld p removed).1).1
        · intro q member
          exact absurd member (noRuleQueries ▸ List.not_mem_nil)
      · exact rowFresh
    apply (f.atPresent W).admits_of_outsideRegions X rowsBack
    · refine ⟨fun o selected => (sameRows o selected).symm, ?_⟩
      intro b σ solved p member
      exact absurd member (withoutRowQueries ▸ List.not_mem_nil)
    · exact fresh
  · intro admitted
    have rowsForward : (f.atPresent W).Admits X ambient := by
      apply f.admits_of_outsideRegions X admitted
      · refine ⟨sameRows, ?_⟩
        intro b σ solved p member
        exact absurd member (withoutRowQueries ▸ List.not_mem_nil)
      · exact rowFresh
    apply (f.atPresent W).admits_of_outsideRules X rowsForward
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact (available_on_ruleSupport_iff f ambient).mpr admitted.1.2.2.available
      · intro ρ made held
        exact admitted.1.2.2.madeNew ρ made (Finset.mem_inter.mp held).1
      · intro p removed
        have supported : p.2 ∈ f.ruleSupport := by
          have picked : p.2 ∈ f.removedRules := (List.of_mem_zip removed).2
          simp only [RFiring.ruleSupport, Finset.mem_union, List.mem_toFinset]
          exact Or.inl (Or.inr picked)
        exact Finset.mem_inter.mpr ⟨(admitted.1.2.2.removedHeld p removed).1, supported⟩
      · intro q member
        exact absurd member (noRuleQueries ▸ List.not_mem_nil)
    · exact bothFresh

/-- The executable profile uses the same check on the full view or the
small view. A caller may reuse this equivalence after establishing fresh
opening; publication still acts on the full state. -/
theorem positiveStep_admits_onSupport_iff {ambient : Set C} (fresh : f.Fresh X) :
    (positiveStep X codes ambient).Admits f.onSupport ↔
      (positiveStep X codes ambient).Admits f := by
  change (f.onSupport.Admits X ambient ∧ f.spec.positiveCheck = true) ↔
    (f.Admits X ambient ∧ f.spec.positiveCheck = true)
  exact ⟨fun ⟨admitted, positive⟩ => ⟨(f.admits_onSupport_iff X positive fresh).mp admitted, positive⟩,
    fun ⟨admitted, positive⟩ => ⟨(f.admits_onSupport_iff X positive fresh).mpr admitted, positive⟩⟩

/-- Changing the presence of other rows or rules cannot affect positive
admission at fixed knowledge and labels, if the opening remains fresh.
This permits deletions as well as insertions outside the support. -/
theorem positiveStep_admits_iff_of_sameSupport {ambient : Set C} {W : Finset O} {Q : Finset R}
    (rows : W ∩ f.rowSupport = s.present ∩ f.rowSupport)
    (rules : Q ∩ f.ruleSupport = s.rules ∩ f.ruleSupport)
    (fresh : f.Fresh X) (fresh' : ((f.atPresent W).atRules Q).Fresh X) :
    (positiveStep X codes ambient).Admits ((f.atPresent W).atRules Q) ↔
      (positiveStep X codes ambient).Admits f := by
  rw [← positiveStep_admits_onSupport_iff X _ fresh', ← positiveStep_admits_onSupport_iff X _ fresh]
  change (positiveStep X codes ambient).Admits
      ((f.atPresent (W ∩ f.rowSupport)).atRules (Q ∩ f.ruleSupport)) ↔
    (positiveStep X codes ambient).Admits
      ((f.atPresent (s.present ∩ f.rowSupport)).atRules (s.rules ∩ f.ruleSupport))
  rw [rows, rules]

end Footprint

#print axioms Spec.positiveCheck_iff
#print axioms positiveStep_admits_iff
#print axioms positiveStep_run_checks
#print axioms RFiring.admits_onSupport_iff
#print axioms positiveStep_admits_onSupport_iff
#print axioms positiveStep_admits_iff_of_sameSupport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
