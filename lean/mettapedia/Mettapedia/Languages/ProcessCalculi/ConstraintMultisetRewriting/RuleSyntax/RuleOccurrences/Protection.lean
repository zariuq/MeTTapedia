import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces

/-!
# Adding never removes, and a protected zone is a restriction of the step

**Adding never removes.** The held rules a firing takes are the occurrence it uses, when that
occurrence is linear (`RFiring.UsesUp`), and the occurrences its spec removes (`RFiring.Takes`,
`mem_kept`). Every other held rule is held by the result, with the same code, mode and zone, its
arguments carried along the extension (`held_stays`); and a made or installed rule occurrence has a
new identity, so it overwrites nothing (the shape `RuleShapes.madeNew`). In particular a rule added
beside a rule already held leaves that rule held: making and installing take nothing.

**Where a made rule goes.** A made, installed or published occurrence lies in the zone its spec
names (`zone_of_made`).

**A protected zone.** For a predicate `guarded` on zones, a firing **respects** it (`Respects`) when
its spec makes, installs and publishes no rule in a guarded zone and no occurrence it takes (uses up
or removes) is in one. The **sealed step** (`sealedStep`) is the restriction of the candidate (`Spaces.restrict`) to
the firings that respect the protection. Along every one of its firings, and so along every one of
its runs, the rule occurrences of the guarded zones are exactly those of the start
(`guarded_rules_iff`, `sealed_run`). The ambient program is fixed by every firing by construction; a
guarded zone is a part of the state with the same property, by a stated restriction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- Each element of a list is paired, in the zip with a list of the same length. -/
theorem exists_zip_of_mem {α β : Type*} : ∀ (as : List α) (bs : List β), as.length = bs.length →
    ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | [], _, _, _, inside => absurd inside List.not_mem_nil
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | first :: as, other :: bs, lengths, a, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨other, List.mem_cons_self⟩
      · obtain ⟨b, zipped⟩ := exists_zip_of_mem as bs (Nat.succ.inj lengths) a later
        exact ⟨b, List.mem_cons_of_mem _ zipped⟩

namespace RFiring

variable {X : Frames Tm Hom} {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {s : RState Tm O R C Z}
  (f : RFiring O R E codes s)

/-- **The occurrence a firing uses up**: the one it uses, when that occurrence is linear. -/
def UsesUp (ρ : R) : Prop := f.use = Use.held ρ ∧ (s.held ρ).mode = Mode.linear

/-- **The occurrences a firing takes**: the one it uses up, and the ones it removes. -/
def Takes (ρ : R) : Prop := f.UsesUp ρ ∨ ρ ∈ f.removedRules

/-- What the use leaves: every held rule it does not use up. -/
theorem mem_left [DecidableEq R] {ρ : R} : ρ ∈ f.left ↔ ρ ∈ s.rules ∧ ¬ f.UsesUp ρ := by
  obtain ⟨use, ext, opening, selection, seen, made, installed, removed, published⟩ := f
  cases use with
  | ambient c =>
      show ρ ∈ s.rules ↔ ρ ∈ s.rules ∧ ¬ (Use.ambient c = Use.held ρ ∧ (s.held ρ).mode = Mode.linear)
      constructor
      · intro held
        exact ⟨held, fun takes => nomatch takes.1⟩
      · exact fun both => both.1
  | held used =>
      show ρ ∈ (if (s.held used).mode = Mode.linear then s.rules.erase used else s.rules) ↔
        ρ ∈ s.rules ∧ ¬ (Use.held used = Use.held ρ ∧ (s.held ρ).mode = Mode.linear)
      by_cases linear : (s.held used).mode = Mode.linear
      · rw [if_pos linear, Finset.mem_erase]
        constructor
        · rintro ⟨other, held⟩
          exact ⟨held, fun takes => other (Use.held.inj takes.1).symm⟩
        · rintro ⟨held, stays⟩
          refine ⟨fun same => stays ?_, held⟩
          subst same
          exact ⟨rfl, linear⟩
      · rw [if_neg linear]
        constructor
        · intro held
          refine ⟨held, fun takes => linear ?_⟩
          have same : used = ρ := Use.held.inj takes.1
          rw [same]
          exact takes.2
        · exact fun both => both.1

/-- **What is kept**: every held rule the firing does not take. -/
theorem mem_kept [DecidableEq R] {ρ : R} : ρ ∈ f.kept ↔ ρ ∈ s.rules ∧ ¬ f.Takes ρ := by
  unfold kept Takes
  rw [Finset.mem_sdiff, List.mem_toFinset, f.mem_left]
  constructor
  · rintro ⟨⟨held, notUsed⟩, notRemoved⟩
    exact ⟨held, fun takes => takes.elim notUsed notRemoved⟩
  · rintro ⟨held, stays⟩
    exact ⟨⟨held, fun used => stays (Or.inl used)⟩, fun removed => stays (Or.inr removed)⟩

variable [DecidableEq O] [DecidableEq R] {ambient : Set C}

/-- **Adding never removes**: a held rule the firing does not take is held by the result, with its
label carried along the extension. -/
theorem held_stays (admitted : f.Admits X ambient) {ρ : R} (held : ρ ∈ s.rules)
    (stays : ¬ f.Takes ρ) :
    ρ ∈ (f.result X).rules ∧ (f.result X).held ρ = (s.held ρ).act X (E.weaken f.ext) :=
  ⟨(f.mem_result_rules (X := X)).mpr (Or.inl (f.mem_kept.mpr ⟨held, stays⟩)),
    f.result_held_other (fun made => admitted.1.2.2.madeNew ρ made held)⟩

/-- **A made, installed or published occurrence lies in the zone its spec names.** -/
theorem zone_of_made (shapes : f.RuleShapes ambient) {ρ : R} (made : ρ ∈ f.madeRules) :
    (∃ h ∈ f.spec.makes, ((f.result X).held ρ).zone = h.zone) ∨
      (∃ i ∈ f.spec.installs, ((f.result X).held ρ).zone = i.zone) ∨
      ∃ p ∈ f.spec.publishes, ((f.result X).held ρ).zone = p.2.2 := by
  obtain ⟨label, zipped⟩ := exists_zip_of_mem f.madeRules (f.madeLabels X)
    (f.length_madeLabels shapes).symm ρ made
  have holds : (f.result X).held ρ = label := f.result_held_made shapes zipped
  have inside : label ∈ f.madeLabels X := (List.of_mem_zip zipped).2
  rw [holds]
  unfold madeLabels at inside
  rcases List.mem_append.mp inside with fromFirst | fromPublished
  · rcases List.mem_append.mp fromFirst with fromMakes | fromInstalls
    · obtain ⟨h, member, rfl⟩ := List.mem_map.mp fromMakes
      exact Or.inl ⟨h, member, rfl⟩
    · obtain ⟨x, member, rfl⟩ := List.mem_map.mp fromInstalls
      exact Or.inr (Or.inl ⟨x.1, (List.of_mem_zip member).1, rfl⟩)
  · obtain ⟨x, member, rfl⟩ := List.mem_map.mp fromPublished
    exact Or.inr (Or.inr ⟨x.1, (List.of_mem_zip member).1, rfl⟩)

/-- **A firing respects a protection**: its spec makes, installs and publishes no rule in a guarded
zone, and no occurrence it takes, by using it up or by removing it, is in one. -/
def Respects (guarded : Z → Prop) : Prop :=
  (∀ h ∈ f.spec.makes, ¬ guarded h.zone) ∧ (∀ i ∈ f.spec.installs, ¬ guarded i.zone) ∧
    (∀ ρ, f.Takes ρ → ¬ guarded (s.held ρ).zone) ∧ ∀ p ∈ f.spec.publishes, ¬ guarded p.2.2

/-- **A firing that respects the protection leaves the guarded zones as they are**: the rule
occurrences of the guarded zones after it are exactly those before it. -/
theorem guarded_rules_iff (guarded : Z → Prop) (admitted : f.Admits X ambient)
    (respects : f.Respects guarded) (ρ : R) :
    (ρ ∈ (f.result X).rules ∧ guarded ((f.result X).held ρ).zone) ↔
      (ρ ∈ s.rules ∧ guarded (s.held ρ).zone) := by
  constructor
  · rintro ⟨inside, zone⟩
    rcases (f.mem_result_rules (X := X)).mp inside with kept | made
    · obtain ⟨held, -⟩ := f.mem_kept.mp kept
      have other : ρ ∉ f.madeRules := fun made => admitted.1.2.2.madeNew ρ made held
      rw [f.result_held_other other] at zone
      exact ⟨held, zone⟩
    · rcases f.zone_of_made admitted.1.2.2 made with
        ⟨h, member, same⟩ | ⟨i, member, same⟩ | ⟨p, member, same⟩
      · rw [same] at zone
        exact absurd zone (respects.1 h member)
      · rw [same] at zone
        exact absurd zone (respects.2.1 i member)
      · rw [same] at zone
        exact absurd zone (respects.2.2.2 p member)
  · rintro ⟨held, zone⟩
    have stays : ¬ f.Takes ρ := fun takes => respects.2.2.1 ρ takes zone
    obtain ⟨inside, label⟩ := f.held_stays admitted held stays
    refine ⟨inside, ?_⟩
    rw [label]
    exact zone

end RFiring

/-! ## The sealed step -/

section Sealed

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (R : Type uR) [DecidableEq R]
  (E : Extensions.{uO, uH, uE} Hom) {C : Type uC} {Z : Type uZ} (codes : Codes Tm C Z)
  (ambient : Set C) (guarded : Z → Prop)

/-- **The sealed step**: the candidate restricted to the firings that respect the protection. -/
def sealedStep : Interface.Step X O (RState Tm O R C Z) (fun s => RFiring O R E codes s) :=
  Spaces.restrict (rstep X O R E codes ambient).toStep (fun {_} f => f.Respects guarded)

variable {X O R E codes ambient guarded}

theorem sealed_admits_iff {s : RState Tm O R C Z} (f : RFiring O R E codes s) :
    (sealedStep X O R E codes ambient guarded).Admits f ↔ f.Admits X ambient ∧ f.Respects guarded :=
  Iff.rfl

/-- **No run of the sealed step changes a guarded zone**: at the end of every run, the rule
occurrences of the guarded zones are exactly those of the start. -/
theorem sealed_run : ∀ {s : RState Tm O R C Z}
    (r : (sealedStep X O R E codes ambient guarded).Run s) (ρ : R),
    (ρ ∈ r.last.rules ∧ guarded (r.last.held ρ).zone) ↔ (ρ ∈ s.rules ∧ guarded (s.held ρ).zone)
  | _, .nil _, _ => Iff.rfl
  | _, .cons f admitted rest, ρ =>
      (sealed_run rest ρ).trans (f.guarded_rules_iff guarded admitted.1 admitted.2 ρ)

end Sealed

#print axioms exists_zip_of_mem
#print axioms RFiring.mem_left
#print axioms RFiring.mem_kept
#print axioms RFiring.held_stays
#print axioms RFiring.zone_of_made
#print axioms RFiring.guarded_rules_iff
#print axioms sealed_admits_iff
#print axioms sealed_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
