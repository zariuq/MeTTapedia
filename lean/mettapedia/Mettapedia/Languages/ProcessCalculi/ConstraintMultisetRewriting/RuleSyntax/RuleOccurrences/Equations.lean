import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Protection

/-!
# An equation as one rule occurrence: a small model over first-order atoms

A model of the three rules of a hosted program that concern its equations, over first-order atoms at
one frame, with two zones (`true`: the zone of equations). A call is the row `7`; its value is the
row `8`.

* **The equation** (`Code.equation`): take the call `7`, make the value `8`. It is held as one rule
  occurrence in the zone of equations, and the state holds no row for it.
* **The rule for an unmatched call** (`Code.unmatched`): read a call `x`, ask the **rule query** "no
  held rule of the zone of equations could take `x`", and make the row `99`.
* **Adding an equation** (`Code.add`): take a request `60` and **make a rule occurrence** of the
  equation in the zone of equations.

What is proved.

* `unmatched_admitted`: with no equation held, the rule for an unmatched call fires on the call.
* `add_admitted`, `extended_holds`: the request is answered by a firing whose result holds the
  equation as a new rule occurrence.
* `unmatched_refused`: after it, the rule for an unmatched call is refused on the same call: the
  rule query sees the occurrence. The query is the one check here that an added rule can turn off.
* `equation_admitted`, `equation_result_label`: the added equation fires on the call and makes `8`.
* **Two copies** (`copy_admitted`, `copies_differ`, `copies_same_result`): with the equation held
  persistently by two identities, the call has two admitted firings, one per occurrence, with one
  result. **Linear copies** (`linear_copies_results_differ`): when the two occurrences are linear,
  the two results differ in which occurrence is left.
* **Sealing** (`add_not_respects`, `add_refused_sealed`, `equation_admitted_sealed`): with the zone
  of equations guarded, the sealed step refuses the firing that adds the equation and admits the
  firing of the equation; the unrestricted step admits both (`add_admitted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Equations

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Examples (Tm X E x c shift)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## The code system -/

/-- The codes of the model. -/
inductive Code where
  | equation
  | unmatched
  | add
  deriving DecidableEq

/-- The equation: take the call `7`, make the value `8`. -/
def equationRule : Rule Tm := ⟨PUnit.unit, ⟨[c 7], [], [], [], [c 8]⟩, []⟩

/-- The rule for an unmatched call: read a call `x`, ask that no held rule of the zone of equations
could take it, make `99`. -/
def unmatchedSpec : Spec Tm Code Bool :=
  ⟨PUnit.unit, ⟨[], [x], [], [], [c 99]⟩, [], [], [(true, x)], [], [], [], []⟩

/-- Adding an equation: take the request `60`, make an occurrence of the equation, with the given
mode, in the zone of equations. -/
def addSpec : Spec Tm Code Bool :=
  ⟨PUnit.unit, ⟨[c 60], [], [], [], []⟩, [], [], [], [⟨Code.equation, [], .persistent, true⟩], [],
    [], []⟩

/-- The code system; no term denotes a code. -/
def codes : Codes Tm Code Bool where
  unfold
    | .equation => Spec.ofRule equationRule
    | .unmatched => unmatchedSpec
    | .add => addSpec
  denotes _ _ _ := False
  close _ _ _ := none

/-! ## Before the equation is added -/

/-- The call `7` at row `0`, the request `60` at row `1`; held, outside the zone of equations: the
rule for an unmatched call at identity `0` and the rule that adds the equation at identity `1`. -/
def bare : RState Tm ℕ ℕ Code Bool :=
  ⟨⟨PUnit.unit, [], {0, 1}, fun o => c (if o = 0 then 7 else 60)⟩, {0, 1},
    fun ρ => ⟨if ρ = 0 then Code.unmatched else Code.add, [], .persistent, false⟩⟩

/-- The rule for an unmatched call reads the call and makes row `9`. -/
def unmatchedFiring : RFiring ℕ ℕ E codes bare :=
  ⟨.held 0, PUnit.unit, shift, ⟨[], [0], [9]⟩, [], [], [], [], []⟩

theorem unmatched_information : unmatchedFiring.information X = [(.var 1, c 7)] := rfl

theorem unmatched_fresh : unmatchedFiring.Fresh X := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t ((member | member | ⟨o, -, rfl⟩) | ⟨ρ, -, member⟩)
    · simp [bare] at member
    · simp [bare] at member
    · rfl
    · exact absurd member List.not_mem_nil
  · intro t member
    have inside : t ∈ unmatchedSpec.terms := member
    simp [unmatchedSpec, Spec.terms, Rule.terms] at inside
    rcases inside with rfl | rfl | rfl <;> rfl

/-- **With no equation held, the call is unmatched.** -/
theorem unmatched_admitted : unmatchedFiring.Admits X (∅ : Set Code) := by
  refine ⟨⟨unmatched_fresh, ⟨List.nodup_nil, List.nodup_singleton 9, rfl, rfl, rfl, rfl⟩,
    ⟨Finset.mem_insert_self 0 {1}, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩⟩, ?_, ?_, ?_⟩
  · apply enabled_of <;> simp [unmatchedFiring, bare]
  · rw [unmatched_information]
    exact ⟨PUnit.unit, fun _ => c 7, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · intro b σ _
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro q member ρ _ zone
      have inside : q ∈ [((true, x) : Bool × Tm PUnit.unit)] := member
      obtain rfl := List.mem_singleton.mp inside
      exact absurd zone Bool.false_ne_true
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil

/-! ## Adding the equation at run time -/

theorem bare_closed : bare.Closed := fun _ _ => rfl

/-- The request is taken and an occurrence of the equation is made at identity `2`. -/
def addFiring : RFiring ℕ ℕ E codes bare :=
  ⟨.held 1, PUnit.unit, Subst.id atoms, ⟨[1], [], []⟩, [], [2], [], [], []⟩

theorem add_plain : addFiring.spec.Plain :=
  ⟨rfl, rfl, rfl, fun h inside => by
    have member : h ∈ [(⟨Code.equation, [], .persistent, true⟩ : Held Tm Code Bool PUnit.unit)] := inside
    obtain rfl := List.mem_singleton.mp member
    rfl, rfl, rfl⟩

theorem add_base_admitted : addFiring.base.Admits X bare.toState := by
  refine ⟨⟨?_, List.nodup_singleton 1, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action bare.toState addFiring.base
    intro t member σ
    have inside : t ∈ addSpec.toRule.terms := member
    simp [addSpec, Rule.terms] at inside
    subst inside
    rfl
  · apply enabled_of <;> simp [addFiring, bare]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have inside : e ∈ [(c 60, c 60)] := member
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

theorem add_ruleShapes : addFiring.RuleShapes (∅ : Set Code) := by
  refine ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self 1), rfl, rfl, List.nodup_singleton 2,
    rfl, ?_, rfl, List.nodup_nil, fun _ inside => absurd inside List.not_mem_nil, rfl⟩
  intro ρ inside held
  obtain rfl := List.mem_singleton.mp inside
  have member : (2 : ℕ) ∈ ({0, 1} : Finset ℕ) := held
  exact absurd member (by decide)

/-- **The equation is added by a firing**: the unrestricted step admits it. -/
theorem add_admitted : addFiring.Admits X (∅ : Set Code) :=
  (addFiring.admits_plain X bare_closed add_plain ∅).mpr ⟨add_base_admitted, add_ruleShapes⟩

/-- The state after the equation was added. -/
def extended : RState Tm ℕ ℕ Code Bool := addFiring.result X

/-- **The result holds the equation as a rule occurrence**, in the zone of equations. -/
theorem extended_holds : extended.held 2 = ⟨Code.equation, [], .persistent, true⟩ := rfl

theorem extended_mem_rules : 2 ∈ extended.rules :=
  (RFiring.mem_result_rules _).mpr (Or.inr (List.mem_singleton_self 2))

/-- The equation is no row: the one row left is the call. -/
theorem extended_present : extended.present = {0} := by
  show fire ({0, 1} : Finset ℕ) ((⟨[1], [], []⟩ : Selection ℕ).commit (T := Unit)) = {0}
  decide

theorem extended_closed : extended.Closed := by
  intro ρ inside
  rcases (RFiring.mem_result_rules _).mp inside with kept | made
  · have other : ρ ∉ addFiring.madeRules := fun made =>
      add_ruleShapes.madeNew ρ made (RFiring.kept_subset _ kept)
    show ((addFiring.result X).held ρ).args = []
    rw [RFiring.result_held_other _ other]
    rfl
  · obtain rfl := List.mem_singleton.mp made
    rfl

/-! ## After the equation is added -/

/-- The rule for an unmatched call, tried on the same call after the equation was added. -/
def unmatchedAfter : RFiring ℕ ℕ E codes extended :=
  ⟨.held 0, PUnit.unit, shift, ⟨[], [0], [9]⟩, [], [], [], [], []⟩

theorem unmatchedAfter_information :
    unmatchedAfter.information X = [(c 60, c 60), (.var 1, c 7)] := rfl

/-- **The added equation turns the unmatched call off**: the rule query sees the new occurrence. -/
theorem unmatched_refused : ¬ unmatchedAfter.Admits X (∅ : Set Code) := by
  intro admitted
  have asks := admitted.2.2.2
  rw [unmatchedAfter_information] at asks
  have holds := asks PUnit.unit (fun _ => c 7) (fun e member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)
  have query := holds.2.1 (true, x) (List.mem_singleton_self _)
  exact query 2 extended_mem_rules rfl (c 7) (List.mem_singleton_self _) (Subst.id atoms)
    (fun _ inside => absurd inside List.not_mem_nil) rfl

/-- The added equation takes the call and makes row `8`. -/
def equationFiring : RFiring ℕ ℕ E codes extended :=
  ⟨.held 2, PUnit.unit, Subst.id atoms, ⟨[0], [], [8]⟩, [], [], [], [], []⟩

theorem equation_plain : equationFiring.spec.Plain := Spec.plain_ofRule equationRule

theorem equation_base_admitted : equationFiring.base.Admits X extended.toState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 8, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action extended.toState equationFiring.base
    intro t member σ
    have inside : t ∈ equationRule.terms := member
    simp [equationRule, Rule.terms] at inside
    rcases inside with rfl | rfl <;> rfl
  · have present : extended.toState.present = {0} := extended_present
    apply enabled_of
    · intro o inside
      rw [present]
      obtain rfl := List.mem_singleton.mp inside
      exact Finset.mem_singleton_self 0
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o _ inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      rw [present]
      obtain rfl := List.mem_singleton.mp inside
      decide
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have inside : e ∈ [(c 60, c 60), (c 7, c 7)] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

theorem equation_ruleShapes : equationFiring.RuleShapes (∅ : Set Code) :=
  ⟨extended_mem_rules, rfl, rfl, List.nodup_nil, rfl, fun _ inside => absurd inside List.not_mem_nil,
    rfl, List.nodup_nil, fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- **The added equation fires on the call.** -/
theorem equation_admitted : equationFiring.Admits X (∅ : Set Code) :=
  (equationFiring.admits_plain X extended_closed equation_plain ∅).mpr
    ⟨equation_base_admitted, equation_ruleShapes⟩

/-- **It makes the value.** -/
theorem equation_result_label : (equationFiring.result X).label 8 = c 8 := rfl

/-! ## Two copies of an equation -/

/-- The call at row `0`, and the equation held by the identities `2` and `3`, in the given mode. -/
def doubled (mode : Mode) : RState Tm ℕ ℕ Code Bool :=
  ⟨⟨PUnit.unit, [], {0}, fun _ => c 7⟩, {2, 3}, fun _ => ⟨Code.equation, [], mode, true⟩⟩

/-- The occurrence `ρ` of the equation takes the call and makes row `8`. -/
def copyFiring (mode : Mode) (ρ : ℕ) : RFiring ℕ ℕ E codes (doubled mode) :=
  ⟨.held ρ, PUnit.unit, Subst.id atoms, ⟨[0], [], [8]⟩, [], [], [], [], []⟩

theorem copy_base_admitted (mode : Mode) (ρ : ℕ) :
    (copyFiring mode ρ).base.Admits X (doubled mode).toState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 8, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action (doubled mode).toState (copyFiring mode ρ).base
    intro t member σ
    have inside : t ∈ equationRule.terms := member
    simp [equationRule, Rule.terms] at inside
    rcases inside with rfl | rfl <;> rfl
  · apply enabled_of <;> simp [copyFiring, doubled]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have inside : e ∈ [(c 7, c 7)] := member
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

/-- **Each held copy fires on the call.** -/
theorem copy_admitted (mode : Mode) {ρ : ℕ} (held : ρ ∈ ({2, 3} : Finset ℕ)) :
    (copyFiring mode ρ).Admits X (∅ : Set Code) :=
  ((copyFiring mode ρ).admits_plain X (fun _ _ => rfl) (Spec.plain_ofRule equationRule) ∅).mpr
    ⟨copy_base_admitted mode ρ, held, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- **Two copies are two firings.** -/
theorem copies_differ (mode : Mode) : copyFiring mode 2 ≠ copyFiring mode 3 := by
  intro same
  have uses : Use.held 2 = (Use.held 3 : Use Code ℕ) := congrArg RFiring.use same
  exact absurd (Use.held.inj uses) (by decide)

/-- **Persistent copies give one result**: the two firings reach the same state. -/
theorem copies_same_result :
    (copyFiring .persistent 2).result X = (copyFiring .persistent 3).result X := rfl

/-- **Linear copies give two results**: each firing takes the occurrence it uses, so the occurrence
`3` is left by the first firing and not by the second. -/
theorem linear_copies_results_differ :
    3 ∈ ((copyFiring .linear 2).result X).rules ∧ 3 ∉ ((copyFiring .linear 3).result X).rules := by
  constructor
  · refine (RFiring.mem_result_rules _).mpr (Or.inl ((RFiring.mem_kept _).mpr ⟨by decide, ?_⟩))
    intro takes
    rcases takes with used | removed
    · exact absurd (Use.held.inj used.1) (by decide)
    · exact absurd removed List.not_mem_nil
  · intro inside
    rcases (RFiring.mem_result_rules _).mp inside with kept | made
    · exact ((RFiring.mem_kept _).mp kept).2 (Or.inl ⟨rfl, rfl⟩)
    · exact absurd made List.not_mem_nil

/-! ## Sealing the zone of equations -/

/-- The zone of equations is guarded. -/
def guarded : Bool → Prop := fun z => z = true

/-- **Adding an equation does not respect the protection.** -/
theorem add_not_respects : ¬ addFiring.Respects guarded :=
  fun respects => respects.1 _ (List.mem_singleton_self _) rfl

/-- **The sealed step refuses the firing that adds the equation**, which the unrestricted step
admits (`add_admitted`). -/
theorem add_refused_sealed :
    ¬ (sealedStep X ℕ ℕ E codes (∅ : Set Code) guarded).Admits addFiring :=
  fun admitted => add_not_respects admitted.2

/-- **The sealed step admits the firing of the equation**: using a persistent rule of a guarded zone
respects the protection. -/
theorem equation_admitted_sealed :
    (sealedStep X ℕ ℕ E codes (∅ : Set Code) guarded).Admits equationFiring := by
  refine ⟨equation_admitted, ?_, ?_, ?_, ?_⟩
  · intro h inside
    exact absurd inside List.not_mem_nil
  · intro i inside
    exact absurd inside List.not_mem_nil
  · intro ρ takes
    rcases takes with usedUp | removed
    · have used : ρ = 2 := (Use.held.inj usedUp.1).symm
      subst used
      exact absurd usedUp.2 (by decide)
    · exact absurd removed List.not_mem_nil
  · intro p inside
    exact absurd inside List.not_mem_nil

#print axioms unmatched_admitted
#print axioms add_admitted
#print axioms extended_holds
#print axioms extended_present
#print axioms unmatched_refused
#print axioms equation_admitted
#print axioms equation_result_label
#print axioms copy_admitted
#print axioms copies_differ
#print axioms copies_same_result
#print axioms linear_copies_results_differ
#print axioms add_not_respects
#print axioms add_refused_sealed
#print axioms equation_admitted_sealed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Equations
