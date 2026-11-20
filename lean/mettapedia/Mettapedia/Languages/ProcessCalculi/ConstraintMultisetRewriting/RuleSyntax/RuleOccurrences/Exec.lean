import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Protection

/-!
# Rules that are taken when they fire, make rules, and are scheduled by a key

**With no ambient program, a state that holds no rule is stuck** (`stuck_of_no_rules`), for every
frame action and code system.

Then, over first-order atoms at one frame, three linear codes (`Exec.codes`):

* `once`: take the fact `12`, make the fact `22` (remove one fact, add one);
* `loop`: take a token `1`, make a token `2`, and **make an occurrence of `loop` itself**: a code
  that makes its own code, which a code system allows because it is a coalgebra;
* `stage`: take nothing, and make an occurrence of `once`.

What is proved.

* **Taken when it fires** (`once_admitted`, `once_result_label`, `once_taken`, `once_then_stuck`):
  the linear occurrence of `once` fires, makes `22`, and is taken; the result holds no rule, so no
  firing is admitted there.
* **A loop is a rule that makes itself again** (`loop_admitted`, `loop_result_rules`, `loop_reemits`,
  `loop_again_admitted`): the firing takes the occurrence it uses and makes a new occurrence of the
  same code, which fires on the next token.
* **The next rule by a key is a restriction of the step** (`keyed`, `stage_first`): with the key of
  each code as its place in the order, the candidate restricted to the firings whose occurrence has
  the least key among the held ones (`Spaces.restrict`) admits the firing of `stage` and refuses the
  firing of `once` at a state where the unrestricted step admits both.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

section Stuck

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)
  {O : Type uOcc} [DecidableEq O] {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {s : RState Tm O R C Z}

/-- **With no ambient program, a state that holds no rule admits no firing.** -/
theorem stuck_of_no_rules (none : s.rules = ∅) (f : RFiring O R E codes s) :
    ¬ f.Admits X (∅ : Set C) := by
  intro admitted
  have available := admitted.1.2.2.available
  obtain ⟨use, ext, opening, selection, seen, made, installed⟩ := f
  cases use with
  | ambient c => exact Set.notMem_empty c available
  | held ρ =>
      have held : ρ ∈ s.rules := available
      rw [none] at held
      exact Finset.notMem_empty ρ held

end Stuck

namespace Exec

open Mettapedia.Logic.LP
open Examples (Tm X E x c shift)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## The code system -/

/-- The codes of the model. -/
inductive Code where
  | once
  | loop
  | stage
  deriving DecidableEq

/-- Take the fact `12`, make the fact `22`. -/
def onceRule : Rule Tm := ⟨PUnit.unit, ⟨[c 12], [], [], [], [c 22]⟩, []⟩

/-- Take a token `1`, make a token `2`, and make an occurrence of `loop` again. -/
def loopSpec : Spec Tm Code Unit :=
  ⟨PUnit.unit, ⟨[c 1], [], [], [], [c 2]⟩, [], [], [], [⟨Code.loop, [], .linear, ()⟩], [], [], []⟩

/-- Take nothing, make an occurrence of `once`. -/
def stageSpec : Spec Tm Code Unit :=
  ⟨PUnit.unit, ⟨[], [], [], [], []⟩, [], [], [], [⟨Code.once, [], .linear, ()⟩], [], [], []⟩

/-- The code system; no term denotes a code. -/
def codes : Codes Tm Code Unit where
  unfold
    | .once => Spec.ofRule onceRule
    | .loop => loopSpec
    | .stage => stageSpec
  denotes _ _ _ := False
  close _ _ _ := none

theorem made_closed {mode : Mode} {code : Code} (h : Held Tm Code Unit PUnit.unit)
    (inside : h ∈ [(⟨code, [], mode, ()⟩ : Held Tm Code Unit PUnit.unit)]) : h.args = [] := by
  obtain rfl := List.mem_singleton.mp inside
  rfl

/-! ## Taken when it fires -/

/-- The fact `12` at row `0`, and `once` held linearly at identity `0`. -/
def factState : RState Tm ℕ ℕ Code Unit :=
  ⟨⟨PUnit.unit, [], {0}, fun _ => c 12⟩, {0}, fun _ => ⟨Code.once, [], .linear, ()⟩⟩

/-- `once` takes the fact and makes row `1`. -/
def onceFiring : RFiring ℕ ℕ E codes factState :=
  ⟨.held 0, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, [], [], [], [], []⟩

theorem once_base_admitted : onceFiring.base.Admits X factState.toState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action factState.toState onceFiring.base
    intro t member σ
    have inside : t ∈ onceRule.terms := member
    simp [onceRule, Rule.terms] at inside
    rcases inside with rfl | rfl <;> rfl
  · apply enabled_of <;> simp [onceFiring, factState]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have inside : e ∈ [(c 12, c 12)] := member
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

/-- **The linear occurrence fires.** -/
theorem once_admitted : onceFiring.Admits X (∅ : Set Code) :=
  (onceFiring.admits_plain X (fun _ _ => rfl) (Spec.plain_ofRule onceRule) ∅).mpr
    ⟨once_base_admitted, Finset.mem_singleton_self 0, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩

theorem once_result_label : (onceFiring.result X).label 1 = c 22 := rfl

/-- **It is taken**: the result holds no rule. -/
theorem once_taken : (onceFiring.result X).rules = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro ρ inside
  rcases (RFiring.mem_result_rules _).mp inside with kept | made
  · obtain ⟨held, stays⟩ := (RFiring.mem_kept _).mp kept
    have same : ρ = 0 := Finset.mem_singleton.mp held
    subst same
    exact stays (Or.inl ⟨rfl, rfl⟩)
  · exact absurd made List.not_mem_nil

/-- **Nothing fires after it.** -/
theorem once_then_stuck (f : RFiring ℕ ℕ E codes (onceFiring.result X)) :
    ¬ f.Admits X (∅ : Set Code) :=
  stuck_of_no_rules X once_taken f

/-! ## A loop is a rule that makes itself again -/

/-- Two tokens `1`, at rows `0` and `1`, and `loop` held linearly at identity `0`. -/
def loopState : RState Tm ℕ ℕ Code Unit :=
  ⟨⟨PUnit.unit, [], {0, 1}, fun _ => c 1⟩, {0}, fun _ => ⟨Code.loop, [], .linear, ()⟩⟩

/-- `loop` takes the token at row `0`, makes row `2`, and makes an occurrence of `loop` at identity
`5`. -/
def loopFiring : RFiring ℕ ℕ E codes loopState :=
  ⟨.held 0, PUnit.unit, Subst.id atoms, ⟨[0], [], [2]⟩, [], [5], [], [], []⟩

theorem loop_plain : loopSpec.Plain :=
  ⟨rfl, rfl, rfl, fun h inside => made_closed h inside, rfl, rfl⟩

theorem loop_base_admitted : loopFiring.base.Admits X loopState.toState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 2, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action loopState.toState loopFiring.base
    intro t member σ
    have inside : t ∈ loopSpec.toRule.terms := member
    simp [loopSpec, Rule.terms] at inside
    rcases inside with rfl | rfl <;> rfl
  · apply enabled_of <;> simp [loopFiring, loopState]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have inside : e ∈ [(c 1, c 1)] := member
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

theorem loop_ruleShapes : loopFiring.RuleShapes (∅ : Set Code) := by
  refine ⟨Finset.mem_singleton_self 0, rfl, rfl, List.nodup_singleton 5, rfl, ?_, rfl,
    List.nodup_nil, fun _ inside => absurd inside List.not_mem_nil, rfl⟩
  intro ρ inside held
  obtain rfl := List.mem_singleton.mp inside
  exact absurd (Finset.mem_singleton.mp held) (by decide)

theorem loop_admitted : loopFiring.Admits X (∅ : Set Code) :=
  (loopFiring.admits_plain X (fun _ _ => rfl) loop_plain ∅).mpr ⟨loop_base_admitted, loop_ruleShapes⟩

/-- **The used occurrence is gone and a new one is held.** -/
theorem loop_result_rules (ρ : ℕ) : ρ ∈ (loopFiring.result X).rules ↔ ρ = 5 := by
  constructor
  · intro inside
    rcases (RFiring.mem_result_rules _).mp inside with kept | made
    · obtain ⟨held, stays⟩ := (RFiring.mem_kept _).mp kept
      have same : ρ = 0 := Finset.mem_singleton.mp held
      subst same
      exact absurd (Or.inl ⟨rfl, rfl⟩) stays
    · exact List.mem_singleton.mp made
  · rintro rfl
    exact (RFiring.mem_result_rules _).mpr (Or.inr (List.mem_singleton_self 5))

/-- **The new occurrence holds the same code.** -/
theorem loop_reemits : (loopFiring.result X).held 5 = ⟨Code.loop, [], .linear, ()⟩ := rfl

theorem loop_result_closed : (loopFiring.result X).Closed := by
  intro ρ inside
  obtain rfl := (loop_result_rules ρ).mp inside
  rfl

theorem loop_result_present : (loopFiring.result X).present = {1, 2} := by
  show fire ({0, 1} : Finset ℕ) ((⟨[0], [], [2]⟩ : Selection ℕ).commit (T := Unit)) = {1, 2}
  decide

/-- The new occurrence takes the token at row `1`, makes row `3`, and makes `loop` at identity `6`. -/
def loopAgain : RFiring ℕ ℕ E codes (loopFiring.result X) :=
  ⟨.held 5, PUnit.unit, Subst.id atoms, ⟨[1], [], [3]⟩, [], [6], [], [], []⟩

theorem loopAgain_base_admitted : loopAgain.base.Admits X (loopFiring.result X).toState := by
  refine ⟨⟨?_, List.nodup_singleton 1, List.nodup_singleton 3, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action (loopFiring.result X).toState loopAgain.base
    intro t member σ
    have inside : t ∈ loopSpec.toRule.terms := member
    simp [loopSpec, Rule.terms] at inside
    rcases inside with rfl | rfl <;> rfl
  · have present : (loopFiring.result X).toState.present = {1, 2} := loop_result_present
    apply enabled_of
    · intro o inside
      rw [present]
      obtain rfl := List.mem_singleton.mp inside
      decide
    · intro o inside
      exact absurd inside List.not_mem_nil
    · intro o _ inside
      exact absurd inside List.not_mem_nil
    · intro o inside
      rw [present]
      obtain rfl := List.mem_singleton.mp inside
      decide
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have inside : e ∈ [(c 1, c 1), (c 1, c 1)] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

/-- **The loop goes on**: the occurrence made by the first firing fires on the next token. -/
theorem loop_again_admitted : loopAgain.Admits X (∅ : Set Code) := by
  refine (loopAgain.admits_plain X loop_result_closed loop_plain ∅).mpr
    ⟨loopAgain_base_admitted, (loop_result_rules 5).mpr rfl, rfl, rfl, List.nodup_singleton 6, rfl, ?_,
      rfl, List.nodup_nil, fun _ inside => absurd inside List.not_mem_nil, rfl⟩
  intro ρ inside held
  obtain rfl := List.mem_singleton.mp inside
  exact absurd ((loop_result_rules 6).mp held) (by decide)

/-! ## The next rule by a key -/

/-- The place of each code in the order. -/
def key : Code → ℕ
  | .stage => 0
  | .once => 1
  | .loop => 2

/-- **Least key**: the occurrence a firing uses has the least key among the held ones. -/
def Least {s : RState Tm ℕ ℕ Code Unit} (f : RFiring ℕ ℕ E codes s) : Prop :=
  ∀ ρ, f.use = Use.held ρ → ∀ ρ' ∈ s.rules, key (s.held ρ).code ≤ key (s.held ρ').code

/-- **The candidate scheduled by the key**: its restriction to the firings of least key. -/
def keyed : Interface.Step X ℕ (RState Tm ℕ ℕ Code Unit) (fun s => RFiring ℕ ℕ E codes s) :=
  Spaces.restrict (rstep X ℕ ℕ E codes (∅ : Set Code)).toStep (fun {_} f => Least f)

/-- The fact `12` at row `0`; `stage` held at identity `0` and `once` at identity `1`, linearly. -/
def staged : RState Tm ℕ ℕ Code Unit :=
  ⟨⟨PUnit.unit, [], {0}, fun _ => c 12⟩, {0, 1},
    fun ρ => ⟨if ρ = 0 then Code.stage else Code.once, [], .linear, ()⟩⟩

/-- `stage` makes an occurrence of `once` at identity `5`. -/
def stageFiring : RFiring ℕ ℕ E codes staged :=
  ⟨.held 0, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, [], [5], [], [], []⟩

/-- `once`, held at identity `1`, takes the fact and makes row `1`. -/
def laterFiring : RFiring ℕ ℕ E codes staged :=
  ⟨.held 1, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, [], [], [], [], []⟩

theorem stage_plain : stageSpec.Plain :=
  ⟨rfl, rfl, rfl, fun h inside => made_closed h inside, rfl, rfl⟩

theorem stage_base_admitted : stageFiring.base.Admits X staged.toState := by
  refine ⟨⟨?_, List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action staged.toState stageFiring.base
    intro t member σ
    exact absurd member List.not_mem_nil
  · apply enabled_of <;> simp [stageFiring, staged]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    exact absurd member List.not_mem_nil
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

theorem stage_admitted : stageFiring.Admits X (∅ : Set Code) := by
  refine (stageFiring.admits_plain X (fun _ _ => rfl) stage_plain ∅).mpr
    ⟨stage_base_admitted, Finset.mem_insert_self 0 {1}, rfl, rfl, List.nodup_singleton 5, rfl, ?_,
      rfl, List.nodup_nil, fun _ inside => absurd inside List.not_mem_nil, rfl⟩
  intro ρ inside held
  obtain rfl := List.mem_singleton.mp inside
  have member : (5 : ℕ) ∈ ({0, 1} : Finset ℕ) := held
  exact absurd member (by decide)

theorem later_base_admitted : laterFiring.base.Admits X staged.toState := by
  refine ⟨⟨?_, List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action staged.toState laterFiring.base
    intro t member σ
    have inside : t ∈ onceRule.terms := member
    simp [onceRule, Rule.terms] at inside
    rcases inside with rfl | rfl <;> rfl
  · apply enabled_of <;> simp [laterFiring, staged]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have inside : e ∈ [(c 12, c 12)] := member
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

theorem later_admitted : laterFiring.Admits X (∅ : Set Code) :=
  (laterFiring.admits_plain X (fun _ _ => rfl) (Spec.plain_ofRule onceRule) ∅).mpr
    ⟨later_base_admitted, Finset.mem_insert_of_mem (Finset.mem_singleton_self 1), rfl, rfl,
      List.nodup_nil, rfl, fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩

theorem stage_least : Least stageFiring := by
  intro ρ use ρ' _
  have used : ρ = 0 := (Use.held.inj use).symm
  subst used
  exact Nat.zero_le _

theorem later_not_least : ¬ Least laterFiring := by
  intro least
  have order := least 1 rfl 0 (Finset.mem_insert_self 0 {1})
  exact absurd order (by decide)

/-- **Scheduling by the key is a restriction**: the scheduled step admits the firing of least key and
refuses the other, which the unrestricted step admits. -/
theorem stage_first :
    keyed.Admits stageFiring ∧ ¬ keyed.Admits laterFiring ∧ laterFiring.Admits X (∅ : Set Code) :=
  ⟨⟨stage_admitted, stage_least⟩, fun admitted => later_not_least admitted.2, later_admitted⟩

#print axioms once_admitted
#print axioms once_taken
#print axioms once_then_stuck
#print axioms loop_admitted
#print axioms loop_result_rules
#print axioms loop_reemits
#print axioms loop_again_admitted
#print axioms stage_admitted
#print axioms later_admitted
#print axioms stage_first

end Exec

#print axioms stuck_of_no_rules

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
