import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIteratedAgreement

/-!
# Controls for iterated native residuals

## Positive: three makers

Three live firings that make different occurrences and tell nothing form a clear family
(`makers_clear`), so every order of the three is admitted and every two orders agree up to dead
names (`makers_every_order`).

## Negative: pairwise clearness is not enough

A state with two shared names `X` and `Y`, and three tellers: `X = true`, `Y = false` and `X = Y`.

* Each is admitted (`tellers_admitted`), and every two leave each other clear
  (`tellers_pairwise`): every two equations have a common solution.
* The three have no joint solution (`tellers_not_jointly`), so **no order of the three is a
  sequential run** (`tellers_no_order`): the third firing of every order is refused, whichever it is.

So the residual of a pairwise clear family need not be pairwise clear, and the condition of
`Step/NativeIterated` is the right one: joint solvability of the whole family is necessary for a word
without inner causal dependence (`Sequential.jointly`), and together with pairwise clearness it is
sufficient (`every_order_admitted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeIterated
open NativeResidualExample (tiny noLocals bit maker maker_realized clear_makers initial)

namespace NativeIteratedControls

/-! ## Positive: three makers -/

theorem makers_clears (port other : ℕ) (different : port ≠ other) : Clears (maker port none) (maker other none) :=
  ⟨clear_makers port other different, clear_makers other port (Ne.symm different)⟩

/-- Three makers of different occurrences. -/
def makers : List (LiveFiring initial) := [maker 0 none, maker 1 none, maker 2 none]

/-- **Three makers of different occurrences form a clear family.** -/
theorem makers_clear : FamilyClear initial makers where
  admitted f member := by
    simp only [makers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact maker_realized _ _
  pairwise := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact makers_clears 0 1 (by decide)
      · exact makers_clears 0 2 (by decide)
    · intro x member
      rw [List.mem_singleton] at member
      subst member
      exact makers_clears 1 2 (by decide)
  jointly := by
    refine ⟨initial.infoFrame, Assignment.compose (generator _)
      (ContextualSelectionViews.capturedTarget noLocals NativeResidualExample.oneName), fun f member => ?_⟩
    simp only [makers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      exact ⟨generator _, fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- **Every order of the three makers is admitted, and every two agree up to dead names.** -/
theorem makers_every_order :
    ∃ t₀, Sequential initial makers t₀ ∧ ∀ order : List (LiveFiring initial), order.Perm makers →
      ∃ t, Sequential initial order t ∧ NativeDead.DeadEquiv t₀ t :=
  every_order_agrees makers_clear

/-! ## Negative: three tellers -/

/-- Two parameterless shared names, `X` (`true`) and `Y` (`false`). -/
def twoNames : Bool → MetaArity tiny := fun _ => ([], ())

/-- **The state**: the names `X` and `Y`, no occurrences, no knowledge. -/
def pair : NativeState tiny ℕ ([] : Ctx tiny) () :=
  ⟨Empty, inferInstance, noLocals,
    { Names := Bool
      equality := inferInstance
      declarations := twoNames
      occupied := ∅
      equations := []
      present := ∅
      rows := fun _ => ContextualConditionalRows.ofStored noLocals twoNames (.shared (bit twoNames true)) }⟩

/-- A shared name, in a rule. -/
def name (x : Bool) : Term (signature tiny (ContextualActivatedStep.source noLocals twoNames)) ([] : Ctx tiny) () :=
  generator (ContextualActivatedStep.source noLocals twoNames) (.inr x)

/-- A live firing that makes the occurrence `port` and tells one equation. -/
def teller (port : ℕ) (left right : Term (signature tiny (ContextualActivatedStep.source noLocals twoNames))
    ([] : Ctx tiny) ()) : LiveFiring pair where
  rule := ⟨[], [], [(left, right)], [], [bit (ContextualActivatedStep.source noLocals twoNames) false]⟩
  selection := ⟨[], [], [port]⟩
  outputs _ := bit (ContextualActivatedStep.target noLocals twoNames) false
  patterns := []
  fuel := 0

/-- The scope a teller's rule opens at. -/
abbrev ruleScope (port : ℕ) : ℕ :=
  ContextualActivationScopes.scopeAt (∅ : Finset ℕ) (ContextualActivationScopes.rulePort (⟨[], [], [port]⟩ : Selection ℕ))

theorem teller_information (port : ℕ) (left right : Term (signature tiny
    (ContextualActivatedStep.source noLocals twoNames)) ([] : Ctx tiny) ()) :
    (teller port left right).toNative.information =
      [(observe (ContextualFreshening.termAt noLocals twoNames (ruleScope port) left),
        observe (ContextualFreshening.termAt noLocals twoNames (ruleScope port) right))] := rfl

/-- **A teller's solutions are the solutions of its equation.** -/
theorem models_teller_iff {W : Type} {next : W → MetaArity tiny}
    (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) next) (port : ℕ)
    (left right : Term (signature tiny (ContextualActivatedStep.source noLocals twoNames)) ([] : Ctx tiny) ()) :
    ContextualResidual.Models σ (teller port left right).toNative.information ↔
      instantiate σ (ContextualFreshening.termAt noLocals twoNames (ruleScope port) left) =
        instantiate σ (ContextualFreshening.termAt noLocals twoNames (ruleScope port) right) := by
  rw [teller_information]
  constructor
  · intro solved
    exact observe_injective (solved _ List.mem_cons_self)
  · intro same equation member
    rw [List.mem_singleton.mp member]
    exact congrArg observe same

theorem opened (port : ℕ) (x : Bool) :
    ContextualFreshening.termAt noLocals twoNames (ruleScope port) (name x) =
      generator (ContextualActivatedStep.target noLocals twoNames) (.inr x) :=
  instantiate_generator (ContextualFreshening.assignment noLocals twoNames (ruleScope port)) (.inr x)

/-- A solution giving `X` and `Y` constants. -/
def valuation (valueX valueY : Bool) :
    Assignment (ContextualActivatedStep.target noLocals twoNames) (ContextualActivatedStep.target noLocals twoNames)
  | .inl local_ => nomatch local_.name
  | .inr x => bit (ContextualActivatedStep.target noLocals twoNames) (cond x valueX valueY)

theorem read_name {W : Type} {next : W → MetaArity tiny}
    (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) next) (port : ℕ) (x : Bool) :
    instantiate σ (ContextualFreshening.termAt noLocals twoNames (ruleScope port) (name x)) = σ (.inr x) :=
  (congrArg (instantiate σ) (opened port x)).trans (instantiate_generator σ (.inr x))

/-- `X = true`. -/
def tellX : LiveFiring pair := teller 0 (name true) (bit _ true)

/-- `Y = false`. -/
def tellY : LiveFiring pair := teller 1 (name false) (bit _ false)

/-- `X = Y`. -/
def tellSame : LiveFiring pair := teller 2 (name true) (name false)

/-- The three tellers. -/
def tellers : List (LiveFiring pair) := [tellX, tellY, tellSame]

theorem models_tellX {W : Type} {next : W → MetaArity tiny}
    (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) next) :
    ContextualResidual.Models σ tellX.toNative.information ↔ σ (.inr true) = bit next true :=
  (models_teller_iff σ 0 _ _).trans (by rw [read_name]; rfl)

theorem models_tellY {W : Type} {next : W → MetaArity tiny}
    (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) next) :
    ContextualResidual.Models σ tellY.toNative.information ↔ σ (.inr false) = bit next false :=
  (models_teller_iff σ 1 _ _).trans (by rw [read_name]; rfl)

theorem models_tellSame {W : Type} {next : W → MetaArity tiny}
    (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) next) :
    ContextualResidual.Models σ tellSame.toNative.information ↔ σ (.inr true) = σ (.inr false) :=
  (models_teller_iff σ 2 _ _).trans (by rw [read_name, read_name]; exact Iff.rfl)

/-- **A teller with a solution is admitted.** -/
theorem teller_realized (port : ℕ)
    (left right : Term (signature tiny (ContextualActivatedStep.source noLocals twoNames)) ([] : Ctx tiny) ())
    (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) (ContextualActivatedStep.target noLocals twoNames))
    (solved : ContextualResidual.Models σ (teller port left right).toNative.information) :
    (teller port left right).toNative.Realized := by
  apply (native_admits_iff (S := tiny) (teller port left right).toNative).mpr
  refine ⟨⟨List.nodup_nil, List.nodup_singleton port, rfl, rfl, rfl⟩, ?_, ⟨pair.infoFrame, σ, solved⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, fun _ member => by simp [Selection.commit] at member⟩
    · show ([] : List ℕ).toFinset ⊆ (∅ : Finset ℕ)
      simp
    · show ([] : List ℕ).toFinset ⊆ (∅ : Finset ℕ)
      simp
    · show Disjoint ([] : List ℕ).toFinset ([] : List ℕ).toFinset
      simp
    · show Disjoint [port].toFinset (∅ : Finset ℕ)
      simp
  · intro b ρ _
    exact ⟨fun check member => absurd member List.not_mem_nil, fun query member => absurd member List.not_mem_nil⟩

/-- **Each teller is admitted.** -/
theorem tellers_admitted : ∀ f ∈ tellers, f.toNative.Realized := by
  intro f member
  simp only [tellers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact teller_realized 0 _ _ (valuation true false) ((models_tellX _).mpr rfl)
  · exact teller_realized 1 _ _ (valuation true false) ((models_tellY _).mpr rfl)
  · exact teller_realized 2 _ _ (valuation true true) ((models_tellSame _).mpr rfl)

/-- Two tellers with a common solution leave each other clear. -/
theorem tellers_clear {port other : ℕ} (different : port ≠ other)
    {left right left' right' : Term (signature tiny (ContextualActivatedStep.source noLocals twoNames)) ([] : Ctx tiny) ()}
    (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) (ContextualActivatedStep.target noLocals twoNames))
    (first : ContextualResidual.Models σ (teller port left right).toNative.information)
    (second : ContextualResidual.Models σ (teller other left' right').toNative.information) :
    Clear (teller port left right) (teller other left' right').selection (teller other left' right').rule
      (teller other left' right').outputs where
  takes := by
    show Disjoint ([] : List ℕ).toFinset ([] : List ℕ).toFinset
    simp
  ports := by
    show Disjoint [port].toFinset [other].toFinset
    simp [different]
  keeps := by
    show Disjoint ([] : List ℕ).toFinset ([] : List ℕ).toFinset
    simp
  consistent := ⟨pair.infoFrame, ⟨⟨σ, σ, first, second, rfl⟩⟩⟩
  blindTakes _ _ _ taken := absurd taken List.not_mem_nil
  blindOutputs _ _ _ _ := ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **Every two tellers leave each other clear.** -/
theorem tellers_pairwise : tellers.Pairwise Clears := by
  have xy : Clears tellX tellY :=
    ⟨tellers_clear (by decide) (valuation true false) ((models_tellX _).mpr rfl) ((models_tellY _).mpr rfl),
      tellers_clear (by decide) (valuation true false) ((models_tellY _).mpr rfl) ((models_tellX _).mpr rfl)⟩
  have xs : Clears tellX tellSame :=
    ⟨tellers_clear (by decide) (valuation true true) ((models_tellX _).mpr rfl) ((models_tellSame _).mpr rfl),
      tellers_clear (by decide) (valuation true true) ((models_tellSame _).mpr rfl) ((models_tellX _).mpr rfl)⟩
  have ys : Clears tellY tellSame :=
    ⟨tellers_clear (by decide) (valuation false false) ((models_tellY _).mpr rfl) ((models_tellSame _).mpr rfl),
      tellers_clear (by decide) (valuation false false) ((models_tellSame _).mpr rfl) ((models_tellY _).mpr rfl)⟩
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩
  · intro x member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact xy
    · exact xs
  · intro x member
    rw [List.mem_singleton] at member
    subst member
    exact ys

/-- The tellers take and read nothing. -/
theorem tellers_unmade : Unmade tellers := by
  intro x inX y _ o member
  simp only [tellers, List.mem_cons, List.not_mem_nil, or_false] at inX
  rcases inX with rfl | rfl | rfl <;> exact absurd member List.not_mem_nil

/-- **The three tellers have no joint solution.** -/
theorem tellers_not_jointly : ¬ Jointly pair tellers := by
  rintro ⟨b, shared, each⟩
  obtain ⟨σ₁, models₁, agree₁⟩ := each tellX List.mem_cons_self
  obtain ⟨σ₂, models₂, agree₂⟩ := each tellY (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨σ₃, models₃, agree₃⟩ := each tellSame (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have atName : ∀ (σ : Assignment (ContextualActivatedStep.target noLocals twoNames) b.arity),
      Assignment.compose σ (ContextualSelectionViews.capturedTarget noLocals twoNames) = shared →
        ∀ x, σ (.inr x) = shared x :=
    fun σ agree x => (instantiate_generator σ (.inr x)).symm.trans (congrFun agree x)
  have clash : bit b.arity true = bit b.arity false :=
    ((models_tellX σ₁).mp models₁).symm.trans ((atName σ₁ agree₁ true).trans
      ((atName σ₃ agree₃ true).symm.trans (((models_tellSame σ₃).mp models₃).trans
        ((atName σ₃ agree₃ false).trans ((atName σ₂ agree₂ false).symm.trans ((models_tellY σ₂).mp models₂))))))
  unfold bit at clash
  cases clash

/-- **No order of the three tellers is a sequential run**, though every two leave each other clear. -/
theorem tellers_no_order {order : List (LiveFiring pair)} (perm : order.Perm tellers) {t : NativeState tiny ℕ ([] : Ctx tiny) ()} :
    ¬ Sequential pair order t :=
  no_order_of_not_jointly tellers_unmade tellers_not_jointly perm

/-- **Pairwise clearness is not enough**: three admitted, pairwise clear live firings with no
sequential run in any order. -/
theorem pairwise_not_enough :
    (∀ f ∈ tellers, f.toNative.Realized) ∧ tellers.Pairwise Clears ∧
      ∀ order : List (LiveFiring pair), order.Perm tellers → ∀ t, ¬ Sequential pair order t :=
  ⟨tellers_admitted, tellers_pairwise, fun _ perm _ => tellers_no_order perm⟩

end NativeIteratedControls

#print axioms NativeIteratedControls.makers_clear
#print axioms NativeIteratedControls.makers_every_order
#print axioms NativeIteratedControls.tellers_admitted
#print axioms NativeIteratedControls.tellers_pairwise
#print axioms NativeIteratedControls.tellers_not_jointly
#print axioms NativeIteratedControls.tellers_no_order
#print axioms NativeIteratedControls.pairwise_not_enough

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
