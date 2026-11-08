import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceLogic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceStepControls

/-!
# Controls for the step and history logics

## A firing that writes nothing (`Silent.silent_control`)

The firing `silent` takes, reads and makes nothing. It is statically independent of itself, so it
repeats without bound in one step: at `{a}` there is a step under `{(), …, ()}` for every positive
multiplicity. Each step label still has finitely many successors (the program is finite), but the
steps at one configuration are infinitely many, which the write hypothesis of
`RaceLogic.stepMoves_finite` excludes.

## Separating formulas

* **Step logic** (`step_formula_separates`): `⟨{a, b}⟩⊤` holds at `a | b` and fails at `a.b + b.a`
  (the programs of `RaceStepControls`), which are interleaving bisimilar.
* **History logic** (`hist_formula_separates`): `⟨(a, ∅)⟩⟨(b, {0})⟩⊤`, with the causal past of the
  second modality read off `(a | b) + a.b`, holds at `(a | b) + a.b` and fails at `a | b`, which are
  step bisimilar: only in the first does a `b` depend on an `a`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.LogicControls

open AnnotatedRuns (Firing follow StaticIndependent Executable)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open Mettapedia.GSLT.HennessyMilner (Formula)

universe uT uS

/-! ## A firing that writes nothing -/

namespace Silent

/-- One occurrence identity. -/
inductive Site
  | a
  deriving DecidableEq

variable {T : Type uT} {S : Type uS} (τ : T)

def label : Site → T := fun _ => τ

/-- **The firing that writes nothing**: it takes, reads and makes nothing. -/
def silent : Firing T S Site := ⟨⟨[], [], [], [], []⟩, [], ⟨[], [], []⟩⟩

def alphabet : List (Unit × Firing T S Site) := [((), silent)]

def offers (ℓ : Unit) (f : Firing T S Site) : Prop := (ℓ, f) ∈ alphabet (S := S)

def C : Configuration T Site := ⟨[], {.a}⟩

theorem ground_silent : Ground (label τ) (silent (T := T) (S := S)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, List.nodup_nil, List.nodup_nil⟩

theorem enabled_silent (store : Finset Site) :
    Enabled (label τ) store ((silent (T := T) (S := S)).selection.commit (T := T)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, silent]

variable (A : SubstitutionAction T S)

include A in
theorem independent_silent : StaticIndependent (label τ) (silent (T := T) (S := S)) silent := by
  have static : (silent (T := T) (S := S)).Static :=
    ⟨rfl, fun query member => by simp [silent] at member⟩
  exact ⟨static, static, (AnnotatedRuns.independent_self_iff (label τ) A.identity silent).mpr ⟨rfl, rfl⟩⟩

theorem executable_silent :
    ∀ (k : ℕ) (D : Configuration T Site), Reflexive D.equations →
      Executable A (label τ) D (List.replicate k (silent (T := T) (S := S)))
  | 0, _, refl => consistent_of_reflexive A refl
  | k + 1, _, refl =>
      ⟨((ground_silent τ).valid_iff A refl).mpr (enabled_silent τ _),
        executable_silent k _ ((ground_silent τ).reflexive_result refl)⟩

/-- **`silent` repeats without bound in one step.** -/
theorem steps (k : ℕ) :
    StepMoves A (label τ) (offers (T := T) (S := S)) C (Multiset.replicate (k + 1) ())
      (follow (label τ) C (List.replicate (k + 1) (silent (T := T) (S := S)))) := by
  refine ⟨List.replicate (k + 1) ((), silent), by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro x member
    rw [List.eq_of_mem_replicate member]
    simp [offers, alphabet]
  · rw [List.map_replicate]
    exact List.pairwise_replicate.mpr (.inr (independent_silent τ A))
  · rw [List.map_replicate]
    exact executable_silent τ A (k + 1) C reflexive_nil
  · rw [List.map_replicate]
    exact (Multiset.coe_replicate _ _).symm
  · rw [List.map_replicate]

/-- **Image-finite per label, not finitely branching.** The program is finite, so each step label has
finitely many successors; the steps at `{a}` are infinitely many; and `silent` writes nothing. -/
theorem silent_control :
    (stepSystem A (label τ) (offers (T := T) (S := S))).ImageFiniteModulo ∧
      ¬ {p : Multiset Unit × Configuration T Site |
          StepMoves A (label τ) (offers (T := T) (S := S)) C p.1 p.2}.Finite ∧
      (silent (T := T) (S := S)).selection.taken = [] ∧ (silent (T := T) (S := S)).selection.made = [] := by
  refine ⟨stepSystem_imageFiniteModulo A (label τ) offers fun ℓ =>
    (Set.finite_singleton (silent (T := T) (S := S))).subset ?_, ?_, rfl, rfl⟩
  · intro f offered
    simpa [offers, alphabet] using offered
  · refine Set.infinite_of_injective_forall_mem (α := ℕ)
      (f := fun k => ((Multiset.replicate (k + 1) () : Multiset Unit),
        follow (label τ) C (List.replicate (k + 1) (silent (T := T) (S := S))))) ?_ (steps τ A)
    intro k k' same
    have cards := congrArg (fun p : Multiset Unit × Configuration T Site => Multiset.card p.1) same
    simpa using cards

end Silent

/-! ## Separating formulas -/

section Separating

open StepControls

variable {T : Type uT} {S : Type uS} (τ : T) (A : SubstitutionAction T S)

/-- **The step logic separates `a | b` from `a.b + b.a`**: `⟨{a, b}⟩⊤`. -/
theorem step_formula_separates :
    StepSat A (StepControls.label τ) (StepControls.offers (alphabet₃ (S := S) τ))
        (.dia ↑[Act.a, Act.b] .top) PAR ∧
      ¬ StepSat A (StepControls.label τ) (StepControls.offers (alphabet₃ (S := S) τ))
        (.dia ↑[Act.a, Act.b] .top) SEQ := by
  refine ⟨⟨End₂ τ, PAR_steps_both₃ τ A, trivial⟩, ?_⟩
  rintro ⟨D, stepped, _⟩
  have := SEQ_no_double_step τ A stepped
  simp at this

/-- The history formula: an `a` with empty past, then a `b` whose past is that of `ht` after
`hs`. -/
noncomputable def dependentB : Formula PEmpty.{1} (Act × Finset ℕ) :=
  .dia (Act.a, ∅) (.dia (Act.b, past (StepControls.label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ)) .top)

/-- **The history logic separates `(a | b) + a.b` from `a | b`**, which are step bisimilar: only in the
first does a `b` depend on an `a`. -/
theorem hist_formula_separates :
    HistSat A (StepControls.label τ) (StepControls.offers (alphabet₄ (S := S) τ)) (dependentB (S := S) τ) (MIX, []) ∧
      ¬ HistSat A (StepControls.label τ) (StepControls.offers (alphabet₄ (S := S) τ)) (dependentB (S := S) τ)
        (PAR, []) := by
  constructor
  · have move₁ : HMoves A (StepControls.label τ) (StepControls.offers (alphabet₄ τ)) (MIX, [])
        (Act.a, ∅) ((hs (S := S) τ).result (StepControls.label τ) MIX, [] ++ [(hs τ, ∅)]) :=
      ⟨hs τ, mem₄_hs τ, valid₄_of τ A .a (mem₄_hs τ) reflexive_nil (of_decide_eq_true rfl),
        (past_nil τ _).symm, rfl⟩
    have move₂ : HMoves A (StepControls.label τ) (StepControls.offers (alphabet₄ τ))
        ((hs (S := S) τ).result (StepControls.label τ) MIX, [] ++ [(hs τ, ∅)])
        (Act.b, past (StepControls.label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ))
        ((ht τ).result (StepControls.label τ) ((hs τ).result (StepControls.label τ) MIX),
          ([] ++ [(hs τ, ∅)]) ++
            [(ht τ, past (StepControls.label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ))]) :=
      ⟨ht τ, mem₄_ht τ, by
        rw [result_hs]
        exact valid₄_of τ A .b (mem₄_ht τ) (reflexive_E τ 2) (of_decide_eq_true rfl), rfl, rfl⟩
    exact ⟨_, move₁, _, move₂, trivial⟩
  · rintro ⟨x, ⟨f, offered, valid, _, rfl⟩, y, ⟨g, offered', valid', samePast, _⟩, _⟩
    rcases at₄_PAR offered valid with ⟨_, rfl⟩ | ⟨wrong, _⟩
    swap
    · exact absurd wrong (by simp)
    have valid'' : g.Valid A (StepControls.label τ) ((fa τ).result (StepControls.label τ) PAR) := valid'
    rw [result_fa] at valid''
    obtain ⟨_, rfl⟩ := at₄_PARa offered' valid''
    have dependentPast : 0 ∈ past (StepControls.label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ) :=
      directPast_subset_past _ _ (mem_directPast.mpr ⟨by simp, _, rfl, hs_ht_dependent τ A⟩)
    have independentPast : past (StepControls.label τ) ([] ++ [(fa (S := S) τ, (∅ : Finset ℕ))]) (fb τ) ⊆
        Finset.range 0 := by
      refine past_subset_of_independent (wf_concat wf_nil (Finset.empty_subset _)) ?_
      intro i e _ get
      rcases getElem?_concat_eq_some get with ⟨lt, _⟩ | ⟨_, rfl⟩
      · simp at lt
      · exact fa_fb_independent τ A
    have key : past (StepControls.label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ) =
        past (StepControls.label τ) ([] ++ [(fa (S := S) τ, (∅ : Finset ℕ))]) (fb τ) := samePast
    rw [key] at dependentPast
    have := independentPast dependentPast
    simp at this

end Separating

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.LogicControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.LogicControls in
#print axioms Silent.steps
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.LogicControls in
#print axioms Silent.silent_control
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.LogicControls in
#print axioms step_formula_separates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.LogicControls in
#print axioms hist_formula_separates
