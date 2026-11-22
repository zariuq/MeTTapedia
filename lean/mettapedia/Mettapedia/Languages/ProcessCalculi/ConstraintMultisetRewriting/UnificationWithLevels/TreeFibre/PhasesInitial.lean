import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAudit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknown

/-!
# Initial solutions beyond telescopes of universe families, in phases

A principal answer that is an epimorphism on terms is the initial solution (`Principal.initial`). The phases of
`ThroughPhases` compose decisions along three kinds of updates, and each keeps answers epimorphic:

* **composition** (`then_epi`): an update followed by another;
* **carrying past a declaration** (the tree's `Update.lift`, epimorphic by `NativeTypesOnTheStep.lift_epi`);
* **exchanging the two newest declarations** (`exchange_epi`): its answer has a section (`epi_of_section`). Exchanging
  twice gives the store back (`exchange_twice_remaining`), which is why the phases bound exchanges by a depth.

So **every store decided in phases from bases with epimorphic answers has an initial solution** (`phases_epi`,
`phases_initial`), whatever its telescope, declarations mentioning solved unknowns included. A base with epimorphic
answers: a run driven by the rank whose answer covers its frame by variables at their own types (`Decided.ofRankCover`,
`ofRankCover_epi`, by `NativeTypesOnTheStep.epi_of_cover`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

/-! ## Epimorphic answers compose -/

section Epi

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **Epimorphisms on terms compose.** -/
theorem comp_epi {A B C : Context rules} (σ : B ⟶ A) (τ : C ⟶ B) (epiσ : EpiOnTerms (frames levels) σ)
    (epiτ : EpiOnTerms (frames levels) τ) : EpiOnTerms (frames levels) (τ ≫ σ) := by
  intro D g h same
  have moved : ∀ (k : D ⟶ C) (t : TotalTerm A),
      (frames levels).act (k ≫ τ) ((frames levels).act σ t) = (frames levels).act k ((frames levels).act (τ ≫ σ) t) := by
    intro k t
    show (t.reindex σ).reindex (k ≫ τ) = (t.reindex (τ ≫ σ)).reindex k
    rw [reindex_comp, reindex_comp]
  have stepFirst : Agree (frames levels) (g ≫ τ) (h ≫ τ) := by
    apply epiσ
    intro t
    rw [moved g t, moved h t]
    exact same t
  apply epiτ
  intro u
  have agree := stepFirst u
  have e1 : (frames levels).act (g ≫ τ) u = (frames levels).act g ((frames levels).act τ u) := reindex_comp u g τ
  have e2 : (frames levels).act (h ≫ τ) u = (frames levels).act h ((frames levels).act τ u) := reindex_comp u h τ
  rw [e1, e2] at agree
  exact agree

/-- **An update followed by another has an epimorphic answer** when both have. -/
theorem then_epi {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)} (first : Update levels problem)
    (second : Update levels first.remaining) (epiFirst : EpiOnTerms (frames levels) first.answer)
    (epiSecond : EpiOnTerms (frames levels) second.answer) :
    EpiOnTerms (frames levels) (first.then second).answer :=
  comp_epi first.answer second.answer epiFirst epiSecond

/-- **An answer with a section is an epimorphism on terms**: every term over its target is the instance of one over
its source. -/
theorem epi_of_section {Γ target : Context rules} (answer : target ⟶ Γ) (inverse : Γ ⟶ target)
    (split : answer ≫ inverse = 𝟙 target) : EpiOnTerms (frames levels) answer := by
  intro b g h same u
  have key : (u.reindex inverse).reindex answer = u := by
    rw [← reindex_comp, split, reindex_id]
  have moved := same (u.reindex inverse)
  change (frames levels).E (((u.reindex inverse).reindex answer).reindex g)
    (((u.reindex inverse).reindex answer).reindex h) at moved
  rw [key] at moved
  exact moved

/-- **The exchange of the two newest declarations has an epimorphic answer.** -/
theorem exchange_epi {Γ : Context rules} (first next : TypeOver Γ)
    (problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))) :
    EpiOnTerms (frames levels) (ContextualDependentPrune.exchange levels first next problem).answer :=
  epi_of_section (ContextualDependentParameterExchange.swap next first)
    (ContextualDependentParameterExchange.swap first next) (ContextualDependentParameterExchange.swap_twice next first)

/-- **Exchanging twice gives the store back.** So no rank of telescopes and stores is lowered by every exchange; the
phases bound their exchanges by a depth instead. -/
theorem exchange_twice_remaining {Γ : Context rules} (first next : TypeOver Γ)
    (problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))) :
    (ContextualDependentPrune.exchange levels next first
      (ContextualDependentPrune.exchange levels first next problem).remaining).remaining = problem := by
  show (frames levels).applyStore (ContextualDependentParameterExchange.swap first next)
      ((frames levels).applyStore (ContextualDependentParameterExchange.swap next first) problem) = problem
  unfold Frames.applyStore
  rw [List.map_map]
  conv_rhs => rw [← List.map_id problem]
  apply List.map_congr_left
  intro e _
  show (((e.1.reindex (ContextualDependentParameterExchange.swap next first)).reindex
      (ContextualDependentParameterExchange.swap first next)),
    ((e.2.reindex (ContextualDependentParameterExchange.swap next first)).reindex
      (ContextualDependentParameterExchange.swap first next))) = e
  rw [← reindex_comp, ← reindex_comp, ContextualDependentParameterExchange.swap_twice, reindex_id, reindex_id]

end Epi

/-! ## Decisions with epimorphic answers -/

section Decisions

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A decision with an epimorphic answer**: a finished update whose answer is an epimorphism on terms, or a
refutation. -/
def Decided.Epi {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} : Decided problem → Prop
  | .solved update _ => EpiOnTerms (frames S.levels) update.answer
  | .refuted _ => True

/-- **A solved decision with an epimorphic answer is the initial solution.** -/
theorem Decided.initial_of_epi {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem} {finished : update.remaining = []}
    (epi : (Decided.solved update finished).Epi) : InitialSolution (frames S.levels) problem update.answer :=
  Principal.initial (update.completed finished) epi

theorem Decided.after_epi {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (first : Update S.levels problem)
    (epiFirst : EpiOnTerms (frames S.levels) first.answer) (d : Decided first.remaining) (epi : d.Epi) :
    (Decided.after first d).Epi := by
  cases d with
  | solved update finished => exact then_epi first update epiFirst epi
  | refuted absent => trivial

theorem Decided.equivalent_epi {Θ : Context S.R} {problem other : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent problem other) (d : Decided other) (epi : d.Epi) :
    (Decided.equivalent same d).Epi := by
  cases d with
  | solved update finished => exact epi
  | refuted absent => trivial

theorem decideNewest_epi {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (decide : {Γ : Context S.R} → (type : TypeOver Γ) → (stored : EquationStore (TotalTerm (extend Γ type))) →
      Option (Decided stored))
    (epi : ∀ {Γ : Context S.R} (type : TypeOver Γ) (stored : EquationStore (TotalTerm (extend Γ type)))
      (d : Decided stored), decide type stored = some d → d.Epi) :
    ∀ d, decideNewest view problem decide = some d → d.Epi := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact epi type problem

theorem decideTwo_epi {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (problem : EquationStore (TotalTerm Θ))
    (decide : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Decided stored))
    (epi : ∀ {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) (d : Decided stored),
        decide older newer stored = some d → d.Epi) :
    ∀ d, decideTwo outer inner problem decide = some d → d.Epi := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact epi older newer problem

end Decisions

/-! ## The phases keep answers epimorphic -/

section Phases

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **Two phases at the newest declaration keep answers epimorphic**: the first phase's answer carried past the
declaration stays one, and composing with the second phase's keeps it. -/
theorem phaseAt_epi (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (stored : EquationStore (TotalTerm (extend Γ type)))
    (decide : {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Option (Decided problem))
    (epi : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (d : Decided problem),
      decide problem = some d → d.Epi) :
    ∀ d, phaseAt facts roots heads algebra declared choices reducer fuel type stored decide = some d → d.Epi := by
  intro d found
  unfold phaseAt at found
  dsimp only at found
  split at found
  · cases found
  · cases found
    trivial
  · rename_i update finished first
    have epiUpdate : EpiOnTerms (frames S.levels) update.answer := epi _ _ first
    obtain ⟨rest, restFound, rfl⟩ := Option.map_eq_some_iff.mp found
    exact Decided.after_epi _ (NativeTypesOnTheStep.lift_epi S.levels update type epiUpdate) _
      (Decided.equivalent_epi _ rest (epi _ rest restFound))

/-- **The exchange of the two newest declarations keeps answers epimorphic.** -/
theorem exchangeAt_epi (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (decide : {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Option (Decided problem))
    (epi : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (d : Decided problem),
      decide problem = some d → d.Epi) :
    ∀ d, exchangeAt facts roots heads algebra declared choices reducer fuel older newer stored decide = some d →
      d.Epi := by
  intro d found
  unfold exchangeAt at found
  split at found
  · cases found
  · split at found
    · cases found
    · split at found
      · rename_i next _ same
        have independent : newer = ContextualDependentParameterExchange.second older next.val :=
          TypeOver.ext same.1 same.2
        subst independent
        obtain ⟨rest, restFound, rfl⟩ := Option.map_eq_some_iff.mp found
        exact Decided.after_epi _ (exchange_epi older next.val stored) _ (epi _ rest restFound)
      · cases found

variable (base : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Option (Decided problem))

/-- **Every decision in phases from bases with epimorphic answers has an epimorphic answer.** -/
theorem phases_epi
    (baseEpi : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (d : Decided problem),
      base problem = some d → d.Epi) (fuel : Nat) :
    ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (d : Decided problem),
      phases facts roots heads algebra declared choices reducer base fuel depth problem = some d → d.Epi
  | 0, _, problem, d, found => baseEpi problem d found
  | depth + 1, Θ, problem, d, found => by
      have ih : ∀ {Θ' : Context S.R} (P : EquationStore (TotalTerm Θ')) (d' : Decided P),
          phases facts roots heads algebra declared choices reducer base fuel depth P = some d' → d'.Epi :=
        fun P d' h => phases_epi baseEpi fuel depth P d' h
      have unfolded := phases.eq_2 facts roots heads algebra declared choices reducer base fuel Θ problem depth
      rw [Nat.succ_eq_add_one] at unfolded
      rw [unfolded] at found
      split at found
      · rename_i found' hb
        cases found
        exact baseEpi problem _ hb
      · split at found
        · cases found
        · rename_i outer _
          split at found
          · rename_i found' hNewest
            cases found
            exact decideNewest_epi outer problem _
              (fun type stored d' h => phaseAt_epi facts roots heads algebra declared choices reducer fuel type stored
                _ (fun P d'' h'' => ih P d'' h'') d' h) _ hNewest
          · split at found
            · cases found
            · rename_i inner _
              exact decideTwo_epi outer inner problem _
                (fun older newer stored d' h => exchangeAt_epi facts roots heads algebra declared choices reducer fuel
                  older newer stored _ (fun P d'' h'' => ih P d'' h'') d' h) d found

/-- **Initial solutions beyond telescopes of universe families**: a store decided in phases, from bases with epimorphic
answers, to a finished update has its answer as the initial solution. -/
theorem phases_initial
    (baseEpi : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (d : Decided problem),
      base problem = some d → d.Epi) {fuel depth : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem} {finished : update.remaining = []}
    (found : phases facts roots heads algebra declared choices reducer base fuel depth problem =
      some (.solved update finished)) :
    InitialSolution (frames S.levels) problem update.answer :=
  Decided.initial_of_epi (finished := finished)
    (phases_epi facts roots heads algebra declared choices reducer base baseEpi fuel depth problem
      (.solved update finished) found)

end Phases

/-! ## A base with epimorphic answers -/

section Base

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [DecidableEq Head]

/-- **A decision of a run driven by the rank whose answer covers its frame**: a solved run whose answer sends some
variable of the store's frame to each variable of its own, at its own type; or a refutation. -/
def Decided.ofRankCover (solver : ContextualDependentWorklist.Solver S.levels) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Option (Decided problem) :=
  match runRank solver problem with
  | .solved state finished => if NativeTypesOnTheStep.VariableCover state.answer then some (.solved state finished)
      else none
  | .refuted absent => some (.refuted absent)
  | _ => none

/-- **Its decisions have epimorphic answers.** -/
theorem ofRankCover_epi (solver : ContextualDependentWorklist.Solver S.levels) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) (d : Decided problem)
    (found : Decided.ofRankCover solver problem = some d) : d.Epi := by
  unfold Decided.ofRankCover at found
  split at found
  · rename_i state finished _
    split at found
    · rename_i cover
      cases found
      exact NativeTypesOnTheStep.epi_of_cover S.levels cover
    · cases found
  · cases found
    trivial
  · cases found

end Base

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
