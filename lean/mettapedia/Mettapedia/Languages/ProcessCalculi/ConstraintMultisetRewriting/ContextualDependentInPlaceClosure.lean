import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentControls

/-!
# `Stratified` is not closed under in-place answers; the class with η-short metavariable occurrences

R90's concern 2: solving an older metavariable in place instantiates the later declarations, and a later declaration may
get more leading Π binders. Its occurrences keep their arguments, so they are no longer applied to exactly the declared
arity, and the store leaves `Stratified`, whose sides read arities from the declarations.

**The witness** (`witnessStore`), over `A : U0, X : U0, G : U0 → U0 → X`:

* `X ≐ Π A (Π A A)` at `U0`, and `λ a b. G a b ≐ λ a b. G b a` at `U0 → U0 → X`;
* it is in the dynamic pattern fragment (`witness_in_fragment`);
* the first round of the intersection family solves `X` in place past `G` (R107's placed rule): `G` is declared
  `U0 → U0 → Π A (Π A A)`, four Π binders, and its occurrences keep two arguments; the residual store is **not**
  `Stratified` (`witness_first_round`); the same holds for the later families, which act only where this one is stuck
  (`ContextualDependentInPlaceClosure.Controls.witness_first_round_last`);
* the family still commits on it, by intersection (`witness_committed`).

So the settling class of the final family cannot be `Stratified`. The same witness raises the declarations plus the total
metavariable arity from `3 + 2` to `2 + 4`, so that sum is not a rank the answers lower (`witness_first_round`).

**The corrected class** (`StratifiedShort`) reads every metavariable occurrence as applied to **at most** its declared
arity: an η-short occurrence. It contains `Stratified` (`stratifiedShort_of_stratified`), hence the fragment
(`stratifiedShort_of_fragment`), and it contains the witness's residual store (`witness_first_round`). Its closure under
every progress of the family is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInPlaceClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentWorklist ContextualDependentClosure ContextualDependentUpdate
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Leaving the class at the first equation -/

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)

/-- **A store leaves `Stratified` when a normal reduct of its first opened left side leaves the fragment.** -/
theorem not_stratified_of_head {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    {code : Tm Head (Θ.arity + ContextualDependentPatternSolver.lamDepth equation.1.2.code)}
    (reduces : Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.1.2.code) code) (normal : Normal rules code)
    (outside : ¬ InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code) :
    ¬ Stratified levels (equation :: rest) := by
  intro stratified
  exact outside ((stratified [] rest equation rfl).1.1 code reduces normal)

/-! ## Arities at most the declared ones -/

/-- **η-short arities**: every flexible spine has at most the arity of its head. -/
def aritiesShort : {n : Nat} → (Fin n → Bool) → (Fin n → Nat) → Tm Head n → Bool
  | _, _, _, .var _ => true
  | _, _, _, .const _ => true
  | _, _, _, .head _ => true
  | _, flexible, arity, .pi A B =>
      aritiesShort flexible arity A && aritiesShort (liftFlexible flexible) (liftArity arity) B
  | _, flexible, arity, .sigma A B =>
      aritiesShort flexible arity A && aritiesShort (liftFlexible flexible) (liftArity arity) B
  | _, flexible, arity, .id A a b =>
      aritiesShort flexible arity A && aritiesShort flexible arity a && aritiesShort flexible arity b
  | _, flexible, arity, .lam body => aritiesShort (liftFlexible flexible) (liftArity arity) body
  | _, flexible, arity, .app f a =>
      if flexHead flexible (spineHead f) then decide (spineLength f + 1 ≤ headArity arity (spineHead f))
      else aritiesShort flexible arity f && aritiesShort flexible arity a
  | _, flexible, arity, .pair a b => aritiesShort flexible arity a && aritiesShort flexible arity b
  | _, flexible, arity, .fst p => aritiesShort flexible arity p
  | _, flexible, arity, .snd p => aritiesShort flexible arity p
  | _, flexible, arity, .refl a => aritiesShort flexible arity a

/-- **Exact arities are η-short arities.** -/
theorem arities_short : ∀ {n : Nat} (flexible : Fin n → Bool) (arity : Fin n → Nat) (t : Tm Head n),
    arities flexible arity t = true → aritiesShort flexible arity t = true
  | _, _, _, .var _, _ => rfl
  | _, _, _, .const _, _ => rfl
  | _, _, _, .head _, _ => rfl
  | _, flexible, arity, .pi A B, holds => by
      simp only [arities, Bool.and_eq_true] at holds
      simp only [aritiesShort, Bool.and_eq_true]
      exact ⟨arities_short _ _ A holds.1, arities_short _ _ B holds.2⟩
  | _, flexible, arity, .sigma A B, holds => by
      simp only [arities, Bool.and_eq_true] at holds
      simp only [aritiesShort, Bool.and_eq_true]
      exact ⟨arities_short _ _ A holds.1, arities_short _ _ B holds.2⟩
  | _, flexible, arity, .id A a b, holds => by
      simp only [arities, Bool.and_eq_true] at holds
      simp only [aritiesShort, Bool.and_eq_true]
      exact ⟨⟨arities_short _ _ A holds.1.1, arities_short _ _ a holds.1.2⟩, arities_short _ _ b holds.2⟩
  | _, flexible, arity, .lam body, holds => by
      simp only [arities] at holds
      simp only [aritiesShort]
      exact arities_short _ _ body holds
  | _, flexible, arity, .app f a, holds => by
      unfold arities at holds
      unfold aritiesShort
      by_cases flex : flexHead flexible (spineHead f) = true
      · rw [if_pos flex] at holds ⊢
        simp only [decide_eq_true_eq] at holds ⊢
        omega
      · rw [if_neg flex] at holds ⊢
        simp only [Bool.and_eq_true] at holds ⊢
        exact ⟨arities_short _ _ f holds.1, arities_short _ _ a holds.2⟩
  | _, flexible, arity, .pair a b, holds => by
      simp only [arities, Bool.and_eq_true] at holds
      simp only [aritiesShort, Bool.and_eq_true]
      exact ⟨arities_short _ _ a holds.1, arities_short _ _ b holds.2⟩
  | _, flexible, arity, .fst p, holds => by
      simp only [arities] at holds
      simp only [aritiesShort]
      exact arities_short _ _ p holds
  | _, flexible, arity, .snd p, holds => by
      simp only [arities] at holds
      simp only [aritiesShort]
      exact arities_short _ _ p holds
  | _, flexible, arity, .refl a, holds => by
      simp only [arities] at holds
      simp only [aritiesShort]
      exact arities_short _ _ a holds

/-- **An opened side with η-short metavariable occurrences**: Miller occurrences, and every metavariable applied to at
most its declared arity. -/
def InFragmentCodeShort {n : Nat} (context : Ctx Head n) (count : Nat) (code : Tm Head (n + count)) : Prop :=
  miller (openedFlexible count) code = true ∧
    aritiesShort (openedFlexible count) (metaArity context count) code = true

instance {n : Nat} (context : Ctx Head n) (count : Nat) (code : Tm Head (n + count)) :
    Decidable (InFragmentCodeShort context count code) := by
  unfold InFragmentCodeShort
  infer_instance

theorem short_of_inFragment {n : Nat} {context : Ctx Head n} {count : Nat} {code : Tm Head (n + count)}
    (inside : InFragmentCode context count code) : InFragmentCodeShort context count code :=
  ⟨inside.1, arities_short _ _ _ inside.2⟩

/-- **Fragment sides with η-short occurrences.** -/
def FragmentSidesShort {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Prop :=
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.1.2.code) code → Normal rules code →
    InFragmentCodeShort Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code) ∧
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      equation.2.2.code) code → Normal rules code →
    InFragmentCodeShort Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code)

/-- **The stratified fragment with η-short metavariable occurrences**: `Stratified`, with every metavariable applied to
at most the arity of its declaration. -/
def StratifiedShort {Θ : Context rules} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ∀ (before after : EquationStore (TotalTerm Θ)) (equation : Equation (TotalTerm Θ)),
    problem = before ++ equation :: after → FragmentSidesShort equation ∧ StratifiedAt levels before equation

variable {levels}

/-- **The corrected class contains `Stratified`.** -/
theorem stratifiedShort_of_stratified {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (stratified : Stratified levels problem) : StratifiedShort levels problem := by
  intro before after equation split
  obtain ⟨sides, annotations⟩ := stratified before after equation split
  exact ⟨⟨fun code reduces normal => short_of_inFragment (sides.1 code reduces normal),
    fun code reduces normal => short_of_inFragment (sides.2 code reduces normal)⟩, annotations⟩

/-- **The corrected class contains the dynamic pattern fragment.** -/
theorem stratifiedShort_of_fragment {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFragmentStore problem) : StratifiedShort levels problem :=
  stratifiedShort_of_stratified (stratified_of_fragment inside)

/-- A one-equation store with equal annotation codes and η-short sides is in the corrected class. -/
theorem stratifiedShort_single {Θ : Context rules} (equation : Equation (TotalTerm Θ))
    (annotations : equation.1.1.code = equation.2.1.code) (sides : FragmentSidesShort equation) :
    StratifiedShort levels [equation] := by
  intro before after other split
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨same, -⟩ := split
      subst same
      refine ⟨sides, fun σ _ => ?_⟩
      rw [annotations]
      exact (equation.2.1.reindex σ).isType.refl
  | cons first rest => simp at split

end General

/-! ## Executable readings in the tower -/

section Tower

open ContextualDependentPatternFiring.Controls

/-- A side's computed normal form, with η-short occurrences. -/
def sideShort {Θ : Context setting.R} (count : Nat) (code : Tower.Tm (Θ.arity + count)) : Bool :=
  match ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | some result => (step Tower.rules (fun _ => none) result.val).isNone &&
      decide (InFragmentCodeShort Θ.raw count result.val)
  | none => false

theorem sideShort_sound {Θ : Context setting.R} {count : Nat} {code : Tower.Tm (Θ.arity + count)}
    (check : sideShort count code = true) :
    ∀ other, Star (R := Tower.rules) code other → Normal Tower.rules other → InFragmentCodeShort Θ.raw count other := by
  unfold sideShort at check
  cases computed : ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | none =>
      rw [computed] at check
      cases check
  | some result =>
      rw [computed] at check
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at check
      intro other reduces normal
      have toResult := ContextualDependentExecutableConversion.normalize_star 64 computed
      have resultNormal := (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr check.1
      rw [normal_reduct_unique rfl toResult resultNormal reduces normal]
      exact check.2

/-- A side's computed normal form, outside the fragment. -/
def sideOutside {Θ : Context setting.R} (count : Nat) (code : Tower.Tm (Θ.arity + count)) : Bool :=
  match ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | some result => (step Tower.rules (fun _ => none) result.val).isNone &&
      !decide (InFragmentCode Θ.raw count result.val)
  | none => false

/-- The first equation's left side leaves the fragment. -/
def headOutside {Θ : Context setting.R} : EquationStore (TotalTerm Θ) → Bool
  | [] => false
  | equation :: _ => sideOutside (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
      (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code)

theorem not_stratified_of_headOutside {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (check : headOutside problem = true) : ¬ Stratified setting.levels problem := by
  cases problem with
  | nil => cases check
  | cons equation rest =>
      change sideOutside (Θ := Θ) (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) = true at check
      unfold sideOutside at check
      cases computed : ContextualDependentExecutableConversion.red (L := Nat) 64
          (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) with
      | none =>
          rw [computed] at check
          cases check
      | some result =>
          rw [computed] at check
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true', decide_eq_false_iff_not] at check
          exact not_stratified_of_head setting.levels
            (ContextualDependentExecutableConversion.normalize_star 64 computed)
            ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr check.1) check.2

/-- A one-equation store whose annotations agree and whose computed sides are η-short. -/
def singleShort {Θ : Context setting.R} : EquationStore (TotalTerm Θ) → Bool
  | [equation] => decide (equation.1.1.code = equation.2.1.code) &&
      sideShort (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) &&
      sideShort (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code)
  | _ => false

theorem stratifiedShort_of_singleShort {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (check : singleShort problem = true) : StratifiedShort setting.levels problem := by
  match problem, check with
  | [equation], check =>
      simp only [singleShort, Bool.and_eq_true, decide_eq_true_eq] at check
      exact stratifiedShort_single equation check.1.1 ⟨sideShort_sound check.1.2, sideShort_sound check.2⟩

end Tower

/-! ## The witness -/

section Witness

open ContextualDependentPatternFiring.Controls ContextualDependentIntersection.Controls

/-- `U0`, over `A`. -/
def universeA : TypeOver typeContext := formIn typeContext (.head (.sort Tower.zero)) (by decide +kernel)

/-- `A : U0, X : U0`. -/
abbrev withX := extend typeContext universeA

/-- `U0 → U0 → X`, over `A, X`. -/
def binaryX : TypeOver withX :=
  formIn withX (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.var 2))) (by decide +kernel)

/-- `A : U0, X : U0, G : U0 → U0 → X`. -/
abbrev withXG := extend withX binaryX

def universeXG : TypeOver withXG := formIn withXG (.head (.sort Tower.zero)) (by decide +kernel)

/-- `U0 → U0 → X`, over `A, X, G`. -/
def binaryXG : TypeOver withXG :=
  formIn withXG (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.var 3))) (by decide +kernel)

/-- `X ≐ Π A (Π A A)`. -/
def witnessFirst : Equation (TotalTerm withXG) :=
  (termIn withXG universeXG (.var 1) (by decide +kernel),
    termIn withXG universeXG (.pi (.var 2) (.pi (.var 3) (.var 4))) (by decide +kernel))

/-- `λ a b. G a b ≐ λ a b. G b a`. -/
def witnessSecond : Equation (TotalTerm withXG) :=
  (termIn withXG binaryXG (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withXG binaryXG (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))) (by decide +kernel))

/-- **The witness store.** -/
def witnessStore : EquationStore (TotalTerm withXG) := [witnessFirst, witnessSecond]

theorem witnessFirst_in_fragment : InFragment witnessFirst := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl witnessFirst.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem witnessSecond_in_fragment : InFragment witnessSecond := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl witnessSecond.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The witness is in the dynamic pattern fragment.** -/
theorem witness_in_fragment : InFragmentStore witnessStore := by
  intro equation member
  rcases List.mem_cons.mp member with same | later
  · rw [same]
    exact witnessFirst_in_fragment
  · rw [List.mem_singleton.mp later]
    exact witnessSecond_in_fragment

/-- The first round's residual: outside `Stratified`, inside the corrected class, and with more declarations plus total
arity than the store. -/
noncomputable def firstRoundCheck : Bool :=
  match run intersectOnly witnessStore 1 with
  | .cutoff state => headOutside state.remaining && singleShort state.remaining &&
      decide (withXG.arity + ContextualDependentMetaArityRank.totalArity withXG.raw <
        state.target.arity + ContextualDependentMetaArityRank.totalArity state.target.raw)
  | _ => false

theorem firstRoundCheck_true : firstRoundCheck = true := by decide +kernel

/-- **The first round leaves `Stratified`.** The intersection family's first round on the witness progresses (the run of one
round is cut off at an update), to a residual store that is not `Stratified`, that is in the corrected class, and whose
context has more declarations plus total metavariable arity than the witness's. -/
theorem witness_first_round :
    ∃ state : Update setting.levels witnessStore, run intersectOnly witnessStore 1 = .cutoff state ∧
      ¬ Stratified setting.levels state.remaining ∧ StratifiedShort setting.levels state.remaining ∧
      withXG.arity + ContextualDependentMetaArityRank.totalArity withXG.raw <
        state.target.arity + ContextualDependentMetaArityRank.totalArity state.target.raw := by
  have key := firstRoundCheck_true
  unfold firstRoundCheck at key
  generalize ran : run intersectOnly witnessStore 1 = outcome at key
  cases outcome with
  | cutoff state =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at key
      exact ⟨state, rfl, not_stratified_of_headOutside key.1.1, stratifiedShort_of_singleShort key.1.2, key.2⟩
  | solved _ _ => simp at key
  | refuted _ => simp at key
  | stuck _ => simp at key

/-- **The intersection family commits on the witness.** -/
theorem witness_committed : (run intersectOnly witnessStore 8).readout = .commit := by decide +kernel

end Witness

end ContextualDependentInPlaceClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
