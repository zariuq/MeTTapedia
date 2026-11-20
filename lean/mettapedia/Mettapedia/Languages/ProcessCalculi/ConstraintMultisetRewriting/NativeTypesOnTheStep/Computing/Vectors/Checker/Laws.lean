import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Check
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.Laws

/-!
# The checker as a budgeted decision procedure

**The question** (`Admissible`): every row of the definition elaborates, and its firing is admitted by
conversion, the settler-independent admission of the converting step (`AdmitsByConversion`: each made
row typed in its frame at a type usable at the declared type at every solution of what the patterns
teach, and that information solvable).

**The procedure** (`procedure`) is the tree's `Decider.procedure` (`Budgets/Laws.lean`): at budget `k`,
the first answer of the checker at a budget up to `k`. Its laws hold by construction:

* law 1, yes and no are sound (`procedure_yes`, `procedure_no`);
* law 2, raising the budget only resolves (`procedure_resolves`), and a yes and a no never meet;
* law 3, not decided is exactly the record that no budget up to `k` answered (`procedure_undecided_iff`).

**Soundness of no needs elaboration to be stable in the budget** (`elaborate_mono`, `elaborate_unique`):
the frames, types and information certified at two budgets are the same, by the tree's fuel stability
of executable checking (`ContextualDependentCheckingBudget`) and of the package's reduction
(`normalizer_stable`).

A single answer of the checker fixes the procedure's verdict from its budget on
(`procedure_of_admitted`, `procedure_of_refused`): sound answers never disagree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ContextualDependentConversionBudget (Keeps keeps_bind keeps_refl)
open UnificationWithLevels.TreeFibre.Budgets (Procedure Decider)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)

/-! ## Elaboration is stable in the budget -/

/-- The package's reduction keeps what it returns. -/
theorem vecReducer_stable : ∀ {n : Nat} (fuel : Nat) (term : Tower.Tm n),
    Keeps (vecReducer level1 fuel term) (vecReducer level1 (fuel + 1) term) :=
  fun fuel term =>
    ContextualDependentConversionBudget.normalizer_stable (TowerVectorsModel.rules level1) (vecRoot level1) fuel term

theorem formed?_succ (fuel : Nat) {a : Nat} (Γ : Ctx Tower.Head a) :
    Keeps (formed? fuel Γ) (formed? (fuel + 1) Γ) := by
  unfold formed?
  exact keeps_bind (ContextualDependentCheckingBudget.formContext_succ vecS.R vecChoices (vecReducer level1)
    vecReducer_stable fuel Γ) (fun _ => keeps_refl _)

theorem level?_succ (fuel : Nat) (Γ : Context pkg) (T : Tower.Tm Γ.arity) :
    Keeps (level? fuel Γ T) (level? (fuel + 1) Γ T) := by
  unfold level?
  exact keeps_bind ((ContextualDependentCheckingBudget.synth_check_succ vecS.R vecChoices (vecReducer level1)
      vecReducer_stable).1 fuel Γ.raw T)
    (fun s => keeps_bind (ContextualDependentCheckingBudget.asUniverse_succ vecS.R (vecReducer level1)
      vecReducer_stable fuel s.1) (fun _ => keeps_refl _))

theorem typedNum?_succ (fuel : Nat) (Γ : Context pkg) (t : Tower.Tm Γ.arity) :
    Keeps (typedNum? fuel Γ t) (typedNum? (fuel + 1) Γ t) := by
  unfold typedNum?
  exact keeps_bind ((ContextualDependentCheckingBudget.synth_check_succ vecS.R vecChoices (vecReducer level1)
    vecReducer_stable).2 fuel Γ.raw t TowerVectorsModel.numC) (fun _ => keeps_refl _)

/-- **More budget keeps an elaboration.** -/
theorem elaborate_succ (fuel : Nat) (d : Definition) (r : Row) :
    Keeps (elaborate fuel d r) (elaborate (fuel + 1) d r) := by
  intro e found
  unfold elaborate at found ⊢
  obtain ⟨acc, raw, rest⟩ := Option.bind_eq_some_iff.mp found
  rw [raw, Option.bind_some]
  split at rest
  · rename_i pos
    rw [dif_pos pos]
    obtain ⟨formed, hf, rest⟩ := Option.bind_eq_some_iff.mp rest
    rw [formed?_succ fuel acc.frame formed hf, Option.bind_some]
    split at rest
    · obtain ⟨l, hl, rest⟩ := Option.bind_eq_some_iff.mp rest
      rw [level?_succ fuel _ _ l hl, Option.bind_some]
      exact rest
    · rename_i v _
      obtain ⟨tv, ht, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨l, hl, rest⟩ := Option.bind_eq_some_iff.mp rest
      rw [typedNum?_succ fuel (prefixOf acc formed.down) v tv ht, Option.bind_some, level?_succ fuel _ _ l hl,
        Option.bind_some]
      exact rest
  · cases rest

theorem elaborate_mono {fuel larger : Nat} {d : Definition} {r : Row} {e : Elaborated d.arity}
    (found : elaborate fuel d r = some e) (enough : fuel ≤ larger) : elaborate larger d r = some e := by
  induction enough with
  | refl => exact found
  | step _ ih => exact elaborate_succ _ d r e ih

/-- **Two budgets elaborate a row alike.** -/
theorem elaborate_unique {j k : Nat} {d : Definition} {r : Row} {e e' : Elaborated d.arity}
    (first : elaborate j d r = some e) (second : elaborate k d r = some e') : e = e' := by
  have atFirst := elaborate_mono first (le_max_left j k)
  have atSecond := elaborate_mono second (le_max_right j k)
  rw [atFirst] at atSecond
  exact Option.some.inj atSecond

/-! ## Rows: yes and no against admission by conversion -/

/-- `vecAdmits?` says no only on unsolvable information. -/
theorem vecAdmits?_unsolvable {families : List (Family vecS.levels)} {fuel : Nat} {s : Interface.DependentFull.State vecS.R Nat}
    {f : Interface.DependentFull.Firing vecS.levels s}
    {frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B}
    (decided : vecAdmits? families fuel f frameType = some false) :
    ¬ (frames vecS.levels).Solvable f.information := by
  unfold vecAdmits? at decided
  by_cases empty : (f.guards.isEmpty && f.queries.isEmpty) = true
  · rw [if_pos empty] at decided
    cases first : firstDecisionAt vecS.levels f.information families with
    | settled M σ initial =>
        rw [first] at decided
        simp only [vecAdmitsAt?] at decided
        split at decided <;> cases decided
    | refuted none => exact none
    | undecided =>
        rw [first] at decided
        cases decided
  · rw [if_neg empty] at decided
    cases decided

/-- **An admitted row is admitted by conversion.** -/
theorem checkRow_admitsByConversion {fuel n : Nat} {e : Elaborated n} (verdict : checkRow fuel e = .admitted) :
    AdmitsByConversion vecS.levels e.firing :=
  converting_admitsByConversion vecS.levels _ (checkRow_admitted verdict)

/-- **A refused row is not admitted by conversion.** -/
theorem checkRow_not_admitsByConversion {fuel n : Nat} {e : Elaborated n} (verdict : checkRow fuel e = .refused) :
    ¬ AdmitsByConversion vecS.levels e.firing := by
  intro admitted
  have typed : TypedAfterMatch vecS.levels e.tells e.made :=
    admitted.admitsAfterMatch.1.2.2.2.2 (0, e.made) (List.mem_singleton_self _)
  have fromRefutation : (refuteRow? fuel e).isSome = true → False := fun found => by
    obtain ⟨r, _⟩ := Option.isSome_iff_exists.mp found
    exact r.down typed
  unfold checkRow at verdict
  split at verdict
  · split at verdict
    · cases verdict
    · rename_i decided
      exact vecAdmits?_unsolvable decided admitted.2.2.1
    · split at verdict
      · rename_i found
        exact fromRefutation found
      · cases verdict
  · split at verdict
    · rename_i found
      exact fromRefutation found
    · cases verdict

/-! ## The question and the procedure -/

/-- **What a yes asserts and a no denies**: every row elaborates within some budget, and its firing is
admitted by conversion. -/
def Admissible (d : Definition) : Prop :=
  ∀ r ∈ d.rows, ∃ fuel e, elaborate fuel d r = some e ∧ AdmitsByConversion vecS.levels e.firing

theorem admissible_of_admitted {fuel : Nat} {d : Definition} (verdict : checkDefinition fuel d = .admitted) :
    Admissible d := by
  intro r member
  have rowAdmitted := combine_admitted verdict (rowVerdict fuel d r) (List.mem_map_of_mem member)
  unfold rowVerdict at rowAdmitted
  split at rowAdmitted
  · cases rowAdmitted
  · rename_i e elaborated
    exact ⟨fuel, e, elaborated, checkRow_admitsByConversion rowAdmitted⟩

/-- The refused row, elaborated, with its row verdict. -/
theorem refused_row {fuel : Nat} {d : Definition} {i : Nat} (verdict : checkDefinition fuel d = .refused i) :
    ∃ r ∈ d.rows, ∃ e, elaborate fuel d r = some e ∧ checkRow fuel e = .refused := by
  obtain ⟨-, at'⟩ := combine_refused verdict
  simp only [Nat.sub_zero, List.getElem?_map] at at'
  cases row : d.rows[i]? with
  | none => rw [row] at at'; cases at'
  | some r =>
      rw [row] at at'
      simp only [Option.map_some, Option.some.injEq] at at'
      refine ⟨r, List.mem_of_getElem? row, ?_⟩
      unfold rowVerdict at at'
      split at at'
      · cases at'
      · rename_i e elaborated
        exact ⟨e, elaborated, at'⟩

theorem not_admissible_of_refused {fuel : Nat} {d : Definition} {i : Nat}
    (verdict : checkDefinition fuel d = .refused i) : ¬ Admissible d := by
  intro admissible
  obtain ⟨r, member, e, elaborated, refused⟩ := refused_row verdict
  obtain ⟨_, e', elaborated', admits⟩ := admissible r member
  obtain rfl := elaborate_unique elaborated' elaborated
  exact checkRow_not_admitsByConversion refused admits

/-- **The checker as a budget-indexed decider**: its answers carry their soundness. -/
def decider : Decider Admissible where
  Answer d := {b : Bool // (b = true → Admissible d) ∧ (b = false → ¬ Admissible d)}
  attempt fuel d :=
    match verdict : checkDefinition fuel d with
    | .admitted => some ⟨true, fun _ => admissible_of_admitted verdict, (fun no => by cases no)⟩
    | .refused _ => some ⟨false, (fun yes => by cases yes), fun _ => not_admissible_of_refused verdict⟩
    | .undecided => none
  sign a := a.1
  yes a signed := a.2.1 signed
  no a signed := a.2.2 signed

/-- **The checker as a budgeted decision procedure**: the first answer up to the budget. -/
def procedure : Procedure Admissible := decider.procedure

/-- **Law 1, yes is sound.** -/
theorem procedure_yes {k : Nat} {d : Definition} (verdict : procedure.verdict k d = .equal) : Admissible d :=
  procedure.equal_sound verdict

/-- **Law 1, no is sound.** -/
theorem procedure_no {k : Nat} {d : Definition} (verdict : procedure.verdict k d = .different) :
    ¬ Admissible d :=
  procedure.different_sound verdict

/-- **Law 2, raising the budget only resolves.** -/
theorem procedure_resolves {k k' : Nat} {d : Definition} (le : k ≤ k')
    (decided : procedure.verdict k d ≠ .undecided) : procedure.verdict k' d = procedure.verdict k d :=
  procedure.resolves le decided

/-- **Law 3, not decided is exactly that no budget up to `k` answered.** -/
theorem procedure_undecided_iff {k : Nat} {d : Definition} :
    procedure.verdict k d = .undecided ↔ ∀ j, j ≤ k → decider.attempt j d = none :=
  procedure.undecided_iff

/-- **One yes of the checker fixes the procedure's verdict from its budget on.** -/
theorem procedure_of_admitted {k : Nat} {d : Definition} (verdict : checkDefinition k d = .admitted) :
    ∀ k', k ≤ k' → procedure.verdict k' d = .equal := by
  intro k' le
  have notUndecided : procedure.verdict k d ≠ .undecided := by
    intro undecided
    have none' := (procedure_undecided_iff.mp undecided) k le_rfl
    simp only [decider] at none'
    split at none' <;> simp_all
  rw [procedure_resolves le notUndecided]
  cases h : procedure.verdict k d with
  | equal => rfl
  | different => exact absurd (admissible_of_admitted verdict) (procedure_no h)
  | undecided => exact absurd h notUndecided

/-- **One no of the checker fixes the procedure's verdict from its budget on.** -/
theorem procedure_of_refused {k i : Nat} {d : Definition} (verdict : checkDefinition k d = .refused i) :
    ∀ k', k ≤ k' → procedure.verdict k' d = .different := by
  intro k' le
  have notUndecided : procedure.verdict k d ≠ .undecided := by
    intro undecided
    have none' := (procedure_undecided_iff.mp undecided) k le_rfl
    simp only [decider] at none'
    split at none' <;> simp_all
  rw [procedure_resolves le notUndecided]
  cases h : procedure.verdict k d with
  | equal => exact absurd (procedure_yes h) (not_admissible_of_refused verdict)
  | different => rfl
  | undecided => exact absurd h notUndecided

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.vecReducer_stable
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.elaborate_succ
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.elaborate_mono
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.elaborate_unique
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.vecAdmits?_unsolvable
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkRow_admitsByConversion
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.checkRow_not_admitsByConversion
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.admissible_of_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.refused_row
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.not_admissible_of_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.decider
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.procedure
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.procedure_yes
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.procedure_no
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.procedure_resolves
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.procedure_undecided_iff
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.procedure_of_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.procedure_of_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
