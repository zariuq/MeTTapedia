import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.OnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.Observability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy

/-!
# Numbers on the tree's program step, and soft numbers observed by counting

**The program step.** The runs of `OnTheStep.Reach` are the runs of the tree's first-order step
under a rule set (`ProgramAdequacy.program`, read through `StepSpan.Succ`): one firing of `Reach` is
one successor of that step (`fires_iff_succ`). So representation independence holds on the tree's
program step itself (`succ_restore`, `succ_restore_back`).

**Soft numbers are observed by counting**, through the tree's observability theorems
(`EqualityOnTheStep.Options.Observability`). Beside the knowledge of `OnTheStep` (soft: values are
compared), take the strict knowledge, which compares the evaluated terms with their storage
(`StrictIdentified`). The soft knowledge extends the strict one (`strict_le_soft`) and identifies the
stored integer `5` with the fraction `5`, which the strict one does not (`five_strictly_apart`). So
by `Observability.count_changes` the count of `5` among the one row `5.0` is `0` under the strict
knowledge and not `0` under the soft one (`soft_numbers_observed`), and by
`Observability.count_conservative_iff` the soft knowledge changes some count answer of the strict
one (`soft_not_conservative`). The choice between soft and strict numbers is visible to programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Observed

open Distinctions.NumberLens Tower OnTheStep
open EqualityOnTheStep.Options.Observability (CountUnder count_changes count_zero_of_apart
  count_conservative_iff)

/-! ## The program step -/

/-- **One firing of a program is one successor of the tree's program step.** -/
theorem fires_iff_succ {O : Type} [DecidableEq O] (G : Table) (label : O → NTerm Stored)
    (R : Set (RuleInstance (NTerm Stored))) (C D : Configuration (NTerm Stored) O) :
    (∃ rule ∈ R, Step (action G) label rule C D) ↔
      StepSpan.Succ (ProgramAdequacy.program (action G) label R) C D := by
  rw [ProgramAdequacy.program_succ_iff]
  constructor
  · rintro ⟨rule, member, sel, valid, rfl⟩
    exact ⟨rule, sel, member, valid, rfl⟩
  · rintro ⟨rule, sel, member, valid, rfl⟩
    exact ⟨rule, member, sel, valid, rfl⟩

/-- **Re-storing every numeral carries every successor of the tree's program step to a
successor.** -/
theorem succ_restore {O : Type} [DecidableEq O] {G : Table} (respects : TableRespects G)
    {ρ : Stored → Stored} (restoring : Restoring ρ) {label : O → NTerm Stored}
    {R : Set (RuleInstance (NTerm Stored))} {C D : Configuration (NTerm Stored) O}
    (succ : StepSpan.Succ (ProgramAdequacy.program (action G) label R) C D) :
    StepSpan.Succ (ProgramAdequacy.program (action G) (NTerm.map ρ ∘ label) (restoreProgram ρ R))
      (restoreConf ρ C) (restoreConf ρ D) := by
  obtain ⟨rule, member, step⟩ := (fires_iff_succ G label R C D).mpr succ
  exact (fires_iff_succ G _ _ _ _).mp
    ⟨rule.map (NTerm.map ρ), ⟨rule, member, rfl⟩, step_restore respects restoring step⟩

/-- **For an injective re-storing, every successor of the re-stored program step comes from a
successor.** -/
theorem succ_restore_back {O : Type} [DecidableEq O] {G : Table} (respects : TableRespects G)
    {ρ : Stored → Stored} (restoring : Restoring ρ) (injective : Function.Injective ρ)
    {label : O → NTerm Stored} {R : Set (RuleInstance (NTerm Stored))}
    {C D' : Configuration (NTerm Stored) O}
    (succ : StepSpan.Succ (ProgramAdequacy.program (action G) (NTerm.map ρ ∘ label)
      (restoreProgram ρ R)) (restoreConf ρ C) D') :
    ∃ D, StepSpan.Succ (ProgramAdequacy.program (action G) label R) C D ∧ D' = restoreConf ρ D := by
  obtain ⟨_, ⟨rule, member, rfl⟩, step⟩ := (fires_iff_succ G _ _ _ _).mpr succ
  obtain ⟨D, back, rfl⟩ := step_restore_back respects restoring injective step
  exact ⟨D, (fires_iff_succ G label R C D).mp ⟨rule, member, back⟩, rfl⟩

/-- **The witness run is a successor of the tree's program step.** -/
theorem incr_succ : StepSpan.Succ (ProgramAdequacy.program (action exactTable) incrLabel {incr})
    start finish :=
  (fires_iff_succ exactTable incrLabel {incr} start finish).mp ⟨incr, rfl, incr_fires⟩

/-! ## Soft numbers observed by counting -/

/-- **The strict knowledge**: every instance of the two terms evaluates to the same term, storage
included. -/
def StrictIdentified (G : Table) (s t : NTerm Stored) : Prop :=
  ∀ σ : ℕ → NTerm Stored, eval G (s.subst σ) = eval G (t.subst σ)

/-- **The soft knowledge extends the strict one.** -/
theorem strict_le_soft (G : Table) (s t : NTerm Stored) (strict : StrictIdentified G s t) :
    Identified G s t :=
  fun σ => congrArg (NTerm.map value) (strict σ)

/-- **The stored integer `5` and the fraction `5`: identified softly, apart strictly.** -/
theorem five_strictly_apart (G : Table) :
    Identified G (.num five) (.num fiveFrac) ∧ ¬ StrictIdentified G (.num five) (.num fiveFrac) := by
  refine ⟨(numerals_identified G five fiveFrac).mpr (value_five.trans value_fiveFrac.symm), ?_⟩
  intro strict
  have atIdentity := strict NTerm.var
  change NTerm.num five = NTerm.num fiveFrac at atIdentity
  simp [five, fiveFrac] at atIdentity

/-- **Soft numbers are observed**: the count of the stored integer `5` among the one row holding
the fraction `5` is `0` under the strict knowledge and not `0` under the soft one. -/
theorem soft_numbers_observed (G : Table) :
    CountUnder (StrictIdentified G) (.num five) ({0} : Finset ℕ) (fun _ => .num fiveFrac) 0 ∧
      ¬ CountUnder (Identified G) (.num five) ({0} : Finset ℕ) (fun _ => .num fiveFrac) 0 := by
  obtain ⟨soft, strict⟩ := five_strictly_apart G
  have before := count_zero_of_apart (E := StrictIdentified G) (0 : ℕ) strict
  exact ⟨before, count_changes (strict_le_soft G) (Finset.mem_singleton_self 0) soft strict before⟩

/-- **The soft knowledge is not a conservative extension of the strict one**: some count answer
changes. -/
theorem soft_not_conservative (G : Table) :
    ¬ ∀ (pattern : NTerm Stored) (present : Finset ℕ) (row : ℕ → NTerm Stored) (number : ℕ),
      CountUnder (StrictIdentified G) pattern present row number ↔
        CountUnder (Identified G) pattern present row number := by
  intro same
  have back := (count_conservative_iff (0 : ℕ) (strict_le_soft G)).mp same
  exact (five_strictly_apart G).2 (back _ _ (five_strictly_apart G).1)

#print axioms fires_iff_succ
#print axioms succ_restore
#print axioms succ_restore_back
#print axioms incr_succ
#print axioms strict_le_soft
#print axioms five_strictly_apart
#print axioms soft_numbers_observed
#print axioms soft_not_conservative

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Observed
