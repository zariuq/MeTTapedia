import Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire
import Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization.EveryStep

/-!
# The MM2 profile names an instance of the step

The GSLT support-transform profile of MM2 (`MM2ExecutionProfileWire.presentation`; opt's
`langdef/mm2/gslt_profile_v1.metta` is its rendering) names the parts of the step an exec fires:

* the work shell `(exec LOC INPUT OUTPUT)`: the kernel is the exec;
* the scheduler `least-mork-compact-expression-key-v1`: the least exec in MORK's order, a queue
  of parked rules;
* the transition laws:
  - `consume-selected`: the kernel takes the exec (`everyStep` publishes into `M.erase exec`);
  - `snapshot-includes-selected`: the rows read the snapshot with the exec in it (`readCopy_eq`);
  - `relational-product-may-reuse-support`: two sources may read one atom (`EveryRow` asks each
    source for an atom of its own; the step law's `Reads` counts a value read twice once);
  - `stage-all-matches-per-sink`: each sink stages every row (`stageOf`);
  - `finalize-sinks-left-to-right`: `Policy.leftToRight`;
* the sources `,` (and `I` with `BTM`, `==`, `!=`) and the sinks `+ - head tail count pure`.

Results:

* `profilePolicy_presentation`: the profile declares `Policy.leftToRight`.
* `profileStep_eq_morkFire`: **the step the profile declares is MORK's firing** whenever no
  removal meets an add written after it; `profileStep_ne_morkFire`: otherwise it is not, as
  `(O (- t) (+ t))` shows. MORK's kernel writes adds first (`morkFire_eq_everyStep`), so a profile
  naming the kernel exactly declares adds first.
* `profile_lacks_folds`: the profile names none of `fmin`, `fmax`, `sum`, `fsum`, `fprod`, which
  MM2 programs use (the Viterbi showcase's `fmin`).

The wire is rendered by Lean today (`MM2ExecutionProfileWire.render`, `writeWire`,
`OSLF/Tools/ExportMM2ExecutionProfile.lean`). Generation in CeTTa belongs in C or MeTTa; this file
only reads `presentation` and generates nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire

universe uV uT uP

/-- The publication policy a transition law names. -/
def lawPolicy : TransitionLaw → Option Policy
  | .finalizeSinksLeftToRight => some .leftToRight
  | _ => none

/-- The publication policy a profile declares: the first law naming one. -/
def profilePolicy (p : ExecutionPresentation) : Option Policy :=
  (p.transitions.filterMap lawPolicy).head?

theorem profilePolicy_presentation : profilePolicy presentation = some .leftToRight := rfl

/-- The profile's transition laws, as authored. -/
theorem presentation_transitions :
    presentation.transitions =
      [.consumeSelected, .snapshotIncludesSelected, .relationalProductMayReuseSupport,
        .stageAllMatchesPerSink, .finalizeSinksLeftToRight] := rfl

variable {V : Type uV} {T : Type uT} {P : Type uP} [DecidableEq T] (L : TermLayer V T P)

/-- **The step the profile declares is MORK's firing when no removal meets a later add.** -/
theorem profileStep_eq_morkFire {exec : T} {M : Finset T} (selected : exec ∈ M)
    {sources : List P} {sinks : List (MSink T P)} {enum : List (Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Subst V T)}
    {R : Finset (Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Subst V T)}
    (enumerates : ∀ σ, σ ∈ enum ↔ EveryRow L sources (readCopy exec M) σ)
    (rows : ∀ σ, σ ∈ R ↔ EveryRow L sources M σ) (noMeet : NoRemovalMeetsLaterAdd L R sinks) :
    everyStep L .leftToRight exec sinks R M = morkFire L exec sinks enum M := by
  rw [everyStep_leftToRight_eq_addsFirst L noMeet, morkFire_eq_everyStep selected enumerates rows]

/-- **Otherwise the profile's step is not MORK's firing**: for `(O (- t) (+ t))` with a row
instantiating `t` to `u`, the profile's step keeps `u` and MORK's firing removes it. -/
theorem profileStep_ne_morkFire {exec u : T} {M : Finset T} (selected : exec ∈ M)
    {sources : List P} {t : P} {enum : List (Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Subst V T)} {R : Finset (Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Subst V T)}
    (enumerates : ∀ σ, σ ∈ enum ↔ EveryRow L sources (readCopy exec M) σ)
    (rows : ∀ σ, σ ∈ R ↔ EveryRow L sources M σ) {σ : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Subst V T} (σR : σ ∈ R)
    (inst : L.inst σ t = some u) :
    u ∈ everyStep L .leftToRight exec [.remove t, .add t] R M ∧
      u ∉ morkFire L exec [.remove t, .add t] enum M := by
  rw [morkFire_eq_everyStep selected enumerates rows]
  have inStage : u ∈ (stageOf L R (.add t : MSink T P)).image Prod.fst :=
    Finset.mem_image.mpr ⟨(u, u), mem_stageOf.mpr ⟨σ, σR, by simp [MSink.contrib, inst]⟩, rfl⟩
  have same : (stageOf L R (.remove t : MSink T P)) = stageOf L R (.add t) := by
    simp only [stageOf, MSink.contrib]
  constructor
  · simp only [everyStep, publishSeq, MSink.publish]
    exact Finset.mem_union_right _ inStage
  · simp only [everyStep, List.filter, MSink.isAdd, Bool.not_true, Bool.not_false, publishSeq,
      MSink.publish]
    rw [same]
    simp [inStage]

/-- **The profile names none of the folds `fmin`, `fmax`, `sum`, `fsum`, `fprod`.** -/
theorem profile_lacks_folds :
    ∀ s ∈ ["fmin", "fmax", "sum", "fsum", "fprod"],
      s ∉ (presentation.output.coreSinks ++ presentation.output.extensionSinks).map
        OperatorDecl.interface := by
  decide

/-- The sinks the profile names. -/
theorem profile_sinks :
    (presentation.output.coreSinks ++ presentation.output.extensionSinks).map OperatorDecl.interface =
      ["+", "-", "head", "tail", "count", "pure"] := rfl

end Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization
