import Mettapedia.GSLT.Coordination.ConsensusNumbers.StepSpace
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Where the step exceeds COMM: conditions on the whole space

Consensus numbers do not separate the step from rho's COMM: both are infinite (`StepSpace`,
`Rho`), and rho runs every deterministic object, the step-space with its absence checks included,
by keeping the object's history in one message. What rho cannot do is run a space **one part at
a time**: a COMM that can fire still fires when more processes are put beside it (the PAR rule of
the calculus), while an absence check does not.

## The observer

`WeakBarb step barb s`: some run from `s` reaches a configuration showing `barb`. Example: in the
step language, `{trigger}` can reach a space containing `done`.
An encoding is **complete** for weak barbs when every source configuration that can show the barb
is sent to a target configuration that can, and **sound** when the converse holds. These are the
weakest operational requirements an encoding can meet; nothing about the shape of runs is asked.

## The theorem

`no_parallel_encoding`: let the target's steps be closed under putting something beside them
(`t ⟶ t'` gives `t ∥ u ⟶ t' ∥ u`), and its barb survive that too. If a source configuration `P`
can show the barb while `P` beside `Q` cannot, then no encoding whose image of `P` beside `Q` is
`enc P ∥ u` for some `u` (for example `enc P ∥ enc Q`) is complete and sound.

The step language has such a pair (`absence_fires`, `absence_blocked`): the step
`take trigger, make done, provided no blocker` (`absenceExample`) fires at `{trigger}` and never
at `{trigger, blocker}`, where the blocker stays forever.

* **Positive rules over bags** (`positive_rules_cannot_encode_absence`): no encoding into steps
  without conditions on the whole space (take, keep and make: COMM over a bag) whose image of a
  union contains the image of each part is complete and sound for an upward-closed test.
* **The rho calculus** (`rho_cannot_encode_absence`): no encoding into the rho calculus that sends
  union to parallel composition is complete and sound for the output barb on a name (read through
  nested parallel compositions, `HasOutput`).
* One step at a time this is `Rule.step_unconditional_iff`: the absence step's label is honoured
  in some larger environment and not in all (`absence_step_conditional`).

## The hypotheses are needed

* **Compositionality**: an encoding that looks at the whole configuration at once is complete and
  sound into a target with no rules (`Controls.whole_configuration_encoding`). Rho's history
  simulation is of this kind: one message holds the whole space.
* **A condition on the whole space**: without it, the step language is encoded into itself
  compositionally, and its steps are closed under adding beside them (`positive_reduces_frame`).

## Peek and take-and-re-send

A rule set and the same rules with every keep turned into take-and-re-send have the same reduction
relation (`remake_reduces_iff`), so weak barbs and interleaving bisimilarity cannot separate them.
Independence does (`OccurrenceCommits.Basis.not_encodes_keep`): two peeks of one atom commute, two
take-and-re-sends of it do not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Avoids
  Reduces Label)

/-! ## The abstract theorem -/

/-- Some run from `s` reaches a configuration showing the barb. -/
def WeakBarb {S : Type*} (step : S → S → Prop) (barb : S → Prop) (s : S) : Prop :=
  ∃ s', Relation.ReflTransGen step s s' ∧ barb s'

theorem reflTransGen_par {T : Type*} {step : T → T → Prop} {par : T → T → T}
    (parClosed : ∀ t t' u, step t t' → step (par t u) (par t' u)) {t t' : T} (u : T)
    (run : Relation.ReflTransGen step t t') : Relation.ReflTransGen step (par t u) (par t' u) := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (parClosed _ _ u last)

/-- **No encoding sending composition to `∥` into a PAR-closed target expresses a step that a
neighbour can block.** -/
theorem no_parallel_encoding {Src Tgt : Type*} {srcStep : Src → Src → Prop} {srcBarb : Src → Prop}
    {tgtStep : Tgt → Tgt → Prop} {tgtPar : Tgt → Tgt → Tgt} {tgtBarb : Tgt → Prop}
    (parClosed : ∀ t t' u, tgtStep t t' → tgtStep (tgtPar t u) (tgtPar t' u))
    (barbClosed : ∀ t u, tgtBarb t → tgtBarb (tgtPar t u))
    {P PQ : Src} (fires : WeakBarb srcStep srcBarb P) (blocked : ¬ WeakBarb srcStep srcBarb PQ)
    (enc : Src → Tgt) (compositional : ∃ u, enc PQ = tgtPar (enc P) u)
    (complete : ∀ S, WeakBarb srcStep srcBarb S → WeakBarb tgtStep tgtBarb (enc S))
    (sound : ∀ S, WeakBarb tgtStep tgtBarb (enc S) → WeakBarb srcStep srcBarb S) : False := by
  obtain ⟨t, run, barb⟩ := complete P fires
  obtain ⟨u, hu⟩ := compositional
  apply blocked
  apply sound
  rw [hu]
  exact ⟨_, reflTransGen_par parClosed u run, barbClosed _ _ barb⟩

/-! ## The step language has an absence step a neighbour blocks -/

/-- Atoms of the source example. -/
inductive Src where
  | trigger | blocker | done
  deriving DecidableEq

/-- `take trigger, make done, provided no blocker`. -/
def absenceExample : Rule Src := ⟨{.trigger}, 0, {.done}, fun a => decide (a = .blocker)⟩

/-- The source: bags of atoms with the absence step. -/
def srcStep : Multiset Src → Multiset Src → Prop := Reduces (· = absenceExample)

/-- The source barb: `done` is present. -/
def hasDone (M : Multiset Src) : Prop := Src.done ∈ M

/-- **The absence step fires alone.** -/
theorem absence_fires : WeakBarb srcStep hasDone {.trigger} := by
  refine ⟨{.done}, .single ⟨absenceExample, rfl, ⟨?_, ?_⟩, ?_⟩, by simp [hasDone]⟩
  · simp [Rule.redex, absenceExample]
  · simp [Rule.redex, absenceExample]
  · simp [Rule.result, absenceExample]

/-- **Beside a blocker it never fires.** -/
theorem absence_blocked : ¬ WeakBarb srcStep hasDone ({.trigger} + {.blocker}) := by
  have stuck : ∀ M', ¬ srcStep ({.trigger} + {.blocker}) M' := by
    rintro M' ⟨ρ, rfl, ⟨-, avoids⟩, -⟩
    have := avoids .blocker (by simp [Rule.redex, absenceExample])
    simp [absenceExample] at this
  rintro ⟨M', run, barb⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨M'', step, -⟩
  · simp [hasDone] at barb
  · exact stuck _ step

/-- The absence step is not positive. -/
theorem absenceExample_not_positive : ¬ absenceExample.Positive := fun h => by
  have := h .blocker
  simp [absenceExample] at this

/-- **One step at a time** (`Rule.step_unconditional_iff`): the absence step at `{trigger}`
borrows nothing, and some environment beside it still disables it. -/
theorem absence_step_conditional :
    ¬ ∀ E : Multiset Src, absenceExample.Enabled ({.trigger} + 0 + E) := by
  have step : absenceExample.Step {.trigger} ⟨0, absenceExample.closed⟩ {.done} := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [Rule.redex, absenceExample]
    · simp [Rule.redex, absenceExample]
    · simp [Rule.result, absenceExample]
  rw [Rule.step_unconditional_iff step]
  exact absenceExample_not_positive

/-! ## Into positive rules over bags -/

/-- **Steps without conditions on the whole space are closed under adding beside them.** -/
theorem positive_reduces_frame {R : Type*} [DecidableEq R] {Γ : Rule R → Prop}
    (positive : ∀ ρ, Γ ρ → ρ.Positive) {M M' : Multiset R} (h : Reduces Γ M M') (E : Multiset R) :
    Reduces Γ (M + E) (M' + E) := by
  obtain ⟨ρ, member, enabled, rfl⟩ := h
  refine ⟨ρ, member, (Rule.enabled_iff_of_positive (positive ρ member) _).mpr
    (enabled.1.trans (Multiset.le_add_right _ _)), ?_⟩
  have le := Multiset.le_iff_count.mp ((Rule.take_le_redex ρ).trans enabled.1)
  ext x
  have := le x
  simp only [Rule.result, Multiset.count_add, Multiset.count_sub]
  omega

/-- **No encoding into positive rules over bags expresses absence**, when the image of a union
contains the image of each part and the test is upward closed. -/
theorem positive_rules_cannot_encode_absence {R : Type*} [DecidableEq R] {Γ : Rule R → Prop}
    (positive : ∀ ρ, Γ ρ → ρ.Positive) (test : Multiset R → Prop)
    (upward : ∀ M N, M ≤ N → test M → test N) (enc : Multiset Src → Multiset R)
    (contains : enc {.trigger} ≤ enc ({.trigger} + {.blocker}))
    (complete : ∀ S, WeakBarb srcStep hasDone S → WeakBarb (Reduces Γ) test (enc S))
    (sound : ∀ S, WeakBarb (Reduces Γ) test (enc S) → WeakBarb srcStep hasDone S) : False :=
  no_parallel_encoding (tgtPar := (· + ·))
    (fun _ _ u step => positive_reduces_frame positive step u)
    (fun t u barb => upward _ _ (Multiset.le_add_right t u) barb)
    absence_fires absence_blocked enc
    ⟨_, (add_tsub_cancel_of_le contains).symm⟩ complete sound

/-! ## Into the rho calculus -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-- Parallel composition of two rho processes. -/
def rhoPar (P Q : Pattern) : Pattern := .collection .hashBag [P, Q] none

/-- An output on `n` at the top level, through nested parallel compositions. -/
inductive HasOutput (n : Pattern) : Pattern → Prop
  | here {q : Pattern} : HasOutput n (.apply "POutput" [n, q])
  | inBag {ps : List Pattern} {g : Option String} {p : Pattern} :
      p ∈ ps → HasOutput n p → HasOutput n (.collection .hashBag ps g)

/-- **No encoding into the rho calculus that sends union to parallel composition expresses
absence**, for the output barb on any name. -/
theorem rho_cannot_encode_absence (n : Pattern) (enc : Multiset Src → Pattern)
    (compositional : enc ({.trigger} + {.blocker}) = rhoPar (enc {.trigger}) (enc {.blocker}))
    (complete : ∀ S, WeakBarb srcStep hasDone S →
      WeakBarb (fun P Q => Nonempty (P ⇝ Q)) (HasOutput n) (enc S))
    (sound : ∀ S, WeakBarb (fun P Q => Nonempty (P ⇝ Q)) (HasOutput n) (enc S) →
      WeakBarb srcStep hasDone S) : False :=
  no_parallel_encoding (tgtPar := rhoPar)
    (fun _ _ u ⟨step⟩ => ⟨Reduces.par (rest := [u]) step⟩)
    (fun t u barb => HasOutput.inBag (by simp) barb)
    absence_fires absence_blocked enc ⟨_, compositional⟩ complete sound

/-! ## Peek and take-and-re-send reduce alike -/

/-- **Turning every keep into take-and-re-send does not change the reductions.** -/
theorem remake_reduces_iff {R : Type} [DecidableEq R] (Γ : Rule R → Prop) (M M' : Multiset R) :
    Reduces (fun ρ => ∃ σ, Γ σ ∧ ρ = remake σ) M M' ↔ Reduces Γ M M' := by
  constructor
  · rintro ⟨ρ, ⟨σ, member, rfl⟩, enabled, rfl⟩
    have enabled := (remake_enabled_iff σ M).mp enabled
    exact ⟨σ, member, enabled, remake_result enabled⟩
  · rintro ⟨σ, member, enabled, rfl⟩
    exact ⟨remake σ, ⟨σ, member, rfl⟩, (remake_enabled_iff σ M).mpr enabled,
      (remake_result enabled).symm⟩

/-! ## Controls -/

namespace Controls

open Classical in
/-- An encoding that looks at the whole configuration: one `done` when the source can show
`done`, nothing otherwise. -/
noncomputable def wholeEncoding (M : Multiset Src) : Multiset Src :=
  if WeakBarb srcStep hasDone M then {.done} else 0

/-- **Without compositionality the conclusion fails**: the whole-configuration encoding, into a
target with no rules, is complete and sound, and does not send union to union. -/
theorem whole_configuration_encoding :
    (∀ S, WeakBarb srcStep hasDone S ↔ WeakBarb (Reduces fun _ => False) hasDone (wholeEncoding S)) ∧
      wholeEncoding ({.trigger} + {.blocker}) ≠ wholeEncoding {.trigger} + wholeEncoding {.blocker} := by
  have noStep : ∀ M M', ¬ Reduces (fun _ : Rule Src => False) M M' := fun _ _ ⟨_, f, _⟩ => f
  have only : ∀ M M', Relation.ReflTransGen (Reduces fun _ : Rule Src => False) M M' → M' = M := by
    intro M M' run
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, step, -⟩
    · rfl
    · exact absurd step (noStep _ _)
  refine ⟨fun S => ?_, ?_⟩
  · constructor
    · intro h
      exact ⟨_, .refl, by simp [wholeEncoding, h, hasDone]⟩
    · rintro ⟨t, run, barb⟩
      rw [only _ _ run] at barb
      by_contra h
      simp [wholeEncoding, h, hasDone] at barb
  · simp only [wholeEncoding, if_neg absence_blocked, if_pos absence_fires]
    intro h
    have := congrArg (Multiset.card) h
    simp at this

/-- **Positive control**: the output barb survives putting a process beside it. -/
theorem output_survives_par (n q u : Pattern) :
    HasOutput n (rhoPar (.apply "POutput" [n, q]) u) :=
  HasOutput.inBag (p := .apply "POutput" [n, q]) (by simp) .here

/-- **Negative control**: the inactive process shows no output. -/
theorem nil_no_output (n : Pattern) : ¬ HasOutput n (.collection .hashBag [] none) := by
  rintro (_ | ⟨mem, _⟩)
  simp at mem

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
