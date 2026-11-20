import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Decision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Systems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Criteria

/-!
# Barbs on the step of the program, runs through the representation, and divergence

The step is `ByInstantiation.theStep`, the step defined by rule syntax with the four-rule program at
the contextual frames of the twin-binder signature. Its reduction is `Moves` and its runs `Runs`.

## Barbs

* **The output barb on a channel** (`OutBarb c`): the tree's may-barb (`RuleSyntax.Equivalence.MayBarb`,
  the barb observers see) of the pattern `c!(Q)`, with `Q` the pattern's own unknown
  (`outPattern`). At a represented state it holds exactly when some row's value is an output on a
  channel name-equivalent to `c` (`outBarb_iff`).
* The source's barb is the earlier placement's `Barb` (an output prime on a canonical channel in the
  canonical bag, the calculus's OUT-BARB read on canonical forms). An output barb of a represented
  state is a barb of the process (`barb_of_outBarb`); at a state whose rows are all primes the
  converse holds (`outBarb_of_barb`); in general it holds after housekeeping
  (`barb_eventually`).

## Runs through the representation

* `reaches_sound`: every run of a state that represents `P` ends at a state that represents a
  reduct of `P`.
* `reaches_complete`: every run of `P` is matched by a run of every state that represents `P`.
* `weak_barbs_agree`: reachable barbs agree.

## Weak barbed bisimilarity

`WeakBarbedBisimulation` (reductions answered by runs, output barbs on closed channels answered by
runs that show them) and `WeaklyBarbedBisimilar`. Two states that represent the same process are
weakly barbed bisimilar (`weaklyBarbedBisimilar_of_represents`), and weakly barbed bisimilar
states have the same reachable output barbs (`weaklyBarbedBisimilar_succeeds`). Existence: the
relation is inhabited at every represented state (`weaklyBarbedBisimilar_refl_of_represents`).

## Divergence

From a represented state, an infinite run of the step gives an infinite run of the source
(`divergence_reflected`): housekeeping runs are bounded by the spine weight, so an infinite run has
infinitely many communications, each a source reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding GroundSolves read inputT outputT zeroT
  bagT pnilT pconsT dropqT quoteT spine knowledge groundFrame someGrounding)
open Interface.Frames (Frame)

/-! ## The step's reduction -/

/-- **A reduction of the step of the program.** -/
abbrev Moves (s s' : ByInstantiation.State) : Prop :=
  LogicOverTheStep.StepSpan.Succ ByInstantiation.theStep.toStep s s'

/-- **Runs of the step.** -/
abbrev Runs : ByInstantiation.State → ByInstantiation.State → Prop := Relation.ReflTransGen Moves

theorem administers_moves {s s' : ByInstantiation.State} (fires : ByInstantiation.Administers s s') :
    Moves s s' :=
  (ByInstantiation.succ_iff s s').mpr (.inr fires)

theorem communicates_moves {s s' : ByInstantiation.State}
    (fires : ByInstantiation.Communicates s s') : Moves s s' :=
  (ByInstantiation.succ_iff s s').mpr (.inl fires)

theorem runs_of_administrative {s s' : ByInstantiation.State}
    (run : Relation.ReflTransGen ByInstantiation.Administers s s') : Runs s s' :=
  Relation.ReflTransGen.mono (fun _ _ fires => administers_moves fires) s s' run

/-! ## Ground terms in every declaration family -/

/-- A ground term, read in any declaration family. -/
def embed {W : Type} {D : W → MetaArity sig} {Γ : Ctx sig} {s : ByInstantiation.Srt} (t : G Γ s) :
    Term (signature sig D) Γ s :=
  instantiate (fun e => nomatch e : Assignment ByInstantiation.noUnknowns D) t

theorem instantiate_embed {W W' : Type} {D : W → MetaArity sig} {D' : W' → MetaArity sig}
    (h : Assignment D D') {Γ : Ctx sig} {s : ByInstantiation.Srt} (t : G Γ s) :
    instantiate h (embed (D := D) t) = embed t := by
  unfold embed
  rw [instantiate_comp]
  congr 1
  funext e
  exact nomatch e

theorem embed_ground {Γ : Ctx sig} {s : ByInstantiation.Srt} (t : G Γ s) :
    embed (D := ByInstantiation.noUnknowns) t = t :=
  ByInstantiation.instantiate_ground _ t

theorem instantiate_outputT {W W' : Type} {D : W → MetaArity sig} {D' : W' → MetaArity sig}
    (h : Assignment D D') {Γ : Ctx sig} (c : Term (signature sig D) Γ .nm)
    (p : Term (signature sig D) Γ .pr) :
    instantiate h (outputT c p) = outputT (instantiate h c) (instantiate h p) := rfl

/-! ## The output barb -/

/-- The frame of the payload of an output barb: one process unknown. -/
abbrev payloadFrame : Frame sig := ⟨Unit, fun _ => ([], .pr)⟩

/-- The payload unknown. -/
abbrev payloadUnknown : Term (signature sig payloadFrame.arity) [] .pr := generator payloadFrame.arity ()

/-- **The output pattern on a channel**, `c!(Q)` with `Q` its own unknown. -/
def outPattern (c : G [] .nm) : RuleSyntax.Equivalence.Pattern (RuleSyntax.Contextual.Terms sig) :=
  ⟨payloadFrame, ⟨[], .pr, outputT (embed c) payloadUnknown⟩⟩

/-- **The output barb of the step**: the tree's may-barb of the output pattern on `c`. -/
def OutBarb (c : G [] .nm) (s : ByInstantiation.State) : Prop :=
  RuleSyntax.Equivalence.MayBarb knowledge (outPattern c) s

/-- **At a represented state, the output barb on `c` is a row whose value is an output on a channel
name-equivalent to `c`.** -/
theorem outBarb_iff {s : ByInstantiation.State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : ByInstantiation.RepresentsBy s P value) (c : G [] .nm) :
    OutBarb c s ↔ ∃ o ∈ s.present, ∃ (c' : G [] .nm) (q : G [] .pr),
      value o = outputT c' q ∧ Similar c' c := by
  constructor
  · rintro ⟨o, present, b, σ, h, solved, equal⟩
    change Assignment payloadFrame.arity b.arity at h
    have known : GroundSolves (Assignment.compose (someGrounding b) σ) s.knowledge :=
      ByInstantiation.groundSolves_of_models solved (someGrounding b)
    obtain ⟨u, at', similar⟩ := represented.determined _ known o present
    have related : ObsSimilar
        (instantiateObservation (someGrounding b) (instantiateObservation σ (s.label o)))
        (instantiateObservation (someGrounding b)
          (instantiateObservation h ⟨[], .pr, outputT (embed c) payloadUnknown⟩)) :=
      equal (someGrounding b)
    rw [instantiateObservation_comp, instantiateObservation_comp, at'] at related
    have inner : Similar u (instantiate (Assignment.compose (someGrounding b) h)
        (outputT (embed c) payloadUnknown)) :=
      ByInstantiation.obsSimilar_closed.mp related
    rw [instantiate_outputT, instantiate_embed, embed_ground, instantiate_generator] at inner
    obtain ⟨c', q', shape, channel, _⟩ :=
      ByInstantiation.similar_output_inv (ByInstantiation.similar_trans
        (ByInstantiation.similar_symm inner) similar)
    exact ⟨o, present, c', q', shape, ByInstantiation.similar_symm channel⟩
  · rintro ⟨o, present, c', q, shape, channel⟩
    obtain ⟨g₀, known⟩ := represented.solvable
    obtain ⟨u, at', similar⟩ := represented.determined g₀ known o present
    refine ⟨o, present, groundFrame, g₀, fun _ => q, ByInstantiation.models_of_groundSolves known, ?_⟩
    intro g
    show ObsSimilar (instantiateObservation g (instantiateObservation g₀ (s.label o)))
      (instantiateObservation g (instantiateObservation (fun _ => q : Assignment payloadFrame.arity
        ByInstantiation.noUnknowns) ⟨[], .pr, outputT (embed c) payloadUnknown⟩))
    rw [at', ByInstantiation.instantiateObservation_ground, ByInstantiation.instantiateObservation_ground]
    refine .mk ?_
    show Similar u (instantiate (fun _ => q : Assignment payloadFrame.arity
      ByInstantiation.noUnknowns) (outputT (embed c) payloadUnknown))
    rw [instantiate_outputT, instantiate_embed, embed_ground, instantiate_generator]
    rw [shape] at similar
    exact ByInstantiation.similar_trans similar (.output channel (ByInstantiation.similar_refl q))

/-- The channel of a closed output value is closed. -/
theorem closed_channel {c : G [] .nm} {q : G [] .pr} (closed : Closed (outputT c q)) : Closed c := by
  have unfolded : binderSafeAt "NQuote" 0 (.apply "POutput" [read c, read q]) = true := closed
  simp only [binderSafeAt, binderSafeListAt, Bool.and_eq_true] at unfolded
  exact unfolded.1

/-- **An output barb of a represented state is a barb of the process.** -/
theorem barb_of_outBarb {s : ByInstantiation.State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : ByInstantiation.RepresentsBy s P value) {c : G [] .nm} (barb : OutBarb c s) :
    Barb P (canonicalize (read c)) := by
  obtain ⟨o, present, c', q, shape, channel⟩ := (outBarb_iff represented c).mp barb
  have meaning : canonicalize (read (value o)) =
      output (canonicalize (read c)) (canonicalize (read q)) := by
    rw [shape, ByInstantiation.canonical_outputT, ByInstantiation.similar_canonical channel]
  have prime := ByInstantiation.prime_output (represented.closed o present) meaning
  refine ⟨canonicalize (read q), ?_⟩
  rw [← represented.inventory_eq]
  unfold ByInstantiation.inventoryOf
  refine Multiset.mem_sum.mpr ⟨o, present, ?_⟩
  rw [ByInstantiation.primes_of_canonical_prime meaning prime]
  exact Multiset.mem_singleton_self _

/-- **At a state of primes, a barb of the process is an output barb.** -/
theorem outBarb_of_barb {s : ByInstantiation.State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : ByInstantiation.RepresentsBy s P value)
    (heated : ∀ o ∈ s.present, spine (value o) = 0) {c : G [] .nm} (closed : Closed c)
    (barb : Barb P (canonicalize (read c))) : OutBarb c s := by
  obtain ⟨payload, member⟩ := barb
  have rows : (fromProcess P).1 = s.present.val.map fun o => canonicalize (read (value o)) := by
    rw [← represented.inventory_eq, ByInstantiation.inventory_heated represented.closed heated]
  rw [rows] at member
  obtain ⟨o, present, at'⟩ := Multiset.mem_map.mp member
  obtain ⟨c', q, shape, channel, _⟩ := ByInstantiation.output_value (heated o present) at'
  have closed' : Closed c' := by
    have value_closed := represented.closed o present
    rw [shape] at value_closed
    exact closed_channel value_closed
  refine (outBarb_iff represented c).mpr ⟨o, present, c', q, shape, .name closed' closed ?_⟩
  exact StructuralCongruence.trans _ _ _ (Canonical.canonicalize_sound _)
    (channel ▸ StructuralCongruence.symm _ _ (Canonical.canonicalize_sound _))

/-- **A barb of a represented process is shown after housekeeping.** -/
theorem barb_eventually {s : ByInstantiation.State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : ByInstantiation.RepresentsBy s P value) {c : G [] .nm} (closed : Closed c)
    (barb : Barb P (canonicalize (read c))) : ∃ s', Runs s s' ∧ OutBarb c s' := by
  obtain ⟨s', value', run, represented', heated⟩ := ByInstantiation.heats_to_primes represented
  exact ⟨s', runs_of_administrative run, outBarb_of_barb represented' heated closed barb⟩

/-! ## Runs through the representation -/

/-- **Every run of a represented state ends at a state that represents a reduct.** -/
theorem reaches_sound {s t : ByInstantiation.State} {P : RhoProcess}
    (represented : ByInstantiation.Represents s P) (run : Runs s t) :
    ∃ P', Relation.ReflTransGen rhoLanguageDefGSLT.Step P P' ∧ ByInstantiation.Represents t P' := by
  induction run with
  | refl => exact ⟨P, .refl, represented⟩
  | tail _ last ih =>
      obtain ⟨P₁, run₁, represented₁⟩ := ih
      rcases (ByInstantiation.succ_iff _ _).mp last with comm | admin
      · obtain ⟨P₂, step, represented₂⟩ :=
          ByInstantiation.reflective_calculus_by_instantiation.2.2.2.1 represented₁ comm
        exact ⟨P₂, run₁.tail step, represented₂⟩
      · exact ⟨P₁, run₁, ByInstantiation.reflective_calculus_by_instantiation.2.2.1 represented₁ admin⟩

/-- **Every run of the source is matched by a run of every state that represents it.** -/
theorem reaches_complete {s : ByInstantiation.State} {P P' : RhoProcess}
    (represented : ByInstantiation.Represents s P)
    (run : Relation.ReflTransGen rhoLanguageDefGSLT.Step P P') :
    ∃ t, Runs s t ∧ ByInstantiation.Represents t P' := by
  induction run with
  | refl => exact ⟨s, .refl, represented⟩
  | tail _ step ih =>
      obtain ⟨t₁, run₁, represented₁⟩ := ih
      obtain ⟨s₁, s₂, admin, comm, represented₂⟩ :=
        ByInstantiation.reflective_calculus_by_instantiation.2.2.2.2.1 represented₁ step
      exact ⟨s₂, run₁.trans ((runs_of_administrative admin).tail (communicates_moves comm)),
        represented₂⟩

/-- Reachable barbs of the source. -/
def SourceSucceeds (channel : Pattern) (P : RhoProcess) : Prop :=
  ∃ P', Relation.ReflTransGen rhoLanguageDefGSLT.Step P P' ∧ Barb P' channel

/-- **Reachable barbs agree** between a represented state and the process it represents. -/
theorem weak_barbs_agree {s : ByInstantiation.State} {P : RhoProcess}
    (represented : ByInstantiation.Represents s P) {c : G [] .nm} (closed : Closed c) :
    SourceSucceeds (canonicalize (read c)) P ↔ ∃ s', Runs s s' ∧ OutBarb c s' := by
  constructor
  · rintro ⟨P', run, barb⟩
    obtain ⟨t, run₁, value, represented'⟩ := reaches_complete represented run
    obtain ⟨t', run₂, shows⟩ := barb_eventually represented' closed barb
    exact ⟨t', run₁.trans run₂, shows⟩
  · rintro ⟨s', run, shows⟩
    obtain ⟨P', run', value, represented'⟩ := reaches_sound represented run
    exact ⟨P', run', barb_of_outBarb represented' shows⟩

/-! ## Weak barbed bisimilarity -/

/-- **A weak barbed bisimulation of the step**: symmetric; a reduction is answered by a run into the
relation; an output barb on a closed channel is answered by a run that shows it. -/
structure WeakBarbedBisimulation (R : ByInstantiation.State → ByInstantiation.State → Prop) :
    Prop where
  symm : ∀ {s t}, R s t → R t s
  moves : ∀ {s t s'}, R s t → Moves s s' → ∃ t', Runs t t' ∧ R s' t'
  barbs : ∀ {s t} (c : G [] .nm), Closed c → R s t → OutBarb c s → ∃ t', Runs t t' ∧ OutBarb c t'

/-- **Weak barbed bisimilarity** of the step. -/
def WeaklyBarbedBisimilar (s t : ByInstantiation.State) : Prop :=
  ∃ R, WeakBarbedBisimulation R ∧ R s t

/-- Two states that represent the same process. -/
def CoRepresent (s t : ByInstantiation.State) : Prop :=
  ∃ P, ByInstantiation.Represents s P ∧ ByInstantiation.Represents t P

/-- **Representing the same process is a weak barbed bisimulation.** -/
theorem coRepresent_bisimulation : WeakBarbedBisimulation CoRepresent where
  symm := fun ⟨P, one, two⟩ => ⟨P, two, one⟩
  moves := by
    rintro s t s' ⟨P, onS, onT⟩ moved
    rcases (ByInstantiation.succ_iff s s').mp moved with comm | admin
    · obtain ⟨P', step, onS'⟩ := ByInstantiation.reflective_calculus_by_instantiation.2.2.2.1 onS comm
      obtain ⟨t', run, onT'⟩ := reaches_complete onT (.single step)
      exact ⟨t', run, P', onS', onT'⟩
    · exact ⟨t, .refl, P, ByInstantiation.reflective_calculus_by_instantiation.2.2.1 onS admin, onT⟩
  barbs := by
    rintro s t c closed ⟨P, ⟨value, onS⟩, ⟨value', onT⟩⟩ barb
    exact barb_eventually onT closed (barb_of_outBarb onS barb)

/-- **States that represent the same process are weakly barbed bisimilar.** -/
theorem weaklyBarbedBisimilar_of_represents {s t : ByInstantiation.State} {P : RhoProcess}
    (onS : ByInstantiation.Represents s P) (onT : ByInstantiation.Represents t P) :
    WeaklyBarbedBisimilar s t :=
  ⟨CoRepresent, coRepresent_bisimulation, P, onS, onT⟩

/-- Existence: every represented state is weakly barbed bisimilar to itself through the relation. -/
theorem weaklyBarbedBisimilar_refl_of_represents {s : ByInstantiation.State} {P : RhoProcess}
    (onS : ByInstantiation.Represents s P) : WeaklyBarbedBisimilar s s :=
  weaklyBarbedBisimilar_of_represents onS onS

/-- A weak barbed bisimulation answers runs by runs. -/
theorem WeakBarbedBisimulation.runs {R : ByInstantiation.State → ByInstantiation.State → Prop}
    (bisimulation : WeakBarbedBisimulation R) {s t s' : ByInstantiation.State} (related : R s t)
    (run : Runs s s') : ∃ t', Runs t t' ∧ R s' t' := by
  induction run with
  | refl => exact ⟨t, .refl, related⟩
  | tail _ last ih =>
      obtain ⟨t₁, run₁, related₁⟩ := ih
      obtain ⟨t', run', related'⟩ := bisimulation.moves related₁ last
      exact ⟨t', run₁.trans run', related'⟩

/-- **Weakly barbed bisimilar states have the same reachable output barbs.** -/
theorem weaklyBarbedBisimilar_succeeds {s t : ByInstantiation.State}
    (bisimilar : WeaklyBarbedBisimilar s t) {c : G [] .nm} (closed : Closed c)
    (succeeds : ∃ s', Runs s s' ∧ OutBarb c s') : ∃ t', Runs t t' ∧ OutBarb c t' := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  obtain ⟨s', run, barb⟩ := succeeds
  obtain ⟨t₁, run₁, related₁⟩ := bisimulation.runs related run
  obtain ⟨t', run', barb'⟩ := bisimulation.barbs c closed related₁ barb
  exact ⟨t', run₁.trans run', barb'⟩

theorem weaklyBarbedBisimilar_symm {s t : ByInstantiation.State}
    (bisimilar : WeaklyBarbedBisimilar s t) : WeaklyBarbedBisimilar t s := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  exact ⟨R, bisimulation, bisimulation.symm related⟩

/-! ## Divergence -/

/-- From a represented position of an infinite run, a communication is reached. -/
theorem next_communication {f : ℕ → ByInstantiation.State} (steps : ∀ n, Moves (f n) (f (n + 1))) :
    ∀ (w n : ℕ) {Q : RhoProcess} {value : ℕ → G [] .pr},
      ByInstantiation.weightOf (f n).present value = w →
      ByInstantiation.RepresentsBy (f n) Q value →
      ∃ m, n ≤ m ∧ ∃ Q', rhoLanguageDefGSLT.Step Q Q' ∧ ByInstantiation.Represents (f (m + 1)) Q' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro n Q value weight represented
    rcases (ByInstantiation.succ_iff _ _).mp (steps n) with comm | admin
    · obtain ⟨Q', value', step, represented'⟩ := ByInstantiation.communication_sound represented comm
      exact ⟨n, le_refl n, Q', step, value', represented'⟩
    · obtain ⟨value', represented', lighter⟩ :=
        ByInstantiation.administration_decreases represented admin
      obtain ⟨m, later, Q', step, represented''⟩ :=
        ih (ByInstantiation.weightOf (f (n + 1)).present value') (by omega) (n + 1) rfl represented'
      exact ⟨m, by omega, Q', step, represented''⟩

/-- **Divergence is reflected**: an infinite run of the step from a state that represents `P` gives
an infinite run of the source from `P`. -/
theorem divergence_reflected {s : ByInstantiation.State} {P : RhoProcess}
    (represented : ByInstantiation.Represents s P)
    (diverges : ∃ f : ℕ → ByInstantiation.State, f 0 = s ∧ ∀ n, Moves (f n) (f (n + 1))) :
    ∃ g : ℕ → RhoProcess, g 0 = P ∧ ∀ n, rhoLanguageDefGSLT.Step (g n) (g (n + 1)) := by
  classical
  obtain ⟨f, start, steps⟩ := diverges
  have next : ∀ x : {x : ℕ × RhoProcess // ByInstantiation.Represents (f x.1) x.2},
      ∃ y : {y : ℕ × RhoProcess // ByInstantiation.Represents (f y.1) y.2},
        rhoLanguageDefGSLT.Step x.1.2 y.1.2 := by
    rintro ⟨⟨n, Q⟩, ⟨value, represented⟩⟩
    obtain ⟨m, _, Q', step, represented'⟩ := next_communication steps _ n rfl represented
    exact ⟨⟨(m + 1, Q'), represented'⟩, step⟩
  have initial : ByInstantiation.Represents (f 0) P := by
    rw [start]
    exact represented
  let sequence : ℕ → {x : ℕ × RhoProcess // ByInstantiation.Represents (f x.1) x.2} :=
    fun k => Nat.rec (motive := fun _ => {x : ℕ × RhoProcess // ByInstantiation.Represents (f x.1) x.2})
      ⟨(0, P), initial⟩ (fun _ x => Classical.choose (next x)) k
  exact ⟨fun k => (sequence k).1.2, rfl, fun k => Classical.choose_spec (next (sequence k))⟩

#print axioms instantiate_embed
#print axioms outBarb_iff
#print axioms barb_of_outBarb
#print axioms outBarb_of_barb
#print axioms barb_eventually
#print axioms reaches_sound
#print axioms reaches_complete
#print axioms weak_barbs_agree
#print axioms coRepresent_bisimulation
#print axioms weaklyBarbedBisimilar_of_represents
#print axioms weaklyBarbedBisimilar_succeeds
#print axioms divergence_reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
