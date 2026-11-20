import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.RhoTarget

/-!
# A strict separation under one criterion, with composition restricted to solvable joint knowledge

**The criterion** is the uniform one of `NullsOnTheStep.ParallelClosed` (`UniformTranslation`): a
translation homomorphic on parallel composition up to the target's static equivalence, on composable
pairs, preserving and reflecting reachable success. By `Criteria.uniform_iff` it is Gorla's
Definition 5.2 (homomorphism of `|`) together with his Property 5 (success sensitiveness), with three
differences, all named here: it has no renaming clause (Palamidessi's uniform encodings also ask that
a renaming of names be translated to a renaming); success is an output barb on a channel `ω` that is
not reserved (any closed channel); and homomorphism is asked up to the target's static equivalence,
on the pairs the source composes.

**The step as a calculus with a parallel composition** (`stepParallelSolvable ω`): systems of the step
at the contextual frames of the twin-binder signature, with the knowledge of the reflective placement
(a program and a state, `RuleSyntax.Equivalence.System`); a system reduces by a step of its program;
two systems are composed by the union of their programs and the tensor of their states (unknowns kept
apart, identities renamed apart); **two systems are composable when their joint knowledge is
solvable**, which holds exactly when each knowledge is solvable, since the tensor keeps the unknowns
of the two sides apart (`tensor_solvable_iff`); success is the output barb on `ω`; the static
equivalence is equality.

**Both directions under that criterion, for every closed channel `ω`** (`strict_separation_solvable`):

* the reflective calculus embeds into the step: `rhoIntoStepSolvable` sends `P` to the four-rule
  program with the state `encode P`; it is homomorphic on the nose (`encode_par`), the images of any
  two processes are composable (`image_composable`), and it is success sensitive
  (`encode_successSensitive`);
* the step does not embed into the reflective calculus: in that composition the step is switchable
  (`solvable_switchable`): the system with one rule guarded by the none query of a row (make `ω!(0)` where
  no row is `*@0`) and no row succeeds, and beside the composable system with the row `*@0` and no
  rule it never succeeds; the reflective calculus is persistent (`rhoParallel_persistent`), so
  `no_uniformTranslation` applies. Of the reflective calculus the argument uses persistence only
  (`solvable_not_into_persistent`), and of its equivalence only that it respects reachable success:
  no translation of the step is homomorphic up to any such relation and success sensitive
  (`no_translation_any`; instances: equality, the equations, barbed bisimilarity over names that
  include `ω`). With the relation that relates every two processes, which does not respect success,
  the characteristic function of success is a uniform translation (`oracle_with_total`).

**Why composition is restricted.** Admission of a firing and the may-barb both ask that the whole
knowledge be solvable. With every pair composable (`stepParallel ω`), a neighbour with no rule, no
row and knowledge without a solution switches off every system: the four-rule program of the
reflective calculus, which has no check, no collect pattern and no tell (`program_positive`), is
switched off (`junk_switches`), and so is the translation of a process (`image_switched_off`). By the
same criterion the reflective calculus is then also strictly separated from the states of its own
four-rule program (`strict_separation_fourRule`). The separation with every pair composable
(`strict_separation`) is true, and its negative half is witnessed by that failure state as well as by
none queries; it is kept as the control.

**What the negative half rests on** (`DividingLine`). In the restricted composition a system whose
rules have only equation checks and no collect pattern is switched off by no composable neighbour,
whatever the neighbour's rows and rules (`succeeds_beside`); the four-rule program of the reflective
calculus is such a system (`image_never_switched`). So every switching pair has, in the switched
system, a rule with a none check, a count check or a collect pattern (`switched_has_guard`), and
the calculus of the other systems is not switchable (`positiveParallel_not_switchable`): for it this
argument gives no separation, and whether it embeds into the reflective calculus under this criterion
is open.

**What the criterion does not cover.** Gorla's compositionality with a coordinating context for `|`
(his Property 1 without Definition 5.2) is not the criterion here; for it the separation needs that
the context keeps reachable success of its first hole (`ParallelClosed.KeepsFirst`), which fails for
a context that guards its hole (`ParallelClosed.Controls.guarded_context`), and it is not claimed.
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
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus UniformTranslation isEmpty_uniformTranslation)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding GroundSolves read inputT outputT zeroT
  bagT pnilT pconsT dropqT quoteT spine knowledge groundFrame someGrounding)
open Interface.Frames (Frame)

/-! ## Systems -/

/-- A system of the step at the twin-binder frames: a program and a state. -/
abbrev System := RuleSyntax.Equivalence.System (RuleSyntax.Contextual.Terms sig) ℕ

/-- A reduction of a system: a step of its program. -/
abbrev SystemReduces (S T : System) : Prop :=
  RuleSyntax.Equivalence.Reduces knowledge ℕ (RuleSyntax.Contextual.declarations sig) S T

/-- **The step with every pair of systems composable**: the union of the programs and the tensor of the
states, for every two systems. Admission and the may-barb ask the whole knowledge to be solvable, so a
neighbour whose knowledge has no solution switches off every system here (`junk_switches`); this
calculus is the control for `stepParallelSolvable`, where composition asks for solvable joint
knowledge. -/
def stepParallel (ω : G [] .nm) : ParallelCalculus.{1} where
  Term := System
  step := SystemReduces
  par S T := ⟨S.program ∪ T.program, tensor S.state T.state⟩
  composable _ _ := True
  success S := OutBarb ω S.state
  same := Eq

/-- Runs of a system of the four-rule program are runs of the step. -/
theorem systemRuns_program {s : ByInstantiation.State} {T : System}
    (run : Relation.ReflTransGen SystemReduces ⟨ByInstantiation.program, s⟩ T) :
    T.program = ByInstantiation.program ∧ Runs s T.state := by
  induction run with
  | refl => exact ⟨rfl, .refl⟩
  | @tail B C _ last ih =>
      obtain ⟨same, run⟩ := ih
      obtain ⟨keeps, moved⟩ := last
      obtain ⟨program, state⟩ := B
      change program = ByInstantiation.program at same
      subst same
      exact ⟨keeps, run.tail moved⟩

theorem systemRuns_of_runs {s t : ByInstantiation.State} (run : Runs s t) :
    Relation.ReflTransGen SystemReduces ⟨ByInstantiation.program, s⟩ ⟨ByInstantiation.program, t⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail ⟨rfl, last⟩

/-- Success of a system of the four-rule program is reachable output on `ω` of its state. -/
theorem stepParallel_succeeds_iff (ω : G [] .nm) (s : ByInstantiation.State) :
    (stepParallel ω).Succeeds ⟨ByInstantiation.program, s⟩ ↔ ∃ t, Runs s t ∧ OutBarb ω t := by
  constructor
  · rintro ⟨T, run, shows⟩
    exact ⟨T.state, (systemRuns_program run).2, shows⟩
  · rintro ⟨t, run, shows⟩
    exact ⟨⟨ByInstantiation.program, t⟩, systemRuns_of_runs run, shows⟩

/-! ## The reflective calculus into the step, uniformly -/

/-- **The uniform translation of the reflective calculus into the step with every pair composable**: a
process goes to the four-rule program with the state `encode P`. Into the step with restricted
composition it is `rhoIntoStepSolvable`, the same map. -/
def rhoIntoStep {ω : G [] .nm} (closed : Closed ω) :
    UniformTranslation (rhoParallel ω) (stepParallel ω) where
  map P := ⟨ByInstantiation.program, encode P⟩
  homomorphic P Q _ := by
    show (⟨ByInstantiation.program, encode (par P Q)⟩ : System) =
      ⟨ByInstantiation.program ∪ ByInstantiation.program, tensor (encode P) (encode Q)⟩
    rw [Set.union_self]
    exact congrArg (fun s => (⟨ByInstantiation.program, s⟩ : System)) (encode_par P Q)
  preserves P succeeds :=
    (stepParallel_succeeds_iff ω _).mpr ((encode_successSensitive closed P).mp succeeds)
  reflects P succeeds :=
    (encode_successSensitive closed P).mpr ((stepParallel_succeeds_iff ω _).mp succeeds)

/-! ## The step is switchable -/

/-- The inert drop `*@0`: the neighbour's row. -/
abbrev blockerRow : G [] .pr := dropqT zeroT

/-- The output on `ω` the guarded rule makes. -/
abbrev successRow (ω : G [] .nm) : G [] .pr := outputT ω zeroT

/-- **The guarded spawn**: no take, read or tell; it asks that no row be `*@0`, and makes `ω!(0)`. -/
abbrev guardedSpawn (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [], read := [], tell := [], checks := [.predicate .none (ByInstantiation.obs blockerRow)],
            produce := [ByInstantiation.obs (successRow ω)] }
  collect := []

/-- The system of the guarded spawn, with no row. -/
def spawnSystem (ω : G [] .nm) : System := ⟨{guardedSpawn ω}, emptyState⟩

/-- The system with the row `*@0` and no rule. -/
def blockerSystem : System := ⟨∅, single blockerRow⟩

/-- Instantiating a ground observation and then grounding gives it back. -/
theorem ground_back {W : Type} {D : W → MetaArity sig} (a : Assignment ByInstantiation.noUnknowns D)
    (g : Assignment D ByInstantiation.noUnknowns) (o : Observation sig ByInstantiation.noUnknowns) :
    instantiateObservation g (instantiateObservation a o) = o := by
  rw [instantiateObservation_comp, ByInstantiation.instantiateObservation_ground]

/-- The same along three assignments. -/
theorem ground_back₃ {W W' : Type} {D : W → MetaArity sig} {D' : W' → MetaArity sig}
    (a : Assignment ByInstantiation.noUnknowns D) (b : Assignment D D')
    (g : Assignment D' ByInstantiation.noUnknowns) (o : Observation sig ByInstantiation.noUnknowns) :
    instantiateObservation g (instantiateObservation b (instantiateObservation a o)) = o := by
  rw [instantiateObservation_comp a b, ground_back]

/-- The output pattern on `c`, its payload grounded at `q`. -/
theorem outPattern_ground (c : G [] .nm) (q : G [] .pr) :
    instantiateObservation (fun _ => q : Assignment payloadFrame.arity ByInstantiation.noUnknowns)
      (⟨[], .pr, outputT (embed c) payloadUnknown⟩ : Observation sig payloadFrame.arity) =
        ⟨[], .pr, outputT c q⟩ := by
  change (⟨[], .pr, instantiate (fun _ => q : Assignment payloadFrame.arity ByInstantiation.noUnknowns)
    (outputT (embed c) payloadUnknown)⟩ : Observation sig ByInstantiation.noUnknowns) = _
  rw [instantiate_outputT, instantiate_embed, embed_ground, instantiate_generator]

/-- At the frames of the step, the canonical opening is fresh for the knowledge, for every program. -/
theorem canonical_fresh_knowledge {P : RuleSyntax.Program (RuleSyntax.Contextual.Terms sig)}
    (s : ByInstantiation.State) (r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig)) (member : r ∈ P)
    (selection : Selection ℕ) (seen : List (Finset ℕ)) :
    (RuleSyntax.Contextual.canonical (F := s.frame) r member selection seen).Fresh knowledge s := by
  intro B g h
  obtain ⟨u, state, rule⟩ :=
    RuleSyntax.Contextual.canonical_fresh (S := sig) s r member selection seen B g h
  refine ⟨u, fun t mentioned => ?_, fun t inside => ?_⟩
  · exact (congrArg (fun x => ByInstantiation.Equal x ((Interface.Frames.contextual sig).act g t))
      (state t mentioned)).mpr (fun _ => ByInstantiation.obsSimilar_refl _)
  · exact (congrArg (fun x => ByInstantiation.Equal x ((Interface.Frames.contextual sig).act h t))
      (rule t inside)).mpr (fun _ => ByInstantiation.obsSimilar_refl _)

/-- The firing of the guarded spawn at the empty state, making identity `0`. -/
abbrev spawnFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations sig)
      ({guardedSpawn ω} : RuleSyntax.Program (RuleSyntax.Contextual.Terms sig)) emptyState.frame :=
  RuleSyntax.Contextual.canonical (F := emptyState.frame) (guardedSpawn ω) (Set.mem_singleton _)
    ⟨[], [], [0]⟩ []

theorem spawn_information (ω : G [] .nm) :
    (spawnFiring ω).information knowledge emptyState = [] := rfl

/-- **Alone, the guarded spawn fires.** -/
theorem spawn_admitted (ω : G [] .nm) : (spawnFiring ω).Admits knowledge emptyState := by
  refine ⟨⟨canonical_fresh_knowledge emptyState (guardedSpawn ω) (Set.mem_singleton _) _ _,
    List.nodup_nil, List.nodup_singleton 0, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ()) (∅ : Finset ℕ) ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [spawn_information]
    exact fun e inside => nomatch inside
  · intro b σ _
    refine ⟨fun c inside => ?_, fun q inside => ?_⟩
    · change c ∈ [Check.map (knowledge.act (spawnFiring ω).opening)
        (Check.predicate .none (ByInstantiation.obs blockerRow))] at inside
      rw [List.mem_singleton] at inside
      subst inside
      exact fun o present => absurd present (Finset.notMem_empty o)
    · exact nomatch inside

theorem spawn_result_label (ω : G [] .nm) :
    ((spawnFiring ω).result knowledge emptyState).label 0 =
      knowledge.act (RuleSyntax.Contextual.canonicalOpening sig emptyState.frame groundFrame)
        (ByInstantiation.obs (successRow ω)) := rfl

/-- **Alone, the system of the guarded spawn succeeds**: it fires and shows `ω!(0)`. -/
theorem spawnSystem_succeeds (ω : G [] .nm) : (stepParallel ω).Succeeds (spawnSystem ω) := by
  refine ⟨⟨{guardedSpawn ω}, (spawnFiring ω).result knowledge emptyState⟩,
    .single ⟨rfl, spawnFiring ω, spawn_admitted ω, rfl⟩, ?_⟩
  refine ⟨0, ?_, groundFrame, someGrounding _, fun _ => zeroT, ?_, ?_⟩
  · change 0 ∈ fire emptyState.present ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact .inr (by simp [Selection.commit])
  · intro e inside
    change e ∈ (spawnFiring ω).information knowledge emptyState at inside
    rw [spawn_information] at inside
    exact nomatch inside
  · intro g
    have made : instantiateObservation (someGrounding _)
        (((spawnFiring ω).result knowledge emptyState).label 0) = ByInstantiation.obs (successRow ω) := by
      rw [spawn_result_label]
      show instantiateObservation (someGrounding _)
        (instantiateObservation (RuleSyntax.Contextual.canonicalOpening sig emptyState.frame groundFrame)
          (ByInstantiation.obs (successRow ω))) = _
      exact ground_back _ _ _
    show ObsSimilar (instantiateObservation g (instantiateObservation (someGrounding _)
        (((spawnFiring ω).result knowledge emptyState).label 0)))
      (instantiateObservation g (instantiateObservation (fun _ => zeroT : Assignment payloadFrame.arity
        ByInstantiation.noUnknowns)
          (⟨[], .pr, outputT (embed ω) payloadUnknown⟩ : Observation sig payloadFrame.arity)))
    have pattern : instantiateObservation g (instantiateObservation
        (fun _ => zeroT : Assignment payloadFrame.arity ByInstantiation.noUnknowns)
        (⟨[], .pr, outputT (embed ω) payloadUnknown⟩ : Observation sig payloadFrame.arity)) =
          instantiateObservation g (ByInstantiation.obs (successRow ω)) :=
      congrArg (instantiateObservation g) (outPattern_ground ω zeroT)
    rw [made]
    exact (congrArg (ObsSimilar (instantiateObservation g (ByInstantiation.obs (successRow ω)))) pattern).mpr
      (ByInstantiation.obsSimilar_refl _)

/-- The tensor of the empty state and the blocker's state represents `*@0`. -/
theorem blocked_represents :
    ByInstantiation.RepresentsBy (tensor emptyState (single blockerRow))
      (ByInstantiation.rowProcess blockerRow (by decide))
      (tensorValue (fun _ => zeroT) (fun _ => blockerRow)) :=
  tensor_represents (empty_represents (P := nil) ReflectiveCalculus.primes_zero)
    (ByInstantiation.initial_represents (ByInstantiation.rowProcess blockerRow (by decide)) rfl)
    (by rw [show (fromProcess nil).1 = 0 from ReflectiveCalculus.primes_zero, zero_add])

/-- **Beside the blocker, no output on `ω` is shown.** -/
theorem blocked_no_barb (ω : G [] .nm) : ¬ OutBarb ω (tensor emptyState (single blockerRow)) := by
  intro shows
  obtain ⟨o, present, c', q, shape, _⟩ := (outBarb_iff blocked_represents ω).mp shows
  rcases mem_tensor.mp present with ⟨k, inside, _⟩ | ⟨k, inside, rfl⟩
  · exact absurd inside (Finset.notMem_empty k)
  · rw [tensorValue_odd] at shape
    cases shape

/-- **Beside the blocker, the guarded spawn is refused**: every firing of the program at the tensor
of the two states fails its none check, at a solution of its information. -/
theorem blocked_stuck (ω : G [] .nm) (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations sig)
    ({guardedSpawn ω} ∪ ∅ : RuleSyntax.Program (RuleSyntax.Contextual.Terms sig))
    (tensor emptyState (single blockerRow)).frame) :
    ¬ f.Admits knowledge (tensor emptyState (single blockerRow)) := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  have isSpawn : rule = guardedSpawn ω := by
    rcases member with inside | inside
    · exact inside
    · exact inside.elim
  subst isSpawn
  rintro ⟨_, _, _, entails⟩
  have information : RuleSyntax.Firing.information knowledge (tensor emptyState (single blockerRow))
      ⟨guardedSpawn ω, member, ext, opening, selection, seen⟩ = [] := rfl
  have holds := entails groundFrame (someGrounding _) (by
    intro e inside
    rw [information] at inside
    exact nomatch inside)
  have check := holds.1 (.predicate .none (knowledge.act opening (ByInstantiation.obs blockerRow)))
    (List.mem_singleton_self _)
  have present : (1 : ℕ) ∈ (tensor emptyState (single blockerRow)).present :=
    mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)
  apply check 1 present
  intro g
  have label : (tensor emptyState (single blockerRow)).label 1 =
      instantiateObservation (rightIn emptyState.frame (single blockerRow).frame)
        (ByInstantiation.obs blockerRow) := tensor_label_odd emptyState (single blockerRow) 0
  have left : instantiateObservation (someGrounding _)
      (instantiateObservation opening (ByInstantiation.obs blockerRow)) = ByInstantiation.obs blockerRow :=
    ground_back _ _ _
  have right : instantiateObservation (someGrounding _)
      (instantiateObservation (RuleSyntax.Contextual.weakenNames sig (tensor emptyState (single blockerRow)).frame ext)
        ((tensor emptyState (single blockerRow)).label 1)) = ByInstantiation.obs blockerRow := by
    rw [label]
    exact ground_back₃ _ _ _ _
  change ObsSimilar (instantiateObservation g (instantiateObservation (someGrounding _)
      (instantiateObservation opening (ByInstantiation.obs blockerRow))))
    (instantiateObservation g (instantiateObservation (someGrounding _)
      (instantiateObservation (RuleSyntax.Contextual.weakenNames sig (tensor emptyState (single blockerRow)).frame ext)
        ((tensor emptyState (single blockerRow)).label 1))))
  rw [left, right]
  exact ByInstantiation.obsSimilar_refl _

/-- **Beside the blocker, success is never reached.** -/
theorem blocked_never_succeeds (ω : G [] .nm) :
    ¬ (stepParallel ω).Succeeds ((stepParallel ω).par (spawnSystem ω) blockerSystem) := by
  rintro ⟨T, run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨T₁, ⟨_, f, admitted, _⟩, _⟩
  · exact blocked_no_barb ω shows
  · exact blocked_stuck ω f admitted

/-- **With every pair composable, the step is switchable by none queries**: the system of the guarded spawn
succeeds, and beside the system with the row `*@0` it never does. The same pair is composable when
composition asks for solvable joint knowledge (`solvable_switchable`). -/
theorem stepParallel_switchable (ω : G [] .nm) : (stepParallel ω).Switchable :=
  ⟨spawnSystem ω, blockerSystem, trivial, spawnSystem_succeeds ω, blocked_never_succeeds ω⟩

/-! ## Composition restricted to solvable joint knowledge -/

/-- **The tensor's knowledge is solvable exactly when both knowledges are**: the tensor keeps the
unknowns of its two sides apart, so a solution of each side gives one of the whole by the copair. -/
theorem tensor_solvable_iff (s t : ByInstantiation.State) :
    knowledge.Solvable (tensor s t).knowledge ↔
      knowledge.Solvable s.knowledge ∧ knowledge.Solvable t.knowledge := by
  rw [ByInstantiation.solvable_iff, ByInstantiation.solvable_iff, ByInstantiation.solvable_iff]
  constructor
  · rintro ⟨g, solves⟩
    exact ⟨⟨_, tensor_solves_left solves⟩, ⟨_, tensor_solves_right solves⟩⟩
  · rintro ⟨⟨gs, solvesS⟩, ⟨gt, solvesT⟩⟩
    refine ⟨RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt, fun e member => ?_⟩
    rcases List.mem_append.mp member with inLeft | inRight
    · obtain ⟨e₀, inS, rfl⟩ := List.mem_map.mp inLeft
      change ObsSimilar
          (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
            (instantiateObservation (leftIn s.frame t.frame) e₀.1))
        (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
          (instantiateObservation (leftIn s.frame t.frame) e₀.2))
      rw [RuleSyntax.Contextual.copair_weaken, RuleSyntax.Contextual.copair_weaken]
      exact solvesS e₀ inS
    · obtain ⟨e₀, inT, rfl⟩ := List.mem_map.mp inRight
      change ObsSimilar
          (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
            (instantiateObservation (rightIn s.frame t.frame) e₀.1))
        (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
          (instantiateObservation (rightIn s.frame t.frame) e₀.2))
      rw [RuleSyntax.Contextual.copair_opening, RuleSyntax.Contextual.copair_opening]
      exact solvesT e₀ inT

/-- **The step as a calculus with a parallel composition, composition restricted to solvable joint
knowledge**: systems; a step of the system's program; the union of the programs with the tensor of the
states, defined on the pairs whose joint knowledge (the tensor's) is solvable; success the output barb
on `ω`; equality as the static equivalence. -/
def stepParallelSolvable (ω : G [] .nm) : ParallelCalculus.{1} where
  Term := System
  step := SystemReduces
  par S T := ⟨S.program ∪ T.program, tensor S.state T.state⟩
  composable S T := knowledge.Solvable (tensor S.state T.state).knowledge
  success S := OutBarb ω S.state
  same := Eq

/-- Reachable success does not depend on which pairs are composable. -/
theorem succeeds_solvable_iff (ω : G [] .nm) (S : System) :
    (stepParallelSolvable ω).Succeeds S ↔ (stepParallel ω).Succeeds S :=
  Iff.rfl

/-- **Composable means: each knowledge is solvable.** -/
theorem solvable_composable_iff (ω : G [] .nm) (S T : System) :
    (stepParallelSolvable ω).composable S T ↔
      knowledge.Solvable S.state.knowledge ∧ knowledge.Solvable T.state.knowledge :=
  tensor_solvable_iff S.state T.state

/-- **The uniform translation of the reflective calculus into the step with restricted composition**:
the same map, `P` to the four-rule program with the state `encode P`. -/
def rhoIntoStepSolvable {ω : G [] .nm} (closed : Closed ω) :
    UniformTranslation (rhoParallel ω) (stepParallelSolvable ω) where
  map := (rhoIntoStep closed).map
  homomorphic := (rhoIntoStep closed).homomorphic
  preserves := (rhoIntoStep closed).preserves
  reflects := (rhoIntoStep closed).reflects

/-- **The images of any two processes are composable**: the tensor of their states represents their
parallel composition, so its knowledge is solvable. -/
theorem image_composable {ω : G [] .nm} (closed : Closed ω) (P Q : RhoProcess) :
    (stepParallelSolvable ω).composable ((rhoIntoStepSolvable closed).map P)
      ((rhoIntoStepSolvable closed).map Q) := by
  change knowledge.Solvable (tensor (encode P) (encode Q)).knowledge
  obtain ⟨left, onP⟩ := encode_represents P
  obtain ⟨right, onQ⟩ := encode_represents Q
  exact (ByInstantiation.solvable_iff _).mpr (tensor_represents onP onQ (fromProcess_par P Q)).solvable

/-- **With composition restricted to solvable joint knowledge, the step is still switchable, by
none queries**: the system of the guarded spawn and the system with the row `*@0` are composable (neither
has knowledge), the first succeeds, and side by side they never do. -/
theorem solvable_switchable (ω : G [] .nm) : (stepParallelSolvable ω).Switchable := by
  refine ⟨spawnSystem ω, blockerSystem, ?_, spawnSystem_succeeds ω, blocked_never_succeeds ω⟩
  refine (ByInstantiation.solvable_iff _).mpr ⟨ByInstantiation.someGrounding _, ?_⟩
  intro e member
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  simp [Interface.Frames.applyStore] at member

/-! ## The strict separation -/

/-- **A strict separation under the uniform criterion, with composition restricted to solvable joint
knowledge.** For every closed channel `ω`, with success the output barb on `ω` on both sides: a
uniform translation of the reflective calculus into the step exists, and none of the step into the
reflective calculus. The negative half is witnessed by a rule guarded by the none query of a row
(`solvable_switchable`). -/
theorem strict_separation_solvable {ω : G [] .nm} (closed : Closed ω) :
    Nonempty (UniformTranslation (rhoParallel ω) (stepParallelSolvable ω)) ∧
      IsEmpty (UniformTranslation (stepParallelSolvable ω) (rhoParallel ω)) :=
  ⟨⟨rhoIntoStepSolvable closed⟩,
    isEmpty_uniformTranslation (solvable_switchable ω) (rhoParallel_persistent ω)⟩

/-- **The negative half names no property of the reflective calculus but persistence**: no uniform
translation of the step, with restricted composition, goes into any persistent calculus. -/
theorem solvable_not_into_persistent (ω : G [] .nm) (M : ParallelCalculus) (persistent : M.Persistent) :
    IsEmpty (UniformTranslation (stepParallelSolvable ω) M) :=
  isEmpty_uniformTranslation (solvable_switchable ω) persistent

/-- **The control: with every pair composable.** Both halves hold here too, but the negative half
needs no none query: a neighbour whose knowledge has no solution switches off every system
(`junk_switches`), and by the same criterion the reflective calculus is separated from the states of
its own four-rule program (`strict_separation_fourRule`). The separation that names its feature is
`strict_separation_solvable`. -/
theorem strict_separation {ω : G [] .nm} (closed : Closed ω) :
    Nonempty (UniformTranslation (rhoParallel ω) (stepParallel ω)) ∧
      IsEmpty (UniformTranslation (stepParallel ω) (rhoParallel ω)) :=
  ⟨⟨rhoIntoStep closed⟩,
    isEmpty_uniformTranslation (stepParallel_switchable ω) (rhoParallel_persistent ω)⟩

/-- **`strict_separation_solvable` in Gorla's terms**: some translation of the reflective calculus into
the step is homomorphic on parallel composition (Definition 5.2) and success sensitive (Property 5),
and no translation of the step into the reflective calculus is homomorphic, up to the equations, on
the pairs of systems with solvable joint knowledge, and success sensitive. Gorla's parallel
composition is total; here the step's is defined on those pairs, and homomorphism is asked there. -/
theorem strict_separation_gorla {ω : G [] .nm} (closed : Closed ω) :
    (∃ map : RhoProcess → System,
      (∀ P Q, map (par P Q) = (stepParallelSolvable ω).par (map P) (map Q)) ∧
        SuccessSensitive (L := ofParallel (rhoParallel ω) rhoProcessEquations.r)
          (M := ofParallel (stepParallelSolvable ω) Eq) map) ∧
      ¬ ∃ map : System → RhoProcess,
        (∀ S T, (stepParallelSolvable ω).composable S T →
          rhoProcessEquations.r (map ((stepParallelSolvable ω).par S T)) (par (map S) (map T))) ∧
          SuccessSensitive (L := ofParallel (stepParallelSolvable ω) Eq)
            (M := ofParallel (rhoParallel ω) rhoProcessEquations.r) map := by
  refine ⟨⟨(rhoIntoStepSolvable closed).map, fun P Q => (rhoIntoStepSolvable closed).homomorphic P Q trivial,
    ((uniform_iff _ _ _).mp ⟨rhoIntoStepSolvable closed, rfl⟩).2⟩, ?_⟩
  rintro ⟨map, homomorphic, sensitive⟩
  obtain ⟨τ, _⟩ := (uniform_iff (L := stepParallelSolvable ω) (M := rhoParallel ω) Eq
    rhoProcessEquations.r map).mpr ⟨homomorphic, sensitive⟩
  exact (strict_separation_solvable closed).2.false τ

/-! ## The negative half for every relation that respects success -/

/-- **The reflective calculus with any relation `E` as its static equivalence**: the same processes,
reduction, parallel composition and success. -/
def rhoWith (ω : G [] .nm) (E : RhoProcess → RhoProcess → Prop) : ParallelCalculus.{0} :=
  { rhoParallel ω with same := E }

/-- `E` **respects reachable success** in one direction: `E t t'` and `t'` succeeds give `t`
succeeds (Gorla's coherence condition, one way). -/
def RespectsSuccess (ω : G [] .nm) (E : RhoProcess → RhoProcess → Prop) : Prop :=
  ∀ t t', E t t' → (rhoParallel ω).Succeeds t' → (rhoParallel ω).Succeeds t

/-- **Persistence needs of `E` only that it respects success.** -/
theorem rhoWith_persistent (ω : G [] .nm) {E : RhoProcess → RhoProcess → Prop}
    (respects : RespectsSuccess ω E) : (rhoWith ω E).Persistent where
  closed := rho_closedBeside
  persists P R shows := barb_par_left P R _ shows
  respects := respects

/-- **No translation of the step, with restricted composition, into the reflective calculus is
homomorphic up to a relation that respects success and success sensitive**, whatever that
relation. -/
theorem no_translation_any (ω : G [] .nm) {E : RhoProcess → RhoProcess → Prop}
    (respects : RespectsSuccess ω E) :
    ¬ ∃ map : System → RhoProcess,
      (∀ S T, (stepParallelSolvable ω).composable S T →
        E (map ((stepParallelSolvable ω).par S T)) (par (map S) (map T))) ∧
        ∀ S, (stepParallelSolvable ω).Succeeds S ↔ (rhoParallel ω).Succeeds (map S) := by
  rintro ⟨map, homomorphic, sensitive⟩
  exact (isEmpty_uniformTranslation (solvable_switchable ω) (rhoWith_persistent ω respects)).false
    ⟨map, homomorphic, fun S => (sensitive S).mp, fun S => (sensitive S).mpr⟩

/-- Equality respects success. -/
theorem eq_respects (ω : G [] .nm) : RespectsSuccess ω Eq := by
  rintro t t' rfl succeeds
  exact succeeds

/-- **Instance: Definition 5.2 on the nose.** -/
theorem no_translation_eq (ω : G [] .nm) :
    ¬ ∃ map : System → RhoProcess,
      (∀ S T, (stepParallelSolvable ω).composable S T →
        map ((stepParallelSolvable ω).par S T) = par (map S) (map T)) ∧
        ∀ S, (stepParallelSolvable ω).Succeeds S ↔ (rhoParallel ω).Succeeds (map S) :=
  no_translation_any ω (eq_respects ω)

/-- **Instance: the equations of the calculus.** -/
theorem no_translation_equations (ω : G [] .nm) :
    ¬ ∃ map : System → RhoProcess,
      (∀ S T, (stepParallelSolvable ω).composable S T →
        rhoProcessEquations.r (map ((stepParallelSolvable ω).par S T)) (par (map S) (map T))) ∧
        ∀ S, (stepParallelSolvable ω).Succeeds S ↔ (rhoParallel ω).Succeeds (map S) :=
  no_translation_any ω (rhoParallel_persistent ω).respects

/-- A source bisimulation answers runs by runs. -/
theorem SourceBisimulation.runs {N : G [] .nm → Prop} {R : RhoProcess → RhoProcess → Prop}
    (bisimulation : SourceBisimulation N R) {P Q P' : RhoProcess} (related : R P Q)
    (run : Relation.ReflTransGen rhoLanguageDefGSLT.Step P P') :
    ∃ Q', Relation.ReflTransGen rhoLanguageDefGSLT.Step Q Q' ∧ R P' Q' := by
  induction run with
  | refl => exact ⟨Q, .refl, related⟩
  | tail _ last ih =>
      obtain ⟨Q₁, run₁, related₁⟩ := ih
      obtain ⟨Q', run', related'⟩ := bisimulation.step related₁ last
      exact ⟨Q', run₁.trans run', related'⟩

/-- **Barbed bisimilarity over names that include the success channel respects success.** -/
theorem bisimilar_respects (ω : G [] .nm) {N : G [] .nm → Prop} (observed : N ω) :
    RespectsSuccess ω (SourceBisimilar N) := by
  rintro t t' ⟨R, bisimulation, related⟩ ⟨t'', run, shows⟩
  obtain ⟨t₁, run₁, related₁⟩ := SourceBisimulation.runs bisimulation (bisimulation.symm related) run
  obtain ⟨t₂, run₂, shows₂⟩ := bisimulation.barb ω observed related₁ shows
  exact ⟨t₂, run₁.trans run₂, shows₂⟩

/-- **Instance: the barbed bisimilarity of the 2005 paper** (Definition 4.2, read on canonical
forms), over any set of names that contains `ω`. -/
theorem no_translation_bisimilar (ω : G [] .nm) {N : G [] .nm → Prop} (observed : N ω) :
    ¬ ∃ map : System → RhoProcess,
      (∀ S T, (stepParallelSolvable ω).composable S T →
        SourceBisimilar N (map ((stepParallelSolvable ω).par S T)) (par (map S) (map T))) ∧
        ∀ S, (stepParallelSolvable ω).Succeeds S ↔ (rhoParallel ω).Succeeds (map S) :=
  no_translation_any ω (bisimilar_respects ω observed)

/-! ### Control: a relation that does not respect success -/

/-- The relation that relates every two processes keeps the reduction closed beside and success
persistent. -/
theorem total_keeps_closed_and_persists (ω : G [] .nm) :
    NullsOnTheStep.ParallelClosed.ClosedBeside (rhoWith ω fun _ _ => True).step
        (rhoWith ω fun _ _ => True).par ∧
      ∀ t u, (rhoWith ω fun _ _ => True).success t →
        (rhoWith ω fun _ _ => True).success ((rhoWith ω fun _ _ => True).par t u) :=
  ⟨rho_closedBeside, fun P R shows => barb_par_left P R _ shows⟩

/-- It does not respect success. -/
theorem total_not_respects : ¬ RespectsSuccess ByInstantiation.nameZero (fun _ _ => True) := by
  intro respects
  exact nil_not_succeeds _ (respects nil outputNil trivial succeeds_output)

open Classical in
/-- The characteristic function of reachable success of the step, into the reflective calculus. -/
noncomputable def characteristic (S : System) : RhoProcess :=
  if (stepParallelSolvable ByInstantiation.nameZero).Succeeds S then outputNil else nil

theorem characteristic_succeeds {S : System}
    (succeeds : (stepParallelSolvable ByInstantiation.nameZero).Succeeds S) :
    characteristic S = outputNil := by
  unfold characteristic
  exact if_pos succeeds

theorem characteristic_fails {S : System}
    (fails : ¬ (stepParallelSolvable ByInstantiation.nameZero).Succeeds S) : characteristic S = nil := by
  unfold characteristic
  exact if_neg fails

/-- **Control: with a relation that does not respect success, the characteristic function of success
is a uniform translation.** It meets every condition of the criterion except respect of success by
the target's equivalence (`total_not_respects`; `total_keeps_closed_and_persists` gives the other two
conditions of persistence). -/
noncomputable def oracle_with_total :
    UniformTranslation (stepParallelSolvable ByInstantiation.nameZero)
      (rhoWith ByInstantiation.nameZero fun _ _ => True) where
  map := characteristic
  homomorphic _ _ _ := trivial
  preserves S succeeds := by
    change (rhoParallel ByInstantiation.nameZero).Succeeds (characteristic S)
    rw [characteristic_succeeds succeeds]
    exact succeeds_output
  reflects S succeeds := by
    change (rhoParallel ByInstantiation.nameZero).Succeeds (characteristic S) at succeeds
    by_contra never
    rw [characteristic_fails never] at succeeds
    exact nil_not_succeeds _ succeeds

#print axioms systemRuns_program
#print axioms stepParallel_succeeds_iff
#print axioms rhoIntoStep
#print axioms spawn_admitted
#print axioms spawnSystem_succeeds
#print axioms blocked_represents
#print axioms blocked_no_barb
#print axioms blocked_stuck
#print axioms blocked_never_succeeds
#print axioms stepParallel_switchable
#print axioms tensor_solvable_iff
#print axioms succeeds_solvable_iff
#print axioms solvable_composable_iff
#print axioms rhoIntoStepSolvable
#print axioms image_composable
#print axioms solvable_switchable
#print axioms strict_separation_solvable
#print axioms solvable_not_into_persistent
#print axioms strict_separation
#print axioms strict_separation_gorla
#print axioms rhoWith_persistent
#print axioms no_translation_any
#print axioms no_translation_eq
#print axioms no_translation_equations
#print axioms SourceBisimulation.runs
#print axioms bisimilar_respects
#print axioms no_translation_bisimilar
#print axioms total_keeps_closed_and_persists
#print axioms total_not_respects
#print axioms oracle_with_total

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
