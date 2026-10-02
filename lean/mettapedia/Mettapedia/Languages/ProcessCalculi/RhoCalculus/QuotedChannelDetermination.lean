import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelCalculus

/-!
# The observer class determined by parallel interaction, in the quoted-channel calculus

The reduction rules of the quoted-channel calculus use one kind of context: a
partner placed in parallel.  Taking those as the mandatory interaction
contexts, the two-step determination of `ObserverDetermination` computes

* `equivStar`: the relative equivalence of the class they generate, which is
  the class `parallel` of contexts built from parallel composition
  (`generatedBy_mandatory_eq_parallel`);
* `dStar`: every context that preserves `equivStar`.

This module computes `dStar` on one-layer positions:

* it contains every guarded context, input continuations included
  (`guarded_le_dStar`), and the guarded equivalence equals `equivStar`
  (`relEquiv_guarded_iff_equivStar`);
* it excludes every position that reads code: an output payload, an output
  channel, an input channel and an echo channel (`outPayload_not_mem_dStar`,
  `outChannel_not_mem_dStar`, `inpChannel_not_mem_dStar`,
  `echoChannel_not_mem_dStar`).

The top class is a fixed point of determination as well, with syntactic
identity as its equivalence; the two fixed points are incomparable when
classes and relations are both ordered by inclusion
(`fixed_points_incomparable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass

/-! ## Parallel contexts -/

namespace Ctx

/-- The hole is reached through parallel composition only. -/
def Parallel : Ctx → Prop
  | .hole => True
  | .parL context _ => context.Parallel
  | .parR _ context => context.Parallel
  | _ => False

theorem parallel_comp {outer inner : Ctx} (outerParallel : outer.Parallel)
    (innerParallel : inner.Parallel) : (outer.comp inner).Parallel := by
  induction outer with
  | hole => exact innerParallel
  | parL _ _ ih => exact ih outerParallel
  | parR _ _ ih => exact ih outerParallel
  | outChannel => exact (outerParallel : False).elim
  | outPayload => exact (outerParallel : False).elim
  | inpChannel => exact (outerParallel : False).elim
  | inpBody => exact (outerParallel : False).elim
  | echoChannel => exact (outerParallel : False).elim

theorem Parallel.guarded {context : Ctx} (parallel : context.Parallel) : context.Guarded := by
  induction context with
  | hole => trivial
  | parL _ _ ih => exact ih parallel
  | parR _ _ ih => exact ih parallel
  | outChannel => exact (parallel : False).elim
  | outPayload => exact (parallel : False).elim
  | inpChannel => exact (parallel : False).elim
  | inpBody => exact (parallel : False).elim
  | echoChannel => exact (parallel : False).elim

end Ctx

/-- The class of parallel contexts. -/
def parallel : AdmissibleClass quotedRules where
  Admissible := Ctx.Parallel
  identity_mem := trivial
  compose_mem := Ctx.parallel_comp

/-- The mandatory interaction contexts: one partner beside the hole. -/
def mandatory : Set quotedRules.Context :=
  {context | ∃ right, context = Ctx.parL Ctx.hole right} ∪
    {context | ∃ left, context = Ctx.parR left Ctx.hole}

theorem generatedBy_mandatory_eq_parallel : generatedBy mandatory = parallel := by
  apply le_antisymm
  · rw [generatedBy_le_iff]
    rintro _ (⟨right, rfl⟩ | ⟨left, rfl⟩) <;> trivial
  · intro context isParallel
    induction context with
    | hole => exact (generatedBy mandatory).identity_mem
    | parL inner right ih =>
        exact (generatedBy mandatory).compose_mem (outer := .parL .hole right) (inner := inner)
          (generator_mem (Or.inl ⟨right, rfl⟩)) (ih isParallel)
    | parR left inner ih =>
        exact (generatedBy mandatory).compose_mem (outer := .parR left .hole) (inner := inner)
          (generator_mem (Or.inr ⟨left, rfl⟩)) (ih isParallel)
    | outChannel => exact (isParallel : False).elim
    | outPayload => exact (isParallel : False).elim
    | inpChannel => exact (isParallel : False).elim
    | inpBody => exact (isParallel : False).elim
    | echoChannel => exact (isParallel : False).elim

theorem parallel_le_guarded : parallel ≤ guarded := fun _ isParallel => isParallel.guarded

/-- The equivalence fixed by parallel interaction. -/
theorem equivStar_iff (left right : Proc) :
    equivStar barbs mandatory left right ↔ parallel.RelEquiv barbs left right := by
  unfold equivStar
  rw [generatedBy_mandatory_eq_parallel]

/-! ## Separations by parallel observers -/

theorem parallel_listenOn (channel : Proc) : parallel.Admissible (listenOn channel) := trivial

theorem not_relEquiv_out_payload_of_mem (A : AdmissibleClass quotedRules) (channel : Proc)
    (echoMember : A.Admissible (.parL .hole (.echo channel)))
    (listenMember : A.Admissible (listenOn .nil)) :
    ¬ A.RelEquiv barbs (.out channel (.par .nil .nil)) (.out channel .nil) := by
  intro related
  obtain ⟨echoed, stepEcho, echoedRelated⟩ :=
    AdmissibleContextCongruence.bisimilar_forward related ⟨.parL .hole (.echo channel), echoMember⟩
      (Step.echo channel (.par .nil .nil) :
        Step ((Ctx.parL .hole (.echo channel)).fill (.out channel (.par .nil .nil)))
          (.out (.par .nil .nil) .nil))
  have echoedEq : echoed = .out .nil .nil := step_out_echo stepEcho
  subst echoedEq
  obtain ⟨_, stepListen, _⟩ :=
    AdmissibleContextCongruence.bisimilar_backward echoedRelated ⟨listenOn .nil, listenMember⟩
      (Step.receive .nil .nil .nil : Step ((listenOn .nil).fill (.out .nil .nil)) .nil)
  exact Proc.noConfusion (channel_eq_of_step_out_inp stepListen)

theorem not_relEquiv_out_channel_of_mem (A : AdmissibleClass quotedRules) (payload : Proc)
    (listenMember : A.Admissible (listenOn .nil)) :
    ¬ A.RelEquiv barbs (.out (.par .nil .nil) payload) (.out .nil payload) := by
  intro related
  obtain ⟨_, stepListen, _⟩ :=
    AdmissibleContextCongruence.bisimilar_backward related ⟨listenOn .nil, listenMember⟩
      (Step.receive .nil payload .nil : Step ((listenOn .nil).fill (.out .nil payload)) .nil)
  exact Proc.noConfusion (channel_eq_of_step_out_inp stepListen)

/-- An output on `nil` placed before the hole. -/
def sendNilBefore : Ctx := .parR (.out .nil .nil) .hole

theorem parallel_sendNilBefore : parallel.Admissible sendNilBefore := trivial

theorem not_relEquiv_inp_channel_of_mem (A : AdmissibleClass quotedRules) (body : Proc)
    (sendMember : A.Admissible sendNilBefore) :
    ¬ A.RelEquiv barbs (.inp (.par .nil .nil) body) (.inp .nil body) := by
  intro related
  obtain ⟨_, stepSend, _⟩ :=
    AdmissibleContextCongruence.bisimilar_backward related ⟨sendNilBefore, sendMember⟩
      (Step.receive .nil .nil body : Step (sendNilBefore.fill (.inp .nil body)) body)
  exact Proc.noConfusion (channel_eq_of_step_out_inp stepSend).symm

theorem not_relEquiv_echo_channel_of_mem (A : AdmissibleClass quotedRules)
    (sendMember : A.Admissible sendNilBefore) :
    ¬ A.RelEquiv barbs (.echo (.par .nil .nil)) (.echo .nil) := by
  intro related
  obtain ⟨_, stepSend, _⟩ :=
    AdmissibleContextCongruence.bisimilar_backward related ⟨sendNilBefore, sendMember⟩
      (Step.echo .nil .nil : Step (sendNilBefore.fill (.echo .nil)) (.out .nil .nil))
  cases stepSend with
  | parL _ inner => cases inner
  | parR _ inner => cases inner

/-! ## Input prefixes preserve the parallel equivalence -/

/-- A parallel filling of an input is never an output. -/
theorem parallel_fill_inp_ne_out {context : Ctx} (isParallel : context.Parallel)
    {channel body channel' payload : Proc} :
    context.fill (.inp channel body) ≠ .out channel' payload := by
  cases context with
  | hole => nofun
  | parL => nofun
  | parR => nofun
  | outChannel => exact (isParallel : False).elim
  | outPayload => exact (isParallel : False).elim
  | inpChannel => exact (isParallel : False).elim
  | inpBody => exact (isParallel : False).elim
  | echoChannel => exact (isParallel : False).elim

/-- A parallel filling of an input is never an echo. -/
theorem parallel_fill_inp_ne_echo {context : Ctx} (isParallel : context.Parallel)
    {channel body channel' : Proc} : context.fill (.inp channel body) ≠ .echo channel' := by
  cases context with
  | hole => nofun
  | parL => nofun
  | parR => nofun
  | outChannel => exact (isParallel : False).elim
  | outPayload => exact (isParallel : False).elim
  | inpChannel => exact (isParallel : False).elim
  | inpBody => exact (isParallel : False).elim
  | echoChannel => exact (isParallel : False).elim

/-- A parallel filling of an input that is itself an input is the hole. -/
theorem parallel_fill_inp_eq_inp {context : Ctx} (isParallel : context.Parallel)
    {channel body channel' body' : Proc}
    (equal : context.fill (.inp channel body) = .inp channel' body') :
    context = .hole ∧ channel = channel' ∧ body = body' := by
  cases context with
  | hole =>
      cases equal
      exact ⟨rfl, rfl, rfl⟩
  | parL => cases equal
  | parR => cases equal
  | outChannel => exact (isParallel : False).elim
  | outPayload => exact (isParallel : False).elim
  | inpChannel => exact (isParallel : False).elim
  | inpBody => exact (isParallel : False).elim
  | echoChannel => exact (isParallel : False).elim

theorem CtxStep.parallel {context context' : Ctx} (step : CtxStep context context')
    (isParallel : context.Parallel) : context'.Parallel := by
  induction step with
  | receive => exact (isParallel : False).elim
  | parLInner _ _ ih => exact ih isParallel
  | parRInner _ _ ih => exact ih isParallel
  | parLSibling => exact isParallel
  | parRSibling => exact isParallel

/-- **Decomposition for an input in a parallel context.**  A step either happens
beside the input, or delivers a message to it and releases its continuation. -/
theorem step_fill_inp {channel body : Proc} :
    ∀ (context : Ctx), context.Parallel → ∀ {target : Proc},
      Step (context.fill (.inp channel body)) target →
        (∃ context', CtxStep context context' ∧ target = context'.fill (.inp channel body)) ∨
        (∃ rest : Ctx, rest.Parallel ∧ target = rest.fill body ∧
          ∀ body', Step (context.fill (.inp channel body')) (rest.fill body')) := by
  intro context
  induction context with
  | hole =>
      intro _ target step
      exact absurd step (not_step_inp _ _ _)
  | parL inner right ih =>
      intro isParallel target step
      change Step (.par (inner.fill (.inp channel body)) right) target at step
      generalize filledEq : inner.fill (.inp channel body) = filled at step
      cases step with
      | receive => exact absurd filledEq (parallel_fill_inp_ne_out (context := inner) isParallel)
      | echo => exact absurd filledEq (parallel_fill_inp_ne_out (context := inner) isParallel)
      | parL _ innerStep =>
          subst filledEq
          rcases ih isParallel innerStep with ⟨inner', innerCtx, rfl⟩ | ⟨rest, restParallel, rfl, replay⟩
          · exact Or.inl ⟨.parL inner' right, .parLInner right innerCtx, rfl⟩
          · exact Or.inr ⟨.parL rest right, restParallel, rfl,
              fun body' => .parL right (replay body')⟩
      | parR _ siblingStep =>
          subst filledEq
          exact Or.inl ⟨.parL inner _, .parLSibling inner siblingStep, rfl⟩
  | parR left inner ih =>
      intro isParallel target step
      change Step (.par left (inner.fill (.inp channel body))) target at step
      generalize filledEq : inner.fill (.inp channel body) = filled at step
      cases step with
      | receive channel' payload body'' =>
          obtain ⟨rfl, rfl, rfl⟩ := parallel_fill_inp_eq_inp (context := inner) isParallel filledEq
          exact Or.inr ⟨.hole, trivial, rfl,
            fun body' => .receive channel payload body'⟩
      | echo => exact absurd filledEq (parallel_fill_inp_ne_echo (context := inner) isParallel)
      | parL _ siblingStep =>
          subst filledEq
          exact Or.inl ⟨.parR _ inner, .parRSibling inner siblingStep, rfl⟩
      | parR _ innerStep =>
          subst filledEq
          rcases ih isParallel innerStep with ⟨inner', innerCtx, rfl⟩ | ⟨rest, restParallel, rfl, replay⟩
          · exact Or.inl ⟨.parR left inner', .parRInner left innerCtx, rfl⟩
          · exact Or.inr ⟨.parR left rest, restParallel, rfl,
              fun body' => .parR left (replay body')⟩
  | outChannel => intro isParallel; exact (isParallel : False).elim
  | outPayload => intro isParallel; exact (isParallel : False).elim
  | inpChannel => intro isParallel; exact (isParallel : False).elim
  | inpBody => intro isParallel; exact (isParallel : False).elim
  | echoChannel => intro isParallel; exact (isParallel : False).elim

/-- Barbs of a parallel filling of an input do not depend on its continuation. -/
theorem barbed_fill_inp {context : Ctx} (isParallel : context.Parallel)
    (channel body body' : Proc) (barb : Barb) :
    Barbed (context.fill (.inp channel body)) barb ↔ Barbed (context.fill (.inp channel body')) barb := by
  induction context with
  | hole =>
      change Barbed (.inp channel body) barb ↔ Barbed (.inp channel body') barb
      constructor
      · intro barbed
        cases barbed
        exact .input _ _
      · intro barbed
        cases barbed
        exact .input _ _
  | parL inner right ih =>
      change Barbed (.par (inner.fill _) right) barb ↔ Barbed (.par (inner.fill _) right) barb
      rw [barbed_par_iff, barbed_par_iff, ih isParallel]
  | parR left inner ih =>
      change Barbed (.par left (inner.fill _)) barb ↔ Barbed (.par left (inner.fill _)) barb
      rw [barbed_par_iff, barbed_par_iff, ih isParallel]
  | outChannel => exact (isParallel : False).elim
  | outPayload => exact (isParallel : False).elim
  | inpChannel => exact (isParallel : False).elim
  | inpBody => exact (isParallel : False).elim
  | echoChannel => exact (isParallel : False).elim

/-- Pairs of parallel-equivalent terms, or parallel fillings of inputs on one
channel with parallel-equivalent continuations. -/
def inputPrefixed (left right : Proc) : Prop :=
  parallel.RelEquiv barbs left right ∨
    ∃ (context : Ctx) (channel body body' : Proc), context.Parallel ∧
      parallel.RelEquiv barbs body body' ∧
        left = context.fill (.inp channel body) ∧ right = context.fill (.inp channel body')

private theorem inputPrefixed_forward {left right : Proc} (related : inputPrefixed left right)
    {left' : Proc} (step : Step left left') :
    ∃ right', Step right right' ∧ inputPrefixed left' right' := by
  rcases related with equivalent | ⟨context, channel, body, body', isParallel, bodies, rfl, rfl⟩
  · obtain ⟨right', stepRight, related'⟩ :=
      (parallel.isReductionBisimulation_relEquiv barbs).1.1 equivalent step
    exact ⟨right', stepRight, Or.inl related'⟩
  · rcases step_fill_inp context isParallel step with
      ⟨context', contextStep, rfl⟩ | ⟨rest, restParallel, rfl, replay⟩
    · exact ⟨context'.fill (.inp channel body'), contextStep.step _,
        Or.inr ⟨context', channel, body, body', contextStep.parallel isParallel, bodies, rfl, rfl⟩⟩
    · exact ⟨rest.fill body', replay body',
        Or.inl (parallel.relEquiv_closedUnder barbs restParallel bodies)⟩

private theorem inputPrefixed_symm {left right : Proc} (related : inputPrefixed left right) :
    inputPrefixed right left := by
  rcases related with equivalent | ⟨context, channel, body, body', isParallel, bodies, rfl, rfl⟩
  · exact Or.inl (parallel.relEquiv_symm barbs equivalent)
  · exact Or.inr ⟨context, channel, body', body, isParallel,
      parallel.relEquiv_symm barbs bodies, rfl, rfl⟩

theorem inputPrefixed_isReductionBisimulation : IsReductionBisimulation barbs inputPrefixed := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro left right related left' step
    exact inputPrefixed_forward related step
  · intro left right related right' step
    obtain ⟨left', stepLeft, related'⟩ := inputPrefixed_forward (inputPrefixed_symm related) step
    exact ⟨left', stepLeft, inputPrefixed_symm related'⟩
  · intro left right related barb
    rcases related with equivalent | ⟨context, channel, body, body', isParallel, _, rfl, rfl⟩
    · exact (parallel.isReductionBisimulation_relEquiv barbs).2 equivalent barb
    · exact barbed_fill_inp isParallel channel body body' barb

theorem inputPrefixed_closedUnder : parallel.ClosedUnder inputPrefixed := by
  intro outer left right outerParallel related
  rcases related with equivalent | ⟨context, channel, body, body', isParallel, bodies, rfl, rfl⟩
  · exact Or.inl (parallel.relEquiv_closedUnder barbs outerParallel equivalent)
  · exact Or.inr ⟨outer.comp context, channel, body, body',
      Ctx.parallel_comp outerParallel isParallel, bodies,
      (Ctx.fill_comp outer context _).symm, (Ctx.fill_comp outer context _).symm⟩

/-- **Input prefixing preserves the parallel equivalence.** -/
theorem relEquiv_parallel_inp {body body' : Proc} (channel : Proc)
    (bodies : parallel.RelEquiv barbs body body') :
    parallel.RelEquiv barbs (.inp channel body) (.inp channel body') :=
  parallel.relEquiv_of_isReductionBisimulation barbs inputPrefixed_isReductionBisimulation
    inputPrefixed_closedUnder (Or.inr ⟨.hole, channel, body, body', trivial, bodies, rfl, rfl⟩)

/-! ## The determined class -/

/-- Every guarded context preserves the parallel equivalence. -/
theorem guarded_preserves_parallel {context : Ctx} (isGuarded : context.Guarded) :
    Preserves (rules := quotedRules) context (parallel.RelEquiv barbs) := by
  induction context with
  | hole => exact fun _ _ related => related
  | parL inner right ih =>
      intro left' right' related
      exact parallel.relEquiv_closedUnder barbs (context := .parL .hole right)
        (trivial : Ctx.Parallel (.parL .hole right)) (ih isGuarded related)
  | parR left inner ih =>
      intro left' right' related
      exact parallel.relEquiv_closedUnder barbs (context := .parR left .hole)
        (trivial : Ctx.Parallel (.parR left .hole)) (ih isGuarded related)
  | inpBody channel inner ih =>
      intro left' right' related
      exact relEquiv_parallel_inp channel (ih isGuarded related)
  | outChannel => exact (isGuarded : False).elim
  | outPayload => exact (isGuarded : False).elim
  | inpChannel => exact (isGuarded : False).elim
  | echoChannel => exact (isGuarded : False).elim

theorem dStar_admissible_iff (context : Ctx) :
    (dStar barbs mandatory).Admissible context ↔
      Preserves (rules := quotedRules) context (parallel.RelEquiv barbs) := by
  change Preserves (rules := quotedRules) context ((generatedBy mandatory).RelEquiv barbs) ↔ _
  rw [generatedBy_mandatory_eq_parallel]

/-- **The determined class contains every guarded context.** -/
theorem guarded_le_dStar : guarded ≤ dStar barbs mandatory :=
  fun _ isGuarded => (dStar_admissible_iff _).mpr (guarded_preserves_parallel isGuarded)

/-- **The guarded equivalence is the one fixed by parallel interaction.** -/
theorem relEquiv_guarded_iff_equivStar (left right : Proc) :
    guarded.RelEquiv barbs left right ↔ equivStar barbs mandatory left right := by
  have below : generatedBy mandatory ≤ guarded := by
    rw [generatedBy_mandatory_eq_parallel]
    exact parallel_le_guarded
  exact (relEquiv_iff_iff_le_determined barbs below).mpr guarded_le_dStar left right

theorem equivStar_parNil_nil : equivStar barbs mandatory (.par .nil .nil) .nil :=
  (relEquiv_guarded_iff_equivStar _ _).mp relEquiv_guarded_parNil_nil

/-- **Output payloads are excluded.** -/
theorem outPayload_not_mem_dStar (channel : Proc) :
    ¬ (dStar barbs mandatory).Admissible (.outPayload channel .hole) := by
  intro preserves
  have image := ((dStar_admissible_iff _).mp preserves)
    ((equivStar_iff _ _).mp equivStar_parNil_nil)
  exact not_relEquiv_out_payload_of_mem parallel channel trivial (parallel_listenOn .nil) image

/-- **Output channels are excluded.** -/
theorem outChannel_not_mem_dStar (payload : Proc) :
    ¬ (dStar barbs mandatory).Admissible (.outChannel .hole payload) := by
  intro preserves
  have image := ((dStar_admissible_iff _).mp preserves)
    ((equivStar_iff _ _).mp equivStar_parNil_nil)
  exact not_relEquiv_out_channel_of_mem parallel payload (parallel_listenOn .nil) image

/-- **Input channels are excluded.** -/
theorem inpChannel_not_mem_dStar (body : Proc) :
    ¬ (dStar barbs mandatory).Admissible (.inpChannel .hole body) := by
  intro preserves
  have image := ((dStar_admissible_iff _).mp preserves)
    ((equivStar_iff _ _).mp equivStar_parNil_nil)
  exact not_relEquiv_inp_channel_of_mem parallel body parallel_sendNilBefore image

/-- **Echo channels are excluded.** -/
theorem echoChannel_not_mem_dStar :
    ¬ (dStar barbs mandatory).Admissible (.echoChannel .hole) := by
  intro preserves
  have image := ((dStar_admissible_iff _).mp preserves)
    ((equivStar_iff _ _).mp equivStar_parNil_nil)
  exact not_relEquiv_echo_channel_of_mem parallel parallel_sendNilBefore image

/-! ## Two fixed points -/

/-- The top class is a fixed point whose equivalence is syntactic identity. -/
theorem top_fixed_point :
    (⊤ : AdmissibleClass quotedRules).determined barbs = ⊤ ∧
      ∀ left right, (⊤ : AdmissibleClass quotedRules).RelEquiv barbs left right ↔ left = right :=
  ⟨determined_top barbs, relEquiv_top_iff_eq⟩

/-- **The two fixed points are incomparable** when classes and relations are
both ordered by inclusion: the determined class is smaller than the top class,
and its equivalence is larger. -/
theorem fixed_points_incomparable :
    (dStar barbs mandatory).determined barbs = dStar barbs mandatory ∧
      (⊤ : AdmissibleClass quotedRules).determined barbs = ⊤ ∧
      ¬ ((⊤ : AdmissibleClass quotedRules) ≤ dStar barbs mandatory) ∧
      ¬ (∀ left right, (dStar barbs mandatory).RelEquiv barbs left right →
          (⊤ : AdmissibleClass quotedRules).RelEquiv barbs left right) := by
  refine ⟨dStar_determined barbs mandatory, determined_top barbs, ?_, ?_⟩
  · intro le
    exact outPayload_not_mem_dStar .nil (le _ (top_admissible _))
  · intro included
    have related := included _ _
      ((relEquiv_dStar_iff barbs mandatory).mpr equivStar_parNil_nil)
    exact Proc.noConfusion ((relEquiv_top_iff_eq _ _).mp related)

/-! ## Adding observers: conservative and strict -/

/-- Input continuations, as one-layer contexts. -/
def inputBodies : Set quotedRules.Context :=
  {context | ∃ channel, context = Ctx.inpBody channel Ctx.hole}

/-- Output payloads, as one-layer contexts. -/
def outputPayloads : Set quotedRules.Context :=
  {context | ∃ channel, context = Ctx.outPayload channel Ctx.hole}

/-- **Conservative extension.**  Adjoining input continuations to the parallel
observers leaves the equivalence unchanged, because each of them preserves it. -/
theorem parallel_sup_inputBodies_conservative (left right : Proc) :
    (parallel ⊔ generatedBy inputBodies).RelEquiv barbs left right ↔
      parallel.RelEquiv barbs left right :=
  (parallel.relEquiv_sup_generatedBy_iff barbs inputBodies).mpr
    (by
      rintro _ ⟨channel, rfl⟩
      exact guarded_preserves_parallel (context := Ctx.inpBody channel Ctx.hole) trivial)
    left right

/-- **Strict extension.**  Adjoining output payloads separates a pair the
parallel observers identify, because a payload position does not preserve the
parallel equivalence. -/
theorem parallel_sup_outputPayloads_strict :
    parallel.RelEquiv barbs (.par .nil .nil) .nil ∧
      ¬ (parallel ⊔ generatedBy outputPayloads).RelEquiv barbs (.par .nil .nil) .nil :=
  ⟨(equivStar_iff _ _).mp equivStar_parNil_nil,
    parallel.not_relEquiv_sup_of_not_preserved barbs (added := outputPayloads)
      (context := Ctx.outPayload .nil .hole) ⟨.nil, rfl⟩ (not_relEquiv_out_payload_of_mem parallel .nil trivial (parallel_listenOn .nil))⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel
