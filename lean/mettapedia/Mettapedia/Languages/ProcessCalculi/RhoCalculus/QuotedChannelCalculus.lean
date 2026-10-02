import Mettapedia.GSLT.Logic.ObserverDetermination

/-!
# A quoted-channel calculus: which positions may observe a process

A small reflective calculus.  Channels are processes, compared by syntactic
identity, as quoted processes are in rho.  An output sends a payload; an input
discards what it receives and continues; an *echo* receiver turns the payload
it receives into the channel of a fresh output, which is what an input
`for (x <- c) x!(0)` does in rho.

Three admissible classes of one-hole contexts are compared:

* `guarded`: holes reached only through parallel composition and input
  continuations;
* `quoteFree`: additionally output payloads — the positions the rho module
  `AdmissibleContexts.QuoteFreePath` admits;
* `⊤`: every position, channels included.

Results:

* **positive control** (`relEquiv_guarded_of_passive`): any two processes
  built from `nil` and parallel composition are `guarded`-equivalent; in
  particular `nil ∣ nil` and `nil`;
* **a payload position is a delayed quote** (`relEquiv_quoteFree_iff_eq`): once
  payload positions are admissible, the relative equivalence collapses to
  syntactic identity, because any process can be sent to an echo and then
  compared as a channel.  The same holds for `⊤` (`relEquiv_top_iff_eq`);
* **equal for one class, distinct for a richer one**
  (`guarded_equal_quoteFree_distinct`);
* **congruence fails beyond the class** (`not_guarded_closedUnder_payload`,
  `not_guarded_closedUnder_channel`): an output payload or an output channel
  maps a `guarded`-equivalent pair to a pair `guarded` observers separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass

/-! ## Syntax and reduction -/

/-- Processes.  Channels are processes compared by identity. -/
inductive Proc where
  | nil : Proc
  | par (left right : Proc) : Proc
  /-- Send `payload` on the channel quoting `channel`. -/
  | out (channel payload : Proc) : Proc
  /-- Receive on `channel`, discard the payload, continue as `body`. -/
  | inp (channel body : Proc) : Proc
  /-- Receive a payload on `channel` and send `nil` on the payload. -/
  | echo (channel : Proc) : Proc
  deriving DecidableEq

/-- One reduction step.  Communication requires identical channels. -/
inductive Step : Proc → Proc → Prop where
  | receive (channel payload body : Proc) :
      Step (.par (.out channel payload) (.inp channel body)) body
  | echo (channel payload : Proc) :
      Step (.par (.out channel payload) (.echo channel)) (.out payload .nil)
  | parL {left left' : Proc} (right : Proc) :
      Step left left' → Step (.par left right) (.par left' right)
  | parR (left : Proc) {right right' : Proc} :
      Step right right' → Step (.par left right) (.par left right')

theorem not_step_nil (target : Proc) : ¬ Step .nil target := nofun

theorem not_step_out (channel payload target : Proc) : ¬ Step (.out channel payload) target :=
  nofun

theorem not_step_inp (channel body target : Proc) : ¬ Step (.inp channel body) target := nofun

theorem not_step_echo (channel target : Proc) : ¬ Step (.echo channel) target := nofun

/-- The only step of an output beside an echo on its channel. -/
theorem step_out_echo {channel payload target : Proc}
    (step : Step (.par (.out channel payload) (.echo channel)) target) :
    target = .out payload .nil := by
  cases step with
  | echo => rfl
  | parL _ inner => cases inner
  | parR _ inner => cases inner

/-- An output beside an input steps only when the channels are identical. -/
theorem channel_eq_of_step_out_inp {channel channel' payload body target : Proc}
    (step : Step (.par (.out channel payload) (.inp channel' body)) target) :
    channel = channel' := by
  cases step with
  | receive => rfl
  | parL _ inner => cases inner
  | parR _ inner => cases inner

/-- Observations: an output or input capability on a channel, at top level. -/
inductive Barb where
  | output (channel : Proc)
  | input (channel : Proc)

/-- A process shows a barb when some parallel component offers it. -/
inductive Barbed : Proc → Barb → Prop where
  | output (channel payload : Proc) : Barbed (.out channel payload) (.output channel)
  | input (channel body : Proc) : Barbed (.inp channel body) (.input channel)
  | echo (channel : Proc) : Barbed (.echo channel) (.input channel)
  | parL {left : Proc} (right : Proc) {barb : Barb} :
      Barbed left barb → Barbed (.par left right) barb
  | parR (left : Proc) {right : Proc} {barb : Barb} :
      Barbed right barb → Barbed (.par left right) barb

theorem barbed_par_iff {left right : Proc} {barb : Barb} :
    Barbed (.par left right) barb ↔ Barbed left barb ∨ Barbed right barb := by
  constructor
  · intro barbed
    cases barbed with
    | parL _ inner => exact Or.inl inner
    | parR _ inner => exact Or.inr inner
  · rintro (inner | inner)
    · exact .parL _ inner
    · exact .parR _ inner

/-! ## Contexts -/

/-- One-hole contexts, with the hole in any position. -/
inductive Ctx where
  | hole : Ctx
  | parL (context : Ctx) (right : Proc) : Ctx
  | parR (left : Proc) (context : Ctx) : Ctx
  /-- The hole is the channel of an output: under a quote. -/
  | outChannel (context : Ctx) (payload : Proc) : Ctx
  /-- The hole is the payload of an output. -/
  | outPayload (channel : Proc) (context : Ctx) : Ctx
  /-- The hole is the channel of an input: under a quote. -/
  | inpChannel (context : Ctx) (body : Proc) : Ctx
  /-- The hole is the continuation of an input. -/
  | inpBody (channel : Proc) (context : Ctx) : Ctx
  /-- The hole is the channel of an echo: under a quote. -/
  | echoChannel (context : Ctx) : Ctx
  deriving DecidableEq

namespace Ctx

/-- Filling the hole. -/
def fill : Ctx → Proc → Proc
  | .hole, term => term
  | .parL context right, term => .par (context.fill term) right
  | .parR left context, term => .par left (context.fill term)
  | .outChannel context payload, term => .out (context.fill term) payload
  | .outPayload channel context, term => .out channel (context.fill term)
  | .inpChannel context body, term => .inp (context.fill term) body
  | .inpBody channel context, term => .inp channel (context.fill term)
  | .echoChannel context, term => .echo (context.fill term)

/-- Placing `inner` in the hole of `outer`. -/
def comp : Ctx → Ctx → Ctx
  | .hole, inner => inner
  | .parL context right, inner => .parL (context.comp inner) right
  | .parR left context, inner => .parR left (context.comp inner)
  | .outChannel context payload, inner => .outChannel (context.comp inner) payload
  | .outPayload channel context, inner => .outPayload channel (context.comp inner)
  | .inpChannel context body, inner => .inpChannel (context.comp inner) body
  | .inpBody channel context, inner => .inpBody channel (context.comp inner)
  | .echoChannel context, inner => .echoChannel (context.comp inner)

theorem fill_comp (outer inner : Ctx) (term : Proc) :
    (outer.comp inner).fill term = outer.fill (inner.fill term) := by
  induction outer with
  | hole => rfl
  | parL _ _ ih => simp [comp, fill, ih]
  | parR _ _ ih => simp [comp, fill, ih]
  | outChannel _ _ ih => simp [comp, fill, ih]
  | outPayload _ _ ih => simp [comp, fill, ih]
  | inpChannel _ _ ih => simp [comp, fill, ih]
  | inpBody _ _ ih => simp [comp, fill, ih]
  | echoChannel _ ih => simp [comp, fill, ih]

/-- The hole is reached through parallel composition and input continuations
only. -/
def Guarded : Ctx → Prop
  | .hole => True
  | .parL context _ => context.Guarded
  | .parR _ context => context.Guarded
  | .inpBody _ context => context.Guarded
  | _ => False

/-- The hole never sits in a channel position; output payloads are allowed. -/
def QuoteFree : Ctx → Prop
  | .hole => True
  | .parL context _ => context.QuoteFree
  | .parR _ context => context.QuoteFree
  | .outPayload _ context => context.QuoteFree
  | .inpBody _ context => context.QuoteFree
  | _ => False

theorem guarded_comp {outer inner : Ctx} (outerGuarded : outer.Guarded)
    (innerGuarded : inner.Guarded) : (outer.comp inner).Guarded := by
  induction outer with
  | hole => exact innerGuarded
  | parL _ _ ih => exact ih outerGuarded
  | parR _ _ ih => exact ih outerGuarded
  | inpBody _ _ ih => exact ih outerGuarded
  | outChannel => exact outerGuarded.elim
  | outPayload => exact outerGuarded.elim
  | inpChannel => exact outerGuarded.elim
  | echoChannel => exact outerGuarded.elim

theorem quoteFree_comp {outer inner : Ctx} (outerFree : outer.QuoteFree)
    (innerFree : inner.QuoteFree) : (outer.comp inner).QuoteFree := by
  induction outer with
  | hole => exact innerFree
  | parL _ _ ih => exact ih outerFree
  | parR _ _ ih => exact ih outerFree
  | outPayload _ _ ih => exact ih outerFree
  | inpBody _ _ ih => exact ih outerFree
  | outChannel => exact outerFree.elim
  | inpChannel => exact outerFree.elim
  | echoChannel => exact outerFree.elim

theorem Guarded.quoteFree {context : Ctx} (guarded : context.Guarded) : context.QuoteFree := by
  induction context with
  | hole => trivial
  | parL _ _ ih => exact ih guarded
  | parR _ _ ih => exact ih guarded
  | inpBody _ _ ih => exact ih guarded
  | outChannel => exact guarded.elim
  | outPayload => exact guarded.elim
  | inpChannel => exact guarded.elim
  | echoChannel => exact guarded.elim

end Ctx

/-! ## The calculus as a GSLT with contextual rules -/

abbrev quotedGSLT : GSLT where
  Term := Proc
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

abbrev quotedRules : ContextualRules quotedGSLT where
  Context := Ctx
  identity := .hole
  compose := Ctx.comp
  plug := Ctx.fill
  plug_identity _ := rfl
  plug_compose := Ctx.fill_comp
  plug_resp context := by
    intro left right equal
    subst equal
    rfl
  Rule := Unit
  fires _ := Step
  fires_resp_left := by
    intro _ left right target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ source target target' fires equal
    subst equal
    exact fires
  fires_step := fun fires => fires

/-- Barbs as observations. -/
abbrev barbs : ContextualRules.Observations quotedGSLT where
  Atom := Barb
  observes barb term := Barbed term barb
  observes_resp := by
    intro _ left right equal
    subst equal
    exact Iff.rfl

/-- Parallel composition and input continuations. -/
def guarded : AdmissibleClass quotedRules where
  Admissible := Ctx.Guarded
  identity_mem := trivial
  compose_mem := Ctx.guarded_comp

/-- Every position except channels. -/
def quoteFree : AdmissibleClass quotedRules where
  Admissible := Ctx.QuoteFree
  identity_mem := trivial
  compose_mem := Ctx.quoteFree_comp

theorem guarded_le_quoteFree : guarded ≤ quoteFree := fun _ guarded => guarded.quoteFree

/-! ## Passive processes are bystanders in guarded contexts -/

/-- Processes built from `nil` and parallel composition. -/
inductive Passive : Proc → Prop where
  | nil : Passive .nil
  | par {left right : Proc} : Passive left → Passive right → Passive (.par left right)

theorem Passive.not_step {term target : Proc} (passive : Passive term) : ¬ Step term target := by
  induction passive generalizing target with
  | nil => exact not_step_nil target
  | par leftPassive _ ihLeft ihRight =>
      intro step
      cases step with
      | receive => cases leftPassive
      | echo => cases leftPassive
      | parL _ inner => exact ihLeft inner
      | parR _ inner => exact ihRight inner

theorem Passive.not_barbed {term : Proc} (passive : Passive term) (barb : Barb) :
    ¬ Barbed term barb := by
  induction passive with
  | nil => nofun
  | par _ _ ihLeft ihRight =>
      intro barbed
      rcases barbed_par_iff.mp barbed with inner | inner
      · exact ihLeft inner
      · exact ihRight inner

/-- A step of a guarded context around any filling. -/
inductive CtxStep : Ctx → Ctx → Prop where
  | receive (channel payload : Proc) (body : Ctx) :
      CtxStep (.parR (.out channel payload) (.inpBody channel body)) body
  | parLInner {context context' : Ctx} (right : Proc) :
      CtxStep context context' → CtxStep (.parL context right) (.parL context' right)
  | parRInner (left : Proc) {context context' : Ctx} :
      CtxStep context context' → CtxStep (.parR left context) (.parR left context')
  | parLSibling (context : Ctx) {right right' : Proc} :
      Step right right' → CtxStep (.parL context right) (.parL context right')
  | parRSibling {left left' : Proc} (context : Ctx) :
      Step left left' → CtxStep (.parR left context) (.parR left' context)

theorem CtxStep.step {context context' : Ctx} (step : CtxStep context context') (term : Proc) :
    Step (context.fill term) (context'.fill term) := by
  induction step with
  | receive channel payload body => exact .receive channel payload (body.fill term)
  | parLInner right _ ih => exact .parL right ih
  | parRInner left _ ih => exact .parR left ih
  | parLSibling context inner => exact .parR (context.fill term) inner
  | parRSibling context inner => exact .parL (context.fill term) inner

theorem CtxStep.guarded {context context' : Ctx} (step : CtxStep context context')
    (guarded : context.Guarded) : context'.Guarded := by
  induction step with
  | receive _ _ body => exact guarded
  | parLInner _ _ ih => exact ih guarded
  | parRInner _ _ ih => exact ih guarded
  | parLSibling => exact guarded
  | parRSibling => exact guarded

/-- A guarded filling of a passive process is never an output. -/
theorem fill_ne_out {context : Ctx} (guarded : context.Guarded) {term : Proc}
    (passive : Passive term) (channel payload : Proc) :
    context.fill term ≠ .out channel payload := by
  cases context with
  | hole =>
      intro equal
      change term = .out channel payload at equal
      subst equal
      cases passive
  | parL => nofun
  | parR => nofun
  | inpBody => nofun
  | outChannel => exact guarded.elim
  | outPayload => exact guarded.elim
  | inpChannel => exact guarded.elim
  | echoChannel => exact guarded.elim

/-- A guarded filling of a passive process is never an echo. -/
theorem fill_ne_echo {context : Ctx} (guarded : context.Guarded) {term : Proc}
    (passive : Passive term) (channel : Proc) : context.fill term ≠ .echo channel := by
  cases context with
  | hole =>
      intro equal
      change term = .echo channel at equal
      subst equal
      cases passive
  | parL => nofun
  | parR => nofun
  | inpBody => nofun
  | outChannel => exact guarded.elim
  | outPayload => exact guarded.elim
  | inpChannel => exact guarded.elim
  | echoChannel => exact guarded.elim

/-- A guarded filling of a passive process that is an input is an input
continuation context. -/
theorem fill_eq_inp {context : Ctx} (guarded : context.Guarded) {term : Proc}
    (passive : Passive term) {channel body : Proc}
    (equal : context.fill term = .inp channel body) :
    ∃ inner, context = .inpBody channel inner ∧ body = inner.fill term := by
  cases context with
  | hole =>
      change term = .inp channel body at equal
      subst equal
      cases passive
  | parL => cases equal
  | parR => cases equal
  | inpBody channel' inner =>
      cases equal
      exact ⟨inner, rfl, rfl⟩
  | outChannel => exact guarded.elim
  | outPayload => exact guarded.elim
  | inpChannel => exact guarded.elim
  | echoChannel => exact guarded.elim

/-- **Decomposition.**  Every step of a guarded context filled with a passive
process is a step of the context alone. -/
theorem step_fill_passive {term : Proc} (passive : Passive term) :
    ∀ (context : Ctx), context.Guarded → ∀ {target : Proc}, Step (context.fill term) target →
      ∃ context', CtxStep context context' ∧ target = context'.fill term := by
  intro context
  induction context with
  | hole =>
      intro _ target step
      exact absurd step passive.not_step
  | parL inner right ih =>
      intro guarded target step
      change Step (.par (inner.fill term) right) target at step
      generalize filledEq : inner.fill term = filled at step
      cases step with
      | receive channel payload body =>
          exact absurd filledEq (fill_ne_out (context := inner) guarded passive _ _)
      | echo channel payload =>
          exact absurd filledEq (fill_ne_out (context := inner) guarded passive _ _)
      | parL _ innerStep =>
          subst filledEq
          obtain ⟨inner', innerCtx, rfl⟩ := ih guarded innerStep
          exact ⟨.parL inner' right, .parLInner right innerCtx, rfl⟩
      | parR _ siblingStep =>
          subst filledEq
          exact ⟨.parL inner _, .parLSibling inner siblingStep, rfl⟩
  | parR left inner ih =>
      intro guarded target step
      change Step (.par left (inner.fill term)) target at step
      generalize filledEq : inner.fill term = filled at step
      cases step with
      | receive channel payload body =>
          obtain ⟨innermost, rfl, rfl⟩ := fill_eq_inp (context := inner) guarded passive filledEq
          exact ⟨innermost, .receive channel payload innermost, rfl⟩
      | echo channel payload =>
          exact absurd filledEq (fill_ne_echo (context := inner) guarded passive _)
      | parL _ siblingStep =>
          subst filledEq
          exact ⟨.parR _ inner, .parRSibling inner siblingStep, rfl⟩
      | parR _ innerStep =>
          subst filledEq
          obtain ⟨inner', innerCtx, rfl⟩ := ih guarded innerStep
          exact ⟨.parR left inner', .parRInner left innerCtx, rfl⟩
  | inpBody channel inner _ =>
      intro _ target step
      exact absurd step (not_step_inp _ _ _)
  | outChannel => intro guarded; exact (guarded : False).elim
  | outPayload => intro guarded; exact (guarded : False).elim
  | inpChannel => intro guarded; exact (guarded : False).elim
  | echoChannel => intro guarded; exact (guarded : False).elim

/-- Barbs of a guarded filling do not depend on which passive process fills it. -/
theorem barbed_fill_passive {context : Ctx} (guarded : context.Guarded) {term term' : Proc}
    (passive : Passive term) (passive' : Passive term') (barb : Barb) :
    Barbed (context.fill term) barb ↔ Barbed (context.fill term') barb := by
  induction context with
  | hole =>
      exact ⟨fun barbed => absurd barbed (passive.not_barbed barb),
        fun barbed => absurd barbed (passive'.not_barbed barb)⟩
  | parL inner right ih =>
      change Barbed (.par (inner.fill term) right) barb ↔ Barbed (.par (inner.fill term') right) barb
      rw [barbed_par_iff, barbed_par_iff, ih guarded]
  | parR left inner ih =>
      change Barbed (.par left (inner.fill term)) barb ↔ Barbed (.par left (inner.fill term')) barb
      rw [barbed_par_iff, barbed_par_iff, ih guarded]
  | inpBody channel inner _ =>
      change Barbed (.inp channel (inner.fill term)) barb ↔ Barbed (.inp channel (inner.fill term')) barb
      constructor
      · intro barbed
        cases barbed
        exact .input _ _
      · intro barbed
        cases barbed
        exact .input _ _
  | outChannel => exact guarded.elim
  | outPayload => exact guarded.elim
  | inpChannel => exact guarded.elim
  | echoChannel => exact guarded.elim

/-- Guarded fillings with passive processes. -/
def passiveFillings (left right : Proc) : Prop :=
  ∃ (context : Ctx) (term term' : Proc), context.Guarded ∧ Passive term ∧ Passive term' ∧
    left = context.fill term ∧ right = context.fill term'

theorem passiveFillings_isReductionBisimulation :
    IsReductionBisimulation barbs passiveFillings := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ _ ⟨context, term, term', guarded, passive, passive', rfl, rfl⟩ target step
    obtain ⟨context', contextStep, rfl⟩ := step_fill_passive passive _ guarded step
    exact ⟨context'.fill term', contextStep.step term',
      context', term, term', contextStep.guarded guarded, passive, passive', rfl, rfl⟩
  · rintro _ _ ⟨context, term, term', guarded, passive, passive', rfl, rfl⟩ target step
    obtain ⟨context', contextStep, rfl⟩ := step_fill_passive passive' _ guarded step
    exact ⟨context'.fill term, contextStep.step term,
      context', term, term', contextStep.guarded guarded, passive, passive', rfl, rfl⟩
  · rintro _ _ ⟨context, term, term', guarded, passive, passive', rfl, rfl⟩ barb
    exact barbed_fill_passive guarded passive passive' barb

theorem passiveFillings_closedUnder : guarded.ClosedUnder passiveFillings := by
  rintro outer _ _ outerGuarded ⟨context, term, term', guarded, passive, passive', rfl, rfl⟩
  exact ⟨outer.comp context, term, term', Ctx.guarded_comp outerGuarded guarded, passive,
    passive', (Ctx.fill_comp outer context term).symm, (Ctx.fill_comp outer context term').symm⟩

/-- **Positive control.**  Any two passive processes are `guarded`-equivalent. -/
theorem relEquiv_guarded_of_passive {term term' : Proc} (passive : Passive term)
    (passive' : Passive term') : guarded.RelEquiv barbs term term' :=
  guarded.relEquiv_of_isReductionBisimulation barbs passiveFillings_isReductionBisimulation
    passiveFillings_closedUnder ⟨.hole, term, term', trivial, passive, passive', rfl, rfl⟩

/-- In particular `nil ∣ nil` and `nil`. -/
theorem relEquiv_guarded_parNil_nil : guarded.RelEquiv barbs (.par .nil .nil) .nil :=
  relEquiv_guarded_of_passive (.par .nil .nil) .nil

/-! ## A payload position is a delayed quote -/

/-- Send the hole to an echo on `nil`. -/
def echoPayload : Ctx := .parL (.outPayload .nil .hole) (.echo .nil)

/-- Listen on the channel `channel`. -/
def listenOn (channel : Proc) : Ctx := .parL .hole (.inp channel .nil)

theorem echoPayload_quoteFree : echoPayload.QuoteFree := trivial

theorem listenOn_guarded (channel : Proc) : (listenOn channel).Guarded := trivial

/-- **Collapse.**  With payload positions admissible, two processes are
equivalent only when they are identical: sent to an echo, a process becomes
a channel, and a listener on that channel tells it from every other process. -/
theorem eq_of_relEquiv_quoteFree {left right : Proc}
    (related : quoteFree.RelEquiv barbs left right) : left = right := by
  obtain ⟨echoedRight, stepRight, echoedRelated⟩ :=
    AdmissibleContextCongruence.bisimilar_forward related ⟨echoPayload, echoPayload_quoteFree⟩
      (Step.echo .nil left : Step (echoPayload.fill left) (.out left .nil))
  have echoed : echoedRight = .out right .nil := step_out_echo stepRight
  subst echoed
  obtain ⟨_, stepListen, _⟩ :=
    AdmissibleContextCongruence.bisimilar_forward echoedRelated
      ⟨listenOn left, (listenOn_guarded left).quoteFree⟩
      (Step.receive left .nil .nil : Step ((listenOn left).fill (.out left .nil)) .nil)
  exact (channel_eq_of_step_out_inp stepListen).symm

theorem relEquiv_quoteFree_iff_eq (left right : Proc) :
    quoteFree.RelEquiv barbs left right ↔ left = right :=
  ⟨eq_of_relEquiv_quoteFree, fun equal => by subst equal; exact quoteFree.relEquiv_refl barbs left⟩

/-- The same collapse for every position. -/
theorem relEquiv_top_iff_eq (left right : Proc) :
    (⊤ : AdmissibleClass quotedRules).RelEquiv barbs left right ↔ left = right :=
  ⟨fun related => eq_of_relEquiv_quoteFree
      (AdmissibleClass.relEquiv_antitone barbs le_top related),
    fun equal => by subst equal; exact (⊤ : AdmissibleClass quotedRules).relEquiv_refl barbs left⟩

/-- **Equal for one class, distinct for a richer one.** -/
theorem guarded_equal_quoteFree_distinct :
    guarded ≤ quoteFree ∧ guarded.RelEquiv barbs (.par .nil .nil) .nil ∧
      ¬ quoteFree.RelEquiv barbs (.par .nil .nil) .nil :=
  ⟨guarded_le_quoteFree, relEquiv_guarded_parNil_nil,
    fun related => Proc.noConfusion (eq_of_relEquiv_quoteFree related)⟩

/-! ## Congruence fails beyond the class -/

/-- Sent to an echo and then heard on `nil`, an output whose payload is `nil`
communicates; one whose payload is `nil ∣ nil` does not.  Only guarded
observers are used. -/
theorem not_guarded_relEquiv_out_payload (channel : Proc) :
    ¬ guarded.RelEquiv barbs (.out channel (.par .nil .nil)) (.out channel .nil) := by
  intro related
  obtain ⟨echoed, stepEcho, echoedRelated⟩ :=
    AdmissibleContextCongruence.bisimilar_forward related
      ⟨.parL .hole (.echo channel), (trivial : Ctx.Guarded (.parL .hole (.echo channel)))⟩
      (Step.echo channel (.par .nil .nil) :
        Step ((Ctx.parL .hole (.echo channel)).fill (.out channel (.par .nil .nil)))
          (.out (.par .nil .nil) .nil))
  have echoedEq : echoed = .out .nil .nil := step_out_echo stepEcho
  subst echoedEq
  obtain ⟨_, stepListen, _⟩ :=
    AdmissibleContextCongruence.bisimilar_backward echoedRelated ⟨listenOn .nil, trivial⟩
      (Step.receive .nil .nil .nil : Step ((listenOn .nil).fill (.out .nil .nil)) .nil)
  exact Proc.noConfusion (channel_eq_of_step_out_inp stepListen)

/-- A listener on `nil` tells an output on `nil` from an output on `nil ∣ nil`. -/
theorem not_guarded_relEquiv_out_channel (payload : Proc) :
    ¬ guarded.RelEquiv barbs (.out (.par .nil .nil) payload) (.out .nil payload) := by
  intro related
  obtain ⟨_, stepListen, _⟩ :=
    AdmissibleContextCongruence.bisimilar_backward related ⟨listenOn .nil, trivial⟩
      (Step.receive .nil payload .nil : Step ((listenOn .nil).fill (.out .nil payload)) .nil)
  exact Proc.noConfusion (channel_eq_of_step_out_inp stepListen)

/-- **Congruence fails at output payloads.**  The payload position is
admissible for `quoteFree`, and it maps the `guarded`-equivalent pair
`nil ∣ nil`, `nil` to a pair that guarded observers separate. -/
theorem not_guarded_closedUnder_payload : ¬ quoteFree.ClosedUnder (guarded.RelEquiv barbs) :=
  fun closed => not_guarded_relEquiv_out_payload .nil
    (closed (context := .outPayload .nil .hole) trivial relEquiv_guarded_parNil_nil)

/-- **Congruence fails at channels.** -/
theorem not_guarded_closedUnder_channel :
    ¬ (⊤ : AdmissibleClass quotedRules).ClosedUnder (guarded.RelEquiv barbs) :=
  fun closed => not_guarded_relEquiv_out_channel .nil
    (closed (context := .outChannel .hole .nil) (top_admissible _) relEquiv_guarded_parNil_nil)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel
