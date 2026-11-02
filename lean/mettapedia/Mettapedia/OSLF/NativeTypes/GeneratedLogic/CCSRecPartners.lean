import Mettapedia.Languages.ProcessCalculi.CCS.LabelledBisimilarity
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms

/-!
# Least partners of CCS with recursion, at the front door

The front door reads `ccsRecCalc` modulo its static theory, and its plain steps are reductions (`Reduces`). The
labelled transitions are recovered from reductions beside least partners.

- **A reduction is a silent transition**, up to the canonical form (`reduces_iff_tau`): a raw step is a silent
  transition (`tau_of_raw`), the static theory matches transitions (`matched_of_procEquiv`), and a silent transition is
  a step of the canonical form (`harmony`).
- **Least partners** (`reduces_coPartner_iff`, `reduces_partner_iff`): a process performs an action on a channel to a
  residual exactly when, beside the least partner `~a.k.0`, it reduces to the residual beside the sentinel `k.0`, `k`
  a name it does not use; and dually for co-actions beside `a.k.0`. A reduction leaving the partner standing keeps it,
  and the partner has no action on `k`, while the sentinel has one.
- **Least-partner bisimilarity is strong bisimilarity** (`leastPartnerBisimilar_iff`): the largest relation whose
  reductions, alone and beside every least partner with a fresh sentinel, are matched to related residuals is strong
  bisimilarity of the labelled transitions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartners

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)
open Mettapedia.Languages.ProcessCalculi.CCS.Recursive
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms (reading domain typed_of_domain domain_of_typed names
  names_context domain_iff_of_equivalent equationEquiv_of_objectEquivalent objectEquivalent_of_sortedEquiv
  reference_iff_raw)

variable {definitions : List Definition}

/-! ## Processes and reductions -/

/-- The block canonical form. -/
abbrev blockCanon (term : Pattern) : Pattern := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon ccsBlock term

/-- **The front door of CCS with recursion**, in the environment of the definitions. -/
abbrev frontDoor (definitions : List Definition) : NativeStructure Pattern :=
  referenceStructure (definitionsEnv definitions) ccsRecCalc reading

/-- The processes: object processes with no free bound variable, their free variables names. -/
abbrev processes (term : Pattern) : Prop := domain term = true

/-- **A reduction**: a plain step of the front door, a step of `ccsRecCalc` modulo its static theory. -/
def Reduces (definitions : List Definition) (source target : Pattern) : Prop :=
  (frontDoor definitions).step source .any target

/-- Parallel composition, as a bag of two. -/
def par (first second : Pattern) : Pattern := .collection .hashBag [first, second] none

theorem isState_of_process {term : Pattern} (admitted : processes term) : IsState term :=
  ⟨by simpa using (typed_of_domain admitted).1.isWellScopedAt, (typed_of_domain admitted).2⟩

theorem par_process {first second : Pattern} (firstIn : processes first) (secondIn : processes second) :
    processes (par first second) := by
  apply domain_of_typed
  · apply Mettapedia.GSLT.LanguageDef.RestrictionBlocks.bag_typed (block := ccsBlock) (rest := none)
    intro element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (typed_of_domain firstIn).1
    · exact (typed_of_domain secondIn).1
  · simp [par, isObjectPattern, isObjectPatternList, (typed_of_domain firstIn).2, (typed_of_domain secondIn).2]

/-- **Processes with one canonical form are related by a chain of laws through processes.** -/
theorem procEquiv_of_canon {first second : Pattern} (firstIn : processes first) (secondIn : processes second)
    (same : blockCanon first = blockCanon second) : ProcEquiv ccsRecCalc ccsBlock names [] first second := by
  have toFirst := (canon_sound (block := ccsBlock) names_context (typed_of_domain firstIn).1).2
  have toSecond := (canon_sound (block := ccsBlock) names_context (typed_of_domain secondIn).1).2
  have same' : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon ccsBlock first =
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon ccsBlock second := same
  rw [same'] at toFirst
  exact .trans _ _ _ toFirst (.symm _ _ toSecond)

theorem equivalent_of_canon_eq {first second : Pattern} (firstIn : processes first) (secondIn : processes second)
    (same : blockCanon first = blockCanon second) :
    ObjectEquivalent (definitionsEnv definitions) ccsRecCalc reading first second :=
  objectEquivalent_of_sortedEquiv _ (procEquiv_of_canon firstIn secondIn same) (typed_of_domain firstIn).2

theorem canon_eq_of_equivalent {first second : Pattern} (firstIn : processes first)
    (equivalent : ObjectEquivalent (definitionsEnv definitions) ccsRecCalc reading first second) :
    blockCanon first = blockCanon second :=
  canon_complete (block := ccsBlock) (typed_of_domain firstIn).2 (equationEquiv_of_objectEquivalent equivalent)

/-- Processes with one canonical form are strongly bisimilar. -/
theorem bisimilar_of_canon (admitted : admits definitions = true) {first second : Pattern} (firstIn : processes first)
    (secondIn : processes second) (same : blockCanon first = blockCanon second) : Bisimilar definitions first second :=
  (sameCanon_bisimulation admitted names_context).bisimilar ⟨(typed_of_domain firstIn).1, (typed_of_domain secondIn).1,
    (typed_of_domain firstIn).2, (typed_of_domain secondIn).2, same⟩

/-- A transition keeps a process a process. -/
theorem process_of_step (admitted : admits definitions = true) {source : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions source action target) (sourceIn : processes source) : processes target :=
  let ⟨typed, object⟩ := step.typed admitted (typed_of_domain sourceIn).1 (typed_of_domain sourceIn).2
  domain_of_typed typed object

/-- A reduction keeps a process a process. -/
theorem reduces_process (admitted : admits definitions = true) {source target : Pattern} (sourceIn : processes source)
    (reduces : Reduces definitions source target) : processes target := by
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := reduces
  have redexIn : processes redex := (domain_iff_of_equivalent before).mp sourceIn
  have raw := reference_iff_raw.mp ⟨witness, valid⟩
  obtain ⟨contractumTyped, contractumObject⟩ :=
    typed_of_raw admitted raw (typed_of_domain redexIn).1 (typed_of_domain redexIn).2
  exact (domain_iff_of_equivalent after).mp (domain_of_typed contractumTyped contractumObject)

/-- **A reduction is a silent transition**, up to the canonical form. -/
theorem reduces_iff_tau (admitted : admits definitions = true) {source target : Pattern} (sourceIn : processes source)
    (targetIn : processes target) :
    Reduces definitions source target ↔
      ∃ target', LStep definitions source .tau target' ∧ blockCanon target' = blockCanon target := by
  constructor
  · rintro ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩
    have redexIn : processes redex := (domain_iff_of_equivalent before).mp sourceIn
    have raw := reference_iff_raw.mp ⟨witness, valid⟩
    obtain ⟨-, contractumObject⟩ := typed_of_raw admitted raw (typed_of_domain redexIn).1 (typed_of_domain redexIn).2
    obtain ⟨-, backward⟩ := matched_of_procEquiv admitted names_context
      (procEquiv_of_canon sourceIn redexIn (canon_eq_of_equivalent sourceIn before)) (typed_of_domain sourceIn).2
    obtain ⟨target', step', related⟩ := backward (tau_of_raw raw)
    exact ⟨target', step', (canon_complete (block := ccsBlock) contractumObject related).symm.trans
      (canon_complete (block := ccsBlock) contractumObject (equationEquiv_of_objectEquivalent after))⟩
  · rintro ⟨target', step, same⟩
    obtain ⟨sourceTyped, sourceObject⟩ := typed_of_domain sourceIn
    obtain ⟨contractum, raw, contractumSame⟩ := harmony admitted names_context step sourceTyped sourceObject
    obtain ⟨canonTyped, canonEquivalent⟩ := canon_sound (block := ccsBlock) names_context sourceTyped
    have canonObject : isObjectPattern (blockCanon source) = true := by
      rw [← equationEquiv_isObject (block := ccsBlock) canonEquivalent.toEquationEquiv]; exact sourceObject
    have canonIn : processes (blockCanon source) := domain_of_typed canonTyped canonObject
    obtain ⟨contractumTyped, contractumObject⟩ := typed_of_raw admitted raw canonTyped canonObject
    have contractumIn : processes contractum := domain_of_typed contractumTyped contractumObject
    obtain ⟨witness, valid⟩ := reference_iff_raw.mpr raw
    exact ⟨isState_of_process sourceIn, isState_of_process targetIn, _, _, witness,
      objectEquivalent_of_sortedEquiv _ canonEquivalent sourceObject, isState_of_process canonIn, valid,
      isState_of_process contractumIn, equivalent_of_canon_eq contractumIn targetIn (contractumSame.trans same), rfl⟩

/-! ## Actions of processes are on free names -/

/-- An action whose name, if any, is a name of the context. -/
def ActionTypedIn (free : FreeTypeContext) (bound : List TypeExpr) : Action → Prop
  | .act name | .coact name => HasType ccsRecCalc free bound name (.base "Name") ∧ isObjectPattern name = true
  | .tau => True

/-- **The name of a typed process's action is a name of its context.** -/
theorem action_typed (admitted : admits definitions = true) {source : Pattern} {action : Action}
    {target : Pattern} (step : LStep definitions source action target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType ccsRecCalc free bound source (.base "Proc") →
      isObjectPattern source = true → ActionTypedIn free bound action := by
  induction step with
  | @offer component guards offered k hk action continuation performs =>
      intro free bound typed object
      have guardTyped := offers_guards_typed admitted typed offered _ (List.getElem_mem hk)
      have guardObject := offers_guards_objects admitted object offered _ (List.getElem_mem hk)
      rcases guardAction_some performs with ⟨name, rfl, guardIs⟩ | ⟨name, rfl, guardIs⟩ | ⟨rfl, -⟩
      · rw [guardIs] at guardTyped guardObject
        refine ⟨(prefix_parts (.inl rfl) guardTyped).1, ?_⟩
        simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at guardObject
        exact guardObject.1
      · rw [guardIs] at guardTyped guardObject
        refine ⟨(prefix_parts (.inr rfl) guardTyped).1, ?_⟩
        simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at guardObject
        exact guardObject.1
      · trivial
  | @par elements tail i hi action target inner recurse =>
      intro free bound typed object
      cases bag_tail_none object
      exact recurse (members_of_bag (block := ccsBlock) typed _ (List.getElem_mem hi))
        (bag_objects object _ (List.getElem_mem hi))
  | sync => intro _ _ _ _; trivial
  | @res binder source target action action' inner seen recurse =>
      intro free bound typed object
      cases restriction_binder (block := ccsBlock) typed
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      have inner' := recurse (restriction_body (block := ccsBlock) typed) bodyObject
      have lowered : ∀ {name name' : Pattern},
          HasType ccsRecCalc free (.base "Name" :: bound) name (.base "Name") ∧ isObjectPattern name = true →
          lowerName? name = some name' →
          HasType ccsRecCalc free bound name' (.base "Name") ∧ isObjectPattern name' = true := by
        intro name name' ⟨nameTyped, _⟩ found
        match name, nameTyped, found with
        | .bvar (index + 1), nameTyped, found =>
            simp only [lowerName?, Option.some.injEq] at found
            subst found
            cases nameTyped with
            | bvar lookup => exact ⟨.bvar (by simpa using lookup), rfl⟩
        | .fvar held, nameTyped, found =>
            simp only [lowerName?, Option.some.injEq] at found
            subst found
            cases nameTyped with
            | fvar lookup => exact ⟨.fvar lookup, rfl⟩
      cases action with
      | act name =>
          obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
          exact lowered inner' found
      | coact name =>
          obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
          exact lowered inner' found
      | tau =>
          simp only [Action.lower?, Option.some.injEq] at seen
          subst seen
          trivial

/-- **A process's actions are on free names**, or silent. -/
theorem free_action (admitted : admits definitions = true) {source : Pattern} {action : Action}
    {target : Pattern} (step : LStep definitions source action target) (sourceIn : processes source) :
    (∃ channel, action = .act (.fvar channel)) ∨ (∃ channel, action = .coact (.fvar channel)) ∨ action = .tau := by
  have typedIn := action_typed admitted step (typed_of_domain sourceIn).1 (typed_of_domain sourceIn).2
  have closed : ∀ {name : Pattern}, HasType ccsRecCalc names [] name (.base "Name") → isObjectPattern name = true →
      ∃ channel, name = .fvar channel := by
    intro name nameTyped nameObject
    rcases name_variable nameTyped nameObject with ⟨index, rfl⟩ | ⟨channel, rfl⟩
    · cases nameTyped with
      | bvar lookup => simp at lookup
    · exact ⟨channel, rfl⟩
  cases action with
  | act name =>
      obtain ⟨channel, rfl⟩ := closed typedIn.1 typedIn.2
      exact .inl ⟨channel, rfl⟩
  | coact name =>
      obtain ⟨channel, rfl⟩ := closed typedIn.1 typedIn.2
      exact .inr (.inl ⟨channel, rfl⟩)
  | tau => exact .inr (.inr rfl)

/-! ## Least partners -/

/-- **The least partner of an action** on `channel`: the co-action, then the sentinel `k.0`. -/
def coPartner (channel name : String) : Pattern :=
  .apply "CSum" [.collection .hashBag [.apply "CCoAct" [.fvar channel, sentinel name]] none]

/-- **The least partner of a co-action** on `channel`: the action, then the sentinel `k.0`. -/
def partner (channel name : String) : Pattern :=
  .apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar channel, sentinel name]] none]

theorem coPartner_process (channel name : String) : processes (coPartner channel name) := rfl

theorem partner_process (channel name : String) : processes (partner channel name) := rfl

theorem sentinel_process (name : String) : processes (sentinel name) := rfl

theorem coPartner_step {channel name : String} {action : Action} {target : Pattern}
    (step : LStep definitions (coPartner channel name) action target) :
    action = .coact (.fvar channel) ∧ target = sentinel name := by
  obtain ⟨k, hk, performs⟩ := lstep_sum_inv step
  match k, hk, performs with
  | 0, _, performs =>
      simp only [List.getElem_cons_zero, guardAction, Option.some.injEq, Prod.mk.injEq] at performs
      exact ⟨performs.1.symm, performs.2.symm⟩

theorem partner_step {channel name : String} {action : Action} {target : Pattern}
    (step : LStep definitions (partner channel name) action target) :
    action = .act (.fvar channel) ∧ target = sentinel name := by
  obtain ⟨k, hk, performs⟩ := lstep_sum_inv step
  match k, hk, performs with
  | 0, _, performs =>
      simp only [List.getElem_cons_zero, guardAction, Option.some.injEq, Prod.mk.injEq] at performs
      exact ⟨performs.1.symm, performs.2.symm⟩

/-- **A process with no free `k`, beside a partner with no action on `k`, has no action on `k`.** -/
theorem no_sentinel_action (admitted : admits definitions = true) {process other : Pattern} {name : String}
    (fresh : name ∉ process.freeFvarNames)
    (otherStill : ∀ {action target}, LStep definitions other action target → action ≠ .act (.fvar name))
    {target : Pattern} : ¬ LStep definitions (par process other) (.act (.fvar name)) target := by
  intro step
  unfold par at step
  cases step with
  | offer offered => simp [offers] at offered
  | par i hi inner =>
      match i, hi, inner with
      | 0, _, inner => exact fresh ((inner.names_sub admitted).2 name (by simp [Action.names, Pattern.freeFvarNames]))
      | 1, _, inner => exact otherStill inner rfl

/-- **Least partners of actions**: a process performs an action on `channel` to a residual exactly when, beside the
least partner `~channel.k.0`, it reduces to the residual beside the sentinel `k.0`, `k` a name it does not use. -/
theorem reduces_coPartner_iff (admitted : admits definitions = true) {process residual : Pattern}
    {channel name : String} (processIn : processes process) (residualIn : processes residual)
    (fresh : name ∉ process.freeFvarNames) :
    Reduces definitions (par process (coPartner channel name)) (par residual (sentinel name)) ↔
      ∃ residual', LStep definitions process (.act (.fvar channel)) residual' ∧
        blockCanon (par residual' (sentinel name)) = blockCanon (par residual (sentinel name)) := by
  have bagIn := par_process processIn (coPartner_process channel name)
  have targetIn := par_process residualIn (sentinel_process name)
  rw [reduces_iff_tau admitted bagIn targetIn]
  constructor
  · rintro ⟨target', step, same⟩
    have targetIn' := process_of_step admitted step bagIn
    unfold par at step
    cases step with
    | offer offered => simp [offers] at offered
    | par i hi inner =>
        match i, hi, inner with
        | 0, _, inner =>
            exfalso
            have sentinelStep : LStep definitions (par residual (sentinel name)) (.act (.fvar name))
                (.collection .hashBag [.apply "CNil" [], residual] none) :=
              .par 1 (by simp) (.offer rfl 0 (by simp) rfl)
            obtain ⟨matched, matchedStep, -⟩ :=
              (bisimilar_of_canon admitted targetIn' targetIn same).symm.forth sentinelStep
            exact no_sentinel_action admitted
              (fun member => fresh ((inner.names_sub admitted).1 name member))
              (fun step same => by cases (coPartner_step step).1.symm.trans same) matchedStep
        | 1, _, inner => exact absurd (coPartner_step inner).1 (by simp)
    | sync i hi j hj first second =>
        match i, hi, j, hj, first, second with
        | 0, _, 0, _, first, second =>
            obtain ⟨actionIs, rfl⟩ := coPartner_step second
            cases actionIs
            exact ⟨_, first, same⟩
        | 1, _, 0, _, first, _ => exact absurd (coPartner_step first).1 (by simp)
  · rintro ⟨residual', step, same⟩
    exact ⟨_, .sync (elements := [process, coPartner channel name]) 0 (by simp) 0 (by simp) step
      (.offer rfl 0 (by simp) rfl), same⟩

/-- **Least partners of co-actions**: a process performs a co-action on `channel` to a residual exactly when, beside
the least partner `channel.k.0`, it reduces to the residual beside the sentinel `k.0`, `k` a name it does not use,
other than the channel. -/
theorem reduces_partner_iff (admitted : admits definitions = true) {process residual : Pattern}
    {channel name : String} (processIn : processes process) (residualIn : processes residual)
    (fresh : name ∉ process.freeFvarNames) (different : channel ≠ name) :
    Reduces definitions (par process (partner channel name)) (par residual (sentinel name)) ↔
      ∃ residual', LStep definitions process (.coact (.fvar channel)) residual' ∧
        blockCanon (par residual' (sentinel name)) = blockCanon (par residual (sentinel name)) := by
  have bagIn := par_process processIn (partner_process channel name)
  have targetIn := par_process residualIn (sentinel_process name)
  rw [reduces_iff_tau admitted bagIn targetIn]
  have swapped : ∀ {residual' : Pattern}, processes residual' →
      blockCanon (.collection .hashBag [sentinel name, residual'] none) = blockCanon (par residual' (sentinel name)) := by
    intro residual' residualIn'
    have reorderedIn := par_process (sentinel_process name) residualIn'
    exact canon_complete (block := ccsBlock) (typed_of_domain reorderedIn).2
      (bag_result_equivalent (List.Perm.swap _ _ _) (typed_of_domain reorderedIn).1)
  constructor
  · rintro ⟨target', step, same⟩
    have targetIn' := process_of_step admitted step bagIn
    unfold par at step
    cases step with
    | offer offered => simp [offers] at offered
    | par i hi inner =>
        match i, hi, inner with
        | 0, _, inner =>
            exfalso
            have sentinelStep : LStep definitions (par residual (sentinel name)) (.act (.fvar name))
                (.collection .hashBag [.apply "CNil" [], residual] none) :=
              .par 1 (by simp) (.offer rfl 0 (by simp) rfl)
            obtain ⟨matched, matchedStep, -⟩ :=
              (bisimilar_of_canon admitted targetIn' targetIn same).symm.forth sentinelStep
            exact no_sentinel_action admitted
              (fun member => fresh ((inner.names_sub admitted).1 name member))
              (fun step same => different (by simpa using (partner_step step).1.symm.trans same)) matchedStep
        | 1, _, inner => exact absurd (partner_step inner).1 (by simp)
    | sync i hi j hj first second =>
        match i, hi, j, hj, first, second with
        | 0, _, 0, _, _, second => exact absurd (partner_step second).1 (by simp)
        | 1, _, 0, _, first, second =>
            obtain ⟨actionIs, rfl⟩ := partner_step first
            cases actionIs
            have secondIn := process_of_step admitted second processIn
            exact ⟨_, second, (swapped secondIn).symm.trans same⟩
  · rintro ⟨residual', step, same⟩
    have residualIn' := process_of_step admitted step processIn
    exact ⟨_, .sync (elements := [process, partner channel name]) 1 (by simp) 0 (by simp)
      (.offer rfl 0 (by simp) rfl) step, (swapped residualIn').trans same⟩

/-! ## Least-partner bisimilarity -/

/-- **A least-partner bisimulation**: a relation between processes whose reductions, alone and beside every least
partner with a fresh sentinel, are matched to related residuals, both ways. -/
structure LeastPartnerBisimulation (definitions : List Definition) (relation : Pattern → Pattern → Prop) : Prop where
  inProcesses : ∀ ⦃first second⦄, relation first second → processes first ∧ processes second
  silent : ∀ ⦃first second⦄, relation first second → ∀ ⦃target⦄, processes target → Reduces definitions first target →
    ∃ target', processes target' ∧ Reduces definitions second target' ∧ relation target target'
  silentBack : ∀ ⦃first second⦄, relation first second → ∀ ⦃target'⦄, processes target' →
    Reduces definitions second target' →
    ∃ target, processes target ∧ Reduces definitions first target ∧ relation target target'
  act : ∀ ⦃first second⦄, relation first second → ∀ ⦃channel name : String⦄ ⦃residual : Pattern⦄,
    name ∉ first.freeFvarNames → name ∉ second.freeFvarNames → name ∉ residual.freeFvarNames → processes residual →
    Reduces definitions (par first (coPartner channel name)) (par residual (sentinel name)) →
    ∃ residual', processes residual' ∧ name ∉ residual'.freeFvarNames ∧
      Reduces definitions (par second (coPartner channel name)) (par residual' (sentinel name)) ∧
      relation residual residual'
  actBack : ∀ ⦃first second⦄, relation first second → ∀ ⦃channel name : String⦄ ⦃residual' : Pattern⦄,
    name ∉ first.freeFvarNames → name ∉ second.freeFvarNames → name ∉ residual'.freeFvarNames → processes residual' →
    Reduces definitions (par second (coPartner channel name)) (par residual' (sentinel name)) →
    ∃ residual, processes residual ∧ name ∉ residual.freeFvarNames ∧
      Reduces definitions (par first (coPartner channel name)) (par residual (sentinel name)) ∧
      relation residual residual'
  coact : ∀ ⦃first second⦄, relation first second → ∀ ⦃channel name : String⦄ ⦃residual : Pattern⦄,
    channel ≠ name → name ∉ first.freeFvarNames → name ∉ second.freeFvarNames → name ∉ residual.freeFvarNames →
    processes residual → Reduces definitions (par first (partner channel name)) (par residual (sentinel name)) →
    ∃ residual', processes residual' ∧ name ∉ residual'.freeFvarNames ∧
      Reduces definitions (par second (partner channel name)) (par residual' (sentinel name)) ∧
      relation residual residual'
  coactBack : ∀ ⦃first second⦄, relation first second → ∀ ⦃channel name : String⦄ ⦃residual' : Pattern⦄,
    channel ≠ name → name ∉ first.freeFvarNames → name ∉ second.freeFvarNames → name ∉ residual'.freeFvarNames →
    processes residual' → Reduces definitions (par second (partner channel name)) (par residual' (sentinel name)) →
    ∃ residual, processes residual ∧ name ∉ residual.freeFvarNames ∧
      Reduces definitions (par first (partner channel name)) (par residual (sentinel name)) ∧
      relation residual residual'

/-- **Least-partner bisimilarity**: related by a least-partner bisimulation. -/
def LeastPartnerBisimilar (definitions : List Definition) (first second : Pattern) : Prop :=
  ∃ relation, LeastPartnerBisimulation definitions relation ∧ relation first second

/-- The converse of a least-partner bisimulation is one. -/
theorem LeastPartnerBisimulation.flip {relation : Pattern → Pattern → Prop}
    (bisimulation : LeastPartnerBisimulation definitions relation) :
    LeastPartnerBisimulation definitions (fun first second => relation second first) where
  inProcesses _ _ related := (bisimulation.inProcesses related).symm
  silent _ _ related _ targetIn step := bisimulation.silentBack related targetIn step
  silentBack _ _ related _ targetIn step := bisimulation.silent related targetIn step
  act _ _ related _ _ _ firstFresh secondFresh residualFresh residualIn step :=
    bisimulation.actBack related secondFresh firstFresh residualFresh residualIn step
  actBack _ _ related _ _ _ firstFresh secondFresh residualFresh residualIn step :=
    bisimulation.act related secondFresh firstFresh residualFresh residualIn step
  coact _ _ related _ _ _ different firstFresh secondFresh residualFresh residualIn step :=
    bisimulation.coactBack related different secondFresh firstFresh residualFresh residualIn step
  coactBack _ _ related _ _ _ different firstFresh secondFresh residualFresh residualIn step :=
    bisimulation.coact related different secondFresh firstFresh residualFresh residualIn step

/-- A name used by none of three processes, nor equal to a channel. -/
theorem exists_fresh (first second third : Pattern) (channel : String) :
    ∃ name, name ∉ first.freeFvarNames ∧ name ∉ second.freeFvarNames ∧ name ∉ third.freeFvarNames ∧
      channel ≠ name := by
  obtain ⟨name, absent⟩ := Infinite.exists_notMem_finset
    (first.freeFvarNames ++ second.freeFvarNames ++ third.freeFvarNames ++ [channel]).toFinset
  simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, not_or] at absent
  exact ⟨name, absent.1.1.1, absent.1.1.2, absent.1.2, fun same => absent.2 same.symm⟩

/-- **A transition is matched through a least-partner bisimulation**, up to strong bisimilarity on both sides. -/
theorem leastPartner_forth (admitted : admits definitions = true) {relation : Pattern → Pattern → Prop}
    (bisimulation : LeastPartnerBisimulation definitions relation) {first second first₀ second₀ : Pattern}
    (firstIn : processes first) (secondIn : processes second) (toFirst : Bisimilar definitions first first₀)
    (related : relation first₀ second₀) (toSecond : Bisimilar definitions second₀ second)
    {action : Action} {target : Pattern} (step : LStep definitions first action target) :
    ∃ target', LStep definitions second action target' ∧ processes target ∧ processes target' ∧
      ∃ target₀ target₀', Bisimilar definitions target target₀ ∧ relation target₀ target₀' ∧
        Bisimilar definitions target₀' target' := by
  obtain ⟨first₀In, second₀In⟩ := bisimulation.inProcesses related
  have targetIn := process_of_step admitted step firstIn
  obtain ⟨target₀, step₀, toTarget₀⟩ := toFirst.forth step
  have target₀In := process_of_step admitted step₀ first₀In
  rcases free_action admitted step₀ first₀In with ⟨channel, rfl⟩ | ⟨channel, rfl⟩ | rfl
  · obtain ⟨name, first₀Fresh, second₀Fresh, target₀Fresh, -⟩ := exists_fresh first₀ second₀ target₀ channel
    have reduces := (reduces_coPartner_iff admitted first₀In target₀In first₀Fresh).mpr ⟨target₀, step₀, rfl⟩
    obtain ⟨target₀', target₀In', target₀Fresh', reduces', related'⟩ :=
      bisimulation.act related first₀Fresh second₀Fresh target₀Fresh target₀In reduces
    obtain ⟨residual, stepResidual, same⟩ :=
      (reduces_coPartner_iff admitted second₀In target₀In' second₀Fresh).mp reduces'
    have residualIn := process_of_step admitted stepResidual second₀In
    have residualFresh : name ∉ residual.freeFvarNames :=
      fun member => second₀Fresh ((stepResidual.names_sub admitted).1 name member)
    have residualBisimilar : Bisimilar definitions residual target₀' :=
      bisimilar_cancel admitted residualFresh target₀Fresh' (bisimilar_of_canon admitted
        (par_process residualIn (sentinel_process name)) (par_process target₀In' (sentinel_process name)) same)
    obtain ⟨target', step', toTarget'⟩ := toSecond.forth stepResidual
    exact ⟨target', step', targetIn, process_of_step admitted step' secondIn, target₀, target₀', toTarget₀, related',
      residualBisimilar.symm.trans toTarget'⟩
  · obtain ⟨name, first₀Fresh, second₀Fresh, target₀Fresh, different⟩ :=
      exists_fresh first₀ second₀ target₀ channel
    have reduces := (reduces_partner_iff admitted first₀In target₀In first₀Fresh different).mpr ⟨target₀, step₀, rfl⟩
    obtain ⟨target₀', target₀In', target₀Fresh', reduces', related'⟩ :=
      bisimulation.coact related different first₀Fresh second₀Fresh target₀Fresh target₀In reduces
    obtain ⟨residual, stepResidual, same⟩ :=
      (reduces_partner_iff admitted second₀In target₀In' second₀Fresh different).mp reduces'
    have residualIn := process_of_step admitted stepResidual second₀In
    have residualFresh : name ∉ residual.freeFvarNames :=
      fun member => second₀Fresh ((stepResidual.names_sub admitted).1 name member)
    have residualBisimilar : Bisimilar definitions residual target₀' :=
      bisimilar_cancel admitted residualFresh target₀Fresh' (bisimilar_of_canon admitted
        (par_process residualIn (sentinel_process name)) (par_process target₀In' (sentinel_process name)) same)
    obtain ⟨target', step', toTarget'⟩ := toSecond.forth stepResidual
    exact ⟨target', step', targetIn, process_of_step admitted step' secondIn, target₀, target₀', toTarget₀, related',
      residualBisimilar.symm.trans toTarget'⟩
  · have reduces := (reduces_iff_tau admitted first₀In target₀In).mpr ⟨target₀, step₀, rfl⟩
    obtain ⟨target₀', target₀In', reduces', related'⟩ := bisimulation.silent related target₀In reduces
    obtain ⟨residual, stepResidual, same⟩ := (reduces_iff_tau admitted second₀In target₀In').mp reduces'
    have residualIn := process_of_step admitted stepResidual second₀In
    obtain ⟨target', step', toTarget'⟩ := toSecond.forth stepResidual
    exact ⟨target', step', targetIn, process_of_step admitted step' secondIn, target₀, target₀', toTarget₀, related',
      (bisimilar_of_canon admitted target₀In' residualIn same.symm).trans toTarget'⟩

/-- **Least-partner bisimilarity is strong bisimilarity** of the labelled transitions: matching reductions, alone and
beside every least partner with a fresh sentinel, is matching transitions. -/
theorem leastPartnerBisimilar_iff (admitted : admits definitions = true) {first second : Pattern}
    (firstIn : processes first) (secondIn : processes second) :
    LeastPartnerBisimilar definitions first second ↔ Bisimilar definitions first second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => processes left ∧ processes right ∧ ∃ left₀ right₀, Bisimilar definitions left left₀ ∧
        relation left₀ right₀ ∧ Bisimilar definitions right₀ right, ?_,
      firstIn, secondIn, first, second, .refl _, related, .refl _⟩
    rintro left right ⟨leftIn, rightIn, left₀, right₀, toLeft, relatedHere, toRight⟩
    constructor
    · intro action target step
      obtain ⟨target', step', targetIn, targetIn', target₀, target₀', toTarget, related', toTarget'⟩ :=
        leastPartner_forth admitted bisimulation leftIn rightIn toLeft relatedHere toRight step
      exact ⟨target', step', targetIn, targetIn', target₀, target₀', toTarget, related', toTarget'⟩
    · intro action target' step
      obtain ⟨target, step', targetIn', targetIn, target₀', target₀, toTarget', related', toTarget⟩ :=
        leastPartner_forth admitted bisimulation.flip rightIn leftIn toRight.symm relatedHere toLeft.symm step
      exact ⟨target, step', targetIn, targetIn', target₀, target₀', toTarget.symm, related', toTarget'.symm⟩
  · intro bisimilar
    refine ⟨fun left right => processes left ∧ processes right ∧ Bisimilar definitions left right, ?_,
      firstIn, secondIn, bisimilar⟩
    have silentForth : ∀ {left right : Pattern}, processes left → processes right → Bisimilar definitions left right →
        ∀ {target : Pattern}, processes target → Reduces definitions left target →
          ∃ target', processes target' ∧ Reduces definitions right target' ∧ Bisimilar definitions target target' := by
      intro left right leftIn rightIn related target targetIn reduces
      obtain ⟨target₁, step₁, same⟩ := (reduces_iff_tau admitted leftIn targetIn).mp reduces
      have target₁In := process_of_step admitted step₁ leftIn
      obtain ⟨target₂, step₂, related₂⟩ := related.forth step₁
      have target₂In := process_of_step admitted step₂ rightIn
      exact ⟨target₂, target₂In, (reduces_iff_tau admitted rightIn target₂In).mpr ⟨target₂, step₂, rfl⟩,
        (bisimilar_of_canon admitted targetIn target₁In same.symm).trans related₂⟩
    have actForth : ∀ {left right : Pattern}, processes left → processes right → Bisimilar definitions left right →
        ∀ {channel name : String} {residual : Pattern}, name ∉ left.freeFvarNames → name ∉ right.freeFvarNames →
          name ∉ residual.freeFvarNames → processes residual →
          Reduces definitions (par left (coPartner channel name)) (par residual (sentinel name)) →
          ∃ residual', processes residual' ∧ name ∉ residual'.freeFvarNames ∧
            Reduces definitions (par right (coPartner channel name)) (par residual' (sentinel name)) ∧
            Bisimilar definitions residual residual' := by
      intro left right leftIn rightIn related channel name residual leftFresh rightFresh residualFresh residualIn
        reduces
      obtain ⟨residual₁, step₁, same⟩ := (reduces_coPartner_iff admitted leftIn residualIn leftFresh).mp reduces
      have residual₁In := process_of_step admitted step₁ leftIn
      obtain ⟨residual₂, step₂, related₂⟩ := related.forth step₁
      have residual₂In := process_of_step admitted step₂ rightIn
      have residual₂Fresh : name ∉ residual₂.freeFvarNames :=
        fun member => rightFresh ((step₂.names_sub admitted).1 name member)
      refine ⟨residual₂, residual₂In, residual₂Fresh,
        (reduces_coPartner_iff admitted rightIn residual₂In rightFresh).mpr ⟨residual₂, step₂, rfl⟩, ?_⟩
      exact bisimilar_cancel admitted residualFresh residual₂Fresh
        ((bisimilar_of_canon admitted (par_process residualIn (sentinel_process name))
          (par_process residual₁In (sentinel_process name)) same.symm).trans
          (bisimilar_bag (.cons related₂ (.cons (.refl _) .nil))))
    have coactForth : ∀ {left right : Pattern}, processes left → processes right → Bisimilar definitions left right →
        ∀ {channel name : String} {residual : Pattern}, channel ≠ name → name ∉ left.freeFvarNames →
          name ∉ right.freeFvarNames → name ∉ residual.freeFvarNames → processes residual →
          Reduces definitions (par left (partner channel name)) (par residual (sentinel name)) →
          ∃ residual', processes residual' ∧ name ∉ residual'.freeFvarNames ∧
            Reduces definitions (par right (partner channel name)) (par residual' (sentinel name)) ∧
            Bisimilar definitions residual residual' := by
      intro left right leftIn rightIn related channel name residual different leftFresh rightFresh residualFresh
        residualIn reduces
      obtain ⟨residual₁, step₁, same⟩ :=
        (reduces_partner_iff admitted leftIn residualIn leftFresh different).mp reduces
      have residual₁In := process_of_step admitted step₁ leftIn
      obtain ⟨residual₂, step₂, related₂⟩ := related.forth step₁
      have residual₂In := process_of_step admitted step₂ rightIn
      have residual₂Fresh : name ∉ residual₂.freeFvarNames :=
        fun member => rightFresh ((step₂.names_sub admitted).1 name member)
      refine ⟨residual₂, residual₂In, residual₂Fresh,
        (reduces_partner_iff admitted rightIn residual₂In rightFresh different).mpr ⟨residual₂, step₂, rfl⟩, ?_⟩
      exact bisimilar_cancel admitted residualFresh residual₂Fresh
        ((bisimilar_of_canon admitted (par_process residualIn (sentinel_process name))
          (par_process residual₁In (sentinel_process name)) same.symm).trans
          (bisimilar_bag (.cons related₂ (.cons (.refl _) .nil))))
    refine ⟨fun _ _ related => ⟨related.1, related.2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ _ ⟨leftIn, rightIn, related⟩ _ targetIn reduces
      obtain ⟨target', targetIn', reduces', related'⟩ := silentForth leftIn rightIn related targetIn reduces
      exact ⟨target', targetIn', reduces', targetIn, targetIn', related'⟩
    · rintro _ _ ⟨leftIn, rightIn, related⟩ _ targetIn reduces
      obtain ⟨target, targetIn', reduces', related'⟩ := silentForth rightIn leftIn related.symm targetIn reduces
      exact ⟨target, targetIn', reduces', targetIn', targetIn, related'.symm⟩
    · rintro _ _ ⟨leftIn, rightIn, related⟩ _ _ _ leftFresh rightFresh residualFresh residualIn reduces
      obtain ⟨residual', residualIn', residualFresh', reduces', related'⟩ :=
        actForth leftIn rightIn related leftFresh rightFresh residualFresh residualIn reduces
      exact ⟨residual', residualIn', residualFresh', reduces', residualIn, residualIn', related'⟩
    · rintro _ _ ⟨leftIn, rightIn, related⟩ _ _ _ leftFresh rightFresh residualFresh residualIn reduces
      obtain ⟨residual, residualIn', residualFresh', reduces', related'⟩ :=
        actForth rightIn leftIn related.symm rightFresh leftFresh residualFresh residualIn reduces
      exact ⟨residual, residualIn', residualFresh', reduces', residualIn', residualIn, related'.symm⟩
    · rintro _ _ ⟨leftIn, rightIn, related⟩ _ _ _ different leftFresh rightFresh residualFresh residualIn reduces
      obtain ⟨residual', residualIn', residualFresh', reduces', related'⟩ :=
        coactForth leftIn rightIn related different leftFresh rightFresh residualFresh residualIn reduces
      exact ⟨residual', residualIn', residualFresh', reduces', residualIn, residualIn', related'⟩
    · rintro _ _ ⟨leftIn, rightIn, related⟩ _ _ _ different leftFresh rightFresh residualFresh residualIn reduces
      obtain ⟨residual, residualIn', residualFresh', reduces', related'⟩ :=
        coactForth rightIn leftIn related.symm different rightFresh leftFresh residualFresh residualIn reduces
      exact ⟨residual, residualIn', residualFresh', reduces', residualIn', residualIn, related'.symm⟩

/-! ## Saturated reduction bisimilarity -/

/-- **A saturated reduction bisimulation**: beside every process, a reduction of either side is matched by one of the
other, to related processes. -/
def IsSaturatedReduction (definitions : List Definition) (relation : Pattern → Pattern → Prop) : Prop :=
  ∀ ⦃first second⦄, relation first second → ∀ partner, processes partner →
    (∀ next, Reduces definitions (par first partner) next →
      ∃ matched, Reduces definitions (par second partner) matched ∧ relation next matched) ∧
    (∀ next, Reduces definitions (par second partner) next →
      ∃ matched, Reduces definitions (par first partner) matched ∧ relation matched next)

/-- **Saturated reduction bisimilarity** of processes. -/
def SaturatedReductionBisimilar (definitions : List Definition) (first second : Pattern) : Prop :=
  ∃ relation, IsSaturatedReduction definitions relation ∧
    (∀ ⦃left right⦄, relation left right → processes left ∧ processes right) ∧ relation first second

/-- **Strongly bisimilar processes are saturated reduction bisimilar**: bisimilarity is a congruence for parallel
composition, and a reduction is a silent transition. The converse fails for a process that can always move
silently. -/
theorem saturated_of_bisimilar (admitted : admits definitions = true) {first second : Pattern}
    (firstIn : processes first) (secondIn : processes second) (bisimilar : Bisimilar definitions first second) :
    SaturatedReductionBisimilar definitions first second := by
  refine ⟨fun left right => processes left ∧ processes right ∧ Bisimilar definitions left right, ?_,
    fun _ _ related => ⟨related.1, related.2.1⟩, firstIn, secondIn, bisimilar⟩
  have forth : ∀ {left right : Pattern}, processes left → processes right → Bisimilar definitions left right →
      ∀ partner, processes partner → ∀ next, Reduces definitions (par left partner) next →
        ∃ matched, Reduces definitions (par right partner) matched ∧ processes next ∧ processes matched ∧
          Bisimilar definitions next matched := by
    intro left right leftIn rightIn related partner partnerIn next reduces
    have bagIn := par_process leftIn partnerIn
    have bagIn' := par_process rightIn partnerIn
    have nextIn := reduces_process admitted bagIn reduces
    obtain ⟨next₁, step₁, same⟩ := (reduces_iff_tau admitted bagIn nextIn).mp reduces
    have next₁In := process_of_step admitted step₁ bagIn
    obtain ⟨next₂, step₂, related₂⟩ :=
      (bisimilar_bag (definitions := definitions) (.cons related (.cons (.refl partner) .nil))).forth step₁
    have next₂In := process_of_step admitted step₂ bagIn'
    exact ⟨next₂, (reduces_iff_tau admitted bagIn' next₂In).mpr ⟨next₂, step₂, rfl⟩, nextIn, next₂In,
      (bisimilar_of_canon admitted nextIn next₁In same.symm).trans related₂⟩
  rintro left right ⟨leftIn, rightIn, related⟩ partner partnerIn
  constructor
  · intro next reduces
    obtain ⟨matched, reduces', nextIn, matchedIn, related'⟩ := forth leftIn rightIn related partner partnerIn next reduces
    exact ⟨matched, reduces', nextIn, matchedIn, related'⟩
  · intro next reduces
    obtain ⟨matched, reduces', nextIn, matchedIn, related'⟩ :=
      forth rightIn leftIn related.symm partner partnerIn next reduces
    exact ⟨matched, reduces', matchedIn, nextIn, related'.symm⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartners
