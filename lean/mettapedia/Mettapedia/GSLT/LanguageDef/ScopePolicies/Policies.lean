import Mettapedia.GSLT.LanguageDef.ScopePolicies.Core

/-!
# A scope policy as a language, in two presentations

A scope policy is a `Config`: ownership, lifetime, readout.  There are two ways
to say that it is a language.

* **(A) The policy's own theory on authored text** (`policyGSLT`).  A term is
  an authored program (equations and a query, spellings only) or an
  observation.  A program steps to the observation that the policy gives of
  it: elaborate under the policy, run (`PolicyEvaluates`).  Two programs are
  statically equivalent when they are the same text; observations are compared
  as in the core.
* **(B) The core read along the policy's elaboration** (`policyRead`).  The
  elaboration `elabState` sends a program to a judgment of the core: the
  policy's discipline, the elaborated equations, the elaborated query.  The
  theory is the core read along it (`GSLT.readAlong`): two programs are
  statically equivalent when their elaborations are.

## How they relate

They have the same terms and the same reduction (`policy_rewrites_iff_read`,
through `policy_rewrites_iff`): what a policy gives of a text is what the core
gives of its elaboration, and nothing else.  The static equivalence of (A) is
contained in that of (B) (`policy_equations_read`), strictly: `(new () s)` and
`s` are two texts with one elaboration under every policy
(`spellings_one_elaboration`).  So:

* the elaboration out of (B) is a hosting map into the core
  (`kernelElaboration_hosting`), and the induced static equivalence is the
  only one for which it is (`elaboration_hosting_iff`);
* the elaboration out of (A) is a map that preserves and reflects transitions
  (`elaboration_preserves`, `elaboration_reflects`), hence preserves and
  reflects what every probe sees (`elaboration_bisimilar_iff`), and it is not
  hosting (`elaboration_not_hosting`): (A) keeps spellings apart that no probe
  separates.  That is all that (A) has and (B) does not
  (`forgetSpelling_not_hosting`, `forgetSpelling_exhausting`).

## The image

An elaboration is never exhausting: the core has judgments that are the
elaboration of no program under the policy.  A judgment under the other
discipline is one (`elaboration_not_exhausting`); so is, under the policy's own
discipline, a judgment whose query is contextual code, which no elaboration
writes at its root (`kernelElaboration_not_exhausting`, from
`elabCfg_ne_ctx`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

/-- **Authored terms**: a program as written, or an observation. -/
inductive Authored (S : Type u) (X : Type v) where
  | program (program : Program S X)
  | done (bag : Result S (Slot X))

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- **The elaboration of a policy, on the terms of its theory**: a program goes
to the judgment of the core that runs its elaboration under the policy's
discipline; an observation is an observation. -/
def elabState (c : Config) (u : X) (unit : S) : Authored S X → Core S X
  | .program program =>
      .run c.disc (progSlot c u unit program.clauses) (elabCfg c [] program.query)
  | .done bag => .done bag

/-- **The static equivalence of authored text**: programs as written,
observations as the core compares them. -/
inductive AuthoredEquiv : Authored S X → Authored S X → Prop
  | program (program : Program S X) : AuthoredEquiv (.program program) (.program program)
  | done {bag bag' : Result S (Slot X)} :
      CoreEquiv (.done bag : Core S X) (.done bag') → AuthoredEquiv (.done bag) (.done bag')

theorem AuthoredEquiv.refl : ∀ term : Authored S X, AuthoredEquiv term term
  | .program text => .program text
  | .done _ => .done (.refl _)

theorem AuthoredEquiv.symm {first second : Authored S X} (equivalent : AuthoredEquiv first second) :
    AuthoredEquiv second first := by
  cases equivalent with
  | program text => exact .program text
  | done related => exact .done related.symm

theorem AuthoredEquiv.trans {first second third : Authored S X}
    (firstSecond : AuthoredEquiv first second) (secondThird : AuthoredEquiv second third) :
    AuthoredEquiv first third := by
  cases firstSecond with
  | program text => exact secondThird
  | done related =>
      cases secondThird with
      | done related' => exact .done (related.trans related')

/-- The static equivalence of authored text, as a setoid. -/
def authoredSetoid (S : Type u) (X : Type v) [DecidableEq X] : Setoid (Authored S X) where
  r := AuthoredEquiv
  iseqv := ⟨AuthoredEquiv.refl, AuthoredEquiv.symm, AuthoredEquiv.trans⟩

/-- Statically equivalent programs are one program. -/
theorem AuthoredEquiv.program_eq {first second : Program S X}
    (equivalent : AuthoredEquiv (.program first) (.program second)) : first = second := by
  cases equivalent
  rfl

/-- The elaboration respects the static equivalence of authored text. -/
theorem AuthoredEquiv.elabState (c : Config) (u : X) (unit : S) {first second : Authored S X}
    (equivalent : AuthoredEquiv first second) :
    CoreEquiv (elabState c u unit first) (elabState c u unit second) := by
  cases equivalent with
  | program text => exact .refl _
  | done related => exact related

variable [DecidableEq S]

/-! ## (A): the policy's own theory -/

/-- **What a policy gives of a text**: elaborate under the policy, run under
its discipline. -/
def PolicyEvaluates (c : Config) (u : X) (unit : S) : Authored S X → Authored S X → Prop
  | .program program, .done bag =>
      ∃ n, run c.disc (progSlot c u unit program.clauses) n [] Store.empty
        (elabCfg c [] program.query) = some bag
  | _, _ => False

/-- What a policy gives of a text is what the core gives of its
elaboration. -/
theorem policyEvaluates_iff (c : Config) (u : X) (unit : S) (term next : Authored S X) :
    PolicyEvaluates c u unit term next ↔
      Evaluates (elabState c u unit term) (elabState c u unit next) := by
  cases term <;> cases next <;> exact Iff.rfl

/-- The answers of an authored query under a configuration (`answersCfg`) are
read off the observation. -/
theorem answersCfg_of_policyEvaluates (c : Config) (u : X) (unit : S) (program : Program S X)
    (bag : Result S (Slot X))
    (evaluates : PolicyEvaluates c u unit (.program program) (.done bag)) :
    ∃ n, answersCfg c (progSlot c u unit program.clauses) n program.query =
      some (bag.map fun result => act result.2 result.1) := by
  obtain ⟨n, defined⟩ := evaluates
  refine ⟨n, ?_⟩
  unfold answersCfg answers
  rw [defined]
  rfl

/-- **(A) The policy's own theory on authored text.** -/
def policyGSLT (c : Config) (u : X) (unit : S) : GSLT.{max u v} where
  Term := Authored S X
  equations := authoredSetoid S X
  rewrites := fun term next =>
    ∃ observed, PolicyEvaluates c u unit term observed ∧ AuthoredEquiv observed next
  rewrites_resp_left := by
    rintro term term' next equivalent ⟨observed, evaluates, related⟩
    cases equivalent with
    | program text => exact ⟨next, ⟨observed, evaluates, related⟩, .refl next⟩
    | done _ => cases observed <;> exact evaluates.elim
  rewrites_resp_right := by
    rintro term next next' ⟨observed, evaluates, related⟩ equivalent
    exact ⟨observed, evaluates, related.trans equivalent⟩

/-- **The reduction of (A) is the reduction of the core, read along the
elaboration.** -/
theorem policy_rewrites_iff (c : Config) (u : X) (unit : S) (term next : Authored S X) :
    (policyGSLT c u unit).rewrites term next ↔
      (coreGSLT S X).rewrites (elabState c u unit term) (elabState c u unit next) := by
  constructor
  · rintro ⟨observed, evaluates, related⟩
    exact ⟨elabState c u unit observed, (policyEvaluates_iff c u unit term observed).mp evaluates,
      related.elabState c u unit⟩
  · rintro ⟨observed, evaluates, related⟩
    obtain ⟨_, _, _, bag, -, rfl, -⟩ := evaluates.shape
    cases next with
    | program program => exact absurd related.symm coreEquiv_kind
    | done bag' =>
        exact ⟨.done bag, (policyEvaluates_iff c u unit term (.done bag)).mpr evaluates,
          .done related⟩

/-- **The reduction of (A), in terms of `run`.** -/
theorem policy_rewrites_program_iff (c : Config) (u : X) (unit : S) (program : Program S X)
    (next : Authored S X) :
    (policyGSLT c u unit).rewrites (.program program) next ↔
      ∃ n bag bag', run c.disc (progSlot c u unit program.clauses) n [] Store.empty
          (elabCfg c [] program.query) = some bag ∧
        next = .done bag' ∧ CoreEquiv (.done bag : Core S X) (.done bag') := by
  constructor
  · rintro ⟨observed, evaluates, related⟩
    cases observed with
    | program _ => exact evaluates.elim
    | done bag =>
        obtain ⟨n, defined⟩ := evaluates
        cases related with
        | done related => exact ⟨n, bag, _, defined, rfl, related⟩
  · rintro ⟨n, bag, bag', defined, rfl, related⟩
    exact ⟨.done bag, ⟨n, defined⟩, .done related⟩

/-! ## (B): the core read along the elaboration -/

/-- **(B) The core read along the elaboration of a policy.** -/
def policyRead (c : Config) (u : X) (unit : S) : GSLT.{max u v} :=
  (coreGSLT S X).readAlong (elabState c u unit)

/-- **(A) and (B) have the same reduction.** -/
theorem policy_rewrites_iff_read (c : Config) (u : X) (unit : S) (term next : Authored S X) :
    (policyGSLT c u unit).rewrites term next ↔ (policyRead c u unit).rewrites term next :=
  policy_rewrites_iff c u unit term next

/-- **The static equivalence of (A) is contained in that of (B).** -/
theorem policy_equations_read (c : Config) (u : X) (unit : S) {first second : Authored S X}
    (equivalent : (policyGSLT c u unit).equations.r first second) :
    (policyRead c u unit).equations.r first second :=
  AuthoredEquiv.elabState c u unit equivalent

/-- The readings are closed under reduction: every reduct of an elaboration is
an observation, and an observation is the elaboration of itself. -/
theorem elabState_readingClosed (c : Config) (u : X) (unit : S) :
    GSLT.ReadingClosed (target := coreGSLT S X) (elabState c u unit) := by
  intro origin value step
  obtain ⟨bag, rfl⟩ := core_rewrites_target step
  exact ⟨.done bag, .refl _⟩

/-! ## The maps -/

/-- **The elaboration out of (B)**, as a map of theories into the core. -/
def kernelElaboration (c : Config) (u : X) (unit : S) :
    ContextMap (policyRead c u unit).termsAlone (coreTheory S X) :=
  GSLT.reading (target := coreGSLT S X) (elabState c u unit)

/-- **The elaboration out of (B) is hosting.** -/
theorem kernelElaboration_hosting (c : Config) (u : X) (unit : S) :
    (kernelElaboration (S := S) c u unit).Hosting :=
  GSLT.reading_hosting (target := coreGSLT S X) (elabState c u unit)
    (elabState_readingClosed c u unit)

/-- **For which static equivalence on authored text the elaboration is
hosting**: exactly for the induced one.  At any static equivalence on authored
terms that the elaboration respects, the elaboration is a hosting map into the
core if and only if two terms with equivalent elaborations are equivalent. -/
theorem elaboration_hosting_iff (c : Config) (u : X) (unit : S) (static : Setoid (Authored S X))
    (respects : ∀ {first second : Authored S X}, static.r first second →
      (coreGSLT S X).equations.r (elabState c u unit first) (elabState c u unit second)) :
    (GSLT.readingWith (target := coreGSLT S X) (elabState c u unit) static respects).Hosting ↔
      ∀ first second : Authored S X,
        CoreEquiv (elabState c u unit first) (elabState c u unit second) → static.r first second :=
  (GSLT.readingWith_hosting_iff (target := coreGSLT S X) (elabState c u unit) static respects).trans
    ⟨fun both => both.1, fun reflects => ⟨reflects, elabState_readingClosed c u unit⟩⟩

/-- **The elaboration out of (A)**, as a map of theories into the core. -/
def elaboration (c : Config) (u : X) (unit : S) :
    ContextMap (policyGSLT c u unit).termsAlone (coreTheory S X) :=
  ContextMap.betweenTerms (source := policyGSLT c u unit) (target := coreGSLT S X)
    (elabState c u unit) (AuthoredEquiv.elabState c u unit)

/-- The elaboration out of (A) sends steps to steps. -/
theorem elaboration_preserves (c : Config) (u : X) (unit : S) :
    (elaboration (S := S) c u unit).PreservesTransitions := by
  apply (ContextMap.preservesTransitions_iff_rewrites _).mpr
  intro interface term next step
  exact (policy_rewrites_iff c u unit term next).mp step

/-- The elaboration out of (A) lifts every step of an elaboration. -/
theorem elaboration_reflects (c : Config) (u : X) (unit : S) :
    (elaboration (S := S) c u unit).ReflectsTransitions := by
  apply (ContextMap.reflectsTransitions_iff_rewrites _).mpr
  intro interface term next step
  obtain ⟨bag, rfl⟩ := core_rewrites_target step
  exact ⟨.done bag, (policy_rewrites_iff c u unit term (.done bag)).mpr step, .refl _⟩

/-- The elaboration out of (A), as a morphism of theories. -/
def elaborationMorphism (c : Config) (u : X) (unit : S) :
    ContextMorphism (policyGSLT c u unit).termsAlone (coreTheory S X) :=
  ContextMorphism.ofTransitions (elaboration c u unit) (elaboration_preserves c u unit)
    (elaboration_reflects c u unit)

/-- **Every probe sees in an authored term what it sees in its elaboration**,
no more and no less. -/
theorem elaboration_bisimilar_iff (c : Config) (u : X) (unit : S)
    (probe : (policyGSLT (S := S) c u unit).termsAlone.Probe) {index : probe.Index}
    {left right : (policyGSLT (S := S) c u unit).termsAlone.Term (probe.interface index)} :
    ((elaboration c u unit).push probe).Bisimilar (index := index)
        ((elaboration c u unit).term left) ((elaboration c u unit).term right) ↔
      probe.Bisimilar left right :=
  ContextMap.bisimilar_push_iff_of_transitions _ (elaboration_preserves c u unit)
    (elaboration_reflects c u unit) probe

/-- Forget the spelling: (A) to (B), the identity on terms. -/
def forgetSpelling (c : Config) (u : X) (unit : S) :
    ContextMap (policyGSLT c u unit).termsAlone (policyRead c u unit).termsAlone :=
  ContextMap.betweenTerms (source := policyGSLT c u unit) (target := policyRead c u unit)
    (fun term => term) (fun equivalent => policy_equations_read c u unit equivalent)

/-- Forgetting the spelling changes no step. -/
theorem forgetSpelling_preserves (c : Config) (u : X) (unit : S) :
    (forgetSpelling (S := S) c u unit).PreservesTransitions := by
  apply (ContextMap.preservesTransitions_iff_rewrites _).mpr
  intro interface term next step
  exact (policy_rewrites_iff_read c u unit term next).mp step

theorem forgetSpelling_reflects (c : Config) (u : X) (unit : S) :
    (forgetSpelling (S := S) c u unit).ReflectsTransitions := by
  apply (ContextMap.reflectsTransitions_iff_rewrites _).mpr
  intro interface term next step
  exact ⟨next, (policy_rewrites_iff_read c u unit term next).mpr step,
    (policyRead c u unit).equations.iseqv.refl next⟩

/-- **(B) has nothing that (A) does not**: forgetting the spelling is
exhausting. -/
theorem forgetSpelling_exhausting (c : Config) (u : X) (unit : S) :
    (forgetSpelling (S := S) c u unit).Exhausting :=
  (ContextMap.betweenTerms_exhausting_iff (source := policyGSLT c u unit)
    (target := policyRead c u unit) (fun term => term)
    (fun equivalent => policy_equations_read c u unit equivalent)).mpr
    fun value => ⟨value, (policyRead c u unit).equations.iseqv.refl value⟩

/-! ## What (A) has and (B) does not: spellings -/

omit [DecidableEq S] in
/-- A `new` block that declares nothing elaborates as its body, under every
policy. -/
theorem elabCfg_new_nil_sym (c : Config) (root : Owner) (s : S) :
    elabCfg c root (.new [] (.sym s) : Src S X) = elabCfg c root (.sym s) := by
  obtain ⟨ownership, lifetime, readout⟩ := c
  cases ownership <;> cases lifetime <;> rfl

/-- The program whose query is `(new () s)`, with no equation. -/
def blockProgram (s : S) : Program S X := ⟨fun _ => none, .new [] (.sym s)⟩

/-- The program whose query is `s`, with no equation. -/
def bareProgram (s : S) : Program S X := ⟨fun _ => none, .sym s⟩

omit [DecidableEq X] [DecidableEq S] in
theorem blockProgram_ne_bareProgram (s : S) : (blockProgram s : Program S X) ≠ bareProgram s := by
  intro same
  have queries := congrArg Program.query same
  cases queries

omit [DecidableEq S] in
/-- **Two texts with one elaboration, under every policy.** -/
theorem spellings_one_elaboration (c : Config) (u : X) (unit : S) (s : S) :
    elabState c u unit (.program (blockProgram s)) = elabState c u unit (.program (bareProgram s)) := by
  simp only [elabState, blockProgram, bareProgram, elabCfg_new_nil_sym]

omit [DecidableEq S] in
/-- They are apart in (A). -/
theorem spellings_apart (s : S) :
    ¬ AuthoredEquiv (.program (blockProgram s) : Authored S X) (.program (bareProgram s)) :=
  fun equivalent => blockProgram_ne_bareProgram s equivalent.program_eq

/-- **The static equivalence of (A) is strictly finer than that of (B).** -/
theorem policy_equations_strict (c : Config) (u : X) (unit : S) (s : S) :
    (policyRead c u unit).equations.r (.program (blockProgram s)) (.program (bareProgram s)) ∧
      ¬ (policyGSLT c u unit).equations.r (.program (blockProgram s))
        (.program (bareProgram s)) :=
  ⟨by
    show CoreEquiv _ _
    rw [spellings_one_elaboration]
    exact .refl _, spellings_apart s⟩

/-- **The elaboration out of (A) is not hosting**: it identifies two texts that
(A) keeps apart. -/
theorem elaboration_not_hosting (c : Config) (u : X) (unit : S) (s : S) :
    ¬ (elaboration (S := S) c u unit).Hosting :=
  ContextMap.not_hosting_of_identifies (elaboration c u unit) (origin := PUnit.unit)
    (first := Authored.program (blockProgram s)) (second := Authored.program (bareProgram s))
    (spellings_apart s) (policy_equations_strict c u unit s).1

/-- **Forgetting the spelling is not hosting**: that is what (A) has and (B)
does not. -/
theorem forgetSpelling_not_hosting (c : Config) (u : X) (unit : S) (s : S) :
    ¬ (forgetSpelling (S := S) c u unit).Hosting :=
  ContextMap.not_hosting_of_identifies (forgetSpelling c u unit) (origin := PUnit.unit)
    (first := Authored.program (blockProgram s)) (second := Authored.program (bareProgram s))
    (spellings_apart s) (policy_equations_strict c u unit s).1

/-- Positive, for (A): the program `s` steps to the observation of `s`, under
every policy. -/
theorem bareProgram_steps (c : Config) (u : X) (unit : S) (s : S) :
    (policyGSLT c u unit).rewrites (.program (bareProgram s))
      (.done [(.sym s, Store.empty)]) := by
  refine ⟨.done [(.sym s, Store.empty)], ⟨1, ?_⟩, .refl _⟩
  obtain ⟨ownership, lifetime, readout⟩ := c
  cases ownership <;> cases lifetime <;> rfl

/-- Negative, for (A): an observation has no step. -/
theorem policy_rewrites_done (c : Config) (u : X) (unit : S) (bag : Result S (Slot X))
    (next : Authored S X) : ¬ (policyGSLT c u unit).rewrites (.done bag) next := by
  rintro ⟨observed, evaluates, -⟩
  cases observed <;> exact evaluates.elim

/-! ## The image -/

omit [DecidableEq S] in
/-- Query-wide elaboration never writes contextual code at its root. -/
theorem elabQ_ne_ctx : ∀ (t : Src S X) (env : REnv X) (pos : Owner) (ks : List (Nm (Slot X)))
    (body : Tm S (Slot X)), elabQ env pos t ≠ .ctx ks body
  | .sym _, _, _, _, _ => by simp [elabQ]
  | .fn _, _, _, _, _ => by simp [elabQ]
  | .sv _, _, _, _, _ => by simp [elabQ, slotVar]
  | .par _, _, _, _, _ => by simp [elabQ]
  | .lam _ _ _, _, _, _, _ => by simp [elabQ]
  | .form _ _, _, _, _, _ => by simp [elabQ, formedLam]
  | .app _ _, _, _, _, _ => by simp [elabQ]
  | .quote _, _, _, _, _ => by simp [elabQ]
  | .pquote _, _, _, _, _ => by simp [elabQ]
  | .letS _ _ _ _, _, _, _, _ => by
      simp only [elabQ]
      split <;> simp
  | .unify _ _ _, _, _, _, _ => by simp [elabQ]
  | .alt _ _, _, _, _, _ => by simp [elabQ]
  | .new [] inner, env, pos, ks, body => by
      simpa [elabQ] using elabQ_ne_ctx inner env (pos ++ [0]) ks body
  | .new (_ :: _) _, _, _, _, _ => by simp [elabQ, newBlock]

omit [DecidableEq S] in
/-- Rule M never writes contextual code at its root. -/
theorem elabMS_ne_ctx : ∀ (t : Src S X) (E : List X) (env : REnv X) (pos : Owner)
    (ks : List (Nm (Slot X))) (body : Tm S (Slot X)), elabMS E env pos t ≠ .ctx ks body
  | .sym _, _, _, _, _, _ => by simp [elabMS]
  | .fn _, _, _, _, _, _ => by simp [elabMS]
  | .sv _, _, _, _, _, _ => by simp [elabMS, slotVar]
  | .par _, _, _, _, _, _ => by simp [elabMS]
  | .lam _ _ _, _, _, _, _, _ => by simp [elabMS]
  | .form _ _, _, _, _, _, _ => by simp [elabMS, formedLam]
  | .app _ _, _, _, _, _, _ => by simp [elabMS]
  | .quote _, _, _, _, _, _ => by simp [elabMS]
  | .pquote _, _, _, _, _, _ => by simp [elabMS]
  | .letS _ _ _ _, _, _, _, _, _ => by
      simp only [elabMS]
      split <;> simp
  | .unify _ _ _, _, _, _, _, _ => by simp [elabMS]
  | .alt _ _, _, _, _, _, _ => by simp [elabMS]
  | .new [] inner, E, env, pos, ks, body => by
      simpa [elabMS] using elabMS_ne_ctx inner E env (pos ++ [0]) ks body
  | .new (_ :: _) _, _, _, _, _, _ => by simp [elabMS, newBlock]

omit [DecidableEq S] in
/-- Explicit capture never writes contextual code at its root. -/
theorem elabEC_ne_ctx : ∀ (t : Src S X) (env : REnv X) (pos : Owner) (ks : List (Nm (Slot X)))
    (body : Tm S (Slot X)), elabEC env pos t ≠ .ctx ks body
  | .sym _, _, _, _, _ => by simp [elabEC]
  | .fn _, _, _, _, _ => by simp [elabEC]
  | .sv _, _, _, _, _ => by simp [elabEC, slotVar]
  | .par _, _, _, _, _ => by simp [elabEC]
  | .lam _ _ _, _, _, _, _ => by simp [elabEC]
  | .form _ _, _, _, _, _ => by simp [elabEC, formedLam]
  | .app _ _, _, _, _, _ => by simp [elabEC]
  | .quote _, _, _, _, _ => by simp [elabEC]
  | .pquote _, _, _, _, _ => by simp [elabEC]
  | .letS _ _ _ _, _, _, _, _ => by
      simp only [elabEC]
      split <;> simp
  | .unify _ _ _, _, _, _, _ => by simp [elabEC]
  | .alt _ _, _, _, _, _ => by simp [elabEC]
  | .new [] inner, env, pos, ks, body => by
      simpa [elabEC] using elabEC_ne_ctx inner env (pos ++ [0]) ks body
  | .new (_ :: _) _, _, _, _, _ => by simp [elabEC, newBlock]

omit [DecidableEq S] in
/-- Lexical fresh never writes contextual code at its root. -/
theorem elabLF_ne_ctx : ∀ (t : Src S X) (env : REnv X) (cr : List X) (pos : Owner)
    (ks : List (Nm (Slot X))) (body : Tm S (Slot X)), elabLF env cr pos t ≠ .ctx ks body
  | .sym _, _, _, _, _, _ => by simp [elabLF]
  | .fn _, _, _, _, _, _ => by simp [elabLF]
  | .sv _, _, _, _, _, _ => by simp [elabLF, slotVar]
  | .par _, _, _, _, _, _ => by simp [elabLF]
  | .lam _ _ _, _, _, _, _, _ => by simp [elabLF]
  | .form _ _, _, _, _, _, _ => by simp [elabLF, formedLam]
  | .app _ _, _, _, _, _, _ => by simp [elabLF]
  | .quote _, _, _, _, _, _ => by simp [elabLF]
  | .pquote _, _, _, _, _, _ => by simp [elabLF]
  | .letS _ _ _ _, _, _, _, _, _ => by
      simp only [elabLF]
      split <;> simp
  | .unify _ _ _, _, _, _, _, _ => by simp [elabLF]
  | .alt _ _, _, _, _, _, _ => by simp [elabLF]
  | .new [] inner, env, cr, pos, ks, body => by
      simpa [elabLF] using elabLF_ne_ctx inner env cr (pos ++ [0]) ks body
  | .new (_ :: _) _, _, _, _, _, _ => by simp [elabLF, newBlock]

omit [DecidableEq S] in
/-- No ownership policy writes contextual code at the root of a form. -/
theorem elabForm_ne_ctx (ownership : Ownership) (root : Owner) (t : Src S X)
    (ks : List (Nm (Slot X))) (body : Tm S (Slot X)) : elabForm ownership root t ≠ .ctx ks body := by
  cases ownership
  · exact elabQ_ne_ctx t _ _ ks body
  · exact elabMS_ne_ctx t _ _ _ ks body
  · exact elabLF_ne_ctx t _ _ _ ks body
  · exact elabEC_ne_ctx t _ _ ks body

omit [DecidableEq S] [DecidableEq X] in
/-- Hoisting own lists keeps the root of a term. -/
theorem hoistOwn_ctx {Y : Type v} {t : Tm S Y} {ks : List (Nm Y)} {body : Tm S Y}
    (same : (hoistOwn t).1 = .ctx ks body) : t = .ctx ks body := by
  cases t <;> simp_all [hoistOwn]

omit [DecidableEq S] in
/-- **No policy elaborates a text to contextual code.** -/
theorem elabCfg_ne_ctx (c : Config) (root : Owner) (t : Src S X) (ks : List (Nm (Slot X)))
    (body : Tm S (Slot X)) : elabCfg c root t ≠ .ctx ks body := by
  obtain ⟨ownership, lifetime, readout⟩ := c
  cases lifetime
  · exact elabForm_ne_ctx ownership root t ks body
  · intro same
    exact elabForm_ne_ctx ownership root t ks body (hoistOwn_ctx same)

/-- The other discipline. -/
def otherDisc : Disc → Disc
  | .static => .copyAtCall
  | .copyAtCall => .static

theorem otherDisc_ne (d : Disc) : otherDisc d ≠ d := by
  cases d <;> simp [otherDisc]

omit [DecidableEq S] in
/-- A judgment under the other discipline is the elaboration of no term, up to
the static equivalence. -/
theorem elabState_ne_otherDisc (c : Config) (u : X) (unit : S) (origin : Authored S X)
    (prog : S → Option (Tm S (Slot X))) (t : Tm S (Slot X)) :
    ¬ CoreEquiv (elabState c u unit origin) (.run (otherDisc c.disc) prog t) := by
  intro equivalent
  have same := coreEquiv_discipline equivalent
  cases origin with
  | program program =>
      exact otherDisc_ne c.disc (Option.some.inj same).symm
  | done bag => cases same

omit [DecidableEq S] in
/-- A judgment whose query is contextual code is the elaboration of no term,
up to the static equivalence. -/
theorem elabState_ne_ctx (c : Config) (u : X) (unit : S) (origin : Authored S X) (d : Disc)
    (prog : S → Option (Tm S (Slot X))) (ks : List (Nm (Slot X))) (body : Tm S (Slot X)) :
    ¬ CoreEquiv (elabState c u unit origin) (.run d prog (.ctx ks body)) := by
  intro equivalent
  have alone : ∀ other, ¬ CoreLink (.run d prog (.ctx ks body) : Core S X) other := by
    intro other link
    obtain ⟨-, _, _, reading, program, -, -, same⟩ := link.run_left
    exact elabCfg_ne_ctx reading.config [] program.query ks body same.symm
  have same := coreEquiv_eq_of_unlinked alone equivalent.symm
  cases origin with
  | program program =>
      simp only [elabState, Core.run.injEq] at same
      exact elabCfg_ne_ctx c [] program.query ks body same.2.2.symm
  | done bag => cases same

/-- **The elaboration out of (A) is not exhausting.** -/
theorem elaboration_not_exhausting (c : Config) (u : X) (unit : S) (s : S) :
    ¬ (elaboration (S := S) c u unit).Exhausting := by
  intro exhausting
  obtain ⟨origin, related⟩ :=
    (ContextMap.betweenTerms_exhausting_iff (source := policyGSLT c u unit)
      (target := coreGSLT S X) (elabState c u unit) (AuthoredEquiv.elabState c u unit)).mp
      exhausting (.run (otherDisc c.disc) (fun _ => none) (.sym s))
  exact elabState_ne_otherDisc c u unit origin _ _ related

/-- **The elaboration out of (B) is not exhausting, even at the policy's own
discipline**: a judgment whose query is contextual code is no elaboration. -/
theorem kernelElaboration_not_exhausting (c : Config) (u : X) (unit : S) (s : S) :
    ¬ (kernelElaboration (S := S) c u unit).Exhausting := by
  intro exhausting
  obtain ⟨origin, related⟩ :=
    (GSLT.reading_exhausting_iff (target := coreGSLT S X) (elabState c u unit)).mp
      exhausting (.run c.disc (fun _ => none) (.ctx [] (.sym s)))
  exact elabState_ne_ctx c u unit origin _ _ _ _ related

#print axioms policyGSLT
#print axioms policy_rewrites_iff
#print axioms policy_rewrites_iff_read
#print axioms policy_equations_strict
#print axioms kernelElaboration_hosting
#print axioms elaboration_hosting_iff
#print axioms elaboration_preserves
#print axioms elaboration_reflects
#print axioms elaboration_bisimilar_iff
#print axioms elaboration_not_hosting
#print axioms forgetSpelling_exhausting
#print axioms forgetSpelling_not_hosting
#print axioms elabCfg_ne_ctx
#print axioms elaboration_not_exhausting
#print axioms kernelElaboration_not_exhausting

end Mettapedia.GSLT.LanguageDef.ScopePolicies
