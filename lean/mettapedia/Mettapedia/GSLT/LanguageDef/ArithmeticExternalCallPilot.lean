import Mettapedia.GSLT.LanguageDef.ArithmeticExtension
import Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting

/-!
# Arithmetic GSLT to external-call-machine pilot

This module instantiates the sealed two-sided hosting criterion
(`BehavioralHosting`: forward preservation plus no-invention at one declared
observation) for the smallest useful compilation pipeline with an explicit
libcall-lowering target: the shared exact-integer arithmetic core hosted by a
guarded external-call machine parameterized by an independent external-call
relation.

## What is claimed, and what is not

* The subject is the **typed arithmetic core** — seven operations on exact
  integers, four partial at a zero divisor — not any surface syntax.  No lexical or parsing claim is
  made here; surface operators are treated only in the elaboration layer,
  which maps dialect surface forms into the single shared core.
* The target models a guarded calling discipline: a guard, an
  external relation with a contractual precondition, and a halt.  An
  unguarded external call at a zero divisor has **no step**: the undefined
  behavior of the external library is represented as stuckness, never as an
  invented result.
* Hosting is conditional on an explicit `ExternalCallAdequacy` witness.  The
  target transition relation never invokes the source evaluator.  GMP, an
  emitted C program, and a live CeTTa path therefore remain distinct
  realization obligations rather than being validated by definition.
* Emitted C text (the printer at the end of this file) is a separate,
  unverified boundary, exercised by differential execution against the live
  runtime; the theorems here are about the target machine, not the text.

## The dialect facts this file is faithful to

Measured against the live runtime (2026-08-25), integer surface operators
elaborate differently per dialect while sharing one arithmetic core:

* `he-compat` `/` is the truncating quotient (`7 / 2 = 3`), and `//` is not
  grounded at all — the expression stays **inert**.
* `he` and `prime` `/` on non-divisible integers leaves the exact-integer
  core entirely (float fallback), so it does not elaborate into this core.
* `petta` `%` is the floor remainder (`-7 % 2 = 1`); `he`/`prime` `%` is the
  truncated remainder (`-7 % 2 = -1`).
* Every dialect observes a zero divisor as a `DivisionByZero` error today;
  an abstention observation is a candidate dialect policy, expressible here
  as a post-composition on the same core outcome.
-/

namespace Mettapedia.GSLT.LanguageDef.ArithmeticExternalCallPilot

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger

/-! ## Shared-core fingerprints

Each example matches a probe of the live runtime (2026-08-25): truncating
quotient for `he-compat` `/`, flooring quotient for `//`, truncated remainder
for `he`/`prime` `%`, floor remainder for `petta` `%`, and the declined zero
divisor that every dialect currently observes as `DivisionByZero`. -/

example : coreSem .tquot 7 2 = .val 3 := by decide
example : coreSem .tquot (-7) 2 = .val (-3) := by decide
example : coreSem .fquot (-7) 2 = .val (-4) := by decide
example : coreSem .trem (-7) 2 = .val (-1) := by decide
example : coreSem .frem (-7) 2 = .val 1 := by decide
example : coreSem .trem (-7) 0 = .declined := by decide
example : coreSem .add 2 3 = .val 5 := by decide

/-! ## The source machine: one-step evaluation of a core application -/

/-- Source terms: a pending application, or a finished outcome. -/
inductive ATerm : Type
  | prog (op : CoreOp) (a b : Int)
  | done (op : CoreOp) (a b : Int) (o : Outcome)
  deriving DecidableEq

/-- The source step: evaluate the application by the shared semantics. -/
inductive AStep : ATerm → ATerm → Prop
  | run (op : CoreOp) (a b : Int) :
      AStep (.prog op a b) (.done op a b (coreSem op a b))

/-- Intrinsic source-state meaning.  A pending typed request is meaningful;
a finished request is meaningful only when its retained operands and result
agree with the arithmetic semantics. -/
inductive SourceMeaning : ATerm → Prop
  | prog (op : CoreOp) (a b : Int) : SourceMeaning (.prog op a b)
  | doneDeclined {op : CoreOp} {a b : Int} (h : undefinedAt op b) :
      SourceMeaning (.done op a b .declined)
  | doneValue {op : CoreOp} {a b : Int} (h : ¬ undefinedAt op b) :
      SourceMeaning (.done op a b (.val (op.fn a b)))

private def eqSetoid (α : Type) : Setoid α :=
  ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

/-- The arithmetic core as a GSLT with syntactic equality. -/
def arithGSLT : GSLT where
  Term := ATerm
  equations := eqSetoid ATerm
  rewrites := AStep
  rewrites_resp_left := by
    intro t t' u ht hw
    cases ht; exact ⟨u, hw, rfl⟩
  rewrites_resp_right := by
    intro t u u' hw hu
    cases hu; exact hw

/-! ## The target machine: ExternalCall

A guarded external-call discipline.  `start` dispatches: at the undefined
point of a partial operation the guard halts with `declined`; otherwise
control passes to an independently supplied external relation.  This follows
Bedrock2's `ExtSpec` boundary in the smallest form needed by the pilot. -/

/-- Target instructions are not source operations with a C name attached.
They are the complete operation family understood by this external-call target.
The compiler below must establish their correspondence with `CoreOp`; the
printer later consumes only this target syntax. -/
inductive CompiledOp where
  | add | sub | mul
  | tquot | fquot | trem | frem
  deriving DecidableEq, Repr

/-- The guard is target structure.  A malformed unguarded division
instruction has no constructor. -/
def CompiledOp.guard : CompiledOp → Bool
  | .add | .sub | .mul => false
  | .tquot | .fquot | .trem | .frem => true

/-- Independent mathematical contract of each target external symbol. -/
def CompiledOp.fn : CompiledOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .tquot, a, b => Int.tdiv a b
  | .fquot, a, b => Int.fdiv a b
  | .trem, a, b => Int.tmod a b
  | .frem, a, b => Int.fmod a b

def CompiledOp.undefinedAt (program : CompiledOp) (second : Int) : Prop :=
  program.guard = true ∧ second = 0

instance (program : CompiledOp) (second : Int) :
    Decidable (program.undefinedAt second) := by
  unfold CompiledOp.undefinedAt
  infer_instance

/-- The only source-to-target operation compiler. -/
def compileSyntax : CoreOp → CompiledOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .tquot => .tquot
  | .fquot => .fquot
  | .trem => .trem
  | .frem => .frem

@[simp] theorem compileSyntax_guard (op : CoreOp) :
    (compileSyntax op).guard = op.isPartial := by
  cases op <;> rfl

@[simp] theorem compileSyntax_fn (op : CoreOp) :
    (compileSyntax op).fn = op.fn := by
  cases op <;> rfl

@[simp] theorem compileSyntax_undefinedAt (op : CoreOp) (second : Int) :
    (compileSyntax op).undefinedAt second ↔ undefinedAt op second := by
  cases op <;> rfl

/-- A relational external implementation of one exact-integer call.  It is
deliberately independent of `coreSem`: a concrete GMP/C/CeTTa implementation
must establish its own adequacy witness. -/
abbrev ExternalCallSpec := CompiledOp → Int → Int → Int → Prop

/-- The exact source/target bridge required of an external implementation.
Completeness supplies the compiled forward route; soundness rules out an
invented return.  Neither field is stored in the target transition relation. -/
structure ExternalCallAdequacy (external : ExternalCallSpec) : Prop where
  complete : ∀ (program : CompiledOp) (a b : Int),
    ¬ program.undefinedAt b → external program a b (program.fn a b)
  sound : ∀ {program : CompiledOp} {a b z : Int},
    external program a b z → z = program.fn a b

/-- A mathematical reference external used only for theorem canaries.  It is
not the GMP, emitted-C, or CeTTa realization. -/
def referenceExternal : ExternalCallSpec :=
  fun program a b z => z = program.fn a b

def referenceExternalAdequacy : ExternalCallAdequacy referenceExternal where
  complete := by intro _ _ _ _; rfl
  sound := fun h => h

/-- An implementation that shifts every answer cannot satisfy the external
adequacy boundary.  This prevents target correctness from becoming a
tautological self-validation. -/
def shiftedExternal : ExternalCallSpec :=
  fun program a b z => z = program.fn a b + 1

theorem shiftedExternal_not_adequate :
    ¬ ExternalCallAdequacy shiftedExternal := by
  intro adequate
  have returned := adequate.complete .add 0 1 (by decide)
  simp [shiftedExternal, CompiledOp.fn] at returned

inductive CTerm : Type
  | start (program : CompiledOp) (a b : Int)
  | callExt (program : CompiledOp) (a b : Int)
  | halted (program : CompiledOp) (a b : Int) (o : Outcome)
  deriving DecidableEq

inductive CStep (external : ExternalCallSpec) : CTerm → CTerm → Prop
  | toFault {program : CompiledOp} {a b : Int}
      (h : program.undefinedAt b) :
      CStep external (.start program a b) (.halted program a b .declined)
  | toCall {program : CompiledOp} {a b : Int}
      (h : ¬ program.undefinedAt b) :
      CStep external (.start program a b) (.callExt program a b)
  | callRet {program : CompiledOp} {a b z : Int}
      (h : ¬ program.undefinedAt b) (returned : external program a b z) :
      CStep external (.callExt program a b) (.halted program a b (.val z))

/-- Meaningful target states carry the phase invariant.  In particular, a
call state proves the domain guard and a returned state carries evidence from
the independent external relation. -/
inductive TargetMeaning (external : ExternalCallSpec) : CTerm → Prop
  | start (program : CompiledOp) (a b : Int) :
      TargetMeaning external (.start program a b)
  | callExt {program : CompiledOp} {a b : Int}
      (h : ¬ program.undefinedAt b) :
      TargetMeaning external (.callExt program a b)
  | haltedDeclined {program : CompiledOp} {a b : Int}
      (h : program.undefinedAt b) :
      TargetMeaning external (.halted program a b .declined)
  | haltedValue {program : CompiledOp} {a b z : Int}
      (h : ¬ program.undefinedAt b) (returned : external program a b z) :
      TargetMeaning external (.halted program a b (.val z))

example : TargetMeaning referenceExternal (.callExt .add 2 3) :=
  .callExt (by decide)

example : ¬ TargetMeaning referenceExternal (.callExt .tquot 1 0) := by
  intro meaningful
  cases meaningful with
  | callExt h => exact h (by decide)

def externalCallGSLT (external : ExternalCallSpec) : GSLT where
  Term := CTerm
  equations := eqSetoid CTerm
  rewrites := CStep external
  rewrites_resp_left := by
    intro t t' u ht hw
    cases ht; exact ⟨u, hw, rfl⟩
  rewrites_resp_right := by
    intro t u u' hw hu
    cases hu; exact hw

/-! ## Declared observation

Both machines are observed the same way: the outcome carried by a finished
final term, and nothing else.  Answer identity — not step counts, not
internal call structure — is the declared observation of this pilot. -/

def aObs : ATerm → Option Outcome
  | .prog _ _ _ => none
  | .done _ _ _ o => some o

def cObs : CTerm → Option Outcome
  | .start _ _ _ => none
  | .callExt _ _ _ => none
  | .halted _ _ _ o => some o

def sourceObject : ObservedOperationalObject Outcome where
  operational := ⟨arithGSLT, SourceMeaning⟩
  observe := fun {_ last} _ => aObs last

def targetObject (external : ExternalCallSpec) :
    ObservedOperationalObject Outcome where
  operational := ⟨externalCallGSLT external, TargetMeaning external⟩
  observe := fun {_ last} _ => cObs last

/-! ## The compiler -/

def compileTerm : ATerm → CTerm
  | .prog op a b => .start (compileSyntax op) a b
  | .done op a b o => .halted (compileSyntax op) a b o

/-- One route step in the target. -/
private def one {external : ExternalCallSpec} {s t : CTerm}
    (h : CStep external s t) :
    ExecutionPath (externalCallGSLT external) s t :=
  .cons ⟨h⟩ (.refl t)

/-- Two route steps in the target. -/
private def two {external : ExternalCallSpec} {s m t : CTerm}
    (h₁ : CStep external s m) (h₂ : CStep external m t) :
    ExecutionPath (externalCallGSLT external) s t :=
  .cons ⟨h₁⟩ (.cons ⟨h₂⟩ (.refl t))

/-- Inversion: the only step from an application evaluates it. -/
theorem astep_inv {op : CoreOp} {a b : Int} {t : ATerm}
    (h : AStep (.prog op a b) t) :
    t = .done op a b (coreSem op a b) := by
  cases h; rfl

/-- Finished source terms are stuck. -/
theorem astep_done {op : CoreOp} {a b : Int} {o : Outcome} {t : ATerm}
    (h : AStep (.done op a b o) t) :
    False := by cases h

/-- Each source step lowers to a guarded target execution: the fault branch
is one step, the call branch is two.  This is genuine lowering — internal
step structure differs while the declared observation is preserved.  The
step hypothesis is used only propositionally (inversion), as it must be. -/
def compileStep {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external)
    {s t : ATerm} (step : AStep s t) :
    ExecutionPath (externalCallGSLT external) (compileTerm s) (compileTerm t) := by
  cases s with
  | done op a b o => exact (astep_done step).elim
  | prog op a b =>
      have ht : t = .done op a b (coreSem op a b) := astep_inv step
      subst ht
      by_cases h : undefinedAt op b
      · have targetH : (compileSyntax op).undefinedAt b :=
          (compileSyntax_undefinedAt op b).2 h
        show ExecutionPath (externalCallGSLT external) (.start (compileSyntax op) a b)
          (.halted (compileSyntax op) a b (coreSem op a b))
        rw [coreSem_pos h a]
        exact one (CStep.toFault targetH)
      · have targetH : ¬ (compileSyntax op).undefinedAt b :=
          fun bad => h ((compileSyntax_undefinedAt op b).1 bad)
        show ExecutionPath (externalCallGSLT external) (.start (compileSyntax op) a b)
          (.halted (compileSyntax op) a b (coreSem op a b))
        rw [coreSem_neg h a]
        have returned := adequate.complete (compileSyntax op) a b targetH
        rw [compileSyntax_fn] at returned
        exact two (CStep.toCall targetH)
          (CStep.callRet targetH returned)

def preservesCompiledMeaning {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external)
    {term : ATerm} (meaningful : SourceMeaning term) :
    TargetMeaning external (compileTerm term) := by
  cases meaningful with
  | prog op a b => exact .start (compileSyntax op) a b
  | doneDeclined h =>
      exact .haltedDeclined ((compileSyntax_undefinedAt _ _).2 h)
  | doneValue h =>
      rename_i op a b
      have targetH : ¬ (compileSyntax op).undefinedAt b :=
        fun bad => h ((compileSyntax_undefinedAt op b).1 bad)
      have returned := adequate.complete (compileSyntax op) a b targetH
      rw [compileSyntax_fn] at returned
      exact .haltedValue targetH returned

def realization {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external) :
    OperationalRealization arithGSLT (externalCallGSLT external) where
  mapTerm := compileTerm
  mapEquiv := by intro l r h; cases h; rfl
  mapStep := compileStep adequate

def refinement {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external) :
    Refinement sourceObject.operational (targetObject external).operational where
  realization := realization adequate
  preservesMeaning := fun _ => preservesCompiledMeaning adequate

/-- The forward compiler square: compiled executions carry the same declared
observation.  Because the observation reads only the final term, this reduces
to agreement of the observations on compiled terms. -/
def forward {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external) :
    ObservedRefinement sourceObject (targetObject external) where
  refinement := refinement adequate
  commutes := by
    intro first last _path
    cases last <;> rfl

/-! ## Inversion facts for no-invention -/

theorem no_step_from_halted {external : ExternalCallSpec}
    {program : CompiledOp} {a b : Int} {o : Outcome} {t : CTerm}
    (h : CStep external (.halted program a b o) t) :
    False := by cases h

/-- Complete executions out of a halted state are trivial. -/
theorem path_from_halted {external : ExternalCallSpec}
    {program : CompiledOp} {a b : Int} {o : Outcome} {t : CTerm}
    (path : ExecutionPath (externalCallGSLT external) (.halted program a b o) t) :
    t = .halted program a b o := by
  cases path with
  | refl => rfl
  | cons head _ => exact absurd head.down no_step_from_halted

/-- Target completeness at the declared observation: any observation reachable
from a compiled start state is the core outcome.  The target can neither miss
the outcome nor manufacture a different one — the guarded structure and the
contractual precondition leave no other observable endpoint. -/
theorem target_observation_forces_core {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external)
    {op : CoreOp} {a b : Int} {t : CTerm} {v : Outcome}
    (path : ExecutionPath (externalCallGSLT external)
      (.start (compileSyntax op) a b) t)
    (hobs : cObs t = some v) : v = coreSem op a b := by
  cases path with
  | refl => simp [cObs] at hobs
  | cons head rest =>
      cases head.down with
      | toFault h =>
          have sourceH : undefinedAt op b :=
            (compileSyntax_undefinedAt op b).1 h
          have ht := path_from_halted rest
          subst ht
          simp [cObs] at hobs
          rw [coreSem_pos sourceH a]
          exact hobs.symm
      | toCall h =>
          have sourceH : ¬ undefinedAt op b :=
            fun bad => h ((compileSyntax_undefinedAt op b).2 bad)
          cases rest with
          | refl => simp [cObs] at hobs
          | cons head₂ rest₂ =>
              cases head₂.down with
              | callRet h₂ returned =>
                  have ht := path_from_halted rest₂
                  subst ht
                  simp [cObs] at hobs
                  have hz := adequate.sound returned
                  rw [hz] at hobs
                  rw [compileSyntax_fn] at hobs
                  rw [coreSem_neg sourceH a]
                  exact hobs.symm

/-! ## The two-sided hosting theorem -/

/-- ExternalCall hosts the arithmetic core: forward preservation and no-invention
at the declared observation. This is an executable external-call instance
of the sealed hosting criterion. -/
def arithHostedByExternalCall {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external) :
    BehavioralHosting sourceObject (targetObject external) where
  forward := forward adequate
  noInvention := by
    intro initial v hprod
    obtain ⟨⟨final, path, hobs⟩⟩ := hprod
    cases initial with
    | prog op a b =>
        have hv : v = coreSem op a b :=
          target_observation_forces_core adequate path hobs
        subst hv
        exact ⟨⟨ATerm.done op a b (coreSem op a b),
          ⟨Route.cons ⟨AStep.run op a b⟩ (Route.refl _), rfl⟩⟩⟩
    | done op a b o =>
        have ht := path_from_halted path
        subst ht
        exact ⟨⟨ATerm.done op a b o, ⟨Route.refl _, hobs⟩⟩⟩

/-- The exact statement the perf lane consumes: on compiled terms, target
observations and source observations coincide. -/
theorem hosting_exact {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external)
    (initial : ATerm) (v : Outcome) :
    ProducesObservation (targetObject external) (compileTerm initial) v ↔
      ProducesObservation sourceObject initial v :=
  (arithHostedByExternalCall adequate).produces_iff initial v

/-! ## The permanent negative witness

A deterministic target that invents one behavior.  `CBad` extends ExternalCall
with a single spontaneous step from the declined halt to an invented value.
Every state still has at most one successor — determinism holds — yet
no-invention fails.  Determinism alone can never discharge the backward
direction; it must be proved against the actual step relation. -/

inductive CBadStep : CTerm → CTerm → Prop
  | lift {s t : CTerm} : CStep referenceExternal s t → CBadStep s t
  | invent : CBadStep (.halted .tquot 1 0 .declined)
      (.halted .tquot 1 0 (.val 0))

def cBadGSLT : GSLT where
  Term := CTerm
  equations := eqSetoid CTerm
  rewrites := CBadStep
  rewrites_resp_left := by
    intro t t' u ht hw
    cases ht; exact ⟨u, hw, rfl⟩
  rewrites_resp_right := by
    intro t u u' hw hu
    cases hu; exact hw

def badObject : ObservedOperationalObject Outcome where
  operational := ⟨cBadGSLT, TargetMeaning referenceExternal⟩
  observe := fun {_ last} _ => cObs last

theorem cstep_deterministic {external : ExternalCallSpec}
    (adequate : ExternalCallAdequacy external)
    {s t t' : CTerm} (h₁ : CStep external s t) (h₂ : CStep external s t') :
    t = t' := by
  cases h₁ with
  | toFault h₁ =>
      cases h₂ with
      | toFault _ => rfl
      | toCall h₂ => exact (h₂ h₁).elim
  | toCall h₁ =>
      cases h₂ with
      | toFault h₂ => exact (h₁ h₂).elim
      | toCall _ => rfl
  | callRet _ returned₁ =>
      cases h₂ with
      | callRet _ returned₂ =>
          have hz : _ = _ := (adequate.sound returned₁).trans
            (adequate.sound returned₂).symm
          cases hz
          rfl

/-- CBad is deterministic. -/
theorem cbad_deterministic {s t t' : CTerm}
    (h₁ : CBadStep s t) (h₂ : CBadStep s t') : t = t' := by
  cases h₁ with
  | lift h₁ =>
      cases h₂ with
      | lift h₂ => exact cstep_deterministic referenceExternalAdequacy h₁ h₂
      | invent => exact absurd h₁ no_step_from_halted
  | invent =>
      cases h₂ with
      | lift h₂ => exact absurd h₂ no_step_from_halted
      | invent => rfl

private def liftPath {s t : CTerm} :
    ExecutionPath (externalCallGSLT referenceExternal) s t →
      ExecutionPath cBadGSLT s t
  | .refl _ => .refl _
  | .cons head rest => .cons ⟨CBadStep.lift head.down⟩ (liftPath rest)

/-- The forward square still holds into CBad: compiled executions observe the
same values.  The defect is invisible from the forward direction. -/
def badForward : ObservedRefinement sourceObject badObject where
  refinement :=
    { realization :=
        { mapTerm := compileTerm
          mapEquiv := by intro l r h; cases h; rfl
          mapStep := fun step => liftPath
            (compileStep referenceExternalAdequacy step) }
      preservesMeaning := fun _ =>
        preservesCompiledMeaning referenceExternalAdequacy }
  commutes := by
    intro first last _path
    cases last <;> rfl

/-- CBad invents: from a compiled zero-divisor application it observes a
value the source can never produce.  Hence no `BehavioralHosting` extends
`badForward`, deterministic though CBad is. -/
theorem cbad_invents :
    ProducesObservation badObject (compileTerm (.prog .tquot 1 0)) (.val 0) ∧
      ¬ ProducesObservation sourceObject (.prog .tquot 1 0) (.val 0) := by
  constructor
  · exact ⟨⟨CTerm.halted .tquot 1 0 (.val 0),
      ⟨Route.cons ⟨CBadStep.lift (CStep.toFault (by decide))⟩
        (Route.cons ⟨CBadStep.invent⟩ (Route.refl _)), rfl⟩⟩⟩
  · rintro ⟨⟨final, path, hobs⟩⟩
    cases path with
    | refl => simp [sourceObject, aObs] at hobs
    | cons head rest =>
        cases head.down with
        | run op a b =>
            have hstuck : ∀ t,
                ¬ AStep (ATerm.done .tquot 1 0 (coreSem .tquot 1 0)) t := by
              intro t h; cases h
            cases rest with
            | refl =>
                have : coreSem .tquot 1 0 = Outcome.declined := by decide
                simp [sourceObject, aObs, this] at hobs
            | cons head₂ _ => exact absurd head₂.down (hstuck _)

theorem no_hosting_over_badForward :
    ¬ ∃ hosting : BehavioralHosting sourceObject badObject,
        hosting.forward = badForward := by
  rintro ⟨hosting, hfwd⟩
  obtain ⟨produces, refutes⟩ := cbad_invents
  have : ProducesObservation sourceObject (.prog .tquot 1 0) (.val 0) := by
    have := hosting.noInvention (.prog .tquot 1 0) (.val 0)
    rw [hfwd] at this
    exact this produces
  exact refutes this

/-! ## Dialect elaboration comes from authored sections

The sections themselves live in `ArithmeticExtension`.  This target module
consumes their successful elaborations; it does not own another dialect table.
Absence means the surface form is inert or belongs to another numeric family. -/

/-- One arithmetic: any successful typed surface lookup evaluates through the
shared `coreSem`, irrespective of the dialect section that supplied it. -/
theorem section_elaboration_factors_through_core
    (profileSection : AdmittedSection standardTheory) (spelling : String)
    (op : CoreOp)
    (found : lookup standardTheory profileSection spelling [.integer, .integer] =
      some op) (a b : Int) :
    (lookup standardTheory profileSection spelling [.integer, .integer]).map
        (fun operation => coreSem operation a b) =
      some (coreSem op a b) := by
  rw [found]
  rfl

/-! ### Undefinedness policies

The undefined point has one core identity (`Outcome.declined`) and several
dialect observations.  Each policy is a post-composition on the shared
outcome; none of them re-enters the arithmetic. -/

inductive ErrorObs : Type
  | value (z : Int)
  | errorDivisionByZero
  deriving DecidableEq, Repr

/-- Today's observation in every dialect: an explicit error atom. -/
def errorPolicy : Outcome → ErrorObs
  | .val z => .value z
  | .declined => .errorDivisionByZero

/-- The candidate Prime observation: no ordinary answer, plus a retained
decline receipt so silence stays diagnosable. -/
def abstentionPolicy : Outcome → Option Int × Bool
  | .val z => (some z, false)
  | .declined => (none, true)

/-- Policies observe the same core: they can disagree with each other only at
`declined`, never about a value. -/
theorem policies_agree_on_values (z : Int) :
    errorPolicy (.val z) = .value z ∧
      abstentionPolicy (.val z) = (some z, false) := ⟨rfl, rfl⟩

/-! ## Compiled syntax and the C printer

`CompiledOp` is the syntactic residue of `compileStep`: whether a guard is
emitted, and which external symbol is called.  The printer prints from this
object, so emitted text and proved semantics share one source of truth.  The
text itself remains an unverified boundary, checked by differential
execution. -/

/-- A total operation's compiled form can never fault. -/
theorem noGuard_no_fault {op : CoreOp} (h : (compileSyntax op).guard = false)
    (b : Int) : ¬ undefinedAt op b := by
  intro ⟨hp, _⟩
  rw [compileSyntax_guard] at h
  rw [h] at hp
  cases hp

def cSymbol : CompiledOp → String
  | .add => "mpz_add"
  | .sub => "mpz_sub"
  | .mul => "mpz_mul"
  | .tquot => "mpz_tdiv_q"
  | .fquot => "mpz_fdiv_q"
  | .trem => "mpz_tdiv_r"
  | .frem => "mpz_fdiv_r"

def opTag : CoreOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .tquot => "tquot" | .fquot => "fquot"
  | .trem => "trem" | .frem => "frem"

def cEnum : CompiledOp → String
  | .add => "CETTA_EXTERNAL_CALL_ADD"
  | .sub => "CETTA_EXTERNAL_CALL_SUB"
  | .mul => "CETTA_EXTERNAL_CALL_MUL"
  | .tquot => "CETTA_EXTERNAL_CALL_TQUOT"
  | .fquot => "CETTA_EXTERNAL_CALL_FQUOT"
  | .trem => "CETTA_EXTERNAL_CALL_TREM"
  | .frem => "CETTA_EXTERNAL_CALL_FREM"

/-- Emit one guarded C function from the compiled syntax.  The guard branch
prints the decline; the call branch invokes the GMP external named by the
same syntactic object the hosting theorem executes. -/
def emitFunction (op : CoreOp) : String :=
  let c := compileSyntax op
  let body :=
    if c.guard then
      "    if (mpz_sgn(b) == 0) { printf(\"declined\\n\"); return; }\n" ++
      "    " ++ cSymbol c ++ "(r, a, b);\n"
    else
      "    " ++ cSymbol c ++ "(r, a, b);\n"
  "static void run_" ++ opTag op ++
    "(mpz_t r, const mpz_t a, const mpz_t b) {\n" ++ body ++
    "    mpz_out_str(stdout, 10, r); printf(\"\\n\");\n}\n"

/-- A test-only library header for embedding the generated target in CeTTa's
shadow qualification.  Production arithmetic does not include this interface. -/
def emitShadowHeader : String :=
  "/* Generated test-only ExternalCall shadow interface.\n" ++
  "   It is qualification evidence, not a production evaluator. */\n" ++
  "#ifndef CETTA_EXTERNAL_CALL_SHADOW_V1_GENERATED_H\n" ++
  "#define CETTA_EXTERNAL_CALL_SHADOW_V1_GENERATED_H\n\n" ++
  "#include <gmp.h>\n\n" ++
  "typedef enum {\n" ++
  String.join (allOps.map (fun op =>
    "    " ++ cEnum (compileSyntax op) ++ ",\n")) ++
  "} CettaExternalCallOp;\n\n" ++
  "typedef enum {\n" ++
  "    CETTA_EXTERNAL_CALL_VALUE,\n" ++
  "    CETTA_EXTERNAL_CALL_DECLINED,\n" ++
  "    CETTA_EXTERNAL_CALL_INVALID_OPERATION\n" ++
  "} CettaExternalCallStatus;\n\n" ++
  "CettaExternalCallStatus cetta_external_call_shadow_eval_v1(\n" ++
  "    CettaExternalCallOp op, mpz_t result, const mpz_t lhs, const mpz_t rhs);\n\n" ++
  "#endif\n"

private def emitShadowCase (op : CoreOp) : String :=
  let c := compileSyntax op
  let guard := if c.guard then
      "        if (mpz_sgn(rhs) == 0) return CETTA_EXTERNAL_CALL_DECLINED;\n"
    else ""
  "    case " ++ cEnum c ++ ":\n" ++ guard ++
  "        " ++ cSymbol c ++ "(result, lhs, rhs);\n" ++
  "        return CETTA_EXTERNAL_CALL_VALUE;\n"

/-- Test-only embeddable C generated from the same `CompiledOp` syntax as the
standalone pilot.  Its execution is a separately qualified realization of the
target relation, not part of the Lean hosting theorem. -/
def emitShadowSource : String :=
  "#include \"tests/generated/external_call_shadow_v1.generated.h\"\n\n" ++
  "CettaExternalCallStatus cetta_external_call_shadow_eval_v1(\n" ++
  "    CettaExternalCallOp op, mpz_t result, const mpz_t lhs, const mpz_t rhs) {\n" ++
  "    switch (op) {\n" ++
  String.join (allOps.map emitShadowCase) ++
  "    default:\n" ++
  "        return CETTA_EXTERNAL_CALL_INVALID_OPERATION;\n" ++
  "    }\n}\n"

def emitProgram : String :=
  "/* ExternalCall pilot: generated from the compiled syntax of the hosted\n" ++
  "   arithmetic core.  Protocol: lines of `<op> <a> <b>`; output is the\n" ++
  "   decimal result or `declined`.  Generated text is an unverified\n" ++
  "   boundary; see ArithmeticExternalCallPilot.lean for the hosting proof. */\n" ++
  "#include <stdio.h>\n#include <string.h>\n#include <gmp.h>\n\n" ++
  String.join (allOps.map emitFunction) ++
  "\nint main(void) {\n" ++
  "    char op[16]; char abuf[4096]; char bbuf[4096];\n" ++
  "    mpz_t a, b, r; mpz_inits(a, b, r, NULL);\n" ++
  "    while (scanf(\"%15s %4095s %4095s\", op, abuf, bbuf) == 3) {\n" ++
  "        mpz_set_str(a, abuf, 10); mpz_set_str(b, bbuf, 10);\n" ++
  String.join (allOps.map (fun o =>
    "        if (strcmp(op, \"" ++ opTag o ++ "\") == 0) { run_" ++ opTag o ++
    "(r, a, b); continue; }\n")) ++
  "        printf(\"unknown-op\\n\");\n" ++
  "    }\n" ++
  "    mpz_clears(a, b, r, NULL);\n    return 0;\n}\n"

/-- Reference output for one test vector, straight from the hosted
semantics; the generated C must agree byte for byte. -/
def referenceLine (op : CoreOp) (a b : Int) : String :=
  match coreSem op a b with
  | .val z => toString z
  | .declined => "declined"

end Mettapedia.GSLT.LanguageDef.ArithmeticExternalCallPilot
