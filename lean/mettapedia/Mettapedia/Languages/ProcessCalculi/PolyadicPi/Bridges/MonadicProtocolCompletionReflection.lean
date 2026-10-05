import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPhaseReflection

/-!
# Actual interleavings of private tuple completion

The return body is the real compiler image of the identity function's
reference lookup. A finite assembly of independently scoped final phases
can complete in any actual raw execution order. Inversion retains the
supplied target process, the occurrence of each tuple, its ordered fields,
and the exact number of completed communications. Public call names may be
shared and tuple values may coincide; their private binders remain separate.

These statements concern the real directed relation before arbitrary changes
of structural representative. They are not a claim that every structural
representative has already been normalized into this assembly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Completion

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda

/-- The compiler's reference lookup after receiving argument and result. -/
def returnBody {Γ : Ctx sig} : Proc (.nm :: .nm :: Γ) :=
  out1 (.var .zero) (.var (.succ .zero))

/-- This family is derived from the actual lambda compiler, for any ambient
environment and return channel. -/
theorem identity_compiler {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) :
    compile (.lam (.var .zero)) environment result = inp2 (.var result) returnBody := rfl

/-- Metadata records occurrences, not just the set of unequal field values. -/
structure Request (Γ : Ctx sig) where
  channel : Name Γ
  first : Name Γ
  second : Name Γ
  done : Bool

def finish {Γ : Ctx sig} (request : Request Γ) : Request Γ :=
  { request with done := true }

def released {Γ : Ctx sig} (first second : Name Γ) : Proc Γ :=
  nu (nu (weaken (weaken (out1 first second))))

def render {Γ : Ctx sig} (request : Request Γ) : Proc Γ :=
  if request.done then released request.first request.second
  else secondState request.first request.second returnBody

def assembly {Γ : Ctx sig} : List (Request Γ) → Proc Γ
  | [] => nil
  | request :: rest => par (render request) (assembly rest)

def readback {Γ : Ctx sig} (request : Request Γ) : Proc Γ :=
  if request.done then out1 request.first request.second
  else par (out2 request.channel request.first request.second)
    (inp2 request.channel returnBody)

def readbackAssembly {Γ : Ctx sig} : List (Request Γ) → Proc Γ
  | [] => nil
  | request :: rest => par (readback request) (readbackAssembly rest)

def waiting {Γ : Ctx sig} : List (Request Γ) → Nat
  | [] => 0
  | request :: rest => (if request.done then 0 else 1) + waiting rest

def tupleFields {Γ : Ctx sig} (requests : List (Request Γ)) :
    List (Name Γ × Name Γ × Name Γ) :=
  requests.map (fun request => (request.channel, request.first, request.second))

theorem returnBody_open {Γ : Ctx sig} (first second : Name Γ) :
    openPair returnBody first second = out1 first second := rfl

theorem released_no_raw_step {Γ : Ctx sig} (first second : Name Γ)
    {endpoint : Proc Γ} : ¬ Step (released first second) endpoint := by
  intro step
  cases step with
  | nu outer => cases outer with
    | nu inner => exact output_no_raw_step _ _ inner

/-- A real private final communication updates this occurrence alone. -/
theorem render_raw_endpoint_iff {Γ : Ctx sig} (request : Request Γ)
    (endpoint : Proc Γ) :
    Step (render request) endpoint ↔
      request.done = false ∧ endpoint = render (finish request) := by
  cases status : request.done with
  | false =>
      simp only [render, status, Bool.false_eq_true, ↓reduceIte, finish]
      simpa only [returnBody_open, released, true_and] using
        secondState_endpoint_iff request.first request.second returnBody endpoint
  | true =>
      simp only [render, status, ↓reduceIte, Bool.true_eq_false, false_and]
      exact ⟨fun step => False.elim (released_no_raw_step _ _ step), False.elim⟩

/-- Finishing the selected tuple is the original authored binary COMM. -/
theorem readback_firing {Γ : Ctx sig} (request : Request Γ)
    (pending : request.done = false) :
    Step (readback request) (readback (finish request)) := by
  simp only [readback, pending, Bool.false_eq_true, ↓reduceIte, finish]
  exact .comm2 _ _ _ _

/-- Every actual firing from an assembly chooses one pending occurrence.
The equality describes its supplied endpoint exactly, without choosing a
different successful target execution. -/
theorem assembly_raw_step_iff {Γ : Ctx sig} (requests : List (Request Γ))
    (endpoint : Proc Γ) :
    Step (assembly requests) endpoint ↔
      ∃ (before after : List (Request Γ)) (selected : Request Γ),
        requests = before ++ selected :: after ∧ selected.done = false ∧
        endpoint = assembly (before ++ finish selected :: after) := by
  induction requests generalizing endpoint with
  | nil =>
      constructor
      · intro step
        exact False.elim (nil_no_step step)
      · rintro ⟨before, after, selected, impossible, _, _⟩
        have lengths := congrArg List.length impossible
        simp at lengths
  | cons request rest ih =>
      constructor
      · intro step
        cases status : request.done <;>
          simp only [assembly, render, status, Bool.false_eq_true, ↓reduceIte] at step
        all_goals cases step with
        | @parL _ _ changed _ firing =>
            have sourceFiring : Step (render request) changed := by
              simpa only [render, status, Bool.false_eq_true, ↓reduceIte] using firing
            obtain ⟨pending, supplied⟩ := (render_raw_endpoint_iff request _).1 sourceFiring
            exact ⟨[], rest, request, rfl, pending, by simp only [List.nil_append, assembly, supplied]⟩
        | parR _ firing =>
            obtain ⟨before, after, selected, split, pending, supplied⟩ := (ih _).1 firing
            exact ⟨request :: before, after, selected, by rw [split]; rfl,
              pending, by
                simp only [List.cons_append, assembly, supplied]
                simp only [render, status, Bool.false_eq_true, ↓reduceIte]⟩
      · rintro ⟨before, after, selected, split, pending, rfl⟩
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            obtain ⟨rfl, rfl⟩ := split
            exact .parL _ ((render_raw_endpoint_iff request _).2 ⟨pending, rfl⟩)
        | cons first before =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, restSplit⟩ := split
            exact .parR _ ((ih _).2 ⟨before, after, selected, restSplit, pending, rfl⟩)

private theorem readback_prefix_firing {Γ : Ctx sig}
    (before after : List (Request Γ)) (selected : Request Γ)
    (pending : selected.done = false) :
    Step (readbackAssembly (before ++ selected :: after))
      (readbackAssembly (before ++ finish selected :: after)) := by
  induction before with
  | nil => exact .parL _ (readback_firing selected pending)
  | cons first rest ih => exact .parR _ ih

private theorem waiting_firing {Γ : Ctx sig}
    (before after : List (Request Γ)) (selected : Request Γ)
    (pending : selected.done = false) :
    waiting (before ++ selected :: after) =
      waiting (before ++ finish selected :: after) + 1 := by
  induction before with
  | nil => simp [waiting, finish, pending, Nat.add_comm]
  | cons first rest ih => simp only [List.cons_append, waiting, ih]; omega

private theorem fields_firing {Γ : Ctx sig}
    (before after : List (Request Γ)) (selected : Request Γ) :
    tupleFields (before ++ selected :: after) =
      tupleFields (before ++ finish selected :: after) := by
  simp [tupleFields, finish]

/-- Actual target inversion also supplies a real source COMM, its exact
readback endpoint, the updated occurrence list, and the cost accounting. -/
theorem assembly_step_reflection {Γ : Ctx sig} (requests : List (Request Γ))
    {endpoint : Proc Γ} (step : Step (assembly requests) endpoint) :
    ∃ remaining : List (Request Γ),
      endpoint = assembly remaining ∧
      Step (readbackAssembly requests) (readbackAssembly remaining) ∧
      waiting requests = waiting remaining + 1 ∧
      tupleFields requests = tupleFields remaining := by
  obtain ⟨before, after, selected, rfl, pending, supplied⟩ :=
    (assembly_raw_step_iff requests endpoint).1 step
  exact ⟨before ++ finish selected :: after, supplied,
    readback_prefix_firing before after selected pending,
    waiting_firing before after selected pending, fields_firing before after selected⟩

/-- All real raw interleavings of private completions read back, including
equal requests and calls sharing the same public name. The field list keeps
each occurrence, and the supplied route's length counts the consumed tuples. -/
theorem assembly_path_reflection {Γ : Ctx sig} (requests : List (Request Γ))
    {endpoint : Proc Γ}
    (path : Route (fun p q : Proc Γ => PLift (Step p q)) (assembly requests) endpoint) :
    ∃ remaining : List (Request Γ),
      endpoint = assembly remaining ∧
      (∃ sourcePath : Route (fun p q : Proc Γ => PLift (Step p q))
        (readbackAssembly requests) (readbackAssembly remaining),
        sourcePath.length = path.length) ∧
      waiting requests = waiting remaining + path.length ∧
      tupleFields requests = tupleFields remaining := by
  generalize sourceEq : assembly requests = source at path
  induction path generalizing requests with
  | refl state =>
      exact ⟨requests, sourceEq.symm, ⟨.refl _, rfl⟩, by simp [Route.length], rfl⟩
  | cons step rest ih =>
      rw [← sourceEq] at step
      obtain ⟨middle, actualEndpoint, sourceStep, count, fields⟩ :=
        assembly_step_reflection requests step.down
      obtain ⟨remaining, endpointEq, ⟨sourceRest, sameLength⟩, restCount, restFields⟩ :=
        ih middle actualEndpoint.symm
      refine ⟨remaining, endpointEq,
        ⟨.cons ⟨sourceStep⟩ sourceRest, by simp only [Route.length, sameLength]⟩,
        ?_, fields.trans restFields⟩
      simp only [Route.length]
      omega

/-- No actual raw completion route can consume more tuple occurrences than
the assembly initially contained. -/
theorem assembly_path_length_le {Γ : Ctx sig} (requests : List (Request Γ))
    {endpoint : Proc Γ}
    (path : Route (fun p q : Proc Γ => PLift (Step p q)) (assembly requests) endpoint) :
    path.length ≤ waiting requests := by
  obtain ⟨remaining, _, _, accounting, _⟩ := assembly_path_reflection requests path
  omega

/-- Every pending tuple has an enabled actual private completion. The
statement is an operational characterization, rather than fairness assumed
of a chosen scheduler. -/
theorem assembly_raw_progress_iff {Γ : Ctx sig} (requests : List (Request Γ)) :
    (∃ target, Step (assembly requests) target) ↔ 0 < waiting requests := by
  induction requests with
  | nil =>
      exact ⟨fun ⟨_, step⟩ => False.elim (nil_no_step step), by simp [waiting]⟩
  | cons first rest ih =>
      constructor
      · rintro ⟨target, step⟩
        obtain ⟨remaining, _, _, consumed, _⟩ := assembly_step_reflection (first :: rest) step
        omega
      · intro pending
        cases status : first.done with
        | false =>
            exact ⟨assembly (finish first :: rest),
              .parL _ ((render_raw_endpoint_iff first _).2 ⟨status, rfl⟩)⟩
        | true =>
            have tailPending : 0 < waiting rest := by simpa only [waiting, status, ↓reduceIte, zero_add] using pending
            obtain ⟨target, step⟩ := ih.2 tailPending
            exact ⟨par (render first) target, .parR _ step⟩

/-- A supplied maximal execution consumes every initially pending occurrence.
An unfair prefix ending early is detected by its still-enabled real step. -/
theorem assembly_maximal_path_length {Γ : Ctx sig} (requests : List (Request Γ))
    {endpoint : Proc Γ}
    (path : Route (fun p q : Proc Γ => PLift (Step p q)) (assembly requests) endpoint)
    (maximal : ∀ target, ¬ Step endpoint target) : path.length = waiting requests := by
  obtain ⟨remaining, rfl, _, consumed, _⟩ := assembly_path_reflection requests path
  have noPending : waiting remaining = 0 := by
    by_contra notZero
    have pending : 0 < waiting remaining := Nat.pos_of_ne_zero notZero
    obtain ⟨target, step⟩ := (assembly_raw_progress_iff remaining).2 pending
    exact maximal target step
  omega

private theorem completed_assembly_readback {Γ : Ctx sig} (requests : List (Request Γ))
    (complete : waiting requests = 0) :
    StructuralEq (assembly requests) (readbackAssembly requests) := by
  induction requests with
  | nil => exact .refl _
  | cons first rest ih =>
      cases status : first.done with
      | false => simp [waiting, status] at complete
      | true =>
          have tailComplete : waiting rest = 0 := by simpa [waiting, status] using complete
          apply StructuralEq.par _ (ih tailComplete)
          simp only [render, readback, status, ↓reduceIte, released]
          exact .trans (.nu (.nuUnused _)) (.nuUnused _)

/-- Every maximal supplied raw completion route returns the selected tuples.
The corresponding source route consists of actual binary COMM events and
has precisely the same length; the final structural comparison relates the
actual target endpoint, including its private-scope representative. -/
theorem assembly_maximal_block_reflection {Γ : Ctx sig} (requests : List (Request Γ))
    {endpoint : Proc Γ}
    (path : Route (fun p q : Proc Γ => PLift (Step p q)) (assembly requests) endpoint)
    (maximal : ∀ target, ¬ Step endpoint target) :
    ∃ remaining : List (Request Γ),
      tupleFields requests = tupleFields remaining ∧
      StructuralEq endpoint (readbackAssembly remaining) ∧
      ∃ sourcePath : Route (fun p q : Proc Γ => PLift (Step p q))
        (readbackAssembly requests) (readbackAssembly remaining),
        sourcePath.length = path.length ∧ sourcePath.length = waiting requests := by
  obtain ⟨remaining, endpointEq, ⟨sourcePath, sameLength⟩, consumed, fields⟩ :=
    assembly_path_reflection requests path
  have fullLength := assembly_maximal_path_length requests path maximal
  have complete : waiting remaining = 0 := by omega
  exact ⟨remaining, fields, endpointEq ▸ completed_assembly_readback remaining complete,
    sourcePath, sameLength, sameLength.trans fullLength⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Completion
