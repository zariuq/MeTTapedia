import Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan

/-!
# The gradual guarantee for Prime execution plans (model level)

Siek, Vitousek, Cimini, and Boyland state the gradual guarantee in two halves:
removing type annotations from a well-typed program keeps it well-typed
(static), and removing annotations does not change the program's behaviour
except possibly by removing blame (dynamic).

`GradualExecutionPlan` already separates a raw term from optional typed and
suspended-check decorations and runs every plan by raw erasure.  This module
adds the missing ingredient — a precision order on plans — and proves the
dynamic half for that model: execution and cost are invariant along
precision, and every plan is at least as precise as its raw erasure.

What is *not* proved here, because the model does not yet contain it: blame
monotonicity (a more precise plan produces at least as much blame as a less
precise one).  That requires an order on checker outcomes; it is the honest
remaining obligation for calling Prime's Need layer a gradual type theory
in the sense of New–Licata–Ahmed, and it is recorded as such in the
research-spec draft rather than assumed.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GradualGuarantee

open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan

universe uRaw uTy uKey uObligation uOutput

variable {Raw : Type uRaw} {Ty : Type uTy} {HasType : Raw → Ty → Prop}
  {Key : Type uKey} {Obligation : Type uObligation}

/-- `MoreDynamic p q`: `p` carries no more guarantees than `q` about the same
raw term.  The raw plan is the least precise; typed and checked plans refine
it; precision is reflexive. -/
inductive MoreDynamic :
    Plan Raw Ty HasType Key Obligation → Plan Raw Ty HasType Key Obligation → Prop
  | refl (plan : Plan Raw Ty HasType Key Obligation) : MoreDynamic plan plan
  | raw_typed (plan : TypedPlan Raw Ty HasType) :
      MoreDynamic (.raw ⟨plan.term⟩) (.typed plan)
  | raw_checked (plan : CheckedPlan Raw Key Obligation) :
      MoreDynamic (.raw ⟨plan.term⟩) (.checked plan)

/-- Precision never changes the underlying raw term. -/
theorem MoreDynamic.erase_eq
    {p q : Plan Raw Ty HasType Key Obligation} (h : MoreDynamic p q) :
    p.erase = q.erase := by
  cases h <;> rfl

/-- **Dynamic gradual guarantee (model level).**  Two plans related by
precision execute identically: decorations may add evidence or blame, never
behaviour. -/
theorem run_eq_of_moreDynamic {Output : Type uOutput}
    (runRaw : Raw → Output)
    {p q : Plan Raw Ty HasType Key Obligation} (h : MoreDynamic p q) :
    p.run runRaw = q.run runRaw := by
  unfold Plan.run
  rw [h.erase_eq]

/-- Cost observations are likewise invariant along precision. -/
theorem executionCost_eq_of_moreDynamic (rawCost : Raw → Nat)
    {p q : Plan Raw Ty HasType Key Obligation} (h : MoreDynamic p q) :
    p.executionCost rawCost = q.executionCost rawCost := by
  unfold Plan.executionCost
  rw [h.erase_eq]

/-- Every plan is at least as precise as its own raw erasure. -/
theorem raw_erase_moreDynamic (plan : Plan Raw Ty HasType Key Obligation) :
    MoreDynamic (.raw ⟨plan.erase⟩) plan := by
  cases plan with
  | raw p => exact .refl _
  | typed p => exact .raw_typed p
  | checked p => exact .raw_checked p

/-- **Static half, in this model.**  A typed plan's erasure is a plan; the
typing derivation is data carried alongside, so removing it cannot fail.
Stated as the existence of the less precise plan with identical execution. -/
theorem erase_typed_runs_the_same {Output : Type uOutput}
    (runRaw : Raw → Output) (plan : TypedPlan Raw Ty HasType) :
    ∃ q : Plan Raw Ty HasType Key Obligation,
      MoreDynamic q (Plan.typed (Key := Key) (Obligation := Obligation) plan) ∧
        q.run runRaw =
          (Plan.typed (Key := Key) (Obligation := Obligation) plan).run runRaw :=
  ⟨.raw ⟨plan.term⟩, .raw_typed plan, run_eq_of_moreDynamic runRaw (.raw_typed plan)⟩

#print axioms run_eq_of_moreDynamic
#print axioms raw_erase_moreDynamic
#print axioms erase_typed_runs_the_same

end Mettapedia.Languages.MeTTa.Prime.GradualGuarantee
