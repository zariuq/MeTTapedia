import Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-!
# Disjoint concurrency: two threads over separate resources

Two programs run in parallel by interleaving their primitive calls on one
shared state (`ParStep`).  An interleaving faults when it reaches a primitive
that is undefined where it runs (`ParFaults`); it completes when both programs
have returned (`ParRuns`).  The interleaving semantics is sequentially
consistent by construction: every execution is one total order of the two
threads' primitives.

**The disjoint concurrency rule** (O'Hearn, "Resources, concurrency, and local
reasoning", TCS 375, 2007): if each program meets its own specification, they
run in parallel from separate parts of the state without fault, and every
complete interleaving ends in the separate postconditions:

  `{P₁} c₁ {Q₁}` and `{P₂} c₂ {Q₂}`  imply  `{P₁ ∗ P₂} c₁ ∥ c₂ {Q₁ ∗ Q₂}`.

It holds for every signature of local primitives (`triple_par`), proved once.
The invariant behind it (`Good`) splits every reachable state into the parts
of the two threads (`good_of_reaches`): each primitive a thread runs is defined
on its own part, so it touches nothing the other thread holds.  That is the
abstract form of data-race freedom; `CMemory.Concurrency` reads it off for C
memory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.AbstractSeparationLogic

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v s

variable {S : Type s} {Op : Type u} {Ret : Op → Type v} {α β : Type v}
variable (act : (o : Op) → Action S (Ret o))

/-- **One interleaved step**: either thread performs its next primitive. -/
inductive ParStep : Prog Op Ret α → Prog Op Ret β → S → Prog Op Ret α → Prog Op Ret β → S →
    Prop
  | left {o : Op} {k : Ret o → Prog Op Ret α} {c₂ : Prog Op Ret β} {σ σ' : S} {r : Ret o} :
      (act o).Step σ r σ' → ParStep (.call o k) c₂ σ (k r) c₂ σ'
  | right {c₁ : Prog Op Ret α} {o : Op} {k : Ret o → Prog Op Ret β} {σ σ' : S} {r : Ret o} :
      (act o).Step σ r σ' → ParStep c₁ (.call o k) σ c₁ (k r) σ'

/-- Some interleaving reaches a primitive that is undefined where it runs. -/
inductive ParFaults : Prog Op Ret α → Prog Op Ret β → S → Prop
  | left {o : Op} {k : Ret o → Prog Op Ret α} {c₂ : Prog Op Ret β} {σ : S} :
      ¬ (act o).Safe σ → ParFaults (.call o k) c₂ σ
  | right {c₁ : Prog Op Ret α} {o : Op} {k : Ret o → Prog Op Ret β} {σ : S} :
      ¬ (act o).Safe σ → ParFaults c₁ (.call o k) σ
  | step {c₁ c₁' : Prog Op Ret α} {c₂ c₂' : Prog Op Ret β} {σ σ' : S} :
      ParStep act c₁ c₂ σ c₁' c₂' σ' → ParFaults c₁' c₂' σ' → ParFaults c₁ c₂ σ

/-- A complete interleaving: both threads return. -/
inductive ParRuns : Prog Op Ret α → Prog Op Ret β → S → α → β → S → Prop
  | done {a : α} {b : β} {σ : S} : ParRuns (.ret a) (.ret b) σ a b σ
  | step {c₁ c₁' : Prog Op Ret α} {c₂ c₂' : Prog Op Ret β} {σ σ' σ'' : S} {a : α} {b : β} :
      ParStep act c₁ c₂ σ c₁' c₂' σ' → ParRuns c₁' c₂' σ' a b σ'' → ParRuns c₁ c₂ σ a b σ''

/-- The configurations some interleaving reaches. -/
inductive ParReaches : Prog Op Ret α → Prog Op Ret β → S → Prog Op Ret α → Prog Op Ret β → S →
    Prop
  | refl {c₁ : Prog Op Ret α} {c₂ : Prog Op Ret β} {σ : S} : ParReaches c₁ c₂ σ c₁ c₂ σ
  | step {c₁ c₁' c₁'' : Prog Op Ret α} {c₂ c₂' c₂'' : Prog Op Ret β} {σ σ' σ'' : S} :
      ParStep act c₁ c₂ σ c₁' c₂' σ' → ParReaches c₁' c₂' σ' c₁'' c₂'' σ'' →
        ParReaches c₁ c₂ σ c₁'' c₂'' σ''

/-- **Parallel Hoare triple**: no interleaving faults, and every complete
interleaving ends in the postcondition. -/
def ParTriple (P : S → Prop) (c₁ : Prog Op Ret α) (c₂ : Prog Op Ret β)
    (Q : α → β → S → Prop) : Prop :=
  ∀ σ, P σ → ¬ ParFaults act c₁ c₂ σ ∧ ∀ a b σ', ParRuns act c₁ c₂ σ a b σ' → Q a b σ'

variable [Zero S] [Add S] [SepAlgebra S]

/-- A program meets a postcondition from one state. -/
def Meets (c : Prog Op Ret α) (σ : S) (Q : α → S → Prop) : Prop :=
  c.Safe act σ ∧ ∀ a τ, c.Runs act σ a τ → Q a τ

/-- **The invariant of disjoint concurrency**: the state splits into two
separate parts from which the two threads meet their postconditions. -/
def Good (Q₁ : α → S → Prop) (Q₂ : β → S → Prop) (c₁ : Prog Op Ret α) (c₂ : Prog Op Ret β)
    (σ : S) : Prop :=
  ∃ σ₁ σ₂, σ₁ ## σ₂ ∧ σ = σ₁ + σ₂ ∧ Meets act c₁ σ₁ Q₁ ∧ Meets act c₂ σ₂ Q₂

section

variable {act}
variable (isLocal : ∀ o, (act o).Local)
include isLocal

theorem meets_step {o : Op} {k : Ret o → Prog Op Ret α} {σ₁ τ σ' : S} {r : Ret o}
    {Q : α → S → Prop} (meets : Meets act (.call o k) σ₁ Q) (separate : σ₁ ## τ)
    (step : (act o).Step (σ₁ + τ) r σ') :
    ∃ σ₁', σ₁' ## τ ∧ σ' = σ₁' + τ ∧ Meets act (k r) σ₁' Q := by
  obtain ⟨⟨safe, next⟩, post⟩ := meets
  obtain ⟨σ₁', separate', rfl, step'⟩ := (isLocal o).step_frame safe separate step
  exact ⟨σ₁', separate', rfl, next r σ₁' step', fun a τ' runs => post a τ' ⟨r, σ₁', step', runs⟩⟩

/-- Every interleaved step keeps the invariant. -/
theorem good_step {Q₁ : α → S → Prop} {Q₂ : β → S → Prop} {c₁ c₁' : Prog Op Ret α}
    {c₂ c₂' : Prog Op Ret β} {σ σ' : S} (good : Good act Q₁ Q₂ c₁ c₂ σ)
    (step : ParStep act c₁ c₂ σ c₁' c₂' σ') : Good act Q₁ Q₂ c₁' c₂' σ' := by
  obtain ⟨σ₁, σ₂, separate, rfl, meets₁, meets₂⟩ := good
  cases step with
  | left step =>
    obtain ⟨σ₁', separate', rfl, meets₁'⟩ := meets_step isLocal meets₁ separate step
    exact ⟨σ₁', σ₂, separate', rfl, meets₁', meets₂⟩
  | right step =>
    rw [SepAlgebra.add_comm separate] at step
    obtain ⟨σ₂', separate', rfl, meets₂'⟩ :=
      meets_step isLocal meets₂ (SepAlgebra.separate_symm separate) step
    exact ⟨σ₁, σ₂', SepAlgebra.separate_symm separate', SepAlgebra.add_comm separate',
      meets₁, meets₂'⟩

/-- Every reachable configuration keeps the invariant. -/
theorem good_of_reaches {Q₁ : α → S → Prop} {Q₂ : β → S → Prop} {c₁ c₁' : Prog Op Ret α}
    {c₂ c₂' : Prog Op Ret β} {σ σ' : S} (good : Good act Q₁ Q₂ c₁ c₂ σ)
    (reaches : ParReaches act c₁ c₂ σ c₁' c₂' σ') : Good act Q₁ Q₂ c₁' c₂' σ' := by
  induction reaches with
  | refl => exact good
  | step step _ ih => exact ih (good_step isLocal good step)

/-- A configuration satisfying the invariant does not fault. -/
theorem good_not_faults {Q₁ : α → S → Prop} {Q₂ : β → S → Prop} {c₁ : Prog Op Ret α}
    {c₂ : Prog Op Ret β} {σ : S} (good : Good act Q₁ Q₂ c₁ c₂ σ) :
    ¬ ParFaults act c₁ c₂ σ := by
  intro faults
  induction faults with
  | left undefined =>
    obtain ⟨σ₁, σ₂, separate, rfl, ⟨⟨safe, -⟩, -⟩, -⟩ := good
    exact undefined ((isLocal _).safe_frame safe separate)
  | right undefined =>
    obtain ⟨σ₁, σ₂, separate, rfl, -, ⟨⟨safe, -⟩, -⟩⟩ := good
    rw [SepAlgebra.add_comm separate] at undefined
    exact undefined ((isLocal _).safe_frame safe (SepAlgebra.separate_symm separate))
  | step step _ ih => exact ih (good_step isLocal good step)

/-- A complete interleaving from the invariant ends in the two postconditions. -/
theorem good_runs {Q₁ : α → S → Prop} {Q₂ : β → S → Prop} {c₁ : Prog Op Ret α}
    {c₂ : Prog Op Ret β} {σ σ' : S} {a : α} {b : β} (good : Good act Q₁ Q₂ c₁ c₂ σ)
    (runs : ParRuns act c₁ c₂ σ a b σ') : (Q₁ a ∗ Q₂ b) σ' := by
  induction runs with
  | done =>
    obtain ⟨σ₁, σ₂, separate, rfl, ⟨-, post₁⟩, ⟨-, post₂⟩⟩ := good
    exact ⟨σ₁, σ₂, separate, rfl, post₁ _ σ₁ ⟨rfl, rfl⟩, post₂ _ σ₂ ⟨rfl, rfl⟩⟩
  | step step _ ih => exact ih (good_step isLocal good step)

/-- **The disjoint concurrency rule**, for every signature of local
primitives. -/
theorem triple_par {P₁ P₂ : S → Prop} {c₁ : Prog Op Ret α} {c₂ : Prog Op Ret β}
    {Q₁ : α → S → Prop} {Q₂ : β → S → Prop} (spec₁ : Triple act P₁ c₁ Q₁)
    (spec₂ : Triple act P₂ c₂ Q₂) :
    ParTriple act (P₁ ∗ P₂) c₁ c₂ (fun a b => Q₁ a ∗ Q₂ b) := by
  rintro _ ⟨σ₁, σ₂, separate, rfl, holds₁, holds₂⟩
  have good : Good act Q₁ Q₂ c₁ c₂ (σ₁ + σ₂) :=
    ⟨σ₁, σ₂, separate, rfl, spec₁ σ₁ holds₁, spec₂ σ₂ holds₂⟩
  exact ⟨good_not_faults isLocal good, fun a b σ' runs => good_runs isLocal good runs⟩

end

end Mettapedia.GSLT.Logic.AbstractSeparationLogic
