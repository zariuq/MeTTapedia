import Mettapedia.Machines.FunctionalCorrespondence

/-!
# Shared substrate, divergent control: the two machines separated by a term

The two machines of `FunctionalCorrespondence` interpret the *same* term
type. This file makes the substrate/control split formal:

* `MachineCore` packages a machine as (state, load, step) over a term type;
  `cekCore` and `krivineCore` are two inhabitants over the one `Tm` — the
  shared-substrate claim as a type-level fact.
* The **strategy separation witness**: for the term
  `tKO = (λx. λy. x) 7 Ω`, the call-by-value evaluator returns nothing at
  every fuel (`evalV_tKO_none` — the discarded argument `Ω` is still
  evaluated and diverges), while the call-by-name evaluator computes `7`
  outright (`evalN_tKO`, a kernel `rfl`). So eager and demand-driven
  control genuinely differ on the shared substrate; no fairness or fuel
  bound rescues the eager core on this term.

The divergence proofs are structural recursions over definitional two-step
unrollings of the evaluator. No project-specific axioms or proof placeholders
are introduced.

No common store or heap interface is asserted here.  The CEK environment and
the Krivine thunk environment are components of their derived controls, while
Prime's call-by-need heap additionally requires memoization, update, and cycle
laws absent from call-by-name.  A shared store interface belongs only after
those concrete machines supply refinement maps into it.
-/

namespace Mettapedia.Machines

/-! ## Machines as data over a shared term substrate -/

/-- A machine core: states, a loader, and a step function over a term
substrate. Different evaluation semantics inhabit this signature with
different control structures over the *same* terms. -/
structure MachineCore (Term : Type) where
  State : Type
  load : Term → State
  step : State → Option State

/-- The eager (call-by-value) control core over `Tm`. -/
def cekCore : MachineCore Tm where
  State := CEK.St
  load := fun t => ⟨.ev t [], []⟩
  step := CEK.step

/-- The demand-driven (call-by-name) control core over `Tm`. -/
def krivineCore : MachineCore Tm where
  State := Krivine.KSt
  load := fun t => ⟨t, [], []⟩
  step := Krivine.kstep

/-! ## The separation witness: `(λx. λy. x) 7 Ω` -/

/-- `x x` — the self-application body. -/
def selfApp : Tm := .app (.var 0) (.var 0)

/-- `δ = λx. x x`. -/
def delta : Tm := .lam selfApp

/-- `Ω = δ δ`, the canonical divergent term. -/
def bigOmega : Tm := .app delta delta

/-- The δ-closure value the CBV evaluator builds for `δ`. -/
def deltaV : CEK.Val := .clo selfApp []

/-- `K = λx. λy. x`: returns its first argument, discards its second. -/
def kComb : Tm := .lam (.lam (.var 1))

/-- `tKO = (K 7) Ω`: the answer needs only `7`; the discarded argument
diverges. -/
def tKO : Tm := .app (.app kComb (.lit 7)) bigOmega

/-- Under call-by-value, self-application of the δ-closure never returns,
at any fuel: two evaluator layers reproduce the same call. -/
theorem evalV_selfApp_none : ∀ n, CEK.evalV n [deltaV] selfApp = none
  | 0 => rfl
  | 1 => rfl
  | n + 2 => evalV_selfApp_none (n + 1)

/-- Under call-by-value, `Ω` never returns, at any fuel. -/
theorem evalV_bigOmega_none : ∀ n, CEK.evalV n [] bigOmega = none
  | 0 => rfl
  | 1 => rfl
  | n + 2 => evalV_selfApp_none (n + 1)

/-- **Eager control diverges on `tKO`** at every fuel: call-by-value must
evaluate the discarded argument, and the discarded argument is `Ω`. -/
theorem evalV_tKO_none : ∀ n, CEK.evalV n [] tKO = none := by
  intro n
  cases n with
  | zero => rfl
  | succ m =>
    have hunfold : CEK.evalV (m + 1) [] tKO =
        (match CEK.evalV m [] (.app kComb (.lit 7)) with
         | none => none
         | some fv =>
           match CEK.evalV m [] bigOmega with
           | none => none
           | some av =>
             match fv with
             | .lit _ => none
             | .clo b ρ' => CEK.evalV m (av :: ρ') b) := rfl
    rw [hunfold]
    cases hf : CEK.evalV m [] (.app kComb (.lit 7)) with
    | none => exact rfl
    | some fv =>
      rw [evalV_bigOmega_none m]

/-- **Demand-driven control computes `tKO`** — outright, by kernel
computation: the discarded argument is never demanded. -/
theorem evalN_tKO : Krivine.evalN 6 [] tKO = some (.lit 7) := rfl

/-- The strategy separation, packaged: one substrate term on which the two
control cores of the one machine family provably differ — the eager core
returns nothing at every fuel while the demand-driven core answers. -/
theorem strategy_separation :
    (∀ n, CEK.evalV n [] tKO = none) ∧ Krivine.evalN 6 [] tKO = some (.lit 7) :=
  ⟨evalV_tKO_none, rfl⟩

/-- Demand-driven success transports to the Krivine machine itself: the
machine walk for `tKO` ends presenting the literal `7`. -/
theorem krivine_machine_computes_tKO :
    ∃ st, Krivine.KSteps ⟨tKO, [], []⟩ st ∧ Krivine.Presents (.lit 7) [] st :=
  Krivine.eval_to_machine 6 [] tKO (.lit 7) rfl []

end Mettapedia.Machines
