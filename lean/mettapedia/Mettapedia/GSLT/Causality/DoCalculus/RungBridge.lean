import Mettapedia.GSLT.Causality.Hierarchy
import Mettapedia.GSLT.Causality.StructuralModels

/-!
# Surgery is a rung-2 intervention

On one acyclic chain, `x` is the constant `false` and `y` copies `x`. The
unique solution is `(false, false)`. The binding `do(x := true)` is an
admissible context of `surgeryAction` on the whole key set. Plugging that
context is surgery at `x`, whose unique solution is `(true, true)`. Reading a
passive formula after the intervention is the rung-2 clause of the ladder: the
formula holds at the original model exactly when it holds at the surgical model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.StructuralModels
open Mettapedia.GSLT.Causality.ContextBindings
open OverrideAction

/-- Two keys of a chain. -/
inductive Gate where
  | x
  | y
  deriving DecidableEq

/-- `x` is constantly `false`; `y` copies `x`. -/
def chain : Mechanisms Gate Bool
  | .x, _ => false
  | .y, store => store .x

/-- The chain is recursive: `x` has rank `0` and reads nothing, `y` has rank `1`
and reads only `x`. -/
def chainRecursive : Recursive chain where
  rank
    | .x => 0
    | .y => 1
  bound := 2
  rank_lt key := by cases key <;> decide
  depends
    | .x, _, _, _ => rfl
    | .y, _, _, agree => agree .x (by decide)

/-- The observational solution: both keys are `false`. -/
def chainFalse : Gate → Bool
  | .x => false
  | .y => false

/-- The solution after `do(x := true)`: both keys are `true`. -/
def chainTrue : Gate → Bool
  | .x => true
  | .y => true

theorem chainFalse_isSolution : IsSolution chain chainFalse := by
  intro key
  cases key <;> rfl

theorem chain_solution_eq {store : Gate → Bool} (solution : IsSolution chain store) :
    store = chainFalse :=
  solution_unique chainRecursive solution chainFalse_isSolution

theorem chainTrue_isSolution :
    IsSolution (surgery (single .x true) chain) chainTrue := by
  intro key
  cases key <;> simp [surgery, single, chain, chainTrue]

theorem chain_do_solution_eq {store : Gate → Bool}
    (solution : IsSolution (surgery (single .x true) chain) store) :
    store = chainTrue :=
  solution_unique (recursive_surgery chainRecursive (single .x true)) solution
    chainTrue_isSolution

/-- `do(x := true)` names a key, so it is admissible on the full key set. -/
theorem chain_do_admissible :
    ((surgeryAction (Key := Gate) (Value := Bool)).regionDerived Set.univ).Admissible
      (doBinding .x true) := by
  intro key _
  exact Set.mem_univ key

/-- Plugging the one-key binding is surgery at that key. -/
theorem chain_plug_eq_surgery (store : Gate → Bool) :
    (surgeryAction (Key := Gate) (Value := Bool)).bindingPlug (doBinding .x true)
        ⟨chain, store⟩ =
      surgeryAction.assign (single .x true) ⟨chain, store⟩ := by
  simp [doBinding, bindingPlug]

/-- **Rung 2 on the chain.** A passive formula read after `do(x := true)` holds
at the original model exactly when that formula holds at the model produced by
surgery. -/
theorem chain_do_is_rung2
    (obs : ContextualRules.Observations (modelGSLT Gate Bool))
    (formula : Formula (passive obs).Atom (passive obs).Label)
    (store : Gate → Bool) :
    let action := surgeryAction (Key := Gate) (Value := Bool)
    let admissible := action.regionDerived Set.univ
    let context : {bindings : Bindings Gate Bool // admissible.Admissible bindings} :=
      ⟨doBinding .x true, chain_do_admissible⟩
    (admissible.saturated obs).sat
        (underIntervention admissible obs context formula) ⟨chain, store⟩ ↔
      (passive obs).sat formula (action.assign (single .x true) ⟨chain, store⟩) := by
  dsimp
  rw [← chain_plug_eq_surgery store]
  exact sat_underIntervention (surgeryAction.regionDerived (Set.univ : Set Gate)) obs formula
    ⟨doBinding .x true, chain_do_admissible⟩ ⟨chain, store⟩

end Mettapedia.GSLT.Causality.DoCalculus
