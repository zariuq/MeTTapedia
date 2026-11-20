import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.Origins
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Origin fibres over complete actual runs

A decorated execution splits into its complete base execution and one
available use at each event. The existing event realization and counted-run
equivalence transport this split to actual held-rule firing runs. The fibre
over one specified base run is therefore the product of its origin choices.
The base fixes all openings and occurrence identities, not only result bags.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins

open RuleSyntax RuleSyntax.RuleOccurrences
open EventMultiplicity

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) {P Q : Program Tm}
  {ids : Finset R} {code : R → Rule Tm} (zone : R → Z)

def Decorations : {count : Nat} → {state : State Tm O} →
    (baseEvents X E (P := P) (Q := Q)).Execution count state → Type (max uO uT uR)
  | 0, _, _ => PUnit
  | _ + 1, state, ⟨firing, rest⟩ =>
      Uses X E (ids := ids) (code := code) zone state firing × Decorations rest

def splitExecution : {count : Nat} → {state : State Tm O} →
    (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Execution count state →
      (base : (baseEvents X E (P := P) (Q := Q)).Execution count state) ×
        Decorations X E (ids := ids) (code := code) zone base
  | 0, _, _ => ⟨PUnit.unit, PUnit.unit⟩
  | _ + 1, _, ⟨⟨firing, use⟩, rest⟩ =>
      match splitExecution rest with
      | ⟨base, origins⟩ => ⟨⟨firing, base⟩, ⟨use, origins⟩⟩

def joinExecution : {count : Nat} → {state : State Tm O} →
    ((base : (baseEvents X E (P := P) (Q := Q)).Execution count state) ×
      Decorations X E (ids := ids) (code := code) zone base) →
    (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Execution count state
  | 0, _, _ => PUnit.unit
  | _ + 1, _, ⟨⟨firing, base⟩, ⟨use, origins⟩⟩ =>
      ⟨⟨firing, use⟩, joinExecution ⟨base, origins⟩⟩

theorem join_split : ∀ {count : Nat} {state : State Tm O}
    (run : (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Execution count state),
    joinExecution X E zone (splitExecution X E zone run) = run
  | 0, _, run => by cases run; rfl
  | count + 1, state, ⟨⟨firing, use⟩, rest⟩ => by
      have ih := join_split rest
      rw [splitExecution]
      generalize separated : splitExecution X E zone rest = data at *
      obtain ⟨base, origins⟩ := data
      exact congrArg (fun continuation =>
        (⟨⟨firing, use⟩, continuation⟩ :
          (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Execution
            (count + 1) state)) ih

theorem split_join : ∀ {count : Nat} {state : State Tm O}
    (data : (base : (baseEvents X E (P := P) (Q := Q)).Execution count state) ×
      Decorations X E (ids := ids) (code := code) zone base),
    splitExecution X E zone (joinExecution X E zone data) = data
  | 0, _, ⟨base, origins⟩ => by cases base; cases origins; rfl
  | _ + 1, _, ⟨⟨firing, base⟩, ⟨use, origins⟩⟩ => by
      rw [joinExecution, splitExecution, split_join ⟨base, origins⟩]

def splitEquiv (state : State Tm O) (count : Nat) :
    (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Execution count state ≃
      ((base : (baseEvents X E (P := P) (Q := Q)).Execution count state) ×
        Decorations X E (ids := ids) (code := code) zone base) where
  toFun := splitExecution X E zone
  invFun := joinExecution X E zone
  left_inv := join_split X E zone
  right_inv := split_join X E zone

noncomputable def ways : {count : Nat} → {state : State Tm O} →
    (baseEvents X E (P := P) (Q := Q)).Execution count state → Nat
  | 0, _, _ => 1
  | _ + 1, state, ⟨firing, rest⟩ =>
      Nat.card (Uses X E (ids := ids) (code := code) zone state firing) * ways rest

theorem decorations_card : ∀ {count : Nat} {state : State Tm O}
    (run : (baseEvents X E (P := P) (Q := Q)).Execution count state),
    Nat.card (Decorations X E (ids := ids) (code := code) zone run) = ways X E (ids := ids) (code := code) zone run
  | 0, _, _ => by simp [Decorations, ways]
  | _ + 1, _, ⟨firing, rest⟩ => by
      change Nat.card (Uses X E zone _ firing × Decorations X E zone rest) = _
      rw [Nat.card_prod, decorations_card rest]
      rfl

variable [DecidableEq R] (offers : Offers Q ids code)

abbrev HeldRuns (state : State Tm O) (count : Nat) :=
  {run : (rstep X O R E (ofRules Z) P).toStep.Run (holding state ids code zone) // run.word.length = count}

abbrev BaseRuns (state : State Tm O) (count : Nat) :=
  {run : (step X O E (P ∪ Q)).toStep.Run state // run.word.length = count}

noncomputable def runDecorations (state : State Tm O) (count : Nat) :
    HeldRuns X E (P := P) (ids := ids) (code := code) zone state count ≃
      ((base : (baseEvents X E (P := P) (Q := Q)).Execution count state) ×
        Decorations X E (ids := ids) (code := code) zone base) :=
  ((rstep X O R E (ofRules Z) P).toStep.countedExecutionRunEquiv
      (fun {_} firing => firing.use) (holding state ids code zone) count).symm.trans
    (((realization X E offers zone).bisimulation.executions count rfl).symm.trans
      (splitEquiv X E zone state count))

noncomputable def projectRun (state : State Tm O) (count : Nat)
    (run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count) :
    BaseRuns X E (P := P) (Q := Q) state count :=
  (step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
    (fun {_} firing => (firing.rule, firing.selection)) state count
    (runDecorations X E zone offers state count run).1

noncomputable def runFibreEquiv (state : State Tm O) (count : Nat)
    (base : BaseRuns X E (P := P) (Q := Q) state count) :
    {run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count //
      projectRun X E zone offers state count run = base} ≃
      Decorations X E (ids := ids) (code := code) zone
        (((step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
          (fun {_} firing => (firing.rule, firing.selection)) state count).symm base) := by
  let baseEquiv := (step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
    (fun {_} firing => (firing.rule, firing.selection)) state count
  let actual := runDecorations X E (P := P) zone offers state count
  refine (actual.subtypeEquiv
    (p := fun run => projectRun X E zone offers state count run = base)
    (q := fun pair => pair.1 = baseEquiv.symm base) ?_).trans
      (Equiv.sigmaSubtype (β := fun path => Decorations X E zone path) (baseEquiv.symm base))
  intro run
  change baseEquiv (actual run).1 = base ↔ (actual run).1 = baseEquiv.symm base
  exact baseEquiv.eq_symm_apply.symm

theorem run_fibre_card (state : State Tm O) (count : Nat)
    (base : BaseRuns X E (P := P) (Q := Q) state count) :
    Nat.card {run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count //
      projectRun X E zone offers state count run = base} =
      ways X E (ids := ids) (code := code) zone
        (((step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
          (fun {_} firing => (firing.rule, firing.selection)) state count).symm base) :=
  (Nat.card_congr (runFibreEquiv X E zone offers state count base)).trans (decorations_card X E zone _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins
