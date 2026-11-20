import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.RunFibres

/-!
# Row states and origin words of the counted run correspondence

The fibre decomposition retains the actual final state and the sequence of
ambient or held origins. Its inverse constructs an admitted run, not only a
transition path with erased events.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins

open RuleSyntax RuleSyntax.RuleOccurrences EventMultiplicity

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) {P Q : Program Tm}
  {ids : Finset R} {code : R → Rule Tm} (zone : R → Z)

def originWord : {count : Nat} → {state : State Tm O} →
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state) →
      Decorations X E (ids := ids) (code := code) zone base → List (Use (Rule Tm) R)
  | 0, _, _, _ => []
  | _ + 1, _, ⟨_, rest⟩, ⟨use, origins⟩ => use.val :: originWord rest origins

theorem join_last : ∀ {count : Nat} {state : State Tm O}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state)
    (origins : Decorations X E (ids := ids) (code := code) zone base),
      (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).last
        (joinExecution X E zone ⟨base, origins⟩) = (baseEvents X E).last base
  | 0, _, _, _ => rfl
  | _ + 1, _, ⟨_, rest⟩, ⟨_, origins⟩ => join_last rest origins

theorem join_word : ∀ {count : Nat} {state : State Tm O}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state)
    (origins : Decorations X E (ids := ids) (code := code) zone base),
      (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).word
        (joinExecution X E zone ⟨base, origins⟩) = originWord X E zone base origins
  | 0, _, _, _ => rfl
  | _ + 1, _, ⟨_, rest⟩, ⟨use, origins⟩ =>
      congrArg (List.cons use.val) (join_word rest origins)

variable [DecidableEq R] (offers : Offers Q ids code)

noncomputable def liftOrigins {count : Nat} {state : State Tm O}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state)
    (origins : Decorations X E (ids := ids) (code := code) zone base) :
    HeldRuns X E (P := P) (ids := ids) (code := code) zone state count :=
  (runDecorations X E zone offers state count).symm ⟨base, origins⟩

theorem project_liftOrigins {count : Nat} {state : State Tm O}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state)
    (origins : Decorations X E (ids := ids) (code := code) zone base) :
    projectRun X E zone offers state count (liftOrigins X E zone offers base origins) =
      (step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
        (fun {_} firing => (firing.rule, firing.selection)) state count base := by
  unfold projectRun liftOrigins
  rw [Equiv.apply_symm_apply]

theorem liftOrigins_last {count : Nat} {state : State Tm O}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state)
    (origins : Decorations X E (ids := ids) (code := code) zone base) :
    (liftOrigins X E zone offers base origins).val.last =
      holding ((baseEvents X E).last base) ids code zone := by
  change ((rstep X O R E (ofRules Z) P).toStep.runOfExecution (fun {_} firing => firing.use)
    ((realization X E offers zone).bisimulation.executions count rfl
      (joinExecution X E zone ⟨base, origins⟩))).last = _
  rw [Step.runOfExecution_last]
  have endpoint := (realization X E offers zone).bisimulation.execution_last rfl
    (joinExecution X E zone ⟨base, origins⟩)
  exact endpoint.symm.trans (congrArg (fun final => holding final ids code zone)
    (join_last X E zone base origins))

theorem liftOrigins_word {count : Nat} {state : State Tm O}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state)
    (origins : Decorations X E (ids := ids) (code := code) zone base) :
    (liftOrigins X E zone offers base origins).val.word.map (fun entry => entry.2.use) =
      originWord X E zone base origins := by
  change ((rstep X O R E (ofRules Z) P).toStep.runOfExecution (fun {_} firing => firing.use)
    ((realization X E offers zone).bisimulation.executions count rfl
      (joinExecution X E zone ⟨base, origins⟩))).word.map _ = _
  exact ((rstep X O R E (ofRules Z) P).toStep.runOfExecution_word _ _).trans
    (((realization X E offers zone).bisimulation.execution_word rfl _).trans
      (join_word X E zone base origins))

theorem projectRun_last {state : State Tm O} {count : Nat}
    (run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count) :
    run.val.last = holding (projectRun X E zone offers state count run).val.last ids code zone := by
  let data := runDecorations X E zone offers state count run
  have restored : liftOrigins X E zone offers data.1 data.2 = run :=
    (runDecorations X E zone offers state count).symm_apply_apply run
  rw [← restored, liftOrigins_last, project_liftOrigins]
  change holding ((baseEvents X E).last data.1) ids code zone =
    holding ((step X O E (P ∪ Q)).toStep.runOfExecution _ data.1).last ids code zone
  rw [Step.runOfExecution_last]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins
