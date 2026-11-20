import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.Firings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.Readouts

/-!
# Persistent rule origins and set-supported world executions

Actual runs holding indexed persistent rules project through the existing
origin-fibre correspondence to base firing runs, then to actual singleton
world paths with shared rule support. The exact supplied run length and final
row state are preserved. Every supplied world path lifts back to a held-rule
run, with a choice of available origins.

The set support does not retain origin multiplicity. The original run and its
origin word remain available; the fibre over a fixed base run is the existing
`Origins.Decorations`. These laws concern fixed persistent rules, not changes
to a live rule table or arbitrary fork/publication/merge paths.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.OriginSupport

open RuleSyntax RuleSyntax.Worlds RuleSyntax.RuleOccurrences
open LiveRules.Origins
open Mettapedia.GSLT.IndexedOperational

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO,uH,uE} Hom) {P Q : Program Tm}
  {ids : Finset R} {code : R → Rule Tm} (zone : R → Z) (offers : Offers Q ids code)

include offers

noncomputable def worldPath {state : State Tm O} {count : Nat}
    (run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count) :
    ExecutionPath (firings X E) (singleton P Q state)
      (singleton P Q (projectRun X E zone offers state count run).val.last) :=
  singletonRunPath X E P Q (projectRun X E zone offers state count run).val

theorem worldPath_length {state : State Tm O} {count : Nat}
    (run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count) :
    (worldPath X E zone offers run).length = count :=
  (singletonRunPath_length X E P Q _).trans
    (projectRun X E zone offers state count run).property

theorem worldPath_rows {state : State Tm O} {count : Nat}
    (run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count) :
    run.val.last = holding (projectRun X E zone offers state count run).val.last ids code zone :=
  projectRun_last X E zone offers run

/-- Every supplied target path lifts with its actual endpoint and length.
The lift chooses origins; it does not prove that origin erasure is injective. -/
theorem worldPath_lifts {state : State Tm O} {last : RuleSyntax.Worlds.Bag Tm O}
    (path : ExecutionPath (firings X E) (singleton P Q state) last) :
    ∃ after : State Tm O, singleton P Q after = last ∧
      ∃ run : (rstep X O R E (ofRules Z) P).toStep.Run (holding state ids code zone),
        run.last = holding after ids code zone ∧ run.word.length = path.length := by
  obtain ⟨base, endpoint, length⟩ := singletonPathRun X E P Q path state rfl
  obtain ⟨run, rows, count⟩ := LiveRules.persistentRun_lifts X E offers zone base
  exact ⟨base.last, endpoint, run, rows, count.trans length⟩

/-- Arbitrary row-state readouts compose through the actual represented
states. The observation may inspect the retained frame and knowledge. -/
theorem world_readout_iff (state : State Tm O) (observe : State Tm O → Prop) :
    (∃ last, (firings X E).MultiStep (singleton P Q state) last ∧ Shows observe last) ↔
      ∃ run : (rstep X O R E (ofRules Z) P).toStep.Run (holding state ids code zone),
        observe run.last.toState :=
  (singleton_reachable_iff_run X E P Q state observe).trans
    (LiveRules.persistent_readout_iff X E offers zone state observe)

/-- Normalization is transported separately from finite reachability. This
uses the existing strong comparisons in both links of the chain. -/
theorem world_normalization_iff (state : State Tm O) :
    Acc (fun after before =>
      LogicOverTheStep.StepSpan.Succ (rstep X O R E (ofRules Z) P).toStep before after)
      (holding state ids code zone) ↔
    Acc (fun after before => Fires (events X O E) before after) (singleton P Q state) :=
  (LiveRules.persistent_normalization_iff X E offers zone state).symm.trans
    (singleton_normalization_iff X E P Q state)

/-- The target path is constructed from the fixed base run. Its origin
decoration remains a separate, recoverable part of the held execution. -/
theorem lifted_world_rows {state : State Tm O} {count : Nat}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state)
    (origins : Decorations X E (ids := ids) (code := code) zone base) :
    (liftOrigins X E zone offers base origins).val.last =
      holding ((baseEvents X E).last base) ids code zone ∧
    (liftOrigins X E zone offers base origins).val.word.map (fun entry => entry.2.use) =
      originWord X E zone base origins :=
  ⟨liftOrigins_last X E zone offers base origins, liftOrigins_word X E zone offers base origins⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.OriginSupport
