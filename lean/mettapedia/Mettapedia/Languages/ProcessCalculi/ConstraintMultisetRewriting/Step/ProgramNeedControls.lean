import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNeedValue
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNeedStepAdequacy

/-!
# Controls for call by need on the step

- `loop_on_step`: `bind 0 (call l) c` with `(= l (call l))` is answered `c` by a run of translated
  firings of the by-need schemas; by value it has no answer (`value_diverges_loop`).
- `shared_on_step`: `bind 0 (call (g c)) (pair 0 0)` with `(= (g $x) (pair x x))` reaches
  `((c c) (c c))` on the step: the first demand takes the thunk row, the second reads the value row.
- `shared_choice`, `choice_first`, `choice_second`, `choice_never_mixed`: with `(= c a)` and
  `(= c b)`, `bind 0 (call c) (pair 0 0)` answers `(a a)` and `(b b)` by need, and never the mixed
  `(a b)`: the thunk is evaluated once, and both demands read its one value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed

open ProgramRows ProgramTranslation

theorem loop_restricted : RangeRestricted loopProg := by
  intro j x hx
  rcases j with ⟨_ | k, hk⟩
  · simp [loopProg, ProgramNested.EPat.vars, Pat.vars] at hx
  · simp [loopProg] at hk

theorem loop_inside : Inside [0] (.ev loopBind, [], Heap.none) :=
  ⟨fun e same ℓ member => by
      cases same
      simp [loopBind, locsX] at member
      simp [member],
    fun f member => absurd member List.not_mem_nil,
    fun ℓ e stored => by cases stored⟩

/-- **By need, on the step, the program answers `c`.** -/
theorem loop_on_step : ∃ q : Config × ℕ,
    Relation.ReflTransGen (Translated (nschema loopProg)) (initial (rowsList [0] (.ev loopBind, [], Heap.none)), 1) q ∧
      Represents q.1 (rowsOf [0] (.ret (.sym 11), [], Heap.none.set 0 (.thunk (.call (.val (.sym 10)))))) q.2 :=
  (need_eval_on_step (List.nodup_singleton 0) loop_restricted loop_inside).1 need_answers_loop

theorem share_restricted : RangeRestricted shareProg := by
  intro j x hx
  rcases j with ⟨_ | k, hk⟩
  · simpa [shareProg, ProgramNested.EPat.vars, Pat.vars] using hx
  · simp [shareProg] at hk

theorem share_inside : Inside [0] (.ev shareBind, [], Heap.none) :=
  ⟨fun e same ℓ member => by
      cases same
      simp [shareBind, locsX] at member
      simp [member],
    fun f member => absurd member List.not_mem_nil,
    fun ℓ e stored => by cases stored⟩

/-- **The shared thunk on the step.** -/
theorem shared_on_step : ∃ q : Config × ℕ,
    Relation.ReflTransGen (Translated (nschema shareProg)) (initial (rowsList [0] (.ev shareBind, [], Heap.none)), 1) q ∧
      Represents q.1 (rowsOf [0] (.ret (.cell (.cell (.sym 21) (.sym 21)) (.cell (.sym 21) (.sym 21))), [],
        (((Heap.none.set 0 (.thunk (.call (.val (.cell (.sym 20) (.sym 21)))))).set 0 .busy).set 0
          (.value (.cell (.sym 21) (.sym 21)))))) q.2 :=
  (need_eval_on_step (List.nodup_singleton 0) share_restricted share_inside).1 shared_thunk_once

/-! ## Sharing a choice -/

/-- `(= c a)` and `(= c b)`: the call `c` has two answers. -/
def choiceProg : Program := [⟨.sym 30, .val (.sym 31)⟩, ⟨.sym 30, .val (.sym 32)⟩]

/-- `bind 0 (call c) (pair 0 0)`: two demands of one thunk with two answers. -/
def choiceBind : NEx := .bind 0 (.call (.val (.sym 30))) (.pair (.loc 0) (.loc 0))

/-- **Both demands read the same answer**: by need, the pair is never mixed. -/
theorem shared_choice {H' : Heap} {v : Sx} (eval : NEval choiceProg Heap.none choiceBind H' v) :
    ∃ w, v = .cell w w := by
  cases eval with
  | bind _ body =>
      cases body with
      | pair left right =>
          cases left with
          | read stored =>
              rw [Heap.set_same] at stored
              cases stored
          | force stored inner =>
              rw [Heap.set_same] at stored
              cases stored
              cases right with
              | read stored' =>
                  rw [Heap.set_same] at stored'
                  cases stored'
                  exact ⟨_, rfl⟩
              | force stored' _ =>
                  rw [Heap.set_same] at stored'
                  cases stored'

theorem choice_first : NEval choiceProg Heap.none choiceBind
    (((Heap.none.set 0 (.thunk (.call (.val (.sym 30))))).set 0 .busy).set 0 (.value (.sym 31)))
    (.cell (.sym 31) (.sym 31)) :=
  .bind rfl (.pair (.force (Heap.set_same _ _ _)
    (.call ⟨0, by decide⟩ (fun _ => .sym 0) (.val _ _) rfl (.val _ _))) (.read (Heap.set_same _ _ _)))

theorem choice_second : NEval choiceProg Heap.none choiceBind
    (((Heap.none.set 0 (.thunk (.call (.val (.sym 30))))).set 0 .busy).set 0 (.value (.sym 32)))
    (.cell (.sym 32) (.sym 32)) :=
  .bind rfl (.pair (.force (Heap.set_same _ _ _)
    (.call ⟨1, by decide⟩ (fun _ => .sym 0) (.val _ _) rfl (.val _ _))) (.read (Heap.set_same _ _ _)))

/-- The mixed pair is no answer. -/
theorem choice_never_mixed (H' : Heap) : ¬ NEval choiceProg Heap.none choiceBind H' (.cell (.sym 31) (.sym 32)) := by
  intro eval
  obtain ⟨w, same⟩ := shared_choice eval
  simp only [Sx.cell.injEq] at same
  obtain ⟨rfl, h⟩ := same
  cases h

#print axioms loop_on_step
#print axioms shared_on_step
#print axioms shared_choice
#print axioms choice_first
#print axioms choice_second
#print axioms choice_never_mixed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed
