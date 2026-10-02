import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction

/-!
# Pi processes with one hole

A context is a process with one hole.  Plugging fills the hole; a hole
beneath an input, a restriction or a replication is in the scope of the name
bound there, so plugging captures.  Contexts compose, and plugging a composite
is plugging twice.

A context whose hole sits beneath parallel compositions and restrictions
only is one in which reductions take place: the reduction rules of the
calculus close under exactly those two constructions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

/-- A pi process with one hole. -/
inductive ProcessContext : Type where
  | hole : ProcessContext
  | parLeft (inner : ProcessContext) (right : Process) : ProcessContext
  | parRight (left : Process) (inner : ProcessContext) : ProcessContext
  | input (channel bound : Name) (inner : ProcessContext) : ProcessContext
  | nu (bound : Name) (inner : ProcessContext) : ProcessContext
  | replicate (channel bound : Name) (inner : ProcessContext) : ProcessContext

namespace ProcessContext

/-- Plug a process into the hole. -/
def fill : ProcessContext → Process → Process
  | .hole, process => process
  | .parLeft inner right, process => .par (inner.fill process) right
  | .parRight left inner, process => .par left (inner.fill process)
  | .input channel bound inner, process => .input channel bound (inner.fill process)
  | .nu bound inner, process => .nu bound (inner.fill process)
  | .replicate channel bound inner, process => .replicate channel bound (inner.fill process)

/-- Plug a context into the hole of a context. -/
def comp : ProcessContext → ProcessContext → ProcessContext
  | .hole, second => second
  | .parLeft inner right, second => .parLeft (inner.comp second) right
  | .parRight left inner, second => .parRight left (inner.comp second)
  | .input channel bound inner, second => .input channel bound (inner.comp second)
  | .nu bound inner, second => .nu bound (inner.comp second)
  | .replicate channel bound inner, second => .replicate channel bound (inner.comp second)

/-- The names bound above the hole, outermost first. -/
def captured : ProcessContext → List Name
  | .hole => []
  | .parLeft inner _ => inner.captured
  | .parRight _ inner => inner.captured
  | .input _ bound inner => bound :: inner.captured
  | .nu bound inner => bound :: inner.captured
  | .replicate _ bound inner => bound :: inner.captured

@[simp] theorem fill_hole (process : Process) : hole.fill process = process := rfl

/-- Plugging a composite is plugging twice. -/
@[simp] theorem fill_comp :
    ∀ (first second : ProcessContext) (process : Process),
      (first.comp second).fill process = first.fill (second.fill process)
  | .hole, _, _ => rfl
  | .parLeft inner _, second, process => by simp only [comp, fill, fill_comp inner second]
  | .parRight _ inner, second, process => by simp only [comp, fill, fill_comp inner second]
  | .input _ _ inner, second, process => by simp only [comp, fill, fill_comp inner second]
  | .nu _ inner, second, process => by simp only [comp, fill, fill_comp inner second]
  | .replicate _ _ inner, second, process => by
      simp only [comp, fill, fill_comp inner second]

@[simp] theorem hole_comp (context : ProcessContext) : hole.comp context = context := rfl

@[simp] theorem comp_hole : ∀ context : ProcessContext, context.comp hole = context
  | .hole => rfl
  | .parLeft inner _ => by simp only [comp, comp_hole inner]
  | .parRight _ inner => by simp only [comp, comp_hole inner]
  | .input _ _ inner => by simp only [comp, comp_hole inner]
  | .nu _ inner => by simp only [comp, comp_hole inner]
  | .replicate _ _ inner => by simp only [comp, comp_hole inner]

theorem comp_assoc :
    ∀ first second third : ProcessContext,
      (first.comp second).comp third = first.comp (second.comp third)
  | .hole, _, _ => rfl
  | .parLeft inner _, second, third => by simp only [comp, comp_assoc inner second third]
  | .parRight _ inner, second, third => by simp only [comp, comp_assoc inner second third]
  | .input _ _ inner, second, third => by simp only [comp, comp_assoc inner second third]
  | .nu _ inner, second, third => by simp only [comp, comp_assoc inner second third]
  | .replicate _ _ inner, second, third => by simp only [comp, comp_assoc inner second third]

/-- The names captured by a composite are those of the outer context followed
by those of the inner one. -/
theorem captured_comp :
    ∀ first second : ProcessContext,
      (first.comp second).captured = first.captured ++ second.captured
  | .hole, _ => rfl
  | .parLeft inner _, second => by simp only [comp, captured, captured_comp inner second]
  | .parRight _ inner, second => by simp only [comp, captured, captured_comp inner second]
  | .input _ _ inner, second => by
      simp only [comp, captured, captured_comp inner second, List.cons_append]
  | .nu _ inner, second => by
      simp only [comp, captured, captured_comp inner second, List.cons_append]
  | .replicate _ _ inner, second => by
      simp only [comp, captured, captured_comp inner second, List.cons_append]

/-- **Structural congruence is preserved by every context.** -/
def congruent : ∀ (context : ProcessContext) {left right : Process},
    StructuralCongruence left right →
      StructuralCongruence (context.fill left) (context.fill right)
  | .hole, _, _, related => related
  | .parLeft inner right, _, _, related =>
      .par_cong _ _ _ _ (congruent inner related) (.refl right)
  | .parRight left inner, _, _, related =>
      .par_cong _ _ _ _ (.refl left) (congruent inner related)
  | .input channel bound inner, _, _, related =>
      .input_cong channel bound _ _ (congruent inner related)
  | .nu bound inner, _, _, related => .nu_cong bound _ _ (congruent inner related)
  | .replicate channel bound inner, _, _, related =>
      .replicate_cong channel bound _ _ (congruent inner related)

/-- **No context separates structurally congruent processes**: plugged into
any context they have the same reducts. -/
theorem reduces_iff_of_congruent (context : ProcessContext) {left right : Process}
    (related : StructuralCongruence left right) (target : Process) :
    Nonempty (Reduces (context.fill left) target) ↔
      Nonempty (Reduces (context.fill right) target) :=
  ⟨fun ⟨step⟩ => ⟨.struct _ _ _ _ (.symm _ _ (context.congruent related)) step (.refl _)⟩,
    fun ⟨step⟩ => ⟨.struct _ _ _ _ (context.congruent related) step (.refl _)⟩⟩

/-- A context in which reductions take place: the hole sits beneath parallel
compositions and restrictions only. -/
inductive Reactive : ProcessContext → Prop where
  | hole : Reactive .hole
  | parLeft {inner : ProcessContext} (right : Process) :
      Reactive inner → Reactive (.parLeft inner right)
  | parRight (left : Process) {inner : ProcessContext} :
      Reactive inner → Reactive (.parRight left inner)
  | nu (bound : Name) {inner : ProcessContext} : Reactive inner → Reactive (.nu bound inner)

/-- **A reduction of the plugged process is a reduction of the whole**, in a
context in which reductions take place. -/
theorem Reactive.reduces {context : ProcessContext} (reactive : Reactive context)
    {source target : Process} (step : Nonempty (Reduces source target)) :
    Nonempty (Reduces (context.fill source) (context.fill target)) := by
  induction reactive with
  | hole => exact step
  | parLeft right _ recurse =>
      obtain ⟨inner⟩ := recurse
      exact ⟨.par_left _ _ right inner⟩
  | parRight left _ recurse =>
      obtain ⟨inner⟩ := recurse
      exact ⟨.par_right left _ _ inner⟩
  | nu bound _ recurse =>
      obtain ⟨inner⟩ := recurse
      exact ⟨.res bound _ _ inner⟩

end ProcessContext

end Mettapedia.Languages.ProcessCalculi.PiCalculus
