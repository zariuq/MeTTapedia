import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Enumeration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ReadModels

/-!
# Candidate exclusion is relative to every future frame

A certificate may exclude a row only when no independently interpreted caller
and datum can meet. This interface has no required term representation. The
actual selected-information theorem supplies the reading used below; guard,
freshness and resource admission are not replaced by the index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.FrameFilter

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom)

def Excludes {caller source : Obj} (pattern : Tm caller) (row : Row Tm source) : Prop :=
  ∀ (future : Obj) (query : Hom caller future) (ambient : Hom source future),
    ¬ Row.ReadsAt X ambient (X.act query pattern) row

def Complete {caller source : Obj} (pattern : Tm caller) (keep : Row Tm source → Bool) : Prop :=
  ∀ row, keep row = false → Excludes X pattern row

theorem reading_survives {caller source future : Obj} (pattern : Tm caller)
    (keep : Row Tm source → Bool) (complete : Complete X pattern keep)
    (row : Row Tm source) (query : Hom caller future) (ambient : Hom source future)
    (reading : Row.ReadsAt X ambient (X.act query pattern) row) : keep row = true := by
  cases accepted : keep row with
  | true => rfl
  | false => exact False.elim (complete row accepted future query ambient reading)

theorem reading_output_congr {source future : Obj} (row : Row Tm source)
    (ambient : Hom source future) (first second : Tm future)
    (reading : Row.ReadsAt X ambient first row) (same : X.E first second) :
    Row.ReadsAt X ambient second row := by
  cases row with
  | shared value => exact (X.equivalence future).trans reading same
  | schematic closure =>
      obtain ⟨locals, known, captures, output⟩ := reading
      exact ⟨locals, known, captures, (X.equivalence future).trans output same⟩

theorem resolver_word {caller source : Obj} {Occurrence Answer : Type}
    (pattern : Tm caller) (keep : Row Tm source → Bool) (complete : Complete X pattern keep)
    (label : Occurrence → Row Tm source) (rows : List Occurrence) (resolve : Occurrence → List Answer)
    (sound : ∀ occurrence answer, answer ∈ resolve occurrence →
      ∃ (future : Obj) (query : Hom caller future) (ambient : Hom source future),
        Row.ReadsAt X ambient (X.act query pattern) (label occurrence)) :
    (enumerate (fun occurrence => keep (label occurrence)) rows).flatMap resolve = rows.flatMap resolve := by
  apply enumerate_resolver_word
  intro occurrence _ nonempty
  obtain ⟨answer, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨future, query, ambient, reading⟩ := sound occurrence answer member
  exact reading_survives X pattern keep complete (label occurrence) query ambient reading

theorem actual_selected_read_survives
    {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
    {P : Set (Rule Tm)} {source : State Tm O} (firing : Firing O E P source)
    (admitted : firing.Admits X)
    (pattern : Tm firing.rule.basic.locals) (keep : Row Tm source.frame → Bool)
    (complete : Complete X pattern keep)
    (selected : PackedUse Tm Hom source.frame (E.target firing.ext)) (member : selected ∈ firing.uses)
    (paired : (X.act firing.opening pattern, selected.2.value X (E.weaken firing.ext)) ∈
      (firing.rule.basic.body.read.map (X.act firing.opening)).zip (firing.readValues X)) :
    keep selected.1 = true := by
  obtain ⟨future, point, solved⟩ := admitted.2.2.1
  have reading := firing.selected_reading X point solved admitted.1 selected member
  have equation := solved _ (List.mem_append_left _ (List.mem_append_right _ paired))
  have same : X.E (X.act point (selected.2.value X (E.weaken firing.ext)))
      (X.act (X.comp point firing.opening) pattern) := by
    rw [X.act_comp]
    exact (X.equivalence future).symm equation
  exact reading_survives X pattern keep complete selected.1
    (X.comp point firing.opening) (X.comp point (E.weaken firing.ext))
    (reading_output_congr X selected.1 _ _ _ reading same)

#print axioms reading_survives
#print axioms resolver_word
#print axioms actual_selected_read_survives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.FrameFilter
