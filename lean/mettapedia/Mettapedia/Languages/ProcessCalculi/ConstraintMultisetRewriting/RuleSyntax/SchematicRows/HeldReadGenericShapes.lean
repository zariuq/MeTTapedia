import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericSpan

/-!
# Shapes, resources and actual guards of the generic read protocol

Freshness is supplied by the separately proved joint/staged equivalence. The
remaining shapes, access modes and empty guards are computed from the actual
rules; physical enabling keeps source presence and fresh output allocation
explicit. No admission or solver conclusion is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}
  (X : Frames Tm Hom) (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))
  (temporary output : O)

theorem direct_shapes
    (fresh : (direct ordinary rows closures selected extension ruleOpening datumOpening output).Fresh X)
    (wellFormed : (closures selected).WellFormed) :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).Shapes X := by
  refine ⟨fresh, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro packed member
    change packed ∈ [⟨Row.schematic (closures selected), RowUse.schematic (closures selected) datumOpening⟩] at member
    obtain rfl := List.mem_singleton.mp member
    exact wellFormed
  · intro row member
    cases member

theorem datum_shapes (ambient : Set (HeldReadEncoding.Code Tm)) (present : selected ∈ rows)
    (fresh : (datum ordinary rows closures selected extension datumOpening temporary).Fresh X)
    (wellFormed : (closures selected).WellFormed) :
    (datum ordinary rows closures selected extension datumOpening temporary).Shapes X ambient := by
  refine ⟨fresh, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_⟩
  exact {
    available := present
    arguments := wellFormed
    installed := rfl
    madeNodup := List.nodup_nil
    madeLength := rfl
    madeNew := by intro r member; cases member
    removed := rfl
    removedNodup := List.nodup_nil
    removedHeld := by intro pair member; cases member
    published := rfl }

theorem direct_holds {b : Obj} (point : Hom (E.target extension) b) :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).Holds X point := by
  constructor
  · intro check member
    cases member
  · intro query member
    cases member

theorem datum_holds {b : Obj} (point : Hom (E.target extension) b) :
    (datum ordinary rows closures selected extension datumOpening temporary).Holds X point :=
  holds_of_none X (datum ordinary rows closures selected extension datumOpening temporary)
    rfl rfl rfl rfl rfl rfl point

variable [DecidableEq O] [DecidableEq R]

theorem direct_enabled (present : selected ∈ rows) (fresh : output ∉ ordinary.present) :
    Enabled (fun _ : O ⊕ R => ()) (mixed ordinary rows closures).present
      ((direct ordinary rows closures selected extension ruleOpening datumOpening output).selection.commit (T := Unit)) := by
  apply enabled_of
  · intro occurrence member
    cases member
  · intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    exact (schematic_present ordinary rows closures selected).mpr present
  · intro occurrence member
    cases member
  · intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    exact fun old => fresh ((ordinary_present ordinary rows closures output).mp old)

omit [DecidableEq R] in
theorem datum_enabled (fresh : temporary ∉ ordinary.present) :
    Enabled (fun _ : O => ()) ordinary.present
      ((datum ordinary rows closures selected extension datumOpening temporary).selection.commit (T := Unit)) := by
  apply enabled_of
  · intro occurrence member
    cases member
  · intro occurrence member
    cases member
  · intro occurrence member
    cases member
  · intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    exact fresh

theorem consumer_shapes (ambient : Set (HeldReadEncoding.Code Tm))
    (available : Sum.inr (consumeRule (closures selected).schema) ∈ ambient)
    (fresh : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Fresh X) :
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Shapes X ambient := by
  refine ⟨fresh, ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_⟩
  exact {
    available := available
    arguments := rfl
    installed := rfl
    madeNodup := List.nodup_nil
    madeLength := rfl
    madeNew := by intro r member; cases member
    removed := rfl
    removedNodup := List.nodup_nil
    removedHeld := by intro pair member; cases member
    published := rfl }

theorem consumer_enabled (fresh : output ∉ ordinary.present) (different : temporary ≠ output) :
    Enabled (fun _ : O => ())
      ((datum ordinary rows closures selected extension datumOpening temporary).result X).present
      ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).selection.commit (T := Unit)) := by
  apply enabled_of
  · intro occurrence member
    have same := List.mem_singleton.mp member
    subst occurrence
    exact (datum_present X ordinary rows closures selected extension datumOpening temporary).symm ▸
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · intro occurrence member
    cases member
  · intro occurrence _ member
    cases member
  · intro occurrence member
    have same := List.mem_singleton.mp member
    subst occurrence
    intro old
    rw [datum_present] at old
    rcases Finset.mem_union.mp old with original | made
    · exact fresh original
    · exact different (Finset.mem_singleton.mp made).symm

theorem consumer_holds {b : Obj} (point : Hom (E.target extension) b) :
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Holds X point :=
  holds_of_none X (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output)
    rfl rfl rfl rfl rfl rfl point

#print axioms direct_shapes
#print axioms datum_shapes
#print axioms consumer_shapes
#print axioms direct_enabled
#print axioms consumer_enabled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
