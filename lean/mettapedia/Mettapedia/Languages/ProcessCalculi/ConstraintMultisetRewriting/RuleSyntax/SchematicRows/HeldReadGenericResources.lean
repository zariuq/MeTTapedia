import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericModels

/-!
# The held read protocol preserves the same public occurrences and labels

The intermediate ordinary occurrence is removed, persistent schema identities
remain, and every public live label agrees with the independent direct read.
Missing label slots are not identified with live resources. These laws do not
make fresh identities private to arbitrary contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources
open MeTTaCalculus.OccurrenceCommits (fire)

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}

theorem held_act_identity {C : Type*} {Z : Type*} (X : Frames Tm Hom) {a : Obj}
    (held : Held Tm C Z a) : held.act X (X.id a) = held := by
  cases held with
  | mk code args mode zone =>
    have action : X.act (X.id a) = id := funext (fun term => X.act_id term)
    change (⟨code, args.map (X.act (X.id a)), mode, zone⟩ : Held Tm C Z a) =
      ⟨code, args, mode, zone⟩
    rw [action, List.map_id]

variable (X : Frames Tm Hom) (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))
  [DecidableEq O] [DecidableEq R] (temporary output : O)

theorem datum_present :
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).present =
      ordinary.present ∪ {temporary} :=
  Materialization.result_present_single X
    (datum ordinary rows closures selected extension datumOpening temporary) temporary rfl rfl

theorem datum_rules :
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).rules = rows :=
  (Materialization.persistent_source_retained X
    (datum ordinary rows closures selected extension datumOpening temporary) selected rfl rfl rfl rfl).1

theorem datum_held (r : R) :
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).held r =
      ((hosted ordinary rows closures).held r).act X (E.weaken extension) :=
  (datum ordinary rows closures selected extension datumOpening temporary).result_held_other
    (by exact List.not_mem_nil)

theorem consumer_rules :
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).rules = rows := by
  change (((datum ordinary rows closures selected extension datumOpening temporary).result X).rules \ ∅) ∪ ∅ = rows
  rw [Finset.sdiff_empty, Finset.union_empty, datum_rules]

theorem consumer_held (r : R) :
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).held r =
      ((hosted ordinary rows closures).held r).act X (E.weaken extension) := by
  have first := (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result_held_other
    (X := X) (ρ := r) (by exact List.not_mem_nil)
  have identity := held_act_identity X
    (((datum ordinary rows closures selected extension datumOpening temporary).result X).held r :
      Held Tm (HeldReadEncoding.Code Tm) Unit (E.target extension))
  exact first.trans (identity.trans
    (datum_held X ordinary rows closures selected extension datumOpening temporary r))

theorem datum_label_other (o : O) (different : o ≠ temporary) :
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).label o =
      X.act (E.weaken extension) (ordinary.label o) :=
  HeldReadDatumSpan.label_other X
    (datum ordinary rows closures selected extension datumOpening temporary)
    temporary (closures selected).schema.value rfl rfl o different

theorem consumer_label_other (o : O) (notOutput : o ≠ output) (notTemporary : o ≠ temporary) :
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).label o =
      X.act (E.weaken extension) (ordinary.label o) := by
  have first := HeldReadDatumSpan.label_other X
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output)
    output (closures selected).schema.value rfl rfl o notOutput
  have identity := X.act_id
    (((datum ordinary rows closures selected extension datumOpening temporary).result X).label o : Tm (E.target extension))
  exact first.trans (identity.trans
    (datum_label_other X ordinary rows closures selected extension datumOpening temporary o notTemporary))

theorem consumer_present (fresh : temporary ∉ ordinary.present) :
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).present =
      ordinary.present ∪ {output} := by
  change ((((datum ordinary rows closures selected extension datumOpening temporary).result X).present \ {temporary}) ∪
    {output}) = _
  rw [datum_present]
  ext o
  by_cases same : o = temporary
  · subst o
    simp [fresh]
  · simp [same]

theorem private_not_present (different : temporary ≠ output) :
    temporary ∉ ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).present :=
  Materialization.consumed_private_instance_not_present X
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output)
    temporary (List.mem_singleton_self _) (by
      change temporary ∉ [output]
      exact fun member => different (List.mem_singleton.mp member))

theorem direct_present :
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).present =
      (ordinary.present ∪ {output}).disjSum rows := by
  ext occurrence
  cases occurrence with
  | inl o => simp [SchematicRows.Firing.result, direct, mixed, Selection.commit, fire]
  | inr r => simp [SchematicRows.Firing.result, direct, mixed, Selection.commit, fire]

#print axioms consumer_rules
#print axioms consumer_held
#print axioms consumer_present
#print axioms private_not_present
#print axioms direct_present

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
