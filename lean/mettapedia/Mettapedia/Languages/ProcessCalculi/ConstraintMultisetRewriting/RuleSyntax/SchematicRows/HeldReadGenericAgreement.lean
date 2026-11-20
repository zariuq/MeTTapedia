import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericProtocol
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservations

/-!
# The direct and held read return the same complete public live view

The held result is decoded using its actual ordinary state and held arguments.
Its knowledge, public identities and all live raw row labels agree with the
direct result. This includes schema code and variable sharing, not just one
selected answer. Dead temporary label slots are deliberately not observed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}
  (X : Frames Tm Hom) (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))
  [DecidableEq O] [DecidableEq R] (temporary output : O)

theorem direct_label_ordinary (o : O) (different : o ≠ output) :
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).label (.inl o) =
      Row.shared (X.act (E.weaken extension) (ordinary.label o)) := by
  change (if (Sum.inl o : O ⊕ R) = .inl output then
    Row.shared (X.act ruleOpening (closures selected).schema.value)
    else Row.shared (X.act (E.weaken extension) (ordinary.label o))) = _
  exact if_neg (fun same => different (Sum.inl.inj same))

theorem direct_label_schematic (r : R) :
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).label (.inr r) =
      Row.schematic ((closures r).act X (E.weaken extension)) := by
  change (if (Sum.inr r : O ⊕ R) = .inl output then
    Row.shared (X.act ruleOpening (closures selected).schema.value)
    else Row.schematic ((closures r).act X (E.weaken extension))) = _
  exact if_neg (fun impossible => nomatch impossible)

def publicResult : SchematicRows.State Tm (O ⊕ R) :=
  mixed
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).toState
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).rules
    (fun r => ⟨(closures r).schema,
      (((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).held r).args⟩)

theorem public_knowledge :
    (publicResult X ordinary rows closures selected extension ruleOpening datumOpening temporary output).knowledge =
      ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).knowledge :=
  information_eq X ordinary rows closures selected extension ruleOpening datumOpening temporary output

theorem public_present (fresh : temporary ∉ ordinary.present) :
    (publicResult X ordinary rows closures selected extension ruleOpening datumOpening temporary output).present =
      ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).present := by
  change ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).present.disjSum
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).rules = _
  rw [consumer_present X ordinary rows closures selected extension ruleOpening datumOpening temporary output fresh,
    consumer_rules, direct_present]

theorem public_live_labels (fresh : temporary ∉ ordinary.present)
    (occurrence : O ⊕ R)
    (present : occurrence ∈ ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).present) :
    (publicResult X ordinary rows closures selected extension ruleOpening datumOpening temporary output).label occurrence =
      ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).label occurrence := by
  cases occurrence with
  | inl o =>
    by_cases same : o = output
    · subst o
      exact (congrArg (Row.shared (Tm := Tm))
        (consumer_output_label X ordinary rows closures selected extension ruleOpening datumOpening temporary output)).trans
          (direct_output_label X ordinary rows closures selected extension ruleOpening datumOpening output).symm
    · have old : o ∈ ordinary.present := by
        rw [direct_present, Finset.inl_mem_disjSum, Finset.mem_union, Finset.mem_singleton] at present
        exact present.resolve_right same
      have notTemporary : o ≠ temporary := fun equality => fresh (equality ▸ old)
      exact (congrArg (Row.shared (Tm := Tm))
        (consumer_label_other X ordinary rows closures selected extension ruleOpening datumOpening temporary output o same notTemporary)).trans
          (direct_label_ordinary X ordinary rows closures selected extension ruleOpening datumOpening output o same).symm
  | inr r =>
    have args :
        (((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).held r).args =
          (closures r).args.map (X.act (E.weaken extension)) :=
      congrArg (fun held : Held Tm (HeldReadEncoding.Code Tm) Unit (E.target extension) => held.args)
        (consumer_held X ordinary rows closures selected extension ruleOpening datumOpening temporary output r)
    have closureLabels := congrArg
      (fun arguments : List (Tm (E.target extension)) =>
        (Row.schematic (⟨(closures r).schema, arguments⟩ : Closure Tm (E.target extension)))) args
    exact closureLabels.trans
      (direct_label_schematic X ordinary rows closures selected extension ruleOpening datumOpening output r).symm

theorem public_view_eq (fresh : temporary ∉ ordinary.present) :
    LiveObservations.observe (publicResult X ordinary rows closures selected extension ruleOpening datumOpening temporary output) =
      LiveObservations.observe ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X) := by
  exact (LiveObservations.observe_eq (E.target extension)
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).knowledge
    (publicResult X ordinary rows closures selected extension ruleOpening datumOpening temporary output).knowledge
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).present
    (publicResult X ordinary rows closures selected extension ruleOpening datumOpening temporary output).present
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).label
    (publicResult X ordinary rows closures selected extension ruleOpening datumOpening temporary output).label
    (public_knowledge X ordinary rows closures selected extension ruleOpening datumOpening temporary output).symm
    (public_present X ordinary rows closures selected extension ruleOpening datumOpening temporary output fresh).symm
    (fun occurrence present =>
      (public_live_labels X ordinary rows closures selected extension ruleOpening datumOpening temporary output fresh occurrence present).symm)).symm

#print axioms public_knowledge
#print axioms public_present
#print axioms public_live_labels
#print axioms public_view_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
