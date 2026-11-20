import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericAdmission

/-!
# Reading a schematic occurrence of an arbitrary mixed source

The selected datum supplies its own local frame. A dependent accessor rejects
the shared-row branch and retains the actual schematic opening. The common
ordinary/held representation is the existing encoding, with its explicit
ordinary-label filler; no globally inhabited term frame is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter

open Interface (Frames)
open HeldReadEncoding HeldReadGenericFirings
open JointFirings

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}

def schemaUse {a target : Obj} : (row : Row Tm a) →
    Hom (closure row).schema.locals target → sharedTag row = false → RowUse Tm Hom target row
  | .shared _, _, impossible => nomatch impossible
  | .schematic row, opening, _ => .schematic row opening

theorem schemaUse_packed {a target : Obj} (row : Row Tm a)
    (opening : Hom (closure row).schema.locals target) (schematic : sharedTag row = false) :
    (⟨row, schemaUse row opening schematic⟩ : PackedUse Tm Hom a target) =
      ⟨.schematic (closure row), RowUse.schematic (closure row) opening⟩ := by
  cases row with
  | shared _ => cases schematic
  | schematic _ => rfl

variable (source : SchematicRows.State Tm O) (selected output : O) (extension : E.Ext source.frame)
  (ruleOpening datumOpening : Hom (closure (source.label selected)).schema.locals (E.target extension))
  (schematic : sharedTag (source.label selected) = false)

def direct : SchematicRows.Firing O E (copyProgram (closure (source.label selected)).schema) source where
  rule := SchematicRows.Rule.ofShared (copyRule (closure (source.label selected)).schema)
  member := Set.mem_singleton _
  ext := extension
  opening := ruleOpening
  selection := ⟨[], [selected], [output]⟩
  taken i := Fin.elim0 i
  read i := by
    have same : i = 0 := Fin.eq_zero i
    subst i
    exact schemaUse (source.label selected) datumOpening schematic
  seen := []

theorem direct_readUses :
    (direct source selected output extension ruleOpening datumOpening schematic).readUses =
      [⟨.schematic (closure (source.label selected)),
        RowUse.schematic (closure (source.label selected)) datumOpening⟩] :=
  congrArg (fun packed => [packed]) (schemaUse_packed (source.label selected) datumOpening schematic)

theorem direct_uses :
    (direct source selected output extension ruleOpening datumOpening schematic).uses =
      [⟨.schematic (closure (source.label selected)),
        RowUse.schematic (closure (source.label selected)) datumOpening⟩] :=
  direct_readUses source selected output extension ruleOpening datumOpening schematic

variable (filler : Tm source.frame)

def common :=
  HeldReadGenericSources.mixed (encode source filler).toState (encode source filler).rules
    (fun o => closure (source.label o))

def commonDirect := HeldReadGenericFirings.direct
  (encode source filler).toState (encode source filler).rules (fun o => closure (source.label o))
  selected extension ruleOpening datumOpening output

theorem hosted_common :
    HeldReadGenericSources.hosted (encode source filler).toState (encode source filler).rules
      (fun o => closure (source.label o)) = encode source filler := rfl

theorem common_mentions (term : Tm source.frame) :
    source.scope.Mentions term ↔ (common source filler).scope.Mentions term :=
  (HeldReadEncoding.scope_mentions_iff source filler term).symm.trans
    (HeldReadGenericSources.scope_mentions_iff (encode source filler).toState
      (encode source filler).rules (fun o => closure (source.label o)) term).symm

theorem scope_members :
    (direct source selected output extension ruleOpening datumOpening schematic).scopeBag.members =
      (commonDirect source selected output extension ruleOpening datumOpening filler).scopeBag.members := by
  unfold SchematicRows.Firing.scopeBag
  rw [direct_uses]
  rfl

variable (X : Frames Tm Hom)

theorem fresh_iff :
    (direct source selected output extension ruleOpening datumOpening schematic).Fresh X ↔
      (commonDirect source selected output extension ruleOpening datumOpening filler).Fresh X := by
  have members := scope_members source selected output extension ruleOpening datumOpening schematic filler
  constructor
  · intro fresh target caller
    have realized := fresh target caller
    have renamed := members ▸ realized
    apply Realized.mono X _ ?_ renamed
    intro combined kept term mentioned
    exact kept term ((common_mentions source filler term).mpr mentioned)
  · intro fresh target caller
    have realized := fresh target caller
    have renamed := members.symm ▸ realized
    apply Realized.mono X _ ?_ renamed
    intro combined kept term mentioned
    exact kept term ((common_mentions source filler term).mp mentioned)

#print axioms schemaUse_packed
#print axioms direct_uses
#print axioms hosted_common
#print axioms common_mentions
#print axioms scope_members
#print axioms fresh_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter
