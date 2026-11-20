import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericSources
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Step
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadFreshStaging
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Materialization

/-!
# Direct and materialize/consume readings at an arbitrary frame

Both copy rules use the datum's own local frame and value pattern. They do not
require a universal variable object. The direct reading and held activation
are independently constructed actual firings of the existing candidates.
The internal consumer uses the explicitly supplied identity-extension family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}

def copyRule (schema : Schema Tm) : RuleSyntax.Rule Tm :=
  ⟨schema.locals, ⟨[], [schema.value], [], [], [schema.value]⟩, []⟩

def consumeRule (schema : Schema Tm) : RuleSyntax.Rule Tm :=
  ⟨schema.locals, ⟨[schema.value], [], [], [], [schema.value]⟩, []⟩

def copyProgram (schema : Schema Tm) : Set (SchematicRows.Rule Tm) :=
  {SchematicRows.Rule.ofShared (copyRule schema)}

variable (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))

def direct (output : O) :
    SchematicRows.Firing (O ⊕ R) E (copyProgram (closures selected).schema) (mixed ordinary rows closures) where
  rule := SchematicRows.Rule.ofShared (copyRule (closures selected).schema)
  member := Set.mem_singleton _
  ext := extension
  opening := ruleOpening
  selection := ⟨[], [.inr selected], [.inl output]⟩
  taken i := Fin.elim0 i
  read i := by
    have same : i = 0 := Fin.eq_zero i
    subst i
    exact .schematic (closures selected) datumOpening
  seen := []

def datum (temporary : O) :
    RFiring O R E HeldReadEncoding.codes (hosted ordinary rows closures) where
  use := .held selected
  ext := extension
  opening := datumOpening
  selection := ⟨[], [], [temporary]⟩
  seen := []
  madeRules := []
  installed := []
  removedRules := []
  published := []

variable (X : Frames Tm Hom)

def datumInformation : EquationStore (Tm (E.target extension)) :=
  X.applyStore (E.weaken extension) ordinary.knowledge ++
    X.applyStore datumOpening (closures selected).schema.knowledge ++
    ((closures selected).schema.params.map (X.act datumOpening)).zip
      ((closures selected).args.map (X.act (E.weaken extension)))

theorem datum_information (temporary : O) :
    (datum ordinary rows closures selected extension datumOpening temporary).information X =
      datumInformation ordinary closures selected extension datumOpening X := by
  exact Opening.information_no_inputs X
    (datum ordinary rows closures selected extension datumOpening temporary) rfl rfl

theorem direct_information (output : O) :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).information X =
      datumInformation ordinary closures selected extension datumOpening X ++
        [(X.act ruleOpening (closures selected).schema.value,
          X.act datumOpening (closures selected).schema.value)] := by
  change (X.applyStore (E.weaken extension) ordinary.knowledge ++
      ((X.applyStore datumOpening (closures selected).schema.knowledge ++
        ((closures selected).schema.params.map (X.act datumOpening)).zip
          ((closures selected).args.map (X.act (E.weaken extension)))) ++ [])) ++ [] ++
      [(X.act ruleOpening (closures selected).schema.value,
        X.act datumOpening (closures selected).schema.value)] ++ X.applyStore ruleOpening [] =
    datumInformation ordinary closures selected extension datumOpening X ++
      [(X.act ruleOpening (closures selected).schema.value,
        X.act datumOpening (closures selected).schema.value)]
  simp only [datumInformation, Frames.applyStore, List.map_nil, List.append_nil, List.append_assoc]

variable [DecidableEq O] [DecidableEq R]

def consumer (temporary output : O) :
    RFiring O R (HeldReadScopeReassociation.identityExtensions X) HeldReadEncoding.codes
      ((datum ordinary rows closures selected extension datumOpening temporary).result X) where
  use := .ambient (.inr (consumeRule (closures selected).schema))
  ext := PUnit.unit
  opening := ruleOpening
  selection := ⟨[temporary], [], [output]⟩
  seen := []
  madeRules := []
  installed := []
  removedRules := []
  published := []

#print axioms datum_information
#print axioms direct_information

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
