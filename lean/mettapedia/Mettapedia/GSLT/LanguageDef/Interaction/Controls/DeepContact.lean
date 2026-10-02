import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactMorphisms

/-!
# A contact rule that looks inside its operand

The same signature as the contact family, with one rule: an input prefix
meets an output prefix whose body is wrapped, and the rule unwraps it,

  `Join(In(x), Out(Wrap(y))) ⟶ Join(x, y)`.

The theory is interactive, and it reduces.  Its rule does not factor as two
introductions each handing over a continuation: on the output side the
argument of the prefix is not a continuation but a term the rule takes
apart.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- An input meets an output whose body is wrapped, and the wrapper is
removed. -/
def deepRule : RewriteRule where
  name := "DeepSync"
  typeContext := [("x", .base "Proc"), ("y", .base "Proc")]
  premises := []
  left := join (input (.fvar "x")) (output (wrap (.fvar "y")))
  right := join (.fvar "x") (.fvar "y")

/-- The contact signature with the unwrapping rule. -/
def contactDeep : LanguageDef :=
  { name := "Contact"
    types := ["Proc"]
    terms := terms
    equations := []
    rewrites := [deepRule] }

theorem deepRule_validates : LanguageDef.validateRewrite contactDeep deepRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [deepRule, contactDeep, terms, join, input, output, wrap]

/-- The theory passes the declaration gate. -/
theorem contactDeep_validate_eq_nil : contactDeep.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    obtain rfl : rewrite = deepRule := List.mem_singleton.mp membership
    exact deepRule_validates

/-- The presentation: processes, the contact `Join`, and the unwrapping
rule. -/
def deepPresentation : InteractivePresentation where
  presentation := ⟨contactDeep, contactDeep_validate_eq_nil⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨terms[7], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨deepRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

theorem deep_executionFlowErrors_eq_nil : contactDeep.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    obtain rfl : rule = deepRule := List.mem_singleton.mp membership
    rfl
  · intro rule membership name nameMembership
    obtain rfl : rule = deepRule := List.mem_singleton.mp membership
    simp [deepRule, join, input, output, wrap, Pattern.freeFvarNames] at nameMembership ⊢
    exact nameMembership

/-- The theory as an iGSLT. -/
def deep : IGSLT where
  presentation := deepPresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := contactDeep
          admitted := LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes _
            contactDeep_validate_eq_nil deep_executionFlowErrors_eq_nil }
      exactLanguage := rfl }

/-- It is interactive: a same-sort contact heads a base rule. -/
theorem contactDeep_isInteractive : IsInteractive contactDeep :=
  deepPresentation.isInteractive (isBaseRewrite_of_premises_eq_nil rfl)

/-- It reduces: `Join(In(A), Out(Wrap(B)))` steps to `Join(A, B)`. -/
theorem deep_steps :
    Step base contactDeep (join (input termA) (output (wrap termB))) (join termA termB) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

end Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
