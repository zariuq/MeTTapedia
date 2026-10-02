import Mettapedia.GSLT.LanguageDef.ContinuationRetyping

/-!
# Cuts whose two operands are introductions

In a process calculus the two operands of the interaction rule are prefixes:
each is introduced by its own constructor, different from the contact.  Two
side conditions of an interaction cut and of its continuation signature are
then inequalities between declared constructors, and both follow from an
inequality between labels.

* An operand whose constructor label differs from the contact's is placed
  away from contact.
* A constructor whose label differs from the labels of the two introductions
  belongs to the continuation closure of the cut: it receives a wrapped copy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism

/-- An introduced operand whose constructor is labelled differently from the
contact is placed away from contact. -/
theorem InteractionOperandPlacement.of_label_ne
    {interactive : InteractivePresentation}
    {contact : CoreContactPresentation interactive.presentation}
    {side : CutSide} {operand : InteractionOperandProfile interactive}
    (kind : operand.kind = .introduced)
    (labels : operand.constructor.1.label ≠ contact.constructor.1.label) :
    InteractionOperandPlacement contact side operand :=
  .introduced kind fun equality =>
    labels (congrArg (fun constructor => constructor.1.label) equality)

/-- A declared constructor labelled differently from both introductions of a
cut belongs to its continuation closure. -/
theorem mem_continuationConstructors_of_label_ne {theory : IGSLT}
    (cut : InteractionCutPresentation theory)
    (constructor : DeclaredConstructor theory.presentation.presentation)
    (program : constructor.1.label ≠ cut.program.constructor.1.label)
    (environment : constructor.1.label ≠ cut.environment.constructor.1.label) :
    constructor ∈ continuationConstructors cut := by
  apply (ContinuationRetypingPlan.mem_continuationConstructors_iff cut constructor).2
  constructor
  · intro equality
    exact program (congrArg (fun declared => declared.1.label) equality)
  · intro equality
    exact environment (congrArg (fun declared => declared.1.label) equality)

/-- The wrapped copy of such a constructor is a constructor of the
continuation signature. -/
theorem ContinuationRetypingPlan.costWrappedConstructor_mem_of_label_ne {theory : IGSLT}
    {cut : InteractionCutPresentation theory} (plan : ContinuationRetypingPlan cut)
    (constructor : DeclaredConstructor theory.presentation.presentation)
    (program : constructor.1.label ≠ cut.program.constructor.1.label)
    (environment : constructor.1.label ≠ cut.environment.constructor.1.label) :
    costWrappedConstructor (theory := theory) constructor.1 ∈
      plan.generatedLanguage.terms :=
  plan.costWrappedConstructor_mem_generated constructor
    (mem_continuationConstructors_of_label_ne cut constructor program environment)

end Mettapedia.GSLT.LanguageDef
