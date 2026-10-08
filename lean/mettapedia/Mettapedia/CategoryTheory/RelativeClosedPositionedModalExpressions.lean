import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicPresentation

/-!
# Authored complete-input expressions for positioned modalities

Function inputs are independent raw predicate functions. Implication is
formed on their full value and parameter context. Precomposition retains
the actual assay and reduct maps; universal quantification binds complete
instances over focus assignments, and existential quantification reads
the actual focus image.

These expressions are reusable raw constituents. A modality declaration
must additionally retain an authored rewrite and selected position; an
arbitrary collection of arrows does not itself supply those origins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPositionedModal

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedPredicateLogic

universe k
variable {C : Type k} [Category.{k} C]

def pointwiseImplicationRaw {context : Object (signature (C := C))} (value : C)
    (first second : RawHom context (power value)) : RawHom context (power value) :=
  RawHom.quote (implyRaw (RawHom.read first) (RawHom.read second))

variable {instances assignments assay carrier outgoing : C}

def conditionRaw (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    RawHom (product (power assay) (power outgoing)) (power instances) :=
  pointwiseImplicationRaw instances
    ((RawHom.first (power assay) (power outgoing)).compose (precompositionRaw instantiate))
    ((RawHom.second (power assay) (power outgoing)).compose (precompositionRaw reduct))

def modalityRaw (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    RawHom (product (power assay) (power outgoing)) (power carrier) :=
  ((conditionRaw instantiate reduct).compose (universalRaw forget)).compose (existentialRaw focus)

def possibilityRaw {events programs : C} (source target : events ⟶ programs) :
    RawHom (power programs) (power programs) :=
  (precompositionRaw target).compose (existentialRaw source)

end Mettapedia.CategoryTheory.RelativeClosedPositionedModal
