import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticTypingCore

/-!
# Exact declaration inventory for finite Cost profiles

The source cut computes the nonprincipal declaration inventory. Additional
continuation slots retain their authored positions; they do not create a
second constructor authority. The intrinsic Cost constructor and role types
are the existing ones. Materialization uses the finite profile's actual
parameter retyping, including every additional continuation position.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism

namespace ContinuationDecorationProfile
variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Exact nonprincipal closure is the extra declaration fact needed by the
existing region role discipline. It supplies a wrapped declaration for each
static base declaration and excludes both principals. -/
theorem declaredCostConstructorRole_base_static_iff
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment))
    (authored : DeclaredConstructor theory.presentation.presentation) :
    (withNonprincipalInventory programAdditional environmentAdditional).declaredCostConstructorRole
      ⟨.base authored, trivial⟩ = .static .base ↔
      authored ∈ (withNonprincipalInventory programAdditional environmentAdditional).constructorClosure := by
  rw [withNonprincipalInventory_mem]
  simp [declaredCostConstructorRole, not_or]

/-- A certified static base row is uniformly typed; finite retyping of all
principal payload positions remains in the structural boundary instead. -/
theorem static_base_params
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment))
    (authored : DeclaredConstructor theory.presentation.presentation)
    (static : (withNonprincipalInventory programAdditional environmentAdditional).declaredCostConstructorRole
      ⟨.base authored, trivial⟩ = .static .base) :
    ((withNonprincipalInventory programAdditional environmentAdditional).materializeDeclaredCostConstructor
      ⟨.base authored, trivial⟩).params = authored.1.params.map (mapTermParam costBaseStaticSymbols) := by
  have included := (declaredCostConstructorRole_base_static_iff programAdditional environmentAdditional authored).mp static
  have excluded := (withNonprincipalInventory_mem programAdditional environmentAdditional authored).mp included
  exact (withNonprincipalInventory programAdditional environmentAdditional).baseConstructor_params_eq_map_of_nonprincipal
    authored.1 (fun same => excluded.1 (Subtype.ext same))
      (fun same => excluded.2 (Subtype.ext same))

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
