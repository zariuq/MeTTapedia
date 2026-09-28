import Mettapedia.Languages.Agda.Structural.AdministrativeEndpointRegularity
import Mettapedia.Languages.Agda.Structural.StaticAdmission
import Mettapedia.Languages.Agda.Structural.StaticContextConversion

/-!
# Admitted contexts for the administrative presentation

The contextual construction uses the actual thirty-six-rule derivations and
their proved substitution action. Its supported category retains raw context
and substitution syntax; derivation histories remain in their companion
fibres. Dependent context conversion is instantiated with the proved native
endpoint operation, rather than an assumed regularity law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory
open Statics (RawContext)

noncomputable def administrativeAdmission : CwfDerivations Statics.rawCwf :=
  Statics.admissionData coreAlgebra CoreDerivation.substitution

noncomputable def administrativeCwf : CwfWithTerminal :=
  CwfDerivations.admittedWithTerminal ContextGeometry.rawAgdaTelescopeCwfWithTerminal
    administrativeAdmission (includeCanonical Statics.Derivation.empty)
    (fun _ formed => Statics.TypedSubstitution.empty coreAlgebra formed)

abbrev ContextConversion {n : Nat} (Γ Δ : RawContext n) := Statics.ContextConversion CoreDerivation Γ Δ

noncomputable def ContextConversion.identitySubstitution {n : Nat} {Γ Δ : RawContext n}
    (conversion : ContextConversion Γ Δ) :
    Statics.TypedSubstitution CoreDerivation Γ Δ (Telescope.identity (S := sig) .term n) :=
  Statics.ContextConversion.identitySubstitution administrativeOperations CoreDerivation.typeEndpoints conversion

noncomputable def ContextConversion.typing {n : Nat} {Γ Δ : RawContext n}
    (conversion : ContextConversion Γ Δ) {t : Statics.RawTm n} {A : Statics.RawTy n}
    (typed : CoreDerivation (Statics.typed Γ t A)) : CoreDerivation (Statics.typed Δ t A) :=
  Statics.ContextConversion.typing administrativeOperations CoreDerivation.typeEndpoints conversion typed

def ContextReflexivity : Judgment → Type
  | .core j => Statics.ContextReflexivity CoreDerivation j
  | _ => PUnit

noncomputable def CoreDerivation.contextReflexivity {n : Nat} {Γ : RawContext n}
    (tree : CoreDerivation (Statics.context Γ)) : ContextConversion Γ Γ := by
  refine IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => ContextReflexivity j) ?_ () (.core (Statics.context Γ)) tree
  intro _ _ shape children ih
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact Statics.contextReflexivityRule administrativeOperations shape
            (SpineStatics.corePremiseEvidence children) (SpineStatics.corePremiseEvidence ih)
      | nil | cons | append | inputConversion | outputConversion | elimination => exact ⟨⟩
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
