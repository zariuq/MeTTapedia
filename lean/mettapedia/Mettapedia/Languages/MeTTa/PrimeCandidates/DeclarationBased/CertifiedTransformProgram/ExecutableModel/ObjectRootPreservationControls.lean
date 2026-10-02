import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRootPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedControls

/-!
# Controls for the typed templates of the object package

**The identity eliminator's rule is not typed without its endpoint equations**
(`j_not_templateTyped`). Without the equations `a = x` and `a = y`, a substitution
typing the eliminator's context can send the base point to `zero`, the endpoint
and the point to `suc zero` and `zero`, the motive to `λ y p. Id num zero y` and
the method to `refl zero`. The method would then be typed at the motive's value
`P (suc zero) (refl zero)`, whose erasure is convertible, by two β-steps at a
second annotation of the same motive, to `Id num zero (suc zero)`; and no closed
term of the object package proves `zero = suc zero` (`numeral_identity_apart`).
So the equations of the eliminator's reflexivity position are needed, and the
eliminator's template holds only under them (`j_templateTypedEq`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Package (jName)

namespace CodeModel

/-- The motive `λ (y : num). λ (p : Id num zero y). Id num zero y`, annotated with
the domain the eliminator's context asks for. -/
abbrev endpointMotiveC : CTm Tower.Head 0 :=
  .lam cnum (.lam (.id cnum czero (.var 0)) (.id cnum czero (.var 1)))

theorem endpointMotiveC_typed : CTyped objectChurch .nil endpointMotiveC
    (.pi cnum (.pi (.id cnum czero (.var 0)) cU0)) := by
  have formedB : CTyped objectChurch (.snoc .nil cnum) (.id cnum czero (.var 0)) cU0 :=
    cidT cnum_typed czero_typed (.var 0)
  have formed₂ : CTyped objectChurch (.snoc .nil cnum) (.pi (.id cnum czero (.var 0)) cU0) cU1 :=
    cpiT (craise formedB) cU0_typed
  have body : CTyped objectChurch (.snoc (.snoc .nil cnum) (.id cnum czero (.var 0)))
      (.id cnum czero (.var 1)) cU0 :=
    cidT cnum_typed czero_typed (.var 1)
  exact .lamIntro cnum_typed (.sort _) (cpiT (craise cnum_typed) formed₂) (.sort _)
    (.lamIntro formedB (.sort _) formed₂ (.sort _) body)

/-- The instance of the eliminator's context without its endpoint equations:
`a := zero`, `y := suc zero`, `d := refl zero`, `P := endpointMotiveC`,
`x := zero`, `A := num`. -/
def endpointInstance : CSub Tower.Head 6 0 :=
  ![czero, csuc czero, .refl czero, endpointMotiveC, czero, cnum]

theorem endpointInstance_mor : CSubstMor objectChurch cJTele .nil endpointInstance := by
  intro i
  match i with
  | 0 => exact czero_typed
  | 1 => exact csuc_typed czero_typed
  | 2 =>
      have formedB : CTyped objectChurch (.snoc .nil cnum) (.id cnum czero (.var 0)) cU0 :=
        cidT cnum_typed czero_typed (.var 0)
      have β := cbetaTwo (A := cnum) (B := .id cnum czero (.var 0))
        (M := .id cnum czero (.var 1)) (a := czero) (b := .refl czero)
        (cpiT (craise cnum_typed) (cpiT (craise formedB) cU0_typed))
        (cpiT (craise formedB) cU0_typed) (craise formedB)
        (cidT cnum_typed czero_typed (.var 1)) czero_typed (.reflIntro czero_typed)
      exact .conv (.reflIntro czero_typed) (.symm β) (.sort _)
  | 3 => exact endpointMotiveC_typed
  | 4 => exact czero_typed
  | 5 => exact cnum_typed

/-- **The identity eliminator's rule is not typed without its endpoint
equations.** -/
theorem j_not_templateTyped :
    ¬ TemplateTyped objectChurch objectDecls (eliminatorLeft jName) (.var 2) := by
  rintro ⟨Θ, T, know, left, typed⟩
  rw [j_leftType] at left
  cases left
  have lookups : ∀ i, Θ.lookup i = cJTele.lookup i := fun i =>
    Option.some.inj ((know i).symm.trans (j_knowledge i))
  have mor : CSubstMor objectChurch Θ .nil endpointInstance := fun i => by
    rw [lookups i]
    exact endpointInstance_mor i
  rw [j_elabRight] at typed
  -- the method at the motive's value at the endpoint, erased
  have atEnd := (typed.substitute mor).erase
  -- the motive's second annotation computes that value, erased
  have formedB : CTyped objectChurch (.snoc .nil cnum) (.id cnum czero czero) cU0 :=
    cidT cnum_typed czero_typed czero_typed
  have β := cbetaTwo (A := cnum) (B := .id cnum czero czero) (M := .id cnum czero (.var 1))
    (a := csuc czero) (b := .refl czero)
    (cpiT (craise cnum_typed) (cpiT (craise formedB) cU0_typed))
    (cpiT (craise formedB) cU0_typed) (craise formedB)
    (cidT cnum_typed czero_typed (.var 1)) (csuc_typed czero_typed)
    (.reflIntro czero_typed)
  have computed := β.erase
  exact numeral_identity_apart (j := 0) (k := 1) (by decide) (.refl SetProfile.zeroNative)
    (.conv atEnd computed (.sort _))

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
