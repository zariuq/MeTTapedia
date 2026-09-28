import Mettapedia.Languages.Agda.Structural.AdministrativeTypeViews
import Mettapedia.Languages.Agda.Structural.StaticPiFormation

/-!
# Syntactic Pi generation in the administrative presentation

The original Pi-generation algebra is applied to its actual premise trees in
the enlarged family. Elimination typing cannot introduce a raw Pi constructor,
and the added equality rules do not add a term-typing constructor. This is
generation for written Pi syntax, not Pi injectivity modulo typed conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawContext TypeParameter TypeBody)

def PiFormation : Judgment → Type
  | .core j => Statics.PiFormation CoreDerivation j
  | _ => PUnit

def piFormationRule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence PiFormation (premises shape)) : PiFormation j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core shape =>
          exact Statics.piFormationRule shape (SpineStatics.corePremiseEvidence children)
            (SpineStatics.corePremiseEvidence ih)
      | nil | cons | append | inputConversion | outputConversion => exact ⟨⟩
      | elimination =>
          intro A B same
          cases B <;> cases same
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def Derivation.piFormation {j : Judgment} (tree : Derivation j) : PiFormation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => PiFormation j)
    (fun _ _ shape children ih => piFormationRule shape children ih) () j tree

noncomputable def CoreDerivation.formationPiParts {n : Nat} {Γ : RawContext n}
    {A : TypeParameter n} {B : TypeBody n}
    (tree : CoreDerivation (Statics.formed Γ (Statics.piType A B).code)) :
    CoreDerivation (Statics.formed Γ A.code) × CoreDerivation (Statics.formed (Γ.snoc A.code) B.open.code) :=
  tree.piFormation A B rfl

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
