import Mettapedia.Languages.Agda.Structural.AdministrativeRenaming
import Mettapedia.Languages.Agda.Structural.SpineContextRegularity
import Mettapedia.Languages.Agda.Structural.StaticContextRegularity

/-!
# Context regularity for administrative static derivations

The canonical context algebra is reused through the actual inclusion of rule
presentations. The new core equalities obtain context formation from an actual typed
head or head equality. A conditional spine action by itself need not have a formed context;
in particular its empty rule provides no such evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext)

def ContextRegularity (D : Judgment → Type) : Judgment → Type
  | .core j => Statics.ContextRegularity (fun j => D (.core j)) j
  | .spineAction _ _ _ _ | .spineEquality _ _ _ _ _ => PUnit

def toPriorContext {D : Judgment → Type} {j : SpineStatics.CombinedJudgment}
    (value : ContextRegularity D (mapPrior j)) : SpineStatics.ContextRegularity (fun j => D (mapPrior j)) j := by
  cases j <;> exact value

def ofPriorContext {D : Judgment → Type} {j : SpineStatics.CombinedJudgment}
    (value : SpineStatics.ContextRegularity (fun j => D (mapPrior j)) j) : ContextRegularity D (mapPrior j) := by
  cases j <;> exact value

noncomputable def contextRule {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (renameEvidence : ∀ {j : Statics.Judgment}, D (.core j) →
      Statics.RenamingAction (fun j => D (.core j)) j)
    {j : Judgment} (shape : RuleShape j)
    (children : Evidence D (premises shape))
    (ih : Evidence (ContextRegularity D) (premises shape)) : ContextRegularity D j := by
  cases shape with
  | prior shape =>
      exact ofPriorContext (SpineStatics.contextRule (priorAlgebra algebra) renameEvidence shape
        (priorPremiseEvidence children) (fun position => toPriorContext (priorPremiseEvidence ih position)))
  | eliminationCongruence | emptyElimination | nestedElimination =>
      simp only [premises] at ih
      exact ih 0
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons => exact ⟨⟩

noncomputable def Derivation.contextRegularity {j : Judgment} (tree : Derivation j) :
    ContextRegularity Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => ContextRegularity Derivation j)
    (fun _ _ shape children ih => contextRule
      (IndexedPolynomial.Algebra.initial presentation.polynomial) CoreDerivation.renaming shape children ih)
    () j tree

noncomputable def CoreDerivation.formedContext {n : Nat} {Γ : RawContext n}
    (tree : CoreDerivation (Statics.context Γ)) : Statics.FormedContextEvidence CoreDerivation Γ :=
  Derivation.contextRegularity tree

noncomputable def CoreDerivation.lookupFormation {n : Nat} {Γ : RawContext n}
    (tree : CoreDerivation (Statics.context Γ)) (v : Var (scope n) .term) :
    CoreDerivation (Statics.formed Γ (ContextGeometry.lookup Γ v)) := tree.formedContext.lookup v

noncomputable def CoreDerivation.contextOfFormation {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : CoreDerivation (Statics.formed Γ A)) : CoreDerivation (Statics.context Γ) :=
  Derivation.contextRegularity tree

noncomputable def CoreDerivation.contextOfTyping {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ t A)) : CoreDerivation (Statics.context Γ) :=
  Derivation.contextRegularity tree

noncomputable def CoreDerivation.contextOfTypeEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : CoreDerivation (Statics.typeEqual Γ A B)) : CoreDerivation (Statics.context Γ) :=
  Derivation.contextRegularity tree

noncomputable def CoreDerivation.contextOfTermEquality {n : Nat} {Γ : RawContext n}
    {t u : RawTm n} {A : RawTy n} (tree : CoreDerivation (Statics.termEqual Γ t u A)) :
    CoreDerivation (Statics.context Γ) := Derivation.contextRegularity tree

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
