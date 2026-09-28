import Mettapedia.Languages.Agda.Structural.SpineRenaming
import Mettapedia.Languages.Agda.Structural.StaticContextRegularity

/-!
# Context regularity with recursively admitted spine terms

The canonical context algebra is reused through the actual inclusion of rule
presentations. An elimination obtains its context formation from its typed
head. A conditional spine action by itself need not have a formed context;
in particular its empty rule provides no such evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext)

def ContextRegularity (D : CombinedJudgment → Type) : CombinedJudgment → Type
  | .core j => Statics.ContextRegularity (fun j => D (.core j)) j
  | .spineAction _ _ _ _ => PUnit

noncomputable def contextRule {D : CombinedJudgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (renameEvidence : ∀ {j : Statics.Judgment}, D (.core j) →
      Statics.RenamingAction (fun j => D (.core j)) j)
    {j : CombinedJudgment} (shape : RuleShape j)
    (children : Evidence D (premises shape))
    (ih : Evidence (ContextRegularity D) (premises shape)) : ContextRegularity D j := by
  cases shape with
  | core shape =>
      exact Statics.contextRule (canonicalAlgebra algebra) renameEvidence shape
        (corePremiseEvidence children) (corePremiseEvidence ih)
  | elimination =>
      simp only [premises] at ih
      exact ih 0
  | nil | cons | append | inputConversion | outputConversion => exact ⟨⟩

noncomputable def Derivation.contextRegularity {j : CombinedJudgment} (tree : Derivation j) :
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

end Mettapedia.Languages.Agda.Structural.SpineStatics
