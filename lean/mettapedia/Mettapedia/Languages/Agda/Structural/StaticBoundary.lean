import Mettapedia.Languages.Agda.Structural.StaticConstructors
import Mettapedia.Languages.Agda.Structural.Reduction

/-!
# The canonical static fragment does not type administrative spine nodes

The eighteen canonical rules type ordinary applications. Structural beta
computation retains the remaining spine, even when it is empty. This module
exhibits an actual typed beta redex whose intermediate result has no derivation
in the canonical static presentation. Thus pairing that presentation with every
structural computation step does not satisfy subject reduction.

The boundary is a counterexample to an overbroad claim, not a reduction or
typing rule. A spine-typing extension must account for the intermediate nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics.Boundary

open Mettapedia.OSLF.Binding

def hasEmptyElimination {n : Nat} : RawTm n → Bool
  | .op .eliminate (.cons _ (.cons (.op .nil .nil) .nil)) => true
  | _ => false

/-- This observation restricts term-typing conclusions only. -/
def excludesEmpty (j : Judgment) : Prop :=
  match j with
  | .term ⟨_, _⟩ _ ⟨term⟩ => hasEmptyElimination term = false
  | _ => True

theorem rules_exclude_empty : presentation.RuleClosed (fun _ j => excludesEmpty j) := by
  intro _ j shape children
  cases shape with
  | conversion Γ t A B => exact children ⟨0, by change 0 < 2; decide⟩
  | pi Γ A B => cases B <;> rfl
  | lambda Γ A B body => cases body <;> rfl
  | _ => first | rfl | trivial

theorem no_empty_elimination_typing {n : Nat} (Γ : RawContext n) (head : RawTm n) (A : RawTy n) :
    ¬ Nonempty (Derivation (typed Γ (eliminate head nil) A)) := by
  rintro ⟨d⟩
  have impossible := least excludesEmpty rules_exclude_empty _ d
  change true = false at impossible
  contradiction

def universeFormed {n : Nat} {Γ : RawContext n} (formed : Derivation (context Γ)) (k : Nat) :
    Derivation (Statics.formed Γ (universeType n k).code) :=
  Derivation.formation (Derivation.sort k formed)

def domain : TypeParameter 0 := universeType 0 1
def oneContext : RawContext 1 := .snoc .nil domain.code
def oneContextFormed : Derivation (context oneContext) :=
  Derivation.extend Derivation.empty (universeFormed Derivation.empty 1)

def identityType : TypeParameter 0 := piType domain (.noBind domain)
def identityTerm : RawTm 0 := lam (.var .zero)
def identityTyped : Derivation (typed (.nil : RawContext 0) identityTerm identityType.code) :=
  Derivation.lambda (A := domain) (B := .noBind domain) (body := .bind (.var .zero))
    (universeFormed Derivation.empty 1) (universeFormed oneContextFormed 1)
    (Derivation.variableTerm (Γ := oneContext) .zero oneContextFormed)

def redexTyped : Derivation
    (typed (.nil : RawContext 0) (app identityTerm (universeTerm 0)) (universeType 0 1).code) :=
  Derivation.application (A := domain) (B := .noBind domain)
    identityTyped (Derivation.sort 0 Derivation.empty)

def betaStep : Step (app identityTerm (universeTerm 0)) (eliminate (universeTerm 0) nil) :=
  .root (.beta (.var .zero) (universeTerm 0) nil)

theorem beta_intermediate_untypable :
    ¬ Nonempty (Derivation
      (typed (.nil : RawContext 0) (eliminate (universeTerm 0) nil) (universeType 0 1).code)) :=
  no_empty_elimination_typing .nil _ _

theorem unrestricted_subject_reduction_false :
    ¬ (∀ {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A : RawTy n},
      Derivation (typed Γ t A) → Step t u → Nonempty (Derivation (typed Γ u A))) := by
  intro preserve
  exact beta_intermediate_untypable (preserve redexTyped betaStep)

end Mettapedia.Languages.Agda.Structural.Statics.Boundary
