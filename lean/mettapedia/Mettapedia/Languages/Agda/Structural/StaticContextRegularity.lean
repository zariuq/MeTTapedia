import Mettapedia.Languages.Agda.Structural.StaticRenaming

/-!
# Context formation recovered from structural static derivations

The rule algebra recovers an actual formation tree for the context of every
type, term, and equality judgment. A context tree also supplies formation of
every dependent lookup. The latter uses admissible weakening, including the
older declarations under a newly added variable.

The algebra is parametrized by the evidence family so that extensions reuse
these cases while allowing their own derivations in every recursive premise.
It does not assume regularity as a field or add it as an inference rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

structure FormedContextEvidence (D : Judgment → Type) {n : Nat} (Γ : RawContext n) where
  tree : D (context Γ)
  lookup : (v : Var (scope n) .term) → D (formed Γ (ContextGeometry.lookup Γ v))

def ContextRegularity (D : Judgment → Type) : Judgment → Type
  | .context ⟨_, Γ⟩ => FormedContextEvidence D Γ
  | .type ⟨_, Γ⟩ _ => D (context Γ)
  | .term ⟨_, Γ⟩ _ _ => D (context Γ)
  | .typeEquality ⟨_, Γ⟩ _ _ => D (context Γ)
  | .termEquality ⟨_, Γ⟩ _ _ _ => D (context Γ)
  | .substitution _ _ _ => Empty

def contextRule {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (renameEvidence : ∀ {j : Judgment}, D j → RenamingAction D j)
    {j : Judgment} (shape : RuleShape j)
    (children : Evidence D (premises shape))
    (ih : Evidence (ContextRegularity D) (premises shape)) : ContextRegularity D j := by
  let build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  cases shape <;> simp only [premises] at children ih
  case empty => exact ⟨build .empty (noEvidence D), fun v => nomatch v⟩
  case extend Γ A =>
    let target := build (.extend Γ A) children
    refine ⟨target, fun v => ?_⟩
    cases v with
    | zero =>
      have image := renameEvidence (children 1) (Γ.snoc A)
        (Telescope.RawRen.projection (S := sig) .term _)
        (Telescope.RawRen.respects_projection Γ A) target
      exact (congrArg (fun T => D (formed (Γ.snoc A) T))
        (Telescope.bind_projection (S := sig) (b := .term) A)).mp image
    | succ v =>
      have image := renameEvidence ((ih 0).lookup v) (Γ.snoc A)
        (Telescope.RawRen.projection (S := sig) .term _)
        (Telescope.RawRen.respects_projection Γ A) target
      exact (congrArg (fun T => D (formed (Γ.snoc A) T))
        (Telescope.bind_projection (S := sig) (b := .term) (ContextGeometry.lookup Γ v))).mp image
  case formation => exact ih 0
  case sort => exact children 0
  case «variable» => exact children 0
  case pi => exact ih 0
  case lambda => exact ih 0
  case application => exact ih 0
  case conversion => exact ih 0
  case typeEquality => exact ih 0
  case reflexivity => exact ih 0
  case symmetry => exact ih 0
  case transitivity => exact ih 0
  case equalityConversion => exact ih 0
  case piCongruence => exact ih 0
  case applicationCongruence => exact ih 0
  case beta => exact ih 0
  case eta => exact ih 0

/-- Recursion on actual rule trees supplies both context and lookup regularity. -/
noncomputable def Derivation.contextRegularity {j : Judgment} (tree : Derivation j) :
    ContextRegularity Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => ContextRegularity Derivation j)
    (fun _ _ shape children ih => contextRule
      (IndexedPolynomial.Algebra.initial presentation.polynomial) Derivation.renaming shape children ih)
    () j tree

noncomputable def Derivation.formedContext {n : Nat} {Γ : RawContext n}
    (tree : Derivation (context Γ)) : FormedContextEvidence Derivation Γ := tree.contextRegularity

noncomputable def Derivation.lookupFormation {n : Nat} {Γ : RawContext n}
    (tree : Derivation (context Γ)) (v : Var (scope n) .term) :
    Derivation (formed Γ (ContextGeometry.lookup Γ v)) := tree.formedContext.lookup v

noncomputable def Derivation.contextOfFormation {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : Derivation (formed Γ A)) : Derivation (context Γ) := tree.contextRegularity

noncomputable def Derivation.contextOfTyping {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : Derivation (typed Γ t A)) : Derivation (context Γ) := tree.contextRegularity

noncomputable def Derivation.contextOfTypeEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : Derivation (typeEqual Γ A B)) : Derivation (context Γ) := tree.contextRegularity

noncomputable def Derivation.contextOfTermEquality {n : Nat} {Γ : RawContext n}
    {t u : RawTm n} {A : RawTy n} (tree : Derivation (termEqual Γ t u A)) :
    Derivation (context Γ) := tree.contextRegularity

end Mettapedia.Languages.Agda.Structural.Statics
