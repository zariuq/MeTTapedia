import Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation
import Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy

/-!
# The constructed internal universe tower in the set-coded CwF

The existing contextual Tarski hierarchy is instantiated with the actual
set-code tower. Its product and sum decoding equations are strict equalities
of set codes because the selected contextual type formers are themselves
set-coded. This does not turn graph/function equivalences into type equality.
The contextual operations, beta/eta, and substitution laws come from the
independently constructed set-coded CwF.
-/

open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetContextualUniverseInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetDependentProducts ZFSetContextualInterpretation
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
open ZFSetInterpretation

universe u

variable {L : Type} [LevelOrder L]

noncomputable def hierarchy (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    TarskiUniverseFamily L codedCwf.{u} where
  univ _ n := fun _ => universeSet h seed n
  el code := fun γ => (code γ).1

theorem substitutionStable (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (hierarchy (L := L) h seed).SubstitutionStable := by
  constructor <;> intros <;> rfl

noncomputable def cumulative (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (hierarchy (L := L) h seed).StrictlyCumulative (fun i j : L => i ≤ j) where
  liftCode := by
    intro lower upper below context code
    exact fun γ => liftCode below (code γ)
  el_liftCode := by
    intro lower upper below context code
    rfl

noncomputable def piCodeMax {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {i j : L} (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) : Γ → Code h seed (max i j) :=
  fun γ => piCode (a γ) (fun x => b ⟨γ, x⟩)

noncomputable def sigmaCodeMax {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {i j : L} (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) : Γ → Code h seed (max i j) :=
  fun γ => sigmaCode (a γ) (fun x => b ⟨γ, x⟩)

theorem el_piCodeMax {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {i j : L} (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) :
    (hierarchy (L := L) h seed).el (piCodeMax a b) =
      products.pi ((hierarchy (L := L) h seed).el a) ((hierarchy (L := L) h seed).el b) := rfl

theorem el_sigmaCodeMax {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {i j : L} (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) :
    (hierarchy (L := L) h seed).el (sigmaCodeMax a b) =
      sums.sigma ((hierarchy (L := L) h seed).el a) ((hierarchy (L := L) h seed).el b) := rfl

noncomputable def piCodeAt {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : L} (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) : Γ → Code h seed n :=
  fun γ => liftCode (max_le (le_refl n) (le_refl n)) (piCodeMax a b γ)

noncomputable def sigmaCodeAt {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : L} (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) : Γ → Code h seed n :=
  fun γ => liftCode (max_le (le_refl n) (le_refl n)) (sigmaCodeMax a b γ)

noncomputable def productsClosed (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (hierarchy (L := L) h seed).PiClosed products where
  piCode := piCodeAt
  el_piCode _ _ := rfl

noncomputable def sumsClosed (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (hierarchy (L := L) h seed).SigmaClosed sums where
  sigmaCode := sigmaCodeAt
  el_sigmaCode _ _ := rfl

/-! ## Strict contextual and cumulative code coherence -/

theorem piCodeMax_substitution {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ Δ : Type (u + 1)} {i j : L} (θ : Δ → Γ) (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) :
    piCodeMax a b ∘ θ = piCodeMax (a ∘ θ) (fun p => b ⟨θ p.1, p.2⟩) := rfl

theorem sigmaCodeMax_substitution {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ Δ : Type (u + 1)} {i j : L} (θ : Δ → Γ) (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) :
    sigmaCodeMax a b ∘ θ = sigmaCodeMax (a ∘ θ) (fun p => b ⟨θ p.1, p.2⟩) := rfl

theorem piCodeAt_substitution {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ Δ : Type (u + 1)} {n : L} (θ : Δ → Γ) (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) :
    piCodeAt a b ∘ θ = piCodeAt (a ∘ θ) (fun p => b ⟨θ p.1, p.2⟩) := rfl

theorem sigmaCodeAt_substitution {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ Δ : Type (u + 1)} {n : L} (θ : Δ → Γ) (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) :
    sigmaCodeAt a b ∘ θ = sigmaCodeAt (a ∘ θ) (fun p => b ⟨θ p.1, p.2⟩) := rfl

theorem piCodeAt_lift {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n m : L} (below : n ≤ m) (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) :
    (fun γ => liftCode below (piCodeAt a b γ)) =
      piCodeAt (fun γ => liftCode below (a γ)) (fun p => liftCode below (b p)) := rfl

theorem sigmaCodeAt_lift {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n m : L} (below : n ≤ m) (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) :
    (fun γ => liftCode below (sigmaCodeAt a b γ)) =
      sigmaCodeAt (fun γ => liftCode below (a γ)) (fun p => liftCode below (b p)) := rfl

/-! ## The code carrier of an earlier level is internal at every later level -/

noncomputable def universeCodeBelowSection (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (Γ : Type (u + 1)) {c d : L} (below : c < d) : Γ → Code h seed d :=
  fun _ => universeCodeBelow h seed below

theorem el_universeCodeBelowSection (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (Γ : Type (u + 1)) {c d : L} (below : c < d) :
    (hierarchy (L := L) h seed).el (level := d) (universeCodeBelowSection h seed Γ below) =
      (hierarchy (L := L) h seed).univ Γ c := rfl

theorem universeCodeBelowSection_substitution (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    {Γ Δ : Type (u + 1)} (θ : Δ → Γ) {c d : L} (below : c < d) :
    universeCodeBelowSection h seed Γ below ∘ θ = universeCodeBelowSection h seed Δ below := rfl


noncomputable def universeCodeSection (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (Γ : Type (u + 1)) (n : L) : Γ → Code h seed (LevelOrder.succ n) :=
  fun _ => universeCode h seed n

theorem el_universeCodeSection (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (Γ : Type (u + 1)) (n : L) :
    (hierarchy (L := L) h seed).el (level := LevelOrder.succ n) (universeCodeSection h seed Γ n) =
      (hierarchy (L := L) h seed).univ Γ n := rfl

theorem universeCodeSection_substitution (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    {Γ Δ : Type (u + 1)} (θ : Δ → Γ) (n : L) :
    universeCodeSection h seed Γ n ∘ θ = universeCodeSection h seed Δ n := rfl

#print axioms hierarchy
#print axioms substitutionStable
#print axioms cumulative
#print axioms productsClosed
#print axioms sumsClosed
#print axioms el_piCodeMax
#print axioms el_sigmaCodeMax
#print axioms piCodeMax_substitution
#print axioms sigmaCodeMax_substitution
#print axioms piCodeAt_lift
#print axioms sigmaCodeAt_lift
#print axioms el_universeCodeSection
#print axioms el_universeCodeBelowSection

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetContextualUniverseInterpretation
