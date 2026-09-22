import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetContextualUniverseInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
import Mettapedia.Logic.HOL.Embedding.ZFSetListClosure

/-!
# Trace products and actual lists in the existing internal universe tower

The constructed tower, its codes, cumulative inclusions and decoding are
reused unchanged. Trace product codes have proved closure at the maximum
level and strict contextual decoding. Canonical proof products remain small
even for large set domains, by the independently proved trace truth law.
A natural-index seed additionally closes every level under actual lists.
These are constructed model components, not full native syntax soundness.
-/

open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetDependentProducts ZFSetTraceProducts
open ZFSetContextualInterpretation (codedCwf)
open ZFSetTraceProofDecoding (truthCode truthFamily)
open ZFSetInterpretation
open ZFSetContextualUniverseInterpretation (hierarchy)
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy

universe u

noncomputable def piCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) : Code h seed (max i j) :=
  ⟨tracePiSet a.1 (fibres a b), (universeSet_closed h seed _).tracePiSet_mem
    (universeSet_mono h seed (Nat.le_max_left i j) a.2) _ (fun x hx => by
      rw [fibres_at a b ⟨x, hx⟩]
      exact universeSet_mono h seed (Nat.le_max_right i j) (b ⟨x, hx⟩).2)⟩

noncomputable def piCodeMax {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {i j : Nat} (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) : Γ → Code h seed (max i j) :=
  fun γ => piCode (a γ) (fun x => b ⟨γ, x⟩)

theorem el_piCodeMax {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {i j : Nat} (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) :
    (hierarchy h seed).el (piCodeMax a b) =
      ZFSetTraceContextual.products.pi ((hierarchy h seed).el a) ((hierarchy h seed).el b) := rfl

noncomputable def piCodeAt {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) : Γ → Code h seed n :=
  fun γ => liftCode (Nat.max_le.mpr ⟨Nat.le_refl n, Nat.le_refl n⟩) (piCodeMax a b γ)

noncomputable def productsClosed (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (hierarchy h seed).PiClosed ZFSetTraceContextual.products where
  piCode := piCodeAt
  el_piCode _ _ := rfl

theorem piCodeMax_substitution {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ Δ : Type (u + 1)} {i j : Nat} (θ : Δ → Γ) (a : Γ → Code h seed i)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed j) :
    piCodeMax a b ∘ θ = piCodeMax (a ∘ θ) (fun pair => b ⟨θ pair.1, pair.2⟩) := rfl

theorem piCodeAt_lift {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n m : Nat} (below : n ≤ m) (a : Γ → Code h seed n)
    (b : (Σ γ : Γ, El (a γ)) → Code h seed n) :
    (fun γ => liftCode below (piCodeAt a b γ)) =
      piCodeAt (fun γ => liftCode below (a γ)) (fun pair => liftCode below (b pair)) := rfl

/-! ## Proof products decode literally and inhabit the bottom universe -/

theorem truthCode_mem (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (n : Nat) (P : Prop) : truthCode P ∈ universeSet h seed n :=
  (universeSet_closed h seed n).separation_mem
    ((universeSet_closed h seed n).singleton_mem
      ((universeSet_closed h seed n).empty_mem (seed_mem_level h seed n))) _

noncomputable def proofCode (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (n : Nat) (P : Prop) : Code h seed n := ⟨truthCode P, truthCode_mem h seed n P⟩

/-- The domain may be any actual set, not just a code at the bottom level.
Smallness follows from literal equality with the canonical proof code. -/
theorem arbitrary_domain_proof_product_small (h : CofinalInaccessibles.{u})
    (seed a : ZFSet.{u}) (P : Elements a → Prop) :
    tracePiSet a (ZFSetContextualInterpretation.totalFamily a (fun x => truthCode (P x))) ∈
      universeSet h seed 0 := by
  rw [ZFSetTraceProofDecoding.trace_forall_code]
  exact truthCode_mem h seed 0 _

theorem proofCode_forall_decoder {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {i : Nat} (a : Γ → Code h seed i)
    (P : (Σ γ : Γ, El (a γ)) → Prop) :
    (hierarchy h seed).el (level := 0) (fun γ => proofCode h seed 0 (∀ x : El (a γ), P ⟨γ, x⟩)) =
      ZFSetTraceContextual.piFamily ((hierarchy h seed).el a) (truthFamily P) :=
  ZFSetTraceProofDecoding.forall_decoder _ _

/-! ## A declared index seed supports lists at every level -/

theorem indices_mem_level (h : CofinalInaccessibles.{u}) (parameter : ZFSet.{u}) (n : Nat) :
    ZFSetIndexedClosure.finiteRankIndex ∈ universeSet h (ZFSetIndexedClosure.seed parameter) n :=
  universeSet_mono h _ (Nat.zero_le n) (ZFSetIndexedClosure.seed_contains_indices h parameter)

noncomputable def listCode {h : CofinalInaccessibles.{u}} {parameter : ZFSet.{u}} {n : Nat}
    (a : Code h (ZFSetIndexedClosure.seed parameter) n) :
    Code h (ZFSetIndexedClosure.seed parameter) n :=
  ⟨ZFSetList.listCode a.1, ZFSetListClosure.listCode_mem
    (universeSet_closed h _ n) a.2 (indices_mem_level h parameter n)⟩

theorem listCode_lift {h : CofinalInaccessibles.{u}} {parameter : ZFSet.{u}} {n m : Nat}
    (below : n ≤ m) (a : Code h (ZFSetIndexedClosure.seed parameter) n) :
    listCode (liftCode below a) = liftCode below (listCode a) := rfl

noncomputable def decodeList {h : CofinalInaccessibles.{u}} {parameter : ZFSet.{u}} {n : Nat}
    (a : Code h (ZFSetIndexedClosure.seed parameter) n) :
    El (listCode a) ≃ List (El a) := ZFSetList.listEquiv a.1

#print axioms piCode
#print axioms productsClosed
#print axioms el_piCodeMax
#print axioms piCodeMax_substitution
#print axioms piCodeAt_lift
#print axioms arbitrary_domain_proof_product_small
#print axioms proofCode_forall_decoder
#print axioms listCode
#print axioms listCode_lift
#print axioms decodeList

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation
