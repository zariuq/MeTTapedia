import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetContextualUniverseInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
import Mettapedia.Logic.HOL.Embedding.ZFSetListClosure
import Mettapedia.TypeTheory.Models.SetCodedTypeOperations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetTypeExpressionInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.RussellTarskiBoundary

/-!
# Trace products, lists and type expressions in the internal universe tower

The constructed tower, its codes, cumulative inclusions and decoding are
reused unchanged. Trace product codes have proved closure at the maximum
level and strict contextual decoding. Canonical proof products remain small
even for large set domains, by the independently proved trace truth law.
A natural-index seed additionally closes every level under actual lists.
The scoped type-expression interpretation respects universe specialization.
These components do not yet establish full native syntax soundness.
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

/-- Decode a universe's actual trace product, retaining its declared domain. -/
noncomputable def decodePi {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) :
    El (piCode a b) ≃ ((x : El a) → El (b x)) :=
  (tracePiEquiv a.1 (fibres a b)).trans (Equiv.piCongrRight
    (fun x => Equiv.cast (congrArg Elements (fibres_at a b x))))

theorem decodePi_value {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j)
    (f : El (piCode a b)) (x : El a) :
    (decodePi a b f x).1 = traceApp f.1 x.1 := by
  change ((Equiv.cast (congrArg Elements (fibres_at a b x)))
    (traceValue f x)).1 = _
  have cast_value {c d : ZFSet.{u}} (equal : c = d) (value : Elements c) :
      ((Equiv.cast (congrArg Elements equal)) value).1 = value.1 := by
    subst d
    rfl
  exact cast_value (fibres_at a b x) (traceValue f x)

/-- Closure at an explicit upper level; lifting changes no underlying set. -/
noncomputable def piCodeWithin {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {i k : Nat} (below : i ≤ k) (a : Code h seed i) (b : El a → Code h seed k) :
    Code h seed k :=
  liftCode (Nat.max_le.mpr ⟨below, Nat.le_refl k⟩) (piCode a b)

/-- A raw family and a coded family need only agree on their common domain
to determine the same product set. -/
theorem tracePiSet_eq_piCodeWithin {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {i k : Nat} (below : i ≤ k) (a : Code h seed i) (b : El a → Code h seed k)
    (body : ZFSet.{u} → ZFSet.{u}) (agrees : ∀ x : El a, body x.1 = (b x).1) :
    tracePiSet a.1 body = (piCodeWithin below a b).1 := by
  apply tracePiSet_congr
  intro x member
  exact (agrees ⟨x, member⟩).trans (fibres_at a b ⟨x, member⟩).symm

noncomputable def decodePiWithin {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {i k : Nat} (below : i ≤ k) (a : Code h seed i) (b : El a → Code h seed k) :
    El (piCodeWithin below a b) ≃ ((x : El a) → El (b x)) := decodePi a b

theorem traceApp_encodePiWithin {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {i k : Nat} (below : i ≤ k) (a : Code h seed i) (b : El a → Code h seed k)
    (body : (x : El a) → El (b x)) (x : El a) :
    traceApp ((decodePiWithin below a b).symm body).1 x.1 = (body x).1 := by
  exact (decodePi_value a b ((decodePi a b).symm body) x).symm.trans
    (congrArg (fun f => (f x).1) ((decodePi a b).apply_symm_apply body))

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

/-! ## Identity codes share the contextual model and its cumulative tower -/

noncomputable def identityCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (left right : (γ : Γ) → El (a γ)) : Γ → Code h seed n :=
  fun γ => proofCode h seed n (left γ = right γ)

theorem el_identityCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (left right : (γ : Γ) → El (a γ)) :
    (hierarchy h seed).el (identityCode a left right) =
      Mettapedia.TypeTheory.Models.SetCodedIdentity.formation.idTy
        ((hierarchy h seed).el a) left right := rfl

noncomputable def identitiesClosed (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (hierarchy h seed).IdClosed Mettapedia.TypeTheory.Models.SetCodedIdentity.formation where
  idCode := identityCode
  el_idCode := el_identityCode

theorem identityCode_substitution {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ Δ : Type (u + 1)} {n : Nat} (θ : Δ → Γ) (a : Γ → Code h seed n)
    (left right : (γ : Γ) → El (a γ)) :
    identityCode a left right ∘ θ =
      identityCode (a ∘ θ) (fun δ => left (θ δ)) (fun δ => right (θ δ)) := rfl

theorem identityCode_lift {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n m : Nat} (below : n ≤ m) (a : Γ → Code h seed n)
    (left right : (γ : Γ) → El (a γ)) :
    (fun γ => liftCode below (identityCode a left right γ)) =
      identityCode (fun γ => liftCode below (a γ)) left right := rfl

open ZFSetContextualInterpretation (SetFamily Section Extension)
open Mettapedia.TypeTheory.Models
open Mettapedia.TypeTheory.ContextualBasedIdentityOperations (basedContext witnessType)

noncomputable def identityWitnessCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (left : (γ : Γ) → El (a γ)) : Extension ((hierarchy h seed).el a) → Code h seed n :=
  identityCode (fun point => a point.1) (fun point => left point.1) (fun point => point.2)

/-- The residual two-argument type of based J is a code in the very same
universe as its domain and motive. Its inner domain is the actual identity
code, not a second representation of equality. -/
noncomputable def basedFunctionCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (left : (γ : Γ) → El (a γ))
    (motive : basedContext SetCodedTypeOperations.formation left → Code h seed n) :
    Γ → Code h seed n :=
  piCodeAt a (piCodeAt (identityWitnessCode a left) motive)

theorem el_basedFunctionCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (left : (γ : Γ) → El (a γ))
    (motive : basedContext SetCodedTypeOperations.formation left → Code h seed n) :
    (hierarchy h seed).el (basedFunctionCode a left motive) =
      ZFSetTraceContextual.piFamily ((hierarchy h seed).el a)
        (ZFSetTraceContextual.piFamily (witnessType SetCodedTypeOperations.formation left)
          ((hierarchy h seed).el motive)) := rfl

/-- The constructed J function inhabits the decoded code. Universe closure
and computation now refer to the same trace-coded value. -/
noncomputable def basedFunctionSection {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (left : (γ : Γ) → El (a γ))
    (motive : basedContext SetCodedTypeOperations.formation left → Code h seed n)
    (base : Section ((hierarchy h seed).el motive ∘
      SetCodedTypeOperations.Based.elimination.reflSection left)) :
    Section ((hierarchy h seed).el (basedFunctionCode a left motive)) :=
  SetCodedTypeOperations.Based.function left ((hierarchy h seed).el motive) base

theorem basedFunctionSection_beta {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n : Nat} (a : Γ → Code h seed n)
    (left : (γ : Γ) → El (a γ))
    (motive : basedContext SetCodedTypeOperations.formation left → Code h seed n)
    (base : Section ((hierarchy h seed).el motive ∘
      SetCodedTypeOperations.Based.elimination.reflSection left)) :
    ZFSetTraceContextual.app (a := SetCodedIdentity.identityFamily left left)
      (b := fun point => (motive ⟨⟨point.1, left point.1⟩, point.2⟩).1)
      (ZFSetTraceContextual.app (a := (hierarchy h seed).el a)
        (b := ZFSetTraceContextual.piFamily (witnessType SetCodedTypeOperations.formation left)
          ((hierarchy h seed).el motive))
        (basedFunctionSection a left motive base) left)
      (SetCodedIdentity.reflSection left) = base :=
  SetCodedTypeOperations.Based.function_beta left ((hierarchy h seed).el motive) base

theorem basedFunctionCode_lift {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}}
    {Γ : Type (u + 1)} {n m : Nat} (below : n ≤ m) (a : Γ → Code h seed n)
    (left : (γ : Γ) → El (a γ))
    (motive : basedContext SetCodedTypeOperations.formation left → Code h seed n) :
    (fun γ => liftCode below (basedFunctionCode a left motive γ)) =
      basedFunctionCode (fun γ => liftCode below (a γ)) left
        (fun point => liftCode below (motive point)) := rfl

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

/-! ## Universe heads and specialization of actual type expressions -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation ZFSetTypeExpressionInterpretation RussellTarski

noncomputable def interpretHead (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (valuation : Nat → Nat) : Tower.Head → ZFSet.{u}
  | .legacyGround => ground
  | .sort level => universeSet h seed (level.eval valuation)

theorem interpretHead_substLevels (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (valuation : Nat → Nat) (theta : Nat → LevelExpr) :
    interpretHead h seed ground valuation ∘ substLevelsHead theta =
      interpretHead h seed ground (fun index => (theta index).eval valuation) := by
  funext head
  cases head <;> simp only [Function.comp_apply, substLevelsHead, interpretHead, LevelExpr.eval_subst]

/-- Specializing the actual universe expressions before interpretation
agrees with composing their valuation. Declaration values remain fixed;
this is not a choice of polymorphic constant semantics. -/
theorem interpret_substLevels {n : Nat} (h : CofinalInaccessibles.{u})
    (seed ground : ZFSet.{u}) (valuation : Nat → Nat) (theta : Nat → LevelExpr)
    (constants : DeclName → ZFSet.{u}) (term : Tower.Tm n) (admitted : supported term = true)
    (environment : Environment.{u} n) :
    interpret (interpretHead h seed ground valuation) constants (substLevelsTm theta term)
      ((supported_mapHead (substLevelsHead theta) term).trans admitted) environment =
      interpret (interpretHead h seed ground (fun index => (theta index).eval valuation))
        constants term admitted environment := by
  simpa only [RussellTarski.substLevelsTm, interpretHead_substLevels] using
    (interpret_mapHead (substLevelsHead theta) (interpretHead h seed ground valuation)
      constants term admitted environment)

#print axioms piCode
#print axioms productsClosed
#print axioms el_piCodeMax
#print axioms piCodeMax_substitution
#print axioms piCodeAt_lift
#print axioms arbitrary_domain_proof_product_small
#print axioms proofCode_forall_decoder
#print axioms identitiesClosed
#print axioms el_identityCode
#print axioms identityCode_substitution
#print axioms identityCode_lift
#print axioms el_basedFunctionCode
#print axioms basedFunctionSection
#print axioms basedFunctionSection_beta
#print axioms basedFunctionCode_lift
#print axioms listCode
#print axioms listCode_lift
#print axioms decodeList
#print axioms tracePiSet_eq_piCodeWithin
#print axioms interpret_substLevels

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation
