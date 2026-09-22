import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
import Mettapedia.TypeTheory.UniverseLevel.Algebra
import Mettapedia.TypeTheory.TarskiUniverseEmbedding

/-!
# Internal set universes interpreting the native level algebra

The same least-universe operation constructs a Nat-indexed, strictly growing
tower of actual internal sets, starting from a supplied seed set. Codes are members of these sets, and decoding takes
their members. Cumulative lifts preserve the underlying set exactly; each
successor additionally codes its predecessor's code carrier.

Dependent product and sum codes are the actual graphs and Kuratowski pairs
of `ZFSetDependentProducts`. Their decoding is an equivalence, not literal
equality with Lean Pi/Sigma types. Native level expressions are interpreted
through their existing zero/successor/maximum and substitution semantics.
This is universe and type-former model content, not a full native DTT model.
-/

open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetDependentProducts
open Mettapedia.TypeTheory.TarskiUniverseCapabilities
open Mettapedia.TypeTheory.TarskiUniverseEmbedding
open Mettapedia.TypeTheory.UniverseClosureProfiles

universe u

noncomputable def universeSet (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => univOf h seed
  | n + 1 => univOf h (universeSet h seed n)

theorem seed_mem_zero (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    seed ∈ universeSet h seed 0 := mem_univOf h seed

theorem universeSet_closed (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    Closed (universeSet h seed n) := by
  cases n <;> exact univOf_closed h _

theorem universeSet_mem_next (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    universeSet h seed n ∈ universeSet h seed (n + 1) := mem_univOf h _

theorem universeSet_subset_next (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    universeSet h seed n ⊆ universeSet h seed (n + 1) :=
  (universeSet_closed h seed (n + 1)).transitive _ (universeSet_mem_next h seed n)

theorem universeSet_mono (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) {i j : Nat} (below : i ≤ j) :
    universeSet h seed i ⊆ universeSet h seed j := by
  induction below with
  | refl => exact fun _ hx => hx
  | @step j _ ih =>
      exact fun _ hx => universeSet_subset_next h seed j (ih hx)

theorem seed_mem_level (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    seed ∈ universeSet h seed n :=
  universeSet_mono h seed (Nat.zero_le n) (seed_mem_zero h seed)

theorem universeSet_seed_mono (h : CofinalInaccessibles.{u})
    {small large : ZFSet.{u}} (below : small ⊆ large) (n : Nat) :
    universeSet h small n ⊆ universeSet h large n := by
  induction n with
  | zero => exact univOf_mono h below
  | succ n ih => exact univOf_mono h ih

abbrev Code (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) := Elements (universeSet h seed n)

abbrev El {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {n : Nat} (code : Code h seed n) := Elements code.1

noncomputable def family (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) : TarskiCodeFamily.{0, u + 1, u + 1} where
  Level := Nat
  Code := Code h seed
  El _ := El

def liftCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (below : i ≤ j) (code : Code h seed i) : Code h seed j :=
  ⟨code.1, universeSet_mono h seed below code.2⟩

theorem liftCode_refl {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i : Nat} (code : Code h seed i) :
    liftCode (Nat.le_refl i) code = code := rfl

theorem liftCode_trans {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j k : Nat}
    (first : i ≤ j) (second : j ≤ k) (code : Code h seed i) :
    liftCode (first.trans second) code = liftCode second (liftCode first code) := rfl

theorem decode_liftCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (below : i ≤ j) (code : Code h seed i) : El (liftCode below code) = El code := rfl

noncomputable def cumulative (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    (family h seed).Cumulative Nat.le where
  lift := liftCode
  decodeLift _ code := Equiv.refl (El code)

noncomputable def universeCode (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) : Code h seed (n + 1) :=
  ⟨universeSet h seed n, universeSet_mem_next h seed n⟩

theorem decode_universeCode (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    El (universeCode h seed n) = Code h seed n := rfl

noncomputable def successorEmbedding (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    UniverseEmbedding (universeAt (family h seed) (n + 1)) (universeAt (family h seed) n) where
  codeCarrier := universeCode h seed n
  decodeCodeCarrier := Equiv.refl _
  decodedType := liftCode (Nat.le_succ n)
  decodeDecodedType _ := Equiv.refl _

/-! ## Dependent products and sums at the maximum level -/

noncomputable def fibres {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ a.1 then (b ⟨x, hx⟩).1 else ∅

theorem fibres_at {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) (x : El a) :
    fibres a b x.1 = (b x).1 := by
  simp only [fibres, dif_pos x.2]

noncomputable def piCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) : Code h seed (max i j) :=
  ⟨piSet a.1 (fibres a b), (universeSet_closed h seed _).piSet_mem
    (universeSet_mono h seed (Nat.le_max_left i j) a.2) _ (fun x hx => by
      rw [fibres_at a b ⟨x, hx⟩]
      exact universeSet_mono h seed (Nat.le_max_right i j) (b ⟨x, hx⟩).2)⟩

noncomputable def sigmaCode {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) : Code h seed (max i j) :=
  ⟨sigmaSet a.1 (fibres a b), (universeSet_closed h seed _).sigmaSet_mem
    (universeSet_mono h seed (Nat.le_max_left i j) a.2) _ (fun x hx => by
      rw [fibres_at a b ⟨x, hx⟩]
      exact universeSet_mono h seed (Nat.le_max_right i j) (b ⟨x, hx⟩).2)⟩

noncomputable def decodePi {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) : El (piCode a b) ≃ ((x : El a) → El (b x)) :=
  (piEquiv a.1 (fibres a b)).trans (Equiv.piCongrRight
    (fun x => Equiv.cast (congrArg Elements (fibres_at a b x))))

noncomputable def decodeSigma {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}
    (a : Code h seed i) (b : El a → Code h seed j) : El (sigmaCode a b) ≃ (Σ x : El a, El (b x)) :=
  (sigmaEquiv a.1 (fibres a b)).trans (Equiv.sigmaCongrRight
    (fun x => Equiv.cast (congrArg Elements (fibres_at a b x))))

theorem piClosed (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) : (family h seed).PiClosed := by
  intro n a b
  let code : Code h seed n := ⟨(piCode a b).1, by
    have hc := (piCode a b).2
    exact universeSet_mono h seed (Nat.max_le.mpr ⟨Nat.le_refl n, Nat.le_refl n⟩) hc⟩
  exact ⟨code, ⟨decodePi a b⟩⟩

theorem sigmaClosed (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) : (family h seed).SigmaClosed := by
  intro n a b
  let code : Code h seed n := ⟨(sigmaCode a b).1, by
    have hc := (sigmaCode a b).2
    exact universeSet_mono h seed (Nat.max_le.mpr ⟨Nat.le_refl n, Nat.le_refl n⟩) hc⟩
  exact ⟨code, ⟨decodeSigma a b⟩⟩

/-- Cumulative lifts change only universe-membership proofs. They do not
re-encode the dependent function graphs. -/
theorem piCode_lift_underlying {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j i' j' : Nat}
    (hi : i ≤ i') (hj : j ≤ j') (a : Code h seed i) (b : El a → Code h seed j) :
    (piCode (liftCode hi a) (fun x => liftCode hj (b x))).1 = (piCode a b).1 := rfl

theorem sigmaCode_lift_underlying {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j i' j' : Nat}
    (hi : i ≤ i') (hj : j ≤ j') (a : Code h seed i) (b : El a → Code h seed j) :
    (sigmaCode (liftCode hi a) (fun x => liftCode hj (b x))).1 = (sigmaCode a b).1 := rfl

/-- Semantic context substitution is pullback. No environment-dependent
re-encoding is inserted by either dependent type former. -/
theorem piCode_context_substitution {h : CofinalInaccessibles.{u}}
    {seed : ZFSet.{u}} {i j : Nat} {Γ Δ : Type*} (θ : Δ → Γ)
    (a : Γ → Code h seed i) (b : (γ : Γ) → El (a γ) → Code h seed j) :
    (fun γ => piCode (a γ) (b γ)) ∘ θ =
      (fun δ => piCode (a (θ δ)) (b (θ δ))) := rfl

theorem sigmaCode_context_substitution {h : CofinalInaccessibles.{u}}
    {seed : ZFSet.{u}} {i j : Nat} {Γ Δ : Type*} (θ : Δ → Γ)
    (a : Γ → Code h seed i) (b : (γ : Γ) → El (a γ) → Code h seed j) :
    (fun γ => sigmaCode (a γ) (b γ)) ∘ θ =
      (fun δ => sigmaCode (a (θ δ)) (b (θ δ))) := rfl

/-! ## The existing native level algebra -/

noncomputable def interpretLevel (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → Nat) (level : LevelExpr) : ZFSet.{u} :=
  universeSet h seed (level.eval valuation)

theorem interpretLevel_zero (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (valuation : Nat → Nat) :
    interpretLevel h seed valuation (.const 0) = univOf h seed := rfl

theorem interpretLevel_successor (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → Nat) (level : LevelExpr) :
    interpretLevel h seed valuation level ∈ interpretLevel h seed valuation (.succ level) :=
  universeSet_mem_next h seed _

theorem interpretLevel_max_left (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → Nat) (left right : LevelExpr) :
    interpretLevel h seed valuation left ⊆ interpretLevel h seed valuation (.max left right) :=
  universeSet_mono h seed (Nat.le_max_left _ _)

theorem interpretLevel_max_right (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → Nat) (left right : LevelExpr) :
    interpretLevel h seed valuation right ⊆ interpretLevel h seed valuation (.max left right) :=
  universeSet_mono h seed (Nat.le_max_right _ _)

theorem interpretLevel_substitution (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → Nat) (θ : Nat → LevelExpr) (level : LevelExpr) :
    interpretLevel h seed valuation (level.subst θ) =
      interpretLevel h seed (fun n => (θ n).eval valuation) level := by
  unfold interpretLevel
  rw [LevelExpr.eval_subst]

theorem interpretedCode_substitution (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (valuation : Nat → Nat) (θ : Nat → LevelExpr) (level : LevelExpr) :
    Code h seed ((level.subst θ).eval valuation) =
      Code h seed (level.eval (fun n => (θ n).eval valuation)) := by
  rw [LevelExpr.eval_subst]

theorem universeSet_no_self_membership (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    universeSet h seed n ∉ universeSet h seed n := ZFSet.mem_irrefl _

theorem successor_not_equal (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (n : Nat) :
    universeSet h seed (n + 1) ≠ universeSet h seed n :=
  univOf_ne_self h _

/-! ## A nonconstant family already present over the empty seed

This control concerns finite set codes only; it does not claim that any
specific native inductive datatype has been interpreted.
-/

namespace Controls

noncomputable def emptyCode (h : CofinalInaccessibles.{u}) : Code h ∅ 0 :=
  ⟨∅, seed_mem_zero h ∅⟩

noncomputable def twoCode (h : CofinalInaccessibles.{u}) : Code h ∅ 0 :=
  ⟨ZFSetDependentProducts.Controls.two,
    (universeSet_closed h ∅ 0).power_mem
      ((universeSet_closed h ∅ 0).power_mem (emptyCode h).2)⟩

noncomputable def varyingCodes (h : CofinalInaccessibles.{u})
    (x : El (twoCode h)) : Code h ∅ 0 := by
  classical
  refine ⟨ZFSetDependentProducts.Controls.varying x.1, ?_⟩
  unfold ZFSetDependentProducts.Controls.varying
  split
  · exact (universeSet_closed h ∅ 0).singleton_mem (emptyCode h).2
  · exact (twoCode h).2

theorem varying_pi_underlying (h : CofinalInaccessibles.{u}) :
    (piCode (twoCode h) (varyingCodes h)).1 =
      piSet ZFSetDependentProducts.Controls.two ZFSetDependentProducts.Controls.varying := by
  change piSet ZFSetDependentProducts.Controls.two (fibres (twoCode h) (varyingCodes h)) = _
  apply piSet_congr
  intro x hx
  exact fibres_at (twoCode h) (varyingCodes h) ⟨x, hx⟩

theorem varying_pi_inhabited (h : CofinalInaccessibles.{u}) :
    Nonempty (El (piCode (twoCode h) (varyingCodes h))) := by
  let witness := ZFSetDependentProducts.Controls.varyingFunction.{u}
  refine ⟨⟨witness.1, ?_⟩⟩
  rw [varying_pi_underlying]
  exact witness.2

theorem varying_fibres_not_equal (h : CofinalInaccessibles.{u}) :
    (varyingCodes h ⟨∅, ZFSetDependentProducts.Controls.empty_mem_two⟩).1 ≠
      (varyingCodes h ⟨ZFSet.powerset ∅,
        ZFSetDependentProducts.Controls.power_empty_mem_two⟩).1 :=
  ZFSetDependentProducts.Controls.varying_fibres_distinct

theorem empty_code_not_inhabited (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (El (emptyCode h)) := by
  rintro ⟨⟨x, impossible⟩⟩
  exact ZFSet.notMem_empty x impossible

end Controls

#print axioms universeSet_closed
#print axioms seed_mem_level
#print axioms universeSet_seed_mono
#print axioms universeSet_mono
#print axioms cumulative
#print axioms successorEmbedding
#print axioms piCode
#print axioms sigmaCode
#print axioms decodePi
#print axioms decodeSigma
#print axioms piClosed
#print axioms sigmaClosed
#print axioms piCode_lift_underlying
#print axioms piCode_context_substitution
#print axioms interpretLevel_substitution
#print axioms successor_not_equal
#print axioms Controls.varying_pi_inhabited
#print axioms Controls.varying_fibres_not_equal
#print axioms Controls.empty_code_not_inhabited

end Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
