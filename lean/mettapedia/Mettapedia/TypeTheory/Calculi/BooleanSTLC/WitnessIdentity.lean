import Mettapedia.Logic.TheoryModel.IdentityCarve
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.ProofRelevance
import Mettapedia.TypeTheory.OneToOneCorrespondence
import Mettapedia.TypeTheory.UnivalentUniverseTransport

/-!
# Identifications as witnesses: the carved part and the universe

Higher observational type theory keeps the recursion of observational equality
on type formers but lets identifications be structured witnesses rather than a
relation, and takes the identity of types to be one-to-one correspondence
(Altenkirch, Kaposi and Shulman, TYPES 2022).  This module takes the first step
on the boolean calculus.

**Witnesses at the types of the calculus.**  `ObsId A t u` is a type of
witnesses, by recursion on `A`: an equation of booleans, an equivalence of the
proof types of two propositions, a pair of witnesses, a family of witnesses
indexed by arguments.  Witnesses form a groupoid (`obsIdStructure`), exist
exactly when the terms are observationally equal (`ObsId.ofObsEq`,
`ObsId.toObsEq`), and are unique (`ObsId.subsingleton`): the groupoid lies in
the h-set fragment (`obsIdStructure_mem_hsetFragment`).  Uniqueness at `prop`
comes from the irrelevance of proofs.

**The universe.**  Coding the types of the calculus in a universe whose
elements decode to their observational types, `ObsType A` (closed terms up to
observational equality), and taking equivalences as identifications of types,
gives a groupoid (`universeIdStructure`) that satisfies the groupoid laws but
not UIP: the identity and negation are two distinct identifications of `bool`
with itself (`boolNot_ne_refl`), and transport along negation sends `tt` to
`ff` (`transport_boolNot_tt`).  So the universe lies outside the h-set fragment
(`universeIdStructure_not_mem_hsetFragment`), which is exactly the carved part
where UIP holds.  In the path layer of this universe, univalence holds by
construction (`obsType_univalent`) and route UIP fails (`not_routeUIP_obsType`).

Identifications of types as one-to-one correspondences, the clause of higher
observational type theory, determine and are determined by these equivalences
(`OneToOne.toEquiv_ofEquiv`, `OneToOne.relEquivGraph`); negation gives a
correspondence of `bool` with itself distinct from the identity
(`boolNotCorrespondence_ne_refl`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.BooleanSTLC

open Mettapedia.Logic.TheoryModel
open Mettapedia.Logic.TheoryModel.IdentityProofs
open Mettapedia.TypeTheory

/-! ## Witnesses at the types of the calculus -/

/-- **Witness-carrying observational equality**, by recursion on the type. -/
def ObsId : (A : Ty) → Closed A → Closed A → Type
  | .bool, t, u => PLift (t.value = u.value)
  | .prop, t, u => (t.propCode Env.empty).Proof ≃ (u.propCode Env.empty).Proof
  | .prod A B, t, u => ObsId A (.fst t) (.fst u) × ObsId B (.snd t) (.snd u)
  | .arr A B, t, u => (a : Closed A) → ObsId B (.app t a) (.app u a)

def ObsId.refl : (A : Ty) → (t : Closed A) → ObsId A t t
  | .bool, _ => ⟨rfl⟩
  | .prop, _ => Equiv.refl _
  | .prod A B, t => (ObsId.refl A (.fst t), ObsId.refl B (.snd t))
  | .arr _ B, t => fun a => ObsId.refl B (.app t a)

def ObsId.symm : {A : Ty} → {t u : Closed A} → ObsId A t u → ObsId A u t
  | .bool, _, _, ⟨equal⟩ => ⟨equal.symm⟩
  | .prop, _, _, e => Equiv.symm e
  | .prod _ _, _, _, (first, second) => (ObsId.symm first, ObsId.symm second)
  | .arr _ _, _, _, family => fun a => ObsId.symm (family a)

def ObsId.trans : {A : Ty} → {t u v : Closed A} → ObsId A t u → ObsId A u v → ObsId A t v
  | .bool, _, _, _, ⟨equal⟩, ⟨equal'⟩ => ⟨equal.trans equal'⟩
  | .prop, _, _, _, e, e' => Equiv.trans e e'
  | .prod _ _, _, _, _, (first, second), (first', second') =>
      (ObsId.trans first first', ObsId.trans second second')
  | .arr _ _, _, _, _, family, family' => fun a => ObsId.trans (family a) (family' a)

/-- Observational equality yields a witness. -/
def ObsId.ofObsEq : {A : Ty} → {t u : Closed A} → ObsEq A t u → ObsId A t u
  | .bool, _, _, related => ⟨related⟩
  | .prop, t, u, related =>
      PropCode.proofEquivOfMaps (t.propCode_inFragment _) (u.propCode_inFragment _)
        (fun proof => (u.propBridge _).prove (related.mp ((t.propBridge _).sound proof)))
        (fun proof => (t.propBridge _).prove (related.mpr ((u.propBridge _).sound proof)))
  | .prod _ _, _, _, related => (ObsId.ofObsEq related.1, ObsId.ofObsEq related.2)
  | .arr _ _, _, _, related => fun a => ObsId.ofObsEq (related a)

/-- A witness yields observational equality. -/
theorem ObsId.toObsEq : {A : Ty} → {t u : Closed A} → ObsId A t u → ObsEq A t u
  | .bool, _, _, ⟨equal⟩ => equal
  | .prop, t, u, e => (obsEq_prop_iff_proofEquiv t u).mpr ⟨e⟩
  | .prod _ _, _, _, (first, second) => ⟨ObsId.toObsEq first, ObsId.toObsEq second⟩
  | .arr _ _, _, _, family => fun a => ObsId.toObsEq (family a)

/-- **Witnesses exist exactly for observationally equal terms.** -/
theorem nonempty_obsId_iff {A : Ty} (t u : Closed A) : Nonempty (ObsId A t u) ↔ ObsEq A t u :=
  ⟨fun ⟨witness⟩ => witness.toObsEq, fun related => ⟨ObsId.ofObsEq related⟩⟩

/-- **Witnesses at the types of the calculus are unique.** -/
theorem ObsId.subsingleton : ∀ (A : Ty) (t u : Closed A), Subsingleton (ObsId A t u)
  | .bool, _, _ => ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩
  | .prop, _, u => by
      have := PropCode.proof_subsingleton (u.propCode_inFragment Env.empty)
      exact ⟨fun e f => Equiv.ext fun _ => Subsingleton.elim _ _⟩
  | .prod A B, _, _ =>
      ⟨fun first second => Prod.ext ((ObsId.subsingleton A _ _).elim _ _)
        ((ObsId.subsingleton B _ _).elim _ _)⟩
  | .arr _ B, _, _ => ⟨fun family family' => funext fun a => (ObsId.subsingleton B _ _).elim _ _⟩

/-- The witnesses of the calculus as an identity structure. -/
def obsIdStructure (A : Ty) : IdStructure.{0} where
  Pt := Closed A
  Pf := ObsId A
  refl := ObsId.refl A
  inv := ObsId.symm
  comp := ObsId.trans

theorem obsIdStructure_sat_uip (A : Ty) : (obsIdStructure A).Sat .uip :=
  fun p q => (ObsId.subsingleton A _ _).elim p q

/-- **The witnesses at the types of the calculus lie in the h-set fragment**: they
form a groupoid, and UIP holds. -/
theorem obsIdStructure_mem_hsetFragment (A : Ty) : obsIdStructure A ∈ hsetFragment := by
  have uip : (obsIdStructure A).Sat .uip := obsIdStructure_sat_uip A
  refine mem_hsetFragment_iff.mpr ?_
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact uip
  · exact fun _ _ _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _
  · exact fun _ => uip _ _

/-! ## The universe of observational types -/

/-- The observational type of a code: closed terms up to observational
equality. -/
def ObsType (A : Ty) : Type :=
  Quotient (obsEqSetoid A)

/-- The class of a closed term in its observational type. -/
def ObsType.mk {A : Ty} (t : Closed A) : ObsType A :=
  Quotient.mk (obsEqSetoid A) t

theorem ObsType.mk_eq_mk {A : Ty} {t u : Closed A} : ObsType.mk t = ObsType.mk u ↔ ObsEq A t u :=
  ⟨Quotient.exact, fun related => Quotient.sound related⟩

/-- Identity of types as equivalence of their observational types. -/
def universeIdStructure : IdStructure.{0} where
  Pt := Ty
  Pf A B := ObsType A ≃ ObsType B
  refl A := Equiv.refl (ObsType A)
  inv e := e.symm
  comp e f := e.trans f

/-- The identifications of types satisfy the groupoid laws. -/
theorem universeIdStructure_mem_groupoidUniverse : universeIdStructure ∈ groupoidUniverse :=
  mem_models_groupoidLaws (fun _ _ _ => Equiv.ext fun _ => rfl)
    (fun _ => Equiv.ext fun _ => rfl) (fun _ => Equiv.ext fun _ => rfl)
    (fun e => Equiv.ext e.right_inv) (fun e => Equiv.ext e.left_inv)

/-- Negation on the observational booleans. -/
def ObsType.boolNot : ObsType .bool ≃ ObsType .bool where
  toFun := Quotient.map (fun t => .app Examples.notBool t)
    (fun _ _ related => ObsEq.app_right Examples.notBool related)
  invFun := Quotient.map (fun t => .app Examples.notBool t)
    (fun _ _ related => ObsEq.app_right Examples.notBool related)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h t =>
        apply Quotient.sound
        show cond (cond t.value false true) false true = t.value
        generalize t.value = b
        cases b <;> rfl
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h t =>
        apply Quotient.sound
        show cond (cond t.value false true) false true = t.value
        generalize t.value = b
        cases b <;> rfl

/-- **Transport along negation computes**: it sends `tt` to `ff`. -/
theorem transport_boolNot_tt : ObsType.boolNot (ObsType.mk .tt) = ObsType.mk .ff :=
  ObsType.mk_eq_mk.mpr rfl

theorem obsType_tt_ne_ff : ObsType.mk (Tm.tt : Closed .bool) ≠ ObsType.mk .ff := fun equal =>
  Bool.noConfusion (ObsType.mk_eq_mk.mp equal : (true : Bool) = false)

/-- **Two distinct identifications of `bool` with itself.** -/
theorem boolNot_ne_refl : ObsType.boolNot ≠ Equiv.refl (ObsType .bool) := fun equal =>
  obsType_tt_ne_ff (by
    have := congrArg (fun e : ObsType .bool ≃ ObsType .bool => e (ObsType.mk .tt)) equal
    simp only [Equiv.refl_apply] at this
    rw [← this, transport_boolNot_tt])

/-- **UIP fails for the identity of types.** -/
theorem universeIdStructure_not_uip : ¬ universeIdStructure.Sat .uip := fun uip =>
  boolNot_ne_refl (@uip Ty.bool Ty.bool ObsType.boolNot (Equiv.refl _))

/-- The universe of observational types lies outside the h-set fragment. -/
theorem universeIdStructure_not_mem_hsetFragment : universeIdStructure ∉ hsetFragment :=
  fun member => universeIdStructure_not_uip (hsetFragment_subset_thin member)

open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.RouteTransportDiscriminator
open Mettapedia.TypeTheory.UnivalentUniverseTransport

/-- In the path layer of the universe of observational types, univalence holds
by construction. -/
theorem obsType_univalent : (decoding ObsType).Univalent :=
  decoding_univalent ObsType

/-- Route UIP fails in the universe of observational types. -/
theorem not_routeUIP_obsType : ¬ RouteUIP (pathLayer ObsType) := fun uip =>
  boolNot_ne_refl ((uip Ty.bool Ty.bool).elim _ _)

/-! ## Correspondences -/

/-- Negation as a one-to-one correspondence of `bool` with itself. -/
def boolNotCorrespondence : OneToOne (ObsType .bool) (ObsType .bool) :=
  OneToOne.ofEquiv ObsType.boolNot

/-- The correspondence of negation differs from the identity
correspondence. -/
theorem boolNotCorrespondence_ne_refl : boolNotCorrespondence ≠ OneToOne.refl _ := fun equal =>
  boolNot_ne_refl (by
    have := congrArg OneToOne.toEquiv equal
    rwa [boolNotCorrespondence, OneToOne.refl, OneToOne.toEquiv_ofEquiv,
      OneToOne.toEquiv_ofEquiv] at this)

/-! ## Plain and groupoid-valued stages -/

section Stages

open CategoryTheory

universe uC vC

/-- **The identity of types is not the identity of a plain presheaf stage**:
the stage identities of plain presheaves are thin. -/
theorem universeIdStructure_not_mem_presheafIdentities (C : Type uC) [Category.{vC} C] :
    universeIdStructure ∉ presheafIdentities C := by
  rintro ⟨X, c, equal⟩
  have thin : (presheafIdentity X c).Sat .uip := presheafIdentity_sat_uip X c
  rw [← equal] at thin
  exact universeIdStructure_not_uip thin

/-- The codes of the universe, as objects of the groupoid of identifications. -/
def UniverseCode : Type := Ty

/-- The groupoid of identifications of types. -/
instance universeGroupoid : Groupoid.{0} UniverseCode where
  Hom A B := ObsType A ≃ ObsType B
  id A := Equiv.refl (ObsType A)
  comp e f := e.trans f
  id_comp _ := Equiv.ext fun _ => rfl
  comp_id _ := Equiv.ext fun _ => rfl
  assoc _ _ _ := Equiv.ext fun _ => rfl
  inv e := e.symm
  inv_comp e := Equiv.ext e.right_inv
  comp_inv e := Equiv.ext e.left_inv

/-- **The identity of types is the identity of a groupoid-valued presheaf
stage**: the constant presheaf at the groupoid of identifications. -/
theorem universe_mem_groupoidPresheafIdentities (C : Type) [Category.{0} C] (c₀ : C) :
    ofGroupoid UniverseCode ∈ groupoidPresheafIdentities C :=
  groupoidValued_subset_groupoidPresheafIdentities C c₀ ⟨UniverseCode, universeGroupoid, rfl⟩

/-- That stage lies outside the h-set fragment. -/
theorem ofGroupoid_universe_not_mem_hsetFragment : ofGroupoid UniverseCode ∉ hsetFragment := by
  intro member
  have thin := (ofGroupoid_sat_uip_iff UniverseCode).mp (hsetFragment_subset_thin member)
  have := thin Ty.bool Ty.bool
  exact boolNot_ne_refl (Subsingleton.elim (α := ObsType .bool ≃ ObsType .bool) _ _)

end Stages

end Mettapedia.TypeTheory.Calculi.BooleanSTLC
