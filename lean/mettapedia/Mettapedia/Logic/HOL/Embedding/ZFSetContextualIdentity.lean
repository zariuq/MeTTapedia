import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Contextual identity with actual set-coded proof fibres

Equality of two sections is represented by the canonical subterminal set
`truthCode (left = right)`.  Reflexivity is the empty set, the unique member
of every inhabited identity fibre.  Full dependent elimination is defined by
recovering endpoint equality from that membership witness and transporting an
arbitrary set-valued motive.

This is an extensional set model of identity.  It does not assert that every
native identity proof is definitionally equal, erase retained native paths, or
identify object equality with kernel conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetContextualIdentity

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension codedCwf)
open ZFSetTraceProofDecoding (truthCode mem_truthCode truthCode_subset)

universe u

noncomputable def identityFamily {Γ : Type (u + 1)} (a : SetFamily Γ)
    (left right : Section a) : SetFamily Γ :=
  fun γ => truthCode (left γ = right γ)

noncomputable def formation : IdentityFormationOperations codedCwf.{u} where
  idTy := identityFamily

theorem formation_substitution : StrictIdentityFormationSubstitution formation.{u} := by
  intro source target substitution type left right
  rfl

noncomputable def reflexivity : IdentityReflexivityOperations formation.{u} where
  refl _term _γ := ⟨∅, (mem_truthCode _ ∅).mpr ⟨rfl, rfl⟩⟩

theorem reflexivity_substitution : StrictReflexivitySubstitution reflexivity.{u} := by
  intro source target substitution type term
  exact HEq.rfl

noncomputable def reflexivitySubstitution {Γ : Type (u + 1)} (a : SetFamily Γ) :
    codedCwf.Sub (Extension a) (formation.identityContext a) :=
  fun point =>
    ⟨⟨⟨point.1, point.2⟩, point.2⟩,
      ⟨∅, (mem_truthCode _ ∅).mpr ⟨rfl, rfl⟩⟩⟩

private theorem witness_eq_refl {P : Prop} (witness : Elements (truthCode.{u} P))
    (proof : P) : witness = ⟨∅, (mem_truthCode P ∅).mpr ⟨rfl, proof⟩⟩ := by
  apply Subtype.ext
  exact (mem_truthCode P witness.1).mp witness.2 |>.1

noncomputable def elimination : IdentityEliminationOperations formation.{u} where
  reflexivitySubstitution := reflexivitySubstitution
  j motive base := by
    intro point
    rcases point with ⟨⟨⟨γ, left⟩, right⟩, witness⟩
    have endpointEquality : left = right :=
      ((mem_truthCode (left = right) witness.1).mp witness.2).2
    cases endpointEquality
    have witnessEquality :
        witness = ⟨∅, (mem_truthCode (left = left) ∅).mpr ⟨rfl, rfl⟩⟩ :=
      witness_eq_refl witness rfl
    cases witnessEquality
    exact base ⟨γ, left⟩

noncomputable def reindexing : IdentityReindexing formation.{u} where
  map substitution _type point :=
    ⟨⟨⟨substitution point.1.1.1, point.1.1.2⟩, point.1.2⟩, point.2⟩

noncomputable def identity : IdentityOperations codedCwf.{u} where
  formation := formation
  reflexivity := reflexivity
  elimination := elimination
  reindexing := reindexing

noncomputable def products : PiOperations codedCwf.{u} :=
  PiOperations.ofQualified ZFSetTraceContextual.products

noncomputable def sums : SigmaOperations codedCwf.{u} :=
  SigmaOperations.ofQualified ZFSetContextualInterpretation.sums

noncomputable def operations : Operations codedCwf.{u} where
  products := products
  sums := sums
  identity := identity

theorem products_substitution : StrictPiSubstitution products.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution domain codomain
    rfl
  · intro source target substitution domain codomain body
    exact HEq.rfl
  · intro source target substitution domain codomain function argument reindexedFunction same
    have equal : codedCwf.tmSub function substitution = reindexedFunction := eq_of_heq same
    cases equal
    exact HEq.rfl

theorem sums_substitution : StrictSigmaSubstitution sums.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution domain codomain
    rfl
  · intro source target substitution domain codomain first second reindexedSecond same
    have equal : codedCwf.tmSub second substitution = reindexedSecond := eq_of_heq same
    cases equal
    exact HEq.rfl
  · intro source target substitution domain codomain value reindexedValue same
    have equal : codedCwf.tmSub value substitution = reindexedValue := eq_of_heq same
    cases equal
    exact ⟨HEq.rfl, HEq.rfl⟩

theorem boundary : IdentityBoundary reflexivity.{u} elimination := by
  constructor
  · intro context type
    rfl
  · intro context type
    exact HEq.rfl

theorem beta : IdentityBeta elimination.{u} := by
  intro context type motive base
  rfl

theorem reindexing_laws : StrictIdentityReindexing elimination.{u} reindexing := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution type
    rfl
  · intro source target substitution type
    exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩
  · intro source target substitution type
    rfl

theorem j_substitution : StrictJSubstitution elimination.{u} reindexing := by
  intro source target substitution type motive base reindexedBase same
  have baseEquality : codedCwf.tmSub base
      (TypeOver.extensionSubstitution substitution type) = reindexedBase :=
    eq_of_heq same
  cases baseEquality
  apply heq_of_eq
  funext point
  rcases point with ⟨⟨⟨γ, left⟩, right⟩, witness⟩
  have endpointEquality : left = right :=
    ((mem_truthCode (left = right) witness.1).mp witness.2).2
  cases endpointEquality
  have witnessEquality :
      witness = ⟨∅, (mem_truthCode (left = left) ∅).mpr ⟨rfl, rfl⟩⟩ :=
    witness_eq_refl witness rfl
  cases witnessEquality
  rfl

theorem beta_laws : BetaLaws operations.{u} :=
  ⟨PiOperations.ofQualified_beta ZFSetTraceContextual.products,
    SigmaOperations.ofQualified_beta ZFSetContextualInterpretation.sums,
    boundary, beta⟩

theorem substitution_laws : StrictSubstitutionLaws operations.{u} :=
  ⟨products_substitution, sums_substitution, formation_substitution,
    reflexivity_substitution, reindexing_laws, j_substitution⟩

/-- Identity fibres lie in every closed universe that contains the canonical
singleton proof code.  The statement makes the exact universe premise visible. -/
theorem identityFamily_mem_closed {U : ZFSet.{u}}
    (closed : ZFSetUniverseClosure.Closed U) (proofCodeMem : ({∅} : ZFSet.{u}) ∈ U)
    {Γ : Type (u + 1)} (a : SetFamily Γ) (left right : Section a) (γ : Γ) :
    identityFamily a left right γ ∈ U :=
  closed.subset_mem proofCodeMem (truthCode_subset _)

theorem proof_sections_unique {Γ : Type (u + 1)} (a : SetFamily Γ)
    (left right : Section a) (first second : Section (identityFamily a left right)) :
    first = second := by
  funext γ
  apply Subtype.ext
  exact ((mem_truthCode _ (first γ).1).mp (first γ).2).1.trans
    ((mem_truthCode _ (second γ).1).mp (second γ).2).1.symm

theorem inhabited_identity_reflects_endpoints {Γ : Type (u + 1)} (a : SetFamily Γ)
    (left right : Section a) (witness : Section (identityFamily a left right)) :
    left = right := by
  funext γ
  exact ((mem_truthCode _ (witness γ).1).mp (witness γ).2).2

/-! ## Concrete controls -/

def two : ZFSet.{u} := {∅, ZFSet.powerset ∅}

theorem empty_mem_two : (∅ : ZFSet.{u}) ∈ two := by simp [two]

theorem power_empty_mem_two : ZFSet.powerset (∅ : ZFSet.{u}) ∈ two := by simp [two]

def domain : SetFamily PUnit.{u + 2} := fun _ => two

def left : Section domain := fun _ => ⟨∅, empty_mem_two⟩

def rightSame : Section domain := left

def rightDifferent : Section domain :=
  fun _ => ⟨ZFSet.powerset ∅, power_empty_mem_two⟩

noncomputable def equalWitness : Section (identityFamily domain left rightSame) :=
  reflexivity.refl left

theorem unequal_fibre_empty :
    identityFamily domain left rightDifferent PUnit.unit = (∅ : ZFSet.{u}) := by
  have distinct : left PUnit.unit ≠ rightDifferent PUnit.unit := by
    intro equal
    have values := congrArg Subtype.val equal
    change (∅ : ZFSet.{u}) = ZFSet.powerset ∅ at values
    have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
      ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
    rw [← values] at member
    exact ZFSet.notMem_empty _ member
  apply ZFSet.ext
  intro x
  unfold identityFamily
  rw [mem_truthCode]
  constructor
  · rintro ⟨_, equal⟩
    exact (distinct equal).elim
  · intro impossible
    exact (ZFSet.notMem_empty _ impossible).elim

theorem unequal_has_no_section :
    ¬ Nonempty (Section (identityFamily domain left rightDifferent)) := by
  rintro ⟨witnessSection⟩
  have membershipEquality := congrArg
    (fun fibre => (witnessSection PUnit.unit).1 ∈ fibre)
    unequal_fibre_empty
  have impossible :=
    membershipEquality.mp (witnessSection PUnit.unit).2
  exact ZFSet.notMem_empty _ impossible

noncomputable def varyingMotive : SetFamily (formation.identityContext domain) :=
  fun point => truthCode (point.1.1.2 = point.1.2)

noncomputable def varyingBase : Section
    (codedCwf.tySub varyingMotive (elimination.reflexivitySubstitution domain)) :=
  fun _ => ⟨∅, (mem_truthCode _ ∅).mpr ⟨rfl, rfl⟩⟩

theorem varying_j_computes (point : Extension domain) :
    (elimination.j varyingMotive varyingBase
      (elimination.reflexivitySubstitution domain point)).1 = ∅ := by
  rfl

#print axioms formation_substitution
#print axioms reflexivity_substitution
#print axioms boundary
#print axioms beta
#print axioms reindexing_laws
#print axioms j_substitution
#print axioms beta_laws
#print axioms substitution_laws
#print axioms identityFamily_mem_closed
#print axioms proof_sections_unique
#print axioms inhabited_identity_reflects_endpoints
#print axioms unequal_fibre_empty
#print axioms unequal_has_no_section
#print axioms varying_j_computes

end Mettapedia.Logic.HOL.Embedding.ZFSetContextualIdentity
