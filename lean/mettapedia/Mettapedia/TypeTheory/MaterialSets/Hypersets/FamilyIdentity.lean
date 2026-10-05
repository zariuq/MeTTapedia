import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyDescent
import Mettapedia.TypeTheory.ContextualIdentitySubstitution

/-!
# Identity and full dependent J in the material hyperset family model

An identity fibre is an actual separated singleton hyperset: it contains the
empty set exactly when its two endpoint members are equal. Three material
comprehensions carry the base, both endpoints and this witness. Their decoding
and reconstruction provide full dependent elimination, including motives which
depend on the endpoints and witness, and substitution coherence.

This is the extensional equality interpretation of identity. Its singleton
witnesses and endpoint reflection are properties of this model, not rules
imposed on an intensional syntax or on presentation occurrences. Non-well-founded
endpoint values are admitted. Context encoding takes an explicit presentation;
identity separation and witness decoding require no additional selection.
All contexts and families remain hypersets at level `u`, with member carriers
at `Type (u + 1)`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyIdentity

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.ContextualTypeOperations
open FamilyCwf

universe u uIndex uValue

/-- The actual material equality fibre, constructed by separation. -/
def identitySet {X : HSet.{u}} (left right : Elements X) : HSet.{u} :=
  HSet.sep (fun _ => left = right) {∅}

theorem mem_identitySet_iff {X : HSet.{u}} {left right : Elements X} {z : HSet.{u}} :
    z ∈ identitySet left right ↔ z = ∅ ∧ left = right :=
  HSet.mem_sep.trans (and_congr HSet.mem_singleton Iff.rfl)

theorem identityMember_value {X : HSet.{u}} {left right : Elements X}
    (witness : Elements (identitySet left right)) : witness.1 = ∅ :=
  (mem_identitySet_iff.mp witness.2).1

theorem identityDecode {X : HSet.{u}} {left right : Elements X}
    (witness : Elements (identitySet left right)) : left = right :=
  (mem_identitySet_iff.mp witness.2).2

def identityEncode {X : HSet.{u}} {left right : Elements X} (same : left = right) :
    Elements (identitySet left right) :=
  ⟨∅, mem_identitySet_iff.mpr ⟨rfl, same⟩⟩

theorem identityEncode_value {X : HSet.{u}} {left right : Elements X}
    (same : left = right) : (identityEncode same).1 = ∅ := rfl

/-- Explicit inverse laws connect actual material witnesses with equality. -/
def identityMemberEquiv {X : HSet.{u}} (left right : Elements X) :
    Elements (identitySet left right) ≃ ULift.{u + 1} (PLift (left = right)) where
  toFun witness := ⟨⟨identityDecode witness⟩⟩
  invFun same := identityEncode same.down.down
  left_inv witness := El.ext HSet.propositional (identityMember_value witness).symm
  right_inv _ := rfl

theorem identitySet_refl {X : HSet.{u}} (endpoint : Elements X) :
    identitySet endpoint endpoint = {∅} := by
  apply HSet.ext
  intro z
  exact mem_identitySet_iff.trans (and_iff_left rfl) |>.trans HSet.mem_singleton.symm

theorem identitySet_eq_empty {X : HSet.{u}} {left right : Elements X}
    (different : left ≠ right) : identitySet left right = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro z belongs
  exact different (mem_identitySet_iff.mp belongs).2

def identityFormation (p : HSet.Presentation.{u}) : IdentityFormation (hypersetCwf p) where
  idTy _ left right γ := identitySet (left γ) (right γ)
  idTy_sub _ _ _ _ := rfl

def identityReflexivity (p : HSet.Presentation.{u}) :
    IdentityReflexivity (hypersetCwf p) (identityFormation p) where
  refl term γ := identityEncode (rfl : term γ = term γ)
  refl_sub := by intros; rfl

/-- The second endpoint family over one actual material comprehension. -/
def secondFamily (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Family (extension p A) := A ∘ projection p A

/-- Encode two endpoints as an actual member of the second comprehension. -/
def endpointPair (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ)
    (point : Elements (extension p A)) (right : Elements (secondFamily p A point)) :
    Elements (extension p (secondFamily p A)) :=
  (extensionDecode p (secondFamily p A)).symm ⟨point, right⟩

theorem endpointPair_decode (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ)
    (point : Elements (extension p A)) (right : Elements (secondFamily p A point)) :
    extensionDecode p (secondFamily p A) (endpointPair p A point right) = ⟨point, right⟩ :=
  (extensionDecode p (secondFamily p A)).apply_symm_apply _

/-- Identity witnesses over both material endpoint members. -/
def witnessFamily (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Family (extension p (secondFamily p A)) := fun point =>
  identitySet (lastVariable p A (projection p (secondFamily p A) point))
    (lastVariable p (secondFamily p A) point)

theorem witnessFamily_eq_generic (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    witnessFamily p A = identityWitnessType (hypersetCwf p) (identityFormation p) A := rfl

/-- Decoding an encoded pair identifies its endpoint-equality predicate. -/
theorem endpointPair_equal_iff (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ)
    (point : Elements (extension p A)) (right : Elements (secondFamily p A point)) :
    (lastVariable p A (projection p (secondFamily p A) (endpointPair p A point right)) =
      lastVariable p (secondFamily p A) (endpointPair p A point right)) ↔
    lastVariable p A point = right := by
  have same := congrArg (fun q : Σ' q : Elements (extension p A),
      Elements (secondFamily p A q) => lastVariable p A q.1 = q.2)
    (endpointPair_decode p A point right)
  exact iff_of_eq same

/-- The reflexivity substitution is a third material ordered-pair encoding. -/
def reflexivitySubstitution (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Substitution (extension p A) (extension p (witnessFamily p A)) := fun point =>
  (extensionDecode p (witnessFamily p A)).symm
    ⟨endpointPair p A point (lastVariable p A point), identityEncode
      ((endpointPair_equal_iff p A point (lastVariable p A point)).mpr rfl)⟩

def readEndpoint (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Substitution (extension p (witnessFamily p A)) (extension p A) :=
  projection p (secondFamily p A) ∘ projection p (witnessFamily p A)

theorem readEndpoint_reflexivity (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    readEndpoint p A ∘ reflexivitySubstitution p A = id := by
  funext point
  have outer := congrArg PSigma.fst ((extensionDecode p (witnessFamily p A)).apply_symm_apply
    ⟨endpointPair p A point (lastVariable p A point), identityEncode
      ((endpointPair_equal_iff p A point (lastVariable p A point)).mpr rfl)⟩)
  change projection p (secondFamily p A)
    (projection p (witnessFamily p A) (reflexivitySubstitution p A point)) = point
  rw [show projection p (witnessFamily p A) (reflexivitySubstitution p A point) =
      endpointPair p A point (lastVariable p A point) from outer]
  exact congrArg PSigma.fst (endpointPair_decode p A point (lastVariable p A point))

/-- Every full material identity point is exactly its decoded reflexive point.
This uses endpoint equality and the actual separated-singleton witness. -/
theorem reflexivity_readEndpoint (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    reflexivitySubstitution p A ∘ readEndpoint p A = id := by
  funext q
  obtain ⟨⟨endpoints, witness⟩, rfl⟩ := (extensionDecode p (witnessFamily p A)).symm.surjective q
  obtain ⟨⟨point, right⟩, rfl⟩ := (extensionDecode p (secondFamily p A)).symm.surjective endpoints
  have equal : lastVariable p A point = right :=
    (endpointPair_equal_iff p A point right).mp (identityDecode witness)
  cases equal
  have outer := congrArg PSigma.fst ((extensionDecode p (witnessFamily p A)).apply_symm_apply
    ⟨endpointPair p A point (lastVariable p A point), witness⟩)
  have inner := congrArg PSigma.fst (endpointPair_decode p A point (lastVariable p A point))
  have read : readEndpoint p A ((extensionDecode p (witnessFamily p A)).symm
      ⟨endpointPair p A point (lastVariable p A point), witness⟩) = point := by
    change projection p (secondFamily p A) (_ : Elements (extension p (secondFamily p A))) = point
    rw [show projection p (witnessFamily p A) ((extensionDecode p (witnessFamily p A)).symm
        ⟨endpointPair p A point (lastVariable p A point), witness⟩) =
        endpointPair p A point (lastVariable p A point) from outer]
    exact inner
  change reflexivitySubstitution p A (readEndpoint p A _) = _
  apply (congrArg (reflexivitySubstitution p A) read).trans
  apply El.ext HSet.propositional
  change HSet.kpair (endpointPair p A point (lastVariable p A point)).1 ∅ =
    HSet.kpair (endpointPair p A point (lastVariable p A point)).1 witness.1
  rw [identityMember_value witness]

/-- Material comprehension, endpoints and witness have a proved inverse to
the reflexivity substitution in this extensional interpretation. -/
def identityContextEquiv (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Elements (extension p A) ≃
      Elements (identityContext (hypersetCwf p) (identityFormation p) A) where
  toFun := reflexivitySubstitution p A
  invFun := readEndpoint p A
  left_inv point := congrFun (readEndpoint_reflexivity p A) point
  right_inv point := congrFun (reflexivity_readEndpoint p A) point

set_option maxHeartbeats 800000 in
theorem endpointPair_witnessFamily (p : HSet.Presentation.{u}) {Γ : HSet.{u}}
    (A : Family Γ) (point : Elements (extension p A))
    (right : Elements (secondFamily p A point)) :
    witnessFamily p A (endpointPair p A point right) =
      identitySet (lastVariable p A point) right :=
  congrArg (fun q : Σ' q : Elements (extension p A), Elements (secondFamily p A q) =>
    identitySet (lastVariable p A q.1) q.2) (endpointPair_decode p A point right)

theorem reflexivity_over_diagonal (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    projection p (witnessFamily p A) ∘ reflexivitySubstitution p A =
      endpointDiagonal (hypersetCwf p) A := by
  funext point
  exact congrArg PSigma.fst ((extensionDecode p (witnessFamily p A)).apply_symm_apply
    ⟨endpointPair p A point (lastVariable p A point), identityEncode
      ((endpointPair_equal_iff p A point (lastVariable p A point)).mpr rfl)⟩)

private theorem elements_heq {X Y : HSet.{u}} (same : X = Y)
    (left : Elements X) (right : Elements Y) (values : left.1 = right.1) : HEq left right := by
  cases same
  exact heq_of_eq (El.ext HSet.propositional values)

private theorem sections_heq {I : Sort uIndex} {F G : I → Sort uValue}
    {s : (i : I) → F i} {t : (i : I) → G i} (same : ∀ i, HEq (s i) (t i)) : HEq s t := by
  have types : F = G := funext fun i => type_eq_of_heq (same i)
  cases types
  exact heq_of_eq (funext fun i => eq_of_heq (same i))

theorem reflexivity_witness (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    HEq (fun point => lastVariable p (witnessFamily p A) (reflexivitySubstitution p A point))
      ((identityReflexivity p).refl (lastVariable p A)) := by
  apply sections_heq
  intro point
  have endpoints := congrFun (reflexivity_over_diagonal p A) point
  have familyEq := (congrArg (witnessFamily p A) endpoints).trans
    (endpointPair_witnessFamily p A point (lastVariable p A point))
  apply elements_heq familyEq
  exact identityMember_value _

/-- Full dependent elimination transports an actual material base member
along reconstruction of the complete endpoint-and-witness point. -/
def j (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) : Section motive :=
  fun point => transport
    (congrArg motive ((identityContextEquiv p A).apply_symm_apply point))
    (base (readEndpoint p A point))

/-- Equality transport retains the actual hyperset result selected by the base. -/
theorem j_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A))
    (point : Elements (extension p (witnessFamily p A))) :
    (j p motive base point).1 = (base (readEndpoint p A point)).1 :=
  transport_fst _ _

theorem j_beta (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) :
    (fun point => j p motive base (reflexivitySubstitution p A point)) = base := by
  funext point
  apply El.ext HSet.propositional
  exact (j_value p motive base _).trans
    (congrArg (fun point => (base point).1) (congrFun (readEndpoint_reflexivity p A) point))

def identityElimination (p : HSet.Presentation.{u}) :
    IdentityEliminationBeta (hypersetCwf p) (identityFormation p) (identityReflexivity p) where
  reflexivitySubstitution := reflexivitySubstitution p
  over_diagonal := reflexivity_over_diagonal p
  witness_is_refl := reflexivity_witness p
  j := j p
  beta := j_beta p

/-- Reindex the entire material identity point through its proved decoding,
the actual material comprehension lift, and its reconstructed witness. -/
def identityReindex (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    Substitution (extension p (witnessFamily p (A ∘ σ))) (extension p (witnessFamily p A)) :=
  reflexivitySubstitution p A ∘ liftSubstitution p σ A ∘ readEndpoint p (A ∘ σ)

theorem identityReindex_readEndpoint (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    readEndpoint p A ∘ identityReindex p σ A =
      liftSubstitution p σ A ∘ readEndpoint p (A ∘ σ) := by
  funext point
  exact congrFun (readEndpoint_reflexivity p A) _

theorem reflexivity_square (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    identityReindex p σ A ∘ reflexivitySubstitution p (A ∘ σ) =
      reflexivitySubstitution p A ∘ liftSubstitution p σ A := by
  funext point
  exact congrArg (reflexivitySubstitution p A ∘ liftSubstitution p σ A)
    (congrFun (readEndpoint_reflexivity p (A ∘ σ)) point)

theorem identityReindex_id (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    identityReindex p id A = id := by
  unfold identityReindex
  rw [liftSubstitution_id]
  exact reflexivity_readEndpoint p A

theorem identityReindex_comp (p : HSet.Presentation.{u}) {Γ Δ Θ : HSet.{u}}
    (σ : Substitution Δ Θ) (τ : Substitution Γ Δ) (A : Family Θ) :
    identityReindex p (σ ∘ τ) A =
      identityReindex p σ A ∘ identityReindex p τ (A ∘ σ) := by
  funext point
  have read := congrFun (identityReindex_readEndpoint p τ (A ∘ σ)) point
  have lift := congrFun (liftSubstitution_comp p σ τ A) (readEndpoint p (A ∘ (σ ∘ τ)) point)
  exact congrArg (reflexivitySubstitution p A) (lift.trans
    (congrArg (liftSubstitution p σ A) read).symm)

/-- The reindexed base is constructed using the proved reflexivity square,
with an explicit material-family equality cast. -/
def reindexBase (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ)
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) :
    Section (motive ∘ identityReindex p σ A ∘ reflexivitySubstitution p (A ∘ σ)) :=
  sectionTransport (funext fun point =>
    congrArg motive (congrFun (reflexivity_square p σ A) point).symm)
    (fun point => base (liftSubstitution p σ A point))

theorem reindexBase_heq (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ)
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) :
    HEq (reindexBase p σ A motive base) (fun point => base (liftSubstitution p σ A point)) :=
  sectionTransport_heq _ _

theorem reindexBase_value (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ)
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A))
    (point : Elements (extension p (A ∘ σ))) :
    (reindexBase p σ A motive base point).1 = (base (liftSubstitution p σ A point)).1 :=
  sectionTransport_value _ _ _

set_option maxHeartbeats 2000000 in
/-- Full J commutes with substitution of the base, both endpoints and the
identity witness. The motive is arbitrary over that entire material context. -/
theorem j_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ)
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) :
    (fun point => j p motive base (identityReindex p σ A point)) =
      j p (motive ∘ identityReindex p σ A) (reindexBase p σ A motive base) := by
  funext point
  apply El.ext HSet.propositional
  calc
    _ = (base (readEndpoint p A (identityReindex p σ A point))).1 := j_value p motive base _
    _ = (base (liftSubstitution p σ A (readEndpoint p (A ∘ σ) point))).1 :=
      congrArg (fun point => (base point).1) (congrFun (identityReindex_readEndpoint p σ A) point)
    _ = (reindexBase p σ A motive base (readEndpoint p (A ∘ σ) point)).1 :=
      (reindexBase_value p σ A motive base _).symm
    _ = _ := (j_value p (A := A ∘ σ) (motive ∘ identityReindex p σ A)
      (reindexBase p σ A motive base) point).symm

theorem j_beta_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ)
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) :
    (fun point => j p motive base
      (identityReindex p σ A (reflexivitySubstitution p (A ∘ σ) point))) =
      reindexBase p σ A motive base := by
  exact (congrArg (fun term => fun point => term (reflexivitySubstitution p (A ∘ σ) point))
    (j_substitution p σ A motive base)).trans (j_beta p _ _)

/-- Successive and composite substitutions of full J agree across the
proved equality of their material motive families. -/
theorem j_substitution_comp (p : HSet.Presentation.{u}) {Γ Δ Θ : HSet.{u}}
    (σ : Substitution Δ Θ) (τ : Substitution Γ Δ) (A : Family Θ)
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) :
    HEq (fun point => j p motive base
      (identityReindex p σ A (identityReindex p τ (A ∘ σ) point)))
      (j p (motive ∘ identityReindex p (σ ∘ τ) A)
        (reindexBase p (σ ∘ τ) A motive base)) := by
  apply sections_heq
  intro point
  have composite := congrFun (identityReindex_comp p σ τ A) point
  apply elements_heq (congrArg motive composite.symm)
  exact (congrArg (fun point => (j p motive base point).1) composite.symm).trans
    (congrArg PSigma.fst (congrFun (j_substitution p (σ ∘ τ) A motive base) point))

def hypersetIdentityOperations (p : HSet.Presentation.{u}) :
    IdentityOperations (hypersetCwf p) where
  formation := IdentityFormationOperations.ofQualified (identityFormation p)
  reflexivity := IdentityReflexivityOperations.ofQualified (identityReflexivity p)
  elimination := IdentityEliminationOperations.ofQualified (identityElimination p)
  reindexing.map := identityReindex p

theorem hypersetIdentityOperations_boundary (p : HSet.Presentation.{u}) :
    IdentityBoundary (hypersetIdentityOperations p).reflexivity
      (hypersetIdentityOperations p).elimination :=
  IdentityEliminationOperations.ofQualified_boundary (identityElimination p)

theorem hypersetIdentityOperations_beta (p : HSet.Presentation.{u}) :
    IdentityBeta (hypersetIdentityOperations p).elimination :=
  IdentityEliminationOperations.ofQualified_beta (identityElimination p)

theorem hypersetIdentityOperations_formation_substitution (p : HSet.Presentation.{u}) :
    StrictIdentityFormationSubstitution (hypersetIdentityOperations p).formation :=
  IdentityFormationOperations.ofQualified_substitution (identityFormation p)

theorem hypersetIdentityOperations_reflexivity_substitution (p : HSet.Presentation.{u}) :
    StrictReflexivitySubstitution (hypersetIdentityOperations p).reflexivity :=
  IdentityReflexivityOperations.ofQualified_substitution (identityReflexivity p)

theorem hypersetIdentityOperations_reflexivity_square (p : HSet.Presentation.{u}) :
    ReflexivityReindexSquare (hypersetIdentityOperations p).elimination
      (hypersetIdentityOperations p).reindexing := reflexivity_square p

theorem hypersetIdentityOperations_j_substitution (p : HSet.Presentation.{u}) :
    StrictJSubstitution (hypersetIdentityOperations p).elimination
      (hypersetIdentityOperations p).reindexing := by
  intro Γ Δ σ A motive base reindexedBase same
  have canonical : reindexBase p σ A motive base = reindexedBase :=
    eq_of_heq ((reindexBase_heq p σ A motive base).trans same)
  cases canonical
  exact heq_of_eq (j_substitution p σ A motive base)

theorem identityBase_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    projection p A ∘ readEndpoint p A ∘ identityReindex p σ A =
      σ ∘ projection p (A ∘ σ) ∘ readEndpoint p (A ∘ σ) := by
  funext point
  exact (congrArg (projection p A) (congrFun (identityReindex_readEndpoint p σ A) point)).trans
    (congrFun (liftSubstitution_projection p σ A) (readEndpoint p (A ∘ σ) point))

theorem liftSubstitution_variable_value (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) (point : Elements (extension p (A ∘ σ))) :
    (lastVariable p A (liftSubstitution p σ A point)).1 =
      (lastVariable p (A ∘ σ) point).1 := by
  have familyEq : (fun point => A (projection p A (liftSubstitution p σ A point))) =
      (fun point => (A ∘ σ) (projection p (A ∘ σ) point)) :=
    funext fun point => congrArg A (congrFun (liftSubstitution_projection p σ A) point)
  have canonical : sectionTransport familyEq (fun point => lastVariable p A (liftSubstitution p σ A point)) =
      lastVariable p (A ∘ σ) :=
    eq_of_heq ((sectionTransport_heq familyEq _).trans (liftSubstitution_variable_heq p σ A))
  exact (sectionTransport_value familyEq _ point).symm.trans
    (congrArg (fun term => (term point).1) canonical)

theorem identityLeft_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    HEq (fun point => lastVariable p A (readEndpoint p A (identityReindex p σ A point)))
      (fun point => lastVariable p (A ∘ σ) (readEndpoint p (A ∘ σ) point)) := by
  apply sections_heq
  intro point
  apply elements_heq (congrArg A (congrFun (identityBase_substitution p σ A) point))
  exact (congrArg (fun q => (lastVariable p A q).1)
    (congrFun (identityReindex_readEndpoint p σ A) point)).trans
    (liftSubstitution_variable_value p σ A (readEndpoint p (A ∘ σ) point))

theorem identityRight_eq_left (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ)
    (point : Elements (extension p (witnessFamily p A))) :
    lastVariable p (secondFamily p A) (projection p (witnessFamily p A) point) =
      lastVariable p A (readEndpoint p A point) :=
  (identityDecode (lastVariable p (witnessFamily p A) point)).symm

theorem identityRight_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    HEq (fun point => lastVariable p (secondFamily p A)
      (projection p (witnessFamily p A) (identityReindex p σ A point)))
      (fun point => lastVariable p (secondFamily p (A ∘ σ))
        (projection p (witnessFamily p (A ∘ σ)) point)) := by
  have targetEq := funext fun point => identityRight_eq_left p A (identityReindex p σ A point)
  have sourceEq := funext fun point => identityRight_eq_left p (A ∘ σ) point
  exact (heq_of_eq targetEq).trans ((identityLeft_substitution p σ A).trans (heq_of_eq sourceEq).symm)

theorem identityWitness_substitution (p : HSet.Presentation.{u}) {Γ Δ : HSet.{u}}
    (σ : Substitution Γ Δ) (A : Family Δ) :
    HEq (fun point => lastVariable p (witnessFamily p A) (identityReindex p σ A point))
      (fun point => lastVariable p (witnessFamily p (A ∘ σ)) point) := by
  apply sections_heq
  intro point
  have targetEq : witnessFamily p A (projection p (witnessFamily p A)
      (identityReindex p σ A point)) =
      identitySet (lastVariable p A (readEndpoint p A (identityReindex p σ A point)))
        (lastVariable p A (readEndpoint p A (identityReindex p σ A point))) := by
    change identitySet _ _ = _
    rw [identityRight_eq_left p A]
    rfl
  have sourceEq : witnessFamily p (A ∘ σ) (projection p (witnessFamily p (A ∘ σ)) point) =
      identitySet (lastVariable p (A ∘ σ) (readEndpoint p (A ∘ σ) point))
        (lastVariable p (A ∘ σ) (readEndpoint p (A ∘ σ) point)) := by
    change identitySet _ _ = _
    rw [identityRight_eq_left p (A ∘ σ)]
    rfl
  have sets := targetEq.trans ((identitySet_refl _).trans ((identitySet_refl _).symm.trans sourceEq.symm))
  apply elements_heq sets
  exact (identityMember_value _).trans (identityMember_value _).symm

theorem hypersetIdentityOperations_reindexing (p : HSet.Presentation.{u}) :
    StrictIdentityReindexing (hypersetIdentityOperations p).elimination
      (hypersetIdentityOperations p).reindexing := by
  refine ⟨identityBase_substitution p, ?_, reflexivity_square p⟩
  intro Γ Δ σ A
  exact ⟨identityLeft_substitution p σ A, identityRight_substitution p σ A,
    identityWitness_substitution p σ A⟩

/-- The existing material products, sums and actual identity interpretation
share one contextual core. -/
def hypersetOperations (p : HSet.Presentation.{u}) : Operations (hypersetCwf p) where
  products := hypersetPiOperations p
  sums := hypersetSigmaOperations p
  identity := hypersetIdentityOperations p

theorem hypersetOperations_beta (p : HSet.Presentation.{u}) : BetaLaws (hypersetOperations p) :=
  ⟨hypersetPiOperations_beta p, hypersetSigmaOperations_beta p,
    hypersetIdentityOperations_boundary p, hypersetIdentityOperations_beta p⟩

theorem hypersetOperations_substitution (p : HSet.Presentation.{u}) :
    StrictSubstitutionLaws (hypersetOperations p) :=
  ⟨hypersetPiOperations_substitution p, hypersetSigmaOperations_substitution p,
    hypersetIdentityOperations_formation_substitution p,
    hypersetIdentityOperations_reflexivity_substitution p,
    hypersetIdentityOperations_reindexing p, hypersetIdentityOperations_j_substitution p⟩

/-! ## Comparison with the existing equality model -/

/-- Decode material comprehension into the actual dependent endpoint values
used by the set-family CwF. The inverse re-encodes their material ordered pair. -/
def setFamilyEndpointEquiv (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Elements (extension p A) ≃ Σ γ : Elements Γ, Elements (A γ) where
  toFun point := ⟨(extensionDecode p A point).1, (extensionDecode p A point).2⟩
  invFun point := (extensionDecode p A).symm ⟨point.1, point.2⟩
  left_inv point := (extensionDecode p A).symm_apply_apply point
  right_inv point := congrArg (fun point : Σ' γ : Elements Γ, Elements (A γ) =>
    (⟨point.1, point.2⟩ : Σ γ : Elements Γ, Elements (A γ)))
    ((extensionDecode p A).apply_symm_apply ⟨point.1, point.2⟩)

abbrev SetFamilyIdentityContext {Γ : HSet.{u}} (A : Family Γ) :=
  identityContext (familiesCwf.{u + 1}) ContextualIdentityTypes.Families.identityFormation
    (fun γ : Elements Γ => Elements (A γ))

/-- In the set-family equality model, full set-family equality points likewise
decode and reconstruct from their single endpoint. -/
def setFamilyReflexivityEquiv {Γ : HSet.{u}} (A : Family Γ) :
    (Σ γ : Elements Γ, Elements (A γ)) ≃ SetFamilyIdentityContext A where
  toFun := ContextualIdentityTypes.Families.identityElimination.reflexivitySubstitution
    (fun γ : Elements Γ => Elements (A γ))
  invFun point := point.1.1
  left_inv _ := rfl
  right_inv point := by
    rcases point with ⟨⟨⟨γ, left⟩, right⟩, same⟩
    cases same.down.down
    rfl

/-- Explicit material/set-family identity-context comparison with inverse laws.
Both actual endpoint members and equality witnesses are accounted for. -/
def setFamilyIdentityEquiv (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Elements (extension p (witnessFamily p A)) ≃ SetFamilyIdentityContext A :=
  (identityContextEquiv p A).symm.trans ((setFamilyEndpointEquiv p A).trans (setFamilyReflexivityEquiv A))

theorem setFamilyIdentityEquiv_left (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ)
    (point : Elements (extension p (witnessFamily p A))) :
    (setFamilyIdentityEquiv p A point).1.1.2 = lastVariable p A (readEndpoint p A point) := rfl

theorem setFamilyIdentityEquiv_right (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ)
    (point : Elements (extension p (witnessFamily p A))) :
    (setFamilyIdentityEquiv p A point).1.2 =
      lastVariable p (secondFamily p A) (projection p (witnessFamily p A) point) :=
  (identityRight_eq_left p A point).symm

def setFamilyMotive (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    (motive : Family (extension p (witnessFamily p A))) : SetFamilyIdentityContext A → Type (u + 1) :=
  fun point => Elements (motive ((setFamilyIdentityEquiv p A).symm point))

def setFamilyBase (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) :
    (point : Σ γ : Elements Γ, Elements (A γ)) →
      setFamilyMotive p motive (setFamilyReflexivityEquiv A point) :=
  fun point => base ((setFamilyEndpointEquiv p A).symm point)

theorem setFamilyJ_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A)) (point : SetFamilyIdentityContext A) :
    (ContextualIdentityTypes.Families.identityElimination.j (setFamilyMotive p motive)
      (setFamilyBase p motive base) point).1 =
      (base ((setFamilyEndpointEquiv p A).symm point.1.1)).1 := by
  rcases point with ⟨⟨⟨γ, left⟩, right⟩, same⟩
  cases same.down.down
  rfl

/-- The full-motive J of the existing equality model, transferred through
the explicit material/set-family context isomorphism, is the constructed material
J. The transport identifies the motive fibres and retains their actual values. -/
theorem setFamilyJ_comparison (p : HSet.Presentation.{u}) {Γ : HSet.{u}} {A : Family Γ}
    (motive : Family (extension p (witnessFamily p A)))
    (base : Section (motive ∘ reflexivitySubstitution p A))
    (point : Elements (extension p (witnessFamily p A))) :
    transport (congrArg motive ((setFamilyIdentityEquiv p A).symm_apply_apply point))
      (ContextualIdentityTypes.Families.identityElimination.j (setFamilyMotive p motive)
        (setFamilyBase p motive base) (setFamilyIdentityEquiv p A point)) = j p motive base point := by
  apply El.ext HSet.propositional
  calc
    _ = _ := transport_fst _ _
    _ = (base ((setFamilyEndpointEquiv p A).symm (setFamilyIdentityEquiv p A point).1.1)).1 :=
      setFamilyJ_value p motive base _
    _ = (base (readEndpoint p A point)).1 := congrArg (fun point => (base point).1)
      ((setFamilyEndpointEquiv p A).symm_apply_apply (readEndpoint p A point))
    _ = _ := (j_value p motive base point).symm

/-! ## Positive and negative interpretation controls -/

/-- This extensional model has singleton material equality witnesses. -/
theorem model_proofIrrelevance (p : HSet.Presentation.{u}) :
    IdentityProofIrrelevance (hypersetCwf p) (identityFormation p) := by
  intro Γ A left right
  refine ⟨?_⟩
  intro first second
  funext γ
  apply El.ext HSet.propositional
  exact (identityMember_value (first γ)).trans (identityMember_value (second γ)).symm

/-- Reflection is proved only for the material equality interpretation. -/
theorem model_endpointReflection (p : HSet.Presentation.{u}) :
    IdentityEndpointReflection (hypersetCwf p) (identityFormation p) := by
  intro Γ A left right equality
  exact funext fun γ => identityDecode (equality γ)

def quineEndpoint : Elements ({HSet.quineAtom.{u}} : HSet.{u}) :=
  ⟨HSet.quineAtom, HSet.mem_singleton_self _⟩

/-- Non-well-founded endpoint values have actual reflexivity witnesses. -/
theorem quine_identity_inhabited :
    Nonempty (Elements (identitySet quineEndpoint.{u} quineEndpoint)) :=
  ⟨identityEncode rfl⟩

def mixedEmptyEndpoint : Elements ({∅, HSet.quineAtom.{u}} : HSet.{u}) :=
  ⟨∅, HSet.mem_pair.mpr (Or.inl rfl)⟩

def mixedQuineEndpoint : Elements ({∅, HSet.quineAtom.{u}} : HSet.{u}) :=
  ⟨HSet.quineAtom, HSet.mem_pair.mpr (Or.inr rfl)⟩

theorem empty_quine_identity_empty :
    identitySet mixedEmptyEndpoint.{u} mixedQuineEndpoint = ∅ :=
  identitySet_eq_empty (fun equal => HSet.empty_ne_quineAtom (congrArg PSigma.fst equal))

theorem no_empty_quine_identity :
    ¬ Nonempty (Elements (identitySet mixedEmptyEndpoint.{u} mixedQuineEndpoint)) := by
  rintro ⟨witness⟩
  exact HSet.empty_ne_quineAtom (congrArg PSigma.fst (identityDecode witness))

/-- A motive carrying the full actual identity point as its result value. -/
def pointMotive (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Family (extension p (witnessFamily p A)) := fun point => {point.1}

def pointBase (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Section (pointMotive p A ∘ reflexivitySubstitution p A) :=
  fun point => ⟨(reflexivitySubstitution p A point).1, HSet.mem_singleton_self _⟩

theorem pointMotive_injective (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ) :
    Function.Injective (pointMotive p A) :=
  fun _ _ same => El.ext HSet.propositional (HSet.singleton_inj.mp same)

def mixedFamily : Family terminalContext.{u} := fun _ => {∅, HSet.quineAtom}

/-- The full identity-point motive has genuinely different material fibres;
it cannot be supplied by a constant-motive eliminator. -/
theorem pointMotive_not_constant (p : HSet.Presentation.{u}) :
    ¬ ∃ X : HSet.{u}, ∀ point, pointMotive p mixedFamily point = X := by
  rintro ⟨X, constant⟩
  let γ : Elements terminalContext.{u} := ⟨∅, HSet.mem_singleton_self _⟩
  let first : Elements (extension p mixedFamily) :=
    (extensionDecode p mixedFamily).symm ⟨γ, mixedEmptyEndpoint⟩
  let second : Elements (extension p mixedFamily) :=
    (extensionDecode p mixedFamily).symm ⟨γ, mixedQuineEndpoint⟩
  have endpoints : first = second := (identityContextEquiv p mixedFamily).injective
    (pointMotive_injective p mixedFamily ((constant _).trans (constant _).symm))
  exact HSet.empty_ne_quineAtom (HSet.kpair_inj.mp (congrArg PSigma.fst endpoints)).2

/-- Full dependent J reconstructs a value containing the actual base,
both material endpoints and the witness, rather than using a constant motive. -/
theorem j_pointMotive_value (p : HSet.Presentation.{u}) {Γ : HSet.{u}} (A : Family Γ)
    (point : Elements (extension p (witnessFamily p A))) :
    (j p (pointMotive p A) (pointBase p A) point).1 = point.1 :=
  (j_value p _ _ point).trans (congrArg PSigma.fst (congrFun (reflexivity_readEndpoint p A) point))

/-- Contextual J admits a genuinely non-well-founded hyperset-valued motive. -/
def quineMotive (p : HSet.Presentation.{u}) :
    Family (extension p (witnessFamily p quineFamily)) := fun _ => {HSet.quineAtom}

def quineBase (p : HSet.Presentation.{u}) :
    Section (quineMotive p ∘ reflexivitySubstitution p quineFamily) :=
  fun _ => ⟨HSet.quineAtom, HSet.mem_singleton_self _⟩

theorem j_quine_value (p : HSet.Presentation.{u})
    (point : Elements (extension p (witnessFamily p quineFamily))) :
    (j p (quineMotive p) (quineBase p) point).1 = HSet.quineAtom := j_value p _ _ point

/-- Distinct presentation occurrences can observe equal material endpoints.
The actual equality witness does not identify the occurrence types. -/
theorem duplicate_occurrences_equal_endpoints_distinct :
    let first : Elements (AccessiblePointedGraph.picture AccessiblePointedGraph.twoChildren.{u}) :=
      ⟨(AccessiblePointedGraph.memberObservation _ (AccessiblePointedGraph.twoChildrenOccurrence true)).1,
        (AccessiblePointedGraph.memberObservation _ (AccessiblePointedGraph.twoChildrenOccurrence true)).2⟩
    let second : Elements (AccessiblePointedGraph.picture AccessiblePointedGraph.twoChildren.{u}) :=
      ⟨(AccessiblePointedGraph.memberObservation _ (AccessiblePointedGraph.twoChildrenOccurrence false)).1,
        (AccessiblePointedGraph.memberObservation _ (AccessiblePointedGraph.twoChildrenOccurrence false)).2⟩
    Nonempty (Elements (identitySet first second)) ∧
      AccessiblePointedGraph.twoChildrenOccurrence true ≠
        AccessiblePointedGraph.twoChildrenOccurrence false := by
  dsimp only
  refine ⟨⟨identityEncode ?_⟩, AccessiblePointedGraph.twoChildrenOccurrence_ne⟩
  exact El.ext HSet.propositional
    (congrArg Subtype.val AccessiblePointedGraph.twoChildren_same_member)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyIdentity
