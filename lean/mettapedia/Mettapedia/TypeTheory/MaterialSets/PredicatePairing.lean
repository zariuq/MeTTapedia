import Mettapedia.TypeTheory.MaterialSets.DependentSum

/-!
# Guarded dependent pairs on an existing pairing carrier

The predicate is the actual image of the pairing operation. Decoding uses
the existing projections; re-encoding recovers every admitted code. The
weaker projection predicate preserves inhabitance but may admit extra codes.
No global surjectivity, inhabited fibre or disjoint unit tag is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets
namespace Pairing

universe u
variable {S : Type u} (P : Pairing S)

def InImage (code : S) : Prop := ∃ first second, P.pair first second = code

def SigmaGuard (domain : S → Prop) (family : S → S → Prop) (code : S) : Prop :=
  ∃ first second, P.pair first second = code ∧ domain first ∧ family first second

def ProjectionGuard (domain : S → Prop) (family : S → S → Prop) (code : S) : Prop :=
  domain (P.fst code) ∧ family (P.fst code) (P.snd code)

theorem inImage_iff_eta (code : S) :
    P.InImage code ↔ P.pair (P.fst code) (P.snd code) = code := by
  constructor
  · rintro ⟨first, second, rfl⟩
    rw [P.fst_pair, P.snd_pair]
  · intro same
    exact ⟨P.fst code, P.snd code, same⟩

theorem sigmaGuard_iff (domain : S → Prop) (family : S → S → Prop) (code : S) :
    P.SigmaGuard domain family code ↔ P.InImage code ∧ P.ProjectionGuard domain family code := by
  constructor
  · rintro ⟨first, second, rfl, firstMember, secondMember⟩
    refine ⟨⟨first, second, rfl⟩, ?_⟩
    simpa only [ProjectionGuard, P.fst_pair, P.snd_pair] using (And.intro firstMember secondMember)
  · rintro ⟨image, firstMember, secondMember⟩
    exact ⟨P.fst code, P.snd code, (P.inImage_iff_eta code).mp image, firstMember, secondMember⟩

theorem sigmaGuard_pair (domain : S → Prop) (family : S → S → Prop) (first second : S) :
    P.SigmaGuard domain family (P.pair first second) ↔ domain first ∧ family first second := by
  rw [P.sigmaGuard_iff]
  simp only [InImage, ProjectionGuard, P.fst_pair, P.snd_pair]
  exact ⟨fun valid => valid.2, fun valid => ⟨⟨first, second, rfl⟩, valid⟩⟩

abbrev GuardedSigma (domain : S → Prop) (family : S → S → Prop) :=
  Σ first : {value : S // domain value}, {value : S // family first.val value}

theorem guardedSigma_ext {domain : S → Prop} {family : S → S → Prop}
    {first second : GuardedSigma domain family}
    (heads : first.1.val = second.1.val) (tails : first.2.val = second.2.val) : first = second := by
  rcases first with ⟨first, tail⟩
  rcases second with ⟨second, tail'⟩
  obtain rfl : first = second := Subtype.ext heads
  obtain rfl : tail = tail' := Subtype.ext tails
  rfl

def pack {domain : S → Prop} {family : S → S → Prop} (value : GuardedSigma domain family) :
    {code : S // P.SigmaGuard domain family code} :=
  ⟨P.pair value.1.val value.2.val,
    value.1.val, value.2.val, rfl, value.1.property, value.2.property⟩

def unpack {domain : S → Prop} {family : S → S → Prop}
    (code : {value : S // P.SigmaGuard domain family value}) : GuardedSigma domain family :=
  ⟨⟨P.fst code.val, ((P.sigmaGuard_iff domain family code.val).mp code.property).2.1⟩,
    ⟨P.snd code.val, ((P.sigmaGuard_iff domain family code.val).mp code.property).2.2⟩⟩

theorem pack_unpack {domain : S → Prop} {family : S → S → Prop}
    (code : {value : S // P.SigmaGuard domain family value}) : P.pack (P.unpack code) = code := by
  apply Subtype.ext
  exact (P.inImage_iff_eta code.val).mp ((P.sigmaGuard_iff domain family code.val).mp code.property).1

theorem unpack_pack {domain : S → Prop} {family : S → S → Prop} (value : GuardedSigma domain family) :
    P.unpack (P.pack value) = value := by
  exact guardedSigma_ext (P.fst_pair value.1.val value.2.val) (P.snd_pair value.1.val value.2.val)

def sigmaEquiv (domain : S → Prop) (family : S → S → Prop) :
    {code : S // P.SigmaGuard domain family code} ≃ GuardedSigma domain family where
  toFun := P.unpack
  invFun := P.pack
  left_inv := P.pack_unpack
  right_inv := P.unpack_pack

theorem pack_injective {domain : S → Prop} {family : S → S → Prop} :
    Function.Injective (P.pack (domain := domain) (family := family)) :=
  Function.LeftInverse.injective P.unpack_pack

theorem nonempty_projection_iff (domain : S → Prop) (family : S → S → Prop) :
    (∃ code, P.ProjectionGuard domain family code) ↔ ∃ code, P.SigmaGuard domain family code := by
  constructor
  · rintro ⟨code, firstMember, secondMember⟩
    exact ⟨P.pair (P.fst code) (P.snd code), P.fst code, P.snd code, rfl, firstMember, secondMember⟩
  · rintro ⟨code, valid⟩
    exact ⟨code, ((P.sigmaGuard_iff domain family code).mp valid).2⟩

/-- Any admission predicate with valid decoded components and exact
reconstruction is contained in the pair-image predicate. -/
theorem sigmaGuard_maximal (domain : S → Prop) (family : S → S → Prop) (admitted : S → Prop)
    (components : ∀ code, admitted code → P.ProjectionGuard domain family code)
    (reconstructs : ∀ code, admitted code → P.pair (P.fst code) (P.snd code) = code) :
    ∀ code, admitted code → P.SigmaGuard domain family code := by
  intro code accepted
  exact (P.sigmaGuard_iff domain family code).mpr
    ⟨(P.inImage_iff_eta code).mpr (reconstructs code accepted), components code accepted⟩

theorem sigmaGuard_iff_projection_of_surjective
    (onto : Function.Surjective (fun value : S × S => P.pair value.1 value.2))
    (domain : S → Prop) (family : S → S → Prop) (code : S) :
    P.SigmaGuard domain family code ↔ P.ProjectionGuard domain family code := by
  obtain ⟨⟨first, second⟩, same⟩ := onto code
  exact (P.sigmaGuard_iff domain family code).trans
    (and_iff_right (show P.InImage code from ⟨first, second, same⟩))

theorem empty_domain {domain : S → Prop} {family : S → S → Prop}
    (empty : ∀ first, ¬ domain first) (code : S) : ¬ P.SigmaGuard domain family code := by
  rintro ⟨first, _, _, member, _⟩
  exact empty first member

theorem empty_fibres {domain : S → Prop} {family : S → S → Prop}
    (empty : ∀ first, domain first → ∀ second, ¬ family first second) (code : S) :
    ¬ P.SigmaGuard domain family code := by
  rintro ⟨first, second, _, firstMember, secondMember⟩
  exact empty first firstMember second secondMember

theorem pair_injective : Function.Injective (fun value : S × S => P.pair value.1 value.2) := by
  intro first second same
  apply Prod.ext
  · simpa only [P.fst_pair] using congrArg P.fst same
  · simpa only [P.snd_pair] using congrArg P.snd same

/-- The existing material dependent sum has this exact image predicate.
The family may depend on its member evidence; membership is propositional. -/
theorem mem_sigmaSet_iff {Mem : S → S → Prop} (replacement : DependentReplacement Mem)
    (union : UnionOperation Mem) (set : S) (family : El Mem set → S) (code : S) :
    Mem code (sigmaSet replacement union P set family) ↔
      P.SigmaGuard (fun first => Mem first set)
        (fun first second => ∃ evidence : Mem first set, Mem second (family ⟨first, evidence⟩)) code := by
  constructor
  · intro member
    obtain ⟨first, second, same⟩ := exists_of_mem_sigmaSet replacement union P member
    exact ⟨first.1, second.1, same, first.2, first.2, second.2⟩
  · rintro ⟨first, second, same, _, evidence, member⟩
    have encoded := (pairMember replacement union P
      (⟨⟨first, evidence⟩, ⟨second, member⟩⟩ : Σ' value : El Mem set, El Mem (family value))).2
    exact same ▸ encoded

#print axioms sigmaEquiv
#print axioms nonempty_projection_iff
#print axioms mem_sigmaSet_iff

end Pairing
end Mettapedia.TypeTheory.MaterialSets
