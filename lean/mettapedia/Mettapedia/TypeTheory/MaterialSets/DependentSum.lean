import Mettapedia.TypeTheory.MaterialSets.DependentReplacement

/-!
# The set of dependent pairs and the dependent sum of member types

For a family `B : El X → set`, the set of dependent pairs is

  `sigmaSet X B := Union (Image X (λa. Image (B a) (λb. Pair (fst a) (fst b))))`.

Its members are compared with the dependent sum of member types,

  `El (sigmaSet X B) ≃ Σ' a : El X, El (B a)`.

The inverse map must recover a member of `X` and a member of its fibre from a
member of the set of pairs. The pair projections recover the members;
`EvidenceRecovery` recovers their evidence, eliminating the existential that
membership in an image provides into the membership propositions. Propositional
membership makes the recovered evidence the evidence that was paired, so the
two maps are inverse (`sigmaSetEquiv`), and the set encoding is faithful
(`pairMember_fst_injective`).

Without propositional membership the set of pairs forgets which witness was
paired (`pairMember_fst_not_injective`); `Instances.TwoWitness` shows that the
comparison then fails altogether.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets

universe u v

/-- Ordered pairs with their projections. The profile defines `Pair` from `UPair`,
and the projections from `Union` and `Sep`. -/
structure Pairing (S : Type u) where
  pair : S → S → S
  fst : S → S
  snd : S → S
  fst_pair : ∀ x y, fst (pair x y) = x
  snd_pair : ∀ x y, snd (pair x y) = y

section Sum

variable {S : Type u} (Mem : S → S → Sort v)

/-- Union, with evidence-producing introduction and propositional elimination. -/
structure UnionOperation where
  union : S → S
  mem_union : ∀ {x W Y : S}, Mem x W → Mem W Y → Mem x (union Y)
  exists_of_mem_union : ∀ {x Y : S}, Mem x (union Y) →
    ∃ W, Nonempty (Mem x W) ∧ Nonempty (Mem W Y)

variable {Mem}
variable (R : DependentReplacement Mem) (U : UnionOperation Mem) (P : Pairing S)

/-- `SigmaSet X B := Union (Image X (λa. Image (B a) (λb. Pair (fst a) (fst b))))`. -/
def sigmaSet (X : S) (B : El Mem X → S) : S :=
  U.union (R.image X fun a => R.image (B a) fun b => P.pair a.1 b.1)

/-- A member of `X` and a member of its fibre give a member of the set of
pairs. -/
def pairMember {X : S} {B : El Mem X → S} (ab : Σ' a : El Mem X, El Mem (B a)) :
    El Mem (sigmaSet R U P X B) :=
  ⟨P.pair ab.1.1 ab.2.1,
    U.mem_union (R.mem_image (fun b => P.pair ab.1.1 b.1) ab.2)
      (R.mem_image (fun a => R.image (B a) fun b => P.pair a.1 b.1) ab.1)⟩

theorem exists_of_mem_sigmaSet {X z : S} {B : El Mem X → S}
    (m : Mem z (sigmaSet R U P X B)) :
    ∃ (a : El Mem X) (b : El Mem (B a)), P.pair a.1 b.1 = z := by
  obtain ⟨W, ⟨inW⟩, ⟨mW⟩⟩ := U.exists_of_mem_union m
  obtain ⟨a, rfl⟩ := R.exists_of_mem_image mW
  obtain ⟨b, rfl⟩ := R.exists_of_mem_image inW
  exact ⟨a, b, rfl⟩

theorem nonempty_mem_fst {X z : S} {B : El Mem X → S} (m : Mem z (sigmaSet R U P X B)) :
    Nonempty (Mem (P.fst z) X) := by
  obtain ⟨a, b, rfl⟩ := exists_of_mem_sigmaSet R U P m
  rw [P.fst_pair]
  exact ⟨a.2⟩

/-- The second projection lies in the fibre over the recovered first member.
Descent identifies that fibre with the fibre the pair was built from. -/
theorem nonempty_mem_snd (h : PropositionalMembership Mem) {X z : S} {B : El Mem X → S}
    (m : Mem z (sigmaSet R U P X B)) (a : El Mem X) (first : a.1 = P.fst z) :
    Nonempty (Mem (P.snd z) (B a)) := by
  obtain ⟨a₀, b₀, rfl⟩ := exists_of_mem_sigmaSet R U P m
  obtain rfl : a₀ = a := El.ext h ((P.fst_pair _ _).symm.trans first.symm)
  rw [P.snd_pair]
  exact ⟨b₀.2⟩

/-- Recover a member of `X` and a member of its fibre from a member of the set
of pairs. -/
def unpairMember (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem) {X : S}
    {B : El Mem X → S} (c : El Mem (sigmaSet R U P X B)) : Σ' a : El Mem X, El Mem (B a) :=
  ⟨⟨P.fst c.1, r.recover (nonempty_mem_fst R U P c.2)⟩,
    ⟨P.snd c.1, r.recover (nonempty_mem_snd R U P h c.2 _ rfl)⟩⟩

/-- Elements of the dependent sum are determined by their two members. -/
theorem psigma_el_ext (h : PropositionalMembership Mem) {X : S} {B : El Mem X → S}
    {c d : Σ' a : El Mem X, El Mem (B a)} (first : c.1.1 = d.1.1) (second : c.2.1 = d.2.1) :
    c = d := by
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := d
  obtain rfl : a = a' := El.ext h first
  obtain rfl : b = b' := El.ext h second
  rfl

/-- The members of the set of dependent pairs are the dependent sum of the
member types, `El (SigmaSet X B) ≃ Σ a : El X. El (B a)`. -/
def sigmaSetEquiv (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem) (X : S)
    (B : El Mem X → S) : El Mem (sigmaSet R U P X B) ≃ Σ' a : El Mem X, El Mem (B a) where
  toFun := unpairMember R U P h r
  invFun := pairMember R U P
  left_inv c := by
    obtain ⟨z, m⟩ := c
    apply El.ext h
    change P.pair (P.fst z) (P.snd z) = z
    obtain ⟨a, b, rfl⟩ := exists_of_mem_sigmaSet R U P m
    rw [P.fst_pair, P.snd_pair]
  right_inv ab := psigma_el_ext h (P.fst_pair ab.1.1 ab.2.1) (P.snd_pair ab.1.1 ab.2.1)

theorem sigmaSetEquiv_symm_apply_fst (h : PropositionalMembership Mem)
    (r : EvidenceRecovery Mem) {X : S} {B : El Mem X → S}
    (ab : Σ' a : El Mem X, El Mem (B a)) :
    ((sigmaSetEquiv R U P h r X B).symm ab).1 = P.pair ab.1.1 ab.2.1 := rfl

/-- The set encoding of the dependent sum is faithful: the underlying pair
determines the member of `X`, its fibre member, and their evidence. -/
theorem pairMember_fst_injective (h : PropositionalMembership Mem) {X : S}
    {B : El Mem X → S} :
    Function.Injective
      (fun ab : Σ' a : El Mem X, El Mem (B a) => (pairMember R U P ab).1) := by
  intro c d same
  exact psigma_el_ext h
    ((P.fst_pair c.1.1 c.2.1).symm.trans ((congrArg P.fst same).trans (P.fst_pair d.1.1 d.2.1)))
    ((P.snd_pair c.1.1 c.2.1).symm.trans ((congrArg P.snd same).trans (P.snd_pair d.1.1 d.2.1)))

/-- When a member `x` of `X` has two witnesses whose fibres
share a member, two distinct elements of the dependent sum are sent to one
pair. The set of pairs forgets which witness was paired. -/
theorem pairMember_fst_not_injective {X x : S} {B : El Mem X → S} {p q : Mem x X}
    (distinct : p ≠ q) (b : El Mem (B ⟨x, p⟩)) (b' : El Mem (B ⟨x, q⟩)) (same : b.1 = b'.1) :
    ¬ Function.Injective
      (fun ab : Σ' a : El Mem X, El Mem (B a) => (pairMember R U P ab).1) := by
  intro injective
  have equal := @injective ⟨⟨x, p⟩, b⟩ ⟨⟨x, q⟩, b'⟩ (congrArg (P.pair x) same)
  exact distinct (eq_of_heq (PSigma.mk.inj_iff.mp (PSigma.mk.inj_iff.mp equal).1).2)

end Sum

end Mettapedia.TypeTheory.MaterialSets
