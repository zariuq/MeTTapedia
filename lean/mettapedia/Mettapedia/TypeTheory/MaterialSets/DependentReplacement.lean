import Mettapedia.TypeTheory.MaterialSets.MembershipEvidence

/-!
# Dependent replacement over members with evidence

`image X F`, for a family `F : El X → set`, is the dependent replacement
`Image`. Its introduction rule produces membership evidence for each value
`F a`. Its elimination rule gives only the bare fact that a preimage exists,
because an existential eliminates into propositions. `repl X f`, replacement
over `set → set`, is `Image` restricted along the first projection.

Extensionality is stated with Lean equality: `eq@set` is read as identity, so
`J` for sets is `Eq.rec`.

With propositional membership:

* `image_descends`: `Image` depends only on the family descended to the members
  of `X`;
* `image_members`: a value is in `Image X F` exactly when it is the value of `F`
  at some member, and then at every evidence of that member;
* `elImageEquiv`: the members of `Image X F`, with their evidence, are the values
  of `F`;
* `image_reindex`: reindexing a family along an evidence map between sets with
  the same members leaves its image unchanged;
* `transportFamily_eq_of_fst_eq`: transporting a family along an equality of
  sets gives, at each member, its value at the same member.

`Instances.TwoWitness` is a model of the same interface in which every
membership has two witnesses; there descent, `image_members`, `image_reindex` and
transport of families all fail.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets

universe u v

variable {S : Type u} (Mem : S → S → Sort v)

/-- Dependent replacement: `Image : (X : set) → (El X → set) → set`. -/
structure DependentReplacement where
  image : (X : S) → (El Mem X → S) → S
  mem_image : ∀ {X : S} (F : El Mem X → S) (a : El Mem X), Mem (F a) (image X F)
  exists_of_mem_image : ∀ {X : S} {F : El Mem X → S} {y : S},
    Mem y (image X F) → ∃ a, F a = y

/-- Extensionality: sets with the same members are equal. -/
def Extensional : Prop :=
  ∀ {X Y : S}, (∀ z, Nonempty (Mem z X) ↔ Nonempty (Mem z Y)) → X = Y

variable {Mem}

/-- Evidence maps both ways make two sets coextensional. -/
theorem coextensional_of_maps {X Y : S} (forth : ∀ z, Mem z X → Mem z Y)
    (back : ∀ z, Mem z Y → Mem z X) (z : S) : Nonempty (Mem z X) ↔ Nonempty (Mem z Y) :=
  ⟨fun ⟨p⟩ => ⟨forth z p⟩, fun ⟨q⟩ => ⟨back z q⟩⟩

namespace DependentReplacement

variable (R : DependentReplacement Mem)

/-- Replacement over `set → set`: `Repl X f := Image X (λa. f (fst a))`. -/
def repl (X : S) (f : S → S) : S := R.image X fun a => f a.1

theorem nonempty_mem_image_iff {X y : S} {F : El Mem X → S} :
    Nonempty (Mem y (R.image X F)) ↔ ∃ a, F a = y :=
  ⟨fun ⟨m⟩ => R.exists_of_mem_image m, fun ⟨a, e⟩ => ⟨e ▸ R.mem_image F a⟩⟩

/-- The replacement law over `set → set`. -/
theorem nonempty_mem_repl_iff {X y : S} {f : S → S} :
    Nonempty (Mem y (R.repl X f)) ↔ ∃ x, Nonempty (Mem x X) ∧ f x = y := by
  rw [repl, nonempty_mem_image_iff]
  constructor
  · rintro ⟨a, e⟩
    exact ⟨a.1, ⟨a.2⟩, e⟩
  · rintro ⟨x, ⟨p⟩, e⟩
    exact ⟨⟨x, p⟩, e⟩

/-- On the restriction of a total function, `Image` is replacement. -/
theorem image_eq_repl {X : S} {F : El Mem X → S} {f : S → S} (agrees : ∀ a, F a = f a.1) :
    R.image X F = R.repl X f :=
  congrArg (R.image X) (funext agrees)

/-! ## Descent -/

/-- Descent: the image of a family on `El X` is the image of the family it
induces on the members of `X`. -/
theorem image_descends (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem) {X : S}
    (F : El Mem X → S) : R.image X F = R.image X fun a => descend r F (forget a) :=
  congrArg (R.image X) (funext fun a => (descend_forget h r F a).symm)

/-- The members of `Image X F` are the member-level values of `F`: a value at
some evidence is the value at every evidence. -/
theorem image_members (h : PropositionalMembership Mem) {X y : S} {F : El Mem X → S} :
    Nonempty (Mem y (R.image X F)) ↔
      ∃ x, Nonempty (Mem x X) ∧ ∀ p : Mem x X, F ⟨x, p⟩ = y := by
  rw [nonempty_mem_image_iff]
  constructor
  · rintro ⟨a, e⟩
    exact ⟨a.1, ⟨a.2⟩, fun p => (descends_of_propositional h F ⟨a.1, p⟩ a rfl).trans e⟩
  · rintro ⟨x, ⟨p⟩, e⟩
    exact ⟨⟨x, p⟩, e p⟩

/-- A family on `El X` and its image correspond: the members of `Image X F`,
with their evidence, are the values of `F`. -/
def elImageEquiv (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem) {X : S}
    (F : El Mem X → S) : El Mem (R.image X F) ≃ {y : S // ∃ a, F a = y} where
  toFun b := ⟨b.1, R.exists_of_mem_image b.2⟩
  invFun y := ⟨y.1, r.recover (R.nonempty_mem_image_iff.mpr y.2)⟩
  left_inv _ := El.ext h rfl
  right_inv _ := rfl

/-- `Image` is well defined on members: families with the same descent to the
members have the same image. -/
theorem image_congr_descend (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem)
    {X : S} {F G : El Mem X → S} (same : descend r F = descend r G) :
    R.image X F = R.image X G := by
  rw [R.image_descends h r F, R.image_descends h r G, same]

/-! ## Extensionality and transport -/

/-- Reindexing a family along an evidence map between two sets with the same
members leaves its image unchanged. This is the computation `J` must perform
along an equality produced by extensionality. -/
theorem image_reindex (h : PropositionalMembership Mem) (hext : Extensional Mem) {X Y : S}
    (forth : ∀ z, Mem z X → Mem z Y) (back : ∀ z, Mem z Y → Mem z X) (F : El Mem Y → S) :
    R.image X (fun a => F (reindex forth a)) = R.image Y F := by
  apply hext
  intro y
  rw [nonempty_mem_image_iff, nonempty_mem_image_iff]
  constructor
  · rintro ⟨a, e⟩
    exact ⟨reindex forth a, e⟩
  · rintro ⟨b, e⟩
    exact ⟨reindex back b,
      (congrArg F (El.ext (a := reindex forth (reindex back b)) (b := b) h rfl)).trans e⟩

/-- Transport of a family on `El X` along an equality of sets. -/
def transportFamily {X Y : S} (e : X = Y) (F : El Mem X → S) : El Mem Y → S :=
  Eq.ndrec (motive := fun Z => El Mem Z → S) F e

theorem image_transportFamily {X Y : S} (e : X = Y) (F : El Mem X → S) :
    R.image Y (transportFamily e F) = R.image X F := by
  subst e
  rfl

/-- Transport along an equality of sets preserves the family: at each member
it is the value of the original family at the same member. -/
theorem transportFamily_eq_of_fst_eq (h : PropositionalMembership Mem) {X Y : S} (e : X = Y)
    (F : El Mem X → S) (b : El Mem Y) (a : El Mem X) (same : a.1 = b.1) :
    transportFamily e F b = F a := by
  subst e
  exact congrArg F (El.ext h same.symm)

/-- Along the equality given by extensionality, the transported family at a
member is the original family at that member. -/
theorem transportFamily_ext (h : PropositionalMembership Mem) (hext : Extensional Mem)
    {X Y : S} (coext : ∀ z, Nonempty (Mem z X) ↔ Nonempty (Mem z Y)) (F : El Mem X → S)
    {x : S} (q : Mem x Y) (p : Mem x X) :
    transportFamily (hext coext) F ⟨x, q⟩ = F ⟨x, p⟩ :=
  transportFamily_eq_of_fst_eq h (hext coext) F ⟨x, q⟩ ⟨x, p⟩ rfl

end DependentReplacement

end Mettapedia.TypeTheory.MaterialSets
