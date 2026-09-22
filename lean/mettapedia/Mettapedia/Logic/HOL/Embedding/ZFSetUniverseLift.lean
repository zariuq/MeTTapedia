import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts

/-!
# A larger set code for the entire lower-universe ZFSet carrier

The recursive pre-set universe lift descends to an injective, membership-
preserving map of actual ZF sets. Its range is a set one universe higher,
whose membership fibre is equivalent to the entire original ZFSet type.
This is not an internal universal set and requires no inaccessible-cardinal
hypothesis. Set-operation compatibility is stated for the actual operations
on each side, rather than operations defined by transporting the originals.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift

open ZFSetHenkinInterpretation ZFSetDependentProducts

universe u

theorem pset_lift_equiv (x y : PSet.{u}) :
    PSet.Equiv (PSet.Lift.{u, u + 1} x) (PSet.Lift.{u, u + 1} y) ↔ PSet.Equiv x y := by
  induction x generalizing y with
  | mk α f ih =>
      cases y with
      | mk β g =>
          change ((∀ a : ULift α, ∃ b : ULift β,
              PSet.Equiv (PSet.Lift (f a.down)) (PSet.Lift (g b.down))) ∧
            (∀ b : ULift β, ∃ a : ULift α,
              PSet.Equiv (PSet.Lift (f a.down)) (PSet.Lift (g b.down)))) ↔
            ((∀ a, ∃ b, PSet.Equiv (f a) (g b)) ∧ ∀ b, ∃ a, PSet.Equiv (f a) (g b))
          constructor
          · rintro ⟨forward, backward⟩
            constructor
            · intro a
              obtain ⟨b, related⟩ := forward ⟨a⟩
              exact ⟨b.down, (ih a (g b.down)).mp related⟩
            · intro b
              obtain ⟨a, related⟩ := backward ⟨b⟩
              exact ⟨a.down, (ih a.down (g b)).mp related⟩
          · rintro ⟨forward, backward⟩
            constructor
            · rintro ⟨a⟩
              obtain ⟨b, related⟩ := forward a
              exact ⟨⟨b⟩, (ih a (g b)).mpr related⟩
            · rintro ⟨b⟩
              obtain ⟨a, related⟩ := backward b
              exact ⟨⟨a⟩, (ih a (g b)).mpr related⟩

def lift (x : ZFSet.{u}) : ZFSet.{u + 1} :=
  Quotient.liftOn x (fun p => ZFSet.mk (PSet.Lift.{u, u + 1} p))
    (fun a b equal => ZFSet.sound ((pset_lift_equiv a b).mpr equal))

theorem lift_mk (x : PSet.{u}) :
    lift (ZFSet.mk x) = ZFSet.mk (PSet.Lift.{u, u + 1} x) := rfl

theorem lift_injective : Function.Injective lift.{u} := by
  intro x y equal
  induction x using Quotient.inductionOn with
  | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
          exact ZFSet.sound ((pset_lift_equiv x y).mp (ZFSet.exact equal))

theorem lift_mem_lift {x y : ZFSet.{u}} : lift x ∈ lift y ↔ x ∈ y := by
  induction x using Quotient.inductionOn with
  | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
          cases y with
          | mk β g =>
              change (∃ b : ULift β, PSet.Equiv (PSet.Lift x) (PSet.Lift (g b.down))) ↔
                ∃ b, PSet.Equiv x (g b)
              constructor
              · rintro ⟨b, related⟩
                exact ⟨b.down, (pset_lift_equiv x (g b.down)).mp related⟩
              · rintro ⟨b, related⟩
                exact ⟨⟨b⟩, (pset_lift_equiv x (g b)).mpr related⟩

/-- Every member of a lifted set is itself a lifted small set. -/
theorem mem_lift {x : ZFSet.{u + 1}} {y : ZFSet.{u}} :
    x ∈ lift y ↔ ∃ z ∈ y, lift z = x := by
  induction y using Quotient.inductionOn with
  | _ y =>
      induction x using Quotient.inductionOn with
      | _ x =>
          cases y with
          | mk β g =>
              constructor
              · intro member
                change ∃ b : ULift β, PSet.Equiv x (PSet.Lift (g b.down)) at member
                obtain ⟨b, related⟩ := member
                refine ⟨ZFSet.mk (g b.down), ?_, ZFSet.sound related.symm⟩
                exact PSet.Mem.mk g b.down
              · rintro ⟨z, hz, equal⟩
                rw [← equal]
                exact lift_mem_lift.mpr hz

theorem lift_subset_lift {x y : ZFSet.{u}} : lift x ⊆ lift y ↔ x ⊆ y := by
  constructor
  · intro below z hz
    exact lift_mem_lift.mp (below (lift_mem_lift.mpr hz))
  · intro below z hz
    obtain ⟨w, hw, rfl⟩ := mem_lift.mp hz
    exact lift_mem_lift.mpr (below hw)

/-! ## Actual set-operation preservation -/

theorem lift_empty : lift (∅ : ZFSet.{u}) = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_lift, ZFSet.notMem_empty, false_and, exists_false]

theorem lift_unorderedPair (a b : ZFSet.{u}) :
    lift ({a, b} : ZFSet.{u}) = ({lift a, lift b} : ZFSet.{u + 1}) := by
  apply ZFSet.ext
  intro z
  rw [mem_lift, ZFSet.mem_pair]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases ZFSet.mem_pair.mp hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨a, ZFSet.mem_pair.mpr (Or.inl rfl), rfl⟩
    · exact ⟨b, ZFSet.mem_pair.mpr (Or.inr rfl), rfl⟩

theorem lift_singleton (a : ZFSet.{u}) : lift ({a} : ZFSet.{u}) = {lift a} := by
  apply ZFSet.ext
  intro z
  simp only [mem_lift, ZFSet.mem_singleton]
  constructor
  · rintro ⟨x, rfl, rfl⟩
    rfl
  · intro equal
    exact ⟨a, rfl, equal.symm⟩

theorem lift_pair (a b : ZFSet.{u}) : lift (ZFSet.pair a b) = ZFSet.pair (lift a) (lift b) := by
  unfold ZFSet.pair
  rw [lift_unorderedPair, lift_singleton, lift_unorderedPair]

theorem lift_sUnion (a : ZFSet.{u}) : lift (ZFSet.sUnion a) = ZFSet.sUnion (lift a) := by
  apply ZFSet.ext
  intro z
  rw [mem_lift, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hx⟩ := ZFSet.mem_sUnion.mp hx
    exact ⟨lift b, lift_mem_lift.mpr hb, lift_mem_lift.mpr hx⟩
  · rintro ⟨b, hb, hz⟩
    obtain ⟨smallB, smallBmem, equalB⟩ := mem_lift.mp hb
    rw [← equalB] at hz
    obtain ⟨smallZ, smallZmem, equalZ⟩ := mem_lift.mp hz
    exact ⟨smallZ, ZFSet.mem_sUnion.mpr ⟨smallB, smallBmem, smallZmem⟩, equalZ⟩

theorem lift_separation (a : ZFSet.{u})
    (p : ZFSet.{u} → Prop) (q : ZFSet.{u + 1} → Prop)
    (agree : ∀ x ∈ a, p x ↔ q (lift x)) :
    lift (ZFSet.sep p a) = ZFSet.sep q (lift a) := by
  apply ZFSet.ext
  intro z
  rw [mem_lift, ZFSet.mem_sep]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨ha, hp⟩ := ZFSet.mem_sep.mp hx
    exact ⟨lift_mem_lift.mpr ha, (agree x ha).mp hp⟩
  · rintro ⟨hz, hq⟩
    obtain ⟨x, hx, rfl⟩ := mem_lift.mp hz
    exact ⟨x, ZFSet.mem_sep.mpr ⟨hx, (agree x hx).mpr hq⟩, rfl⟩

/-- Even a larger-indexed subset of a lifted set comes from a small subset.
Separation on the original bound constructs that subset explicitly. -/
theorem subset_lift_classification {a : ZFSet.{u}} {b : ZFSet.{u + 1}} :
    b ⊆ lift a ↔ ∃ c : ZFSet.{u}, c ⊆ a ∧ lift c = b := by
  constructor
  · intro below
    let c : ZFSet.{u} := ZFSet.sep (fun x => lift x ∈ b) a
    refine ⟨c, (fun _ hc => (ZFSet.mem_sep.mp hc).1), ?_⟩
    change lift (ZFSet.sep (fun x => lift x ∈ b) a) = b
    rw [lift_separation a (fun x => lift x ∈ b) (fun x => x ∈ b)
      (fun _ _ => Iff.rfl)]
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨And.right, fun hz => ⟨below hz, hz⟩⟩
  · rintro ⟨c, below, rfl⟩
    exact lift_subset_lift.mpr below

theorem lift_powerset (a : ZFSet.{u}) : lift (ZFSet.powerset a) = ZFSet.powerset (lift a) := by
  apply ZFSet.ext
  intro z
  rw [mem_lift, ZFSet.mem_powerset, subset_lift_classification]
  constructor <;> rintro ⟨b, hb, equal⟩
  · exact ⟨b, ZFSet.mem_powerset.mp hb, equal⟩
  · exact ⟨b, ZFSet.mem_powerset.mpr hb, equal⟩

theorem lift_replacement (a : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u})
    (F : ZFSet.{u + 1} → ZFSet.{u + 1})
    (agree : ∀ x ∈ a, F (lift x) = lift (f x)) :
    lift (replacement a f) = replacement (lift a) F := by
  apply ZFSet.ext
  intro z
  rw [mem_lift, mem_replacement]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_replacement.mp hy
    exact ⟨lift x, lift_mem_lift.mpr hx, agree x hx⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_lift.mp hx
    exact ⟨f w, mem_replacement.mpr ⟨w, hw, rfl⟩, (agree w hw).symm⟩

/-! ## The larger carrier code and its actual decoding -/

noncomputable def carrierCode : ZFSet.{u + 1} := ZFSet.range lift.{u}

theorem mem_carrierCode {x : ZFSet.{u + 1}} : x ∈ carrierCode ↔ ∃ y, lift y = x :=
  ZFSet.mem_range

def encode (x : ZFSet.{u}) : Elements carrierCode.{u} :=
  ⟨lift x, mem_carrierCode.mpr ⟨x, rfl⟩⟩

theorem encode_bijective : Function.Bijective encode.{u} := by
  constructor
  · intro x y equal
    exact lift_injective (congrArg Subtype.val equal)
  · intro x
    obtain ⟨y, equal⟩ := mem_carrierCode.mp x.2
    exact ⟨y, Subtype.ext equal⟩

noncomputable def carrierEquiv : Elements carrierCode.{u} ≃ ZFSet.{u} :=
  (Equiv.ofBijective encode encode_bijective).symm

theorem decode_encode (x : ZFSet.{u}) : carrierEquiv (encode x) = x :=
  carrierEquiv.apply_symm_apply x

theorem lift_decode (x : Elements carrierCode.{u}) : lift (carrierEquiv x) = x.1 :=
  congrArg Subtype.val (carrierEquiv.symm_apply_apply x)

noncomputable def lowerValue (x : ZFSet.{u + 1}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ carrierCode then carrierEquiv ⟨x, hx⟩ else ∅

theorem lift_lowerValue {x : ZFSet.{u + 1}} (hx : x ∈ carrierCode) :
    lift (lowerValue x) = x := by
  simp only [lowerValue, dif_pos hx]
  exact lift_decode ⟨x, hx⟩

theorem lowerValue_lift (x : ZFSet.{u}) : lowerValue (lift x) = x :=
  lift_injective (lift_lowerValue (mem_carrierCode.mpr ⟨x, rfl⟩))

theorem carrierCode_transitive : ZFSet.IsTransitive carrierCode.{u} := by
  intro x hx z hz
  obtain ⟨a, rfl⟩ := mem_carrierCode.mp hx
  obtain ⟨b, _, equal⟩ := mem_lift.mp hz
  exact mem_carrierCode.mpr ⟨b, equal⟩

/-- The larger set of all lifted small sets is closed under the actual
universe operations, including larger functions whose values stay in it. -/
theorem carrierCode_closed : ZFSetUniverseClosure.Closed carrierCode.{u} where
  transitive := carrierCode_transitive
  union_mem := by
    intro a ha
    obtain ⟨small, rfl⟩ := mem_carrierCode.mp ha
    exact mem_carrierCode.mpr ⟨ZFSet.sUnion small, lift_sUnion small⟩
  power_mem := by
    intro a ha
    obtain ⟨small, rfl⟩ := mem_carrierCode.mp ha
    exact mem_carrierCode.mpr ⟨ZFSet.powerset small, lift_powerset small⟩
  replacement_mem := by
    intro a ha F hF
    obtain ⟨small, rfl⟩ := mem_carrierCode.mp ha
    let f : ZFSet.{u} → ZFSet.{u} := fun x => lowerValue (F (lift x))
    have agree : ∀ x ∈ small, F (lift x) = lift (f x) := by
      intro x hx
      exact (lift_lowerValue (hF (lift x) (lift_mem_lift.mpr hx))).symm
    exact mem_carrierCode.mpr ⟨replacement small f, lift_replacement small f F agree⟩

/-! ## Actual operations on the decoded full carrier -/

theorem membership_decode (x y : Elements carrierCode.{u}) :
    x.1 ∈ y.1 ↔ carrierEquiv x ∈ carrierEquiv y := by
  rw [← lift_decode x, ← lift_decode y]
  exact lift_mem_lift

def carrierEmpty : Elements carrierCode.{u} :=
  ⟨∅, mem_carrierCode.mpr ⟨∅, lift_empty⟩⟩

noncomputable def carrierUnion (a : Elements carrierCode.{u}) : Elements carrierCode.{u} :=
  ⟨ZFSet.sUnion a.1, carrierCode_closed.union_mem a.2⟩

noncomputable def carrierPower (a : Elements carrierCode.{u}) : Elements carrierCode.{u} :=
  ⟨ZFSet.powerset a.1, carrierCode_closed.power_mem a.2⟩

noncomputable def carrierSeparation (a : Elements carrierCode.{u})
    (q : ZFSet.{u + 1} → Prop) : Elements carrierCode.{u} :=
  ⟨ZFSet.sep q a.1, carrierCode_closed.separation_mem a.2 q⟩

noncomputable def extendCarrierMap (F : Elements carrierCode.{u} → Elements carrierCode.{u})
    (x : ZFSet.{u + 1}) : ZFSet.{u + 1} := by
  classical
  exact if hx : x ∈ carrierCode then (F ⟨x, hx⟩).1 else ∅

theorem extendCarrierMap_at (F : Elements carrierCode.{u} → Elements carrierCode.{u})
    (x : Elements carrierCode.{u}) : extendCarrierMap F x.1 = (F x).1 := by
  simp only [extendCarrierMap, dif_pos x.2]

noncomputable def carrierReplacement (a : Elements carrierCode.{u})
    (F : Elements carrierCode.{u} → Elements carrierCode.{u}) : Elements carrierCode.{u} :=
  ⟨replacement a.1 (extendCarrierMap F), carrierCode_closed.replacement_mem a.2 _
    (fun x hx => by
      have small : x ∈ carrierCode := carrierCode_transitive _ a.2 hx
      rw [extendCarrierMap_at F ⟨x, small⟩]
      exact (F ⟨x, small⟩).2)⟩

theorem decode_empty : carrierEquiv carrierEmpty.{u} = ∅ := by
  apply lift_injective
  rw [lift_decode, lift_empty]
  rfl

theorem decode_union (a : Elements carrierCode.{u}) :
    carrierEquiv (carrierUnion a) = ZFSet.sUnion (carrierEquiv a) := by
  apply lift_injective
  rw [lift_decode, lift_sUnion, lift_decode]
  rfl

theorem decode_power (a : Elements carrierCode.{u}) :
    carrierEquiv (carrierPower a) = ZFSet.powerset (carrierEquiv a) := by
  apply lift_injective
  rw [lift_decode, lift_powerset, lift_decode]
  rfl

theorem decode_separation (a : Elements carrierCode.{u}) (q : ZFSet.{u + 1} → Prop) :
    carrierEquiv (carrierSeparation a q) = ZFSet.sep (fun x => q (lift x)) (carrierEquiv a) := by
  apply lift_injective
  rw [lift_decode, lift_separation (carrierEquiv a) (fun x => q (lift x)) q
    (fun _ _ => Iff.rfl), lift_decode]
  rfl

theorem decode_replacement (a : Elements carrierCode.{u})
    (F : Elements carrierCode.{u} → Elements carrierCode.{u}) :
    carrierEquiv (carrierReplacement a F) =
      replacement (carrierEquiv a) (fun x => carrierEquiv (F (encode x))) := by
  apply lift_injective
  rw [lift_decode]
  have agree : ∀ x ∈ carrierEquiv a,
      extendCarrierMap F (lift x) = lift (carrierEquiv (F (encode x))) := by
    intro x _
    rw [lift_decode]
    exact extendCarrierMap_at F (encode x)
  rw [lift_replacement _ _ (extendCarrierMap F) agree, lift_decode]
  rfl

theorem carrier_not_member : carrierCode.{u} ∉ carrierCode.{u} := ZFSet.mem_irrefl _

theorem lift_not_surjective : ¬ Function.Surjective lift.{u} := by
  intro onto
  exact carrier_not_member (mem_carrierCode.mpr (onto carrierCode))

/-- No same-level set can even have a decoding bijective with the whole
external ZFSet carrier: its image would produce an internal universal set. -/
theorem no_same_level_carrier_code :
    ¬ ∃ a : ZFSet.{u}, Nonempty (Elements a ≃ ZFSet.{u}) := by
  rintro ⟨a, ⟨equivalence⟩⟩
  let universal : ZFSet.{u} := ZFSet.range equivalence
  have selfMember : universal ∈ universal :=
    ZFSet.mem_range.mpr (equivalence.surjective universal)
  exact ZFSet.mem_irrefl _ selfMember

#print axioms pset_lift_equiv
#print axioms lift_injective
#print axioms lift_mem_lift
#print axioms mem_lift
#print axioms lift_pair
#print axioms lift_sUnion
#print axioms lift_separation
#print axioms subset_lift_classification
#print axioms lift_powerset
#print axioms lift_replacement
#print axioms carrierEquiv
#print axioms carrierCode_closed
#print axioms membership_decode
#print axioms decode_empty
#print axioms decode_union
#print axioms decode_power
#print axioms decode_separation
#print axioms decode_replacement
#print axioms no_same_level_carrier_code
#print axioms lift_not_surjective

end Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift
