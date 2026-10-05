import Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedMaterialDecoder
import Mettapedia.TypeTheory.GeneratedUniverseCoherence

/-!
# Successor comparisons of actual presented material types

Lifting a presented material type constructs a larger graph and its explicit
member decoder. Semantic comparisons retain dependent base and fibre data.
The material comparison is equality of encoded values after universe lifting;
graphs themselves may have different node carriers and are compared by
bisimilarity. This is successor coherence, not an internal closure operator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeCumulativity

open Mettapedia.TypeTheory.FamilyEnclosingUniverse

universe u v w

def liftModel {T : Type u} (model : PresentedType T) : PresentedType (ULift.{u + 1, u} T) where
  graph := model.graph.lift
  decode := (HSet.liftedMembersEquiv model.carrier).symm.trans
    (model.decode.trans Equiv.ulift.symm)

theorem liftModel_carrier {T : Type u} (model : PresentedType T) :
    (liftModel model).carrier = HSet.lift model.carrier := rfl

theorem liftModel_value {T : Type u} (model : PresentedType T) (term : ULift.{u + 1, u} T) :
    (liftModel model).value term = HSet.lift (model.value term.down) := rfl

private def piBaseEquiv {α : Type u} {β : Type v} (base : α ≃ β) (family : β → Sort w) :
    (∀ a, family (base a)) ≃ (∀ b, family b) where
  toFun term b := cast (congrArg family (base.apply_symm_apply b)) (term (base.symm b))
  invFun term a := term (base a)
  left_inv term := by
    funext a
    exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq term (base.symm_apply_apply a)))
  right_inv term := by
    funext b
    exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq term (base.apply_symm_apply b)))

private theorem piBaseEquiv_apply {α : Type u} {β : Type v} (base : α ≃ β) (family : β → Sort w)
    (term : ∀ a, family (base a)) (a : α) :
    piBaseEquiv base family term (base a) = term a :=
  eq_of_heq ((cast_heq _ _).trans (congr_arg_heq term (base.symm_apply_apply a)))

def piEquiv {A : Type u} {A' : Type v} {B : A → Type u} {B' : A' → Type v}
    (base : A' ≃ A) (fibres : ∀ a', B' a' ≃ B (base a')) :
    (∀ a', B' a') ≃ (∀ a, B a) :=
  (Equiv.piCongrRight fibres).trans (piBaseEquiv base B)

theorem piEquiv_apply {A : Type u} {A' : Type v} {B : A → Type u} {B' : A' → Type v}
    (base : A' ≃ A) (fibres : ∀ a', B' a' ≃ B (base a'))
    (term : ∀ a', B' a') (a' : A') :
    piEquiv base fibres term (base a') = fibres a' (term a') :=
  piBaseEquiv_apply base B (fun a' => fibres a' (term a')) a'

private def sigmaBaseEquiv {α : Type u} {β : Type v} (base : α ≃ β) (family : β → Type w) :
    (Σ a, family (base a)) ≃ (Σ b, family b) where
  toFun value := ⟨base value.1, value.2⟩
  invFun value :=
    ⟨base.symm value.1, cast (congrArg family (base.apply_symm_apply value.1).symm) value.2⟩
  left_inv value := Sigma.ext (base.symm_apply_apply value.1) (cast_heq _ _)
  right_inv value := Sigma.ext (base.apply_symm_apply value.1) (cast_heq _ _)

private def sigmaFibreEquiv {α : Type v} {first : α → Type v} {second : α → Type u}
    (fibres : ∀ a, first a ≃ second a) : Sigma first ≃ Sigma second where
  toFun value := ⟨value.1, fibres value.1 value.2⟩
  invFun value := ⟨value.1, (fibres value.1).symm value.2⟩
  left_inv value := congrArg (Sigma.mk value.1) ((fibres value.1).symm_apply_apply value.2)
  right_inv value := congrArg (Sigma.mk value.1) ((fibres value.1).apply_symm_apply value.2)

def sigmaEquiv {A : Type u} {A' : Type v} {B : A → Type u} {B' : A' → Type v}
    (base : A' ≃ A) (fibres : ∀ a', B' a' ≃ B (base a')) : Sigma B' ≃ Sigma B :=
  (sigmaFibreEquiv fibres).trans (sigmaBaseEquiv base B)

def identityEquiv {A : Type u} {A' : Type v} (base : A' ≃ A) (left right : A) :
    ULift.{v, 0} (PLift (base.symm left = base.symm right)) ≃ ULift.{u, 0} (PLift (left = right)) where
  toFun witness := ⟨⟨(base.apply_symm_apply left).symm.trans
    ((congrArg base witness.down.down).trans (base.apply_symm_apply right))⟩⟩
  invFun witness := ⟨⟨congrArg base.symm witness.down.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace Trees

variable {A : Type u} {A' : Type v} {B : A → Type u} {B' : A' → Type v}
variable (base : A' ≃ A) (fibres : ∀ a', B' a' ≃ B (base a'))

def lower : WTree A' B' → WTree A B
  | .sup shape children => .sup (base shape) (fun p => lower (children ((fibres shape).symm p)))

def raise : WTree A B → WTree A' B'
  | .sup shape children => .sup (base.symm shape) (fun p =>
      raise (children (cast (congrArg B (base.apply_symm_apply shape)) (fibres (base.symm shape) p))))

private theorem sup_eq_of_cast {S : Type u} {P : S → Type u} {first second : S}
    (same : first = second) (left : P first → WTree S P) (right : P second → WTree S P)
    (children : ∀ p, left p = right (cast (congrArg P same) p)) :
    WTree.sup first left = WTree.sup second right := by
  cases same
  exact congrArg (WTree.sup first) (funext children)

private theorem fibre_cast {first second : A'} (same : first = second) (term : B' first) :
    cast (congrArg (fun a' => B (base a')) same) (fibres first term) =
      fibres second (cast (congrArg B' same) term) := by
  cases same
  rfl

theorem lower_raise (tree : WTree A B) : lower base fibres (raise base fibres tree) = tree := by
  induction tree with
  | sup shape children earlier =>
    simp only [lower, raise]
    apply sup_eq_of_cast (base.apply_symm_apply shape)
    intro p
    simpa only [Equiv.apply_symm_apply] using
      earlier (cast (congrArg B (base.apply_symm_apply shape)) p)

theorem raise_lower (tree : WTree A' B') : raise base fibres (lower base fibres tree) = tree := by
  induction tree with
  | sup shape children earlier =>
    simp only [lower, raise]
    apply sup_eq_of_cast (base.symm_apply_apply shape)
    intro p
    have index : (fibres shape).symm
        (cast (congrArg B (base.apply_symm_apply (base shape))) (fibres (base.symm (base shape)) p)) =
        cast (congrArg B' (base.symm_apply_apply shape)) p :=
      (congrArg (fibres shape).symm (fibre_cast base fibres (base.symm_apply_apply shape) p)).trans
        ((fibres shape).symm_apply_apply _)
    rw [index]
    exact earlier _

def equiv : WTree A' B' ≃ WTree A B where
  toFun := lower base fibres
  invFun := raise base fibres
  left_inv := raise_lower base fibres
  right_inv := lower_raise base fibres

end Trees

section MaterialComparison

variable {T : Type u} {T' : Type (u + 1)}
variable (original : PresentedType T) (upper : PresentedType T') (comparison : T' ≃ T)

theorem carrier_eq_lift_of_values
    (values : ∀ term, upper.value term = HSet.lift (original.value (comparison term))) :
    upper.carrier = HSet.lift original.carrier := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    let term := upper.decode ⟨value, member⟩
    exact HSet.mem_lift_iff.mpr ⟨original.value (comparison term), original.value_mem _,
      (values term).symm.trans (upper.value_decode ⟨value, member⟩)⟩
  · intro member
    obtain ⟨old, oldMember, same⟩ := HSet.mem_lift_iff.mp member
    let term := comparison.symm (original.decode ⟨old, oldMember⟩)
    have encoded : upper.value term = value := by
      rw [values, Equiv.apply_symm_apply]
      exact (congrArg HSet.lift (original.value_decode ⟨old, oldMember⟩)).trans same
    exact encoded ▸ upper.value_mem term

/-- Both inverse operations use the existing actual decoders. The following
value law identifies this equivalence with the material universe embedding. -/
def memberEquiv : {value : HSet.{u + 1} // value ∈ upper.carrier} ≃
    {value : HSet.{u} // value ∈ original.carrier} :=
  (upper.decode.trans comparison).trans original.decode.symm

theorem memberEquiv_value
    (values : ∀ term, upper.value term = HSet.lift (original.value (comparison term)))
    (member : {value : HSet.{u + 1} // value ∈ upper.carrier}) :
    HSet.lift (memberEquiv original upper comparison member).1 = member.1 :=
  (values (upper.decode member)).symm.trans (upper.value_decode member)

theorem memberEquiv_symm_value
    (values : ∀ term, upper.value term = HSet.lift (original.value (comparison term)))
    (member : {value : HSet.{u} // value ∈ original.carrier}) :
    ((memberEquiv original upper comparison).symm member).1 = HSet.lift member.1 := by
  change upper.value (comparison.symm (original.decode member)) = HSet.lift member.1
  rw [values, Equiv.apply_symm_apply]
  exact congrArg HSet.lift (original.value_decode member)

theorem decode_memberEquiv (member : {value : HSet.{u + 1} // value ∈ upper.carrier}) :
    original.decode (memberEquiv original upper comparison member) = comparison (upper.decode member) :=
  original.decode.apply_symm_apply _

theorem termGraph_bisimilar
    (values : ∀ term, upper.value term = HSet.lift (original.value (comparison term))) (term : T') :
    upper.termGraph term ≈ (original.termGraph (comparison term)).lift := by
  apply HSet.mk_eq_mk_iff.mp
  rw [← HSet.lift_mk, PresentedType.mk_termGraph, PresentedType.mk_termGraph, values]

end MaterialComparison

section Constructors

variable {A : Type u} {A' : Type (u + 1)} {B : A → Type u} {B' : A' → Type (u + 1)}
variable (domain : PresentedType A) (fibres : ∀ a, PresentedType (B a))
variable (upperDomain : PresentedType A') (upperFibres : ∀ a', PresentedType (B' a'))
variable (base : A' ≃ A) (family : ∀ a', B' a' ≃ B (base a'))
variable (domainValues : ∀ a', upperDomain.value a' = HSet.lift (domain.value (base a')))
variable (fibreValues : ∀ a' b', (upperFibres a').value b' =
  HSet.lift ((fibres (base a')).value (family a' b')))

include domainValues fibreValues in
theorem product_value (term : ∀ a', B' a') :
    (PresentedType.product upperDomain upperFibres).value term =
      HSet.lift ((PresentedType.product domain fibres).value (piEquiv base family term)) := by
  rw [PresentedType.product_value, PresentedType.product_value]
  have row (a' : A') :
      HSet.lift (HSet.kpair (domain.value (base a'))
        ((fibres (base a')).value (piEquiv base family term (base a')))) =
        HSet.kpair (upperDomain.value a') ((upperFibres a').value (term a')) := by
    rw [HSet.lift_kpair, piEquiv_apply, ← domainValues, ← fibreValues]
  apply HSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨a', same⟩ := (PresentedType.mem_functionGraph_iff upperDomain upperFibres term value).mp member
    exact HSet.mem_lift_iff.mpr ⟨_,
      (PresentedType.mem_functionGraph_iff domain fibres _ _).mpr ⟨base a', rfl⟩,
      (row a').trans same⟩
  · intro member
    obtain ⟨old, oldMember, same⟩ := HSet.mem_lift_iff.mp member
    obtain ⟨a, oldRow⟩ := (PresentedType.mem_functionGraph_iff domain fibres _ _).mp oldMember
    obtain ⟨a', rfl⟩ := base.surjective a
    exact (PresentedType.mem_functionGraph_iff upperDomain upperFibres term value).mpr
      ⟨a', (row a').symm.trans ((congrArg HSet.lift oldRow).trans same)⟩

include domainValues fibreValues in
theorem sum_value (term : Sigma B') :
    (PresentedType.sum upperDomain upperFibres).value term =
      HSet.lift ((PresentedType.sum domain fibres).value (sigmaEquiv base family term)) := by
  rw [PresentedType.sum_value, PresentedType.sum_value, HSet.lift_kpair]
  exact congrArg₂ HSet.kpair (domainValues term.1) (fibreValues term.1 term.2)

theorem identity_value (left right : A)
    (witness : ULift.{u + 1, 0} (PLift (base.symm left = base.symm right))) :
    (PresentedType.identity upperDomain (base.symm left) (base.symm right)).value witness =
      HSet.lift ((PresentedType.identity domain left right).value (identityEquiv base left right witness)) := by
  rw [PresentedType.identity_value, PresentedType.identity_value, HSet.lift_empty]

include domainValues in
private theorem shapeTag_value (a' : A') :
    PresentedType.W.shapeTag upperDomain a' =
      HSet.lift (PresentedType.W.shapeTag domain (base a')) := by
  rw [PresentedType.W.shapeTag, PresentedType.W.shapeTag, HSet.lift_kpair, HSet.lift_empty, domainValues]

include domainValues fibreValues in
private theorem positionTag_value (a' : A') (p' : B' a') :
    PresentedType.W.positionTag upperDomain upperFibres a' p' =
      HSet.lift (PresentedType.W.positionTag domain fibres (base a') (family a' p')) := by
  rw [PresentedType.W.positionTag, PresentedType.W.positionTag, HSet.lift_kpair, HSet.lift_singleton,
    HSet.lift_empty, HSet.lift_kpair, domainValues, fibreValues]

include domainValues fibreValues in
theorem tree_encode_value (tree : WTree A' B') :
    PresentedType.W.encode upperDomain upperFibres tree =
      HSet.lift (PresentedType.W.encode domain fibres (Trees.lower base family tree)) := by
  induction tree with
  | sup a' children earlier =>
    have shapeRow :
        HSet.kpair (PresentedType.W.shapeTag upperDomain a') ∅ =
          HSet.lift (HSet.kpair (PresentedType.W.shapeTag domain (base a')) ∅) := by
      rw [HSet.lift_kpair, HSet.lift_empty, shapeTag_value domain upperDomain base domainValues]
    have positionRow (p' : B' a') :
        HSet.kpair (PresentedType.W.positionTag upperDomain upperFibres a' p')
          (PresentedType.W.encode upperDomain upperFibres (children p')) =
        HSet.lift (HSet.kpair (PresentedType.W.positionTag domain fibres (base a') (family a' p'))
          (PresentedType.W.encode domain fibres (Trees.lower base family (children p')))) := by
      rw [HSet.lift_kpair,
        positionTag_value domain fibres upperDomain upperFibres base family domainValues fibreValues,
        earlier p']
    apply HSet.ext
    intro value
    rw [PresentedType.W.mem_encode_sup_iff, Trees.lower]
    constructor
    · rintro (shape | ⟨p', position⟩)
      · exact HSet.mem_lift_iff.mpr ⟨_,
          (PresentedType.W.mem_encode_sup_iff domain fibres _ _ _).mpr (Or.inl rfl),
          shapeRow.symm.trans shape.symm⟩
      · exact HSet.mem_lift_iff.mpr ⟨_,
          (PresentedType.W.mem_encode_sup_iff domain fibres _ _ _).mpr
            (Or.inr ⟨family a' p', by rw [Equiv.symm_apply_apply]⟩),
          (positionRow p').symm.trans position.symm⟩
    · intro member
      obtain ⟨old, oldMember, same⟩ := HSet.mem_lift_iff.mp member
      rcases (PresentedType.W.mem_encode_sup_iff domain fibres _ _ _).mp oldMember with shape | ⟨p, position⟩
      · exact Or.inl ((same.symm.trans (congrArg HSet.lift shape)).trans shapeRow.symm)
      · refine Or.inr ⟨(family a').symm p, ?_⟩
        exact (same.symm.trans (congrArg HSet.lift position)).trans
          (by simpa only [Equiv.apply_symm_apply] using (positionRow ((family a').symm p)).symm)

include domainValues fibreValues in
theorem w_value (tree : WTree A' B') :
    (PresentedType.W.model upperDomain upperFibres).value tree =
      HSet.lift ((PresentedType.W.model domain fibres).value (Trees.equiv base family tree)) := by
  rw [PresentedType.W.model_value, PresentedType.W.model_value]
  exact tree_encode_value domain fibres upperDomain upperFibres base family domainValues fibreValues tree

end Constructors

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeCumulativity
