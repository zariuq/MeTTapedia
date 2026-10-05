import Mettapedia.TypeTheory.PresheafSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentity

/-!
# Full dependent discrete identity elimination across successor sites

The raised context contains two actual endpoint coordinates and the actual
material singleton witness. Explicit natural maps raise and lower all three
coordinates. Their inverse, diagonal and readout squares transport arbitrary
natural motives and reflexive methods. Full dependent J and its computation
are compared with the independently formed upper identity interpretation.

The scope is the discrete identity profile and translation from a lower
site to its successor. No upper motive is assumed to descend to the lower
bound, and these laws do not install UIP or reflection in native syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentitySiteLift

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent (compose identity)

universe u
variable {C : Type u} [Category.{u} C]
variable (P : Cᵒᵖ ⥤ Type u) (domain : P.Elements ⥤ Type u)

abbrev upperDomain := PresheafSiteLift.family P domain
abbrev lowerContext := DisplayedPresheafIdentity.identityContext domain
abbrev upperContext := DisplayedPresheafIdentity.identityContext (upperDomain P domain)

def raiseWitness {T : Type u} {first second : T} (witness : PresheafIdentityWitness.Witness first second) :
    PresheafIdentityWitness.Witness (ULift.up first : ULift.{u + 1, u} T) (ULift.up second) :=
  PresheafIdentityWitness.encode (congrArg ULift.up (PresheafIdentityWitness.decode witness))

def lowerWitness {T : Type u} {first second : ULift.{u + 1, u} T}
    (witness : PresheafIdentityWitness.Witness first second) : PresheafIdentityWitness.Witness first.down second.down :=
  PresheafIdentityWitness.encode (congrArg ULift.down (PresheafIdentityWitness.decode witness))

theorem lower_raise_witness {T : Type u} {first second : T} (witness : PresheafIdentityWitness.Witness first second) :
    lowerWitness (raiseWitness witness) = witness := Subsingleton.elim _ _

theorem raise_lower_witness {T : Type u} {first second : ULift.{u + 1, u} T}
    (witness : PresheafIdentityWitness.Witness first second) : raiseWitness (lowerWitness witness) = witness :=
  Subsingleton.elim _ _

private theorem witness_eq {T : Type u} {first second : T}
    (left right : PresheafIdentityWitness.Witness first second) : left = right := Subsingleton.elim _ _

/-- Actual raising retains the base receipt, both endpoint values and a
constructed witness, rather than retaining only endpoint support. -/
def contextTo : NatTrans (PresheafSiteLift.base (lowerContext P domain)) (upperContext P domain) where
  app _ := TypeCat.ofHom fun receipt =>
    ⟨⟨⟨ULift.up receipt.down.1.1.1, ULift.up receipt.down.1.1.2⟩, ULift.up receipt.down.1.2⟩, raiseWitness receipt.down.2⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Sigma.ext rfl
    exact heq_of_eq (witness_eq _ _)

def contextFrom : NatTrans (upperContext P domain) (PresheafSiteLift.base (lowerContext P domain)) where
  app _ := TypeCat.ofHom fun receipt =>
    ULift.up ⟨⟨⟨receipt.1.1.1.down, receipt.1.1.2.down⟩, receipt.1.2.down⟩, lowerWitness receipt.2⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply congrArg ULift.up
    apply Sigma.ext rfl
    exact heq_of_eq (witness_eq _ _)

theorem context_left : compose (contextTo P domain) (contextFrom P domain) = identity (PresheafSiteLift.base (lowerContext P domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  apply congrArg ULift.up
  exact Sigma.ext rfl (heq_of_eq (lower_raise_witness receipt.down.2))

theorem context_right : compose (contextFrom P domain) (contextTo P domain) = identity (upperContext P domain) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  exact Sigma.ext rfl (heq_of_eq (raise_lower_witness receipt.2))

def contextEquiv (world : (PresheafSiteLift.Site C)ᵒᵖ) :
    (PresheafSiteLift.base (lowerContext P domain)).obj world ≃ (upperContext P domain).obj world where
  toFun := (contextTo P domain).app world
  invFun := (contextFrom P domain).app world
  left_inv receipt := congrArg ULift.up (Sigma.ext rfl (heq_of_eq (lower_raise_witness receipt.down.2)))
  right_inv receipt := Sigma.ext rfl (heq_of_eq (raise_lower_witness receipt.2))

theorem diagonal_to :
    compose (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.diagonal domain)) (contextTo P domain) =
      compose (PresheafSiteLift.comprehensionTo P domain) (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  apply Sigma.ext rfl
  exact heq_of_eq (witness_eq _ _)

theorem diagonal_from :
    compose (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) (contextFrom P domain) =
      compose (PresheafSiteLift.comprehensionFrom P domain) (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.diagonal domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  apply congrArg ULift.up
  apply Sigma.ext rfl
  exact heq_of_eq (witness_eq _ _)

theorem readLeft_to :
    compose (contextTo P domain) (DisplayedPresheafIdentity.readLeft (upperDomain P domain)) =
      compose (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.readLeft domain)) (PresheafSiteLift.comprehensionTo P domain) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem readLeft_from :
    compose (DisplayedPresheafIdentity.readLeft (upperDomain P domain)) (PresheafSiteLift.comprehensionFrom P domain) =
      compose (contextFrom P domain) (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.readLeft domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

variable (motive : (lowerContext P domain).Elements ⥤ Type u)
variable (method : (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain) motive).sections)

def upperMotive : (upperContext P domain).Elements ⥤ Type (u + 1) :=
  PowerClassPresheafProducts.reindex (contextFrom P domain) (PresheafSiteLift.family (lowerContext P domain) motive)

theorem reflexiveMotive :
    PowerClassPresheafProducts.reindex (PresheafSiteLift.comprehensionFrom P domain)
      (PresheafSiteLift.family (totalSpace domain)
        (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain) motive)) =
      PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) (upperMotive P domain motive) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def upperMethod :
    (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) (upperMotive P domain motive)).sections :=
  PowerClassPresheafProducts.CP.castSection (reflexiveMotive P domain motive)
    (PowerClassPresheafProducts.reindexSection (PresheafSiteLift.comprehensionFrom P domain)
      (PresheafSiteLift.family (totalSpace domain) (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain) motive))
      (PresheafSiteLift.raiseTerm (totalSpace domain) (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain) motive) method))

private theorem up_heq {A B : Type u} {first : A} {second : B} (same : HEq first second) :
    HEq (ULift.up first : ULift.{u + 1, u} A) (ULift.up second : ULift.{u + 1, u} B) := by
  cases same
  rfl

/-- Full dependent J retains both endpoints and the constructed material
witness, and agrees as a natural section with raising the lower eliminator. -/
theorem J_lift : DisplayedPresheafIdentity.J (upperDomain P domain) (upperMotive P domain motive)
      (upperMethod P domain motive method) =
    PowerClassPresheafProducts.reindexSection (contextFrom P domain)
      (PresheafSiteLift.family (lowerContext P domain) motive)
      (PresheafSiteLift.raiseTerm (lowerContext P domain) motive (DisplayedPresheafIdentity.J domain motive method)) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  have upper := DisplayedPresheafIdentity.J_value_heq (upperDomain P domain) (upperMotive P domain motive)
    (upperMethod P domain motive method) point
  have castMethod := PowerClassPresheafProducts.CP.castSection_value (reflexiveMotive P domain motive)
    (PowerClassPresheafProducts.reindexSection (PresheafSiteLift.comprehensionFrom P domain)
      (PresheafSiteLift.family (totalSpace domain) (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain) motive))
      (PresheafSiteLift.raiseTerm (totalSpace domain) (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain) motive) method))
    ((PowerClassPresheafProducts.elementMap (DisplayedPresheafIdentity.readLeft (upperDomain P domain))).obj point)
  have lower := DisplayedPresheafIdentity.J_value_heq domain motive method
    ((PresheafSiteLift.elementsDown (lowerContext P domain)).obj ((PowerClassPresheafProducts.elementMap (contextFrom P domain)).obj point))
  exact upper.trans (castMethod.trans (up_heq lower).symm)

theorem J_beta_lift : PowerClassPresheafProducts.reindexSection (DisplayedPresheafIdentity.diagonal (upperDomain P domain))
      (upperMotive P domain motive)
      (PowerClassPresheafProducts.reindexSection (contextFrom P domain) (PresheafSiteLift.family (lowerContext P domain) motive)
        (PresheafSiteLift.raiseTerm (lowerContext P domain) motive (DisplayedPresheafIdentity.J domain motive method))) =
    upperMethod P domain motive method := by
  rw [← J_lift]
  exact DisplayedPresheafIdentity.J_beta _ _ _

section Substitution

variable {Q R : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)

/-- The actual raised comprehension change acts on its dependent receipt.
Its construction uses the two proved comprehension inverses. -/
def totalChange : NatTrans
    (totalSpace (upperDomain Q (PowerClassPresheafProducts.reindex change domain))) (totalSpace (upperDomain P domain)) :=
  compose (PresheafSiteLift.comprehensionFrom Q (PowerClassPresheafProducts.reindex change domain))
    (compose (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.totalReindex change domain))
      (PresheafSiteLift.comprehensionTo P domain))

/-- The complete endpoint-and-witness substitution is constructed through
the actual raised identity context, retaining all three coordinates. -/
def identityChange : NatTrans (upperContext Q (PowerClassPresheafProducts.reindex change domain)) (upperContext P domain) :=
  compose (contextFrom Q (PowerClassPresheafProducts.reindex change domain))
    (compose (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.identityReindex change domain)) (contextTo P domain))

theorem totalChange_identity : totalChange P domain (identity P) = identity (totalSpace (upperDomain P domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem identityChange_identity : identityChange P domain (identity P) = identity (upperContext P domain) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  exact Sigma.ext rfl (heq_of_eq (raise_lower_witness receipt.2))

theorem totalChange_comp (earlier : NatTrans R Q) : totalChange P domain (compose earlier change) =
    compose (totalChange Q (PowerClassPresheafProducts.reindex change domain) earlier) (totalChange P domain change) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem identityChange_comp (earlier : NatTrans R Q) : identityChange P domain (compose earlier change) =
    compose (identityChange Q (PowerClassPresheafProducts.reindex change domain) earlier) (identityChange P domain change) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  exact Sigma.ext rfl (heq_of_eq (witness_eq _ _))

theorem diagonal_square : compose (DisplayedPresheafIdentity.diagonal (upperDomain Q (PowerClassPresheafProducts.reindex change domain)))
      (identityChange P domain change) =
    compose (totalChange P domain change) (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  exact Sigma.ext rfl (heq_of_eq (witness_eq _ _))

theorem readLeft_square : compose (identityChange P domain change) (DisplayedPresheafIdentity.readLeft (upperDomain P domain)) =
    compose (DisplayedPresheafIdentity.readLeft (upperDomain Q (PowerClassPresheafProducts.reindex change domain))) (totalChange P domain change) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem contextTo_square : compose (contextTo Q (PowerClassPresheafProducts.reindex change domain)) (identityChange P domain change) =
    compose (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.identityReindex change domain)) (contextTo P domain) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  exact Sigma.ext rfl (heq_of_eq (witness_eq _ _))

theorem contextFrom_square : compose (identityChange P domain change) (contextFrom P domain) =
    compose (contextFrom Q (PowerClassPresheafProducts.reindex change domain))
      (PresheafSiteLift.raiseChange (DisplayedPresheafIdentity.identityReindex change domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  apply congrArg ULift.up
  exact Sigma.ext rfl (heq_of_eq (witness_eq _ _))

variable (targetMotive : (upperContext P domain).Elements ⥤ Type (u + 1))
variable (targetMethod : (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) targetMotive).sections)

theorem substitutedReflexiveMotive :
    PowerClassPresheafProducts.reindex (totalChange P domain change)
      (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) targetMotive) =
    PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain Q (PowerClassPresheafProducts.reindex change domain)))
      (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive) := by
  rw [DisplayedPresheafIdentity.reindex_comp, DisplayedPresheafIdentity.reindex_comp, diagonal_square]

def substitutedMethod :
    (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain Q (PowerClassPresheafProducts.reindex change domain)))
      (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive)).sections :=
  PowerClassPresheafProducts.CP.castSection (substitutedReflexiveMotive P domain change targetMotive)
    (PowerClassPresheafProducts.reindexSection (totalChange P domain change)
      (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) targetMotive) targetMethod)

/-- Substitution is valid for every natural upper motive, including those
whose fibres have no lower-universe presentation. -/
theorem J_substitution : PowerClassPresheafProducts.reindexSection (identityChange P domain change) targetMotive
      (DisplayedPresheafIdentity.J (upperDomain P domain) targetMotive targetMethod) =
    DisplayedPresheafIdentity.J (upperDomain Q (PowerClassPresheafProducts.reindex change domain))
      (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive)
      (substitutedMethod P domain change targetMotive targetMethod) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  have first := DisplayedPresheafIdentity.J_value_heq (upperDomain P domain) targetMotive targetMethod
    ((PowerClassPresheafProducts.elementMap (identityChange P domain change)).obj point)
  have second := DisplayedPresheafIdentity.J_value_heq (upperDomain Q (PowerClassPresheafProducts.reindex change domain))
    (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive)
    (substitutedMethod P domain change targetMotive targetMethod) point
  have methodCast := PowerClassPresheafProducts.CP.castSection_value (substitutedReflexiveMotive P domain change targetMotive)
    (PowerClassPresheafProducts.reindexSection (totalChange P domain change)
      (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal (upperDomain P domain)) targetMotive) targetMethod)
    ((PowerClassPresheafProducts.elementMap (DisplayedPresheafIdentity.readLeft
      (upperDomain Q (PowerClassPresheafProducts.reindex change domain)))).obj point)
  exact first.trans (second.trans methodCast).symm

theorem J_beta_substitution :
    PowerClassPresheafProducts.reindexSection (DisplayedPresheafIdentity.diagonal (upperDomain Q (PowerClassPresheafProducts.reindex change domain)))
      (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive)
      (PowerClassPresheafProducts.reindexSection (identityChange P domain change) targetMotive
        (DisplayedPresheafIdentity.J (upperDomain P domain) targetMotive targetMethod)) =
      substitutedMethod P domain change targetMotive targetMethod := by
  rw [J_substitution]
  exact DisplayedPresheafIdentity.J_beta _ _ _

theorem J_lift_substitution :
    PowerClassPresheafProducts.reindexSection (identityChange P domain change) (upperMotive P domain motive)
      (PowerClassPresheafProducts.reindexSection (contextFrom P domain)
        (PresheafSiteLift.family (lowerContext P domain) motive)
        (PresheafSiteLift.raiseTerm (lowerContext P domain) motive (DisplayedPresheafIdentity.J domain motive method))) =
      DisplayedPresheafIdentity.J (upperDomain Q (PowerClassPresheafProducts.reindex change domain))
        (PowerClassPresheafProducts.reindex (identityChange P domain change) (upperMotive P domain motive))
        (substitutedMethod P domain change (upperMotive P domain motive) (upperMethod P domain motive method)) := by
  rw [← J_lift]
  exact J_substitution P domain change (upperMotive P domain motive) (upperMethod P domain motive method)

private theorem reindexTerm_heq {D : Type u} [Category.{u} D] {firstBase secondBase : Dᵒᵖ ⥤ Type u}
    {first second : NatTrans firstBase secondBase} (same : first = second)
    (family : secondBase.Elements ⥤ Type u) (term : family.sections) :
    HEq (PowerClassPresheafProducts.reindexSection first family term) (PowerClassPresheafProducts.reindexSection second family term) := by
  cases same
  rfl

/-- Composite and successive substitutions give the same complete J term.
The heterogeneous statement retains the proved source-motive comparison
instead of asserting that the two authored substitution records are literal
syntax aliases. -/
theorem J_substitution_comp (earlier : NatTrans R Q) :
    HEq (DisplayedPresheafIdentity.J (upperDomain R (PowerClassPresheafProducts.reindex (compose earlier change) domain))
        (PowerClassPresheafProducts.reindex (identityChange P domain (compose earlier change)) targetMotive)
        (substitutedMethod P domain (compose earlier change) targetMotive targetMethod))
      (PowerClassPresheafProducts.reindexSection
        (identityChange Q (PowerClassPresheafProducts.reindex change domain) earlier)
        (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive)
        (DisplayedPresheafIdentity.J (upperDomain Q (PowerClassPresheafProducts.reindex change domain))
          (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive)
          (substitutedMethod P domain change targetMotive targetMethod))) := by
  have composite := J_substitution P domain (compose earlier change) targetMotive targetMethod
  have first := J_substitution P domain change targetMotive targetMethod
  refine (heq_of_eq composite.symm).trans ?_
  refine (reindexTerm_heq (identityChange_comp P domain change earlier) targetMotive
    (DisplayedPresheafIdentity.J (upperDomain P domain) targetMotive targetMethod)).trans ?_
  exact heq_of_eq (congrArg (fun term => PowerClassPresheafProducts.reindexSection
    (identityChange Q (PowerClassPresheafProducts.reindex change domain) earlier)
    (PowerClassPresheafProducts.reindex (identityChange P domain change) targetMotive) term) first)

/-- Full domain restriction, including its actual upper arrows, coincides
with independently raising the restricted lower family. -/
theorem domain_reindex : upperDomain Q (PowerClassPresheafProducts.reindex change domain) =
    PowerClassPresheafProducts.reindex (PresheafSiteLift.raiseChange change) (upperDomain P domain) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

private def contextMapCast {D : Type u} [Category.{u} D] {source target : Dᵒᵖ ⥤ Type u}
    {first second : source.Elements ⥤ Type u} (same : first = second)
    (operation : NatTrans (DisplayedPresheafIdentity.identityContext second) target) :
    NatTrans (DisplayedPresheafIdentity.identityContext first) target := by
  cases same
  exact operation

private theorem contextMapCast_apply {D : Type u} [Category.{u} D] {source target : Dᵒᵖ ⥤ Type u}
    {first second : source.Elements ⥤ Type u} (same : first = second)
    (operation : NatTrans (DisplayedPresheafIdentity.identityContext second) target) (world : Dᵒᵖ)
    (left : (DisplayedPresheafIdentity.identityContext first).obj world)
    (right : (DisplayedPresheafIdentity.identityContext second).obj world) (receipts : HEq left right) :
    (contextMapCast same operation).app world left = operation.app world right := by
  cases same
  cases eq_of_heq receipts
  rfl

/-- The constructed complete context action agrees with ordinary native
upper identity substitution after the proved whole-domain comparison. -/
theorem identityChange_native : identityChange P domain change =
    contextMapCast (domain_reindex P domain change)
      (DisplayedPresheafIdentity.identityReindex (PresheafSiteLift.raiseChange change) (upperDomain P domain)) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  have casted := contextMapCast_apply (domain_reindex P domain change)
    (DisplayedPresheafIdentity.identityReindex (PresheafSiteLift.raiseChange change) (upperDomain P domain))
    world receipt receipt HEq.rfl
  refine Eq.trans ?_ casted.symm
  exact Sigma.ext rfl (heq_of_eq (witness_eq _ _))

end Substitution

end Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentitySiteLift
