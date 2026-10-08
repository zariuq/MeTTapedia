import Mettapedia.TypeTheory.PresheafNativePredicateRefinement

/-!
# Introduction and forgetting of native predicate refinements

Any coherent complete context map satisfying the supplied predicate factors
uniquely through refinement. Both inverse laws retain the complete original
receipt. Specializing to natural sections gives native introduction and
forgetting with their computation and uniqueness laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateRefinement

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf ContextualLocalUniverses NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}
variable (A : DisplayedFamily P) (predicate : Subfunctor (totalSpace A))

def guardedMap (term : Q ⟶ totalSpace A)
    (satisfies : ∀ world value, term.app world value ∈ predicate.obj world) :
    Q ⟶ predicate.toFunctor where
  app world := TypeCat.ofHom fun value => ⟨term.app world value, satisfies world value⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact term.naturality_apply arrow value

def introTotal (term : Q ⟶ totalSpace A)
    (satisfies : ∀ world value, term.app world value ∈ predicate.obj world) :
    Q ⟶ totalSpace (displayed A predicate) :=
  guardedMap A predicate term satisfies ≫ (totalIso A predicate).inv

/-- Introduction followed by forgetting recovers the complete supplied
context map, including the actual original dependent inhabitant. -/
theorem introTotal_beta (term : Q ⟶ totalSpace A)
    (satisfies : ∀ world value, term.app world value ∈ predicate.obj world) :
    introTotal A predicate term satisfies ≫ forgetTotal A predicate = term := by
  ext world value
  rfl

theorem forgetTotal_satisfies (world : Cᵒᵖ)
    (value : (totalSpace (displayed A predicate)).obj world) :
    (forgetTotal A predicate).app world value ∈ predicate.obj world := value.2.property

/-- Every full refinement-valued map is recovered from its forgetful
map. Only proposition-valued membership proofs are identified. -/
theorem introTotal_eta (refined : Q ⟶ totalSpace (displayed A predicate)) :
    introTotal A predicate (refined ≫ forgetTotal A predicate)
        (fun world value => forgetTotal_satisfies A predicate world (refined.app world value)) =
      refined := by
  ext world value
  rfl

theorem forgetTotal_injective (world : Cᵒᵖ) :
    Function.Injective ((forgetTotal A predicate).app world) := by
  intro first second same
  have encoded : (totalIso A predicate).hom.app world first =
      (totalIso A predicate).hom.app world second := Subtype.ext same
  have firstInverse := ConcreteCategory.congr_hom
    ((totalIso A predicate).hom_inv_id_app world) first
  have secondInverse := ConcreteCategory.congr_hom
    ((totalIso A predicate).hom_inv_id_app world) second
  exact firstInverse.symm.trans
    ((congrArg ((totalIso A predicate).inv.app world) encoded).trans secondInverse)

/-- Any other coherent introduction with the same original complete
receipt is equal to the constructed introduction. -/
theorem introTotal_unique (term : Q ⟶ totalSpace A)
    (satisfies : ∀ world value, term.app world value ∈ predicate.obj world)
    (other : Q ⟶ totalSpace (displayed A predicate))
    (forgets : other ≫ forgetTotal A predicate = term) :
    other = introTotal A predicate term satisfies := by
  ext world value
  apply forgetTotal_injective A predicate world
  have given := ConcreteCategory.congr_hom (NatTrans.congr_app forgets world) value
  have constructed := ConcreteCategory.congr_hom
    (NatTrans.congr_app (introTotal_beta A predicate term satisfies) world) value
  exact given.trans constructed.symm

def introSection (term : A.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A).obj world) ∈ predicate.obj world) : (displayed A predicate).sections where
  val point := by
    rcases point with ⟨world, base⟩
    exact ⟨term.val ⟨world, base⟩, satisfies world base⟩
  property := by
    intro first second arrow
    apply Subtype.ext
    exact term.property arrow

def forgetSection (term : (displayed A predicate).sections) : A.sections where
  val point := (term.val point).val
  property arrow := congrArg Subtype.val (term.property arrow)

theorem introSection_beta (term : A.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A).obj world) ∈ predicate.obj world) :
    forgetSection A predicate (introSection A predicate term satisfies) = term := by
  apply Subtype.ext
  rfl

theorem introSection_eta (term : (displayed A predicate).sections) :
    introSection A predicate (forgetSection A predicate term)
      (fun world base => (term.val ⟨world, base⟩).property) = term := by
  apply Subtype.ext
  rfl

def introNative (type : NativeType P) (predicate : Subfunctor (totalSpace type.decoded))
    (term : type.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace type.decoded).obj world) ∈ predicate.obj world) : (refinement type predicate).decoded.sections :=
  introSection type.decoded predicate term satisfies

def forgetNative (type : NativeType P) (predicate : Subfunctor (totalSpace type.decoded))
    (term : (refinement type predicate).decoded.sections) : type.decoded.sections :=
  forgetSection type.decoded predicate term

theorem native_beta (type : NativeType P) (predicate : Subfunctor (totalSpace type.decoded))
    (term : type.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace type.decoded).obj world) ∈ predicate.obj world) :
    forgetNative type predicate (introNative type predicate term satisfies) = term :=
  introSection_beta type.decoded predicate term satisfies

theorem native_eta (type : NativeType P) (predicate : Subfunctor (totalSpace type.decoded))
    (term : (refinement type predicate).decoded.sections) :
    introNative type predicate (forgetNative type predicate term)
      (fun world base => (term.val ⟨world, base⟩).property) = term :=
  introSection_eta type.decoded predicate term

end Mettapedia.TypeTheory.PresheafNativePredicateRefinement
