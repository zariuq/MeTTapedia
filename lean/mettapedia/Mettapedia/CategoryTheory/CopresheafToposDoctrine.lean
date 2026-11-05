import Mettapedia.CategoryTheory.PredicateDoctrine
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# The subobject doctrine of a copresheaf topos: Kripke–Joyal semantics, higher order

For a category `C`, the copresheaves `C ⥤ Type` form a topos. Read Kripke-style, its **stages**
are the objects of `C`, and a stage `y` is accessible from `x` along each arrow `x ⟶ y`. A
predicate on a copresheaf `P` is a subfunctor: at each stage a set of elements, closed under
moving forward along arrows (persistence).

## The first-order doctrine (`doctrine`)

* Fibres are Heyting algebras of subfunctors. Meets and joins are taken stagewise; implication
  is **Kripke implication**: `a` forces `S ⇨ T` at `x` when every move `p : x ⟶ y` that brings
  `a` into `S` brings it into `T` (`mem_himp_iff`).
* Reindexing is the preimage, existence along a map is the stagewise image (`mem_exists_iff`),
  and universality along a map quantifies over all later stages (`mem_forall_iff`).
* Both quantifiers are adjoints of reindexing, Frobenius reciprocity holds, and Beck–Chevalley
  holds for both on every pullback square: for existence stagewise, for universality as the mate
  of existence on the transposed square (`forall_baseChange_of_exists`, which holds for any
  doctrine with both adjoints).

These clauses are the Kripke–Joyal forcing clauses of the copresheaf topos; for copresheaves no
covering appears in the existential clause.

## The generic predicate (`omega`, `truth`, `generic`)

* The truth values at a stage `x` are the **cosieves** on `x`: the subfunctors of the
  representable copresheaf of arrows out of `x`, that is, sets of arrows out of `x` closed under
  postcomposition. A move `p : x ⟶ y` sends a cosieve `σ` to `{q | p ≫ q ∈ σ}`.
* `truth` is the predicate "the cosieve is maximal". The characteristic map of `S ⊆ P` sends `a`
  to the cosieve of moves that bring `a` into `S`. It classifies `S`, and it is the only map that
  does (`generic`).
* With Mathlib's cartesian closed structure on copresheaves this is a
  `PredicateDoctrine.HigherOrder` doctrine (`higherOrder`).
* The generic predicate is not degenerate: at every stage the empty cosieve is a truth value
  other than the maximal one (`omega_bot_ne_top`), and it is not true (`bot_not_mem_truth`).

## Comprehension in any higher-order doctrine

`comprehension`: on a cartesian closed base, predicates on `X ⊗ Y` correspond exactly to maps
`Y ⟶ (X ⟹ Ω)`, and every predicate is the membership predicate reindexed along its
comprehension map (`comprehension_spec`). This is what quantifying over predicates means: a
predicate variable ranges over the power object `X ⟹ Ω`.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.CopresheafToposDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite MonoidalCategory
open Mettapedia.CategoryTheory.PredicateDoctrine

universe w v u w' uB vB wB

/-! ## Beck–Chevalley for universality is the mate of Beck–Chevalley for existence -/

section BaseChange

variable {B : Type uB} [Category.{vB} B]

/-- **For a doctrine with both adjoints, Beck–Chevalley for universality on a pullback square
follows from Beck–Chevalley for existence on the transposed square.** Both sides of the
universal law are right adjoints of the two sides of the existential law for the flipped
square, and right adjoints of equal maps are equal. -/
theorem forall_baseChange_of_exists (D : IndexedHeyting.{uB, vB, wB} B)
    (existsAlong : ∀ {X Y : B}, (X ⟶ Y) → D.Fiber X → D.Fiber Y)
    (forallAlong : ∀ {X Y : B}, (X ⟶ Y) → D.Fiber X → D.Fiber Y)
    (exists_adj : ∀ {X Y : B} (f : X ⟶ Y), GaloisConnection (existsAlong f) (D.reindex f))
    (forall_adj : ∀ {X Y : B} (f : X ⟶ Y), GaloisConnection (D.reindex f) (forallAlong f))
    (exists_baseChange : ∀ {P Q R S : B} (top : P ⟶ Q) (left : P ⟶ R) (right : Q ⟶ S)
      (bottom : R ⟶ S), IsPullback top left right bottom →
      ∀ φ : D.Fiber Q, D.reindex bottom (existsAlong right φ) = existsAlong left (D.reindex top φ))
    {P Q R S : B} (top : P ⟶ Q) (left : P ⟶ R) (right : Q ⟶ S) (bottom : R ⟶ S)
    (pullback : IsPullback top left right bottom) (φ : D.Fiber Q) :
    D.reindex bottom (forallAlong right φ) = forallAlong left (D.reindex top φ) := by
  have flipped := exists_baseChange left top bottom right pullback.flip
  have first := (exists_adj bottom).compose (forall_adj right)
  have second := (forall_adj left).compose (exists_adj top)
  exact first.u_unique second fun ψ => flipped ψ

end BaseChange

/-! ## The Heyting algebra of subfunctors -/

section Heyting

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w'}

/-- **Kripke implication**: `a` lies in `S ⇨ T` at `x` when every move out of `x` that brings `a`
into `S` brings it into `T`. -/
def himp (S T : Subfunctor F) : Subfunctor F where
  obj x := {a | ∀ ⦃y : C⦄ (p : x ⟶ y), F.map p a ∈ S.obj y → F.map p a ∈ T.obj y}
  map {x x'} q a holds := by
    intro y p inS
    have later := holds (q ≫ p)
    rw [Functor.map_comp_apply] at later
    exact later inS

instance : DistribLattice (Subfunctor F) :=
  DistribLattice.ofInfSupLe fun S T U x a member => by
    obtain ⟨inS, inTU⟩ := member
    rcases inTU with inT | inU
    · exact Or.inl ⟨inS, inT⟩
    · exact Or.inr ⟨inS, inU⟩

theorem le_himp_iff' (S T U : Subfunctor F) : S ≤ himp T U ↔ S ⊓ T ≤ U := by
  constructor
  · intro below x a member
    have holds := below x member.1 (𝟙 x)
    rw [Functor.map_id_apply] at holds
    exact holds member.2
  · intro below x a inS y p inT
    exact below y ⟨S.map p inS, inT⟩

instance : HeytingAlgebra (Subfunctor F) :=
  HeytingAlgebra.ofHImp himp le_himp_iff'

theorem mem_himp_iff (S T : Subfunctor F) (x : C) (a : F.obj x) :
    a ∈ (S ⇨ T).obj x ↔ ∀ ⦃y : C⦄ (p : x ⟶ y), F.map p a ∈ S.obj y → F.map p a ∈ T.obj y :=
  Iff.rfl

/-- **Kripke negation**: `a` lies in `Sᶜ` at `x` when no move out of `x` brings it into `S`. -/
theorem mem_compl_iff (S : Subfunctor F) (x : C) (a : F.obj x) :
    a ∈ Sᶜ.obj x ↔ ∀ ⦃y : C⦄ (p : x ⟶ y), F.map p a ∉ S.obj y :=
  ⟨fun holds _ p inS => holds p inS, fun holds _ p inS => absurd inS (holds p)⟩

theorem mem_inf_iff (S T : Subfunctor F) (x : C) (a : F.obj x) :
    a ∈ (S ⊓ T).obj x ↔ a ∈ S.obj x ∧ a ∈ T.obj x := Iff.rfl

theorem mem_sup_iff (S T : Subfunctor F) (x : C) (a : F.obj x) :
    a ∈ (S ⊔ T).obj x ↔ a ∈ S.obj x ∨ a ∈ T.obj x := Iff.rfl

/-- **Persistence**: what holds at a stage holds at every later stage. -/
theorem persistent (S : Subfunctor F) {x y : C} (p : x ⟶ y) {a : F.obj x} (member : a ∈ S.obj x) :
    F.map p a ∈ S.obj y :=
  S.map p member

theorem subfunctor_ext {S T : Subfunctor F} (same : ∀ x a, a ∈ S.obj x ↔ a ∈ T.obj x) : S = T :=
  Subfunctor.ext (funext fun x => Set.ext (same x))

end Heyting

/-! ## Universality along a map -/

section Forall

variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w'}

/-- **Universality along `f`**: `b` lies in `∀_f S` at `x` when, at every later stage, every
element over the moved `b` lies in `S`. -/
def forallAlong (f : P ⟶ Q) (S : Subfunctor P) : Subfunctor Q where
  obj x := {b | ∀ ⦃y : C⦄ (p : x ⟶ y) (a : P.obj y), f.app y a = Q.map p b → a ∈ S.obj y}
  map {x x'} q b holds := by
    intro y p a same
    exact holds (q ≫ p) a (by rw [Functor.map_comp_apply]; exact same)

theorem preimage_le_iff (f : P ⟶ Q) (S : Subfunctor P) (T : Subfunctor Q) :
    T.preimage f ≤ S ↔ T ≤ forallAlong f S := by
  constructor
  · intro below x b inT y p a same
    apply below y
    change f.app y a ∈ T.obj y
    rw [same]
    exact T.map p inT
  · intro below x a inT
    have holds := below x inT (𝟙 x) a (by rw [Functor.map_id_apply])
    exact holds

end Forall

/-! ## The doctrine -/

section Doctrine

variable (C : Type u) [Category.{v} C]

/-- **Subfunctors as an indexed Heyting algebra**: reindexing is the preimage. -/
def indexedHeyting : IndexedHeyting (C ⥤ Type (max w v u)) where
  Fiber P := Subfunctor P
  reindex f S := S.preimage f
  reindex_mono f := fun _ _ below => (Subfunctor.le_def _ _).mpr fun x _ member =>
    (Subfunctor.le_def _ _).mp below x member
  reindex_id _ S := Subfunctor.preimage_id S
  reindex_comp f g S := Subfunctor.preimage_comp S f g
  reindex_top _ := rfl
  reindex_bot _ := rfl
  reindex_inf _ _ _ := rfl
  reindex_sup _ _ _ := rfl
  reindex_himp {P Q} f S T := by
    ext x a
    change (∀ ⦃y : C⦄ (p : x ⟶ y), Q.map p (f.app x a) ∈ S.obj y → Q.map p (f.app x a) ∈ T.obj y) ↔
      (∀ ⦃y : C⦄ (p : x ⟶ y), f.app y (P.map p a) ∈ S.obj y → f.app y (P.map p a) ∈ T.obj y)
    simp only [NatTrans.naturality_apply]

/-- **Beck–Chevalley for existence**, stagewise from pullbacks of types. -/
theorem image_baseChange {P Q R S : C ⥤ Type (max w v u)} (top : P ⟶ Q) (left : P ⟶ R)
    (right : Q ⟶ S) (bottom : R ⟶ S) (pullback : IsPullback top left right bottom)
    (φ : Subfunctor Q) : (φ.image right).preimage bottom = (φ.preimage top).image left := by
  ext x k
  constructor
  · rintro ⟨q, inφ, same⟩
    obtain ⟨p, pTop, pLeft⟩ := Types.exists_of_isPullback (pullback.app x) q k same
    exact ⟨p, by change top.app x p ∈ φ.obj x; rw [pTop]; exact inφ, pLeft⟩
  · rintro ⟨p, inφ, rfl⟩
    refine ⟨top.app x p, inφ, ?_⟩
    have square := congrArg (fun g => g.app x p) pullback.w
    simpa using square

/-- **The subobject doctrine of the copresheaf topos**, with Kripke implication and both
quantifiers. -/
def doctrine : FirstOrder (C ⥤ Type (max w v u)) where
  toIndexedHeyting := indexedHeyting.{w} C
  existsAlong f S := S.image f
  forallAlong f S := forallAlong f S
  exists_mono f := fun _ _ below => (Subfunctor.le_def _ _).mpr fun x _ ⟨a, member, same⟩ =>
    ⟨a, (Subfunctor.le_def _ _).mp below x member, same⟩
  forall_mono f := fun _ _ below => (Subfunctor.le_def _ _).mpr fun _ _ holds _ p a same =>
    (Subfunctor.le_def _ _).mp below _ (holds p a same)
  exists_adj f := fun S T => Subfunctor.image_le_iff S f T
  forall_adj f := fun T S => preimage_le_iff f S T
  frobenius f S T := by
    refine subfunctor_ext fun x b => ?_
    constructor
    · rintro ⟨a, ⟨inS, inT⟩, rfl⟩
      exact ⟨⟨a, inS, rfl⟩, inT⟩
    · rintro ⟨⟨a, inS, rfl⟩, inT⟩
      exact ⟨a, ⟨inS, inT⟩, rfl⟩
  exists_baseChange top left right bottom pullback φ :=
    image_baseChange C top left right bottom pullback φ
  forall_baseChange top left right bottom pullback φ :=
    forall_baseChange_of_exists (indexedHeyting.{w} C) (fun f S => S.image f)
      (fun f S => forallAlong f S) (fun f S T => Subfunctor.image_le_iff S f T)
      (fun f T S => preimage_le_iff f S T)
      (fun top left right bottom pullback φ => image_baseChange C top left right bottom pullback φ)
      top left right bottom pullback φ

variable {C}

/-! ### The Kripke–Joyal clauses -/

theorem mem_reindex_iff {P Q : C ⥤ Type (max w v u)} (f : P ⟶ Q) (S : Subfunctor Q) (x : C)
    (a : P.obj x) : a ∈ ((doctrine.{w} C).reindex f S).obj x ↔ f.app x a ∈ S.obj x := Iff.rfl

theorem mem_exists_iff {P Q : C ⥤ Type (max w v u)} (f : P ⟶ Q) (S : Subfunctor P) (x : C)
    (b : Q.obj x) :
    b ∈ ((doctrine.{w} C).existsAlong f S).obj x ↔ ∃ a ∈ S.obj x, f.app x a = b := Iff.rfl

theorem mem_forall_iff {P Q : C ⥤ Type (max w v u)} (f : P ⟶ Q) (S : Subfunctor P) (x : C)
    (b : Q.obj x) :
    b ∈ ((doctrine.{w} C).forallAlong f S).obj x ↔
      ∀ ⦃y : C⦄ (p : x ⟶ y) (a : P.obj y), f.app y a = Q.map p b → a ∈ S.obj y := Iff.rfl

end Doctrine

/-! ## The generic predicate: cosieves -/

section Generic

variable (C : Type u) [Category.{v} C]

/-- Moving a cosieve on `x` along `p : x ⟶ y`: the moves `q` out of `y` with `p ≫ q` in it. -/
abbrev moveCosieve {x y : C} (p : x ⟶ y) (σ : Subfunctor (coyoneda.obj (op x))) :
    Subfunctor (coyoneda.obj (op y)) :=
  σ.preimage (coyoneda.map p.op)

theorem mem_moveCosieve_iff {x y z : C} (p : x ⟶ y) (σ : Subfunctor (coyoneda.obj (op x)))
    (q : y ⟶ z) : q ∈ (moveCosieve C p σ).obj z ↔ p ≫ q ∈ σ.obj z := Iff.rfl

/-- **A move lies in a cosieve exactly when the cosieve moved along it is maximal.** -/
theorem moveCosieve_eq_top_iff {x y : C} (p : x ⟶ y) (σ : Subfunctor (coyoneda.obj (op x))) :
    moveCosieve C p σ = ⊤ ↔ p ∈ σ.obj y := by
  constructor
  · intro maximal
    have member : 𝟙 y ∈ (moveCosieve C p σ).obj y := by
      rw [maximal]
      exact Set.mem_univ _
    have inσ : p ≫ 𝟙 y ∈ σ.obj y := member
    rwa [Category.comp_id] at inσ
  · intro member
    ext z q
    simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
    exact σ.map q member

/-- **The truth values**: at a stage `x`, the cosieves on `x`. -/
def omega : C ⥤ Type (max w v u) where
  obj x := ULift.{w} (Subfunctor (coyoneda.obj (op x)))
  map p := TypeCat.ofHom fun σ => ULift.up (moveCosieve C p σ.down)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply ULift.ext
    change σ.down.preimage (coyoneda.map (𝟙 x).op) = σ.down
    rw [op_id, CategoryTheory.Functor.map_id]
    exact Subfunctor.preimage_id σ.down
  map_comp p q := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply ULift.ext
    change σ.down.preimage (coyoneda.map (p ≫ q).op) =
      (σ.down.preimage (coyoneda.map p.op)).preimage (coyoneda.map q.op)
    rw [op_comp, CategoryTheory.Functor.map_comp]
    exact Subfunctor.preimage_comp σ.down _ _

/-- **Truth**: the maximal cosieve. -/
def truth : Subfunctor (omega.{w} C) where
  obj x := {σ | σ.down = ⊤}
  map {x y} p σ maximal := by
    change moveCosieve C p σ.down = ⊤
    rw [moveCosieve_eq_top_iff]
    have member : p ∈ (⊤ : Subfunctor (coyoneda.obj (op x))).obj y := Set.mem_univ _
    rw [← maximal] at member
    exact member

variable {C}

/-- The cosieve of the moves that bring `a` into `S`. -/
def characteristicCosieve {X : C ⥤ Type (max w v u)} (S : Subfunctor X) {x : C} (a : X.obj x) :
    Subfunctor (coyoneda.obj (op x)) where
  obj y := {q | X.map q a ∈ S.obj y}
  map {y z} g q member := by
    change X.map (q ≫ g) a ∈ S.obj z
    rw [Functor.map_comp_apply]
    exact S.map g member

theorem characteristicCosieve_eq_top_iff {X : C ⥤ Type (max w v u)} (S : Subfunctor X) {x : C}
    (a : X.obj x) : characteristicCosieve S a = ⊤ ↔ a ∈ S.obj x := by
  constructor
  · intro maximal
    have member : 𝟙 x ∈ (characteristicCosieve S a).obj x := by
      rw [maximal]
      exact Set.mem_univ _
    have inS : X.map (𝟙 x) a ∈ S.obj x := member
    rwa [Functor.map_id_apply] at inS
  · intro member
    ext y q
    simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
    exact S.map q member

/-- **The characteristic map** of a predicate. -/
def characteristic {X : C ⥤ Type (max w v u)} (S : Subfunctor X) : X ⟶ omega.{w} C where
  app x := TypeCat.ofHom fun a => ULift.up (characteristicCosieve S a)
  naturality {x y} p := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    ext z q
    change X.map q (X.map p a) ∈ S.obj z ↔ X.map (p ≫ q) a ∈ S.obj z
    rw [Functor.map_comp_apply]

variable (C)

/-- **The generic predicate of the copresheaf topos**: every predicate is the reindexing of truth
along exactly one map into the cosieves. -/
def generic : GenericPredicate (C ⥤ Type (max w v u)) (doctrine.{w} C).toIndexedHeyting where
  object := omega.{w} C
  truth := truth.{w} C
  characteristic _ S := characteristic S
  classifies X S := by
    refine subfunctor_ext fun x a => ?_
    exact characteristicCosieve_eq_top_iff S a
  unique X S f classifiesS := by
    subst classifiesS
    ext x a
    apply ULift.ext
    ext y q
    change q ∈ (f.app x a).down.obj y ↔ (f.app y (X.map q a)).down = ⊤
    rw [NatTrans.naturality_apply]
    exact (moveCosieve_eq_top_iff C q (f.app x a).down).symm

/-- **The copresheaf topos carries a higher-order predicate doctrine.** -/
def higherOrder : HigherOrder (C ⥤ Type (max w v u)) where
  toFirstOrder := doctrine.{w} C
  generic := generic.{w} C

/-- **Non-degeneracy**: at every stage the empty cosieve is a truth value other than the maximal
one. -/
theorem omega_bot_ne_top (x : C) :
    (ULift.up ⊥ : (omega.{w} C).obj x) ≠ ULift.up ⊤ := by
  intro same
  have botTop : (⊥ : Subfunctor (coyoneda.obj (op x))) = ⊤ := congrArg ULift.down same
  have member : 𝟙 x ∈ (⊤ : Subfunctor (coyoneda.obj (op x))).obj x := Set.mem_univ _
  rw [← botTop] at member
  exact member

/-- **Non-degeneracy**: the empty cosieve is not true. -/
theorem bot_not_mem_truth (x : C) :
    (ULift.up ⊥ : (omega.{w} C).obj x) ∉ (truth.{w} C).obj x :=
  fun maximal => omega_bot_ne_top.{w} C x (congrArg ULift.up maximal)

end Generic

/-! ## Comprehension in a higher-order doctrine -/

section Comprehension

variable {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B] [MonoidalClosed B]
variable (D : HigherOrder.{uB, vB, wB} B)

/-- **Membership**: the predicate on `X ⊗ (X ⟹ Ω)` obtained by evaluating and asking for truth. -/
def membership (X : B) : D.Fiber (X ⊗ (ihom X).obj D.generic.object) :=
  D.reindex ((ihom.ev X).app D.generic.object) D.generic.truth

/-- **Comprehension**: predicates on `X ⊗ Y` are exactly the maps from `Y` into the power object
`X ⟹ Ω`. -/
def comprehension (X Y : B) : D.Fiber (X ⊗ Y) ≃ (Y ⟶ (ihom X).obj D.generic.object) :=
  (D.generic.characteristicEquiv (X ⊗ Y)).symm.trans
    ((ihom.adjunction X).homEquiv Y D.generic.object)

/-- **Every predicate is membership in a power object**, reindexed along its comprehension map. -/
theorem comprehension_spec (X Y : B) (φ : D.Fiber (X ⊗ Y)) :
    D.reindex (X ◁ comprehension D X Y φ) (membership D X) = φ := by
  unfold membership
  rw [← D.reindex_comp]
  have uncurried : X ◁ comprehension D X Y φ ≫ (ihom.ev X).app D.generic.object =
      D.generic.characteristic (X ⊗ Y) φ := by
    have counit := Adjunction.homEquiv_counit (ihom.adjunction X) (g := comprehension D X Y φ)
    have back : ((ihom.adjunction X).homEquiv Y D.generic.object).symm (comprehension D X Y φ) =
        D.generic.characteristic (X ⊗ Y) φ :=
      ((ihom.adjunction X).homEquiv Y D.generic.object).symm_apply_apply _
    exact counit.symm.trans back
  rw [uncurried]
  exact D.generic.classifies (X ⊗ Y) φ

end Comprehension

#print axioms forall_baseChange_of_exists
#print axioms le_himp_iff'
#print axioms mem_compl_iff
#print axioms preimage_le_iff
#print axioms indexedHeyting
#print axioms image_baseChange
#print axioms doctrine
#print axioms moveCosieve_eq_top_iff
#print axioms omega
#print axioms truth
#print axioms characteristicCosieve_eq_top_iff
#print axioms characteristic
#print axioms generic
#print axioms higherOrder
#print axioms omega_bot_ne_top
#print axioms bot_not_mem_truth
#print axioms comprehension
#print axioms comprehension_spec

end Mettapedia.CategoryTheory.CopresheafToposDoctrine
