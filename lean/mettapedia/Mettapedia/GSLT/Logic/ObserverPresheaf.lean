import Mettapedia.GSLT.Logic.ObserverDetermination
import Mettapedia.Logic.TheoryModel.Forgetting
import Mathlib.CategoryTheory.Category.Preorder

/-!
# The observer presheaf and its hyperdoctrine

Admissible classes of contexts form a complete lattice, hence a thin category in
which `A ⟶ B` exactly when `A ≤ B`.  Sending a class `D` to the behavioural
classes of its saturated system, `S.Term / D.RelEquiv obs`, and an inclusion
`A ≤ B` to the forgetting map `classMapOfLe` is a presheaf on that category, the
**observer presheaf** (`observerPresheaf`).  It is the composite of the functor
from classes to observers (`saturatedObserver`) with the behavioural-class functor
on the category of observers, so its functoriality is `relEquiv_antitone`.

Every forgetting map is surjective (`restrict_surjective`).

**Stage predicates.**  A predicate at stage `D` is a set of `D`-classes.  Along an
inclusion `A ≤ B`, reindexing (`reindex`, preimage under forgetting) has a left
adjoint, existential image (`existsAlong`), and a right adjoint, universal image
(`forallAlong`), so stage predicates are a bifibration over the observer lattice.
Reindexing preserves the Boolean operations, and both images satisfy Frobenius
reciprocity (`existsAlong_inter_reindex`, `forallAlong_imp_reindex`).  Because
forgetting is surjective, existential image and reindexing form a Galois insertion
and reindexing and universal image a Galois coinsertion.  All three operations
compose along chains of inclusions.  Stage predicates therefore satisfy every
clause of a first-order hyperdoctrine over the observer lattice except
Beck–Chevalley, which is the subject of the next paragraph.

**Beck–Chevalley.**  For a square of inclusions `A ≤ B ≤ D`, `A ≤ C ≤ D`, both
Beck–Chevalley equations (existential and universal) hold exactly when the square
of forgetting maps is a weak pullback (`beckChevalley_exists_iff`,
`beckChevalley_forall_iff`, for any commuting square of functions).  For the
observer presheaf this is the amalgamation property `Amalgamates obs A B C`: two
terms equivalent for `A` are matched by one term equivalent to the first for `B`
and to the second for `C`.  It does not depend on `D`.  The comparison map into
the pullback is injective exactly when the `D`-equivalence is the intersection of
the `B`- and `C`-equivalences (`Separated`).  Both conditions can fail; the
controls module exhibits each failure and a square where both hold.

**Chains and sub-sites.**  Restricting along a monotone map of indices gives a
presheaf on the indices (`restrictedPresheaf`): a chain of observer classes, such
as an oracle tower, or the inclusion of a carved sub-site.

**Forgetting in the theory–model framework.**  Reading a stage predicate on terms
gives exactly the predicates invariant under the stage's equivalence, that is,
`observable predicateSat` of its behavioural setoid (`range_liftStage`), and
reindexing along forgetting is the inclusion `observable_anti` of the coarser
observer's predicates among the finer observer's (`liftStage_reindex`).

All results in this module use only `propext` and `Quot.sound`, except the order
packaging (`existsReindexInsertion`, `reindexForallCoinsertion`), which inherits
`Classical.choice` from Mathlib's order instance on `Set`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.AdmissibleContextCongruence

open CategoryTheory Opposite
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext

universe uS uContext uRule uAtom uW uX uY uZ

/-! ## Weak pullbacks and Beck–Chevalley for predicates on types -/

section WeakPullback

variable {W : Type uW} {X : Type uX} {Y : Type uY} {Z : Type uZ}

/-- A commuting square of functions is a weak pullback when every pair agreeing in
`Z` comes from one element of `W`. -/
def IsWeakPullback (p : W → X) (q : W → Y) (f : X → Z) (g : Y → Z) : Prop :=
  ∀ ⦃x : X⦄ ⦃y : Y⦄, f x = g y → ∃ w, p w = x ∧ q w = y

/-- Universal image: the points all of whose preimages satisfy the predicate. -/
def universalImage (f : X → Z) (φ : Set X) : Set Z :=
  {z | ∀ x, f x = z → x ∈ φ}

theorem mem_universalImage {f : X → Z} {φ : Set X} {z : Z} :
    z ∈ universalImage f φ ↔ ∀ x, f x = z → x ∈ φ :=
  Iff.rfl

theorem image_subset_iff' {f : X → Z} {φ : Set X} {ψ : Set Z} :
    f '' φ ⊆ ψ ↔ φ ⊆ f ⁻¹' ψ :=
  ⟨fun below x member => below ⟨x, member, rfl⟩,
    fun below _ ⟨_, member, equal⟩ => equal ▸ below member⟩

theorem subset_universalImage_iff {f : X → Z} {ψ : Set Z} {φ : Set X} :
    ψ ⊆ universalImage f φ ↔ f ⁻¹' ψ ⊆ φ :=
  ⟨fun below x member => below member x rfl,
    fun below _ member x equal => below (show f x ∈ ψ from equal ▸ member)⟩

variable (p : W → X) (q : W → Y) (f : X → Z) (g : Y → Z)

/-- **Beck–Chevalley, existential form.**  For a commuting square,
`g⁻¹ ∘ ∃f = ∃q ∘ p⁻¹` holds for every predicate exactly when the square is a weak
pullback. -/
theorem beckChevalley_exists_iff (comm : ∀ w, f (p w) = g (q w)) :
    (∀ φ : Set X, g ⁻¹' (f '' φ) = q '' (p ⁻¹' φ)) ↔ IsWeakPullback p q f g := by
  constructor
  · intro square x y equal
    have member : y ∈ g ⁻¹' (f '' {x}) := ⟨x, rfl, equal⟩
    rw [square {x}] at member
    obtain ⟨w, pw, qw⟩ := member
    exact ⟨w, pw, qw⟩
  · intro weak φ
    apply Set.Subset.antisymm
    · rintro y ⟨x, member, equal⟩
      obtain ⟨w, pw, qw⟩ := weak equal
      exact ⟨w, show p w ∈ φ from pw ▸ member, qw⟩
    · rintro y ⟨w, member, rfl⟩
      exact ⟨p w, member, comm w⟩

/-- **Beck–Chevalley, universal form.**  For a commuting square,
`g⁻¹ ∘ ∀f = ∀q ∘ p⁻¹` holds for every predicate exactly when the square is a weak
pullback. -/
theorem beckChevalley_forall_iff (comm : ∀ w, f (p w) = g (q w)) :
    (∀ φ : Set X, g ⁻¹' universalImage f φ = universalImage q (p ⁻¹' φ)) ↔
      IsWeakPullback p q f g := by
  constructor
  · intro square x y equal
    let witnessed : Set X := {x' | ∃ w, p w = x' ∧ q w = y}
    have member : y ∈ universalImage q (p ⁻¹' witnessed) :=
      fun w qw => ⟨w, rfl, qw⟩
    rw [← square witnessed] at member
    exact member x equal
  · intro weak φ
    apply Set.Subset.antisymm
    · intro y member w qw
      exact member (p w) (by rw [comm w, qw])
    · intro y member x equal
      obtain ⟨w, pw, qw⟩ := weak equal
      exact pw ▸ member w qw

end WeakPullback

namespace AdmissibleClass

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
variable (observations : ContextualRules.Observations.{uAtom} S)

/-! ## The observer presheaf -/

/-- Admissible classes as observers: a class goes to its saturated system and an
inclusion to the refinement that re-reads its labels and atoms. -/
def saturatedObserver :
    AdmissibleClass rules ⥤ ObserverObject.{uS, max uAtom uContext, uContext} S where
  obj D := ⟨D.saturated observations⟩
  map f := refinementOfLe observations (leOfHom f)
  map_id _ := ObserverRefinement.ext rfl rfl
  map_comp _ _ := ObserverRefinement.ext rfl rfl

/-- The stage of a class: its behavioural classes. -/
abbrev Stage (D : AdmissibleClass rules) : Type uS :=
  (D.saturated observations).BehavioralClass

/-- The class of a term at a stage. -/
abbrev stageClass (D : AdmissibleClass rules) (term : S.Term) : Stage observations D :=
  (D.saturated observations).toBehavioralClass term

theorem stageClass_eq_iff (D : AdmissibleClass rules) (left right : S.Term) :
    stageClass observations D left = stageClass observations D right ↔
      D.RelEquiv observations left right :=
  (D.saturated observations).behavioralClass_eq_iff left right

theorem stageClass_surjective (D : AdmissibleClass rules) :
    Function.Surjective (stageClass observations D) := by
  intro stageClassOf
  induction stageClassOf using Quotient.inductionOn with
  | _ term => exact ⟨term, rfl⟩

/-- Forgetting from the stage of `B` to the stage of `A`, for `A ≤ B`. -/
def restrict {A B : AdmissibleClass rules} (le : A ≤ B) :
    Stage observations B → Stage observations A :=
  classMapOfLe observations le

@[simp]
theorem restrict_stageClass {A B : AdmissibleClass rules} (le : A ≤ B) (term : S.Term) :
    restrict observations le (stageClass observations B term) =
      stageClass observations A term :=
  rfl

/-- **Forgetting is surjective**: every coarse class is the image of a fine
class. -/
theorem restrict_surjective {A B : AdmissibleClass rules} (le : A ≤ B) :
    Function.Surjective (restrict observations le) := by
  intro coarse
  obtain ⟨term, rfl⟩ := stageClass_surjective observations A coarse
  exact ⟨stageClass observations B term, rfl⟩

theorem restrict_refl (A : AdmissibleClass rules) (x : Stage observations A) :
    restrict observations (le_refl A) x = x := by
  induction x using Quotient.inductionOn with
  | _ term => rfl

theorem restrict_trans {A B C : AdmissibleClass rules} (first : A ≤ B) (second : B ≤ C)
    (x : Stage observations C) :
    restrict observations (le_trans first second) x =
      restrict observations first (restrict observations second x) := by
  induction x using Quotient.inductionOn with
  | _ term => rfl

/-- **The observer presheaf**: a class goes to the behavioural classes of its
saturated system, and an inclusion `A ≤ B` to the map forgetting the
distinctions `B` makes and `A` does not.  It is defined directly, so that its
axioms are those of `restrict`; `observerPresheaf_eq_comp` identifies it with the
composite through the category of observers. -/
def observerPresheaf : (AdmissibleClass rules)ᵒᵖ ⥤ Type uS where
  obj D := Stage observations D.unop
  map f := TypeCat.ofHom (restrict observations (leOfHom f.unop))
  map_id D := by
    ext x
    exact restrict_refl observations D.unop x
  map_comp f g := by
    ext x
    exact restrict_trans observations (leOfHom g.unop) (leOfHom f.unop) x

theorem observerPresheaf_obj (D : AdmissibleClass rules) :
    (observerPresheaf observations).obj (op D) = Stage observations D :=
  rfl

/-- The presheaf acts on an arrow by forgetting. -/
theorem observerPresheaf_map_apply {A B : AdmissibleClass rules} (f : op B ⟶ op A)
    (x : (observerPresheaf observations).obj (op B)) :
    (observerPresheaf observations).map f x = restrict observations (leOfHom f.unop) x :=
  rfl

/-- **The observer presheaf factors through the category of observers**: it is the
composite of `saturatedObserver` with the behavioural-class functor. -/
theorem observerPresheaf_eq_comp :
    observerPresheaf (rules := rules) observations =
      (saturatedObserver observations).op ⋙ ObserverObject.behavioralClasses :=
  rfl

/-- Forgetting loses nothing exactly when the two classes have the same
equivalence. -/
theorem restrict_injective_iff {A B : AdmissibleClass rules} (le : A ≤ B) :
    Function.Injective (restrict observations le) ↔
      ∀ left right, A.RelEquiv observations left right → B.RelEquiv observations left right := by
  constructor
  · intro injective left right related
    apply (stageClass_eq_iff observations B left right).mp
    apply injective
    exact (stageClass_eq_iff observations A left right).mpr related
  · intro reflects first second equal
    induction first using Quotient.inductionOn with
    | _ left =>
      induction second using Quotient.inductionOn with
      | _ right =>
        exact (stageClass_eq_iff observations B left right).mpr
          (reflects left right ((stageClass_eq_iff observations A left right).mp equal))

/-! ## Stage predicates and the adjoints to reindexing -/

/-- Reindexing a predicate on `A`-classes along forgetting to `B`-classes. -/
def reindex {A B : AdmissibleClass rules} (le : A ≤ B) (φ : Set (Stage observations A)) :
    Set (Stage observations B) :=
  restrict observations le ⁻¹' φ

/-- Existential image along forgetting: the `A`-classes containing some `B`-class
satisfying the predicate. -/
def existsAlong {A B : AdmissibleClass rules} (le : A ≤ B) (ψ : Set (Stage observations B)) :
    Set (Stage observations A) :=
  restrict observations le '' ψ

/-- Universal image along forgetting: the `A`-classes all of whose `B`-classes
satisfy the predicate. -/
def forallAlong {A B : AdmissibleClass rules} (le : A ≤ B) (ψ : Set (Stage observations B)) :
    Set (Stage observations A) :=
  universalImage (restrict observations le) ψ

variable {observations}

theorem mem_reindex_stageClass {A B : AdmissibleClass rules} {le : A ≤ B}
    {φ : Set (Stage observations A)} {term : S.Term} :
    stageClass observations B term ∈ reindex observations le φ ↔
      stageClass observations A term ∈ φ :=
  Iff.rfl

theorem mem_existsAlong_stageClass {A B : AdmissibleClass rules} {le : A ≤ B}
    {ψ : Set (Stage observations B)} {term : S.Term} :
    stageClass observations A term ∈ existsAlong observations le ψ ↔
      ∃ witness, A.RelEquiv observations witness term ∧ stageClass observations B witness ∈ ψ := by
  constructor
  · rintro ⟨fine, member, equal⟩
    induction fine using Quotient.inductionOn with
    | _ witness =>
      exact ⟨witness, (stageClass_eq_iff observations A witness term).mp equal, member⟩
  · rintro ⟨witness, related, member⟩
    exact ⟨stageClass observations B witness, member,
      (stageClass_eq_iff observations A witness term).mpr related⟩

theorem mem_forallAlong_stageClass {A B : AdmissibleClass rules} {le : A ≤ B}
    {ψ : Set (Stage observations B)} {term : S.Term} :
    stageClass observations A term ∈ forallAlong observations le ψ ↔
      ∀ witness, A.RelEquiv observations witness term → stageClass observations B witness ∈ ψ := by
  constructor
  · intro member witness related
    exact member _ ((stageClass_eq_iff observations A witness term).mpr related)
  · intro member fine equal
    induction fine using Quotient.inductionOn with
    | _ witness => exact member witness ((stageClass_eq_iff observations A witness term).mp equal)

/-- **Existential image is left adjoint to reindexing**, elementwise. -/
theorem existsAlong_subset_iff {A B : AdmissibleClass rules} (le : A ≤ B)
    {ψ : Set (Stage observations B)} {φ : Set (Stage observations A)} :
    existsAlong observations le ψ ⊆ φ ↔ ψ ⊆ reindex observations le φ :=
  image_subset_iff'

/-- **Universal image is right adjoint to reindexing**, elementwise. -/
theorem subset_forallAlong_iff {A B : AdmissibleClass rules} (le : A ≤ B)
    {φ : Set (Stage observations A)} {ψ : Set (Stage observations B)} :
    φ ⊆ forallAlong observations le ψ ↔ reindex observations le φ ⊆ ψ :=
  subset_universalImage_iff

/-- Surjectivity of forgetting: existential image undoes reindexing. -/
theorem existsAlong_reindex {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : Set (Stage observations A)) :
    existsAlong observations le (reindex observations le φ) = φ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨fine, member, rfl⟩
    exact member
  · intro coarse member
    obtain ⟨fine, rfl⟩ := restrict_surjective observations le coarse
    exact ⟨fine, member, rfl⟩

/-- Surjectivity of forgetting: universal image undoes reindexing. -/
theorem forallAlong_reindex {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : Set (Stage observations A)) :
    forallAlong observations le (reindex observations le φ) = φ := by
  apply Set.Subset.antisymm
  · intro coarse member
    obtain ⟨fine, rfl⟩ := restrict_surjective observations le coarse
    exact member fine rfl
  · intro coarse member fine equal
    exact show restrict observations le fine ∈ φ from equal ▸ member

/-- Reindexing along forgetting is injective on predicates. -/
theorem reindex_injective {A B : AdmissibleClass rules} (le : A ≤ B) :
    Function.Injective (reindex observations le) := by
  intro φ φ' equal
  rw [← existsAlong_reindex le φ, ← existsAlong_reindex le φ', equal]

/-! ### Frobenius reciprocity and the Boolean operations -/

/-- **Frobenius reciprocity** for existential image. -/
theorem existsAlong_inter_reindex {A B : AdmissibleClass rules} (le : A ≤ B)
    (ψ : Set (Stage observations B)) (φ : Set (Stage observations A)) :
    existsAlong observations le (ψ ∩ reindex observations le φ) =
      existsAlong observations le ψ ∩ φ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, ⟨member, image⟩, rfl⟩
    exact ⟨⟨x, member, rfl⟩, image⟩
  · rintro _ ⟨⟨x, member, rfl⟩, image⟩
    exact ⟨x, ⟨member, image⟩, rfl⟩

/-- **Frobenius reciprocity** for universal image, with implication. -/
theorem forallAlong_imp_reindex {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : Set (Stage observations A)) (ψ : Set (Stage observations B)) :
    forallAlong observations le {x | x ∈ reindex observations le φ → x ∈ ψ} =
      {a | a ∈ φ → a ∈ forallAlong observations le ψ} := by
  apply Set.Subset.antisymm
  · intro a member holds x equal
    exact member x equal (show restrict observations le x ∈ φ from equal ▸ holds)
  · intro a member x equal holds
    exact member (equal ▸ holds) x equal

/-- Reindexing preserves meets, joins and implication: it is a map of Boolean
algebras of predicates. -/
theorem reindex_inter {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ φ' : Set (Stage observations A)) :
    reindex observations le (φ ∩ φ') = reindex observations le φ ∩ reindex observations le φ' :=
  rfl

theorem reindex_union {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ φ' : Set (Stage observations A)) :
    reindex observations le (φ ∪ φ') = reindex observations le φ ∪ reindex observations le φ' :=
  rfl

theorem reindex_imp {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ φ' : Set (Stage observations A)) :
    reindex observations le {a | a ∈ φ → a ∈ φ'} =
      {b | b ∈ reindex observations le φ → b ∈ reindex observations le φ'} :=
  rfl

/-! ### Functoriality of the three operations -/

theorem reindex_refl (A : AdmissibleClass rules) (φ : Set (Stage observations A)) :
    reindex observations (le_refl A) φ = φ := by
  ext x
  change restrict observations (le_refl A) x ∈ φ ↔ x ∈ φ
  rw [restrict_refl]

theorem reindex_trans {A B C : AdmissibleClass rules} (first : A ≤ B) (second : B ≤ C)
    (φ : Set (Stage observations A)) :
    reindex observations (le_trans first second) φ =
      reindex observations second (reindex observations first φ) := by
  ext x
  change restrict observations (le_trans first second) x ∈ φ ↔
    restrict observations first (restrict observations second x) ∈ φ
  rw [restrict_trans]

theorem existsAlong_trans {A B C : AdmissibleClass rules} (first : A ≤ B) (second : B ≤ C)
    (ψ : Set (Stage observations C)) :
    existsAlong observations (le_trans first second) ψ =
      existsAlong observations first (existsAlong observations second ψ) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, member, rfl⟩
    exact ⟨restrict observations second x, ⟨x, member, rfl⟩, (restrict_trans observations _ _ x).symm⟩
  · rintro _ ⟨_, ⟨x, member, rfl⟩, rfl⟩
    exact ⟨x, member, restrict_trans observations _ _ x⟩

theorem forallAlong_trans {A B C : AdmissibleClass rules} (first : A ≤ B) (second : B ≤ C)
    (ψ : Set (Stage observations C)) :
    forallAlong observations (le_trans first second) ψ =
      forallAlong observations first (forallAlong observations second ψ) := by
  apply Set.Subset.antisymm
  · intro a member b equalB c equalC
    apply member c
    rw [restrict_trans observations first second, equalC, equalB]
  · intro a member c equal
    exact member (restrict observations second c) (by rw [← restrict_trans]; exact equal) c rfl

/-! ### Order packaging -/

variable (observations)

/-- Existential image and reindexing: a Galois insertion, since forgetting is
surjective. -/
def existsReindexInsertion {A B : AdmissibleClass rules} (le : A ≤ B) :
    GaloisInsertion (existsAlong observations le) (reindex observations le) :=
  GaloisConnection.toGaloisInsertion (fun _ _ => existsAlong_subset_iff le)
    (fun φ => (existsAlong_reindex le φ).symm.subset)

/-- Reindexing and universal image: a Galois coinsertion, since forgetting is
surjective. -/
def reindexForallCoinsertion {A B : AdmissibleClass rules} (le : A ≤ B) :
    GaloisCoinsertion (reindex observations le) (forallAlong observations le) :=
  GaloisConnection.toGaloisCoinsertion (fun _ _ => (subset_forallAlong_iff le).symm)
    (fun φ => (forallAlong_reindex le φ).subset)

/-! ## Beck–Chevalley for the observer presheaf -/

/-- **Amalgamation for a square**: two terms equivalent for `A` are matched by
one term equivalent to the first for `B` and to the second for `C`. -/
def Amalgamates (A B C : AdmissibleClass rules) : Prop :=
  ∀ ⦃left right : S.Term⦄, A.RelEquiv observations left right →
    ∃ glued, B.RelEquiv observations glued left ∧ C.RelEquiv observations glued right

/-- **Separation for a square**: terms equivalent for both `B` and `C` are
equivalent for `D`. -/
def Separated (B C D : AdmissibleClass rules) : Prop :=
  ∀ ⦃left right : S.Term⦄, B.RelEquiv observations left right →
    C.RelEquiv observations left right → D.RelEquiv observations left right

variable {observations}

/-- The square of forgetting maps of `A ≤ B ≤ D`, `A ≤ C ≤ D` commutes. -/
theorem restrict_square {A B C D : AdmissibleClass rules} (hAB : A ≤ B) (hAC : A ≤ C)
    (hBD : B ≤ D) (hCD : C ≤ D) (x : Stage observations D) :
    restrict observations hAB (restrict observations hBD x) =
      restrict observations hAC (restrict observations hCD x) := by
  induction x using Quotient.inductionOn with
  | _ term => rfl

/-- **The square of forgetting maps is a weak pullback exactly when the three
classes amalgamate**, whatever the fourth class `D ≥ B, C` is. -/
theorem isWeakPullback_iff_amalgamates {A B C D : AdmissibleClass rules} (hAB : A ≤ B)
    (hAC : A ≤ C) (hBD : B ≤ D) (hCD : C ≤ D) :
    IsWeakPullback (restrict observations hBD) (restrict observations hCD)
        (restrict observations hAB) (restrict observations hAC) ↔
      Amalgamates observations A B C := by
  constructor
  · intro weak left right related
    obtain ⟨glued, gluedB, gluedC⟩ := weak
      (x := stageClass observations B left) (y := stageClass observations C right)
      ((stageClass_eq_iff observations A left right).mpr related)
    induction glued using Quotient.inductionOn with
    | _ term =>
      exact ⟨term, (stageClass_eq_iff observations B term left).mp gluedB,
        (stageClass_eq_iff observations C term right).mp gluedC⟩
  · intro amalgamates x y equal
    induction x using Quotient.inductionOn with
    | _ left =>
      induction y using Quotient.inductionOn with
      | _ right =>
        obtain ⟨glued, gluedB, gluedC⟩ :=
          amalgamates ((stageClass_eq_iff observations A left right).mp equal)
        exact ⟨stageClass observations D glued,
          (stageClass_eq_iff observations B glued left).mpr gluedB,
          (stageClass_eq_iff observations C glued right).mpr gluedC⟩

/-- **Beck–Chevalley along forgetting, existential form, is amalgamation.** -/
theorem beckChevalley_exists_iff_amalgamates {A B C D : AdmissibleClass rules} (hAB : A ≤ B)
    (hAC : A ≤ C) (hBD : B ≤ D) (hCD : C ≤ D) :
    (∀ φ : Set (Stage observations B),
        reindex observations hAC (existsAlong observations hAB φ) =
          existsAlong observations hCD (reindex observations hBD φ)) ↔
      Amalgamates observations A B C :=
  (beckChevalley_exists_iff _ _ _ _ (restrict_square hAB hAC hBD hCD)).trans
    (isWeakPullback_iff_amalgamates hAB hAC hBD hCD)

/-- **Beck–Chevalley along forgetting, universal form, is amalgamation.** -/
theorem beckChevalley_forall_iff_amalgamates {A B C D : AdmissibleClass rules} (hAB : A ≤ B)
    (hAC : A ≤ C) (hBD : B ≤ D) (hCD : C ≤ D) :
    (∀ φ : Set (Stage observations B),
        reindex observations hAC (forallAlong observations hAB φ) =
          forallAlong observations hCD (reindex observations hBD φ)) ↔
      Amalgamates observations A B C :=
  (beckChevalley_forall_iff _ _ _ _ (restrict_square hAB hAC hBD hCD)).trans
    (isWeakPullback_iff_amalgamates hAB hAC hBD hCD)

/-- A square with an identity side always amalgamates. -/
theorem amalgamates_of_eq_left (A C : AdmissibleClass rules) :
    Amalgamates observations A A C :=
  fun _ right related => ⟨right, A.relEquiv_symm observations related,
    C.relEquiv_refl observations right⟩

/-- **The comparison map into the pullback is injective exactly when the square
is separated.** -/
theorem pairing_injective_iff_separated {B C D : AdmissibleClass rules} (hBD : B ≤ D)
    (hCD : C ≤ D) :
    Function.Injective
        (fun x : Stage observations D => (restrict observations hBD x, restrict observations hCD x)) ↔
      Separated observations B C D := by
  constructor
  · intro injective left right relatedB relatedC
    apply (stageClass_eq_iff observations D left right).mp
    apply injective
    exact Prod.ext ((stageClass_eq_iff observations B left right).mpr relatedB)
      ((stageClass_eq_iff observations C left right).mpr relatedC)
  · intro separated x y equal
    induction x using Quotient.inductionOn with
    | _ left =>
      induction y using Quotient.inductionOn with
      | _ right =>
        exact (stageClass_eq_iff observations D left right).mpr
          (separated ((stageClass_eq_iff observations B left right).mp (congrArg Prod.fst equal))
            ((stageClass_eq_iff observations C left right).mp (congrArg Prod.snd equal)))

/-- Separation says that the `D`-equivalence is the intersection of the `B`- and
`C`-equivalences. -/
theorem separated_iff_relEquiv_iff {B C D : AdmissibleClass rules} (hBD : B ≤ D)
    (hCD : C ≤ D) :
    Separated observations B C D ↔
      ∀ left right, D.RelEquiv observations left right ↔
        B.RelEquiv observations left right ∧ C.RelEquiv observations left right := by
  constructor
  · intro separated left right
    exact ⟨fun related => ⟨AdmissibleClass.relEquiv_antitone observations hBD related,
        AdmissibleClass.relEquiv_antitone observations hCD related⟩,
      fun both => separated both.1 both.2⟩
  · intro same left right relatedB relatedC
    exact (same left right).mpr ⟨relatedB, relatedC⟩

/-- A square whose top class is one of its sides is separated. -/
theorem separated_of_eq_left (B C : AdmissibleClass rules) :
    Separated observations B C B :=
  fun _ _ relatedB _ => relatedB

/-! ## Chains and sub-sites -/

variable (observations)

/-- The observer presheaf restricted along a monotone map of indices: a chain of
observer classes, or the inclusion of a sub-site. -/
def restrictedPresheaf {I : Type uW} [Preorder I] {chain : I → AdmissibleClass rules}
    (monotone : Monotone chain) : Iᵒᵖ ⥤ Type uS where
  obj i := Stage observations (chain i.unop)
  map f := TypeCat.ofHom (restrict observations (monotone (leOfHom f.unop)))
  map_id i := by
    ext x
    exact restrict_refl observations (chain i.unop) x
  map_comp f g := by
    ext x
    exact restrict_trans observations (monotone (leOfHom g.unop)) (monotone (leOfHom f.unop)) x

/-- The restricted presheaf is the composite of the chain with the observer
presheaf. -/
theorem restrictedPresheaf_eq_comp {I : Type uW} [Preorder I]
    {chain : I → AdmissibleClass rules} (monotone : Monotone chain) :
    restrictedPresheaf observations monotone = monotone.functor.op ⋙ observerPresheaf observations :=
  rfl

theorem restrictedPresheaf_map_apply {I : Type uW} [Preorder I]
    {chain : I → AdmissibleClass rules} (monotone : Monotone chain) {i j : I}
    (f : op j ⟶ op i) (x : Stage observations (chain j)) :
    (restrictedPresheaf observations monotone).map f x =
      restrict observations (monotone (leOfHom f.unop)) x :=
  rfl

/-! ## Stage predicates as observable predicates on terms -/

/-- A stage predicate read on terms. -/
def liftStage (D : AdmissibleClass rules) (φ : Set (Stage observations D)) : Set S.Term :=
  stageClass observations D ⁻¹' φ

open Mettapedia.Logic.TheoryModel in
/-- A stage predicate, read on terms, is observable for the stage's equivalence. -/
theorem liftStage_mem_observable (D : AdmissibleClass rules) (φ : Set (Stage observations D)) :
    liftStage observations D φ ∈
      observable (predicateSat (Str := S.Term)) (D.saturated observations).behavioralSetoid := by
  intro left right related
  change stageClass observations D left ∈ φ ↔ stageClass observations D right ∈ φ
  rw [(stageClass_eq_iff observations D left right).mpr related]

open Mettapedia.Logic.TheoryModel in
/-- **The observable predicates of a stage are exactly its stage predicates read on
terms.** -/
theorem range_liftStage (D : AdmissibleClass rules) :
    Set.range (liftStage observations D) =
      observable (predicateSat (Str := S.Term)) (D.saturated observations).behavioralSetoid := by
  apply Set.Subset.antisymm
  · rintro _ ⟨φ, rfl⟩
    exact liftStage_mem_observable observations D φ
  · intro ψ invariant
    refine ⟨{x | ∃ term, stageClass observations D term = x ∧ term ∈ ψ}, ?_⟩
    ext term
    constructor
    · rintro ⟨witness, equal, member⟩
      exact (invariant ((stageClass_eq_iff observations D witness term).mp equal)).mp member
    · intro member
      exact ⟨term, rfl, member⟩

/-- Reindexing along forgetting does not change a predicate read on terms. -/
theorem liftStage_reindex {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : Set (Stage observations A)) :
    liftStage observations B (reindex observations le φ) = liftStage observations A φ :=
  rfl

/-- The behavioural setoid of a finer class is finer. -/
theorem behavioralSetoid_le {A B : AdmissibleClass rules} (le : A ≤ B) :
    (B.saturated observations).behavioralSetoid ≤ (A.saturated observations).behavioralSetoid :=
  fun _ _ related => AdmissibleClass.relEquiv_antitone observations le related

open Mettapedia.Logic.TheoryModel in
/-- **Reindexing is the inclusion of observable predicates.**  The predicates a
coarser class observes are among those a finer class observes: this is
`observable_anti` of the theory–model framework, applied to stage predicates. -/
theorem observable_subset_of_le {A B : AdmissibleClass rules} (le : A ≤ B) :
    observable (predicateSat (Str := S.Term)) (A.saturated observations).behavioralSetoid ⊆
      observable (predicateSat (Str := S.Term)) (B.saturated observations).behavioralSetoid :=
  observable_anti (behavioralSetoid_le observations le)

end AdmissibleClass

end Mettapedia.GSLT.AdmissibleContextCongruence
