import Mettapedia.GSLT.LanguageDef.MultiSortedCloneFiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Clone translations and finite-product context categories

A fixed-sort clone translation preserves positional projections and simultaneous
substitution. It induces a functor between the actual categories of ordered
contexts, preserving terminal contexts and all finite products. In particular,
this is a reusable categorical interface for interpreting authored operations
through equation quotients.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory

universe u v w z

/-- A fixed-sort translation of multisorted clones, preserving variables and
simultaneous substitution. -/
structure CloneTranslation {Sorts : Type u}
    (source : MultiSortedClone.{u, v} Sorts)
    (target : MultiSortedClone.{u, w} Sorts) where
  map : {Γ : List Sorts} → {sort : Sorts} →
    source.Hom Γ sort → target.Hom Γ sort
  map_project : ∀ {Γ : List Sorts} (index : Fin Γ.length),
    map (source.project index) = target.project index
  map_substitute : ∀ {Γ Δ : List Sorts} {sort : Sorts}
    (term : source.Hom Γ sort)
    (env : (index : Fin Γ.length) → source.Hom Δ (Γ.get index)),
    map (source.substitute term env) =
      target.substitute (map term) (fun i => map (env i))

/-- Clone translations are determined by their action on all operations. -/
@[ext] theorem CloneTranslation.ext {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    {first second : CloneTranslation source target}
    (agree : ∀ {Γ : List Sorts} {sort : Sorts}
      (term : source.Hom Γ sort), first.map term = second.map term) :
    first = second := by
  cases first with
  | mk firstMap firstProject firstSubstitute =>
    cases second with
    | mk secondMap secondProject secondSubstitute =>
      have mapsEqual : @firstMap = @secondMap := by
        funext Γ sort term
        exact agree term
      cases mapsEqual
      rfl

/-- The categorical action of a clone translation on ordered contexts and
their substitution arrows. -/
def CloneTranslation.contextFunctor {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target) :
    MultiSortedClone.ContextObject source ⥤
      MultiSortedClone.ContextObject target where
  obj Γ := MultiSortedClone.ContextObject.ofList target Γ.context
  map f := fun i => translation.map (f i)
  map_id Γ := by
    funext i
    exact translation.map_project i
  map_comp f g := by
    funext i
    exact translation.map_substitute (g i) f

theorem CloneTranslation.map_weakenOperation {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target)
    {Γ : List Sorts} {input output : Sorts}
    (term : source.Hom Γ output) :
    translation.map (MultiSortedClone.weakenOperation source (input := input) term) =
      MultiSortedClone.weakenOperation target (input := input) (translation.map term) := by
  unfold MultiSortedClone.weakenOperation
  rw [translation.map_substitute]
  congr 1
  funext i
  exact translation.map_project (Γ := input :: Γ) i.succ

theorem CloneTranslation.map_leftProjection {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target) :
    ∀ (first second : List Sorts) (i : Fin first.length),
      translation.map
        (MultiSortedClone.leftProjectionEnvironment source first second i) =
        MultiSortedClone.leftProjectionEnvironment target first second i := by
  intro first
  induction first with
  | nil =>
      intro second i
      exact Fin.elim0 i
  | cons input rest inductionHypothesis =>
      intro second i
      refine Fin.cases ?_ (fun later => ?_) i
      · exact translation.map_project
          (⟨0, Nat.zero_lt_succ _⟩ : Fin (input :: rest ++ second).length)
      · change translation.map
          (MultiSortedClone.weakenOperation source
            (MultiSortedClone.leftProjectionEnvironment source rest second later)) =
          MultiSortedClone.weakenOperation target
            (MultiSortedClone.leftProjectionEnvironment target rest second later)
        rw [translation.map_weakenOperation, inductionHypothesis second later]

theorem CloneTranslation.map_rightProjection {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target) :
    ∀ (first second : List Sorts) (i : Fin second.length),
      translation.map
        (MultiSortedClone.rightProjectionEnvironment source first second i) =
        MultiSortedClone.rightProjectionEnvironment target first second i := by
  intro first
  induction first with
  | nil =>
      intro second i
      exact translation.map_project i
  | cons input rest inductionHypothesis =>
      intro second i
      change translation.map
        (MultiSortedClone.weakenOperation source
          (MultiSortedClone.rightProjectionEnvironment source rest second i)) =
        MultiSortedClone.weakenOperation target
          (MultiSortedClone.rightProjectionEnvironment target rest second i)
      rw [translation.map_weakenOperation, inductionHypothesis second i]

theorem CloneTranslation.map_fstProjection {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target)
    (first second : MultiSortedClone.ContextObject source) :
    translation.contextFunctor.map
        (MultiSortedClone.fstProjection source first second) =
      MultiSortedClone.fstProjection target
        (translation.contextFunctor.obj first)
        (translation.contextFunctor.obj second) := by
  funext i
  exact translation.map_leftProjection first.context second.context i

theorem CloneTranslation.map_sndProjection {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target)
    (first second : MultiSortedClone.ContextObject source) :
    translation.contextFunctor.map
        (MultiSortedClone.sndProjection source first second) =
      MultiSortedClone.sndProjection target
        (translation.contextFunctor.obj first)
        (translation.contextFunctor.obj second) := by
  funext i
  exact translation.map_rightProjection first.context second.context i

theorem CloneTranslation.map_appendEnvironment {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target)
    {Γ : List Sorts} :
    ∀ (first second : List Sorts)
      (left : source.Environment Γ first)
      (right : source.Environment Γ second)
      (i : Fin (first ++ second).length),
      translation.map
        (MultiSortedClone.appendEnvironment source first second left right i) =
      MultiSortedClone.appendEnvironment target first second
        (fun j => translation.map (left j))
        (fun j => translation.map (right j)) i := by
  intro first
  induction first with
  | nil =>
      intro second left right i
      rfl
  | cons input rest inductionHypothesis =>
      intro second left right i
      refine Fin.cases ?_ (fun later => ?_) i
      · rfl
      · exact inductionHypothesis second
          (fun j => left j.succ) right later

theorem CloneTranslation.map_pair {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target)
    {Γ first second : MultiSortedClone.ContextObject source}
    (left : Γ ⟶ first) (right : Γ ⟶ second) :
    translation.contextFunctor.map
        (MultiSortedClone.pair source left right) =
      MultiSortedClone.pair target
        (translation.contextFunctor.map left)
        (translation.contextFunctor.map right) := by
  funext i
  exact translation.map_appendEnvironment first.context second.context
    left right i

/-- The image of the concrete concatenation product is the target clone's
concatenation product, not merely a pair of commuting projections. -/
def CloneTranslation.mappedConcatIsLimit {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target)
    (first second : MultiSortedClone.ContextObject source) :
    CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.BinaryFan.mk
        (translation.contextFunctor.map
          (MultiSortedClone.fstProjection source first second))
        (translation.contextFunctor.map
          (MultiSortedClone.sndProjection source first second))) := by
  rw [translation.map_fstProjection, translation.map_sndProjection]
  exact MultiSortedClone.concatIsLimit target
    (translation.contextFunctor.obj first)
    (translation.contextFunctor.obj second)

theorem CloneTranslation.preservesPair {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target)
    (first second : MultiSortedClone.ContextObject source) :
    CategoryTheory.Limits.PreservesLimit
      (CategoryTheory.Limits.pair first second)
      translation.contextFunctor := by
  apply CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
    (MultiSortedClone.concatIsLimit source first second)
  exact (CategoryTheory.Limits.isLimitMapConeBinaryFanEquiv
    translation.contextFunctor
    (MultiSortedClone.fstProjection source first second)
    (MultiSortedClone.sndProjection source first second)).symm
      (translation.mappedConcatIsLimit first second)

theorem CloneTranslation.preservesTerminal {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target) :
    CategoryTheory.Limits.PreservesLimit
      (Functor.empty.{0} (MultiSortedClone.ContextObject source))
      translation.contextFunctor := by
  apply CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
    (MultiSortedClone.emptyIsTerminal source)
  refine (CategoryTheory.Limits.isLimitMapConeEmptyConeEquiv
    translation.contextFunctor
    (MultiSortedClone.ContextObject.ofList source [])).symm ?_
  change CategoryTheory.Limits.IsTerminal
    (MultiSortedClone.ContextObject.ofList target [])
  exact MultiSortedClone.emptyIsTerminal target

theorem CloneTranslation.preservesFiniteProducts {Sorts : Type u}
    {source : MultiSortedClone.{u, v} Sorts}
    {target : MultiSortedClone.{u, w} Sorts}
    (translation : CloneTranslation source target) :
    CategoryTheory.Limits.PreservesFiniteProducts translation.contextFunctor := by
  letI : CategoryTheory.Limits.PreservesLimitsOfShape
      (Discrete CategoryTheory.Limits.WalkingPair) translation.contextFunctor := by
    refine ⟨?_⟩
    intro K
    have : CategoryTheory.Limits.PreservesLimit
        (CategoryTheory.Limits.pair
          (K.obj ⟨CategoryTheory.Limits.WalkingPair.left⟩)
          (K.obj ⟨CategoryTheory.Limits.WalkingPair.right⟩))
        translation.contextFunctor :=
      translation.preservesPair _ _
    exact CategoryTheory.Limits.preservesLimit_of_iso_diagram
      translation.contextFunctor
      (CategoryTheory.Limits.diagramIsoPair K).symm
  letI : CategoryTheory.Limits.PreservesLimit
      (Functor.empty.{0} (MultiSortedClone.ContextObject source))
      translation.contextFunctor := translation.preservesTerminal
  letI : CategoryTheory.Limits.PreservesLimitsOfShape
      (Discrete.{0} PEmpty) translation.contextFunctor :=
    CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal
      translation.contextFunctor
  letI : CategoryTheory.Limits.HasFiniteProducts
      (MultiSortedClone.ContextObject source) :=
    CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal
  exact CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal
    translation.contextFunctor

/-- Identity translation preserves every operation exactly. -/
def CloneTranslation.id {Sorts : Type u}
    (clone : MultiSortedClone.{u, v} Sorts) :
    CloneTranslation clone clone where
  map := _root_.id
  map_project := by intros; rfl
  map_substitute := by intros; rfl

/-- Compose two same-sort clone translations. -/
def CloneTranslation.comp {Sorts : Type u}
    {first : MultiSortedClone.{u, v} Sorts}
    {middle : MultiSortedClone.{u, w} Sorts}
    {last : MultiSortedClone.{u, z} Sorts}
    (earlier : CloneTranslation first middle)
    (later : CloneTranslation middle last) :
    CloneTranslation first last where
  map := fun term => later.map (earlier.map term)
  map_project := by
    intro Γ i
    rw [earlier.map_project, later.map_project]
  map_substitute := by
    intro Γ Δ sort term env
    rw [earlier.map_substitute, later.map_substitute]

theorem CloneTranslation.contextFunctor_id {Sorts : Type u}
    (clone : MultiSortedClone.{u, v} Sorts) :
    (CloneTranslation.id clone).contextFunctor =
      Functor.id (MultiSortedClone.ContextObject clone) := by
  rfl

theorem CloneTranslation.contextFunctor_comp {Sorts : Type u}
    {first : MultiSortedClone.{u, v} Sorts}
    {middle : MultiSortedClone.{u, w} Sorts}
    {last : MultiSortedClone.{u, z} Sorts}
    (earlier : CloneTranslation first middle)
    (later : CloneTranslation middle last) :
    (earlier.comp later).contextFunctor =
      earlier.contextFunctor ⋙ later.contextFunctor := by
  rfl


end Mettapedia.GSLT.LanguageDef
