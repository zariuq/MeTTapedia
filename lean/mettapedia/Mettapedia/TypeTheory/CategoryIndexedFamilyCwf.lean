import Mathlib.CategoryTheory.Elements
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.TypeTheory.RouteFamilyCwf

/-!
# The CwF of category-indexed families

A proof-relevant route context is a small category.  Its morphisms retain
which route was taken and compose as routes do.  A dependent type over such a
context is a covariant functor to `Type`; a term is a natural section; and
context comprehension is the category of elements.

This module also locates the exact boundary of the proposition-valued route
model.  A category-indexed family descends to the support relation
`Nonempty (x ⟶ y)` exactly when all parallel morphisms induce the same map on
the family.  Thus proposition truncation is lawful for route-insensitive
families and is provably unavailable for families that observe path identity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.RouteFamilyCwf
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

universe u

/-! ## Contexts, substitutions, families, and terms -/

/-- A proof-relevant context is a small category. -/
abbrev Context := Cat.{u, u}

/-- Substitutions are ordinary functors between the underlying categories. -/
abbrev ContextHom (source target : Context.{u}) :=
  (source : Type u) ⥤ (target : Type u)

/-- Identity substitution. -/
def contextIdentity (context : Context.{u}) : ContextHom context context :=
  𝟭 (context : Type u)

/-- Composition in execution order. -/
def contextCompose {first middle last : Context.{u}}
    (earlier : ContextHom first middle) (later : ContextHom middle last) :
    ContextHom first last :=
  earlier ⋙ later

/-- A dependent family over a proof-relevant context. -/
abbrev IndexedFamily (context : Context.{u}) :=
  (context : Type u) ⥤ Type u

/-- Terms are natural sections of their family. -/
abbrev IndexedSection {context : Context.{u}}
    (family : IndexedFamily context) :=
  family.sections

/-- Reindex a family by functor precomposition. -/
def reindexFamily {source target : Context.{u}}
    (family : IndexedFamily target) (substitution : ContextHom source target) :
    IndexedFamily source :=
  substitution ⋙ family

/-- Reindex a natural section by precomposition. -/
def reindexSection {source target : Context.{u}}
    {family : IndexedFamily target} (term : IndexedSection family)
    (substitution : ContextHom source target) :
    IndexedSection (reindexFamily family substitution) :=
  ⟨fun point => term.1 (substitution.obj point), fun route =>
    term.2 (substitution.map route)⟩

@[simp] theorem reindexSection_value {source target : Context.{u}}
    {family : IndexedFamily target} (term : IndexedSection family)
    (substitution : ContextHom source target) (point : source) :
    (reindexSection term substitution).1 point =
      term.1 (substitution.obj point) :=
  rfl

/-! ## Category-of-elements comprehension -/

/-- Extend a context by a category-indexed family. -/
def extend (context : Context.{u}) (family : IndexedFamily context) :
    Context.{u} :=
  Cat.of family.Elements

/-- The first projection from the category of elements. -/
def weaken {context : Context.{u}} (family : IndexedFamily context) :
    ContextHom (extend context family) context :=
  CategoryOfElements.π family

/-- The last variable is the canonical natural section over comprehension. -/
def lastVariable {context : Context.{u}} (family : IndexedFamily context) :
    IndexedSection (reindexFamily family (weaken family)) :=
  ⟨fun point => point.2, fun route => route.property⟩

/-- Pair a substitution and a term into the category of elements. -/
def pair {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target)
    (term : IndexedSection (reindexFamily family substitution)) :
    ContextHom source (extend target family) where
  obj point := ⟨substitution.obj point, term.1 point⟩
  map route := CategoryOfElements.homMk _ _ (substitution.map route)
    (term.2 route)
  map_id point := by
    apply CategoryOfElements.ext family
    exact substitution.map_id point
  map_comp earlier later := by
    apply CategoryOfElements.ext family
    exact substitution.map_comp earlier later

@[simp] theorem weaken_pair {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target)
    (term : IndexedSection (reindexFamily family substitution)) :
    contextCompose (pair substitution family term) (weaken family) =
      substitution := by
  rfl

/-! ## The category-indexed CwF -/

/-- Small categories, functors, category-indexed families, natural sections,
and categories of elements form a category with families. -/
def categoryIndexedCwf : Cwf where
  Ctx := Context.{u}
  Sub := ContextHom
  idS := contextIdentity
  compS later earlier := contextCompose earlier later
  id_comp substitution := Functor.comp_id substitution
  comp_id substitution := Functor.id_comp substitution
  comp_assoc later middle earlier :=
    (Functor.assoc earlier middle later).symm
  Ty := IndexedFamily
  tySub family substitution := reindexFamily family substitution
  tySub_id family := Functor.id_comp family
  tySub_comp family later earlier := Functor.assoc earlier later family
  Tm _ family := IndexedSection family
  tmSub term substitution := reindexSection term substitution
  tmSub_id term := by
    apply Subtype.ext
    rfl
  tmSub_comp term later earlier := by
    apply Subtype.ext
    rfl
  ext := extend
  wk family := weaken family
  vz family := lastVariable family
  pair substitution family term := pair substitution family term
  wk_pair substitution family term := weaken_pair substitution family term
  vz_pair substitution family term := by
    apply Subtype.ext
    rfl
  pair_eta family substitution := rfl

/-! ## Chosen terminal context -/

/-- The one-object discrete category is the empty dependent context. -/
abbrev emptyContext : Context.{u} :=
  CategoryTheory.Cat.of (Discrete PUnit)

/-- Every proof-relevant context has the constant functor to the empty
context. -/
def toEmpty (context : Context.{u}) : ContextHom context emptyContext :=
  (Functor.const (context : Type u)).obj (Discrete.mk PUnit.unit)

/-- The substitution into the empty context is unique. -/
theorem toEmpty_unique (context : Context.{u})
    (substitution : ContextHom context emptyContext) :
    substitution = toEmpty context := by
  exact Functor.ext (by simp [eq_iff_true_of_subsingleton])

/-- The category-indexed family CwF with its chosen terminal context. -/
def categoryIndexedCwfWithTerminal : CwfWithTerminal where
  toCwf := categoryIndexedCwf
  empty := emptyContext
  toEmpty := toEmpty
  toEmpty_unique := toEmpty_unique

/-! ## The proposition-truncated support and its descent criterion -/

/-- Forget which morphism was taken, retaining only existence of a route. -/
def thinSupport (context : Context.{u}) : RouteType.{u} where
  carrier := context
  Route source target := Nonempty (source ⟶ target)
  route_refl point := ⟨𝟙 point⟩

/-- A family is insensitive to parallel route identity when all parallel
morphisms induce the same fibre map. -/
def ParallelInvariant {context : Context.{u}}
    (family : IndexedFamily context) : Prop :=
  ∀ {source target : context} (left right : source ⟶ target),
    ∀ value : family.obj source,
      family.map left value = family.map right value

/-- A lawful descent to the proposition-valued route support, together with
the theorem that its chosen transport agrees with every original morphism. -/
structure ThinDescent {context : Context.{u}}
    (family : IndexedFamily context) where
  routeFamily : RouteFamily (thinSupport context)
  fibre_eq : routeFamily.fibre = family.obj
  transport_agrees : ∀ {source target : context}
    (route : source ⟶ target) (value : family.obj source),
    cast (congrFun fibre_eq target)
        (routeFamily.transport ⟨route⟩
          (cast (congrFun fibre_eq source).symm value)) =
      family.map route value

namespace ThinDescent

/-- Descent forces parallel morphisms to act identically. -/
theorem parallelInvariant {context : Context.{u}}
    {family : IndexedFamily context} (descent : ThinDescent family) :
    ParallelInvariant family := by
  intro source target left right value
  rw [← descent.transport_agrees left value,
    ← descent.transport_agrees right value]

/-- Parallel invariance is sufficient for descent.  Choice selects one
morphism from an inhabited hom fibre; invariance proves the result independent
of that selection. -/
noncomputable def ofParallelInvariant {context : Context.{u}}
    (family : IndexedFamily context) (invariant : ParallelInvariant family) :
    ThinDescent family where
  routeFamily :=
    { fibre := family.obj
      transport := fun route => family.map (Classical.choice route)
      transport_refl := by
        intro point value
        calc
          family.map (Classical.choice
              (show Nonempty
                  ((show context from point) ⟶ (show context from point)) from
                ⟨𝟙 (show context from point)⟩)) value =
              family.map (𝟙 (show context from point)) value :=
                invariant _ _ value
          _ = value := family.map_id_apply point value }
  fibre_eq := rfl
  transport_agrees := by
    intro source target route value
    exact invariant (Classical.choice
      (show Nonempty (source ⟶ target) from ⟨route⟩)) route value

/-- Exact criterion for proposition-truncated route descent. -/
theorem nonempty_iff_parallelInvariant {context : Context.{u}}
    (family : IndexedFamily context) :
    Nonempty (ThinDescent family) ↔ ParallelInvariant family := by
  constructor
  · rintro ⟨descent⟩
    exact descent.parallelInvariant
  · intro invariant
    exact ⟨ofParallelInvariant family invariant⟩

end ThinDescent

/-! ## Positive and negative controls -/

namespace Canary

/-- A constant family cannot observe route identity. -/
def constantBoolFamily (context : Context.{u}) : IndexedFamily context :=
  (Functor.const (context : Type u)).obj (ULift.{u} Bool)

theorem constantBool_parallelInvariant (context : Context.{u}) :
    ParallelInvariant (constantBoolFamily context) := by
  intro source target left right value
  rfl

theorem constantBool_descends (context : Context.{u}) :
    Nonempty (ThinDescent (constantBoolFamily context)) :=
  (ThinDescent.nonempty_iff_parallelInvariant _).2
    (constantBool_parallelInvariant context)

/-- The sole point of the two-loop category. -/
inductive TogglePoint : Type
  | star

/-- The one-object category with Boolean xor as route composition. -/
instance toggleCategoryStructure : Category TogglePoint where
  Hom _ _ := Bool
  id _ := false
  comp earlier later := xor earlier later
  id_comp route := by cases route <;> rfl
  comp_id route := by cases route <;> rfl
  assoc first second third := by
    cases first <;> cases second <;> cases third <;> rfl

/-- The proof-relevant context formed by the two-loop category. -/
def toggleContext : Context.{0} := Cat.of TogglePoint

/-- The Boolean action of a route: the identity loop preserves values and
the nontrivial loop negates them. -/
def toggleAction (route value : Bool) : Bool := xor route value

/-- The tautological action remembers which of the two loops was taken. -/
def toggleFamily : IndexedFamily toggleContext where
  obj _ := Bool
  map route := TypeCat.ofHom (toggleAction route)
  map_id point := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    cases value <;> rfl
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    cases earlier <;> cases later <;> cases value <;> rfl

/-- Names for the identity and nontrivial parallel loops. -/
def stayRoute : TogglePoint.star ⟶ TogglePoint.star := false
def flipRoute : TogglePoint.star ⟶ TogglePoint.star := true

/-- The two parallel loops are distinct. -/
theorem stayRoute_ne_flipRoute : stayRoute ≠ flipRoute :=
  Bool.false_ne_true

/-- The dependent action separates those two routes. -/
theorem toggleFamily_distinguishes_routes :
    toggleFamily.map stayRoute false ≠
      toggleFamily.map flipRoute false := by
  change false ≠ true
  exact Bool.false_ne_true

/-- Consequently this genuine proof-relevant family cannot descend through
the proposition-valued support relation. -/
theorem toggleFamily_does_not_descend :
    ¬ Nonempty (ThinDescent toggleFamily) := by
  intro descended
  have invariant : ParallelInvariant toggleFamily :=
    (ThinDescent.nonempty_iff_parallelInvariant toggleFamily).1 descended
  exact toggleFamily_distinguishes_routes
    (invariant (source := TogglePoint.star) (target := TogglePoint.star)
      stayRoute flipRoute false)

end Canary

#print axioms categoryIndexedCwf
#print axioms categoryIndexedCwfWithTerminal
#print axioms ThinDescent.parallelInvariant
#print axioms ThinDescent.nonempty_iff_parallelInvariant
#print axioms Canary.constantBool_descends
#print axioms Canary.stayRoute_ne_flipRoute
#print axioms Canary.toggleFamily_does_not_descend

end Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
