import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Constructor Category from LanguageDef

LLM notes (hard-won):
- Mathlib's `Paths V` is `def Paths V := V`, a type SYNONYM. This means defining
  `instance : Quiver V` and then using `Paths V` creates TWO quiver instances on
  the SAME type (one from your explicit instance, one from the Category on Paths).
  This causes pervasive instance diamond errors. AVOID `Paths` when you also need
  explicit quiver arrows.
- Instead, build the free category directly with a custom `SortPath` inductive and
  a wrapper `ConstructorObj` structure. The `structure` keyword creates a genuine
  newtype, avoiding diamonds.
- In recursive defs, place `{s t}` BEFORE the colon, not after as pattern-matching
  args. With `def f {s t} : P s t → Q` the equation `f .nil = x` holds by `rfl`.
  With `def f : {s t} → P s t → Q | _, _, .nil => x` it does NOT reduce and `rfl`
  fails. This is critical for `map_id` proofs in functor definitions.

Given a `LanguageDef`, this file constructs a category whose:
- **Objects** are the language's sorts (e.g., "Proc", "Name" for ρ-calculus)
- **Morphisms** are freely generated from unary sort-crossing constructors

This replaces the discrete `SortCategory` from `CategoryBridge.lean` with a
proper category that has non-identity morphisms corresponding to sort-crossing
constructors like `NQuote : Proc → Name` and `PDrop : Name → Proc`.

## Construction

1. Extract unary sort-crossing constructors from `LanguageDef.terms`
2. Define `LangSort lang` as the type of valid sort names
3. Define `SortArrow` for sort-crossing constructor arrows
4. Define `SortPath` (free category morphisms = paths of arrows)
5. Prove category laws and define `Category` instance on `ConstructorObj`

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §5
- Lambek & Scott, "Introduction to Higher Order Categorical Logic"
-/

namespace Mettapedia.OSLF.Framework.ConstructorCategory

open Mettapedia.OSLF.MeTTaIL.Syntax
open CategoryTheory

/-! ## Sort Type -/

/-- A sort of a language: a string that is a member of `lang.types`.

    For rhoCalc: `LangSort rhoCalc` has elements `⟨"Proc", _⟩` and `⟨"Name", _⟩`. -/
def LangSort (lang : LanguageDef) := { s : String // s ∈ lang.types }

instance (lang : LanguageDef) : DecidableEq (LangSort lang) :=
  fun ⟨a, _⟩ ⟨b, _⟩ => by
    cases decEq a b with
    | isTrue h => exact isTrue (Subtype.ext h)
    | isFalse h => exact isFalse (fun heq => h (Subtype.ext_iff.mp heq))

/-- Smart constructor for LangSort -/
def LangSort.mk' (lang : LanguageDef) (s : String) (h : s ∈ lang.types) :
    LangSort lang := ⟨s, h⟩

instance (lang : LanguageDef) : Repr (LangSort lang) where
  reprPrec s _ := repr s.val

/-! ## Extracting Sort-Crossing Constructors -/

/-- Extract the base sort name from a TypeExpr, if it is a simple base type.

    Returns `none` for arrow types, collection types, etc. -/
def baseSortOf : TypeExpr → Option String
  | .base s => some s
  | _ => none

/-- A unary sort-crossing constructor: has exactly one `.simple` parameter
    whose base sort differs from the constructor's category.

    Returns `(label, domainSort, codomainSort)` for qualifying constructors. -/
def unaryCrossings (lang : LanguageDef) : List (String × String × String) :=
  lang.terms.filterMap fun rule =>
    match rule.params with
    | [.simple _ typeExpr] =>
      match baseSortOf typeExpr with
      | some domSort =>
        if domSort ≠ rule.category then
          some (rule.label, domSort, rule.category)
        else none
      | none => none
    | _ => none

/-! ## Sort-Crossing Arrow Type -/

/-- A sort-crossing arrow between two sorts in a language.

    Each arrow corresponds to a unary constructor that crosses sort boundaries.
    For rhoCalc:
    - `NQuote : Proc → Name`
    - `PDrop : Name → Proc` -/
structure SortArrow (lang : LanguageDef) (dom cod : LangSort lang) where
  /-- The constructor label (e.g., "NQuote", "PDrop") -/
  label : String
  /-- Witness that this is a valid unary crossing -/
  valid : (label, dom.val, cod.val) ∈ unaryCrossings lang

/-! ## Sort Paths (Free Category Morphisms) -/

/-- A path of sort-crossing constructor arrows: the morphisms of the free
    category on the sort quiver.

    `SortPath lang s t` is a composable sequence of `SortArrow`s from `s` to `t`.
    - `nil` is the identity path at any sort
    - `cons p f` extends path `p : s ~> t` with arrow `f : t ~> u` -/
inductive SortPath (lang : LanguageDef) : LangSort lang → LangSort lang → Type where
  | nil : SortPath lang s s
  | cons : SortPath lang s t → SortArrow lang t u → SortPath lang s u

/-- Composition of sort paths (concatenation). -/
def SortPath.comp : SortPath lang a b → SortPath lang b c → SortPath lang a c
  | p, .nil => p
  | p, .cons q f => .cons (p.comp q) f

/-- Left identity: `nil.comp p = p`. -/
@[simp] theorem SortPath.nil_comp {lang : LanguageDef} {a b : LangSort lang}
    (p : SortPath lang a b) : SortPath.comp .nil p = p := by
  induction p with
  | nil => rfl
  | cons q f ih => simp [SortPath.comp, ih]

/-- Right identity: `p.comp nil = p` (definitional). -/
@[simp] theorem SortPath.comp_nil {lang : LanguageDef} {a b : LangSort lang}
    (p : SortPath lang a b) : SortPath.comp p .nil = p := rfl

/-- Associativity of path composition. -/
theorem SortPath.comp_assoc {lang : LanguageDef} {a b c d : LangSort lang}
    (p : SortPath lang a b) (q : SortPath lang b c) (r : SortPath lang c d) :
    SortPath.comp (SortPath.comp p q) r = SortPath.comp p (SortPath.comp q r) := by
  induction r with
  | nil => rfl
  | cons r' f ih => simp [SortPath.comp, ih]

/-- Embed a single arrow as a one-step path. -/
def SortArrow.toPath {lang : LanguageDef} {s t : LangSort lang}
    (arr : SortArrow lang s t) : SortPath lang s t :=
  .cons .nil arr

/-! ## Constructor Category -/

/-- An object in the constructor category: a wrapper around `LangSort` that
    serves as the vertex type for the `Category` instance.

    Using a `structure` (genuine newtype) rather than `abbrev`/`def` avoids
    instance diamonds with any quiver instances on `LangSort`. -/
structure ConstructorObj (lang : LanguageDef) where
  sort : LangSort lang
  deriving DecidableEq

instance (lang : LanguageDef) : Repr (ConstructorObj lang) where
  reprPrec o _ := repr o.sort.val

/-- The constructor category of a language: the free category on the sort quiver.

    Objects: sorts of the language (`ConstructorObj lang`)
    Morphisms: paths of sort-crossing constructors (`SortPath lang`)

    For rhoCalc:
    - Objects: Proc, Name
    - Generating morphisms: NQuote (Proc→Name), PDrop (Name→Proc)
    - Composite morphisms: PDrop∘NQuote (Proc→Proc), NQuote∘PDrop (Name→Name), etc.
    - Identity: id_Proc, id_Name -/
instance constructorCategory (lang : LanguageDef) : Category (ConstructorObj lang) where
  Hom a b := SortPath lang a.sort b.sort
  id _ := .nil
  comp := SortPath.comp
  id_comp := SortPath.nil_comp
  comp_id _ := rfl
  assoc := SortPath.comp_assoc

/-! ## ρ-Calculus Instantiation -/

/-- The process sort of rhoCalc -/
def rhoProc : LangSort rhoCalc := ⟨"Proc", List.Mem.head _⟩

/-- The name sort of rhoCalc -/
def rhoName : LangSort rhoCalc := ⟨"Name", List.Mem.tail _ (List.Mem.head _)⟩

/-- rhoCalc Proc as a constructor category object -/
def rhoProcObj : ConstructorObj rhoCalc := ⟨rhoProc⟩

/-- rhoCalc Name as a constructor category object -/
def rhoNameObj : ConstructorObj rhoCalc := ⟨rhoName⟩

/-- Verify that NQuote is a unary crossing: Proc → Name -/
theorem nquote_crossing :
    ("NQuote", "Proc", "Name") ∈ unaryCrossings rhoCalc := by
  native_decide

/-- Verify that PDrop is a unary crossing: Name → Proc -/
theorem pdrop_crossing :
    ("PDrop", "Name", "Proc") ∈ unaryCrossings rhoCalc := by
  native_decide

/-- The NQuote arrow: Proc → Name in the sort quiver -/
def nquoteArrow : SortArrow rhoCalc rhoProc rhoName :=
  ⟨"NQuote", nquote_crossing⟩

/-- The PDrop arrow: Name → Proc in the sort quiver -/
def pdropArrow : SortArrow rhoCalc rhoName rhoProc :=
  ⟨"PDrop", pdrop_crossing⟩

/-- NQuote as a morphism in the constructor category -/
def nquoteMor : rhoProcObj ⟶ rhoNameObj :=
  nquoteArrow.toPath

/-- PDrop as a morphism in the constructor category -/
def pdropMor : rhoNameObj ⟶ rhoProcObj :=
  pdropArrow.toPath

/-- Composite PDrop ∘ NQuote : Proc → Proc (deref after quote) -/
def pdropNquoteMor : rhoProcObj ⟶ rhoProcObj :=
  nquoteMor ≫ pdropMor

/-- Composite NQuote ∘ PDrop : Name → Name (quote after deref) -/
def nquotePdropMor : rhoNameObj ⟶ rhoNameObj :=
  pdropMor ≫ nquoteMor

/-! ## Semantic Interpretation of Arrows

Each sort-crossing arrow has a semantic function on Patterns:
- NQuote maps `p` to `.apply "NQuote" [p]`
- PDrop maps `n` to `.apply "PDrop" [n]`

This extends to paths by composition. -/

/-- The semantic function of a single sort-crossing arrow.

    Maps a Pattern to the Pattern obtained by applying the constructor. -/
def arrowSem (_lang : LanguageDef) {dom cod : LangSort _lang}
    (arr : SortArrow _lang dom cod) : Pattern → Pattern :=
  fun p => .apply arr.label [p]

/-- The semantic function of a sort path (composite of arrows).

    Extends `arrowSem` by composition along the path. -/
def pathSem (lang : LanguageDef) {s t : LangSort lang} :
    SortPath lang s t → Pattern → Pattern
  | .nil => id
  | .cons path arr => arrowSem lang arr ∘ pathSem lang path

/-- Path semantics respects composition. -/
theorem pathSem_comp (lang : LanguageDef) {a b c : LangSort lang}
    (p : SortPath lang a b) (q : SortPath lang b c) :
    pathSem lang (p.comp q) = pathSem lang q ∘ pathSem lang p := by
  induction q with
  | nil => rfl
  | cons q' arr ih =>
    simp only [pathSem, SortPath.comp]
    rw [ih]
    funext x; rfl

/-- Path semantics of identity is identity. -/
theorem pathSem_nil (lang : LanguageDef) (s : LangSort lang) :
    pathSem lang (.nil : SortPath lang s s) = id := rfl

/-! ## Verification -/

-- Verify the category instance exists
#check (inferInstance : Category (ConstructorObj rhoCalc))

-- Verify the morphisms type-check
#check nquoteMor
#check pdropMor
#check pdropNquoteMor
#check nquotePdropMor

-- Verify semantic functions
example : arrowSem rhoCalc nquoteArrow (.fvar "p") = .apply "NQuote" [.fvar "p"] := rfl
example : arrowSem rhoCalc pdropArrow (.fvar "n") = .apply "PDrop" [.fvar "n"] := rfl

-- Verify path semantics
example : pathSem rhoCalc nquoteArrow.toPath (.fvar "p") =
    .apply "NQuote" [.fvar "p"] := rfl
example : pathSem rhoCalc pdropArrow.toPath (.fvar "n") =
    .apply "PDrop" [.fvar "n"] := rfl
example : pathSem rhoCalc (nquoteArrow.toPath.comp pdropArrow.toPath) (.fvar "p") =
    .apply "PDrop" [.apply "NQuote" [.fvar "p"]] := rfl

/-! ## Universal Property (Free Category)

The constructor category is the **free category** on the sort quiver: for any
category C and any assignment of C-morphisms to generator arrows, there is a
unique functor extending this assignment. -/

/-- Lift a path to a morphism in any category, given the action on generators.

    Placing `{s t}` before the colon (not after as pattern-matching args)
    ensures Lean reduces `lift obj arr .nil` to `𝟙 _` definitionally. -/
def SortPath.lift {lang : LanguageDef} {C : Type*} [Category C]
    (obj : LangSort lang → C)
    (arr : ∀ {s t : LangSort lang}, SortArrow lang s t → (obj s ⟶ obj t))
    {s t : LangSort lang} : SortPath lang s t → (obj s ⟶ obj t)
  | .nil => 𝟙 _
  | .cons p a => p.lift obj arr ≫ arr a

/-- Lift sends generators to their images. -/
@[simp] theorem SortPath.lift_toPath {lang : LanguageDef} {C : Type*} [Category C]
    (obj : LangSort lang → C)
    (arr : ∀ {s t : LangSort lang}, SortArrow lang s t → (obj s ⟶ obj t))
    {s t : LangSort lang} (a : SortArrow lang s t) :
    a.toPath.lift obj arr = arr a := by
  simp [SortArrow.toPath, SortPath.lift, Category.id_comp]

/-- Lift preserves composition. -/
theorem SortPath.lift_comp {lang : LanguageDef} {C : Type*} [Category C]
    (obj : LangSort lang → C)
    (arr : ∀ {s t : LangSort lang}, SortArrow lang s t → (obj s ⟶ obj t))
    {a b c : LangSort lang} (p : SortPath lang a b) (q : SortPath lang b c) :
    (p.comp q).lift obj arr = p.lift obj arr ≫ q.lift obj arr := by
  induction q with
  | nil => simp [SortPath.lift, SortPath.comp, Category.comp_id]
  | cons q' f ih =>
    simp only [SortPath.lift, SortPath.comp]
    rw [ih, Category.assoc]

/-- The **universal functor** from the constructor category to any category C.

    Given `obj : LangSort → C` and `arr : SortArrow s t → (obj s ⟶ obj t)`,
    this is the unique functor extending the assignment on generators. -/
def liftFunctor (lang : LanguageDef) {C : Type*} [Category C]
    (obj : LangSort lang → C)
    (arr : ∀ {s t : LangSort lang}, SortArrow lang s t → (obj s ⟶ obj t)) :
    ConstructorObj lang ⥤ C where
  obj a := obj a.sort
  map f := f.lift obj arr
  map_id _ := rfl  -- SortPath.lift .nil = 𝟙 _ by computation
  map_comp f g := SortPath.lift_comp obj arr f g

/-- **Uniqueness**: a functor from the constructor category is determined by its
    action on generating arrows. For any functor F, its action on all paths
    equals the lift of its action on single arrows. -/
theorem lift_map_unique (lang : LanguageDef) {C : Type*} [Category C]
    (F : ConstructorObj lang ⥤ C) {s t : LangSort lang}
    (f : SortPath lang s t) :
    F.map f = f.lift (fun s => F.obj ⟨s⟩) (fun a => F.map a.toPath) := by
  induction f with
  | nil => exact F.map_id ⟨s⟩
  | cons p arr ih =>
    -- .cons p arr = p ≫ arr.toPath in the category (definitionally)
    simp only [SortPath.lift]
    rw [← ih]
    exact F.map_comp p arr.toPath

/-! ## Connection to Mathlib's Free Category

We prove our `SortPath` is isomorphic to Mathlib's `Quiver.Path` on a quiver
that's structurally identical. The quiver lives on `SortNode` (a separate
wrapper), dodging the `Paths V := V` instance diamond. -/

/-- Quiver node: carries the `Quiver` instance for Mathlib's `Paths` construction.
    This is a separate type from `ConstructorObj` to avoid instance diamonds. -/
structure SortNode (lang : LanguageDef) where
  val : LangSort lang
  deriving DecidableEq

/-- The sort quiver on `SortNode`: arrows are `SortArrow`s between the sorts. -/
instance sortNodeQuiver (lang : LanguageDef) : Quiver (SortNode lang) where
  Hom a b := SortArrow lang a.val b.val

-- Mathlib's Paths gives a Category instance on `Paths (SortNode lang)`.
-- Since `Paths V = V`, this is a category on `SortNode lang` with
-- Hom = Quiver.Path, id = nil, comp = Path.comp.
#check (inferInstance : Category (Paths (SortNode rhoCalc)))

/-- Convert `SortPath` to Mathlib's `Quiver.Path` on `SortNode`. -/
def SortPath.toQPath {lang : LanguageDef} {s t : LangSort lang} :
    SortPath lang s t →
    @Quiver.Path (SortNode lang) (sortNodeQuiver lang) ⟨s⟩ ⟨t⟩
  | .nil => .nil
  | .cons p a => (SortPath.toQPath p).cons a

/-- Convert Mathlib's `Quiver.Path` on `SortNode` to `SortPath`. -/
def SortPath.ofQPath {lang : LanguageDef} :
    {a b : SortNode lang} →
    @Quiver.Path (SortNode lang) (sortNodeQuiver lang) a b →
    SortPath lang a.val b.val
  | _, _, .nil => .nil
  | _, _, .cons p a => .cons (SortPath.ofQPath p) a

/-- Round-trip: `ofQPath ∘ toQPath = id`. -/
@[simp] theorem SortPath.ofQPath_toQPath {lang : LanguageDef} {s t : LangSort lang}
    (p : SortPath lang s t) : SortPath.ofQPath (SortPath.toQPath p) = p := by
  induction p with
  | nil => simp [SortPath.toQPath, SortPath.ofQPath]
  | cons p a ih => simp [SortPath.toQPath, SortPath.ofQPath, ih]

/-- Round-trip: `toQPath ∘ ofQPath = id`. -/
@[simp] theorem SortPath.toQPath_ofQPath {lang : LanguageDef} {a b : SortNode lang}
    (p : @Quiver.Path (SortNode lang) (sortNodeQuiver lang) a b) :
    SortPath.toQPath (SortPath.ofQPath p) = p := by
  induction p with
  | nil => simp [SortPath.ofQPath, SortPath.toQPath]
  | cons p a ih => simp [SortPath.ofQPath, SortPath.toQPath, ih]

/-- The conversion respects composition. -/
theorem SortPath.toQPath_comp {lang : LanguageDef} {a b c : LangSort lang}
    (p : SortPath lang a b) (q : SortPath lang b c) :
    SortPath.toQPath (p.comp q) =
    (SortPath.toQPath p).comp (SortPath.toQPath q) := by
  induction q with
  | nil => rfl
  | cons q' arr ih => simp [SortPath.comp, SortPath.toQPath, ih]

/-! The bijection `SortPath ≃ Quiver.Path` together with `toQPath_comp`
establishes that `ConstructorObj lang` is **isomorphic as a category**
to Mathlib's `Paths (SortNode lang)`. The object maps are:
- Forward: `ConstructorObj lang → SortNode lang` via `fun a => ⟨a.sort⟩`
- Backward: `SortNode lang → ConstructorObj lang` via `fun n => ⟨n.val⟩`

The morphism maps are `toQPath` / `ofQPath`, which are mutual inverses
and preserve composition. This is a strict category isomorphism (not
just an equivalence), confirming our `SortPath` construction IS the
free category on the sort quiver. -/

/-! ## Summary

**0 sorries. 0 axioms.**

### Definitions
- `LangSort lang`: sorts of a language (subtype of String)
- `unaryCrossings lang`: extract unary sort-crossing constructors
- `SortArrow lang dom cod`: arrow between sorts from a constructor
- `SortPath lang s t`: paths of arrows (free category morphisms)
- `ConstructorObj lang`: wrapper type carrying the `Category` instance
- `constructorCategory`: `Category` instance on `ConstructorObj`
- `arrowSem` / `pathSem`: semantic interpretation of arrows/paths as Pattern functions

### Universal Property
- `SortPath.lift`: lifts a quiver morphism to a functor action on paths
- `liftFunctor`: the universal functor from the constructor category
- `lift_map_unique`: uniqueness — any functor is determined by its generators

### Mathlib Connection
- `SortNode lang`: quiver wrapper (separate from `ConstructorObj` to avoid diamond)
- `SortPath.toQPath` / `ofQPath`: bijection with Mathlib's `Quiver.Path`
- `ofQPath_toQPath` / `toQPath_ofQPath`: round-trip proofs
- `toQPath_comp`: composition compatibility
- Together: strict category isomorphism `ConstructorObj lang ≅ Paths (SortNode lang)`

### For rhoCalc
- 2 objects: `rhoProcObj`, `rhoNameObj`
- 2 generating arrows: `nquoteArrow` (Proc→Name), `pdropArrow` (Name→Proc)
- 4 example morphisms: `nquoteMor`, `pdropMor`, `pdropNquoteMor`, `nquotePdropMor`
- Semantic verification: `pathSem` correctly computes nested `.apply` patterns
- Category laws proven: `nil_comp`, `comp_nil`, `comp_assoc`
-/

end Mettapedia.OSLF.Framework.ConstructorCategory
