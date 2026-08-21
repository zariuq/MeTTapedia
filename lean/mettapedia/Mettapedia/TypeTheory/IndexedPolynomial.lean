import Mathlib.Logic.Equiv.Basic

/-!
# Indexed polynomial families

An `IndexedPolynomial Base Index` presents strictly positive recursive data in
a context `base : Base` and at an index `index : Index base`.

* `Shape base index` chooses a constructor, including all of its nonrecursive
  data.
* `Position shape` names the recursive arguments of that constructor.
* `next shape position` gives the index of each recursive argument.

The recursive family `Fix polynomial` is therefore strictly positive by
construction.  Its dependent eliminator and computation law are ordinary Lean
definitions rather than an external positivity predicate.  Reindexing along a
map of bases models substitution: the fixed family of the reindexed polynomial
is canonically equivalent to the reindexing of the original fixed family.

This file is independent of any object-language syntax.  A concrete dependent
type theory can use indexed polynomials as semantic descriptions, then prove
that its declarations, constructors, eliminators, and computation rules
realize those descriptions.
-/

namespace Mettapedia.TypeTheory

universe u v w uBase uIndex uShape uPosition uNewBase uSource uTarget

/-- A context-indexed dependent polynomial.  Recursive occurrences are exactly
the positions, and every position records the index of its recursive child. -/
structure IndexedPolynomial (Base : Type uBase) (Index : Base → Type uIndex) where
  Shape : (base : Base) → Index base → Type uShape
  Position : {base : Base} → {index : Index base} →
    Shape base index → Type uPosition
  next : {base : Base} → {index : Index base} →
    (shape : Shape base index) → Position shape → Index base

namespace IndexedPolynomial

variable {Base : Type uBase} {Index : Base → Type uIndex}

/-- The polynomial extension of a family. -/
def Extension
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    (family : (base : Base) → Index base → Type v)
    (base : Base) (index : Index base) :
    Type (max uShape uPosition v) :=
  Σ shape : polynomial.Shape base index,
    (position : polynomial.Position shape) →
      family base (polynomial.next shape position)

/-- A map of indexed families acts on recursive children while retaining the
constructor shape and every recursive position. -/
def Extension.map
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {source : (base : Base) → Index base → Type uSource}
    {target : (base : Base) → Index base → Type uTarget}
    (mapping : ∀ base index, source base index → target base index)
    {base : Base} {index : Index base} :
    polynomial.Extension source base index →
      polynomial.Extension target base index
  | ⟨shape, children⟩ =>
      ⟨shape, fun position =>
        mapping base (polynomial.next shape position) (children position)⟩

@[simp] theorem Extension.map_id
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {family : (base : Base) → Index base → Type v}
    {base : Base} {index : Index base}
    (layer : polynomial.Extension family base index) :
    Extension.map polynomial (fun _ _ value => value) layer = layer := by
  cases layer
  rfl

@[simp] theorem Extension.map_comp
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {first second third : (base : Base) → Index base → Type v}
    (earlier : ∀ base index, first base index → second base index)
    (later : ∀ base index, second base index → third base index)
    {base : Base} {index : Index base}
    (layer : polynomial.Extension first base index) :
    Extension.map polynomial later
        (Extension.map polynomial earlier layer) =
      Extension.map polynomial
        (fun base index value => later base index (earlier base index value))
        layer := by
  cases layer
  rfl

/-- The least family closed under the constructors of an indexed polynomial. -/
inductive Fix
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    (base : Base) : Index base → Type (max uIndex uShape uPosition) where
  | roll {index : Index base}
      (shape : polynomial.Shape base index)
      (children : (position : polynomial.Position shape) →
        Fix polynomial base (polynomial.next shape position)) :
      Fix polynomial base index

namespace Fix

variable
  (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
    Base Index)

/-- Expose the top polynomial layer of a fixed point. -/
def out {base : Base} {index : Index base} :
    Fix polynomial base index →
      polynomial.Extension (Fix polynomial) base index
  | .roll shape children => ⟨shape, children⟩

/-- Build a fixed point from one polynomial layer. -/
def rollExtension {base : Base} {index : Index base} :
    polynomial.Extension (Fix polynomial) base index →
      Fix polynomial base index
  | ⟨shape, children⟩ => .roll shape children

@[simp] theorem rollExtension_out {base : Base} {index : Index base}
    (tree : Fix polynomial base index) :
    Fix.rollExtension polynomial (Fix.out polynomial tree) = tree := by
  cases tree
  rfl

@[simp] theorem out_rollExtension {base : Base} {index : Index base}
    (layer : polynomial.Extension (Fix polynomial) base index) :
    Fix.out polynomial (Fix.rollExtension polynomial layer) = layer := by
  cases layer
  rfl

/-- Dependent elimination for the fixed family. -/
@[elab_as_elim]
noncomputable def eliminate
    (motive : ∀ base index, Fix polynomial base index → Sort w)
    (method : ∀ base index
      (shape : polynomial.Shape base index)
      (children : (position : polynomial.Position shape) →
        Fix polynomial base (polynomial.next shape position)),
      (∀ position, motive base (polynomial.next shape position)
        (children position)) →
      motive base index (.roll shape children))
    (base : Base) :
    ∀ index (tree : Fix polynomial base index), motive base index tree :=
  @Fix.rec Base Index polynomial base
    (fun index tree => motive base index tree)
    (fun {index} shape children hypotheses =>
      method base index shape children hypotheses)

/-- The dependent eliminator computes at every constructor. -/
@[simp] theorem eliminate_roll
    (motive : ∀ base index, Fix polynomial base index → Sort w)
    (method : ∀ base index
      (shape : polynomial.Shape base index)
      (children : (position : polynomial.Position shape) →
        Fix polynomial base (polynomial.next shape position)),
      (∀ position, motive base (polynomial.next shape position)
        (children position)) →
      motive base index (.roll shape children))
    {base : Base} {index : Index base}
    (shape : polynomial.Shape base index)
    (children : (position : polynomial.Position shape) →
      Fix polynomial base (polynomial.next shape position)) :
    eliminate polynomial motive method base index (.roll shape children) =
      method base index shape children
        (fun position =>
          eliminate polynomial motive method base _ (children position)) :=
  rfl

/-- The catamorphism into an arbitrary indexed algebra. -/
noncomputable def fold
    {carrier : (base : Base) → Index base → Type v}
    (algebra : ∀ base index,
      polynomial.Extension carrier base index → carrier base index) :
    ∀ base index, Fix polynomial base index → carrier base index :=
  eliminate polynomial (fun base index _ => carrier base index)
    (fun base index shape _children foldedChildren =>
      algebra base index ⟨shape, foldedChildren⟩)

/-- Folding commutes with every constructor. -/
@[simp] theorem fold_roll
    {carrier : (base : Base) → Index base → Type v}
    (algebra : ∀ base index,
      polynomial.Extension carrier base index → carrier base index)
    {base : Base} {index : Index base}
    (shape : polynomial.Shape base index)
    (children : (position : polynomial.Position shape) →
      Fix polynomial base (polynomial.next shape position)) :
    fold polynomial algebra base index (.roll shape children) =
      algebra base index
        ⟨shape, fun position =>
          fold polynomial algebra base _ (children position)⟩ :=
  rfl

end Fix

/-! ## Indexed algebras and initiality -/

/-- An algebra for an indexed polynomial on a chosen carrier family. -/
structure Algebra
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    (carrier : (base : Base) → Index base → Type v) where
  act : ∀ base index,
    polynomial.Extension carrier base index → carrier base index

namespace Algebra

variable
  {polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
    Base Index}
variable {source : (base : Base) → Index base → Type uSource}
variable {target : (base : Base) → Index base → Type uTarget}

/-- A homomorphism of indexed polynomial algebras. -/
structure Hom (sourceAlgebra : Algebra polynomial source)
    (targetAlgebra : Algebra polynomial target) where
  toFun : ∀ base index, source base index → target base index
  commutes : ∀ base index
    (layer : polynomial.Extension source base index),
    toFun base index (sourceAlgebra.act base index layer) =
      targetAlgebra.act base index
        (Extension.map polynomial toFun layer)

/-- The fixed family carries the constructor algebra. -/
def initial (polynomial : IndexedPolynomial Base Index) :
    Algebra polynomial (Fix polynomial) where
  act := fun _ _ layer => Fix.rollExtension polynomial layer

/-- Folding is an algebra homomorphism from the fixed family. -/
noncomputable def foldHom (targetAlgebra : Algebra polynomial target) :
    Hom (initial polynomial) targetAlgebra where
  toFun := Fix.fold polynomial targetAlgebra.act
  commutes := by
    intro base index layer
    cases layer
    rfl

/-- Every algebra homomorphism out of the fixed family is the fold. -/
theorem hom_eq_fold (targetAlgebra : Algebra polynomial target)
    (homomorphism : Hom (initial polynomial) targetAlgebra) :
    ∀ base index (tree : Fix polynomial base index),
      homomorphism.toFun base index tree =
        Fix.fold polynomial targetAlgebra.act base index tree := by
  intro base index tree
  exact
    @Fix.rec Base Index polynomial base
      (fun index tree =>
        homomorphism.toFun base index tree =
          Fix.fold polynomial targetAlgebra.act base index tree)
      (fun {index} shape children hypotheses => by
      rw [show Fix.roll shape children =
        (initial polynomial).act base index ⟨shape, children⟩ from rfl]
      rw [homomorphism.commutes]
      change targetAlgebra.act base index
          ⟨shape, fun position =>
            homomorphism.toFun base _ (children position)⟩ =
        targetAlgebra.act base index
          ⟨shape, fun position =>
            Fix.fold polynomial targetAlgebra.act base _
              (children position)⟩
      have childrenEqual :
          (fun position =>
            homomorphism.toFun base _ (children position)) =
          (fun position =>
            Fix.fold polynomial targetAlgebra.act base _
              (children position)) := by
        funext position
        exact hypotheses position
      rw [childrenEqual])
      index tree

end Algebra

/-! ## Substitution as base reindexing -/

/-- Reindex a polynomial along a substitution of base contexts. -/
def reindex
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {NewBase : Type uNewBase} (substitution : NewBase → Base) :
    IndexedPolynomial NewBase (fun newBase => Index (substitution newBase)) where
  Shape := fun newBase index => polynomial.Shape (substitution newBase) index
  Position := fun shape => polynomial.Position shape
  next := fun shape position => polynomial.next shape position

namespace Fix

/-- Interpret a fixed point of a reindexed polynomial in the original fixed
family at the substituted base. -/
noncomputable def reindexTo
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {NewBase : Type uNewBase} (substitution : NewBase → Base) :
    ∀ {base index}, Fix (polynomial.reindex substitution) base index →
      Fix polynomial (substitution base) index := by
  intro base
  exact
    @Fix.rec NewBase (fun newBase => Index (substitution newBase))
      (polynomial.reindex substitution) base
      (fun index _ => Fix polynomial (substitution base) index)
      (fun shape _children hypotheses => .roll shape hypotheses)

/-- Rebuild the fixed point of a reindexed polynomial from the original fixed
family at a substituted base. -/
noncomputable def reindexFrom
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {NewBase : Type uNewBase} (substitution : NewBase → Base) :
    ∀ {base index}, Fix polynomial (substitution base) index →
      Fix (polynomial.reindex substitution) base index := by
  intro base
  exact
    @Fix.rec Base Index polynomial (substitution base)
      (fun index _ => Fix (polynomial.reindex substitution) base index)
      (fun shape _children hypotheses => .roll shape hypotheses)

@[simp] theorem reindexFrom_to
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {NewBase : Type uNewBase} (substitution : NewBase → Base)
    {base : NewBase} {index : Index (substitution base)}
    (tree : Fix (polynomial.reindex substitution) base index) :
    reindexFrom polynomial substitution
        (reindexTo polynomial substitution tree) = tree := by
  exact
    @Fix.rec NewBase (fun newBase => Index (substitution newBase))
      (polynomial.reindex substitution) base
      (fun index tree =>
        reindexFrom polynomial substitution
            (reindexTo polynomial substitution tree) = tree)
      (fun shape children hypotheses => by
      simp only [reindexTo, reindexFrom]
      congr 1
      funext position
      exact hypotheses position)
      index tree

@[simp] theorem reindexTo_from
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {NewBase : Type uNewBase} (substitution : NewBase → Base)
    {base : NewBase} {index : Index (substitution base)}
    (tree : Fix polynomial (substitution base) index) :
    reindexTo polynomial substitution
        (reindexFrom polynomial substitution tree) = tree := by
  exact
    @Fix.rec Base Index polynomial (substitution base)
      (fun index tree =>
        reindexTo polynomial substitution
            (reindexFrom polynomial substitution tree) = tree)
      (fun shape children hypotheses => by
      simp only [reindexTo, reindexFrom]
      congr 1
      funext position
      exact hypotheses position)
      index tree

/-- Formation of a strictly-positive fixed family commutes with substitution,
up to a canonical equivalence retaining every constructor and child. -/
noncomputable def reindexEquiv
    (polynomial : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
      Base Index)
    {NewBase : Type uNewBase} (substitution : NewBase → Base)
    (base : NewBase) (index : Index (substitution base)) :
    Fix (polynomial.reindex substitution) base index ≃
      Fix polynomial (substitution base) index where
  toFun := reindexTo polynomial substitution
  invFun := reindexFrom polynomial substitution
  left_inv := reindexFrom_to polynomial substitution
  right_inv := reindexTo_from polynomial substitution

end Fix

/-! ## Strict-positivity boundary -/

/-- A representative negative occurrence: the recursive candidate appears in
the domain of a function. -/
def NegativeOccurrence (candidate : Type u) : Type u := candidate → Empty

/-- Negative occurrence is not covariant even before asking for functor laws.
The unique map `Empty → PUnit` would have to send an inhabitant of
`NegativeOccurrence Empty` to an inhabitant of `NegativeOccurrence PUnit`. -/
theorem negativeOccurrence_has_no_covariant_map :
    (∀ {source target : Type},
      (source → target) → NegativeOccurrence source →
        NegativeOccurrence target) → False := by
  intro mapping
  let impossible : NegativeOccurrence PUnit :=
    mapping (source := Empty) (target := PUnit)
      (fun empty => empty.elim) (fun empty => empty.elim)
  exact Empty.elim (impossible PUnit.unit)

/-! ## Lists as ordinary polynomial fixed points

Lists exercise the non-index-changing special case.  They are kept here as a
semantic instance of the general construction, independently of any concrete
object-language declaration syntax or runtime representation.
-/

namespace ListExample

/-- A universe-polymorphic singleton used for the closed parameter context and
the sole list-family index. -/
inductive One : Type u where
  | star

/-- A universe-polymorphic empty position type for the nullary constructor. -/
inductive Void : Type u

/-- List constructor shapes retain all nonrecursive constructor data. -/
inductive Shape (A : Type u) : Type u where
  | nil
  | cons (head : A)

/-- The list polynomial has no recursive position at `nil` and one recursive
tail position at `cons`. -/
@[reducible] def polynomial (A : Type u) :
    IndexedPolynomial.{u, u, u, u} (One.{u}) (fun _ => One.{u}) where
  Shape := fun _ _ => Shape A
  Position := fun shape =>
    match shape with
    | .nil => Void
    | .cons _ => One
  next := fun shape position =>
    match shape with
    | .nil => nomatch position
    | .cons _ => .star

/-- Lists are the fixed family of the list polynomial. -/
abbrev ListP (A : Type u) : Type u :=
  Fix (polynomial A) .star .star

def nilChildren {A : Type u} :
    (position : (polynomial A).Position (base := .star) (index := .star)
      (Shape.nil (A := A))) →
      ListP A :=
  fun position => nomatch position

def consChildren {A : Type u} {head : A} (tail : ListP A) :
    (position : (polynomial A).Position (base := .star) (index := .star)
      (Shape.cons head)) →
      ListP A :=
  fun _ => tail

/-- The nullary list constructor. -/
def nil {A : Type u} : ListP A :=
  .roll .nil nilChildren

/-- The binary list constructor: the head is nonrecursive shape data and the
tail occupies the unique recursive position. -/
def cons {A : Type u} (head : A) (tail : ListP A) : ListP A :=
  .roll (.cons head) (consChildren tail)

/-- Every presentation of the empty child assignment yields `nil`. -/
theorem roll_nil_eq_nil {A : Type u}
    (children :
      (position : (polynomial A).Position (base := .star) (index := .star)
        (Shape.nil (A := A))) →
        ListP A) :
    (Fix.roll .nil children : ListP A) = nil := by
  have childrenEqual : children = nilChildren := by
    funext position
    exact nomatch position
  rw [childrenEqual]
  rfl

/-- Every presentation of the singleton child assignment yields `cons`. -/
theorem roll_cons_eq_cons {A : Type u} (head : A)
    (children :
      (position : (polynomial A).Position (base := .star) (index := .star)
        (Shape.cons head)) → ListP A) :
    (Fix.roll (.cons head) children : ListP A) =
      cons head (children .star) := by
  have childrenEqual : children = consChildren (children .star) := by
    funext position
    cases position
    rfl
  rw [childrenEqual]
  rfl

/-- Transport a nullary branch to an arbitrary empty child assignment. -/
def motiveAtNil {A : Type u} (motive : ListP A → Sort v)
    (children :
      (position : (polynomial A).Position (base := .star) (index := .star)
        (Shape.nil (A := A))) →
        ListP A)
    (value : motive nil) :
    motive (Fix.roll .nil children) :=
  Eq.mpr (congrArg motive (roll_nil_eq_nil children)) value

/-- Transport a cons branch to an arbitrary singleton child assignment. -/
def motiveAtCons {A : Type u} (motive : ListP A → Sort v)
    (head : A)
    (children :
      (position : (polynomial A).Position (base := .star) (index := .star)
        (Shape.cons head)) → ListP A)
    (value : motive (cons head (children .star))) :
    motive (Fix.roll (.cons head) children) :=
  Eq.mpr (congrArg motive (roll_cons_eq_cons head children)) value

@[simp] theorem motiveAtNil_canonical {A : Type u}
    (motive : ListP A → Sort v) (value : motive nil) :
    motiveAtNil motive nilChildren value = value := by
  simp only [motiveAtNil, eq_mpr_eq_cast]
  exact eq_of_heq (cast_heq _ _)

@[simp] theorem motiveAtCons_canonical {A : Type u}
    (motive : ListP A → Sort v) (head : A) (tail : ListP A)
    (value : motive (cons head tail)) :
    motiveAtCons motive head (consChildren tail) value = value := by
  simp only [motiveAtCons, eq_mpr_eq_cast]
  exact eq_of_heq (cast_heq _ _)

/-- The usual dependent list eliminator, derived from the polynomial
eliminator rather than postulated for this instance. -/
noncomputable def eliminate {A : Type u}
    (motive : ListP A → Sort v)
    (nilCase : motive nil)
    (consCase : ∀ head tail, motive tail → motive (cons head tail)) :
    ∀ list : ListP A, motive list :=
  Fix.eliminate (polynomial A) (fun _ _ list => motive list)
    (fun _ _ shape children hypotheses => by
      cases shape with
      | nil => exact motiveAtNil motive children nilCase
      | cons head =>
          exact motiveAtCons motive head children
            (consCase head (children .star) (hypotheses .star)))
    .star .star

/-- List elimination computes at `nil`. -/
@[simp] theorem eliminate_nil {A : Type u}
    (motive : ListP A → Sort v)
    (nilCase : motive nil)
    (consCase : ∀ head tail, motive tail → motive (cons head tail)) :
    eliminate motive nilCase consCase nil = nilCase := by
  simp only [eliminate, nil, Fix.eliminate_roll, motiveAtNil_canonical]

/-- List elimination computes at `cons`. -/
@[simp] theorem eliminate_cons {A : Type u}
    (motive : ListP A → Sort v)
    (nilCase : motive nil)
    (consCase : ∀ head tail, motive tail → motive (cons head tail))
    (head : A) (tail : ListP A) :
    eliminate motive nilCase consCase (cons head tail) =
      consCase head tail (eliminate motive nilCase consCase tail) := by
  simp only [eliminate, cons, Fix.eliminate_roll, motiveAtCons_canonical]
  rfl

/-- Functorial action of lists, obtained from the native eliminator. -/
noncomputable def map {A : Type u} {B : Type v} (function : A → B) :
    ListP A → ListP B :=
  eliminate (fun _ => ListP B) nil
    (fun head _tail mappedTail => cons (function head) mappedTail)

@[simp] theorem map_nil {A : Type u} {B : Type v} (function : A → B) :
    map function nil = nil := by
  simp [map]

@[simp] theorem map_cons {A : Type u} {B : Type v}
    (function : A → B) (head : A) (tail : ListP A) :
    map function (cons head tail) = cons (function head) (map function tail) := by
  simp [map]

theorem map_id {A : Type u} (list : ListP A) :
    map (fun value => value) list = list := by
  apply eliminate (motive := fun list => map (fun value => value) list = list)
  · rfl
  · intro head tail hypothesis
    simp only [map_cons, hypothesis]

theorem map_comp {A : Type u} {B : Type v} {C : Type w}
    (earlier : A → B) (later : B → C) (list : ListP A) :
    map later (map earlier list) = map (later ∘ earlier) list := by
  apply eliminate
    (motive := fun list =>
      map later (map earlier list) = map (later ∘ earlier) list)
  · rfl
  · intro head tail hypothesis
    simp only [map_cons, hypothesis, Function.comp_apply]

/-- Structural length, used below to relate the indexed vector instance to
the ordinary list instance. -/
noncomputable def length {A : Type u} : ListP A → Nat :=
  eliminate (fun _ => Nat) 0 (fun _head _tail result => result + 1)

@[simp] theorem length_nil {A : Type u} : length (nil : ListP A) = 0 := by
  simp [length]

@[simp] theorem length_cons {A : Type u} (head : A) (tail : ListP A) :
    length (cons head tail) = length tail + 1 := by
  simp [length]

theorem length_map {A : Type u} {B : Type v} (function : A → B)
    (list : ListP A) : length (map function list) = length list := by
  apply eliminate
    (motive := fun list => length (map function list) = length list)
  · rfl
  · intro head tail hypothesis
    simp only [map_cons, length_cons, hypothesis]

/-- Interpret a polynomial list as Lean's ordinary inductive list. -/
noncomputable def toList {A : Type u} : ListP A → List A :=
  eliminate (fun _ => List A) [] (fun head _tail result => head :: result)

/-- Rebuild a polynomial list from Lean's ordinary inductive list. -/
def ofList {A : Type u} : List A → ListP A
  | [] => nil
  | head :: tail => cons head (ofList tail)

@[simp] theorem toList_nil {A : Type u} : toList (nil : ListP A) = [] := by
  simp [toList]

@[simp] theorem toList_cons {A : Type u} (head : A) (tail : ListP A) :
    toList (cons head tail) = head :: toList tail := by
  simp [toList]

@[simp] theorem toList_ofList {A : Type u} (list : List A) :
    toList (ofList list) = list := by
  induction list with
  | nil => rfl
  | cons head tail hypothesis => simp [ofList, hypothesis]

@[simp] theorem ofList_toList {A : Type u} (list : ListP A) :
    ofList (toList list) = list := by
  apply eliminate (motive := fun list => ofList (toList list) = list)
  · rfl
  · intro head tail hypothesis
    simp [ofList, hypothesis]

/-- The polynomial list is equivalent to the familiar inductive list, so the
generic construction has not introduced junk or lost constructors. -/
noncomputable def equivList (A : Type u) : ListP A ≃ List A where
  toFun := toList
  invFun := ofList
  left_inv := ofList_toList
  right_inv := toList_ofList

theorem toList_injective {A : Type u} :
    Function.Injective (@toList A) := by
  intro first second equality
  rw [← ofList_toList first, ← ofList_toList second, equality]

@[simp] theorem toList_map {A : Type u} {B : Type v}
    (function : A → B) (list : ListP A) :
    toList (map function list) = List.map function (toList list) := by
  apply eliminate
    (motive := fun list =>
      toList (map function list) = List.map function (toList list))
  · rfl
  · intro head tail hypothesis
    simp only [map_cons, toList_cons, List.map_cons, hypothesis]

/-! ### Proof-relevant relation lifting -/

/-- Pointwise equality retained as ordinary data rather than collapsed into
the definition of a relation. -/
abbrev Graph {A : Type u} {B : Type v} (function : A → B)
    (source : A) (target : B) : Type w :=
  ULift.{w} (PLift (function source = target))

/-- Proof-relevant pointwise lifting over ordinary list spines.  Keeping this
spine separate from the polynomial representation makes constructor
injectivity explicit; `RelLift` below transports it across `equivList`. -/
inductive ListRel {A : Type u} {B : Type v}
    (relation : A → B → Type w) : List A → List B →
      Type (max u v w) where
  | nil : ListRel relation [] []
  | cons {sourceHead : A} {targetHead : B}
      {sourceTail : List A} {targetTail : List B} :
      relation sourceHead targetHead →
      ListRel relation sourceTail targetTail →
      ListRel relation (sourceHead :: sourceTail)
        (targetHead :: targetTail)

namespace ListRel

/-- A pointwise map of relation evidence acts on every retained witness in a
list-relator derivation.  Endpoints and spine shape are unchanged. -/
def mapEvidence {A : Type u} {B : Type v}
    {earlier later : A → B → Type w}
    (map : ∀ source target, earlier source target → later source target) :
    {source : List A} → {target : List B} →
      ListRel earlier source target → ListRel later source target
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail =>
      .cons (map _ _ head) (mapEvidence map tail)

@[simp] theorem mapEvidence_nil {A : Type u} {B : Type v}
    {earlier later : A → B → Type w}
    (map : ∀ source target, earlier source target → later source target) :
    mapEvidence map (.nil : ListRel earlier [] []) = .nil :=
  rfl

@[simp] theorem mapEvidence_cons {A : Type u} {B : Type v}
    {earlier later : A → B → Type w}
    (map : ∀ source target, earlier source target → later source target)
    {sourceHead : A} {targetHead : B}
    {sourceTail : List A} {targetTail : List B}
    (head : earlier sourceHead targetHead)
    (tail : ListRel earlier sourceTail targetTail) :
    mapEvidence map (.cons head tail) =
      .cons (map sourceHead targetHead head) (mapEvidence map tail) :=
  rfl

/-- Pointwise equivalence of proof fibres lifts to an exact equivalence of
whole list-relator evidence.  In particular, this preserves branching
multiplicity rather than comparing only propositional support. -/
def evidenceEquiv {A : Type u} {B : Type v}
    {earlier later : A → B → Type w}
    (pointwise : ∀ source target,
      earlier source target ≃ later source target)
    (source : List A) (target : List B) :
    ListRel earlier source target ≃ ListRel later source target where
  toFun := mapEvidence (fun left right => pointwise left right)
  invFun := mapEvidence (fun left right => (pointwise left right).symm)
  left_inv := by
    intro evidence
    induction evidence with
    | nil => rfl
    | cons head tail hypothesis =>
        simp only [mapEvidence_cons]
        rw [hypothesis, Equiv.symm_apply_apply]
  right_inv := by
    intro evidence
    induction evidence with
    | nil => rfl
    | cons head tail hypothesis =>
        simp only [mapEvidence_cons]
        rw [hypothesis, Equiv.apply_symm_apply]

end ListRel

/-- The native polynomial-list relator, transported across the proved
no-junk/no-confusion representation equivalence. -/
abbrev RelLift {A : Type u} {B : Type v}
    (relation : A → B → Type w) (source : ListP A) (target : ListP B) :
    Type (max u v w) :=
  ListRel relation (toList source) (toList target)

/-- Relational map is the proof-relevant list relator.  The name emphasizes
its role as the nondeterministic generalization of `map`. -/
abbrev mapRel {A : Type u} {B : Type v}
    (relation : A → B → Type w) : ListP A → ListP B → Type (max u v w) :=
  RelLift relation

def listGraphLift {A : Type u} {B : Type v} (function : A → B) :
    ∀ source : List A,
      ListRel (Graph.{u, v, w} function) source (List.map function source)
  | [] => .nil
  | _head :: tail => .cons ⟨⟨rfl⟩⟩ (listGraphLift function tail)

theorem listRelGraph_to_map_eq {A : Type u} {B : Type v}
    (function : A → B) {source : List A} {target : List B} :
    ListRel (Graph.{u, v, w} function) source target →
      List.map function source = target := by
  intro related
  induction related with
  | nil => rfl
  | @cons sourceHead targetHead sourceTail targetTail head _tail hypothesis =>
      rcases head with ⟨⟨headEquality⟩⟩
      subst targetHead
      simp only [List.map_cons, List.cons.injEq, true_and]
      exact hypothesis

def listMap_eq_to_relGraph {A : Type u} {B : Type v}
    (function : A → B) {source : List A} {target : List B}
    (equality : List.map function source = target) :
    ListRel (Graph.{u, v, w} function) source target := by
  subst target
  exact listGraphLift function source

theorem listRelGraph_subsingleton {A : Type u} {B : Type v}
    (function : A → B) (source : List A) (target : List B) :
    Subsingleton (ListRel (Graph.{u, v, w} function) source target) := by
  constructor
  intro first
  induction first with
  | nil =>
      intro second
      cases second
      rfl
  | @cons sourceHead targetHead sourceTail targetTail head tail hypothesis =>
      intro second
      cases second with
      | cons otherHead otherTail =>
          have headSame : head = otherHead := Subsingleton.elim _ _
          have tailSame : tail = otherTail := hypothesis otherTail
          cases headSame
          cases tailSame
          rfl

noncomputable def listRel_graph_equiv_graph_map
    {A : Type u} {B : Type v} (function : A → B)
    (source : List A) (target : List B) :
    ListRel (Graph.{u, v, w} function) source target ≃
      Graph.{u, v, w} (List.map function) source target where
  toFun related := ⟨⟨listRelGraph_to_map_eq function related⟩⟩
  invFun equality := listMap_eq_to_relGraph function equality.down.down
  left_inv _ := (listRelGraph_subsingleton function source target).elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Equality of mapped polynomial lists is exactly equality of their ordinary
list representations after mapping. -/
noncomputable def representedMapEqualityEquiv
    {A : Type u} {B : Type v} (function : A → B)
    (source : ListP A) (target : ListP B) :
    Graph.{u, v, w} (List.map function) (toList source) (toList target) ≃
      Graph.{u, v, w} (map function) source target where
  toFun equality := ⟨⟨toList_injective (by
    rw [toList_map]
    exact equality.down.down)⟩⟩
  invFun equality := ⟨⟨by
    rw [← toList_map]
    exact congrArg toList equality.down.down⟩⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- `mapRel (graph f)` agrees fibrewise with `graph (map f)`.  This exact
evidence equivalence makes pure map the deterministic special case without
installing functions as the meaning of relations. -/
noncomputable def relLift_graph_equiv_graph_map
    {A : Type u} {B : Type v} (function : A → B)
    (source : ListP A) (target : ListP B) :
    RelLift (Graph.{u, v, w} function) source target ≃
      Graph.{u, v, w} (map function) source target :=
  (listRel_graph_equiv_graph_map function (toList source) (toList target)).trans
    (representedMapEqualityEquiv function source target)

/-- Public graph-agreement seam under the relational-map name. -/
noncomputable def mapRel_graph_equiv_graph_map
    {A : Type u} {B : Type v} (function : A → B)
    (source : ListP A) (target : ListP B) :
    mapRel (Graph.{u, v, w} function) source target ≃
      Graph.{u, v, w} (map function) source target :=
  relLift_graph_equiv_graph_map function source target

/-! ### Multiplicity and impossibility controls -/

inductive BranchEvidence where
  | left
  | right
  deriving DecidableEq

def branchingRelation (_source _target : Unit) : Type := BranchEvidence

noncomputable def singletonUnit : ListP Unit := cons () nil

noncomputable def branchLeft :
    mapRel branchingRelation singletonUnit singletonUnit := by
  change ListRel branchingRelation (toList singletonUnit) (toList singletonUnit)
  rw [show toList singletonUnit = [()] by simp [singletonUnit]]
  exact .cons .left .nil

noncomputable def branchRight :
    mapRel branchingRelation singletonUnit singletonUnit := by
  change ListRel branchingRelation (toList singletonUnit) (toList singletonUnit)
  rw [show toList singletonUnit = [()] by simp [singletonUnit]]
  exact .cons .right .nil

theorem branchLeft_ne_branchRight : branchLeft ≠ branchRight := by
  intro equality
  have evidenceEquality : BranchEvidence.left = BranchEvidence.right := by
    injection equality
  exact BranchEvidence.noConfusion evidenceEquality

/-- Nondeterministic head evidence remains two distinct list-map derivations;
the relator does not deduplicate it into Boolean support. -/
theorem branching_mapRel_not_subsingleton :
    ¬ Subsingleton
      (mapRel branchingRelation singletonUnit singletonUnit) := by
  intro subsingleton
  exact branchLeft_ne_branchRight (subsingleton.elim branchLeft branchRight)

def impossibleRelation (_source _target : Unit) : Type := Empty

/-- An impossible element relation cannot manufacture a singleton-list
derivation. -/
theorem impossible_singleton_mapRel_isEmpty :
    IsEmpty (mapRel impossibleRelation singletonUnit singletonUnit) where
  false := by
    intro related
    change ListRel impossibleRelation (toList singletonUnit)
      (toList singletonUnit) at related
    rw [show toList singletonUnit = [()] by simp [singletonUnit]] at related
    cases related with
    | cons impossible _ => exact impossible.elim

end ListExample

/-! ## Vectors as genuinely indexed polynomial fixed points

Unlike lists, vector constructors change the family index.  This makes vectors
a second, independent check that the generic eliminator is genuinely indexed
rather than an ordinary recursor wrapped in indexed notation.
-/

namespace VectorExample

inductive One : Type u where
  | star

inductive Void : Type u

/-- Constructor shapes at a vector length. -/
inductive Shape (A : Type u) : Nat → Type u where
  | nil : Shape A 0
  | cons (length : Nat) (head : A) : Shape A (length + 1)

/-- The vector polynomial: `nil` has no recursive child; `cons n a` has one
child at index `n`. -/
@[reducible] def polynomial (A : Type u) :
    IndexedPolynomial.{u, 0, u, u} (One.{u}) (fun _ => Nat) where
  Shape := fun _ length => Shape A length
  Position := fun shape =>
    match shape with
    | .nil => Void
    | .cons _ _ => One
  next := fun shape position =>
    match shape with
    | .nil => nomatch position
    | .cons length _ => length

abbrev VectorP (A : Type u) (length : Nat) : Type u :=
  Fix (polynomial A) .star length

def nilChildren {A : Type u} :
    (position : (polynomial A).Position (base := .star) (index := 0)
      (Shape.nil (A := A))) →
      VectorP A ((polynomial A).next (base := .star)
        (Shape.nil (A := A)) position) :=
  fun position => nomatch position

def consChildren {A : Type u} {length : Nat} {head : A}
    (tail : VectorP A length) :
    (position : (polynomial A).Position (base := .star)
      (index := length + 1) (Shape.cons length head)) →
      VectorP A ((polynomial A).next (base := .star)
        (Shape.cons length head) position) :=
  fun _ => tail

def nil {A : Type u} : VectorP A 0 :=
  .roll .nil nilChildren

def cons {A : Type u} {length : Nat} (head : A)
    (tail : VectorP A length) : VectorP A (length + 1) :=
  .roll (.cons length head) (consChildren tail)

theorem roll_nil_eq_nil {A : Type u}
    (children :
      (position : (polynomial A).Position (base := .star) (index := 0)
        (Shape.nil (A := A))) →
        VectorP A ((polynomial A).next (base := .star)
          (Shape.nil (A := A)) position)) :
    (Fix.roll .nil children : VectorP A 0) = nil := by
  have childrenEqual : children = nilChildren := by
    funext position
    exact nomatch position
  rw [childrenEqual]
  rfl

theorem roll_cons_eq_cons {A : Type u} (length : Nat) (head : A)
    (children :
      (position : (polynomial A).Position (base := .star)
        (index := length + 1) (Shape.cons length head)) →
        VectorP A ((polynomial A).next (base := .star)
          (Shape.cons length head) position)) :
    (Fix.roll (.cons length head) children : VectorP A (length + 1)) =
      cons head (children .star) := by
  have childrenEqual : children = consChildren (children .star) := by
    funext position
    cases position
    rfl
  rw [childrenEqual]
  rfl

def motiveAtNil {A : Type u}
    (motive : ∀ length, VectorP A length → Sort v)
    (children :
      (position : (polynomial A).Position (base := .star) (index := 0)
        (Shape.nil (A := A))) →
        VectorP A ((polynomial A).next (base := .star)
          (Shape.nil (A := A)) position))
    (value : motive 0 nil) :
    motive 0 (Fix.roll .nil children) :=
  Eq.mpr (congrArg (motive 0) (roll_nil_eq_nil children)) value

def motiveAtCons {A : Type u}
    (motive : ∀ length, VectorP A length → Sort v)
    (length : Nat) (head : A)
    (children :
      (position : (polynomial A).Position (base := .star)
        (index := length + 1) (Shape.cons length head)) →
        VectorP A ((polynomial A).next (base := .star)
          (Shape.cons length head) position))
    (value : motive (length + 1) (cons head (children .star))) :
    motive (length + 1) (Fix.roll (.cons length head) children) :=
  Eq.mpr
    (congrArg (motive (length + 1))
      (roll_cons_eq_cons length head children)) value

@[simp] theorem motiveAtNil_canonical {A : Type u}
    (motive : ∀ length, VectorP A length → Sort v)
    (value : motive 0 nil) :
    motiveAtNil motive nilChildren value = value := by
  simp only [motiveAtNil, eq_mpr_eq_cast]
  exact eq_of_heq (cast_heq _ _)

@[simp] theorem motiveAtCons_canonical {A : Type u}
    (motive : ∀ length, VectorP A length → Sort v)
    (length : Nat) (head : A) (tail : VectorP A length)
    (value : motive (length + 1) (cons head tail)) :
    motiveAtCons motive length head (consChildren tail) value = value := by
  simp only [motiveAtCons, eq_mpr_eq_cast]
  exact eq_of_heq (cast_heq _ _)

/-- Dependent vector elimination, including dependency on the length index. -/
noncomputable def eliminate {A : Type u}
    (motive : ∀ length, VectorP A length → Sort v)
    (nilCase : motive 0 nil)
    (consCase : ∀ length head tail,
      motive length tail → motive (length + 1) (cons head tail)) :
    ∀ length (vector : VectorP A length), motive length vector :=
  Fix.eliminate (polynomial A) (fun _ length vector => motive length vector)
    (fun _ _ shape children hypotheses => by
      cases shape with
      | nil => exact motiveAtNil motive children nilCase
      | cons length head =>
          exact motiveAtCons motive length head children
            (consCase length head (children .star) (hypotheses .star)))
    .star

@[simp] theorem eliminate_nil {A : Type u}
    (motive : ∀ length, VectorP A length → Sort v)
    (nilCase : motive 0 nil)
    (consCase : ∀ length head tail,
      motive length tail → motive (length + 1) (cons head tail)) :
    eliminate motive nilCase consCase 0 nil = nilCase := by
  simp only [eliminate, nil, Fix.eliminate_roll, motiveAtNil_canonical]

@[simp] theorem eliminate_cons {A : Type u}
    (motive : ∀ length, VectorP A length → Sort v)
    (nilCase : motive 0 nil)
    (consCase : ∀ length head tail,
      motive length tail → motive (length + 1) (cons head tail))
    (length : Nat) (head : A) (tail : VectorP A length) :
    eliminate motive nilCase consCase (length + 1) (cons head tail) =
      consCase length head tail (eliminate motive nilCase consCase length tail) := by
  simp only [eliminate, cons, Fix.eliminate_roll, motiveAtCons_canonical]
  rfl

/-- Forget the length index while retaining every element. -/
noncomputable def erase {A : Type u} :
    ∀ length, VectorP A length → ListExample.ListP A :=
  eliminate (fun _ _ => ListExample.ListP A) ListExample.nil
    (fun _length head _tail erasedTail =>
      ListExample.cons head erasedTail)

@[simp] theorem erase_nil {A : Type u} :
    erase 0 (nil : VectorP A 0) = ListExample.nil := by
  simp [erase]

@[simp] theorem erase_cons {A : Type u} (length : Nat) (head : A)
    (tail : VectorP A length) :
    erase (length + 1) (cons head tail) =
      ListExample.cons head (erase length tail) := by
  simp [erase]

/-- The vector index is exactly the structural length of its erased list. -/
theorem erase_length {A : Type u} (length : Nat)
    (vector : VectorP A length) :
    ListExample.length (erase length vector) = length := by
  apply eliminate
    (motive := fun length vector =>
      ListExample.length (erase length vector) = length)
  · rfl
  · intro priorLength head tail hypothesis
    simp only [erase_cons, ListExample.length_cons, hypothesis]

/-- Negative indexed control: no length-one vector can be built over the
empty element type. -/
theorem empty_vector_length_zero (length : Nat)
    (vector : VectorP Empty length) : length = 0 :=
  eliminate (A := Empty) (motive := fun length _ => length = 0) rfl
    (fun _length head _tail _hypothesis => Empty.elim head) length vector

theorem empty_one_isEmpty : IsEmpty (VectorP Empty 1) where
  false := fun vector => Nat.noConfusion (empty_vector_length_zero 1 vector)

end VectorExample

/-! ## Identity as an indexed polynomial

Identity is a useful canary for the indexed theory: its sole constructor
changes the family index from an arbitrary endpoint pair to the diagonal, and
its eliminator must therefore be genuinely dependent. -/

namespace IdentityExample

/-- A universe-polymorphic singleton used as the closed base context. -/
inductive One : Type u where
  | star

/-- A universe-polymorphic empty type used for constructors without recursive
positions. -/
inductive Void : Type u

/-- The constructor shapes for identity.  `refl point` is available only at
the diagonal index `(point, point)`. -/
inductive Shape (A : Type u) : A × A → Type u where
  | refl (point : A) : Shape A (point, point)

/-- The strictly-positive indexed polynomial for identity over a fixed type. -/
def polynomial (A : Type u) :
    IndexedPolynomial.{u, u, u, u} (One.{u}) (fun _ => A × A) where
  Shape := fun _ endpoints => Shape A endpoints
  Position := fun _ => Void
  next := fun _ position => nomatch position

/-- Identity obtained as the fixed family of its indexed polynomial. -/
abbrev Identity (A : Type u) (left right : A) : Type u :=
  Fix (polynomial A) .star (left, right)

/-- The unique recursive-child assignment for reflexivity's empty position
type.  Naming it makes the propositional computation proof explicit. -/
def reflChildren {A : Type u} (point : A) :
    (position : (polynomial A).Position (base := One.star)
      (Shape.refl point)) →
      Fix (polynomial A) .star
        ((polynomial A).next (base := One.star)
          (Shape.refl point) position) :=
  fun position => nomatch position

/-- Reflexivity is the sole identity constructor. -/
def refl {A : Type u} (point : A) : Identity A point point :=
  .roll (.refl point) (reflChildren point)

/-- Every empty recursive-child assignment gives the same reflexivity
constructor. -/
def roll_eq_refl {A : Type u} (point : A)
    (children :
      (position : (polynomial A).Position (base := One.star)
        (Shape.refl point)) →
        Fix (polynomial A) .star
          ((polynomial A).next (base := One.star)
            (Shape.refl point) position)) :
    (Fix.roll (.refl point) children : Identity A point point) = refl point := by
  have childrenEqual : children = reflChildren point := by
    funext position
    exact nomatch position
  rw [childrenEqual]
  rfl

/-- The unique-constructor equality is reflexive at the chosen empty child
assignment. -/
@[simp] theorem roll_eq_refl_canonical {A : Type u} (point : A) :
    roll_eq_refl point (reflChildren point) = rfl :=
  Subsingleton.elim _ _

/-- Transport a reflexivity case to an arbitrary presentation of the same
zero-child constructor. -/
def motiveAtRoll {A : Type u}
    (motive : ∀ left right, Identity A left right → Sort v)
    (point : A)
    (children :
      (position : (polynomial A).Position (base := One.star)
        (Shape.refl point)) →
        Fix (polynomial A) .star
          ((polynomial A).next (base := One.star)
            (Shape.refl point) position))
    (value : motive point point (refl point)) :
    motive point point (Fix.roll (.refl point) children) :=
  Eq.mpr
    (congrArg (motive point point) (roll_eq_refl point children))
    value

@[simp] theorem motiveAtRoll_canonical {A : Type u}
    (motive : ∀ left right, Identity A left right → Sort v)
    (reflexivity : ∀ point, motive point point (refl point))
    (point : A) :
    motiveAtRoll motive point (reflChildren point) (reflexivity point) =
      reflexivity point := by
  unfold motiveAtRoll
  change Eq.mpr
      (congrArg (motive point point)
        (roll_eq_refl point (reflChildren point)))
      (reflexivity point) = reflexivity point
  rw [roll_eq_refl_canonical]
  rfl

/-- Path induction derived from the generic polynomial eliminator. -/
noncomputable def j {A : Type u}
    (motive : ∀ left right, Identity A left right → Sort v)
    (reflexivity : ∀ point, motive point point (refl point))
    {left right : A} (path : Identity A left right) :
    motive left right path :=
  @Fix.rec One (fun _ => A × A) (polynomial A) .star
    (fun endpoints path => motive endpoints.1 endpoints.2 path)
    (fun {endpoints} shape children _hypotheses => by
      cases shape with
      | refl point =>
          exact motiveAtRoll motive point children (reflexivity point))
    (left, right) path

/-- J computes on reflexivity. -/
@[simp] theorem j_refl {A : Type u}
    (motive : ∀ left right, Identity A left right → Sort v)
    (reflexivity : ∀ point, motive point point (refl point))
    (point : A) :
    j motive reflexivity (refl point) = reflexivity point := by
  simp only [j, refl, motiveAtRoll_canonical]

/-- Polynomial identity reflects to ordinary equality. -/
noncomputable def toEq {A : Type u} {left right : A} :
    Identity A left right → left = right :=
  j (fun left right _ => left = right) (fun _ => rfl)

/-- Ordinary equality introduces polynomial identity. -/
def ofEq {A : Type u} {left right : A} (equality : left = right) :
    Identity A left right := by
  cases equality
  exact refl left

@[simp] theorem toEq_refl {A : Type u} (point : A) :
    toEq (refl point) = rfl := by
  rfl

@[simp] theorem ofEq_rfl {A : Type u} (point : A) :
    ofEq (Eq.refl point) = refl point := by
  rfl

/-- Every polynomial identity is recovered from its reflected equality. -/
theorem ofEq_toEq {A : Type u} {left right : A}
    (path : Identity A left right) :
    ofEq (toEq path) = path := by
  apply j (motive := fun left right path => ofEq (toEq path) = path)
  intro point
  rfl

/-- Polynomial identity and ordinary intensional equality are equivalent. -/
noncomputable def equivEq {A : Type u} (left right : A) :
    Identity A left right ≃ (left = right) where
  toFun := toEq
  invFun := ofEq
  left_inv := ofEq_toEq
  right_inv := by
    intro equality
    cases equality
    rfl

/-- Negative endpoint control: the identity fibre between distinct Boolean
constructors is empty. -/
theorem false_true_empty : IsEmpty (Identity Bool false true) where
  false := fun path => Bool.noConfusion (toEq path)

end IdentityExample

end IndexedPolynomial
end Mettapedia.TypeTheory
