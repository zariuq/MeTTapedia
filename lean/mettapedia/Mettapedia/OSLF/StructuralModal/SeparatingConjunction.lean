import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.Logic.SeparationAlgebra
import Mettapedia.OSLF.StructuralModal.EquationInvariance

/-!
# The cut as a separating conjunction

The structural layer adds one connective per term former, and reading a term
against such a connective means decomposing it.  When the former is the
interaction cut and the cut is associative–commutative, that decomposition must
be taken *modulo the equations*: a term satisfies `φ | ψ` when it splits into
two parts satisfying the two predicates in **some** presentation of it, not
only in the one it happens to be written in.  That is what makes the connective
a separating conjunction in the sense of spatial and separation logics rather
than a positional projection.

The two readings are not the same, and the difference is exactly what the
collection tag contributes.  `sepConj_positional` shows every positional split
is a separation.  `positional_not_closed_under_swap` shows the converse fails:
the positional reading is not even symmetric.  `sepConj_comm` shows the
separating reading is symmetric as soon as the tag supplies permutation
invariance, so the extra decompositions are precisely the equational ones.

Nothing here assumes which laws a tag supplies.  Permutation invariance is a
hypothesis, discharged for a concrete presentation by its own derived laws.

## The algebra the equations decide

A presentation that declares an associative collection former — flattening of
nested occurrences, which also makes the empty collection a unit — makes its
terms of the former's category, taken modulo the equations, a monoid
(`AssociativeFormer.Configuration`).  When the former is a bag, the derived
permutation law makes that monoid commutative, hence a separation algebra in
which every two configurations are separate, and the separating reading of the
cut on sorted terms *is* that algebra's separating conjunction
(`AssociativeFormer.sepConj_iff_configuration_sepConj`).

The equations decide nothing more than that: a commutative monoid of
configurations.  Exclusive ownership, cancellativity, positivity and a local
transition relation are not consequences of them.

**Negative.**  `Sequences` declares an associative former over a sequence kind,
which carries no permutation law.  Its configurations are a monoid that does not
commute (`Sequences.configurations_not_commutative`), and its cut is not
symmetric (`Sequences.sepConj_not_symmetric`): without commutativity there is no
separating conjunction, only the positional reading up to regrouping.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.StructuralModal.SeparatingConjunction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.StructuralModal

/-! ## The connective -/

/-- The positional reading: a term is literally a collection whose element
list is the concatenation of two lists satisfying the two predicates. -/
def PositionalConj (kind : CollType) (left right : Pattern → Prop)
    (term : Pattern) : Prop :=
  ∃ leftElements rightElements : List Pattern,
    term = .collection kind (leftElements ++ rightElements) none ∧
      left (.collection kind leftElements none) ∧
      right (.collection kind rightElements none)

/-- The separating reading: the term is equal, **modulo the equations**, to
such a collection.  `equiv` is the equation theory of the presentation. -/
def SepConj (equiv : Pattern → Pattern → Prop) (kind : CollType)
    (left right : Pattern → Prop) (term : Pattern) : Prop :=
  ∃ leftElements rightElements : List Pattern,
    equiv term (.collection kind (leftElements ++ rightElements) none) ∧
      left (.collection kind leftElements none) ∧
      right (.collection kind rightElements none)

/-! ## Basic laws -/

/-- Every positional split is a separation, for any reflexive equation
theory. -/
theorem sepConj_positional {equiv : Pattern → Pattern → Prop}
    (refl : ∀ term, equiv term term) {kind : CollType}
    {left right : Pattern → Prop} {term : Pattern}
    (positional : PositionalConj kind left right term) :
    SepConj equiv kind left right term := by
  obtain ⟨leftElements, rightElements, rfl, hleft, hright⟩ := positional
  exact ⟨leftElements, rightElements, refl _, hleft, hright⟩

/-- The separating conjunction is a predicate on equation classes: equivalent
terms satisfy it alike. -/
theorem sepConj_resp {equiv : Pattern → Pattern → Prop}
    (trans : ∀ {a b c}, equiv a b → equiv b c → equiv a c)
    (symm : ∀ {a b}, equiv a b → equiv b a)
    {kind : CollType} {left right : Pattern → Prop} {first second : Pattern}
    (equivalent : equiv first second) :
    SepConj equiv kind left right first ↔ SepConj equiv kind left right second := by
  constructor
  · rintro ⟨leftElements, rightElements, split, hleft, hright⟩
    exact ⟨leftElements, rightElements, trans (symm equivalent) split, hleft, hright⟩
  · rintro ⟨leftElements, rightElements, split, hleft, hright⟩
    exact ⟨leftElements, rightElements, trans equivalent split, hleft, hright⟩

/-- Permutation invariance for one collection kind, **on the collections a
presentation sorts**.

The unrestricted form is not what a sorted presentation delivers.  Its derived
permutation law is conditioned on the collection being sorted at the carrier's
declared category, and an arbitrary list of terms is not sorted there — so a
lemma asking for permutation invariance at every list asks for something no
sorted presentation supplies, and can never be discharged.  Carrying the
condition is what makes the law available. -/
def PermInvariantOn (equiv : Pattern → Pattern → Prop) (kind : CollType)
    (admits : List Pattern → Prop) : Prop :=
  ∀ {elements elements' : List Pattern}, admits elements →
    List.Perm elements elements' →
      equiv (.collection kind elements none) (.collection kind elements' none)

/-- Permutation invariance with no condition: the special case where every
element list is admitted.  It is stated because the laws below are proved from
the conditioned form and this is the shape a presentation without a sorting
discipline would supply. -/
abbrev PermInvariant (equiv : Pattern → Pattern → Prop) (kind : CollType) : Prop :=
  PermInvariantOn equiv kind (fun _ => True)

/-- **The separating conjunction is symmetric** as soon as the tag supplies
permutation invariance.  This is the law that makes the connective separating
rather than positional. -/
theorem sepConj_comm {equiv : Pattern → Pattern → Prop}
    (trans : ∀ {a b c}, equiv a b → equiv b c → equiv a c)
    {kind : CollType} {admits : List Pattern → Prop}
    (perm : PermInvariantOn equiv kind admits)
    {left right : Pattern → Prop} {term : Pattern}
    (split : SepConj equiv kind left right term)
    (admitted : ∀ leftElements rightElements : List Pattern,
      left (.collection kind leftElements none) →
      right (.collection kind rightElements none) →
      admits (leftElements ++ rightElements)) :
    SepConj equiv kind right left term := by
  obtain ⟨leftElements, rightElements, decomposition, hleft, hright⟩ := split
  exact ⟨rightElements, leftElements,
    trans decomposition
      (perm (admitted leftElements rightElements hleft hright) List.perm_append_comm),
    hright, hleft⟩

/-! ## The two readings are different

A two-element bag, with the predicates that name its two singletons in the
order opposite to the one the term is written in.  The positional reading fails
and the separating reading succeeds, so the equational decompositions are not
redundant. -/

/-! ## The monoid laws

Symmetry alone does not make a connective a separating conjunction.  What does
is that the connective, its unit, and the equation theory form a commutative
monoid on predicates: associative, symmetric, and with the empty collection
neutral on both sides.

Symmetry needs permutation invariance; the other two laws need a different and
weaker property of the equation theory, that replacing one part of a
composition by an equivalent part leaves the composition equivalent.  It is
named here rather than assumed, for the same reason permutation invariance is:
a presentation supplies it or it does not.

Half of each unit law holds outright, with no condition at all. -/

/-- **Replacing a part leaves the whole equivalent.**  The condition the
associativity and unit laws need: an equivalence between two compositions
survives being placed beside a common prefix. -/
structure SplitCongruent (equiv : Pattern → Pattern → Prop) (kind : CollType) : Prop where
  /-- Replacing the second part of a composition. -/
  onRight : ∀ prefixElements first second : List Pattern,
    equiv (.collection kind first none) (.collection kind second none) →
      equiv (.collection kind (prefixElements ++ first) none)
        (.collection kind (prefixElements ++ second) none)
  /-- And the first. -/
  onLeft : ∀ suffixElements first second : List Pattern,
    equiv (.collection kind first none) (.collection kind second none) →
      equiv (.collection kind (first ++ suffixElements) none)
        (.collection kind (second ++ suffixElements) none)

/-- The unit of the connective: the empty composition, read modulo the
equations. -/
def Emp (equiv : Pattern → Pattern → Prop) (kind : CollType) (term : Pattern) : Prop :=
  equiv term (.collection kind [] none)

/-- **The unit is neutral on the right, the easy half**, and it needs nothing:
a composition satisfying a predicate splits as itself beside the empty
composition. -/
theorem sepConj_emp_right_of {equiv : Pattern → Pattern → Prop}
    (refl : ∀ term, equiv term term) {kind : CollType} {left : Pattern → Prop}
    {elements : List Pattern} (holds : left (.collection kind elements none)) :
    SepConj equiv kind left (Emp equiv kind) (.collection kind elements none) :=
  ⟨elements, [], by simpa using refl _, holds, refl _⟩

/-- And on the left. -/
theorem sepConj_emp_left_of {equiv : Pattern → Pattern → Prop}
    (refl : ∀ term, equiv term term) {kind : CollType} {right : Pattern → Prop}
    {elements : List Pattern} (holds : right (.collection kind elements none)) :
    SepConj equiv kind (Emp equiv kind) right (.collection kind elements none) :=
  ⟨[], elements, by simpa using refl _, refl _, holds⟩

/-- **And the other half**, which is where the condition is spent: a split
against the unit gives the predicate back, up to the equations. -/
theorem of_sepConj_emp_right {equiv : Pattern → Pattern → Prop}
    (trans : ∀ {a b c}, equiv a b → equiv b c → equiv a c)
    {kind : CollType} (congruent : SplitCongruent equiv kind)
    {left : Pattern → Prop} {term : Pattern}
    (split : SepConj equiv kind left (Emp equiv kind) term) :
    ∃ elements : List Pattern,
      equiv term (.collection kind elements none) ∧
        left (.collection kind elements none) := by
  obtain ⟨leftElements, rightElements, decomposition, holds, empty⟩ := split
  refine ⟨leftElements, ?_, holds⟩
  have collapse :
      equiv (.collection kind (leftElements ++ rightElements) none)
        (.collection kind (leftElements ++ []) none) :=
    congruent.onRight leftElements rightElements [] empty
  exact trans decomposition (by simpa using collapse)

/-- **Associativity, rightwards.**  A split whose right part splits again is a
split whose left part splits. -/
theorem sepConj_assoc_right {equiv : Pattern → Pattern → Prop}
    (refl : ∀ term, equiv term term) (trans : ∀ {a b c}, equiv a b → equiv b c → equiv a c)
    {kind : CollType} (congruent : SplitCongruent equiv kind)
    {first second third : Pattern → Prop} {term : Pattern}
    (split : SepConj equiv kind first (SepConj equiv kind second third) term) :
    SepConj equiv kind (SepConj equiv kind first second) third term := by
  obtain ⟨firstElements, restElements, decomposition, holdsFirst, splitRest⟩ := split
  obtain ⟨secondElements, thirdElements, restDecomposition, holdsSecond, holdsThird⟩ :=
    splitRest
  refine ⟨firstElements ++ secondElements, thirdElements, ?_, ?_, holdsThird⟩
  · refine trans decomposition ?_
    have step :
        equiv (.collection kind (firstElements ++ restElements) none)
          (.collection kind (firstElements ++ (secondElements ++ thirdElements)) none) :=
      congruent.onRight firstElements restElements (secondElements ++ thirdElements)
        restDecomposition
    simpa [List.append_assoc] using step
  · exact ⟨firstElements, secondElements, refl _, holdsFirst, holdsSecond⟩

/-- **And leftwards.** -/
theorem sepConj_assoc_left {equiv : Pattern → Pattern → Prop}
    (refl : ∀ term, equiv term term) (trans : ∀ {a b c}, equiv a b → equiv b c → equiv a c)
    {kind : CollType} (congruent : SplitCongruent equiv kind)
    {first second third : Pattern → Prop} {term : Pattern}
    (split : SepConj equiv kind (SepConj equiv kind first second) third term) :
    SepConj equiv kind first (SepConj equiv kind second third) term := by
  obtain ⟨restElements, thirdElements, decomposition, splitRest, holdsThird⟩ := split
  obtain ⟨firstElements, secondElements, restDecomposition, holdsFirst, holdsSecond⟩ :=
    splitRest
  refine ⟨firstElements, secondElements ++ thirdElements, ?_, holdsFirst, ?_⟩
  · refine trans decomposition ?_
    have step :
        equiv (.collection kind (restElements ++ thirdElements) none)
          (.collection kind ((firstElements ++ secondElements) ++ thirdElements) none) :=
      congruent.onLeft thirdElements restElements (firstElements ++ secondElements)
        restDecomposition
    simpa [List.append_assoc] using step
  · exact ⟨secondElements, thirdElements, refl _, holdsSecond, holdsThird⟩

/-- **Monotone in both arguments**, which a comprehension over decompositions
must be. -/
theorem sepConj_mono {equiv : Pattern → Pattern → Prop} {kind : CollType}
    {left left' right right' : Pattern → Prop}
    (weakerLeft : ∀ t, left t → left' t) (weakerRight : ∀ t, right t → right' t)
    {term : Pattern} (split : SepConj equiv kind left right term) :
    SepConj equiv kind left' right' term := by
  obtain ⟨leftElements, rightElements, decomposition, holdsLeft, holdsRight⟩ := split
  exact ⟨leftElements, rightElements, decomposition,
    weakerLeft _ holdsLeft, weakerRight _ holdsRight⟩

namespace Difference

/-- Two distinct atoms. -/
def atomA : Pattern := .apply "A" []

/-- The second atom. -/
def atomB : Pattern := .apply "B" []

/-- "Is the singleton bag of `B`". -/
def isSingletonB (term : Pattern) : Prop :=
  term = .collection .hashBag [atomB] none

/-- "Is the singleton bag of `A`". -/
def isSingletonA (term : Pattern) : Prop :=
  term = .collection .hashBag [atomA] none

/-- The term as written: the bag of `A` then `B`. -/
def bagAB : Pattern := .collection .hashBag [atomA, atomB] none

/-- The positional reading cannot split `{A, B}` as `{B}` beside `{A}`: no
concatenation of element lists puts `B` first. -/
theorem positional_not_closed_under_swap :
    ¬ PositionalConj .hashBag isSingletonB isSingletonA bagAB := by
  rintro ⟨leftElements, rightElements, hsplit, hleft, hright⟩
  simp only [isSingletonB, Pattern.collection.injEq] at hleft
  simp only [isSingletonA, Pattern.collection.injEq] at hright
  obtain ⟨-, hl, -⟩ := hleft
  obtain ⟨-, hr, -⟩ := hright
  subst hl; subst hr
  simp only [bagAB, Pattern.collection.injEq] at hsplit
  obtain ⟨-, hlist, -⟩ := hsplit
  simp [atomA, atomB] at hlist

/-- The separating reading does split it that way, given permutation
invariance — which is what the bag tag supplies. -/
theorem sepConj_closed_under_swap {equiv : Pattern → Pattern → Prop}
    {admits : List Pattern → Prop} (perm : PermInvariantOn equiv .hashBag admits)
    (admitted : admits [atomA, atomB]) :
    SepConj equiv .hashBag isSingletonB isSingletonA bagAB := by
  refine ⟨[atomB], [atomA], ?_, rfl, rfl⟩
  exact perm admitted (by
    show List.Perm [atomA, atomB] ([atomB] ++ [atomA])
    simpa using List.Perm.swap atomB atomA [])

end Difference

/-! ## The presentation's own equations supply the law

For a presentation whose parallel former is a declared bag carrier, permutation
invariance is not an assumption but a derived law, so the cut of that
presentation really is a separating conjunction. -/

/-- **Permutation invariance is a derived law of the presentation**, on exactly
the collections the presentation sorts at the carrier's category.

No hypothesis beyond the carrier declaration is needed.  The admitted class is
not chosen: it is read off the same sorting judgement the derived law is
conditioned on, so the statement is discharged rather than assumed. -/
theorem permInvariantOn_of_bagCarrier
    {base : BasePremiseEvaluator} {language : LanguageDef} {rule : GrammarRule}
    (declaration : CollectionCarrierRule language rule .hashBag) :
    PermInvariantOn (EquationEquiv base language) .hashBag
      (fun elements =>
        SortedAt language (.collection .hashBag elements none) rule.category) := by
  intro elements elements' sorted permutation
  exact equationEquiv_bag_perm declaration sorted permutation

/-- The cut of such a presentation really is a separating conjunction: it is
symmetric on every decomposition the presentation sorts. -/
theorem sepConj_comm_of_bagCarrier
    {base : BasePremiseEvaluator} {language : LanguageDef} {rule : GrammarRule}
    (declaration : CollectionCarrierRule language rule .hashBag)
    {left right : Pattern → Prop} {term : Pattern}
    (split : SepConj (EquationEquiv base language) .hashBag left right term)
    (admitted : ∀ leftElements rightElements : List Pattern,
      left (.collection .hashBag leftElements none) →
      right (.collection .hashBag rightElements none) →
      SortedAt language
        (.collection .hashBag (leftElements ++ rightElements) none) rule.category) :
    SepConj (EquationEquiv base language) .hashBag right left term :=
  sepConj_comm (equiv := EquationEquiv base language)
    (fun first second => Relation.EqvGen.trans _ _ _ first second)
    (permInvariantOn_of_bagCarrier declaration) split admitted

/-! ## Why the cut has to be a connective

The structural layer adds one connective per term former, and before the two
collection formers it had one for applications — `Formula.headed` — and none
for collections.  That was not a stylistic gap: a collection was invisible to
the whole language.  Every other former either ignores the term (`top`, `bot`,
and the propositional formers) or matches an application node, and the two
modal formers read the reduction span rather than the term.  So on a
presentation with no reductions in play, no formula of the collection-free
fragment separates any two collections whatsoever — not two different kinds,
not two different element lists.

The theorem below is stated over exactly that fragment, and it is the reason
`Formula.emptyColl` and `Formula.cut` exist.  It is deliberately not restricted
inside `headed`: the spatial former fails at a collection whatever its argument
formulas are, so admitting arbitrary arguments makes the statement stronger. -/

/-- The span of a presentation in which nothing reduces. -/
def inertSpan : ReductionSpan Pattern where
  Edge := Empty
  source := fun edge => edge.elim
  target := fun edge => edge.elim

/-- The structural language as it stood before the collection formers. -/
inductive CollectionFree : Formula → Prop
  | top : CollectionFree .top
  | bot : CollectionFree .bot
  | and {left right : Formula} :
      CollectionFree left → CollectionFree right → CollectionFree (.and left right)
  | or {left right : Formula} :
      CollectionFree left → CollectionFree right → CollectionFree (.or left right)
  | headed (constructor : String) (arguments : List Formula) :
      CollectionFree (.headed constructor arguments)
  | diamond {inner : Formula} : CollectionFree inner → CollectionFree (.diamond inner)
  | box {inner : Formula} : CollectionFree inner → CollectionFree (.box inner)

/-- **Without the collection formers the language cannot see inside a
collection.**  With no reductions in play, every collection-free
structural-modal formula assigns the same truth value to every collection. -/
theorem collections_indistinguishable {formula : Formula}
    (free : CollectionFree formula) (kind kind' : CollType)
    (elements elements' : List Pattern) (rest rest' : Option String) :
    satisfiesOver inertSpan formula (.collection kind elements rest) ↔
      satisfiesOver inertSpan formula (.collection kind' elements' rest') := by
  induction free with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | and _ _ leftIH rightIH => exact and_congr leftIH rightIH
  | or _ _ leftIH rightIH => exact or_congr leftIH rightIH
  | headed _ _ =>
      simp only [satisfiesOver]
      constructor
      · rintro ⟨_, shape, _⟩; exact absurd shape (by simp)
      · rintro ⟨_, shape, _⟩; exact absurd shape (by simp)
  | diamond _ _ =>
      simp only [satisfiesOver, derivedDiamond, di, pb]
      constructor
      · rintro ⟨edge, _, _⟩; exact edge.elim
      · rintro ⟨edge, _, _⟩; exact edge.elim
  | box _ _ =>
      simp only [satisfiesOver, derivedBox, ui, pb]
      constructor
      · intro _ edge _; exact edge.elim
      · intro _ edge _; exact edge.elim

/-- The consequence, on the two bags the section above separates by hand: the
collection-free fragment has no formula that tells the bag of `A` from the bag
of `B`. -/
theorem no_collectionFree_formula_separates_singleton_bags {formula : Formula}
    (free : CollectionFree formula) :
    satisfiesOver inertSpan formula (.collection .hashBag [Difference.atomA] none) ↔
      satisfiesOver inertSpan formula (.collection .hashBag [Difference.atomB] none) :=
  collections_indistinguishable free _ _ _ _ _ _

/-- And the two bags really are different terms, so the failure to separate them
is a failure of the fragment and not a coincidence of the example. -/
theorem singleton_bags_distinct :
    (Pattern.collection .hashBag [Difference.atomA] none) ≠
      (.collection .hashBag [Difference.atomB] none) := by
  simp [Difference.atomA, Difference.atomB]

/-- The fragment cannot separate the empty bag from a one-element bag either. -/
theorem no_collectionFree_formula_separates_empty_bag {formula : Formula}
    (free : CollectionFree formula) :
    satisfiesOver inertSpan formula (.collection .hashBag [] none) ↔
      satisfiesOver inertSpan formula (.collection .hashBag [Difference.atomA] none) :=
  collections_indistinguishable free _ _ _ _ _ _

/-- **And one formula of the extended language does separate them**, with no
reductions and no equations in play.  That closes the gap the theorem above
exhibits, which is what makes the new formers necessary rather than
convenient. -/
theorem emptyColl_separates_empty_bag :
    satisfiesOver inertSpan (.emptyColl .hashBag) (.collection .hashBag [] none) ∧
      ¬ satisfiesOver inertSpan (.emptyColl .hashBag)
        (.collection .hashBag [Difference.atomA] none) := by
  refine ⟨rfl, ?_⟩
  intro shape
  simp [satisfiesOver, Difference.atomA] at shape

/-! ## The cut is the separating conjunction

Read on the term as written, the connective is the positional conjunction.
Read modulo the equations of a presentation — which is the reading that makes
the whole structural language a family of predicates on equation classes — it
is `SepConj` of its two sub-readings, on the nose.  The separating reading is
therefore derived from the connective and the presentation, not posited beside
them. -/

/-- The direct reading of the cut is the positional conjunction. -/
theorem satisfiesOver_cut (span : ReductionSpan Pattern)
    (kind : CollType) (left right : Formula) (pattern : Pattern) :
    satisfiesOver span (.cut kind left right) pattern ↔
      PositionalConj kind (satisfiesOver span left) (satisfiesOver span right)
        pattern :=
  Iff.rfl

/-- **The reading modulo the equations of the cut is the separating
conjunction.**  Both sides are the same proposition. -/
theorem satisfiesModuloOver_cut (equiv : Pattern → Pattern → Prop)
    (span : ReductionSpan Pattern)
    (kind : CollType) (left right : Formula) (pattern : Pattern) :
    EquationInvariance.satisfiesModuloOver equiv span (.cut kind left right) pattern ↔
      SepConj equiv kind
        (EquationInvariance.satisfiesModuloOver equiv span left)
        (EquationInvariance.satisfiesModuloOver equiv span right) pattern :=
  Iff.rfl

/-- The cut of a presentation with a declared sorted bag carrier is symmetric on
every decomposition the presentation sorts: the connective really is separating,
by the presentation's own derived permutation law. -/
theorem satisfiesModuloOver_cut_comm
    {base : BasePremiseEvaluator} {language : LanguageDef} {rule : GrammarRule}
    (declaration : CollectionCarrierRule language rule .hashBag)
    (span : ReductionSpan Pattern) (left right : Formula) (pattern : Pattern)
    (holds : EquationInvariance.satisfiesModuloOver (EquationEquiv base language)
      span (.cut .hashBag left right) pattern)
    (admitted : ∀ leftElements rightElements : List Pattern,
      EquationInvariance.satisfiesModuloOver (EquationEquiv base language) span left
        (.collection .hashBag leftElements none) →
      EquationInvariance.satisfiesModuloOver (EquationEquiv base language) span right
        (.collection .hashBag rightElements none) →
      SortedAt language
        (.collection .hashBag (leftElements ++ rightElements) none) rule.category) :
    EquationInvariance.satisfiesModuloOver (EquationEquiv base language) span
      (.cut .hashBag right left) pattern :=
  sepConj_comm_of_bagCarrier declaration holds admitted


/-- **The cut reaches a collection's elements through the presentation's own
singleton law**, not through a third connective.  Given that law, the formula
naming a one-element collection is the cut of the element's formula with the
empty collection, so no `single` former has to be added to the language: it is
cleanly derived where the law holds, and where the law does not hold there is
no singleton to name. -/
theorem satisfiesModuloUsing_cut_reaches_element
    (relEnv : RelationEnv) (lang : LanguageDef) (kind : CollType)
    (element : Pattern) (inner : Formula)
    (singletonLaw : (langGSLTUsing relEnv lang).Equiv element
      (.collection kind [element] none))
    (holds : EquationInvariance.satisfiesModuloUsing relEnv lang inner element) :
    EquationInvariance.satisfiesModuloUsing relEnv lang
      (.cut kind inner (.emptyColl kind)) (.collection kind [element] none) :=
  ⟨[element], [],
    (langGSLTUsing relEnv lang).equations.iseqv.refl _,
    (EquationInvariance.satisfiesModuloUsing_equationInvariant relEnv lang inner
      singletonLaw).mp holds,
    (langGSLTUsing relEnv lang).equations.iseqv.refl _⟩

/-! ## Configurations modulo the equations

A declared associative former of a presentation turns the terms of its category
into a monoid modulo the equations: the composition of two terms is the
two-element collection, and the empty collection is the unit.  Associativity and
the unit laws are the presentation's flattening and singleton laws.  A bag
former adds the permutation law, and with it commutativity.

The carrier is fixed to one typing context, because sortedness is what every
derived law is conditioned on, and two terms sorted in different contexts need
not be sorted together. -/

open Mettapedia.GSLT.LanguageDef.WellSorted (HasSort HasType ElementsHaveType
  FreeTypeContext)
open Mettapedia.GSLT.SeparationAlgebra

/-- A declared associative collection former: an authored rule whose single
parameter is a collection of its own category, declaring flattening. -/
structure AssociativeFormer (language : LanguageDef) (rule : GrammarRule)
    (kind : CollType) (algebra : CollectionAlgebra) : Prop where
  declared : AlgebraRule language rule kind algebra
  flattens : algebra.flatten = true

namespace AssociativeFormer

variable {language : LanguageDef} {rule : GrammarRule} {kind : CollType}
  {algebra : CollectionAlgebra}

theorem elementsHaveType_append {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {first second : List Pattern}
    (firstTyped : ElementsHaveType language free bound first type)
    (secondTyped : ElementsHaveType language free bound second type) :
    ElementsHaveType language free bound (first ++ second) type := by
  induction first with
  | nil => exact secondTyped
  | cons head tail inductionHypothesis =>
      cases firstTyped with
      | cons headTyped tailTyped => exact .cons headTyped (inductionHypothesis tailTyped)

/-- A collection of terms of the former's category is again one. -/
theorem collection_sorted (former : AssociativeFormer language rule kind algebra)
    {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (typed : ElementsHaveType language free bound elements (.base rule.category)) :
    HasSort language free bound (.collection kind elements none) rule.category := by
  obtain ⟨parameterName, parameters⟩ := former.declared.selfSorted
  exact HasType.collectionConstructor former.declared.authored parameters typed

/-- The terms of the former's category in one typing context. -/
abbrev SortedTerm (language : LanguageDef) (rule : GrammarRule) (free : FreeTypeContext)
    (bound : List TypeExpr) : Type :=
  {term : Pattern // HasSort language free bound term rule.category}

/-- Equivalence modulo the presentation's equations, on sorted terms. -/
def setoid (base : BasePremiseEvaluator) (language : LanguageDef) (rule : GrammarRule)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    Setoid (SortedTerm language rule free bound) where
  r first second := EquationEquiv base language first.1 second.1
  iseqv :=
    ⟨fun _ => Relation.EqvGen.refl _, fun related => Relation.EqvGen.symm _ _ related,
      fun first second => Relation.EqvGen.trans _ _ _ first second⟩

/-- **Configurations**: sorted terms of the former's category modulo the
equations. -/
def Configuration (_former : AssociativeFormer language rule kind algebra)
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr) :
    Type :=
  Quotient (setoid base language rule free bound)

variable {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}

/-- Two sorted terms side by side. -/
def composeTerms (former : AssociativeFormer language rule kind algebra)
    (first second : SortedTerm language rule free bound) :
    SortedTerm language rule free bound :=
  ⟨.collection kind [first.1, second.1] none,
    former.collection_sorted (.cons first.2 (.cons second.2 (.nil _ _)))⟩

/-- The empty collection. -/
def emptyTerm (former : AssociativeFormer language rule kind algebra) :
    SortedTerm language rule free bound :=
  ⟨.collection kind [] none, former.collection_sorted (.nil _ _)⟩

/-- Composition of configurations. -/
def compose (former : AssociativeFormer language rule kind algebra) :
    Configuration former base free bound → Configuration former base free bound →
    Configuration former base free bound :=
  Quotient.map₂ (former.composeTerms) fun _ _ firstRelated _ _ secondRelated =>
    equationEquiv_collection_of_forall₂ kind none
      (.cons firstRelated (.cons secondRelated .nil))

theorem sortedAt_of_typed (former : AssociativeFormer language rule kind algebra)
    {elements : List Pattern}
    (typed : ElementsHaveType language free bound elements (.base rule.category)) :
    SortedAt language (.collection kind elements none) rule.category :=
  ⟨free, bound, former.collection_sorted typed⟩

/-- Flattening, at the root, for typed element lists. -/
theorem flatten_equiv (former : AssociativeFormer language rule kind algebra)
    {pre inner post : List Pattern}
    (preTyped : ElementsHaveType language free bound pre (.base rule.category))
    (innerTyped : ElementsHaveType language free bound inner (.base rule.category))
    (postTyped : ElementsHaveType language free bound post (.base rule.category)) :
    EquationEquiv base language
      (.collection kind (pre ++ (.collection kind inner none) :: post) none)
      (.collection kind (pre ++ inner ++ post) none) :=
  derivedInstance_equivalent (DerivedInstance.flatten former.declared former.flattens
    (former.sortedAt_of_typed (elementsHaveType_append preTyped
      (.cons (former.collection_sorted innerTyped) postTyped))))

/-- The singleton law, at the root. -/
theorem singleton_equiv (former : AssociativeFormer language rule kind algebra)
    {element : Pattern}
    (typed : HasSort language free bound element rule.category) :
    EquationEquiv base language (.collection kind [element] none) element :=
  derivedInstance_equivalent (DerivedInstance.singleton former.declared former.flattens
    (former.sortedAt_of_typed (.cons typed (.nil _ _))))

/-- The empty configuration. -/
instance instZero (former : AssociativeFormer language rule kind algebra) :
    Zero (Configuration former base free bound) :=
  ⟨Quotient.mk _ former.emptyTerm⟩

/-- Composition of configurations. -/
instance instAdd (former : AssociativeFormer language rule kind algebra) :
    Add (Configuration former base free bound) :=
  ⟨former.compose⟩

/-- The configuration of a sorted term. -/
def toConfiguration (former : AssociativeFormer language rule kind algebra)
    (base : BasePremiseEvaluator) (term : SortedTerm language rule free bound) :
    Configuration former base free bound :=
  Quotient.mk _ term

/-- Composition on representatives. -/
theorem toConfiguration_add (former : AssociativeFormer language rule kind algebra)
    (first second : SortedTerm language rule free bound) :
    former.toConfiguration base first + former.toConfiguration base second =
      former.toConfiguration base (former.composeTerms first second) :=
  rfl

/-- Configurations are equal exactly when representatives are equivalent modulo
the equations. -/
theorem toConfiguration_eq_iff (former : AssociativeFormer language rule kind algebra)
    {first second : SortedTerm language rule free bound} :
    former.toConfiguration base first = former.toConfiguration base second ↔
      EquationEquiv base language first.1 second.1 :=
  Quotient.eq

/-- **A declared associative former makes configurations a monoid.**
Associativity is flattening on either side; the unit laws are flattening of the
empty collection followed by the singleton law. -/
instance instAddMonoid (former : AssociativeFormer language rule kind algebra) :
    AddMonoid (Configuration former base free bound) where
  add_assoc := by
    rintro ⟨first⟩ ⟨second⟩ ⟨third⟩
    apply Quotient.sound
    show EquationEquiv base language
      (.collection kind [.collection kind [first.1, second.1] none, third.1] none)
      (.collection kind [first.1, .collection kind [second.1, third.1] none] none)
    have leftFlat := former.flatten_equiv (base := base) (pre := []) (inner := [first.1, second.1])
      (post := [third.1]) (.nil _ _) (.cons first.2 (.cons second.2 (.nil _ _)))
      (.cons third.2 (.nil _ _))
    have rightFlat := former.flatten_equiv (base := base) (pre := [first.1])
      (inner := [second.1, third.1]) (post := []) (.cons first.2 (.nil _ _))
      (.cons second.2 (.cons third.2 (.nil _ _))) (.nil _ _)
    exact Relation.EqvGen.trans _ _ _ leftFlat (Relation.EqvGen.symm _ _ rightFlat)
  zero_add := by
    rintro ⟨term⟩
    apply Quotient.sound
    show EquationEquiv base language
      (.collection kind [.collection kind [] none, term.1] none) term.1
    have flat := former.flatten_equiv (base := base) (pre := []) (inner := [])
      (post := [term.1]) (.nil _ _) (.nil _ _) (.cons term.2 (.nil _ _))
    exact Relation.EqvGen.trans _ _ _ flat (former.singleton_equiv term.2)
  add_zero := by
    rintro ⟨term⟩
    apply Quotient.sound
    show EquationEquiv base language
      (.collection kind [term.1, .collection kind [] none] none) term.1
    have flat := former.flatten_equiv (base := base) (pre := [term.1]) (inner := [])
      (post := []) (.cons term.2 (.nil _ _)) (.nil _ _) (.nil _ _)
    exact Relation.EqvGen.trans _ _ _ flat (former.singleton_equiv term.2)
  nsmul := nsmulRec

/-- The bag former's carrier declaration. -/
theorem carrierRule (former : AssociativeFormer language rule .hashBag algebra) :
    CollectionCarrierRule language rule .hashBag := by
  obtain ⟨parameterName, parameters⟩ := former.declared.selfSorted
  exact ⟨former.declared.authored, parameterName, _, parameters⟩

/-- **A bag former makes configurations a commutative monoid**, by the derived
permutation law. -/
instance instAddCommMonoid (former : AssociativeFormer language rule .hashBag algebra) :
    AddCommMonoid (Configuration former base free bound) where
  add_comm := by
    rintro ⟨first⟩ ⟨second⟩
    apply Quotient.sound
    exact equationEquiv_bag_perm former.carrierRule
      (former.sortedAt_of_typed (.cons first.2 (.cons second.2 (.nil _ _))))
      (List.Perm.swap second.1 first.1 [])

/-- **Configurations of a bag former form a separation algebra**, in which every
two configurations are separate. -/
instance instSepAlgebra (former : AssociativeFormer language rule .hashBag algebra) :
    SepAlgebra (Configuration former base free bound) :=
  ofAddCommMonoid (Configuration former base free bound)

/-- An equation-invariant predicate on terms, read on configurations. -/
def lift (former : AssociativeFormer language rule kind algebra) (predicate : Pattern → Prop)
    (invariant : ∀ first second, EquationEquiv base language first second →
      (predicate first ↔ predicate second)) :
    Configuration former base free bound → Prop :=
  Quotient.lift (fun term => predicate term.1) fun _ _ related =>
    propext (invariant _ _ related)

/-- **The cut, read modulo the equations, is the separating conjunction of the
configuration algebra**, on sorted terms and for equation-invariant readings
that hold only of collections of sorted terms. -/
theorem sepConj_iff_configuration_sepConj (former : AssociativeFormer language rule .hashBag algebra)
    {left right : Pattern → Prop}
    (leftInvariant : ∀ first second, EquationEquiv base language first second →
      (left first ↔ left second))
    (rightInvariant : ∀ first second, EquationEquiv base language first second →
      (right first ↔ right second))
    (leftTyped : ∀ elements, left (.collection .hashBag elements none) →
      ElementsHaveType language free bound elements (.base rule.category))
    (rightTyped : ∀ elements, right (.collection .hashBag elements none) →
      ElementsHaveType language free bound elements (.base rule.category))
    (term : SortedTerm language rule free bound) :
    SepConj (EquationEquiv base language) .hashBag left right term.1 ↔
      (former.lift left leftInvariant ∗ former.lift right rightInvariant)
        (former.toConfiguration base term) := by
  constructor
  · rintro ⟨leftElements, rightElements, decomposition, holdsLeft, holdsRight⟩
    have typedLeft := leftTyped _ holdsLeft
    have typedRight := rightTyped _ holdsRight
    let leftTerm : SortedTerm language rule free bound :=
      ⟨_, former.collection_sorted typedLeft⟩
    let rightTerm : SortedTerm language rule free bound :=
      ⟨_, former.collection_sorted typedRight⟩
    refine ⟨former.toConfiguration base leftTerm, former.toConfiguration base rightTerm,
      trivial, ?_, holdsLeft, holdsRight⟩
    rw [toConfiguration_add]
    apply (former.toConfiguration_eq_iff).mpr
    show EquationEquiv base language term.1
      (.collection .hashBag
        [.collection .hashBag leftElements none, .collection .hashBag rightElements none]
        none)
    have outer := former.flatten_equiv (base := base) (pre := []) (inner := leftElements)
      (post := [.collection .hashBag rightElements none]) (.nil _ _) typedLeft
      (.cons (former.collection_sorted typedRight) (.nil _ _))
    have inner := former.flatten_equiv (base := base) (pre := leftElements)
      (inner := rightElements) (post := []) typedLeft typedRight (.nil _ _)
    simp only [List.nil_append, List.append_nil] at outer inner
    exact Relation.EqvGen.trans _ _ _ decomposition
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ outer inner))
  · rintro ⟨first, second, -, decomposition, holdsLeft, holdsRight⟩
    obtain ⟨leftTerm, rfl⟩ := Quotient.exists_rep first
    obtain ⟨rightTerm, rfl⟩ := Quotient.exists_rep second
    have related : EquationEquiv base language term.1
        (.collection .hashBag ([leftTerm.1] ++ [rightTerm.1]) none) :=
      (former.toConfiguration_eq_iff (first := term)
        (second := former.composeTerms leftTerm rightTerm)).mp decomposition
    exact ⟨[leftTerm.1], [rightTerm.1], related,
      (leftInvariant _ _ (former.singleton_equiv leftTerm.2)).mpr holdsLeft,
      (rightInvariant _ _ (former.singleton_equiv rightTerm.2)).mpr holdsRight⟩

end AssociativeFormer

/-! ## Positive: rho's parallel composition

The rho presentation declares its parallel former as a flattening bag with unit
`PZero`, so its processes modulo the equations, in any typing context, form a
commutative monoid and hence a separation algebra
(`AssociativeFormer.instSepAlgebra` at `rhoParallel`). -/

/-- Rho's parallel composition, as authored. -/
def rhoParallelRule : GrammarRule :=
  { label := "PPar", category := "Proc"
    params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)]
    syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"]
    algebra? := some { flatten := true, unit := some "PZero" } }

/-- Rho's empty process, as authored. -/
def rhoZeroRule : GrammarRule :=
  { label := "PZero", category := "Proc", params := [], syntaxPattern := [.terminal "0"] }

/-- **Rho's parallel composition is a declared associative bag former.** -/
theorem rhoParallel :
    AssociativeFormer rhoCalc rhoParallelRule .hashBag { flatten := true, unit := some "PZero" } where
  declared :=
    { authored := by simp [rhoCalc, rhoParallelRule]
      declared := rfl
      selfSorted := ⟨"ps", rfl⟩
      unitAuthored := by
        intro unit isUnit
        cases isUnit
        exact ⟨rhoZeroRule, by simp [rhoCalc, rhoZeroRule], rfl, rfl, rfl⟩ }
  flattens := rfl

/-- Rho processes modulo the equations, in one typing context, form a separation
algebra. -/
example (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr) :
    SepAlgebra (AssociativeFormer.Configuration rhoParallel base free bound) :=
  inferInstance

/-! ## Without the bag law: a monoid that does not commute

A presentation with two atoms and one associative former over sequences.  The
former declares flattening, so its configurations are a monoid, but the
sequence kind carries no permutation law.  The labels of the atoms, read left
to right through every collection, are invariant under every equation of the
presentation, and they tell `[A, B]` from `[B, A]`. -/

namespace Sequences

/-- A nullary atom of the one category. -/
def atomRule (label : String) : GrammarRule :=
  { label, category := "T", params := [], syntaxPattern := [.terminal label] }

/-- The associative sequence former, with no unit constructor. -/
def seqRule : GrammarRule :=
  { label := "Seq", category := "T"
    params := [.simple "xs" (.collection .vec (.base "T"))]
    syntaxPattern := [.terminal "[", .nonTerminal "xs", .terminal "]"]
    algebra? := some { flatten := true, unit := none } }

/-- The presentation: two atoms and the sequence former, and no equations. -/
def language : LanguageDef :=
  { name := "sequences", types := [], terms := [atomRule "A", atomRule "B", seqRule],
    equations := [], rewrites := [] }

/-- The two atoms. -/
def atomA : Pattern := .apply "A" []

def atomB : Pattern := .apply "B" []

theorem former : AssociativeFormer language seqRule .vec { flatten := true, unit := none } where
  declared :=
    { authored := by simp [language]
      declared := rfl
      selfSorted := ⟨"xs", rfl⟩
      unitAuthored := by intro unit isUnit; cases isUnit }
  flattens := rfl

theorem atom_sorted (label : String) (member : atomRule label ∈ language.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    HasSort language free bound (.apply label []) seqRule.category :=
  HasType.constructor (rule := atomRule label) member
    (by rintro ⟨_, _, _, parameters⟩; cases parameters) .nil

mutual

/-- The atom labels of a pattern, left to right, through every collection. -/
def leaves : Pattern → List String
  | .bvar _ => []
  | .fvar _ => []
  | .apply label arguments => label :: leavesList arguments
  | .lambda _ body => leaves body
  | .multiLambda _ _ body => leaves body
  | .subst body replacement => leaves body ++ leaves replacement
  | .collection _ elements _ => leavesList elements

/-- The atom labels of a list of patterns. -/
def leavesList : List Pattern → List String
  | [] => []
  | pattern :: patterns => leaves pattern ++ leavesList patterns

end

theorem leavesList_append (first second : List Pattern) :
    leavesList (first ++ second) = leavesList first ++ leavesList second := by
  induction first with
  | nil => simp [leavesList]
  | cons head tail inductionHypothesis =>
      simp [leavesList, inductionHypothesis, List.append_assoc]

theorem leaves_fill (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    {first second : Pattern} (same : leaves first = leaves second) :
    leaves (context.fill first) = leaves (context.fill second) := by
  induction context with
  | hole => exact same
  | apply constructor before inner after inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, leaves,
        leavesList_append, leavesList, inductionHypothesis]
  | lambda binderName inner inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, leaves,
        inductionHypothesis]
  | multiLambda arity binderNames inner inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, leaves,
        inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, leaves,
        inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, leaves,
        inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, leaves,
        leavesList_append, leavesList, inductionHypothesis]

/-- The only declared collections are sequences, and the only declared algebra
is the sequence former's, which has no unit. -/
private theorem no_bag_or_set_carrier {rule : GrammarRule} {kind : CollType}
    (declaration : CollectionCarrierRule language rule kind) : kind = .vec := by
  obtain ⟨authored, parameterName, elementType, parameters⟩ := declaration
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl | rfl <;>
    simp_all [atomRule, seqRule]

private theorem algebra_has_no_unit {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} (declaration : AlgebraRule language rule kind algebra) :
    algebra.unit = none := by
  have declared := declaration.declared
  have authored := declaration.authored
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl | rfl <;>
    simp_all [atomRule, seqRule]
  · cases declared; rfl

/-- **Every equation of the presentation preserves the atom labels.** -/
theorem generator_leaves {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base language source target) :
    leaves source = leaves target := by
  rcases generator with authored | derived
  · exact absurd authored (no_equationInstance_of_equations_eq_nil rfl _ _)
  · cases derived with
    | bagPerm declaration _ _ => cases no_bag_or_set_carrier declaration
    | setPerm declaration _ _ => cases no_bag_or_set_carrier declaration
    | setDedup declaration _ => cases no_bag_or_set_carrier declaration
    | flatten _ _ _ => simp [leaves, leavesList_append, leavesList]
    | singleton _ _ _ => simp [leaves, leavesList]
    | unitElim declaration isUnit _ =>
        rw [algebra_has_no_unit declaration] at isUnit; cases isUnit
    | emptyUnit declaration isUnit _ =>
        rw [algebra_has_no_unit declaration] at isUnit; cases isUnit

theorem equationEquiv_leaves {base : BasePremiseEvaluator} {source target : Pattern}
    (related : EquationEquiv base language source target) :
    leaves source = leaves target := by
  induction related with
  | rel _ _ step =>
      cases step with
      | inContext context generator => exact leaves_fill context (generator_leaves generator)
  | refl _ => rfl
  | symm _ _ _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ _ _ _ firstIH secondIH => exact firstIH.trans secondIH

/-- The two-atom sequences in the two orders are not equal modulo the
equations. -/
theorem not_equiv_swap (base : BasePremiseEvaluator) :
    ¬ EquationEquiv base language (.collection .vec [atomA, atomB] none)
      (.collection .vec [atomB, atomA] none) := by
  intro related
  have := equationEquiv_leaves related
  simp [leaves, leavesList, atomA, atomB] at this

/-- **The configurations of an associative former without the bag law do not
commute.**  They are a monoid (`AssociativeFormer.instAddMonoid`), and no more. -/
theorem configurations_not_commutative (base : BasePremiseEvaluator)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    ∃ first second : AssociativeFormer.Configuration former base free bound,
      first + second ≠ second + first := by
  refine ⟨former.toConfiguration base ⟨atomA, atom_sorted "A" (by simp [language]) free bound⟩,
    former.toConfiguration base ⟨atomB, atom_sorted "B" (by simp [language]) free bound⟩, ?_⟩
  intro equal
  rw [AssociativeFormer.toConfiguration_add, AssociativeFormer.toConfiguration_add,
    AssociativeFormer.toConfiguration_eq_iff] at equal
  exact not_equiv_swap base equal

/-- Being `A` up to the equations. -/
def isA (base : BasePremiseEvaluator) (term : Pattern) : Prop :=
  EquationEquiv base language term atomA

/-- Being `B` up to the equations. -/
def isB (base : BasePremiseEvaluator) (term : Pattern) : Prop :=
  EquationEquiv base language term atomB

/-- **The cut of this presentation is not symmetric.**  `[A, B]` splits as `A`
beside `B`, and not as `B` beside `A`, although both readings are invariant
under the equations. -/
theorem sepConj_not_symmetric (base : BasePremiseEvaluator) :
    SepConj (EquationEquiv base language) .vec (isA base) (isB base)
        (.collection .vec [atomA, atomB] none) ∧
      ¬ SepConj (EquationEquiv base language) .vec (isB base) (isA base)
        (.collection .vec [atomA, atomB] none) := by
  refine ⟨⟨[atomA], [atomB], Relation.EqvGen.refl _, ?_, ?_⟩, ?_⟩
  · exact former.singleton_equiv (atom_sorted "A" (by simp [language])
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [])
  · exact former.singleton_equiv (atom_sorted "B" (by simp [language])
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [])
  · rintro ⟨leftElements, rightElements, decomposition, holdsLeft, holdsRight⟩
    have whole := equationEquiv_leaves decomposition
    have leftLeaves := equationEquiv_leaves holdsLeft
    have rightLeaves := equationEquiv_leaves holdsRight
    simp only [leaves, leavesList, atomA, atomB, leavesList_append, List.append_nil]
      at whole leftLeaves rightLeaves
    rw [leftLeaves, rightLeaves] at whole
    simp at whole

end Sequences

end Mettapedia.OSLF.StructuralModal.SeparatingConjunction
