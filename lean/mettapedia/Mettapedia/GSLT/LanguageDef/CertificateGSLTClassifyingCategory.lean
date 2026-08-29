import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpen
import Mathlib.CategoryTheory.Category.Basic

/-!
# The classifying category of a CertificateGSLT

Contexts and open-derivation vectors already carry a complete substitution
calculus: `assumptionEnvironment` is an identity environment, `bind` plugs one
environment into another, and the unit and associativity laws are proved in
`CertificateGSLTOpen`.  This module packages that calculus as an honest category.

* Objects are ordered premise contexts (`List Pattern`).
* A morphism from `Γ` to `Δ` derives every judgment of `Δ` from the ordered
  premise occurrences of `Γ`.
* Identity is the assumption environment; composition is substitution.

The category laws are exactly the three substitution theorems — nothing new
is proved here, which is the point: the classifying category is the
substitution calculus, stated once.

The empty context is terminal (`emptyContext`, `toEmpty_unique`), and context
concatenation carries binary-product structure: projections select premise
occurrences (`fstProjection`, `sndProjection`), pairing is concatenation of
derivation vectors (`pair`), and both projection laws hold exactly
(`pair_fst`, `pair_snd`).  Morphisms are proof relevant throughout: two equal
judgments at different positions remain different occurrences, and nothing
below quotients derivations.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open CategoryTheory

/-- An object of the classifying category: an ordered context of premise
occurrences for the fixed definition. -/
structure ClassifyingContext (definition : ValidatedCalculusLanguageDef) where
  judgments : List Pattern

namespace ClassifyingContext

variable {definition : ValidatedCalculusLanguageDef}

/-- Contexts and open-derivation vectors form a category: identity is the
assumption environment and composition is substitution.  Each law is one of
the already-proved substitution theorems. -/
instance instCategory (definition : ValidatedCalculusLanguageDef) :
    CategoryTheory.Category (ClassifyingContext definition) where
  Hom source target :=
    OpenDerivationList definition source.judgments target.judgments
  id source := assumptionEnvironment definition source.judgments
  comp first second := second.bind first
  id_comp first := OpenDerivationList.bind_assumptionEnvironment first
  comp_id first := OpenDerivationList.assumptionEnvironment_bind first
  assoc first second third :=
    (OpenDerivationList.bind_assoc third second first).symm

@[simp] theorem id_def (source : ClassifyingContext definition) :
    𝟙 source = assumptionEnvironment definition source.judgments := rfl

@[simp] theorem comp_def {source middle target : ClassifyingContext definition}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    first ≫ second = second.bind first := rfl

/-! ## The empty context is terminal -/

/-- The empty premise context. -/
def emptyContext (definition : ValidatedCalculusLanguageDef) :
    ClassifyingContext definition :=
  ⟨[]⟩

/-- The unique morphism into the empty context. -/
def toEmpty (source : ClassifyingContext definition) :
    source ⟶ emptyContext definition :=
  .nil

/-- Every open-derivation vector with no goals is empty. -/
theorem OpenDerivationList.eq_nil {context : List Pattern}
    (derivations : OpenDerivationList definition context []) :
    derivations = .nil := by
  cases derivations
  rfl

/-- The empty context admits exactly one morphism from every context. -/
theorem toEmpty_unique {source : ClassifyingContext definition}
    (morphism : source ⟶ emptyContext definition) :
    morphism = toEmpty source :=
  OpenDerivationList.eq_nil morphism

end ClassifyingContext

/-! ## Concatenation of derivation vectors -/

namespace OpenDerivationList

variable {definition : ValidatedCalculusLanguageDef}

/-- Concatenate two ordered derivation vectors over one shared context. -/
def append {context firstGoals secondGoals : List Pattern}
    (left : OpenDerivationList definition context firstGoals)
    (right : OpenDerivationList definition context secondGoals) :
    OpenDerivationList definition context (firstGoals ++ secondGoals) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (tail.append right)

@[simp] theorem nil_append {context secondGoals : List Pattern}
    (right : OpenDerivationList definition context secondGoals) :
    (OpenDerivationList.nil).append right = right := rfl

@[simp] theorem cons_append {context : List Pattern} {goal : Pattern}
    {firstGoals secondGoals : List Pattern}
    (head : OpenDerivation definition context goal)
    (tail : OpenDerivationList definition context firstGoals)
    (right : OpenDerivationList definition context secondGoals) :
    (OpenDerivationList.cons head tail).append right =
      .cons head (tail.append right) := rfl

/-- Substitution distributes over concatenation. -/
@[simp] theorem append_bind
    {sourceContext targetContext firstGoals secondGoals : List Pattern}
    (left : OpenDerivationList definition sourceContext firstGoals)
    (right : OpenDerivationList definition sourceContext secondGoals)
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    (left.append right).bind environment =
      (left.bind environment).append (right.bind environment) := by
  cases left with
  | nil => rfl
  | cons head tail =>
      simp [OpenDerivationList.bind, append,
        append_bind tail right environment]

/-! ## Selecting from a concatenated context

The left-block index keeps its numeral; the right-block index is shifted by
`firstGoals.length` on the right so that both selection lemmas reduce
definitionally. -/

theorem length_left {firstGoals secondGoals : List Pattern}
    (index : Fin firstGoals.length) :
    index.1 < (firstGoals ++ secondGoals).length := by
  have := index.isLt
  simp only [List.length_append]
  omega

theorem length_right {firstGoals secondGoals : List Pattern}
    (index : Fin secondGoals.length) :
    index.1 + firstGoals.length < (firstGoals ++ secondGoals).length := by
  have := index.isLt
  simp only [List.length_append]
  omega

theorem get_left {firstGoals secondGoals : List Pattern}
    (index : Fin firstGoals.length) :
    (firstGoals ++ secondGoals).get ⟨index.1, length_left index⟩ =
      firstGoals.get index := by
  match firstGoals, index with
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: rest, ⟨tailIndex + 1, isLt⟩ =>
      exact get_left (firstGoals := rest)
        ⟨tailIndex, Nat.lt_of_succ_lt_succ isLt⟩

theorem get_right {firstGoals secondGoals : List Pattern}
    (index : Fin secondGoals.length) :
    (firstGoals ++ secondGoals).get
        ⟨index.1 + firstGoals.length, length_right index⟩ =
      secondGoals.get index := by
  match firstGoals with
  | [] => rfl
  | _ :: rest => exact get_right (firstGoals := rest) index

/-- Substituting through a transported derivation transports the result. -/
theorem cast_bind {sourceContext targetContext : List Pattern}
    {firstGoal secondGoal : Pattern} (equal : firstGoal = secondGoal)
    (derivation : OpenDerivation definition sourceContext firstGoal)
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    (equal ▸ derivation).bind environment =
      equal ▸ (derivation.bind environment) := by
  cases equal
  rfl

/-- Selecting a left-block entry of a concatenated vector. -/
theorem append_get_left {context firstGoals secondGoals : List Pattern}
    (left : OpenDerivationList definition context firstGoals)
    (right : OpenDerivationList definition context secondGoals)
    (index : Fin firstGoals.length) :
    (left.append right).get ⟨index.1, length_left index⟩ =
      (get_left index).symm ▸ left.get index := by
  match left, index with
  | .nil, index => exact Fin.elim0 index
  | .cons head tail, ⟨0, _⟩ => rfl
  | .cons head tail, ⟨tailIndex + 1, isLt⟩ =>
      exact append_get_left tail right
        ⟨tailIndex, Nat.lt_of_succ_lt_succ isLt⟩

/-- Selecting a right-block entry of a concatenated vector. -/
theorem append_get_right {context firstGoals secondGoals : List Pattern}
    (left : OpenDerivationList definition context firstGoals)
    (right : OpenDerivationList definition context secondGoals)
    (index : Fin secondGoals.length) :
    (left.append right).get
        ⟨index.1 + firstGoals.length, length_right index⟩ =
      (get_right index).symm ▸ right.get index := by
  match left with
  | .nil => rfl
  | .cons head tail => exact append_get_right tail right index

/-- Transporting a derivation and then transporting back is the identity. -/
theorem cast_cast {context : List Pattern}
    {firstGoal secondGoal : Pattern} (equal : firstGoal = secondGoal)
    (derivation : OpenDerivation definition context secondGoal) :
    equal ▸ (equal.symm ▸ derivation) = derivation := by
  cases equal
  rfl

/-! ## Projections out of a concatenated context, at the raw level -/

/-- Derive every left-block judgment from its own premise occurrence inside
the concatenated context. -/
def leftProjection (firstGoals secondGoals : List Pattern) :
    OpenDerivationList definition (firstGoals ++ secondGoals) firstGoals :=
  OpenDerivationList.ofFn firstGoals fun index =>
    get_left index ▸
      OpenDerivation.assumption ⟨index.1, length_left index⟩

/-- Derive every right-block judgment from its own premise occurrence inside
the concatenated context. -/
def rightProjection (firstGoals secondGoals : List Pattern) :
    OpenDerivationList definition (firstGoals ++ secondGoals) secondGoals :=
  OpenDerivationList.ofFn secondGoals fun index =>
    get_right index ▸
      OpenDerivation.assumption
        ⟨index.1 + firstGoals.length, length_right index⟩

/-- Substituting a concatenated environment through the left projection
recovers the left vector exactly. -/
theorem leftProjection_bind_append
    {context firstGoals secondGoals : List Pattern}
    (toFirst : OpenDerivationList definition context firstGoals)
    (toSecond : OpenDerivationList definition context secondGoals) :
    (leftProjection firstGoals secondGoals).bind (toFirst.append toSecond) =
      toFirst := by
  unfold leftProjection
  simp only [OpenDerivationList.ofFn_bind]
  refine .trans
    (congrArg (OpenDerivationList.ofFn firstGoals)
      (funext fun index => ?_))
    (OpenDerivationList.ofFn_get toFirst)
  rw [cast_bind, OpenDerivation.assumption_bind, append_get_left, cast_cast]

/-- Substituting a concatenated environment through the right projection
recovers the right vector exactly. -/
theorem rightProjection_bind_append
    {context firstGoals secondGoals : List Pattern}
    (toFirst : OpenDerivationList definition context firstGoals)
    (toSecond : OpenDerivationList definition context secondGoals) :
    (rightProjection firstGoals secondGoals).bind (toFirst.append toSecond) =
      toSecond := by
  unfold rightProjection
  simp only [OpenDerivationList.ofFn_bind]
  refine .trans
    (congrArg (OpenDerivationList.ofFn secondGoals)
      (funext fun index => ?_))
    (OpenDerivationList.ofFn_get toSecond)
  rw [cast_bind, OpenDerivation.assumption_bind, append_get_right, cast_cast]

end OpenDerivationList

/-! ## Binary products by context concatenation -/

namespace ClassifyingContext

variable {definition : ValidatedCalculusLanguageDef}

/-- The product context: concatenation of premise contexts. -/
def concat (first second : ClassifyingContext definition) :
    ClassifyingContext definition :=
  ⟨first.judgments ++ second.judgments⟩

/-- First projection: each left-block judgment is its own premise
occurrence inside the concatenated context. -/
def fstProjection (first second : ClassifyingContext definition) :
    concat first second ⟶ first :=
  OpenDerivationList.leftProjection first.judgments second.judgments

/-- Second projection: each right-block judgment is its own premise
occurrence inside the concatenated context. -/
def sndProjection (first second : ClassifyingContext definition) :
    concat first second ⟶ second :=
  OpenDerivationList.rightProjection first.judgments second.judgments

/-- Pairing: concatenate the two derivation vectors. -/
def pair {source first second : ClassifyingContext definition}
    (toFirst : source ⟶ first) (toSecond : source ⟶ second) :
    source ⟶ concat first second :=
  OpenDerivationList.append toFirst toSecond

/-- The first projection law: pairing then projecting left recovers the
left derivation vector exactly. -/
@[simp] theorem pair_fst {source first second : ClassifyingContext definition}
    (toFirst : source ⟶ first) (toSecond : source ⟶ second) :
    pair toFirst toSecond ≫ fstProjection first second = toFirst :=
  OpenDerivationList.leftProjection_bind_append toFirst toSecond

/-- The second projection law: pairing then projecting right recovers the
right derivation vector exactly. -/
@[simp] theorem pair_snd {source first second : ClassifyingContext definition}
    (toFirst : source ⟶ first) (toSecond : source ⟶ second) :
    pair toFirst toSecond ≫ sndProjection first second = toSecond :=
  OpenDerivationList.rightProjection_bind_append toFirst toSecond

end ClassifyingContext

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
