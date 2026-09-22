import Mettapedia.GSLT.LanguageDef.MultiSortedClone
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Finite products of contexts in a multisorted clone

The clone laws already make ordered sort contexts a category. This module
establishes the universal property of the empty context and concatenation in
that category. Operations and their occurrences remain in the hom-sets; no
quotient by extensional semantics is taken.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MultiSortedClone

open CategoryTheory

universe u v

variable {Sorts : Type u} (clone : MultiSortedClone.{u, v} Sorts)

/-- Concatenate two environments over one shared source context. -/
def appendEnvironment {source : List Sorts} :
    (first second : List Sorts) →
      clone.Environment source first → clone.Environment source second →
        clone.Environment source (first ++ second)
  | [], _, _, right => right
  | _ :: first, second, left, right =>
      fun index => Fin.cases (left 0)
        (fun later => appendEnvironment first second
          (fun earlier => left earlier.succ) right later) index

/-- The empty context is terminal: an environment with no target positions
has exactly one possible value. -/
def emptyIsTerminal :
    CategoryTheory.Limits.IsTerminal
      (ContextObject.ofList clone []) :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun _ index => Fin.elim0 index)
    (fun _ morphism => by funext index; exact Fin.elim0 index)

/-- Add one unused input sort to a clone operation. -/
def weakenOperation {context : List Sorts} {input output : Sorts}
    (operation : clone.Hom context output) :
    clone.Hom (input :: context) output :=
  clone.substitute operation
    (fun index => clone.project (context := input :: context) index.succ)

/-- The left projection selects each left-block input occurrence. -/
def leftProjectionEnvironment :
    (first second : List Sorts) →
      clone.Environment (first ++ second) first
  | [], _, index => Fin.elim0 index
  | input :: first, second, index =>
      Fin.cases (clone.project (context := input :: first ++ second)
        ⟨0, Nat.zero_lt_succ _⟩)
        (fun later => weakenOperation clone
          (leftProjectionEnvironment first second later)) index

/-- The right projection selects each right-block input occurrence after
the complete left block. -/
def rightProjectionEnvironment :
    (first second : List Sorts) →
      clone.Environment (first ++ second) second
  | [], _, index => clone.project index
  | _ :: first, second, index =>
      weakenOperation clone (rightProjectionEnvironment first second index)

/-- Concatenation of two context objects. -/
def concat (first second : ContextObject clone) : ContextObject clone :=
  ContextObject.ofList clone (first.context ++ second.context)

/-- The two categorical projections are the corresponding positional
environments in the clone. -/
def fstProjection (first second : ContextObject clone) :
    concat clone first second ⟶ first :=
  leftProjectionEnvironment clone first.context second.context

def sndProjection (first second : ContextObject clone) :
    concat clone first second ⟶ second :=
  rightProjectionEnvironment clone first.context second.context

/-- Pair two simultaneous substitutions by concatenating their target
contexts. -/
def pair {source first second : ContextObject clone}
    (toFirst : source ⟶ first) (toSecond : source ⟶ second) :
    source ⟶ concat clone first second :=
  appendEnvironment clone first.context second.context toFirst toSecond

/-- Substituting an environment into a weakened operation discards the added
head entry and uses exactly the tail of that environment. -/
theorem substitute_weakenOperation
    {context target : List Sorts} {input output : Sorts}
    (operation : clone.Hom context output)
    (environment : clone.Environment target (input :: context)) :
    clone.substitute (weakenOperation clone operation) environment =
      clone.substitute operation (fun index => environment index.succ) := by
  calc
    clone.substitute (weakenOperation clone operation) environment =
        clone.substitute operation
          (fun index => clone.substitute
            (clone.project (context := input :: context) index.succ)
            environment) := by
              exact clone.substitute_assoc operation _ environment
    _ = clone.substitute operation (fun index => environment index.succ) := by
      congr 1
      funext index
      exact clone.substitute_project environment index.succ

/-- Pairing followed by the left projection returns exactly the original
left environment, including its operation identities. -/
theorem pair_fst {source : List Sorts} :
    ∀ (first second : List Sorts)
      (left : clone.Environment source first)
      (right : clone.Environment source second)
      (index : Fin first.length),
      clone.substitute
        (leftProjectionEnvironment clone first second index)
        (appendEnvironment clone first second left right) = left index := by
  intro first
  induction first with
  | nil =>
      intro second left right index
      exact Fin.elim0 index
  | cons input rest inductionHypothesis =>
      intro second left right index
      refine Fin.cases ?_ (fun later => ?_) index
      · exact clone.substitute_project _ _
      · change clone.substitute
          (weakenOperation clone (leftProjectionEnvironment clone rest second later))
          (appendEnvironment clone (input :: rest) second left right) = left later.succ
        rw [substitute_weakenOperation]
        exact inductionHypothesis second
          (fun earlier => left earlier.succ) right later

/-- Pairing followed by the right projection returns exactly the original
right environment. -/
theorem pair_snd {source : List Sorts} :
    ∀ (first second : List Sorts)
      (left : clone.Environment source first)
      (right : clone.Environment source second)
      (index : Fin second.length),
      clone.substitute
        (rightProjectionEnvironment clone first second index)
        (appendEnvironment clone first second left right) = right index := by
  intro first
  induction first with
  | nil =>
      intro second left right index
      exact clone.substitute_project _ _
  | cons input rest inductionHypothesis =>
      intro second left right index
      rw [rightProjectionEnvironment, substitute_weakenOperation]
      exact inductionHypothesis second
        (fun earlier => left earlier.succ) right index

/-- A simultaneous environment is uniquely reconstructed from its two
projections out of an appended target context. -/
theorem appendEnvironment_eta {source : List Sorts} :
    ∀ (first second : List Sorts)
      (environment : clone.Environment source (first ++ second)),
      appendEnvironment clone first second
        (fun index => clone.substitute
          (leftProjectionEnvironment clone first second index) environment)
        (fun index => clone.substitute
          (rightProjectionEnvironment clone first second index) environment) =
        environment := by
  intro first
  induction first with
  | nil =>
      intro second environment
      funext index
      exact clone.substitute_project environment index
  | cons input rest inductionHypothesis =>
      intro second environment
      funext index
      refine Fin.cases ?_ (fun later => ?_) index
      · exact clone.substitute_project environment _
      · have tailEqual := congrFun
          (inductionHypothesis second (fun index => environment index.succ)) later
        change appendEnvironment clone rest second
          (fun earlier => clone.substitute
            (weakenOperation clone
              (leftProjectionEnvironment clone rest second earlier)) environment)
          (fun earlier => clone.substitute
            (weakenOperation clone
              (rightProjectionEnvironment clone rest second earlier)) environment)
          later = environment later.succ
        simpa only [substitute_weakenOperation] using tailEqual

/-- The categorical first projection law, derived from clone substitution. -/
theorem categorical_pair_fst
    {source first second : ContextObject clone}
    (toFirst : source ⟶ first) (toSecond : source ⟶ second) :
    pair clone toFirst toSecond ≫ fstProjection clone first second = toFirst := by
  funext index
  exact pair_fst clone first.context second.context toFirst toSecond index

/-- The categorical second projection law. -/
theorem categorical_pair_snd
    {source first second : ContextObject clone}
    (toFirst : source ⟶ first) (toSecond : source ⟶ second) :
    pair clone toFirst toSecond ≫ sndProjection clone first second = toSecond := by
  funext index
  exact pair_snd clone first.context second.context toFirst toSecond index

/-- The eta law makes the finite-product property a genuine uniqueness
statement, not merely two projection equations. -/
theorem categorical_pair_eta
    {source first second : ContextObject clone}
    (morphism : source ⟶ concat clone first second) :
    pair clone (morphism ≫ fstProjection clone first second)
      (morphism ≫ sndProjection clone first second) = morphism :=
  appendEnvironment_eta clone first.context second.context morphism

theorem categorical_pair_unique
    {source first second : ContextObject clone}
    (toFirst : source ⟶ first) (toSecond : source ⟶ second)
    (morphism : source ⟶ concat clone first second)
    (firstEq : morphism ≫ fstProjection clone first second = toFirst)
    (secondEq : morphism ≫ sndProjection clone first second = toSecond) :
    morphism = pair clone toFirst toSecond := by
  calc
    morphism = pair clone (morphism ≫ fstProjection clone first second)
        (morphism ≫ sndProjection clone first second) :=
      (categorical_pair_eta clone morphism).symm
    _ = pair clone toFirst toSecond := by rw [firstEq, secondEq]

/-- The clone context category has binary products by concatenating input
sort lists. -/
def concatIsLimit (first second : ContextObject clone) :
    CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.BinaryFan.mk
        (fstProjection clone first second) (sndProjection clone first second)) :=
  CategoryTheory.Limits.BinaryFan.IsLimit.mk _
    (fun toFirst toSecond => pair clone toFirst toSecond)
    (fun toFirst toSecond => categorical_pair_fst clone toFirst toSecond)
    (fun toFirst toSecond => categorical_pair_snd clone toFirst toSecond)
    (fun toFirst toSecond morphism firstEq secondEq =>
      categorical_pair_unique clone toFirst toSecond morphism firstEq secondEq)

instance hasTerminal :
    CategoryTheory.Limits.HasTerminal (ContextObject clone) :=
  (emptyIsTerminal clone).hasTerminal

instance hasLimitPair (first second : ContextObject clone) :
    CategoryTheory.Limits.HasLimit (CategoryTheory.Limits.pair first second) :=
  ⟨⟨CategoryTheory.Limits.BinaryFan.mk
      (fstProjection clone first second) (sndProjection clone first second),
    concatIsLimit clone first second⟩⟩

instance hasBinaryProducts :
    CategoryTheory.Limits.HasBinaryProducts (ContextObject clone) :=
  CategoryTheory.Limits.hasBinaryProducts_of_hasLimit_pair (ContextObject clone)

#print axioms appendEnvironment_eta
#print axioms concatIsLimit

end Mettapedia.GSLT.LanguageDef.MultiSortedClone
