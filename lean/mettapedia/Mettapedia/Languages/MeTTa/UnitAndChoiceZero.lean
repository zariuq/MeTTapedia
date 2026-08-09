import Mathlib.Logic.Equiv.Defs
import Mettapedia.Languages.MeTTa.EmptinessTaxonomy

/-!
# Unit is one, zero is none — and having a spelling is not being a datum

Two questions kept getting answered together and need separating.

**Is `()` a unit or an emptiness?**  It is a unit, and the reason is
arithmetic rather than taste.  Counting answers, `return ()` has one and zero
has none; over unit answers the whole answer algebra *is* the natural
numbers, with the empty bag as `0` and `[()]` as `1`
(`listUnitEquivNat`).  Calling `()` a kind of emptiness confuses the additive
identity of choice with the multiplicative identity of sequencing.

**Does zero get a spelling?**  Yes.  A previous report of mine concluded that
"zero has no term spelling at all", which overstated what was proved.  The
dichotomy in `EmptinessTaxonomy` is about *data*: no ordinary returned datum
can also mean zero.  It says nothing against an explicit computation form,
and the model there uses one.  This module states the sharp version
generically — `ret_ne_zero`, `zero_is_not_a_return` — and then proves the
positive counterpart that the earlier phrasing wrongly excluded:

* `zeroForm_has_no_occurrences` and `quoted_zeroForm_has_one_occurrence` —
  the same piece of syntax yields no answers when elaborated and exactly one
  when quoted.

So a source spelling such as `(empty)` is coherent, provided it elaborates
to the computation form rather than to a returned datum, and provided
quotation returns its syntax instead of executing it.  Spelling and
datum-hood are independent, and conflating them is what produced the
overstatement.

The nondegeneracy hypothesis throughout is *counting*: the effect can say how
many answers it has, with `ret` giving one and `zero` giving none.  That is
weaker than assuming any particular carrier and is satisfied by every answer
algebra worth the name.  Without some such hypothesis the results are false,
since the one-point effect satisfies every law.
-/

namespace Mettapedia.Languages.MeTTa.UnitZero

/-! ## A choice effect that can count -/

/-- Computations with return, choice, sequencing, and an occurrence count.
Counting is the nondegeneracy assumption; everything else is standard. -/
structure CountedChoice (Value : Type) where
  /-- Computations over `Value`. -/
  Computation : Type
  /-- One answer. -/
  ret : Value → Computation
  /-- No answers. -/
  zero : Computation
  /-- Choice. -/
  merge : Computation → Computation → Computation
  /-- Sequencing. -/
  bind : Computation → (Value → Computation) → Computation
  /-- How many answers. -/
  occurrences : Computation → Nat
  /-- Returning gives exactly one answer. -/
  occurrences_ret : ∀ value, occurrences (ret value) = 1
  /-- Zero gives none. -/
  occurrences_zero : occurrences zero = 0
  /-- Choice adds answers. -/
  occurrences_merge : ∀ left right,
    occurrences (merge left right) = occurrences left + occurrences right
  /-- Zero annihilates sequencing. -/
  zero_bind : ∀ continuation, bind zero continuation = zero
  /-- Zero is the identity of choice, on the left. -/
  merge_zero_left : ∀ computation, merge zero computation = computation
  /-- and on the right. -/
  merge_zero_right : ∀ computation, merge computation zero = computation
  /-- Returning then continuing is continuing. -/
  ret_bind : ∀ value continuation, bind (ret value) continuation = continuation value

namespace CountedChoice

variable {Value : Type} (effect : CountedChoice Value)

/-! ## No datum is zero

This is the sharp, generic form of the taxonomy's dichotomy.  It is a
statement about *returned values*, and it is proved by counting. -/

/-- **Returning a value is never zero.**  One answer is not no answers. -/
theorem ret_ne_zero (value : Value) : effect.ret value ≠ effect.zero := by
  intro equal
  have counted : effect.occurrences (effect.ret value) = effect.occurrences effect.zero :=
    congrArg effect.occurrences equal
  rw [effect.occurrences_ret, effect.occurrences_zero] at counted
  exact Nat.one_ne_zero counted

/-- **Zero is not the return of anything.**  Equivalently: no datum, however
spelled, denotes zero.  This is exactly as far as the data argument goes. -/
theorem zero_is_not_a_return : ¬ ∃ value : Value, effect.ret value = effect.zero := by
  rintro ⟨value, isZero⟩
  exact effect.ret_ne_zero value isZero

/-! ## Unit answers are arithmetic

Over a one-element value type, counting is a bijection: the answer algebra is
the natural numbers.  `zero` is `0` and `ret ()` is `1`, which settles what
kind of thing `()` is. -/

/-- Sequencing after a single unit answer is just the continuation — `()` is
the identity of sequencing, not of choice. -/
theorem unit_ret_is_sequencing_identity (effect : CountedChoice Unit)
    (continuation : Unit → effect.Computation) :
    effect.bind (effect.ret ()) continuation = continuation () :=
  effect.ret_bind () continuation

/-- Zero is the identity of *choice*.  Stated beside the previous theorem to
make the two roles visibly different. -/
theorem zero_is_choice_identity (computation : effect.Computation) :
    effect.merge effect.zero computation = computation :=
  effect.merge_zero_left computation

/-- **There is only one computation zero in a declared choice algebra.**  Any
candidate that is a left identity for choice is the chosen zero.  No answer
type or container index appears in the statement. -/
theorem choice_zero_unique (candidate : effect.Computation)
    (leftIdentity : ∀ computation,
      effect.merge candidate computation = computation) :
    candidate = effect.zero := by
  calc
    candidate = effect.merge candidate effect.zero :=
      (effect.merge_zero_right candidate).symm
    _ = effect.zero := leftIdentity effect.zero

/-- A quotient/interpretation of choice computations that preserves merge and
is onto.  Preservation of zero is deliberately not a field: it follows from
surjectivity and uniqueness of the choice identity. -/
structure MergeQuotient {SourceValue TargetValue : Type}
    (source : CountedChoice SourceValue) (target : CountedChoice TargetValue) where
  map : source.Computation → target.Computation
  map_merge : ∀ left right,
    map (source.merge left right) = target.merge (map left) (map right)
  surjective : Function.Surjective map

namespace MergeQuotient

variable {SourceValue TargetValue : Type}
  {source : CountedChoice SourceValue} {target : CountedChoice TargetValue}

/-- **Zero is uniform across answer-level quotients.**  Every surjective
merge-preserving interpretation sends the unique source zero to the unique
target zero.  Thus list-to-bag and bag-to-set quotient maps cannot create
distinct computation empties. -/
theorem map_zero (quotient : MergeQuotient source target) :
    quotient.map source.zero = target.zero := by
  apply target.choice_zero_unique
  intro computation
  obtain ⟨preimage, rfl⟩ := quotient.surjective computation
  rw [← quotient.map_merge, source.merge_zero_left]

end MergeQuotient

/-- The unit answer is not the absence of answers. -/
theorem unit_ne_zero (effect : CountedChoice Unit) : effect.ret () ≠ effect.zero :=
  effect.ret_ne_zero ()

end CountedChoice

/-! ## The list instance -/

/-- Answer bags as lists: the standard instance. -/
def listChoice (Value : Type) : CountedChoice Value where
  Computation := List Value
  ret value := [value]
  zero := []
  merge left right := left ++ right
  bind computation continuation := computation.flatMap continuation
  occurrences := List.length
  occurrences_ret := by intro _; rfl
  occurrences_zero := rfl
  occurrences_merge := by intro left right; simp
  zero_bind := by intro _; rfl
  merge_zero_left := by intro _; simp
  merge_zero_right := by intro _; simp
  ret_bind := by intro value continuation; simp

/-- **Unit answers are literally the natural numbers.**  The empty bag is
zero, one unit answer is one, and `n` unit answers are `n`.  This is the
precise sense in which `()` belongs on the side of one. -/
def listUnitEquivNat : List Unit ≃ Nat where
  toFun := List.length
  invFun count := List.replicate count ()
  left_inv := by
    intro bag
    induction bag with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        cases head
        simp [List.replicate, inductionHypothesis]
  right_inv := by intro count; simp

@[simp] theorem listUnitEquivNat_zero : listUnitEquivNat [] = 0 := rfl

@[simp] theorem listUnitEquivNat_one : listUnitEquivNat [()] = 1 := rfl

@[simp] theorem listUnitEquivNat_two : listUnitEquivNat [(), ()] = 2 := rfl

/-- Multiplicity is real: two unit answers are not one. -/
theorem two_unit_answers_ne_one : ([(), ()] : List Unit) ≠ [()] := by decide

/-! ## Having a spelling is not being a datum

The point the earlier overstatement missed.  A syntax may contain an explicit
zero form; what it may not do is make that form elaborate to a returned
value.  Quotation then behaves exactly as it should: quoting the zero form
produces one answer, namely its syntax. -/

/-- A syntax with an explicit zero form and a quotation form. -/
structure QuotingSyntax {Value : Type} (effect : CountedChoice Value) where
  /-- Forms of the concrete syntax. -/
  Form : Type
  /-- What a form means. -/
  elaborate : Form → effect.Computation
  /-- The form that denotes no answers — a spelling such as `(empty)`. -/
  zeroForm : Form
  /-- It elaborates to the computation zero, not to a returned datum. -/
  elaborate_zeroForm : elaborate zeroForm = effect.zero
  /-- Quotation as a syntactic operation. -/
  quoteForm : Form → Form
  /-- The datum a quoted form yields. -/
  quoted : Form → Value
  /-- Quoting returns syntax as one ordinary answer instead of running it. -/
  elaborate_quoteForm : ∀ form,
    elaborate (quoteForm form) = effect.ret (quoted form)

namespace QuotingSyntax

variable {Value : Type} {effect : CountedChoice Value} (syntax' : QuotingSyntax effect)

/-- The zero form yields no answers. -/
theorem zeroForm_has_no_occurrences :
    effect.occurrences (syntax'.elaborate syntax'.zeroForm) = 0 := by
  rw [syntax'.elaborate_zeroForm, effect.occurrences_zero]

/-- Its quotation yields exactly one — the syntax, as ordinary data. -/
theorem quoted_zeroForm_has_one_occurrence :
    effect.occurrences (syntax'.elaborate (syntax'.quoteForm syntax'.zeroForm)) = 1 := by
  rw [syntax'.elaborate_quoteForm, effect.occurrences_ret]

/-- **Spelling and datum-hood are independent.**  The same piece of syntax
denotes no answers when elaborated and one answer when quoted, so a language
may name zero without any datum ever meaning zero. -/
theorem zeroForm_ne_its_quotation :
    syntax'.elaborate syntax'.zeroForm ≠
      syntax'.elaborate (syntax'.quoteForm syntax'.zeroForm) := by
  intro equal
  have counted := congrArg effect.occurrences equal
  rw [syntax'.zeroForm_has_no_occurrences,
    syntax'.quoted_zeroForm_has_one_occurrence] at counted
  exact Nat.zero_ne_one counted

/-- And the zero form is still not the return of anything, so naming it costs
nothing in the data language. -/
theorem zeroForm_elaborates_outside_ret :
    ¬ ∃ value : Value, effect.ret value = syntax'.elaborate syntax'.zeroForm := by
  rw [syntax'.elaborate_zeroForm]
  exact effect.zero_is_not_a_return

end QuotingSyntax

/-! ## A concrete quoting syntax

Instantiated so the two theorems above are not vacuous.  Forms are the small
expression language of the taxonomy; the datum a quotation yields is the
inert symbol naming the form. -/

open Mettapedia.Languages.MeTTa.Emptiness in
/-- Name a form, for quotation. -/
def formName : Expr → Datum
  | .zero => .sym "empty"
  | .pure datum => .cons (.sym "pure") datum
  | .plus _ _ => .sym "plus"
  | .build _ _ => .sym "build"
  | .call _ => .sym "call"
  | .collapse _ => .sym "collapse"

open Mettapedia.Languages.MeTTa.Emptiness in
/-- Elaboration of the concrete syntax, with quotation added on top. -/
def concreteElaborate : Option Expr × Expr → List Datum
  | (some quotedForm, _) => [formName quotedForm]
  | (none, expression) => denoteClean expression

open Mettapedia.Languages.MeTTa.Emptiness in
/-- The concrete instance: `(empty)` elaborates to no answers, while its
quotation elaborates to the single datum naming it. -/
def concreteQuoting : QuotingSyntax (listChoice Datum) where
  Form := Option Expr × Expr
  elaborate := concreteElaborate
  zeroForm := (none, .zero)
  elaborate_zeroForm := rfl
  quoteForm form := (some form.2, form.2)
  quoted form := formName form.2
  elaborate_quoteForm := by intro form; rfl

open Mettapedia.Languages.MeTTa.Emptiness in
/-- The concrete zero form really yields nothing. -/
theorem concrete_zero_empty :
    concreteElaborate ((none, .zero) : Option Expr × Expr) = [] := rfl

open Mettapedia.Languages.MeTTa.Emptiness in
/-- and its quotation really yields the naming symbol. -/
theorem concrete_quoted_zero :
    concreteElaborate ((some .zero, .zero) : Option Expr × Expr) = [.sym "empty"] := rfl

end Mettapedia.Languages.MeTTa.UnitZero
