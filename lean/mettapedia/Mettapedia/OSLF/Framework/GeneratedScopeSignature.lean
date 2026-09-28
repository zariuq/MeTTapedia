import Mettapedia.OSLF.StructuralModal.Recursive
import Mettapedia.OSLF.Framework.GeneratedScope

/-!
# The generated scope as a recursive signature

`GeneratedScope` builds a name scope as the least fixed point of a transformer
written by hand.  The structural layer already has a better home for exactly that
shape — an indexed recursive signature whose every branch is witnessed by a
constructor the presentation declares, with its own unfolding and leastness — and
until collection branches existed, a scope could not live there, because the
parallel composition it splits on is a bag.

It can now, and this is the scope rebuilt on it.

**Two states, and why.**  A scope is a set of *names*, and its recursion asks
whether the quotes of the two parts are in scope, not whether the parts are.  So
the signature carries a second index: the processes whose quote is in scope.  A
name is in scope when it is the quote of one of those, and a process is one of
those when it is a declared atom or a composition of two more.  That is the same
recursion, indexed so that every step matches a term former.

**What it costs.**  The hand-written scope takes arbitrary predicates for its
atoms.  A signature cannot: its branches are constructors of the presentation.
So the atoms here are declared nullary processes, and that restriction is the
content of being language-generated rather than a loss of generality that was
quietly taken.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneratedScopeSignature

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.StructuralModal
open Mettapedia.OSLF.StructuralModal.Recursive

/-! ## The presentation -/

/-- The quote former: a name is a quoted process. -/
def quoteRule : GrammarRule where
  label := "NQuote"
  category := "Name"
  params := [.simple "quoted" (.base "Proc")]
  syntaxPattern := [.terminal "NQuote"]

/-- The first atom. -/
def atomARule : GrammarRule where
  label := "A"
  category := "Proc"
  params := []
  syntaxPattern := [.terminal "A"]

/-- The second atom. -/
def atomBRule : GrammarRule where
  label := "B"
  category := "Proc"
  params := []
  syntaxPattern := [.terminal "B"]

/-- An atom the scope does not generate. -/
def atomCRule : GrammarRule where
  label := "C"
  category := "Proc"
  params := []
  syntaxPattern := [.terminal "C"]

/-- The parallel carrier. -/
def parRule : GrammarRule where
  label := "Par"
  category := "Proc"
  params := [.simple "parts" (.collection .hashBag (.base "Proc"))]
  syntaxPattern := [.terminal "Par"]

/-- The presentation the scope is generated over. -/
def language : LanguageDef where
  name := "ScopeCalculus"
  types := [TypeDecl.plain "Proc", TypeDecl.plain "Name"]
  terms := [quoteRule, atomARule, atomBRule, atomCRule, parRule]
  equations := []
  rewrites := []

/-! ## The signature -/

/-- The two indices: names that are in scope, and processes whose quote is. -/
inductive State where
  /-- A name of the generated scope. -/
  | inScope
  /-- A process whose quote is a name of the generated scope. -/
  | quotable
  deriving DecidableEq, Repr

/-- The branches, one per term former the scope reads. -/
inductive Branch where
  /-- A name in scope is the quote of a quotable process. -/
  | quoted
  /-- The first atom is quotable. -/
  | atomA
  /-- The second atom is quotable. -/
  | atomB
  /-- A composition of two quotable processes is quotable. -/
  | composed
  deriving DecidableEq, Repr

/-- Every branch matches a term former, and its arguments are states. -/
def describe : Branch → BranchDescription State
  | .quoted => ⟨.inScope, .headed "NQuote", [.recur .quotable]⟩
  | .atomA => ⟨.quotable, .headed "A", []⟩
  | .atomB => ⟨.quotable, .headed "B", []⟩
  | .composed =>
      ⟨.quotable, .collected .hashBag, [.recur .quotable, .recur .quotable]⟩

/-- **The signature.**  Every branch is witnessed by the presentation: the three
headed branches by declared rules of matching arity, and the collection branch
by the declared parallel carrier. -/
def signature : Signature State where
  language := language
  Branch := Branch
  describe := describe
  declared := by
    intro branch
    cases branch with
    | quoted => exact ⟨quoteRule, by simp [language], rfl, rfl⟩
    | atomA => exact ⟨atomARule, by simp [language], rfl, rfl⟩
    | atomB => exact ⟨atomBRule, by simp [language], rfl, rfl⟩
    | composed =>
        exact ⟨parRule, by simp [language], "parts", .base "Proc", rfl⟩

/-! ## Terms -/

/-- The first atom. -/
def termA : Pattern := .apply "A" []

/-- The second atom. -/
def termB : Pattern := .apply "B" []

/-- The atom outside the scope. -/
def termC : Pattern := .apply "C" []

/-- A quoted process. -/
def quote (process : Pattern) : Pattern := .apply "NQuote" [process]

/-- A parallel composition. -/
def par (left right : Pattern) : Pattern :=
  .collection .hashBag [left, right] none

/-! ## The scope, inhabited -/

variable (span : ReductionSpan Pattern)

/-- The first atom is quotable. -/
theorem quotable_atomA : Satisfies span signature .quotable termA := by
  have evidence := Satisfies.headed (span := span) (signature := signature)
    Branch.atomA "A" [] rfl .nil
  simpa [signature, describe, termA] using evidence

/-- And the second. -/
theorem quotable_atomB : Satisfies span signature .quotable termB := by
  have evidence := Satisfies.headed (span := span) (signature := signature)
    Branch.atomB "B" [] rfl .nil
  simpa [signature, describe, termB] using evidence

/-- A composition of two quotable processes is quotable. -/
theorem quotable_par {left right : Pattern}
    (leftQuotable : Satisfies span signature .quotable left)
    (rightQuotable : Satisfies span signature .quotable right) :
    Satisfies span signature .quotable (par left right) := by
  have evidence := Satisfies.collected (span := span) (signature := signature)
    Branch.composed .hashBag [left, right] rfl
    (.recur leftQuotable (.recur rightQuotable .nil))
  simpa [signature, describe, par] using evidence

/-- **The quote of a quotable process is in scope.**  This is the generator's
unfolding, and it is what makes the scope unboundedly large while its
description stays the size it is. -/
theorem inScope_quote {process : Pattern}
    (quotable : Satisfies span signature .quotable process) :
    Satisfies span signature .inScope (quote process) := by
  have evidence := Satisfies.headed (span := span) (signature := signature)
    Branch.quoted "NQuote" [process] rfl (.recur quotable .nil)
  simpa [signature, describe, quote] using evidence

/-- The two atoms' quotes are in scope. -/
theorem inScope_atomA : Satisfies span signature .inScope (quote termA) :=
  inScope_quote span (quotable_atomA span)

theorem inScope_atomB : Satisfies span signature .inScope (quote termB) :=
  inScope_quote span (quotable_atomB span)

/-- **And so is the quote of their composition** — the case the collection
branch exists for. -/
theorem inScope_composite :
    Satisfies span signature .inScope (quote (par termA termB)) :=
  inScope_quote span (quotable_par span (quotable_atomA span) (quotable_atomB span))

/-- Nesting: the scope is closed under composing what it already has. -/
theorem inScope_nested :
    Satisfies span signature .inScope
      (quote (par (par termA termB) termA)) :=
  inScope_quote span
    (quotable_par span
      (quotable_par span (quotable_atomA span) (quotable_atomB span))
      (quotable_atomA span))

/-! ## And what it excludes -/

/-- The third atom is not quotable: no branch of the signature matches it, so
nothing puts it in. -/
theorem not_quotable_atomC : ¬ Satisfies span signature .quotable termC := by
  intro evidence
  obtain ⟨branch, output, children, shape, _⟩ :=
    (satisfies_iff_layer span signature .quotable termC).mp evidence
  cases branch <;>
    simp [signature, describe, termC, BranchShape.Matches] at output shape

/-- **So its quote is not in scope.**  The scope is generated, not everything. -/
theorem not_inScope_atomC : ¬ Satisfies span signature .inScope (quote termC) := by
  intro evidence
  obtain ⟨branch, output, children, shape, childrenLayer⟩ :=
    (satisfies_iff_layer span signature .inScope (quote termC)).mp evidence
  cases branch with
  | quoted =>
      simp only [signature, describe, BranchShape.Matches, quote,
        Pattern.apply.injEq] at shape
      obtain ⟨-, childrenEq⟩ := shape
      subst childrenEq
      simp only [signature, describe, layerAll] at childrenLayer
      exact not_quotable_atomC span childrenLayer.1
  | atomA => simp [signature, describe] at output
  | atomB => simp [signature, describe] at output
  | composed => simp [signature, describe] at output

/-! ## The hand-written scope, recovered

`GeneratedScope` builds the same region as the least fixed point of a
transformer written by hand.  If the two only resembled each other this module
would be a second construction beside the first, which is the thing it exists to
avoid.  They do not resemble each other: they are equal, and each containment is
proved by the leastness principle of its own side — the signature's polynomial
is closed in the hand-written fixed point, and the hand-written fixed point's
induction principle lands in the signature's index.

So the hand-written transformer is what the signature's polynomial *comes to* at
these four branches, and everything the older module proved about the scope —
in particular that membership is decided by descent — is a statement about this
one.
-/

open Mettapedia.OSLF.Framework.FormulaFixpoint (Pred)
open Mettapedia.OSLF.Framework.GeneratedScope
  (generatedScope scope_induction mem_of_atomA mem_of_atomB mem_of_par inScope_iff)

/-- The first atom's quote, as a decidable test on names. -/
def atomADecide : Pattern → Bool := fun name => name == quote termA

/-- And the second's. -/
def atomBDecide : Pattern → Bool := fun name => name == quote termB

/-- The atoms the presentation declares, read as predicates on names.  The
hand-written scope takes arbitrary predicates here; what the signature can
supply is exactly the tests that a declared nullary process has been quoted. -/
def atomAName : Pred := fun name => atomADecide name = true

/-- And the second. -/
def atomBName : Pred := fun name => atomBDecide name = true

/-- **The two indices, read as one predicate of the hand-written scope.**  A
name is in scope when the scope holds it; a process is quotable when the scope
holds its quote.  That the second index needs no separate fixed point is the
content of the signature carrying it: the recursion on processes is the
recursion on their quotes, transposed. -/
def bridge : State → Pattern → Prop
  | .inScope => generatedScope atomAName atomBName
  | .quotable => fun process => generatedScope atomAName atomBName (quote process)

/-- **The signature's polynomial is closed in the hand-written fixed point.**
One case per branch, and each is the corresponding case of the hand-written
transformer. -/
theorem bridge_closed : Closed span signature bridge := by
  rintro index pattern ⟨branch, output, children, shape, childrenLayer⟩
  cases branch with
  | quoted =>
      simp only [signature, describe] at output shape childrenLayer
      subst output
      match children, childrenLayer with
      | [process], childrenLayer =>
          simp only [BranchShape.Matches] at shape
          subst shape
          exact childrenLayer.1
  | atomA =>
      simp only [signature, describe] at output shape childrenLayer
      subst output
      match children, childrenLayer with
      | [], _ =>
          simp only [BranchShape.Matches] at shape
          subst shape
          exact mem_of_atomA (by simp [atomAName, atomADecide, quote, termA])
  | atomB =>
      simp only [signature, describe] at output shape childrenLayer
      subst output
      match children, childrenLayer with
      | [], _ =>
          simp only [BranchShape.Matches] at shape
          subst shape
          exact mem_of_atomB (by simp [atomBName, atomBDecide, quote, termB])
  | composed =>
      simp only [signature, describe] at output shape childrenLayer
      subst output
      match children, childrenLayer with
      | [left, right], childrenLayer =>
          simp only [BranchShape.Matches] at shape
          subst shape
          exact mem_of_par childrenLayer.1 childrenLayer.2.1

/-- **Inversion at the quote.**  A name is in scope only as the quote of a
quotable process: the signature has one branch at that index, and this is what
having exactly one says. -/
theorem quotable_of_inScope_quote {process : Pattern}
    (evidence : Satisfies span signature .inScope (quote process)) :
    Satisfies span signature .quotable process := by
  obtain ⟨branch, output, children, shape, childrenLayer⟩ :=
    (satisfies_iff_layer span signature .inScope (quote process)).mp evidence
  cases branch with
  | quoted =>
      simp only [signature, describe, BranchShape.Matches, quote,
        Pattern.apply.injEq] at shape
      obtain ⟨-, childrenEq⟩ := shape
      subst childrenEq
      simp only [signature, describe, layerAll] at childrenLayer
      exact childrenLayer.1
  | atomA => simp [signature, describe] at output
  | atomB => simp [signature, describe] at output
  | composed => simp [signature, describe] at output

/-- The other containment: the hand-written fixed point's induction principle
lands in the signature's index. -/
theorem satisfies_inScope_of_generatedScope (name : Pattern)
    (member : generatedScope atomAName atomBName name) :
    Satisfies span signature .inScope name := by
  refine scope_induction
    (invariant := fun name => Satisfies span signature .inScope name) ?_ ?_ ?_ name member
  · intro candidate isAtomA
    simp only [atomAName, atomADecide, beq_iff_eq] at isAtomA
    subst isAtomA
    exact inScope_atomA span
  · intro candidate isAtomB
    simp only [atomBName, atomBDecide, beq_iff_eq] at isAtomB
    subst isAtomB
    exact inScope_atomB span
  · intro left right leftInScope rightInScope
    exact inScope_quote span
      (quotable_par span
        (quotable_of_inScope_quote span leftInScope)
        (quotable_of_inScope_quote span rightInScope))

/-- **The two constructions agree.**  The signature's index at names is the
generated scope of the presentation's own atoms — so the recursive signature is
the scope construction, not a second one resembling it. -/
theorem inScope_iff_generatedScope (name : Pattern) :
    Satisfies span signature .inScope name ↔ generatedScope atomAName atomBName name :=
  ⟨fun evidence => evidence.least (bridge_closed span),
    satisfies_inScope_of_generatedScope span name⟩

/-- And at the other index, transposed along the quote. -/
theorem quotable_iff_generatedScope (process : Pattern) :
    Satisfies span signature .quotable process ↔
      generatedScope atomAName atomBName (quote process) :=
  ⟨fun evidence => evidence.least (bridge_closed span),
    fun member =>
      quotable_of_inScope_quote span ((inScope_iff_generatedScope span _).mpr member)⟩

/-- **So membership of the signature's index is decided by descent.**  The
decision procedure was written against the hand-written fixed point; the
agreement above makes it a decision procedure for this one, with no second
procedure and no second correctness proof. -/
theorem inScope_iff_descent (name : Pattern) :
    Satisfies span signature .inScope name ↔
      GeneratedScope.inScope atomADecide atomBDecide name = true :=
  (inScope_iff_generatedScope span name).trans (inScope_iff name).symm

/-- Decided, positively: the composite's quote. -/
theorem descent_composite :
    GeneratedScope.inScope atomADecide atomBDecide (quote (par termA termB)) = true := by
  simp [GeneratedScope.inScope, quote, par, termA, termB, atomADecide, atomBDecide,
    GeneratedScope.quote, GeneratedScope.par]

/-- And negatively: the excluded atom's quote. -/
theorem descent_atomC :
    GeneratedScope.inScope atomADecide atomBDecide (quote termC) = false := by
  simp [GeneratedScope.inScope, quote, termC, termA, termB, atomADecide, atomBDecide]

end Mettapedia.OSLF.Framework.GeneratedScopeSignature
