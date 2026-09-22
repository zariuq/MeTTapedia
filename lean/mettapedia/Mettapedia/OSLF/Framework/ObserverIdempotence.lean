import Mettapedia.OSLF.Framework.ObserverExtension

/-!
# Extending twice adds nothing on the terms one started with

The source states that the observer extension is idempotent: the bisimilarity of
the twice-extended theory and that of the once-extended theory agree on the terms
of the original signature.

The step-level content of that claim is proved here, and it is proved by
**applying the conservativity theorem a second time** rather than by a new
argument. Conservativity says that on a term headed by an authored operation the
extension rewrites exactly as the authored theory does. Reading the once-extended
theory as the authored one and extending it again, the same theorem says that the
second extension changes nothing there either. So the original terms step alike
under no extension, one extension and two.

What the second application costs is one honest hypothesis, and naming it is the
point of doing this rather than asserting the idempotence. Conservativity is
conditional on the adjoined vocabulary being fresh for the theory it is adjoined
to, and freshness for the *original* theory says nothing about freshness for the
*extended* one: a second round of instruments may collide with the first round's.
`AdministrativeFresh` is decidable, so the condition is checkable on a
presentation rather than assumed of it, and that is what "in the source-qualified
sense" has to mean here.
-/

namespace Mettapedia.OSLF.Framework.ObserverIdempotence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.ObserverExtension

set_option autoImplicit false

/-- The original signature's operations remain authored operations of the
extension, since the extension retains the authored grammar and only adjoins to
it. -/
theorem authored_in_extension (lang : LanguageDef) (cut : CollType)
    (opened : List String) {names : List String}
    (namesAuthored : ∀ name ∈ names, name ∈ lang.terms.map GrammarRule.label) :
    ∀ name ∈ names,
      name ∈ (observerExtension lang cut opened).terms.map GrammarRule.label := by
  intro name mem
  have := namesAuthored name mem
  simpa [observerExtension, List.map_append] using Or.inl this

/-- **The second extension changes nothing the first left alone.**  On a term
headed by an operation of the original signature, the once-extended and
twice-extended theories produce the same reducts -- conditional on the second
round's vocabulary being fresh for the first-extended theory, which is decidable
and can fail. -/
theorem rewriteAt_eq_of_second_extension
    (lang : LanguageDef) (cut : CollType) (opened secondOpened : List String)
    {names : List String}
    (namesAuthored : ∀ name ∈ names, name ∈ lang.terms.map GrammarRule.label)
    (freshSecond :
      AdministrativeFresh (observerExtension lang cut opened) secondOpened)
    (closedFirst : ∀ rule ∈ (observerExtension lang cut opened).rewrites,
      CallsWithin names rule.premises)
    (baseOne baseTwo : BasePremiseEvaluator) (fuel : Nat) {source : Pattern}
    (head : HasOperationHead names source) :
    rewriteAt baseOne (observerExtension lang cut opened) fuel source
      = rewriteAt baseTwo
          (observerExtension (observerExtension lang cut opened) cut secondOpened)
          fuel source :=
  rewriteAt_eq_of_authored_head (observerExtension lang cut opened) cut secondOpened
    (authored_in_extension lang cut opened namesAuthored)
    freshSecond closedFirst baseOne baseTwo fuel head

/-- **Idempotence on the authored terms.**  Under both rounds' conditions, the
original theory, its extension and the extension of its extension all produce the
same reducts on a term of the original signature.  So the instruments are added
once; adding them again is inert where the authored vocabulary lives. -/
theorem rewriteAt_eq_of_two_extensions
    (lang : LanguageDef) (cut : CollType) (opened secondOpened : List String)
    {names : List String}
    (namesAuthored : ∀ name ∈ names, name ∈ lang.terms.map GrammarRule.label)
    (freshFirst : AdministrativeFresh lang opened)
    (freshSecond :
      AdministrativeFresh (observerExtension lang cut opened) secondOpened)
    (closedBase : ∀ rule ∈ lang.rewrites, CallsWithin names rule.premises)
    (closedFirst : ∀ rule ∈ (observerExtension lang cut opened).rewrites,
      CallsWithin names rule.premises)
    (baseOne baseTwo : BasePremiseEvaluator) (fuel : Nat) {source : Pattern}
    (head : HasOperationHead names source) :
    rewriteAt baseOne lang fuel source
      = rewriteAt baseTwo
          (observerExtension (observerExtension lang cut opened) cut secondOpened)
          fuel source := by
  refine (rewriteAt_eq_of_authored_head lang cut opened namesAuthored freshFirst
    closedBase baseOne baseOne fuel head).trans ?_
  exact rewriteAt_eq_of_second_extension lang cut opened secondOpened
    namesAuthored freshSecond closedFirst baseOne baseTwo fuel head


/-! ## The qualification is real, and it is not the one the name suggests

The source calls the property idempotence.  Idempotence would suggest that
applying the construction twice is the same as applying it once, for any second
round.  It is not: the condition the second application needs **fails exactly
when the second round opens a constructor the first already instrumented**,
because the vocabulary it would adjoin is already declared.

Both directions are decided on the worked presentation, whose three constructors
let a second round be disjoint from the first. -/

/-- **A disjoint second round is fresh**, so the idempotence theorem above has a
non-degenerate instance: the second round really does adjoin instruments, for a
constructor the first round left alone. -/
theorem disjoint_second_round_is_fresh :
    AdministrativeFresh Gap.extended ["D"] := by decide

/-- **Repeating a round is not fresh.**  Re-opening the constructors the first
round instrumented collides with the vocabulary it adjoined, so the hypothesis
the idempotence theorem carries is a condition a presentation can fail rather
than a formality. -/
theorem repeating_a_round_is_not_fresh :
    ¬ AdministrativeFresh Gap.extended Gap.opened := by decide

/-- And failing on a single repeated constructor is enough. -/
theorem reopening_one_constructor_is_not_fresh :
    ¬ AdministrativeFresh Gap.extended ["C"] := by decide


/-! ## Calibration's presentation-level half

The source's calibration lemma says equal terms are bisimilar in the extension.
Its **semantic** half needs the extension's step relation to respect the
equations, and that is not established here, so the ledger's row for it stands as
constructed rather than proved.

Its **presentation-level** half is immediate and worth recording, because it is
the reason the semantic half is even plausible: the extension adjoins vocabulary
and rules and takes nothing away, so the authored equational theory it must
calibrate against is the one it started with, unchanged and unrenamed. -/

/-- **The extension retains the authored equations exactly.**  Not one is
dropped, added or rewritten, so there is no gap between the theory being
calibrated and the theory calibrating it. -/
theorem equations_preserved (lang : LanguageDef) (cut : CollType)
    (opened : List String) :
    (observerExtension lang cut opened).equations = lang.equations := rfl

/-- **And the authored sorts, grammar and rules survive as prefixes.**  The
extension only appends, so every authored declaration is still present, in
order, under its own name. -/
theorem authored_retained (lang : LanguageDef) (cut : CollType)
    (opened : List String) :
    lang.types <+: (observerExtension lang cut opened).types
      ∧ lang.terms <+: (observerExtension lang cut opened).terms
      ∧ lang.rewrites <+: (observerExtension lang cut opened).rewrites :=
  ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_append _ _⟩

end Mettapedia.OSLF.Framework.ObserverIdempotence
