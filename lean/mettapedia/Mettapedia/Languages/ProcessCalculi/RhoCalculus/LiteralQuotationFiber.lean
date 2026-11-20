import Mettapedia.OSLF.MeTTaIL.ReflectiveResolution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

/-!
# The literal-quotation fiber of rho substitution

The compiled reflective substitution first resolves every quotation `@P`
whose payload is a single drop `*n` modulo the parallel unit and nesting, and
then substitutes structurally. The paper-facing substitution
(Meredith and Radestock 2005, section 2.7) compares names modulo name
equivalence but keeps their spelling. This module locates where the two
coincide and where they cannot.

* The fiber is the set of derived rho processes whose quotations expose a
  drop only literally. On it the compiled substitution is the paper-facing
  one (`LanguageDefAdequacy.substituteReflective_rhoProc_agrees`).
* The fiber is closed under substitution of fiber names
  (`ReflectiveResolution.quotesLiteral_substituteReflective`).
* It is not closed under COMM, and no COMM-closed set containing two small
  fiber members admits exact agreement: COMM quotes received processes, and
  quoting `0 | *z` exposes `*z` through the parallel unit.
* Every derived process is related to its resolution, which lies in the fiber,
  by every congruence satisfying the parallel monoid laws and quote-drop. The
  congruence is a parameter; no particular relation is fixed here.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LiteralQuotationFiber

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent
open Mettapedia.OSLF.MeTTaIL.ReflectiveResolution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

/-! ## Reading the fiber condition on rho constructors -/

@[simp] theorem quotesLiteral_bvar (index : Nat) :
    quotesLiteral rhoReflectivePresentation (.bvar index) = true := rfl

@[simp] theorem quotesLiteral_fvar (name : String) :
    quotesLiteral rhoReflectivePresentation (.fvar name) = true := rfl

@[simp] theorem quotesLiteral_zero :
    quotesLiteral rhoReflectivePresentation (.apply "PZero" []) = true := rfl

@[simp] theorem quotesLiteral_drop (name : Pattern) :
    quotesLiteral rhoReflectivePresentation (.apply "PDrop" [name]) =
      quotesLiteral rhoReflectivePresentation name := by
  simp [quotesLiteral, rhoReflectivePresentation]

@[simp] theorem quotesLiteral_quote (code : Pattern) :
    quotesLiteral rhoReflectivePresentation (.apply "NQuote" [code]) =
      (exposesLiterally rhoReflectivePresentation code && quotesLiteral rhoReflectivePresentation code) := by
  simp [quotesLiteral, rhoReflectivePresentation]

@[simp] theorem quotesLiteral_output (channel payload : Pattern) :
    quotesLiteral rhoReflectivePresentation (.apply "POutput" [channel, payload]) =
      (quotesLiteral rhoReflectivePresentation channel &&
        quotesLiteral rhoReflectivePresentation payload) := by
  simp [quotesLiteral, quotesLiteralList]

@[simp] theorem quotesLiteral_input (channel body : Pattern) :
    quotesLiteral rhoReflectivePresentation (.apply "PInput" [channel, .lambda none body]) =
      (quotesLiteral rhoReflectivePresentation channel &&
        quotesLiteral rhoReflectivePresentation body) := by
  simp [quotesLiteral, quotesLiteralList]

@[simp] theorem quotesLiteral_parallel (members : List Pattern) :
    quotesLiteral rhoReflectivePresentation (.collection .hashBag members none) =
      quotesLiteralList rhoReflectivePresentation members := rfl

@[simp] theorem quotesLiteralList_nil :
    quotesLiteralList rhoReflectivePresentation [] = true := rfl

@[simp] theorem quotesLiteralList_cons (first : Pattern) (rest : List Pattern) :
    quotesLiteralList rhoReflectivePresentation (first :: rest) =
      (quotesLiteral rhoReflectivePresentation first &&
        quotesLiteralList rhoReflectivePresentation rest) := rfl

/-! ## The rho fiber -/

private theorem rho_distinct :
    rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor ≠
      rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor := by
  decide

/-- The literal-quotation fiber in a binder context: derived rho processes
whose quotations expose a drop only literally. -/
def InFiber (free : FreeSortContext) (bound : List String) (process : Pattern) : Prop :=
  ProcWellSorted rhoReflectivePresentation free bound process ∧
    quotesLiteral rhoReflectivePresentation process = true

/-- On the fiber the compiled substitution is the paper-facing substitution
at every depth and for every replacement name. -/
theorem substitution_exact {free : FreeSortContext} {bound : List String} {process : Pattern}
    (member : InFiber free bound process) (depth : Nat) (replacementName : Pattern) :
    substituteReflective rhoReflectivePresentation depth replacementName process =
      semanticSubstProc depth replacementName process :=
  substituteReflective_rhoProc_agrees member.1 member.2 depth replacementName

/-- **The fiber is closed under substitution of fiber names.** Removing one
communication binder by a closed, scope-safe fiber name keeps a scope-safe
fiber member in the fiber, and the compiled and paper-facing substitutions
coincide there. -/
theorem substitute_fiber_name {free : FreeSortContext} {index : Nat}
    {body replacementName : Pattern}
    (member : InFiber free (List.replicate (index + 1) rhoReflectivePresentation.nameSort) body)
    (bodySafe : binderSafeAt "NQuote" (index + 1) body = true)
    (replacementTyped : NameWellSorted rhoReflectivePresentation free [] replacementName)
    (replacementSafe : binderSafeAt "NQuote" 0 replacementName = true)
    (replacementLiteral : quotesLiteral rhoReflectivePresentation replacementName = true) :
    substituteReflective rhoReflectivePresentation index replacementName body =
        semanticSubstProc index replacementName body ∧
      InFiber free (List.replicate index rhoReflectivePresentation.nameSort)
        (substituteReflective rhoReflectivePresentation index replacementName body) ∧
      binderSafeAt "NQuote" index
        (substituteReflective rhoReflectivePresentation index replacementName body) = true := by
  have exact := substitution_exact member index replacementName
  have preserved := semanticSubstProc_preserves member.1 bodySafe replacementTyped replacementSafe
  have literal := quotesLiteral_substituteReflective rho_distinct replacementLiteral index body
  rw [exact] at literal ⊢
  exact ⟨rfl, ⟨preserved.1, literal⟩, preserved.2⟩

/-- The control `@(*x | 0)!(0)` lies outside the fiber. -/
theorem hiddenQuoteDropBody_not_inFiber (free : FreeSortContext) (bound : List String) :
    ¬ InFiber free bound hiddenQuoteDropBody := fun member => by
  have literal := member.2
  revert literal
  decide +kernel

/-! ## COMM leaves the fiber

COMM quotes the received process. Receiving `0` at `*y` in `*y | *z` leaves
`0 | *z`, a fiber member; sending it on `y` and quoting it yields the channel
`@(0 | *z)`, which exposes `*z` only through the parallel unit. -/

/-- The free name `z` of the obstruction. -/
def zContext : FreeSortContext :=
  fun name => if name = "z" then some rhoReflectivePresentation.nameSort else none

/-- `*y | *z` under the received binder `y`. -/
def drops : Pattern :=
  .collection .hashBag [.apply "PDrop" [.bvar 0], .apply "PDrop" [.fvar "z"]] none

/-- `0 | *z`. -/
def received : Pattern :=
  .collection .hashBag [.apply "PZero" [], .apply "PDrop" [.fvar "z"]] none

/-- The output of `0` on the received binder `y`. -/
def sendZero : Pattern := .apply "POutput" [.bvar 0, .apply "PZero" []]

theorem drops_inFiber : InFiber zContext [rhoReflectivePresentation.nameSort] drops :=
  ⟨.parallel (.cons (.drop (.bvar rfl)) (.cons (.drop (.fvar rfl)) .nil)), by decide +kernel⟩

theorem zero_inFiber : InFiber zContext [] (.apply "PZero" []) := ⟨.unit, by decide +kernel⟩

theorem received_inFiber : InFiber zContext [] received :=
  ⟨.parallel (.cons .unit (.cons (.drop (.fvar rfl)) .nil)), by decide +kernel⟩

theorem sendZero_inFiber : InFiber zContext [rhoReflectivePresentation.nameSort] sendZero :=
  ⟨.output (.bvar rfl) .unit, by decide +kernel⟩

/-- `0 | *z` is the COMM contractum of `*y | *z` receiving `0`. -/
theorem received_eq_comm : semanticCommSubst drops (.apply "PZero" []) = received := by
  decide +kernel

/-- **The fiber is not closed under COMM.** -/
theorem comm_leaves_fiber :
    ¬ InFiber zContext [] (semanticCommSubst sendZero received) := fun member => by
  have literal := member.2
  revert literal
  decide +kernel

/-- **No COMM-closed set with exact agreement contains `y!(0)` and `0 | *z`.**
COMM takes the two to `@(0 | *z)!(0)`; receiving `0 | *z` there, the
compiled COMM step resolves the channel to `z`, while the paper-facing
substitution keeps the name as written. The responsible laws are the unit law
`P | 0 ≡ P` of structural congruence (section 2.3) and quote-drop
`@(*x) ≡N x` of name equivalence (section 2.4): the compiled substitution
normalizes a name by them, the paper-facing one only compares names by them. -/
theorem exact_agreement_not_comm_closed (fiber : Pattern → Prop)
    (hasSend : fiber sendZero) (hasReceived : fiber received)
    (closed : ∀ body payload, fiber body → fiber payload → fiber (semanticCommSubst body payload))
    (channel : Pattern) (rest : List Pattern) :
    ¬ ∀ body payload, fiber body → fiber payload →
        applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
            (rhoCommBindings channel body payload rest) =
          .collection .hashBag (semanticCommSubst body payload :: rest) none := by
  intro agrees
  have equal := agrees _ _ (closed _ _ hasSend hasReceived) hasReceived
  rw [applyBindingsForRule_rhoComm] at equal
  injection equal with _ elements
  injection elements with heads
  revert heads
  decide +kernel

/-! ## Every process is related to a fiber member

The congruence is a parameter. Its laws are those of the paper's structural
congruence on parallel composition (section 2.3), read for an n-ary
presentation, together with quote-drop (section 2.4), and congruence at every
position, name positions inside processes included (the paper uses name
equivalence under a prefix in section 2.8). A finer relation without
congruence at name positions does not relate a process to its resolution. -/

/-- **Every derived rho process is related to a fiber member**, by every
congruence with the parallel monoid laws and quote-drop, and the compiled
substitution of the process is the paper-facing substitution of that member. -/
theorem related_fiber_member (congruence : QuoteDropCongruence rhoReflectivePresentation)
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process) :
    ∃ member, congruence.rel process member ∧ InFiber free bound member ∧
      ∀ (depth : Nat) (replacementName : Pattern),
        substituteReflective rhoReflectivePresentation depth replacementName process =
          semanticSubstProc depth replacementName member :=
  ⟨resolveQuotes rhoReflectivePresentation process,
    congruence.related_resolveQuotes process,
    ⟨rhoProc_resolveQuotes_typed typed, quotesLiteral_of_resolved (resolveQuotes_resolved process)⟩,
    substituteReflective_rhoProc_eq_resolved typed⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LiteralQuotationFiber
