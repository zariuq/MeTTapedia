import Mettapedia.GSLT.Core.MultiRewrite
import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Multi-argument rewrites as a coGSLT *declaration* layer

The five-field `LanguageDef` is unchanged.  This layer stores n-ary window
declarations; it is not the object-language matcher.

Honest limits of `denotedGSLT` in this file:

* Rules fire on **literal** source/target pattern lists.  There is no
  instantiation, no join (shared variables across sources), and no call
  to `mergeBindingsWith`.  A COMM canary on `.fvar "out"` is a fact about
  the declaration syntax, not rho semantics.
* Unary `LanguageDef.rewrites` are embedded as singleton windows of their
  `left`/`right` patterns only.  Their `premises` stay the engine's job.
* The ordered (pre-net) carrier is used.  Rho soups and Petri markings
  are the commutative collapse in `GSLT.Core.MultiRewrite.Comm`, which
  is the bag-plus-rest idiom already in `PetriNetInstance`.

Quotation is an exact section.  Invalid libraries fail at elaboration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MultiRewriteExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.MultiRewrite
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- One authored n-ary rewrite: a list of source patterns becomes a list of
target patterns. -/
structure MultiRewriteDecl where
  name : String
  sources : List Pattern
  targets : List Pattern
deriving Repr, DecidableEq

inductive MultiRewriteSyntax where
  | rule (name : String) (sources targets : List Pattern)
deriving Repr, DecidableEq

def encodeDecl (declaration : MultiRewriteDecl) : MultiRewriteSyntax :=
  .rule declaration.name declaration.sources declaration.targets

def decodeDecl : MultiRewriteSyntax → MultiRewriteDecl
  | .rule name sources targets => { name, sources, targets }

@[simp] theorem decode_encode (declaration : MultiRewriteDecl) :
    decodeDecl (encodeDecl declaration) = declaration := by
  cases declaration
  rfl

@[simp] theorem encode_decode (source : MultiRewriteSyntax) :
    encodeDecl (decodeDecl source) = source := by
  cases source
  rfl

def multiRewriteCodec :
    ExactDeclarationCodec MultiRewriteSyntax MultiRewriteDecl where
  encode := encodeDecl
  decode := decodeDecl
  decode_encode := decode_encode
  encode_decode := encode_decode

/-- A rule must be named and must actually rewrite something. -/
def MultiRewriteDecl.admissible (declaration : MultiRewriteDecl) : Bool :=
  !declaration.name.isEmpty &&
    (!declaration.sources.isEmpty || !declaration.targets.isEmpty)

def LibraryAdmissible (declarations : List MultiRewriteDecl) : Bool :=
  decide (declarations.map (fun d => d.name)).Nodup &&
    declarations.all MultiRewriteDecl.admissible

abbrev AdmittedLibrary :=
  { declarations : List MultiRewriteDecl // LibraryAdmissible declarations = true }

def authoringGSLT : DeclarationAuthoringGSLT MultiRewriteDecl :=
  multiRewriteCodec.compositionalElaboration

def documentGSLT : GSLT :=
  authoringGSLT.authoring.theory

private def elaborateLibrary? (_language : LanguageDef)
    (source : DeclarationDocument MultiRewriteSyntax) :
    Option AdmittedLibrary :=
  let declarations := multiRewriteCodec.elaborate source
  if admitted : LibraryAdmissible declarations = true then
    some ⟨declarations, admitted⟩
  else
    none

private def quoteLibrary (_language : LanguageDef)
    (library : AdmittedLibrary) :
    DeclarationDocument MultiRewriteSyntax :=
  multiRewriteCodec.quote library.1

/-- Multi-argument rewrites form a coGSLT-authored dependent layer over the
five-field term language.  The fibre does not depend on the base sorts: any
language may attach interaction rules on its patterns. -/
def layer : CoGSLTLayer LanguageDef where
  Fiber := fun _ => AdmittedLibrary
  sourceGSLT := fun _ => documentGSLT
  elaborate := elaborateLibrary?
  quote := quoteLibrary
  elaborate_quote := by
    intro language library
    simp [quoteLibrary, elaborateLibrary?,
      ExactDeclarationCodec.elaborate_quote, library.2]
  elaborate_equation := by
    intro language source target equal
    unfold elaborateLibrary?
    rw [multiRewriteCodec.elaborate_equation equal]
  elaborate_rewrite := by
    intro language source target impossible
    exact False.elim impossible

@[simp] theorem erase_attach (language : LanguageDef)
    (library : AdmittedLibrary) :
    layer.erase (layer.attach language library) = language :=
  rfl

/-! ## Denotation: one kernel GSLT -/

/-- Unary LanguageDef rewrites as singleton multi-rules, plus authored
n-ary windows.  Side-condition `RewriteRule.premises` stay the engine's
job; they are not packed into this window. -/
def denotedTheory (language : LanguageDef)
    (library : AdmittedLibrary) : MultiRewriteTheory where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun sources targets =>
    (∃ rule ∈ language.rewrites, sources = [rule.left] ∧ targets = [rule.right]) ∨
      (∃ decl ∈ library.1, sources = decl.sources ∧ targets = decl.targets)
  rewrites_resp_left := by
    intro sources sources' targets equiv rule
    have hsrc : sources' = sources := (Pointwise.eq_of_eq equiv).symm
    subst hsrc
    exact ⟨targets, rule, Pointwise.refl (fun _ => rfl) targets⟩
  rewrites_resp_right := by
    intro sources targets targets' rule equiv
    have htgt : targets' = targets := (Pointwise.eq_of_eq equiv).symm
    subst htgt
    exact rule

/-- The kernel GSLT authors run.  Unary and n-ary rules are both windows. -/
def denotedGSLT (language : LanguageDef) (library : AdmittedLibrary) : GSLT :=
  (denotedTheory language library).toGSLT

/-! ## Canaries -/

private def exampleLanguage : LanguageDef :=
  LanguageDef.empty "multi-rewrite-example"

private def commDecl : MultiRewriteDecl :=
  { name := "comm"
    sources := [.fvar "out", .fvar "inp"]
    targets := [.fvar "body"] }

private def commLibrary : AdmittedLibrary :=
  ⟨[commDecl], by decide⟩

example :
    layer.elaborate exampleLanguage
        (layer.quote exampleLanguage commLibrary) =
      some commLibrary :=
  layer.elaborate_quote exampleLanguage commLibrary

theorem empty_name_rejected :
    LibraryAdmissible
      [{ name := "", sources := [.fvar "a"], targets := [.fvar "b"] }] =
      false := by
  simp [LibraryAdmissible, MultiRewriteDecl.admissible]

/-- Positive: the authored 2→1 rule is a kernel step on a two-element
document. -/
theorem comm_is_a_kernel_step :
    (denotedGSLT exampleLanguage commLibrary).Step
      [.fvar "out", .fvar "inp"] [.fvar "body"] := by
  refine MultiRewriteTheory.step_of_binary
    (denotedTheory exampleLanguage commLibrary) ?_
  exact Or.inr ⟨commDecl, List.Mem.head [], rfl, rfl⟩

/-- Negative: that step is not a unary LanguageDef rewrite.  The object
language has no `rewrites` at all. -/
theorem comm_is_not_a_unary_language_rewrite :
    exampleLanguage.rewrites = [] :=
  rfl

theorem empty_window_rejected :
    LibraryAdmissible
      [{ name := "noop", sources := [], targets := [] }] = false := by
  simp [LibraryAdmissible, MultiRewriteDecl.admissible]

#print axioms comm_is_a_kernel_step
#print axioms erase_attach
#print axioms decode_encode

end Mettapedia.GSLT.LanguageDef.MultiRewriteExtension
