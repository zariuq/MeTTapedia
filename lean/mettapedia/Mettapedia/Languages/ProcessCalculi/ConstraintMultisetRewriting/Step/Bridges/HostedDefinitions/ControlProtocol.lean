import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Encoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HeadSeparation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSyntax

/-!
# Literal control and continuation data of the hosted definition interpreter

Native terms remain quoted payloads. Control phases are entered only through
explicit calls of the fixed program. The done head identifies a final protocol
result; the value invariant is proved by operation correspondence, not by this
constructor alone. These tags do not impose authority on arbitrary extensions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open SourceLanguage.Elaboration

abbrev activeTag : String := "hd-active"
abbrev doneTag : String := "hd-done"

def listC : List MClosed → MClosed
  | [] => nodeC "prime-list-nil" []
  | first :: rest => nodeC "prime-list-cons" [first, listC rest]

def environmentC (values : List (Presentation.NativeSyntax.Raw Presentation.Tower.Head)) : MClosed :=
  listC (values.map quoteRaw)

def activeC (phase : String) (arguments : List MClosed) : MClosed := nodeC activeTag [nodeC phase arguments]
def resumeC (value continuation : MClosed) : MClosed := activeC "hd-resume" [value, continuation]
def doneC (value : MClosed) : MClosed := nodeC doneTag [value]

def shiftC (amount cutoff : Nat) (term continuation : MClosed) : MClosed :=
  activeC "hd-shift" [encodeNat amount, encodeNat cutoff, term, continuation]

def substituteZeroC (argument : MClosed) (depth : Nat) (body continuation : MClosed) : MClosed :=
  activeC "hd-subst-zero" [argument, encodeNat depth, body, continuation]

def substituteEnvironmentC (environment body continuation : MClosed) : MClosed :=
  activeC "hd-subst-env" [environment, body, continuation]

def emptyContext : MClosed := nodeC "hd-context-empty" []
def finishContinuation : MClosed := nodeC "hd-main-finish" []
def evaluateC (term continuation : MClosed) : MClosed := activeC "hd-eval" [term, continuation]
def seekC (term context continuation : MClosed) : MClosed := activeC "hd-seek" [term, context, continuation]
def plugC (term context continuation : MClosed) : MClosed := activeC "hd-plug" [term, context, continuation]
def rootC (term continuation : MClosed) : MClosed := activeC "hd-root" [term, continuation]
def valueC (term continuation : MClosed) : MClosed := activeC "hd-value" [term, continuation]

def queryCode (term : Presentation.Tower.Tm 0) : MClosed := evaluateC (encodeTm term) finishContinuation

/-- The existing intrinsically scoped context, represented with its innermost
frame first. No new reduction contexts are introduced. -/
def contextCode : {outer inner : Nat} → ComputationSyntax.Context Presentation.Tower.Head outer inner →
    MClosed → MClosed
  | _, _, .hole, rest => rest
  | _, _, .piDom inner codomain, rest => contextCode inner (nodeC "hd-context-pi-domain" [encodeTm codomain, rest])
  | _, _, .piCod domain inner, rest => contextCode inner (nodeC "hd-context-pi-codomain" [encodeTm domain, rest])
  | _, _, .sigmaDom inner codomain, rest => contextCode inner (nodeC "hd-context-sigma-domain" [encodeTm codomain, rest])
  | _, _, .sigmaCod domain inner, rest => contextCode inner (nodeC "hd-context-sigma-codomain" [encodeTm domain, rest])
  | _, _, .idType inner left right, rest => contextCode inner (nodeC "hd-context-id-type" [encodeTm left, encodeTm right, rest])
  | _, _, .idLeft carrier inner right, rest => contextCode inner (nodeC "hd-context-id-left" [encodeTm carrier, encodeTm right, rest])
  | _, _, .idRight carrier left inner, rest => contextCode inner (nodeC "hd-context-id-right" [encodeTm carrier, encodeTm left, rest])
  | _, _, .lam inner, rest => contextCode inner (nodeC "hd-context-lam" [rest])
  | _, _, .appFun inner argument, rest => contextCode inner (nodeC "hd-context-app-function" [encodeTm argument, rest])
  | _, _, .appArg function inner, rest => contextCode inner (nodeC "hd-context-app-argument" [encodeTm function, rest])
  | _, _, .pairFst inner second, rest => contextCode inner (nodeC "hd-context-pair-first" [encodeTm second, rest])
  | _, _, .pairSnd first inner, rest => contextCode inner (nodeC "hd-context-pair-second" [encodeTm first, rest])
  | _, _, .fst inner, rest => contextCode inner (nodeC "hd-context-first" [rest])
  | _, _, .snd inner, rest => contextCode inner (nodeC "hd-context-second" [rest])
  | _, _, .refl inner, rest => contextCode inner (nodeC "hd-context-refl" [rest])

theorem active_head (phase : String) (arguments : List MClosed) :
    closedHead (activeC phase arguments) = some activeTag := rfl

theorem done_head (value : MClosed) : closedHead (doneC value) = some doneTag := rfl

theorem active_done_distinct : activeTag ≠ doneTag := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
