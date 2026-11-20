import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextOperations

/-!
# A typed view of the interpreter's existing context stack data

This is ghost representation evidence for literal context frames. Each stack
maps to an existing ComputationSyntax.Context, and its code agrees with the
previous contextCode. It introduces neither a source term grammar nor a new
operational reduction relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextStack

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration
open ComputationSyntax

inductive Stack : Nat → Nat → Type
  | nil {n : Nat} : Stack n n
  | piDom {o n : Nat} (codomain : Tower.Tm (n + 1)) (rest : Stack o n) : Stack o n
  | piCod {o n : Nat} (domain : Tower.Tm n) (rest : Stack o n) : Stack o (n + 1)
  | sigmaDom {o n : Nat} (codomain : Tower.Tm (n + 1)) (rest : Stack o n) : Stack o n
  | sigmaCod {o n : Nat} (domain : Tower.Tm n) (rest : Stack o n) : Stack o (n + 1)
  | idType {o n : Nat} (left right : Tower.Tm n) (rest : Stack o n) : Stack o n
  | idLeft {o n : Nat} (carrier right : Tower.Tm n) (rest : Stack o n) : Stack o n
  | idRight {o n : Nat} (carrier left : Tower.Tm n) (rest : Stack o n) : Stack o n
  | lam {o n : Nat} (rest : Stack o n) : Stack o (n + 1)
  | appFun {o n : Nat} (argument : Tower.Tm n) (rest : Stack o n) : Stack o n
  | appArg {o n : Nat} (function : Tower.Tm n) (rest : Stack o n) : Stack o n
  | pairFst {o n : Nat} (second : Tower.Tm n) (rest : Stack o n) : Stack o n
  | pairSnd {o n : Nat} (first : Tower.Tm n) (rest : Stack o n) : Stack o n
  | fst {o n : Nat} (rest : Stack o n) : Stack o n
  | snd {o n : Nat} (rest : Stack o n) : Stack o n
  | refl {o n : Nat} (rest : Stack o n) : Stack o n

def context : {o n : Nat} → Stack o n → Context Tower.Head o n
  | _, _, .nil => .hole
  | _, _, .piDom codomain rest => ContextOperations.append (context rest) (.piDom .hole codomain)
  | _, _, .piCod domain rest => ContextOperations.append (context rest) (.piCod domain .hole)
  | _, _, .sigmaDom codomain rest => ContextOperations.append (context rest) (.sigmaDom .hole codomain)
  | _, _, .sigmaCod domain rest => ContextOperations.append (context rest) (.sigmaCod domain .hole)
  | _, _, .idType left right rest => ContextOperations.append (context rest) (.idType .hole left right)
  | _, _, .idLeft carrier right rest => ContextOperations.append (context rest) (.idLeft carrier .hole right)
  | _, _, .idRight carrier left rest => ContextOperations.append (context rest) (.idRight carrier left .hole)
  | _, _, .lam rest => ContextOperations.append (context rest) (.lam .hole)
  | _, _, .appFun argument rest => ContextOperations.append (context rest) (.appFun .hole argument)
  | _, _, .appArg function rest => ContextOperations.append (context rest) (.appArg function .hole)
  | _, _, .pairFst second rest => ContextOperations.append (context rest) (.pairFst .hole second)
  | _, _, .pairSnd first rest => ContextOperations.append (context rest) (.pairSnd first .hole)
  | _, _, .fst rest => ContextOperations.append (context rest) (.fst .hole)
  | _, _, .snd rest => ContextOperations.append (context rest) (.snd .hole)
  | _, _, .refl rest => ContextOperations.append (context rest) (.refl .hole)

def plug {o n : Nat} (stack : Stack o n) (term : Tower.Tm n) : Tower.Tm o := (context stack).plug term

def code : {o n : Nat} → Stack o n → MClosed
  | _, _, .nil => emptyContext
  | _, _, .piDom codomain rest => nodeC "hd-context-pi-domain" [encodeTm codomain, code rest]
  | _, _, .piCod domain rest => nodeC "hd-context-pi-codomain" [encodeTm domain, code rest]
  | _, _, .sigmaDom codomain rest => nodeC "hd-context-sigma-domain" [encodeTm codomain, code rest]
  | _, _, .sigmaCod domain rest => nodeC "hd-context-sigma-codomain" [encodeTm domain, code rest]
  | _, _, .idType left right rest => nodeC "hd-context-id-type" [encodeTm left, encodeTm right, code rest]
  | _, _, .idLeft carrier right rest => nodeC "hd-context-id-left" [encodeTm carrier, encodeTm right, code rest]
  | _, _, .idRight carrier left rest => nodeC "hd-context-id-right" [encodeTm carrier, encodeTm left, code rest]
  | _, _, .lam rest => nodeC "hd-context-lam" [code rest]
  | _, _, .appFun argument rest => nodeC "hd-context-app-function" [encodeTm argument, code rest]
  | _, _, .appArg function rest => nodeC "hd-context-app-argument" [encodeTm function, code rest]
  | _, _, .pairFst second rest => nodeC "hd-context-pair-first" [encodeTm second, code rest]
  | _, _, .pairSnd first rest => nodeC "hd-context-pair-second" [encodeTm first, code rest]
  | _, _, .fst rest => nodeC "hd-context-first" [code rest]
  | _, _, .snd rest => nodeC "hd-context-second" [code rest]
  | _, _, .refl rest => nodeC "hd-context-refl" [code rest]

theorem code_context {o n : Nat} (stack : Stack o n) : contextCode (context stack) emptyContext = code stack := by
  induction stack <;> simp_all only [context, ContextOperations.code_append, contextCode, code]

def prepend : {o n m : Nat} → Context Tower.Head n m → Stack o n → Stack o m
  | _, _, _, .hole, rest => rest
  | _, _, _, .piDom inner codomain, rest => prepend inner (.piDom codomain rest)
  | _, _, _, .piCod domain inner, rest => prepend inner (.piCod domain rest)
  | _, _, _, .sigmaDom inner codomain, rest => prepend inner (.sigmaDom codomain rest)
  | _, _, _, .sigmaCod domain inner, rest => prepend inner (.sigmaCod domain rest)
  | _, _, _, .idType inner left right, rest => prepend inner (.idType left right rest)
  | _, _, _, .idLeft carrier inner right, rest => prepend inner (.idLeft carrier right rest)
  | _, _, _, .idRight carrier left inner, rest => prepend inner (.idRight carrier left rest)
  | _, _, _, .lam inner, rest => prepend inner (.lam rest)
  | _, _, _, .appFun inner argument, rest => prepend inner (.appFun argument rest)
  | _, _, _, .appArg function inner, rest => prepend inner (.appArg function rest)
  | _, _, _, .pairFst inner second, rest => prepend inner (.pairFst second rest)
  | _, _, _, .pairSnd first inner, rest => prepend inner (.pairSnd first rest)
  | _, _, _, .fst inner, rest => prepend inner (.fst rest)
  | _, _, _, .snd inner, rest => prepend inner (.snd rest)
  | _, _, _, .refl inner, rest => prepend inner (.refl rest)

theorem prepend_code {o n m : Nat} (inner : Context Tower.Head n m) (rest : Stack o n) :
    code (prepend inner rest) = contextCode inner (code rest) := by
  induction inner generalizing o <;> simp_all only [prepend, code, contextCode]

theorem prepend_plug {o n m : Nat} (inner : Context Tower.Head n m) (rest : Stack o n)
    (term : Tower.Tm m) : plug (prepend inner rest) term = plug rest (inner.plug term) := by
  induction inner generalizing o <;>
    simp_all only [prepend, plug, context, ContextOperations.plug_append, Context.plug]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextStack
