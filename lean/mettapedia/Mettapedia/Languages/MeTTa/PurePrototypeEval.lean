import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
import Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

/-!
# MeTTa-Pure Prototype Evaluator

A small executable evaluator for the current closed Pure kernel fragment, plus a
tiny MeTTa-flavored parser/printer and proof-connected result packaging.

This module is intentionally narrow:

- closed terms only
- current Pure core only
- beta and sigma projection reduction
- proof-side artifact agreement always
- proof-side typing preservation when a typing proof is already available

It does **not** claim ordinary-family or fixpoint reduction.
-/

namespace Mettapedia.Languages.MeTTa.PurePrototypeEval

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

/-! ## Executable evaluator -/

/-- One executable reduction step for the current Pure kernel fragment. -/
def stepCert? : (t : PureTm n) -> Option { u : PureTm n // Red t u }
  | .var _ => none
  | .u0 => none
  | .u1 => none
  | .pi A B =>
      match stepCert? A with
      | some ⟨A', hA⟩ => some ⟨.pi A' B, .congPiDom hA⟩
      | none =>
          match stepCert? B with
          | some ⟨B', hB⟩ => some ⟨.pi A B', .congPiCod hB⟩
          | none => none
  | .sigma A B =>
      match stepCert? A with
      | some ⟨A', hA⟩ => some ⟨.sigma A' B, .congSigmaDom hA⟩
      | none =>
          match stepCert? B with
          | some ⟨B', hB⟩ => some ⟨.sigma A B', .congSigmaCod hB⟩
          | none => none
  | .id A a b =>
      match stepCert? A with
      | some ⟨A', hA⟩ => some ⟨.id A' a b, .congIdTy hA⟩
      | none =>
          match stepCert? a with
          | some ⟨a', ha⟩ => some ⟨.id A a' b, .congIdLeft ha⟩
          | none =>
              match stepCert? b with
              | some ⟨b', hb⟩ => some ⟨.id A a b', .congIdRight hb⟩
              | none => none
  | .lam body =>
      match stepCert? body with
      | some ⟨body', hbody⟩ => some ⟨.lam body', .congLam hbody⟩
      | none => none
  | .app (.lam body) a =>
      some ⟨inst0 a body, .betaPi body a⟩
  | .app f a =>
      match stepCert? f with
      | some ⟨f', hf⟩ => some ⟨.app f' a, .congAppFun hf⟩
      | none =>
          match stepCert? a with
          | some ⟨a', ha⟩ => some ⟨.app f a', .congAppArg ha⟩
          | none => none
  | .pair a b =>
      match stepCert? a with
      | some ⟨a', ha⟩ => some ⟨.pair a' b, .congPairFst ha⟩
      | none =>
          match stepCert? b with
          | some ⟨b', hb⟩ => some ⟨.pair a b', .congPairSnd hb⟩
          | none => none
  | .fst (.pair a b) =>
      some ⟨a, .betaSigmaFst a b⟩
  | .fst p =>
      match stepCert? p with
      | some ⟨p', hp⟩ => some ⟨.fst p', .congFst hp⟩
      | none => none
  | .snd (.pair a b) =>
      some ⟨b, .betaSigmaSnd a b⟩
  | .snd p =>
      match stepCert? p with
      | some ⟨p', hp⟩ => some ⟨.snd p', .congSnd hp⟩
      | none => none
  | .refl a =>
      match stepCert? a with
      | some ⟨a', ha⟩ => some ⟨.refl a', .congRefl ha⟩
      | none => none

def evalPureStep? (t : PureTm n) : Option (PureTm n) :=
  (stepCert? t).map (·.1)

def evalPureFuel : Nat -> PureTm n -> PureTm n
  | 0, t => t
  | fuel + 1, t =>
      match stepCert? t with
      | some ⟨u, _⟩ => evalPureFuel fuel u
      | none => t

theorem evalPureStep?_sound {t u : PureTm n}
    (h : evalPureStep? t = some u) :
    Red t u := by
  unfold evalPureStep? at h
  cases hstep : stepCert? t with
  | none =>
      simp [hstep] at h
  | some step =>
      simp [hstep] at h
      cases h
      exact step.2

theorem evalPureFuel_redStar :
    ∀ (fuel : Nat) (t : PureTm n), RedStar t (evalPureFuel fuel t)
  | 0, t => RedStar.refl t
  | fuel + 1, t =>
      match hstep : stepCert? t with
      | none => by
          simp [evalPureFuel, hstep]
          exact RedStar.refl t
      | some step => by
          have htail : RedStar step.1 (evalPureFuel fuel step.1) :=
            evalPureFuel_redStar fuel step.1
          have hhead : RedStar t step.1 := red_to_redStar step.2
          simpa [evalPureFuel, hstep] using RedStar.trans hhead htail

/-! ## Proof-connected run packaging -/

structure ExecutablePureRun where
  input : SurfacePureTm 0
  fuel : Nat
  normalForm : PureTm 0
  theoryReduction : RedStar input.toPureTm normalForm

def runSurfacePure (fuel : Nat) (input : SurfacePureTm 0) : ExecutablePureRun :=
  { input := input
    fuel := fuel
    normalForm := evalPureFuel fuel input.toPureTm
    theoryReduction := evalPureFuel_redStar fuel input.toPureTm }

def ExecutablePureRun.artifact (run : ExecutablePureRun) : SharedArtifact :=
  ⟨quoteClosedTm run.normalForm⟩

theorem ExecutablePureRun.quoteAgreement (run : ExecutablePureRun) :
    run.artifact.pattern = quoteClosedTm run.normalForm := rfl

theorem ExecutablePureRun.profileBridge (run : ExecutablePureRun) :
    PureProfileTheoryStepStar
      (quoteClosedTm run.input.toPureTm)
      (quoteClosedTm run.normalForm) := by
  exact pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed run.theoryReduction

theorem subjectReductionStar {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasType Γ t A) (hred : RedStar t u) :
    HasType Γ u A := by
  induction hred with
  | refl =>
      simpa using ht
  | tail hxy hyz ih =>
      exact subject_reduction ih hyz

def pureCertificateOfClosed (t : PureTm 0) : PureCertificate :=
  { term := t
    artifact := ⟨quoteClosedTm t⟩
    artifact_eq := rfl }

structure TypedExecutablePureRun where
  run : ExecutablePureRun
  claimedType : PureTm 0
  inputTyping : HasType .nil run.input.toPureTm claimedType

def TypedExecutablePureRun.outputTyping (run : TypedExecutablePureRun) :
    HasType .nil run.run.normalForm run.claimedType :=
  subjectReductionStar run.inputTyping run.run.theoryReduction

def TypedExecutablePureRun.checkedOutput (run : TypedExecutablePureRun) :
    CheckedPureCertificate :=
  checkImportedPureCertificate
    (.pure (pureCertificateOfClosed run.run.normalForm))
    run.claimedType
    run.outputTyping

theorem TypedExecutablePureRun.checkedOutput_quoteAgreement
    (run : TypedExecutablePureRun) :
    run.checkedOutput.artifact.pattern = quoteClosedTm run.run.normalForm := by
  simpa [TypedExecutablePureRun.checkedOutput, CheckedPureCertificate.term]
    using run.checkedOutput.quoteAgreement

/-! ## Tiny pretty surface AST -/

inductive PrettyPureTm where
  | var (name : String)
  | u0
  | u1
  | pi (dom : PrettyPureTm) (binder : String) (body : PrettyPureTm)
  | sigma (dom : PrettyPureTm) (binder : String) (body : PrettyPureTm)
  | id (A : PrettyPureTm) (a : PrettyPureTm) (b : PrettyPureTm)
  | lam (binder : String) (body : PrettyPureTm)
  | app (f : PrettyPureTm) (a : PrettyPureTm)
  | pair (a : PrettyPureTm) (b : PrettyPureTm)
  | fst (p : PrettyPureTm)
  | snd (p : PrettyPureTm)
  | refl (a : PrettyPureTm)
deriving DecidableEq, Repr

def lookupName : (env : List String) -> String -> Option (Fin env.length)
  | [], _ => none
  | x :: xs, name =>
      if x = name then
        some 0
      else
        match lookupName xs name with
        | some i => some i.succ
        | none => none

def PrettyPureTm.toSurface : (env : List String) -> PrettyPureTm -> Except String (SurfacePureTm env.length)
  | env, .var name =>
      match lookupName env name with
      | some i => pure (.var i)
      | none => throw s!"unbound variable `{name}`"
  | _, .u0 => pure .u0
  | _, .u1 => pure .u1
  | env, .pi dom binder body => do
      let dom' <- PrettyPureTm.toSurface env dom
      let body' <- PrettyPureTm.toSurface (binder :: env) body
      pure (.pi dom' body')
  | env, .sigma dom binder body => do
      let dom' <- PrettyPureTm.toSurface env dom
      let body' <- PrettyPureTm.toSurface (binder :: env) body
      pure (.sigma dom' body')
  | env, .id A a b => do
      pure (.id
        (<- PrettyPureTm.toSurface env A)
        (<- PrettyPureTm.toSurface env a)
        (<- PrettyPureTm.toSurface env b))
  | env, .lam binder body => do
      let body' <- PrettyPureTm.toSurface (binder :: env) body
      pure (.lam body')
  | env, .app f a => do
      pure (.app
        (<- PrettyPureTm.toSurface env f)
        (<- PrettyPureTm.toSurface env a))
  | env, .pair a b => do
      pure (.pair
        (<- PrettyPureTm.toSurface env a)
        (<- PrettyPureTm.toSurface env b))
  | env, .fst p => do
      pure (.fst (<- PrettyPureTm.toSurface env p))
  | env, .snd p => do
      pure (.snd (<- PrettyPureTm.toSurface env p))
  | env, .refl a => do
      pure (.refl (<- PrettyPureTm.toSurface env a))

def parseClosedPrettyPureToSurface (term : PrettyPureTm) : Except String (SurfacePureTm 0) :=
  PrettyPureTm.toSurface [] term

/-! ## Tiny tokenizer/parser -/

inductive Token where
  | lparen
  | rparen
  | lambda
  | arrow
  | ident (name : String)
deriving DecidableEq, Repr

private def flushIdent (chars : List Char) (tokensRev : List Token) : List Token :=
  if chars.isEmpty then
    tokensRev
  else
    Token.ident (String.ofList chars.reverse) :: tokensRev

private def isIdentChar (c : Char) : Bool :=
  !(c.isWhitespace || c = '(' || c = ')' || c = '\\')

private def tokenizeLoop :
    List Char -> List Char -> List Token -> Except String (List Token)
  | [], identRev, tokensRev =>
      pure (flushIdent identRev tokensRev).reverse
  | '=' :: '>' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.arrow :: flushIdent identRev tokensRev)
  | '(' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.lparen :: flushIdent identRev tokensRev)
  | ')' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.rparen :: flushIdent identRev tokensRev)
  | '\\' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.lambda :: flushIdent identRev tokensRev)
  | c :: cs, identRev, tokensRev =>
      if c.isWhitespace then
        tokenizeLoop cs [] (flushIdent identRev tokensRev)
      else if isIdentChar c then
        tokenizeLoop cs (c :: identRev) tokensRev
      else
        throw s!"unexpected character `{c}`"

def tokenize (input : String) : Except String (List Token) :=
  tokenizeLoop input.toList [] []

private def expectRParen : List Token -> Except String (List Token)
  | .rparen :: rest => pure rest
  | _ => throw "expected `)`"

mutual

partial def parsePrettyPure : List Token -> Except String (PrettyPureTm × List Token)
  | .ident "Type0" :: rest => pure (.u0, rest)
  | .ident "Type1" :: rest => pure (.u1, rest)
  | .ident name :: rest => pure (.var name, rest)
  | .lparen :: .ident "Type0" :: rest => do
      pure (.u0, <- expectRParen rest)
  | .lparen :: .ident "Type1" :: rest => do
      pure (.u1, <- expectRParen rest)
  | .lparen :: .ident "Pi" :: rest => do
      let (dom, rest) <- parsePrettyPure rest
      let (binder, body, rest) <- parseBinder rest
      pure (.pi dom binder body, <- expectRParen rest)
  | .lparen :: .ident "Sigma" :: rest => do
      let (dom, rest) <- parsePrettyPure rest
      let (binder, body, rest) <- parseBinder rest
      pure (.sigma dom binder body, <- expectRParen rest)
  | .lparen :: .ident "Id" :: rest => do
      let (A, rest) <- parsePrettyPure rest
      let (a, rest) <- parsePrettyPure rest
      let (b, rest) <- parsePrettyPure rest
      pure (.id A a b, <- expectRParen rest)
  | .lparen :: .ident "lam" :: rest => do
      let (binder, body, rest) <- parseBinder rest
      pure (.lam binder body, <- expectRParen rest)
  | .lparen :: .ident "app" :: rest => do
      let (f, rest) <- parsePrettyPure rest
      let (a, rest) <- parsePrettyPure rest
      pure (.app f a, <- expectRParen rest)
  | .lparen :: .ident "pair" :: rest => do
      let (a, rest) <- parsePrettyPure rest
      let (b, rest) <- parsePrettyPure rest
      pure (.pair a b, <- expectRParen rest)
  | .lparen :: .ident "fst" :: rest => do
      let (p, rest) <- parsePrettyPure rest
      pure (.fst p, <- expectRParen rest)
  | .lparen :: .ident "snd" :: rest => do
      let (p, rest) <- parsePrettyPure rest
      pure (.snd p, <- expectRParen rest)
  | .lparen :: .ident "refl" :: rest => do
      let (a, rest) <- parsePrettyPure rest
      pure (.refl a, <- expectRParen rest)
  | _ => throw "expected Pure expression"

partial def parseBinder :
    List Token -> Except String (String × PrettyPureTm × List Token)
  | .lparen :: .lambda :: .ident binder :: .arrow :: rest => do
      let (body, rest) <- parsePrettyPure rest
      pure (binder, body, <- expectRParen rest)
  | _ => throw "expected binder of the form `(\\ x => body)`"

end

def parseClosedPrettyPure (input : String) : Except String (PrettyPureTm × SurfacePureTm 0) := do
  let tokens <- tokenize input
  let (pretty, rest) <- parsePrettyPure tokens
  if rest.isEmpty then
    pure (pretty, <- parseClosedPrettyPureToSurface pretty)
  else
    throw s!"unexpected trailing tokens: {reprStr rest}"

/-! ## Pretty printer -/

def binderName (depth : Nat) : String :=
  s!"x{depth}"

def lookupBinderDisplay (env : List String) (i : Fin env.length) : String :=
  env.get i

def prettyWith : (env : List String) -> Nat -> PureTm env.length -> String
  | env, _, .var i => lookupBinderDisplay env i
  | _, _, .u0 => "(Type0)"
  | _, _, .u1 => "(Type1)"
  | env, depth, .pi A B =>
      let x := binderName depth
      s!"(Pi {prettyWith env depth A} (\\ {x} => {prettyWith (x :: env) (depth + 1) B}))"
  | env, depth, .sigma A B =>
      let x := binderName depth
      s!"(Sigma {prettyWith env depth A} (\\ {x} => {prettyWith (x :: env) (depth + 1) B}))"
  | env, depth, .id A a b =>
      s!"(Id {prettyWith env depth A} {prettyWith env depth a} {prettyWith env depth b})"
  | env, depth, .lam body =>
      let x := binderName depth
      s!"(lam (\\ {x} => {prettyWith (x :: env) (depth + 1) body}))"
  | env, depth, .app f a =>
      s!"(app {prettyWith env depth f} {prettyWith env depth a})"
  | env, depth, .pair a b =>
      s!"(pair {prettyWith env depth a} {prettyWith env depth b})"
  | env, depth, .fst p =>
      s!"(fst {prettyWith env depth p})"
  | env, depth, .snd p =>
      s!"(snd {prettyWith env depth p})"
  | env, depth, .refl a =>
      s!"(refl {prettyWith env depth a})"

def prettyClosed (t : PureTm 0) : String :=
  prettyWith [] 0 t

/-! ## Example runs with typing proofs -/

def universeIdSurface : SurfacePureTm 0 :=
  .app (.lam (.var 0)) .u0

theorem universeIdSurface_typing :
    HasType .nil universeIdSurface.toPureTm .u1 := by
  exact
    HasType.app_elim
      (HasType.lam_intro (HasType.var (Γ := .snoc .nil .u1) (i := 0)))
      (HasType.u0_type .nil)

def pairFstSurface : SurfacePureTm 0 :=
  .fst (.pair .u0 .u0)

theorem pairFstSurface_typing :
    HasType .nil pairFstSurface.toPureTm .u1 := by
  exact
    HasType.fst_elim (A := .u1) (B := .u1)
      (HasType.pair_intro
        (HasType.u0_type .nil)
        (HasType.u0_type .nil))

def pairSndSurface : SurfacePureTm 0 :=
  .snd (.pair .u0 .u0)

theorem pairSndSurface_typing :
    HasType .nil pairSndSurface.toPureTm .u1 := by
  exact
    HasType.snd_elim (A := .u1) (B := .u1)
      (HasType.pair_intro
        (HasType.u0_type .nil)
        (HasType.u0_type .nil))

def nestedSurface : SurfacePureTm 0 :=
  .fst (.pair (.app (.lam (.var 0)) .u0) .u0)

theorem nestedSurface_typing :
    HasType .nil nestedSurface.toPureTm .u1 := by
  exact
    HasType.fst_elim (A := .u1) (B := .u1)
      (HasType.pair_intro
        universeIdSurface_typing
        (HasType.u0_type .nil))

def typedUniverseIdRun : TypedExecutablePureRun :=
  { run := runSurfacePure 8 universeIdSurface
    claimedType := .u1
    inputTyping := universeIdSurface_typing }

def typedPairFstRun : TypedExecutablePureRun :=
  { run := runSurfacePure 8 pairFstSurface
    claimedType := .u1
    inputTyping := pairFstSurface_typing }

def typedPairSndRun : TypedExecutablePureRun :=
  { run := runSurfacePure 8 pairSndSurface
    claimedType := .u1
    inputTyping := pairSndSurface_typing }

theorem typedUniverseIdRun_normalForm :
    typedUniverseIdRun.run.normalForm = .u0 := rfl

theorem typedPairFstRun_normalForm :
    typedPairFstRun.run.normalForm = .u0 := rfl

theorem typedPairSndRun_normalForm :
    typedPairSndRun.run.normalForm = .u0 := rfl

theorem nestedSurface_normalizes_to_u0 :
    (runSurfacePure 16 nestedSurface).normalForm = .u0 := rfl

/-! ## CLI support -/

def defaultFuel : Nat := 64

def knownTypedRun? (fuel : Nat) (surface : SurfacePureTm 0) : Option TypedExecutablePureRun :=
  if h : surface = universeIdSurface then
    by
      subst h
      exact some
        { run := runSurfacePure fuel universeIdSurface
          claimedType := .u1
          inputTyping := universeIdSurface_typing }
  else if h : surface = pairFstSurface then
    by
      subst h
      exact some
        { run := runSurfacePure fuel pairFstSurface
          claimedType := .u1
          inputTyping := pairFstSurface_typing }
  else if h : surface = pairSndSurface then
    by
      subst h
      exact some
        { run := runSurfacePure fuel pairSndSurface
          claimedType := .u1
          inputTyping := pairSndSurface_typing }
  else if h : surface = nestedSurface then
    by
      subst h
      exact some
        { run := runSurfacePure fuel nestedSurface
          claimedType := .u1
          inputTyping := nestedSurface_typing }
  else
    none

private def formatArtifact (run : ExecutablePureRun) : String :=
  s!"{repr run.artifact.pattern}"

private def formatProofSummary (typed? : Option TypedExecutablePureRun) : List String :=
  let typingStatus :=
    match typed? with
    | some _ => "ok"
    | none => "not-checked"
  [ "proof: artifact-agreement=ok"
  , "proof: profile-bridge=ok"
  , s!"proof: closed-typing={typingStatus}"
  ]

def runPureEvalFile (path : System.FilePath) (fuel : Nat := defaultFuel) : IO UInt32 := do
  let input <- IO.FS.readFile path
  match parseClosedPrettyPure input with
  | .error err =>
      IO.eprintln s!"pure-eval parse error in {path}: {err}"
      pure 1
  | .ok (_pretty, surface) =>
      let run := runSurfacePure fuel surface
      let typed? := knownTypedRun? fuel surface
      IO.println s!"input: {prettyClosed surface.toPureTm}"
      IO.println s!"normalized: {prettyClosed run.normalForm}"
      IO.println s!"artifact: {formatArtifact run}"
      for line in formatProofSummary typed? do
        IO.println line
      pure 0

end Mettapedia.Languages.MeTTa.PurePrototypeEval
