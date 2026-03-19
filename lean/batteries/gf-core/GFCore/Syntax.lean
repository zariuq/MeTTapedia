/-
# GFCore.Syntax — Core types for the GF ↔ Lean AST bridge

Four-layer architecture:
  RawTerm       — wire format (JSON from GF runtime, untyped)
  CheckedExpr   — Lean-verified GF AST (typed against GrammarSig)
  RGLView       — readable semantic core (peeled RGL wrappers)
  Meaning       — semantic interpretation with grounding

Reference: GPT-5.4 Pro reviews, 2026-03-17 through 2026-03-19
-/

import Std.Data.HashMap

namespace GFCore

/-- Whether a GF function is primitive (fun), a data constructor, or def-defined. -/
inductive FunStatus where
  | primitive
  | constructor
  | defined
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A GF abstract function declaration: name, argument categories, result category. -/
structure FunDecl where
  name      : String
  argCats   : Array String
  resultCat : String
  status    : FunStatus := .primitive
  deriving Repr, BEq, Inhabited

instance : DecidableEq FunDecl := fun a b =>
  if h₁ : a.name = b.name then
    if h₂ : a.argCats = b.argCats then
      if h₃ : a.resultCat = b.resultCat then
        if h₄ : a.status = b.status then
          isTrue (by cases a; cases b; simp_all)
        else isFalse (by intro h; cases h; exact h₄ rfl)
      else isFalse (by intro h; cases h; exact h₃ rfl)
    else isFalse (by intro h; cases h; exact h₂ rfl)
  else isFalse (by intro h; cases h; exact h₁ rfl)

namespace FunDecl

/-- Number of arguments this function expects. -/
def arity (f : FunDecl) : Nat := f.argCats.size

end FunDecl

/-- A grammar signature: all categories and function declarations.
    Generated from GF's PGF JSON export. -/
structure GrammarSig where
  grammar    : String
  startCats  : Array String
  funs       : Std.HashMap String FunDecl
  sourceHash : String := ""
  deriving Repr, Inhabited

namespace GrammarSig

/-- Look up a function declaration by name. -/
def findFun? (sig : GrammarSig) (name : String) : Option FunDecl :=
  sig.funs.get? name

/-- All category names appearing as result categories. -/
def categories (sig : GrammarSig) : Array String :=
  let cats := sig.funs.fold (init := #[]) fun acc _ decl =>
    if acc.contains decl.resultCat then acc else acc.push decl.resultCat
  sig.funs.fold (init := cats) fun acc _ decl =>
    decl.argCats.foldl (fun a c => if a.contains c then a else a.push c) acc

end GrammarSig

/-- Raw term from GF runtime — the JSON wire format between GF and Lean.
    Renamed from RawTree; structurally identical but with clearer naming.
    Literal support (str/int/float/meta) will be added when needed via
    a separate GFLiteral type — not as additional constructors, due to
    Lean 4 nested inductive limitations with pattern matching. -/
inductive RawTerm where
  | app (funName : String) (catHint? : Option String) (args : Array RawTerm)
  deriving Repr, Inhabited

def RawTerm.leaf (funName : String) : RawTerm := .app funName none #[]

def RawTerm.mk (funName : String) (args : Array RawTerm) : RawTerm := .app funName none args

namespace RawTerm

def funName : RawTerm → String
  | .app f _ _ => f

def args : RawTerm → Array RawTerm
  | .app _ _ as => as

def catHint? : RawTerm → Option String
  | .app _ c _ => c

def isLeaf : RawTerm → Bool
  | .app _ _ as => as.isEmpty

end RawTerm

/-- A parse candidate from GF runtime: surface text + parsed tree + metadata. -/
structure ParseCandidate where
  language : String
  surface  : String
  prob?    : Option Float := none
  tree     : RawTerm

  deriving Repr, Inhabited

/-- A checked expression: GF abstract tree verified against a GrammarSig.
    Every node carries its resolved FunDecl, guaranteeing well-typedness. -/
inductive CheckedExpr where
  | node (decl : FunDecl) (args : Array CheckedExpr)
  deriving Repr

instance : Inhabited CheckedExpr :=
  ⟨.node default #[]⟩

namespace CheckedExpr

def decl : CheckedExpr → FunDecl
  | .node d _ => d

def args : CheckedExpr → Array CheckedExpr
  | .node _ as => as

/-- The result category of this expression. -/
def resultCat (e : CheckedExpr) : String := e.decl.resultCat

/-- The function name at the root. -/
def funName (e : CheckedExpr) : String := e.decl.name

/-- Is this a leaf (zero-argument function application)? -/
def isLeaf (e : CheckedExpr) : Bool := e.args.isEmpty

end CheckedExpr

/-- Errors that can occur when checking a RawTerm against a GrammarSig. -/
inductive CheckError where
  | unknownFun (name : String)
  | wrongArity (funName : String) (expected got : Nat)
  | catMismatch (funName : String) (argIndex : Nat) (expected got : String)
  | inconsistentCatHint (funName : String) (hint actual : String)
  deriving Repr, Inhabited

namespace CheckError

def toString : CheckError → String
  | .unknownFun n => s!"unknown function: {n}"
  | .wrongArity f e g => s!"{f}: expected {e} args, got {g}"
  | .catMismatch f i e g => s!"{f} arg {i}: expected cat {e}, got {g}"
  | .inconsistentCatHint f h a => s!"{f}: cat hint {h} ≠ actual {a}"

instance : ToString CheckError := ⟨CheckError.toString⟩

end CheckError

-- ============================================================
-- Analysis: processing results with provenance
-- ============================================================

/-- How a sentence was obtained for processing. -/
inductive Source where
  | direct
  | paraphrased (original : String) (confidence : Float)
  deriving Repr, Inhabited

/-- Classification of parse failures (4-bucket taxonomy). -/
inductive FailureClass where
  | unknownLexeme (token : String)
  | wrongFrame (token : String) (detail : String)
  | missingConstruction (description : String)
  | noise (description : String)
  deriving Repr, Inhabited

namespace FailureClass

def toString : FailureClass → String
  | .unknownLexeme t => s!"unknown lexeme: {t}"
  | .wrongFrame t d => s!"wrong frame for {t}: {d}"
  | .missingConstruction d => s!"missing construction: {d}"
  | .noise d => s!"noise/out-of-grammar: {d}"

instance : ToString FailureClass := ⟨FailureClass.toString⟩

end FailureClass

/-- Result of processing a sentence through the GF→Lean pipeline.
    Only `exact` results enter the proof path. -/
inductive Analysis where
  | exact (expr : CheckedExpr) (source : Source)
  | opaque (surface : String) (reason : FailureClass)
  deriving Repr

namespace Analysis

def isExact : Analysis → Bool
  | .exact .. => true
  | .opaque .. => false

def getExpr? : Analysis → Option CheckedExpr
  | .exact e _ => some e
  | .opaque .. => none

end Analysis

end GFCore
