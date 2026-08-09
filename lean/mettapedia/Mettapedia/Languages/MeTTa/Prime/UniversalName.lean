import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubjectEquiv

/-!
# Universal structural names for Prime

This module separates three concerns:

* `Name` reifies arbitrary syntax without evaluating it.
* `PersistentName` records the additional closedness obligation required by
  stable runtime identities.
* `NamedTerm` is name-parametric syntax whose elaboration erases binders to
  de Bruijn indices.

The Prime definitions are independent of the rho-calculus definitions.  The
bridge at the end maps Prime syntax into rho patterns and proves the two
quote/drop directions using rho's existing subject equivalences.
-/

namespace Mettapedia.Languages.MeTTa.Prime.UniversalName

/-! ## Reified names and persistent-name admission -/

/-- A structural name is quoted syntax.  The payload type is deliberately
parametric: binding, matching, and resolution are distinct consumers of the
same name-forming operation. -/
structure Name (Expr : Type u) where
  quoted : Expr
deriving Repr, DecidableEq

namespace Name

/-- Reify syntax as inert name data. -/
def quote (expr : Expr) : Name Expr := ⟨expr⟩

/-- Release the syntax carried by a name. -/
def unquote (name : Name Expr) : Expr := name.quoted

@[simp] theorem unquote_quote (expr : Expr) : unquote (quote expr) = expr := rfl

@[simp] theorem quote_unquote (name : Name Expr) : quote (unquote name) = name := by
  cases name
  rfl

/-- Structural maps commute with quotation. -/
def map (f : Expr → Expr') (name : Name Expr) : Name Expr' := quote (f name.quoted)

@[simp] theorem unquote_map (f : Expr → Expr') (name : Name Expr) :
    unquote (map f name) = f (unquote name) := rfl

theorem map_injective (f : Expr → Expr') (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro left right h
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      simp only [map, quote, mk.injEq] at h ⊢
      exact hf h

end Name

/-- Syntax used by the first executable Prime name model.  `meta` represents
syntax containing a free matcher variable: it is quotable, but not a stable
persistent descriptor until closed. -/
inductive NameExpr where
  | symbol : String → NameExpr
  | string : String → NameExpr
  | natural : Nat → NameExpr
  | metavar : String → NameExpr
  | app : NameExpr → List NameExpr → NameExpr
deriving Repr

namespace NameExpr

mutual
  private def decEq : (left right : NameExpr) → Decidable (left = right)
    | .symbol left, .symbol right =>
        if h : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro eq; cases eq; exact h rfl)
    | .string left, .string right =>
        if h : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro eq; cases eq; exact h rfl)
    | .natural left, .natural right =>
        if h : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro eq; cases eq; exact h rfl)
    | .metavar left, .metavar right =>
        if h : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro eq; cases eq; exact h rfl)
    | .app leftHead leftArgs, .app rightHead rightArgs =>
        match decEq leftHead rightHead with
        | isFalse h => isFalse (by intro eq; cases eq; exact h rfl)
        | isTrue hHead =>
            match decEqList leftArgs rightArgs with
            | isFalse h => isFalse (by intro eq; cases eq; exact h rfl)
            | isTrue hArgs => isTrue (by cases hHead; cases hArgs; rfl)
    | .symbol _, .string _ => isFalse NameExpr.noConfusion
    | .symbol _, .natural _ => isFalse NameExpr.noConfusion
    | .symbol _, .metavar _ => isFalse NameExpr.noConfusion
    | .symbol _, .app _ _ => isFalse NameExpr.noConfusion
    | .string _, .symbol _ => isFalse NameExpr.noConfusion
    | .string _, .natural _ => isFalse NameExpr.noConfusion
    | .string _, .metavar _ => isFalse NameExpr.noConfusion
    | .string _, .app _ _ => isFalse NameExpr.noConfusion
    | .natural _, .symbol _ => isFalse NameExpr.noConfusion
    | .natural _, .string _ => isFalse NameExpr.noConfusion
    | .natural _, .metavar _ => isFalse NameExpr.noConfusion
    | .natural _, .app _ _ => isFalse NameExpr.noConfusion
    | .metavar _, .symbol _ => isFalse NameExpr.noConfusion
    | .metavar _, .string _ => isFalse NameExpr.noConfusion
    | .metavar _, .natural _ => isFalse NameExpr.noConfusion
    | .metavar _, .app _ _ => isFalse NameExpr.noConfusion
    | .app _ _, .symbol _ => isFalse NameExpr.noConfusion
    | .app _ _, .string _ => isFalse NameExpr.noConfusion
    | .app _ _, .natural _ => isFalse NameExpr.noConfusion
    | .app _ _, .metavar _ => isFalse NameExpr.noConfusion

  private def decEqList : (left right : List NameExpr) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | left :: leftRest, right :: rightRest =>
        match decEq left right with
        | isFalse h => isFalse (by intro eq; cases eq; exact h rfl)
        | isTrue hHead =>
            match decEqList leftRest rightRest with
            | isFalse h => isFalse (by intro eq; cases eq; exact h rfl)
            | isTrue hTail => isTrue (by cases hHead; cases hTail; rfl)
end

instance : DecidableEq NameExpr := decEq

mutual
  /-- Closed syntax has no free matcher variables. -/
  def closed : NameExpr → Bool
    | .symbol _ => true
    | .string _ => true
    | .natural _ => true
    | .metavar _ => false
    | .app head args => closed head && closedList args

  def closedList : List NameExpr → Bool
    | [] => true
    | expr :: rest => closed expr && closedList rest
end

end NameExpr

abbrev PrimeName := Name NameExpr

/-- A persistent name is a structural name plus checked closedness.  This is
the boundary required by spaces, agents, and distributed descriptors; plain
quoted names remain available to lexical consumers. -/
structure PersistentName where
  name : PrimeName
  closed : NameExpr.closed name.quoted = true
deriving Repr

namespace PersistentName

def recognize (name : PrimeName) : Option PersistentName :=
  if h : NameExpr.closed name.quoted = true then some ⟨name, h⟩ else none

@[simp] theorem recognize_closed {name : PrimeName}
    (h : NameExpr.closed name.quoted = true) : recognize name = some ⟨name, h⟩ := by
  simp [recognize, h]

@[simp] theorem recognize_open {name : PrimeName}
    (h : NameExpr.closed name.quoted = false) : recognize name = none := by
  simp [recognize, h]

end PersistentName

/-! ## Name-parametric ABT syntax -/

/-- A small binding syntax sufficient to state the name-parametric
elaboration theorem.  The production signature-driven ABT supports more
constructors; all of them recurse through the same binder lookup. -/
inductive NamedTerm (N : Type u) where
  | atom : String → NamedTerm N
  | var : N → NamedTerm N
  | app : NamedTerm N → NamedTerm N → NamedTerm N
  | lam : N → NamedTerm N → NamedTerm N
deriving Repr, DecidableEq

/-- Canonical result of named elaboration.  Binder names are absent. -/
inductive CoreTerm where
  | atom : String → CoreTerm
  | bvar : Nat → CoreTerm
  | app : CoreTerm → CoreTerm → CoreTerm
  | lam : CoreTerm → CoreTerm
deriving Repr, DecidableEq

namespace NamedTerm

def mapNames (f : N → M) : NamedTerm N → NamedTerm M
  | .atom name => .atom name
  | .var name => .var (f name)
  | .app function argument => .app (mapNames f function) (mapNames f argument)
  | .lam binder body => .lam (f binder) (mapNames f body)

def lookupIndex [DecidableEq N] (needle : N) : List N → Option Nat
  | [] => none
  | candidate :: rest =>
      if needle = candidate then some 0 else (lookupIndex needle rest).map Nat.succ

def elaborate [DecidableEq N] (environment : List N) : NamedTerm N → Option CoreTerm
  | .atom name => some (.atom name)
  | .var name => (lookupIndex name environment).map CoreTerm.bvar
  | .app function argument => do
      let function' ← elaborate environment function
      let argument' ← elaborate environment argument
      pure (.app function' argument')
  | .lam binder body => do
      let body' ← elaborate (binder :: environment) body
      pure (.lam body')

theorem lookupIndex_map_of_injective [DecidableEq N] [DecidableEq M]
    (f : N → M) (hf : Function.Injective f) (needle : N) (environment : List N) :
    lookupIndex (f needle) (environment.map f) = lookupIndex needle environment := by
  induction environment with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [List.map_cons, lookupIndex]
    by_cases h : needle = candidate
    · subst candidate
      simp
    · have hmap : f needle ≠ f candidate := fun eq => h (hf eq)
      simp [h, hmap, ih]

/-- Elaboration is parametric in the name representation.  Injectively
renaming every binder and occurrence cannot change the canonical de Bruijn
term. -/
theorem elaborate_map_of_injective [DecidableEq N] [DecidableEq M]
    (f : N → M) (hf : Function.Injective f)
    (environment : List N) (term : NamedTerm N) :
    elaborate (environment.map f) (mapNames f term) = elaborate environment term := by
  induction term generalizing environment with
  | atom name => rfl
  | var name =>
      simp only [mapNames, elaborate, lookupIndex_map_of_injective f hf]
  | app function argument ihFunction ihArgument =>
      simp only [mapNames, elaborate, ihFunction, ihArgument]
  | lam binder body ih =>
      simp only [mapNames, elaborate]
      have hbody := ih (binder :: environment)
      simp only [List.map_cons] at hbody
      rw [hbody]

@[simp] theorem elaborate_identity [DecidableEq N] (name : N) :
    elaborate [] (.lam name (.var name)) = some (.lam (.bvar 0)) := by
  simp [elaborate, lookupIndex]

@[simp] theorem elaborate_shadow [DecidableEq N] (outer inner : N) :
    elaborate [] (.lam outer (.lam inner (.var inner))) =
      some (.lam (.lam (.bvar 0))) := by
  simp [elaborate, lookupIndex]

theorem elaborate_outer_under_inner [DecidableEq N] {outer inner : N}
    (hne : outer ≠ inner) :
    elaborate [] (.lam outer (.lam inner (.var outer))) =
      some (.lam (.lam (.bvar 1))) := by
  simp [elaborate, lookupIndex, hne]

/-- Canonical naming of an elaborated ABT is defined only after the named
syntax has successfully erased to de Bruijn form. -/
def canonicalName? [DecidableEq N] (term : NamedTerm N) : Option (Name CoreTerm) :=
  (elaborate [] term).map Name.quote

/-- Injectively changing the representation of every source name cannot
change the structural name of the resulting canonical ABT. -/
theorem canonicalName_map_of_injective [DecidableEq N] [DecidableEq M]
    (f : N → M) (hf : Function.Injective f) (term : NamedTerm N) :
    canonicalName? (mapNames f term) = canonicalName? term := by
  unfold canonicalName?
  have h := elaborate_map_of_injective f hf ([] : List N) term
  simp only [List.map_nil] at h
  rw [h]

end NamedTerm

/-! ## Quotation opacity -/

/-- A minimal host syntax used to state the outer-substitution boundary.
Quoted payloads are names, not recursively substitutable host terms. -/
inductive StagedTerm where
  | free : String → StagedTerm
  | app : StagedTerm → StagedTerm → StagedTerm
  | quoted : PrimeName → StagedTerm
deriving Repr, DecidableEq

namespace StagedTerm

/-- Capture-free substitution in the host stage.  It deliberately stops at a
quoted name. -/
def substitute (target : String) (replacement : StagedTerm) : StagedTerm → StagedTerm
  | .free name => if name = target then replacement else .free name
  | .app function argument =>
      .app (substitute target replacement function)
           (substitute target replacement argument)
  | .quoted name => .quoted name

@[simp] theorem substitute_quoted
    (target : String) (replacement : StagedTerm) (name : PrimeName) :
    substitute target replacement (.quoted name) = .quoted name := rfl

example :
    substitute "x" (.free "replacement")
      (.app (.free "x") (.quoted (Name.quote (.symbol "x")))) =
    .app (.free "replacement") (.quoted (Name.quote (.symbol "x"))) := by
  decide

end StagedTerm

/-! ## Independent rho correspondence -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

mutual
  /-- Encode Prime name syntax as rho pattern data.  This is an explicit
  translation between independently defined syntaxes. -/
  def NameExpr.toRhoPattern : NameExpr → Pattern
    | .symbol value => .apply "PrimeSymbol" [.apply value []]
    | .string value => .apply "PrimeString" [.apply value []]
    | .natural value => .apply "PrimeNat" [.apply (toString value) []]
    | .metavar value => .apply "PrimeMeta" [.apply value []]
    | .app head args => .apply "PrimeApp" (toRhoPattern head :: toRhoPatterns args)

  def NameExpr.toRhoPatterns : List NameExpr → List Pattern
    | [] => []
    | expr :: rest => toRhoPattern expr :: toRhoPatterns rest
end

/-- Translate a Prime name to the rho name constructor. -/
def primeNameToRho (name : PrimeName) : Pattern :=
  .apply "NQuote" [NameExpr.toRhoPattern name.quoted]

/-- Prime unquotation corresponds to rho's independently defined
drop-of-quote process residual. -/
theorem rho_drop_of_prime_quote (expr : NameExpr) :
    ProcResidualEquiv
      (.apply "PDrop" [primeNameToRho (Name.quote expr)])
      expr.toRhoPattern := by
  exact ProcResidualEquiv.unquote expr.toRhoPattern

/-- Re-quoting a rho drop is name-equivalent to the original translated Prime
name. -/
theorem rho_quote_of_drop_prime_name (name : PrimeName) :
    NameEquiv
      (.apply "NQuote" [.apply "PDrop" [primeNameToRho name]])
      (primeNameToRho name) := by
  exact NameEquiv.quote_drop (primeNameToRho name)

/-! ## Executable witnesses -/

def mmPh : PrimeName := Name.quote (.app (.symbol "mm-var") [.string "ph"])
def mmPsi : PrimeName := Name.quote (.app (.symbol "mm-var") [.string "ps"])

example : (PersistentName.recognize mmPh).isSome = true := by decide
example : PersistentName.recognize (Name.quote (.metavar "open")) = none := by decide

example :
    NamedTerm.elaborate []
      (NamedTerm.lam mmPh (NamedTerm.app (NamedTerm.atom "wff") (NamedTerm.var mmPh))) =
      some (CoreTerm.lam (CoreTerm.app (CoreTerm.atom "wff") (CoreTerm.bvar 0))) := by
  decide

example :
    NamedTerm.elaborate []
      (NamedTerm.lam mmPh (NamedTerm.lam mmPsi (NamedTerm.var mmPh))) =
      some (CoreTerm.lam (CoreTerm.lam (CoreTerm.bvar 1))) := by
  decide

example :
    NamedTerm.canonicalName?
        (NamedTerm.lam mmPh (NamedTerm.var mmPh)) =
      NamedTerm.canonicalName?
        (NamedTerm.lam mmPsi (NamedTerm.var mmPsi)) := by
  decide

end Mettapedia.Languages.MeTTa.Prime.UniversalName
