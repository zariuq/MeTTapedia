import Mettapedia.OSLF.Syntax.ContextualRigidReflection
import Mettapedia.OSLF.Syntax.ContextualFamilyComposition
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# A higher-order source language with explicit holding and running: syntax

**Data** are the intrinsically scoped terms of a binding signature `S` (`Term`), at one ambient
context `Γ` of constants and one sort `star` of atoms. Object binders live inside data, so a datum may
be `(lam x. body)`; second-order unknowns may be applied to bound variables, `$F x`.

**Names** (unknowns) are keys of a *key system* with a list of scopes. A key belongs to a binder
*site* (an equation, a `let`, a by-need cell, a space creation) and carries its metavariable arity.
Running a binder site at scope `n` prefixes `n` to the scopes of that site's names (`openAt`); firing
an equation or using a stored row prefixes `n` to every name of the copy (`copyAt`). A fresh scope is
a counter, so the family of names never changes along a run.

**Computations** (`Comp`) are the core, with explicit forms:
* `ret t` returns the datum `t` as written (holding);
* `run t` runs the datum `t` as code, through the program's reading of text as code (`reflect`);
* `apply t` answers the datum `t` by the equations at its root, by two-way unification;
* `let_ s p c k` runs `c` and binds each answer to the pattern `p` (a shadowing arrow: `p`'s own names
  are those of site `s`, fresh at each run; a name of `p` from outside crosses);
* `choice`, `fail`; `query`, `add`, `remove` on spaces addressed by data, `new` for a fresh space;
* `check T c` asks the type discipline at every reading of each answer;
* `delay s x c k` and `force x`: a cell `x` whose computation `c` runs at its first demand and is
  shared afterwards (call by need), local to its alternative.

A **program** is a list of equations (each a site, a left-hand side datum and a right-hand side
computation) and a reading of text as code. Declarations, strategies and readings of unannotated
positions are not here: they are what an elaboration consults to produce these explicit forms
(`SourceLanguage.Elaboration`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

/-! ## Names -/

/-- A key system: binder keys, the binder site of each key, and each key's metavariable arity. -/
structure Keys (S : Signature) where
  Key : Type
  Site : Type
  site : Key → Site
  arity : Key → MetaArity S
  siteEq : DecidableEq Site

instance {S : Signature} (κ : Keys S) : DecidableEq κ.Site := κ.siteEq

variable {S : Signature}

/-- A name: a key and the scopes it was opened at, newest first. -/
structure Name (κ : Keys S) where
  scopes : List ℕ
  key : κ.Key

instance {κ : Keys S} [DecidableEq κ.Key] : DecidableEq (Name κ) := fun a b =>
  if h : a.scopes = b.scopes ∧ a.key = b.key then
    isTrue (by cases a; cases b; simp only at h; rw [h.1, h.2])
  else isFalse (by intro same; subst same; exact h ⟨rfl, rfl⟩)

/-- The declaration family of all names. -/
abbrev fam (κ : Keys S) : Name κ → MetaArity S := fun name => κ.arity name.key

/-- Data: binding terms of the top sort over the names. -/
abbrev Data (κ : Keys S) (Γ : Ctx S) (star : S.Srt) := Term (signature S (fam κ)) Γ star

/-- The name of a key at the empty scope list, as a datum (its parameters are its own projections). -/
def nameAt (κ : Keys S) (scopes : List ℕ) (key : κ.Key) :
    Term (signature S (fam κ)) (κ.arity key).1 (κ.arity key).2 :=
  generator (fam κ) ⟨scopes, key⟩

/-- Rename every name by changing its scopes; arities are kept. -/
def relabel (κ : Keys S) (scopes : Name κ → List ℕ) : Assignment (fam κ) (fam κ) :=
  fun name => generator (fam κ) ⟨scopes name, name.key⟩

/-- A fresh copy at scope `n`: every name gets `n` prefixed. -/
def copyAt (κ : Keys S) (n : ℕ) : Assignment (fam κ) (fam κ) :=
  relabel κ fun name => n :: name.scopes

/-- Opening the site `s` at scope `n`: the names of `s` get `n` prefixed, the others are kept. -/
def openAt (κ : Keys S) (s : κ.Site) (n : ℕ) : Assignment (fam κ) (fam κ) :=
  relabel κ fun name => if κ.site name.key = s then n :: name.scopes else name.scopes

/-! ## Computations -/

/-- The explicit core: holding (`ret`), running (`run`), calling (`apply`), arrows, choice, spaces,
checks and shared cells. `Ty` is the type language of the discipline asked by `check`. -/
inductive Comp (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) : Type where
  | ret (datum : Data κ Γ star)
  | apply (call : Data κ Γ star)
  | run (text : Data κ Γ star)
  | let_ (site : κ.Site) (pattern : Data κ Γ star) (bound body : Comp κ Γ star Ty)
  | choice (left right : Comp κ Γ star Ty)
  | fail
  | query (space pattern : Data κ Γ star) (body : Comp κ Γ star Ty)
  | add (space atom : Data κ Γ star) (body : Comp κ Γ star Ty)
  | remove (space atom : Data κ Γ star) (body : Comp κ Γ star Ty)
  | new (site : κ.Site) (handle : Data κ Γ star) (body : Comp κ Γ star Ty)
  | check (type : Ty) (body : Comp κ Γ star Ty)
  | delay (site : κ.Site) (cell : Data κ Γ star) (suspended body : Comp κ Γ star Ty)
  | force (cell : Data κ Γ star)

variable {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}

/-- Apply a map to every datum of a computation. -/
def Comp.mapData (f : Data κ Γ star → Data κ Γ star) : Comp κ Γ star Ty → Comp κ Γ star Ty
  | .ret t => .ret (f t)
  | .apply t => .apply (f t)
  | .run t => .run (f t)
  | .let_ s p c k => .let_ s (f p) (c.mapData f) (k.mapData f)
  | .choice c d => .choice (c.mapData f) (d.mapData f)
  | .fail => .fail
  | .query sp p k => .query (f sp) (f p) (k.mapData f)
  | .add sp t k => .add (f sp) (f t) (k.mapData f)
  | .remove sp t k => .remove (f sp) (f t) (k.mapData f)
  | .new s x k => .new s (f x) (k.mapData f)
  | .check T k => .check T (k.mapData f)
  | .delay s x c k => .delay s (f x) (c.mapData f) (k.mapData f)
  | .force x => .force (f x)

theorem Comp.mapData_id (c : Comp κ Γ star Ty) : c.mapData id = c := by
  induction c <;> simp_all [Comp.mapData]

theorem Comp.mapData_comp (f g : Data κ Γ star → Data κ Γ star) (c : Comp κ Γ star Ty) :
    (c.mapData f).mapData g = c.mapData (g ∘ f) := by
  induction c <;> simp_all [Comp.mapData]

/-- Instantiate every datum of a computation. -/
abbrev Comp.inst (σ : Assignment (fam κ) (fam κ)) (c : Comp κ Γ star Ty) : Comp κ Γ star Ty :=
  c.mapData (instantiate σ)

/-! ## Programs -/

/-- An equation `(= lhs rhs)` at its binder site: the left-hand side is a datum (a pattern), the
right-hand side a computation. -/
structure Equation (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  site : κ.Site
  lhs : Data κ Γ star
  rhs : Comp κ Γ star Ty

/-- A program: its equations, and the reading of text as code that `run` uses. -/
structure Program (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  equations : List (Equation κ Γ star Ty)
  reflect : Data κ Γ star → Comp κ Γ star Ty

/-- Programs compose by union of their equations; the reading of text is the left one's. -/
def Program.union (P Q : Program κ Γ star Ty) : Program κ Γ star Ty :=
  ⟨P.equations ++ Q.equations, P.reflect⟩

/-- The type discipline asked by `check`: a type language and what each type admits of a closed
reading. -/
structure Discipline (S : Signature) (Γ : Ctx S) (star : S.Srt) where
  Ty : Type
  admits : Ty → Term S Γ star → Prop

/-! ## Configurations -/

/-- An equation of the store: two data at the top sort. -/
abbrev Constraint (κ : Keys S) (Γ : Ctx S) (star : S.Srt) := Data κ Γ star × Data κ Γ star

/-- A stored row: the atom, and the store of the branch that added it (its own unknowns are renamed
apart at every use). -/
structure Row (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  atom : Data κ Γ star
  store : List (Constraint κ Γ star)

/-- Continuation frames. -/
inductive Frame (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) : Type where
  | bindTo (site : κ.Site) (pattern : Data κ Γ star) (body : Comp κ Γ star Ty)
  | checkAt (type : Ty)
  | memo (cell : Data κ Γ star)

/-- What a branch is doing. -/
inductive Focus (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) : Type where
  | eval (comp : Comp κ Γ star Ty)
  | value (datum : Data κ Γ star)
  | refused (datum : Data κ Γ star) (type : Ty)

/-- One alternative: its own store of equations, its focus, its frames, its pending shared cells. -/
structure Branch (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  store : List (Constraint κ Γ star)
  focus : Focus κ Γ star Ty
  frames : List (Frame κ Γ star Ty)
  pending : List (Data κ Γ star × Comp κ Γ star Ty)

/-- What every alternative shares: the scope counter, the handle counter, and the spaces, each a
bag of rows addressed by a closed datum. -/
structure World (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  scope : ℕ
  handles : ℕ
  spaces : Term S Γ star → Multiset (Row κ Γ star)

/-- A configuration: the shared world and the bag of alternatives. -/
structure Config (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  world : World κ Γ star
  branches : Multiset (Branch κ Γ star Ty)

/-- The initial configuration of a query over initial spaces. -/
def Config.initial (spaces : Term S Γ star → Multiset (Row κ Γ star)) (query : Comp κ Γ star Ty) :
    Config κ Γ star Ty :=
  ⟨⟨0, 0, spaces⟩, {⟨[], .eval query, [], []⟩}⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage
