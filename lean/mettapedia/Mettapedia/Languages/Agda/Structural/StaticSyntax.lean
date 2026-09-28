import Mettapedia.Languages.Agda.Structural.ContextGeometryCwf
import Mettapedia.GSLT.Core.ContextualJudgments

/-!
# Parameters for finite-universe Pi rules over structural syntax

The parameters below select finite Set annotations and binding/nonbinding
bodies from the existing structural signature. They are parameters of static
rules, not a replacement syntax or an evaluator. Their variable actions use
the generic binding operations. A parameter need not be formed or typed.

The supported source constructors are the relevant Pi fragment of Agda 2.8.0.2
(`Agda.Syntax.Internal`, `Abs`, `El`, `Pi`, `Lam`) and Cockx's Agda Core
(`Syntax.agda`, `TApp`/`EArg`). Universe levels here are closed natural numbers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Core.ContextualLadder

abbrev RawTm := ContextGeometry.RawTm
abbrev RawTy := ContextGeometry.RawTy
abbrev RawContext := ContextGeometry.RawContext
abbrev RawSub := ContextGeometry.RawSub

/-- A finite annotation and a raw type-denoting term, used in rule parameters. -/
structure TypeParameter (n : Nat) where
  level : Nat
  term : RawTm n

def TypeParameter.code {n : Nat} (A : TypeParameter n) : RawTy n :=
  el (set (levelClosed A.level)) A.term

def universeTerm {n : Nat} (level : Nat) : RawTm n :=
  sortTerm (set (levelClosed level))

def universeType (n level : Nat) : TypeParameter n := ⟨level + 1, universeTerm level⟩

def TypeParameter.substitute {n m : Nat} (A : TypeParameter n) (σ : RawSub n m) :
    TypeParameter m := ⟨A.level, bind σ A.term⟩

@[simp] theorem TypeParameter.code_substitute {n m : Nat}
    (A : TypeParameter n) (σ : RawSub n m) :
    (A.substitute σ).code = bind σ A.code := rfl

def TypeParameter.weaken {n : Nat} (A : TypeParameter n) : TypeParameter (n + 1) :=
  A.substitute (Telescope.projection (S := sig) .term n)

/-- A rule may refer to either Agda abstraction form, retaining its actual scope. -/
inductive TermBody (n : Nat) where
  | bind (body : RawTm (n + 1))
  | noBind (body : RawTm n)

inductive TypeBody (n : Nat) where
  | bind (body : TypeParameter (n + 1))
  | noBind (body : TypeParameter n)

def TermBody.open {n : Nat} : TermBody n → RawTm (n + 1)
  | .bind body => body
  | .noBind body => Mettapedia.OSLF.Binding.bind (Telescope.projection (S := sig) .term n) body

def TypeBody.open {n : Nat} : TypeBody n → TypeParameter (n + 1)
  | .bind body => body
  | .noBind body => body.weaken

def TypeBody.level {n : Nat} : TypeBody n → Nat
  | .bind body => body.level
  | .noBind body => body.level

def TermBody.lambda {n : Nat} : TermBody n → RawTm n
  | .bind body => lam body
  | .noBind body => lamNoAbs body

def TypeBody.pi {n : Nat} (A : TypeParameter n) : TypeBody n → RawTm n
  | .bind body => Structural.pi A.code body.code
  | .noBind body => Structural.piNoAbs A.code body.code

def piType {n : Nat} (A : TypeParameter n) (B : TypeBody n) : TypeParameter n :=
  ⟨max A.level B.level, B.pi A⟩

/-- One ordinary elimination; no computation occurs while constructing syntax. -/
def app {n : Nat} (function argument : RawTm n) : RawTm n :=
  eliminate function (cons (apply argument) nil)

def single {n : Nat} (argument : RawTm n) : RawSub (n + 1) n :=
  Telescope.pair (Telescope.identity (S := sig) .term n) argument

def TermBody.instantiate {n : Nat} (body : TermBody n) (argument : RawTm n) : RawTm n :=
  Mettapedia.OSLF.Binding.bind (single argument) body.open

def TypeBody.instantiate {n : Nat} (body : TypeBody n) (argument : RawTm n) : TypeParameter n :=
  body.open.substitute (single argument)

@[simp] theorem TermBody.instantiate_noBind {n : Nat} (body argument : RawTm n) :
    (TermBody.noBind body).instantiate argument = body := by
  change Mettapedia.OSLF.Binding.bind (single argument)
    (Mettapedia.OSLF.Binding.bind (Telescope.projection (S := sig) .term n) body) = body
  exact (congrArg (fun t : RawTm (n + 1) => Mettapedia.OSLF.Binding.bind (single argument) t)
    (Telescope.bind_projection (S := sig) (b := .term) body)).trans
    ((Telescope.bind_pair_weaken (Telescope.identity (S := sig) .term n) argument body).trans
      (Telescope.bind_identity body))

@[simp] theorem TypeBody.instantiate_noBind {n : Nat}
    (body : TypeParameter n) (argument : RawTm n) :
    (TypeBody.noBind body).instantiate argument = body := by
  cases body with
  | mk level term =>
    change TypeParameter.mk level _ = TypeParameter.mk level term
    apply congrArg (TypeParameter.mk level)
    change Mettapedia.OSLF.Binding.bind (single argument)
      (Mettapedia.OSLF.Binding.bind (Telescope.projection (S := sig) .term n) term) = term
    exact (congrArg (fun t : RawTm (n + 1) => Mettapedia.OSLF.Binding.bind (single argument) t)
      (Telescope.bind_projection (S := sig) (b := .term) term)).trans
      ((Telescope.bind_pair_weaken (Telescope.identity (S := sig) .term n) argument term).trans
        (Telescope.bind_identity term))

abbrev rawCwf := ContextGeometry.rawAgdaTelescopeCwfWithTerminal.toCwf
abbrev Judgment := ContextualJudgment rawCwf

def context {n : Nat} (Γ : RawContext n) : Judgment := .context ⟨n, Γ⟩
def formed {n : Nat} (Γ : RawContext n) (A : RawTy n) : Judgment := .type ⟨n, Γ⟩ A
def typed {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n) : Judgment :=
  .term ⟨n, Γ⟩ A ⟨t⟩
def typeEqual {n : Nat} (Γ : RawContext n) (A B : RawTy n) : Judgment :=
  .typeEquality ⟨n, Γ⟩ A B
def termEqual {n : Nat} (Γ : RawContext n) (t u : RawTm n) (A : RawTy n) : Judgment :=
  .termEquality ⟨n, Γ⟩ A ⟨t⟩ ⟨u⟩

end Mettapedia.Languages.Agda.Structural.Statics
