import Mettapedia.OSLF.Syntax.BindingSignature
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Free raw terms for a many-sorted binding signature

The first, terms-only rung of a graph-structured presentation is initial
among context-indexed algebras of its declared binders and operators.
An algebra has a carrier at every sort and ambient context, an interpretation
of positional variables, and an operation on arguments in the contexts
extended by exactly the binder lists from the signature. There is one and only
one map from raw terms preserving these constructors.

This is the raw binding-syntax universal property. Equations, reductions,
semantic substitution, and cartesian closure require further structure and
are not consequences of this theorem alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FreeBindingTerms

universe u v w

variable {S : Signature}

/-- An operator's semantic arguments live in the contexts named by its
binding arity. This is a polynomial family, with no quotient or equation. -/
inductive FamilyArgs (S : Signature)
    (F : Ctx S → S.Srt → Type u) :
    List (List S.Srt × S.Srt) → Ctx S → Type u where
  | nil {Γ : Ctx S} : FamilyArgs S F [] Γ
  | cons {bs : List S.Srt} {s : S.Srt}
      {rest : List (List S.Srt × S.Srt)} {Γ : Ctx S} :
      F (bs ++ Γ) s → FamilyArgs S F rest Γ →
        FamilyArgs S F ((bs, s) :: rest) Γ

namespace FamilyArgs

def map {F : Ctx S → S.Srt → Type u}
    {G : Ctx S → S.Srt → Type v}
    (f : {Γ : Ctx S} → {s : S.Srt} → F Γ s → G Γ s) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FamilyArgs S F arity Γ → FamilyArgs S G arity Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (f head) (map f tail)

theorem map_id {F : Ctx S → S.Srt → Type u} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S F arity Γ),
      map (fun {Γ s} (x : F Γ s) => x) args = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg (cons head) (map_id tail)

theorem map_comp {F : Ctx S → S.Srt → Type u}
    {G : Ctx S → S.Srt → Type v}
    {H : Ctx S → S.Srt → Type w}
    (f : {Γ : Ctx S} → {s : S.Srt} → F Γ s → G Γ s)
    (g : {Γ : Ctx S} → {s : S.Srt} → G Γ s → H Γ s) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S F arity Γ),
      map g (map f args) = map (fun x => g (f x)) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg (cons (g (f head))) (map_comp f g tail)

end FamilyArgs

/-- A raw model of the signature's variable and binder constructors. -/
structure Algebra (S : Signature) where
  Carrier : Ctx S → S.Srt → Type u
  injectVar : {Γ : Ctx S} → {s : S.Srt} → Var Γ s → Carrier Γ s
  operation : {Γ : Ctx S} → {s : S.Srt} →
    (o : S.Op s) → FamilyArgs S Carrier (S.arity o) Γ → Carrier Γ s

/-- A map of raw binding algebras preserves variables and every declared
operator, including the contexts beneath each binder. -/
structure Hom (A : Algebra.{u} S) (B : Algebra.{v} S) where
  map : {Γ : Ctx S} → {s : S.Srt} → A.Carrier Γ s → B.Carrier Γ s
  map_variable : ∀ {Γ : Ctx S} {s : S.Srt} (x : Var Γ s),
    map (A.injectVar x) = B.injectVar x
  map_operation : ∀ {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : FamilyArgs S A.Carrier (S.arity o) Γ),
    map (A.operation o args) = B.operation o (FamilyArgs.map map args)

namespace Hom

@[ext] theorem ext {A : Algebra.{u} S} {B : Algebra.{v} S}
    {f g : Hom A B}
    (agree : ∀ {Γ : Ctx S} {s : S.Srt} (x : A.Carrier Γ s),
      f.map x = g.map x) : f = g := by
  cases f with
  | mk fm fv fo =>
      cases g with
      | mk gm gv go =>
          have maps_equal : @fm = @gm := by
            funext Γ s x
            exact agree x
          cases maps_equal
          rfl

end Hom

namespace Hom

def id (A : Algebra.{u} S) : Hom A A where
  map := fun x => x
  map_variable := by intro Γ s x; rfl
  map_operation := by
    intro Γ s o args
    rw [FamilyArgs.map_id]

def comp {A : Algebra.{u} S} {B : Algebra.{v} S} {C : Algebra.{w} S}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  map := fun x => g.map (f.map x)
  map_variable := by
    intro Γ s x
    rw [f.map_variable, g.map_variable]
  map_operation := by
    intro Γ s o args
    calc
      g.map (f.map (A.operation o args)) =
          g.map (B.operation o (FamilyArgs.map f.map args)) := by
            rw [f.map_operation]
      _ = C.operation o (FamilyArgs.map g.map (FamilyArgs.map f.map args)) :=
        g.map_operation o (FamilyArgs.map f.map args)
      _ = C.operation o (FamilyArgs.map (fun x => g.map (f.map x)) args) := by
        rw [FamilyArgs.map_comp]

end Hom

/-- The homomorphisms of raw binding algebras compose by their carrier maps. -/
instance algebraCategory : CategoryTheory.Category (Algebra.{u} S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro A B f
    apply Hom.ext
    intro Γ s x
    rfl
  comp_id := by
    intro A B f
    apply Hom.ext
    intro Γ s x
    rfl
  assoc := by
    intro A B C D f g h
    apply Hom.ext
    intro Γ s x
    rfl

/-- The actual intrinsically scoped terms form a raw algebra. -/
def terms (S : Signature) : Algebra S where
  Carrier := Term S
  injectVar := Term.var
  operation := fun o args => Term.op o (familyToSyntax args)
where
  familyToSyntax : {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FamilyArgs S (Term S) arity Γ → Args S arity Γ
    | _, _, .nil => .nil
    | _, _, .cons head tail => .cons head (familyToSyntax tail)

/-- Repackage actual constructor arguments as the polynomial argument family. -/
def syntaxToFamily : {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args S arity Γ → FamilyArgs S (Term S) arity Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head (syntaxToFamily tail)

theorem familyToSyntax_syntaxToFamily :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args S arity Γ),
      (terms.familyToSyntax S) (syntaxToFamily args) = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg (Args.cons head) (familyToSyntax_syntaxToFamily tail)

mutual

/-- The unique candidate interpretation of a term in a raw binding algebra. -/
def fold (A : Algebra.{u} S) :
    {Γ : Ctx S} → {s : S.Srt} → Term S Γ s → A.Carrier Γ s
  | _, _, .var x => A.injectVar x
  | _, _, .op o args => A.operation o (foldArgs A args)

def foldArgs (A : Algebra.{u} S) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args S arity Γ → FamilyArgs S A.Carrier arity Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (fold A head) (foldArgs A tail)

end

theorem foldArgs_familyToSyntax (A : Algebra.{u} S) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (Term S) arity Γ),
      foldArgs A ((terms.familyToSyntax S) args) =
        FamilyArgs.map (fold A) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg (FamilyArgs.cons (fold A head))
        (foldArgs_familyToSyntax A tail)

/-- Interpret raw terms in any algebra, preserving each constructor. -/
def foldHom (A : Algebra.{u} S) : Hom (terms S) A where
  map := fold A
  map_variable := by
    intro Γ s x
    rfl
  map_operation := by
    intro Γ s o args
    exact congrArg (A.operation o) (foldArgs_familyToSyntax A args)

mutual

theorem homMap_eq_fold (A : Algebra.{u} S) (h : Hom (terms S) A) :
    ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
      h.map term = fold A term
  | _, _, .var x => h.map_variable x
  | _, _, .op o args => by
      let semanticArgs := syntaxToFamily args
      have reconstruction : (terms.familyToSyntax S) semanticArgs = args :=
        familyToSyntax_syntaxToFamily args
      calc
        h.map (.op o args) = h.map ((terms S).operation o semanticArgs) := by
          rw [show (terms S).operation o semanticArgs = .op o args from
            congrArg (Term.op o) reconstruction]
        _ = A.operation o (FamilyArgs.map h.map semanticArgs) :=
          h.map_operation o semanticArgs
        _ = A.operation o (foldArgs A args) := by
          exact congrArg (A.operation o) (homArgs_eq_foldArgs A h args)

theorem homArgs_eq_foldArgs (A : Algebra.{u} S) (h : Hom (terms S) A) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args S arity Γ),
      FamilyArgs.map h.map (syntaxToFamily args) = foldArgs A args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg₂ FamilyArgs.cons
        (homMap_eq_fold A h head) (homArgs_eq_foldArgs A h tail)

end

/-- No second constructor-preserving interpretation of raw terms exists. -/
theorem hom_unique (A : Algebra.{u} S) (h : Hom (terms S) A) :
    h = foldHom A := by
  apply Hom.ext
  intro Γ s term
  exact homMap_eq_fold A h term

/-- The free raw term algebra has exactly one map into every raw binding
algebra, including algebras in larger universes. -/
instance uniqueHom (A : Algebra.{u} S) : Unique (Hom (terms S) A) where
  default := foldHom A
  uniq := hom_unique A

/-- In the category of small raw binding algebras, actual scoped terms are
an initial object. This initiality covers the terms-only rung. -/
def termsIsInitial (S : Signature) :
    CategoryTheory.Limits.IsInitial (terms S) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom foldHom (fun A h => hom_unique A h)

/-- A nontrivial target algebra counts operator nodes and ignores variables.
Binder contexts remain present in the argument indices. -/
def argumentCount : {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    FamilyArgs S (fun _ _ => Nat) arity Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => head + argumentCount tail

def operationCount (S : Signature) : Algebra S where
  Carrier := fun _ _ => Nat
  injectVar := fun _ => 0
  operation := fun _ args => 1 + argumentCount args

/-- The unique fold into the counting algebra. -/
def countTerm {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s) : Nat :=
  fold (operationCount S) term

theorem count_variable {Γ : Ctx S} {s : S.Srt} (x : Var Γ s) :
    countTerm (Term.var x) = 0 := rfl

theorem count_operator {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Args S (S.arity o) Γ) :
    0 < countTerm (Term.op o args) := by
  change 0 < 1 + argumentCount (foldArgs (operationCount S) args)
  omega

/-- The universal fold is not a vacuous identity: this concrete algebra
separates every variable from every operator term of the same sort. -/
theorem count_operator_ne_variable {Γ : Ctx S} {s : S.Srt}
    (o : S.Op s) (args : Args S (S.arity o) Γ) (x : Var Γ s) :
    countTerm (Term.op o args) ≠ countTerm (Term.var x) := by
  rw [count_variable]
  exact Nat.ne_of_gt (count_operator o args)

end Mettapedia.OSLF.Binding.FreeBindingTerms
