import Mettapedia.Languages.Agda.Specification.Syntax

/-!
# Finite hereditary application and substitution

The judgments below describe the finite computations of the application-only
fragment of Agda 2.8.0.2, commit
`cccf42fa88eae25ccbe2623f489021d2075f6f73`.

Rule sources:

* `Apply.nil`, `Apply.var`, `Apply.defn`, `Apply.con`, and `Apply.lam` follow
  `Agda.TypeChecking.Substitute.applyTermE`, `defApp`, and the `Apply` branch of
  `conApp`. Definition names in this fragment exclude projection functions.
* `Instantiate.bind` and `Instantiate.noBind` follow
  `Agda.TypeChecking.Substitute.Class.lazyAbsApp`.
* `Substitute` follows `Agda.TypeChecking.Substitute.applySubstTerm`: at a variable,
  first substitute its eliminations, then apply them to the substitution image.
* `SubstituteAbs` follows the `Subst (Abs a)` instance, which lifts only under
  `Abs`. `SubstituteSpine` follows the list and `Elim'` substitution instances.

These are derivation types, not propositions or normalization oracles. Finite
evidence is required, because a well-scoped untyped input need not normalize.
`Apply` is hereditary application to a spine, rather than a one-step reduction.
It includes beta computation inside substitution images and preserves the
beta-normal syntax of the reference fragment.

Cockx's Agda Core `Reduce.agda` at commit
`2fb9574e78326ec532dcb2af8272631c765e947d` independently motivates separating the
focus and elimination stack and requiring finite reduction evidence. The
`beta-red` rule of `logrel-mltt/Definition/Typed.agda` at
`9d6e290064962a1987c9e1a131c2fb967d6ef928` is a comparison for ordinary function
beta computation only; this module makes no claim about that development's
typing, universes, logical relation, or normalization theorem.
-/

namespace Mettapedia.Languages.Agda.Specification

mutual
  /-- Finite hereditary application, including beta substitution. -/
  inductive Apply : {n : Nat} → Term n → Spine n → Term n → Type
    | nil (t : Term n) : Apply t .nil t
    | var (i : Fin n) (es : Spine n) (e : Elim n) (fs : Spine n) :
        Apply (.var i es) (.cons e fs) (.var i (es.append (.cons e fs)))
    | defn (f : String) (es : Spine n) (e : Elim n) (fs : Spine n) :
        Apply (.defn f es) (.cons e fs) (.defn f (es.append (.cons e fs)))
    | con (c : String) (es : Spine n) (e : Elim n) (fs : Spine n) :
        Apply (.con c es) (.cons e fs) (.con c (es.append (.cons e fs)))
    | lam {b : Abs n} {u v w : Term n} {es : Spine n} :
        Instantiate b u v → Apply v es w →
        Apply (.lam b) (.cons (.apply u) es) w

  /-- Applying an abstraction, including the non-binding `NoAbs` case. -/
  inductive Instantiate : {n : Nat} → Abs n → Term n → Term n → Type
    | bind {t : Term (n + 1)} {u v : Term n} :
        Substitute (Substitution.single u) t v → Instantiate (.bind t) u v
    | noBind (t u : Term n) : Instantiate (.noBind t) u t

  /-- Capture-avoiding hereditary substitution into a term. -/
  inductive Substitute : {n m : Nat} → Substitution n m → Term n → Term m → Type
    | var {σ : Substitution n m} {i : Fin n} {es : Spine n}
        {fs : Spine m} {v : Term m} :
        SubstituteSpine σ es fs → Apply (σ i) fs v → Substitute σ (.var i es) v
    | defn {σ : Substitution n m} {es : Spine n} {fs : Spine m} (f : String) :
        SubstituteSpine σ es fs → Substitute σ (.defn f es) (.defn f fs)
    | con {σ : Substitution n m} {es : Spine n} {fs : Spine m} (c : String) :
        SubstituteSpine σ es fs → Substitute σ (.con c es) (.con c fs)
    | lam {σ : Substitution n m} {b : Abs n} {c : Abs m} :
        SubstituteAbs σ b c → Substitute σ (.lam b) (.lam c)
    | pi {σ : Substitution n m} {a : Ty n} {b : TyAbs n}
        {a' : Ty m} {b' : TyAbs m} :
        SubstituteTy σ a a' → SubstituteTyAbs σ b b' →
        Substitute σ (.pi a b) (.pi a' b')
    | sort (σ : Substitution n m) (l : Nat) : Substitute σ (.sort l) (.sort l)
    | level (σ : Substitution n m) (l : Nat) : Substitute σ (.level l) (.level l)

  /-- The substitution is lifted precisely at the scope-extending binder. -/
  inductive SubstituteAbs : {n m : Nat} → Substitution n m → Abs n → Abs m → Type
    | bind {σ : Substitution n m} {t : Term (n + 1)} {u : Term (m + 1)} :
        Substitute (Substitution.lift σ) t u → SubstituteAbs σ (.bind t) (.bind u)
    | noBind {σ : Substitution n m} {t : Term n} {u : Term m} :
        Substitute σ t u → SubstituteAbs σ (.noBind t) (.noBind u)

  /-- Substitution preserves the closed sort annotation of a type. -/
  inductive SubstituteTy : {n m : Nat} → Substitution n m → Ty n → Ty m → Type
    | el {σ : Substitution n m} {t : Term n} {u : Term m} (l : Nat) :
        Substitute σ t u → SubstituteTy σ (.el l t) (.el l u)

  /-- Substitution into a sort-annotated type abstraction. -/
  inductive SubstituteTyAbs :
      {n m : Nat} → Substitution n m → TyAbs n → TyAbs m → Type
    | bind {σ : Substitution n m} {t : Ty (n + 1)} {u : Ty (m + 1)} :
        SubstituteTy (Substitution.lift σ) t u →
        SubstituteTyAbs σ (.bind t) (.bind u)
    | noBind {σ : Substitution n m} {t : Ty n} {u : Ty m} :
        SubstituteTy σ t u → SubstituteTyAbs σ (.noBind t) (.noBind u)

  /-- Substitution visits every argument, preserving elimination order. -/
  inductive SubstituteSpine :
      {n m : Nat} → Substitution n m → Spine n → Spine m → Type
    | nil (σ : Substitution n m) : SubstituteSpine σ .nil .nil
    | cons {σ : Substitution n m} {t : Term n} {u : Term m}
        {es : Spine n} {fs : Spine m} :
        Substitute σ t u → SubstituteSpine σ es fs →
        SubstituteSpine σ (.cons (.apply t) es) (.cons (.apply u) fs)
end

namespace Apply

def variableSpine (i : Fin n) (es fs : Spine n) :
    Apply (.var i es) fs (.var i (es.append fs)) := by
  match fs with
  | .nil => simpa only [Spine.append_nil] using Apply.nil (.var i es)
  | .cons e fs => exact .var i es e fs

def definition (f : String) (es fs : Spine n) :
    Apply (.defn f es) fs (.defn f (es.append fs)) := by
  match fs with
  | .nil => simpa only [Spine.append_nil] using Apply.nil (.defn f es)
  | .cons e fs => exact .defn f es e fs

def constructor (c : String) (es fs : Spine n) :
    Apply (.con c es) fs (.con c (es.append fs)) := by
  match fs with
  | .nil => simpa only [Spine.append_nil] using Apply.nil (.con c es)
  | .cons e fs => exact .con c es e fs

def bvar (i : Fin n) (es : Spine n) : Apply (Term.bvar i) es (.var i es) :=
  variableSpine i .nil es

theorem nil_result {t u : Term n} (h : Apply t .nil u) : u = t := by
  cases h
  rfl

/-- Concrete sorts are never functions in this fragment. -/
theorem no_sort_cons (l : Nat) (e : Elim n) (es : Spine n) (t : Term n) :
    ¬ Nonempty (Apply (.sort l) (.cons e es) t) := by
  rintro ⟨h⟩
  cases h

/-- A Pi type is syntax for a type former, not an applicable lambda. -/
theorem no_pi_cons (a : Ty n) (b : TyAbs n) (e : Elim n) (es : Spine n)
    (t : Term n) : ¬ Nonempty (Apply (.pi a b) (.cons e es) t) := by
  rintro ⟨h⟩
  cases h

theorem no_level_cons (l : Nat) (e : Elim n) (es : Spine n) (t : Term n) :
    ¬ Nonempty (Apply (.level l) (.cons e es) t) := by
  rintro ⟨h⟩
  cases h

end Apply

namespace Substitution

def ofRenaming (ρ : Renaming n m) : Substitution n m := fun i => Term.bvar (ρ i)

@[simp] theorem ofRenaming_id :
    ofRenaming (id : Renaming n n) = (identity : Substitution n n) := rfl

theorem lift_ofRenaming (ρ : Renaming n m) :
    lift (ofRenaming ρ) = ofRenaming (Renaming.lift ρ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end Substitution

mutual
  /-- Every pure renaming has a finite hereditary-substitution derivation. -/
  def Substitute.rename (t : Term n) (ρ : Renaming n m) :
      Substitute (Substitution.ofRenaming ρ) t (t.rename ρ) := by
    match t with
    | .var i es => exact .var (SubstituteSpine.rename es ρ) (Apply.bvar (ρ i) _)
    | .defn f es => exact .defn f (SubstituteSpine.rename es ρ)
    | .con c es => exact .con c (SubstituteSpine.rename es ρ)
    | .lam b => exact .lam (SubstituteAbs.rename b ρ)
    | .pi a b => exact .pi (SubstituteTy.rename a ρ) (SubstituteTyAbs.rename b ρ)
    | .sort l => exact .sort _ l
    | .level l => exact .level _ l

  def SubstituteAbs.rename (b : Abs n) (ρ : Renaming n m) :
      SubstituteAbs (Substitution.ofRenaming ρ) b (b.rename ρ) := by
    match b with
    | .bind t =>
      apply SubstituteAbs.bind
      rw [Substitution.lift_ofRenaming]
      exact Substitute.rename t (Renaming.lift ρ)
    | .noBind t => exact .noBind (Substitute.rename t ρ)

  def SubstituteTy.rename (a : Ty n) (ρ : Renaming n m) :
      SubstituteTy (Substitution.ofRenaming ρ) a (a.rename ρ) := by
    match a with
    | .el l t => exact .el l (Substitute.rename t ρ)

  def SubstituteTyAbs.rename (b : TyAbs n) (ρ : Renaming n m) :
      SubstituteTyAbs (Substitution.ofRenaming ρ) b (b.rename ρ) := by
    match b with
    | .bind t =>
      apply SubstituteTyAbs.bind
      rw [Substitution.lift_ofRenaming]
      exact SubstituteTy.rename t (Renaming.lift ρ)
    | .noBind t => exact .noBind (SubstituteTy.rename t ρ)

  def SubstituteSpine.rename (es : Spine n) (ρ : Renaming n m) :
      SubstituteSpine (Substitution.ofRenaming ρ) es (es.rename ρ) := by
    match es with
    | .nil => exact .nil _
    | .cons (.apply t) es =>
      exact .cons (Substitute.rename t ρ) (SubstituteSpine.rename es ρ)
end

/-- Identity substitution is derived for every term, including nested binders. -/
def Substitute.identity (t : Term n) : Substitute Substitution.identity t t := by
  simpa only [Term.rename_id, Substitution.ofRenaming_id] using Substitute.rename t id

def SubstituteAbs.identity (b : Abs n) : SubstituteAbs Substitution.identity b b := by
  simpa only [Abs.rename_id, Substitution.ofRenaming_id] using SubstituteAbs.rename b id

def SubstituteTy.identity (a : Ty n) : SubstituteTy Substitution.identity a a := by
  simpa only [Ty.rename_id, Substitution.ofRenaming_id] using
    SubstituteTy.rename a id

def SubstituteTyAbs.identity (b : TyAbs n) : SubstituteTyAbs Substitution.identity b b := by
  simpa only [TyAbs.rename_id, Substitution.ofRenaming_id] using
    SubstituteTyAbs.rename b id

def SubstituteSpine.identity (es : Spine n) :
    SubstituteSpine Substitution.identity es es := by
  simpa only [Spine.rename_id, Substitution.ofRenaming_id] using SubstituteSpine.rename es id

end Mettapedia.Languages.Agda.Specification
