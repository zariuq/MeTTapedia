import Mettapedia.Languages.Agda.Adequacy.Embedding
import Mettapedia.Languages.Agda.Specification.Reduction
import Mettapedia.Languages.Agda.Structural.Reduction
import Mettapedia.OSLF.Syntax.BindingCompatiblePaths

/-!
# Finite hereditary computation is realized by structural paths

Source application performs substitution and beta computation together.
Structural substitution is a total raw operation, and its resulting redexes
are reduced explicitly. The comparison consequently retains finite paths;
it is not a claim of syntactic equality or strong normalization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Adequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

abbrev Path {Γ : Ctx sig} {s : Structural.Srt} (source target : Term sig Γ s) :=
  CompatibleDerivations.Path Structural.Root source target

namespace Path

def lam {Γ : Ctx sig} {source target : Structural.Tm (.term :: Γ)}
    (path : Path source target) : Path (Structural.lam source) (Structural.lam target) :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.lam (.cons path .nil)

def lamNoAbs {Γ : Ctx sig} {source target : Structural.Tm Γ}
    (path : Path source target) : Path (Structural.lamNoAbs source) (Structural.lamNoAbs target) :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.lamNoAbs (.cons path .nil)

def eliminate {Γ : Ctx sig} {a b : Structural.Tm Γ} {es fs : Structural.Spine Γ}
    (head : Path a b) (spine : Path es fs) :
    Path (Structural.eliminate a es) (Structural.eliminate b fs) :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.eliminate
    (.cons head (.cons spine .nil))

def spineCons {Γ : Ctx sig} {a b : Structural.Elim Γ} {es fs : Structural.Spine Γ}
    (head : Path a b) (spine : Path es fs) :
    Path (Structural.cons a es) (Structural.cons b fs) :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.cons
    (.cons head (.cons spine .nil))

def apply {Γ : Ctx sig} {a b : Structural.Tm Γ} (path : Path a b) :
    Path (Structural.apply a) (Structural.apply b) :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.apply (.cons path .nil)

def el {Γ : Ctx sig} (sort : Structural.UnivSort Γ) {a b : Structural.Tm Γ}
    (path : Path a b) : Path (Structural.el sort a) (Structural.el sort b) :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.el
    (.cons (.refl _) (.cons path .nil))

def pi {Γ : Ctx sig} {a a' : Structural.Ty Γ} {b b' : Structural.Ty (.term :: Γ)}
    (domain : Path a a') (codomain : Path b b') :
    Path (Structural.pi a b) (Structural.pi a' b') :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.pi
    (.cons domain (.cons codomain .nil))

def piNoAbs {Γ : Ctx sig} {a a' b b' : Structural.Ty Γ}
    (domain : Path a a') (codomain : Path b b') :
    Path (Structural.piNoAbs a b) (Structural.piNoAbs a' b') :=
  CompatibleDerivations.Path.congr (R := Structural.Root) Structural.Op.piNoAbs
    (.cons domain (.cons codomain .nil))

end Path

def appendPath {n : Nat} (first second : Specification.Spine n) :
    Path (Structural.append (embedSpine first) (embedSpine second))
      (embedSpine (first.append second)) :=
  match first with
  | .nil => .single (.root (.appendEmpty _))
  | .cons (.apply _head) tail =>
      .cons (.root (.appendCons _ _ _)) (Path.spineCons (.refl _) (appendPath tail second))

/-- A neutral source head with a nonempty stored spine composes with the
pending spine through the structural append computation. -/
def variableApplication {n : Nat} (index : Fin n) (stored : Specification.Spine n)
    (next : Specification.Elim n) (rest : Specification.Spine n) :
    Path (Structural.eliminate (embedTerm (.var index stored)) (embedSpine (.cons next rest)))
      (embedTerm (.var index (stored.append (.cons next rest)))) :=
  match stored with
  | .nil => .refl _
  | .cons (.apply head) tail =>
      .cons (.root (.eliminateAppend _ _ _))
        (Path.eliminate (.refl _) (appendPath (.cons (.apply head) tail) (.cons next rest)))

def definitionApplication {n : Nat} (name : String) (stored : Specification.Spine n)
    (next : Specification.Elim n) (rest : Specification.Spine n) :
    Path (Structural.eliminate (embedTerm (.defn name stored)) (embedSpine (.cons next rest)))
      (embedTerm (.defn name (stored.append (.cons next rest)))) :=
  match stored with
  | .nil => .refl _
  | .cons (.apply head) tail =>
      .cons (.root (.eliminateAppend _ _ _))
        (Path.eliminate (.refl _) (appendPath (.cons (.apply head) tail) (.cons next rest)))

def constructorApplication {n : Nat} (name : String) (stored : Specification.Spine n)
    (next : Specification.Elim n) (rest : Specification.Spine n) :
    Path (Structural.eliminate (embedTerm (.con name stored)) (embedSpine (.cons next rest)))
      (embedTerm (.con name (stored.append (.cons next rest)))) :=
  match stored with
  | .nil => .refl _
  | .cons (.apply head) tail =>
      .cons (.root (.eliminateAppend _ _ _))
        (Path.eliminate (.refl _) (appendPath (.cons (.apply head) tail) (.cons next rest)))



def piAbstraction {n : Nat} (domain : Structural.Ty (scope n)) :
    Specification.TyAbs n → Structural.Tm (scope n)
  | .bind body => Structural.pi domain (embedTy body)
  | .noBind body => Structural.piNoAbs domain (embedTy body)

theorem embedTerm_pi {n : Nat} (domain : Specification.Ty n) (body : Specification.TyAbs n) :
    embedTerm (.pi domain body) = piAbstraction (embedTy domain) body := by
  cases body <;> rfl

mutual
  /-- Every finite source application is realized by a structural path. -/
  def realizeApply {n : Nat} {term result : Specification.Term n}
      {spine : Specification.Spine n} (derivation : Specification.Apply term spine result) :
      Path (Structural.eliminate (embedTerm term) (embedSpine spine)) (embedTerm result) := by
    match derivation with
    | .nil _ => exact .single (.root (.eliminateEmpty _))
    | .var index stored next rest => exact variableApplication index stored next rest
    | .defn name stored next rest => exact definitionApplication name stored next rest
    | .con name stored next rest => exact constructorApplication name stored next rest
    | .lam instantiate continuation =>
        exact (realizeInstantiate instantiate _).trans (realizeApply continuation)

  def realizeInstantiate {n : Nat} {body : Specification.Abs n} {argument result : Specification.Term n}
      (derivation : Specification.Instantiate body argument result) (rest : Structural.Spine (scope n)) :
      Path (Structural.eliminate (embedTerm (.lam body))
          (Structural.cons (Structural.apply (embedTerm argument)) rest))
        (Structural.eliminate (embedTerm result) rest) := by
    match derivation with
    | .bind substitution =>
        apply CompatibleDerivations.Path.cons (.root (Structural.Root.beta _ _ _))
        apply Path.eliminate _ (.refl _)
        have path := realizeSubstitute substitution
        rw [embedSub_single] at path
        exact path
    | .noBind _ _ => exact .single (.root (.betaNoAbs _ _ _))

  /-- Raw substitution computes to the source hereditary-substitution result. -/
  def realizeSubstitute {n m : Nat} {σ : Specification.Substitution n m}
      {term : Specification.Term n} {result : Specification.Term m}
      (derivation : Specification.Substitute σ term result) :
      Path (bind (embedSub σ) (embedTerm term)) (embedTerm result) := by
    match derivation with
    | .var (i := index) spine application =>
        match spine with
        | .nil _ =>
            have same := Specification.Apply.nil_result application
            subst result
            change Path (embedSub σ _ (embedVar index)) (embedTerm (σ index))
            rw [embedSub_var]
            exact .refl _
        | .cons head tail =>
            change Path (Structural.eliminate (embedSub σ _ (embedVar index))
              (Structural.cons (Structural.apply (bind (embedSub σ) (embedTerm _)))
                (bind (embedSub σ) (embedSpine _)))) _
            rw [embedSub_var]
            exact (Path.eliminate (.refl _)
              (Path.spineCons (Path.apply (realizeSubstitute head)) (realizeSpine tail))).trans
              (realizeApply application)
    | .defn _ spine =>
        match spine with
        | .nil _ => exact .refl _
        | .cons head tail =>
            exact Path.eliminate (.refl _)
              (Path.spineCons (Path.apply (realizeSubstitute head)) (realizeSpine tail))
    | .con _ spine =>
        match spine with
        | .nil _ => exact .refl _
        | .cons head tail =>
            exact Path.eliminate (.refl _)
              (Path.spineCons (Path.apply (realizeSubstitute head)) (realizeSpine tail))
    | .lam abstraction => exact realizeAbs abstraction
    | .pi domain codomain =>
        simpa only [embedTerm_pi] using realizeTyAbs codomain _ _ (realizeTy domain)
    | .sort _ _ => exact .refl _
    | .level _ _ => exact .refl _

  def realizeAbs {n m : Nat} {σ : Specification.Substitution n m}
      {source : Specification.Abs n} {target : Specification.Abs m}
      (derivation : Specification.SubstituteAbs σ source target) :
      Path (bind (embedSub σ) (embedTerm (.lam source))) (embedTerm (.lam target)) := by
    match derivation with
    | .bind body =>
        apply Path.lam
        have path := realizeSubstitute body
        rw [embedSub_lift] at path
        exact path
    | .noBind body => exact Path.lamNoAbs (realizeSubstitute body)

  def realizeTy {n m : Nat} {σ : Specification.Substitution n m}
      {ty : Specification.Ty n} {result : Specification.Ty m}
      (derivation : Specification.SubstituteTy σ ty result) :
      Path (bind (embedSub σ) (embedTy ty)) (embedTy result) := by
    match derivation with
    | .el _ term => exact Path.el _ (realizeSubstitute term)

  def realizeTyAbs {n m : Nat} {σ : Specification.Substitution n m}
      {source : Specification.TyAbs n} {target : Specification.TyAbs m}
      (derivation : Specification.SubstituteTyAbs σ source target)
      (domain : Structural.Ty (scope n)) (domain' : Structural.Ty (scope m))
      (domainPath : Path (bind (embedSub σ) domain) domain') :
      Path (bind (embedSub σ) (piAbstraction domain source)) (piAbstraction domain' target) := by
    match derivation with
    | .bind body =>
        apply Path.pi domainPath
        have path := realizeTy body
        rw [embedSub_lift] at path
        exact path
    | .noBind body => exact Path.piNoAbs domainPath (realizeTy body)

  def realizeSpine {n m : Nat} {σ : Specification.Substitution n m}
      {spine : Specification.Spine n} {result : Specification.Spine m}
      (derivation : Specification.SubstituteSpine σ spine result) :
      Path (bind (embedSub σ) (embedSpine spine)) (embedSpine result) := by
    match derivation with
    | .nil _ => exact .refl _
    | .cons head tail => exact Path.spineCons (Path.apply (realizeSubstitute head)) (realizeSpine tail)
end

end Mettapedia.Languages.Agda.Adequacy
