import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

/-!
Nil Geisweiller's backward-via-forward propositional MP fragment, following
`github.com/ngeiswei/chaining`
(`experimental/backward-via-forward/bfc-xp.metta`).
-/

namespace Mettapedia.Logic.LP.BackwardViaForwardMP

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

universe u

inductive Formula (Atom : Type u) where
  | atom : Atom -> Formula Atom
  | imp : Formula Atom -> Formula Atom -> Formula Atom
  | neg : Formula Atom -> Formula Atom
deriving DecidableEq, Repr

namespace Formula

infixr:60 " ==> " => Formula.imp

end Formula

open Formula

inductive BwdRaw (Atom : Type u) where
  | ax1 : Formula Atom -> Formula Atom -> BwdRaw Atom
  | ax2 : Formula Atom -> Formula Atom -> Formula Atom -> BwdRaw Atom
  | ax3 : Formula Atom -> Formula Atom -> BwdRaw Atom
  | mp : BwdRaw Atom -> BwdRaw Atom -> BwdRaw Atom
deriving Repr

namespace BwdRaw

def size : BwdRaw Atom -> Nat
  | .ax1 _ _ => 1
  | .ax2 _ _ _ => 1
  | .ax3 _ _ => 1
  | .mp f x => 1 + size f + size x

end BwdRaw

inductive BwdHasType : BwdRaw Atom -> Formula Atom -> Prop where
  | ax1 (phi psi : Formula Atom) :
      BwdHasType (.ax1 phi psi) (phi ==> (psi ==> phi))
  | ax2 (phi psi chi : Formula Atom) :
      BwdHasType (.ax2 phi psi chi)
        ((phi ==> (psi ==> chi)) ==> ((phi ==> psi) ==> (phi ==> chi)))
  | ax3 (phi psi : Formula Atom) :
      BwdHasType (.ax3 phi psi)
        (((.neg phi) ==> (.neg psi)) ==> (psi ==> phi))
  | mp {phi psi : Formula Atom} {f x : BwdRaw Atom} :
      BwdHasType f (phi ==> psi) ->
      BwdHasType x phi ->
      BwdHasType (.mp f x) psi

namespace BwdHasType

theorem type_unique {t : BwdRaw Atom} {tau1 tau2 : Formula Atom}
    (h1 : BwdHasType t tau1) (h2 : BwdHasType t tau2) :
    tau1 = tau2 := by
  induction h1 generalizing tau2 with
  | ax1 phi psi =>
      cases h2
      rfl
  | ax2 phi psi chi =>
      cases h2
      rfl
  | ax3 phi psi =>
      cases h2
      rfl
  | mp hf hx ihf ihx =>
      cases h2 with
      | mp hf' hx' =>
          cases ihf hf'
          rfl

end BwdHasType

abbrev BwdProof (Atom : Type u) (tau : Formula Atom) : Type u :=
  { raw : BwdRaw Atom // BwdHasType raw tau }

namespace BwdProof

def size (p : BwdProof Atom tau) : Nat :=
  BwdRaw.size p.1

def mp {a b : Formula Atom}
    (f : BwdProof Atom (a ==> b)) (x : BwdProof Atom a) :
    BwdProof Atom b :=
  Subtype.mk (.mp f.1 x.1) (BwdHasType.mp f.2 x.2)

end BwdProof

inductive Ty (Atom : Type u) where
  | prop : Formula Atom -> Ty Atom
  | arr : Ty Atom -> Ty Atom -> Ty Atom
deriving DecidableEq, Repr

namespace Ty

infixr:55 " ~~> " => Ty.arr

end Ty

open Ty

inductive FwdRaw (Atom : Type u) where
  | bwd : BwdRaw Atom -> FwdRaw Atom
  | id : Ty Atom -> FwdRaw Atom
  | blue : Ty Atom -> Ty Atom -> Ty Atom -> FwdRaw Atom
  | black : Ty Atom -> Ty Atom -> Ty Atom -> Ty Atom -> FwdRaw Atom
  | mpConst : Formula Atom -> Formula Atom -> FwdRaw Atom
  | mpInv : Formula Atom -> Formula Atom -> Ty Atom -> FwdRaw Atom
  | app : FwdRaw Atom -> FwdRaw Atom -> FwdRaw Atom
deriving Repr

namespace FwdRaw

def size : FwdRaw Atom -> Nat
  | .bwd t => 1 + BwdRaw.size t
  | .id _ => 1
  | .blue _ _ _ => 1
  | .black _ _ _ _ => 1
  | .mpConst _ _ => 1
  | .mpInv _ _ _ => 1
  | .app f x => 1 + size f + size x

end FwdRaw

inductive FwdHasType : FwdRaw Atom -> Ty Atom -> Type u where
  | bwd {t : BwdRaw Atom} {tau : Formula Atom} :
      BwdHasType t tau ->
      FwdHasType (.bwd t) (.prop tau)
  | id (sigma : Ty Atom) :
      FwdHasType (.id sigma) (sigma ~~> sigma)
  | blue (a b c : Ty Atom) :
      FwdHasType (.blue a b c) ((b ~~> c) ~~> ((a ~~> b) ~~> (a ~~> c)))
  | black (a b c d : Ty Atom) :
      FwdHasType (.black a b c d)
        ((c ~~> d) ~~> ((a ~~> (b ~~> c)) ~~> (a ~~> (b ~~> d))))
  | mpConst (a b : Formula Atom) :
      FwdHasType (.mpConst a b) (.prop (a ==> b) ~~> (.prop a ~~> .prop b))
  | mpInv (a b : Formula Atom) (gamma : Ty Atom) :
      FwdHasType (.mpInv a b gamma)
        ((.prop b ~~> gamma) ~~>
          (.prop (a ==> b) ~~> (.prop a ~~> gamma)))
  | app {sigma tau : Ty Atom} {f x : FwdRaw Atom} :
      FwdHasType f (sigma ~~> tau) ->
      FwdHasType x sigma ->
      FwdHasType (.app f x) tau

abbrev FwdProof (Atom : Type u) (tau : Formula Atom) : Type u :=
  Sigma (fun raw : FwdRaw Atom => FwdHasType raw (.prop tau))

namespace FwdProof

def size (p : FwdProof Atom tau) : Nat :=
  FwdRaw.size p.1

end FwdProof

namespace FwdHasType

theorem type_unique {t : FwdRaw Atom} {ty1 ty2 : Ty Atom}
    (h1 : FwdHasType t ty1) (h2 : FwdHasType t ty2) :
    ty1 = ty2 := by
  induction h1 generalizing ty2 with
  | bwd h =>
      cases h2 with
      | bwd h' =>
          exact congrArg Ty.prop (BwdHasType.type_unique h h')
  | id sigma =>
      cases h2
      rfl
  | blue a b c =>
      cases h2
      rfl
  | black a b c d =>
      cases h2
      rfl
  | mpConst a b =>
      cases h2
      rfl
  | mpInv a b gamma =>
      cases h2
      rfl
  | app hf hx ihf ihx =>
      cases h2 with
      | app hf' hx' =>
          cases ihf hf'
          rfl

theorem derivation_unique {t : FwdRaw Atom} {ty : Ty Atom}
    (h1 h2 : FwdHasType t ty) :
    h1 = h2 := by
  induction h1 with
  | bwd h =>
      cases h2 with
      | bwd h' =>
          have hp : h = h' := proof_irrel h h'
          cases hp
          rfl
  | id sigma =>
      cases h2
      rfl
  | blue a b c =>
      cases h2
      rfl
  | black a b c d =>
      cases h2
      rfl
  | mpConst a b =>
      cases h2
      rfl
  | mpInv a b gamma =>
      cases h2
      rfl
  | app hf hx ihf ihx =>
      cases h2 with
      | app hf' hx' =>
          cases type_unique hf hf'
          cases ihf hf'
          cases ihx hx'
          rfl

instance subsingleton (t : FwdRaw Atom) (ty : Ty Atom) :
    Subsingleton (FwdHasType t ty) where
  allEq := derivation_unique

end FwdHasType

def NormTy (Atom : Type u) : Ty Atom -> Type u
  | .prop tau => BwdProof Atom tau
  | .arr sigma tau => NormTy Atom sigma -> NormTy Atom tau

def normalize {t : FwdRaw Atom} {ty : Ty Atom}
    (ht : FwdHasType t ty) :
    NormTy Atom ty :=
  match ht with
  | .bwd h => Subtype.mk _ h
  | .id _ => fun x => x
  | .blue _ _ _ => fun f g x => f (g x)
  | .black _ _ _ _ => fun f g x y => f (g x y)
  | .mpConst _ _ => fun g x => BwdProof.mp g x
  | .mpInv _ _ _ => fun z g x => z (BwdProof.mp g x)
  | .app hf hx => (normalize hf) (normalize hx)

def reduceRaw {tau : Formula Atom}
    (t : FwdRaw Atom) (ht : FwdHasType t (.prop tau)) :
    BwdRaw Atom :=
  (normalize ht).1

theorem reduce_type_preserved {tau : Formula Atom}
    (t : FwdRaw Atom) (ht : FwdHasType t (.prop tau)) :
    BwdHasType (reduceRaw t ht) tau :=
  (normalize ht).2

def reduce {tau : Formula Atom} (p : FwdProof Atom tau) : BwdProof Atom tau :=
  normalize p.2

inductive Red : FwdRaw Atom -> FwdRaw Atom -> Prop where
  | mpInv {a b : Formula Atom} {gamma : Ty Atom}
      {z g x : FwdRaw Atom} :
      Red
        (.app (.app (.app (.mpInv a b gamma) z) g) x)
        (.app z (.app (.app (.mpConst a b) g) x))
  | blue {a b c : Ty Atom} {f g x : FwdRaw Atom} :
      Red
        (.app (.app (.app (.blue a b c) f) g) x)
        (.app f (.app g x))
  | black {a b c d : Ty Atom} {f g x y : FwdRaw Atom} :
      Red
        (.app (.app (.app (.app (.black a b c d) f) g) x) y)
        (.app f (.app (.app g x) y))
  | id {sigma : Ty Atom} {x : FwdRaw Atom} :
      Red (.app (.id sigma) x) x
  | app_fun {f f' x : FwdRaw Atom} :
      Red f f' ->
      Red (.app f x) (.app f' x)
  | app_arg {f x x' : FwdRaw Atom} :
      Red x x' ->
      Red (.app f x) (.app f x')

theorem red_type_preserved_exists {t t' : FwdRaw Atom}
    (hred : Red t t') {ty : Ty Atom}
    (ht : FwdHasType t ty) :
    Nonempty (FwdHasType t' ty) := by
  induction hred generalizing ty with
  | mpInv =>
      cases ht with
      | app hfun hx =>
          cases hfun with
          | app hfun hg =>
              cases hfun with
              | app hmpi hz =>
                  cases hmpi
                  exact Nonempty.intro
                    (FwdHasType.app hz
                      (FwdHasType.app
                        (FwdHasType.app (FwdHasType.mpConst _ _) hg)
                        hx))
  | blue =>
      cases ht with
      | app hfun hx =>
          cases hfun with
          | app hfun hg =>
              cases hfun with
              | app hblue hf =>
                  cases hblue
                  exact Nonempty.intro
                    (FwdHasType.app hf (FwdHasType.app hg hx))
  | black =>
      cases ht with
      | app hfun hy =>
          cases hfun with
          | app hfun hx =>
              cases hfun with
              | app hfun hg =>
                  cases hfun with
                  | app hblack hf =>
                      cases hblack
                      exact Nonempty.intro
                        (FwdHasType.app hf
                          (FwdHasType.app (FwdHasType.app hg hx) hy))
  | id =>
      cases ht with
      | app hfun hx =>
          cases hfun
          exact Nonempty.intro hx
  | app_fun h ih =>
      cases ht with
      | app hf hx =>
          cases ih hf with
          | intro hf' =>
              exact Nonempty.intro (FwdHasType.app hf' hx)
  | app_arg h ih =>
      cases ht with
      | app hf hx =>
          cases ih hx with
          | intro hx' =>
              exact Nonempty.intro (FwdHasType.app hf hx')

noncomputable def red_type_preserved {t t' : FwdRaw Atom}
    (hred : Red t t') {ty : Ty Atom}
    (ht : FwdHasType t ty) :
    FwdHasType t' ty :=
  Classical.choice (red_type_preserved_exists hred ht)

theorem red_normalize_eq {t t' : FwdRaw Atom}
    (hred : Red t t') {ty : Ty Atom}
    (ht : FwdHasType t ty) (ht' : FwdHasType t' ty) :
    normalize ht = normalize ht' := by
  induction hred generalizing ty with
  | mpInv =>
      cases ht with
      | app hfun hx =>
          cases hfun with
          | app hfun hg =>
              cases hfun with
              | app hmpi hz =>
                  cases hmpi
                  cases ht' with
                  | app hz' harg =>
                      cases harg with
                      | app hfun' hx' =>
                          cases hfun' with
                          | app hmp' hg' =>
                              cases hmp'
                              cases FwdHasType.type_unique hz hz'
                              cases FwdHasType.type_unique hg hg'
                              cases FwdHasType.type_unique hx hx'
                              cases FwdHasType.derivation_unique hz hz'
                              cases FwdHasType.derivation_unique hg hg'
                              cases FwdHasType.derivation_unique hx hx'
                              rfl
  | blue =>
      cases ht with
      | app hfun hx =>
          cases hfun with
          | app hfun hg =>
              cases hfun with
              | app hblue hf =>
                  cases hblue
                  cases ht' with
                  | app hf' harg =>
                      cases harg with
                      | app hg' hx' =>
                          cases FwdHasType.type_unique hf hf'
                          cases FwdHasType.type_unique hg hg'
                          cases FwdHasType.type_unique hx hx'
                          cases FwdHasType.derivation_unique hf hf'
                          cases FwdHasType.derivation_unique hg hg'
                          cases FwdHasType.derivation_unique hx hx'
                          rfl
  | black =>
      cases ht with
      | app hfun hy =>
          cases hfun with
          | app hfun hx =>
              cases hfun with
              | app hfun hg =>
                  cases hfun with
                  | app hblack hf =>
                      cases hblack
                      cases ht' with
                      | app hf' harg =>
                          cases harg with
                          | app harg hy' =>
                              cases harg with
                              | app hg' hx' =>
                                  cases FwdHasType.type_unique hf hf'
                                  cases FwdHasType.type_unique hg hg'
                                  cases FwdHasType.type_unique hx hx'
                                  cases FwdHasType.type_unique hy hy'
                                  cases FwdHasType.derivation_unique hf hf'
                                  cases FwdHasType.derivation_unique hg hg'
                                  cases FwdHasType.derivation_unique hx hx'
                                  cases FwdHasType.derivation_unique hy hy'
                                  rfl
  | id =>
      cases ht with
      | app hfun hx =>
          cases hfun
          cases FwdHasType.derivation_unique hx ht'
          rfl
  | app_fun h ih =>
      cases ht with
      | app hf hx =>
          cases ht' with
          | app hf' hx' =>
              cases FwdHasType.type_unique hx hx'
              cases FwdHasType.derivation_unique hx hx'
              exact congrFun (ih hf hf') (normalize hx)
  | app_arg h ih =>
      cases ht with
      | app hf hx =>
          cases ht' with
          | app hf' hx' =>
              cases FwdHasType.type_unique hf hf'
              cases FwdHasType.derivation_unique hf hf'
              exact congrArg (normalize hf) (ih hx hx')

abbrev RedStar (Atom : Type u) : FwdRaw Atom -> FwdRaw Atom -> Prop :=
  Relation.ReflTransGen (@Red Atom)

theorem redStar_type_preserved_exists {t t' : FwdRaw Atom}
    (hred : RedStar Atom t t') {ty : Ty Atom}
    (ht : FwdHasType t ty) :
    Nonempty (FwdHasType t' ty) := by
  induction hred generalizing ty with
  | refl =>
      exact Nonempty.intro ht
  | tail hsteps hstep ih =>
      cases ih ht with
      | intro hmid =>
          exact red_type_preserved_exists hstep hmid

noncomputable def redStar_type_preserved {t t' : FwdRaw Atom}
    (hred : RedStar Atom t t') {ty : Ty Atom}
    (ht : FwdHasType t ty) :
    FwdHasType t' ty :=
  Classical.choice (redStar_type_preserved_exists hred ht)

theorem redStar_normalize_eq {t t' : FwdRaw Atom}
    (hred : RedStar Atom t t') {ty : Ty Atom}
    (ht : FwdHasType t ty) (ht' : FwdHasType t' ty) :
    normalize ht = normalize ht' := by
  induction hred generalizing ty with
  | refl =>
      cases FwdHasType.derivation_unique ht ht'
      rfl
  | tail hsteps hstep ih =>
      cases redStar_type_preserved_exists hsteps ht with
      | intro hmid =>
          exact (ih ht hmid).trans (red_normalize_eq hstep hmid ht')

def mpInvReduct (a b : Formula Atom) (_gamma : Ty Atom)
    (z g x : FwdRaw Atom) : FwdRaw Atom :=
  .app z (.app (.app (.mpConst a b) g) x)

def mpInvApp (a b : Formula Atom) (gamma : Ty Atom)
    (z g x : FwdRaw Atom) : FwdRaw Atom :=
  .app (.app (.app (.mpInv a b gamma) z) g) x

def blackMpApp (a b : Formula Atom) (gamma : Ty Atom)
    (z g x : FwdRaw Atom) : FwdRaw Atom :=
  .app
    (.app
      (.app
        (.app (.black (.prop (a ==> b)) (.prop a) (.prop b) gamma) z)
        (.mpConst a b))
      g)
    x

theorem mpInv_blackbird_agree
    (a b : Formula Atom) (gamma : Ty Atom) (z g x : FwdRaw Atom) :
    Red (mpInvApp a b gamma z g x) (mpInvReduct a b gamma z g x) /\
      Red (blackMpApp a b gamma z g x) (mpInvReduct a b gamma z g x) := by
  exact And.intro Red.mpInv Red.black

inductive ObcReaches : Nat -> Formula Atom -> BwdRaw Atom -> Prop where
  | ax1 {n : Nat} (phi psi : Formula Atom) :
      1 <= n ->
      ObcReaches n (phi ==> (psi ==> phi)) (.ax1 phi psi)
  | ax2 {n : Nat} (phi psi chi : Formula Atom) :
      1 <= n ->
      ObcReaches n
        ((phi ==> (psi ==> chi)) ==> ((phi ==> psi) ==> (phi ==> chi)))
        (.ax2 phi psi chi)
  | ax3 {n : Nat} (phi psi : Formula Atom) :
      1 <= n ->
      ObcReaches n (((.neg phi) ==> (.neg psi)) ==> (psi ==> phi))
        (.ax3 phi psi)
  | mp {n nf nx : Nat} {phi psi : Formula Atom} {f x : BwdRaw Atom} :
      ObcReaches nf (phi ==> psi) f ->
      ObcReaches nx phi x ->
      1 + nf + nx <= n ->
      ObcReaches n psi (.mp f x)

namespace ObcReaches

theorem sound {n : Nat} {tau : Formula Atom} {raw : BwdRaw Atom}
    (h : ObcReaches n tau raw) :
    BwdHasType raw tau ∧ BwdRaw.size raw <= n := by
  induction h with
  | ax1 phi psi hbudget =>
      exact ⟨BwdHasType.ax1 phi psi, by simpa [BwdRaw.size] using hbudget⟩
  | ax2 phi psi chi hbudget =>
      exact ⟨BwdHasType.ax2 phi psi chi, by simpa [BwdRaw.size] using hbudget⟩
  | ax3 phi psi hbudget =>
      exact ⟨BwdHasType.ax3 phi psi, by simpa [BwdRaw.size] using hbudget⟩
  | mp hf hx hbudget ihf ihx =>
      exact ⟨BwdHasType.mp ihf.1 ihx.1, by
        simp [BwdRaw.size]
        omega⟩

theorem complete {n : Nat} {tau : Formula Atom} {raw : BwdRaw Atom}
    (ht : BwdHasType raw tau) (hsize : BwdRaw.size raw <= n) :
    ObcReaches n tau raw := by
  induction ht generalizing n with
  | ax1 phi psi =>
      exact ObcReaches.ax1 phi psi (by simpa [BwdRaw.size] using hsize)
  | ax2 phi psi chi =>
      exact ObcReaches.ax2 phi psi chi (by simpa [BwdRaw.size] using hsize)
  | ax3 phi psi =>
      exact ObcReaches.ax3 phi psi (by simpa [BwdRaw.size] using hsize)
  | mp hf hx ihf ihx =>
      refine ObcReaches.mp (ihf le_rfl) (ihx le_rfl) ?_
      simpa [BwdRaw.size] using hsize

theorem iff_typed_size {n : Nat} {tau : Formula Atom} {raw : BwdRaw Atom} :
    ObcReaches n tau raw ↔ BwdHasType raw tau ∧ BwdRaw.size raw <= n := by
  constructor
  · exact sound
  · intro h
    exact complete h.1 h.2

end ObcReaches

def OfcBudgetOK (depth hypcnt : Nat) : Prop :=
  hypcnt <= depth + 1

inductive OfcTyReaches : Nat -> Nat -> Ty Atom -> FwdRaw Atom -> Prop where
  | bwd {depth hypcnt : Nat} {tau : Formula Atom} {raw : BwdRaw Atom} :
      BwdHasType raw tau ->
      FwdRaw.size (.bwd raw) <= depth ->
      OfcBudgetOK depth hypcnt ->
      OfcTyReaches depth hypcnt (.prop tau) (.bwd raw)
  | id {depth hypcnt : Nat} (sigma : Ty Atom) :
      FwdRaw.size (.id sigma) <= depth ->
      OfcBudgetOK depth hypcnt ->
      OfcTyReaches depth hypcnt (sigma ~~> sigma) (.id sigma)
  | blue {depth hypcnt : Nat} (a b c : Ty Atom) :
      FwdRaw.size (.blue a b c) <= depth ->
      OfcBudgetOK depth hypcnt ->
      OfcTyReaches depth hypcnt ((b ~~> c) ~~> ((a ~~> b) ~~> (a ~~> c)))
        (.blue a b c)
  | black {depth hypcnt : Nat} (a b c d : Ty Atom) :
      FwdRaw.size (.black a b c d) <= depth ->
      OfcBudgetOK depth hypcnt ->
      OfcTyReaches depth hypcnt
        ((c ~~> d) ~~> ((a ~~> (b ~~> c)) ~~> (a ~~> (b ~~> d))))
        (.black a b c d)
  | mpConst {depth hypcnt : Nat} (a b : Formula Atom) :
      FwdRaw.size (.mpConst a b) <= depth ->
      OfcBudgetOK depth hypcnt ->
      OfcTyReaches depth hypcnt (.prop (a ==> b) ~~> (.prop a ~~> .prop b))
        (.mpConst a b)
  | mpInv {depth hypcnt : Nat} (a b : Formula Atom) (gamma : Ty Atom) :
      FwdRaw.size (.mpInv a b gamma) <= depth ->
      OfcBudgetOK depth (hypcnt + 1) ->
      OfcTyReaches depth hypcnt
        ((.prop b ~~> gamma) ~~>
          (.prop (a ==> b) ~~> (.prop a ~~> gamma)))
        (.mpInv a b gamma)
  | app {depth df dx hypcnt : Nat} {sigma tau : Ty Atom} {f x : FwdRaw Atom} :
      OfcTyReaches df hypcnt (sigma ~~> tau) f ->
      OfcTyReaches dx hypcnt sigma x ->
      1 + df + dx <= depth ->
      OfcBudgetOK depth hypcnt ->
      OfcTyReaches depth hypcnt tau (.app f x)

abbrev OfcReaches (depth hypcnt : Nat) (tau : Formula Atom)
    (raw : FwdRaw Atom) : Prop :=
  OfcTyReaches depth hypcnt (.prop tau) raw

namespace OfcTyReaches

theorem sound {depth hypcnt : Nat} {ty : Ty Atom} {raw : FwdRaw Atom}
    (h : OfcTyReaches depth hypcnt ty raw) :
    Nonempty (FwdHasType raw ty) ∧ FwdRaw.size raw <= depth ∧
      OfcBudgetOK depth hypcnt := by
  induction h with
  | bwd ht hsize hbudget =>
      exact ⟨⟨FwdHasType.bwd ht⟩, hsize, hbudget⟩
  | id sigma hsize hbudget =>
      exact ⟨⟨FwdHasType.id sigma⟩, hsize, hbudget⟩
  | blue a b c hsize hbudget =>
      exact ⟨⟨FwdHasType.blue a b c⟩, hsize, hbudget⟩
  | black a b c d hsize hbudget =>
      exact ⟨⟨FwdHasType.black a b c d⟩, hsize, hbudget⟩
  | mpConst a b hsize hbudget =>
      exact ⟨⟨FwdHasType.mpConst a b⟩, hsize, hbudget⟩
  | mpInv a b gamma hsize hbudget =>
      exact ⟨⟨FwdHasType.mpInv a b gamma⟩, hsize, by
        dsimp [OfcBudgetOK] at hbudget ⊢
        omega⟩
  | app hf hx hbudget hcurrent ihf ihx =>
      rcases ihf with ⟨⟨htf⟩, hsf, _⟩
      rcases ihx with ⟨⟨htx⟩, hsx, _⟩
      exact ⟨⟨FwdHasType.app htf htx⟩, by
        simp [FwdRaw.size]
        omega, hcurrent⟩

theorem complete_seed {depth : Nat} {ty : Ty Atom} {raw : FwdRaw Atom}
    (ht : FwdHasType raw ty) (hsize : FwdRaw.size raw <= depth) :
    OfcTyReaches depth 1 ty raw := by
  induction ht generalizing depth with
  | bwd h =>
      exact OfcTyReaches.bwd h hsize (by
        dsimp [OfcBudgetOK]
        omega)
  | id sigma =>
      exact OfcTyReaches.id sigma hsize (by
        dsimp [OfcBudgetOK]
        omega)
  | blue a b c =>
      exact OfcTyReaches.blue a b c hsize (by
        dsimp [OfcBudgetOK]
        omega)
  | black a b c d =>
      exact OfcTyReaches.black a b c d hsize (by
        dsimp [OfcBudgetOK]
        omega)
  | mpConst a b =>
      exact OfcTyReaches.mpConst a b hsize (by
        dsimp [OfcBudgetOK]
        omega)
  | mpInv a b gamma =>
      exact OfcTyReaches.mpInv a b gamma hsize (by
        dsimp [OfcBudgetOK]
        have hdepth : 1 <= depth := by
          simpa [FwdRaw.size] using hsize
        omega)
  | app hf hx ihf ihx =>
      refine OfcTyReaches.app (ihf le_rfl) (ihx le_rfl) ?_ ?_
      · simpa [FwdRaw.size] using hsize
      · dsimp [OfcBudgetOK]
        omega

end OfcTyReaches

theorem ofc_sound {depth hypcnt : Nat} {tau : Formula Atom} {raw : FwdRaw Atom}
    (h : OfcReaches depth hypcnt tau raw) :
    Nonempty (FwdHasType raw (.prop tau)) ∧ FwdRaw.size raw <= depth ∧
      OfcBudgetOK depth hypcnt :=
  OfcTyReaches.sound h

theorem ofc_complete_seed {depth : Nat} {tau : Formula Atom} {raw : FwdRaw Atom}
    (ht : FwdHasType raw (.prop tau)) (hsize : FwdRaw.size raw <= depth) :
    OfcReaches depth 1 tau raw :=
  OfcTyReaches.complete_seed ht hsize

theorem ofc_prune_necessary {depth hypcnt : Nat} {tau : Formula Atom}
    {raw : FwdRaw Atom} (h : OfcReaches depth hypcnt tau raw) :
    OfcBudgetOK depth hypcnt :=
  (ofc_sound h).2.2

theorem ofc_pruned {depth hypcnt : Nat} {tau : Formula Atom}
    {raw : FwdRaw Atom} (hbad : depth + 1 < hypcnt) :
    ¬ OfcReaches depth hypcnt tau raw := by
  intro h
  have hok := ofc_prune_necessary h
  dsimp [OfcBudgetOK] at hok
  omega

theorem ofc_reduces_to_bwd_exists {depth hypcnt : Nat} {tau : Formula Atom}
    {raw : FwdRaw Atom} (h : OfcReaches depth hypcnt tau raw) :
    ∃ p : BwdRaw Atom, BwdHasType p tau := by
  rcases (ofc_sound h).1 with ⟨ht⟩
  exact ⟨reduceRaw raw ht, reduce_type_preserved raw ht⟩

abbrev BoundedBwdProof (Atom : Type u) (n : Nat) (tau : Formula Atom) : Type u :=
  { p : BwdProof Atom tau // BwdProof.size p <= n }

abbrev ForwardSeedTrace (Atom : Type u) (n : Nat) (tau : Formula Atom) : Type u :=
  { raw : BwdRaw Atom //
      BwdHasType raw tau ∧ BwdRaw.size raw <= n ∧
        OfcReaches (n + 1) 1 tau (.bwd raw) }

def forwardSeedProof {tau : Formula Atom} (p : BwdProof Atom tau) :
    FwdProof Atom tau :=
  Sigma.mk (.bwd p.1) (FwdHasType.bwd p.2)

theorem forwardSeed_reduce {tau : Formula Atom} (p : BwdProof Atom tau) :
    reduce (forwardSeedProof p) = p := by
  cases p
  rfl

def bwdForwardSeedEquiv (Atom : Type u) (n : Nat) (tau : Formula Atom) :
    BoundedBwdProof Atom n tau ≃ ForwardSeedTrace Atom n tau where
  toFun := fun p =>
    ⟨p.1.1, p.1.2, p.2, by
      exact OfcTyReaches.bwd p.1.2 (by
        have hs : BwdRaw.size p.1.1 <= n := by
          simpa [BwdProof.size] using p.2
        simp [FwdRaw.size, BwdProof.size]
        omega) (by
        dsimp [OfcBudgetOK]
        omega)⟩
  invFun := fun q => ⟨⟨q.1, q.2.1⟩, q.2.2.1⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro q
    apply Subtype.ext
    rfl

theorem bwdForwardSeedEquiv_reduce {n : Nat} {tau : Formula Atom}
    (p : BoundedBwdProof Atom n tau) :
    reduce (forwardSeedProof p.1) = p.1 :=
  forwardSeed_reduce p.1

namespace Examples

variable {Atom : Type u}

def idBwdRaw (p : Formula Atom) : BwdRaw Atom :=
  .mp
    (.mp (.ax2 p (p ==> p) p) (.ax1 p (p ==> p)))
    (.ax1 p p)

theorem idBwdRaw_typed (p : Formula Atom) :
    BwdHasType (idBwdRaw p) (p ==> p) := by
  exact
    BwdHasType.mp
      (BwdHasType.mp
        (BwdHasType.ax2 p (p ==> p) p)
        (BwdHasType.ax1 p (p ==> p)))
      (BwdHasType.ax1 p p)

def idBwd (p : Formula Atom) : BwdProof Atom (p ==> p) :=
  Subtype.mk (idBwdRaw p) (idBwdRaw_typed p)

theorem badMpAx1Ax1_not_typed
    (p q target : Formula Atom) :
    Not (BwdHasType (.mp (.ax1 p q) (.ax1 p q)) target) := by
  intro h
  cases h with
  | mp hf hx =>
      cases hx
      cases hf

def idSeedRaw (tau : Formula Atom) : FwdRaw Atom :=
  .id (.prop tau)

def idSeedRaw_typed (tau : Formula Atom) :
    FwdHasType (idSeedRaw tau) (.prop tau ~~> .prop tau) :=
  FwdHasType.id (.prop tau)

def mpInvRaw_typed (a b : Formula Atom) (gamma : Ty Atom) :
    FwdHasType (.mpInv a b gamma)
      ((.prop b ~~> gamma) ~~>
        (.prop (a ==> b) ~~> (.prop a ~~> gamma))) :=
  FwdHasType.mpInv a b gamma

theorem badFwdIdApp_not_object_typed
    (p target : Formula Atom) :
    FwdHasType
      (.app (.id (.prop p)) (.id (.prop p)))
      (.prop target) -> False := by
  intro h
  cases h with
  | app hf hx =>
      cases hf
      cases hx

def T (p : Formula Atom) : Formula Atom :=
  p ==> p

def A (p : Formula Atom) : Formula Atom :=
  p ==> T p

def B (p : Formula Atom) : Formula Atom :=
  p ==> (T p ==> p)

def F (p : Formula Atom) : Formula Atom :=
  A p ==> T p

def ax2IdRaw (p : Formula Atom) : BwdRaw Atom :=
  .ax2 p (T p) p

def ax1LeftRaw (p : Formula Atom) : BwdRaw Atom :=
  .ax1 p (T p)

def ax1RightRaw (p : Formula Atom) : BwdRaw Atom :=
  .ax1 p p

def ax2IdFwdRaw (p : Formula Atom) : FwdRaw Atom :=
  .bwd (ax2IdRaw p)

def ax1LeftFwdRaw (p : Formula Atom) : FwdRaw Atom :=
  .bwd (ax1LeftRaw p)

def ax1RightFwdRaw (p : Formula Atom) : FwdRaw Atom :=
  .bwd (ax1RightRaw p)

def ax2IdFwd_typed (p : Formula Atom) :
    FwdHasType (ax2IdFwdRaw p) (.prop (B p ==> F p)) :=
  FwdHasType.bwd (BwdHasType.ax2 p (T p) p)

def ax1LeftFwd_typed (p : Formula Atom) :
    FwdHasType (ax1LeftFwdRaw p) (.prop (B p)) :=
  FwdHasType.bwd (BwdHasType.ax1 p (T p))

def ax1RightFwd_typed (p : Formula Atom) :
    FwdHasType (ax1RightFwdRaw p) (.prop (A p)) :=
  FwdHasType.bwd (BwdHasType.ax1 p p)

def k0Raw (p : Formula Atom) : FwdRaw Atom :=
  .id (.prop (T p))

def k0_typed (p : Formula Atom) :
    FwdHasType (k0Raw p) (.prop (T p) ~~> .prop (T p)) :=
  FwdHasType.id (.prop (T p))

def k1Raw (p : Formula Atom) : FwdRaw Atom :=
  .app (.mpInv (A p) (T p) (.prop (T p))) (k0Raw p)

def k1_typed (p : Formula Atom) :
    FwdHasType (k1Raw p) (.prop (F p) ~~> (.prop (A p) ~~> .prop (T p))) :=
  FwdHasType.app (FwdHasType.mpInv (A p) (T p) (.prop (T p))) (k0_typed p)

def k2Raw (p : Formula Atom) : FwdRaw Atom :=
  .app (.mpInv (B p) (F p) (.prop (A p) ~~> .prop (T p))) (k1Raw p)

def k2_typed (p : Formula Atom) :
    FwdHasType (k2Raw p)
      (.prop (B p ==> F p) ~~> (.prop (B p) ~~> (.prop (A p) ~~> .prop (T p)))) :=
  FwdHasType.app
    (FwdHasType.mpInv (B p) (F p) (.prop (A p) ~~> .prop (T p)))
    (k1_typed p)

def idFwdRaw (p : Formula Atom) : FwdRaw Atom :=
  .app
    (.app
      (.app (k2Raw p) (ax2IdFwdRaw p))
      (ax1LeftFwdRaw p))
    (ax1RightFwdRaw p)

def idFwd_typed (p : Formula Atom) :
    FwdHasType (idFwdRaw p) (.prop (T p)) :=
  FwdHasType.app
    (FwdHasType.app
      (FwdHasType.app (k2_typed p) (ax2IdFwd_typed p))
      (ax1LeftFwd_typed p))
    (ax1RightFwd_typed p)

def idFwd (p : Formula Atom) : FwdProof Atom (T p) :=
  Sigma.mk (idFwdRaw p) (idFwd_typed p)

theorem reduce_idFwd_eq_idBwd (p : Formula Atom) :
    reduce (idFwd p) = idBwd p := by
  rfl

def mpAx2Raw (p : Formula Atom) : FwdRaw Atom :=
  .app (.mpConst (B p) (F p)) (ax2IdFwdRaw p)

def mpAx2_typed (p : Formula Atom) :
    FwdHasType (mpAx2Raw p) (.prop (B p) ~~> .prop (F p)) :=
  FwdHasType.app (FwdHasType.mpConst (B p) (F p)) (ax2IdFwd_typed p)

def blueLiftCoreRaw (p : Formula Atom) : FwdRaw Atom :=
  .app
    (.app
      (.app (.blue (.prop (B p)) (.prop (F p)) (.prop (A p) ~~> .prop (T p)))
        (k1Raw p))
      (mpAx2Raw p))
    (ax1LeftFwdRaw p)

def blueLiftCore_typed (p : Formula Atom) :
    FwdHasType (blueLiftCoreRaw p) (.prop (A p) ~~> .prop (T p)) :=
  FwdHasType.app
    (FwdHasType.app
      (FwdHasType.app
        (FwdHasType.blue (.prop (B p)) (.prop (F p)) (.prop (A p) ~~> .prop (T p)))
        (k1_typed p))
      (mpAx2_typed p))
    (ax1LeftFwd_typed p)

def blueLiftFwdRaw (p : Formula Atom) : FwdRaw Atom :=
  .app (blueLiftCoreRaw p) (ax1RightFwdRaw p)

def blueLiftFwd_typed (p : Formula Atom) :
    FwdHasType (blueLiftFwdRaw p) (.prop (T p)) :=
  FwdHasType.app (blueLiftCore_typed p) (ax1RightFwd_typed p)

def blueLiftFwd (p : Formula Atom) : FwdProof Atom (T p) :=
  Sigma.mk (blueLiftFwdRaw p) (blueLiftFwd_typed p)

theorem reduce_blueLiftFwd_eq_idBwd (p : Formula Atom) :
    reduce (blueLiftFwd p) = idBwd p := by
  rfl

theorem idBwd_obc_reaches (p : Formula Atom) :
    ObcReaches (BwdProof.size (idBwd p)) (T p) (idBwdRaw p) :=
  ObcReaches.complete (idBwdRaw_typed p) le_rfl

theorem idBwd_not_obc_budget4 (p : Formula Atom) :
    ¬ ObcReaches 4 (T p) (idBwdRaw p) := by
  intro h
  have hsize := (ObcReaches.sound h).2
  simp [idBwdRaw, BwdRaw.size] at hsize

theorem idFwd_ofc_reaches (p : Formula Atom) :
    OfcReaches (FwdRaw.size (idFwdRaw p)) 1 (T p) (idFwdRaw p) :=
  ofc_complete_seed (idFwd_typed p) le_rfl

theorem idFwd_pruned_hypcnt_not_reached (p : Formula Atom) :
    ¬ OfcReaches (FwdRaw.size (idFwdRaw p))
      (FwdRaw.size (idFwdRaw p) + 2) (T p) (idFwdRaw p) := by
  exact ofc_pruned (by omega)

theorem forward_reduce_not_injective (p : Formula Atom) :
    reduce (idFwd p) = reduce (blueLiftFwd p) ∧
      idFwdRaw p ≠ blueLiftFwdRaw p := by
  constructor
  · rw [reduce_idFwd_eq_idBwd, reduce_blueLiftFwd_eq_idBwd]
  · intro h
    simp [idFwdRaw, blueLiftFwdRaw, k2Raw, blueLiftCoreRaw] at h

theorem idBwd_forwardSeed_roundtrip (p : Formula Atom) :
    ((bwdForwardSeedEquiv Atom (BwdProof.size (idBwd p)) (T p)).symm
      ((bwdForwardSeedEquiv Atom (BwdProof.size (idBwd p)) (T p))
        ⟨idBwd p, le_rfl⟩)) = ⟨idBwd p, le_rfl⟩ := by
  simp

end Examples

namespace PureKernelCanary

def formulaName : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.Formula
def impName : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.Formula.imp
def negName : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.Formula.neg
def proofName : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.BwdProof
def ax1Name : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.BwdProof.ax1
def ax2Name : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.BwdProof.ax2
def ax3Name : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.BwdProof.ax3
def mpName : DeclName := `Mettapedia.Logic.LP.BackwardViaForwardMP.BwdProof.mp

def formulaTm : PureTm n := .const formulaName
def impTm (a b : PureTm n) : PureTm n := .app (.app (.const impName) a) b
def negTm (a : PureTm n) : PureTm n := .app (.const negName) a
def proofTm : PureTm n := .const proofName
def proofTy (phi : PureTm n) : PureTm n := .app proofTm phi

def formulaSpec : DeclSpec :=
  { name := formulaName, type := .u0 }

def impSpec : DeclSpec :=
  { name := impName, type := .pi formulaTm (.pi formulaTm formulaTm) }

def negSpec : DeclSpec :=
  { name := negName, type := .pi formulaTm formulaTm }

def proofSpec : DeclSpec :=
  { name := proofName, type := .pi formulaTm .u0 }

def ax1Type : PureTm 0 :=
  .pi formulaTm
    (.pi formulaTm
      (proofTy (impTm (.var 1) (impTm (.var 0) (.var 1)))))

def ax2Type : PureTm 0 :=
  .pi formulaTm
    (.pi formulaTm
      (.pi formulaTm
        (proofTy
          (impTm
            (impTm (.var 2) (impTm (.var 1) (.var 0)))
            (impTm
              (impTm (.var 2) (.var 1))
              (impTm (.var 2) (.var 0)))))))

def ax3Type : PureTm 0 :=
  .pi formulaTm
    (.pi formulaTm
      (proofTy
        (impTm
          (impTm (negTm (.var 1)) (negTm (.var 0)))
          (impTm (.var 0) (.var 1)))))

def mpType : PureTm 0 :=
  .pi formulaTm
    (.pi formulaTm
      (.pi (proofTy (impTm (.var 1) (.var 0)))
        (.pi (proofTy (.var 2))
          (proofTy (.var 2)))))

def ax1Spec : DeclSpec := { name := ax1Name, type := ax1Type }
def ax2Spec : DeclSpec := { name := ax2Name, type := ax2Type }
def ax3Spec : DeclSpec := { name := ax3Name, type := ax3Type }
def mpSpec : DeclSpec := { name := mpName, type := mpType }

def specs : List DeclSpec :=
  [ formulaSpec
  , impSpec
  , negSpec
  , proofSpec
  , ax1Spec
  , ax2Spec
  , ax3Spec
  , mpSpec
  ]

def declEnv : DeclEnv :=
  envOfSpecs specs

@[simp] theorem typeOf_formula :
    typeOf? declEnv formulaName = some .u0 := by
  decide

@[simp] theorem typeOf_proof :
    typeOf? declEnv proofName = some (.pi formulaTm .u0) := by
  decide

@[simp] theorem typeOf_imp :
    typeOf? declEnv impName = some (.pi formulaTm (.pi formulaTm formulaTm)) := by
  decide

@[simp] theorem typeOf_ax1 :
    typeOf? declEnv ax1Name = some ax1Type := by
  decide

@[simp] theorem typeOf_ax2 :
    typeOf? declEnv ax2Name = some ax2Type := by
  decide

@[simp] theorem typeOf_mp :
    typeOf? declEnv mpName = some mpType := by
  decide

theorem hasType_formula :
    HasTypeDecl declEnv .nil (.const formulaName) .u0 :=
  hasType_const_from_lookup
    (E := declEnv) (c := formulaName) (A0 := .u0) (by
      simp)

theorem hasType_proof :
    HasTypeDecl declEnv .nil (.const proofName) (.pi formulaTm .u0) :=
  hasType_const_from_lookup
    (E := declEnv) (c := proofName) (A0 := .pi formulaTm .u0) (by
      simp)

theorem hasType_imp :
    HasTypeDecl declEnv .nil (.const impName) (.pi formulaTm (.pi formulaTm formulaTm)) :=
  hasType_const_from_lookup
    (E := declEnv) (c := impName) (A0 := .pi formulaTm (.pi formulaTm formulaTm)) (by
      simp)

theorem hasType_ax1 :
    HasTypeDecl declEnv .nil (.const ax1Name) ax1Type :=
  hasType_const_from_lookup
    (E := declEnv) (c := ax1Name) (A0 := ax1Type) (by
      simp)

theorem hasType_ax2 :
    HasTypeDecl declEnv .nil (.const ax2Name) ax2Type :=
  hasType_const_from_lookup
    (E := declEnv) (c := ax2Name) (A0 := ax2Type) (by
      simp)

theorem hasType_mp :
    HasTypeDecl declEnv .nil (.const mpName) mpType :=
  hasType_const_from_lookup
    (E := declEnv) (c := mpName) (A0 := mpType) (by
      simp)

end PureKernelCanary

end Mettapedia.Logic.LP.BackwardViaForwardMP
