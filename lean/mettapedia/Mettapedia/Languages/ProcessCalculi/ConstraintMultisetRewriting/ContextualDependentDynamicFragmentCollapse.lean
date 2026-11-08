import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingCertify
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRigidRefutation

/-!
# Pattern occurrences collapse to renamings

An application spine is written innermost argument first: `appsRev t [aₖ, …, a₁] = t a₁ … aₖ`, and
`lamsRev [aₖ, …, a₁] b` abstracts one binder for each argument. Applying an abstraction to as many
arguments as it has binders reduces, by β, to the body under the **spine substitution** that sends
the binders to the arguments.

When the arguments are distinct variables and the body only mentions its binders and variables
reached through an injective renaming that avoids them, the spine substitution is an injective
renaming. So instantiating a metavariable by a pattern solution `λ z̄. u` turns every occurrence
`F ȳ` into a renaming of `u`: normal when `u` is, by renaming invariance of normality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDynamicFragment

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentExecutableJoin

variable {Head : Type}

/-! ## Variable spines and abstractions -/

/-- `appsVar t [yₖ, …, y₁] = t y₁ … yₖ`: a head applied to variables, innermost first. -/
def appsVar {n : Nat} (head : Tm Head n) : List (Fin n) → Tm Head n
  | [] => head
  | argument :: rest => .app (appsVar head rest) (.var argument)

/-- One abstraction for each argument of the list. -/
def lamsVar {n : Nat} : (count : Nat) → Tm Head (n + count) → Tm Head n
  | 0, body => body
  | count + 1, body => lamsVar count (.lam body)

/-- **The spine substitution**: the binders go to the arguments, the outer variables stay. -/
def spineSub {n : Nat} : (arguments : List (Fin n)) → Sub Head (n + arguments.length) n
  | [] => ids
  | argument :: rest => Fin.cases (.var argument) (spineSub rest)

/-- Substituting a variable spine whose arguments go to variables. -/
theorem subst_appsVar {n m : Nat} (σ : Sub Head n m) (ρ : Ren n m) (head : Tm Head n) :
    ∀ arguments : List (Fin n), (∀ argument ∈ arguments, σ argument = .var (ρ argument)) →
      subst σ (appsVar head arguments) = appsVar (subst σ head) (arguments.map ρ)
  | [], _ => rfl
  | argument :: rest, onVariables => by
      simp only [appsVar, subst, List.map_cons]
      rw [subst_appsVar σ ρ head rest (fun other member => onVariables other (List.mem_cons_of_mem _ member)),
        onVariables argument List.mem_cons_self]

theorem rename_appsVar {n m : Nat} (ρ : Ren n m) (head : Tm Head n) :
    ∀ arguments : List (Fin n), rename ρ (appsVar head arguments) = appsVar (rename ρ head) (arguments.map ρ)
  | [] => rfl
  | argument :: rest => by simp only [appsVar, rename, rename_appsVar ρ head rest, List.map_cons]

/-- Opening the newest binder of a lifted substitution extends the substitution. -/
theorem inst0_subst_liftSub {n m : Nat} (σ : Sub Head n m) (argument : Tm Head m) (body : Tm Head (n + 1)) :
    inst0 argument (subst (liftSub σ) body) = subst (Fin.cases argument σ) body := by
  rw [inst0, subst_subComp]
  apply subst_ext
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · change subst (subst0 argument) (rename wk (σ prior)) = σ prior
    exact inst0_rename_wk argument (σ prior)

variable {R : Rules Head}

theorem star_lam {n : Nat} {b b' : Tm Head (n + 1)} (steps : Star (R := R) b b') :
    Star (R := R) (.lam b) (.lam b') :=
  star_map (fun b => Tm.lam b) (fun step => .congLam step) steps

theorem star_pair {n : Nat} {a a' b b' : Tm Head n} (first : Star (R := R) a a') (second : Star (R := R) b b') :
    Star (R := R) (.pair a b) (.pair a' b') :=
  (star_map (fun a => Tm.pair a b) (fun step => .congPairFst step) first).trans
    (star_map (fun b => Tm.pair a' b) (fun step => .congPairSnd step) second)

/-- **β along a spine**: an abstraction applied to as many variables as it has binders reduces to
its body under the spine substitution. -/
theorem collapse {n : Nat} :
    ∀ (arguments : List (Fin n)) (body : Tm Head (n + arguments.length)),
      Star (R := R) (appsVar (lamsVar arguments.length body) arguments) (subst (spineSub arguments) body)
  | [], body => by
      simp only [appsVar, spineSub, subst_ids]
      exact .refl
  | argument :: rest, body => by
      have inner := collapse rest (.lam body)
      have contracted : Star (R := R) (.app (.lam (subst (liftSub (spineSub rest)) body)) (.var argument))
          (inst0 (.var argument) (subst (liftSub (spineSub rest)) body)) :=
        Relation.ReflTransGen.single (.betaPi _ _)
      rw [inst0_subst_liftSub] at contracted
      exact (star_app inner .refl).trans contracted

/-! ## Variable spines are renamings -/

/-- The renaming that sends the binders to the arguments and the body's outer variables through
`outer`. -/
def combined {n m : Nat} (outer : Ren m n) : (arguments : List (Fin n)) → Ren (m + arguments.length) n
  | [] => outer
  | argument :: rest => Fin.cases argument (combined outer rest)

/-- Lift a renaming under as many binders as there are arguments. -/
def liftRenK {n m : Nat} : (count : Nat) → Ren m n → Ren (m + count) (n + count)
  | 0, outer => outer
  | count + 1, outer => liftRen (liftRenK count outer)

theorem spineSub_liftRenK {n m : Nat} (outer : Ren m n) :
    ∀ (arguments : List (Fin n)) (index : Fin (m + arguments.length)),
      spineSub (Head := Head) arguments (liftRenK arguments.length outer index) = .var (combined outer arguments index)
  | [], index => rfl
  | argument :: rest, index => by
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · exact spineSub_liftRenK outer rest prior

/-- **Pattern occurrences collapse to renamings**: `(λ z̄. u↑) ȳ` reduces to `u` renamed by
`combined`: the binders to the arguments, the outer variables through `outer`. -/
theorem collapse_rename {n m : Nat} (outer : Ren m n) (arguments : List (Fin n))
    (body : Tm Head (m + arguments.length)) :
    Star (R := R) (appsVar (lamsVar arguments.length (rename (liftRenK arguments.length outer) body)) arguments)
      (rename (combined outer arguments) body) := by
  have reduced := collapse (R := R) arguments (rename (liftRenK arguments.length outer) body)
  rw [subst_rename] at reduced
  have same : subst (fun index => spineSub arguments (liftRenK arguments.length outer index)) body =
      rename (combined outer arguments) body := by
    rw [← subst_renSub]
    exact subst_ext (fun index => spineSub_liftRenK outer arguments index) body
  rw [same] at reduced
  exact reduced

theorem combined_avoids {n m : Nat} (outer : Ren m n) : ∀ (arguments : List (Fin n)) (argument : Fin n),
    argument ∉ arguments → (∀ index, outer index ≠ argument) → ∀ index, combined outer arguments index ≠ argument
  | [], _, _, avoids, index => avoids index
  | first :: rest, argument, missing, avoids, index => by
      refine Fin.cases ?_ (fun prior => ?_) index
      · intro same
        exact missing (same ▸ List.mem_cons_self)
      · exact combined_avoids outer rest argument (fun member => missing (List.mem_cons_of_mem _ member)) avoids prior

/-- The combined map is injective when the arguments are distinct and avoid the image of the
injective outer renaming. -/
theorem combined_injective {n m : Nat} {outer : Ren m n} (injective : Function.Injective outer) :
    ∀ (arguments : List (Fin n)), arguments.Nodup → (∀ argument ∈ arguments, ∀ index, outer index ≠ argument) →
      Function.Injective (combined outer arguments)
  | [], _, _ => injective
  | argument :: rest, distinct, avoids => by
      have restInjective := combined_injective injective rest (List.nodup_cons.mp distinct).2
        (fun other member => avoids other (List.mem_cons_of_mem _ member))
      have fresh : ∀ index, combined outer rest index ≠ argument :=
        combined_avoids outer rest argument (List.nodup_cons.mp distinct).1 (avoids argument List.mem_cons_self)
      intro first second same
      rcases Fin.eq_zero_or_eq_succ first with rfl | ⟨first, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ second with rfl | ⟨second, rfl⟩
      · rfl
      · exact absurd same.symm (fresh second)
      · exact absurd same (fresh first)
      · exact congrArg Fin.succ (restInjective same)

end ContextualDependentDynamicFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
