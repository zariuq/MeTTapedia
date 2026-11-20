import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyVectors

/-!
# The dependent eliminator of vectors as a declared family

The eliminator of the declared family of vectors,

`vec-elim : Π (A : U) (P : Π (n : num). vec A n → V) (mn : P zero (vnil A))
    (mc : Π (m : num) (x : A) (xs : vec A m). P m xs → P (succ m) (vcons A m x xs))
    (n : num) (t : vec A n). P n t`,

with its two computation rules, which ignore the parameter the constructor stores:

* `vec-elim A P mn mc n (vnil A') ⟶ mn`;
* `vec-elim A P mn mc n (vcons A' m x xs) ⟶ mc m x xs (vec-elim A P mn mc m xs)`.

The rules form a root computation of the framework (`vecIota`): they are closed under
renaming and substitution. They are steps of a computing constant of arity six that inspects
its last argument for a constructor (`vecIota_spine`), and they are deterministic
(`vecIota_deterministic`), which are the two obligations of `RootShape`.

What waits for the family case of the relation is the preservation of typing by these rules:
the redex is typed at `P n (vcons A' m x xs)` and the reduct at `P (succ m) (vcons A m x xs)`,
and relating the two types needs `A' ≡ A` and `n ≡ succ m` from the typing of the scrutinee,
that is, injectivity of `vec`, which is a consequence of normalization with families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace FamilyVectorsEliminator

open FamilyVectors

/-- The eliminator of vectors. -/
def vecElim : DeclName := .mkSimple "vec-elim"

theorem vnil_ne_vcons' : FamilyVectors.vnil ≠ FamilyVectors.vcons := by decide

variable {Head : Type}

/-! ## The declared type -/

/-- The motive type `Π (n : num). vec A n → V`, over `A`. -/
def motiveType (v : Head) : Tm Head 1 :=
  .pi (.const num) (.pi (.app (.app (.const vec) (.var 1)) (.var 0)) (.head v))

/-- The method for `vnil`: `P zero (vnil A)`, over `A, P`. -/
def nilMethodType : Tm Head 2 :=
  .app (.app (.var 0) (.const zero)) (.app (.const vnil) (.var 1))

/-- The method for `vcons`: `Π (m : num) (x : A) (xs : vec A m). P m xs →
P (succ m) (vcons A m x xs)`, over `A, P, mn`. -/
def consMethodType : Tm Head 3 :=
  .pi (.const num) (.pi (.var 3) (.pi (.app (.app (.const vec) (.var 4)) (.var 1))
    (.pi (.app (.app (.var 4) (.var 2)) (.var 0))
      (.app (.app (.var 5) (.app (.const succ) (.var 3)))
        (appSpine (.const vcons) [.var 6, .var 3, .var 2, .var 1])))))

/-- The declared type of the eliminator into the universe `v`, for vectors over types of
the universe `u`. -/
def elimType (u v : Head) : Tm Head 0 :=
  .pi (.head u) (.pi (motiveType v) (.pi nilMethodType (.pi consMethodType
    (.pi (.const num) (.pi (.app (.app (.const vec) (.var 4)) (.var 0))
      (.app (.app (.var 4) (.var 1)) (.var 0)))))))

/-! ## The computation rules -/

/-- The two computation rules of the eliminator. -/
inductive VecIota : {n : Nat} → Tm Head n → Tm Head n → Prop where
  | vnil {n : Nat} (A P mn mc len A' : Tm Head n) :
      VecIota (appSpine (.const vecElim) [A, P, mn, mc, len, .app (.const vnil) A']) mn
  | vcons {n : Nat} (A P mn mc len A' m x xs : Tm Head n) :
      VecIota (appSpine (.const vecElim) [A, P, mn, mc, len, appSpine (.const vcons) [A', m, x, xs]])
        (appSpine mc [m, x, xs, appSpine (.const vecElim) [A, P, mn, mc, m, xs]])

theorem VecIota.rename {n m : Nat} (ρ : Ren n m) :
    ∀ {l r : Tm Head n}, VecIota l r → VecIota (Presentation.rename ρ l) (Presentation.rename ρ r)
  | _, _, .vnil A P mn mc len A' => by
      simpa only [rename_appSpine, List.map_cons, List.map_nil, Presentation.rename] using
        VecIota.vnil (Presentation.rename ρ A) (Presentation.rename ρ P) (Presentation.rename ρ mn)
          (Presentation.rename ρ mc) (Presentation.rename ρ len) (Presentation.rename ρ A')
  | _, _, .vcons A P mn mc len A' x₁ x₂ x₃ => by
      simpa only [rename_appSpine, List.map_cons, List.map_nil, Presentation.rename] using
        VecIota.vcons (Presentation.rename ρ A) (Presentation.rename ρ P) (Presentation.rename ρ mn)
          (Presentation.rename ρ mc) (Presentation.rename ρ len) (Presentation.rename ρ A')
          (Presentation.rename ρ x₁) (Presentation.rename ρ x₂) (Presentation.rename ρ x₃)

theorem VecIota.subst {n m : Nat} (σ : Sub Head n m) :
    ∀ {l r : Tm Head n}, VecIota l r → VecIota (Presentation.subst σ l) (Presentation.subst σ r)
  | _, _, .vnil A P mn mc len A' => by
      simpa only [subst_appSpine, List.map_cons, List.map_nil, Presentation.subst] using
        VecIota.vnil (Presentation.subst σ A) (Presentation.subst σ P) (Presentation.subst σ mn)
          (Presentation.subst σ mc) (Presentation.subst σ len) (Presentation.subst σ A')
  | _, _, .vcons A P mn mc len A' x₁ x₂ x₃ => by
      simpa only [subst_appSpine, List.map_cons, List.map_nil, Presentation.subst] using
        VecIota.vcons (Presentation.subst σ A) (Presentation.subst σ P) (Presentation.subst σ mn)
          (Presentation.subst σ mc) (Presentation.subst σ len) (Presentation.subst σ A')
          (Presentation.subst σ x₁) (Presentation.subst σ x₂) (Presentation.subst σ x₃)

/-- **The computation rules of the eliminator as a root computation of the framework.** -/
def vecIota : RootComputation Head where
  step := VecIota
  rename := fun ρ _ _ step => step.rename ρ
  substitute := fun σ _ _ step => step.subst σ

/-! ## The obligations of `RootShape` -/

section Shape

variable {roles : Roles Head}

/-- Every rule is a step of the eliminator applied to exactly its six arguments, whose last
argument is a constructor form. -/
theorem vecIota_spine (hElim : roles vecElim = .computes 6 (.split 5 .constructor fun _ => .leaf))
    (hNil : roles vnil = .constructor 1) (hCons : roles vcons = .constructor 4)
    {n : Nat} : ∀ {l r : Tm Head n}, VecIota l r →
      ∃ c arity inspect args, roles c = .computes arity inspect ∧ l = appSpine (.const c) args ∧
        args.length = arity ∧ inspect.Accepts roles args
  | _, _, .vnil _ _ _ _ _ A' =>
      ⟨vecElim, 6, _, _, hElim, rfl, rfl,
        InspectTree.accepts_single.mpr ⟨_, rfl, .inr ⟨vnil, 1, [A'], hNil, rfl⟩⟩⟩
  | _, _, .vcons _ _ _ _ _ A' x₁ x₂ x₃ =>
      ⟨vecElim, 6, _, _, hElim, rfl, rfl,
        InspectTree.accepts_single.mpr ⟨_, rfl, .inr ⟨vcons, 4, [A', x₁, x₂, x₃], hCons, rfl⟩⟩⟩

/-- A default term, for positions outside a list. -/
def junk {n : Nat} : Tm Head n := .const .anonymous

/-- The rule at `vnil` gives the method for `vnil`. -/
theorem vnil_reduct {n : Nat} {A P mn mc len A' r : Tm Head n}
    (step : VecIota (appSpine (.const vecElim) [A, P, mn, mc, len, .app (.const vnil) A']) r) :
    r = mn := by
  generalize hl : appSpine (.const vecElim) [A, P, mn, mc, len, .app (.const vnil) A'] = l
    at step
  cases step with
  | vnil A₂ P₂ mn₂ mc₂ len₂ A₂' =>
      have args := (appSpine_const_injective hl).2
      exact (congrArg (fun l => l.getD 2 junk) args).symm
  | vcons A₂ P₂ mn₂ mc₂ len₂ A₂' m₂ x₂ xs₂ =>
      have args := (appSpine_const_injective hl).2
      have last : Tm.app (.const vnil) A' = appSpine (.const vcons) [A₂', m₂, x₂, xs₂] :=
        congrArg (fun l => l.getD 5 junk) args
      exact absurd (appSpine_const_injective (as := [A']) last).1 vnil_ne_vcons'

/-- The rule at `vcons` gives the method for `vcons` at the fields and the recursive call. -/
theorem vcons_reduct {n : Nat} {A P mn mc len A' m x xs r : Tm Head n}
    (step : VecIota (appSpine (.const vecElim)
      [A, P, mn, mc, len, appSpine (.const vcons) [A', m, x, xs]]) r) :
    r = appSpine mc [m, x, xs, appSpine (.const vecElim) [A, P, mn, mc, m, xs]] := by
  generalize hl : appSpine (.const vecElim)
    [A, P, mn, mc, len, appSpine (.const vcons) [A', m, x, xs]] = l at step
  cases step with
  | vnil A₂ P₂ mn₂ mc₂ len₂ A₂' =>
      have args := (appSpine_const_injective hl).2
      have last : appSpine (.const vcons) [A', m, x, xs] = Tm.app (.const vnil) A₂' :=
        congrArg (fun l => l.getD 5 junk) args
      exact absurd (appSpine_const_injective (bs := [A₂']) last).1 (Ne.symm vnil_ne_vcons')
  | vcons A₂ P₂ mn₂ mc₂ len₂ A₂' m₂ x₂ xs₂ =>
      have args := (appSpine_const_injective hl).2
      have e0 : A = A₂ := congrArg (fun l => l.getD 0 junk) args
      have e1 : P = P₂ := congrArg (fun l => l.getD 1 junk) args
      have e2 : mn = mn₂ := congrArg (fun l => l.getD 2 junk) args
      have e3 : mc = mc₂ := congrArg (fun l => l.getD 3 junk) args
      have last : appSpine (.const vcons) [A', m, x, xs] =
          appSpine (.const vcons) [A₂', m₂, x₂, xs₂] :=
        congrArg (fun l => l.getD 5 junk) args
      have inner := (appSpine_const_injective last).2
      have f1 : m = m₂ := congrArg (fun l => l.getD 1 junk) inner
      have f2 : x = x₂ := congrArg (fun l => l.getD 2 junk) inner
      have f3 : xs = xs₂ := congrArg (fun l => l.getD 3 junk) inner
      subst e0 e1 e2 e3 f1 f2 f3
      rfl

/-- The computation rules are deterministic. -/
theorem vecIota_deterministic {n : Nat} :
    ∀ {l r r' : Tm Head n}, VecIota l r → VecIota l r' → r = r'
  | _, _, _, .vnil _ _ _ _ _ _, step' => (vnil_reduct step').symm
  | _, _, _, .vcons _ _ _ _ _ _ _ _ _, step' => (vcons_reduct step').symm

end Shape

end FamilyVectorsEliminator
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
