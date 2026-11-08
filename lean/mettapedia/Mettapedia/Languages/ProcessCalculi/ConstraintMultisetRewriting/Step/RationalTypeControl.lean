import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalControls
import Mathlib.Logic.Relation

/-!
# Control: rational trees as types break normalization

Rational trees are for object terms and data. This control shows what goes wrong if they are used
as types. Curry's simple typing (`HasType`) is stated over any algebra of types with an arrow.

* Over finite types (`Term`, with `arrowT`), self-application `λx. x x` has no type
  (`selfApplication_untypable`): its typing needs `A = A → B`, which the occurs check refutes.
* Over rational types it has one: `T = T → T` is the rational tree `→(→(…), →(…))` (`loop .arrow`),
  and `Ω = (λx. x x)(λx. x x)` has type `T` (`omega_typable`).
* `Ω` has no normal form: its only reduct is itself (`omega_step`, `omega_no_normal_form`).

So normalization of typable terms, a theorem for simple types over finite trees (not proved here),
fails over rational types. Type syntax keeps its occurs check; the rational-tree fibre is a profile
for object terms only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls

open Mettapedia.Logic.LP
open Raw (node bot)

/-- Untyped λ-terms, with de Bruijn indices. -/
inductive Lam where
  | var (n : ℕ)
  | app (t u : Lam)
  | lam (t : Lam)

namespace Lam

/-- Lift the free indices from `c` on by one. -/
def shift (c : ℕ) : Lam → Lam
  | var n => if n < c then var n else var (n + 1)
  | app t u => app (shift c t) (shift c u)
  | lam t => lam (shift (c + 1) t)

/-- Substitute `s` for index `j`, lowering the indices above it. -/
def substAt (j : ℕ) (s : Lam) : Lam → Lam
  | var n => if n = j then s else if j < n then var (n - 1) else var n
  | app t u => app (substAt j s t) (substAt j s u)
  | lam t => lam (substAt (j + 1) (shift 0 s) t)

/-- One step of β-reduction, anywhere in a term. -/
inductive Beta : Lam → Lam → Prop
  | beta (t u : Lam) : Beta (app (lam t) u) (substAt 0 u t)
  | appL {t t' u : Lam} : Beta t t' → Beta (app t u) (app t' u)
  | appR {t u u' : Lam} : Beta u u' → Beta (app t u) (app t u')
  | lam {t t' : Lam} : Beta t t' → Beta (lam t) (lam t')

/-- `λx. x x`. -/
def self : Lam := lam (app (var 0) (var 0))

/-- `Ω = (λx. x x)(λx. x x)`. -/
def omega : Lam := app self self

end Lam

open Lam

/-- **Curry's simple typing** over an algebra of types with an arrow. -/
inductive HasType {Ty : Type*} (arrow : Ty → Ty → Ty) : List Ty → Lam → Ty → Prop
  | var {Γ : List Ty} {n : ℕ} {A : Ty} : Γ[n]? = some A → HasType arrow Γ (.var n) A
  | app {Γ : List Ty} {t u : Lam} {A B : Ty} : HasType arrow Γ t (arrow A B) → HasType arrow Γ u A →
      HasType arrow Γ (.app t u) B
  | lam {Γ : List Ty} {t : Lam} {A B : Ty} : HasType arrow (A :: Γ) t B →
      HasType arrow Γ (.lam t) (arrow A B)

/-! ## Finite types -/

/-- **Over finite types, self-application has no type.** -/
theorem selfApplication_untypable (Γ : List (Term ctlSig)) (A : Term ctlSig) :
    ¬ HasType arrowT Γ self A := by
  intro typed
  cases typed with
  | lam body =>
    rename_i A' B
    cases body with
    | app fn arg =>
      rename_i C
      cases fn with
      | var found =>
        cases arg with
        | var found' =>
          have first : A' = arrowT C B := Option.some.inj found
          have second : A' = C := Option.some.inj found'
          rw [second] at first
          have smaller := Term.size_subterm (f := Sym.arrow)
            (ts := fun i => if i.val = 0 then C else B) ⟨0, by decide⟩
          have cyclic : C = Term.app Sym.arrow fun i => if i.val = 0 then C else B := first
          rw [← cyclic] at smaller
          exact lt_irrefl _ smaller

/-! ## Rational types -/

/-- The arrow of rational trees. -/
def rarrow (a b : RTree ctlSig) : RTree ctlSig :=
  ⟨node (.fn Sym.arrow) (fun i => if i = 0 then a.1 else b.1),
    Raw.wf_node fun i _ => by split_ifs; exacts [a.2.1, b.2.1],
    Raw.rational_node fun i _ => by split_ifs; exacts [a.2.2, b.2.2]⟩

/-- **The rational type `T = T → T`.** -/
theorem loop_arrow_fixed : rarrow (loop .arrow) (loop .arrow) = loop .arrow := by
  refine RTree.ext ((Raw.node_congr fun i _ => ?_).trans (loop_eq .arrow).symm)
  split_ifs <;> rfl

/-- **Over rational types, `Ω` has the type `T = T → T`.** -/
theorem omega_typable : HasType rarrow [] omega (loop .arrow) := by
  have var0 : HasType rarrow [loop .arrow] (.var 0) (loop .arrow) := .var rfl
  have var0' : HasType rarrow [loop .arrow] (.var 0) (rarrow (loop .arrow) (loop .arrow)) := by
    rw [loop_arrow_fixed]
    exact var0
  have selfTyped : HasType rarrow [] self (rarrow (loop .arrow) (loop .arrow)) := .lam (.app var0' var0)
  have selfTyped' : HasType rarrow [] self (loop .arrow) := by
    rw [← loop_arrow_fixed]
    exact selfTyped
  exact .app selfTyped selfTyped'

/-! ## `Ω` has no normal form -/

theorem self_irreducible (t : Lam) : ¬ Lam.Beta self t := by
  intro step
  cases step with
  | lam body =>
    cases body with
    | appL inner => cases inner
    | appR inner => cases inner

/-- **`Ω` reduces only to itself.** -/
theorem omega_step (t : Lam) : Lam.Beta omega t ↔ t = omega := by
  constructor
  · intro step
    cases step with
    | beta => rfl
    | appL inner => exact absurd inner (self_irreducible _)
    | appR inner => exact absurd inner (self_irreducible _)
  · rintro rfl
    exact Lam.Beta.beta (app (var 0) (var 0)) self

/-- **`Ω` has no normal form**: everything it reduces to reduces further. -/
theorem omega_no_normal_form (t : Lam) (reached : Relation.ReflTransGen Lam.Beta omega t) :
    ∃ u, Lam.Beta t u := by
  have stays : t = omega := by
    induction reached with
    | refl => rfl
    | tail _ step ih =>
      subst ih
      exact (omega_step _).mp step
  subst stays
  exact ⟨omega, (omega_step omega).mpr rfl⟩

/-- **A cyclic type breaks normalization**: self-application is untypable over finite types, while
over rational types `Ω` is typable and has no normal form. -/
theorem cyclic_type_breaks_normalization :
    (∀ (Γ : List (Term ctlSig)) (A : Term ctlSig), ¬ HasType arrowT Γ self A) ∧
      HasType rarrow [] omega (loop .arrow) ∧
      ∀ t, Relation.ReflTransGen Lam.Beta omega t → ∃ u, Lam.Beta t u :=
  ⟨selfApplication_untypable, omega_typable, omega_no_normal_form⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Controls.selfApplication_untypable
#print axioms Rational.Controls.omega_typable
#print axioms Rational.Controls.omega_step
#print axioms Rational.Controls.omega_no_normal_form
#print axioms Rational.Controls.cyclic_type_breaks_normalization

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
