import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRealizers
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Comparison

/-!
# The root steps of the object package, constant by constant

A root step of the object package at a spine of a constant other than `holds`
is a step of that constant's own computation: the decoder rewrites only
`holds`, and every listed computation rewrites only applications of its
constant. So each computing constant steps only as its equations say:

* addition at `zero` returns its first argument, and at `suc m` the successor
  of the sum with `m`;
* the iterated power set at `zero` returns its set, and at `suc m` the power set
  of the iterate at `m`;
* the recursor at `zero` returns its value at zero, and at `suc m` the step
  applied to `m` and the recursive call;
* identity elimination steps only at reflexivity, to its method;
* the iterator at `zero` pairs its value with its evidence, and at `suc m` makes
  one shared use of the step, then iterates `m` times;
* a definition by one equation steps only to its right-hand side.

The computing constants keep their roles in the object package
(`objectRoles_add`, `objectRoles_eqAt`, …).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName iterName eqAtName sucMoveName keepName transportName composeName
  returnIterName sucStepName numRecApp jApp iterPartial)

namespace CodeModel

/-! ## The roles of the computing constants -/

theorem objectRoles_add : objectRoles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_add nofun

theorem objectRoles_pow : objectRoles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_pow nofun

theorem objectRoles_eqAt : objectRoles eqAtName = .computes 1 .leaf :=
  objectRoles_of_roles roles_eqAt nofun

theorem objectRoles_sucMove : objectRoles sucMoveName = .computes 2 .leaf :=
  objectRoles_of_roles roles_sucMove nofun

theorem objectRoles_keep : objectRoles keepName = .computes 4 .leaf :=
  objectRoles_of_roles roles_keep nofun

theorem objectRoles_transport : objectRoles transportName = .computes 6 .leaf :=
  objectRoles_of_roles roles_transport nofun

theorem objectRoles_compose : objectRoles composeName = .computes 6 .leaf :=
  objectRoles_of_roles roles_compose nofun

theorem objectRoles_returnIter : objectRoles returnIterName = .computes 1 .leaf :=
  objectRoles_of_roles roles_returnIter nofun

theorem objectRoles_sucStep : objectRoles sucStepName = .computes 2 .leaf :=
  objectRoles_of_roles roles_sucStep nofun

/-! ## Root steps -/

/-- A root step of the object package at a spine of a listed constant other
than `holds` is a step of that constant's computation. -/
theorem objectStep_entry {c : DeclName} {comp : RootComputation Tower.Head}
    (mem : (c, comp) ∈ computations) (notHolds : c ≠ holdsN) {n : Nat}
    {args : List (Tower.Tm n)} {r : Tower.Tm n}
    (step : objectRules.computation.step (appSpine (.const c) args) r) :
    comp.step (appSpine (.const c) args) r := by
  rcases step with step | step
  · obtain ⟨⟨c', comp'⟩, mem', h⟩ := rules_computation.mp step
    obtain ⟨args', same⟩ := computations_headed _ mem' h
    obtain ⟨rfl, -⟩ := appSpine_const_injective same
    cases List.inj_on_of_nodup_map computations_distinct mem' mem rfl
    exact h
  · exfalso
    generalize e : appSpine (.const c) args = l at step
    have head : ∀ {x : Tower.Tm n}, appSpine (.const c) args ≠ .app (.const holdsN) x := by
      intro x same
      obtain ⟨init, -, hf⟩ := appSpine_const_eq_app same
      obtain ⟨rfl, -⟩ := appSpine_const_injective (as := []) (bs := init) hf
      exact notHolds rfl
    cases step with
    | imp p q => exact head e
    | all _ f => exact head e
    | eq _ x y => exact head e

/-- The steps of addition. -/
theorem objectStep_add {n : Nat} {x y r : Tower.Tm n}
    (step : objectRules.computation.step (appSpine (.const addN) [x, y]) r) :
    (y = .const zeroN ∧ r = x) ∨
      ∃ m, y = .app (.const sucN) m ∧ r = .app (.const sucN) (appSpine (.const addN) [x, m]) := by
  obtain ⟨k, fields, σ, as, memk, has, same, rfl⟩ :=
    objectStep_entry (listed 1 (by decide)) (by decide) step
  simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
  rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases as with _ | ⟨_, _⟩
    · have same' : (Tm.app (.app (.const addN) x) y : Tower.Tm n) =
          .app (.app (.const addN) (σ 1)) (.const zeroN) := same
      obtain ⟨hf, rfl⟩ := Tm.app.inj same'
      obtain ⟨-, rfl⟩ := Tm.app.inj hf
      exact .inl ⟨rfl, rfl⟩
    · cases has
  · rcases as with _ | ⟨a, _ | ⟨_, _⟩⟩
    · cases has
    · have same' : (Tm.app (.app (.const addN) x) y : Tower.Tm n) =
          .app (.app (.const addN) (σ 1)) (.app (.const sucN) a) := same
      obtain ⟨hf, rfl⟩ := Tm.app.inj same'
      obtain ⟨-, rfl⟩ := Tm.app.inj hf
      exact .inr ⟨a, rfl, rfl⟩
    · cases has

/-- The steps of the iterated power set. -/
theorem objectStep_pow {n : Nat} {x X r : Tower.Tm n}
    (step : objectRules.computation.step (appSpine (.const powN) [x, X]) r) :
    (x = .const zeroN ∧ r = X) ∨
      ∃ m, x = .app (.const sucN) m ∧ r = .app (.const powerN) (appSpine (.const powN) [m, X]) := by
  obtain ⟨k, fields, σ, as, memk, has, same, rfl⟩ :=
    objectStep_entry (listed 2 (by decide)) (by decide) step
  simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
  rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases as with _ | ⟨_, _⟩
    · have same' : (Tm.app (.app (.const powN) x) X : Tower.Tm n) =
          .app (.app (.const powN) (.const zeroN)) (σ 0) := same
      obtain ⟨hf, rfl⟩ := Tm.app.inj same'
      obtain ⟨-, rfl⟩ := Tm.app.inj hf
      exact .inl ⟨rfl, rfl⟩
    · cases has
  · rcases as with _ | ⟨a, _ | ⟨_, _⟩⟩
    · cases has
    · have same' : (Tm.app (.app (.const powN) x) X : Tower.Tm n) =
          .app (.app (.const powN) (.app (.const sucN) a)) (σ 0) := same
      obtain ⟨hf, rfl⟩ := Tm.app.inj same'
      obtain ⟨-, rfl⟩ := Tm.app.inj hf
      exact .inr ⟨a, rfl, rfl⟩
    · cases has

/-- The steps of the recursor on the numbers. -/
theorem objectStep_numRec {n : Nat} {p z s a r : Tower.Tm n}
    (step : objectRules.computation.step (appSpine (.const numRecName) [p, z, s, a]) r) :
    (a = .const zeroN ∧ r = z) ∨
      ∃ m, a = .app (.const sucN) m ∧
        r = .app (.app s m) (appSpine (.const numRecName) [p, z, s, m]) := by
  obtain ⟨p', ms, i, k, fields, args, mt, hms, hi, has, hm, same, rfl⟩ :=
    objectStep_entry (listed 0 (by decide)) (by decide) step
  obtain ⟨-, same⟩ := appSpine_const_injective same
  rcases ms with _ | ⟨z', _ | ⟨s', _ | ⟨_, _⟩⟩⟩
  · cases hms
  · cases hms
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at same
    obtain ⟨rfl, rfl, rfl, rfl⟩ := same
    rcases i with _ | _ | i
    · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨_, _⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
        subst hm
        exact .inl ⟨rfl, rfl⟩
      · cases has
    · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨m, _ | ⟨_, _⟩⟩
      · cases has
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
        subst hm
        exact .inr ⟨m, rfl, rfl⟩
      · cases has
    · cases hi
  · cases hms

/-- Identity elimination steps only at reflexivity, to its method. -/
theorem objectStep_j {n : Nat} {a₀ a₁ a₂ a₃ a₄ a₅ r : Tower.Tm n}
    (step : objectRules.computation.step (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, a₅]) r) :
    ∃ u, a₅ = .refl u ∧ r = a₃ := by
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, same, rfl⟩ :=
    objectStep_entry (listed 3 (by decide)) (by decide) step
  obtain ⟨-, same⟩ := appSpine_const_injective same
  simp only [List.cons.injEq, and_true] at same
  obtain ⟨-, -, -, rfl, -, rfl⟩ := same
  exact ⟨b₅, rfl, rfl⟩

/-- The steps of the iterator. -/
theorem objectStep_iter {n : Nat} {c A P s a e r : Tower.Tm n}
    (step : objectRules.computation.step (appSpine (.const iterName) [c, A, P, s, a, e]) r) :
    (c = .const zeroN ∧ r = .pair a e) ∨
      ∃ m, c = .app (.const sucN) m ∧
        r = CertifiedTransforms.shared s (iterPartial m A P s) a e := by
  obtain ⟨k, fields, σ, as, memk, has, same, rfl⟩ :=
    objectStep_entry (listed 9 (by decide)) (by decide) step
  simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
  rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases as with _ | ⟨_, _⟩
    · have same' : appSpine (.const iterName) [c, A, P, s, a, e] =
          appSpine (.const iterName) [.const zeroN, σ 4, σ 3, σ 2, σ 1, σ 0] := same
      obtain ⟨-, same'⟩ := appSpine_const_injective same'
      simp only [List.cons.injEq, and_true] at same'
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := same'
      exact .inl ⟨rfl, rfl⟩
    · cases has
  · rcases as with _ | ⟨m, _ | ⟨_, _⟩⟩
    · cases has
    · have same' : appSpine (.const iterName) [c, A, P, s, a, e] =
          appSpine (.const iterName) [.app (.const sucN) m, σ 4, σ 3, σ 2, σ 1, σ 0] := same
      obtain ⟨-, same'⟩ := appSpine_const_injective same'
      simp only [List.cons.injEq, and_true] at same'
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := same'
      exact .inr ⟨m, rfl, rfl⟩
    · cases has

/-- A definition by one equation steps only to its right-hand side. -/
theorem objectStep_definition {f : DeclName} {k : Nat} {Θ : Tower.Ctx k} {rhs : Tower.Tm k}
    (mem : (f, definitionComputation f Θ rhs) ∈ computations) (notHolds : f ≠ holdsN)
    {n : Nat} {σ : Sub Tower.Head k n} {r : Tower.Tm n}
    (step : objectRules.computation.step (appSpine (.const f) (telescopeArgs Θ σ)) r) :
    r = subst σ rhs := by
  obtain ⟨σ', same, rfl⟩ := objectStep_entry mem notHolds step
  rw [applyClosed_eq_appSpine] at same
  rw [telescopeArgs_inj Θ (appSpine_const_injective same).2]

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
