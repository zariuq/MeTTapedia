import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetInductive
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DefinedConstants

/-!
# A definition by equations has a set model when a term satisfies its equations

A constant defined by equations (`withDefinition`) computes by the instances of its equations.
The equations may call the constant again, so they do not say by themselves that the constant
has a value. This module gives the criterion under which it has one in the set tower.

**The criterion** (`definition_setModel`): let the package before the definition have a set
model at every assignment that agrees with a given one on the names it declares, let the
defined name be new to it, and let a closed term of that package (the *witness*) have the
declared type and satisfy the equations (`SatisfiedBy`): with the witness in place of the
defined constant, the two sides of each equation are equal in the package, over the
equation's telescope. Then the package with the definition has a set model, at every
assignment that agrees on the names it declares with the base assignment extended by the value
of the witness. So a further declaration or definition can be added over it.

The general form asks only for a value: a set that lies in the declared type and at which
both sides of every equation have one value (`definition_setModel_of_value`). It is used where
the value is built in the model and no term is at hand, as for definitions by structural
recursion (`SetRecursion.lean`).

The value of the defined constant is the value of the witness. An equation holds because
instantiating a constant by a term is evaluating at the assignment that gives the constant
the term's value (`ev_instConsts`), and the instantiated equation holds by the soundness of
the package before the definition. No uniqueness of types is used: equal values are equal at
every type.

Consequences: soundness, and a closed type with an empty set has no closed term
(`definition_no_closed_inhabitant`).

This is how a function defined by pattern equations is justified: the witness is the term
built from the recursor of the datatype, and the pattern equations are its computation rules
followed by β-steps. Positive example: the append of two lists by pattern equations, over the
object package with the lists of numbers (`ObjectAppendByEquations.lean`, in the executable
model of the candidate). Negative example there: the equation `bad ⟶ suc bad` has no set
model at all.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet)

universe u

variable {Head : Type} (heads : Head → ZFSet.{u})

/-! ## Instantiating constants and evaluating -/

/-- **Instantiating constants by closed terms is evaluating at the assignment of their
values.** -/
theorem ev_instConsts (consts : DeclName → ZFSet.{u}) (θ : DeclName → CTm Head 0) :
    ∀ {n : Nat} (t : CTm Head n) (ρ : Env.{u} n),
      ev heads consts (t.instConsts θ) ρ =
        ev heads (fun c => ev heads consts (θ c) Fin.elim0) t ρ := by
  intro n t
  induction t with
  | var i => exact fun _ => rfl
  | const c => exact fun ρ => ev_liftClosed heads consts (θ c) ρ
  | head h => exact fun _ => rfl
  | pi A B ihA ihB =>
      intro ρ
      change tracePiSet (ev heads consts (A.instConsts θ) ρ)
          (fun x => ev heads consts (B.instConsts θ) (extend ρ x)) =
        tracePiSet (ev heads (fun c => ev heads consts (θ c) Fin.elim0) A ρ)
          (fun x => ev heads (fun c => ev heads consts (θ c) Fin.elim0) B (extend ρ x))
      rw [ihA ρ]
      congr 1
      funext x
      exact ihB _
  | sigma A B ihA ihB =>
      intro ρ
      change ZFSetDependentProducts.sigmaSet (ev heads consts (A.instConsts θ) ρ)
          (fun x => ev heads consts (B.instConsts θ) (extend ρ x)) =
        ZFSetDependentProducts.sigmaSet (ev heads (fun c => ev heads consts (θ c) Fin.elim0) A ρ)
          (fun x => ev heads (fun c => ev heads consts (θ c) Fin.elim0) B (extend ρ x))
      rw [ihA ρ]
      congr 1
      funext x
      exact ihB _
  | id A a b _ iha ihb =>
      intro ρ
      change ZFSetTraceProofDecoding.truthCode
          (ev heads consts (a.instConsts θ) ρ = ev heads consts (b.instConsts θ) ρ) =
        ZFSetTraceProofDecoding.truthCode
          (ev heads (fun c => ev heads consts (θ c) Fin.elim0) a ρ =
            ev heads (fun c => ev heads consts (θ c) Fin.elim0) b ρ)
      rw [iha ρ, ihb ρ]
  | lam A b ihA ihb =>
      intro ρ
      change traceLam (graph (ev heads consts (A.instConsts θ) ρ)
          (fun x => ev heads consts (b.instConsts θ) (extend ρ x))) =
        traceLam (graph (ev heads (fun c => ev heads consts (θ c) Fin.elim0) A ρ)
          (fun x => ev heads (fun c => ev heads consts (θ c) Fin.elim0) b (extend ρ x)))
      rw [ihA ρ]
      congr 2
      funext x
      exact ihb _
  | app g a ihg iha =>
      intro ρ
      change traceApp (ev heads consts (g.instConsts θ) ρ) (ev heads consts (a.instConsts θ) ρ) =
        traceApp (ev heads (fun c => ev heads consts (θ c) Fin.elim0) g ρ)
          (ev heads (fun c => ev heads consts (θ c) Fin.elim0) a ρ)
      rw [ihg ρ, iha ρ]
  | pair a b iha ihb =>
      intro ρ
      change ZFSet.pair (ev heads consts (a.instConsts θ) ρ) (ev heads consts (b.instConsts θ) ρ) =
        ZFSet.pair (ev heads (fun c => ev heads consts (θ c) Fin.elim0) a ρ)
          (ev heads (fun c => ev heads consts (θ c) Fin.elim0) b ρ)
      rw [iha ρ, ihb ρ]
  | fst p ih =>
      intro ρ
      change Mettapedia.SetTheory.ZFSetOrderedPair.first (ev heads consts (p.instConsts θ) ρ) =
        Mettapedia.SetTheory.ZFSetOrderedPair.first
          (ev heads (fun c => ev heads consts (θ c) Fin.elim0) p ρ)
      rw [ih ρ]
  | snd p ih =>
      intro ρ
      change Mettapedia.SetTheory.ZFSetOrderedPair.second (ev heads consts (p.instConsts θ) ρ) =
        Mettapedia.SetTheory.ZFSetOrderedPair.second
          (ev heads (fun c => ev heads consts (θ c) Fin.elim0) p ρ)
      rw [ih ρ]
  | refl a _ => exact fun _ => rfl

variable {heads} {consts : DeclName → ZFSet.{u}} {f : DeclName} {witness : CTm Head 0}

/-- At an assignment that gives the defined constant the value of the witness, a term and its
instance by the witness have one value. -/
theorem ev_defineBy (value : consts f = ev heads consts witness Fin.elim0) {n : Nat}
    (t : CTm Head n) (ρ : Env.{u} n) :
    ev heads consts (t.instConsts (defineBy f witness)) ρ = ev heads consts t ρ := by
  have assignment : (fun c => ev heads consts (defineBy f witness c) Fin.elim0) = consts := by
    funext c
    by_cases same : c = f
    · subst same
      rw [defineBy_defined]
      exact value.symm
    · rw [defineBy_other witness same]
      rfl
  rw [ev_instConsts, assignment]

/-- At such an assignment an environment of a telescope is one of its instance by the
witness. -/
theorem sat_defineBy (value : consts f = ev heads consts witness Fin.elim0) {k : Nat}
    {Θ : CCtx Head k} {η : Env.{u} k} (sat : Sat heads consts Θ η) :
    Sat heads consts (Θ.instConsts (defineBy f witness)) η := fun i => by
  rw [← CCtx.instConsts_lookup, ev_defineBy value]
  exact sat i

/-! ## The set model of a definition -/

variable {R : Rules Head} {base : DeclName → ZFSet.{u}} {A : CTm Head 0}
  {eqs : List (DefiningEquation Head)}

/-- **A definition by equations has a set model when a value satisfies its equations.** The
package before the definition has a set model at every assignment that agrees with the base
assignment on the names it declares, and the defined name is new to it. At each such
assignment that gives the defined name the value: the value lies in the set of the declared
type, and both sides of every equation have one value at every environment of the equation's
telescope. The model is at every assignment that agrees, on the names the package with the
definition declares, with the base assignment extended by the value. -/
theorem definition_setModel_of_value (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (value : ZFSet.{u})
    (typed : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → consts f = value →
        value ∈ ev heads consts A Fin.elim0)
    (valid : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → consts f = value →
        ∀ e ∈ eqs, ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
          ev heads consts e.left η = ev heads consts e.right η)
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withDefinition B f A eqs).constantType c ≠ none →
      consts c = Function.update base f value c) :
    SetModel heads consts (withDefinition B f A eqs) := by
  have agreesBase : ∀ c, B.constantType c ≠ none → consts c = base c := by
    intro c declared
    have other : c ≠ f := fun same => declared (same ▸ new)
    have inSum : (withDefinition B f A eqs).constantType c ≠ none := by
      cases found : B.constantType c with
      | none => exact absurd found declared
      | some type =>
        have known : (withDefinition B f A eqs).constantType c = some type := sumDecls_left found
        rw [known]
        exact Option.some_ne_none type
    rw [agrees c inSum, Function.update_of_ne other]
  have modelB := baseModel consts agreesBase
  have atDefined : consts f = value := by
    have declared : (withDefinition B f A eqs).constantType f ≠ none := by
      rw [withDefinition_defined B new]
      exact Option.some_ne_none A
    rw [agrees f declared, Function.update_self]
  refine SetModel.sum modelB
    { universes := { modelB.universes with }
      headEq := modelB.headEq
      constants := fun {c T} declared => ?_
      steps := fun {n Γ l r premises} _ required holds ρ sat => ?_ }
  · by_cases isDefined : c = f
    · subst isDefined
      rw [definedChurch_defined] at declared
      obtain rfl := Option.some.inj declared
      rw [atDefined]
      exact typed consts agreesBase atDefined
    · rw [definedChurch_other _ isDefined] at declared
      exact nomatch declared
  · obtain ⟨e, member, σ, rfl, rfl, rfl⟩ := required
    have satTele : Sat heads consts e.telescope fun i => ev heads consts (σ i) ρ := fun i => by
      have typedAt := holds _ (mem_telescopePremises.mpr ⟨i, rfl⟩) ρ sat
      rwa [ev_subst] at typedAt
    rw [ev_subst, ev_subst]
    exact valid consts agreesBase atDefined e member _ satTele

/-- **A definition by equations that a term satisfies has a set model.** The package before
the definition has a set model at every assignment that agrees with the base assignment on the
names it declares; the defined name is new to it; the witness is a closed term of it at the
declared type; and with the witness in place of the defined constant every equation holds in
it. The model is at every assignment that agrees, on the names the package with the definition
declares, with the base assignment extended by the value of the witness. -/
theorem definition_setModel (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (typed : CTyped B .nil witness A)
    (satisfied : SatisfiedBy B f eqs witness) (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withDefinition B f A eqs).constantType c ≠ none →
      consts c = Function.update base f (ev heads base witness Fin.elim0) c) :
    SetModel heads consts (withDefinition B f A eqs) := by
  refine definition_setModel_of_value B baseModel new (ev heads base witness Fin.elim0)
    (fun consts agreesBase atDefined => ?_) (fun consts agreesBase atDefined e member η sat => ?_)
    consts agrees
  · have same : ev heads consts witness Fin.elim0 = ev heads base witness Fin.elim0 :=
      CDerivable.ev_congr_declared heads agreesBase typed Fin.elim0
    rw [← same]
    exact CDerivable.sound (baseModel consts agreesBase) typed Fin.elim0
      (sat_nil heads consts Fin.elim0)
  · have same : ev heads consts witness Fin.elim0 = ev heads base witness Fin.elim0 :=
      CDerivable.ev_congr_declared heads agreesBase typed Fin.elim0
    have value : consts f = ev heads consts witness Fin.elim0 := atDefined.trans same.symm
    obtain ⟨C, equal⟩ := satisfied e member
    have key := (CDerivable.sound (baseModel consts agreesBase) equal _
      (sat_defineBy value sat)).1
    rwa [ev_defineBy value, ev_defineBy value] at key

/-- The model at the base assignment extended by the value of the witness. -/
theorem definition_setModel_read (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (typed : CTyped B .nil witness A)
    (satisfied : SatisfiedBy B f eqs witness) :
    SetModel heads (Function.update base f (ev heads base witness Fin.elim0))
      (withDefinition B f A eqs) :=
  definition_setModel B baseModel new typed satisfied _ fun _ _ => rfl

/-- **Consistency**: a closed type whose set is empty has no closed term in a package with a
definition that a term satisfies. -/
theorem definition_no_closed_inhabitant (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : B.constantType f = none) (typed : CTyped B .nil witness A)
    (satisfied : SatisfiedBy B f eqs witness) {T : CTm Head 0}
    (empty : ∀ z, z ∉ ev heads (Function.update base f (ev heads base witness Fin.elim0)) T
      Fin.elim0) (t : CTm Head 0) :
    ¬ CTyped (withDefinition B f A eqs) .nil t T :=
  CDerivable.no_closed_inhabitant (definition_setModel_read B baseModel new typed satisfied)
    empty t

/-- **Equations derivable from a definition's equations may replace them.** A set model of a
package with a definition is a set model of the package in which the same constant computes
by other equations, when each of those is derivable in the first package over its telescope.
A function may so be defined in the form a theorem covers and used by the equations a
programmer writes. -/
theorem definition_setModel_of_derived {B : ChurchRules R} {consts : DeclName → ZFSet.{u}}
    {eqs eqs' : List (DefiningEquation Head)} (new : B.constantType f = none)
    (model : SetModel heads consts (withDefinition B f A eqs))
    (derived : ∀ e ∈ eqs', ∃ C : CTm Head e.arity,
      CEqual (withDefinition B f A eqs) e.telescope e.left e.right C) :
    SetModel heads consts (withDefinition B f A eqs') := by
  have modelB : SetModel heads consts B := SetModel.of_sum_left model
  refine SetModel.sum modelB
    { universes := { modelB.universes with }
      headEq := modelB.headEq
      constants := fun {c T} declared => ?_
      steps := fun {n Γ l r premises} _ required holds ρ sat => ?_ }
  · by_cases isDefined : c = f
    · subst isDefined
      rw [definedChurch_defined] at declared
      obtain rfl := Option.some.inj declared
      exact model.constants (withDefinition_defined B new)
    · rw [definedChurch_other _ isDefined] at declared
      exact nomatch declared
  · obtain ⟨e, member, σ, rfl, rfl, rfl⟩ := required
    have satTele : Sat heads consts e.telescope fun i => ev heads consts (σ i) ρ := fun i => by
      have typedAt := holds _ (mem_telescopePremises.mpr ⟨i, rfl⟩) ρ sat
      rwa [ev_subst] at typedAt
    obtain ⟨C, equal⟩ := derived e member
    rw [ev_subst, ev_subst]
    exact (CDerivable.sound model equal _ satTele).1

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
