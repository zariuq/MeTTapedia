import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.IotaKnowledge

/-!
# A constant defined by equations

A definition gives a constant its type and equations that it computes by: for each equation a
telescope of metavariables and two sides over it (`DefiningEquation`). A function defined by pattern
equations is the main case: on the left the constant applied to patterns, on the right a term
that may call the constant again.

**The package of a definition** (`definedChurch`, `withDefinition`): the constant at its
declared type, and as computation steps the instances of the equations. An instance requires
the typings of the instances of its metavariables along the equation's telescope
(`telescopePremises`), and nothing else. The telescope is given with the equation; no
knowledge is computed from the left side.

**In the judgment**, in every package that contains the definition's steps: the constant has
its declared type when that type is a type (`definition_typed`), and an instance of an
equation at a substitution typed along the equation's telescope is an equality at every type
both sides have (`equation_holds`).

**The witness of a definition** (`defineBy`): the instantiation of constants that sends the
defined constant to a closed term and every other constant to itself. A definition is
*satisfied by a term* of the package before it when, for each equation, the two instantiated
sides are equal in that package over the instantiated telescope. The set model of a satisfied
definition is in `TowerInterpretation/SetDefinitions.lean`.

Positive example: a constant with no equation is a declared constant, and its package has no
step (`no_step_of_no_equation`). Negative example: a name that the definition does not define
has no declared type in its package (`definedChurch_other`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type}

/-! ## Equations -/

/-- **An equation of a definition**: a telescope of metavariables and two sides over it. -/
structure DefiningEquation (Head : Type) where
  arity : Nat
  telescope : CCtx Head arity
  left : CTm Head arity
  right : CTm Head arity

/-- The premises of an instance of an equation: the typing of each metavariable's instance at
its type in the telescope. -/
def telescopePremises {k n : Nat} (Θ : CCtx Head k) (σ : CSub Head k n) : List (CPremise Head n) :=
  (List.finRange k).map fun i => CPremise.typing (σ i) ((Θ.lookup i).subst σ)

theorem mem_telescopePremises {k n : Nat} {Θ : CCtx Head k} {σ : CSub Head k n}
    {premise : CPremise Head n} :
    premise ∈ telescopePremises Θ σ ↔
      ∃ i, premise = CPremise.typing (σ i) ((Θ.lookup i).subst σ) := by
  unfold telescopePremises
  rw [List.mem_map]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, List.mem_finRange i, rfl⟩

theorem telescopePremises_rename {k n m : Nat} (Θ : CCtx Head k) (σ : CSub Head k n)
    (ρ : Ren n m) :
    (telescopePremises Θ σ).map (CPremise.rename ρ) =
      telescopePremises Θ fun i => (σ i).rename ρ := by
  unfold telescopePremises
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, CPremise.rename, CTm.rename_subst]

theorem telescopePremises_subst {k n m : Nat} (Θ : CCtx Head k) (σ : CSub Head k n)
    (τ : CSub Head n m) :
    (telescopePremises Θ σ).map (CPremise.subst τ) =
      telescopePremises Θ fun i => (σ i).subst τ := by
  unfold telescopePremises
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, CPremise.subst, CTm.subst_comp]

/-- **The computation of a list of equations**: its steps are the instances of the equations,
and an instance requires the typings of its metavariables along the equation's telescope. -/
def equationComputation (eqs : List (DefiningEquation Head)) : CRootComputation Head where
  step := fun {n} l r => ∃ e ∈ eqs, ∃ σ : CSub Head e.arity n,
    l = e.left.subst σ ∧ r = e.right.subst σ
  rename := by
    rintro n m ρ _ _ ⟨e, member, σ, rfl, rfl⟩
    exact ⟨e, member, fun i => (σ i).rename ρ, CTm.rename_subst ρ σ _, CTm.rename_subst ρ σ _⟩
  substitute := by
    rintro n m τ _ _ ⟨e, member, σ, rfl, rfl⟩
    exact ⟨e, member, fun i => (σ i).subst τ, CTm.subst_comp τ σ _, CTm.subst_comp τ σ _⟩
  requires := fun {n} l r premises => ∃ e ∈ eqs, ∃ σ : CSub Head e.arity n,
    l = e.left.subst σ ∧ r = e.right.subst σ ∧ premises = telescopePremises e.telescope σ
  requires_rename := by
    rintro n m ρ _ _ _ ⟨e, member, σ, rfl, rfl, rfl⟩
    exact ⟨e, member, fun i => (σ i).rename ρ, CTm.rename_subst ρ σ _, CTm.rename_subst ρ σ _,
      telescopePremises_rename e.telescope σ ρ⟩
  requires_substitute := by
    rintro n m τ _ _ _ ⟨e, member, σ, rfl, rfl, rfl⟩
    exact ⟨e, member, fun i => (σ i).subst τ, CTm.subst_comp τ σ _, CTm.subst_comp τ σ _,
      telescopePremises_subst e.telescope σ τ⟩

/-- The erased computation of a list of equations: the instances of the erased equations. -/
def erasedComputation (eqs : List (DefiningEquation Head)) : RootComputation Head where
  step := fun {n} t u => ∃ e ∈ eqs, ∃ σ : Sub Head e.arity n,
    t = Presentation.subst σ e.left.erase ∧ u = Presentation.subst σ e.right.erase
  rename := by
    rintro n m ρ _ _ ⟨e, member, σ, rfl, rfl⟩
    exact ⟨e, member, fun i => Presentation.rename ρ (σ i), Presentation.rename_subst ρ σ _,
      Presentation.rename_subst ρ σ _⟩
  substitute := by
    rintro n m τ _ _ ⟨e, member, σ, rfl, rfl⟩
    exact ⟨e, member, fun i => Presentation.subst τ (σ i), Presentation.subst_comp τ σ _,
      Presentation.subst_comp τ σ _⟩

/-! ## The package of a definition -/

/-- **The rule package of a definition**, over the universe rules of a package: the defined
constant at its erased type, and the erased equations. -/
def definedRules (target : Rules Head) (f : DeclName) (A : CTm Head 0)
    (eqs : List (DefiningEquation Head)) : Rules Head :=
  { target with
    constantType := fun c => if c = f then some A.erase else none
    computation := erasedComputation eqs }

/-- **The annotated package of a definition**: the defined constant at its type, and the
instances of its equations with the typings of their metavariables as premises. -/
def definedChurch (target : Rules Head) (f : DeclName) (A : CTm Head 0)
    (eqs : List (DefiningEquation Head)) : ChurchRules (definedRules target f A eqs) where
  constantType := fun c => if c = f then some A else none
  computation := equationComputation eqs
  erase_constantType := by
    intro c
    show (if c = f then some A else none).map CTm.erase = if c = f then some A.erase else none
    by_cases same : c = f
    · rw [if_pos same, if_pos same]
      rfl
    · rw [if_neg same, if_neg same]
      rfl
  erase_step := by
    rintro n _ _ ⟨e, member, σ, rfl, rfl⟩
    exact ⟨e, member, CTm.eraseSub σ, CTm.erase_subst σ _, CTm.erase_subst σ _⟩

variable {R : Rules Head}

/-- **A package with a definition**: the sum of the package and the package of the
definition. -/
abbrev withDefinition (B : ChurchRules R) (f : DeclName) (A : CTm Head 0)
    (eqs : List (DefiningEquation Head)) :
    ChurchRules (Rules.sum R (definedRules R f A eqs)) :=
  B.sum (definedChurch R f A eqs)

variable {f : DeclName} {A : CTm Head 0} {eqs : List (DefiningEquation Head)}

/-- The defined constant is declared at its type in the package of the definition. -/
theorem definedChurch_defined (target : Rules Head) :
    (definedChurch target f A eqs).constantType f = some A :=
  if_pos rfl

/-- Negative example: a name that the definition does not define has no declared type in its
package. -/
theorem definedChurch_other (target : Rules Head) {c : DeclName} (other : c ≠ f) :
    (definedChurch target f A eqs).constantType c = none :=
  if_neg other

/-- The defined constant is declared at its type in a package to which it is new. -/
theorem withDefinition_defined (B : ChurchRules R) (new : B.constantType f = none) :
    (withDefinition B f A eqs).constantType f = some A :=
  (sumDecls_right new).trans (definedChurch_defined R)

/-- Positive example: a definition without equations has no computation step. -/
theorem no_step_of_no_equation (target : Rules Head) {n : Nat} {l r : CTm Head n} :
    ¬ (definedChurch target f A ([] : List (DefiningEquation Head))).computation.step l r := by
  rintro ⟨e, member, -⟩
  exact nomatch member

/-! ## The definition in the judgment -/

section Judgment

variable {R' : Rules Head} {Q : ChurchRules R'}

/-- **The defined constant has its declared type**, in every context of a package that
declares it at that type, when the type is a type there. -/
theorem definition_typed (declared : Q.constantType f = some A) {u : Head}
    (formed : CTyped Q .nil A (.head u)) (isUniverse : R'.isUniverse u) {n : Nat}
    {Γ : CCtx Head n} : CTyped Q Γ (.const f) A.liftClosed :=
  CDerivable.const declared formed isUniverse

/-- **An equation of a definition holds at its typed instances**: in a package that contains
the definition's steps, an instance of an equation at a substitution typed along the
equation's telescope is an equality at every type both sides have. -/
theorem equation_holds (target : Rules Head)
    (steps : StepsWithin (definedChurch target f A eqs) Q) {e : DefiningEquation Head}
    (member : e ∈ eqs) {n : Nat} {Γ : CCtx Head n} (σ : CSub Head e.arity n)
    (typed : CSubstMor Q e.telescope Γ σ) {C : CTm Head n}
    (left : CTyped Q Γ (e.left.subst σ) C) (right : CTyped Q Γ (e.right.subst σ) C) :
    CEqual Q Γ (e.left.subst σ) (e.right.subst σ) C := by
  have step : (definedChurch target f A eqs).computation.step (e.left.subst σ)
      (e.right.subst σ) := ⟨e, member, σ, rfl, rfl⟩
  have required : (definedChurch target f A eqs).computation.requires (e.left.subst σ)
      (e.right.subst σ) (telescopePremises e.telescope σ) := ⟨e, member, σ, rfl, rfl, rfl⟩
  refine .root (steps.step step) (steps.requires step required) (fun premise among => ?_)
    left right
  obtain ⟨i, rfl⟩ := mem_telescopePremises.mp among
  exact typed i

end Judgment

/-! ## The witness of a definition -/

/-- The instantiation of constants that sends the defined constant to a closed term and every
other constant to itself. -/
def defineBy (f : DeclName) (witness : CTm Head 0) : DeclName → CTm Head 0 :=
  fun c => if c = f then witness else .const c

theorem defineBy_defined (f : DeclName) (witness : CTm Head 0) : defineBy f witness f = witness :=
  if_pos rfl

theorem defineBy_other {f c : DeclName} (witness : CTm Head 0) (other : c ≠ f) :
    defineBy f witness c = .const c :=
  if_neg other

/-- The instance of the defined constant by a witness is the witness. -/
theorem instConsts_defined (f : DeclName) (witness : CTm Head 0) {n : Nat} :
    (CTm.const f : CTm Head n).instConsts (defineBy f witness) = witness.liftClosed := by
  show (defineBy f witness f).liftClosed = witness.liftClosed
  rw [defineBy_defined]

/-- The instance of another constant by a witness is the constant. -/
theorem instConsts_other {f c : DeclName} (witness : CTm Head 0) (other : c ≠ f) {n : Nat} :
    (CTm.const c : CTm Head n).instConsts (defineBy f witness) = .const c := by
  show (defineBy f witness c).liftClosed = CTm.const c
  rw [defineBy_other witness other]
  rfl

/-- **A definition is satisfied by a term** of a package when, for each of its equations, the
two sides with the term in place of the defined constant are equal in the package, over the
equation's telescope with the same replacement. -/
def SatisfiedBy (B : ChurchRules R) (f : DeclName) (eqs : List (DefiningEquation Head))
    (witness : CTm Head 0) : Prop :=
  ∀ e ∈ eqs, ∃ C : CTm Head e.arity,
    CEqual B (e.telescope.instConsts (defineBy f witness)) (e.left.instConsts (defineBy f witness))
      (e.right.instConsts (defineBy f witness)) C

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
