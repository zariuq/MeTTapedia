import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DefinedConstants

/-!
# A family of constants declared together

A definition by equations declares one constant (`DefinedConstants`). A signature declares
several at once: their types may mention one another, and its equations may relate several of
them. This module gives the package of such a family.

**The package of a family** (`familyChurch`, `withFamily`): the declared constants at their
types, given as a function from names to types, and as computation steps the instances of the
family's equations. An instance requires the typings of the instances of its metavariables
along the equation's telescope, as for a single definition.

A family is usually written as a table of names and types (`tableLookup`).

**In the judgment**, in every package that contains the family's steps, an instance of an
equation at a substitution typed along the equation's telescope is an equality at every type
both sides have (`family_equation_holds`). A declared constant has its type by
`definition_typed`, which asks only that the constant be declared at the type.

The set model of a family, from values of its constants, is in
`TowerInterpretation/SetConstantFamilies.lean`.

Positive example: a family without equations has no computation step
(`family_no_step_of_no_equation`). Negative example: a name the family does not declare has
no declared type in its package (`familyChurch_undeclared`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type}

/-- **The rule package of a family of constants**, over the universe rules of a package: the
declared constants at their erased types, and the erased equations. -/
def familyRules (target : Rules Head) (decls : DeclName → Option (CTm Head 0))
    (eqs : List (DefiningEquation Head)) : Rules Head :=
  { target with
    constantType := fun c => (decls c).map CTm.erase
    computation := erasedComputation eqs }

/-- **The annotated package of a family of constants**: the declared constants at their types,
and the instances of the equations with the typings of their metavariables as premises. -/
def familyChurch (target : Rules Head) (decls : DeclName → Option (CTm Head 0))
    (eqs : List (DefiningEquation Head)) : ChurchRules (familyRules target decls eqs) where
  constantType := decls
  computation := equationComputation eqs
  erase_constantType := fun _ => rfl
  erase_step := by
    rintro n _ _ ⟨e, member, σ, rfl, rfl⟩
    exact ⟨e, member, CTm.eraseSub σ, CTm.erase_subst σ _, CTm.erase_subst σ _⟩

/-! ## Declarations given by a table -/

/-- **A table of entries read as a function on names**: the entry of the first row with the
name, if there is one. A family is usually written as such a table. -/
def tableLookup {α : Type*} : List (DeclName × α) → DeclName → Option α
  | [], _ => none
  | (name, entry) :: rest, c => if c = name then some entry else tableLookup rest c

/-- What a table gives at a name is one of its rows. -/
theorem tableLookup_mem {α : Type*} : ∀ {table : List (DeclName × α)} {c : DeclName} {entry : α},
    tableLookup table c = some entry → (c, entry) ∈ table
  | [], _, _, found => nomatch found
  | (name, first) :: rest, c, entry, found => by
      unfold tableLookup at found
      by_cases same : c = name
      · rw [if_pos same] at found
        obtain rfl := Option.some.inj found
        exact same ▸ List.mem_cons_self
      · rw [if_neg same] at found
        exact List.mem_cons_of_mem _ (tableLookup_mem found)

variable {R : Rules Head}

/-- **A package with a family of constants**: the sum of the package and the package of the
family. -/
abbrev withFamily (B : ChurchRules R) (decls : DeclName → Option (CTm Head 0))
    (eqs : List (DefiningEquation Head)) :
    ChurchRules (Rules.sum R (familyRules R decls eqs)) :=
  B.sum (familyChurch R decls eqs)

variable {decls : DeclName → Option (CTm Head 0)} {eqs : List (DefiningEquation Head)}

/-- A name new to a package is declared in the package with a family as the family declares
it. -/
theorem withFamily_declared (B : ChurchRules R) {c : DeclName} (new : B.constantType c = none) :
    (withFamily B decls eqs).constantType c = decls c :=
  sumDecls_right new

/-- A name the package declares keeps its declaration in the package with a family. -/
theorem withFamily_base (B : ChurchRules R) {c : DeclName} {T : CTm Head 0}
    (declared : B.constantType c = some T) :
    (withFamily B decls eqs).constantType c = some T :=
  sumDecls_left declared

/-- Negative example: a name the family does not declare has no declared type in its
package. -/
theorem familyChurch_undeclared (target : Rules Head) {c : DeclName} (undeclared : decls c = none) :
    (familyChurch target decls eqs).constantType c = none :=
  undeclared

/-- Positive example: a family without equations has no computation step. -/
theorem family_no_step_of_no_equation (target : Rules Head) {n : Nat} {l r : CTm Head n} :
    ¬ (familyChurch target decls ([] : List (DefiningEquation Head))).computation.step l r := by
  rintro ⟨e, member, -⟩
  exact nomatch member

section Judgment

variable {R' : Rules Head} {Q : ChurchRules R'}

/-- **An equation of a family holds at its typed instances**: in a package that contains the
family's steps, an instance of an equation at a substitution typed along the equation's
telescope is an equality at every type both sides have. -/
theorem family_equation_holds (target : Rules Head)
    (steps : StepsWithin (familyChurch target decls eqs) Q) {e : DefiningEquation Head}
    (member : e ∈ eqs) {n : Nat} {Γ : CCtx Head n} (σ : CSub Head e.arity n)
    (typed : CSubstMor Q e.telescope Γ σ) {C : CTm Head n}
    (left : CTyped Q Γ (e.left.subst σ) C) (right : CTyped Q Γ (e.right.subst σ) C) :
    CEqual Q Γ (e.left.subst σ) (e.right.subst σ) C := by
  have step : (familyChurch target decls eqs).computation.step (e.left.subst σ)
      (e.right.subst σ) := ⟨e, member, σ, rfl, rfl⟩
  have required : (familyChurch target decls eqs).computation.requires (e.left.subst σ)
      (e.right.subst σ) (telescopePremises e.telescope σ) := ⟨e, member, σ, rfl, rfl, rfl⟩
  refine .root (steps.step step) (steps.requires step required) (fun premise among => ?_)
    left right
  obtain ⟨i, rfl⟩ := mem_telescopePremises.mp among
  exact typed i

end Judgment

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
