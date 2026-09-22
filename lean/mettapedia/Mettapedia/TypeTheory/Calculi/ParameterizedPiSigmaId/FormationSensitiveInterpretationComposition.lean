import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation

/-!
# Composition of typed declaration interpretations

Sequential constant interpretations compose on their actual closed bodies.
The same composition acts on terms, telescope entries and substitutions;
the primitive typing and root-conversion obligations are discharged from
the two component interpretations. No equality of source constants with
their interpreted bodies is installed in either presentation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstantExpansion

open FormationSensitive

variable {Head : Type} {n m : Nat}

private theorem liftClosed_empty (term : Tm Head 0) :
    (liftClosed term : Tm Head 0) = term := by
  have emptyIdentity : (Fin.elim0 : Ren 0 0) = idRen := by
    funext index
    exact Fin.elim0 index
  simp only [liftClosed, emptyIdentity, rename_id]

def andThen (first second : Bodies Head) : Bodies Head :=
  fun name => expand second (first name)

theorem expand_andThen (first second : Bodies Head) (term : Tm Head n) :
    expand (andThen first second) term = expand second (expand first term) := by
  induction term <;> simp_all only [expand, andThen, expand_liftClosed]

theorem expandCtx_andThen (first second : Bodies Head) (context : Ctx Head n) :
    expandCtx (andThen first second) context =
      expandCtx second (expandCtx first context) := by
  induction context <;> simp_all only [expandCtx, expand_andThen]

theorem andThen_associative (first second third : Bodies Head) :
    andThen (andThen first second) third = andThen first (andThen second third) := by
  funext name
  exact (expand_andThen second third (first name)).symm

theorem andThen_identity_left (bodies : Bodies Head) :
    andThen (fun name => .const name) bodies = bodies := by
  funext name
  exact liftClosed_empty (bodies name)

theorem andThen_identity_right (bodies : Bodies Head) :
    andThen bodies (fun name => .const name) = bodies := by
  funext name
  exact expand_identity (bodies name)

namespace TypedInterpretation

variable {source middle target : Rules Head} {first second : Bodies Head}

theorem andThen (firstInterpretation : TypedInterpretation source middle first)
    (secondInterpretation : TypedInterpretation middle target second) :
    TypedInterpretation source target (ConstantExpansion.andThen first second) where
  headTyping := fun typed => secondInterpretation.headTyping (firstInterpretation.headTyping typed)
  isUniverse := fun universeWitness =>
    secondInterpretation.isUniverse (firstInterpretation.isUniverse universeWitness)
  join := fun joined => secondInterpretation.join (firstInterpretation.join joined)
  cumulative := fun raised => secondInterpretation.cumulative (firstInterpretation.cumulative raised)
  headEq := firstInterpretation.headEq.trans secondInterpretation.headEq
  constant := by
    intro name type known
    simpa only [ConstantExpansion.andThen, expand_andThen, expandCtx] using
      secondInterpretation.typing (firstInterpretation.constant known)
  root := by
    intro k left right contracted
    simpa only [expand_andThen] using
      secondInterpretation.conversion (firstInterpretation.root contracted)

/-- A declaration lookup by itself does not establish that the declaration
is formed. The identity interpretation therefore requests actual formation
certificates, rather than admitting every arbitrary table of declarations. -/
theorem identity (rules : Rules Head)
    (declarationsFormed : ∀ {name type}, rules.constantType name = some type →
      ∃ level, FormationSensitive.Typing rules .nil type (.head level) ∧ rules.isUniverse level) :
    TypedInterpretation rules rules (fun name => .const name) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := rfl
  constant := by
    intro name type known
    obtain ⟨level, formed, universeWitness⟩ := declarationsFormed known
    simpa only [expand_identity, liftClosed_empty] using
      (FormationSensitive.Typing.const (Γ := .nil) known formed universeWitness)
  root := by
    intro k left right contracted
    simpa only [expand_identity] using
      (Relation.EqvGen.rel left right (StepCore.root contracted) :
        Conv rules.headEq left right rules.computation)

/-- A single composed translation and successive translations preserve the
same substituted judgment, including the actual target telescope. -/
theorem composed_substituted_judgment
    (firstInterpretation : TypedInterpretation source middle first)
    (secondInterpretation : TypedInterpretation middle target second)
    {context : Ctx Head n} {destination : Ctx Head m}
    {term type : Tm Head n} {sigma : Sub Head n m}
    (judged : Judgment source context term type)
    (formed : ContextFormation source destination)
    (substitution : FormationSensitive.CtxMor source context destination sigma) :
    Judgment target (expandCtx second (expandCtx first destination))
      (subst (fun index => expand second (expand first (sigma index)))
        (expand second (expand first term)))
      (subst (fun index => expand second (expand first (sigma index)))
        (expand second (expand first type))) := by
  simpa only [expandCtx_andThen, expand_andThen] using
    (firstInterpretation.andThen secondInterpretation).substituted_judgment
      judged formed substitution

end TypedInterpretation

namespace Controls

def introduce (name : DeclName) : Tm Unit 0 :=
  if name = `source then .app (.const `operation) (.const `argument) else .const name

def replaceArgument (name : DeclName) : Tm Unit 0 :=
  if name = `argument then .const `replacement else .const name

/-- Later interpretations act inside bodies inserted by earlier ones. -/
theorem composed_body :
    expand (andThen introduce replaceArgument) (.const `source : Tm Unit 0) =
      .app (.const `operation) (.const `replacement) := by decide

/-- Associativity does not license exchanging interpretation order. -/
theorem order_matters :
    expand (andThen introduce replaceArgument) (.const `source : Tm Unit 0) ≠
      expand (andThen replaceArgument introduce) (.const `source : Tm Unit 0) := by decide

end Controls

#print axioms expand_andThen
#print axioms expandCtx_andThen
#print axioms andThen_associative
#print axioms TypedInterpretation.andThen
#print axioms TypedInterpretation.identity
#print axioms TypedInterpretation.composed_substituted_judgment
#print axioms Controls.composed_body
#print axioms Controls.order_matters

end ConstantExpansion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
