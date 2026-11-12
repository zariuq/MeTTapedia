import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughLater
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.OneSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlace

/-!
# Reading a store through its later declarations

`Through` names the stores decided past later declarations; this module **reads** them. With a budget of steps, the
reader tries in turn:
* the fragment's own reader;
* **strip the newest declaration**, when every equation strengthens past it (`separation`: the codes are inverted along
  the weakening and checked again in the older telescope), and read the strengthened store;
* **exchange the two newest declarations**, when the newer does not depend on the older (its type code inverts past
  the older one and forms in the older telescope), and read the exchanged store.

The reader returns the derivation it found, so it is sound by construction (`throughRead_sound`), and every store it
reads is settled when the fragment's stores are (`throughRead_settles`). The one solver's fragment is settled
(`one_settles`), and so is every store through later declarations over it (`throughOne_settles`), in particular every
store the reader finds through the mixed reader (`oneWitness`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section Views

variable {S : Setting Head L} (Q : ∀ {Γ : Context S.R}, EquationStore (TotalTerm Γ) → Prop)

/-- Read at the newest declaration of a context. -/
def atNewest {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (read : {Γ : Context S.R} → (type : TypeOver Γ) → (stored : EquationStore (TotalTerm (extend Γ type))) →
      Option (PLift (Through Q stored))) :
    Option (PLift (Through Q problem)) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact read type problem

/-- Read at the two newest declarations of a context. -/
def atTwo {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base) (problem : EquationStore (TotalTerm Θ))
    (read : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (PLift (Through Q stored))) :
    Option (PLift (Through Q problem)) := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact read older newer problem

end Views

section Reader

variable {S : Setting Head L} (Q : ∀ {Γ : Context S.R}, EquationStore (TotalTerm Γ) → Prop)
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **Strip the newest declaration** when every equation strengthens past it: the store is then the strengthened
store read past the declaration. -/
def stripNewest (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (stored : EquationStore (TotalTerm (extend Γ type)))
    (read : (strong : EquationStore (TotalTerm Γ)) → Option (PLift (Through Q strong))) :
    Option (PLift (Through Q stored)) :=
  let parts := ContextualDependentInPlace.separation facts roots heads algebra declared choices reducer fuel type stored
  if empty : parts.val.2.isEmpty = true then
    (read parts.val.1).map fun found => ⟨.equivalent (by
      have same := parts.property
      rw [List.isEmpty_iff.mp empty, List.nil_append] at same
      exact same) (.later type found.down)⟩
  else none

/-- **Exchange the two newest declarations** when the newer does not depend on the older: its type code inverts past
the older declaration and forms in the older telescope. -/
def exchangeNewest (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (read : (next : TypeOver Γ₀) →
      (exchanged : EquationStore (TotalTerm (ContextualDependentParameterExchange.context next older))) →
        Option (PLift (Through Q exchanged))) :
    Option (PLift (Through Q stored)) :=
  match (ContextualDependentInPlace.strengthenCode (n := Γ₀.arity) newer.code).map Subtype.val with
  | none => none
  | some code =>
      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀ code with
      | none => none
      | some next =>
          if same : newer.code = (ContextualDependentParameterExchange.second older next.val).code ∧
              newer.level = (ContextualDependentParameterExchange.second older next.val).level then by
            have independent : newer = ContextualDependentParameterExchange.second older next.val :=
              TypeOver.ext same.1 same.2
            subst independent
            exact (read next.val (ContextualDependentPrune.exchange S.levels older next.val stored).remaining).map
              fun found => ⟨.exchange older next.val found.down⟩
          else none

variable (qW : ∀ {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)), Option (PLift (Q problem)))

/-- **The reader of stores through later declarations**, with a budget of steps: the fragment's reader; or strip the
newest declaration; or exchange the two newest. It returns the derivation it found. -/
def throughRead (fuel : Nat) : (depth : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (PLift (Through Q problem))
  | 0, _, problem => (qW problem).map fun inside => ⟨.base inside.down⟩
  | depth + 1, Θ, problem =>
      match qW problem with
      | some inside => some ⟨.base inside.down⟩
      | none =>
          match newestOf facts roots heads algebra declared choices reducer fuel Θ with
          | none => none
          | some outer =>
              match atNewest Q outer problem (fun type stored =>
                  stripNewest Q facts roots heads algebra declared choices reducer fuel type stored
                    (throughRead fuel depth)) with
              | some found => some found
              | none =>
                  match newestOf facts roots heads algebra declared choices reducer fuel outer.base with
                  | none => none
                  | some inner => atTwo Q outer inner problem fun older newer stored =>
                      exchangeNewest Q facts roots heads algebra declared choices reducer fuel older newer stored
                        (fun _ exchanged => throughRead fuel depth exchanged)

/-- **The reader is sound by construction.** -/
theorem throughRead_sound {fuel depth : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (throughRead Q facts roots heads algebra declared choices reducer qW fuel depth problem).isSome = true) :
    Through Q problem :=
  ((throughRead Q facts roots heads algebra declared choices reducer qW fuel depth problem).get found).down

/-- **Every store the reader reads is settled** when every store of the fragment is. -/
theorem throughRead_settles
    (settle : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, Q problem → Settles problem)
    {fuel depth : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (throughRead Q facts roots heads algebra declared choices reducer qW fuel depth problem).isSome = true) :
    Settles problem :=
  through_settles settle (throughRead_sound Q facts roots heads algebra declared choices reducer qW found)

end Reader

/-! ## The one solver through later declarations -/

section One

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Miller.Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
  (glbTotal : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)
  (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)

include facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening joinSound spec
  glbTotal joinTotal in
/-- **The one solver's fragment is settled**, by a run of the one solver. -/
theorem one_settles {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InOne choices problem) :
    Settles problem := by
  obtain ⟨fuel, decided⟩ := one_decided choices facts roots heads algebra rigid complete normalizes inh
    headTypingUnique declared strengthening join joinSound glb spec glbTotal joinTotal inside
  rcases (decided fuel le_rfl).2 with ⟨state, finished, _, _⟩ | ⟨absent, _⟩
  · exact .inl ⟨state, finished⟩
  · exact .inr absent

include facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening joinSound spec
  glbTotal joinTotal in
/-- **Every store through later declarations over the one solver's fragment is settled**: a principal answer over the
instantiated, reordered telescope, or no solution. -/
theorem throughOne_settles {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : Through (InOne choices) problem) : Settles problem :=
  through_settles (fun inside => one_settles choices facts roots heads algebra rigid complete normalizes inh
    headTypingUnique declared strengthening join joinSound glb spec glbTotal joinTotal inside) inside

omit [DecidableRel S.R.headEq] in
/-- The one solver's fragment, read by the mixed reader (Miller patterns with arrow codes). -/
def oneWitness {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (PLift (InOne choices problem)) :=
  if mixed : inMixedB choices problem = true then some ⟨inOne_of_mixed choices (inMixed_of_B choices mixed)⟩
  else none

end One

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
