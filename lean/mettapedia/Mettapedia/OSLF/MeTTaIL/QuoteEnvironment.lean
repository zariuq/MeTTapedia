import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

/-!
# Object-variable substitution at a quotation

A contextual quotation `Q[closure body env]` holds a body together with an
explicit environment for the body's own context.  The environment is a
telescope of the existing explicit one-variable substitution node
`Pattern.subst`: `closure body [v₀, …, vₙ₋₁]` is
`.subst (… (.subst body vₙ₋₁) …) v₀`, and entry `vⱼ` lies under the `j`
earlier entries.  The body is *sealed* when it is inScope by its environment
alone.

The single substitution operation is the existing simultaneous de Bruijn
action `ContextSubstitution.substitute`, which commutes with every
constructor, quotation included.  It does not execute explicit substitution
nodes, so on a contextual quotation it composes the outer substitution with
the environment and leaves the sealed body untouched (`substitute_closure`).
Realization executes every explicit substitution node; on quotations it turns
the contextual presentation into the transparent one, and it commutes with
substitution for every term (`realize_substitute`).

The sealed presentation is the contextual one with empty environments.  The
tree's present binder elimination leaves an outer index inside a genuine
quotation unchanged; the last section shows that this produces an ill-inScope
term.

Evaluation at a drop (whether a received quotation runs) is a separate
question, treated in `ReceivedNames.lean`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteEnvironment

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-! ## Renaming is substitution -/

/-- The assignment that inserts `amount` fresh variables at `cutoff`. -/
def insertAt (cutoff amount : Nat) : Assignment :=
  fun index => if index < cutoff then .bvar index else .bvar (index + amount)

theorem lift_insertAt (arity cutoff amount : Nat) :
    lift arity (insertAt cutoff amount) = insertAt (cutoff + arity) amount := by
  funext index
  simp only [lift, insertAt]
  by_cases below : index < arity
  · simp [below, show index < cutoff + arity by omega]
  · by_cases inner : index - arity < cutoff
    · simp only [below, inner, ite_false, ite_true, liftBVars, Nat.zero_le,
        show index < cutoff + arity by omega]
      congr 1
      omega
    · simp only [below, inner, ite_false, liftBVars, Nat.zero_le, ite_true,
        show ¬ index < cutoff + arity by omega]
      congr 1
      omega

/-- De Bruijn lifting is the substitution of a renaming. -/
theorem liftBVars_eq_substitute (cutoff amount : Nat) (pattern : Pattern) :
    liftBVars cutoff amount pattern = substitute (insertAt cutoff amount) pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      simp only [liftBVars, substitute, insertAt]
      by_cases below : index < cutoff
      · simp [below, show ¬ index ≥ cutoff by omega]
      · simp [below, show index ≥ cutoff by omega]
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [liftBVars, liftBVarsList_eq_map, substitute, substituteList_eq_map]
      exact congrArg (Pattern.apply constructor)
        (List.map_congr_left fun p hp => ih p hp cutoff)
  | hlambda name body ih => simp only [liftBVars, substitute, lift_insertAt, ih]
  | hmultiLambda arity names body ih => simp only [liftBVars, substitute, lift_insertAt, ih]
  | hsubst body value ihBody ihValue =>
      simp only [liftBVars, substitute, lift_insertAt, ihBody, ihValue]
  | hcollection kind elements rest ih =>
      simp only [liftBVars, liftBVarsList_eq_map, substitute, substituteList_eq_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp cutoff)

/-! ## The substitution lemma -/

/-- Substituting into a weakened term ignores the weakened variable. -/
theorem substitute_single_liftBVars (value pattern : Pattern) :
    substitute (single value) (liftBVars 0 1 pattern) = pattern := by
  rw [liftBVars_eq_substitute, substitute_comp]
  conv_rhs => rw [← substitute_id pattern]
  congr 1

/-- **Substitution lemma.** An outer substitution after eliminating the
innermost variable equals eliminating it with the substituted value after
substituting beneath it. -/
theorem substitute_substitute_single (σ : Assignment) (value body : Pattern) :
    substitute σ (substitute (single value) body) =
      substitute (single (substitute σ value)) (substitute (lift 1 σ) body) := by
  rw [substitute_comp, substitute_comp]
  congr 1
  funext index
  cases index with
  | zero => simp [single, lift, substitute]
  | succ index => simp [single, lift, substitute, substitute_single_liftBVars]

/-- Lifting commutes with eliminating the innermost variable. -/
theorem liftBVars_substitute_single (cutoff amount : Nat) (value body : Pattern) :
    liftBVars cutoff amount (substitute (single value) body) =
      substitute (single (liftBVars cutoff amount value))
        (liftBVars (cutoff + 1) amount body) := by
  simp only [liftBVars_eq_substitute]
  rw [← lift_insertAt 1 cutoff amount]
  exact substitute_substitute_single _ _ _

/-- The same lemma for the tree's binder-eliminating operation, with the inner
binder `x` at level `0` and the outer binder `y` at level `1`:
`t[x := a][y := b] = t[y := b][x := a[y := b]]`. -/
theorem instantiateBVar_instantiateBVar (outer inner body : Pattern) :
    instantiateBVar outer (instantiateBVar inner body) =
      instantiateBVar (instantiateBVar outer inner) (instantiateBVarAt 1 outer body) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar,
    ← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar,
    ← substitute_lift_single outer body 1]
  exact substitute_substitute_single (single outer) inner body

/-! ## Transparent elimination: scope and composition -/

/-- Eliminate the innermost variable with `replacement`: substitution enters
every constructor, quotation included. -/
abbrev transparent (replacement body : Pattern) : Pattern :=
  substitute (single replacement) body

theorem transparent_eq_instantiateBVar (replacement body : Pattern) :
    transparent replacement body = instantiateBVar replacement body :=
  substitute_single_eq_instantiateBVar replacement body

theorem wellScopedAssignment_single {depth : Nat} {replacement : Pattern}
    (inScope : replacement.isWellScopedAt depth = true) :
    WellScopedAssignment (depth + 1) depth (single replacement) := by
  intro index below
  cases index with
  | zero => exact inScope
  | succ index =>
      simp only [single, Pattern.isWellScopedAt]
      exact decide_eq_true (by omega)

/-- **Scope (transparent).** -/
theorem transparent_isWellScopedAt {depth : Nat} {replacement body : Pattern}
    (bodyScoped : body.isWellScopedAt (depth + 1) = true)
    (replacementScoped : replacement.isWellScopedAt depth = true) :
    (transparent replacement body).isWellScopedAt depth = true :=
  substitute_wellScoped (wellScopedAssignment_single replacementScoped) bodyScoped

/-- **Composition (transparent).** `t[x := a][y := b] = t[y := b][x := a[y := b]]`. -/
theorem transparent_transparent (outer inner body : Pattern) :
    transparent outer (transparent inner body) =
      transparent (transparent outer inner) (substitute (lift 1 (single outer)) body) :=
  substitute_substitute_single (single outer) inner body

/-! ## Realization -/

mutual
  /-- Execute every explicit substitution node. -/
  def realize : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments => .apply constructor (realizeList arguments)
    | .lambda name body => .lambda name (realize body)
    | .multiLambda arity names body => .multiLambda arity names (realize body)
    | .subst body value => substitute (single (realize value)) (realize body)
    | .collection kind elements rest => .collection kind (realizeList elements) rest

  def realizeList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => realize pattern :: realizeList patterns
end

@[simp] theorem realizeList_eq_map :
    ∀ patterns : List Pattern, realizeList patterns = patterns.map realize
  | [] => rfl
  | pattern :: patterns => by
      simp only [realizeList, List.map_cons, realizeList_eq_map patterns]

theorem realize_liftBVars (cutoff amount : Nat) (pattern : Pattern) :
    realize (liftBVars cutoff amount pattern) = liftBVars cutoff amount (realize pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      show realize (liftBVars cutoff amount (.bvar index)) =
        liftBVars cutoff amount (.bvar index)
      simp only [liftBVars]
      split <;> rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [liftBVars, liftBVarsList_eq_map, realize, realizeList_eq_map, List.map_map]
      exact congrArg (Pattern.apply constructor)
        (List.map_congr_left fun p hp => ih p hp cutoff)
  | hlambda name body ih => simp only [liftBVars, realize, ih]
  | hmultiLambda arity names body ih => simp only [liftBVars, realize, ih]
  | hsubst body value ihBody ihValue =>
      simp only [liftBVars, realize, ihBody, ihValue, liftBVars_substitute_single]
  | hcollection kind elements rest ih =>
      simp only [liftBVars, liftBVarsList_eq_map, realize, realizeList_eq_map, List.map_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp cutoff)

theorem realize_lift (arity : Nat) (σ : Assignment) :
    (fun index => realize (lift arity σ index)) =
      lift arity (fun index => realize (σ index)) := by
  funext index
  simp only [lift]
  split
  · rfl
  · exact realize_liftBVars 0 arity _

/-- **Observation.** Realization commutes with substitution, for every term
and every assignment. -/
theorem realize_substitute (σ : Assignment) (pattern : Pattern) :
    realize (substitute σ pattern) =
      substitute (fun index => realize (σ index)) (realize pattern) := by
  induction pattern using Pattern.inductionOn generalizing σ with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [substitute, substituteList_eq_map, realize, realizeList_eq_map, List.map_map]
      exact congrArg (Pattern.apply constructor)
        (List.map_congr_left fun p hp => ih p hp σ)
  | hlambda name body ih => simp only [substitute, realize, ih, realize_lift]
  | hmultiLambda arity names body ih => simp only [substitute, realize, ih, realize_lift]
  | hsubst body value ihBody ihValue =>
      simp only [substitute, realize, ihBody, ihValue, realize_lift,
        substitute_substitute_single]
  | hcollection kind elements rest ih =>
      simp only [substitute, substituteList_eq_map, realize, realizeList_eq_map, List.map_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp σ)

/-- Transparent elimination of the realized term equals realization after
elimination, whenever the replacement carries no unexecuted explicit
substitution. -/
theorem realize_transparent {replacement : Pattern}
    (realized : realize replacement = replacement) (body : Pattern) :
    realize (transparent replacement body) = transparent replacement (realize body) := by
  rw [transparent, realize_substitute]
  congr 1
  funext index
  cases index with
  | zero => exact realized
  | succ _ => rfl

/-! ## Contextual quotations -/

/-- `closure body [v₀, …, vₙ₋₁]` is `.subst (… (.subst body vₙ₋₁) …) v₀`. -/
def closure (body : Pattern) : List Pattern → Pattern
  | [] => body
  | value :: environment => .subst (closure body environment) value

/-- How an outer substitution acts on an environment telescope: entry `j`
lies under the `j` earlier entries. -/
def substituteEnvironment (σ : Assignment) : List Pattern → List Pattern
  | [] => []
  | value :: environment =>
      substitute σ value :: substituteEnvironment (lift 1 σ) environment

@[simp] theorem substituteEnvironment_length (σ : Assignment) (environment : List Pattern) :
    (substituteEnvironment σ environment).length = environment.length := by
  induction environment generalizing σ with
  | nil => rfl
  | cons _ _ ih => simp [substituteEnvironment, ih]

private theorem lift_one_fixes {arity : Nat} {σ : Assignment}
    (fixes : ∀ index, index < arity → σ index = .bvar index) (count : Nat) :
    ∀ index, index < arity + count → lift count σ index = .bvar index := by
  intro index below
  simp only [lift]
  split
  · rfl
  · rw [fixes (index - count) (by omega)]
    simp only [liftBVars, Nat.zero_le, ite_true]
    congr 1
    omega

/-- An assignment that fixes the first `arity` variables fixes every term
inScope by them. -/
theorem substitute_eq_self_of_fixes {arity : Nat} {σ : Assignment}
    (fixes : ∀ index, index < arity → σ index = .bvar index) {pattern : Pattern}
    (inScope : pattern.isWellScopedAt arity = true) :
    substitute σ pattern = pattern := by
  induction pattern using Pattern.inductionOn generalizing arity σ with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at inScope
      exact fixes index inScope
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      simp only [substitute, substituteList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id arguments]
      exact List.map_congr_left fun p hp =>
        ih p hp fixes ((isWellScopedListAt_eq_true_iff _ _).mp inScope p hp)
  | hlambda name body ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      simp only [substitute]
      congr 1
      exact ih (lift_one_fixes fixes 1) inScope
  | hmultiLambda count names body ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      simp only [substitute]
      congr 1
      exact ih (lift_one_fixes fixes count) inScope
  | hsubst body value ihBody ihValue =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
      simp only [substitute]
      congr 1
      · exact ihBody (lift_one_fixes fixes 1) inScope.1
      · exact ihValue fixes inScope.2
  | hcollection kind elements rest ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      simp only [substitute, substituteList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elements]
      exact List.map_congr_left fun p hp =>
        ih p hp fixes ((isWellScopedListAt_eq_true_iff _ _).mp inScope p hp)

theorem lift_fixes (arity : Nat) (σ : Assignment) :
    ∀ index, index < arity → lift arity σ index = .bvar index := by
  intro index below
  simp [lift, below]

/-- **Contextual elimination.** On a closure whose body is inScope by its own
environment, an outer substitution acts on the environment only. -/
theorem substitute_closure (σ : Assignment) {body : Pattern} (environment : List Pattern)
    (sealed : body.isWellScopedAt environment.length = true) :
    substitute σ (closure body environment) =
      closure body (substituteEnvironment σ environment) := by
  suffices general : ∀ (environment : List Pattern) (layers : Nat) (σ : Assignment),
      body.isWellScopedAt (layers + environment.length) = true →
      substitute (lift layers σ) (closure body environment) =
        closure body (substituteEnvironment (lift layers σ) environment) by
    simpa using general environment 0 σ (by simpa using sealed)
  intro environment
  induction environment with
  | nil =>
      intro layers σ inScope
      exact substitute_eq_self_of_fixes (lift_fixes layers σ) (by simpa [closure] using inScope)
  | cons value environment ih =>
      intro layers σ inScope
      simp only [closure, substitute, substituteEnvironment, lift_lift]
      congr 1
      exact ih (layers + 1) σ (by simpa [Nat.add_assoc, Nat.add_comm 1] using inScope)

/-- Contextual elimination of a quotation. -/
theorem substitute_contextualQuote (quote : String) (σ : Assignment) {body : Pattern}
    (environment : List Pattern) (sealed : body.isWellScopedAt environment.length = true) :
    substitute σ (.apply quote [closure body environment]) =
      .apply quote [closure body (substituteEnvironment σ environment)] := by
  simp [substitute, substitute_closure σ environment sealed]

/-- A sealed quotation (empty environment) is untouched by every substitution. -/
theorem substitute_sealedQuote (quote : String) (σ : Assignment) {body : Pattern}
    (sealed : body.isWellScopedAt 0 = true) :
    substitute σ (.apply quote [body]) = .apply quote [body] := by
  simpa [closure, substituteEnvironment] using
    substitute_contextualQuote quote σ (body := body) [] sealed

/-- **Composition (contextual).** Successive outer substitutions compose
exactly on the environment. -/
theorem substituteEnvironment_comp (σ τ : Assignment) (environment : List Pattern) :
    substituteEnvironment τ (substituteEnvironment σ environment) =
      substituteEnvironment (fun index => substitute τ (σ index)) environment := by
  induction environment generalizing σ τ with
  | nil => rfl
  | cons value environment ih =>
      simp only [substituteEnvironment, substitute_comp, ih, lift_comp]

/-- Entry `j` of an environment lies `j` binders below the closure. -/
def EnvironmentScopedAt : Nat → List Pattern → Prop
  | _, [] => True
  | depth, value :: environment =>
      value.isWellScopedAt depth = true ∧ EnvironmentScopedAt (depth + 1) environment

theorem closure_isWellScopedAt {body : Pattern} :
    ∀ {depth : Nat} {environment : List Pattern},
      body.isWellScopedAt (depth + environment.length) = true →
      EnvironmentScopedAt depth environment →
      (closure body environment).isWellScopedAt depth = true
  | _, [], bodyScoped, _ => by simpa [closure] using bodyScoped
  | depth, value :: environment, bodyScoped, ⟨valueScoped, rest⟩ => by
      simp only [closure, Pattern.isWellScopedAt, Bool.and_eq_true]
      exact ⟨closure_isWellScopedAt
        (by simpa [Nat.add_assoc, Nat.add_comm 1] using bodyScoped) rest, valueScoped⟩

theorem environmentScopedAt_substitute {source target : Nat} {σ : Assignment}
    (wellScoped : WellScopedAssignment source target σ) :
    ∀ {environment : List Pattern}, EnvironmentScopedAt source environment →
      EnvironmentScopedAt target (substituteEnvironment σ environment)
  | [], _ => trivial
  | _ :: _, ⟨valueScoped, rest⟩ =>
      ⟨substitute_wellScoped wellScoped valueScoped,
        environmentScopedAt_substitute (wellScoped.lift 1) rest⟩

/-- **Scope (contextual).** Eliminating the innermost variable of a contextual
quotation keeps the body and yields a inScope quotation. -/
theorem contextualQuote_isWellScopedAt (quote : String) {depth : Nat}
    {replacement body : Pattern} {environment : List Pattern}
    (sealed : body.isWellScopedAt environment.length = true)
    (environmentScoped : EnvironmentScopedAt (depth + 1) environment)
    (replacementScoped : replacement.isWellScopedAt depth = true) :
    substitute (single replacement) (.apply quote [closure body environment]) =
        .apply quote [closure body (substituteEnvironment (single replacement) environment)] ∧
      (substitute (single replacement)
        (.apply quote [closure body environment])).isWellScopedAt depth = true := by
  refine ⟨substitute_contextualQuote quote _ environment sealed, ?_⟩
  rw [substitute_contextualQuote quote _ environment sealed]
  simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true]
  exact closure_isWellScopedAt
    (isWellScopedAt_mono (by simpa using sealed) (by simp))
    (environmentScopedAt_substitute (wellScopedAssignment_single replacementScoped)
      environmentScoped)

/-- Realizing a closure executes its environment. -/
theorem realize_closure_cons (body value : Pattern) (environment : List Pattern) :
    realize (closure body (value :: environment)) =
      substitute (single (realize value)) (realize (closure body environment)) := rfl

/-! ## Controls: a quotation mentioning the exiting binder -/

section Controls

open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation (instantiate)

/-- A reflective presentation on one carrier. -/
def oneCarrier : ReflectivePresentationDecl where
  name := "one"
  processSort := "Term"
  nameSort := "Term"
  quoteConstructor := "Quote"
  dropConstructor := "Drop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "Nil"
  quoteDropEquation := "QuoteDrop"
  -- Closed: the baseline whose quoted code the environments below keep opaque.
  quoteScope := .closed

/-- The received name `@0`. -/
def receivedName : Pattern := .apply "Quote" [.apply "Nil" []]

/-- Under the binder `x` (index `0`): `F(@G(x))`. -/
def transparentSpelling : Pattern :=
  .apply "F" [.apply "Quote" [.apply "G" [.bvar 0]]]

/-- The same quotation with its dependency in an explicit environment:
`F(@(G(z)[z := x]))`. -/
def contextualSpelling : Pattern :=
  .apply "F" [.apply "Quote" [closure (.apply "G" [.bvar 0]) [.bvar 0]]]

theorem spellings_inScope :
    transparentSpelling.isWellScopedAt 1 = true ∧
      contextualSpelling.isWellScopedAt 1 = true := by decide

theorem contextualSpelling_realizes : realize contextualSpelling = transparentSpelling := by
  decide

/-- Sealed admission rejects the quotation in both spellings. -/
theorem sealed_rejects :
    binderSafeAt "Quote" 1 transparentSpelling = false ∧
      binderSafeAt "Quote" 1 contextualSpelling = false := by decide

/-- Transparent elimination realizes the dependency inside the quotation. -/
theorem transparent_realizes :
    transparent receivedName transparentSpelling =
      .apply "F" [.apply "Quote" [.apply "G" [receivedName]]] := by decide

/-- Contextual elimination keeps the environment and leaves the body `G(z)`
untouched. -/
theorem contextual_keeps_environment :
    transparent receivedName contextualSpelling =
      .apply "F" [.apply "Quote" [closure (.apply "G" [.bvar 0]) [receivedName]]] := by
  decide

theorem control_observation :
    realize (transparent receivedName contextualSpelling) =
      transparent receivedName transparentSpelling := by decide

theorem control_results_inScope :
    (transparent receivedName transparentSpelling).isWellScopedAt 0 = true ∧
      (transparent receivedName contextualSpelling).isWellScopedAt 0 = true := by decide

/-- **Raw counterexample.** The tree's elimination leaves the quotation as
written, so the eliminated binder dangles. -/
theorem raw_dangles :
    instantiate oneCarrier 0 receivedName transparentSpelling = transparentSpelling ∧
      (instantiate oneCarrier 0 receivedName transparentSpelling).isWellScopedAt 0 = false := by
  decide

/-- Positive control: a sealed quotation beside a use of the binder.  Sealed
admission accepts it and transparent elimination agrees with the tree's. -/
def sealedSpelling : Pattern :=
  .apply "F" [.apply "Quote" [.apply "G" [.apply "Nil" []]], .apply "H" [.bvar 0]]

theorem sealed_agreement :
    binderSafeAt "Quote" 1 sealedSpelling = true ∧
      transparent receivedName sealedSpelling =
        .apply "F" [.apply "Quote" [.apply "G" [.apply "Nil" []]], .apply "H" [receivedName]] ∧
      instantiate oneCarrier 0 receivedName sealedSpelling =
        transparent receivedName sealedSpelling := by
  decide +kernel

end Controls

end Mettapedia.OSLF.MeTTaIL.QuoteEnvironment

#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.lift_insertAt
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.liftBVars_eq_substitute
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.substitute_single_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.substitute_substitute_single
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.liftBVars_substitute_single
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.instantiateBVar_instantiateBVar
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.transparent_eq_instantiateBVar
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.wellScopedAssignment_single
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.transparent_isWellScopedAt
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.transparent_transparent
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.realize_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.realize_lift
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.realize_substitute
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.realize_transparent
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.substitute_eq_self_of_fixes
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.lift_fixes
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.substitute_closure
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.substitute_contextualQuote
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.substitute_sealedQuote
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.substituteEnvironment_comp
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.closure_isWellScopedAt
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.environmentScopedAt_substitute
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.contextualQuote_isWellScopedAt
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.realize_closure_cons
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.spellings_inScope
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.contextualSpelling_realizes
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.sealed_rejects
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.transparent_realizes
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.contextual_keeps_environment
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.control_observation
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.control_results_inScope
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.raw_dangles
#print axioms Mettapedia.OSLF.MeTTaIL.QuoteEnvironment.sealed_agreement
