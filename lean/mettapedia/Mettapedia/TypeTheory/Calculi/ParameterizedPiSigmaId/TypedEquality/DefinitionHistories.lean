import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremStability

/-!
# Conservative histories of checked dependent definitions

Entries retain their authored names, types and closed bodies. The inventory is
stored newest first; each body is checked in the preceding stage. Admission
does not accept a witness typed only after installing its own declaration.

The base supplies formation of its primitive declarations and stability of its
primitive computations under expansion of undeclared names. Formation,
stability and conservative erasure of every later stage are constructed from
the checked history. Definitions may name carriers as well as ordinary terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace DefinitionHistories

open Normalization StrongNormalization
open ConstantExpansion (constantNames)

variable {Head : Type}

/-- One closed definition, before checking or installation. -/
structure Definition (Head : Type) where
  name : DeclName
  type : Tm Head 0
  body : Tm Head 0

def Definition.install (definition : Definition Head) (rules : Rules Head) : Rules Head :=
  rules.withTheorem definition.name definition.type definition.body

/-- Newest-first storage retains the chronological checking boundary. -/
def stage (base : Rules Head) : List (Definition Head) → Rules Head
  | [] => base
  | definition :: prior => definition.install (stage base prior)

/-- Primitive declarations must be formed; primitive computation may inspect
declared constants, but must be stable under expanding an undeclared name. -/
structure PrimitiveSafety (rules : Rules Head) : Prop where
  declarations : ∀ {name type}, rules.constantType name = some type →
    IsType rules .nil type
  freshComputation : ∀ {name}, rules.constantType name = none →
    ∀ body : Tm Head 0, rules.computation.ExpandStable (unfoldBodies name body)

/-- Admission retains actual formation and body derivations in the prior
stage, and refuses replacement of an already declared name. -/
inductive Checked (base : Rules Head) : List (Definition Head) → Prop where
  | nil : Checked base []
  | cons {prior : List (Definition Head)} (definition : Definition Head) :
      Checked base prior → (stage base prior).constantType definition.name = none →
      IsType (stage base prior) .nil definition.type →
      Typed (stage base prior) .nil definition.body definition.type →
      Checked base (definition :: prior)

theorem PrimitiveSafety.declared_avoids {rules : Rules Head}
    (safe : PrimitiveSafety rules) {name constant : DeclName} {type : Tm Head 0}
    (fresh : rules.constantType name = none)
    (known : rules.constantType constant = some type) :
    name ∉ constantNames type := by
  obtain ⟨_, _, typed⟩ := safe.declarations known
  exact typed.avoids fresh

theorem PrimitiveSafety.install {rules : Rules Head} (safe : PrimitiveSafety rules)
    (definition : Definition Head) (fresh : rules.constantType definition.name = none)
    (formed : IsType rules .nil definition.type)
    (typed : Typed rules .nil definition.body definition.type) :
    PrimitiveSafety (definition.install rules) where
  declarations := by
    intro name type known
    have included := withTheorem_sub (T := definition.type) (body := definition.body) fresh
    by_cases same : name = definition.name
    · subst name
      have typeEq : definition.type = type := by
        simpa only [Definition.install, withTheorem_constantType_self, Option.some.injEq]
          using known
      subst type
      obtain ⟨level, universeWitness, formedType⟩ := formed
      exact ⟨level, universeWitness, Derivable.mono included formedType⟩
    · have old : rules.constantType name = some type := by
        simpa only [Definition.install, withTheorem_constantType_of_ne same] using known
      obtain ⟨level, universeWitness, formedType⟩ := safe.declarations old
      exact ⟨level, universeWitness, Derivable.mono included formedType⟩
  freshComputation := by
    intro name freshLater body
    have distinct : name ≠ definition.name := by
      intro same
      subst name
      simp only [Definition.install, withTheorem_constantType_self] at freshLater
      cases freshLater
    have freshPrior : rules.constantType name = none := by
      simpa only [Definition.install, withTheorem_constantType_of_ne distinct]
        using freshLater
    intro n left right step
    rcases step with inherited | ⟨rfl, rfl⟩
    · exact .inl (safe.freshComputation freshPrior body inherited)
    · have fixedBody := unfoldTm_eq_self (body := body) (typed.avoids freshPrior)
      have fixedName := unfoldTm_const_of_ne (body := body) (n := n) distinct.symm
      exact .inr ⟨fixedName, by
        change unfoldTm name body (liftClosed definition.body) = liftClosed definition.body
        rw [unfoldTm_liftClosed, fixedBody]⟩

/-- No later stage receives its safety laws as admission assumptions. -/
theorem Checked.safety {base : Rules Head} (safe : PrimitiveSafety base)
    {definitions : List (Definition Head)} (checked : Checked base definitions) :
    PrimitiveSafety (stage base definitions) := by
  induction checked with
  | nil => exact safe
  | cons definition _ fresh formed typed ih => exact ih.install definition fresh formed typed

theorem Checked.inclusion {base : Rules Head} {definitions : List (Definition Head)}
    (checked : Checked base definitions) : RulesSub base (stage base definitions) := by
  induction checked with
  | nil => exact .refl base
  | cons definition _ fresh _ _ ih =>
      exact ih.trans (withTheorem_sub fresh)

/-- Erasure expands a definition and then erases its preceding dependencies. -/
def erase {n : Nat} : List (Definition Head) → Tm Head n → Tm Head n
  | [], term => term
  | definition :: prior, term =>
      erase prior (unfoldTm definition.name definition.body term)

def eraseContext {n : Nat} : List (Definition Head) → Ctx Head n → Ctx Head n
  | [], context => context
  | definition :: prior, context =>
      eraseContext prior (Ctx.unfold definition.name definition.body context)

def eraseStatement : List (Definition Head) → Statement Head → Statement Head
  | [], statement => statement
  | definition :: prior, statement =>
      eraseStatement prior (Statement.unfold definition.name definition.body statement)

@[simp] theorem erase_typing (definitions : List (Definition Head))
    {n : Nat} (context : Ctx Head n) (term type : Tm Head n) :
    eraseStatement definitions (.typing context term type) =
      .typing (eraseContext definitions context) (erase definitions term) (erase definitions type) := by
  induction definitions generalizing context term type with
  | nil => rfl
  | cons definition prior ih => exact ih _ _ _

@[simp] theorem erase_equality (definitions : List (Definition Head))
    {n : Nat} (context : Ctx Head n) (left right type : Tm Head n) :
    eraseStatement definitions (.equality context left right type) =
      .equality (eraseContext definitions context) (erase definitions left)
        (erase definitions right) (erase definitions type) := by
  induction definitions generalizing context left right type with
  | nil => rfl
  | cons definition prior ih => exact ih _ _ _ _

/-- Erasure transports arbitrary typing, typed equality and subsumption
derivations, including their complete dependent context. -/
theorem Checked.erase_derivation {base : Rules Head} (safe : PrimitiveSafety base)
    {definitions : List (Definition Head)} (checked : Checked base definitions)
    {statement : Statement Head} (derivation : Derivable (stage base definitions) statement) :
    Derivable base (eraseStatement definitions statement) := by
  induction checked generalizing statement with
  | nil => exact derivation
  | cons definition prior fresh formed typed ih =>
      obtain ⟨_, _, typedType⟩ := formed
      have priorSafe := prior.safety safe
      exact ih (Derivable.unfoldTheorem typed (typed.avoids fresh)
        (typedType.avoids fresh) (priorSafe.declared_avoids fresh)
        (priorSafe.freshComputation fresh definition.body) derivation)

theorem Checked.erase_context {base : Rules Head} (safe : PrimitiveSafety base)
    {definitions : List (Definition Head)} (checked : Checked base definitions)
    {n : Nat} {context : Ctx Head n} (formed : CtxFormed (stage base definitions) context) :
    CtxFormed base (eraseContext definitions context) := by
  induction checked generalizing n context with
  | nil => exact formed
  | cons definition prior fresh formedType typed ih =>
      obtain ⟨_, _, typedType⟩ := formedType
      have priorSafe := prior.safety safe
      exact ih (CtxFormed.unfoldTheorem typed (typed.avoids fresh)
        (typedType.avoids fresh) (priorSafe.declared_avoids fresh)
        (priorSafe.freshComputation fresh definition.body) formed)

@[simp] theorem erase_rename (definitions : List (Definition Head))
    {n m : Nat} (rho : Ren n m) (term : Tm Head n) :
    erase definitions (rename rho term) = rename rho (erase definitions term) := by
  induction definitions generalizing term with
  | nil => rfl
  | cons definition prior ih =>
      simpa only [erase, unfoldTm_rename] using ih
        (unfoldTm definition.name definition.body term)

@[simp] theorem erase_subst (definitions : List (Definition Head))
    {n m : Nat} (sigma : Sub Head n m) (term : Tm Head n) :
    erase definitions (subst sigma term) =
      subst (fun index => erase definitions (sigma index)) (erase definitions term) := by
  induction definitions generalizing term sigma with
  | nil => rfl
  | cons definition prior ih =>
      simp only [erase, unfoldTm, ConstantExpansion.expand_subst, ih]

@[simp] theorem erase_inst0 (definitions : List (Definition Head))
    {n : Nat} (argument : Tm Head n) (body : Tm Head (n + 1)) :
    erase definitions (inst0 argument body) =
      inst0 (erase definitions argument) (erase definitions body) := by
  induction definitions generalizing argument body with
  | nil => rfl
  | cons definition prior ih => simp only [erase, unfoldTm_inst0, ih]

@[simp] theorem erase_head (definitions : List (Definition Head))
    {n : Nat} (head : Head) : erase definitions (.head head : Tm Head n) = .head head := by
  induction definitions <;> simp_all only [erase, unfoldTm_head]

@[simp] theorem eraseContext_nil (definitions : List (Definition Head)) :
    eraseContext definitions (.nil : Ctx Head 0) = .nil := by
  induction definitions <;> simp_all only [eraseContext, Ctx.unfold]

@[simp] theorem eraseContext_snoc (definitions : List (Definition Head))
    {n : Nat} (context : Ctx Head n) (type : Tm Head n) :
    eraseContext definitions (.snoc context type) =
      .snoc (eraseContext definitions context) (erase definitions type) := by
  induction definitions generalizing context type with
  | nil => rfl
  | cons definition prior ih => exact ih _ _

@[simp] theorem eraseContext_lookup (definitions : List (Definition Head))
    {n : Nat} (context : Ctx Head n) (index : Fin n) :
    Ctx.lookup (eraseContext definitions context) index =
      erase definitions (Ctx.lookup context index) := by
  induction definitions generalizing context with
  | nil => rfl
  | cons definition prior ih =>
      simp only [eraseContext, erase, ih, Ctx.lookup_unfold]

/-- Substitution components and all dependent types are erased by the same
map. Shared de Bruijn slots remain shared. -/
theorem Checked.erase_substitution {base : Rules Head} (safe : PrimitiveSafety base)
    {definitions : List (Definition Head)} (checked : Checked base definitions)
    {n m : Nat} {source : Ctx Head n} {target : Ctx Head m} {sigma : Sub Head n m}
    (typed : SubstMor (stage base definitions) source target sigma) :
    SubstMor base (eraseContext definitions source) (eraseContext definitions target)
      (fun index => erase definitions (sigma index)) := by
  intro index
  simpa only [erase_typing, erase_subst, eraseContext_lookup] using
    checked.erase_derivation safe (typed index)

/-- Formation in the base is enough to discharge every declaration-formation
obligation in the extended checking package. -/
theorem Checked.declarations_formed {base : Rules Head} (safe : PrimitiveSafety base)
    {definitions : List (Definition Head)} (checked : Checked base definitions)
    {name : DeclName} {type : Tm Head 0}
    (known : (stage base definitions).constantType name = some type) :
    IsType (stage base definitions) .nil type := (checked.safety safe).declarations known

/-- A base without primitive root computation has the required fresh-name
stability; its declaration formation is the remaining local obligation. -/
theorem PrimitiveSafety.ofNoRoots {rules : Rules Head}
    (formed : ∀ {name type}, rules.constantType name = some type → IsType rules .nil type)
    (noRoots : ∀ {n : Nat} {left right : Tm Head n}, ¬ rules.computation.step left right) :
    PrimitiveSafety rules where
  declarations := formed
  freshComputation := by
    intro _ _ _ _ _ _ step
    exact False.elim (noRoots step)

/-! ## Exact conservativity for syntax not naming the extension -/

def Avoids {n : Nat} (definitions : List (Definition Head)) (term : Tm Head n) : Prop :=
  ∀ definition ∈ definitions, definition.name ∉ constantNames term

def ContextAvoids (definitions : List (Definition Head)) : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc context type => ContextAvoids definitions context ∧ Avoids definitions type

def StatementAvoids (definitions : List (Definition Head)) : Statement Head → Prop
  | .typing context term type =>
      ContextAvoids definitions context ∧ Avoids definitions term ∧ Avoids definitions type
  | .equality context left right type =>
      ContextAvoids definitions context ∧ Avoids definitions left ∧
        Avoids definitions right ∧ Avoids definitions type
  | .sub context left right =>
      ContextAvoids definitions context ∧ Avoids definitions left ∧ Avoids definitions right

theorem erase_eq_self {definitions : List (Definition Head)} {n : Nat} {term : Tm Head n}
    (avoids : Avoids definitions term) : erase definitions term = term := by
  induction definitions with
  | nil => rfl
  | cons definition prior ih =>
      change erase prior (unfoldTm definition.name definition.body term) = term
      rw [unfoldTm_eq_self (avoids definition (List.mem_cons_self ..))]
      exact ih (fun d mem => avoids d (List.mem_cons_of_mem _ mem))

theorem eraseContext_eq_self {definitions : List (Definition Head)}
    {n : Nat} {context : Ctx Head n} (avoids : ContextAvoids definitions context) :
    eraseContext definitions context = context := by
  induction context with
  | nil => exact eraseContext_nil definitions
  | snoc context type ih =>
      rw [eraseContext_snoc, ih avoids.1, erase_eq_self avoids.2]

@[simp] theorem erase_subsumption (definitions : List (Definition Head))
    {n : Nat} (context : Ctx Head n) (left right : Tm Head n) :
    eraseStatement definitions (.sub context left right) =
      .sub (eraseContext definitions context) (erase definitions left) (erase definitions right) := by
  induction definitions generalizing context left right with
  | nil => rfl
  | cons definition prior ih => exact ih _ _ _

theorem eraseStatement_eq_self {definitions : List (Definition Head)}
    {statement : Statement Head} (avoids : StatementAvoids definitions statement) :
    eraseStatement definitions statement = statement := by
  cases statement with
  | typing context term type =>
      rw [erase_typing, eraseContext_eq_self avoids.1, erase_eq_self avoids.2.1,
        erase_eq_self avoids.2.2]
  | equality context left right type =>
      rw [erase_equality, eraseContext_eq_self avoids.1, erase_eq_self avoids.2.1,
        erase_eq_self avoids.2.2.1, erase_eq_self avoids.2.2.2]
  | sub context left right =>
      rw [erase_subsumption, eraseContext_eq_self avoids.1, erase_eq_self avoids.2.1,
        erase_eq_self avoids.2.2]

/-- The extension proves exactly the same old sequents, with typed equality
and subsumption included, not only closed theorem inhabitation. -/
theorem Checked.conservative {base : Rules Head} (safe : PrimitiveSafety base)
    {definitions : List (Definition Head)} (checked : Checked base definitions)
    {statement : Statement Head} (avoids : StatementAvoids definitions statement) :
    Derivable (stage base definitions) statement ↔ Derivable base statement := by
  constructor
  · intro derivation
    simpa only [eraseStatement_eq_self avoids] using checked.erase_derivation safe derivation
  · exact Derivable.mono checked.inclusion

/-- A proof may use every new name internally. An old closed type acquires
an inhabitant exactly when the base already had one. -/
theorem Checked.inhabited_iff {base : Rules Head} (safe : PrimitiveSafety base)
    {definitions : List (Definition Head)} (checked : Checked base definitions)
    {type : Tm Head 0} (avoids : Avoids definitions type) :
    (∃ term, Typed (stage base definitions) .nil term type) ↔
      ∃ term, Typed base .nil term type := by
  constructor
  · rintro ⟨term, typed⟩
    refine ⟨erase definitions term, ?_⟩
    simpa only [erase_typing, eraseContext_nil, erase_eq_self avoids] using
      checked.erase_derivation safe typed
  · rintro ⟨term, typed⟩
    exact ⟨term, Derivable.mono checked.inclusion typed⟩

/-! ## Incremental checking and coherent erasure -/

theorem stage_append (base : Rules Head) (newer prior : List (Definition Head)) :
    stage base (newer ++ prior) = stage (stage base prior) newer := by
  induction newer with
  | nil => rfl
  | cons definition newer ih => simp only [List.cons_append, stage, ih]

theorem Checked.append {base : Rules Head} {prior newer : List (Definition Head)}
    (earlier : Checked base prior) (later : Checked (stage base prior) newer) :
    Checked base (newer ++ prior) := by
  induction later with
  | nil => exact earlier
  | cons definition _ fresh formed typed ih =>
      apply Checked.cons definition ih
      · simpa only [stage_append] using fresh
      · simpa only [stage_append] using formed
      · simpa only [stage_append] using typed

theorem erase_append (newer prior : List (Definition Head))
    {n : Nat} (term : Tm Head n) :
    erase (newer ++ prior) term = erase prior (erase newer term) := by
  induction newer generalizing term with
  | nil => rfl
  | cons definition newer ih => exact ih _

theorem eraseContext_append (newer prior : List (Definition Head))
    {n : Nat} (context : Ctx Head n) :
    eraseContext (newer ++ prior) context = eraseContext prior (eraseContext newer context) := by
  induction newer generalizing context with
  | nil => rfl
  | cons definition newer ih => exact ih _

theorem eraseStatement_append (newer prior : List (Definition Head))
    (statement : Statement Head) :
    eraseStatement (newer ++ prior) statement =
      eraseStatement prior (eraseStatement newer statement) := by
  induction newer generalizing statement with
  | nil => rfl
  | cons definition newer ih => exact ih _

/-- Normalization is preserved for every admitted history. The base
normalization theorem remains an explicit metatheoretic requirement. -/
theorem Checked.normalizes {base : Rules Head} (safe : PrimitiveSafety base)
    (normalizes : ∀ {n : Nat} {context : Ctx Head n} {term type : Tm Head n},
      CtxFormed base context → Typed base context term type → SN base term ∧ SN base type)
    {definitions : List (Definition Head)} (checked : Checked base definitions)
    {n : Nat} {context : Ctx Head n} {term type : Tm Head n}
    (formed : CtxFormed (stage base definitions) context)
    (typed : Typed (stage base definitions) context term type) :
    SN (stage base definitions) term ∧ SN (stage base definitions) type := by
  induction checked generalizing n context term type with
  | nil => exact normalizes formed typed
  | cons definition prior fresh formedType bodyTyped ih =>
      have priorSafe := prior.safety safe
      exact withTheorem_sn ih fresh formedType bodyTyped
        (priorSafe.declared_avoids fresh)
        (priorSafe.freshComputation fresh definition.body) formed typed

end DefinitionHistories
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
