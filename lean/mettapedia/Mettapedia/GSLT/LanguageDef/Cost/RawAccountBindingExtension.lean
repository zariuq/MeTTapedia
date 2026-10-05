import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra

/-!
# Relative scoped expressions with occurrence-local accounts

The raw carrier retains arbitrary elements of the supplied observed binding
clone, every original binding operator, ordered account words and complete
typed substitution environments.  Substitution in an injected element is
an expression node, not a substitution in the base algebra using erased
environment values.

Interpretation uses an independently specified accounted binding clone and
a genuine over-source clone morphism on the injected elements.  Its source
observation is proved structurally.  Raw expressions remain available as
origin-bearing data; the source observation does not reconstruct them.
No generated quotient or free account adjunction is asserted in this module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open AccountBindingAlgebra
open FreeBindingTerms

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt) (base : Over Q)

mutual

/-- A relative scoped expression.  All marked substitution values are
retained in `substitute`, including values repeated at different variables. -/
inductive Expression : Ctx S → S.Srt → Type u where
  | gen {Γ : Ctx S} {sort : S.Srt}
      (value : base.left.substitution.Carrier Γ sort) : Expression Γ sort
  | operation {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
      (arguments : Arguments (S.arity op) Γ) : Expression Γ sort
  | account {Γ : Ctx S} {sort : S.Srt}
      (word : SourceAccountSubstitution.Account Q accountSort Γ)
      (value : Expression Γ sort) : Expression Γ sort
  | substitute {Γ Δ : Ctx S} {sort : S.Srt}
      (environment : (s : S.Srt) → Var Γ s → Expression Δ s)
      (value : Expression Γ sort) : Expression Δ sort

/-- Actual argument binder lists and ordered positions from the original
signature are retained, rather than replaced by a product outside binders. -/
inductive Arguments : List (List S.Srt × S.Srt) → Ctx S → Type u where
  | nil {Γ : Ctx S} : Arguments [] Γ
  | cons {binders : List S.Srt} {sort : S.Srt}
      {rest : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (head : Expression (binders ++ Γ) sort) (tail : Arguments rest Γ) :
      Arguments ((binders, sort) :: rest) Γ

end

/-- A source variable is retained through the supplied base clone's actual
variable injection.  Its substitution law is imposed only at the later
generated congruence stage. -/
def sourceVariable {Γ : Ctx S} {sort : S.Srt} (v : Var Γ sort) :
    Expression Q accountSort base Γ sort :=
  .gen (base.left.substitution.injectVar v)

mutual

/-- Interpret every retained node using the target's full binding clone,
action and substitution.  The environment is not projected to the base. -/
def interpret (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    {Γ : Ctx S} → {sort : S.Srt} → Expression Q accountSort base Γ sort →
      target.observed.left.substitution.Carrier Γ sort
  | _, _, .gen value => generator.left.raw.map value
  | _, _, .operation op args => target.observed.left.operation op
      (interpretArguments target generator args)
  | _, _, .account word value => target.act word (interpret target generator value)
  | _, _, .substitute env value => target.observed.left.substitution.substitute
      (fun sort v => interpret target generator (env sort v))
      (interpret target generator value)

/-- Interpret each argument in its precise binder-extended context. -/
def interpretArguments (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Arguments Q accountSort base arities Γ →
      FamilyArgs S target.observed.left.substitution.Carrier arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (interpret target generator head)
      (interpretArguments target generator tail)

end

mutual

/-- The complete source value observed from a raw expression.  Ordered
accounts and raw origins are retained in `Expression`, independently of
this deliberately account-invariant source observation. -/
def observe : {Γ : Ctx S} → {sort : S.Srt} →
    Expression Q accountSort base Γ sort → Q.substitution.Carrier Γ sort
  | _, _, .gen value => base.hom.raw.map value
  | _, _, .operation op args => Q.operation op (observeArguments args)
  | _, _, .account _ value => observe value
  | _, _, .substitute env value => Q.substitution.substitute
      (fun sort v => observe (env sort v)) (observe value)

def observeArguments : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Arguments Q accountSort base arities Γ →
      FamilyArgs S Q.substitution.Carrier arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (observe head) (observeArguments tail)

end

mutual

/-- Every actual target interpretation has precisely the raw expression's
source observation, including arbitrary marked substitution environments. -/
theorem observe_interpret (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (value : Expression Q accountSort base Γ sort),
      target.observed.hom.raw.map (interpret Q accountSort base target generator value) =
        observe Q accountSort base value
  | _, _, .gen value => by
      exact congrArg (fun h : FreeBindingClone.Hom _ _ => h.raw.map value)
        (Over.w generator)
  | _, _, .operation op args => by
      change target.observed.hom.raw.map
          (target.observed.left.operation op
            (interpretArguments Q accountSort base target generator args)) =
        Q.operation op (observeArguments Q accountSort base args)
      exact (target.observed.hom.raw.map_operation op _).trans
        (congrArg (Q.operation op)
          (observe_interpretArguments target generator args))
  | _, _, .account word value =>
      (target.observe_act word _).trans (observe_interpret target generator value)
  | _, _, .substitute env value => by
      change target.observed.hom.raw.map
          (target.observed.left.substitution.substitute
            (fun sort v => interpret Q accountSort base target generator (env sort v))
            (interpret Q accountSort base target generator value)) =
        Q.substitution.substitute
          (fun sort v => observe Q accountSort base (env sort v))
          (observe Q accountSort base value)
      rw [target.observed.hom.map_substitute]
      have environments :
          (fun sort v => target.observed.hom.raw.map
            (interpret Q accountSort base target generator (env sort v))) =
          (fun sort v => observe Q accountSort base (env sort v)) := by
        funext sort v
        exact observe_interpret target generator (env sort v)
      rw [environments, observe_interpret target generator value]

theorem observe_interpretArguments (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Arguments Q accountSort base arities Γ),
      FamilyArgs.map target.observed.hom.raw.map
          (interpretArguments Q accountSort base target generator args) =
        observeArguments Q accountSort base args
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
      congrArg₂ FamilyArgs.cons (observe_interpret target generator head)
        (observe_interpretArguments target generator tail)

end

/-- The stored environment readout at a variable is the complete supplied
expression, independent of its source observation. -/
def environmentAt {Γ Δ : Ctx S}
    (env : (sort : S.Srt) → Var Γ sort → Expression Q accountSort base Δ sort)
    {sort : S.Srt} (v : Var Γ sort) : Expression Q accountSort base Δ sort := env sort v

/-- The variable substitution equation is valid under every genuine target
arrow, even when the selected environment value contains accounts. -/
theorem interpret_substitute_variable (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (env : (s : S.Srt) → Var Γ s → Expression Q accountSort base Δ s)
    (v : Var Γ sort) :
    interpret Q accountSort base target generator
      (.substitute env (sourceVariable Q accountSort base v)) =
        interpret Q accountSort base target generator (env sort v) := by
  change target.observed.left.substitution.substitute
      (fun s w => interpret Q accountSort base target generator (env s w))
      (generator.left.raw.map (base.left.substitution.injectVar v)) = _
  exact (congrArg
    (target.observed.left.substitution.substitute
      (fun s w => interpret Q accountSort base target generator (env s w)))
    (generator.left.raw.map_variable v)).trans
      (target.observed.left.substitution.substitute_var _ v)

/-- Inject every actual base argument, retaining its own binder context. -/
def genArguments : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    FamilyArgs S base.left.substitution.Carrier arities Γ →
      Arguments Q accountSort base arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (.gen head) (genArguments tail)

theorem interpret_genArguments (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S base.left.substitution.Carrier arities Γ),
      interpretArguments Q accountSort base target generator
          (genArguments Q accountSort base args) =
        FamilyArgs.map generator.left.raw.map args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (FamilyArgs.cons (generator.left.raw.map head))
      (interpret_genArguments target generator tail)

/-- The defining generator equation for an original binding operator is
valid for all genuine target clone morphisms. -/
theorem interpret_gen_operation (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)
    {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (args : FamilyArgs S base.left.substitution.Carrier (S.arity op) Γ) :
    interpret Q accountSort base target generator (.gen (base.left.operation op args)) =
      interpret Q accountSort base target generator
        (.operation op (genArguments Q accountSort base args)) := by
  change generator.left.raw.map (base.left.operation op args) =
    target.observed.left.operation op
      (interpretArguments Q accountSort base target generator
        (genArguments Q accountSort base args))
  rw [interpret_genArguments]
  exact generator.left.raw.map_operation op args

/-- An injected base substitution may be expanded through an environment
of injected base values.  No corresponding erased-environment law is
asserted for an arbitrary marked environment. -/
theorem interpret_gen_substitute (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S base.left.substitution.Carrier Γ Δ)
    (value : base.left.substitution.Carrier Γ sort) :
    interpret Q accountSort base target generator
        (.gen (base.left.substitution.substitute env value)) =
      interpret Q accountSort base target generator
        (.substitute (fun s v => .gen (env s v)) (.gen value)) :=
  generator.left.map_substitute env value

/-- The raw account node retains the complete ordered word.  It does not
replace it by its length, a bag, or its source payload observation. -/
theorem account_word_injective {Γ : Ctx S} {sort : S.Srt}
    (value : Expression Q accountSort base Γ sort) :
    Function.Injective (fun word : SourceAccountSubstitution.Account Q accountSort Γ =>
      Expression.account word value) := by
  intro first second same
  exact (Expression.account.inj same).1

namespace Arguments

/-- Map the actual argument family, keeping binder prefixes and positions. -/
def map {F : Ctx S → S.Srt → Type u}
    (mapping : {Γ : Ctx S} → {sort : S.Srt} →
      Expression Q accountSort base Γ sort → F Γ sort) :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Arguments Q accountSort base arities Γ → FamilyArgs S F arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (mapping head) (map mapping tail)

end Arguments

theorem interpretArguments_eq_map (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Arguments Q accountSort base arities Γ),
      interpretArguments Q accountSort base target generator args =
        Arguments.map Q accountSort base (interpret Q accountSort base target generator) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg
      (FamilyArgs.cons (interpret Q accountSort base target generator head))
      (interpretArguments_eq_map target generator tail)

/-- An interpretation preserving the independently specified raw
constructors.  This is a raw homomorphism interface, not a claim that the
raw carrier already satisfies the binding-clone quotient equations. -/
structure ConstructorMap (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) where
  map : {Γ : Ctx S} → {sort : S.Srt} → Expression Q accountSort base Γ sort →
    target.observed.left.substitution.Carrier Γ sort
  map_gen : ∀ {Γ : Ctx S} {sort : S.Srt}
    (value : base.left.substitution.Carrier Γ sort),
    map (.gen value) = generator.left.raw.map value
  map_operation : ∀ {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (args : Arguments Q accountSort base (S.arity op) Γ),
    map (.operation op args) = target.observed.left.operation op
      (Arguments.map Q accountSort base map args)
  map_account : ∀ {Γ : Ctx S} {sort : S.Srt}
    (word : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Expression Q accountSort base Γ sort),
    map (.account word value) = target.act word (map value)
  map_substitute : ∀ {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Expression Q accountSort base) Γ Δ)
    (value : Expression Q accountSort base Γ sort),
    map (.substitute env value) = target.observed.left.substitution.substitute
      (fun s v => map (env s v)) (map value)

/-- The structurally constructed fold is a genuine raw homomorphism. -/
def interpretMap (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    ConstructorMap Q accountSort base target generator where
  map := interpret Q accountSort base target generator
  map_gen := fun _ => rfl
  map_operation := by
    intro Γ sort op args
    exact congrArg (target.observed.left.operation op)
      (interpretArguments_eq_map Q accountSort base target generator args)
  map_account := fun _ _ => rfl
  map_substitute := fun _ _ => rfl

mutual

/-- A raw constructor-preserving extension is uniquely determined by its
given full-clone map on the arbitrary base elements. -/
theorem constructorMap_unique (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)
    (mapping : ConstructorMap Q accountSort base target generator) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (value : Expression Q accountSort base Γ sort),
      mapping.map value = interpret Q accountSort base target generator value
  | _, _, .gen value => mapping.map_gen value
  | _, _, .operation op args =>
      (mapping.map_operation op args).trans (congrArg (target.observed.left.operation op)
        (constructorMap_arguments_unique target generator mapping args))
  | _, _, .account word value =>
      (mapping.map_account word value).trans
        (congrArg (target.act word) (constructorMap_unique target generator mapping value))
  | _, _, .substitute env value => by
      apply (mapping.map_substitute env value).trans
      apply congrArg₂ target.observed.left.substitution.substitute
      · funext sort v
        exact constructorMap_unique target generator mapping (env sort v)
      · exact constructorMap_unique target generator mapping value

theorem constructorMap_arguments_unique (target : Model Q accountSort)
    (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)
    (mapping : ConstructorMap Q accountSort base target generator) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Arguments Q accountSort base arities Γ),
      Arguments.map Q accountSort base mapping.map args =
        interpretArguments Q accountSort base target generator args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg₂ FamilyArgs.cons
      (constructorMap_unique target generator mapping head)
      (constructorMap_arguments_unique target generator mapping tail)

end

end Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension
