import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.OSLF.Syntax.CategoricalBindingStageCore
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Valuation models of declaration-derived binding signatures

The existing intrinsic signature supplies every constructor and binder list.
Base-sort meanings and declared constructor meanings are ordinary algebra data.
Arrow sorts retain functions, structural substitution evaluates the complete
body function, and each multiple binder reads its finite prefix of a sequence.
The existing categorical binding construction then supplies the full clone,
including substitution of arbitrary semantic values beneath all binders.

Equation satisfaction is a separate property of the supplied constructor
meanings. This construction does not assert operational adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open _root_.CategoryTheory

universe u

/-- Type expressions are interpreted without discarding arrow values. A
multiple-binder value supplies a sequence; each declared count reads its
finite prefix. Collection representation keeps its ordered input list. -/
def Value (base : String → Type u) : TypeExpr → Type u
  | .base name => base name
  | .arrow domain codomain => Value base domain → Value base codomain
  | .multiBinder domain => Nat → Value base domain
  | .collection _ element => List (Value base element)

abbrev Context (language : LanguageDef) (base : String → Type u) (Γ : List TypeExpr) : Type u :=
  contextOf (S := signatureOf language) (Value base) Γ

abbrev Power (language : LanguageDef) (base : String → Type u) (Γ : List TypeExpr) (sort : TypeExpr) : Type u :=
  Context language base Γ → Value base sort

abbrev Family (language : LanguageDef) (base : String → Type u) (arity : List (List TypeExpr × TypeExpr)) : Type u :=
  familyOf (S := signatureOf language) (Power language base) arity

/-- The actual authored grammar rows supply constructor interpretations;
their arguments retain exactly the parameter scopes from the declaration. -/
structure Constructors (language : LanguageDef) (base : String → Type u) where
  ordinary : ∀ (rule : GrammarRule) (_member : rule ∈ language.terms)
    (_notCollection : ¬ WellSorted.UsesBareCollection rule)
    {arity : List (List TypeExpr × TypeExpr)}
    (_scopes : ParameterScopes rule.params arity),
    Family language base arity → base rule.category
  collection : ∀ (rule : GrammarRule) (_member : rule ∈ language.terms)
    (parameterName : String) (kind : CollType) (element : TypeExpr)
    (_shape : rule.params = [.simple parameterName (.collection kind element)]),
    List (Value base element) → base rule.category

/-- A declared finite multiple binder reads the supplied sequence in order. -/
def sequencePrefix (language : LanguageDef) (base : String → Type u) (domain : TypeExpr) :
    (count : Nat) → (Nat → Value base domain) → Context language base (List.replicate count domain)
  | 0, _ => PUnit.unit
  | count + 1, values => (values 0, sequencePrefix language base domain count (fun n => values (n + 1)))

/-- Nonbinding arguments are evaluated at the unique empty assignment. -/
def listArguments (language : LanguageDef) (base : String → Type u) (element : TypeExpr) :
    (count : Nat) → Family language base (List.replicate count ([], element)) → List (Value base element)
  | 0, _ => []
  | count + 1, args => args.1 PUnit.unit :: listArguments language base element count args.2

/-- Interpret all actual signature operators, including its structural
lambda, simultaneous-binder and explicit-substitution representations. -/
def operator {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) :
    {sort : TypeExpr} → (op : Operator language sort) →
      Family language base ((signatureOf language).arity op) → Value base sort
  | _, .constructor rule member ordinary scopes, args =>
      constructors.ordinary rule member ordinary scopes args
  | _, .collectionConstructor rule member parameter kind element shape count, args =>
      constructors.collection rule member parameter kind element shape
        (listArguments language base element count args)
  | _, .lambda _ _, args => fun value => args.1 (value, PUnit.unit)
  | _, .multiLambda domain _ count, args => fun values =>
      args.1 (sequencePrefix language base domain count values)
  | _, .subst _ _, args => args.1 (args.2.1 PUnit.unit, PUnit.unit)
  | _, .collection _ element count, args => listArguments language base element count args

/-- The categorical model uses actual functions as its chosen binder powers.
Its universal curry laws are proved independently of constructor semantics. -/
abbrev model {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) : Model (signatureOf language) (Type u) where
  sort := Value base
  power := Power language base
  eval := fun _ _ => TypeCat.ofHom (fun input => input.2 input.1)
  curry := fun f => TypeCat.ofHom (fun stage assignment => f (assignment, stage))
  curry_eval := by
    intros
    rfl
  curry_unique := by
    intro Γ sort Z f g same
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext stage assignment
    exact (congrArg (fun h => h (assignment, stage)) same).symm
  op := fun op => TypeCat.ofHom (operator constructors op)

/-- Arbitrary natural semantic values, not merely interpretations of syntax,
form the existing full binding clone at the one-point stage. -/
def algebra {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) :
    BindingCloneAlgebra.Algebra.{u + 1} (signatureOf language) :=
  (model constructors).stage PUnit.{u + 1}

/-- Read a full natural semantic value at an ordinary ordered valuation. -/
def read {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ : List TypeExpr} {sort : TypeExpr}
    (value : (algebra constructors).substitution.Carrier Γ sort)
    (assignment : (type : TypeExpr) → Var Γ type → Value base type) : Value base sort :=
  value.value PUnit (𝟙 _) (fun type v => TypeCat.ofHom (fun _ => assignment type v)) PUnit.unit

/-- The complete mixed-sort valuation is substituted, including function
values and any annotations inside them. -/
theorem read_substitute {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (env : BindingSubstitutionAlgebra.Environment (signatureOf language)
      (algebra constructors).substitution.Carrier Γ Δ)
    (value : (algebra constructors).substitution.Carrier Γ sort)
    (assignment : (type : TypeExpr) → Var Δ type → Value base type) :
    read constructors ((algebra constructors).substitution.substitute env value) assignment =
      read constructors value (fun type v => read constructors (env type v) assignment) := by
  unfold read
  change value.value PUnit (𝟙 _) _ PUnit.unit = value.value PUnit (𝟙 _) _ PUnit.unit
  congr 2

theorem read_variable {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ : List TypeExpr} {sort : TypeExpr}
    (v : Var Γ sort) (assignment : (type : TypeExpr) → Var Γ type → Value base type) :
    read constructors ((algebra constructors).substitution.injectVar v) assignment =
      assignment sort v := rfl

/-- Interpret the existing intrinsic term, with no decoder restriction. -/
def interpret {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) Γ sort) :
    (algebra constructors).substitution.Carrier Γ sort :=
  BindingCloneFoldSubstitution.interpret (algebra constructors) term

/-- The actual simultaneous source substitution is preserved by the full
constructor fold, including every declaration-derived binder list. -/
theorem interpret_bind {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (env : Sub (signatureOf language) Γ Δ) (term : Term (signatureOf language) Γ sort) :
    interpret constructors (bind env term) =
      (algebra constructors).substitution.substitute
        (fun type v => interpret constructors (env type v)) (interpret constructors term) :=
  BindingCloneFoldSubstitution.interpret_bind (algebra constructors) env term

theorem read_bind {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (env : Sub (signatureOf language) Γ Δ) (term : Term (signatureOf language) Γ sort)
    (assignment : (type : TypeExpr) → Var Δ type → Value base type) :
    read constructors (interpret constructors (bind env term)) assignment =
      read constructors (interpret constructors term)
        (fun type v => read constructors (interpret constructors (env type v)) assignment) := by
  rw [interpret_bind, read_substitute]

/-- A full function of ordered valuations determines a natural semantic
value. This is not restricted to the image of source terms. -/
def ofFunction {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ : List TypeExpr} {sort : TypeExpr}
    (function : Context language base Γ → Value base sort) :
    (algebra constructors).substitution.Carrier Γ sort where
  value := fun _ _ assignment =>
    (model constructors).tupleEnv assignment ≫ TypeCat.ofHom function
  natural := by
    intro Z Z' h m assignment
    rw [(model constructors).tupleEnv_restage]
    exact _root_.CategoryTheory.Category.assoc _ _ _

/-- The whole function is read at an actual ordered context value. -/
def readContext {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ : List TypeExpr} {sort : TypeExpr}
    (value : (algebra constructors).substitution.Carrier Γ sort)
    (assignment : Context language base Γ) : Value base sort :=
  value.value (Context language base Γ) (TypeCat.ofHom fun _ => PUnit.unit)
    ((model constructors).projections Γ) assignment

theorem readContext_ofFunction {language : LanguageDef} {base : String → Type u}
    (constructors : Constructors language base) {Γ : List TypeExpr} {sort : TypeExpr}
    (function : Context language base Γ → Value base sort)
    (assignment : Context language base Γ) :
    readContext constructors (ofFunction constructors function) assignment = function assignment := by
  change ((model constructors).tupleEnv ((model constructors).projections Γ) ≫
    TypeCat.ofHom function) assignment = function assignment
  rw [(model constructors).tupleEnv_projections]
  rfl

end Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation
