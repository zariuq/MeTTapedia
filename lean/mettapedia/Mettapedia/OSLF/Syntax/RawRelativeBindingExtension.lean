import Mettapedia.OSLF.Syntax.SecondOrderBindingModelRestriction

/-!
# Relative expressions for added binding operators

The carrier retains arbitrary elements of a supplied full binding clone,
every operator of the extended signature, and explicit simultaneous
substitutions with complete typed expression environments. Substitution in
an injected element never projects those environments back to the base.

Every fold uses an independently specified extended clone and a genuine
full clone map on the generators. The raw syntax is kept separately from
the later equational quotient. It supplies expression provenance, not a
reconstruction of literal authority from semantic generator elements.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RawRelativeBindingExtension

open FreeBindingTerms BindingSubstitutionAlgebra SecondOrderContext

universe u v

variable {S : Signature} (extension : Object S)
  (base : BindingCloneAlgebra.Algebra.{u} S)

mutual

inductive Expression : Ctx S → S.Srt → Type u where
  | gen {Γ : Ctx S} {sort : S.Srt}
      (value : base.substitution.Carrier Γ sort) : Expression Γ sort
  | operation {Γ : Ctx S} {sort : S.Srt}
      (operator : (withMetas S extension.arities).Op sort)
      (arguments : Arguments ((withMetas S extension.arities).arity operator) Γ) :
      Expression Γ sort
  | substitute {Γ Δ : Ctx S} {sort : S.Srt}
      (environment : (s : S.Srt) → Var Γ s → Expression Δ s)
      (value : Expression Γ sort) : Expression Δ sort

inductive Arguments : List (List S.Srt × S.Srt) → Ctx S → Type u where
  | nil {Γ : Ctx S} : Arguments [] Γ
  | cons {binders : List S.Srt} {sort : S.Srt}
      {rest : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (head : Expression (binders ++ Γ) sort) (tail : Arguments rest Γ) :
      Arguments ((binders, sort) :: rest) Γ

end

def injectVariable {Γ : Ctx S} {sort : S.Srt} (index : Var Γ sort) :
    Expression extension base Γ sort :=
  .gen (base.substitution.injectVar index)

mutual

def interpret (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target)) :
    {Γ : Ctx S} → {sort : S.Srt} → Expression extension base Γ sort →
      target.substitution.Carrier Γ sort
  | _, _, .gen value => generator.raw.map value
  | _, _, .operation operator arguments => target.operation operator
      (interpretArguments target generator arguments)
  | _, _, .substitute environment value => target.substitution.substitute
      (fun sort index => interpret target generator (environment sort index))
      (interpret target generator value)

def interpretArguments
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target)) :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Arguments extension base arities Γ →
      FamilyArgs (withMetas S extension.arities) target.substitution.Carrier arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (interpret target generator head)
      (interpretArguments target generator tail)

end

def genArguments : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    FamilyArgs S base.substitution.Carrier arities Γ → Arguments extension base arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (.gen head) (genArguments tail)

theorem interpret_genArguments
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target)) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : FamilyArgs S base.substitution.Carrier arities Γ),
      interpretArguments extension base target generator (genArguments extension base arguments) =
        toAmbientArgs extension (FamilyArgs.map generator.raw.map arguments)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      change FamilyArgs.cons (S := withMetas S extension.arities)
          (F := target.substitution.Carrier) (generator.raw.map head)
          (interpretArguments extension base target generator (genArguments extension base tail)) =
        FamilyArgs.cons (S := withMetas S extension.arities)
          (F := target.substitution.Carrier) (generator.raw.map head)
          (toAmbientArgs extension (FamilyArgs.map generator.raw.map tail))
      exact congrArg (FamilyArgs.cons (S := withMetas S extension.arities)
        (F := target.substitution.Carrier) (generator.raw.map head))
        (interpret_genArguments target generator tail)

theorem interpret_variable
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target))
    {Γ : Ctx S} {sort : S.Srt} (index : Var Γ sort) :
    interpret extension base target generator (injectVariable extension base index) =
      target.substitution.injectVar index := generator.raw.map_variable index

/-- This equation expands an actual base operation through the original
operator inclusion, retaining every argument's declared binder context. -/
theorem interpret_gen_operation
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target))
    {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (arguments : FamilyArgs S base.substitution.Carrier (S.arity operator) Γ) :
    interpret extension base target generator (.gen (base.operation operator arguments)) =
      interpret extension base target generator
        (.operation (.inl operator) (genArguments extension base arguments)) := by
  change generator.raw.map (base.operation operator arguments) =
    target.operation (.inl operator)
      (interpretArguments extension base target generator (genArguments extension base arguments))
  rw [interpret_genArguments]
  exact generator.raw.map_operation operator arguments

/-- Only an environment whose values are themselves injected base elements
can be expanded by the base clone's substitution operation. -/
theorem interpret_gen_substitute
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target))
    {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment S base.substitution.Carrier Γ Δ)
    (value : base.substitution.Carrier Γ sort) :
    interpret extension base target generator
        (.gen (base.substitution.substitute environment value)) =
      interpret extension base target generator
        (.substitute (fun sort index => .gen (environment sort index)) (.gen value)) :=
  generator.map_substitute environment value

/-- An arbitrary expression environment supplies its entire value at the
selected variable, including any newly added operators. -/
theorem interpret_substitute_variable
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target))
    {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment S (Expression extension base) Γ Δ)
    (index : Var Γ sort) :
    interpret extension base target generator
        (.substitute environment (injectVariable extension base index)) =
      interpret extension base target generator (environment sort index) := by
  change target.substitution.substitute
      (fun sort index => interpret extension base target generator (environment sort index))
      (generator.raw.map (base.substitution.injectVar index)) = _
  exact (congrArg (target.substitution.substitute
    (fun sort index => interpret extension base target generator (environment sort index)))
    (generator.raw.map_variable index)).trans (target.substitution.substitute_var _ index)

namespace Arguments

/-- Map each occurrence in its own binder-extended context. -/
def map {F : Ctx S → S.Srt → Type v}
    (function : ∀ {Γ : Ctx S} {sort : S.Srt}, Expression extension base Γ sort → F Γ sort) :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Arguments extension base arities Γ →
      FamilyArgs (withMetas S extension.arities) F arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (function head) (map function tail)

end Arguments

mutual

/-- The existing intrinsically scoped term syntax embeds through the
actual variables and operators; explicit substitutions remain separate. -/
def ofTerm : {Γ : Ctx S} → {sort : S.Srt} →
    Term (withMetas S extension.arities) Γ sort → Expression extension base Γ sort
  | _, _, .var index => injectVariable extension base index
  | _, _, .op operator arguments => .operation operator (ofArguments arguments)

def ofArguments : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args (withMetas S extension.arities) arities Γ → Arguments extension base arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (ofTerm head) (ofArguments tail)

end

mutual

/-- The raw embedding uses precisely the existing full binding fold. -/
theorem interpret_ofTerm
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target)) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      (value : Term (withMetas S extension.arities) Γ sort),
      interpret extension base target generator (ofTerm extension base value) =
        BindingCloneFoldSubstitution.interpret target value
  | _, _, .var index => interpret_variable extension base target generator index
  | _, _, .op operator arguments => by
      change target.operation operator
          (interpretArguments extension base target generator (ofArguments extension base arguments)) =
        target.operation operator (BindingCloneFoldSubstitution.interpretArgs target arguments)
      exact congrArg (target.operation operator) (interpret_ofArguments target generator arguments)

theorem interpret_ofArguments
    (target : BindingCloneAlgebra.Algebra.{v} (withMetas S extension.arities))
    (generator : FreeBindingClone.Hom base (restrictAlgebra extension target)) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (withMetas S extension.arities) arities Γ),
      interpretArguments extension base target generator (ofArguments extension base arguments) =
        BindingCloneFoldSubstitution.interpretArgs target arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
      congrArg₂ FamilyArgs.cons (interpret_ofTerm target generator head)
        (interpret_ofArguments target generator tail)

end

end Mettapedia.OSLF.Binding.RawRelativeBindingExtension
