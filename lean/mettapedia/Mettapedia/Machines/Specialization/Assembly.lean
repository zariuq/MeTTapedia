import Mettapedia.OSLF.Syntax.FreeBindingTerms
import Mettapedia.OSLF.Syntax.ContextualFiniteSupport

/-!
# Staging a binding-algebra fold

A constructor is selected during preparation. Its residual function
takes the dynamic environment and its already prepared arguments.
The ordinary binding fold supplies the specification for any algebra
of these functions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.Assembly

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.OSLF.Binding.FreeBindingTerms

variable {S : Signature} {Environment : Type}

/-- Resolving one operator or projection produces its executable
template. All represented arguments retain their declared contexts. -/
structure Templates (S : Signature) (Environment : Type) where
  Carrier : Ctx S → S.Srt → Type
  projection : {Γ : Ctx S} → {sort : S.Srt} → Var Γ sort → Environment → Carrier Γ sort
  operator : {Γ : Ctx S} → {sort : S.Srt} → (op : S.Op sort) → Environment →
    FamilyArgs S Carrier (S.arity op) Γ → Carrier Γ sort

def Templates.at (templates : Templates S Environment) (environment : Environment) : Algebra S where
  Carrier := templates.Carrier
  injectVar := fun index => templates.projection index environment
  operation := fun op => templates.operator op environment

structure Code (Environment Result : Type) where
  run : Environment → Result
  nodes : Nat

mutual

def lower (templates : Templates S Environment) :
    {Γ : Ctx S} → {sort : S.Srt} → Term S Γ sort → Code Environment (templates.Carrier Γ sort)
  | _, _, .var index => ⟨templates.projection index, 1⟩
  | _, _, .op op arguments =>
    let execute := templates.operator op
    let operands := lowerArgs templates arguments
    ⟨fun environment => execute environment (operands.run environment), operands.nodes + 1⟩

def lowerArgs (templates : Templates S Environment) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args S arity Γ → Code Environment (FamilyArgs S templates.Carrier arity Γ)
  | _, _, .nil => ⟨fun _ => .nil, 0⟩
  | _, _, .cons head tail =>
    let first := lower templates head
    let later := lowerArgs templates tail
    ⟨fun environment => .cons (first.run environment) (later.run environment), first.nodes + later.nodes⟩

end

mutual

theorem lower_fold (templates : Templates S Environment) (environment : Environment) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
      (lower templates term).run environment = fold (templates.at environment) term
  | _, _, .var _ => rfl
  | _, _, .op _ args => by
    simp only [lower, fold, Templates.at, lowerArgs_fold templates environment args]

theorem lowerArgs_fold (templates : Templates S Environment) (environment : Environment) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S arity Γ),
      (lowerArgs templates args).run environment = foldArgs (templates.at environment) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
    simp only [lowerArgs, foldArgs, lower_fold templates environment head,
      lowerArgs_fold templates environment tail]
    rfl

end

mutual

theorem lower_size (templates : Templates S Environment) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
      (lower templates term).nodes = termSize term
  | _, _, .var _ => rfl
  | _, _, .op _ arguments => by
    simp only [lower, termSize, lowerArgs_size templates arguments]

theorem lowerArgs_size (templates : Templates S Environment) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S arity Γ),
      (lowerArgs templates args).nodes = argsSize args
  | _, _, .nil => rfl
  | _, _, .cons first later => by
    simp only [lowerArgs, argsSize, lower_size templates first, lowerArgs_size templates later]

end

variable {Name Address : Type} {source : Name → MetaArity S} {target : Address → MetaArity S}

/-- The source and target signatures have the same object binders. -/
def contextualArgs :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FamilyArgs (signature S source) (Term (signature S target)) arity Γ →
      Args (signature S target) arity Γ
  | _, _, .nil => .nil
  | _, _, .cons first later => .cons first (contextualArgs later)

/-- Binding construction with explicit contextual slots. The template
for a slot substitutes the supplied body into its declared parameters. -/
def contextual (source : Name → MetaArity S) (target : Address → MetaArity S) :
    Templates (signature S source) (Assignment source target) where
  Carrier := Term (signature S target)
  projection := fun index _ => .var index
  operator := fun {_} {_} op =>
    match op with
    | .inl original => fun _ args => .op (.inl original) (contextualArgs args)
    | .inr (.mk slot) => fun environment args =>
      bind (argsToSub (contextualArgs args)) (environment slot)

mutual

theorem lower_contextual (environment : Assignment source target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      (lower (contextual source target) term).run environment = instantiate environment term
  | _, _, .var _ => rfl
  | _, _, .op (.inl op) args => by
    change Term.op (S := signature S target) (.inl op)
      (contextualArgs ((lowerArgs (contextual source target) args).run environment)) =
      Term.op (S := signature S target) (.inl op) (instantiateArgs environment args)
    rw [lowerArgs_contextual environment args]
  | _, _, .op (.inr (.mk slot)) args => by
    change bind (argsToSub (contextualArgs ((lowerArgs (contextual source target) args).run environment)))
      (environment slot) = bind (argsToSub (instantiateArgs environment args)) (environment slot)
    rw [lowerArgs_contextual environment args]

theorem lowerArgs_contextual (environment : Assignment source target) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args (signature S source) arity Γ),
      contextualArgs ((lowerArgs (contextual source target) args).run environment) =
        instantiateArgs environment args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
    simp only [lowerArgs, contextualArgs, instantiateArgs,
      lower_contextual environment head, lowerArgs_contextual environment tail]

end

private theorem applied_generator_size {Γ : Ctx S} {arity : MetaArity S} (address : Address)
    (same : target address = arity)
    (args : Args (signature S target) (arity.1.map (fun sort => ([], sort))) Γ) :
    termSize (bind (argsToSub args) (castMetaBody same (generator target address))) = argsSize args + 1 := by
  cases same
  change argsSize (bindArgs (argsToSub args) (selfArgs (T := signature S target) (target address).1)) + 1 =
    argsSize args + 1
  rw [bindArgs_selfArgs]

mutual

/-- Encoding names as slot ordinals does not copy an argument tree. -/
theorem reindex_size (locations : Name → Address) (same : ∀ name, target (locations name) = source name) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      termSize (instantiate (reindex locations same) term) = termSize term
  | _, _, .var _ => rfl
  | _, _, .op (.inl _) args => by
    simp only [instantiate, termSize, reindexArgs_size locations same args]
  | _, _, .op (.inr (.mk name)) args => by
    change termSize (bind (argsToSub (instantiateArgs (reindex locations same) args))
      (castMetaBody (same name) (generator target (locations name)))) = argsSize args + 1
    rw [applied_generator_size (locations name) (same name), reindexArgs_size locations same args]

theorem reindexArgs_size (locations : Name → Address) (same : ∀ name, target (locations name) = source name) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args (signature S source) arity Γ),
      argsSize (instantiateArgs (reindex locations same) args) = argsSize args
  | _, _, .nil => rfl
  | _, _, .cons first later => by
    simp only [instantiateArgs, argsSize, reindex_size locations same first, reindexArgs_size locations same later]

end

open FiniteSupport

/-- One prepared family can stand for all instances of a generalized
term. The use-site substitution is composed with the input environment.
This keeps repeated and higher-arity slots correlated. -/
theorem fold_substituted {InstanceName : Type} {instanceFamily : InstanceName → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt} (common : Term (signature S source) Γ sort)
    (instanceOf : Assignment source instanceFamily) (input : Assignment instanceFamily target) :
    (lower (contextual instanceFamily target) (instantiate instanceOf common)).run input =
      (lower (contextual source target) common).run (fun slot => instantiate input (instanceOf slot)) := by
  rw [lower_contextual, lower_contextual, instantiate_comp]

theorem dense_size [DecidableEq Name] (names : List Name) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (covered : ∀ name ∈ support term, name ∈ names) :
    termSize (compile names term covered) = termSize term := by
  let code := compile names term covered
  have exactRead := instantiate_compile names (generator source) term covered
  change instantiate (restore names) code = instantiate (generator source) term at exactRead
  rw [instantiate_identity] at exactRead
  calc
    termSize code = termSize (instantiate (restore names) code) :=
      (reindex_size (fun index : Fin names.length => names[index]) (fun _ => rfl) code).symm
    _ = termSize term := congrArg termSize exactRead

mutual

theorem support_le_size :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      (support term).length ≤ termSize term
  | _, _, .var _ => by simp [support, termSize]
  | _, _, .op (.inl _) args => by
    exact (supportArgs_le_size args).trans (Nat.le_succ _)
  | _, _, .op (.inr (.mk _)) args => by
    simpa only [support, List.length_cons, termSize] using Nat.succ_le_succ (supportArgs_le_size args)

theorem supportArgs_le_size :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args (signature S source) arity Γ),
      (supportArgs args).length ≤ argsSize args
  | _, _, .nil => Nat.le_refl _
  | _, _, .cons first later => by
    simpa only [supportArgs, List.length_append, argsSize] using
      Nat.add_le_add (support_le_size first) (supportArgs_le_size later)

end

end Mettapedia.Machines.Specialization.Assembly
