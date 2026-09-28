import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Proof-relevant compatible closure of scoped root steps

One derivation retains a root occurrence and the ordered argument positions
leading to it. Root evidence is never truncated to a proposition. The same
construction works for every many-sorted binding signature; substitution
under an argument uses exactly its declared binder list.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CompatibleDerivations

universe u v

abbrev RootFamily (S : Signature) :=
  {Γ : Ctx S} → {sort : S.Srt} → Term S Γ sort → Term S Γ sort → Type u

variable {S : Signature}

mutual
inductive Step (R : RootFamily.{u} S) :
    {Γ : Ctx S} → {sort : S.Srt} → Term S Γ sort → Term S Γ sort → Type u where
  | root {Γ sort} {source target : Term S Γ sort} : R source target → Step R source target
  | congr {Γ sort} (op : S.Op sort) {source target : Args S (S.arity op) Γ} :
      ArgsStep R source target → Step R (.op op source) (.op op target)

inductive ArgsStep (R : RootFamily.{u} S) :
    {Γ : Ctx S} → {arity : List (List S.Srt × S.Srt)} →
      Args S arity Γ → Args S arity Γ → Type u where
  | head {Γ binders sort rest} {source target : Term S (binders ++ Γ) sort}
      (tail : Args S rest Γ) :
      Step R source target → ArgsStep R (.cons source tail) (.cons target tail)
  | tail {Γ binders sort rest} (head : Term S (binders ++ Γ) sort)
      {source target : Args S rest Γ} :
      ArgsStep R source target → ArgsStep R (.cons head source) (.cons head target)
end

variable {R : RootFamily.{u} S} {Q : RootFamily.{v} S}

mutual
def map (f : ∀ {Γ sort} {source target : Term S Γ sort}, R source target → Q source target) :
    ∀ {Γ sort} {source target : Term S Γ sort}, Step R source target → Step Q source target
  | _, _, _, _, .root occurrence => .root (f occurrence)
  | _, _, _, _, .congr op arguments => .congr op (mapArgs f arguments)

def mapArgs (f : ∀ {Γ sort} {source target : Term S Γ sort}, R source target → Q source target) :
    ∀ {Γ arity} {source target : Args S arity Γ}, ArgsStep R source target → ArgsStep Q source target
  | _, _, _, _, .head tail derivation => .head tail (map f derivation)
  | _, _, _, _, .tail head derivation => .tail head (mapArgs f derivation)
end

mutual
def height : ∀ {Γ sort} {source target : Term S Γ sort}, Step R source target → Nat
  | _, _, _, _, .root _ => 1
  | _, _, _, _, .congr _ arguments => argsHeight arguments + 1

def argsHeight : ∀ {Γ arity} {source target : Args S arity Γ}, ArgsStep R source target → Nat
  | _, _, _, _, .head _ derivation => height derivation
  | _, _, _, _, .tail _ derivation => argsHeight derivation
end

/-- The precise root-level obligation required to substitute a step. -/
abbrev RootSubstitution (R : RootFamily.{u} S) :=
  ∀ {Γ Δ : Ctx S} (σ : Sub S Γ Δ) {sort : S.Srt}
    {source target : Term S Γ sort}, R source target → R (bind σ source) (bind σ target)

mutual
def substitute (rootSubstitute : RootSubstitution R) :
    ∀ {Γ Δ : Ctx S} (σ : Sub S Γ Δ) {sort : S.Srt} {source target : Term S Γ sort},
      Step R source target → Step R (bind σ source) (bind σ target)
  | _, _, σ, _, _, _, .root occurrence => .root (rootSubstitute σ occurrence)
  | _, _, σ, _, _, _, .congr op arguments =>
      .congr op (substituteArgs rootSubstitute σ arguments)

def substituteArgs (rootSubstitute : RootSubstitution R) :
    ∀ {Γ Δ : Ctx S} (σ : Sub S Γ Δ) {arity} {source target : Args S arity Γ},
      ArgsStep R source target → ArgsStep R (bindArgs σ source) (bindArgs σ target)
  | _, _, σ, _, _, _, .head (binders := binders) tail derivation =>
      .head (bindArgs σ tail) (substitute rootSubstitute (liftSub σ binders) derivation)
  | _, _, σ, _, _, _, .tail (binders := binders) head derivation =>
      .tail (bind (liftSub σ binders) head) (substituteArgs rootSubstitute σ derivation)
end

mutual
theorem height_substitute (rootSubstitute : RootSubstitution R) :
    ∀ {Γ Δ : Ctx S} (σ : Sub S Γ Δ) {sort : S.Srt} {source target : Term S Γ sort}
      (derivation : Step R source target),
      height (substitute rootSubstitute σ derivation) = height derivation
  | _, _, _, _, _, _, .root _ => rfl
  | _, _, σ, _, _, _, .congr op arguments =>
      congrArg (· + 1) (argsHeight_substitute rootSubstitute σ arguments)

theorem argsHeight_substitute (rootSubstitute : RootSubstitution R) :
    ∀ {Γ Δ : Ctx S} (σ : Sub S Γ Δ) {arity} {source target : Args S arity Γ}
      (derivation : ArgsStep R source target),
      argsHeight (substituteArgs rootSubstitute σ derivation) = argsHeight derivation
  | _, _, σ, _, _, _, .head (binders := binders) _ derivation =>
      height_substitute rootSubstitute (liftSub σ binders) derivation
  | _, _, σ, _, _, _, .tail _ derivation =>
      argsHeight_substitute rootSubstitute σ derivation
end

end Mettapedia.OSLF.Binding.CompatibleDerivations
