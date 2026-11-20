import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRowCompilation

/-!
# Stable path keys of contextual terms

A path may traverse an argument beneath object binders. Each traversed
operator must be rigid. A metavariable application yields no key, since its
instantiation may erase arguments or change the head. Key choices may be
coarser than operator identity. Matching still uses the contextual equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidIndexKeys

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Key V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}
  (operatorKey : ∀ {sort}, S.Op sort → Key)

mutual

def keyAt : ∀ {Γ : Ctx S} {sort : S.Srt},
    Term (signature S source) Γ sort → List Nat → Option Key
  | _, _, .var _, _ => none
  | _, _, .op (.inr _) _, _ => none
  | _, _, .op (.inl op) _, [] => some (operatorKey op)
  | _, _, .op (.inl _) args, field :: path => keyAtField args field path

def keyAtField : ∀ {arity : List (MetaArity S)} {Γ : Ctx S},
    Args (signature S source) arity Γ → Nat → List Nat → Option Key
  | _, _, .nil, _, _ => none
  | _, _, .cons body _, 0, path => keyAt body path
  | _, _, .cons _ rest, field + 1, path => keyAtField rest field path

end

mutual

theorem keyAt_instantiates (assignment : Assignment source target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
      (path : List Nat) (key : Key), keyAt operatorKey term path = some key →
        keyAt operatorKey (instantiate assignment term) path = some key
  | _, _, .var _, _, _, found => nomatch found
  | _, _, .op (.inr _) _, _, _, found => nomatch found
  | _, _, .op (.inl _) _, [], _, found => found
  | _, _, .op (.inl _) args, field :: path, key, found =>
      keyAtField_instantiates assignment args field path key found

theorem keyAtField_instantiates (assignment : Assignment source target) :
    ∀ {arity : List (MetaArity S)} {Γ : Ctx S}
      (args : Args (signature S source) arity Γ) (field : Nat)
      (path : List Nat) (key : Key), keyAtField operatorKey args field path = some key →
        keyAtField operatorKey (instantiateArgs assignment args) field path = some key
  | _, _, .nil, _, _, _, found => nomatch found
  | _, _, .cons body _, 0, path, key, found => keyAt_instantiates assignment body path key found
  | _, _, .cons _ rest, field + 1, path, key, found =>
      keyAtField_instantiates assignment rest field path key found

end

variable {Local Shared : Type} (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

/-- A query's rigid key can only reject a compiled row with a different
rigid key. The proof uses the actual contextual match relation, including
the common assignment for the row's latent equations. -/
theorem compiled_match_survives [DecidableEq Local] [DecidableEq Shared]
    {Γ : Ctx S} {sort : S.Srt} (candidate : Assignment captures target)
    (pattern : Term (signature S target) Γ sort) (row : ContextualConditionalRows.Row locals captures Γ sort)
    (path : List Nat) (key : Key) (probe : keyAt operatorKey pattern path = some key)
    (matched : ContextualConditionalRows.Matches locals captures candidate pattern row) :
    let stored := keyAt operatorKey (ContextualStoredRowCompilation.compile locals captures row).value path
    stored = none ∨ stored = some key := by
  dsimp only
  cases found : keyAt operatorKey (ContextualStoredRowCompilation.compile locals captures row).value path with
  | none => exact Or.inl rfl
  | some rowKey =>
    obtain ⟨extension, privateImages, _, same⟩ := matched
    let assignment := ContextualGuardMatching.instanceAssignment locals privateImages extension.assignment candidate
    have decoded := (ContextualStoredRowCompilation.compile_instantiates locals captures row assignment).1
    have storedKey := keyAt_instantiates operatorKey
      (FiniteSupport.slots (ContextualStoredRowCompilation.compile locals captures row).names assignment)
      _ path rowKey found
    rw [decoded, same] at storedKey
    have patternKey := keyAt_instantiates operatorKey extension.assignment pattern path key probe
    exact Or.inr (storedKey.symm.trans patternKey)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidIndexKeys
