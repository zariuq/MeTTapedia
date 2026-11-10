import Mettapedia.OSLF.Syntax.ContextualFamily
import Mettapedia.OSLF.Syntax.BindingSignatureABTSubstitution

/-! # Contextual schema application through physical ABT grafting

The blueprint is the existing intrinsically scoped contextual term. Its
interpreter emits ordinary physical binding trees, retaining the result sort
in each constructor head. Metavariable occurrences apply their separately
supplied bodies with the existing scoped graft, including recursively
instantiated arguments. This is not substitution of object-variable indices
for schematic identities.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily.CommonABT

open Mettapedia.GSLT.LanguageDef

variable {S : Signature} {V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}

abbrev TargetHead (target : W → MetaArity S) := Binding.CommonABT.Head (signature S target)
abbrev Physical (target : W → MetaArity S) := SignatureIndexedABT.Term (TargetHead target)

theorem index_signature {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort) :
    Binding.CommonABT.index (S := signature S source) position =
      Binding.CommonABT.index (S := signature S target) position := by
  induction position with
  | zero => rfl
  | succ previous earlier => simpa only [Binding.CommonABT.index] using congrArg Nat.succ earlier

def flatSpine {H : Type} : SignatureIndexedABT.Fields H → Option (List (SignatureIndexedABT.Term H))
  | .nil => some []
  | .cons depth term rest => if depth = 0 then do return term :: (← flatSpine rest) else none

theorem flatSpine_lowerArgs {T : Signature} : ∀ {parameters : Ctx T} {Γ : Ctx T}
    (arguments : Args T (parameters.map (fun sort => ([], sort))) Γ),
    flatSpine (Binding.CommonABT.lowerArgs arguments) = some (Binding.CommonABT.lowerSpine arguments)
  | [], _, .nil => rfl
  | _ :: _, _, .cons head tail => by
      simp only [Binding.CommonABT.lowerArgs, List.length_nil, flatSpine, ↓reduceIte,
        flatSpine_lowerArgs tail]
      rfl

mutual
  def instantiate (assignment : Assignment source target) :
      {Γ : Ctx S} → {sort : S.Srt} → Term (signature S source) Γ sort → Option (Physical target)
    | _, _, .var position => some (.idx (Binding.CommonABT.index position))
    | _, sort, .op (.inl original) arguments => do
        return .node ⟨sort, .inl original⟩ (← instantiateArgs assignment arguments)
    | _, _, .op (.inr (.mk identity)) arguments => do
        let fields ← instantiateArgs assignment arguments
        let spine ← flatSpine fields
        SignatureIndexedABT.ScopedApplication.graft (source identity).1.length
          spine (Binding.CommonABT.lower (assignment identity))

  def instantiateArgs (assignment : Assignment source target) :
      {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args (signature S source) arities Γ → Option (SignatureIndexedABT.Fields (TargetHead target))
    | _, _, .nil => some .nil
    | _, _, .cons (bs := binders) head tail => do
        return .cons binders.length (← instantiate assignment head) (← instantiateArgs assignment tail)

end

mutual
  theorem instantiate_exact (assignment : Assignment source target)
      {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
      instantiate assignment term = some (Binding.CommonABT.lower (ContextualFamily.instantiate assignment term)) := by
    match term with
    | .var position =>
        exact congrArg (fun index => some (SignatureIndexedABT.Term.idx (Head := TargetHead target) index))
          (index_signature (source := source) (target := target) position)
    | .op (.inl original) arguments =>
        simp only [instantiate, instantiateArgs_exact assignment arguments]
        rfl
    | .op (.inr (.mk identity)) arguments =>
        rw [instantiate, instantiateArgs_exact assignment arguments]
        change (flatSpine (Binding.CommonABT.lowerArgs (ContextualFamily.instantiateArgs assignment arguments))).bind
          (fun spine => SignatureIndexedABT.ScopedApplication.graft (source identity).1.length
            spine (Binding.CommonABT.lower (assignment identity))) = _
        rw [flatSpine_lowerArgs]
        exact Binding.CommonABT.graft_lower (assignment identity)
          (ContextualFamily.instantiateArgs assignment arguments)
    termination_by structural term

  theorem instantiateArgs_exact (assignment : Assignment source target)
      {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (signature S source) arities Γ) :
      instantiateArgs assignment arguments =
        some (Binding.CommonABT.lowerArgs (ContextualFamily.instantiateArgs assignment arguments)) := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        simp only [instantiateArgs, instantiate_exact assignment head, instantiateArgs_exact assignment tail]
        rfl
    termination_by structural arguments

end

theorem result_scoped (assignment : Assignment source target)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    ∃ result, instantiate assignment term = some result ∧
      SignatureIndexedABT.Term.supportedAt Γ.length result = true :=
  ⟨_, instantiate_exact assignment term,
    Binding.CommonABT.lower_scoped (S := signature S target) (ContextualFamily.instantiate assignment term)⟩

#print axioms instantiate_exact
#print axioms result_scoped

end Mettapedia.OSLF.Binding.ContextualFamily.CommonABT
