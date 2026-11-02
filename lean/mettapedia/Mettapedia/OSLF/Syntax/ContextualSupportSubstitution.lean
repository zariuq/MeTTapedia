import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# Contextual support bounds through object and hole substitution

Object substitution may introduce the holes of its argument images, while
contextual substitution introduces only holes of the images it actually
uses. Binder lifting preserves these bounds. The statements are inclusions:
general application may erase an argument, so raw support need not survive.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}

def Bounded (allowed : V → Prop) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) : Prop :=
  ∀ identity ∈ support term, allowed identity

def BoundedArgs (allowed : V → Prop) {arities : List (MetaArity S)} {Γ : Ctx S}
    (arguments : Args (signature S source) arities Γ) : Prop :=
  ∀ identity ∈ supportArgs arguments, allowed identity

theorem bounded_liftSub (allowed : V → Prop) {Γ Δ : Ctx S}
    (environment : Sub (signature S source) Γ Δ)
    (bounded : ∀ sort position, Bounded allowed (environment sort position)) :
    ∀ (binders : Ctx S) sort position, Bounded allowed (liftSub environment binders sort position)
  | [], sort, position => bounded sort position
  | _ :: _, _, .zero => by intro identity member; cases member
  | _ :: binders, sort, .succ position => by
      simpa only [liftSub, weaken, Bounded, support_rename] using
        bounded_liftSub allowed environment bounded binders sort position

mutual
theorem bounded_bind (allowed : V → Prop) :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (environment : Sub (signature S source) Γ Δ)
      (term : Term (signature S source) Γ sort),
      Bounded allowed term → (∀ result position, Bounded allowed (environment result position)) →
      Bounded allowed (bind environment term)
  | _, _, _, environment, .var position, _, values => values _ position
  | _, _, _, environment, .op (.inl _) arguments, names, values =>
      boundedArgs_bindArgs allowed environment arguments names values
  | _, _, _, environment, .op (.inr (.mk selected)) arguments, names, values => by
      intro identity member
      cases List.mem_cons.mp member with
      | inl same => exact names identity (List.mem_cons.mpr (.inl same))
      | inr inside =>
          exact boundedArgs_bindArgs allowed environment arguments
            (fun name present => names name (List.mem_cons_of_mem selected present)) values identity inside

theorem boundedArgs_bindArgs (allowed : V → Prop) :
    ∀ {arities : List (MetaArity S)} {Γ Δ : Ctx S}
      (environment : Sub (signature S source) Γ Δ)
      (arguments : Args (signature S source) arities Γ),
      BoundedArgs allowed arguments → (∀ result position, Bounded allowed (environment result position)) →
      BoundedArgs allowed (bindArgs environment arguments)
  | _, _, _, _, .nil, _, _ => by intro identity member; cases member
  | _, _, _, environment, .cons (bs := binders) head tail, names, values => by
      intro identity member
      cases List.mem_append.mp member with
      | inl first =>
          exact bounded_bind allowed (liftSub environment binders) head
            (fun name present => names name (List.mem_append_left _ present))
            (bounded_liftSub allowed environment values binders) identity first
      | inr rest =>
          exact boundedArgs_bindArgs allowed environment tail
            (fun name present => names name (List.mem_append_right _ present)) values identity rest
end

theorem support_argsToSub : ∀ (parameters : Ctx S) {Γ : Ctx S}
    (arguments : Args (signature S source) (parameters.map fun sort => ([], sort)) Γ)
    (sort : S.Srt) (position : Var parameters sort) (identity : V),
    identity ∈ support (argsToSub arguments sort position) → identity ∈ supportArgs arguments
  | _ :: _, _, .cons _ _, _, .zero, _, member => List.mem_append_left _ member
  | _ :: parameters, _, .cons _ tail, sort, .succ position, identity, member =>
      List.mem_append_right _ (support_argsToSub parameters tail sort position identity member)

mutual
theorem bounded_instantiate (allowed : W → Prop) (assignment : Assignment source target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      (∀ identity ∈ support term, Bounded allowed (assignment identity)) →
      Bounded allowed (instantiate assignment term)
  | _, _, .var _, _ => by intro identity member; cases member
  | _, _, .op (.inl _) arguments, images => boundedArgs_instantiateArgs allowed assignment arguments images
  | _, _, .op (.inr (.mk selected)) arguments, images => by
      apply bounded_bind allowed (argsToSub (instantiateArgs assignment arguments)) (assignment selected)
        (images selected List.mem_cons_self)
      intro sort position identity member
      exact boundedArgs_instantiateArgs allowed assignment arguments
        (fun name present => images name (List.mem_cons_of_mem selected present)) identity
        (support_argsToSub (source selected).1 (instantiateArgs assignment arguments) sort position identity member)

theorem boundedArgs_instantiateArgs (allowed : W → Prop) (assignment : Assignment source target) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
      (arguments : Args (signature S source) arities Γ),
      (∀ identity ∈ supportArgs arguments, Bounded allowed (assignment identity)) →
      BoundedArgs allowed (instantiateArgs assignment arguments)
  | _, _, .nil, _ => by intro identity member; cases member
  | _, _, .cons head tail, images => by
      intro identity member
      cases List.mem_append.mp member with
      | inl first =>
          exact bounded_instantiate allowed assignment head
            (fun name present => images name (List.mem_append_left _ present)) identity first
      | inr rest =>
          exact boundedArgs_instantiateArgs allowed assignment tail
            (fun name present => images name (List.mem_append_right _ present)) identity rest
end

end Mettapedia.OSLF.Binding.ContextualFamily
