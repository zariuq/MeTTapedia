import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Computed congruence of finite conversion certificates

Conversion evidence is transported through a term context by transforming
each selected step and retaining its symmetry/composition tree. Pointwise
conversion of substitution images then computes conversion of the substituted
term, including beneath binders. These are operations on existing certificates,
not conversion search or a new equality rule.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionCode
namespace Code

variable {Head : Type} {RootCode : Nat → Type}

def mapContext {n m : Nat} (wrap : Tm Head n → Tm Head m)
    (wrapStep : StepCode Head RootCode n → StepCode Head RootCode m) :
    Code Head RootCode n → Code Head RootCode m
  | .single step => .single (wrapStep step)
  | .refl term => .refl (wrap term)
  | .symm code => .symm (mapContext wrap wrapStep code)
  | .trans first second => .trans (mapContext wrap wrapStep first) (mapContext wrap wrapStep second)

theorem mapContext_id {n : Nat} (code : Code Head RootCode n) :
    mapContext id id code = code := by
  induction code <;> simp_all only [mapContext, id_eq]

theorem mapContext_comp {n m k : Nat} (first : Tm Head n → Tm Head m)
    (second : Tm Head m → Tm Head k)
    (firstStep : StepCode Head RootCode n → StepCode Head RootCode m)
    (secondStep : StepCode Head RootCode m → StepCode Head RootCode k)
    (code : Code Head RootCode n) :
    mapContext second secondStep (mapContext first firstStep code) =
      mapContext (second ∘ first) (secondStep ∘ firstStep) code := by
  induction code <;> simp_all only [mapContext, Function.comp_apply]

variable [DecidableEq Head] (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

theorem decode_mapContext {n m : Nat} (wrap : Tm Head n → Tm Head m)
    (wrapStep : StepCode Head RootCode n → StepCode Head RootCode m)
    (compatible : ∀ (step : StepCode Head RootCode n),
      StepCode.decode headEq decodeRoot (wrapStep step) =
        mapEndpoints wrap (StepCode.decode headEq decodeRoot step))
    (code : Code Head RootCode n) {left right : Tm Head n}
    (accepted : decode headEq decodeRoot code = some (left, right)) :
    decode headEq decodeRoot (mapContext wrap wrapStep code) = some (wrap left, wrap right) := by
  induction code generalizing left right with
  | single step =>
      change StepCode.decode headEq decodeRoot step = some (left, right) at accepted
      simp only [mapContext, decode, compatible, accepted, mapEndpoints, Option.map_some]
  | refl term =>
      cases accepted
      rfl
  | symm code ih =>
      cases decoded : decode headEq decodeRoot code with
      | none => simp [decode, decoded, reverseEndpoints] at accepted
      | some pair =>
          rcases pair with ⟨a, b⟩
          simp only [decode, decoded, reverseEndpoints, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          simp only [mapContext, decode, ih decoded, reverseEndpoints, Option.map_some]
  | trans first second ihFirst ihSecond =>
      cases firstDecoded : decode headEq decodeRoot first with
      | none => simp [decode, firstDecoded, joinEndpoints] at accepted
      | some pair =>
          rcases pair with ⟨a, b⟩
          cases secondDecoded : decode headEq decodeRoot second with
          | none => simp [decode, firstDecoded, secondDecoded, joinEndpoints] at accepted
          | some pair =>
              rcases pair with ⟨c, d⟩
              simp only [decode, firstDecoded, secondDecoded, joinEndpoints] at accepted
              split at accepted
              · rename_i equal
                subst c
                cases accepted
                simp [mapContext, decode, ihFirst firstDecoded, ihSecond secondDecoded, joinEndpoints]
              · cases accepted

theorem check_mapContext {n m : Nat} (wrap : Tm Head n → Tm Head m)
    (wrapStep : StepCode Head RootCode n → StepCode Head RootCode m)
    (compatible : ∀ (step : StepCode Head RootCode n),
      StepCode.decode headEq decodeRoot (wrapStep step) =
        mapEndpoints wrap (StepCode.decode headEq decodeRoot step))
    {code : Code Head RootCode n} {left right : Tm Head n}
    (accepted : check headEq decodeRoot code left right = true) :
    check headEq decodeRoot (mapContext wrap wrapStep code) (wrap left) (wrap right) = true :=
  decide_eq_true (decode_mapContext headEq decodeRoot wrap wrapStep compatible code
    (of_decide_eq_true accepted))

theorem check_refl {n : Nat} (term : Tm Head n) :
    check headEq decodeRoot (.refl term) term term = true := by simp [check, decode]

theorem check_symm {n : Nat} {code : Code Head RootCode n} {left right : Tm Head n}
    (accepted : check headEq decodeRoot code left right = true) :
    check headEq decodeRoot (.symm code) right left = true := by
  have decoded := of_decide_eq_true accepted
  simp [check, decode, decoded, reverseEndpoints]

theorem check_trans {n : Nat} {first second : Code Head RootCode n} {left middle right : Tm Head n}
    (firstAccepted : check headEq decodeRoot first left middle = true)
    (secondAccepted : check headEq decodeRoot second middle right = true) :
    check headEq decodeRoot (.trans first second) left right = true := by
  have firstDecoded := of_decide_eq_true firstAccepted
  have secondDecoded := of_decide_eq_true secondAccepted
  simp [check, decode, firstDecoded, secondDecoded, joinEndpoints]

def congPi {n : Nat} (leftTarget : Tm Head n) (rightSource : Tm Head (n + 1))
    (left : Code Head RootCode n) (right : Code Head RootCode (n + 1)) : Code Head RootCode n :=
  .trans (mapContext (fun term => .pi term rightSource) (fun step => .congPiDom step rightSource) left)
    (mapContext (.pi leftTarget) (.congPiCod leftTarget) right)

theorem check_congPi {n : Nat} {a a' : Tm Head n} {b b' : Tm Head (n + 1)}
    {first : Code Head RootCode n} {second : Code Head RootCode (n + 1)}
    (ha : check headEq decodeRoot first a a' = true)
    (hb : check headEq decodeRoot second b b' = true) :
    check headEq decodeRoot (congPi a' b first second) (.pi a b) (.pi a' b') = true :=
  check_trans headEq decodeRoot
    (check_mapContext headEq decodeRoot (fun term => .pi term b) (fun step => .congPiDom step b)
      (fun _ => rfl) ha)
    (check_mapContext headEq decodeRoot (.pi a') (.congPiCod a') (fun _ => rfl) hb)

def congSigma {n : Nat} (leftTarget : Tm Head n) (rightSource : Tm Head (n + 1))
    (left : Code Head RootCode n) (right : Code Head RootCode (n + 1)) : Code Head RootCode n :=
  .trans (mapContext (fun term => .sigma term rightSource) (fun step => .congSigmaDom step rightSource) left)
    (mapContext (.sigma leftTarget) (.congSigmaCod leftTarget) right)

theorem check_congSigma {n : Nat} {a a' : Tm Head n} {b b' : Tm Head (n + 1)}
    {first : Code Head RootCode n} {second : Code Head RootCode (n + 1)}
    (ha : check headEq decodeRoot first a a' = true)
    (hb : check headEq decodeRoot second b b' = true) :
    check headEq decodeRoot (congSigma a' b first second) (.sigma a b) (.sigma a' b') = true :=
  check_trans headEq decodeRoot
    (check_mapContext headEq decodeRoot (fun term => .sigma term b) (fun step => .congSigmaDom step b)
      (fun _ => rfl) ha)
    (check_mapContext headEq decodeRoot (.sigma a') (.congSigmaCod a') (fun _ => rfl) hb)

def congApp {n : Nat} (leftTarget : Tm Head n) (rightSource : Tm Head n)
    (left : Code Head RootCode n) (right : Code Head RootCode n) : Code Head RootCode n :=
  .trans (mapContext (fun term => .app term rightSource) (fun step => .congAppFun step rightSource) left)
    (mapContext (.app leftTarget) (.congAppArg leftTarget) right)

theorem check_congApp {n : Nat} {a a' : Tm Head n} {b b' : Tm Head n}
    {first : Code Head RootCode n} {second : Code Head RootCode n}
    (ha : check headEq decodeRoot first a a' = true)
    (hb : check headEq decodeRoot second b b' = true) :
    check headEq decodeRoot (congApp a' b first second) (.app a b) (.app a' b') = true :=
  check_trans headEq decodeRoot
    (check_mapContext headEq decodeRoot (fun term => .app term b) (fun step => .congAppFun step b)
      (fun _ => rfl) ha)
    (check_mapContext headEq decodeRoot (.app a') (.congAppArg a') (fun _ => rfl) hb)

def congPair {n : Nat} (leftTarget : Tm Head n) (rightSource : Tm Head n)
    (left : Code Head RootCode n) (right : Code Head RootCode n) : Code Head RootCode n :=
  .trans (mapContext (fun term => .pair term rightSource) (fun step => .congPairFst step rightSource) left)
    (mapContext (.pair leftTarget) (.congPairSnd leftTarget) right)

theorem check_congPair {n : Nat} {a a' : Tm Head n} {b b' : Tm Head n}
    {first : Code Head RootCode n} {second : Code Head RootCode n}
    (ha : check headEq decodeRoot first a a' = true)
    (hb : check headEq decodeRoot second b b' = true) :
    check headEq decodeRoot (congPair a' b first second) (.pair a b) (.pair a' b') = true :=
  check_trans headEq decodeRoot
    (check_mapContext headEq decodeRoot (fun term => .pair term b) (fun step => .congPairFst step b)
      (fun _ => rfl) ha)
    (check_mapContext headEq decodeRoot (.pair a') (.congPairSnd a') (fun _ => rfl) hb)

def congLam {n : Nat} (code : Code Head RootCode (n + 1)) : Code Head RootCode n :=
  mapContext .lam .congLam code

theorem check_congLam {n : Nat} {a b : Tm Head (n + 1)} {code : Code Head RootCode (n + 1)}
    (accepted : check headEq decodeRoot code a b = true) :
    check headEq decodeRoot (congLam code) (.lam a) (.lam b) = true :=
  check_mapContext headEq decodeRoot .lam .congLam (fun _ => rfl) accepted

def congFst {n : Nat} (code : Code Head RootCode n) : Code Head RootCode n :=
  mapContext .fst .congFst code

theorem check_congFst {n : Nat} {a b : Tm Head n} {code : Code Head RootCode n}
    (accepted : check headEq decodeRoot code a b = true) :
    check headEq decodeRoot (congFst code) (.fst a) (.fst b) = true :=
  check_mapContext headEq decodeRoot .fst .congFst (fun _ => rfl) accepted

def congSnd {n : Nat} (code : Code Head RootCode n) : Code Head RootCode n :=
  mapContext .snd .congSnd code

theorem check_congSnd {n : Nat} {a b : Tm Head n} {code : Code Head RootCode n}
    (accepted : check headEq decodeRoot code a b = true) :
    check headEq decodeRoot (congSnd code) (.snd a) (.snd b) = true :=
  check_mapContext headEq decodeRoot .snd .congSnd (fun _ => rfl) accepted

def congRefl {n : Nat} (code : Code Head RootCode n) : Code Head RootCode n :=
  mapContext .refl .congRefl code

theorem check_congRefl {n : Nat} {a b : Tm Head n} {code : Code Head RootCode n}
    (accepted : check headEq decodeRoot code a b = true) :
    check headEq decodeRoot (congRefl code) (.refl a) (.refl b) = true :=
  check_mapContext headEq decodeRoot .refl .congRefl (fun _ => rfl) accepted

def congId {n : Nat} (typeTarget leftSource leftTarget rightSource : Tm Head n)
    (type left right : Code Head RootCode n) : Code Head RootCode n :=
  .trans (mapContext (fun A => .id A leftSource rightSource)
      (fun step => .congIdTy step leftSource rightSource) type)
    (.trans (mapContext (fun a => .id typeTarget a rightSource)
        (fun step => .congIdLeft typeTarget step rightSource) left)
      (mapContext (.id typeTarget leftTarget) (.congIdRight typeTarget leftTarget) right))

theorem check_congId {n : Nat} {A A' a a' b b' : Tm Head n}
    {type first second : Code Head RootCode n}
    (hA : check headEq decodeRoot type A A' = true)
    (ha : check headEq decodeRoot first a a' = true)
    (hb : check headEq decodeRoot second b b' = true) :
    check headEq decodeRoot (congId A' a a' b type first second) (.id A a b) (.id A' a' b') = true :=
  check_trans headEq decodeRoot
    (check_mapContext headEq decodeRoot (fun T => .id T a b) (fun step => .congIdTy step a b)
      (fun _ => rfl) hA)
    (check_trans headEq decodeRoot
      (check_mapContext headEq decodeRoot (fun x => .id A' x b) (fun step => .congIdLeft A' step b)
        (fun _ => rfl) ha)
      (check_mapContext headEq decodeRoot (.id A' a') (.congIdRight A' a') (fun _ => rfl) hb))

variable (renameCode : {n m : Nat} → Ren n m → Code Head RootCode n → Code Head RootCode m)

def liftImageConversions {n m : Nat} (images : Fin n → Code Head RootCode m) :
    Fin (n + 1) → Code Head RootCode (m + 1) :=
  Fin.cases (.refl (.var 0)) (fun index => renameCode wk (images index))

/-- Compute a conversion tree for a term instantiated by pointwise
convertible substitutions. The two substitutions need not be equal. -/
def substitutePointwise : {n m : Nat} → (σ τ : Sub Head n m) →
    (Fin n → Code Head RootCode m) → Tm Head n → Code Head RootCode m
  | _, _, _, _, images, .var index => images index
  | _, _, _, _, _, .head h => .refl (.head h)
  | _, _, _, _, _, .const name => .refl (.const name)
  | _, _, σ, τ, images, .pi A B =>
      congPi (subst τ A) (subst (liftSub σ) B)
        (substitutePointwise σ τ images A)
        (substitutePointwise (liftSub σ) (liftSub τ) (liftImageConversions renameCode images) B)
  | _, _, σ, τ, images, .sigma A B =>
      congSigma (subst τ A) (subst (liftSub σ) B)
        (substitutePointwise σ τ images A)
        (substitutePointwise (liftSub σ) (liftSub τ) (liftImageConversions renameCode images) B)
  | _, _, σ, τ, images, .lam body =>
      congLam (substitutePointwise (liftSub σ) (liftSub τ) (liftImageConversions renameCode images) body)
  | _, _, σ, τ, images, .app f a =>
      congApp (subst τ f) (subst σ a) (substitutePointwise σ τ images f) (substitutePointwise σ τ images a)
  | _, _, σ, τ, images, .pair a b =>
      congPair (subst τ a) (subst σ b) (substitutePointwise σ τ images a) (substitutePointwise σ τ images b)
  | _, _, σ, τ, images, .fst p => congFst (substitutePointwise σ τ images p)
  | _, _, σ, τ, images, .snd p => congSnd (substitutePointwise σ τ images p)
  | _, _, σ, τ, images, .id A a b =>
      congId (subst τ A) (subst σ a) (subst τ a) (subst σ b)
        (substitutePointwise σ τ images A) (substitutePointwise σ τ images a)
        (substitutePointwise σ τ images b)
  | _, _, σ, τ, images, .refl a => congRefl (substitutePointwise σ τ images a)

variable (renamePreserves : ∀ {n m} (ρ : Ren n m) (code : Code Head RootCode n)
  {left right : Tm Head n}, check headEq decodeRoot code left right = true →
    check headEq decodeRoot (renameCode ρ code) (rename ρ left) (rename ρ right) = true)

include renamePreserves in
theorem liftImageConversions_checked {n m : Nat} {σ τ : Sub Head n m}
    {images : Fin n → Code Head RootCode m}
    (accepted : ∀ index, check headEq decodeRoot (images index) (σ index) (τ index) = true)
    (index : Fin (n + 1)) :
    check headEq decodeRoot (liftImageConversions renameCode images index)
      (liftSub σ index) (liftSub τ index) = true := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact check_refl headEq decodeRoot _
  · exact renamePreserves wk (images index) (accepted index)

include renamePreserves in
theorem substitutePointwise_checked {n m : Nat} (term : Tm Head n) (σ τ : Sub Head n m)
    (images : Fin n → Code Head RootCode m)
    (accepted : ∀ index, check headEq decodeRoot (images index) (σ index) (τ index) = true) :
    check headEq decodeRoot (substitutePointwise renameCode σ τ images term)
      (subst σ term) (subst τ term) = true := by
  induction term generalizing m with
  | var index => exact accepted index
  | head h => exact check_refl headEq decodeRoot _
  | const name => exact check_refl headEq decodeRoot _
  | pi A B ihA ihB =>
      exact check_congPi headEq decodeRoot (ihA σ τ images accepted)
        (ihB _ _ _ (liftImageConversions_checked headEq decodeRoot renameCode renamePreserves accepted))
  | sigma A B ihA ihB =>
      exact check_congSigma headEq decodeRoot (ihA σ τ images accepted)
        (ihB _ _ _ (liftImageConversions_checked headEq decodeRoot renameCode renamePreserves accepted))
  | lam body ih =>
      exact check_congLam headEq decodeRoot
        (ih _ _ _ (liftImageConversions_checked headEq decodeRoot renameCode renamePreserves accepted))
  | app f a ihF ihA => exact check_congApp headEq decodeRoot (ihF σ τ images accepted) (ihA σ τ images accepted)
  | pair a b ihA ihB => exact check_congPair headEq decodeRoot (ihA σ τ images accepted) (ihB σ τ images accepted)
  | fst p ih => exact check_congFst headEq decodeRoot (ih σ τ images accepted)
  | snd p ih => exact check_congSnd headEq decodeRoot (ih σ τ images accepted)
  | id A a b ihA iha ihb =>
      exact check_congId headEq decodeRoot (ihA σ τ images accepted)
        (iha σ τ images accepted) (ihb σ τ images accepted)
  | refl a ih => exact check_congRefl headEq decodeRoot (ih σ τ images accepted)

def inst0Argument {n : Nat} (left right : Tm Head n) (code : Code Head RootCode n)
    (body : Tm Head (n + 1)) : Code Head RootCode n :=
  substitutePointwise renameCode (Fin.cases left ids) (Fin.cases right ids)
    (Fin.cases code (fun index => .refl (.var index))) body

include renamePreserves in
theorem inst0Argument_checked {n : Nat} {left right : Tm Head n} {code : Code Head RootCode n}
    (accepted : check headEq decodeRoot code left right = true) (body : Tm Head (n + 1)) :
    check headEq decodeRoot (inst0Argument renameCode left right code body)
      (inst0 left body) (inst0 right body) = true := by
  apply substitutePointwise_checked headEq decodeRoot renameCode renamePreserves
  intro index
  refine Fin.cases accepted (fun index => check_refl headEq decodeRoot _) index

#print axioms check_mapContext
#print axioms substitutePointwise_checked
#print axioms inst0Argument_checked

end Code
end StructuralConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
