import Mettapedia.Logic.HOL.Syntax.ConstMap

/-!
# Partial substitution of closed terms for constants

A partial replacement table acts on the existing intrinsically typed HOL syntax.
Failure means that a constant actually encountered in the term has no replacement;
unrelated missing entries have no effect. Closed replacements are weakened under
binders, so the operation introduces no variable capture.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u}
variable {Const : Ty Base → Type v} {Const' : Ty Base → Type w}

/-- Substitute closed terms for constants, failing at an unavailable replacement. -/
def substConst? (f : ∀ {τ : Ty Base}, Const τ → Option (ClosedTerm Const' τ)) :
    {Γ : Ctx Base} → Term Const Γ τ → Option (Term Const' Γ τ)
  | _, .var v => some (.var v)
  | Γ, .const c => (f c).map (weakenCtx Γ)
  | _, .app g t => do return .app (← substConst? f g) (← substConst? f t)
  | _, .lam t => (substConst? f t).map Term.lam
  | _, .top => some .top
  | _, .bot => some .bot
  | _, .and φ ψ => do return .and (← substConst? f φ) (← substConst? f ψ)
  | _, .or φ ψ => do return .or (← substConst? f φ) (← substConst? f ψ)
  | _, .imp φ ψ => do return .imp (← substConst? f φ) (← substConst? f ψ)
  | _, .not φ => (substConst? f φ).map Term.not
  | _, .eq t s => do return .eq (← substConst? f t) (← substConst? f s)
  | _, .all φ => (substConst? f φ).map Term.all
  | _, .ex φ => (substConst? f φ).map Term.ex

/-- Total replacement tables recover ordinary constant substitution exactly. -/
@[simp] theorem substConst?_some
    (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    (t : Term Const Γ τ) :
    substConst? (fun c => some (f c)) t = some (substConst f t) := by
  induction t <;> simp_all [substConst?, substConst]

/-- Renaming variables commutes with partial constant substitution. -/
theorem substConst?_rename
    (f : ∀ {τ : Ty Base}, Const τ → Option (ClosedTerm Const' τ))
    {Γ Δ : Ctx Base} (ρ : Rename Base Γ Δ) (t : Term Const Γ τ) :
    substConst? f (rename ρ t) = (substConst? f t).map (rename ρ) := by
  induction t generalizing Δ with
  | const c =>
      cases h : f c <;> simp [substConst?, rename, h, rename_weakenCtx]
  | _ => simp_all [substConst?, rename, Option.map_bind, Option.bind_map,
      Function.comp_def]

/-- Weakening is the special case of the renaming law used under a binder. -/
@[simp] theorem substConst?_weaken
    (f : ∀ {τ : Ty Base}, Const τ → Option (ClosedTerm Const' τ))
    (t : Term Const Γ τ) :
    substConst? f (weaken (σ := σ) t) =
      (substConst? f t).map (weaken (σ := σ)) :=
  substConst?_rename f Rename.weaken t

/-- On a successful traversal, any total completion of the available replacements
gives the same result. No availability assumption is made about unused constants. -/
theorem substConst?_success_eq
    (f : ∀ {τ : Ty Base}, Const τ → Option (ClosedTerm Const' τ))
    (g : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    (agrees : ∀ {τ} (c : Const τ) (replacement : ClosedTerm Const' τ),
      f c = some replacement → replacement = g c)
    (t : Term Const Γ τ) (result : Term Const' Γ τ)
    (success : substConst? f t = some result) : result = substConst g t := by
  induction t with
  | var v => simpa [substConst?, substConst] using success.symm
  | const c =>
      cases h : f c with
      | none => simp [substConst?, h] at success
      | some replacement =>
          have replacement_eq := agrees c replacement h
          simpa [substConst?, substConst, h, replacement_eq] using success.symm
  | app x y hx hy | and x y hx hy | or x y hx hy | imp x y hx hy | eq x y hx hy =>
      cases hx' : substConst? f x <;> cases hy' : substConst? f y <;>
        simp_all [substConst?, substConst]
  | lam x hx | not x hx | all x hx | ex x hx =>
      cases hx' : substConst? f x <;> simp_all [substConst?, substConst]
  | top => simpa [substConst?, substConst] using success.symm
  | bot => simpa [substConst?, substConst] using success.symm

/-- Extending a partial replacement table preserves every successful traversal. -/
theorem substConst?_mono
    (f g : ∀ {τ : Ty Base}, Const τ → Option (ClosedTerm Const' τ))
    (extension : ∀ {τ} (c : Const τ) (replacement : ClosedTerm Const' τ),
      f c = some replacement → g c = some replacement)
    (t : Term Const Γ τ) (result : Term Const' Γ τ)
    (success : substConst? f t = some result) : substConst? g t = some result := by
  induction t with
  | const c =>
      cases h : f c with
      | none => simp [substConst?, h] at success
      | some replacement =>
          simpa [substConst?, h, extension c replacement h] using success
  | app x y hx hy | and x y hx hy | or x y hx hy | imp x y hx hy | eq x y hx hy =>
      cases hx' : substConst? f x <;> cases hy' : substConst? f y <;>
        simp_all [substConst?]
  | lam x hx | not x hx | all x hx | ex x hx =>
      cases hx' : substConst? f x <;> simp_all [substConst?]
  | var v => exact success
  | top => exact success
  | bot => exact success

namespace PartialConstSubstitutionExamples

/-- Two proposition constants, one defined and one intentionally unavailable. -/
inductive Constant : Ty Empty → Type where
  | defined : Constant propTy
  | unavailable : Constant propTy

def replacement : ∀ {τ}, Constant τ → Option (ClosedTerm Constant τ)
  | _, .defined => some (.imp .top .top)
  | _, .unavailable => none

/-- An unrelated unavailable constant does not block replacement under a binder. -/
theorem available_under_binder :
    substConst? replacement
        (.lam (.const .defined) : ClosedTerm Constant (propTy ⇒ propTy)) =
      some (.lam (.imp .top .top)) := rfl

/-- An unavailable constant occurring in an argument makes the traversal fail. -/
theorem unavailable_argument :
    substConst? replacement
        (.app (.lam (.var .vz)) (.const .unavailable) : ClosedTerm Constant propTy) =
      none := rfl

end PartialConstSubstitutionExamples

#print axioms substConst?_some
#print axioms substConst?_rename
#print axioms substConst?_success_eq
#print axioms substConst?_mono

end Mettapedia.Logic.HOL
