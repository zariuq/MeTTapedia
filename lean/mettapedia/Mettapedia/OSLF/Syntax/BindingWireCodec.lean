import Mettapedia.OSLF.Syntax.BindingWireData
import Mettapedia.OSLF.Syntax.BindingSignature

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding

variable {S : Signature}

def putVar : {Γ : Ctx S} → {s : S.Srt} → Var Γ s → Nat
  | _, _, .zero => 0
  | _, _, .succ prior => putVar prior + 1

def getVar [DecidableEq S.Srt] : (Γ : Ctx S) → (s : S.Srt) → Nat → Option (Var Γ s)
  | [], _, _ => none
  | t :: _Γ, s, 0 => if equal : t = s then some (equal ▸ Var.zero) else none
  | _ :: Γ, s, n + 1 => (getVar Γ s n).map Var.succ

theorem get_putVar [DecidableEq S.Srt] : ∀ {Γ : Ctx S} {s : S.Srt} (v : Var Γ s),
    getVar Γ s (putVar v) = some v
  | _, _, .zero => by simp only [putVar, getVar, dite_true]
  | _, _, .succ prior => by simp only [putVar, getVar, get_putVar prior]; rfl

def varCodec [DecidableEq S.Srt] (Γ : Ctx S) (s : S.Srt) : Codec (Var Γ s) :=
  Codec.nat.mapped putVar (getVar Γ s) get_putVar

variable (operator : Codec (Σ s : S.Srt, S.Op s))

mutual
  def putTerm : {Γ : Ctx S} → {s : S.Srt} → Term S Γ s → Data
    | _, _, .var v => .pair (.atom 0) (.atom (putVar v))
    | _, s, .op o args => .pair (.atom 1) (.pair (operator.put ⟨s, o⟩) (putArgs args))

  def putArgs : {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} → Args S arity Γ → Data
    | _, _, .nil => .atom 0
    | _, _, .cons head tail => .pair (putTerm head) (putArgs tail)
end

variable [DecidableEq S.Srt]

mutual
  def getTerm (Γ : Ctx S) (s : S.Srt) : Data → Option (Term S Γ s)
    | .pair (.atom 0) (.atom index) => (getVar Γ s index).map Term.var
    | .pair (.atom 1) (.pair op args) => do
        let ⟨t, o⟩ ← operator.get op
        if equal : t = s then
          let o : S.Op s := equal ▸ o
          return .op o (← getArgs Γ (S.arity o) args)
        else none
    | _ => none

  def getArgs (Γ : Ctx S) (arity : List (List S.Srt × S.Srt)) : Data → Option (Args S arity Γ)
    | .atom 0 => match arity with | [] => some .nil | _ => none
    | .pair head tail => match arity with
        | [] => none
        | (bs, s) :: rest => do return .cons (← getTerm (bs ++ Γ) s head) (← getArgs Γ rest tail)
    | _ => none
end

mutual
  theorem get_putTerm : ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
      getTerm operator Γ s (putTerm operator term) = some term
    | _, _, .var v => by simp only [putTerm, getTerm, get_putVar]; rfl
    | _, _, .op o args => by
        simp only [putTerm, getTerm, operator.get_put]
        dsimp only [Bind.bind, Option.bind]
        simp only [dite_true]
        rw [get_putArgs]
        rfl

  theorem get_putArgs : ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S arity Γ),
      getArgs operator Γ arity (putArgs operator args) = some args
    | _, _, .nil => rfl
    | _, _, .cons head tail => by
        simp only [putArgs, getArgs, get_putTerm head, get_putArgs tail]
        rfl
end

def term (Γ : Ctx S) (s : S.Srt) : Codec (Term S Γ s) :=
  ⟨putTerm operator, getTerm operator Γ s, get_putTerm operator⟩

def args (Γ : Ctx S) (arity : List (List S.Srt × S.Srt)) : Codec (Args S arity Γ) :=
  ⟨putArgs operator, getArgs operator Γ arity, get_putArgs operator⟩

end Mettapedia.OSLF.Binding.WireCodec
