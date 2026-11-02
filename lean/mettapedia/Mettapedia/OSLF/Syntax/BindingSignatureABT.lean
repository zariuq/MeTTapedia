import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.GSLT.LanguageDef.ScopedABTApplication

/-!
# Intrinsic binding terms in the common physical ABT carrier

The structural head retains an operator and its result sort. Each field
retains the length of its declared binding prefix; variable positions become
the existing de Bruijn index leaves. Lowering preserves scope and constructor
conformance and is injective at a fixed context and sort.

This is a binding representation map, independent of any guest judgment or
surface parser. The untyped physical carrier still needs a sort interface
when reading arbitrary externally supplied trees.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CommonABT

open Mettapedia.GSLT.LanguageDef

variable {S : Signature}

abbrev Head (S : Signature) := (sort : S.Srt) × S.Op sort

def fieldDepths (head : Head S) : List Nat :=
  (S.arity head.2).map (fun declaration => declaration.1.length)

def index : {Γ : Ctx S} → {sort : S.Srt} → Var Γ sort → Nat
  | _, _, .zero => 0
  | _, _, .succ previous => index previous + 1

theorem index_lt : ∀ {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort), index position < Γ.length
  | _, _, .zero => Nat.zero_lt_succ _
  | _, _, .succ previous => Nat.succ_lt_succ (index_lt previous)

theorem index_injective {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (index (Γ := Γ) (sort := sort)) := by
  intro first
  induction first with
  | zero =>
      intro second same
      cases second with
      | zero => rfl
      | succ previous => simp only [index] at same; omega
  | succ first ih =>
      intro second same
      cases second with
      | zero => simp only [index] at same; omega
      | succ second => exact congrArg Var.succ (ih (Nat.succ.inj same))

mutual

def lower : {Γ : Ctx S} → {sort : S.Srt} → Term S Γ sort → SignatureIndexedABT.Term (Head S)
  | _, _, .var position => .idx (index position)
  | _, sort, .op operator arguments => .node ⟨sort, operator⟩ (lowerArgs arguments)

def lowerArgs : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args S arities Γ → SignatureIndexedABT.Fields (Head S)
  | _, _, .nil => .nil
  | _, _, .cons (bs := binders) head tail => .cons binders.length (lower head) (lowerArgs tail)

end

mutual

theorem lower_scoped : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
    SignatureIndexedABT.Term.supportedAt Γ.length (lower term) = true
  | _, _, .var position => by simp [lower, SignatureIndexedABT.Term.supportedAt, index_lt position]
  | _, _, .op _ arguments => lowerArgs_scoped arguments

theorem lowerArgs_scoped : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S arities Γ), SignatureIndexedABT.Term.Fields.supportedAt Γ.length (lowerArgs arguments) = true
  | _, _, .nil => rfl
  | _, Γ, .cons (bs := binders) head tail => by
      simp only [lowerArgs, SignatureIndexedABT.Term.Fields.supportedAt]
      have validScope := lower_scoped head
      rw [List.length_append, Nat.add_comm] at validScope
      rw [validScope, lowerArgs_scoped tail]
      rfl

end

mutual

theorem lower_conforms : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
    SignatureIndexedABT.Term.conforms fieldDepths (lower term) = true
  | _, _, .var _ => rfl
  | _, _, .op _ arguments => lowerArgs_conforms arguments

theorem lowerArgs_conforms : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S arities Γ),
    SignatureIndexedABT.Term.Fields.conforms fieldDepths (arities.map (fun declaration => declaration.1.length))
      (lowerArgs arguments) = true
  | _, _, .nil => rfl
  | _, _, .cons _ tail => by
      simp only [lowerArgs, List.map_cons, SignatureIndexedABT.Term.Fields.conforms, decide_true,
        lower_conforms, lowerArgs_conforms tail, Bool.and_self]

end

mutual

theorem lower_injective : ∀ {Γ : Ctx S} {sort : S.Srt} (first second : Term S Γ sort),
    lower first = lower second → first = second
  | _, _, .var first, .var second, same =>
      congrArg Term.var (index_injective (SignatureIndexedABT.Term.idx.inj same))
  | _, _, .var _, .op _ _, same => by cases same
  | _, _, .op _ _, .var _, same => by cases same
  | _, sort, .op operator arguments, .op other others, same => by
      have heads : (⟨sort, operator⟩ : Head S) = ⟨sort, other⟩ := (SignatureIndexedABT.Term.node.inj same).1
      have operators : operator = other := eq_of_heq (Sigma.mk.inj heads).2
      subst other
      exact congrArg (Term.op operator)
        (lowerArgs_injective arguments others (SignatureIndexedABT.Term.node.inj same).2)

theorem lowerArgs_injective : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (first second : Args S arities Γ), lowerArgs first = lowerArgs second → first = second
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons head tail, .cons other others, same => by
      have fields := SignatureIndexedABT.Fields.cons.inj same
      exact congrArg₂ Args.cons (lower_injective head other fields.2.1)
        (lowerArgs_injective tail others fields.2.2)

end

end Mettapedia.OSLF.Binding.CommonABT
