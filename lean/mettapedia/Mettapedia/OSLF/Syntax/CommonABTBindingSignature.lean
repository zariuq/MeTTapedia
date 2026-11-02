import Mettapedia.OSLF.Syntax.BindingSignatureABT
import Mettapedia.GSLT.LanguageDef.ABTHeadMapping

/-!
# Scoped common ABTs as intrinsic terms of a binding signature

The existing common physical carrier permits arbitrary structural heads and
records each field's binder depth. Its intrinsic presentation puts precisely
that head and field-depth vector in an operator declaration. The term syntax
is the existing `Binding.Term/Args`; no additional term calculus is introduced.

Scope-checked physical trees read structurally into that presentation.
Lowering back forgets only the redundant operator arity annotation and
recovers the original tree, including every binding index and field depth.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CommonABT.Presentation

open Mettapedia.GSLT.LanguageDef

variable {H : Type}

abbrev signature (H : Type) : Signature where
  Srt := Unit
  Op _ := H × List Nat
  arity operator := operator.2.map (fun depth => (List.replicate depth (), ()))

abbrev context (depth : Nat) : List Unit := List.replicate depth ()

def depths : SignatureIndexedABT.Fields H → List Nat
  | .nil => []
  | .cons depth _ rest => depth :: depths rest

theorem context_add (depth binders : Nat) :
    context (depth + binders) = List.replicate binders () ++ context depth :=
  (congrArg (fun count => List.replicate count ()) (Nat.add_comm depth binders)).trans
    (List.replicate_add binders depth ())

def varOfFin : {depth : Nat} → Fin depth → Var (context depth) ()
  | 0, index => Fin.elim0 index
  | _ + 1, ⟨0, _⟩ => .zero
  | _ + 1, ⟨index + 1, bound⟩ => .succ (varOfFin ⟨index, Nat.lt_of_succ_lt_succ bound⟩)

theorem variable_index : ∀ {depth : Nat} (index : Fin depth),
    CommonABT.index (S := signature H) (varOfFin index) = index.val
  | 0, index => Fin.elim0 index
  | _ + 1, ⟨0, _⟩ => rfl
  | depth + 1, ⟨index + 1, bound⟩ =>
      congrArg Nat.succ (variable_index (depth := depth)
        ⟨index, Nat.lt_of_succ_lt_succ bound⟩)

mutual
def read (tree : SignatureIndexedABT.Term H) (depth : Nat)
    (supported : SignatureIndexedABT.Term.supportedAt depth tree = true) :
    Term (signature H) (context depth) () :=
  match tree with
  | .idx index => .var (varOfFin ⟨index, of_decide_eq_true supported⟩)
  | .node head fields => .op (head, depths fields) (readFields fields depth supported)

def readFields (fields : SignatureIndexedABT.Fields H) (depth : Nat)
    (supported : SignatureIndexedABT.Term.Fields.supportedAt depth fields = true) :
    Args (signature H) ((depths fields).map (fun binders => (List.replicate binders (), ()))) (context depth) :=
  match fields with
  | .nil => .nil
  | .cons binders child rest =>
      .cons (castTermCtx (context_add depth binders)
        (read child (depth + binders) (Bool.and_eq_true_iff.mp supported).1))
        (readFields rest depth (Bool.and_eq_true_iff.mp supported).2)
end

def forgetHead (head : CommonABT.Head (signature H)) : H := head.2.1

def erase {Γ : Ctx (signature H)} (tree : Term (signature H) Γ ()) : SignatureIndexedABT.Term H :=
  SignatureIndexedABT.mapHeads forgetHead (CommonABT.lower tree)

def eraseFields {Γ : Ctx (signature H)} {arity : List (List Unit × Unit)}
    (fields : Args (signature H) arity Γ) : SignatureIndexedABT.Fields H :=
  SignatureIndexedABT.mapFieldHeads forgetHead (CommonABT.lowerArgs fields)

theorem erase_cast {first second : Ctx (signature H)} (same : first = second)
    (tree : Term (signature H) first ()) : erase (castTermCtx same tree) = erase tree := by
  cases same
  rfl

mutual
theorem erase_read (tree : SignatureIndexedABT.Term H) (depth : Nat)
    (supported : SignatureIndexedABT.Term.supportedAt depth tree = true) :
    erase (read tree depth supported) = tree := by
  cases tree with
  | idx index => exact congrArg SignatureIndexedABT.Term.idx (variable_index _)
  | node head fields =>
      exact congrArg (SignatureIndexedABT.Term.node head) (erase_readFields fields depth supported)

theorem erase_readFields (fields : SignatureIndexedABT.Fields H) (depth : Nat)
    (supported : SignatureIndexedABT.Term.Fields.supportedAt depth fields = true) :
    eraseFields (readFields fields depth supported) = fields := by
  cases fields with
  | nil => rfl
  | cons binders child rest =>
      change SignatureIndexedABT.Fields.cons (List.replicate binders ()).length
        (erase (castTermCtx (context_add depth binders)
          (read child (depth + binders) (Bool.and_eq_true_iff.mp supported).1)))
        (eraseFields (readFields rest depth (Bool.and_eq_true_iff.mp supported).2)) = _
      rw [List.length_replicate, erase_cast, erase_read, erase_readFields]
end

theorem read_injective (depth : Nat) (first second : SignatureIndexedABT.Term H)
    (firstScope : SignatureIndexedABT.Term.supportedAt depth first = true)
    (secondScope : SignatureIndexedABT.Term.supportedAt depth second = true)
    (same : read first depth firstScope = read second depth secondScope) : first = second := by
  have lowered := congrArg erase same
  rw [erase_read, erase_read] at lowered
  exact lowered

end Mettapedia.OSLF.Binding.CommonABT.Presentation
