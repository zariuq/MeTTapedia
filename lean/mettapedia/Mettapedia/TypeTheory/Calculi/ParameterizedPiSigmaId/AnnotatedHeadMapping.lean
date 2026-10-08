import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.NativeSubstitution

/-!
# Head substitution through annotated sources and raw indices

Head substitution acts on written domains and bodies at their original
scopes. It commutes with erasure, variable renaming and beta substitution.
The independent raw-index operation agrees with the scoped source operation
and preserves scope recovery. This layer concerns syntax; interpreting a
head substitution as a theory map needs preservation of the head rules and
declaration signature separately.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace ATm

variable {H K J : Type} {n m : Nat}

def mapHead (f : H → K) : {n : Nat} → ATm H n → ATm K n
  | _, .var index => .var index
  | _, .const name => .const name
  | _, .head value => .head (f value)
  | _, .pi domain body => .pi (mapHead f domain) (mapHead f body)
  | _, .sigma domain body => .sigma (mapHead f domain) (mapHead f body)
  | _, .id carrier left right => .id (mapHead f carrier) (mapHead f left) (mapHead f right)
  | _, .lamBare body => .lamBare (mapHead f body)
  | _, .lamTyped domain body => .lamTyped (mapHead f domain) (mapHead f body)
  | _, .app function argument => .app (mapHead f function) (mapHead f argument)
  | _, .pair first second => .pair (mapHead f first) (mapHead f second)
  | _, .fst value => .fst (mapHead f value)
  | _, .snd value => .snd (mapHead f value)
  | _, .refl subject => .refl (mapHead f subject)

@[simp] theorem mapHead_id (source : ATm H n) : source.mapHead _root_.id = source := by
  induction source <;> simp_all [mapHead]

@[simp] theorem mapHead_comp (first : H → K) (second : K → J) (source : ATm H n) :
    (source.mapHead first).mapHead second = source.mapHead (second ∘ first) := by
  induction source <;> simp_all [mapHead]

@[simp] theorem erase_mapHead (f : H → K) (source : ATm H n) :
    (source.mapHead f).erase = source.erase.mapHead f := by
  induction source <;> simp_all [mapHead, erase, Tm.mapHead]

@[simp] theorem mapHead_rename (f : H → K) (rho : Ren n m) (source : ATm H n) :
    (rename rho source).mapHead f = rename rho (source.mapHead f) := by
  induction source generalizing m <;> simp_all [mapHead, rename]

theorem mapHead_liftSub (f : H → K) (sigma : ASub H n m) :
    (fun index => (liftSub sigma index).mapHead f) =
      liftSub (fun index => (sigma index).mapHead f) := by
  funext index
  refine Fin.cases ?_ (fun i => ?_) index
  · rfl
  · simp [liftSub, mapHead_rename]

@[simp] theorem mapHead_subst (f : H → K) (sigma : ASub H n m) (source : ATm H n) :
    (subst sigma source).mapHead f =
      subst (fun index => (sigma index).mapHead f) (source.mapHead f) := by
  induction source generalizing m <;> simp_all [mapHead, subst, mapHead_liftSub]

@[simp] theorem mapHead_inst0 (f : H → K) (argument : ATm H n) (body : ATm H (n+1)) :
    (inst0 argument body).mapHead f = inst0 (argument.mapHead f) (body.mapHead f) := by
  rw [inst0, inst0, mapHead_subst]
  congr 1
  funext index
  refine Fin.cases ?_ (fun i => ?_) index <;> rfl

end ATm

namespace NativeSyntax

variable {H K : Type}

def Raw.mapHead (f : H → K) : Raw H → Raw K
  | .var index => .var index
  | .const name => .const name
  | .head value => .head (f value)
  | .pi domain body => .pi (domain.mapHead f) (body.mapHead f)
  | .sigma domain body => .sigma (domain.mapHead f) (body.mapHead f)
  | .id carrier left right => .id (carrier.mapHead f) (left.mapHead f) (right.mapHead f)
  | .lamBare body => .lamBare (body.mapHead f)
  | .lamTyped domain body => .lamTyped (domain.mapHead f) (body.mapHead f)
  | .app function argument => .app (function.mapHead f) (argument.mapHead f)
  | .pair first second => .pair (first.mapHead f) (second.mapHead f)
  | .fst value => .fst (value.mapHead f)
  | .snd value => .snd (value.mapHead f)
  | .refl subject => .refl (subject.mapHead f)

@[simp] theorem mapHead_encode {n : Nat} (f : H → K) (source : ATm H n) :
    (encode source).mapHead f = encode (source.mapHead f) := by
  induction source <;> simp_all [Raw.mapHead, encode, ATm.mapHead]

@[simp] theorem checkScope_mapHead (f : H → K) (n : Nat) (source : Raw H) :
    checkScope n (source.mapHead f) = checkScope n source := by
  induction source generalizing n <;> simp_all [Raw.mapHead, checkScope]

@[simp] theorem decode_mapHead (f : H → K) (n : Nat) (source : Raw H) :
    decode n (source.mapHead f) = (decode n source).map (ATm.mapHead f) := by
  induction source generalizing n <;>
    simp_all [Raw.mapHead, decode, ATm.mapHead, Option.bind_map, Function.comp_def]

theorem mapHead_beta {n : Nat} (f : H → K) (argument : ATm H n) (body : ATm H (n+1)) :
    decode n ((substituteZero (encode argument) 0 (encode body)).mapHead f) =
      some (ATm.inst0 (argument.mapHead f) (body.mapHead f)) := by
  rw [decode_mapHead, substituteZero_decodes, Option.map_some, ATm.mapHead_inst0]

end NativeSyntax

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
