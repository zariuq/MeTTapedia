import Mettapedia.Languages.Agda.Adequacy.Embedding

/-!
# Retraction of the source-spine embedding

The partial decoder recognizes the source fragment's structural shapes. Bare
neutral heads represent empty spines; explicit elimination requires a nonempty
spine. Closed finite Set annotations and Abs/NoAbs are retained. This is a
syntactic retraction and injectivity result, not reduction reflection or source
elaboration adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Adequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

private def decodeNeutralSpine {n : Nat} (head : Specification.Spine n → Specification.Term n) :
    Option (Specification.Spine n) → Option (Specification.Term n)
  | some (.cons e es) => some (head (.cons e es))
  | _ => none

private def decodeNeutralHead {n : Nat} (term : Structural.Tm (scope n)) :
    Option (Specification.Spine n → Specification.Term n) :=
  match term with
  | .var index => some (.var (readVar index))
  | .op op _ => match op with
    | .defined name => some (.defn name)
    | .constructor name => some (.con name)
    | _ => none

private def decodeClosedLevel {Γ : Ctx sig} (level : Structural.Level Γ) : Option Nat :=
  match level with
  | .var _ => none
  | .op op _ => match op with
    | .levelClosed value => some value
    | _ => none

private def decodeFiniteSet {Γ : Ctx sig} : Structural.UnivSort Γ → Option Nat
  | .var _ => none
  | .op .set (.cons level .nil) => decodeClosedLevel level
  | .op .prop _ | .op (.setOmega _) _ => none

mutual
  /-- Read only the source fragment's canonical term shapes. -/
  def decodeTerm : {n : Nat} → Structural.Tm (scope n) → Option (Specification.Term n)
    | _, .var index => some (.var (readVar index) .nil)
    | _, .op (.defined name) .nil => some (.defn name .nil)
    | _, .op (.constructor name) .nil => some (.con name .nil)
    | n, .op .lam (.cons body .nil) =>
        (decodeTerm (n := n + 1) body).map (fun term => .lam (.bind term))
    | _, .op .lamNoAbs (.cons body .nil) =>
        (decodeTerm body).map (fun term => .lam (.noBind term))
    | n, .op .pi (.cons domain (.cons body .nil)) => do
        let domain ← decodeTy domain
        let body ← decodeTy (n := n + 1) body
        pure (.pi domain (.bind body))
    | _, .op .piNoAbs (.cons domain (.cons body .nil)) => do
        let domain ← decodeTy domain
        let body ← decodeTy body
        pure (.pi domain (.noBind body))
    | _, .op .sortTerm (.cons sort .nil) => (decodeFiniteSet sort).map .sort
    | _, .op .levelTerm (.cons level .nil) => (decodeClosedLevel level).map .level
    | _, .op .eliminate (.cons head (.cons spine .nil)) => do
        let head ← decodeNeutralHead head
        decodeNeutralSpine head (decodeSpine spine)
    | _, .op (.natLiteral _) _ => none
  termination_by _ term => termSize term
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  /-- Source types retain a closed finite Set annotation. -/
  def decodeTy : {n : Nat} → Structural.Ty (scope n) → Option (Specification.Ty n)
    | _, .var _ => none
    | _, .op .el (.cons sort (.cons term .nil)) => do
        let level ← decodeFiniteSet sort
        (decodeTerm term).map (.el level)
  termination_by _ ty => termSize ty
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  /-- Source spines contain applications only, in their authored order. -/
  def decodeSpine : {n : Nat} → Structural.Spine (scope n) → Option (Specification.Spine n)
    | _, .op .nil .nil => some .nil
    | _, .var _ => none
    | _, .op .cons (.cons head (.cons rest .nil)) =>
        match head with
        | .var _ => none
        | .op (.proj _) _ => none
        | .op .apply (.cons term .nil) => do
            let term ← decodeTerm term
            let rest ← decodeSpine rest
            pure (.cons (.apply term) rest)
    | _, .op .append _ => none
  termination_by _ spine => termSize spine
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)
end

mutual
  @[simp] theorem decodeTerm_embedTerm {n : Nat} (term : Specification.Term n) :
      decodeTerm (embedTerm term) = some term := by
    match term with
    | .var index .nil =>
        rw [embedTerm, decodeTerm.eq_def]
        change some (Specification.Term.var (readVar (embedVar index)) .nil) = _
        rw [read_embedVar]
    | .var index (.cons e es) =>
        rw [embedTerm, decodeTerm.eq_def]
        change decodeNeutralSpine (.var (readVar (embedVar index)))
          (decodeSpine (embedSpine (.cons e es))) = _
        rw [read_embedVar, decodeSpine_embedSpine]
        rfl
    | .defn name .nil | .con name .nil =>
        rw [embedTerm, decodeTerm.eq_def]
        rfl
    | .defn name (.cons e es) =>
        rw [embedTerm, decodeTerm.eq_def]
        change decodeNeutralSpine (.defn name) (decodeSpine (embedSpine (.cons e es))) = _
        rw [decodeSpine_embedSpine]
        rfl
    | .con name (.cons e es) =>
        rw [embedTerm, decodeTerm.eq_def]
        change decodeNeutralSpine (.con name) (decodeSpine (embedSpine (.cons e es))) = _
        rw [decodeSpine_embedSpine]
        rfl
    | .lam (.bind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTerm (embedTerm body)).map (fun term => Specification.Term.lam (.bind term)) = _
        rw [decodeTerm_embedTerm]
        rfl
    | .lam (.noBind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTerm (embedTerm body)).map (fun term => Specification.Term.lam (.noBind term)) = _
        rw [decodeTerm_embedTerm]
        rfl
    | .pi domain (.bind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTy (embedTy domain)).bind (fun domain =>
          (decodeTy (embedTy body)).bind (fun body => some (Specification.Term.pi domain (.bind body)))) = _
        rw [decodeTy_embedTy, decodeTy_embedTy]
        rfl
    | .pi domain (.noBind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTy (embedTy domain)).bind (fun domain =>
          (decodeTy (embedTy body)).bind (fun body => some (Specification.Term.pi domain (.noBind body)))) = _
        rw [decodeTy_embedTy, decodeTy_embedTy]
        rfl
    | .sort _ | .level _ =>
        rw [embedTerm, decodeTerm.eq_def]
        rfl

  @[simp] theorem decodeTy_embedTy {n : Nat} (ty : Specification.Ty n) :
      decodeTy (embedTy ty) = some ty := by
    match ty with
    | .el level term =>
        rw [embedTy, decodeTy.eq_def]
        change (decodeTerm (embedTerm term)).map (Specification.Ty.el level) = _
        rw [decodeTerm_embedTerm]
        rfl

  @[simp] theorem decodeSpine_embedSpine {n : Nat} (spine : Specification.Spine n) :
      decodeSpine (embedSpine spine) = some spine := by
    match spine with
    | .nil =>
        rw [embedSpine, decodeSpine.eq_def]
        rfl
    | .cons (.apply term) rest =>
        rw [embedSpine, decodeSpine.eq_def]
        change (decodeTerm (embedTerm term)).bind (fun term =>
          (decodeSpine (embedSpine rest)).bind (fun rest => some (Specification.Spine.cons (.apply term) rest))) = _
        rw [decodeTerm_embedTerm, decodeSpine_embedSpine]
        rfl
end

theorem embedTerm_injective {n : Nat} : Function.Injective (embedTerm (n := n)) := by
  intro first second same
  have decoded := congrArg decodeTerm same
  simpa only [decodeTerm_embedTerm, Option.some.injEq] using decoded

theorem embedTy_injective {n : Nat} : Function.Injective (embedTy (n := n)) := by
  intro first second same
  have decoded := congrArg decodeTy same
  simpa only [decodeTy_embedTy, Option.some.injEq] using decoded

theorem embedSpine_injective {n : Nat} : Function.Injective (embedSpine (n := n)) := by
  intro first second same
  have decoded := congrArg decodeSpine same
  simpa only [decodeSpine_embedSpine, Option.some.injEq] using decoded

theorem decode_rejects_empty_elimination {n : Nat} (index : Fin n) :
    decodeTerm (Structural.eliminate (.var (embedVar index)) Structural.nil) = none := by
  rw [decodeTerm.eq_def]
  change decodeNeutralSpine (.var (readVar (embedVar index))) (decodeSpine Structural.nil) = none
  rw [decodeSpine.eq_def]
  rfl

theorem decode_rejects_projection {n : Nat} (name : String) (rest : Structural.Spine (scope n)) :
    decodeSpine (Structural.cons (Structural.proj name) rest) = none := by
  rw [decodeSpine.eq_def]
  rfl

theorem decode_rejects_prop_annotation {n : Nat} (level : Structural.Level (scope n))
    (term : Structural.Tm (scope n)) :
    decodeTy (Structural.el (Structural.prop level) term) = none := by
  rw [decodeTy.eq_def]
  rfl

theorem decode_rejects_beta_redex {n : Nat} (body : Structural.Tm (.term :: scope n))
    (argument : Structural.Tm (scope n)) :
    decodeTerm (Structural.eliminate (Structural.lam body)
      (Structural.cons (Structural.apply argument) Structural.nil)) = none := by
  rw [decodeTerm.eq_def]
  rfl

#print axioms decodeTerm_embedTerm
#print axioms decodeTy_embedTy
#print axioms decodeSpine_embedSpine
#print axioms embedTerm_injective
#print axioms embedTy_injective
#print axioms embedSpine_injective

end Mettapedia.Languages.Agda.Adequacy
