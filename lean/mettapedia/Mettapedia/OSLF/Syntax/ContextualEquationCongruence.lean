import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Congruence of contextual metavariable instantiation

Related metavariable bodies, ambient values and schema-variable values produce
related instantiations. The dependency prefix and ambient suffix use one joined
substitution, and every binding argument lifts the variable environment while
weakening ambient values. These laws use the existing equation closure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.ContextualAssignment

variable {S : Signature} {M K : List (MetaArity S)} {E : List (EqAxiom S K)}

/-- The joined environment respects pointwise equations on both of its
independently supplied parts. -/
theorem joinSub_eqClosure {Γ Δ : Ctx S} :
    ∀ (dependencies : Ctx S) (arguments arguments' : Sub S dependencies Δ)
      (_ : ∀ s v, EqClosure E (arguments s v) (arguments' s v))
      (ambient ambient' : Sub S Γ Δ)
      (_ : ∀ s v, EqClosure E (ambient s v) (ambient' s v))
      (s : S.Srt) (v : Var (dependencies ++ Γ) s),
      EqClosure E (joinSub arguments ambient s v) (joinSub arguments' ambient' s v)
  | [], _, _, _, _, _, relatedAmbient, s, v => relatedAmbient s v
  | b :: dependencies, _, _, relatedArguments, _, _, _, _, .zero =>
      relatedArguments b (Var.zero (Γ := dependencies))
  | _ :: dependencies, arguments, arguments', relatedArguments,
      ambient, ambient', relatedAmbient, s, .succ v =>
      joinSub_eqClosure dependencies (fun r w => arguments r (.succ w))
        (fun r w => arguments' r (.succ w))
        (fun r w => relatedArguments r (.succ w)) ambient ambient' relatedAmbient s v

/-- Weakening preserves related ambient values without adding source
variables to the environment. -/
theorem weakenSub_eqClosure {Γ Δ : Ctx S} (bs : Ctx S)
    (ambient ambient' : Sub S Γ Δ)
    (related : ∀ s v, EqClosure E (ambient s v) (ambient' s v))
    (s : S.Srt) (v : Var Γ s) :
    EqClosure E (weakenSub bs ambient s v) (weakenSub bs ambient' s v) :=
  eqClosure_rename (fun _ w => weakenVar bs w) (related s v)

/-- Applying a related contextual body to related dependency and ambient
environments respects the same equation theory. -/
theorem apply_eqClosure {Γ Δ : Ctx S}
    (body body' : ContextualAssignment S M Γ)
    (relatedBody : ∀ i, EqClosure E (body i) (body' i))
    (i : Fin M.length) (arguments arguments' : Sub S (M.get i).1 Δ)
    (relatedArguments : ∀ s v, EqClosure E (arguments s v) (arguments' s v))
    (ambient ambient' : Sub S Γ Δ)
    (relatedAmbient : ∀ s v, EqClosure E (ambient s v) (ambient' s v)) :
    EqClosure E (apply body i arguments ambient) (apply body' i arguments' ambient') :=
  .trans (eqClosure_bind (joinSub arguments ambient) (relatedBody i))
    (eqClosure_bind_pointwise (joinSub arguments ambient) (joinSub arguments' ambient')
      (joinSub_eqClosure (M.get i).1 arguments arguments' relatedArguments
        ambient ambient' relatedAmbient) (body' i))

mutual

/-- Instantiation respects equations in the template bodies and both
environments, with binder-local contexts retained. -/
theorem instantiate_eqClosure {Γ : Ctx S}
    (body body' : ContextualAssignment S M Γ)
    (relatedBody : ∀ i, EqClosure E (body i) (body' i)) :
    ∀ {Ξ Δ : Ctx S} {s : S.Srt} (ambient ambient' : Sub S Γ Δ)
      (_ : ∀ s v, EqClosure E (ambient s v) (ambient' s v))
      (valuation valuation' : Sub S Ξ Δ)
      (_ : ∀ s v, EqClosure E (valuation s v) (valuation' s v))
      (term : Term (withMetas S M) Ξ s),
      EqClosure E (instantiate body ambient valuation term)
        (instantiate body' ambient' valuation' term)
  | _, _, _, _, _, _, _, _, relatedValuation, .var v => relatedValuation _ v
  | _, _, _, ambient, ambient', relatedAmbient, valuation, valuation',
      relatedValuation, .op (.inl op) args =>
      .cong op (instantiateArgs_eqArgs body body' relatedBody
        ambient ambient' relatedAmbient valuation valuation' relatedValuation args)
  | _, _, _, ambient, ambient', relatedAmbient, valuation, valuation',
      relatedValuation, .op (.inr (.mk i)) args =>
      apply_eqClosure body body' relatedBody i
        (argsToSub (instantiateArgs body ambient valuation args))
        (argsToSub (instantiateArgs body' ambient' valuation' args))
        (eqArgs_argsToSub E (bs := (M.get i).1)
          (instantiateArgs_eqArgs body body' relatedBody ambient ambient' relatedAmbient
            valuation valuation' relatedValuation args))
        ambient ambient' relatedAmbient

/-- Every argument keeps its own binder context while the ambient
environment is weakened and the schema-variable environment is lifted. -/
theorem instantiateArgs_eqArgs {Γ : Ctx S}
    (body body' : ContextualAssignment S M Γ)
    (relatedBody : ∀ i, EqClosure E (body i) (body' i)) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Ξ Δ : Ctx S}
      (ambient ambient' : Sub S Γ Δ)
      (_ : ∀ s v, EqClosure E (ambient s v) (ambient' s v))
      (valuation valuation' : Sub S Ξ Δ)
      (_ : ∀ s v, EqClosure E (valuation s v) (valuation' s v))
      (args : Args (withMetas S M) arity Ξ),
      EqArgs E (instantiateArgs body ambient valuation args)
        (instantiateArgs body' ambient' valuation' args)
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, ambient, ambient', relatedAmbient, valuation, valuation',
      relatedValuation, .cons (bs := bs) head tail =>
      .cons (instantiate_eqClosure body body' relatedBody
        (weakenSub (S := S) bs ambient) (weakenSub (S := S) bs ambient')
        (weakenSub_eqClosure (S := S) (E := E) bs ambient ambient' relatedAmbient)
        (liftSub valuation bs) (liftSub valuation' bs)
        (eqClosure_liftSub (S := S) valuation valuation' relatedValuation bs) head)
        (instantiateArgs_eqArgs body body' relatedBody ambient ambient' relatedAmbient
          valuation valuation' relatedValuation tail)

end

end Mettapedia.OSLF.Binding.ContextualAssignment
