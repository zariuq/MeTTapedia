import Mettapedia.OSLF.Syntax.SecondOrderContextCategory
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Equational congruence for second-order instantiation

Metavariable assignments are context morphisms. Pointwise equation-equivalent
assignments must act alike on every term, including a metavariable applied to
arguments whose own terms lie beneath binders. This is the right-composition
congruence needed when context morphisms are quotiented by authored equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open Mettapedia.OSLF.Binding

variable {S : Signature} {N K : List (MetaArity S)}
variable (E : List (EqAxiom (withMetas S N) K))

mutual
/-- Second-order instantiation fixes every original operation, variable and
binder in the base signature. -/
theorem instInto_embed {M : List (MetaArity S)}
    (assignment : (i : Fin M.length) →
      Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s),
      instInto assignment (embed (M := M) term) = embed (M := N) term
  | _, _, .var _ => rfl
  | _, _, .op op args => by
      simp only [embed, instInto]
      congr 1
      exact instIntoArgs_embed assignment args

/-- The same fixed-base law for all arguments of a binding operation. -/
theorem instIntoArgs_embed {M : List (MetaArity S)}
    (assignment : (i : Fin M.length) →
      Term (withMetas S N) (M.get i).1 (M.get i).2) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args S arities Γ),
      instIntoArgs assignment (embedArgs (M := M) args) =
        embedArgs (M := N) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [embedArgs, instIntoArgs]
      congr 1
      · exact instInto_embed assignment head
      · exact instIntoArgs_embed assignment tail
end

/-- Reading one of two related argument lists gives related terms. The
argument positions are the dependency context of a metavariable occurrence. -/
theorem eqArgs_argsToSub :
    ∀ {bs : List S.Srt} {Γ : Ctx S}
      {args args' : Args (withMetas S N) (bs.map (fun b => ([], b))) Γ},
      EqArgs E args args' →
      ∀ (s : S.Srt) (v : Var bs s),
        EqClosure E (argsToSub args s v) (argsToSub args' s v)
  | [], _, _, _, _, _, v => nomatch v
  | _ :: _, _, .cons _ _, .cons _ _, .cons related _rest, _, .zero => related
  | _ :: _, _, .cons _ _, .cons _ _, .cons _related rest, _, .succ v =>
      eqArgs_argsToSub rest _ v

mutual
/-- Pointwise equation-equivalent second-order assignments induce the same
action on all terms, including terms under arbitrarily many binders. -/
theorem instInto_pointwise_congr {M : List (MetaArity S)}
    (left right : (i : Fin M.length) →
      Term (withMetas S N) (M.get i).1 (M.get i).2)
    (related : ∀ i, EqClosure E (left i) (right i)) :
    ∀ {Γ : Ctx S} {s : S.Srt}
      (term : Term (withMetas S M) Γ s),
      EqClosure E (instInto left term) (instInto right term)
  | _, _, .var _ => .refl _
  | _, _, .op (Sum.inl op) args => by
      change EqClosure E
        (Term.op (Sum.inl op) (instIntoArgs left args))
        (Term.op (Sum.inl op) (instIntoArgs right args))
      exact EqClosure.cong (E := E) (S := withMetas S N) (Sum.inl op)
        (instIntoArgs_pointwise_congr left right related args)
  | _, _, .op (Sum.inr (.mk i)) args => by
      let firstArgs := instIntoArgs left args
      let secondArgs := instIntoArgs right args
      have argumentRelation : EqArgs E firstArgs secondArgs :=
        instIntoArgs_pointwise_congr left right related args
      have substitutionRelation : ∀ (s : S.Srt) (v : Var (M.get i).1 s),
          EqClosure E (argsToSub firstArgs s v)
            (argsToSub secondArgs s v) :=
        eqArgs_argsToSub E argumentRelation
      exact EqClosure.trans
        (eqClosure_bind (argsToSub firstArgs) (related i))
        (eqClosure_bind_pointwise (argsToSub firstArgs)
          (argsToSub secondArgs) substitutionRelation (right i))

/-- The same congruence on each argument of an authored operator. -/
theorem instIntoArgs_pointwise_congr {M : List (MetaArity S)}
    (left right : (i : Fin M.length) →
      Term (withMetas S N) (M.get i).1 (M.get i).2)
    (related : ∀ i, EqClosure E (left i) (right i)) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S M) arities Γ),
      EqArgs E (instIntoArgs left args) (instIntoArgs right args)
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (instInto_pointwise_congr left right related head)
        (instIntoArgs_pointwise_congr left right related tail)
end

mutual
/-- To transport every derived equation along a second-order assignment,
it suffices to transport each authored generator after instantiating its
schema metavariables. The conclusion includes closure under binders and
metavariable application. -/
theorem instInto_eqClosure_generators {M L : List (MetaArity S)}
    (D : List (EqAxiom (withMetas S N) L))
    (assignment : (i : Fin M.length) →
      Term (withMetas S N) (M.get i).1 (M.get i).2)
    {F : List (EqAxiom (withMetas S M) K)}
    (generators : ∀ (i : Fin F.length)
      (schema : (k : Fin K.length) →
        Term (withMetas S M) (K.get k).1 (K.get k).2),
      EqClosure D
        (instInto assignment (instantiate schema (F.get i).lhs))
        (instInto assignment (instantiate schema (F.get i).rhs))) :
    ∀ {Γ : Ctx S} {s : S.Srt}
      {left right : Term (withMetas S M) Γ s},
      EqClosure F left right →
      EqClosure D (instInto assignment left) (instInto assignment right)
  | _, _, _, _, .ax i schema close => by
      simp only [instInto_bind]
      exact eqClosure_bind
        (fun s v => instInto assignment (close s v)) (generators i schema)
  | _, _, _, _, .refl _ => .refl _
  | _, _, _, _, .symm related =>
      .symm (instInto_eqClosure_generators D assignment generators related)
  | _, _, _, _, .trans first second =>
      .trans (instInto_eqClosure_generators D assignment generators first)
        (instInto_eqClosure_generators D assignment generators second)
  | _, _, _, _, .cong (Sum.inl op) related => by
      change EqClosure D
        (Term.op (Sum.inl op) (instIntoArgs assignment _))
        (Term.op (Sum.inl op) (instIntoArgs assignment _))
      exact EqClosure.cong (E := D) (S := withMetas S N) (Sum.inl op)
        (instInto_eqArgs_generators D assignment generators related)
  | _, _, _, _, .cong (Sum.inr (.mk i)) related => by
      have mapped := instInto_eqArgs_generators D assignment generators related
      exact eqClosure_bind_pointwise _ _
        (eqArgs_argsToSub D mapped) (assignment i)

/-- Generator transport also acts on every argument position of a binding
operation; the head is checked in its extended local context. -/
theorem instInto_eqArgs_generators {M L : List (MetaArity S)}
    (D : List (EqAxiom (withMetas S N) L))
    (assignment : (i : Fin M.length) →
      Term (withMetas S N) (M.get i).1 (M.get i).2)
    {F : List (EqAxiom (withMetas S M) K)}
    (generators : ∀ (i : Fin F.length)
      (schema : (k : Fin K.length) →
        Term (withMetas S M) (K.get k).1 (K.get k).2),
      EqClosure D
        (instInto assignment (instantiate schema (F.get i).lhs))
        (instInto assignment (instantiate schema (F.get i).rhs))) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {left right : Args (withMetas S M) arities Γ},
      EqArgs F left right →
      EqArgs D (instIntoArgs assignment left) (instIntoArgs assignment right)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail =>
      .cons (instInto_eqClosure_generators D assignment generators head)
        (instInto_eqArgs_generators D assignment generators tail)
end

namespace Controls

variable (S : Signature) (sort : S.Srt)

private abbrev TwoGenerators : List (MetaArity S) :=
  [([], sort), ([], sort)]

private def first : Term (withMetas S (TwoGenerators S sort)) [] sort :=
  metaVar (M := TwoGenerators S sort) ⟨0, by simp [TwoGenerators]⟩

private def second : Term (withMetas S (TwoGenerators S sort)) [] sort :=
  metaVar (M := TwoGenerators S sort) ⟨1, by simp [TwoGenerators]⟩

/-- An authored equation can identify two generators that the raw
second-order context category keeps apart. -/
private def identifyGenerators :
    EqAxiom (withMetas S (TwoGenerators S sort)) [] where
  ctx := []
  sort := sort
  lhs := embed (M := []) (first S sort)
  rhs := embed (M := []) (second S sort)

theorem distinct_before_equation : first S sort ≠ second S sort :=
  distinct_nullary_generators S sort

theorem related_after_equation :
    EqClosure [identifyGenerators S sort] (first S sort) (second S sort) := by
  have generated := EqClosure.ax (E := [identifyGenerators S sort])
    (⟨0, by decide⟩ : Fin 1)
    (fun i => Fin.elim0 i)
    (fun _ v => Term.var v)
  simpa [identifyGenerators, first, second, instantiate_embed, bind_id]
    using generated

end Controls

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.instInto_pointwise_congr
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.instInto_eqClosure_generators
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Controls.related_after_equation
