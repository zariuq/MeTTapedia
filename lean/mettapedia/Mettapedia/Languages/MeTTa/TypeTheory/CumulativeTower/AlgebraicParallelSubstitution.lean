import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AlgebraicParallel

/-!
# Binding laws for algebraic parallel reduction

Renaming and simultaneous parallel substitution preserve the existing
algebraic parallel relation. In an algebraic occurrence, every repeated
schema variable still shares one source/target pair after transport.
These laws impose no linearity or confluence condition on the schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace AlgebraicParallel

variable {Head : Type} {headEq : Head → Head → Prop}
  {schema : AlgebraicSchema.SchemaFamily Head}

private theorem map_fin_cases {α β : Type} {n : Nat}
    (f : α → β) (head : α) (tail : Fin n → α) :
    (fun i => f (Fin.cases head tail i)) = Fin.cases (f head) (fun i => f (tail i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

mutual

/-- Renaming preserves the actual algebraic parallel relation. -/
theorem par_rename {n m : Nat} (rho : Ren n m) {source target : Tm Head n}
    : ParRed headEq schema source target →
      ParRed headEq schema (rename rho source) (rename rho target)
  | .var _ => .var _
  | .const _ => .const _
  | .head _ => .head _
  | .headRel equality => .headRel equality
  | .pi domain codomain =>
      .pi (par_rename rho domain) (par_rename (liftRen rho) codomain)
  | .sigma domain codomain =>
      .sigma (par_rename rho domain) (par_rename (liftRen rho) codomain)
  | .id carrier left right =>
      .id (par_rename rho carrier) (par_rename rho left) (par_rename rho right)
  | .lam body => .lam (par_rename (liftRen rho) body)
  | .app function argument => .app (par_rename rho function) (par_rename rho argument)
  | .pair first second => .pair (par_rename rho first) (par_rename rho second)
  | .fst pair => .fst (par_rename rho pair)
  | .snd pair => .snd (par_rename rho pair)
  | .refl term => .refl (par_rename rho term)
  | .betaPi body argument => by
      simpa only [rename, rename_inst0] using
        (ParRed.betaPi (par_rename (liftRen rho) body) (par_rename rho argument))
  | .betaSigmaFst first second =>
      .betaSigmaFst (par_rename rho first) (par_rename rho second)
  | .betaSigmaSnd first second =>
      .betaSigmaSnd (par_rename rho first) (par_rename rho second)
  | .algebraic rule sourceSub targetSub arguments => by
      simpa only [rename_subst] using
        (ParRed.algebraic rule (fun i => rename rho (sourceSub i))
          (fun i => rename rho (targetSub i)) (parSub_rename rho arguments))

/-- The coherent metavariable telescope is retained under renaming. -/
theorem parSub_rename {arity n m : Nat} (rho : Ren n m)
    {source target : Sub Head arity n} : ParSub headEq schema source target →
      ParSub headEq schema (fun i => rename rho (source i))
        (fun i => rename rho (target i))
  | .nil => by
      simpa only [show (fun i : Fin 0 => rename rho (Fin.elim0 i)) =
        (fun i : Fin 0 => (Fin.elim0 i : Tm Head m)) from funext fun i => Fin.elim0 i]
        using (ParSub.nil (headEq := headEq) (schema := schema) (ambient := m))
  | .cons head tail => by
      simpa only [map_fin_cases] using
        (ParSub.cons (par_rename rho head) (parSub_rename rho tail))

end

private theorem parallel_liftSub {n m : Nat} {source target : Sub Head n m}
    (arguments : ∀ i, ParRed headEq schema (source i) (target i)) :
    ∀ i, ParRed headEq schema (liftSub source i) (liftSub target i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact .var 0
  · intro prior
    exact par_rename wk (arguments prior)

mutual

/-- Simultaneous parallel substitution preserves every retained schema
occurrence, including repeated metavariables and beta contraction. -/
theorem par_substitute {n m : Nat} {sourceSub targetSub : Sub Head n m}
    (arguments : ∀ i, ParRed headEq schema (sourceSub i) (targetSub i))
    {source target : Tm Head n} : ParRed headEq schema source target →
      ParRed headEq schema (subst sourceSub source) (subst targetSub target)
  | .var index => arguments index
  | .const _ => .const _
  | .head _ => .head _
  | .headRel equality => .headRel equality
  | .pi domain codomain =>
      .pi (par_substitute arguments domain)
        (par_substitute (parallel_liftSub arguments) codomain)
  | .sigma domain codomain =>
      .sigma (par_substitute arguments domain)
        (par_substitute (parallel_liftSub arguments) codomain)
  | .id carrier left right =>
      .id (par_substitute arguments carrier) (par_substitute arguments left)
        (par_substitute arguments right)
  | .lam body => .lam (par_substitute (parallel_liftSub arguments) body)
  | .app function argument =>
      .app (par_substitute arguments function) (par_substitute arguments argument)
  | .pair first second =>
      .pair (par_substitute arguments first) (par_substitute arguments second)
  | .fst pair => .fst (par_substitute arguments pair)
  | .snd pair => .snd (par_substitute arguments pair)
  | .refl term => .refl (par_substitute arguments term)
  | .betaPi body argument => by
      simpa only [subst, subst_inst0] using
        (ParRed.betaPi (par_substitute (parallel_liftSub arguments) body)
          (par_substitute arguments argument))
  | .betaSigmaFst first second =>
      .betaSigmaFst (par_substitute arguments first) (par_substitute arguments second)
  | .betaSigmaSnd first second =>
      .betaSigmaSnd (par_substitute arguments first) (par_substitute arguments second)
  | .algebraic rule source target occurrence => by
      simpa only [subst_comp] using
        (ParRed.algebraic rule (fun i => subst sourceSub (source i))
          (fun i => subst targetSub (target i)) (parSub_substitute arguments occurrence))

/-- Substitution preserves the coherence of the algebraic argument telescope. -/
theorem parSub_substitute {arity n m : Nat} {sourceSub targetSub : Sub Head n m}
    (arguments : ∀ i, ParRed headEq schema (sourceSub i) (targetSub i))
    {source target : Sub Head arity n} : ParSub headEq schema source target →
      ParSub headEq schema (fun i => subst sourceSub (source i))
        (fun i => subst targetSub (target i))
  | .nil => by
      have sourceEmpty : (fun i : Fin 0 => subst sourceSub (Fin.elim0 i)) =
          (fun i : Fin 0 => (Fin.elim0 i : Tm Head m)) := funext fun i => Fin.elim0 i
      have targetEmpty : (fun i : Fin 0 => subst targetSub (Fin.elim0 i)) =
          (fun i : Fin 0 => (Fin.elim0 i : Tm Head m)) := funext fun i => Fin.elim0 i
      simpa only [sourceEmpty, targetEmpty] using
        (ParSub.nil (headEq := headEq) (schema := schema) (ambient := m))
  | .cons head tail => by
      simpa only [map_fin_cases] using
        (ParSub.cons (par_substitute arguments head) (parSub_substitute arguments tail))

end

/-- Opening a binder transports both its body and its argument in parallel. -/
theorem par_inst0 {n : Nat} {argument argument' : Tm Head n}
    {body body' : Tm Head (n + 1)}
    (argumentStep : ParRed headEq schema argument argument')
    (bodyStep : ParRed headEq schema body body') :
    ParRed headEq schema (inst0 argument body) (inst0 argument' body') := by
  apply par_substitute (sourceSub := subst0 argument) (targetSub := subst0 argument') _ bodyStep
  intro i
  refine Fin.cases ?_ ?_ i
  · exact argumentStep
  · intro prior
    exact .var prior

#print axioms par_rename
#print axioms parSub_rename
#print axioms par_substitute
#print axioms parSub_substitute
#print axioms par_inst0

end AlgebraicParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
