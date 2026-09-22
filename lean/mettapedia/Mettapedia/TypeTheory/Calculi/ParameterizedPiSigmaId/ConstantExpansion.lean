import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution

/-!
# Closed constant expansion commutes with binding

An expansion assigns a closed term to each declaration name. It substitutes
those terms for constants, preserving all other syntax. Expansion is not
normalization: inserted bodies are not expanded again. A declaration package
must independently justify both its chosen bodies and its computation rules.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstantExpansion

variable {Head : Type} {n m : Nat}

abbrev Bodies (Head : Type) := DeclName → Tm Head 0

/-- Constant names in traversal order, retaining repeated occurrences. Bound
variables and heads contribute no declaration dependencies. -/
def constantNames {n : Nat} : Tm Head n → List DeclName
  | .var _ | .head _ => []
  | .const name => [name]
  | .pi A B | .sigma A B => constantNames A ++ constantNames B
  | .id A a b => constantNames A ++ constantNames a ++ constantNames b
  | .lam body => constantNames body
  | .app f a | .pair f a => constantNames f ++ constantNames a
  | .fst p | .snd p | .refl p => constantNames p

@[simp] theorem constantNames_rename (rho : Ren n m) (term : Tm Head n) :
    constantNames (rename rho term) = constantNames term := by
  induction term generalizing m <;> simp_all [rename, constantNames]

@[simp] theorem constantNames_liftClosed (term : Tm Head 0) :
    constantNames (liftClosed term : Tm Head n) = constantNames term :=
  constantNames_rename Fin.elim0 term

/-- Simultaneous replacement of constants by closed bodies. -/
def expand (bodies : Bodies Head) {n : Nat} : Tm Head n → Tm Head n
  | .var i => .var i
  | .const c => liftClosed (bodies c)
  | .head h => .head h
  | .pi A B => .pi (expand bodies A) (expand bodies B)
  | .sigma A B => .sigma (expand bodies A) (expand bodies B)
  | .id A a b => .id (expand bodies A) (expand bodies a) (expand bodies b)
  | .lam body => .lam (expand bodies body)
  | .app f a => .app (expand bodies f) (expand bodies a)
  | .pair a b => .pair (expand bodies a) (expand bodies b)
  | .fst p => .fst (expand bodies p)
  | .snd p => .snd (expand bodies p)
  | .refl a => .refl (expand bodies a)

/-- Expansion replaces each constant occurrence's support by the support of
its selected body, preserving order and multiplicity even below binders. -/
theorem constantNames_expand (bodies : Bodies Head) (term : Tm Head n) :
    constantNames (expand bodies term) =
      (constantNames term).flatMap (fun name => constantNames (bodies name)) := by
  induction term <;> simp_all [expand, constantNames, List.flatMap_append]

/-- Expansion reads only the constants actually occurring in the term. -/
theorem expand_eq_of_agreement (first second : Bodies Head) (term : Tm Head n)
    (agree : ∀ name ∈ constantNames term, first name = second name) :
    expand first term = expand second term := by
  induction term <;>
    simp_all [constantNames, expand, List.mem_append, or_imp, forall_and]

@[simp] theorem expand_identity (term : Tm Head n) :
    expand (fun name => .const name) term = term := by
  induction term <;> simp_all only [expand, liftClosed, rename]

@[simp] theorem expand_rename (bodies : Bodies Head) (rho : Ren n m)
    (term : Tm Head n) :
    expand bodies (rename rho term) = rename rho (expand bodies term) := by
  induction term generalizing m with
  | var i => rfl
  | const c => exact (rename_liftClosed rho (bodies c)).symm
  | head h => rfl
  | pi A B ihA ihB => simp only [rename, expand, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, expand, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, expand, ihA, iha, ihb]
  | lam body ih => simp only [rename, expand, ih]
  | app f a ihf iha => simp only [rename, expand, ihf, iha]
  | pair a b iha ihb => simp only [rename, expand, iha, ihb]
  | fst p ih => simp only [rename, expand, ih]
  | snd p ih => simp only [rename, expand, ih]
  | refl a ih => simp only [rename, expand, ih]

@[simp] theorem expand_liftClosed (bodies : Bodies Head) (term : Tm Head 0) :
    expand bodies (liftClosed term : Tm Head n) = liftClosed (expand bodies term) :=
  expand_rename bodies Fin.elim0 term

theorem expand_liftSub (bodies : Bodies Head) (sigma : Sub Head n m) :
    (fun i => expand bodies (liftSub sigma i)) =
      liftSub (fun i => expand bodies (sigma i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact expand_rename bodies wk (sigma j)

/-- Closedness of replacement bodies prevents capture beneath every binder. -/
@[simp] theorem expand_subst (bodies : Bodies Head) (sigma : Sub Head n m)
    (term : Tm Head n) :
    expand bodies (subst sigma term) =
      subst (fun i => expand bodies (sigma i)) (expand bodies term) := by
  induction term generalizing m with
  | var i => rfl
  | const c => exact (subst_liftClosed _ (bodies c)).symm
  | head h => rfl
  | pi A B ihA ihB => simp only [subst, expand, ihA, ihB, expand_liftSub]
  | sigma A B ihA ihB => simp only [subst, expand, ihA, ihB, expand_liftSub]
  | id A a b ihA iha ihb => simp only [subst, expand, ihA, iha, ihb]
  | lam body ih => simp only [subst, expand, ih, expand_liftSub]
  | app f a ihf iha => simp only [subst, expand, ihf, iha]
  | pair a b iha ihb => simp only [subst, expand, iha, ihb]
  | fst p ih => simp only [subst, expand, ih]
  | snd p ih => simp only [subst, expand, ih]
  | refl a ih => simp only [subst, expand, ih]

@[simp] theorem expand_inst0 (bodies : Bodies Head) (argument : Tm Head n)
    (body : Tm Head (n + 1)) :
    expand bodies (inst0 argument body) =
      inst0 (expand bodies argument) (expand bodies body) := by
  rw [inst0, expand_subst, inst0]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Conversion of each named constant to its selected body suffices for
conversion of every open term to its expansion. -/
theorem term_conv_expand (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {root : RootComputation Head}
    (constants : ∀ name, Conv headEq (.const name) (bodies name) root)
    (term : Tm Head n) : Conv headEq term (expand bodies term) root := by
  induction term with
  | var i => exact .refl _
  | const c => exact (constants c).renameTerms Fin.elim0
  | head h => exact .refl _
  | pi A B ihA ihB => exact Conv.congPi ihA ihB
  | sigma A B ihA ihB => exact Conv.congSigma ihA ihB
  | id A a b ihA iha ihb => exact Conv.congId ihA iha ihb
  | lam body ih => exact Conv.congLam ih
  | app f a ihf iha => exact Conv.congApp ihf iha
  | pair a b iha ihb => exact Conv.congPair iha ihb
  | fst p ih => exact Conv.mapCompatible Tm.fst (fun h => .congFst h) ih
  | snd p ih => exact Conv.mapCompatible Tm.snd (fun h => .congSnd h) ih
  | refl a ih => exact Conv.mapCompatible Tm.refl (fun h => .congRefl h) ih

/-- Primitive root conversions, together with the binding laws above,
transport every contextual step, including beta and projections. -/
theorem step_expand (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {source target : RootComputation Head}
    (roots : ∀ {k : Nat} {left right : Tm Head k}, source.step left right →
      Conv headEq (expand bodies left) (expand bodies right) target)
    {left right : Tm Head n} (step : Step headEq left right source) :
    Conv headEq (expand bodies left) (expand bodies right) target := by
  induction step with
  | betaPi body argument =>
      simpa only [expand, expand_inst0] using
        (Relation.EqvGen.rel _ _
          (Step.betaPi (root := target) (headEq := headEq)
            (expand bodies body) (expand bodies argument)))
  | betaSigmaFst a b => exact .rel _ _ (.betaSigmaFst _ _)
  | betaSigmaSnd a b => exact .rel _ _ (.betaSigmaSnd _ _)
  | head equality => exact .rel _ _ (.head equality)
  | root equation => exact roots equation
  | congPiDom _ ih => exact Conv.congPi ih (.refl _)
  | congPiCod _ ih => exact Conv.congPi (.refl _) ih
  | congSigmaDom _ ih => exact Conv.congSigma ih (.refl _)
  | congSigmaCod _ ih => exact Conv.congSigma (.refl _) ih
  | congIdTy _ ih => exact Conv.congId ih (.refl _) (.refl _)
  | congIdLeft _ ih => exact Conv.congId (.refl _) ih (.refl _)
  | congIdRight _ ih => exact Conv.congId (.refl _) (.refl _) ih
  | congLam _ ih => exact Conv.congLam ih
  | congAppFun _ ih => exact Conv.congApp ih (.refl _)
  | congAppArg _ ih => exact Conv.congApp (.refl _) ih
  | congPairFst _ ih => exact Conv.congPair ih (.refl _)
  | congPairSnd _ ih => exact Conv.congPair (.refl _) ih
  | congFst _ ih => exact Conv.mapCompatible Tm.fst (fun h => .congFst h) ih
  | congSnd _ ih => exact Conv.mapCompatible Tm.snd (fun h => .congSnd h) ih
  | congRefl _ ih => exact Conv.mapCompatible Tm.refl (fun h => .congRefl h) ih

theorem conv_expand (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {source target : RootComputation Head}
    (roots : ∀ {k : Nat} {left right : Tm Head k}, source.step left right →
      Conv headEq (expand bodies left) (expand bodies right) target)
    {left right : Tm Head n} (conversion : Conv headEq left right source) :
    Conv headEq (expand bodies left) (expand bodies right) target := by
  induction conversion with
  | rel _ _ step => exact step_expand bodies roots step
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- Relative expansion preserves and reflects conversion when target roots
remain source roots and every expanded source root converts in the target.
The target may retain native computation; it need not be root-empty. -/
theorem conversion_iff_of_roots (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {source target : RootComputation Head}
    (constants : ∀ name, Conv headEq (.const name) (bodies name) source)
    (roots : ∀ {k : Nat} {left right : Tm Head k}, source.step left right →
      Conv headEq (expand bodies left) (expand bodies right) target)
    (included : ∀ {k : Nat} {left right : Tm Head k},
      target.step left right → source.step left right)
    (left right : Tm Head n) :
    Conv headEq left right source ↔
      Conv headEq (expand bodies left) (expand bodies right) target := by
  constructor
  · exact conv_expand bodies roots
  · intro conversion
    have retained : Conv headEq (expand bodies left) (expand bodies right) source := by
      simpa only [Tm.mapHead_id] using conversion.mapHead
        (fun head => head) (fun equality => equality)
        (targetRoot := source)
        (by intro k a b root; simpa only [Tm.mapHead_id] using included root)
    exact .trans _ _ _ (term_conv_expand bodies constants left)
      (.trans _ _ _ retained (.symm _ _ (term_conv_expand bodies constants right)))

#print axioms expand_eq_of_agreement
#print axioms constantNames_expand
#print axioms expand_identity
#print axioms expand_rename
#print axioms expand_liftClosed
#print axioms expand_liftSub
#print axioms expand_subst
#print axioms expand_inst0
#print axioms term_conv_expand
#print axioms step_expand
#print axioms conv_expand
#print axioms conversion_iff_of_roots

end ConstantExpansion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
