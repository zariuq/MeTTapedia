import Mettapedia.Languages.Agda.Specification.SpineComposition

/-!
# Positive and negative controls for the Agda spine reference

The examples distinguish binding from non-binding abstractions, preserve a free
variable under beta computation, exercise a lambda substituted at an applied
variable, and preserve type sort annotations. The final control proves that a
well-scoped self-application has no finite application derivation.
-/

namespace Mettapedia.Languages.Agda.Specification

namespace Examples

def identity : Term n := .lam (.bind (Term.bvar 0))

def identity_apply (t : Term n) : Apply identity (Spine.singleton t) t :=
  .lam (.bind (Substitute.bvar (Substitution.single t) 0)) (.nil t)

/-- `NoAbs` does not consume a variable from its body's scope. -/
def noBind_apply (t u : Term n) :
    Apply (.lam (.noBind t)) (Spine.singleton u) t :=
  .lam (.noBind t u) (.nil t)

/-- `(lambda x. lambda y. x) u` keeps every free variable of `u` free. -/
def constant_apply (u : Term n) :
    Apply (.lam (.bind (.lam (.bind (Term.bvar (Fin.succ 0))))))
      (Spine.singleton u) (.lam (.bind u.weaken)) :=
  .lam (.bind (.lam (.bind (Substitute.bvar
    (Substitution.lift (Substitution.single u)) (Fin.succ 0))))) (.nil _)

/-- A free variable survives the inner binder; it does not turn into index zero. -/
def capture_preserved :
    Apply (.lam (.bind (.lam (.bind (Term.bvar (1 : Fin 3))))))
      (Spine.singleton (Term.bvar (0 : Fin 1)))
      (.lam (.bind (Term.bvar (1 : Fin 2)))) :=
  constant_apply (Term.bvar 0)

theorem capture_rejected :
    ¬ Nonempty (Apply (.lam (.bind (.lam (.bind (Term.bvar (1 : Fin 3))))))
      (Spine.singleton (Term.bvar (0 : Fin 1)))
      (.lam (.bind (Term.bvar (0 : Fin 2))))) := by
  rintro ⟨h⟩
  have bad := h.deterministic capture_preserved
  cases bad

/-- Substitution exposes and computes a beta redex at a formerly variable head. -/
def substitute_applied_variable (u : Term 0) :
    Substitute (Substitution.single identity)
      (.var (0 : Fin 1) (Spine.singleton u.weaken)) u := by
  apply Substitute.var
    (SubstituteSpine.cons ?_ (SubstituteSpine.nil _)) (identity_apply u)
  have h := Substitute.identity u
  simpa only [Term.rename_id, Term.weaken] using
    h.mapRenaming Fin.succ id (Substitution.single identity) (fun i => Fin.elim0 i)

/-- Two successive beta applications consume the spine in its declared order. -/
def constant_two_arguments (u v : Term 0) :
    Apply (.lam (.bind (.lam (.bind (Term.bvar (1 : Fin 2))))))
      (.cons (.apply u) (Spine.singleton v)) u := by
  have first := constant_apply u
  have second : Apply (.lam (.bind u.weaken)) (Spine.singleton v) u := by
    apply Apply.lam (Instantiate.bind ?_) (.nil u)
    simpa only [Term.rename_id, Term.weaken] using
      (Substitute.identity u).mapRenaming Fin.succ id
        (Substitution.single v) (fun i => Fin.elim0 i)
  exact first.append second

def annotatedPi : Term 0 :=
  .pi (.el 1 (.sort 0)) (.bind (.el 1 (.sort 0)))

def annotatedPi_identity : Substitute Substitution.identity annotatedPi annotatedPi :=
  Substitute.identity annotatedPi

theorem pi_is_not_a_function (t : Term 0) :
    ¬ Nonempty (Apply annotatedPi (Spine.singleton identity) t) :=
  Apply.no_pi_cons _ _ _ _ _

theorem sort_is_not_a_function (t : Term 0) :
    ¬ Nonempty (Apply (.sort 0) (Spine.singleton identity) t) :=
  Apply.no_sort_cons _ _ _ _

def definition_spine (u v : Term n) :
    Apply (.defn "f" (Spine.singleton u)) (Spine.singleton v)
      (.defn "f" (.cons (.apply u) (Spine.singleton v))) :=
  Apply.definition "f" (Spine.singleton u) (Spine.singleton v)

def constructor_spine (u v : Term n) :
    Apply (.con "c" (Spine.singleton u)) (Spine.singleton v)
      (.con "c" (.cons (.apply u) (Spine.singleton v))) :=
  Apply.constructor "c" (Spine.singleton u) (Spine.singleton v)

/-- The beta-normal lambda used in the usual divergent self-application. -/
def selfApply : Term n :=
  .lam (.bind (.var 0 (Spine.singleton (Term.bvar 0))))

private theorem singleton_variable_result {σ : Substitution n m}
    {es : Spine n} {fs : Spine m} (h : SubstituteSpine σ es fs) (i : Fin n)
    (he : es = Spine.singleton (Term.bvar i)) : fs = Spine.singleton (σ i) := by
  cases he
  exact h.deterministic (.cons (Substitute.bvar σ i) (.nil σ))

mutual
  private theorem no_selfApply_aux {f t : Term n} {es : Spine n}
      (h : Apply f es t) (hf : f = selfApply)
      (he : es = Spine.singleton selfApply) : False := by
    match h with
    | .nil _ => cases he
    | .var _ _ _ _ => cases hf
    | .defn _ _ _ _ => cases hf
    | .con _ _ _ _ => cases hf
    | .lam hi _ =>
      exact no_selfInstantiate_aux hi (Term.lam.inj hf)
        (Elim.apply.inj (Spine.cons.inj he).1)

  private theorem no_selfInstantiate_aux {b : Abs n} {u v : Term n}
      (h : Instantiate b u v)
      (hb : b = .bind (.var 0 (Spine.singleton (Term.bvar 0))))
      (hu : u = selfApply) : False := by
    match h with
    | .bind hs => exact no_selfSubstitute_aux hs 0 (Abs.bind.inj hb) hu
    | .noBind _ _ => cases hb

  private theorem no_selfSubstitute_aux {σ : Substitution n m} {t : Term n} {u : Term m}
      (h : Substitute σ t u) (i : Fin n)
      (ht : t = .var i (Spine.singleton (Term.bvar i)))
      (hi : σ i = selfApply) : False := by
    match h with
    | .var he ha =>
      have head := (congrArg σ (Term.var.inj ht).1).trans hi
      have spine := (singleton_variable_result he i (Term.var.inj ht).2).trans
        (congrArg Spine.singleton hi)
      exact no_selfApply_aux ha head spine
    | .defn _ _ => cases ht
    | .con _ _ => cases ht
    | .lam _ => cases ht
    | .pi _ _ => cases ht
    | .sort _ _ => cases ht
    | .level _ _ => cases ht
end

/-- Scoping alone does not justify a total hereditary normalizer. -/
theorem selfApply_no_result {t : Term n}
    (h : Apply selfApply (Spine.singleton selfApply) t) : False :=
  no_selfApply_aux h rfl rfl

end Examples

end Mettapedia.Languages.Agda.Specification
