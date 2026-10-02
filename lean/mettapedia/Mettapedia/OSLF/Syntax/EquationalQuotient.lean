import Mettapedia.OSLF.Syntax.PositionEnumeration
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment

/-!
# Equations as a first-class component

A language definition is a triple, and the second component is not decoration:
the objects the semantics talks about are equation classes, not terms.  This
module makes that structural rather than incidental on the binding-signature
carrier.

Alpha-conversion is not among the equations here, and that is the point of the
carrier: a bound occurrence is a position, so alpha-equivalent presentations are
one term and there is nothing for an equation to say about them.  What remains
in the second component is exactly the structural theory the language author
writes down.

What is proved: renaming, substitution and plugging all descend to the
equational theory, so the quotient carrier is again a presheaf with substitution,
and stepping modulo the equations is well defined on it -- the choice of
representative cannot change an observable.

What is proved *not* to descend: the number of times a one-hole context uses its
hole.  So the linearity condition that makes a chosen occurrence a redex
position is not an invariant of the equation class, and the generator's input has
to be a representative rather than a class.  That is a second sense, independent
of the first, in which the position is extra data.  A positive control shows the
failure is not universal: under the structural equations an author actually
writes for a parallel operator -- associativity and commutativity -- occurrence
counts are invariant, so for those theories the condition does descend.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

/-! ## Renaming and substitution descend -/

mutual
theorem eqClosure_rename {M : List (MetaArity S)} {E : List (EqAxiom S M)} :
    ∀ {Γ Δ : Ctx S} (rho : Ren S Γ Δ) {s : S.Srt} {t u : Term S Γ s},
      EqClosure E t u → EqClosure E (rename rho t) (rename rho u)
  | _, _, rho, _, _, _, .ax i body ambient ordinary => by
      rw [ContextualAssignment.rename_instantiate, ContextualAssignment.rename_instantiate]
      exact .ax i body (fun s v => rename rho (ambient s v))
        (fun s v => rename rho (ordinary s v))
  | _, _, _, _, _, _, .refl _ => .refl _
  | _, _, rho, _, _, _, .symm h => .symm (eqClosure_rename rho h)
  | _, _, rho, _, _, _, .trans h h' =>
      .trans (eqClosure_rename rho h) (eqClosure_rename rho h')
  | _, _, rho, _, _, _, .cong o h => by
      rw [rename, rename]
      exact .cong o (eqArgs_renameArgs rho h)

theorem eqArgs_renameArgs {M : List (MetaArity S)} {E : List (EqAxiom S M)} :
    ∀ {Γ Δ : Ctx S} (rho : Ren S Γ Δ) {ars : List (List S.Srt × S.Srt)}
      {as as' : Args S ars Γ},
      EqArgs E as as' → EqArgs E (renameArgs rho as) (renameArgs rho as')
  | _, _, _, _, _, _, .nil => .nil
  | _, _, rho, _, _, _, .cons (bs := bs) h ht =>
      .cons (eqClosure_rename (liftRen rho bs) h) (eqArgs_renameArgs rho ht)
end

mutual
theorem eqClosure_bind {M : List (MetaArity S)} {E : List (EqAxiom S M)} :
    ∀ {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) {s : S.Srt} {t u : Term S Γ s},
      EqClosure E t u → EqClosure E (bind sigma t) (bind sigma u)
  | _, _, sigma, _, _, _, .ax i body ambient ordinary => by
      rw [ContextualAssignment.bind_instantiate, ContextualAssignment.bind_instantiate]
      exact .ax i body (fun s v => bind sigma (ambient s v))
        (fun s v => bind sigma (ordinary s v))
  | _, _, _, _, _, _, .refl _ => .refl _
  | _, _, sigma, _, _, _, .symm h => .symm (eqClosure_bind sigma h)
  | _, _, sigma, _, _, _, .trans h h' =>
      .trans (eqClosure_bind sigma h) (eqClosure_bind sigma h')
  | _, _, sigma, _, _, _, .cong o h => by
      rw [bind, bind]
      exact .cong o (eqArgs_bindArgs sigma h)

theorem eqArgs_bindArgs {M : List (MetaArity S)} {E : List (EqAxiom S M)} :
    ∀ {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) {ars : List (List S.Srt × S.Srt)}
      {as as' : Args S ars Γ},
      EqArgs E as as' → EqArgs E (bindArgs sigma as) (bindArgs sigma as')
  | _, _, _, _, _, _, .nil => .nil
  | _, _, sigma, _, _, _, .cons (bs := bs) h ht =>
      .cons (eqClosure_bind (liftSub sigma bs) h) (eqArgs_bindArgs sigma ht)
end

/-- Equal substitutions stay equal under a binder. -/
theorem eqClosure_liftSub {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {Γ Δ : Ctx S} (sigma sigma' : Sub S Γ Δ)
    (h : ∀ (s : S.Srt) (x : Var Γ s), EqClosure E (sigma s x) (sigma' s x)) :
    ∀ (bs : List S.Srt) (s : S.Srt) (x : Var (bs ++ Γ) s),
      EqClosure E (liftSub sigma bs s x) (liftSub sigma' bs s x)
  | [], s, x => h s x
  | _ :: bs, s, x => by
      cases x with
      | zero => exact .refl _
      | succ w =>
          exact eqClosure_rename (fun _ v => Var.succ v)
            (eqClosure_liftSub sigma sigma' h bs s w)

mutual
/-- Substituting equal terms gives equal terms. -/
theorem eqClosure_bind_pointwise {M : List (MetaArity S)} {E : List (EqAxiom S M)} :
    ∀ {Γ Δ : Ctx S} (sigma sigma' : Sub S Γ Δ)
      (_ : ∀ (r : S.Srt) (x : Var Γ r), EqClosure E (sigma r x) (sigma' r x))
      {s : S.Srt} (t : Term S Γ s), EqClosure E (bind sigma t) (bind sigma' t)
  | _, _, _, _, h, _, .var v => h _ v
  | _, _, sigma, sigma', h, _, .op o args =>
      .cong o (eqArgs_bindArgs_pointwise sigma sigma' h args)

theorem eqArgs_bindArgs_pointwise {M : List (MetaArity S)} {E : List (EqAxiom S M)} :
    ∀ {Γ Δ : Ctx S} (sigma sigma' : Sub S Γ Δ)
      (_ : ∀ (r : S.Srt) (x : Var Γ r), EqClosure E (sigma r x) (sigma' r x))
      {ars : List (List S.Srt × S.Srt)} (as : Args S ars Γ),
      EqArgs E (bindArgs sigma as) (bindArgs sigma' as)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, sigma, sigma', h, _, .cons (bs := bs) hd tl =>
      .cons (eqClosure_bind_pointwise (liftSub sigma bs) (liftSub sigma' bs)
          (eqClosure_liftSub sigma sigma' h bs) hd)
        (eqArgs_bindArgs_pointwise sigma sigma' h tl)
end

/-- Reading one of two related argument lists gives related terms. The
argument positions are the dependency context of a metavariable occurrence. -/
theorem eqArgs_argsToSub {M : List (MetaArity S)} (E : List (EqAxiom S M)) :
    ∀ {bs : List S.Srt} {Γ : Ctx S}
      {args args' : Args S (bs.map (fun b => ([], b))) Γ},
      EqArgs E args args' →
      ∀ (s : S.Srt) (v : Var bs s),
        EqClosure E (argsToSub args s v) (argsToSub args' s v)
  | [], _, _, _, _, _, v => nomatch v
  | _ :: _, _, .cons _ _, .cons _ _, .cons related _rest, _, .zero => related
  | _ :: _, _, .cons _ _, .cons _ _, .cons _related rest, _, .succ v =>
      eqArgs_argsToSub E rest _ v

/-- **Plugging descends.**  Equal contexts with equal terms in their holes plug
to equal terms, so a factorisation is a construction on equation classes. -/
theorem eqClosure_inst {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {Γ : Ctx S} {c s : S.Srt} {K K' : Term S (c :: Γ) s} {r r' : Term S Γ c}
    (hK : EqClosure E K K') (hr : EqClosure E r r') :
    EqClosure E (inst K r) (inst K' r') :=
  .trans (eqClosure_bind (extend r) hK)
    (eqClosure_bind_pointwise (extend r) (extend r')
      (fun _ x => by
        cases x with
        | zero => exact hr
        | succ _ => exact .refl _) K')

/-! ## The quotient carrier -/

/-- The equational theory as a setoid on each context and sort. -/
def eqSetoid {M : List (MetaArity S)} (E : List (EqAxiom S M)) (Γ : Ctx S) (s : S.Srt) :
    Setoid (Term S Γ s) where
  r := EqClosure E
  iseqv := ⟨fun t => EqClosure.refl t, EqClosure.symm, EqClosure.trans⟩

/-- Terms modulo the equations. -/
abbrev TermQ {M : List (MetaArity S)} (E : List (EqAxiom S M)) (Γ : Ctx S) (s : S.Srt) :
    Type :=
  Quotient (eqSetoid E Γ s)

/-- Renaming descends to the quotient. -/
def renameQ {M : List (MetaArity S)} {E : List (EqAxiom S M)} {Γ Δ : Ctx S}
    (rho : Ren S Γ Δ) {s : S.Srt} : TermQ E Γ s → TermQ E Δ s :=
  Quotient.map (rename rho) (fun _ _ h => eqClosure_rename rho h)

/-- **Substitution descends to the quotient.**  So the quotient is again a
presheaf on contexts with a substitution action: the second component of a
language definition does not cost the first its structure. -/
def bindQ {M : List (MetaArity S)} {E : List (EqAxiom S M)} {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) {s : S.Srt} : TermQ E Γ s → TermQ E Δ s :=
  Quotient.map (bind sigma) (fun _ _ h => eqClosure_bind sigma h)

/-- Plugging descends, in both arguments at once. -/
def instQ {M : List (MetaArity S)} {E : List (EqAxiom S M)} {Γ : Ctx S} {c s : S.Srt} :
    TermQ E (c :: Γ) s → TermQ E Γ c → TermQ E Γ s :=
  Quotient.map₂ inst (fun _ _ hK _ _ hr => eqClosure_inst hK hr)

theorem bindQ_mk {M : List (MetaArity S)} {E : List (EqAxiom S M)} {Γ Δ : Ctx S}
    (sigma : Sub S Γ Δ) {s : S.Srt} (t : Term S Γ s) :
    bindQ (E := E) sigma (Quotient.mk _ t) = Quotient.mk _ (bind sigma t) := rfl

theorem instQ_mk {M : List (MetaArity S)} {E : List (EqAxiom S M)} {Γ : Ctx S}
    {c s : S.Srt} (K : Term S (c :: Γ) s) (r : Term S Γ c) :
    instQ (E := E) (Quotient.mk _ K) (Quotient.mk _ r) = Quotient.mk _ (inst K r) := rfl

/-! ## Stepping is an observable of the class, not of the representative -/

/-- Stepping modulo the equations, as a relation on equation classes. -/
def StepQ {M : List (MetaArity S)} (E : List (EqAxiom S M))
    (P : PositionedRewrite (withMetas S M)) {s : S.Srt} :
    TermQ E [] s → TermQ E [] s → Prop :=
  Quotient.lift₂ (StepModE E P)
    (fun _ _ _ _ ha hb => propext
      ⟨fun h => stepModE_resp_right (stepModE_resp_left (EqClosure.symm ha) h) hb,
       fun h => stepModE_resp_right (stepModE_resp_left ha h) (EqClosure.symm hb)⟩)

/-- **The representative cannot change the observation.** -/
theorem stepQ_mk {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} (t u : Term S [] s) :
    StepQ E P (Quotient.mk _ t) (Quotient.mk _ u) ↔ StepModE E P t u := Iff.rfl

theorem stepQ_congr {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    {P : PositionedRewrite (withMetas S M)} {s : S.Srt} {t t' u u' : Term S [] s}
    (ht : EqClosure E t t') (hu : EqClosure E u u') :
    StepModE E P t u ↔ StepModE E P t' u' := by
  have h : StepQ E P (Quotient.mk _ t) (Quotient.mk _ u)
      ↔ StepQ E P (Quotient.mk _ t') (Quotient.mk _ u') := by
    rw [Quotient.sound (a := t) (b := t') ht, Quotient.sound (a := u) (b := u') hu]
  exact h

/-! ## What does not descend

Occurrence counting is not stable under an arbitrary equational theory, and the
linearity condition that makes a chosen occurrence a redex position is an
occurrence count.  So the generator's input cannot be read off an equation
class: it has to be read off a representative. -/

namespace Duplication

inductive Srt2 where
  | tm
  deriving DecidableEq

inductive Op2 : Srt2 → Type where
  | dup : Op2 Srt2.tm
  | cst : Op2 Srt2.tm

abbrev dsig : Signature where
  Srt := Srt2
  Op := Op2
  arity := fun {_} o => match o with
    | .dup => [([], Srt2.tm), ([], Srt2.tm)]
    | .cst => []

/-- `x = dup(x, x)`: an author's equation that is not linear. -/
def dupAxiom : EqAxiom dsig [] where
  ctx := [Srt2.tm]
  sort := Srt2.tm
  lhs := Term.var Var.zero
  rhs := Term.op (S := withMetas dsig []) (Sum.inl Op2.dup)
    (.cons (Term.var Var.zero) (.cons (Term.var Var.zero) .nil))

def dupE : List (EqAxiom dsig []) := [dupAxiom]

/-- The bare hole. -/
def hole1 : Term dsig [Srt2.tm] Srt2.tm := Term.var Var.zero

/-- The hole, duplicated. -/
def hole2 : Term dsig [Srt2.tm] Srt2.tm :=
  Term.op (S := dsig) Op2.dup (.cons (Term.var Var.zero) (.cons (Term.var Var.zero) .nil))

/-- There are no metavariables, so there is nothing to supply for them. -/
def noBody : (k : Fin ([] : List (MetaArity dsig)).length) →
    Term dsig (([] : List (MetaArity dsig)).get k).1 (([] : List (MetaArity dsig)).get k).2 :=
  fun k => k.elim0

theorem hole1_eq_hole2 : EqClosure dupE hole1 hole2 := by
  have h : EqClosure dupE
      (bind (fun _ _ => Term.var (Var.zero : Var [Srt2.tm] Srt2.tm))
        (instantiate noBody dupAxiom.lhs))
      (bind (fun _ _ => Term.var (Var.zero : Var [Srt2.tm] Srt2.tm))
        (instantiate noBody dupAxiom.rhs)) :=
    EqClosure.ax_closed dupE ⟨0, by decide⟩ noBody
      (fun _ _ => Term.var (Var.zero : Var [Srt2.tm] Srt2.tm))
  simpa only [dupAxiom, hole1, hole2, instantiate, instantiateArgs, bind, bindArgs,
    liftSub] using h

theorem holeCount_hole1 : holeCount (S := dsig) (Γ := []) (c := Srt2.tm) hole1 = 1 := rfl

theorem holeCount_hole2 : holeCount (S := dsig) (Γ := []) (c := Srt2.tm) hole2 = 2 := rfl

/-- **Occurrence counts are not invariants of the equation class**, so neither is
linearity of a one-hole context. -/
theorem holeCount_not_eqClosure_invariant :
    ∃ K K' : Term dsig [Srt2.tm] Srt2.tm,
      EqClosure dupE K K' ∧ holeCount K = 1 ∧ holeCount K' ≠ 1 :=
  ⟨hole1, hole2, hole1_eq_hole2, holeCount_hole1, by rw [holeCount_hole2]; decide⟩

/-- And the two are decompositions of terms in one class, so the failure is not
an artefact of comparing unrelated things. -/
theorem both_factor_equal_terms (r : Term dsig [] Srt2.tm) :
    EqClosure dupE (inst hole1 r) (inst hole2 r) :=
  eqClosure_inst hole1_eq_hole2 (EqClosure.refl r)

end Duplication

/-! ## What does descend

The failure above is not universal.  Under the structural equations an author
actually writes for a parallel operator -- associativity and commutativity, the
ones a process calculus carries -- occurrence counts are invariant, so for those
theories linearity of a context *is* a property of the class. -/

namespace Structural

inductive SrtP where
  | pr
  deriving DecidableEq

inductive OpP : SrtP → Type where
  | par : OpP SrtP.pr
  | nul : OpP SrtP.pr

abbrev psig : Signature where
  Srt := SrtP
  Op := OpP
  arity := fun {_} o => match o with
    | .par => [([], SrtP.pr), ([], SrtP.pr)]
    | .nul => []

/-- `par(x, y) = par(y, x)`. -/
def commAxiom : EqAxiom psig [] where
  ctx := [SrtP.pr, SrtP.pr]
  sort := SrtP.pr
  lhs := Term.op (S := withMetas psig []) (Sum.inl OpP.par)
    (.cons (Term.var Var.zero) (.cons (Term.var (Var.succ Var.zero)) .nil))
  rhs := Term.op (S := withMetas psig []) (Sum.inl OpP.par)
    (.cons (Term.var (Var.succ Var.zero)) (.cons (Term.var Var.zero) .nil))

/-- `par(par(x, y), z) = par(x, par(y, z))`. -/
def assocAxiom : EqAxiom psig [] where
  ctx := [SrtP.pr, SrtP.pr, SrtP.pr]
  sort := SrtP.pr
  lhs := Term.op (S := withMetas psig []) (Sum.inl OpP.par)
    (.cons (Term.op (S := withMetas psig []) (Sum.inl OpP.par)
        (.cons (Term.var Var.zero) (.cons (Term.var (Var.succ Var.zero)) .nil)))
      (.cons (Term.var (Var.succ (Var.succ Var.zero))) .nil))
  rhs := Term.op (S := withMetas psig []) (Sum.inl OpP.par)
    (.cons (Term.var Var.zero)
      (.cons (Term.op (S := withMetas psig []) (Sum.inl OpP.par)
        (.cons (Term.var (Var.succ Var.zero))
          (.cons (Term.var (Var.succ (Var.succ Var.zero))) .nil))) .nil))

def acE : List (EqAxiom psig []) := [commAxiom, assocAxiom]

/-- Each axiom moves its variables around without adding or dropping any, so
under any closing substitution the two sides use every variable equally often. -/
theorem ax_counts : ∀ (i : Fin acE.length) {Γ : Ctx psig} {c : SrtP} (x : Var Γ c)
    (body : (k : Fin ([] : List (MetaArity psig)).length) →
      Term psig (([] : List (MetaArity psig)).get k).1 (([] : List (MetaArity psig)).get k).2)
    (close : Sub psig (acE.get i).ctx Γ),
    countVar x (bind close (instantiate body (acE.get i).lhs))
      = countVar x (bind close (instantiate body (acE.get i).rhs))
  | ⟨0, _⟩, _, _, x, body, close => by
      show countVar x (bind close (instantiate body commAxiom.lhs))
        = countVar x (bind close (instantiate body commAxiom.rhs))
      simp only [commAxiom, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        countVar, countVarArgs, weakenVar]
      omega
  | ⟨1, _⟩, _, _, x, body, close => by
      show countVar x (bind close (instantiate body assocAxiom.lhs))
        = countVar x (bind close (instantiate body assocAxiom.rhs))
      simp only [assocAxiom, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        countVar, countVarArgs, weakenVar]
      omega
  | ⟨_ + 2, h⟩, _, _, _, _, _ => absurd h (by simp [acE])

mutual
/-- **Occurrence counts are invariants of the structural theory.** -/
theorem countVar_ac : ∀ {Γ : Ctx psig} {c : SrtP} (x : Var Γ c) {s : SrtP}
    {t u : Term psig Γ s}, EqClosure acE t u → countVar x t = countVar x u
  | _, _, x, _, _, _, .ax i body ambient ordinary => by
      simp only [ContextualAssignment.instantiate_noMetas]
      exact ax_counts i x (fun k => Fin.elim0 k) ordinary
  | _, _, _, _, _, _, .refl _ => rfl
  | _, _, x, _, _, _, .symm h => (countVar_ac x h).symm
  | _, _, x, _, _, _, .trans h h' => (countVar_ac x h).trans (countVar_ac x h')
  | _, _, x, _, _, _, .cong _ h => by
      rw [countVar, countVar]
      exact countVarArgs_ac x h

theorem countVarArgs_ac : ∀ {Γ : Ctx psig} {c : SrtP} (x : Var Γ c)
    {ars : List (List SrtP × SrtP)} {as as' : Args psig ars Γ},
    EqArgs acE as as' → countVarArgs x as = countVarArgs x as'
  | _, _, _, _, _, _, .nil => rfl
  | _, _, x, _, _, _, .cons (bs := bs) h ht => by
      rw [countVarArgs, countVarArgs, countVar_ac (weakenVar bs x) h,
        countVarArgs_ac x ht]
end

/-- **So for this theory linearity is a property of the class.** -/
theorem holeCount_ac_invariant {Γ : Ctx psig} {c s : SrtP} {K K' : Term psig (c :: Γ) s}
    (h : EqClosure acE K K') : holeCount K = holeCount K' :=
  countVar_ac Var.zero h

end Structural

end Mettapedia.OSLF.Binding
