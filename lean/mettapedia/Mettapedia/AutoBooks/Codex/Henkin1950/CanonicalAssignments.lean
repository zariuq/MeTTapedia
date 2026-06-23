import Mettapedia.AutoBooks.Codex.Henkin1950.TermQuotients
import Mettapedia.Logic.HOL.Soundness

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Soundness

/-!
Representative-substitution layer for Henkin pp. 86-87.

Henkin's p. 87 lemma evaluates an open formula under an assignment by choosing,
for each free variable, a closed representative term for the assigned domain
element and then replacing the free occurrences of that variable by that
representative. In the trusted HOL core, this is ordinary typed substitution
into the empty context. This file packages that operation and the induced
semantic/quotient interfaces in the paper-facing Codex namespace.
-/

/-- A choice of closed representative term for each free variable in context
`Γ`. -/
abbrev RepresentativeAssignment (Γ : Ctx Atom) :=
  ∀ {τ}, Var Γ τ → ClosedTerm τ

/-- Paper-facing variable assignments into the quotient classes used for
Henkin's canonical domains. -/
abbrev ClassAssignment (T : ClosedTheorySet) (Γ : Ctx Atom) :=
  ∀ {τ}, Var Γ τ → TermClass T τ

namespace RepresentativeAssignment

/-- Extend a representative assignment across one bound variable by choosing a
closed representative for the new head variable. -/
def extend (ρ : RepresentativeAssignment Γ) (t : ClosedTerm σ) :
    RepresentativeAssignment (σ :: Γ)
  | _, .vz => t
  | _, .vs v => ρ v

/-- The valuation on the empty context. -/
def closedValuation (M : HenkinModel Atom Primitive) :
    HenkinModel.Valuation M [] :=
  fun v => nomatch v

/-- The empty-context valuation is vacuously admissible. -/
theorem closedValuation_admissible (M : HenkinModel Atom Primitive) :
    HenkinModel.ValuationAdmissible M (closedValuation M) := by
  intro τ v
  nomatch v

/-- The semantic valuation induced by denoting each chosen closed
representative. -/
def toValuation (M : HenkinModel Atom Primitive)
    (ρ : RepresentativeAssignment Γ) :
    HenkinModel.Valuation M Γ :=
  fun v => HenkinModel.denote M (ρ v) (closedValuation M)

/-- The induced valuation is admissible because every representative is a closed
term. -/
theorem toValuation_admissible (M : HenkinModel Atom Primitive)
    (ρ : RepresentativeAssignment Γ) :
    HenkinModel.ValuationAdmissible M (toValuation M ρ) := by
  intro τ v
  exact
    HenkinModel.denote_admissible
      (M := M)
      (ρ := closedValuation M)
      (hρ := closedValuation_admissible M)
      (t := ρ v)

/-- The quotient-class assignment determined by the chosen representatives. -/
def toClassAssignment (T : ClosedTheorySet)
    (ρ : RepresentativeAssignment Γ) :
    ClassAssignment T Γ :=
  fun v => classOf (T := T) (ρ v)

/-- A representative assignment realizes a quotient-class assignment when each
variable is sent to a representative of the requested class. -/
def Realizes (T : ClosedTheorySet)
    (ρ : RepresentativeAssignment Γ) (ν : ClassAssignment T Γ) : Prop :=
  ∀ {τ} (v : Var Γ τ), classOf (T := T) (ρ v) = ν v

/-- The class assignment induced by representatives is realized by definition. -/
theorem realizes_toClassAssignment
    (T : ClosedTheorySet) (ρ : RepresentativeAssignment Γ) :
    Realizes T ρ (toClassAssignment T ρ) := by
  intro τ v
  rfl

/-- Closing a weakened closed term returns the original representative. -/
@[simp] theorem close_weakenCtx
    (ρ : RepresentativeAssignment Γ) (t : ClosedTerm σ) :
    subst ρ (weakenCtx Γ t) = t := by
  simpa using
    (subst_weakenCtx
      (Base := Atom)
      (Const := Primitive)
      (Γ' := Γ)
      (Δ' := ([] : Ctx Atom))
      (σs := ρ)
      (t := t))

/-- Extending the induced semantic valuation agrees with denoting the chosen
head representative. -/
theorem toValuation_extend
    (M : HenkinModel Atom Primitive)
    (ρ : RepresentativeAssignment Γ) (t : ClosedTerm σ) :
    (toValuation M (extend ρ t) :
        HenkinModel.Valuation M (σ :: Γ)) =
      (HenkinModel.extend M (toValuation M ρ)
        (HenkinModel.denote M t (closedValuation M)) :
          HenkinModel.Valuation M (σ :: Γ)) := by
  funext τ
  funext v
  cases v with
  | vz =>
      rfl
  | vs v =>
      rfl

end RepresentativeAssignment

/-- Replace each free variable in a term by its chosen closed representative. -/
def closeTerm (ρ : RepresentativeAssignment Γ) (t : Term Γ τ) : ClosedTerm τ :=
  subst ρ t

/-- Replace each free variable in a formula by its chosen closed representative. -/
abbrev closeFormula (ρ : RepresentativeAssignment Γ) (φ : Formula Γ) : Sentence :=
  closeTerm ρ φ

@[simp] theorem closeTerm_var
    (ρ : RepresentativeAssignment Γ) (v : Var Γ τ) :
    closeTerm ρ (.var v : Term Γ τ) = ρ v :=
  rfl

@[simp] theorem closeTerm_closed
    (ρ : RepresentativeAssignment ([] : Ctx Atom)) (t : ClosedTerm τ) :
    closeTerm ρ t = t := by
  unfold closeTerm
  calc
    subst ρ t =
      subst (Subst.id (Base := Atom) (Const := Primitive) (Γ := [])) t := by
        apply subst_ext
        intro τ v
        nomatch v
    _ = t := subst_id (Base := Atom) (Const := Primitive) t

@[simp] theorem closeFormula_closed
    (ρ : RepresentativeAssignment ([] : Ctx Atom)) (φ : Sentence) :
    closeFormula ρ φ = φ :=
  closeTerm_closed ρ φ

/-- If a bound variable is instantiated with a weakened closed representative
and the remaining free variables are then closed by `ρ`, the result is exactly
what one gets by closing the body using the extended representative
assignment. -/
@[simp] theorem closeTerm_instantiate_weakenCtx
    (ρ : RepresentativeAssignment Γ)
    (t : ClosedTerm σ) (u : Term (σ :: Γ) τ) :
    closeTerm ρ (instantiate (Base := Atom) (weakenCtx Γ t) u) =
      closeTerm (RepresentativeAssignment.extend ρ t) u := by
  have hcomp :
      (Subst.comp
        ρ
        (Subst.single
          (Base := Atom)
          (Const := Primitive)
          (weakenCtx Γ t)) :
        Subst Primitive (σ :: Γ) []) =
      (RepresentativeAssignment.extend ρ t :
        Subst Primitive (σ :: Γ) []) := by
    funext α
    funext v
    cases v with
    | vz =>
        change subst ρ (weakenCtx Γ t) = t
        exact RepresentativeAssignment.close_weakenCtx (ρ := ρ) (t := t)
    | vs v =>
        rfl
  simpa [closeTerm, instantiate, hcomp] using
    (subst_comp
      (Base := Atom)
      (Const := Primitive)
      (τs := ρ)
      (σs := Subst.single
        (Base := Atom)
        (Const := Primitive)
        (weakenCtx Γ t))
      (t := u))

/-- Paper-facing semantic representative lemma: denoting the closed replacement
of a term is the same as denoting the original term under the valuation induced
by the chosen representatives. -/
theorem denote_closeTerm
    (M : HenkinModel Atom Primitive)
    (ρ : RepresentativeAssignment Γ) (t : Term Γ τ) :
    HenkinModel.denote M (closeTerm ρ t)
      (RepresentativeAssignment.closedValuation M) =
      HenkinModel.denote M t (RepresentativeAssignment.toValuation M ρ) := by
  exact (denote_subst M ρ t (RepresentativeAssignment.closedValuation M))

/-- Formula version of `denote_closeTerm`, matching the p. 87 representative
assignment lemma at proposition type. -/
theorem denote_closeFormula
    (M : HenkinModel Atom Primitive)
    (ρ : RepresentativeAssignment Γ) (φ : Formula Γ) :
    (HenkinModel.denote M (closeFormula ρ φ)
      (RepresentativeAssignment.closedValuation M)).down ↔
      (HenkinModel.denote M φ
        (RepresentativeAssignment.toValuation M ρ)).down := by
  exact Iff.of_eq (congrArg ULift.down (denote_closeTerm M ρ φ))

/-- Instantiating a body after closing its outer free variables is the same as
closing the body under the extended representative assignment. -/
@[simp] theorem instantiate_subst_lift
    (ρ : RepresentativeAssignment Γ)
    (t : ClosedTerm σ) (u : Term (σ :: Γ) τ) :
    instantiate (Base := Atom) t
      (subst (Subst.lift (Base := Atom) (Const := Primitive) ρ) u) =
      closeTerm (RepresentativeAssignment.extend ρ t) u := by
  have hcomp :
      (Subst.comp
        (Subst.single (Base := Atom) (Const := Primitive) t)
        (Subst.lift (Base := Atom) (Const := Primitive) ρ) :
        Subst Primitive (σ :: Γ) []) =
      (RepresentativeAssignment.extend ρ t :
        Subst Primitive (σ :: Γ) []) := by
    funext α
    funext v
    cases v with
    | vz =>
        rfl
    | vs v =>
        change
          instantiate (Base := Atom) t
            (weaken (Base := Atom) (Const := Primitive) (Γ := []) (ρ v)) = ρ v
        exact
          (instantiate_weaken
            (Base := Atom)
            (Const := Primitive)
            (t := t)
            (u := ρ v))
  unfold instantiate closeTerm
  calc
    subst
        (Subst.single (Base := Atom) (Const := Primitive) t)
        (subst (Subst.lift (Base := Atom) (Const := Primitive) ρ) u) =
      subst
        (Subst.comp
          (Subst.single (Base := Atom) (Const := Primitive) t)
          (Subst.lift (Base := Atom) (Const := Primitive) ρ))
        u := by
          exact subst_comp
            (Base := Atom)
            (Const := Primitive)
            (τs := Subst.single (Base := Atom) (Const := Primitive) t)
            (σs := Subst.lift (Base := Atom) (Const := Primitive) ρ)
            (t := u)
    _ = subst (RepresentativeAssignment.extend ρ t) u := by
          rw [hcomp]

namespace ClassAssignment

/-- Extend a quotient-valued class assignment across one bound variable. -/
def extend (ν : ClassAssignment T Γ) (c : TermClass T σ) :
    ClassAssignment T (σ :: Γ)
  | _, .vz => c
  | _, .vs v => ν v

/-- Choose a concrete closed representative for a quotient class. -/
noncomputable def representative {T : ClosedTheorySet} {τ : HTy}
    (c : TermClass T τ) : ClosedTerm τ :=
  Quotient.out c

/-- The chosen representative lies in the requested quotient class. -/
@[simp] theorem classOf_representative
    {T : ClosedTheorySet} {τ : HTy} (c : TermClass T τ) :
    classOf (T := T) (representative c) = c :=
  Quotient.out_eq c

/-- Convert a quotient-valued class assignment into a representative assignment
by choosing one closed representative for each quotient class. -/
noncomputable def chooseRepresentatives (ν : ClassAssignment T Γ) :
    RepresentativeAssignment Γ :=
  fun v => representative (ν v)

/-- Choosing representatives commutes pointwise with binder extension. -/
@[simp] theorem chooseRepresentatives_extend
    (ν : ClassAssignment T Γ) (c : TermClass T σ) {τ : HTy}
    (v : Var (σ :: Γ) τ) :
    chooseRepresentatives (extend ν c) v =
      RepresentativeAssignment.extend
        (chooseRepresentatives ν) (representative c) v := by
  cases v with
  | vz =>
      rfl
  | vs v =>
      rfl

/-- The chosen representatives realize the original quotient-valued
assignment. -/
theorem chooseRepresentatives_realizes
    (ν : ClassAssignment T Γ) :
    RepresentativeAssignment.Realizes T (chooseRepresentatives ν) ν := by
  intro τ v
  simp [chooseRepresentatives]

/-- Converting the chosen representatives back to a class assignment recovers
the original quotient-valued assignment. -/
@[simp] theorem toClassAssignment_chooseRepresentatives
    (ν : ClassAssignment T Γ) {τ : HTy} (v : Var Γ τ) :
    RepresentativeAssignment.toClassAssignment T (chooseRepresentatives ν) v = ν v := by
  simp [RepresentativeAssignment.toClassAssignment, chooseRepresentatives]

/-- Closing a term using a quotient-valued assignment means closing it using the
chosen representatives of those quotient classes. -/
noncomputable def closeTerm (ν : ClassAssignment T Γ) (t : Term Γ τ) : ClosedTerm τ :=
  Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm (chooseRepresentatives ν) t

/-- Formula version of `ClassAssignment.closeTerm`. -/
noncomputable abbrev closeFormula (ν : ClassAssignment T Γ) (φ : Formula Γ) : Sentence :=
  closeTerm ν φ

@[simp] theorem closeTerm_var
    (ν : ClassAssignment T Γ) (v : Var Γ τ) :
    closeTerm ν (.var v : Term Γ τ) = representative (ν v) := by
  rfl

/-- The chosen-representative closing operation is realized by the original
class assignment. -/
theorem closeTerm_realizes
    (ν : ClassAssignment T Γ) :
    RepresentativeAssignment.Realizes T (chooseRepresentatives ν) ν :=
  chooseRepresentatives_realizes ν

/-- Quantifier-step version of `closeTerm`: extending a class assignment by a
quotient class is the same as instantiating with a chosen representative after
closing the outer free variables. -/
@[simp] theorem closeTerm_instantiate_representative
    (ν : ClassAssignment T Γ) (c : TermClass T σ) (u : Term (σ :: Γ) τ) :
    instantiate (Base := Atom) (representative c)
      (subst
        (Subst.lift (Base := Atom) (Const := Primitive)
          (chooseRepresentatives ν)) u) =
      closeTerm (extend ν c) u := by
  calc
    instantiate (Base := Atom) (representative c)
        (subst
          (Subst.lift (Base := Atom) (Const := Primitive)
            (chooseRepresentatives ν)) u) =
      Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm
        (RepresentativeAssignment.extend
          (chooseRepresentatives ν) (representative c)) u := by
            exact
              (instantiate_subst_lift
                (ρ := chooseRepresentatives ν)
                (t := representative c)
                (u := u))
    _ = closeTerm (extend ν c) u := by
          unfold ClassAssignment.closeTerm
          unfold Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm
          apply subst_ext
          intro τ v
          simp

end ClassAssignment

end Mettapedia.AutoBooks.Codex.Henkin1950
