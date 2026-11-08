import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalFibre
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelDerivation

/-!
# Controls for the rational-tree fibre

Over a signature with two constants, unary `f`, `g` and binary `arrow`, and variables `X = 0`,
`Y = 1`:

* **`X = f(X)` is solvable** over rational trees (`loop_solves`), by the infinite tree `f(f(f(…)))`
  (`loop`), and its solved form sends `X` there (`mgu_loop`).
* **Unique solutions of guarded systems**: `X = f(X)` with `Y = f(Y)` entails `X = Y`
  (`fixpoints_unique`).
* **Clash**: `f(X) = g(Y)` is refuted, and has no solution (`clash_refuted`).
* **Not reflecting in general**: `X = f(X)` has no finite solution (`finite_occurs`), its rational
  solved form is not finite (`loop_not_finite`, `occurs_not_reflected`).
* **Finite-tree refutations are not rational ones**: from no knowledge, the finite calculus derives
  that no occurrence labelled `X` matches `f(X)`, by the occurs check; the rational calculus does
  not derive it, and at `X := f(f(…))` it is false (`absence_not_transferred`).
* **Rational trees are for object terms, not types**: the simple-type inference problem of
  self-application `x x` is `A = A → B`. It has no finite solution, and it has a rational one
  (`selfApplication_typable_only_rationally`). Typing self-application types `(λx. x x)(λx. x x)`,
  which has no normal form, so normalization theorems for finite types do not transfer to rational
  types; the dependent fibre keeps its occurs check.
* **Sharing**: `arrow(a, a)` with `a` shared and with two copies of `a` are the same tree
  (`arrow_sharing_unobservable`): sharing is invisible for data trees.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls

open Mettapedia.Logic.LP
open Raw (node bot child)

/-- Two unary symbols and a binary one. -/
inductive Sym where
  | f
  | g
  | arrow
  deriving DecidableEq

def Sym.arity : Sym → ℕ
  | .f => 1
  | .g => 1
  | .arrow => 2

/-- The control signature: constants `true`, `false`; symbols `f`, `g`, `arrow`; variables numbers. -/
abbrev ctlSig : LPSignature where
  constants := Bool
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Sym
  functionArity := Sym.arity

abbrev X : Term ctlSig := .var (0 : ℕ)
abbrev Y : Term ctlSig := .var (1 : ℕ)

/-- `s(t)` for a unary symbol. -/
def un (s : Sym) (t : Term ctlSig) : Term ctlSig := .app s fun _ => t

/-- `a → b`. -/
def arrowT (a b : Term ctlSig) : Term ctlSig := .app Sym.arrow fun i => if i.val = 0 then a else b

/-- A finite term as a rational tree. -/
abbrev r (u : Term ctlSig) : RTree ctlSig := RTree.ofTerm u

/-- The one-node graph `x = s(x, …, x)`. -/
def loopGraph (s : Sym) : Raw.Graph ctlSig Unit where
  label _ := .fn s
  edge _ _ := ()

/-- **The infinite tree `s(s(s(…)))`.** -/
def loop (s : Sym) : RTree ctlSig :=
  ⟨(loopGraph s).unfold (), (loopGraph s).wf_unfold (), (loopGraph s).rational_unfold ()⟩

theorem loop_eq (s : Sym) : (loop s).1 = node (.fn s) fun _ => (loop s).1 :=
  (loopGraph s).unfold_eq ()

/-- A tree equal to `s` of itself is the loop. -/
theorem eq_loop {s : Sym} {a : Raw ctlSig} (fixed : a = node (.fn s) fun _ => a) : a = (loop s).1 :=
  (loopGraph s).solves_unique (a := fun _ => a) (fun _ => fixed) ()

theorem subst_ofTerm_app (θ : ctlSig.vars → Raw ctlSig) (s : Sym) (ts : Fin (Sym.arity s) → Term ctlSig) :
    Raw.subst θ (Raw.ofTerm (.app s ts)) =
      node (.fn s) fun i => if h : i < Sym.arity s then Raw.subst θ (Raw.ofTerm (ts ⟨i, h⟩)) else bot := by
  show Raw.subst θ (node (.fn s) fun i => if h : i < Sym.arity s then Raw.ofTerm (ts ⟨i, h⟩) else bot) = _
  rw [Raw.subst_node θ (Raw.rigid_fn s)]
  congr 1
  funext i
  split_ifs
  · rfl
  · exact Raw.subst_bot θ

/-- `δ(s(v))` is `s` over `δ(v)`. -/
theorem subst_un_var (δ : RSubst ctlSig) (s : Sym) (v : ℕ) :
    (RTree.subst δ (r (un s (.var v)))).1 = node (.fn s) fun _ => (δ v).1 := by
  show Raw.subst (fun w => (δ w).1) (Raw.ofTerm (.app s fun _ => .var v)) = _
  rw [subst_ofTerm_app]
  exact Raw.node_congr fun i inside => by
    rw [dif_pos (show i < Sym.arity s from inside)]
    exact Raw.subst_leaf (σ := ctlSig) _ v

/-- `δ(v)` is `δ v`. -/
theorem subst_r_var (δ : RSubst ctlSig) (v : ℕ) : RTree.subst δ (r (.var v)) = δ v :=
  RTree.subst_leaf δ v

/-! ## `X = f(X)` -/

/-- The store `X = f(X)`. -/
def loopStore : EquationStore (RTree ctlSig) := [(r X, r (un .f X))]

theorem loopStore_eq : loopStore = ofStore [(X, un .f X)] := rfl

/-- A solution of `v = s(v)` makes `δ v` the loop. -/
theorem eq_loop_of_solves {δ : RSubst ctlSig} {s : Sym} {v : ℕ}
    (solved : RTree.subst δ (r (.var v)) = RTree.subst δ (r (un s (.var v)))) : δ v = loop s := by
  have raw := congrArg Subtype.val solved
  rw [subst_r_var, subst_un_var] at raw
  exact RTree.ext (eq_loop raw)

/-- **`X = f(X)` is solvable over rational trees.** -/
theorem loop_solves : (rationalAction ctlSig).Models (fun _ => loop .f) loopStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show RTree.subst (fun _ => loop .f) (r X) = RTree.subst (fun _ => loop .f) (r (un .f X))
  refine RTree.ext ?_
  rw [subst_r_var, subst_un_var]
  exact loop_eq .f

/-- **The solved form of `X = f(X)` sends `X` to `f(f(f(…)))`.** -/
theorem mgu_loop : mgu loopStore 0 = loop .f := by
  have unrefuted : ¬ Refuted loopStore := (consistent_iff_not_refuted _).mp ⟨_, loop_solves⟩
  exact eq_loop_of_solves ((mgu_principal unrefuted).sound _ (List.mem_singleton_self _))

/-- **Unique solutions of guarded systems**: `X = f(X)` and `Y = f(Y)` entail `X = Y`. -/
theorem fixpoints_unique :
    (rationalAction ctlSig).Entails [(r X, r (un .f X)), (r Y, r (un .f Y))] fun δ => δ 0 = δ 1 := by
  intro δ solved
  exact (eq_loop_of_solves (solved _ (List.mem_cons_self ..))).trans
    (eq_loop_of_solves (solved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))).symm

/-- **A clash**: `f(X) = g(Y)` is refuted and has no solution. -/
theorem clash_refuted :
    Refuted [(r (un .f X), r (un .g Y))] ∧ ¬ (rationalAction ctlSig).Consistent [(r (un .f X), r (un .g Y))] := by
  have refuted : Refuted [(r (un .f X), r (un .g Y))] :=
    ⟨_, _, .fn .f, .fn .g, Raw.Joined.base (List.mem_singleton_self _), rfl, rfl, Raw.rigid_fn _,
      Raw.rigid_fn _, fun same => by cases same⟩
  exact ⟨refuted, refuted_inconsistent refuted⟩

/-! ## Not reflecting in general -/

/-- **The occurs check**: `X = f(X)` has no finite solution. -/
theorem finite_occurs : ¬ (FirstOrder.action ctlSig).Consistent [(X, un .f X)] := by
  rintro ⟨θ, solved⟩
  have cyclic : θ 0 = Term.app Sym.f fun _ => θ 0 := solved _ (List.mem_singleton_self _)
  have smaller : (θ 0).size < (θ 0).size := by
    have h := Term.size_subterm (f := Sym.f) (ts := fun _ => θ 0) ⟨0, by decide⟩
    rw [← cyclic] at h
    exact h
  exact lt_irrefl _ smaller

theorem raw_loop_not_finite {s : Sym} (pos : 0 < Sym.arity s) :
    ∀ u : Term ctlSig, Raw.ofTerm u ≠ (loop s).1 := by
  intro u
  induction u with
  | var v =>
    intro same
    have roots := congrFun same []
    simp [Raw.ofTerm, Raw.leaf, loop, Raw.Graph.unfold, Raw.Graph.unfoldAt, loopGraph] at roots
  | const c =>
    intro same
    have roots := congrFun same []
    simp [Raw.ofTerm, loop, Raw.Graph.unfold, Raw.Graph.unfoldAt, loopGraph] at roots
  | app s' ts ih =>
    intro same
    have roots := congrFun same []
    have heads : s' = s := by
      simpa [Raw.ofTerm, loop, Raw.Graph.unfold, Raw.Graph.unfoldAt, loopGraph] using roots
    subst heads
    have kids := congrArg (child 0) same
    rw [Raw.ofTerm_app_child ts ⟨0, pos⟩] at kids
    have loopChild : child 0 (loop s').1 = (loop s').1 := by
      show child 0 ((loopGraph s').unfold ()) = (loopGraph s').unfold ()
      rw [Raw.Graph.child_unfold, if_pos (show 0 < ((loopGraph s').label ()).arity from pos)]
    exact ih ⟨0, pos⟩ (kids.trans loopChild)

/-- **The infinite tree is not finite.** -/
theorem loop_not_finite {s : Sym} (pos : 0 < Sym.arity s) : ¬ IsFinite (loop s) := by
  rintro ⟨u, same⟩
  exact raw_loop_not_finite pos u (congrArg Subtype.val same)

/-- **Solvability is not reflected in general**: `X = f(X)` is solvable over rational trees, has no
finite solution, and its rational solved form is not finite. -/
theorem occurs_not_reflected :
    (rationalAction ctlSig).Consistent (ofStore [(X, un .f X)]) ∧
      ¬ (FirstOrder.action ctlSig).Consistent [(X, un .f X)] ∧
      ¬ IsFinite (mgu (ofStore [(X, un .f X)]) 0) := by
  refine ⟨⟨_, loop_solves⟩, finite_occurs, ?_⟩
  rw [← loopStore_eq, mgu_loop]
  exact loop_not_finite (by decide)

/-! ## Refutations do not transfer between the fibres -/

/-- Every occurrence is labelled `X`. -/
def labelX : ℕ → Term ctlSig := fun _ => X

/-- **Finite-tree refutations are not rational ones.** From no knowledge, the finite calculus
derives that no occurrence labelled `X` matches `f(X)`, by the occurs check. The rational calculus
does not derive it: at `X := f(f(…))` the occurrence matches. -/
theorem absence_not_transferred :
    AnnotatedRuns.CertainChecks.Derives (σ := ctlSig) [] labelX {0} (.absent (un .f X)) ∧
      ¬ RationalChecks.Derives (σ := ctlSig) [] (fun o => r (labelX o)) {0} (.absent (r (un .f X))) := by
  constructor
  · refine (AnnotatedRuns.CertainChecks.derives_iff_entails (σ := ctlSig) _ _ _ _).mpr
      ⟨⟨Subst.id ctlSig, fun _ member => by simp at member⟩, fun θ _ o _ same => ?_⟩
    have cyclic : (Term.app Sym.f fun _ => θ 0 : Term ctlSig) = θ 0 := same
    have smaller : (θ 0).size < (θ 0).size := by
      have h := Term.size_subterm (f := Sym.f) (ts := fun _ => θ 0) ⟨0, by decide⟩
      rw [cyclic] at h
      exact h
    exact lt_irrefl _ smaller
  · intro derivation
    obtain ⟨_, asked⟩ := (RationalChecks.derives_iff_entails _ _ _ _).mp derivation
    refine asked (fun _ => loop .f) (fun _ member => by simp at member) 0 (Finset.mem_singleton_self 0) ?_
    show RTree.subst (fun _ => loop .f) (r (un .f X)) = RTree.subst (fun _ => loop .f) (r X)
    refine RTree.ext ?_
    rw [subst_r_var, subst_un_var]
    exact (loop_eq .f).symm

/-! ## Rational trees are for object terms, not types -/

/-- **A cyclic type**: the simple-type inference problem of self-application `x x`, `A = A → B`, has no
finite solution and has a rational one. -/
theorem selfApplication_typable_only_rationally :
    ¬ (FirstOrder.action ctlSig).Consistent [(X, arrowT X Y)] ∧
      (rationalAction ctlSig).Consistent (ofStore [(X, arrowT X Y)]) := by
  constructor
  · rintro ⟨θ, solved⟩
    have cyclic : θ 0 = Term.app Sym.arrow fun i => θ.applyTerm (if i.val = 0 then X else Y) :=
      solved _ (List.mem_singleton_self _)
    have smaller : (θ 0).size < (θ 0).size := by
      have h := Term.size_subterm (f := Sym.arrow)
        (ts := fun i => θ.applyTerm (if i.val = 0 then X else Y)) ⟨0, by decide⟩
      rw [← cyclic] at h
      exact h
    exact lt_irrefl _ smaller
  · refine ⟨fun _ => loop .arrow, fun e member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    show RTree.subst (fun _ => loop .arrow) (r X) = RTree.subst (fun _ => loop .arrow) (r (arrowT X Y))
    rw [subst_r_var]
    refine RTree.ext ?_
    show (loop .arrow).1 = Raw.subst (fun _ => (loop .arrow).1) (Raw.ofTerm (arrowT X Y))
    rw [arrowT, subst_ofTerm_app]
    refine (loop_eq .arrow).trans (Raw.node_congr fun i inside => ?_)
    rw [dif_pos (show i < Sym.arity Sym.arrow from inside)]
    split_ifs
    · exact (Raw.subst_leaf (fun _ => (loop .arrow).1) (0 : ℕ)).symm
    · exact (Raw.subst_leaf (fun _ => (loop .arrow).1) (1 : ℕ)).symm

/-! ## Sharing -/

/-- **`arrow(a, a)` shared and copied are the same tree**, for a constant `a`. -/
theorem arrow_sharing_unobservable (c : Bool) :
    (Raw.sharedGraph (σ := ctlSig) Sym.arrow (.const c)).unfold 0 =
      (Raw.copiedGraph (σ := ctlSig) Sym.arrow (.const c)).unfold 0 :=
  Raw.sharing_unobservable _ _ rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Controls.loop_solves
#print axioms Rational.Controls.mgu_loop
#print axioms Rational.Controls.fixpoints_unique
#print axioms Rational.Controls.clash_refuted
#print axioms Rational.Controls.finite_occurs
#print axioms Rational.Controls.loop_not_finite
#print axioms Rational.Controls.occurs_not_reflected
#print axioms Rational.Controls.absence_not_transferred
#print axioms Rational.Controls.selfApplication_typable_only_rationally
#print axioms Rational.Controls.arrow_sharing_unobservable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
