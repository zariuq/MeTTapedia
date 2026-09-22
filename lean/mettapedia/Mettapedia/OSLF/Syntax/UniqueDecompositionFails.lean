import Mettapedia.OSLF.Syntax.Presentation

/-!
# Disjoint predicates do not determine a unique parallel split

Finding Mind's Proposition 18.1 asserts that when two scopes have disjoint
extensions and are separated at grade zero, every inhabitant of the extension of
their parallel composition decomposes uniquely up to structural congruence.
The example below disproves the weaker statement with the grading condition
omitted: disjoint equation-invariant predicates alone do not determine a unique
partition of a composite. Associativity and commutativity can repartition it.

The two predicates are genuine disjoint unions of congruence classes, defined
by output counts. One process splits two ways, and the same invariant separates
the left halves. There are no rewrite rules, so no reduction occurs. This does
not establish FM's separate grade-zero condition, which is defined by shared
free-name support. No theorem below discharges that condition for the scope
extensions; the full source Proposition 18.1 remains unsettled here.

An independent sufficient hypothesis is proved in UniqueDecompositionRepaired:
the three-output AC1 quotient is a free commutative monoid, and disjoint prime
support determines its split. Cancellation alone does not establish unique
factorization in an arbitrary commutative monoid.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

/-! ## The parallel fragment

One sort, parallel composition with a unit, and outputs on three channels, under
associativity, commutativity and the unit law.  It is the smallest setting in
which a composite has parands to repartition, and it is shared by everything
proved about composition, structure and observation in the modules that follow,
which is why it is named for what it is rather than for the first result proved
on it. -/

namespace ParallelFragment

/-- One sort: processes. -/
inductive PSrt where
  | proc
  deriving DecidableEq

/-- Outputs on three channels, parallel composition, and the unit.  There is no
input former, so no term of this language contains a communication redex. -/
inductive POp : PSrt → Type where
  | nul : POp PSrt.proc
  | par : POp PSrt.proc
  | out (n : Fin 3) : POp PSrt.proc

abbrev psig : Signature where
  Srt := PSrt
  Op := POp
  arity := fun {_} o => match o with
    | .nul => []
    | .par => [([], PSrt.proc), ([], PSrt.proc)]
    | .out _ => []

abbrev noMetas : List (MetaArity psig) := []

abbrev eqSig : Signature := withMetas psig noMetas

/-! ## The structural equations -/

/-- `P | Q = Q | P`. -/
def commAx : EqAxiom psig noMetas where
  ctx := [PSrt.proc, PSrt.proc]
  sort := PSrt.proc
  lhs := Term.op (S := eqSig) (Sum.inl POp.par)
    (.cons (Term.var Var.zero) (.cons (Term.var (Var.succ Var.zero)) .nil))
  rhs := Term.op (S := eqSig) (Sum.inl POp.par)
    (.cons (Term.var (Var.succ Var.zero)) (.cons (Term.var Var.zero) .nil))

/-- `(P | Q) | R = P | (Q | R)`. -/
def assocAx : EqAxiom psig noMetas where
  ctx := [PSrt.proc, PSrt.proc, PSrt.proc]
  sort := PSrt.proc
  lhs := Term.op (S := eqSig) (Sum.inl POp.par)
    (.cons (Term.op (S := eqSig) (Sum.inl POp.par)
        (.cons (Term.var Var.zero) (.cons (Term.var (Var.succ Var.zero)) .nil)))
      (.cons (Term.var (Var.succ (Var.succ Var.zero))) .nil))
  rhs := Term.op (S := eqSig) (Sum.inl POp.par)
    (.cons (Term.var Var.zero)
      (.cons (Term.op (S := eqSig) (Sum.inl POp.par)
        (.cons (Term.var (Var.succ Var.zero))
          (.cons (Term.var (Var.succ (Var.succ Var.zero))) .nil))) .nil))

/-- `P | 0 = P`. -/
def unitAx : EqAxiom psig noMetas where
  ctx := [PSrt.proc]
  sort := PSrt.proc
  lhs := Term.op (S := eqSig) (Sum.inl POp.par)
    (.cons (Term.var Var.zero)
      (.cons (Term.op (S := eqSig) (Sum.inl POp.nul) .nil) .nil))
  rhs := Term.var Var.zero

/-- Associativity, commutativity and unit: the structural congruence. -/
abbrev ac1 : List (EqAxiom psig noMetas) := [commAx, assocAx, unitAx]

/-- The presentation: these equations and **no rewrite rules**. -/
def acOnly : Presentation psig where
  metas := noMetas
  eqs := ac1
  rules := []

/-- With no rules there is no step. This says nothing about name-based grading. -/
theorem no_step {s : PSrt} (t u : Term psig [] s) : ¬ acOnly.Step t u :=
  Presentation.step_empty acOnly rfl t u

/-! ## An invariant of the structural equations -/

/-- The contribution of a single term former to the channel-`n` output count. -/
def headCount (n : Fin 3) {s : PSrt} (o : POp s) : Nat :=
  match o with
  | .out m => if n = m then 1 else 0
  | _ => 0

mutual
/-- How many outputs on channel `n` a process contains. -/
def countOut (n : Fin 3) : {Γ : Ctx psig} → {s : PSrt} → Term psig Γ s → Nat
  | _, _, .var _ => 0
  | _, _, .op o args => headCount n o + countOutArgs n args

def countOutArgs (n : Fin 3) : {as : List (List PSrt × PSrt)} → {Γ : Ctx psig} →
    Args psig as Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => countOut n head + countOutArgs n tail
end

def emptyBody : (k : Fin noMetas.length) →
    Term psig (noMetas.get k).1 (noMetas.get k).2 := fun k => k.elim0

/-- Each axiom moves parands around without creating or destroying an output. -/
theorem countOut_ax (n : Fin 3) : ∀ (i : Fin ac1.length) {Γ : Ctx psig}
    (body : (k : Fin noMetas.length) →
      Term psig (noMetas.get k).1 (noMetas.get k).2)
    (close : Sub psig (ac1.get i).ctx Γ),
    countOut n (bind close (instantiate body (ac1.get i).lhs))
      = countOut n (bind close (instantiate body (ac1.get i).rhs))
  | ⟨0, _⟩, _, body, close => by
      show countOut n (bind close (instantiate body commAx.lhs))
        = countOut n (bind close (instantiate body commAx.rhs))
      simp only [commAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        countOut, countOutArgs, headCount]
      omega
  | ⟨1, _⟩, _, body, close => by
      show countOut n (bind close (instantiate body assocAx.lhs))
        = countOut n (bind close (instantiate body assocAx.rhs))
      simp only [assocAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        countOut, countOutArgs, headCount]
      omega
  | ⟨2, _⟩, _, body, close => by
      show countOut n (bind close (instantiate body unitAx.lhs))
        = countOut n (bind close (instantiate body unitAx.rhs))
      simp only [unitAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        countOut, countOutArgs, headCount]
      omega
  | ⟨_ + 3, h⟩, _, _, _ => by simp [ac1] at h; omega

mutual
/-- **The count is a structural invariant.**  It therefore separates congruence
classes and not merely terms, which is what a counterexample to a statement
"unique up to structural congruence" has to do. -/
theorem countOut_invariant (n : Fin 3) : ∀ {Γ : Ctx psig} {s : PSrt}
    {t u : Term psig Γ s}, EqClosure ac1 t u → countOut n t = countOut n u
  | _, _, _, _, .ax i body close => countOut_ax n i body close
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (countOut_invariant n h).symm
  | _, _, _, _, .trans h h' => (countOut_invariant n h).trans (countOut_invariant n h')
  | _, _, _, _, .cong _ h => by
      simp only [countOut, countOutArgs_invariant n h]

theorem countOutArgs_invariant (n : Fin 3) : ∀ {as : List (List PSrt × PSrt)}
    {Γ : Ctx psig} {x y : Args psig as Γ},
    EqArgs ac1 x y → countOutArgs n x = countOutArgs n y
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons hh ht => by
      simp only [countOutArgs, countOut_invariant n hh, countOutArgs_invariant n ht]
end

/-! ## The witness -/

/-- An output on channel `n`. -/
def u (n : Fin 3) : Term psig [] PSrt.proc := Term.op (S := psig) (POp.out n) Args.nil

/-- Parallel composition. -/
def parT (a b : Term psig [] PSrt.proc) : Term psig [] PSrt.proc :=
  Term.op (S := psig) POp.par (.cons a (.cons b .nil))

/-- Processes with no channel-2 output and at least one output on channel 0 or
1.  Being defined by the invariant, this is a property of congruence classes. -/
def phi (t : Term psig [] PSrt.proc) : Prop :=
  countOut 2 t = 0 ∧ 0 < countOut 0 t + countOut 1 t

/-- Processes with exactly one channel-2 output.  Likewise a property of
congruence classes. -/
def psi (t : Term psig [] PSrt.proc) : Prop :=
  countOut 2 t = 1

/-- Both predicates are closed under the structural congruence, so each names a
set of classes and not an arbitrary set of terms. -/
theorem phi_congruent {t t' : Term psig [] PSrt.proc} (h : EqClosure ac1 t t')
    (ht : phi t) : phi t' := by
  refine ⟨?_, ?_⟩
  · rw [← countOut_invariant 2 h]; exact ht.1
  · rw [← countOut_invariant 0 h, ← countOut_invariant 1 h]; exact ht.2

theorem psi_congruent {t t' : Term psig [] PSrt.proc} (h : EqClosure ac1 t t')
    (ht : psi t) : psi t' := by
  rw [psi, ← countOut_invariant 2 h]; exact ht

/-- **The extensions are disjoint**: the proposition's first hypothesis. -/
theorem phi_psi_disjoint (t : Term psig [] PSrt.proc) : ¬ (phi t ∧ psi t) := by
  rintro ⟨⟨h0, -⟩, h1⟩
  have h1' : countOut 2 t = 1 := h1
  rw [h0] at h1'
  exact absurd h1' (by decide)

/-- Closing substitution witnessing the associativity instance. -/
def threeOuts : (s : PSrt) → Var [PSrt.proc, PSrt.proc, PSrt.proc] s → Term psig [] s
  | _, .zero => u 0
  | _, .succ .zero => u 1
  | _, .succ (.succ .zero) => u 2
  | _, .succ (.succ (.succ w)) => nomatch w

/-! ### Two splittings of one process -/

theorem split_left : phi (u 0) ∧ psi (parT (u 1) (u 2)) := by
  refine ⟨⟨by simp [u, countOut, countOutArgs, headCount],
    by simp [u, countOut, countOutArgs, headCount]⟩,
    by simp [psi, u, parT, countOut, countOutArgs, headCount]⟩

theorem split_right : phi (parT (u 0) (u 1)) ∧ psi (u 2) := by
  refine ⟨⟨by simp [parT, u, countOut, countOutArgs, headCount],
    by simp [parT, u, countOut, countOutArgs, headCount]⟩,
    by simp [psi, u, countOut, countOutArgs, headCount]⟩

/-- The two splittings recompose to structurally congruent processes. -/
theorem same_process :
    EqClosure ac1 (parT (parT (u 0) (u 1)) (u 2)) (parT (u 0) (parT (u 1) (u 2))) := by
  have h : EqClosure ac1 (bind threeOuts (instantiate emptyBody assocAx.lhs))
      (bind threeOuts (instantiate emptyBody assocAx.rhs)) :=
    EqClosure.ax (E := ac1) (Γ := ([] : Ctx psig)) ⟨1, by decide⟩ emptyBody threeOuts
  simpa only [assocAx, instantiate, instantiateArgs, bind, bindArgs, liftSub,
    threeOuts, parT] using h

/-- **The two left halves are not structurally congruent.** -/
theorem halves_differ : ¬ EqClosure ac1 (u 0) (parT (u 0) (u 1)) := by
  intro h
  have hc := countOut_invariant 1 h
  simp [u, parT, countOut, countOutArgs, headCount] at hc

/-- Disjoint class-closed predicates do not suffice for unique splitting.
The language has no steps, but the statement does not include the source's
separate name-based grade-zero hypothesis. -/
theorem unique_decomposition_fails :
    (∀ t, ¬ (phi t ∧ psi t))
      ∧ (∀ {s : PSrt} (t u : Term psig [] s), ¬ acOnly.Step t u)
      ∧ EqClosure ac1 (parT (parT (u 0) (u 1)) (u 2)) (parT (u 0) (parT (u 1) (u 2)))
      ∧ (phi (u 0) ∧ psi (parT (u 1) (u 2)))
      ∧ (phi (parT (u 0) (u 1)) ∧ psi (u 2))
      ∧ ¬ EqClosure ac1 (u 0) (parT (u 0) (u 1)) :=
  ⟨phi_psi_disjoint, fun t u => no_step t u, same_process, split_left, split_right,
    halves_differ⟩

/-! ### The invariant is not vacuous

A negative control: the count does distinguish terms, so `countOut_invariant`
is a real constraint on the congruence and not a constant function. -/

theorem countOut_separates : countOut 1 (u 1) ≠ countOut 1 (u 0) := by
  simp [u, countOut, countOutArgs, headCount]

end ParallelFragment

end Mettapedia.OSLF.Binding
