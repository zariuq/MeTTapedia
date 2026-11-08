import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionFiring

/-!
# Control: the empty clause from `{p(a), ¬p(x)}` on the shared step

The signature has the constants `⊤`, `a` and `nil`, the predicate symbol `p` (an atom `p(t)` is the
equation `p(t) ≈ ⊤`), and the clause formers `lit⁺`, `lit⁻` and `cons` (`code`). The ordering is the
strict subterm ordering (`order`), a stable ordering; the admission theorems need no more.

Two clauses are stored: `p(a) ≈ ⊤` at occurrence `0` and `p(x₀) ≉ ⊤` at occurrence `1`.

* **Binary resolution** (`resolve_admitted`): reading both, renamed apart (`x₀` opened as `x₁`), it
  tells `p(a) = p(x₁)` and makes `⊤ ≉ ⊤` at occurrence `2`. Its most general unifier is `x₁ ↦ a`
  (`mgu`), and the stored clause's own variable stays unbound (`stored_variable_free`).
* **Equality resolution** (`eqRes_admitted`): reading `⊤ ≉ ⊤`, it tells `⊤ = ⊤` and makes the empty
  clause at occurrence `3`.
* **The run** (`empty_clause_derived`): two firings of the guarded step derive the empty clause.
* **A side condition asked at every solution is too strong** (`notAbove_principal`,
  `notAbove_every_refused`, `notAbove_closure_admitted`): `x₁ ⋡ x₀` holds at the most general
  unifier of the empty problem and fails at the instance `x₁ ↦ p(x₀)`; its closure is admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition.ControlsFiring

open Mettapedia.Logic.LP
open Resolution (A)

/-- The predicate symbol and the clause formers. -/
inductive Fn where
  | p
  | lit (negative : Bool)
  | cons
  deriving DecidableEq

/-- The signature: constants `⊤ = 0`, `a = 1`, `nil = 2`. -/
abbrev nsig : LPSignature where
  constants := Fin 3
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Fn
  functionArity
    | .p => 1
    | .lit _ => 2
    | .cons => 2

def top : Term nsig := .const (0 : Fin 3)
def a : Term nsig := .const (1 : Fin 3)
def p (t : Term nsig) : Term nsig := .app Fn.p fun _ => t
def x (n : ℕ) : Term nsig := .var n

/-! ## The clause former -/

def encodeLit (L : NLit nsig) : Term nsig := .app (Fn.lit L.negative) ![L.lhs, L.rhs]

def encode : NClause nsig → Term nsig
  | [] => .const (2 : Fin 3)
  | L :: C => .app Fn.cons ![encodeLit L, encode C]

theorem encodeLit_subst (τ : Subst nsig) (L : NLit nsig) :
    τ.applyTerm (encodeLit L) = encodeLit (L.subst τ) := by
  show Term.app (Fn.lit L.negative) (fun i => τ.applyTerm (![L.lhs, L.rhs] i)) =
    Term.app (Fn.lit L.negative) ![τ.applyTerm L.lhs, τ.applyTerm L.rhs]
  congr 1
  funext i
  rcases i with ⟨_ | _ | n, h⟩
  · rfl
  · rfl
  · exact absurd h (by simp)

theorem encode_subst (τ : Subst nsig) : ∀ C : NClause nsig, τ.applyTerm (encode C) = encode (C.subst τ)
  | [] => rfl
  | L :: C => by
      show Term.app Fn.cons (fun i => τ.applyTerm (![encodeLit L, encode C] i)) =
        Term.app Fn.cons ![encodeLit (L.subst τ), encode (NClause.subst τ C)]
      congr 1
      funext i
      rcases i with ⟨_ | _ | n, h⟩
      · exact encodeLit_subst τ L
      · exact encode_subst τ C
      · exact absurd h (by simp)

/-- **The clause former.** -/
def code : ClauseCode nsig := ⟨encode, encode_subst⟩

/-! ## The strict subterm ordering -/

/-- The strict subterm relation. -/
inductive Below : Term nsig → Term nsig → Prop
  | arg (f : Fn) (args : Fin (nsig.functionArity f) → Term nsig) (i : Fin (nsig.functionArity f)) :
      Below (args i) (.app f args)
  | trans {s t u : Term nsig} : Below s t → Below t u → Below s u

theorem Below.subst (τ : Subst nsig) {s t : Term nsig} (below : Below s t) :
    Below (τ.applyTerm s) (τ.applyTerm t) := by
  induction below with
  | arg f args i => exact .arg f (fun j => τ.applyTerm (args j)) i
  | trans _ _ one two => exact .trans one two

theorem not_below_const {s : Term nsig} {c : Fin 3} : ¬ Below s (.const c) := by
  intro below
  generalize same : (Term.const c : Term nsig) = t at below
  induction below with
  | arg f args i => cases same
  | trans _ _ _ ih => exact ih same

/-- **The strict subterm ordering**, on terms and on the larger sides of literals: stable. -/
def order : StableOrder nsig where
  gt t s := Below s t
  gt_subst τ _ _ below := below.subst τ
  litGt L M := Below M.lhs L.lhs
  litGt_subst τ _ _ below := below.subst τ

theorem top_not_ge_pa : ¬ order.ge top (p a) := by
  rintro (below | same)
  · exact not_below_const below
  · cases same

/-! ## The stored clauses and the run -/

/-- `p(a) ≈ ⊤`. -/
def paClause : NClause nsig := [⟨false, p a, top⟩]
/-- `p(x₀) ≉ ⊤`. -/
def notPx : NClause nsig := [⟨true, p (x 0), top⟩]
/-- `⊤ ≉ ⊤`. -/
def topNeTop : NClause nsig := [⟨true, top, top⟩]

def label : ℕ → Term nsig
  | 0 => encode paClause
  | 1 => encode notPx
  | 2 => encode topNeTop
  | 3 => encode []
  | _ => encode []

def start : Configuration (Term nsig) ℕ := ⟨[], {0, 1}⟩

theorem start_principal : (A nsig).Principal start.equations (Subst.id nsig) :=
  ⟨(fun _ member => by cases member), fun δ _ => ⟨δ, fun t => by
    show δ.applyTerm t = (δ ∘ₛ Subst.id nsig).applyTerm t
    rw [Subst.comp_id_right]⟩⟩

/-- The most general unifier of `p(a)` and `p(x₁)`: `x₁ ↦ a`. -/
def mgu : Subst nsig := Subst.single 1 a

theorem mgu_principal : (A nsig).Principal [(p a, p (x 1))] mgu := by
  refine ⟨fun e member => ?_, fun δ solved => ⟨δ, fun t => ?_⟩⟩
  · rw [List.mem_singleton.mp member]
    rfl
  · have unifies : δ.applyTerm (p a) = δ.applyTerm (p (x 1)) := solved _ List.mem_cons_self
    have atOne : δ 1 = a := by
      have shapes : Term.app Fn.p (fun _ => a) = Term.app Fn.p (fun _ => δ 1) := unifies
      exact (congrFun (eq_of_heq (Term.app.inj shapes).2) 0).symm
    have same : δ ∘ₛ mgu = δ := by
      funext v
      by_cases one : v = 1
      · subst one
        show δ.applyTerm (mgu 1) = δ 1
        rw [mgu, Subst.single_eq (σ := nsig), atOne]
        rfl
      · show δ.applyTerm (mgu v) = δ v
        rw [mgu, Subst.single_ne (σ := nsig) _ one]
        rfl
    show δ.applyTerm t = (δ ∘ₛ mgu).applyTerm t
    rw [same]

theorem mgu_p_x1 : mgu.applyTerm (p (x 1)) = p a := by
  show Term.app Fn.p (fun _ => mgu 1) = Term.app Fn.p (fun _ => a)
  rw [mgu, Subst.single_eq (σ := nsig)]

/-- **Binary resolution**: read both clauses, the second renamed apart, tell `p(a) = p(x₁)`, make
`⊤ ≉ ⊤`. -/
def resolve : GuardedFiring (Term nsig) (Subst nsig) ℕ :=
  resolutionFiring order code top (0, label 0) (1, label 1) 2 (p a) (p (x 1)) [] []

theorem resolve_admitted : (guarded (A nsig) label).Admits (s := start) resolve := by
  refine (resolution_admits_iff order label code start_principal top ⟨rfl, rfl⟩
    ⟨Subst.applyTerm_id _, Subst.applyTerm_id _⟩ 2 [] []).mpr
    ⟨by decide, by decide, by decide, rfl, mgu, mgu_principal, ?_⟩
  refine ⟨(fun v same => by cases same), top_not_ge_pa, ?_, (fun M member => by cases member),
    (fun _ M member => by cases member), fun positive => absurd positive (by decide)⟩
  show ¬ order.ge (mgu.applyTerm top) (mgu.applyTerm (p (x 1)))
  rw [mgu_p_x1]
  exact top_not_ge_pa

/-- **The stored clause's variable stays unbound**: the told unification binds only the renamed copy. -/
theorem stored_variable_free : (mgu ∘ₛ Subst.id nsig) 0 = x 0 := rfl

def afterResolve : Configuration (Term nsig) ℕ := resolve.firing.result label start

theorem afterResolve_principal : (A nsig).Principal afterResolve.equations (mgu ∘ₛ Subst.id nsig) :=
  (unifyFiring_principal label start_principal (reads := [(0, label 0), (1, label 1)])
    (concl := code.encode (supConclusion .hole top [] ⟨true, p (x 1), top⟩ []))
    (G := supConditions order (p (x 1)) (p a) top [] ⟨true, p (x 1), top⟩ []) (by simp)
    ⟨Subst.applyTerm_id _, Subst.applyTerm_id _⟩ 2 (Subst.applyTerm_id _) mgu_principal).1

theorem id_principal : (A nsig).Principal [(top, top)] (Subst.id nsig) :=
  ⟨(fun e member => by rw [List.mem_singleton.mp member]; rfl), fun δ _ => ⟨δ, fun t => by
    show δ.applyTerm t = (δ ∘ₛ Subst.id nsig).applyTerm t
    rw [Subst.comp_id_right]⟩⟩

/-- **Equality resolution**: read `⊤ ≉ ⊤`, tell `⊤ = ⊤`, make the empty clause. -/
def eqRes : GuardedFiring (Term nsig) (Subst nsig) ℕ :=
  eqResFiring order code (2, label 2) 3 ⟨true, top, top⟩ []

theorem eqRes_admitted : (guarded (A nsig) label).Admits (s := afterResolve) eqRes :=
  (eqRes_admits_iff order label code afterResolve_principal rfl ⟨rfl, rfl⟩ 3 []).mpr
    ⟨by decide, by decide, rfl, Subst.id nsig, id_principal, rfl, (fun M member => by cases member)⟩

/-- **The empty clause is derived from `{p(a), ¬p(x)}`** by two firings of the guarded step. -/
theorem empty_clause_derived :
    ∃ r : (guarded (A nsig) label).Run start, 3 ∈ r.last.present ∧ label 3 = code.encode [] :=
  ⟨.cons resolve resolve_admitted (.cons eqRes eqRes_admitted (.nil _)), by decide, rfl⟩

/-! ## A side condition asked at every solution is too strong -/

theorem not_below_var {s : Term nsig} {v : ℕ} : ¬ Below s (.var v) := by
  intro below
  generalize same : (Term.var v : Term nsig) = t at below
  induction below with
  | arg f args i => cases same
  | trans _ _ _ ih => exact ih same

/-- The ordering side condition `x₁ ⋡ x₀`, at a solution. -/
def notAbove : Subst nsig → Prop := fun τ => ¬ order.geAt (x 1) (x 0) τ

/-- **It holds at the most general unifier of the empty problem.** -/
theorem notAbove_principal : notAbove (Subst.id nsig) := by
  rintro (below | same)
  · exact not_below_var below
  · cases same

/-- The instance `x₁ ↦ p(x₀)`. -/
def bump : Subst nsig := Subst.single 1 (p (x 0))

/-- **Asked at every solution, it is refused**: the instance `x₁ ↦ p(x₀)` puts `x₁` above `x₀`. -/
theorem notAbove_every_refused : ¬ (A nsig).Entails [] notAbove := by
  intro asked
  apply asked bump (fun _ member => by cases member)
  left
  show Below (bump.applyTerm (x 0)) (bump.applyTerm (x 1))
  rw [show bump.applyTerm (x 1) = p (x 0) from Subst.single_eq (σ := nsig) 1 _,
    show bump.applyTerm (x 0) = x 0 from Subst.single_ne (σ := nsig) (v := 1) (w := 0) (p (x 0)) (by decide)]
  exact .arg Fn.p (fun _ => x 0) 0

/-- **Its closure is admitted**: the step's guard for a side condition stated at the most general
unifier. -/
theorem notAbove_closure_admitted : (A nsig).Entails [] (Closure (A nsig) [] notAbove) :=
  (entails_closure_iff start_principal (respects_firstOrder _)
    (CoStable.not (order.geAt_stable (x 1) (x 0)))).mpr notAbove_principal

#print axioms encode_subst
#print axioms Below.subst
#print axioms top_not_ge_pa
#print axioms mgu_principal
#print axioms resolve_admitted
#print axioms stored_variable_free
#print axioms afterResolve_principal
#print axioms eqRes_admitted
#print axioms empty_clause_derived
#print axioms notAbove_principal
#print axioms notAbove_every_refused
#print axioms notAbove_closure_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition.ControlsFiring
