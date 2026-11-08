import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAskLocality

/-!
# Rows as S-expressions, patterns, and matching through the first-order unifier

A program's rows are S-expressions (`Sx`): symbols and cells. A rule's take patterns, read patterns
and made terms are S-expressions with pattern variables (`Pat`). On the step, rows are first-order
terms of the signature `rows` (numerals, one binary cell, variables `(scope, name)`), and the
existing first-order unifier solves their equations (`FirstOrder.action rows`).

* `embed` carries a row into the step, `Pat.at n` copies a pattern into the activation scope `n`
  (fresh names, one scope per firing), and `decode` reads a term back.
* **Matching is the special case of two-way unification against an embedded row**
  (`match_at`): a solution that equates a scoped pattern with an embedded row determines the
  pattern's variables, as the instance the row is (`agree_of_apply`), and instantiating by those
  values embeds the instance (`apply_at`).
* `Bounded n t`: every variable of `t` belongs to a scope below `n`; embedded rows have none
  (`embed_bounded`) and a pattern copied at `n` only names scope `n` (`at_scope`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramRows

open Mettapedia.Logic.LP

/-- Rows: S-expressions of symbols and cells. -/
inductive Sx where
  | sym (k : ℕ)
  | cell (head tail : Sx)
  deriving DecidableEq, Inhabited

/-- Patterns: S-expressions with pattern variables. -/
inductive Pat where
  | var (x : ℕ)
  | sym (k : ℕ)
  | cell (head tail : Pat)
  deriving DecidableEq

namespace Pat

/-- The pattern variables, in order of occurrence. -/
def vars : Pat → List ℕ
  | var x => [x]
  | sym _ => []
  | cell a b => a.vars ++ b.vars

/-- The instance of a pattern under an assignment of rows to its variables. -/
def inst (θ : ℕ → Sx) : Pat → Sx
  | var x => θ x
  | sym k => .sym k
  | cell a b => .cell (a.inst θ) (b.inst θ)

theorem inst_congr {θ θ' : ℕ → Sx} (p : Pat) (agree : ∀ x ∈ p.vars, θ x = θ' x) :
    p.inst θ = p.inst θ' := by
  induction p with
  | var x => exact agree x (by simp [vars])
  | sym k => rfl
  | cell a b iha ihb =>
      simp only [inst]
      rw [iha fun x hx => agree x (by simp [vars, hx]), ihb fun x hx => agree x (by simp [vars, hx])]

/-- **An instance determines the pattern's variables.** -/
theorem inst_agree {θ θ' : ℕ → Sx} (p : Pat) (same : p.inst θ = p.inst θ') :
    ∀ x ∈ p.vars, θ x = θ' x := by
  induction p with
  | var x =>
      intro y hy
      simp only [vars, List.mem_singleton] at hy
      subst hy
      exact same
  | sym k => intro y hy; simp [vars] at hy
  | cell a b iha ihb =>
      simp only [inst, Sx.cell.injEq] at same
      intro y hy
      simp only [vars, List.mem_append] at hy
      rcases hy with hy | hy
      · exact iha same.1 y hy
      · exact ihb same.2 y hy

end Pat

/-! ## The runtime signature -/

/-- The step's term signature for rows: numerals, one binary cell, and variables
`(scope, name)`. -/
@[reducible] def rows : LPSignature where
  constants := ℕ
  vars := ℕ × ℕ
  relationSymbols := Empty
  relationArity := fun e => nomatch e
  functionSymbols := Unit
  functionArity := fun _ => 2

/-- The step's terms. -/
abbrev Tm := Term rows

/-- The binary node. -/
def node (a b : Tm) : Tm := .app () ![a, b]

theorem node_inj {a b c d : Tm} : node a b = node c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    simp only [node, Term.app.injEq, heq_eq_eq, true_and] at h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem node_ne_const {a b : Tm} {k : ℕ} : node a b ≠ .const k := by
  intro h
  cases h

theorem apply_node (σ : Subst rows) (a b : Tm) :
    σ.applyTerm (node a b) = node (σ.applyTerm a) (σ.applyTerm b) := by
  simp only [node, Subst.applyTerm_app]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem mem_freeVars_node {a b : Tm} {v : ℕ × ℕ} :
    v ∈ (node a b).freeVars ↔ v ∈ a.freeVars ∨ v ∈ b.freeVars := by
  rw [node, Term.mem_freeVars_app (σ := rows)]
  constructor
  · rintro ⟨i, hi⟩
    match i, hi with
    | ⟨0, _⟩, hi => exact Or.inl hi
    | ⟨1, _⟩, hi => exact Or.inr hi
  · rintro (hi | hi)
    · exact ⟨⟨0, Nat.zero_lt_two⟩, hi⟩
    · exact ⟨⟨1, Nat.one_lt_two⟩, hi⟩

/-- Rows as step terms. -/
def embed : Sx → Tm
  | .sym k => .const k
  | .cell a b => node (embed a) (embed b)

/-- Read a step term back as a row; variables read as the symbol `0`. -/
def decode : Tm → Sx
  | .var _ => .sym 0
  | .const k => .sym k
  | .app _ ts => .cell (decode (ts ⟨0, Nat.zero_lt_two⟩)) (decode (ts ⟨1, Nat.one_lt_two⟩))

theorem decode_embed : ∀ s : Sx, decode (embed s) = s
  | .sym _ => rfl
  | .cell a b => by
      change Sx.cell (decode (embed a)) (decode (embed b)) = Sx.cell a b
      rw [decode_embed a, decode_embed b]

theorem embed_injective : Function.Injective embed := fun s t same => by
  rw [← decode_embed s, ← decode_embed t, same]

/-- Embedded rows are fixed by every substitution. -/
theorem apply_embed (σ : Subst rows) : ∀ s : Sx, σ.applyTerm (embed s) = embed s
  | .sym _ => rfl
  | .cell a b => by
      rw [embed, apply_node, apply_embed σ a, apply_embed σ b]

/-- Copy a pattern into the activation scope `n`. -/
def Pat.at (n : ℕ) : Pat → Tm
  | .var x => .var (n, x)
  | .sym k => .const k
  | .cell a b => node (a.at n) (b.at n)

/-- **Instantiating the copied variables by embedded rows embeds the instance.** -/
theorem apply_at {σ : Subst rows} {n : ℕ} {θ : ℕ → Sx} (p : Pat)
    (values : ∀ x ∈ p.vars, σ (n, x) = embed (θ x)) :
    σ.applyTerm (p.at n) = embed (p.inst θ) := by
  induction p with
  | var x => exact values x (by simp [Pat.vars])
  | sym k => rfl
  | cell a b iha ihb =>
      rw [Pat.at, apply_node, iha fun x hx => values x (by simp [Pat.vars, hx]),
        ihb fun x hx => values x (by simp [Pat.vars, hx])]
      rfl

/-- **Matching is two-way unification against an embedded row**: a solution equating the copied
pattern with an embedded row reads, through `decode`, an assignment whose instance is that row, and
the solution gives each pattern variable the embedded value. -/
theorem match_at {σ : Subst rows} {n : ℕ} (p : Pat) {s : Sx}
    (solved : σ.applyTerm (p.at n) = embed s) :
    p.inst (fun x => decode (σ (n, x))) = s ∧ ∀ x ∈ p.vars, σ (n, x) = embed (decode (σ (n, x))) := by
  induction p generalizing s with
  | var x =>
      have value : σ (n, x) = embed s := solved
      refine ⟨by simp [Pat.inst, value, decode_embed], ?_⟩
      intro y hy
      simp only [Pat.vars, List.mem_singleton] at hy
      subst hy
      rw [value, decode_embed]
  | sym k =>
      cases s with
      | sym k' =>
          have : k = k' := by
            have h : (Term.const k : Tm) = Term.const k' := solved
            cases h
            rfl
          subst this
          exact ⟨rfl, fun x hx => by simp [Pat.vars] at hx⟩
      | cell a b => exact absurd solved.symm node_ne_const
  | cell a b iha ihb =>
      rw [Pat.at, apply_node] at solved
      cases s with
      | sym k => exact absurd solved node_ne_const
      | cell s₁ s₂ =>
          obtain ⟨one, two⟩ := node_inj.mp solved
          obtain ⟨inst₁, values₁⟩ := iha one
          obtain ⟨inst₂, values₂⟩ := ihb two
          refine ⟨by rw [Pat.inst, inst₁, inst₂], ?_⟩
          intro x hx
          simp only [Pat.vars, List.mem_append] at hx
          rcases hx with hx | hx
          · exact values₁ x hx
          · exact values₂ x hx

/-- **A solution matching a copied pattern to an instance gives each variable its value.** -/
theorem agree_of_apply {σ : Subst rows} {n : ℕ} {θ : ℕ → Sx} (p : Pat)
    (solved : σ.applyTerm (p.at n) = embed (p.inst θ)) : ∀ x ∈ p.vars, σ (n, x) = embed (θ x) := by
  obtain ⟨read, values⟩ := match_at p solved
  intro x hx
  rw [values x hx, Pat.inst_agree p read x hx]

/-! ## Scopes -/

/-- Every variable of the term belongs to a scope below `n`. -/
def Bounded (n : ℕ) (t : Tm) : Prop := ∀ v ∈ t.freeVars, v.1 < n

theorem embed_bounded (n : ℕ) : ∀ s : Sx, Bounded n (embed s)
  | .sym _ => fun v hv => by simp [embed, Term.freeVars] at hv
  | .cell a b => fun v hv => by
      rcases mem_freeVars_node.mp hv with hv | hv
      · exact embed_bounded n a v hv
      · exact embed_bounded n b v hv

/-- A pattern copied at `n` names only the scope `n`. -/
theorem at_scope (n : ℕ) : ∀ (p : Pat), ∀ v ∈ (p.at n).freeVars, v.1 = n
  | .var x => fun v hv => by
      rw [Pat.at, Term.mem_freeVars_var (σ := rows)] at hv
      rw [hv]
  | .sym _ => fun v hv => by simp [Pat.at, Term.freeVars] at hv
  | .cell a b => fun v hv => by
      rcases mem_freeVars_node.mp hv with hv | hv
      · exact at_scope n a v hv
      · exact at_scope n b v hv

theorem Bounded.mono {m n : ℕ} {t : Tm} (bounded : Bounded m t) (le : m ≤ n) : Bounded n t :=
  fun v hv => lt_of_lt_of_le (bounded v hv) le

theorem at_bounded (n : ℕ) (p : Pat) : Bounded (n + 1) (p.at n) := fun v hv => by
  rw [at_scope n p v hv]
  exact Nat.lt_succ_self n

/-- Substitutions agreeing below `n` agree on bounded terms. -/
theorem apply_bounded {σ τ : Subst rows} {n : ℕ} {t : Tm} (bounded : Bounded n t)
    (agree : ∀ v : ℕ × ℕ, v.1 < n → σ v = τ v) : σ.applyTerm t = τ.applyTerm t :=
  Subst.applyTerm_congr fun v hv => agree v (bounded v hv)

#print axioms Pat.inst_agree
#print axioms node_inj
#print axioms apply_node
#print axioms decode_embed
#print axioms embed_injective
#print axioms apply_embed
#print axioms apply_at
#print axioms match_at
#print axioms agree_of_apply
#print axioms at_scope
#print axioms apply_bounded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramRows
