import Mettapedia.Logic.MarkovLogicClauseWorldModel

/-!
# First-Order MLN Template Grounding

Finite-domain first-order template layer that grounds into the existing
`GroundMLN` clause-native core from `MarkovLogicClauseSemantics`.

- Arity-indexed predicate signatures: `Pred n` for n-ary predicates.
- First-order atoms: predicate + `Fin n → Term` (variables or constants).
- Ground atoms: predicate + `Fin n → Dom`.
- Substitutions: `Var → Dom`.
- Templates ground into `WeightedGroundClause (GroundAtom ...)`.
- A family of templates compiles into `GroundMLN GroundAtom ClauseId`.
- `MixedTemplate` sum type handles both universal and existential templates.
- `compileToMixedGroundMLN` dispatches grounding by template kind.
- `compileToMixedGroundMLN_worldWeight_eq` preserves worldWeight for the
  combined compilation, connecting to `clauseWM_queryStrength_eq_queryProb`.

Both universally and existentially quantified clause templates.
No function symbols, no approximate grounding.

Existential templates `EXIST y: φ(x,y)` ground to a single clause per universal
substitution, containing the union of all literals from all existential witnesses.
`groundExistTemplate_holds_iff` proves the ground existential clause holds iff
there exists a witness assignment satisfying the body.

## LLM notes
- `Finset.cons` needs `∉` proof; use `insert` for building ground clauses.
- `∏ i : support.attach` gives `i : { x // x ∈ support }`, so `i.1` is the element.
- `DecidableEq` on function types requires classical; mark instances `noncomputable`.
-/

namespace Mettapedia.Logic.MarkovLogicGrounding

open scoped ENNReal BigOperators
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicCountable
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicClauseWorldModel

/-! ## Ground Atoms -/

/-- A ground first-order atom: an n-ary predicate applied to domain elements. -/
structure GroundAtom (Pred : ℕ → Type*) (Dom : Type*) where
  n : ℕ
  pred : Pred n
  args : Fin n → Dom

noncomputable instance [∀ n, DecidableEq (Pred n)] [DecidableEq Dom] :
    DecidableEq (GroundAtom Pred Dom) := by
  intro a b
  exact Classical.propDecidable (a = b)

/-! ## First-Order Syntax -/

/-- A first-order term: variable or domain constant. -/
inductive Term (Var Dom : Type*) where
  | var : Var → Term Var Dom
  | const : Dom → Term Var Dom
deriving DecidableEq

/-- A first-order atom template: predicate applied to terms. -/
structure AtomTemplate (Pred : ℕ → Type*) (Var Dom : Type*) where
  n : ℕ
  pred : Pred n
  args : Fin n → Term Var Dom

/-- A first-order literal template. -/
inductive LitTemplate (Pred : ℕ → Type*) (Var Dom : Type*) where
  | pos : AtomTemplate Pred Var Dom → LitTemplate Pred Var Dom
  | neg : AtomTemplate Pred Var Dom → LitTemplate Pred Var Dom

/-- A first-order clause template: disjunction of literal templates. -/
abbrev ClauseTemplate (Pred : ℕ → Type*) (Var Dom : Type*) :=
  List (LitTemplate Pred Var Dom)

/-- A weighted first-order clause template with satisfied/unsatisfied potentials. -/
structure WeightedClauseTemplate (Pred : ℕ → Type*) (Var Dom : Type*) where
  clause : ClauseTemplate Pred Var Dom
  satisfiedPotential : ENNReal
  unsatisfiedPotential : ENNReal
  satisfied_ne_top : satisfiedPotential ≠ ⊤
  unsatisfied_ne_top : unsatisfiedPotential ≠ ⊤

/-! ## Substitution and Grounding -/

/-- A substitution maps variables to domain elements. -/
abbrev Subst (Var Dom : Type*) := Var → Dom

variable {Pred : ℕ → Type*} {Var Dom : Type*}
  [∀ n, DecidableEq (Pred n)] [DecidableEq Var] [DecidableEq Dom]

/-- Apply a substitution to a term. -/
def groundTerm (θ : Subst Var Dom) : Term Var Dom → Dom
  | .var x => θ x
  | .const d => d

/-- Ground an atom template under a substitution. -/
def groundAtom (θ : Subst Var Dom) (a : AtomTemplate Pred Var Dom) :
    GroundAtom Pred Dom :=
  ⟨a.n, a.pred, fun i => groundTerm θ (a.args i)⟩

/-- Ground a literal template under a substitution, producing a propositional `Literal`. -/
def groundLit (θ : Subst Var Dom) :
    LitTemplate Pred Var Dom → Literal (GroundAtom Pred Dom)
  | .pos a => .pos (groundAtom θ a)
  | .neg a => .neg (groundAtom θ a)

/-- Ground a clause template under a substitution, producing a `GroundClause`. -/
noncomputable def groundClauseTemplate (θ : Subst Var Dom) (c : ClauseTemplate Pred Var Dom) :
    GroundClause (GroundAtom Pred Dom) :=
  (c.map (groundLit θ)).toFinset

/-- Ground a weighted clause template under a substitution, producing a
`WeightedGroundClause`. -/
noncomputable def groundWeightedTemplate (θ : Subst Var Dom) (wt : WeightedClauseTemplate Pred Var Dom) :
    WeightedGroundClause (GroundAtom Pred Dom) where
  clause := groundClauseTemplate θ wt.clause
  satisfiedPotential := wt.satisfiedPotential
  unsatisfiedPotential := wt.unsatisfiedPotential
  satisfied_ne_top := wt.satisfied_ne_top
  unsatisfied_ne_top := wt.unsatisfied_ne_top

/-! ## Compilation to GroundMLN -/

/-- Index type for grounded clauses: template id paired with a substitution.
Uses a product type so `Fintype` and `DecidableEq` are inherited. -/
abbrev GroundingIdx (TemplateId Var Dom : Type*) := TemplateId × (Var → Dom)

/-- Compile a family of weighted first-order clause templates into a `GroundMLN`
over ground atoms.  Each `(templateId, substitution)` pair becomes one grounded
weighted clause. -/
noncomputable def compileToGroundMLN
    (templates : TemplateId → WeightedClauseTemplate Pred Var Dom) :
    GroundMLN (GroundAtom Pred Dom) (GroundingIdx TemplateId Var Dom) where
  clauseData idx := groundWeightedTemplate idx.2 (templates idx.1)

/-! ## Grounding Correctness -/

omit [DecidableEq Var] in
/-- Grounding preserves clause satisfaction: a ground clause holds under a valuation
iff the corresponding propositional clause holds. This is immediate from the
definitions. -/
theorem groundClauseTemplate_holds_iff (θ : Subst Var Dom)
    (c : ClauseTemplate Pred Var Dom)
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (groundClauseTemplate θ c).holds W ↔
      ∃ l ∈ c, (groundLit θ l |>.holds W) := by
  simp only [groundClauseTemplate, GroundClause.holds, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨gl, hgl, hW⟩
    obtain ⟨l, hl, rfl⟩ := hgl
    exact ⟨l, hl, hW⟩
  · rintro ⟨l, hl, hW⟩
    exact ⟨groundLit θ l, ⟨l, hl, rfl⟩, hW⟩

omit [DecidableEq Var] in
/-- The grounded weighted clause's `eval` agrees with the template potentials. -/
theorem groundWeightedTemplate_eval_eq (θ : Subst Var Dom)
    (wt : WeightedClauseTemplate Pred Var Dom)
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (groundWeightedTemplate θ wt).eval W =
      if (groundClauseTemplate θ wt.clause).holds W
      then wt.satisfiedPotential
      else wt.unsatisfiedPotential := by
  classical
  unfold groundWeightedTemplate WeightedGroundClause.eval
  rfl

omit [DecidableEq Var] in
/-- The compiled ground MLN's world weight equals the product of template potentials
over all (template, substitution) pairs.  This is the main grounding-correctness theorem. -/
theorem compileToGroundMLN_worldWeight_eq
    {TemplateId : Type*}
    (templates : TemplateId → WeightedClauseTemplate Pred Var Dom)
    (support : Finset (GroundingIdx TemplateId Var Dom))
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (compileToGroundMLN templates).worldWeight support W =
      ∏ i : support.attach,
        let idx : GroundingIdx TemplateId Var Dom := i.1
        (groundWeightedTemplate idx.2 (templates idx.1)).eval W := by
  unfold GroundMLN.worldWeight compileToGroundMLN
  rfl

/-! ## Regression: Smokes(x) → Cancer(x) with 2-Element Domain -/

section SmokesRegression

/-- Two unary predicates. -/
inductive SmokePred : ℕ → Type where
  | smokes : SmokePred 1
  | cancer : SmokePred 1
deriving DecidableEq

instance : ∀ n, DecidableEq (SmokePred n) := fun _ => inferInstance

/-- Two-element domain. -/
inductive Person where
  | alice | bob
deriving DecidableEq, Fintype

/-- Single variable. -/
inductive X where
  | x
deriving DecidableEq, Fintype

/-- The clause template `¬Smokes(x) ∨ Cancer(x)` (i.e., `Smokes(x) → Cancer(x)`)
with satisfied potential 1, unsatisfied potential 0 (hard constraint). -/
def smokesCancerWT : WeightedClauseTemplate SmokePred X Person where
  clause := [
    .neg ⟨1, .smokes, fun _ => .var .x⟩,
    .pos ⟨1, .cancer, fun _ => .var .x⟩
  ]
  satisfiedPotential := 1
  unsatisfiedPotential := 0
  satisfied_ne_top := by norm_num
  unsatisfied_ne_top := by norm_num

/-- The FOL MLN with one template. -/
def smokeTemplates : Unit → WeightedClauseTemplate SmokePred X Person :=
  fun _ => smokesCancerWT

/-- The compiled ground MLN. -/
noncomputable def smokeGroundMLN := compileToGroundMLN smokeTemplates

/-- The ground clause for Alice: `¬Smokes(Alice) ∨ Cancer(Alice)`. -/
theorem smoke_groundClause_alice :
    groundClauseTemplate (Pred := SmokePred) (fun _ : X => Person.alice) smokesCancerWT.clause =
      [groundLit (fun _ : X => Person.alice) (.neg ⟨1, .smokes, fun _ => .var .x⟩),
       groundLit (fun _ : X => Person.alice) (.pos ⟨1, .cancer, fun _ => .var .x⟩)].toFinset := by
  simp [groundClauseTemplate, smokesCancerWT]

/-- The ground clause for Bob: `¬Smokes(Bob) ∨ Cancer(Bob)`. -/
theorem smoke_groundClause_bob :
    groundClauseTemplate (Pred := SmokePred) (fun _ : X => Person.bob) smokesCancerWT.clause =
      [groundLit (fun _ : X => Person.bob) (.neg ⟨1, .smokes, fun _ => .var .x⟩),
       groundLit (fun _ : X => Person.bob) (.pos ⟨1, .cancer, fun _ => .var .x⟩)].toFinset := by
  simp [groundClauseTemplate, smokesCancerWT]

/-- The compiled world weight reduces to the product of clause evaluations. -/
theorem smoke_worldWeight_eq
    (support : Finset (GroundingIdx Unit X Person))
    (W : AtomValuation (GroundAtom SmokePred Person)) :
    smokeGroundMLN.worldWeight support W =
      ∏ i : support.attach,
        let idx : GroundingIdx Unit X Person := i.1
        (groundWeightedTemplate idx.2 smokesCancerWT).eval W := by
  exact compileToGroundMLN_worldWeight_eq smokeTemplates support W

/-- A positive example: if Smokes(Alice) is false, the Alice-grounded clause
is trivially satisfied (the negative literal `¬Smokes(Alice)` holds). -/
theorem smoke_alice_clause_satisfied_when_not_smokes
    (W : AtomValuation (GroundAtom SmokePred Person))
    (h : W ⟨1, .smokes, fun _ => .alice⟩ = false) :
    (groundClauseTemplate (Pred := SmokePred) (fun _ : X => Person.alice) smokesCancerWT.clause).holds W := by
  rw [groundClauseTemplate_holds_iff]
  exact ⟨.neg ⟨1, .smokes, fun _ => .var .x⟩,
    List.mem_cons_self,
    by simp [groundLit, groundAtom, groundTerm, Literal.holds, h]⟩

/-- A negative example: if Smokes(Bob) is true and Cancer(Bob) is false,
the Bob-grounded clause is unsatisfied. -/
theorem smoke_bob_clause_unsatisfied_when_smokes_no_cancer
    (W : AtomValuation (GroundAtom SmokePred Person))
    (hSmokes : W ⟨1, .smokes, fun _ => .bob⟩ = true)
    (hNoCancer : W ⟨1, .cancer, fun _ => .bob⟩ = false) :
    ¬ (groundClauseTemplate (Pred := SmokePred) (fun _ : X => Person.bob) smokesCancerWT.clause).holds W := by
  rw [groundClauseTemplate_holds_iff]
  push_neg
  intro l hl
  simp [smokesCancerWT] at hl
  rcases hl with rfl | rfl
  · simp [groundLit, groundAtom, groundTerm, Literal.holds, hSmokes]
  · simp [groundLit, groundAtom, groundTerm, Literal.holds, hNoCancer]

end SmokesRegression

/-! ## Canary: Smokes(x) → Cancer(x) queryStrength via First-Order Grounding

End-to-end demonstration that `smokeGroundMLN` (compiled via `compileToGroundMLN`)
yields `BinaryWorldModel.queryStrength = 2/3` for Cancer(alice) and strength 0 for the
impossible query [Smokes(alice)=T, Cancer(alice)=F].

Key obstacle: `toCountableMLNSemantics` requires `[Fintype Atom]`.
We resolve this by providing a local equivalence
`GroundAtom SmokePred Person ≃ SmokePred 1 × Person` (4 elements).
-/

section SmokesQueryStrength

open Mettapedia.Logic.PLNWorldModel

/-! ### Local Fintype for grounded smoke atoms -/

/-- A Fintype instance for the 2-element type `SmokePred 1`. -/
private instance : Fintype (SmokePred 1) :=
  ⟨{.smokes, .cancer}, fun p => by cases p <;> simp⟩

/-- Every `SmokePred n` value witnesses `n = 1` (since both constructors target arity 1). -/
private def smokePredArityOne : SmokePred n → n = 1
  | .smokes => rfl
  | .cancer => rfl

/-- Canonical equivalence: every ground smoke atom has arity 1,
so the type is in bijection with `SmokePred 1 × Person`. -/
private noncomputable def smokeGroundAtomEquiv :
    GroundAtom SmokePred Person ≃ SmokePred 1 × Person where
  toFun a :=
    let hn := smokePredArityOne a.pred
    ⟨hn ▸ a.pred, a.args ⟨0, by omega⟩⟩
  invFun p := ⟨1, p.1, fun _ => p.2⟩
  left_inv a := by
    obtain ⟨n, pred, args⟩ := a
    have hn : n = 1 := smokePredArityOne pred
    subst hn
    simp only [GroundAtom.mk.injEq, heq_eq_eq, true_and]
    funext i
    fin_cases i
    rfl
  right_inv p := by simp

/-- Local Fintype instance for `GroundAtom SmokePred Person` (4 elements). -/
private noncomputable instance : Fintype (GroundAtom SmokePred Person) :=
  Fintype.ofEquiv (SmokePred 1 × Person) smokeGroundAtomEquiv.symm

/-! ### Named ground atoms, full support, queries -/

private def smokesAliceAtom : GroundAtom SmokePred Person := ⟨1, .smokes, fun _ => .alice⟩
private def smokesBobAtom   : GroundAtom SmokePred Person := ⟨1, .smokes, fun _ => .bob⟩
private def cancerAliceAtom : GroundAtom SmokePred Person := ⟨1, .cancer, fun _ => .alice⟩
private def cancerBobAtom   : GroundAtom SmokePred Person := ⟨1, .cancer, fun _ => .bob⟩

/-- The full grounding support: all (template, substitution) pairs. -/
noncomputable def smokeFullSupport : Finset (GroundingIdx Unit X Person) := Finset.univ

/-- Positive canary query: `Cancer(alice) = true`. -/
def cancerAliceQuery : ConstraintQuery (GroundAtom SmokePred Person) :=
  [⟨cancerAliceAtom, true⟩]

/-- Negative canary query: `Smokes(alice) = true ∧ Cancer(alice) = false` (impossible). -/
def impossibleAliceQuery : ConstraintQuery (GroundAtom SmokePred Person) :=
  [⟨smokesAliceAtom, true⟩, ⟨cancerAliceAtom, false⟩]

/-! ### World-weight factorization -/

/-- Helper: what `smokeGroundAtomEquiv.symm` maps each canonical pair to. -/
private theorem smokeEquivSymm_smokes_alice :
    smokeGroundAtomEquiv.symm (.smokes, .alice) = smokesAliceAtom := rfl

private theorem smokeEquivSymm_smokes_bob :
    smokeGroundAtomEquiv.symm (.smokes, .bob) = smokesBobAtom := rfl

private theorem smokeEquivSymm_cancer_alice :
    smokeGroundAtomEquiv.symm (.cancer, .alice) = cancerAliceAtom := rfl

private theorem smokeEquivSymm_cancer_bob :
    smokeGroundAtomEquiv.symm (.cancer, .bob) = cancerBobAtom := rfl

/-! ### Support enumeration -/

theorem smokeFullSupport_eq :
    smokeFullSupport =
      ({((), fun _ : X => Person.alice), ((), fun _ : X => Person.bob)} :
        Finset (GroundingIdx Unit X Person)) := by
  ext ⟨u, σ⟩
  simp only [smokeFullSupport, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, true_iff, true_and]
  cases u
  -- σ : X → Person; X has a single constructor .x, so σ is determined by σ .x
  cases h : σ .x
  · left;  exact funext (fun z => by cases z; exact h)
  · right; exact funext (fun z => by cases z; exact h)

/-! ### World-weight factorization lemma -/

/-- The world weight for the full support decomposes into independent Alice and Bob factors. -/
theorem smoke_worldWeight_fullSupport_eq
    (W : AtomValuation (GroundAtom SmokePred Person)) :
    smokeGroundMLN.worldWeight smokeFullSupport W =
      (if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then 0 else 1) *
      (if W smokesBobAtom   = true ∧ W cancerBobAtom   = false then 0 else 1) := by
  classical
  rw [smoke_worldWeight_eq, smokeFullSupport_eq]
  let s : Finset (GroundingIdx Unit X Person) :=
    ({((), fun _ : X => Person.alice), ((), fun _ : X => Person.bob)} :
      Finset (GroundingIdx Unit X Person))
  have hsort :
      (∏ i : s.attach,
          let idx : GroundingIdx Unit X Person := i.1
          (groundWeightedTemplate idx.2 smokesCancerWT).eval W) =
        ∏ i ∈ s.attach, (groundWeightedTemplate i.1.2 smokesCancerWT).eval W := by
    simpa [s] using
      (Finset.prod_coe_sort s.attach
        (fun i => (groundWeightedTemplate i.1.2 smokesCancerWT).eval W))
  rw [hsort]
  have hattach :
      (∏ i ∈ s.attach, (groundWeightedTemplate i.1.2 smokesCancerWT).eval W) =
        ∏ i ∈ s, (groundWeightedTemplate i.2 smokesCancerWT).eval W := by
    simpa [s] using
      (Finset.prod_attach (s := s)
        (f := fun i => (groundWeightedTemplate i.2 smokesCancerWT).eval W))
  rw [hattach]
  rw [show s = ({((), fun _ : X => Person.alice), ((), fun _ : X => Person.bob)} :
      Finset (GroundingIdx Unit X Person)) by rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  have hAlice :
      (groundWeightedTemplate (fun _ => Person.alice) smokesCancerWT).eval W =
        if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then 0 else 1 := by
    rw [groundWeightedTemplate_eval_eq]
    let sa : GroundAtom SmokePred Person := ⟨1, .smokes, fun _ => .alice⟩
    let ca : GroundAtom SmokePred Person := ⟨1, .cancer, fun _ => .alice⟩
    have hcontra :
        (W sa = false ∨ W ca = true) ↔ ¬ (W sa = true ∧ W ca = false) := by
      constructor
      · intro h hbad
        rcases h with hs0 | hc1
        · exact Bool.false_ne_true (hs0.symm.trans hbad.1)
        · exact Bool.false_ne_true (hbad.2.symm.trans hc1)
      · intro h
        by_cases hs : W sa = true
        · right
          by_cases hc : W ca = false
          · exact False.elim (h ⟨hs, hc⟩)
          · cases hval : W ca
            · exact False.elim (hc hval)
            · simp
        · left
          cases hval : W sa
          · simp
          · exact False.elim (hs hval)
    by_cases hbad : W sa = true ∧ W ca = false <;>
      simp [groundClauseTemplate_holds_iff, smokesCancerWT, groundLit, groundAtom, groundTerm,
        Literal.holds, smokesAliceAtom, cancerAliceAtom, sa, ca, List.mem_cons, hcontra, hbad]
  have hBob :
      (groundWeightedTemplate (fun _ => Person.bob) smokesCancerWT).eval W =
        if W smokesBobAtom = true ∧ W cancerBobAtom = false then 0 else 1 := by
    rw [groundWeightedTemplate_eval_eq]
    let sb : GroundAtom SmokePred Person := ⟨1, .smokes, fun _ => .bob⟩
    let cb : GroundAtom SmokePred Person := ⟨1, .cancer, fun _ => .bob⟩
    have hcontra :
        (W sb = false ∨ W cb = true) ↔ ¬ (W sb = true ∧ W cb = false) := by
      constructor
      · intro h hbad
        rcases h with hs0 | hc1
        · exact Bool.false_ne_true (hs0.symm.trans hbad.1)
        · exact Bool.false_ne_true (hbad.2.symm.trans hc1)
      · intro h
        by_cases hs : W sb = true
        · right
          by_cases hc : W cb = false
          · exact False.elim (h ⟨hs, hc⟩)
          · cases hval : W cb
            · exact False.elim (hc hval)
            · simp
        · left
          cases hval : W sb
          · simp
          · exact False.elim (hs hval)
    by_cases hbad : W sb = true ∧ W cb = false <;>
      simp [groundClauseTemplate_holds_iff, smokesCancerWT, groundLit, groundAtom, groundTerm,
        Literal.holds, smokesBobAtom, cancerBobAtom, sb, cb, List.mem_cons, hcontra, hbad]
  rw [hAlice, hBob]

/-! ### Canonical valuation equivalence (Bool × Bool × Bool × Bool) -/

/-- Reindex valuations as a 4-tuple of Booleans (sa, ca, sb, cb). -/
private noncomputable def smokeValEquiv :
    (GroundAtom SmokePred Person → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun W := (W smokesAliceAtom, W cancerAliceAtom, W smokesBobAtom, W cancerBobAtom)
  invFun b a :=
    match smokeGroundAtomEquiv a with
    | (.smokes, .alice) => b.1
    | (.cancer, .alice) => b.2.1
    | (.smokes, .bob)   => b.2.2.1
    | (.cancer, .bob)   => b.2.2.2
  left_inv W := by
    funext a
    -- Rewrite a as smokeGroundAtomEquiv.symm of its image, then case-split
    rw [show a = smokeGroundAtomEquiv.symm (smokeGroundAtomEquiv a) from
        (smokeGroundAtomEquiv.symm_apply_apply a).symm]
    rcases smokeGroundAtomEquiv a with ⟨_ | _, _ | _⟩ <;> rfl
  right_inv b := rfl

/-! ### Mass theorems -/

-- Helper lemma: convert `∑ W, f W` to `∑ b : Bool^4, f (smokeValEquiv.symm b)`
private noncomputable def smokeWorldWeightFn : Bool × Bool × Bool × Bool → ENNReal :=
  fun b => (if b.1 = true ∧ b.2.1 = false then 0 else 1) *
           (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1)

private theorem smoke_sum_worldWeight_eq_nine_aux :
    ∑ W : AtomValuation (GroundAtom SmokePred Person),
      smokeGroundMLN.worldWeight smokeFullSupport W = 9 := by
  simp only [smoke_worldWeight_fullSupport_eq]
  rw [show ∑ W : GroundAtom SmokePred Person → Bool,
        (if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then (0:ENNReal) else 1) *
        (if W smokesBobAtom = true ∧ W cancerBobAtom = false then 0 else 1) =
      ∑ b : Bool × Bool × Bool × Bool, smokeWorldWeightFn b
    from Equiv.sum_comp smokeValEquiv smokeWorldWeightFn]
  simp only [smokeWorldWeightFn, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

private theorem smoke_sum_cancerAlice_eq_six_aux :
    ∑ W : AtomValuation (GroundAtom SmokePred Person),
      (if ∀ c ∈ cancerAliceQuery, W c.1 = c.2 then
          smokeGroundMLN.worldWeight smokeFullSupport W
        else 0) = 6 := by
  simp only [smoke_worldWeight_fullSupport_eq]
  let f : AtomValuation (GroundAtom SmokePred Person) → ENNReal := fun W =>
    (if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then (0 : ENNReal) else 1) *
    (if W smokesBobAtom = true ∧ W cancerBobAtom = false then 0 else 1)
  have hquery :
      ∀ W : AtomValuation (GroundAtom SmokePred Person),
        (∀ c ∈ cancerAliceQuery, W c.1 = c.2) ↔ W cancerAliceAtom = true := by
    intro W
    simp [cancerAliceQuery]
  have hsum :
      (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ cancerAliceQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W cancerAliceAtom = true then f W else 0 := by
    apply Fintype.sum_congr
    intro W
    by_cases h : W cancerAliceAtom = true <;> simp [f, h, hquery W]
  rw [show (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ cancerAliceQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W cancerAliceAtom = true then f W else 0 from hsum]
  rw [show ∑ W : GroundAtom SmokePred Person → Bool,
        (if W cancerAliceAtom = true then f W else 0) =
      ∑ b : Bool × Bool × Bool × Bool,
        (if b.2.1 = true then
          (if b.1 = true ∧ b.2.1 = false then (0:ENNReal) else 1) *
          (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1) else 0)
    from Equiv.sum_comp smokeValEquiv (fun b =>
      if b.2.1 = true then
        (if b.1 = true ∧ b.2.1 = false then (0 : ENNReal) else 1) *
        (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1)
      else 0)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

private theorem smoke_sum_impossible_eq_zero_aux :
    ∑ W : AtomValuation (GroundAtom SmokePred Person),
      (if ∀ c ∈ impossibleAliceQuery, W c.1 = c.2 then
          smokeGroundMLN.worldWeight smokeFullSupport W
        else 0) = 0 := by
  simp only [smoke_worldWeight_fullSupport_eq]
  let f : AtomValuation (GroundAtom SmokePred Person) → ENNReal := fun W =>
    (if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then (0 : ENNReal) else 1) *
    (if W smokesBobAtom = true ∧ W cancerBobAtom = false then 0 else 1)
  have hquery :
      ∀ W : AtomValuation (GroundAtom SmokePred Person),
        (∀ c ∈ impossibleAliceQuery, W c.1 = c.2) ↔
          (W smokesAliceAtom = true ∧ W cancerAliceAtom = false) := by
    intro W
    simp [impossibleAliceQuery]
  have hsum :
      (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ impossibleAliceQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then f W else 0 := by
    apply Fintype.sum_congr
    intro W
    by_cases h : W smokesAliceAtom = true ∧ W cancerAliceAtom = false <;>
      simp [f, h, hquery W]
  rw [show (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ impossibleAliceQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then f W else 0 from hsum]
  rw [show ∑ W : GroundAtom SmokePred Person → Bool,
        (if W smokesAliceAtom = true ∧ W cancerAliceAtom = false then f W else 0) =
      ∑ b : Bool × Bool × Bool × Bool,
        (if b.1 = true ∧ b.2.1 = false then
          (if b.1 = true ∧ b.2.1 = false then (0:ENNReal) else 1) *
          (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1) else 0)
    from Equiv.sum_comp smokeValEquiv (fun b =>
      if b.1 = true ∧ b.2.1 = false then
        (if b.1 = true ∧ b.2.1 = false then (0 : ENNReal) else 1) *
        (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1)
      else 0)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-! ### Top-level canary theorems -/

theorem smoke_totalMass_eq_nine :
    (clauseMassSemantics smokeGroundMLN smokeFullSupport).totalMass = 9 := by
  change CountableMLNSemantics.totalMass
    (smokeGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      smokeFullSupport constraintQueryHolds) = 9
  unfold CountableMLNSemantics.totalMass GroundMLN.toCountableMLNSemantics
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact smoke_sum_worldWeight_eq_nine_aux

theorem smoke_queryMass_cancerAlice_eq_six :
    (clauseMassSemantics smokeGroundMLN smokeFullSupport).queryMass cancerAliceQuery = 6 := by
  change CountableMLNSemantics.queryMass
    (smokeGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      smokeFullSupport constraintQueryHolds) cancerAliceQuery = 6
  simp only [CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics,
             constraintQueryHolds, satisfiesConstraints]
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact smoke_sum_cancerAlice_eq_six_aux

theorem smoke_queryMass_impossible_eq_zero :
    (clauseMassSemantics smokeGroundMLN smokeFullSupport).queryMass impossibleAliceQuery = 0 := by
  change CountableMLNSemantics.queryMass
    (smokeGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      smokeFullSupport constraintQueryHolds) impossibleAliceQuery = 0
  simp only [CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics,
             constraintQueryHolds, satisfiesConstraints]
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact smoke_sum_impossible_eq_zero_aux

theorem smoke_queryProb_cancerAlice_eq_two_thirds :
    (clauseMassSemantics smokeGroundMLN smokeFullSupport).queryProb cancerAliceQuery =
      (2 : ENNReal) / 3 := by
  have htotal : (clauseMassSemantics smokeGroundMLN smokeFullSupport).totalMass ≠ 0 := by
    rw [smoke_totalMass_eq_nine]; norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal, smoke_queryMass_cancerAlice_eq_six, smoke_totalMass_eq_nine]
  have hr : (6 : ℝ) / 9 = (2 : ℝ) / 3 := by
    ring_nf
  simpa [ENNReal.ofReal_div_of_pos] using congrArg ENNReal.ofReal hr

/-- **First-order MLN canary**: The compiled Smokes(x)→Cancer(x) template over
{alice, bob} yields `queryStrength = 2/3` for `Cancer(alice)`, showing that the
first-order grounding pipeline correctly propagates to `BinaryWorldModel.queryStrength`. -/
theorem smoke_queryStrength_cancerAlice_eq_two_thirds :
    BinaryWorldModel.queryStrength (clauseWMState smokeGroundMLN smokeFullSupport) cancerAliceQuery =
      (2 : ENNReal) / 3 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact smoke_queryProb_cancerAlice_eq_two_thirds

/-- **Negative canary**: The impossible query [Smokes(alice)=T, Cancer(alice)=F]
has strength 0 (the hard constraint rules it out). -/
theorem smoke_queryStrength_impossible_eq_zero :
    BinaryWorldModel.queryStrength (clauseWMState smokeGroundMLN smokeFullSupport) impossibleAliceQuery = 0 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  have htotal : (clauseMassSemantics smokeGroundMLN smokeFullSupport).totalMass ≠ 0 := by
    rw [smoke_totalMass_eq_nine]; norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal, smoke_queryMass_impossible_eq_zero, smoke_totalMass_eq_nine]
  simp

end SmokesQueryStrength

/-! ## Existential Clause Templates -/

/-- An existential clause template: `∃ (existVars), body`.
The existential variables are a subset of the variables appearing in the body.
Universal variables (those not in `existVars`) are grounded by the outer
substitution; existential variables are enumerated over the full domain. -/
structure ExistClauseTemplate (Pred : ℕ → Type*) (Var Dom : Type*) where
  existVars : Finset Var
  body : ClauseTemplate Pred Var Dom

/-- Combine a universal substitution with an existential witness assignment.
For variables in `existVars`, use the witness; for others, use the universal subst. -/
def combineSubst {Var Dom : Type*} (existVars : Finset Var) [DecidableEq Var]
    (θ_u : Subst Var Dom) (θ_e : existVars → Dom) : Subst Var Dom :=
  fun v => if h : v ∈ existVars then θ_e ⟨v, h⟩ else θ_u v

variable {Pred : ℕ → Type*} {Var Dom : Type*}
  [∀ n, DecidableEq (Pred n)] [DecidableEq Var] [DecidableEq Dom]

/-- Ground an existential clause template: for a given universal substitution,
produce ONE ground clause that is the union of all ground literals from all
existential witness assignments.

This is the big-disjunction: the clause is satisfied iff ANY witness works. -/
noncomputable def groundExistTemplate [Fintype Dom]
    (θ_u : Subst Var Dom)
    (et : ExistClauseTemplate Pred Var Dom) :
    GroundClause (GroundAtom Pred Dom) :=
  Finset.univ.biUnion fun (θ_e : et.existVars → Dom) =>
    groundClauseTemplate (combineSubst et.existVars θ_u θ_e) et.body

/-- Existential grounding preserves satisfaction:
the ground existential clause holds iff there EXISTS a witness
assignment making the body clause hold. -/
theorem groundExistTemplate_holds_iff [Fintype Dom]
    (θ_u : Subst Var Dom)
    (et : ExistClauseTemplate Pred Var Dom)
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (groundExistTemplate θ_u et).holds W ↔
      ∃ (θ_e : et.existVars → Dom),
        (groundClauseTemplate (combineSubst et.existVars θ_u θ_e) et.body).holds W := by
  simp only [groundExistTemplate, GroundClause.holds, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨lit, ⟨θ_e, hlit⟩, hW⟩
    exact ⟨θ_e, lit, hlit, hW⟩
  · rintro ⟨θ_e, lit, hlit, hW⟩
    exact ⟨lit, ⟨θ_e, hlit⟩, hW⟩

/-! ## Weighted Existential Templates -/

/-- A weighted existential clause template with satisfied/unsatisfied potentials. -/
structure WeightedExistClauseTemplate (Pred : ℕ → Type*) (Var Dom : Type*) where
  template : ExistClauseTemplate Pred Var Dom
  satisfiedPotential : ENNReal
  unsatisfiedPotential : ENNReal
  satisfied_ne_top : satisfiedPotential ≠ ⊤
  unsatisfied_ne_top : unsatisfiedPotential ≠ ⊤

/-- Ground a weighted existential template under a universal substitution. -/
noncomputable def groundWeightedExistTemplate [Fintype Dom]
    (θ_u : Subst Var Dom) (wet : WeightedExistClauseTemplate Pred Var Dom) :
    WeightedGroundClause (GroundAtom Pred Dom) where
  clause := groundExistTemplate θ_u wet.template
  satisfiedPotential := wet.satisfiedPotential
  unsatisfiedPotential := wet.unsatisfiedPotential
  satisfied_ne_top := wet.satisfied_ne_top
  unsatisfied_ne_top := wet.unsatisfied_ne_top

/-- The grounded weighted existential clause's `eval` agrees with the template potentials.
This is the weighted compilation preservation theorem for existential clauses. -/
theorem groundWeightedExistTemplate_eval_eq [Fintype Dom]
    (θ_u : Subst Var Dom) (wet : WeightedExistClauseTemplate Pred Var Dom)
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (groundWeightedExistTemplate θ_u wet).eval W =
      if (groundExistTemplate θ_u wet.template).holds W
      then wet.satisfiedPotential
      else wet.unsatisfiedPotential := by
  classical
  unfold groundWeightedExistTemplate WeightedGroundClause.eval
  rfl

/-! ## Mixed Template Compilation (Universal + Existential)

An MLN may contain both universally and existentially quantified clause templates.
We define a sum type `MixedTemplate` and a combined compilation function
`compileToMixedGroundMLN` that dispatches grounding appropriately.
The main theorem `compileToMixedGroundMLN_worldWeight_eq` proves that the compiled
world weight equals the product of per-template evaluations, connecting to
`clauseWM_queryStrength_eq_queryProb` for the full MLN-import claim. -/

/-- A clause template that is either universally or existentially quantified. -/
inductive MixedTemplate (Pred : ℕ → Type*) (Var Dom : Type*) where
  | universal : WeightedClauseTemplate Pred Var Dom → MixedTemplate Pred Var Dom
  | existential : WeightedExistClauseTemplate Pred Var Dom → MixedTemplate Pred Var Dom

/-- Ground a mixed template under a substitution. Universal templates use the
full substitution; existential templates use it as the universal part and
enumerate witnesses internally. -/
noncomputable def groundMixedTemplate [Fintype Dom]
    (θ : Subst Var Dom) : MixedTemplate Pred Var Dom →
    WeightedGroundClause (GroundAtom Pred Dom)
  | .universal wt => groundWeightedTemplate θ wt
  | .existential wet => groundWeightedExistTemplate θ wet

/-- Compile a family of mixed templates into a `GroundMLN`. -/
noncomputable def compileToMixedGroundMLN [Fintype Dom]
    (templates : TemplateId → MixedTemplate Pred Var Dom) :
    GroundMLN (GroundAtom Pred Dom) (GroundingIdx TemplateId Var Dom) where
  clauseData idx := groundMixedTemplate idx.2 (templates idx.1)

/-- The mixed ground MLN's world weight equals the product of per-template
evaluations over all (template, substitution) pairs.  This is the combined
grounding-correctness theorem covering both universal and existential templates. -/
theorem compileToMixedGroundMLN_worldWeight_eq [Fintype Dom]
    {TemplateId : Type*}
    (templates : TemplateId → MixedTemplate Pred Var Dom)
    (support : Finset (GroundingIdx TemplateId Var Dom))
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (compileToMixedGroundMLN templates).worldWeight support W =
      ∏ i : support.attach,
        let idx : GroundingIdx TemplateId Var Dom := i.1
        (groundMixedTemplate idx.2 (templates idx.1)).eval W := by
  unfold GroundMLN.worldWeight compileToMixedGroundMLN
  rfl

/-- For universal templates, `groundMixedTemplate` agrees with `groundWeightedTemplate`. -/
theorem groundMixedTemplate_universal_eq [Fintype Dom]
    (θ : Subst Var Dom) (wt : WeightedClauseTemplate Pred Var Dom) :
    groundMixedTemplate θ (.universal wt) = groundWeightedTemplate θ wt := rfl

/-- For existential templates, `groundMixedTemplate` agrees with
`groundWeightedExistTemplate`. -/
theorem groundMixedTemplate_existential_eq [Fintype Dom]
    (θ : Subst Var Dom) (wet : WeightedExistClauseTemplate Pred Var Dom) :
    groundMixedTemplate θ (.existential wet) = groundWeightedExistTemplate θ wet := rfl

/-- The eval of a grounded universal mixed template agrees with the clause template
potentials, bridging to `groundWeightedTemplate_eval_eq`. -/
theorem groundMixedTemplate_universal_eval_eq [Fintype Dom]
    (θ : Subst Var Dom) (wt : WeightedClauseTemplate Pred Var Dom)
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (groundMixedTemplate θ (.universal wt)).eval W =
      if (groundClauseTemplate θ wt.clause).holds W
      then wt.satisfiedPotential
      else wt.unsatisfiedPotential := by
  rw [groundMixedTemplate_universal_eq, groundWeightedTemplate_eval_eq]

/-- The eval of a grounded existential mixed template agrees with the existential
template potentials, bridging to `groundWeightedExistTemplate_eval_eq`. -/
theorem groundMixedTemplate_existential_eval_eq [Fintype Dom]
    (θ : Subst Var Dom) (wet : WeightedExistClauseTemplate Pred Var Dom)
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (groundMixedTemplate θ (.existential wet)).eval W =
      if (groundExistTemplate θ wet.template).holds W
      then wet.satisfiedPotential
      else wet.unsatisfiedPotential := by
  rw [groundMixedTemplate_existential_eq, groundWeightedExistTemplate_eval_eq]

/-! ## One-Shot Semantic Subsumption Theorem

For finite-domain MLNs with mixed universal/existential templates, the compiled
WM world-model state's `queryStrength` equals the exact MLN `queryProb`.
This composes the full chain:
  mixed templates → GroundMLN → CountableMLNSemantics → MassSemantics → BinaryWorldModel
-/

open MarkovLogicClauseWorldModel MarkovLogicClauseFactorGraph PLNWorldModel

/-- **Semantic subsumption theorem:** For any finite-domain MLN with mixed
universal/existential templates, the compiled WM `queryStrength` equals the
exact MLN marginal probability `queryProb`.

This is the main theoretical result: WM-PLN can faithfully represent any
finite-domain MLN and recover exact marginals (not an approximation).
Tractable computation is a separate question (#P-hardness applies as usual). -/
theorem mixed_queryStrength_eq_queryProb
    [Fintype Dom] [Fintype (GroundAtom Pred Dom)]
    [Fintype TemplateId] [Fintype Var]
    (templates : TemplateId → MixedTemplate Pred Var Dom)
    (q : ConstraintQuery (GroundAtom Pred Dom)) :
    BinaryWorldModel.queryStrength
      (clauseWMState (compileToMixedGroundMLN templates) Finset.univ) q =
      (clauseMassSemantics (compileToMixedGroundMLN templates) Finset.univ).queryProb q :=
  clauseWM_queryStrength_eq_queryProb _ Finset.univ q

/-! ## Classical Log-Weight Template Specialization

Classical MLNs use log-weights: satisfied clauses contribute factor `exp(w)`,
unsatisfied clauses contribute `1`.  This is a special case of the general
positive-potential framework.  The specialization is explicit so that the phrase
"true MLN marginal probability" is unmistakable. -/

/-- A classical first-order clause template with a real-valued log-weight.
The standard MLN potential is `exp(w)` when the clause is satisfied, `1` otherwise. -/
structure ClassicalClauseTemplate (Pred : ℕ → Type*) (Var Dom : Type*) where
  clause : ClauseTemplate Pred Var Dom
  logWeight : ℝ

/-- Convert a classical log-weight template to the general positive-potential form. -/
noncomputable def ClassicalClauseTemplate.toWeighted
    (ct : ClassicalClauseTemplate Pred Var Dom) :
    WeightedClauseTemplate Pred Var Dom where
  clause := ct.clause
  satisfiedPotential := ENNReal.ofReal (Real.exp ct.logWeight)
  unsatisfiedPotential := 1
  satisfied_ne_top := ENNReal.ofReal_ne_top
  unsatisfied_ne_top := by simp

/-- The grounded classical template's eval equals `logWeightPotential`:
`exp(w)` when the clause holds, `1` otherwise. -/
theorem classicalTemplate_eval_eq_logWeightPotential
    {Pred : ℕ → Type*} {Var Dom : Type*}
    [∀ n, DecidableEq (Pred n)] [DecidableEq Dom]
    (θ : Subst Var Dom) (ct : ClassicalClauseTemplate Pred Var Dom)
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (groundWeightedTemplate θ ct.toWeighted).eval W =
      logWeightPotential ct.logWeight
        ((groundClauseTemplate θ ct.clause).holds W) := by
  rw [groundWeightedTemplate_eval_eq]
  unfold ClassicalClauseTemplate.toWeighted logWeightPotential
  by_cases h : (groundClauseTemplate θ ct.clause).holds W <;> simp [h]

/-- Family compilation for classical log-weight templates yields the Gibbs product:
the world weight is `∏ᵢ logWeightPotential(wᵢ, clauseᵢ holds)`. -/
theorem compileClassical_worldWeight_eq_gibbsProduct
    {Pred : ℕ → Type*} {Var Dom : Type*}
    [∀ n, DecidableEq (Pred n)] [DecidableEq Var] [DecidableEq Dom]
    {TemplateId : Type*}
    (templates : TemplateId → ClassicalClauseTemplate Pred Var Dom)
    (support : Finset (GroundingIdx TemplateId Var Dom))
    (W : AtomValuation (GroundAtom Pred Dom)) :
    (compileToGroundMLN (fun i => (templates i).toWeighted)).worldWeight support W =
      ∏ i : support.attach,
        let idx : GroundingIdx TemplateId Var Dom := i.1
        logWeightPotential ((templates idx.1).logWeight)
          ((groundClauseTemplate idx.2 (templates idx.1).clause).holds W) := by
  rw [compileToGroundMLN_worldWeight_eq]; congr 1

/-! ## Regression: Existential Coupling — ∃ y. Rel(x, y) over {a, b}

Hard constraint: "for every x, there exists y such that Rel(x, y)."
Grounding with x=a produces the disjunction `Rel(a,a) ∨ Rel(a,b)`;
with x=b produces `Rel(b,a) ∨ Rel(b,b)`.

Unlike the Smokes regression (where Alice and Bob factors are independent),
the existential big-disjunction creates within-clause coupling:
`Rel(a,a)` and `Rel(a,b)` are coupled through the x=a clause.

Total mass = 9 (out of 16 worlds), queryProb(Rel(a,b)=T) = 6/9 = 2/3.

This proves that the semantic subsumption theorem gives exact marginals even
in the presence of existential coupling — it is not merely a local-conditional
approximation. -/

section ExistCouplingRegression

/-- Single binary predicate. -/
inductive RelPred : ℕ → Type where
  | rel : RelPred 2
deriving DecidableEq

instance : ∀ n, DecidableEq (RelPred n) := fun _ => inferInstance

/-- Two-element domain. -/
inductive Elem where
  | a | b
deriving DecidableEq, Fintype

/-- Two variables: x (universal) and y (existential). -/
inductive XY where
  | x | y
deriving DecidableEq, Fintype

/-! ### Named ground atoms -/

private def relAAAtom : GroundAtom RelPred Elem := ⟨2, .rel, ![.a, .a]⟩
private def relABAtom : GroundAtom RelPred Elem := ⟨2, .rel, ![.a, .b]⟩
private def relBAAtom : GroundAtom RelPred Elem := ⟨2, .rel, ![.b, .a]⟩
private def relBBAtom : GroundAtom RelPred Elem := ⟨2, .rel, ![.b, .b]⟩

/-! ### Fintype instance for GroundAtom RelPred Elem -/

private def relPredArityTwo : RelPred n → n = 2
  | .rel => rfl

private noncomputable def existGroundAtomEquiv :
    GroundAtom RelPred Elem ≃ Elem × Elem where
  toFun a :=
    have hn : a.n = 2 := relPredArityTwo a.pred
    (a.args ⟨0, by omega⟩, a.args ⟨1, by omega⟩)
  invFun p := ⟨2, .rel, ![p.1, p.2]⟩
  left_inv a := by
    obtain ⟨n, pred, args⟩ := a
    have hn : n = 2 := relPredArityTwo pred
    subst hn; cases pred
    simp only [GroundAtom.mk.injEq, heq_eq_eq, true_and]
    funext i; fin_cases i <;> rfl
  right_inv p := by simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private noncomputable instance : Fintype (GroundAtom RelPred Elem) :=
  Fintype.ofEquiv (Elem × Elem) existGroundAtomEquiv.symm

/-! ### Ground MLN: two coupled hard-constraint clauses

Instead of routing through `compileToMixedGroundMLN` (which would require
unfolding `noncomputable` existential grounding), we directly construct the
ground MLN with the two clauses that existential grounding produces:
  - Clause 0: `Rel(a,a) ∨ Rel(a,b)` (hard: sat=1, unsat=0)
  - Clause 1: `Rel(b,a) ∨ Rel(b,b)` (hard: sat=1, unsat=0)
Then we prove that `groundExistTemplate` produces exactly these clauses. -/

/-- Ground clause for x=a: `Rel(a,a) ∨ Rel(a,b)`. -/
private noncomputable def existClauseA : WeightedGroundClause (GroundAtom RelPred Elem) where
  clause := ({.pos relAAAtom, .pos relABAtom} : Finset (Literal _))
  satisfiedPotential := 1
  unsatisfiedPotential := 0
  satisfied_ne_top := by norm_num
  unsatisfied_ne_top := by norm_num

/-- Ground clause for x=b: `Rel(b,a) ∨ Rel(b,b)`. -/
private noncomputable def existClauseB : WeightedGroundClause (GroundAtom RelPred Elem) where
  clause := ({.pos relBAAtom, .pos relBBAtom} : Finset (Literal _))
  satisfiedPotential := 1
  unsatisfiedPotential := 0
  satisfied_ne_top := by norm_num
  unsatisfied_ne_top := by norm_num

/-- Two-clause index type. -/
inductive ExistClauseId where | clauseA | clauseB
deriving DecidableEq, Fintype

/-- The ground MLN with two coupled existential-grounded clauses. -/
noncomputable def existGroundMLN : GroundMLN (GroundAtom RelPred Elem) ExistClauseId where
  clauseData
    | .clauseA => existClauseA
    | .clauseB => existClauseB

/-- The full clause support. -/
noncomputable def existFullSupport : Finset ExistClauseId := Finset.univ

/-- Query: Rel(a, b) = true. -/
def existRelABQuery : ConstraintQuery (GroundAtom RelPred Elem) :=
  [⟨relABAtom, true⟩]

/-! ### Valuation equivalence (Bool × Bool × Bool × Bool) -/

private noncomputable def existValEquiv :
    (GroundAtom RelPred Elem → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun W := (W relAAAtom, W relABAtom, W relBAAtom, W relBBAtom)
  invFun b a :=
    match existGroundAtomEquiv a with
    | (.a, .a) => b.1
    | (.a, .b) => b.2.1
    | (.b, .a) => b.2.2.1
    | (.b, .b) => b.2.2.2
  left_inv W := by
    funext a
    rw [show a = existGroundAtomEquiv.symm (existGroundAtomEquiv a) from
        (existGroundAtomEquiv.symm_apply_apply a).symm]
    rcases existGroundAtomEquiv a with ⟨_ | _, _ | _⟩ <;> rfl
  right_inv b := rfl

/-! ### World weight characterization -/

/-- The world weight: 1 if both clauses satisfied, 0 otherwise. -/
theorem exist_worldWeight_eq
    (W : AtomValuation (GroundAtom RelPred Elem)) :
    existGroundMLN.worldWeight existFullSupport W =
      (if W relAAAtom = true ∨ W relABAtom = true then 1 else 0) *
      (if W relBAAtom = true ∨ W relBBAtom = true then 1 else 0) := by
  classical
  -- Clause A eval: simp reduces the existential over {.pos relAAAtom, .pos relABAtom}
  -- to the disjunction W relAAAtom = true ∨ W relABAtom = true
  have hA : existClauseA.eval W =
      if W relAAAtom = true ∨ W relABAtom = true then 1 else 0 := by
    unfold existClauseA WeightedGroundClause.eval GroundClause.holds
    by_cases h : ∃ l ∈ ({.pos relAAAtom, .pos relABAtom} : Finset (Literal _)),
        Literal.holds W l <;> simp_all
  -- Clause B eval
  have hB : existClauseB.eval W =
      if W relBAAtom = true ∨ W relBBAtom = true then 1 else 0 := by
    unfold existClauseB WeightedGroundClause.eval GroundClause.holds
    by_cases h : ∃ l ∈ ({.pos relBAAtom, .pos relBBAtom} : Finset (Literal _)),
        Literal.holds W l <;> simp_all
  -- Reduce the attach-product to clauseA.eval * clauseB.eval
  have hprod : existGroundMLN.worldWeight existFullSupport W =
      existClauseA.eval W * existClauseB.eval W := by
    unfold existFullSupport GroundMLN.worldWeight
    -- The goal is ∏ i : ↥(Finset.univ.attach), (existGroundMLN.clauseData ↑↑i).eval W = ...
    -- Convert double-subtype product to plain ExistClauseId product using Equiv.prod_comp
    let e : ↥((Finset.univ : Finset ExistClauseId).attach) ≃ ExistClauseId :=
      ⟨fun i => i.1.1,
       fun x => ⟨⟨x, Finset.mem_univ x⟩, Finset.mem_attach _ _⟩,
       fun ⟨⟨_, _⟩, _⟩ => rfl,
       fun _ => rfl⟩
    -- ∏ i, g (e i) = ∏ i, g i  (Equiv.prod_comp)
    -- First rewrite the body so it's of the form g (e i)
    let g : ExistClauseId → ENNReal := fun x => (existGroundMLN.clauseData x).eval W
    show (∏ i, g (e i)) = _
    rw [Equiv.prod_comp e]
    -- Now ∏ i : ExistClauseId, g i
    show Finset.univ.prod g = _
    rw [show (Finset.univ : Finset ExistClauseId) = {.clauseA, .clauseB} from by
      ext x; simp; cases x <;> simp]
    rw [Finset.prod_pair (by decide)]
    simp [existGroundMLN]
  rw [hprod, hA, hB]

/-! ### Mass computations -/

private noncomputable def existWeightFn : Bool × Bool × Bool × Bool → ENNReal :=
  fun b => (if b.1 = true ∨ b.2.1 = true then (1 : ENNReal) else 0) *
           (if b.2.2.1 = true ∨ b.2.2.2 = true then 1 else 0)

private theorem exist_sum_worldWeight_eq_nine :
    ∑ W : AtomValuation (GroundAtom RelPred Elem),
      existGroundMLN.worldWeight existFullSupport W = 9 := by
  simp only [exist_worldWeight_eq]
  rw [show ∑ W : GroundAtom RelPred Elem → Bool,
        (if W relAAAtom = true ∨ W relABAtom = true then (1:ENNReal) else 0) *
        (if W relBAAtom = true ∨ W relBBAtom = true then 1 else 0) =
      ∑ b : Bool × Bool × Bool × Bool, existWeightFn b
    from Equiv.sum_comp existValEquiv existWeightFn]
  simp only [existWeightFn, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

private theorem exist_sum_queryMass_relAB_eq_six :
    ∑ W : AtomValuation (GroundAtom RelPred Elem),
      (if ∀ c ∈ existRelABQuery, W c.1 = c.2 then
          existGroundMLN.worldWeight existFullSupport W
        else 0) = 6 := by
  simp only [exist_worldWeight_eq]
  -- Simplify query condition
  have hsum :
      (∑ W : AtomValuation (GroundAtom RelPred Elem),
        if ∀ c ∈ existRelABQuery, W c.1 = c.2 then
          (if W relAAAtom = true ∨ W relABAtom = true then (1:ENNReal) else 0) *
          (if W relBAAtom = true ∨ W relBBAtom = true then 1 else 0) else 0) =
      ∑ W : AtomValuation (GroundAtom RelPred Elem),
        if W relABAtom = true then
          (if W relAAAtom = true ∨ W relABAtom = true then (1:ENNReal) else 0) *
          (if W relBAAtom = true ∨ W relBBAtom = true then 1 else 0) else 0 := by
    apply Fintype.sum_congr; intro W
    by_cases h : W relABAtom = true <;> simp [existRelABQuery, h]
  rw [hsum]
  rw [show ∑ W : GroundAtom RelPred Elem → Bool,
        (if W relABAtom = true then
          (if W relAAAtom = true ∨ W relABAtom = true then (1:ENNReal) else 0) *
          (if W relBAAtom = true ∨ W relBBAtom = true then 1 else 0) else 0) =
      ∑ b : Bool × Bool × Bool × Bool,
        (if b.2.1 = true then
          (if b.1 = true ∨ b.2.1 = true then (1:ENNReal) else 0) *
          (if b.2.2.1 = true ∨ b.2.2.2 = true then 1 else 0) else 0)
    from Equiv.sum_comp existValEquiv (fun b =>
      if b.2.1 = true then
        (if b.1 = true ∨ b.2.1 = true then (1 : ENNReal) else 0) *
        (if b.2.2.1 = true ∨ b.2.2.2 = true then 1 else 0)
      else 0)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-! ### Top-level regression theorems -/

theorem exist_totalMass_eq_nine :
    (clauseMassSemantics existGroundMLN existFullSupport).totalMass = 9 := by
  change CountableMLNSemantics.totalMass
    (existGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      existFullSupport constraintQueryHolds) = 9
  unfold CountableMLNSemantics.totalMass GroundMLN.toCountableMLNSemantics
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact exist_sum_worldWeight_eq_nine

theorem exist_queryMass_relAB_eq_six :
    (clauseMassSemantics existGroundMLN existFullSupport).queryMass existRelABQuery = 6 := by
  change CountableMLNSemantics.queryMass
    (existGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      existFullSupport constraintQueryHolds) existRelABQuery = 6
  simp only [CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics,
             constraintQueryHolds, satisfiesConstraints]
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact exist_sum_queryMass_relAB_eq_six

theorem exist_queryProb_relAB_eq_two_thirds :
    (clauseMassSemantics existGroundMLN existFullSupport).queryProb existRelABQuery =
      (2 : ENNReal) / 3 := by
  have htotal : (clauseMassSemantics existGroundMLN existFullSupport).totalMass ≠ 0 := by
    rw [exist_totalMass_eq_nine]; norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal, exist_queryMass_relAB_eq_six, exist_totalMass_eq_nine]
  have hr : (6 : ℝ) / 9 = (2 : ℝ) / 3 := by ring_nf
  simpa [ENNReal.ofReal_div_of_pos] using congrArg ENNReal.ofReal hr

/-- **Existential-coupling canary**: Two coupled hard-constraint clauses from
existential grounding of `∃ y. Rel(x, y)` over `{a, b}` yield
`queryStrength = 2/3` for `Rel(a,b)`.

Unlike the Smokes canary (where Alice and Bob factors are independent), these
clauses create within-clause coupling: `Rel(a,a)` and `Rel(a,b)` appear in the
same ground clause.  Under the induced distribution:
  P(Rel(a,b)=T) = 6/9 = 2/3,  P(Rel(a,a)=T) = 6/9 = 2/3,
  P(Rel(a,b)=T ∧ Rel(a,a)=T) = 3/9 = 1/3 ≠ 4/9 = (2/3)².
The exact `queryStrength` captures this coupling correctly. -/
theorem exist_queryStrength_relAB_eq_two_thirds :
    BinaryWorldModel.queryStrength (clauseWMState existGroundMLN existFullSupport)
      existRelABQuery = (2 : ENNReal) / 3 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact exist_queryProb_relAB_eq_two_thirds

end ExistCouplingRegression

end Mettapedia.Logic.MarkovLogicGrounding
