import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBinding

/-!
# Reflection: inert quoted data, explicit activation, and declared syntax observations

## Activation after quotation is the identity, one layer at a time
* `activate_quote` (the counit law): `activate (quote c)` reaches `c` in its own scope by two
  administrative steps and one activation, for every `c`; on the step by a run of translated firings
  (`activate_quote_on_step`).
* `one_layer`: an activation removes exactly one quotation layer: `activate (quote (quote d))` halts at
  quoted code in every run.
* Control (`activation_needs_code`): activating an atom is stuck.

## Quoted data is inert
* `quotation_inert`: for every code `c`, quoting halts at quoted code in one step, and a halted
  quotation has no step and no translated firing. Quoting a divergent term halts (`quoted_loop_halts`)
  while activating it never halts (`activated_loop_diverges`).
* `schemas_never_inspect_code`: no take pattern, read pattern or made term of the core has rigid
  structure inside a quotation: matching binds quoted code as one value.

## Only reflection queries observe syntax
The core's firings have no predicate query: they are ordinary (`firing_isSemantic`). A query about
rows is ordinary when it reads labels through solutions (R80's split, `Semantic`).
* `rawQuoted_not_semantic`: the query "this row is literally a quotation", read on raw label syntax,
  does not read through solutions; a firing carrying it is not a firing of the ordinary step
  (`rawQuoted_firing_not_semantic`), as R80's `SemanticControls.syntactic_collision` found for raw
  regions in general.
* `rawQuoted_collision`: two configurations that represent the same rows (a quotation, once as a
  rigid label, once through the knowledge) are told apart by the raw query, and not by its
  through-solutions version.
* `semantic_admission_iff`: the through-solutions query's admission depends only on the rows a
  configuration represents.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation
open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (regionOf)

/-! ## The counit law -/

/-- **Activation after quotation is the identity**: two administrative steps and one activation. -/
theorem activate_quote (c ρ κ : Sx) (W : Multiset Sx) :
    ∃ W₁ W₂ : Multiset Sx, Administrative (ev (activate (quote c)) ρ κ ::ₘ W) W₁ ∧
      Administrative W₁ W₂ ∧ Step W₂ (ev c ρ κ ::ₘ W) :=
  ⟨_, _, .activate (quote c) ρ κ W, .quote c ρ (cons actK κ) W, .activateK c ρ κ W⟩

/-- **The counit law on the step.** -/
theorem activate_quote_on_step (c ρ κ : Sx) (W : Multiset Sx) {C : Config} {n : ℕ}
    (rep : Represents C (ev (activate (quote c)) ρ κ ::ₘ W) n) :
    ∃ q : Config × ℕ, Relation.ReflTransGen (Translated schema) (C, n) q ∧
      Represents q.1 (ev c ρ κ ::ₘ W) q.2 := by
  obtain ⟨_, _, s₁, s₂, s₃⟩ := activate_quote c ρ κ W
  exact path_on_step (.tail (.tail (.single s₁.step) s₂.step) s₃) rep

/-- `activate (quote (quote a))`. -/
def twoLayers : Sx := ev (activate (quote (quote (atom ka)))) nil nil

theorem twoLayers_closed : SuccessorClosed (reach 5 [[twoLayers]]) = true := by decide

/-- **One activation removes exactly one quotation layer**: every run halts at quoted code. -/
theorem one_layer : halted (reach 5 [[twoLayers]]) = [[ret (code (atom ka) nil) nil]] := by decide

/-- `activate a`, for an atom `a`. -/
def activateAtom : Sx := ev (activate (atom ka)) nil nil

theorem activateAtom_closed : SuccessorClosed (reach 3 [[activateAtom]]) = true := by decide

/-- **Control: activation needs quoted code**; activating an atom is stuck. -/
theorem activation_needs_code : halted (reach 3 [[activateAtom]]) = [[ret (atom ka) (cons actK nil)]] := by
  decide

/-! ## Quoted data is inert -/

/-- No single-take rule's take pattern is compatible with `q`. -/
def incompatibleWith (q : Pat) : Bool :=
  allRules.all fun i =>
    match (schema i).take with
    | [p] => !(compatible p q)
    | _ => true

/-- **A row incompatible with every single-take pattern has no step**, whatever fills its
variables. -/
theorem stuck_of_incompatible {q : Pat} (check : incompatibleWith q = true) (θ : ℕ → Sx) (W' : Multiset Sx) :
    ¬ Step {q.inst θ} W' := fun step => by
  obtain ⟨i, p, θ', hi, -, hp, -⟩ := step_singleton.mp step
  simp only [incompatibleWith, List.all_eq_true] at check
  have entry := check i (mem_allRules i)
  rw [hi] at entry
  have compat := compatible_of_inst p q hp
  change (!(compatible p q)) = true at entry
  rw [compat] at entry
  cases entry

/-- A halted quotation: `ret (code x0 x1) nil`. -/
def haltedQuotation : Pat := p2 30 (p2 19 (.var 0) (.var 1)) (p0 20)

theorem haltedQuotation_incompatible : incompatibleWith haltedQuotation = true := by decide

/-- **Quoted code is inert**: for every code `c`, quoting halts at quoted code in one step, and the
halted quotation has no step and no translated firing. -/
theorem quotation_inert (c ρ : Sx) :
    Step ({ev (quote c) ρ nil} : Multiset Sx) {ret (code c ρ) nil} ∧
      (∀ W', ¬ Step ({ret (code c ρ) nil} : Multiset Sx) W') ∧
      ∀ {C : Config} {n : ℕ}, Represents C {ret (code c ρ) nil} n → ∀ q, ¬ Translated schema (C, n) q := by
  have stuck : ∀ W', ¬ Step ({ret (code c ρ) nil} : Multiset Sx) W' :=
    stuck_of_incompatible haltedQuotation_incompatible (args [c, ρ])
  exact ⟨.quote c ρ nil 0, stuck, fun rep q => stuck_of_source rep stuck q⟩

/-- The self-application `ω = λ. var 0 (var 0)`, and the divergent term `Ω = ω ω`. -/
def omega : Sx := lam (app (var zero) (var zero))
def bigOmega : Sx := app omega omega

/-- `quote Ω`. -/
def quotedLoop : Sx := ev (quote bigOmega) nil nil
/-- `activate (quote Ω)`. -/
def activatedLoop : Sx := ev (activate (quote bigOmega)) nil nil

theorem quotedLoop_closed : SuccessorClosed (reach 2 [[quotedLoop]]) = true := by decide
theorem activatedLoop_closed : SuccessorClosed (reach 12 [[activatedLoop]]) = true := by decide

/-- **A quoted loop halts.** -/
theorem quoted_loop_halts : halted (reach 2 [[quotedLoop]]) = [[ret (code bigOmega nil) nil]] := by decide

/-- **An activated loop never halts**: every configuration it reaches has a step. -/
theorem activated_loop_diverges (W : Multiset Sx)
    (path : Relation.ReflTransGen Step ({activatedLoop} : Multiset Sx) W) : ∃ W', Step W W' := by
  have none : halted (reach 12 [[activatedLoop]]) = [] := by decide
  by_contra none'
  have stuck : ∀ W', ¬ Step W W' := fun W' h => none' ⟨W', h⟩
  obtain ⟨H, mem, -⟩ := (halted_runs activatedLoop_closed).2 W path stuck
  rw [none] at mem
  cases mem

/-- Every quotation node in the pattern has a variable as its code. -/
def opaqueCode : Pat → Bool
  | .cell (.sym 19) (.cell (.var _) b) => opaqueCode b
  | .cell (.sym 19) (.cell _ _) => false
  | .cell a b => opaqueCode a && opaqueCode b
  | _ => true

/-- **No rule looks inside a quotation**: in every take pattern, read pattern and made term, the
code of a quotation is a pattern variable. -/
theorem schemas_never_inspect_code (i : RuleName) :
    ∀ p ∈ (schema i).take ++ (schema i).read ++ (schema i).make, opaqueCode p = true := by
  cases i <;> decide

/-! ## Only reflection queries observe syntax -/

/-- A row is a returned quotation. -/
def quotedRow : Sx → Bool
  | .cell (.sym 30) (.cell (.cell (.sym 19) _) _) => true
  | _ => false

/-- **The raw query**: it reads a label's own syntax (variables read as the symbol `0`). -/
def rawQuoted (seen : Finset Occ) : PredicateQueryAdmission.Query Tm (Subst rows) Occ :=
  ⟨fun _ t => quotedRow (decode t), seen⟩

/-- **The ordinary query**: the same test, read through the solution. -/
def semanticQuoted (seen : Finset Occ) : Semantic.SemanticQuery A Occ :=
  Semantic.throughSolutions A (fun t => quotedRow (decode t)) (fun same => by rw [same]) seen

/-- A firing that only asks one predicate query. -/
def queryFiring (query : PredicateQueryAdmission.Query Tm (Subst rows) Occ) : AnnotatedRuns.Firing Tm (Subst rows) Occ :=
  ⟨⟨[], [], [], [], []⟩, [query], ⟨[], [], []⟩⟩

/-- The quoted value of the collision: `code a nil`. -/
def quotedValue : Sx := code (atom ka) nil
/-- The quotation held through the knowledge: `ret X nil`, with `X` a variable. -/
def heldLabel : Tm := node (.const 30) (node (.var (0, 0)) (.const 20))

theorem embed_ret (v κ : Sx) : embed (ret v κ) = node (.const 30) (node (embed v) (embed κ)) := rfl

/-- **The raw query does not read through solutions.** -/
theorem rawQuoted_not_semantic (seen : Finset Occ) : ¬ Semantic.ReadsThroughSolutions A (rawQuoted seen) := by
  intro reads
  let σ : Subst rows := fun v => if v = (0, 0) then embed quotedValue else .var v
  have solves : A.Solves σ (heldLabel, embed (ret quotedValue nil)) := by
    change σ.applyTerm heldLabel = σ.applyTerm (embed (ret quotedValue nil))
    rw [apply_embed, embed_ret, heldLabel, apply_node, apply_node]
    rfl
  have := reads σ solves
  change quotedRow (decode heldLabel) = quotedRow (decode (embed (ret quotedValue nil))) at this
  rw [decode_embed] at this
  exact absurd this (by decide)

/-- **A firing carrying the raw query is not a firing of the ordinary step.** -/
theorem rawQuoted_firing_not_semantic (seen : Finset Occ) :
    ¬ Semantic.IsSemantic A (queryFiring (rawQuoted seen)) := fun reads =>
  rawQuoted_not_semantic seen (reads _ (List.mem_singleton_self _))

/-- The rigid configuration: the quotation as its label. -/
def rigidOcc : Occ := ⟨embed (ret quotedValue nil), 0, 0⟩
def rigidConfig : Config := ⟨[], {rigidOcc}⟩
/-- The held configuration: the label `ret X nil`, and the knowledge `X = code a nil`. -/
def heldOcc : Occ := ⟨heldLabel, 0, 0⟩
def heldConfig : Config := ⟨[(.var (0, 0), embed quotedValue)], {heldOcc}⟩

theorem rigid_represents : Represents rigidConfig {ret quotedValue nil} 1 := by
  refine ⟨⟨Subst.id rows, SubstitutionAction.models_nil A _⟩, fun e h => absurd h List.not_mem_nil, ?_,
    fun _ => ret quotedValue nil, ?_, rfl⟩
  · intro o member
    rw [Finset.mem_singleton.mp member]
    exact ⟨Nat.zero_lt_one, embed_bounded 1 _⟩
  · intro σ _ o member
    rw [Finset.mem_singleton.mp member]
    exact apply_embed σ _

/-- At every solution of the held knowledge, the held label reads as the returned quotation. -/
theorem held_observed (σ : Subst rows) (solved : A.Models σ heldConfig.equations) :
    σ.applyTerm heldLabel = embed (ret quotedValue nil) := by
  have bound : σ (0, 0) = embed quotedValue := by
    have := solved _ (List.mem_singleton_self _)
    change σ.applyTerm (.var (0, 0)) = σ.applyTerm (embed quotedValue) at this
    rwa [apply_embed] at this
  rw [heldLabel, apply_node, apply_node, embed_ret]
  change node (.const 30) (node (σ (0, 0)) (.const 20)) = _
  rw [bound]
  rfl

theorem held_represents : Represents heldConfig {ret quotedValue nil} 1 := by
  let σ₀ : Subst rows := fun v => if v = (0, 0) then embed quotedValue else .var v
  refine ⟨⟨σ₀, ?_⟩, ?_, ?_, fun _ => ret quotedValue nil, ?_, rfl⟩
  · intro e member
    rw [List.mem_singleton.mp member]
    change σ₀ (0, 0) = σ₀.applyTerm (embed quotedValue)
    rw [apply_embed]
    rfl
  · intro e member
    rw [List.mem_singleton.mp member]
    refine ⟨fun v hv => ?_, embed_bounded 1 _⟩
    rw [Term.mem_freeVars_var (σ := rows)] at hv
    rw [hv]
    exact Nat.zero_lt_one
  · intro o member
    rw [Finset.mem_singleton.mp member]
    refine ⟨Nat.zero_lt_one, fun v hv => ?_⟩
    rcases mem_freeVars_node.mp hv with hv | hv
    · simp [Term.freeVars] at hv
    · rcases mem_freeVars_node.mp hv with hv | hv
      · rw [Term.mem_freeVars_var (σ := rows)] at hv
        rw [hv]
        exact Nat.zero_lt_one
      · simp [Term.freeVars] at hv
  · intro σ solved o member
    rw [Finset.mem_singleton.mp member]
    exact held_observed σ solved

theorem queryFiring_valid_iff (query : PredicateQueryAdmission.Query Tm (Subst rows) Occ) (C : Config)
    (consistent : A.Consistent C.equations) :
    (queryFiring query).Valid A Occ.label C ↔ query.Ask A C.equations Occ.label C.present := by
  have problem : (queryFiring query).selection.problem Occ.label (queryFiring query).rule C = C.equations := by
    simp [queryFiring, Selection.problem, Selection.equations]
  constructor
  · intro valid
    have := valid.observations query (List.mem_singleton_self _)
    rwa [problem] at this
  · intro asked
    refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro o h; simp [queryFiring, Selection.commit] at h
    · intro o h; simp [queryFiring, Selection.commit] at h
    · simp [queryFiring, Selection.commit]
    · simp [queryFiring, Selection.commit]
    · intro q h; simp [queryFiring, Selection.commit] at h
    · rw [problem]; exact consistent
    · intro check h; simp [queryFiring] at h
    · intro q h
      rw [List.mem_singleton.mp h, problem]
      exact asked

/-- **The raw query tells apart two representations of the same rows; the ordinary query does
not.** Both configurations represent the one row `ret (code a nil) nil`. The raw query that sees no
literal quotation is admitted at the held configuration and refused at the rigid one; its
through-solutions version is refused at both. -/
theorem rawQuoted_collision :
    Represents rigidConfig {ret quotedValue nil} 1 ∧ Represents heldConfig {ret quotedValue nil} 1 ∧
      (queryFiring (rawQuoted ∅)).Valid A Occ.label heldConfig ∧
      ¬ (queryFiring (rawQuoted ∅)).Valid A Occ.label rigidConfig ∧
      ¬ (queryFiring (semanticQuoted ∅).1).Valid A Occ.label heldConfig ∧
      ¬ (queryFiring (semanticQuoted ∅).1).Valid A Occ.label rigidConfig := by
  obtain ⟨heldConsistent, -, -, -, -, -⟩ := held_represents
  obtain ⟨rigidConsistent, -, -, -, -, -⟩ := rigid_represents
  have rigidSeen : ∀ σ : Subst rows,
      regionOf Occ.label rigidConfig.present (fun t => quotedRow (decode (σ.applyTerm t))) = {rigidOcc} := by
    intro σ
    simp only [rigidConfig, regionOf, Finset.filter_singleton]
    rw [if_pos]
    change quotedRow (decode (σ.applyTerm (embed (ret quotedValue nil)))) = true
    rw [apply_embed, decode_embed]
    rfl
  refine ⟨rigid_represents, held_represents, ?_, ?_, ?_, ?_⟩
  · refine (queryFiring_valid_iff _ _ heldConsistent).mpr fun σ _ => ?_
    change regionOf Occ.label heldConfig.present (fun t => quotedRow (decode t)) = ∅
    simp only [heldConfig, regionOf, Finset.filter_singleton]
    rw [if_neg]
    decide
  · intro valid
    have asked := (queryFiring_valid_iff _ _ rigidConsistent).mp valid (Subst.id rows)
      (SubstitutionAction.models_nil A _)
    change regionOf Occ.label rigidConfig.present (fun t => quotedRow (decode t)) = ∅ at asked
    simp only [rigidConfig, regionOf, Finset.filter_singleton] at asked
    rw [if_pos (by rw [rigidOcc, decode_embed]; rfl)] at asked
    exact Finset.singleton_ne_empty _ asked
  · intro valid
    obtain ⟨σ, solved⟩ := heldConsistent
    have asked := (queryFiring_valid_iff _ _ ⟨σ, solved⟩).mp valid σ solved
    change regionOf Occ.label heldConfig.present (fun t => quotedRow (decode (σ.applyTerm t))) = ∅ at asked
    simp only [heldConfig, regionOf, Finset.filter_singleton] at asked
    rw [if_pos (by
      change quotedRow (decode (σ.applyTerm heldLabel)) = true
      rw [held_observed σ solved, decode_embed]
      rfl)] at asked
    exact Finset.singleton_ne_empty _ asked
  · intro valid
    have asked := (queryFiring_valid_iff _ _ rigidConsistent).mp valid (Subst.id rows)
      (SubstitutionAction.models_nil A _)
    change regionOf Occ.label rigidConfig.present
      (fun t => quotedRow (decode ((Subst.id rows).applyTerm t))) = ∅ at asked
    rw [rigidSeen] at asked
    exact Finset.singleton_ne_empty _ asked

/-- **The ordinary query observes only represented rows**: its firing is admitted at a configuration
exactly when no represented row is a returned quotation. -/
theorem semantic_admission_iff {C : Config} {W : Multiset Sx} {n : ℕ} (rep : Represents C W n) :
    (queryFiring (semanticQuoted ∅).1).Valid A Occ.label C ↔ ∀ s ∈ W, quotedRow s = false := by
  obtain ⟨consistent, -, -, value, observed, rfl⟩ := rep
  rw [queryFiring_valid_iff _ _ consistent]
  obtain ⟨σ₀, solved₀⟩ := consistent
  have region : ∀ σ, A.Models σ C.equations →
      regionOf Occ.label C.present (fun t => quotedRow (decode (σ.applyTerm t))) =
        C.present.filter fun o => quotedRow (value o) = true := by
    intro σ solved
    refine Finset.filter_congr fun o member => ?_
    show quotedRow (decode (σ.applyTerm o.label)) = true ↔ _
    rw [observed σ solved o member, decode_embed]
  constructor
  · intro asked s hs
    obtain ⟨o, member, rfl⟩ := Multiset.mem_map.mp hs
    have empty := asked σ₀ solved₀
    change regionOf Occ.label C.present (fun t => quotedRow (decode (σ₀.applyTerm t))) = ∅ at empty
    rw [region σ₀ solved₀] at empty
    by_contra quoted
    have : o ∈ C.present.filter fun o => quotedRow (value o) = true :=
      Finset.mem_filter.mpr ⟨member, by simpa using quoted⟩
    rw [empty] at this
    exact Finset.notMem_empty o this
  · intro none σ solved
    change regionOf Occ.label C.present (fun t => quotedRow (decode (σ.applyTerm t))) = ∅
    rw [region σ solved]
    exact Finset.filter_false_of_mem fun o member => by
      simp [none (value o) (Multiset.mem_map_of_mem value member)]

#print axioms activate_quote
#print axioms activate_quote_on_step
#print axioms one_layer
#print axioms activation_needs_code
#print axioms stuck_of_incompatible
#print axioms quotation_inert
#print axioms quoted_loop_halts
#print axioms activated_loop_diverges
#print axioms schemas_never_inspect_code
#print axioms rawQuoted_not_semantic
#print axioms rawQuoted_firing_not_semantic
#print axioms rigid_represents
#print axioms held_represents
#print axioms rawQuoted_collision
#print axioms semantic_admission_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
