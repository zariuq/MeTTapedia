import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# One SLD resolution step is one firing of the one-frame step

A definite program is a list of Horn clauses over first-order terms; an atom is a term whose head
symbol is its predicate. A configuration of the one-frame step (`AnnotatedRuns.firstOrder`) over the
first-order equation-store profile (`FirstOrder.action`) holds the goals as occurrences, each
labelled by its atom, and the knowledge as a store of equations.

## The firing (`resolve`)

`resolve o c ρ made` resolves the goal occurrence `o` against the clause `c` renamed by `ρ`:

* it **takes** `o` with the renamed head as pattern, so the take's equation is the unification of
  the goal and the head;
* it **reads** the clause renamed apart: the rule instance is the built-in clause (`builtInRule`)
  prepared from `c` by `ρ`, whose image of the clause's variables is the firing's fresh variables
  (`Fresh`). Reading a clause stored in the space through the read port, which opens it at a fresh
  scope, reduces to this same built-in rule (`ReadPort.solvable_iff_builtIn`);
* it **tells** nothing besides that equation;
* it **makes** the body goals, the occurrences `made`, labelled by the renamed body.

## Admission and result

* **Admission is unification** (`resolve_valid_iff`): the firing is admitted exactly when its goal is
  present, its made occurrences are fresh, distinct and carry the renamed body, and under the
  knowledge the goal and the renamed head unify (`Unifiable`).
* **The result is the resolvent in store form** (`resolve_result`): the goal is replaced by the body
  goals and the unification joins the knowledge.
* **Read at the principal answers, it is Lloyd's SLD step** (`resolve_sld_step`). Let `θ` be the
  answer of the knowledge returned by the total occurs-checked unifier, and let the renaming be fresh
  for the knowledge. Then the firing is admitted exactly when the goal read at `θ` unifies with the
  renamed head. With `μ` a most general unifier of the two, the result's knowledge has the principal
  answer `μ ∘ θ`, and its goals read there are `μ` applied to the other goals read at `θ` together
  with the renamed body: the SLD resolvent of the goal list `θ G` with the variant `ρ c`.
  The abstract step is `consistent_pair_iff` and `Principal.compose`.

## Atomicity

* **An admitted firing commits fully** (`resolve_commits`): its goal is consumed, every body goal is
  made, every other occurrence survives, nothing else appears, and the knowledge gains exactly the
  unification.
* **A refused firing leaves no residue** (`resolve_refused_iff`, `resolve_no_step`): it is refused
  exactly when a presence or freshness condition fails or the unification fails, and then no run
  begins with it, so the configuration is left as it was.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder)
open MeTTaCalculus.OccurrenceCommits (fire Enabled)

universe uO

variable {sig : LPSignature}

/-! ## Clauses, renamings and variables -/

/-- **A definite clause** over first-order terms: a head atom and a list of body atoms. -/
structure Clause (sig : LPSignature) where
  head : Term sig
  body : List (Term sig)

/-- A definite program. -/
abbrev Program (sig : LPSignature) := List (Clause sig)

/-- The substitution of a renaming of variables. -/
def permSubst (ρ : Equiv.Perm sig.vars) : Subst sig := fun v => .var (ρ v)

/-- A term renamed. -/
abbrev rename (ρ : Equiv.Perm sig.vars) (t : Term sig) : Term sig := (permSubst ρ).applyTerm t

theorem permSubst_trans (ρ π : Equiv.Perm sig.vars) :
    permSubst (ρ.trans π) = permSubst π ∘ₛ permSubst ρ := by
  funext v
  rfl

theorem rename_trans (ρ π : Equiv.Perm sig.vars) (t : Term sig) :
    rename (ρ.trans π) t = rename π (rename ρ t) := by
  rw [rename, permSubst_trans, Subst.applyTerm_comp]

theorem permSubst_refl : permSubst (Equiv.refl sig.vars) = Subst.id sig := by
  funext v
  rfl

theorem rename_symm_rename (ρ : Equiv.Perm sig.vars) (t : Term sig) :
    rename ρ.symm (rename ρ t) = t := by
  rw [← rename_trans, Equiv.self_trans_symm, rename, permSubst_refl, Subst.applyTerm_id]

theorem rename_rename_symm (ρ : Equiv.Perm sig.vars) (t : Term sig) :
    rename ρ (rename ρ.symm t) = t := by
  rw [← rename_trans, Equiv.symm_trans_self, rename, permSubst_refl, Subst.applyTerm_id]

/-! ## Unification under the knowledge -/

variable (sig) in
/-- The first-order equation-store profile over the terms of `sig`. -/
abbrev A := FirstOrder.action sig

/-- **Unification under the knowledge**: some solution of `K` makes `s` and `t` equal. -/
def Unifiable (K : EquationStore (Term sig)) (s t : Term sig) : Prop :=
  ∃ τ : Subst sig, (A sig).Models τ K ∧ τ.applyTerm s = τ.applyTerm t

theorem unifiable_iff_consistent (K : EquationStore (Term sig)) (s t : Term sig) :
    Unifiable K s t ↔ (A sig).Consistent (K ++ [(s, t)]) := by
  constructor
  · rintro ⟨τ, solved, same⟩
    exact ⟨τ, ((A sig).models_append _ _ _).mpr
      ⟨solved, ((A sig).models_cons _ _ _).mpr ⟨same, (A sig).models_nil τ⟩⟩⟩
  · rintro ⟨τ, solved⟩
    obtain ⟨knowledge, pair⟩ := ((A sig).models_append _ _ _).mp solved
    exact ⟨τ, knowledge, (((A sig).models_cons _ _ _).mp pair).1⟩

/-- With no knowledge, unification under the knowledge is plain unification. -/
theorem unifiable_nil_iff (s t : Term sig) :
    Unifiable [] s t ↔ ∃ τ : Subst sig, τ.applyTerm s = τ.applyTerm t :=
  ⟨fun ⟨τ, _, same⟩ => ⟨τ, same⟩, fun ⟨τ, same⟩ => ⟨τ, (A sig).models_nil τ, same⟩⟩

/-- **Reading through a principal answer**: a store extended by one equation is consistent exactly
when the equation read at a principal answer of the store is. -/
theorem consistent_pair_iff {T S : Type*} (X : SubstitutionAction T S) {K : EquationStore T} {θ : S}
    (principal : X.Principal K θ) (s t : T) :
    X.Consistent (K ++ [(s, t)]) ↔ X.Consistent [(X.apply θ s, X.apply θ t)] := by
  constructor
  · rintro ⟨τ, solved⟩
    obtain ⟨knowledge, pair⟩ := (X.models_append _ _ _).mp solved
    obtain ⟨residual, through⟩ := principal.factors τ knowledge
    have same : X.E (X.apply τ s) (X.apply τ t) := pair (s, t) List.mem_cons_self
    refine ⟨residual, (X.models_cons _ _ _).mpr ⟨?_, X.models_nil _⟩⟩
    show X.E (X.apply residual (X.apply θ s)) (X.apply residual (X.apply θ t))
    have first := through s
    have second := through t
    rw [X.apply_compose] at first second
    exact X.equivalence.trans (X.equivalence.symm first) (X.equivalence.trans same second)
  · rintro ⟨μ, solved⟩
    have pair : X.E (X.apply μ (X.apply θ s)) (X.apply μ (X.apply θ t)) := solved _ List.mem_cons_self
    refine ⟨X.compose μ θ, (X.models_append _ _ _).mpr
      ⟨SubstitutionAction.Principal.extension_models X principal μ, ?_⟩⟩
    refine (X.models_cons _ _ _).mpr ⟨?_, X.models_nil _⟩
    show X.E (X.apply (X.compose μ θ) s) (X.apply (X.compose μ θ) t)
    rw [X.apply_compose, X.apply_compose]
    exact pair

variable [DecidableEq sig.vars]

/-- The variables of a list of terms. -/
def termsVars : List (Term sig) → Finset sig.vars
  | [] => ∅
  | t :: ts => t.freeVars ∪ termsVars ts

theorem mem_termsVars {v : sig.vars} :
    ∀ {ts : List (Term sig)}, v ∈ termsVars ts ↔ ∃ t ∈ ts, v ∈ t.freeVars
  | [] => by simp [termsVars]
  | t :: ts => by
      rw [termsVars, Finset.mem_union, mem_termsVars]
      simp only [List.mem_cons, exists_eq_or_imp]

/-- The variables of a clause. -/
def Clause.vars (c : Clause sig) : Finset sig.vars := c.head.freeVars ∪ termsVars c.body

theorem Clause.head_vars (c : Clause sig) : c.head.freeVars ⊆ c.vars :=
  Finset.subset_union_left

theorem Clause.body_vars (c : Clause sig) {b : Term sig} (member : b ∈ c.body) :
    b.freeVars ⊆ c.vars := fun _ occurs =>
  Finset.mem_union_right _ (mem_termsVars.mpr ⟨b, member, occurs⟩)

/-- The variables of a renamed term are the renamed variables. -/
theorem mem_freeVars_rename {ρ : Equiv.Perm sig.vars} {t : Term sig} {x : sig.vars} :
    x ∈ (rename ρ t).freeVars ↔ ∃ v ∈ t.freeVars, ρ v = x := by
  rw [rename, Subst.mem_freeVars_applyTerm]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  show x ∈ (Term.var (ρ v) : Term sig).freeVars ↔ ρ v = x
  rw [Term.mem_freeVars_var]
  exact eq_comm

/-- **The renaming is fresh** for the variables `W`: it sends every variable of the clause outside
`W`. Its images of the clause's variables are the firing's fresh variables. -/
def Fresh (W : Finset sig.vars) (ρ : Equiv.Perm sig.vars) (c : Clause sig) : Prop :=
  ∀ v ∈ c.vars, ρ v ∉ W

/-- A fresh renaming moves every variable of a clause term outside `W`. -/
theorem Fresh.term {W : Finset sig.vars} {ρ : Equiv.Perm sig.vars} {c : Clause sig}
    (fresh : Fresh W ρ c) {t : Term sig} (inside : t.freeVars ⊆ c.vars) :
    ∀ x ∈ (rename ρ t).freeVars, x ∉ W := by
  intro x occurs
  obtain ⟨v, member, rfl⟩ := mem_freeVars_rename.mp occurs
  exact fresh v (inside member)

/-- **A fresh renaming exists** in an infinite supply of variables: it moves the clause's variables
outside `W` and fixes every other variable of `W`. -/
theorem exists_fresh [Infinite sig.vars] (W : Finset sig.vars) (c : Clause sig) :
    ∃ ρ : Equiv.Perm sig.vars, Fresh W ρ c ∧ ∀ v ∈ W, v ∉ c.vars → ρ v = v := by
  obtain ⟨ρ, -, moved, fixed⟩ := Observation.exists_fresh_relabelling (label := fun _ : sig.vars => ())
    c.vars (c.vars ∪ W) Finset.subset_union_left
    (fun _ _ G => (Infinite.exists_notMem_finset G).imp fun _ out => ⟨out, rfl⟩)
  exact ⟨ρ, fun v member inW => moved v member (Finset.mem_union_right _ inW),
    fun v inW notC => fixed v (Finset.mem_union_right _ inW) notC⟩

variable {O : Type uO} (label : O → Term sig)

/-- The variables of a configuration: those of its knowledge and of its present goals. -/
def configVars (C : Configuration (Term sig) O) : Finset sig.vars :=
  eqVars C.equations ∪ C.present.biUnion fun o => (label o).freeVars

variable {label}

theorem eqVars_subset_configVars (C : Configuration (Term sig) O) :
    eqVars C.equations ⊆ configVars label C :=
  Finset.subset_union_left

theorem label_vars_subset_configVars {C : Configuration (Term sig) O} {o : O} (present : o ∈ C.present) :
    (label o).freeVars ⊆ configVars label C := fun _ occurs =>
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨o, present, occurs⟩)

variable [DecidableEq O]

/-! ## The firing -/

/-- **The built-in clause as a raw rule instance**: take the goal with the prepared head, make the
prepared body. The read port prepares it by opening a stored clause at a fresh scope
(`ReadPort.solvable_iff_builtIn`); here it is prepared by a renaming. -/
@[simp] def builtInRule {T : Type*} (head : T) (body : List T) : RuleInstance T := ⟨[head], [], [], [], body⟩

/-- The selection of the built-in clause: take the goal, read nothing, make the body goals. -/
@[simp] def builtInSelection {P : Type*} (goal : P) (made : List P) : Selection P := ⟨[goal], [], made⟩

/-- **One SLD resolution step as one firing**: take the goal occurrence `o` with the renamed head as
pattern, so the take's equation is the unification of goal and head; make the renamed body as the
occurrences `made`. It is the built-in clause prepared by the renaming `ρ`. -/
def resolve (o : O) (c : Clause sig) (ρ : Equiv.Perm sig.vars) (made : List O) :
    Firing (Term sig) (Subst sig) O :=
  ⟨builtInRule (rename ρ c.head) (c.body.map (rename ρ)), [], builtInSelection o made⟩

omit [DecidableEq sig.vars] [DecidableEq O] in
variable (label) in
/-- The goal a resolution firing resolves, the clause and renaming it reads, and its made goals. -/
theorem resolve_problem (C : Configuration (Term sig) O) (o : O) (c : Clause sig)
    (ρ : Equiv.Perm sig.vars) (made : List O) :
    (resolve o c ρ made).selection.problem label (resolve o c ρ made).rule C =
      C.equations ++ [(rename ρ c.head, label o)] := by
  simp [resolve, Selection.problem, Selection.equations]

omit [DecidableEq sig.vars] in
variable (label) in
/-- **The result is the resolvent in store form**: the goal is replaced by the body goals, and the
unification of goal and renamed head joins the knowledge. -/
theorem resolve_result (C : Configuration (Term sig) O) (o : O) (c : Clause sig)
    (ρ : Equiv.Perm sig.vars) (made : List O) :
    (resolve o c ρ made).result label C =
      ⟨C.equations ++ [(rename ρ c.head, label o)], (C.present \ {o}) ∪ made.toFinset⟩ := by
  show Selection.result _ _ _ C = _
  rw [Selection.result, resolve_problem label C o c ρ made]
  simp [resolve, fire, Selection.commit]

omit [DecidableEq sig.vars] in
variable (label) in
/-- **Admission is unification**: a resolution firing is admitted exactly when its made occurrences
are distinct and carry the renamed body, its goal is present, its made occurrences are fresh, and
under the knowledge the goal and the renamed head unify. -/
theorem resolve_valid_iff (C : Configuration (Term sig) O) (o : O) (c : Clause sig)
    (ρ : Equiv.Perm sig.vars) (made : List O) :
    (resolve o c ρ made).Valid (A sig) label C ↔
      made.Nodup ∧ made.map label = c.body.map (rename ρ) ∧ o ∈ C.present ∧
        (∀ r ∈ made, r ∉ C.present) ∧ Unifiable C.equations (rename ρ c.head) (label o) := by
  have problem := resolve_problem label C o c ρ made
  constructor
  · rintro ⟨⟨_, nodup, _, _, outputs, occurrences, consistent, _⟩, _⟩
    refine ⟨nodup, outputs, ?_, ?_, ?_⟩
    · exact occurrences.taken_subset (by simp [resolve, Selection.commit])
    · intro r member present
      exact Finset.disjoint_left.mp occurrences.fresh
        (by simpa [resolve, Selection.commit] using member) present
    · rw [unifiable_iff_consistent, ← problem]
      exact consistent
  · rintro ⟨nodup, outputs, present, fresh, unifiable⟩
    refine ⟨⟨List.nodup_singleton o, nodup, rfl, rfl, outputs, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro x member
      have same : x = o := by simpa [resolve, Selection.commit] using member
      rw [same]
      exact present
    · intro x member
      simp [resolve, Selection.commit] at member
    · simp [resolve, Selection.commit]
    · refine Finset.disjoint_left.mpr fun {x} member inPresent => ?_
      exact fresh x (by simpa [resolve, Selection.commit] using member) inPresent
    · intro read member
      simp [resolve, Selection.commit] at member
    · show (A sig).Consistent ((resolve o c ρ made).selection.problem label (resolve o c ρ made).rule C)
      rw [problem, ← unifiable_iff_consistent]
      exact unifiable
    · intro check member
      simp [resolve] at member
    · intro query member
      simp [resolve] at member

/-! ## Read at the principal answers: Lloyd's SLD step -/

omit [DecidableEq sig.vars] in
/-- A principal answer of the first-order profile is a most general unifier. -/
theorem principal_iff_mgu (K : EquationStore (Term sig)) (θ : Subst sig) :
    (A sig).Principal K θ ↔ Unifies θ K ∧ ∀ δ, Unifies δ K → θ.moreGeneral δ := by
  constructor
  · intro principal
    refine ⟨principal.sound, fun δ solves => ?_⟩
    obtain ⟨residual, through⟩ := principal.factors δ solves
    exact ⟨residual, fun v => through (.var v)⟩
  · rintro ⟨sound, general⟩
    exact ⟨sound, fun δ solves => FirstOrder.factors_on_terms (general δ solves)⟩

/-- An idempotent unifier relevant to the knowledge fixes every term over fresh variables. -/
theorem relevant_fixes {θ : Subst sig} {X : Finset sig.vars} (relevant : θ.RelevantIdempotent X)
    {t : Term sig} (outside : ∀ x ∈ t.freeVars, x ∉ X) : θ.applyTerm t = t :=
  Subst.applyTerm_eq_self fun v member => relevant.fixes v (outside v member)

section Solver

variable [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]

/-- **Lloyd's SLD step.** Let `θ` be the answer that the total occurs-checked unifier returns for
the knowledge, and let the renaming be fresh for the knowledge. The firing is admitted exactly when
its shapes hold and the goal read at `θ` unifies with the renamed head. When `μ` is a most general
unifier of the two, the result's knowledge has the principal answer `μ ∘ θ`, and the result's goals
read there are `μ` applied to the other goals read at `θ` and to the renamed body: the SLD
resolvent of the goal list read at `θ` with the variant `ρ c`. -/
theorem resolve_sld_step {C : Configuration (Term sig) O} {θ : Subst sig}
    (solved : unifyTotal C.equations = some θ) {o : O} {c : Clause sig} {ρ : Equiv.Perm sig.vars}
    (fresh : Fresh (eqVars C.equations) ρ c) (made : List O) :
    ((resolve o c ρ made).Valid (A sig) label C ↔
      made.Nodup ∧ made.map label = c.body.map (rename ρ) ∧ o ∈ C.present ∧
        (∀ r ∈ made, r ∉ C.present) ∧
          ∃ μ : Subst sig, μ.applyTerm (rename ρ c.head) = μ.applyTerm (θ.applyTerm (label o))) ∧
      ∀ μ : Subst sig, (A sig).Principal [(rename ρ c.head, θ.applyTerm (label o))] μ →
        (resolve o c ρ made).Valid (A sig) label C →
        (A sig).Principal ((resolve o c ρ made).result label C).equations (μ ∘ₛ θ) ∧
          ((resolve o c ρ made).result label C).present.val.map
              (fun x => (μ ∘ₛ θ).applyTerm (label x)) =
            ((C.present.erase o).val.map (fun x => θ.applyTerm (label x)) +
              ((c.body.map (rename ρ) : List (Term sig)) : Multiset (Term sig))).map μ.applyTerm := by
  have principal : (A sig).Principal C.equations θ := FirstOrder.accepted_principal _ θ solved
  have relevant := unifyTotal_relevantIdempotent C.equations θ solved
  have headFixed : θ.applyTerm (rename ρ c.head) = rename ρ c.head :=
    relevant_fixes relevant (fresh.term c.head_vars)
  have bodyFixed : ∀ b ∈ c.body, θ.applyTerm (rename ρ b) = rename ρ b := fun b member =>
    relevant_fixes relevant (fresh.term (c.body_vars member))
  refine ⟨?_, ?_⟩
  · rw [resolve_valid_iff, unifiable_iff_consistent, consistent_pair_iff (A sig) principal]
    show _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ ∃ μ : Subst sig, _
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ?_
    change (∃ μ, (A sig).Models μ [(θ.applyTerm (rename ρ c.head), θ.applyTerm (label o))]) ↔ _
    rw [headFixed]
    refine exists_congr fun μ => ?_
    simp only [SubstitutionAction.models_cons, SubstitutionAction.models_nil, and_true]
    exact Iff.rfl
  · intro μ mgu valid
    obtain ⟨nodup, outputs, present, freshMade, -⟩ := (resolve_valid_iff label C o c ρ made).mp valid
    rw [resolve_result]
    refine ⟨?_, ?_⟩
    · have residual : (A sig).Principal ((A sig).applyStore θ [(rename ρ c.head, label o)]) μ := by
        have same : (A sig).applyStore θ [(rename ρ c.head, label o)] =
            [(rename ρ c.head, θ.applyTerm (label o))] := by
          show [(θ.applyTerm (rename ρ c.head), θ.applyTerm (label o))] = _
          rw [headFixed]
        rw [same]
        exact mgu
      exact SubstitutionAction.Principal.compose (A sig) principal residual
    · have apart : Disjoint (C.present \ {o}) made.toFinset :=
        Finset.disjoint_left.mpr fun {x} inOld inMade =>
          freshMade x (List.mem_toFinset.mp inMade) (Finset.mem_sdiff.mp inOld).1
      show (((C.present \ {o}) ∪ made.toFinset).val).map _ = _
      rw [← Finset.disjUnion_eq_union _ _ apart, Finset.disjUnion_val, Finset.sdiff_singleton_eq_erase,
        List.toFinset_val, nodup.dedup, Multiset.map_add, Multiset.map_add, Multiset.map_map,
        Multiset.map_coe, Multiset.map_coe]
      have readings : made.map (fun x => (μ ∘ₛ θ).applyTerm (label x)) =
          (c.body.map (rename ρ)).map μ.applyTerm := by
        have rewritten : made.map (fun x => (μ ∘ₛ θ).applyTerm (label x)) =
            (made.map label).map (μ ∘ₛ θ).applyTerm := by
          rw [List.map_map]
          rfl
        rw [rewritten, outputs, List.map_map, List.map_map]
        refine List.map_congr_left fun b member => ?_
        show (μ ∘ₛ θ).applyTerm (rename ρ b) = μ.applyTerm (rename ρ b)
        rw [Subst.applyTerm_comp, bodyFixed b member]
      rw [readings]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      exact Subst.applyTerm_comp μ θ (label x)

end Solver

/-! ## Atomicity -/

omit [DecidableEq sig.vars] in
variable (label) in
/-- **An admitted firing commits fully**: its goal is consumed, every body goal is made, every other
occurrence survives, nothing else appears, and the knowledge gains exactly the unification. -/
theorem resolve_commits {C : Configuration (Term sig) O} {o : O} {c : Clause sig}
    {ρ : Equiv.Perm sig.vars} {made : List O} (valid : (resolve o c ρ made).Valid (A sig) label C) :
    o ∉ ((resolve o c ρ made).result label C).present ∧
      (∀ r ∈ made, r ∈ ((resolve o c ρ made).result label C).present) ∧
      (∀ x ∈ C.present, x ≠ o → x ∈ ((resolve o c ρ made).result label C).present) ∧
      (∀ x ∈ ((resolve o c ρ made).result label C).present, (x ∈ C.present ∧ x ≠ o) ∨ x ∈ made) ∧
      ((resolve o c ρ made).result label C).equations = C.equations ++ [(rename ρ c.head, label o)] := by
  obtain ⟨-, -, present, freshMade, -⟩ := (resolve_valid_iff label C o c ρ made).mp valid
  rw [resolve_result]
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false,
      and_false, false_or, List.mem_toFinset]
    exact fun inMade => freshMade o inMade present
  · intro r member
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr member)
  · intro x member ne
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨member, by simpa using ne⟩)
  · intro x member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inC, notO⟩ := Finset.mem_sdiff.mp old
      exact .inl ⟨inC, by simpa using notO⟩
    · exact .inr (List.mem_toFinset.mp new)

omit [DecidableEq sig.vars] in
variable (label) in
/-- **A refused firing is refused for a reason**: a shape, presence or freshness condition fails, or
the goal and the renamed head do not unify under the knowledge. -/
theorem resolve_refused_iff (C : Configuration (Term sig) O) (o : O) (c : Clause sig)
    (ρ : Equiv.Perm sig.vars) (made : List O) :
    ¬ (resolve o c ρ made).Valid (A sig) label C ↔
      ¬ (made.Nodup ∧ made.map label = c.body.map (rename ρ) ∧ o ∈ C.present ∧
        (∀ r ∈ made, r ∉ C.present)) ∨ ¬ Unifiable C.equations (rename ρ c.head) (label o) := by
  rw [resolve_valid_iff]
  constructor
  · intro refused
    by_cases shapes : made.Nodup ∧ made.map label = c.body.map (rename ρ) ∧ o ∈ C.present ∧
        (∀ r ∈ made, r ∉ C.present)
    · exact .inr fun unifiable =>
        refused ⟨shapes.1, shapes.2.1, shapes.2.2.1, shapes.2.2.2, unifiable⟩
    · exact .inl shapes
  · rintro (noShapes | noUnifier) ⟨nodup, outputs, present, freshMade, unifiable⟩
    · exact noShapes ⟨nodup, outputs, present, freshMade⟩
    · exact noUnifier unifiable

omit [DecidableEq sig.vars] in
variable (label) in
/-- **A refused firing leaves no residue**: no run begins with it, so the configuration stays as it
was, with its goal present and none of its body goals made. -/
theorem resolve_no_step {C : Configuration (Term sig) O} {o : O} {c : Clause sig}
    {ρ : Equiv.Perm sig.vars} {made : List O} (refused : ¬ (resolve o c ρ made).Valid (A sig) label C)
    (r : (firstOrder (A sig) label).Run C) :
    ∀ x ∈ r.word.head?, x.2 ≠ resolve o c ρ made := by
  intro x member
  cases r with
  | nil => simp [Interface.Step.Run.word] at member
  | cons f admitted rest =>
      simp only [Interface.Step.Run.word, List.head?_cons, Option.mem_def, Option.some.injEq] at member
      subst member
      intro same
      exact refused (same ▸ admitted)

#print axioms permSubst_trans
#print axioms rename_trans
#print axioms rename_symm_rename
#print axioms rename_rename_symm
#print axioms mem_termsVars
#print axioms mem_freeVars_rename
#print axioms Fresh.term
#print axioms exists_fresh
#print axioms unifiable_iff_consistent
#print axioms unifiable_nil_iff
#print axioms consistent_pair_iff
#print axioms resolve_problem
#print axioms resolve_result
#print axioms resolve_valid_iff
#print axioms principal_iff_mgu
#print axioms relevant_fixes
#print axioms resolve_sld_step
#print axioms resolve_commits
#print axioms resolve_refused_iff
#print axioms resolve_no_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution
