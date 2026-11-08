import Mettapedia.Logic.ASP.Certificate
import Mettapedia.Logic.ASP.WeightStep

/-!
# Refutation certificates for programs with weight definitions

The C solver checks its refutations of a program with definitions (`asp_certificate_check_weighted`)
over its own numbering and completion; this module is that checker, with its soundness.

## Numbering and completion

A **falsum atom** (`Program.Falsum`, decided by `Program.falsum`) heads some rule, and every rule for
it has its negation in the body: the C reader gives every integrity constraint `:- B` and every
native weight constraint the rule `f :- B, not f` of one shared atom `f`. No stable model holds a
falsum atom (`DefProgram.Stable.not_falsum`), and no stable model satisfies the body of one of its
rules without the negated head (`Program.constraint_fails`). The completion is reduced by this.

* The variables (`DefProgram.varList`) are the atoms in the order of `DefProgram.atomList` (their
  last occurrences over the rules, then over the definitions), falsum atoms among them, then the
  distinct bodies of the rules whose head is no falsum atom and that are not unit bodies
  (`Program.bodyRules`), in the order of their last occurrence: `number_variables` in
  `asp_cdnl_v1.c`. A body shared with such a rule keeps its variable. A unit body, with exactly one
  literal, has no variable: its literal (`Body.lit`) stands for it.
* The completion (`DefProgram.completionNogoods`) takes the rules in order (`Program.ruleNogoods`):
  a rule of a falsum atom gives one nogood (`constraintNogood`), its positive atoms true and its
  other negated atoms false, in the rule's order; any other rule gives its head nogood, the literal
  of its body then `F p`, and its body's nogoods, none for a unit body. One support nogood per atom
  follows in atom order (`DefProgram.supportNogood`): `T a` alone for a falsum atom; for a
  definition's atom `T W` and `F W` beside its bodies, violated by no assignment, as the solver
  propagates the definition itself; otherwise `T a` and the complements of the literals of the
  bodies of its rules.

A binary integrity constraint is so one nogood of two literals, without a variable of its own, and
a rule `p :- a` is the one nogood `{T a, F p}`.

## Steps

A step (`WCertStep`) is an LRAT action, a loop-nogood addition, a Hall addition, a **weight
addition** `weight id clause d`, checked by arithmetic against the definition numbered `d`
(`DefProgram.weightStepOk`, `weightCheck` of `WeightStep`), or an **input** `input id clause`, the
clause of a constraint added to the program, accepted only by the checker over added constraints.

A loop step is accepted only for a set without definition atoms and without falsum atoms
(`DefProgram.loopClause`). A definition's atom has no rules; with the rules alone, the loop nogood
of a set holding it ignores the support the definition gives, and can refute a program that has a
stable model (`WeightStepControls`). The rules of a falsum atom have no body variables, so the loop
clause of a set holding it has no numbering. An external rule with a unit body contributes the
complement of its body's literal. A Hall step's at-least-one and exclusion rules are
rules of falsum atoms (`Program.isConstraintRule`).

The checker (`DefProgram.checkCert`) refuses an ill-formed program, as the C solver's setup does
(`DefProgram.wellFormedB`), starts from the numbered completion with identifiers `1, 2, …`
(`DefProgram.inputs`), applies the steps in order and accepts when the empty clause is live. Over no
definitions it is `Program.checkCert`, with the same numbering and inputs
(`DefProgram.checkCert_noDefs`).

## Soundness

For a stable model `S`, every live clause holds in the numbered assignment of `S`
(`DefProgram.certRun_holds`): the completion by the stable-model conditions, its falsum parts
because the facts of the definitions' atoms, which head no rule of a well-formed program, keep the
falsum atoms of the rules falsum (`DefProgram.falsum_given`), RUP additions by RUP
soundness, loop additions because `S` is a stable model of the rules with the facts of its
definition atoms and the set's loop nogood is the same there, Hall additions by counting in that
program, and weight additions by `weightCheck_sound`. **An accepted certificate means the program
has no stable model** (`DefProgram.checkCert_sound`).

## Added constraints

After a model the C solver's session may be given constraints `(pos, neg)`, each saying that no
stable model has every atom of `pos` true and every atom of `neg` false, and its search goes on. Each
enters the certificate as an input step whose clause is the constraint's: the complements of the
nogood `{T p | p ∈ pos} ∪ {F n | n ∈ neg}`, numbered (`DefProgram.inputClause`). The checker over
added constraints (`DefProgram.checkCertWith`, `asp_certificate_check_constrained`) accepts an input
step exactly when its clause has, as a set, the literals of the clause of an added constraint all of
whose atoms are atoms of the program (`DefProgram.inputStepOk`), and checks every other step as
`checkCert` does; with no constraint added it is `checkCert` (`DefProgram.checkCertWith_nil`). The
live clauses hold in the numbered assignment of every stable model meeting the added constraints:
**an accepted certificate means that no stable model meets them all**
(`DefProgram.checkCertWith_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Mettapedia.GSLT.Logic PropositionalFormula

universe u

variable {A : Type u}

/-- A step of a refutation certificate for a program with definitions. -/
inductive WCertStep
  /-- An LRAT action: a RUP addition or a deletion. -/
  | lrat (action : PropositionalLRATActions.Action)
  /-- Add `clause`, the loop clause of the atoms numbered `atoms` for the atom numbered `atom`. -/
  | loop (id : ℕ) (clause : Clause) (atoms : List ℕ) (atom : ℕ)
  /-- Add `clause` by Hall's condition over the at-least-one rules `groups` and the `cliques`. -/
  | hall (id : ℕ) (clause : Clause) (groups : List ℕ) (cliques : List (List ℕ))
  /-- Add `clause`, implied by the definition numbered `defn`. -/
  | weight (id : ℕ) (clause : Clause) (defn : ℕ)
  /-- Add `clause`, the clause of a constraint added to the program (`DefProgram.inputStepOk`). -/
  | input (id : ℕ) (clause : Clause)

namespace DefProgram

variable [DecidableEq A] (Q : DefProgram A)

/-! ## Numbering -/

/-- The variables in the C solver's order: atoms, then the distinct bodies of the rules whose head is
no falsum atom. -/
def varList : List (Var A) := (Q.atomList.map Var.atom ++ Q.rules.bodyRules.map fun r => Var.body r.body).dedup

/-- The number of a variable. -/
def index (x : Var A) : ℕ := Q.varList.idxOf x

/-- An assignment of the variables as an assignment of their numbers. -/
def encode (v : Valuation A) : ℕ → Bool := fun i => (Q.varList[i]?).elim false v

/-- A solver literal as a native literal over its variable number. -/
def nativeLit (l : Lit A) : Literal := CNF.Literal.toLRAT ⟨Q.index l.var, l.sign⟩

/-- The clause of a nogood: its literals each once, complemented and numbered. -/
def lratClause (lits : List (Lit A)) : Clause := lits.dedup.map fun l => Q.nativeLit l.compl

@[simp] theorem atom_mem_varList {a : A} : Var.atom a ∈ Q.varList ↔ a ∈ Q.atomList := by
  simp [varList]

/-- The body of a rule whose head is no falsum atom is a variable, unless it is a unit body. -/
theorem body_mem_varList {r : Rule A} (hr : r ∈ Q.rules) (hf : Q.rules.falsum r.head = false)
    (hu : ¬ r.body.IsUnit) : Var.body r.body ∈ Q.varList := by
  simp only [varList, List.mem_dedup, List.mem_append, List.mem_map, reduceCtorEq, and_false,
    exists_false, Var.body.injEq, false_or]
  exact ⟨r, (Q.rules.mem_bodyRules).mpr ⟨hr, (Q.rules.falsum_eq_false_iff).mp hf, hu⟩, rfl⟩

/-- The literal of the body of a rule whose head is no falsum atom is over a variable. -/
theorem lit_mem_varList {r : Rule A} (hr : r ∈ Q.rules) (hf : Q.rules.falsum r.head = false) :
    r.body.lit.var ∈ Q.varList := by
  by_cases hu : r.body.IsUnit
  · obtain ⟨a, same, ha⟩ := Body.lit_var_of_isUnit hu
    rw [same]
    rcases ha with ha | ha
    · exact (Q.atom_mem_varList).mpr (Q.pos_mem_atomList hr ha)
    · exact (Q.atom_mem_varList).mpr (Q.neg_mem_atomList hr ha)
  · rw [Body.lit_of_not_isUnit hu]
    exact Q.body_mem_varList hr hf hu

theorem encode_index (v : Valuation A) {x : Var A} (h : x ∈ Q.varList) : Q.encode v (Q.index x) = v x := by
  rw [encode, index, List.getElem?_idxOf h]
  rfl

theorem sat_nativeLit (v : Valuation A) {l : Lit A} (h : l.var ∈ Q.varList) :
    Literal.sat (Q.encode v) (Q.nativeLit l) = decide (l.Sat v) := by
  rw [nativeLit, CNF.Literal.sat_toLRAT]
  simp only [CNF.Literal.eval, Q.encode_index v h, Lit.Sat]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact decide_eq_true_iff.symm

/-- **The clause of a nogood holds exactly when the nogood is not violated.** -/
theorem sat_lratClause (v : Valuation A) {lits : List (Lit A)} (vars : ∀ l ∈ lits, l.var ∈ Q.varList) :
    Clause.sat (Q.encode v) (Q.lratClause lits) = true ↔ ∃ l ∈ lits, ¬ l.Sat v := by
  simp only [Clause.sat, lratClause, List.any_map, List.any_eq_true, List.mem_dedup, Function.comp]
  constructor
  · rintro ⟨l, hl, sat⟩
    rw [Q.sat_nativeLit v (l := l.compl) (vars l hl), decide_eq_true_eq, Lit.sat_compl] at sat
    exact ⟨l, hl, sat⟩
  · rintro ⟨l, hl, notSat⟩
    refine ⟨l, hl, ?_⟩
    rw [Q.sat_nativeLit v (l := l.compl) (vars l hl), decide_eq_true_eq, Lit.sat_compl]
    exact notSat

/-! ## The completion -/

/-- The support nogood of an atom: `T a` alone for a falsum atom; otherwise a true atom has a true
body among its rules, and its literals are `T a`, then the complement of the literal of the body of
each rule for `a`, in rule order. A definition's atom also has `F W` after `T W`, so no assignment
violates its nogood. -/
def supportNogood (a : A) : Nogood A :=
  if Q.rules.falsum a then ⟨[tAtom a], .support a⟩ else
    ⟨tAtom a :: ((if a ∈ Q.defAtoms then [fAtom a] else []) ++
      (Q.rules.filter fun r => r.head = a).map fun r => r.body.lit.compl), .support a⟩

/-- **The completion** as the C solver builds it: the nogoods of each rule in order, then the
support nogoods in atom order. -/
def completionNogoods : List (Nogood A) :=
  Q.rules.flatMap Q.rules.ruleNogoods ++ Q.atomList.map Q.supportNogood

/-- The numbered completion. -/
def completionLRAT : List Clause := Q.completionNogoods.map fun δ => Q.lratClause δ.lits

/-- The input clauses with identifiers `1, 2, …`. -/
def inputs : List (ℕ × Clause) := numberFrom 1 Q.completionLRAT

theorem completionNogoods_vars {δ : Nogood A} (h : δ ∈ Q.completionNogoods) : ∀ l ∈ δ.lits, l.var ∈ Q.varList := by
  simp only [completionNogoods, List.mem_append, List.mem_flatMap, List.mem_map] at h
  rcases h with ⟨r, hr, hδ⟩ | ⟨a, ha, rfl⟩
  · unfold Program.ruleNogoods at hδ
    by_cases hf : Q.rules.falsum r.head = true
    · rw [if_pos hf, List.mem_singleton] at hδ
      subst hδ
      intro l hl
      simp only [constraintNogood, List.mem_append, List.mem_map] at hl
      rcases hl with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
      · exact (Q.atom_mem_varList).mpr (Q.pos_mem_atomList hr hb)
      · exact (Q.atom_mem_varList).mpr (Q.neg_mem_atomList hr (Rule.mem_group.mp hb).1)
    rw [if_neg hf] at hδ
    rcases List.mem_cons.mp hδ with rfl | hδ
    · intro l hl
      simp only [headNogood, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Q.lit_mem_varList hr (Bool.eq_false_iff.mpr hf)
      · exact (Q.atom_mem_varList).mpr (Q.head_mem_atomList hr)
    by_cases hu : r.body.IsUnit
    · simp [bodyNogoods, hu] at hδ
    have body := Q.body_mem_varList hr (Bool.eq_false_iff.mpr hf) hu
    simp only [bodyNogoods, if_neg hu, List.mem_cons, List.mem_append, List.mem_map] at hδ
    rcases hδ with (rfl | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩
    · intro l hl
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hl
      rcases hl with rfl | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
      · exact body
      · exact (Q.atom_mem_varList).mpr (Q.pos_mem_atomList hr hb)
      · exact (Q.atom_mem_varList).mpr (Q.neg_mem_atomList hr hb)
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact body
      · exact (Q.atom_mem_varList).mpr (Q.pos_mem_atomList hr hb)
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact body
      · exact (Q.atom_mem_varList).mpr (Q.neg_mem_atomList hr hb)
  · intro l hl
    by_cases hf : Q.rules.falsum a = true
    · rw [supportNogood, if_pos hf, List.mem_singleton] at hl
      subst hl
      exact (Q.atom_mem_varList).mpr ha
    rw [supportNogood, if_neg hf] at hl
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hl
    rcases hl with rfl | hl | ⟨r, ⟨hr, rfl⟩, rfl⟩
    · exact (Q.atom_mem_varList).mpr ha
    · split_ifs at hl
      · rw [List.mem_singleton.mp hl]
        exact (Q.atom_mem_varList).mpr ha
      · cases hl
    · exact Q.lit_mem_varList hr (Bool.eq_false_iff.mpr hf)

omit [DecidableEq A] in
/-- A falsum atom of the rules is one of the rules with the facts of the definitions' atoms, which
head no rule. -/
theorem falsum_given (wf : Q.WellFormed) (S : Set A) {a : A} (h : Q.rules.Falsum a) : (Q.given S).Falsum a := by
  obtain ⟨⟨r, hr, rfl⟩, every⟩ := h
  refine ⟨⟨r, (Q.mem_given).mpr (.inl hr), rfl⟩, fun q hq hqh => ?_⟩
  rcases (Q.mem_given).mp hq with hq | ⟨d, hd, -, rfl⟩
  · exact every q hq hqh
  · exact absurd (hqh ▸ Q.atom_mem_defAtoms hd) (wf.noHead r hr)

variable {Q}

omit [DecidableEq A] in
/-- **No stable model holds a falsum atom of the rules.** -/
theorem Stable.not_falsum (wf : Q.WellFormed) {S : Set A} (stable : Q.Stable S) {a : A} (h : Q.rules.Falsum a) :
    a ∉ S :=
  (Q.given S).not_mem_of_falsum ((Q.given S).stable_supported stable.2) (Q.falsum_given wf S h)

/-- **A stable model violates no completion nogood.** -/
theorem completionNogood_ok (wf : Q.WellFormed) {S : Set A} (stable : Q.Stable S) {δ : Nogood A}
    (h : δ ∈ Q.completionNogoods) : ∃ l ∈ δ.lits, ¬ l.Sat (Program.canonical S) := by
  have correct : ∀ B : Body A, B.lit.Sat (Program.canonical S) ↔ B.Holds S S := Program.lit_sat_canonical S
  simp only [completionNogoods, List.mem_append, List.mem_flatMap, List.mem_map] at h
  rcases h with ⟨r, hr, hδ⟩ | ⟨a, ha, rfl⟩
  · unfold Program.ruleNogoods at hδ
    by_cases hf : Q.rules.falsum r.head = true
    · rw [if_pos hf, List.mem_singleton] at hδ
      subst hδ
      apply Nogood.not_violated_iff.mp
      rw [constraintNogood_violated, Program.canonical_atoms]
      rintro ⟨pos, group⟩
      exact (Q.given S).constraint_fails ((Q.given S).stable_supported stable.2) ((Q.mem_given).mpr (.inl hr))
        (Q.falsum_given wf S ((Q.rules.falsum_iff).mp hf))
        ⟨pos, fun b hb hbh => group b (Rule.mem_group.mpr ⟨hb, hbh⟩)⟩
    rw [if_neg hf] at hδ
    rcases List.mem_cons.mp hδ with rfl | hδ
    · apply Nogood.not_violated_iff.mp
      rw [Program.headNogood_violated, Program.canonical_atoms]
      rintro ⟨body, notHead⟩
      exact notHead (stable.rules_step_subset ⟨r, hr, rfl, (correct _).mp body⟩)
    · apply Nogood.not_violated_iff.mp
      refine (Program.bodyNogoods_ok_iff (Program.canonical S) r.body).mpr ?_ δ hδ
      rw [Program.canonical_atoms]
      exact correct _
  · apply Nogood.not_violated_iff.mp
    intro violated
    by_cases hf : Q.rules.falsum a = true
    · rw [supportNogood, if_pos hf] at violated
      have present := violated _ List.mem_cons_self
      rw [tAtom_sat, Program.canonical_atoms] at present
      exact stable.not_falsum wf ((Q.rules.falsum_iff).mp hf) present
    rw [supportNogood, if_neg hf] at violated
    simp only [Nogood.Violated, List.forall_mem_cons, List.forall_mem_append, tAtom_sat,
      Program.canonical_atoms, List.forall_mem_map, List.mem_filter, decide_eq_true_eq, Lit.sat_compl,
      and_imp] at violated
    obtain ⟨present, defLits, bodies⟩ := violated
    by_cases hdef : a ∈ Q.defAtoms
    · rw [if_pos hdef] at defLits
      exact (fAtom_sat _ a).mp (defLits _ List.mem_cons_self) (by simpa using present)
    · obtain ⟨r, hr, rfl, holds⟩ := stable.supported present hdef
      exact bodies r hr rfl ((correct _).mpr holds)

theorem inputs_holds (wf : Q.WellFormed) {S : Set A} (stable : Q.Stable S) :
    LiveHolds (Q.encode (Program.canonical S)) Q.inputs := by
  intro e he
  obtain ⟨δ, hδ, same⟩ := List.mem_map.mp (numberFrom_mem he)
  rw [← same]
  exact (Q.sat_lratClause _ (Q.completionNogoods_vars hδ)).mpr (completionNogood_ok wf stable hδ)

variable (Q)

/-! ## Steps -/

/-- The atom a variable number stands for, if it stands for an atom. -/
def atomOf (i : ℕ) : Option A :=
  match Q.varList[i]? with
  | some (.atom a) => some a
  | _ => none

/-- The atom a literal makes true, if it is a positive literal of an atom. -/
def posAtom : Literal → Option A
  | .pos i => Q.atomOf i
  | .neg _ => none

/-- The loop clause of the atoms numbered `atoms` for the atom numbered `atom`, over the rules;
`none` unless every number stands for an atom that is neither a definition's atom nor a falsum
atom, and `atom` is among them. -/
def loopClause (atoms : List ℕ) (atom : ℕ) : Option Clause :=
  if atoms.all (fun i => match Q.atomOf i with
      | some a => !decide (a ∈ Q.defAtoms) && !Q.rules.falsum a
      | none => false) && decide (atom ∈ atoms) then
    (Q.atomOf atom).map fun a => Q.lratClause (Q.rules.loopNogood (atoms.filterMap Q.atomOf).toFinset a).lits
  else none

/-- A loop step is well formed: its clause has exactly the literals of the recomputed loop clause. -/
def loopStepOk (clause : Clause) (atoms : List ℕ) (atom : ℕ) : Bool :=
  match Q.loopClause atoms atom with
  | some c => c.all (fun l => decide (l ∈ clause)) && clause.all fun l => decide (l ∈ c)
  | none => false

/-- A Hall step is well formed, as `Program.hallStepOk` checks it over the rules, in the numbering of
the program with definitions. -/
def hallStepOk (clause : Clause) (groups : List ℕ) (cliques : List (List ℕ)) : Bool :=
  match groups.mapM (Q.rules[·]?) with
  | none => false
  | some rules =>
    clause.all (fun l => (Q.posAtom l).isSome) &&
      cliques.all (fun cl => !cl.isEmpty && cl.all fun i => (Q.atomOf i).isSome) &&
      decide cliques.flatten.Nodup &&
      cliques.all (fun cl =>
        (cl.filterMap Q.atomOf).all fun a => (cl.filterMap Q.atomOf).all fun b => a == b || Q.rules.excludes a b) &&
      rules.all Q.rules.isAtLeastOne &&
      decide (rules.Pairwise fun r q => ∀ a ∈ r.group, a ∉ q.group) &&
      rules.all (fun r => r.group.all fun a =>
        decide (a ∈ clause.filterMap Q.posAtom) || cliques.any fun cl => decide (a ∈ cl.filterMap Q.atomOf)) &&
      decide (cliques.length < rules.length)

/-- **A weight step is well formed** (`weight_step_ok`): the definition numbered `d` exists and its
check accepts the clause over the program's numbering. -/
def weightStepOk (clause : Clause) (d : ℕ) : Bool :=
  match Q.defs[d]? with
  | some df => weightCheck (fun a => Q.index (.atom a)) Q.varList.length df clause
  | none => false

/-- **One step of the checker** on the live clauses. An input step is accepted only for a constraint
added to the program (`certStepWith`), and here none is. -/
def certStep (live : List (ℕ × Clause)) : WCertStep → Option (List (ℕ × Clause))
  | .lrat (.rup id clause hints) =>
    if (lookupClause live id).isSome then none
    else
      match hints.mapM (lookupClause live) with
      | some premises => if PropositionalLRATActions.rupCheck premises clause then some ((id, clause) :: live) else none
      | none => none
  | .lrat (.rat _ _) => none
  | .lrat (.delete ids) => some (live.filter fun e => !ids.contains e.1)
  | .loop id clause atoms atom =>
    if (lookupClause live id).isSome then none
    else if Q.loopStepOk clause atoms atom then some ((id, clause) :: live) else none
  | .hall id clause groups cliques =>
    if (lookupClause live id).isSome then none
    else if Q.hallStepOk clause groups cliques then some ((id, clause) :: live) else none
  | .weight id clause d =>
    if (lookupClause live id).isSome then none
    else if Q.weightStepOk clause d then some ((id, clause) :: live) else none
  | .input _ _ => none

/-- The live clauses after the steps, if every step is accepted. -/
def certRun (steps : List WCertStep) : Option (List (ℕ × Clause)) := steps.foldlM Q.certStep Q.inputs

/-- **The checker** (`asp_certificate_check_weighted`): the program is well formed, every step is
accepted and the empty clause is live. -/
def checkCert (steps : List WCertStep) : Bool :=
  Q.wellFormedB &&
    match Q.certRun steps with
    | some live => live.any fun e => e.2.isEmpty
    | none => false

/-! ## Soundness -/

theorem atomOf_mem {i : ℕ} {a : A} (h : Q.atomOf i = some a) : a ∈ Q.atomList := by
  unfold atomOf at h
  split at h
  · rename_i b hb
    cases h
    exact (Q.atom_mem_varList).mp (List.mem_of_getElem? hb)
  · cases h

theorem encode_of_atomOf (v : Valuation A) {i : ℕ} {a : A} (h : Q.atomOf i = some a) :
    Q.encode v i = v (.atom a) := by
  unfold atomOf at h
  split at h
  · rename_i b hb
    cases h
    rw [encode, hb]
    rfl
  · cases h

/-- Without definition atoms in the set, its loop nogood is the same in the rules with the facts of
the definitions' atoms. -/
theorem loopNogood_given {S : Set A} {U : Finset A} (noDef : ∀ b ∈ U, b ∉ Q.defAtoms) (a : A) :
    (Q.given S).loopNogood U a = Q.rules.loopNogood U a := by
  simp only [Program.loopNogood, Program.externalBodies, given, List.filter_append]
  have facts : ∀ F : List (WeightDef A), (∀ d ∈ F, d ∈ Q.defs) →
      (F.map WeightDef.fact).filter (fun r => decide (Program.ExternalFor U r)) = [] := by
    intro F hF
    apply List.filter_eq_nil_iff.mpr
    intro f hf external
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hf
    exact noDef _ (decide_eq_true_eq.mp external).1 (Q.atom_mem_defAtoms (hF d hd))
  rw [facts _ (fun d hd => (List.mem_filter.mp hd).1), List.append_nil]

/-- The literals of the loop nogood over the rules of a set without falsum atoms are over the
variables: every external rule has its head in the set, so its body is a variable. -/
theorem loopNogood_vars {U : Finset A} {a : A} (ha : a ∈ Q.atomList) (noFalsum : ∀ b ∈ U, Q.rules.falsum b = false) :
    ∀ l ∈ (Q.rules.loopNogood U a).lits, l.var ∈ Q.varList := by
  intro l hl
  simp only [Program.loopNogood, Program.externalBodies, List.mem_cons, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hl
  rcases hl with rfl | ⟨_, ⟨r, ⟨hr, external⟩, rfl⟩, rfl⟩
  · exact (Q.atom_mem_varList).mpr ha
  · exact Q.lit_mem_varList hr (noFalsum _ external.1)

variable {Q}

/-- **A loop clause holds in every stable model.** -/
theorem loopClause_sat {atoms : List ℕ} {atom : ℕ} {c : Clause} (h : Q.loopClause atoms atom = some c)
    {S : Set A} (stable : Q.Stable S) : Clause.sat (Q.encode (Program.canonical S)) c = true := by
  unfold loopClause at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at guard
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
    have member : a ∈ (atoms.filterMap Q.atomOf).toFinset :=
      List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨atom, guard.2, ha⟩)
    have allowed : ∀ b ∈ (atoms.filterMap Q.atomOf).toFinset, b ∉ Q.defAtoms ∧ Q.rules.falsum b = false := by
      intro b hb
      obtain ⟨i, hi, hib⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hb)
      have := guard.1 i hi
      rw [hib] at this
      simpa using this
    apply (Q.sat_lratClause _ (Q.loopNogood_vars (Q.atomOf_mem ha) fun b hb => (allowed b hb).2)).mpr
    obtain ⟨admissible, correct, stable'⟩ := (Q.given S).stable_canonical stable.2
    rw [← Q.loopNogood_given fun b hb => (allowed b hb).1]
    exact (Q.given S).loopNogood_entailed _ member _ admissible correct stable'
  · cases h

theorem loopStepOk_sat {clause : Clause} {atoms : List ℕ} {atom : ℕ} (h : Q.loopStepOk clause atoms atom = true)
    {S : Set A} (stable : Q.Stable S) : Clause.sat (Q.encode (Program.canonical S)) clause = true := by
  unfold loopStepOk at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨l, hl, sat⟩ := List.any_eq_true.mp (loopClause_sat hc stable)
    exact List.any_eq_true.mpr ⟨l, h.1 l hl, sat⟩
  · cases h

omit [DecidableEq A] in
/-- A constraint rule of the rules stays one with the facts of the definitions' atoms, which head no
rule. -/
theorem constraintRule_given (wf : Q.WellFormed) (S : Set A) {r : Rule A} (h : Q.rules.ConstraintRule r) :
    (Q.given S).ConstraintRule r := by
  obtain ⟨hr, hf⟩ := (Q.rules.constraintRule_iff).mp h
  exact ((Q.given S).constraintRule_iff).mpr ⟨(Q.mem_given).mpr (.inl hr), Q.falsum_given wf S hf⟩

/-- **A Hall clause holds in every stable model**: the counting step in the rules with the facts of
the definitions' atoms. -/
theorem hallStepOk_sat (wf : Q.WellFormed) {clause : Clause} {groups : List ℕ} {cliques : List (List ℕ)}
    (h : Q.hallStepOk clause groups cliques = true) {S : Set A} (stable : Q.Stable S) :
    Clause.sat (Q.encode (Program.canonical S)) clause = true := by
  unfold hallStepOk at h
  split at h
  · cases h
  rename_i rules hrules
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hclique⟩, hgroups⟩, hdisj⟩, hcover⟩, hcard⟩ := h
  obtain ⟨a, ha, haM⟩ := (Q.given S).hall_step_sound stable.2 (Finset.univ : Finset (Fin rules.length))
    (fun i => rules[i]) (Finset.univ : Finset (Fin cliques.length))
    (fun k => {a | a ∈ cliques[k].filterMap Q.atomOf}) {a | a ∈ clause.filterMap Q.posAtom}
    (fun i _ => by
      obtain ⟨cr, pos⟩ := Q.rules.atLeastOne_of_isAtLeastOne
        (Q.rules.mem_of_mapM_getElem? hrules _ (List.getElem_mem _)) (hgroups _ (List.getElem_mem _))
      exact ⟨constraintRule_given wf S cr, pos⟩)
    (by
      intro i _ j _ hij a hai haih ⟨haj, hajh⟩
      have pairwise := List.pairwise_iff_getElem.mp hdisj
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with lt | gt
      · exact pairwise i j i.2 j.2 lt a (Rule.mem_group.mpr ⟨hai, haih⟩) (Rule.mem_group.mpr ⟨haj, hajh⟩)
      · exact pairwise j i j.2 i.2 gt a (Rule.mem_group.mpr ⟨haj, hajh⟩) (Rule.mem_group.mpr ⟨hai, haih⟩))
    (by
      intro k _ a ha b hb hab
      obtain ⟨r, cr, shape, neg⟩ := Q.rules.exclusion_of_excludes ((hclique _ (List.getElem_mem k.2) a ha b hb).resolve_left hab)
      exact ⟨r, constraintRule_given wf S cr, shape, neg⟩)
    (by
      intro i _ a ha hah
      rcases hcover _ (List.getElem_mem _) a (Rule.mem_group.mpr ⟨ha, hah⟩) with hE | ⟨cl, hcl, hacl⟩
      · exact Or.inl hE
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcl
        exact Or.inr ⟨⟨k, hk⟩, Finset.mem_univ _, hacl⟩)
    (by simpa using hcard)
  obtain ⟨l, hl, hpos⟩ := List.mem_filterMap.mp ha
  refine List.any_eq_true.mpr ⟨l, hl, ?_⟩
  cases l with
  | pos i =>
    simpa [Literal.sat, Q.encode_of_atomOf _ hpos, Program.canonical] using haM
  | neg i => cases hpos

/-- **A weight clause holds in every stable model**: the stable model satisfies the definition. -/
theorem weightStepOk_sat {clause : Clause} {d : ℕ} (h : Q.weightStepOk clause d = true)
    {S : Set A} (stable : Q.Stable S) : Clause.sat (Q.encode (Program.canonical S)) clause = true := by
  unfold weightStepOk at h
  split at h
  · rename_i df hdf
    have mem : df ∈ Q.defs := List.mem_of_getElem? hdf
    apply weightCheck_sound _ h
    have atomValue : ∀ b ∈ Q.atomList,
        Q.encode (Program.canonical S) (Q.index (.atom b)) = Program.canonical S (.atom b) := fun b hb =>
      Q.encode_index _ ((Q.atom_mem_varList).mpr hb)
    have weight : numWeight (fun a => Q.index (.atom a)) (Q.encode (Program.canonical S)) df.terms =
        weightIn df.terms S S := by
      unfold numWeight weightIn
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [numValue, atomValue _ (Q.termAtom_mem_atomList mem ht), WTerm.value]
      obtain ⟨l, w⟩ := t
      cases l with
      | pos b => by_cases hb : b ∈ S <;> simp [hb, Program.canonical, WLit.atom, WLit.isPos, WLit.Holds]
      | neg b => by_cases hb : b ∈ S <;> simp [hb, Program.canonical, WLit.atom, WLit.isPos, WLit.Holds]
    rw [atomValue _ (Q.defAtom_mem_atomList mem), weight]
    simpa [Program.canonical, WeightDef.Holds] using stable.1 df mem
  · cases h

/-- **Every step keeps the live clauses true in every stable model.** -/
theorem certStep_holds (wf : Q.WellFormed) {S : Set A} (stable : Q.Stable S) {live live' : List (ℕ × Clause)}
    {st : WCertStep} (holds : LiveHolds (Q.encode (Program.canonical S)) live) (h : Q.certStep live st = some live') :
    LiveHolds (Q.encode (Program.canonical S)) live' := by
  cases st with
  | lrat action =>
    cases action with
    | rup id clause hints =>
      simp only [certStep] at h
      split at h
      · cases h
      · split at h
        · rename_i premises hpremises
          split at h
          · rename_i accepted
            cases h
            rintro e (_ | ⟨_, he⟩)
            · apply PropositionalLRATActions.rupCheck_sound accepted
              intro c hc
              obtain ⟨e', he', rfl⟩ := mapM_lookupClause_mem hpremises c hc
              exact holds e' he'
            · exact holds e he
          · cases h
        · cases h
    | rat _ _ => simp [certStep] at h
    | delete ids =>
      simp only [certStep, Option.some.injEq] at h
      subst h
      exact fun e he => holds e (List.mem_filter.mp he).1
  | loop id clause atoms atom =>
    simp only [certStep] at h
    split at h
    · cases h
    · split at h
      · rename_i ok
        cases h
        rintro e (_ | ⟨_, he⟩)
        · exact loopStepOk_sat ok stable
        · exact holds e he
      · cases h
  | hall id clause groups cliques =>
    simp only [certStep] at h
    split at h
    · cases h
    · split at h
      · rename_i ok
        cases h
        rintro e (_ | ⟨_, he⟩)
        · exact hallStepOk_sat wf ok stable
        · exact holds e he
      · cases h
  | weight id clause d =>
    simp only [certStep] at h
    split at h
    · cases h
    · split at h
      · rename_i ok
        cases h
        rintro e (_ | ⟨_, he⟩)
        · exact weightStepOk_sat ok stable
        · exact holds e he
      · cases h
  | input _ _ => simp [certStep] at h

theorem foldlM_certStep_holds (wf : Q.WellFormed) {S : Set A} (stable : Q.Stable S) :
    ∀ (steps : List WCertStep) {live live' : List (ℕ × Clause)}, LiveHolds (Q.encode (Program.canonical S)) live →
      steps.foldlM Q.certStep live = some live' → LiveHolds (Q.encode (Program.canonical S)) live'
  | [], _, _, holds, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ holds
  | st :: steps, live, live', holds, h => by
    simp only [List.foldlM_cons] at h
    cases hst : Q.certStep live st with
    | none => simp [hst] at h
    | some next =>
      simp only [hst, Option.bind_eq_bind, Option.bind_some] at h
      exact foldlM_certStep_holds wf stable steps (certStep_holds wf stable holds hst) h

/-- **Every live clause holds in every stable model.** -/
theorem certRun_holds (wf : Q.WellFormed) {steps : List WCertStep} {live : List (ℕ × Clause)}
    (h : Q.certRun steps = some live) {S : Set A} (stable : Q.Stable S) :
    LiveHolds (Q.encode (Program.canonical S)) live :=
  foldlM_certStep_holds wf stable steps (inputs_holds wf stable) h

/-- **An accepted certificate means the program with definitions has no stable model.** -/
theorem checkCert_sound {steps : List WCertStep} (accepted : Q.checkCert steps = true) (S : Set A) :
    ¬ Q.Stable S := by
  intro stable
  unfold checkCert at accepted
  rw [Bool.and_eq_true] at accepted
  obtain ⟨wellFormed, accepted⟩ := accepted
  split at accepted
  · rename_i live hlive
    obtain ⟨e, he, empty⟩ := List.any_eq_true.mp accepted
    have := certRun_holds (Q.wellFormed_of_wellFormedB wellFormed) hlive stable e he
    rw [List.isEmpty_iff.mp empty] at this
    cases this
  · cases accepted

/-! ## Added constraints

The clause of a constraint `(pos, neg)` has `-(n + 1)` for each atom of `pos` numbered `n` and
`n + 1` for each atom of `neg`, in the C solver's literals. An input clause holds in the numbered
assignment of every set meeting the added constraints, stable or not (`inputStepOk_sat`). -/

omit [DecidableEq A] in
/-- The nogood of an added constraint `(pos, neg)`: its positive atoms true, then its negative atoms
false. -/
def addedLits (c : List A × List A) : List (Lit A) := c.1.map tAtom ++ c.2.map fAtom

variable (Q)

/-- The clause of an added constraint, numbered. -/
def inputClause (c : List A × List A) : Clause := Q.lratClause (addedLits c)

/-- An input step is well formed: its clause has exactly the literals of the clause of an added
constraint over atoms of the program. -/
def inputStepOk (extra : List (List A × List A)) (clause : Clause) : Bool :=
  extra.any fun c => (c.1 ++ c.2).all (fun a => decide (a ∈ Q.atomList)) &&
    (Q.inputClause c).all (fun l => decide (l ∈ clause)) && clause.all fun l => decide (l ∈ Q.inputClause c)

/-- **One step of the checker over added constraints**: an input step joins the live clauses when
its clause is that of an added constraint; any other step is a step of `certStep`. -/
def certStepWith (extra : List (List A × List A)) (live : List (ℕ × Clause)) :
    WCertStep → Option (List (ℕ × Clause))
  | .input id clause =>
    if (lookupClause live id).isSome then none
    else if Q.inputStepOk extra clause then some ((id, clause) :: live) else none
  | st => Q.certStep live st

/-- The live clauses after the steps over added constraints, if every step is accepted. -/
def certRunWith (extra : List (List A × List A)) (steps : List WCertStep) : Option (List (ℕ × Clause)) :=
  steps.foldlM (Q.certStepWith extra) Q.inputs

/-- **The checker over added constraints** (`asp_certificate_check_constrained`): the program is
well formed, every step is accepted and the empty clause is live. -/
def checkCertWith (extra : List (List A × List A)) (steps : List WCertStep) : Bool :=
  Q.wellFormedB &&
    match Q.certRunWith extra steps with
    | some live => live.any fun e => e.2.isEmpty
    | none => false

theorem certStepWith_nil : Q.certStepWith [] = Q.certStep := by
  funext live st
  cases st with
  | input id clause => simp [certStepWith, certStep, inputStepOk]
  | _ => rfl

theorem certRunWith_nil (steps : List WCertStep) : Q.certRunWith [] steps = Q.certRun steps := by
  rw [certRunWith, certRun, certStepWith_nil]

/-- **With no constraint added the checker is `checkCert`.** -/
theorem checkCertWith_nil (steps : List WCertStep) : Q.checkCertWith [] steps = Q.checkCert steps := by
  rw [checkCertWith, checkCert, certRunWith_nil]

variable {Q}

/-- **An input clause holds in the numbered assignment of every set meeting the added
constraints.** -/
theorem inputStepOk_sat {extra : List (List A × List A)} {clause : Clause} (h : Q.inputStepOk extra clause = true)
    {S : Set A} (meets : ∀ c ∈ extra, ¬ ((∀ p ∈ c.1, p ∈ S) ∧ ∀ n ∈ c.2, n ∉ S)) :
    Clause.sat (Q.encode (Program.canonical S)) clause = true := by
  obtain ⟨c, hc, ok⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨known, sub⟩, -⟩ := ok
  have vars : ∀ l ∈ addedLits c, l.var ∈ Q.varList := by
    intro l hl
    simp only [addedLits, List.mem_append, List.mem_map] at hl
    rcases hl with ⟨p, hp, rfl⟩ | ⟨n, hn, rfl⟩
    · exact (Q.atom_mem_varList).mpr (known p (List.mem_append_left _ hp))
    · exact (Q.atom_mem_varList).mpr (known n (List.mem_append_right _ hn))
  have sat : Clause.sat (Q.encode (Program.canonical S)) (Q.inputClause c) = true := by
    apply (Q.sat_lratClause _ vars).mpr
    by_contra all
    simp only [not_exists, not_and, not_not] at all
    refine meets c hc ⟨fun p hp => ?_, fun n hn => ?_⟩
    · have := all (tAtom p) (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
      rwa [tAtom_sat, Program.canonical_atoms] at this
    · have := all (fAtom n) (List.mem_append_right _ (List.mem_map.mpr ⟨n, hn, rfl⟩))
      rwa [fAtom_sat, Program.canonical_atoms] at this
  obtain ⟨l, hl, lSat⟩ := List.any_eq_true.mp sat
  exact List.any_eq_true.mpr ⟨l, sub l hl, lSat⟩

/-- **Every step over added constraints keeps the live clauses true in every stable model meeting
them.** -/
theorem certStepWith_holds (wf : Q.WellFormed) {extra : List (List A × List A)} {S : Set A} (stable : Q.Stable S)
    (meets : ∀ c ∈ extra, ¬ ((∀ p ∈ c.1, p ∈ S) ∧ ∀ n ∈ c.2, n ∉ S)) {live live' : List (ℕ × Clause)}
    {st : WCertStep} (holds : LiveHolds (Q.encode (Program.canonical S)) live)
    (h : Q.certStepWith extra live st = some live') : LiveHolds (Q.encode (Program.canonical S)) live' := by
  cases st with
  | input id clause =>
    simp only [certStepWith] at h
    split at h
    · cases h
    · split at h
      · rename_i ok
        cases h
        rintro e (_ | ⟨_, he⟩)
        · exact inputStepOk_sat ok meets
        · exact holds e he
      · cases h
  | lrat action => exact certStep_holds (st := .lrat action) wf stable holds h
  | loop id clause atoms atom => exact certStep_holds (st := .loop id clause atoms atom) wf stable holds h
  | hall id clause groups cliques => exact certStep_holds (st := .hall id clause groups cliques) wf stable holds h
  | weight id clause d => exact certStep_holds (st := .weight id clause d) wf stable holds h

theorem foldlM_certStepWith_holds (wf : Q.WellFormed) {extra : List (List A × List A)} {S : Set A}
    (stable : Q.Stable S) (meets : ∀ c ∈ extra, ¬ ((∀ p ∈ c.1, p ∈ S) ∧ ∀ n ∈ c.2, n ∉ S)) :
    ∀ (steps : List WCertStep) {live live' : List (ℕ × Clause)}, LiveHolds (Q.encode (Program.canonical S)) live →
      steps.foldlM (Q.certStepWith extra) live = some live' → LiveHolds (Q.encode (Program.canonical S)) live'
  | [], _, _, holds, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ holds
  | st :: steps, live, live', holds, h => by
    simp only [List.foldlM_cons] at h
    cases hst : Q.certStepWith extra live st with
    | none => simp [hst] at h
    | some next =>
      simp only [hst, Option.bind_eq_bind, Option.bind_some] at h
      exact foldlM_certStepWith_holds wf stable meets steps (certStepWith_holds wf stable meets holds hst) h

/-- **Every live clause over added constraints holds in every stable model meeting them.** -/
theorem certRunWith_holds (wf : Q.WellFormed) {extra : List (List A × List A)} {steps : List WCertStep}
    {live : List (ℕ × Clause)} (h : Q.certRunWith extra steps = some live) {S : Set A} (stable : Q.Stable S)
    (meets : ∀ c ∈ extra, ¬ ((∀ p ∈ c.1, p ∈ S) ∧ ∀ n ∈ c.2, n ∉ S)) :
    LiveHolds (Q.encode (Program.canonical S)) live :=
  foldlM_certStepWith_holds wf stable meets steps (inputs_holds wf stable) h

/-- **An accepted certificate over added constraints means that no stable model of the program with
definitions meets every added constraint.** -/
theorem checkCertWith_sound {extra : List (List A × List A)} {steps : List WCertStep}
    (accepted : Q.checkCertWith extra steps = true) (S : Set A) :
    ¬ (Q.Stable S ∧ ∀ c ∈ extra, ¬ ((∀ p ∈ c.1, p ∈ S) ∧ ∀ n ∈ c.2, n ∉ S)) := by
  rintro ⟨stable, meets⟩
  unfold checkCertWith at accepted
  rw [Bool.and_eq_true] at accepted
  obtain ⟨wellFormed, accepted⟩ := accepted
  split at accepted
  · rename_i live hlive
    obtain ⟨e, he, empty⟩ := List.any_eq_true.mp accepted
    have := certRunWith_holds (Q.wellFormed_of_wellFormedB wellFormed) hlive stable meets e he
    rw [List.isEmpty_iff.mp empty] at this
    cases this
  · cases accepted

/-! ## Programs without definitions

The C solver checks the refutation of a program without definitions with the same checker:
`asp_certificate_check` is `asp_certificate_check_weighted` with no definitions. Over no definitions
the numbering, the completion and the inputs are those of `Program` (`varList_noDefs`,
`completionNogoods_noDefs`, `inputs_noDefs`), and a certificate without weight steps is accepted
exactly when `Program.checkCert` accepts it (`checkCert_noDefs`). -/

section NoDefs

variable (P : Program A)

theorem atomList_noDefs : (⟨P, []⟩ : DefProgram A).atomList = P.allAtoms := by
  simp [atomList, Program.allAtoms]

theorem varList_noDefs : (⟨P, []⟩ : DefProgram A).varList = P.varList := by
  rw [varList, atomList_noDefs]
  rfl

theorem index_noDefs (x : Var A) : (⟨P, []⟩ : DefProgram A).index x = P.index x := by
  rw [index, varList_noDefs]
  rfl

theorem lratClause_noDefs (lits : List (Lit A)) : (⟨P, []⟩ : DefProgram A).lratClause lits = P.lratClause lits := by
  simp only [lratClause, Program.lratClause, nativeLit, Program.nativeLit, index_noDefs]

theorem supportNogood_noDefs (a : A) : (⟨P, []⟩ : DefProgram A).supportNogood a = P.supportNogood a := by
  simp [supportNogood, Program.supportNogood, defAtoms]

theorem completionNogoods_noDefs : (⟨P, []⟩ : DefProgram A).completionNogoods = P.completionNogoods := by
  rw [completionNogoods, Program.completionNogoods, atomList_noDefs]
  exact congrArg _ (List.map_congr_left fun a _ => supportNogood_noDefs P a)

theorem inputs_noDefs : (⟨P, []⟩ : DefProgram A).inputs = P.inputs := by
  simp only [inputs, Program.inputs, completionLRAT, Program.completionLRAT, completionNogoods_noDefs,
    lratClause_noDefs]

theorem atomOf_noDefs (i : ℕ) : (⟨P, []⟩ : DefProgram A).atomOf i = P.atomOf i := by
  rw [atomOf, Program.atomOf, varList_noDefs]
  rfl

theorem posAtom_noDefs (l : Literal) : (⟨P, []⟩ : DefProgram A).posAtom l = P.posAtom l := by
  cases l <;> simp [posAtom, Program.posAtom, atomOf_noDefs]

theorem loopClause_noDefs (atoms : List ℕ) (atom : ℕ) :
    (⟨P, []⟩ : DefProgram A).loopClause atoms atom = P.loopClause atoms atom := by
  simp only [loopClause, Program.loopClause, atomOf_noDefs, lratClause_noDefs]
  rfl

theorem hallStepOk_noDefs (clause : Clause) (groups : List ℕ) (cliques : List (List ℕ)) :
    (⟨P, []⟩ : DefProgram A).hallStepOk clause groups cliques = P.hallStepOk clause groups cliques := by
  simp only [hallStepOk, Program.hallStepOk, atomOf_noDefs, posAtom_noDefs]
  rfl

end NoDefs

end DefProgram

/-- A certificate step without weight steps as a step of the checker with definitions. -/
def CertStep.toW : CertStep → WCertStep
  | .lrat action => .lrat action
  | .loop id clause atoms atom => .loop id clause atoms atom
  | .hall id clause groups cliques => .hall id clause groups cliques

namespace DefProgram

variable [DecidableEq A] (P : Program A)

theorem certStep_noDefs (live : List (ℕ × Clause)) (st : CertStep) :
    (⟨P, []⟩ : DefProgram A).certStep live st.toW = P.certStep live st := by
  cases st with
  | lrat action => cases action <;> rfl
  | loop id clause atoms atom =>
    simp only [CertStep.toW, certStep, Program.certStep, loopStepOk, Program.loopStepOk, loopClause_noDefs]
    rfl
  | hall id clause groups cliques =>
    simp only [CertStep.toW, certStep, Program.certStep, hallStepOk_noDefs]

theorem foldlM_certStep_noDefs : ∀ (steps : List CertStep) (live : List (ℕ × Clause)),
    (steps.map CertStep.toW).foldlM (⟨P, []⟩ : DefProgram A).certStep live = steps.foldlM P.certStep live
  | [], _ => rfl
  | st :: steps, live => by
    simp only [List.map_cons, List.foldlM_cons, certStep_noDefs]
    cases P.certStep live st with
    | none => rfl
    | some next => exact foldlM_certStep_noDefs steps next

/-- **Over no definitions the checker is `Program.checkCert`.** -/
theorem checkCert_noDefs (steps : List CertStep) :
    (⟨P, []⟩ : DefProgram A).checkCert (steps.map CertStep.toW) = P.checkCert steps := by
  have wf : (⟨P, []⟩ : DefProgram A).wellFormedB = true := by
    simp [wellFormedB, acyclicB, defAtoms]
  rw [checkCert, Program.checkCert, wf, Bool.true_and, certRun, Program.certRun, inputs_noDefs,
    foldlM_certStep_noDefs]
  rfl

end DefProgram

end Mettapedia.Logic.ASP
