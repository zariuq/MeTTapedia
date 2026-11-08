import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UninterpretedVersions

/-!
# Substitution-threaded uninterpreted regions

`Expr.eval` uses one-way `Pat.matchUnder`: earlier variable values never
change. A two-way binding can instead instantiate variables inside earlier
values. `evalUnifying` extends the existing expression syntax with outcomes
carrying both a value recipe and the current substitution. Its `let` invokes
the existing finite-term most general unifier, then composes its substitution
into the current one. Final observation instantiates the recipe.

The accepted profile below contains data construction, two-way binding,
conditionals, failure and recursive calls with one uninterpreted argument.
Other existing expression forms are delegated to an explicit fallback; no
theorem here asserts that this is the entire canonical PeTTa interpreter.
Closed parameter frames and native/source lowering remain separate links.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UnifyingRegions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

abbrev Substitution := String → Atom
abbrev Outcome := Atom × Substitution
abbrev Fallback := Expr → Substitution → Multiset Outcome
abbrev SelfOracle := List Atom → Multiset Atom

def compose (after before : Substitution) : Substitution := fun x => substA after (before x)

mutual
theorem substA_compose (after before : Substitution) : ∀ a : Atom,
    substA after (substA before a) = substA (compose after before) a
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es => by rw [substA, substA, substL_compose, substA]

theorem substL_compose (after before : Substitution) : ∀ es : List Atom,
    substL after (substL before es) = substL (compose after before) es
  | [] => rfl
  | e :: es => by rw [substL, substL, substA_compose, substL_compose, substL]
end

def Clean (Γ : Decls) (σ : Substitution) : Prop := ∀ x, Uninterp Γ (σ x)

theorem clean_id (Γ : Decls) : Clean Γ Atom.var := fun _ => trivial

theorem Clean.compose {Γ : Decls} {after before : Substitution}
    (ha : Clean Γ after) (hb : Clean Γ before) : Clean Γ (compose after before) :=
  fun x => uninterp_substA ha (before x) (hb x)

/-- A state change is an instance by a clean substitution. -/
def Extends (Γ : Decls) (before after : Substitution) : Prop :=
  ∃ delta, Clean Γ delta ∧ after = compose delta before

theorem Extends.refl (Γ : Decls) (σ : Substitution) : Extends Γ σ σ := by
  refine ⟨Atom.var, clean_id Γ, ?_⟩
  funext x
  exact (substA_var_self (σ x)).symm

theorem Extends.trans {Γ : Decls} {σ τ υ : Substitution}
    (first : Extends Γ σ τ) (second : Extends Γ τ υ) : Extends Γ σ υ := by
  obtain ⟨a, ha, rfl⟩ := first
  obtain ⟨b, hb, rfl⟩ := second
  refine ⟨compose b a, hb.compose ha, ?_⟩
  funext x
  exact substA_compose b a (σ x)

/-- Two-way binding updates every earlier recipe through the composed MGU. -/
def bindPattern (σ : Substitution) (p : Pat) (value : Atom) : Option Substitution :=
  (UnifyAtoms.unify (substA σ p.toAtom) (substA σ value)).map
    fun theta => compose (UnifyAtoms.readBack theta) σ

theorem bindPattern_sound {Γ : Decls} {σ τ : Substitution} {p : Pat} {value : Atom}
    (clean : Clean Γ σ) (pattern : Uninterp Γ p.toAtom) (data : Uninterp Γ value)
    (bound : bindPattern σ p value = some τ) :
    Clean Γ τ ∧ Extends Γ σ τ ∧ substA τ p.toAtom = substA τ value := by
  unfold bindPattern at bound
  cases h : UnifyAtoms.unify (substA σ p.toAtom) (substA σ value) with
  | none => simp [h] at bound
  | some theta =>
      have state : compose (UnifyAtoms.readBack theta) σ = τ := by simpa [h] using bound
      subst τ
      have safe : Clean Γ (UnifyAtoms.readBack theta) :=
        UnifyAtoms.unify_uninterp h (uninterp_substA clean _ pattern)
          (uninterp_substA clean _ data)
      refine ⟨safe.compose clean, ⟨_, safe, rfl⟩, ?_⟩
      rw [← substA_compose, ← substA_compose]
      exact UnifyAtoms.unify_instance h

mutual
/-- Evaluate the existing syntax, retaining a recipe and its current
substitution. Unsupported region forms are supplied by `fallback`. -/
def evalUnifying (fallback : Fallback) (oracle : SelfOracle) :
    Expr → Substitution → Multiset Outcome
  | .var x, σ => {(.var x, σ)}
  | .const a, σ => {(a, σ)}
  | .ctor c args, σ => (evalAllUnifying fallback oracle args σ).map fun out =>
      (.expression (.symbol c :: out.1), out.2)
  | .self args, σ => (evalAllUnifying fallback oracle args σ).bind fun out =>
      (oracle (out.1.map (substA out.2))).map fun value => (value, out.2)
  | .letE p val body, σ => (evalUnifying fallback oracle val σ).bind fun out =>
      match bindPattern out.2 p out.1 with
      | none => 0
      | some τ => evalUnifying fallback oracle body τ
  | .ifE c t e, σ => (evalUnifying fallback oracle c σ).bind fun out =>
      if substA out.2 out.1 = truth then evalUnifying fallback oracle t out.2
      else evalUnifying fallback oracle e out.2
  | .empty, _ => 0
  | e, σ => fallback e σ

def evalAllUnifying (fallback : Fallback) (oracle : SelfOracle) :
    List Expr → Substitution → Multiset (List Atom × Substitution)
  | [], σ => {([], σ)}
  | e :: es, σ => (evalUnifying fallback oracle e σ).bind fun first =>
      (evalAllUnifying fallback oracle es first.2).map fun rest => (first.1 :: rest.1, rest.2)
end

/-- The all-uninterpreted region accepted in this slice. Recursive calls have
one argument; typed closed frames are not silently assumed to survive binds. -/
inductive Accepted (Γ : Decls) : Expr → Prop where
  | var (x : String) : Accepted Γ (.var x)
  | const (a : Atom) (clean : Uninterp Γ a) : Accepted Γ (.const a)
  | ctor {c : String} {args : List Expr} (head : Γ c = [])
      (parts : ∀ e ∈ args, Accepted Γ e) : Accepted Γ (.ctor c args)
  | self {arg : Expr} (argument : Accepted Γ arg) : Accepted Γ (.self [arg])
  | letE {p : Pat} {val body : Expr} (pattern : Uninterp Γ p.toAtom)
      (value : Accepted Γ val) (result : Accepted Γ body) : Accepted Γ (.letE p val body)
  | ifE {c t e : Expr} (condition : Accepted Γ c) (yes : Accepted Γ t) (no : Accepted Γ e) :
      Accepted Γ (.ifE c t e)
  | empty : Accepted Γ .empty

def OracleClean (Γ : Decls) (oracle : SelfOracle) : Prop :=
  ∀ v, Uninterp Γ v → ∀ r ∈ oracle [v], Uninterp Γ r

def Good (Γ : Decls) (initial : Substitution) (out : Outcome) : Prop :=
  Uninterp Γ out.1 ∧ Clean Γ out.2 ∧ Extends Γ initial out.2

def GoodList (Γ : Decls) (initial : Substitution) (out : List Atom × Substitution) : Prop :=
  (∀ a ∈ out.1, Uninterp Γ a) ∧ Clean Γ out.2 ∧ Extends Γ initial out.2

theorem evalAll_good {Γ : Decls} (fallback : Fallback) (oracle : SelfOracle)
    (es : List Expr)
    (each : ∀ e ∈ es, ∀ σ, Clean Γ σ → ∀ out ∈ evalUnifying fallback oracle e σ, Good Γ σ out) :
    ∀ σ, Clean Γ σ → ∀ out ∈ evalAllUnifying fallback oracle es σ, GoodList Γ σ out := by
  induction es with
  | nil =>
      intro σ clean out member
      have eq : out = ([], σ) := by simpa [evalAllUnifying] using member
      subst out
      exact ⟨by simp, clean, Extends.refl Γ σ⟩
  | cons e es ih =>
      intro σ clean out member
      simp only [evalAllUnifying, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨first, hf, rest, hr, rfl⟩ := member
      obtain ⟨data, cleanFirst, extendsFirst⟩ := each e (by simp) σ clean first hf
      obtain ⟨datas, cleanRest, extendsRest⟩ :=
        ih (fun a ha => each a (by simp [ha])) first.2 cleanFirst rest hr
      refine ⟨?_, cleanRest, extendsFirst.trans extendsRest⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact data
      · exact datas a ha

theorem accepted_good {Γ : Decls} (fallback : Fallback) (oracle : SelfOracle)
    (oracleClean : OracleClean Γ oracle) {e : Expr} (accepted : Accepted Γ e) :
    ∀ σ, Clean Γ σ → ∀ out ∈ evalUnifying fallback oracle e σ, Good Γ σ out := by
  induction accepted with
  | var x =>
      intro σ clean out member
      have eq : out = (.var x, σ) := by simpa [evalUnifying] using member
      subst out
      exact ⟨trivial, clean, Extends.refl Γ σ⟩
  | const a data =>
      intro σ clean out member
      have eq : out = (a, σ) := by simpa [evalUnifying] using member
      subst out
      exact ⟨data, clean, Extends.refl Γ σ⟩
  | @ctor c args head parts ih =>
      intro σ clean out member
      simp only [evalUnifying, Multiset.mem_map] at member
      obtain ⟨values, hv, rfl⟩ := member
      obtain ⟨data, cleanFinal, extension⟩ := evalAll_good fallback oracle args ih σ clean values hv
      refine ⟨UnifyAtoms.uninterp_of_all ?_, cleanFinal, extension⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact head
      · exact data a ha
  | @self arg argument ih =>
      intro σ clean out member
      simp only [evalUnifying, evalAllUnifying,
        Multiset.mem_bind, Multiset.mem_map, Multiset.mem_singleton] at member
      obtain ⟨values, hvalues, value, hv, rfl⟩ := member
      obtain ⟨first, hf, tail, htail, htailEq⟩ := hvalues
      subst tail
      subst values
      obtain ⟨data, cleanFinal, extension⟩ := ih σ clean first hf
      exact ⟨oracleClean _ (uninterp_substA cleanFinal _ data) value hv, cleanFinal, extension⟩
  | @letE p val body pattern value result ihv ihb =>
      intro σ clean out member
      simp only [evalUnifying, Multiset.mem_bind] at member
      obtain ⟨first, hf, member⟩ := member
      obtain ⟨data, cleanFirst, extendsFirst⟩ := ihv σ clean first hf
      cases bound : bindPattern first.2 p first.1 with
      | none => simp [bound] at member
      | some τ =>
          rw [bound] at member
          obtain ⟨cleanBound, extendsBound, _⟩ := bindPattern_sound cleanFirst pattern data bound
          obtain ⟨dataOut, cleanOut, extendsOut⟩ := ihb τ cleanBound out member
          exact ⟨dataOut, cleanOut, extendsFirst.trans (extendsBound.trans extendsOut)⟩
  | ifE condition yes no ihc iht ihe =>
      intro σ clean out member
      simp only [evalUnifying, Multiset.mem_bind] at member
      obtain ⟨first, hf, member⟩ := member
      obtain ⟨_, cleanFirst, extendsFirst⟩ := ihc σ clean first hf
      split at member
      · obtain ⟨data, cleanOut, extendsOut⟩ := iht first.2 cleanFirst out member
        exact ⟨data, cleanOut, extendsFirst.trans extendsOut⟩
      · obtain ⟨data, cleanOut, extendsOut⟩ := ihe first.2 cleanFirst out member
        exact ⟨data, cleanOut, extendsFirst.trans extendsOut⟩
  | empty =>
      intro σ clean out member
      exact False.elim (Multiset.notMem_zero out member)

theorem evalAll_length (fallback : Fallback) (oracle : SelfOracle) (es : List Expr) :
    ∀ σ out, out ∈ evalAllUnifying fallback oracle es σ → out.1.length = es.length := by
  induction es with
  | nil =>
      intro σ out member
      have eq : out = ([], σ) := by simpa [evalAllUnifying] using member
      subst out
      rfl
  | cons e es ih =>
      intro σ out member
      simp only [evalAllUnifying, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨first, _, rest, hr, rfl⟩ := member
      simp only [List.length_cons]
      rw [ih first.2 rest hr]

theorem evalAll_congr {Γ : Decls} (fallback : Fallback) (o o' : SelfOracle)
    (es : List Expr)
    (same : ∀ e ∈ es, ∀ σ, Clean Γ σ →
      evalUnifying fallback o e σ = evalUnifying fallback o' e σ)
    (sound : ∀ e ∈ es, ∀ σ, Clean Γ σ →
      ∀ out ∈ evalUnifying fallback o e σ, Good Γ σ out) :
    ∀ σ, Clean Γ σ → evalAllUnifying fallback o es σ = evalAllUnifying fallback o' es σ := by
  induction es with
  | nil => intro σ _; rfl
  | cons e es ih =>
      intro σ clean
      simp only [evalAllUnifying]
      rw [← same e (by simp) σ clean]
      apply Multiset.bind_congr
      intro first member
      have good := sound e (by simp) σ clean first member
      rw [ih (fun e he => same e (by simp [he]))
        (fun e he => sound e (by simp [he])) first.2 good.2.1]

/-- Oracles need agree only at the input boundary the accepted syntax uses. -/
def Agree (Γ : Decls) (o o' : SelfOracle) : Prop :=
  ∀ v, Uninterp Γ v → o [v] = o' [v]

theorem accepted_congr {Γ : Decls} (fallback : Fallback) (o o' : SelfOracle)
    (cleanOracle : OracleClean Γ o) (agree : Agree Γ o o') {e : Expr}
    (accepted : Accepted Γ e) :
    ∀ σ, Clean Γ σ → evalUnifying fallback o e σ = evalUnifying fallback o' e σ := by
  induction accepted with
  | var => intro σ _; rfl
  | const => intro σ _; rfl
  | @ctor c args head parts ih =>
      intro σ clean
      simp only [evalUnifying]
      rw [evalAll_congr fallback o o' args ih
        (fun e he => accepted_good fallback o cleanOracle (parts e he)) σ clean]
  | @self arg argument ih =>
      intro σ clean
      have sameAll := evalAll_congr fallback o o' [arg]
        (fun e he => by
          simp only [List.mem_singleton] at he
          subst e
          exact ih)
        (fun e he => by
          simp only [List.mem_singleton] at he
          subst e
          exact accepted_good fallback o cleanOracle argument) σ clean
      simp only [evalUnifying]
      rw [← sameAll]
      apply Multiset.bind_congr
      intro out member
      have good := evalAll_good fallback o [arg]
        (fun e he => by
          simp only [List.mem_singleton] at he
          subst e
          exact accepted_good fallback o cleanOracle argument) σ clean out member
      obtain ⟨v, shape⟩ := List.length_eq_one_iff.mp (evalAll_length fallback o [arg] σ out member)
      have data : Uninterp Γ v := good.1 v (by simp [shape])
      rw [shape]
      simp only [List.map_cons, List.map_nil]
      rw [agree _ (uninterp_substA good.2.1 v data)]
  | @letE p val body pattern value result ihv ihb =>
      intro σ clean
      simp only [evalUnifying]
      rw [← ihv σ clean]
      apply Multiset.bind_congr
      intro first member
      have good := accepted_good fallback o cleanOracle value σ clean first member
      cases bound : bindPattern first.2 p first.1 with
      | none => rfl
      | some τ =>
          exact ihb τ (bindPattern_sound good.2.1 pattern good.1 bound).1
  | ifE condition yes no ihc iht ihe =>
      intro σ clean
      simp only [evalUnifying]
      rw [← ihc σ clean]
      apply Multiset.bind_congr
      intro first member
      have good := accepted_good fallback o cleanOracle condition σ clean first member
      split
      · exact iht first.2 good.2.1
      · exact ihe first.2 good.2.1
  | empty => intro σ _; rfl

/-- The existing return analysis identifies the same argument recipe after
two-way binding; it does not incorrectly claim the argument's value stayed
unchanged. -/
theorem returns_argument {Γ : Decls} (fallback : Fallback) (oracle : SelfOracle)
    (parameter : String) {e : Expr} (returns : ReturnsPat (.var parameter) e) :
    Accepted Γ e → ∀ σ out, out ∈ evalUnifying fallback oracle e σ → out.1 = .var parameter := by
  induction returns with
  | refl =>
      intro _ σ out member
      have eq : out = (.var parameter, σ) := by simpa [evalUnifying] using member
      exact congrArg Prod.fst eq
  | letE returns ih =>
      intro accepted σ out member
      cases accepted with
      | letE _ _ body =>
          simp only [evalUnifying, Multiset.mem_bind] at member
          obtain ⟨first, _, member⟩ := member
          split at member
          · exact False.elim (Multiset.notMem_zero out member)
          · exact ih body _ out member
  | ifE rt re iht ihe =>
      intro accepted σ out member
      cases accepted with
      | ifE _ yes no =>
          simp only [evalUnifying, Multiset.mem_bind] at member
          obtain ⟨first, _, member⟩ := member
          split at member
          · exact iht yes first.2 out member
          · exact ihe no first.2 out member
  | empty =>
      intro _ σ out member
      exact False.elim (Multiset.notMem_zero out member)
  | caseE => intro accepted; cases accepted
  | matchE => intro accepted; cases accepted

def initial (parameter : String) (value : Atom) : Substitution :=
  Function.update Atom.var parameter value

theorem clean_initial {Γ : Decls} (parameter : String) {value : Atom}
    (clean : Uninterp Γ value) : Clean Γ (initial parameter value) := by
  intro x
  by_cases h : x = parameter
  · subst x
    simpa [initial] using clean
  · simp only [initial, Function.update_of_ne h]
    trivial

def observe (out : Outcome) : Atom := substA out.2 out.1

/-- The accepted one-parameter source body, whose internal two-way binds are
reflected in its final observed answer. -/
def body (fallback : Fallback) (parameter : String) (e : Expr) (oracle : SelfOracle) :
    List Atom → Multiset Atom
  | [value] => (evalUnifying fallback oracle e (initial parameter value)).map observe
  | _ => 0

theorem body_instance {Γ : Decls} (fallback : Fallback) (parameter : String)
    {e : Expr} (accepted : Accepted Γ e) (returns : ReturnsPat (.var parameter) e)
    (oracle : SelfOracle) (cleanOracle : OracleClean Γ oracle) {value : Atom}
    (cleanValue : Uninterp Γ value) :
    ∀ r ∈ body fallback parameter e oracle [value],
      ∃ delta : Substitution, r = substA delta value ∧ Clean Γ delta := by
  intro r member
  simp only [body, Multiset.mem_map] at member
  obtain ⟨out, member, rfl⟩ := member
  have good := accepted_good fallback oracle cleanOracle accepted
    (initial parameter value) (clean_initial parameter cleanValue) out member
  have recipe := returns_argument fallback oracle parameter returns accepted _ out member
  obtain ⟨delta, safe, extension⟩ := good.2.2
  refine ⟨delta, ?_, safe⟩
  simp only [observe, recipe, substA, extension, compose, initial, Function.update_self]

theorem unary_entry_iff {Γ : Decls} {grounded : String → Bool} {args : List Atom} :
    UnintEntry Γ grounded [] [] args ↔ ∃ value, args = [value] ∧ Uninterp Γ value := by
  constructor
  · rintro ⟨us, value, ws, rfl, _, pre, clean, post⟩
    cases pre
    cases post
    exact ⟨value, rfl, clean⟩
  · rintro ⟨value, rfl, clean⟩
    exact ⟨[], value, [], rfl, rfl, .nil, clean, .nil⟩

/-- The semantic hypotheses of the existing version theorem are derived
from syntactic admission and the existing return-pattern analysis. -/
theorem analyzed_hyps {Γ : Decls} (grounded : String → Bool) (fallback : Fallback)
    (parameter : String) {e : Expr} (accepted : Accepted Γ e)
    (returns : ReturnsPat (.var parameter) e) :
    UnintHyps Γ grounded (body fallback parameter e) (body fallback parameter e) [] [] where
  calls o o' agree cleanOracle args entry := by
    obtain ⟨value, rfl, cleanValue⟩ := unary_entry_iff.mp entry
    have clean : OracleClean Γ o := fun v hv => cleanOracle [v] (unary_entry_iff.mpr ⟨v, rfl, hv⟩)
    have same : Agree Γ o o' := fun v hv => agree [v] (unary_entry_iff.mpr ⟨v, rfl, hv⟩)
    simp only [body]
    rw [accepted_congr fallback o o' clean same accepted _ (clean_initial parameter cleanValue)]
  results o cleanOracle us value ws len entry r member := by
    have empty : us = [] := by simpa using len.symm
    subst us
    obtain ⟨v, shape, cleanValue⟩ := unary_entry_iff.mp entry
    have parts : value = v ∧ ws = [] := List.cons.inj shape
    rcases parts with ⟨rfl, rfl⟩
    have clean : OracleClean Γ o := fun v hv => cleanOracle [v] (unary_entry_iff.mpr ⟨v, rfl, hv⟩)
    exact body_instance fallback parameter accepted returns o clean cleanValue r member

/-- Every admitted source region has the protocol's answer bag at every
recursive fuel. The two-way binding effects are already in the source body. -/
theorem analyzed_version_eq_protocol {Γ : Decls} (functional : Functional Γ)
    (grounded : String → Bool) (fallback : Fallback) (parameter typeVariable : String)
    {e : Expr} (accepted : Accepted Γ e) (returns : ReturnsPat (.var parameter) e)
    (fuel : Nat) (value : Atom) (cleanValue : Uninterp Γ value) :
    protocolRun Γ grounded (body fallback parameter e)
        (arrow [.var typeVariable] (.var typeVariable)) fuel [value] =
      versionRun (body fallback parameter e) fuel [value] :=
  unint_version_eq_protocol functional typeVariable
    (analyzed_hyps grounded fallback parameter accepted returns) fuel [value]
    (unary_entry_iff.mpr ⟨value, rfl, cleanValue⟩)

namespace Controls

def noDecls : Decls := fun _ => []
def noFallback : Fallback := fun _ _ => 0
def noCalls : SelfOracle := fun _ => 0
def one : Atom := .grounded (.int 1)
def two : Atom := .grounded (.int 2)

def input : Atom := .expression [.symbol "pair", .var "left", .var "right"]
def pattern : Pat := .ctor "pair" [.var "first", .const one]
def bindingBody : Expr := .letE pattern (.var "argument") (.var "argument")

theorem pattern_clean : Uninterp noDecls pattern.toAtom := by
  simp [pattern, Pat.toAtom, Pat.toAtoms, one, Uninterp, Safe, SafeAll,
    substA, HeadFree, noDecls]

theorem binding_accepted : Accepted noDecls bindingBody :=
  .letE pattern_clean (.var "argument") (.var "argument")

theorem binding_returns : ReturnsPat (.var "argument") bindingBody := .letE .refl

theorem input_clean : Uninterp noDecls input := by
  simp [input, Uninterp, Safe, SafeAll, substA, HeadFree, noDecls]

/-- One-way matching rejects a variable-valued field against the constant. -/
theorem one_way_rejects : Pat.matchUnder [("argument", input)] pattern input = none := by
  decide +kernel

/-- Two-way binding instantiates the argument's old variable, and returning
the argument observes the new instance rather than its earlier value. -/
theorem two_way_instantiates :
    body noFallback "argument" bindingBody noCalls [input] =
      {.expression [.symbol "pair", .var "left", one]} := by
  cbv

theorem binding_protocol (fuel : Nat) (grounded : String → Bool) :
    protocolRun noDecls grounded (body noFallback "argument" bindingBody)
        (arrow [.var "t"] (.var "t")) fuel [input] =
      versionRun (body noFallback "argument" bindingBody) fuel [input] :=
  analyzed_version_eq_protocol (fun _ => by simp [noDecls]) grounded noFallback
    "argument" "t" binding_accepted binding_returns fuel input input_clean

def recursiveBody : Expr :=
  .ifE (.var "argument") (.var "argument")
    (.letE (.var "ignored") (.self [.const truth]) (.var "argument"))

theorem recursive_accepted : Accepted noDecls recursiveBody :=
  .ifE (.var "argument") (.var "argument")
    (.letE trivial (.self (.const truth trivial)) (.var "argument"))

theorem recursive_returns : ReturnsPat (.var "argument") recursiveBody :=
  .ifE .refl (.letE .refl)

theorem recursive_two_steps :
    versionRun (body noFallback "argument" recursiveBody) 2 [.grounded (.bool false)] =
      {.grounded (.bool false)} := by cbv

theorem recursive_protocol (fuel : Nat) (grounded : String → Bool) :
    protocolRun noDecls grounded (body noFallback "argument" recursiveBody)
        (arrow [.var "t"] (.var "t")) fuel [.grounded (.bool false)] =
      versionRun (body noFallback "argument" recursiveBody) fuel [.grounded (.bool false)] :=
  analyzed_version_eq_protocol (fun _ => by simp [noDecls]) grounded noFallback
    "argument" "t" recursive_accepted recursive_returns fuel (.grounded (.bool false)) trivial

def callAndReturn : Expr :=
  .letE (.var "ignored") (.self [.var "argument"]) (.var "argument")

/-- Distinct occurrences of the same callee answer remain distinct source
answers after binding and returning the argument. -/
theorem duplicate_callee_answers_preserved :
    body noFallback "argument" callAndReturn (fun _ => {one, one}) [two] = {two, two} := by
  cbv

theorem deduplicating_the_oracle_changes_answers :
    body noFallback "argument" callAndReturn (fun _ => {one, one}) [two] ≠
      body noFallback "argument" callAndReturn (fun _ => {one}) [two] := by
  intro same
  have counts := congrArg Multiset.card same
  cbv at counts

/-- Mere clean execution does not prove that the result is an instance of
the argument. The return-pattern analysis is necessary. -/
theorem arbitrary_result_not_instance :
    Accepted noDecls (.const one) ∧
      body noFallback "argument" (.const one) noCalls [two] = {one} ∧
      ¬ ∃ delta : Substitution, one = substA delta two := by
  refine ⟨.const one trivial, rfl, ?_⟩
  rintro ⟨delta, h⟩
  cases h

def declared : Decls := fun s => if s = "Known" then [.sym "Tagged"] else []

/-- Binding an open uninterpreted argument to a declared constructor is
outside the admitted clean-binding rule. -/
theorem interpreted_pattern_rejected :
    ¬ Accepted declared (.letE (.ctor "Known" []) (.var "argument") (.var "argument")) := by
  intro accepted
  cases accepted with
  | letE pattern _ _ =>
      simp [Pat.toAtom, Pat.toAtoms, Uninterp, Safe, SafeAll, substA,
        HeadFree, declared] at pattern

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UnifyingRegions
