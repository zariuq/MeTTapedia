import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol

/-!
# Trusted versions of typed relations

A typed relation runs its protocol at every call, its calls to itself
included. A **trusted version** runs the equations with the calls to itself
entering the version directly, skipping the protocol (`versionRun`); a
checked call runs the protocol once and enters the version. This module
proves that the version's answer bag is the protocol's, multiplicity
included, for every relation whose equations an analysis of the kind
CeTTa's contract analysis performs accepts.

* **Entry facts at metatype names.** The guard is
  `get-type(V, T) *-> true ; get-metatype(V, T)`. At a formal that
  `get-metatype` can return, `Expression`, `Symbol`, `Grounded` or `Variable`
  (`MetaName`), the guard can succeed with no answer of the type relation.
  So an entry fact at a metatype name says only that the guard succeeds once,
  and at any other closed type that the type relation types the value once
  (`Holds`). A fact of either kind discharges its guard
  (`Holds.guardCount`); only a fact of the second kind inverts a constructor
  or types a construction.
* **The version theorem** (`version_eq_protocol`): when every argument meeting
  the entry facts passes the argument guards once, the equations call
  themselves only with arguments meeting the entry facts, and every answer
  meets the result's fact whenever the calls to itself do, the protocol's run
  and the version's run agree at every fuel on arguments meeting the entry
  facts. A checked call then has the same answers through either
  (`checked_call_eq`), since under functional declarations an argument list
  that passes the guards meets the entry facts (`entryFacts_of_argCount`).
* **The analysis** (`Accepted`) reads facts from patterns (`PatFact`: a
  variable takes its parameter's fact; an application of a constructor in the
  class, at a closed named type that is not a metatype name, gives each
  checked fixed field its instance), types right-hand sides (`HasType`:
  literals by the relation, constructions by the class from parts typed at
  types that are not metatype names, calls to itself by the result type,
  addition by `Number`), and checks that every call to itself meets the
  formals (`CallsOK`). Its rules are sound (`PatFact.sound`, `HasType.sound`),
  so an accepted relation's version is its protocol
  (`accepted_version_eq_protocol`).

The fragment: one closed row with guarded parameters and a guarded result;
equations with linear patterns; right-hand sides of variables, constants,
data, calls to itself and addition. Controls: the fold `lsum` over lists of
numbers is accepted (`Controls.lsum_accepted`), and its version is its
protocol; at the formal `Expression` the constructor `(C $s)` gives `$s` no
fact, and the run that inverted it anyway answers where the protocol does not
(`Controls.metatype_inversion_differs`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Facts at metatype names -/

/-- The names `get-metatype` returns. -/
def MetaName (T : Ty Empty) : Prop :=
  T = .sym "Expression" ∨ T = .sym "Symbol" ∨ T = .sym "Grounded" ∨ T = .sym "Variable"

instance (T : Ty Empty) : Decidable (MetaName T) := by
  unfold MetaName
  infer_instance

theorem metaName_metatype (grounded : String → Bool) (v : Atom) :
    MetaName (.sym (metatype grounded v)) := by
  cases v with
  | symbol s => by_cases h : grounded s <;> simp [metatype, MetaName, h]
  | var _ => simp [metatype, MetaName]
  | grounded _ => simp [metatype, MetaName]
  | expression _ => simp [metatype, MetaName]

section Facts

variable (Γ : Decls) (grounded : String → Bool)

/-- **An entry fact at a closed type**: at a metatype name, the guard succeeds
once; at any other type, the type relation types the value once. -/
def Holds (v : Atom) (T : Ty Empty) : Prop :=
  if MetaName T then guardCount (info Γ v) T (metatype grounded v) = 1
  else count (info Γ v) T = 1

variable {Γ grounded}

/-- Away from the metatype names the guard is the relation. -/
theorem guardCount_of_not_meta {T : Ty Empty} (h : ¬ MetaName T) (v : Atom) :
    guardCount (info Γ v) T (metatype grounded v) = count (info Γ v) T :=
  guardCount_of_ne _ _ _ fun same => h (same ▸ metaName_metatype grounded v)

/-- **A fact discharges its guard.** -/
theorem Holds.guardCount {v : Atom} {T : Ty Empty} (h : Holds Γ grounded v T) :
    TypedCalls.guardCount (info Γ v) T (metatype grounded v) = 1 := by
  unfold Holds at h
  split_ifs at h with hm
  · exact h
  · rw [guardCount_of_not_meta hm]
    exact h

/-- A value the relation types once meets the fact of its type. -/
theorem Holds.of_count {v : Atom} {T : Ty Empty} (h : count (info Γ v) T = 1) :
    Holds Γ grounded v T := by
  unfold Holds
  split_ifs
  · unfold TypedCalls.guardCount
    rw [if_neg (by omega), h]
  · exact h

/-- Away from the metatype names a fact is the relation's. -/
theorem Holds.count {v : Atom} {T : Ty Empty} (h : Holds Γ grounded v T) (hm : ¬ MetaName T) :
    TypedCalls.count (info Γ v) T = 1 := by
  unfold Holds at h
  rwa [if_neg hm] at h

/-- Under functional declarations, a guard that succeeds meets the fact. -/
theorem Holds.of_guardCount (hΓ : Functional Γ) {v : Atom} {T : Ty Empty}
    (h : TypedCalls.guardCount (info Γ v) T (metatype grounded v) ≠ 0) : Holds Γ grounded v T := by
  unfold Holds
  split_ifs with hm
  · unfold TypedCalls.guardCount at h ⊢
    have := count_le_one hΓ v T
    split_ifs at h ⊢ with h0 h1 <;> omega
  · rw [guardCount_of_not_meta hm] at h
    have := count_le_one hΓ v T
    omega

end Facts

/-! ## The version theorem -/

section Versions

variable (Γ : Decls) (grounded : String → Bool)

/-- A relation's run with the protocol at every call, its calls to itself
included. -/
noncomputable def protocolRun (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (row : Ty String) : ℕ → List Atom → Multiset Atom
  | 0, _ => 0
  | n + 1, vs => chainCall Γ (metatype grounded) (body (protocolRun body row n)) row vs

/-- **The trusted version**: its calls to itself skip the protocol. -/
def versionRun (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom) :
    ℕ → List Atom → Multiset Atom
  | 0, _ => 0
  | n + 1, vs => body (versionRun body n) vs

/-- The entry facts of a closed row's parameters. -/
def EntryFacts (As : List (Ty Empty)) (vs : List Atom) : Prop :=
  List.Forall₂ (fun A v => Holds Γ grounded v A) As vs

variable {Γ grounded}

/-- **The entry facts make every argument guard succeed exactly once.** -/
theorem argCount_of_entryFacts : ∀ {As : List (Ty Empty)} {vs : List Atom},
    EntryFacts Γ grounded As vs → argCount Γ (metatype grounded) As vs = 1
  | [], [], _ => rfl
  | A :: As, v :: vs, .cons hA hAs => by
      simp only [argCount]
      rw [argCount_of_entryFacts hAs, mul_one]
      split_ifs
      · exact hA.guardCount
      · rfl

/-- Under functional declarations, arguments that pass the guards of a row whose
parameters are all guarded meet the entry facts. -/
theorem entryFacts_of_argCount (hΓ : Functional Γ) :
    ∀ {As : List (Ty Empty)} {vs : List Atom}, (∀ A ∈ As, demand A.lift = .guarded) →
      argCount Γ (metatype grounded) As vs ≠ 0 → EntryFacts Γ grounded As vs
  | [], [], _, _ => .nil
  | A :: As, v :: vs, guarded, h => by
      simp only [argCount, guarded A (by simp), if_true] at h
      refine .cons (Holds.of_guardCount hΓ fun h0 => h (by rw [h0, zero_mul])) ?_
      exact entryFacts_of_argCount hΓ (fun B hB => guarded B (by simp [hB]))
        fun h0 => h (by rw [h0, mul_zero])
  | [], _ :: _, _, h => (h rfl).elim
  | _ :: _, [], _, h => by simp [argCount] at h

/-- The hypotheses of the version theorem, for a closed row `(-> A₁ … Aₖ R)` and
equations `body` reading the calls to themselves through an oracle. -/
structure VersionHyps (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (As : List (Ty Empty)) (R : Ty Empty) : Prop where
  /-- The result is guarded. -/
  resultGuarded : ResultGuarded R.lift
  /-- The equations call themselves only with arguments meeting the entry facts:
  two oracles that agree there, and answer there what the result's fact
  allows, give the same answers. -/
  calls : ∀ o o' : List Atom → Multiset Atom,
    (∀ ws, EntryFacts Γ grounded As ws → o ws = o' ws) →
    (∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R) →
    ∀ vs, EntryFacts Γ grounded As vs → body o vs = body o' vs
  /-- Every answer meets the result's fact when the calls to itself do. -/
  results : ∀ o : List Atom → Multiset Atom,
    (∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R) →
    ∀ vs, EntryFacts Γ grounded As vs → ∀ r ∈ body o vs, Holds Γ grounded r R

theorem version_results {body : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty} (h : VersionHyps (Γ := Γ) (grounded := grounded) body As R) :
    ∀ n vs, EntryFacts Γ grounded As vs → ∀ r ∈ versionRun body n vs, Holds Γ grounded r R
  | 0, _, _, r, hr => absurd hr (Multiset.notMem_zero r)
  | n + 1, vs, hvs, r, hr => h.results _ (version_results h n) vs hvs r hr

/-- **The version is the protocol**: on arguments meeting the entry facts, the
run whose calls to themselves skip the protocol has, at every fuel, exactly
the answers of the run whose every call runs it. -/
theorem version_eq_protocol {body : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty} (h : VersionHyps (Γ := Γ) (grounded := grounded) body As R) :
    ∀ n vs, EntryFacts Γ grounded As vs →
      protocolRun Γ grounded body (arrow (As.map Ty.lift) R.lift) n vs = versionRun body n vs
  | 0, _, _ => rfl
  | n + 1, vs, hvs => by
      simp only [protocolRun, versionRun]
      rw [chainCall_closed, argCount_of_entryFacts hvs, one_nsmul]
      simp only [if_pos h.resultGuarded]
      rw [h.calls _ _ (version_eq_protocol h n) (fun ws hws r hr => by
          rw [version_eq_protocol h n ws hws] at hr
          exact version_results h n ws hws r hr) vs hvs]
      refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
      · rw [(h.results _ (version_results h n) vs hvs r hr).guardCount, one_nsmul]
      · rw [Multiset.bind_singleton, Multiset.map_id']

/-- **A checked call has the same answers through the version**: the protocol
runs once at the entry, and its arguments, when they pass, meet the entry
facts. -/
theorem checked_call_eq (hΓ : Functional Γ)
    {body : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty} (guarded : ∀ A ∈ As, demand A.lift = .guarded)
    (h : VersionHyps (Γ := Γ) (grounded := grounded) body As R) (n : ℕ) (vs : List Atom) :
    chainCall Γ (metatype grounded) (body (protocolRun Γ grounded body (arrow (As.map Ty.lift) R.lift) n))
        (arrow (As.map Ty.lift) R.lift) vs =
      chainCall Γ (metatype grounded) (body (versionRun body n)) (arrow (As.map Ty.lift) R.lift) vs := by
  rw [chainCall_closed, chainCall_closed]
  by_cases h0 : argCount Γ (metatype grounded) As vs = 0
  · rw [h0, zero_nsmul, zero_nsmul]
  · have hvs := entryFacts_of_argCount hΓ guarded h0
    rw [h.calls _ _ (version_eq_protocol h n) (fun ws hws r hr => by
      rw [version_eq_protocol h n ws hws] at hr
      exact version_results h n ws hws r hr) vs hvs]

end Versions

/-! ## Equations the analysis reads -/

/-- Patterns of an equation's parameters: variables, constants matched by
equality, and applications of a symbol to patterns. -/
inductive Pat where
  | var (x : String)
  | const (a : Atom)
  | ctor (c : String) (args : List Pat)

/-- Right-hand sides: variables, constants, data built by a symbol, the
relation's calls to itself, and addition, which answers a number. -/
inductive Expr where
  | var (x : String)
  | const (a : Atom)
  | ctor (c : String) (args : List Expr)
  | self (args : List Expr)
  | add (a b : Expr)

namespace Pat

mutual
/-- The variables of a pattern, in order. -/
def vars : Pat → List String
  | .var x => [x]
  | .const _ => []
  | .ctor _ ps => varsAll ps

/-- The variables of a list of patterns. -/
def varsAll : List Pat → List String
  | [] => []
  | p :: ps => vars p ++ varsAll ps
end

mutual
/-- Matching a value: the bindings of the pattern's variables. -/
def «match» : Pat → Atom → Option (List (String × Atom))
  | .var x, v => some [(x, v)]
  | .const a, v => if v = a then some [] else none
  | .ctor c ps, .expression (.symbol c' :: vs) => if c = c' then matchAll ps vs else none
  | .ctor _ _, _ => none

/-- Matching a list of values. -/
def matchAll : List Pat → List Atom → Option (List (String × Atom))
  | [], [] => some []
  | p :: ps, v :: vs =>
      match «match» p v, matchAll ps vs with
      | some ρ, some ρ' => some (ρ ++ ρ')
      | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none
end

mutual
/-- The bindings of a match bind the pattern's variables. -/
theorem match_keys : ∀ (p : Pat) (v : Atom) (ρ : List (String × Atom)), «match» p v = some ρ →
    ρ.map Prod.fst = vars p
  | .var x, v, ρ, h => by
      simp only [«match», Option.some.injEq] at h
      subst h
      rfl
  | .const a, v, ρ, h => by
      simp only [«match»] at h
      split_ifs at h
      cases h
      rfl
  | .ctor c ps, .expression (.symbol c' :: vs), ρ, h => by
      simp only [«match»] at h
      split_ifs at h
      exact matchAll_keys ps vs ρ h
  | .ctor _ _, .symbol _, _, h => by simp [«match»] at h
  | .ctor _ _, .var _, _, h => by simp [«match»] at h
  | .ctor _ _, .grounded _, _, h => by simp [«match»] at h
  | .ctor _ _, .expression [], _, h => by simp [«match»] at h
  | .ctor _ _, .expression (.var _ :: _), _, h => by simp [«match»] at h
  | .ctor _ _, .expression (.grounded _ :: _), _, h => by simp [«match»] at h
  | .ctor _ _, .expression (.expression _ :: _), _, h => by simp [«match»] at h

theorem matchAll_keys : ∀ (ps : List Pat) (vs : List Atom) (ρ : List (String × Atom)),
    matchAll ps vs = some ρ → ρ.map Prod.fst = varsAll ps
  | [], [], ρ, h => by
      simp only [matchAll, Option.some.injEq] at h
      subst h
      rfl
  | p :: ps, v :: vs, ρ, h => by
      simp only [matchAll] at h
      split at h
      · next ρ₁ ρ₂ h₁ h₂ =>
          simp only [Option.some.injEq] at h
          subst h
          rw [List.map_append, match_keys p v ρ₁ h₁, matchAll_keys ps vs ρ₂ h₂]
          rfl
      · cases h
  | [], _ :: _, _, h => by simp [matchAll] at h
  | _ :: _, [], _, h => by simp [matchAll] at h
end

end Pat

/-- The value of addition. -/
def plus : Atom → Atom → Multiset Atom
  | .grounded (.int m), .grounded (.int n) => {.grounded (.int (m + n))}
  | _, _ => 0

namespace Expr

mutual
/-- Evaluation, with the relation's calls to itself through the oracle `o`. -/
def eval (o : List Atom → Multiset Atom) (ρ : List (String × Atom)) : Expr → Multiset Atom
  | .var x => match ρ.lookup x with
    | some v => {v}
    | none => 0
  | .const a => {a}
  | .ctor c args => (evalAll o ρ args).map fun vs => .expression (.symbol c :: vs)
  | .self args => (evalAll o ρ args).bind o
  | .add a b => (eval o ρ a).bind fun x => (eval o ρ b).bind fun y => plus x y

/-- Evaluation of a list: one value list per choice of the values. -/
def evalAll (o : List Atom → Multiset Atom) (ρ : List (String × Atom)) :
    List Expr → Multiset (List Atom)
  | [] => {[]}
  | e :: es => (eval o ρ e).bind fun v => (evalAll o ρ es).map (v :: ·)
end

end Expr

/-- An equation: patterns for the parameters and a right-hand side. -/
structure Equation where
  pats : List Pat
  rhs : Expr

/-- The equations of a relation, read with the calls to itself through `o`: every
equation whose patterns match contributes its answers. -/
def equationsBody (eqs : List Equation) (o : List Atom → Multiset Atom) (vs : List Atom) :
    Multiset Atom :=
  (eqs : Multiset Equation).bind fun eq =>
    match Pat.matchAll eq.pats vs with
    | some ρ => eq.rhs.eval o ρ
    | none => 0

/-! ## Matching, positionally -/

namespace Pat

theorem matchAll_length : ∀ (ps : List Pat) (vs : List Atom) (ρ : List (String × Atom)),
    matchAll ps vs = some ρ → ps.length = vs.length
  | [], [], _, _ => rfl
  | p :: ps, v :: vs, ρ, h => by
      simp only [matchAll] at h
      split at h
      · next ρ₁ ρ₂ _ h₂ => simp [matchAll_length ps vs ρ₂ h₂]
      · cases h
  | [], _ :: _, _, h => by simp [matchAll] at h
  | _ :: _, [], _, h => by simp [matchAll] at h

theorem vars_sublist_varsAll {p : Pat} : ∀ {ps : List Pat}, p ∈ ps → (vars p).Sublist (varsAll ps)
  | q :: qs, h => by
      rw [varsAll]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.sublist_append_left _ _
      · exact (vars_sublist_varsAll h).trans (List.sublist_append_right _ _)

theorem vars_subset_varsAll {p : Pat} {ps : List Pat} (h : p ∈ ps) : vars p ⊆ varsAll ps :=
  (vars_sublist_varsAll h).subset

/-- **A binding of a field's variable comes from the field's own match**, when
the patterns are linear. -/
theorem field_binding {β : Type} {x : String} {w : Atom} :
    ∀ (Bs : List β) (ps : List Pat) (vs : List Atom) (ρ : List (String × Atom)),
      matchAll ps vs = some ρ → (varsAll ps).Nodup → ∀ (B : β) (p : Pat), (B, p) ∈ List.zip Bs ps →
      x ∈ vars p → (x, w) ∈ ρ →
      ∃ v ρ', (B, v) ∈ List.zip Bs vs ∧ «match» p v = some ρ' ∧ (x, w) ∈ ρ'
  | B₀ :: Bs, p₀ :: ps, v₀ :: vs, ρ, h, nodup, B, p, hB, hx, hw => by
      simp only [matchAll] at h
      split at h
      · next ρ₀ ρ₁ h₀ h₁ =>
          simp only [Option.some.injEq] at h
          subst h
          rw [varsAll, List.nodup_append] at nodup
          rw [List.zip_cons_cons, List.mem_cons] at hB
          have keys₀ := match_keys p₀ v₀ ρ₀ h₀
          have keys₁ := matchAll_keys ps vs ρ₁ h₁
          rcases hB with same | hB
          · simp only [Prod.mk.injEq] at same
            obtain ⟨rfl, rfl⟩ := same
            rcases List.mem_append.mp hw with hw | hw
            · exact ⟨v₀, ρ₀, by simp, h₀, hw⟩
            · have : x ∈ varsAll ps := keys₁ ▸ List.mem_map_of_mem (f := Prod.fst) hw
              exact absurd rfl (nodup.2.2 x hx x this)
          · have hp : p ∈ ps := (List.of_mem_zip hB).2
            rcases List.mem_append.mp hw with hw | hw
            · have : x ∈ vars p₀ := keys₀ ▸ List.mem_map_of_mem (f := Prod.fst) hw
              exact absurd rfl (nodup.2.2 x this x (vars_subset_varsAll hp hx))
            · obtain ⟨v, ρ', hv, hm, hw'⟩ := field_binding Bs ps vs ρ₁ h₁ nodup.2.1 B p hB hx hw
              exact ⟨v, ρ', by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hv, hm, hw'⟩
      · cases h
  | [], _, _, _, _, _, _, _, hB, _, _ => by simp at hB
  | _ :: _, [], _, _, _, _, _, _, hB, _, _ => by simp at hB
  | _ :: _, _ :: _, [], _, h, _, _, _, _, _, _ => by simp [matchAll] at h

end Pat

theorem forall₂_zip {α γ : Type} {P : α → γ → Prop} :
    ∀ {As : List α} {vs : List γ}, List.Forall₂ P As vs → ∀ a v, (a, v) ∈ List.zip As vs → P a v
  | [], [], .nil, _, _, h => by simp at h
  | _ :: _, _ :: _, .cons hp hps, a, v, h => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with same | h
      · simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        exact hp
      · exact forall₂_zip hps a v h

theorem zip_of_forall₂ {α β γ : Type} {P : β → γ → Prop} :
    ∀ {es : List β} {vs : List γ}, List.Forall₂ P es vs → ∀ (Bs : List α) (B : α) (v : γ),
      (B, v) ∈ List.zip Bs vs → ∃ e, (B, e) ∈ List.zip Bs es ∧ P e v
  | [], [], .nil, _, _, _, h => by simp at h
  | e :: es, v' :: vs, .cons hp hps, B₀ :: Bs, B, v, h => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with same | h
      · simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        exact ⟨e, by simp, hp⟩
      · obtain ⟨e', he', hp'⟩ := zip_of_forall₂ hps Bs B v h
        exact ⟨e', by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ he', hp'⟩
  | _ :: _, _ :: _, .cons _ _, [], _, _, h => by simp at h

namespace Expr

theorem evalAll_mem (o : List Atom → Multiset Atom) (ρ : List (String × Atom)) :
    ∀ (es : List Expr) (vs : List Atom), vs ∈ evalAll o ρ es →
      List.Forall₂ (fun e v => v ∈ eval o ρ e) es vs
  | [], vs, h => by
      simp only [evalAll, Multiset.mem_singleton] at h
      subst h
      exact .nil
  | e :: es, vs, h => by
      simp only [evalAll, Multiset.mem_bind, Multiset.mem_map] at h
      obtain ⟨v, hv, vs', hvs', rfl⟩ := h
      exact .cons hv (evalAll_mem o ρ es vs' hvs')

theorem evalAll_congr {o o' : List Atom → Multiset Atom} {ρ : List (String × Atom)} :
    ∀ (es : List Expr), (∀ e ∈ es, eval o ρ e = eval o' ρ e) → evalAll o ρ es = evalAll o' ρ es
  | [], _ => rfl
  | e :: es, h => by
      simp only [evalAll]
      rw [h e (by simp), evalAll_congr es fun e' he' => h e' (by simp [he'])]

end Expr

/-! ## The analysis -/

section Analysis

variable (Γ : Decls)

/-- **The facts the analysis reads from a pattern** at a parameter of closed
type `T` (`contract_invert`): a variable has the parameter's fact; an
application of a constructor in the class, at a closed named type that is
not a metatype name, gives each checked fixed field the instance of its type
under the match of the result. -/
inductive PatFact : Pat → Ty Empty → String → Ty Empty → Prop
  | var (x : String) (T : Ty Empty) : PatFact (.var x) T x T
  | ctor {c : String} {Bs : List (Ty String)} {R : Ty String} {ps : List Pat} {T : Ty Empty}
      {σ : String → Ty Empty} {x : String} {U : Ty Empty} {B : Ty String} {p : Pat}
      (row : Γ c = [arrow Bs R]) (cls : Constructor Bs R) (len : ps.length = Bs.length)
      (notMeta : ¬ MetaName T) (named : Named T) (hmatch : R.bind σ = T)
      (field : (B, p) ∈ List.zip Bs ps) (checked : ¬ Unchecked B) (fixed : ¬ FreeField R B)
      (inner : PatFact p (B.bind σ) x U) : PatFact (.ctor c ps) T x U

/-- **The types the analysis gives right-hand sides**, under facts `Φ` for the
pattern variables and the relation's closed result type `R`: a variable its
fact; a constant the type the relation gives it; a construction the result of
a constructor in the class, at an instance its parts fix, each checked fixed
part typed at a type that is not a metatype name
(`contract_constructed_type`); a call to itself the result type; an addition
`Number`. -/
inductive HasType (Φ : String → Ty Empty → Prop) (R : Ty Empty) : Expr → Ty Empty → Prop
  | var {x : String} {U : Ty Empty} : Φ x U → HasType Φ R (.var x) U
  | const {a : Atom} {T : Ty Empty} : count (info Γ a) T = 1 → HasType Φ R (.const a) T
  | ctor {c : String} {Bs : List (Ty String)} {R' : Ty String} {args : List Expr}
      {σ : String → Ty Empty} (row : Γ c = [arrow Bs R']) (cls : Constructor Bs R')
      (len : args.length = Bs.length)
      (notMeta : ∀ q ∈ List.zip Bs args, ¬ Unchecked q.1 → ¬ FreeField R' q.1 →
        ¬ MetaName (q.1.bind σ))
      (parts : ∀ q ∈ List.zip Bs args, ¬ Unchecked q.1 → ¬ FreeField R' q.1 →
        HasType Φ R q.2 (q.1.bind σ)) :
      HasType Φ R (.ctor c args) (R'.bind σ)
  | self {args : List Expr} : HasType Φ R (.self args) R
  | add {a b : Expr} : HasType Φ R (.add a b) (.sym "Number")

/-- **Every call of the relation to itself meets the formals** (`contract_self_call`). -/
inductive CallsOK (Φ : String → Ty Empty → Prop) (R : Ty Empty) (As : List (Ty Empty)) :
    Expr → Prop
  | var {x : String} : CallsOK Φ R As (.var x)
  | const {a : Atom} : CallsOK Φ R As (.const a)
  | ctor {c : String} {args : List Expr} : (∀ e ∈ args, CallsOK Φ R As e) →
      CallsOK Φ R As (.ctor c args)
  | self {args : List Expr} : (∀ e ∈ args, CallsOK Φ R As e) →
      List.Forall₂ (fun A e => HasType Γ Φ R e A) As args → CallsOK Φ R As (.self args)
  | add {a b : Expr} : CallsOK Φ R As a → CallsOK Φ R As b → CallsOK Φ R As (.add a b)

/-- The facts of an equation's pattern variables. -/
def eqFacts (As : List (Ty Empty)) (eq : Equation) (x : String) (U : Ty Empty) : Prop :=
  ∃ A p, (A, p) ∈ List.zip As eq.pats ∧ PatFact Γ p A x U

/-- **An equation the analysis accepts** for the closed row `(-> A₁ … Aₖ R)`. -/
structure Accepted (As : List (Ty Empty)) (R : Ty Empty) (eq : Equation) : Prop where
  linear : (Pat.varsAll eq.pats).Nodup
  len : eq.pats.length = As.length
  calls : CallsOK Γ (eqFacts Γ As eq) R As eq.rhs
  result : HasType Γ (eqFacts Γ As eq) R eq.rhs R

end Analysis

/-! ## Soundness of the analysis -/

section Soundness

variable {Γ : Decls} {grounded : String → Bool}

theorem PatFact.mem_vars {p : Pat} {T : Ty Empty} {x : String} {U : Ty Empty}
    (h : PatFact Γ p T x U) : x ∈ Pat.vars p := by
  induction h with
  | var x T => simp [Pat.vars]
  | ctor _ _ _ _ _ _ field _ _ _ ih =>
      rw [Pat.vars]
      exact Pat.vars_subset_varsAll (List.of_mem_zip field).2 ih

/-- **The facts read from a pattern hold** of the bindings of a value that meets
the parameter's fact. -/
theorem PatFact.sound (hΓ : Functional Γ) {p : Pat} {T : Ty Empty} {x : String} {U : Ty Empty}
    (h : PatFact Γ p T x U) :
    ∀ {v : Atom} {ρ : List (String × Atom)} {w : Atom}, (Pat.vars p).Nodup →
      Pat.match p v = some ρ → Holds Γ grounded v T → (x, w) ∈ ρ → Holds Γ grounded w U := by
  induction h with
  | var x T =>
      intro v ρ w _ hm hv hw
      simp only [Pat.match, Option.some.injEq] at hm
      subst hm
      simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hw
      subst hw
      exact hv
  | @ctor c Bs R ps T σ x U B p row cls len notMeta named hmatch field checked fixed inner ih =>
      intro v ρ w nodup hm hv hw
      match v, hm with
      | .expression (.symbol c' :: vs), hm =>
          simp only [Pat.match] at hm
          split_ifs at hm with hc
          subst hc
          have lenVs : vs.length = Bs.length := by
            rw [← Pat.matchAll_length ps vs ρ hm, len]
          obtain ⟨σ', hσ', fields⟩ := ctor_inversion hΓ row vs lenVs T named (hv.count notMeta)
          obtain ⟨v', ρ', hv', hm', hw'⟩ :=
            Pat.field_binding Bs ps vs ρ hm (by simpa [Pat.vars] using nodup) B p field
              (PatFact.mem_vars inner) hw
          have fixedB : ∀ y ∈ B.vars, y ∈ R.vars := by
            rcases cls.fields B (List.of_mem_zip field).1 with free | fixedB
            · exact absurd free fixed
            · exact fixedB
          have same : B.bind σ' = B.bind σ := fixed_instance_unique fixedB (hσ'.trans hmatch.symm)
          have typed := fields (B, v') hv' checked
          rw [same] at typed
          have nodupPs : (Pat.varsAll ps).Nodup := by simpa [Pat.vars] using nodup
          exact ih ((nodupPs.sublist (Pat.vars_sublist_varsAll (List.of_mem_zip field).2)))
            hm' (Holds.of_count typed) hw'
      | .symbol _, hm => simp [Pat.match] at hm
      | .var _, hm => simp [Pat.match] at hm
      | .grounded _, hm => simp [Pat.match] at hm
      | .expression [], hm => simp [Pat.match] at hm
      | .expression (.var _ :: _), hm => simp [Pat.match] at hm
      | .expression (.grounded _ :: _), hm => simp [Pat.match] at hm
      | .expression (.expression _ :: _), hm => simp [Pat.match] at hm

/-- A number is typed `Number` once, whatever the declarations. -/
theorem count_int (Γ : Decls) (n : ℤ) : count (info Γ (.grounded (.int n))) (.sym "Number") = 1 := by
  classical
  unfold count
  rw [info_int]
  unfold eff
  simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.filter_singleton]
  rw [if_pos ⟨fun _ => default, (solves_append _ _ _).mpr ⟨by simp [classDeriv],
    (solves_singleton _ _).mpr rfl⟩⟩]
  rfl

theorem forall₂_compose {α β γ : Type} {P : α → β → Prop} {Q : β → γ → Prop} {S : α → γ → Prop} :
    ∀ {As : List α} {es : List β} {ws : List γ}, List.Forall₂ P As es → List.Forall₂ Q es ws →
      (∀ A e w, e ∈ es → P A e → Q e w → S A w) → List.Forall₂ S As ws
  | [], [], [], .nil, .nil, _ => .nil
  | A :: As, e :: es, w :: ws, .cons hp hps, .cons hq hqs, h =>
      .cons (h A e w (by simp) hp hq)
        (forall₂_compose hps hqs fun A' e' w' he' => h A' e' w' (by simp [he']))

variable {Φ : String → Ty Empty → Prop} {R : Ty Empty} {As : List (Ty Empty)}
  {o : List Atom → Multiset Atom} {ρ : List (String × Atom)}

mutual
/-- **The types the analysis gives hold of every value**, when the facts hold
of the bindings and the calls to themselves answer values meeting the result's
fact. -/
theorem eval_sound (hΓ : Functional Γ)
    (facts : ∀ x U w, Φ x U → ρ.lookup x = some w → Holds Γ grounded w U)
    (oracle : ∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R) :
    ∀ (e : Expr) (T : Ty Empty), HasType Γ Φ R e T → CallsOK Γ Φ R As e →
      ∀ v ∈ e.eval o ρ, Holds Γ grounded v T
  | .var x, T, h, _, v, hv => by
      cases h with
      | var hx =>
          simp only [Expr.eval] at hv
          cases hl : ρ.lookup x with
          | none =>
              simp only [hl] at hv
              exact absurd hv (Multiset.notMem_zero v)
          | some w =>
              simp only [hl, Multiset.mem_singleton] at hv
              subst hv
              exact facts x T _ hx hl
  | .const a, T, h, _, v, hv => by
      cases h with
      | const hc =>
          simp only [Expr.eval, Multiset.mem_singleton] at hv
          subst hv
          exact Holds.of_count hc
  | .ctor c args, T, h, hc, v, hv => by
      cases h with
      | @ctor _ Bs R' _ σ row cls len notMeta parts =>
          cases hc with
          | ctor hargs =>
              simp only [Expr.eval, Multiset.mem_map] at hv
              obtain ⟨vs, hvs, rfl⟩ := hv
              have each := Expr.evalAll_mem o ρ args vs hvs
              have lenVs : vs.length = Bs.length := by rw [← each.length_eq, len]
              refine Holds.of_count (ctor_construction hΓ row cls vs lenVs σ fun q hq hu hf => ?_)
              obtain ⟨e, he, hv⟩ := zip_of_forall₂ each Bs q.1 q.2 hq
              have mem : e ∈ args := (List.of_mem_zip he).2
              exact (List.forall_iff_forall_mem.mp (evalAll_sound hΓ facts oracle args) e mem (q.1.bind σ)
                (parts (q.1, e) he hu hf) (hargs e mem) q.2 hv).count (notMeta (q.1, e) he hu hf)
  | .self args, T, h, hc, v, hv => by
      cases h with
      | self =>
          cases hc with
          | self hargs typed =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨ws, hws, hv⟩ := hv
              refine oracle ws (forall₂_compose typed (Expr.evalAll_mem o ρ args ws hws)
                fun A e w he hA hw => List.forall_iff_forall_mem.mp (evalAll_sound hΓ facts oracle args) e he A hA
                  (hargs e he) w hw) v hv
  | .add a b, T, h, _, v, hv => by
      cases h with
      | add =>
          simp only [Expr.eval, Multiset.mem_bind] at hv
          obtain ⟨x, -, y, -, hv⟩ := hv
          match x, y, hv with
          | .grounded (.int m), .grounded (.int n), hv =>
              simp only [plus, Multiset.mem_singleton] at hv
              subst hv
              exact Holds.of_count (count_int Γ (m + n))

/-- The list version. -/
theorem evalAll_sound (hΓ : Functional Γ)
    (facts : ∀ x U w, Φ x U → ρ.lookup x = some w → Holds Γ grounded w U)
    (oracle : ∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R) :
    ∀ (args : List Expr), List.Forall (fun e => ∀ (T : Ty Empty),
      HasType Γ Φ R e T → CallsOK Γ Φ R As e → ∀ v ∈ e.eval o ρ, Holds Γ grounded v T) args
  | [] => trivial
  | e :: es => (List.forall_cons _ e es).mpr
      ⟨eval_sound hΓ facts oracle e, evalAll_sound hΓ facts oracle es⟩
end

mutual
/-- **The calls to itself are made at arguments meeting the entry facts**: two
oracles that agree there give the same values. -/
theorem eval_congr (hΓ : Functional Γ)
    (facts : ∀ x U w, Φ x U → ρ.lookup x = some w → Holds Γ grounded w U)
    (oracle : ∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R)
    {o' : List Atom → Multiset Atom} (agree : ∀ ws, EntryFacts Γ grounded As ws → o ws = o' ws) :
    ∀ (e : Expr), CallsOK Γ Φ R As e → e.eval o ρ = e.eval o' ρ
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .ctor c args, hc => by
      cases hc with
      | ctor hargs =>
          simp only [Expr.eval]
          rw [Expr.evalAll_congr args fun e he =>
            List.forall_iff_forall_mem.mp (evalAll_congr hΓ facts oracle agree args) e he (hargs e he)]
  | .self args, hc => by
      cases hc with
      | self hargs typed =>
          simp only [Expr.eval]
          rw [← Expr.evalAll_congr args fun e he =>
            List.forall_iff_forall_mem.mp (evalAll_congr hΓ facts oracle agree args) e he (hargs e he)]
          refine Multiset.bind_congr fun ws hws => agree ws ?_
          exact forall₂_compose typed (Expr.evalAll_mem o ρ args ws hws)
            fun A e w he hA hw => List.forall_iff_forall_mem.mp (evalAll_sound hΓ facts oracle args)
              e he A hA (hargs e he) w hw
  | .add a b, hc => by
      cases hc with
      | add ha hb =>
          simp only [Expr.eval]
          rw [eval_congr hΓ facts oracle agree a ha, eval_congr hΓ facts oracle agree b hb]

/-- The list version. -/
theorem evalAll_congr (hΓ : Functional Γ)
    (facts : ∀ x U w, Φ x U → ρ.lookup x = some w → Holds Γ grounded w U)
    (oracle : ∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R)
    {o' : List Atom → Multiset Atom} (agree : ∀ ws, EntryFacts Γ grounded As ws → o ws = o' ws) :
    ∀ (args : List Expr), List.Forall (fun e => CallsOK Γ Φ R As e → e.eval o ρ = e.eval o' ρ) args
  | [] => trivial
  | e :: es => (List.forall_cons _ e es).mpr
      ⟨eval_congr hΓ facts oracle agree e, evalAll_congr hΓ facts oracle agree es⟩
end

/-- **The facts an accepted equation reads hold** of the bindings of arguments
that meet the entry facts. -/
theorem eqFacts_sound (hΓ : Functional Γ) {eq : Equation} (acc : Accepted Γ As R eq)
    {vs : List Atom} {ρ : List (String × Atom)} (hm : Pat.matchAll eq.pats vs = some ρ)
    (hvs : EntryFacts Γ grounded As vs) :
    ∀ x U w, eqFacts Γ As eq x U → ρ.lookup x = some w → Holds Γ grounded w U := by
  rintro x U w ⟨A, p, hAp, hpf⟩ hl
  have hw : (x, w) ∈ ρ := by
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hl
    simp
  obtain ⟨v, ρ', hv, hm', hw'⟩ := Pat.field_binding As eq.pats vs ρ hm acc.linear A p hAp
    hpf.mem_vars hw
  exact hpf.sound hΓ (acc.linear.sublist (Pat.vars_sublist_varsAll (List.of_mem_zip hAp).2)) hm'
    (forall₂_zip hvs A v hv) hw'

/-- **An accepted relation meets the hypotheses of the version theorem.** -/
theorem accepted_versionHyps (hΓ : Functional Γ) {eqs : List Equation} (rg : ResultGuarded R.lift)
    (acc : ∀ eq ∈ eqs, Accepted Γ As R eq) :
    VersionHyps (Γ := Γ) (grounded := grounded) (equationsBody eqs) As R where
  resultGuarded := rg
  calls o o' agree oracle vs hvs := by
    unfold equationsBody
    refine Multiset.bind_congr fun eq heq => ?_
    split
    · next ρ hm =>
        exact eval_congr hΓ (eqFacts_sound hΓ (acc eq heq) hm hvs) oracle agree eq.rhs
          (acc eq heq).calls
    · rfl
  results o oracle vs hvs r hr := by
    unfold equationsBody at hr
    obtain ⟨eq, heq, hr⟩ := Multiset.mem_bind.mp hr
    split at hr
    · next ρ hm =>
        exact eval_sound hΓ (eqFacts_sound hΓ (acc eq heq) hm hvs) oracle eq.rhs R
          (acc eq heq).result (acc eq heq).calls r hr
    · exact absurd hr (Multiset.notMem_zero r)

/-- **The version of an accepted relation is its protocol**, at every fuel, on
arguments that meet the entry facts. -/
theorem accepted_version_eq_protocol (hΓ : Functional Γ) {eqs : List Equation}
    (rg : ResultGuarded R.lift) (acc : ∀ eq ∈ eqs, Accepted Γ As R eq) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts Γ grounded As vs) :
    protocolRun Γ grounded (equationsBody eqs) (arrow (As.map Ty.lift) R.lift) n vs =
      versionRun (equationsBody eqs) n vs :=
  version_eq_protocol (accepted_versionHyps hΓ rg acc) n vs hvs

/-- **A checked call of an accepted relation has the protocol's answers through
the version**, for every argument list. -/
theorem accepted_checked_call_eq (hΓ : Functional Γ) {eqs : List Equation}
    (guarded : ∀ A ∈ As, demand A.lift = .guarded) (rg : ResultGuarded R.lift)
    (acc : ∀ eq ∈ eqs, Accepted Γ As R eq) (n : ℕ) (vs : List Atom) :
    chainCall Γ (metatype grounded)
        (equationsBody eqs (protocolRun Γ grounded (equationsBody eqs) (arrow (As.map Ty.lift) R.lift) n))
        (arrow (As.map Ty.lift) R.lift) vs =
      chainCall Γ (metatype grounded) (equationsBody eqs (versionRun (equationsBody eqs) n))
        (arrow (As.map Ty.lift) R.lift) vs :=
  checked_call_eq hΓ guarded (accepted_versionHyps hΓ rg acc) n vs

end Soundness

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional sym num str app listOf listNumber consRow
  cons_row cons_constructor)

/-- `(= (lsum Nil) 0)` and `(= (lsum (Cons $x $xs)) (+ $x (lsum $xs)))`. -/
def lsumEqs : List Equation :=
  [⟨[.const (sym "Nil")], .const (num 0)⟩,
   ⟨[.ctor "Cons" [.var "x", .var "xs"]], .add (.var "x") (.self [.var "xs"])⟩]

/-- The fact the fold reads for `$xs` from `(Cons $x $xs)` at `(List Number)`. -/
theorem xs_fact : PatFact decls (.ctor "Cons" [.var "x", .var "xs"]) listNumber "xs" listNumber := by
  have inst : ((listOf (Ty.var "a") : Ty String).bind fun _ => Ty.sym "Number") = listNumber := by
    simp [listOf, listNumber]
  refine PatFact.ctor (σ := fun _ => .sym "Number") (B := listOf (.var "a")) (p := .var "xs")
    cons_row cons_constructor rfl (by simp [MetaName, listNumber, listOf])
    (by simp [Named, listNumber, listOf]) inst (by simp) (by simp [Unchecked, listOf])
    (by simp [FreeField, listOf]) ?_
  rw [inst]
  exact PatFact.var _ _

/-- **The fold `lsum` is accepted**: `$xs` is a `(List Number)`, so the call to
itself meets the formal, and the result is a `Number`. -/
theorem lsum_accepted : ∀ eq ∈ lsumEqs, Accepted decls [listNumber] (.sym "Number") eq := by
  intro eq heq
  simp only [lsumEqs, List.mem_cons, List.not_mem_nil, or_false] at heq
  rcases heq with rfl | rfl
  · exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, .const, .const (count_int decls 0)⟩
  · refine ⟨by simp [Pat.varsAll, Pat.vars], rfl,
      .add .var (.self (fun e he => by
        rw [List.mem_singleton] at he
        subst he
        exact .var) (.cons ?_ .nil)), .add⟩
    exact .var ⟨listNumber, .ctor "Cons" [.var "x", .var "xs"], by simp, xs_fact⟩

theorem number_guarded : ResultGuarded ((Ty.sym "Number" : Ty Empty).lift) := by
  simp [ResultGuarded, Ty.lift, Unchecked]

/-- **The version of `lsum` is its protocol**, at every fuel, on every list that
meets the entry fact. -/
theorem lsum_version (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts decls grounded [listNumber] vs) :
    protocolRun decls grounded (equationsBody lsumEqs) (arrow ([listNumber].map Ty.lift)
        (Ty.sym "Number" : Ty Empty).lift) n vs =
      versionRun (equationsBody lsumEqs) n vs :=
  accepted_version_eq_protocol decls_functional number_guarded lsum_accepted n vs hvs

/-- **At a metatype name the analysis inverts nothing**: `(C $s)` at
`Expression` gives `$s` no fact (`contract_metatype_name`). -/
theorem no_fact_at_metatype (U : Ty Empty) :
    ¬ PatFact decls (.ctor "C" [.var "s"]) (.sym "Expression") "s" U := by
  intro h
  cases h with
  | ctor _ _ _ notMeta => exact notMeta (by simp [MetaName])

/-- The fold's version answers `5` once for `(Cons 5 Nil)`. -/
theorem lsum_five_version :
    versionRun (equationsBody lsumEqs) 2 [app "Cons" [num 5, sym "Nil"]] = {num 5} := by
  decide

/-- The fold's equations at `Nil`: `0`. -/
theorem lsum_body_nil (o : List Atom → Multiset Atom) :
    equationsBody lsumEqs o [sym "Nil"] = {num 0} := by
  unfold equationsBody
  rw [show ((lsumEqs : List Equation) : Multiset Equation) =
    (⟨[.const (sym "Nil")], .const (num 0)⟩ : Equation) ::ₘ
      (⟨[.ctor "Cons" [.var "x", .var "xs"]], .add (.var "x") (.self [.var "xs"])⟩ : Equation) ::ₘ 0
    from rfl, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const (sym "Nil")] [sym "Nil"] = some [] := by decide
  have m2 : Pat.matchAll [.ctor "Cons" [.var "x", .var "xs"]] [sym "Nil"] = none := by decide
  simp only [m1, m2, Expr.eval, add_zero]

/-- The fold's equations at a cell: the head added to each answer for the rest. -/
theorem lsum_body_cons (o : List Atom → Multiset Atom) (n : ℤ) (rest : Atom) :
    equationsBody lsumEqs o [app "Cons" [num n, rest]] = (o [rest]).bind (plus (num n)) := by
  unfold equationsBody
  rw [show ((lsumEqs : List Equation) : Multiset Equation) =
    (⟨[.const (sym "Nil")], .const (num 0)⟩ : Equation) ::ₘ
      (⟨[.ctor "Cons" [.var "x", .var "xs"]], .add (.var "x") (.self [.var "xs"])⟩ : Equation) ::ₘ 0
    from rfl, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const (sym "Nil")] [app "Cons" [num n, rest]] = none := by
    simp [Pat.matchAll, Pat.match]
  have m2 : Pat.matchAll [.ctor "Cons" [.var "x", .var "xs"]] [app "Cons" [num n, rest]] =
      some [("x", num n), ("xs", rest)] := by
    simp [Pat.matchAll, Pat.match]
  simp only [m1, m2, zero_add, Expr.eval, Expr.evalAll, List.lookup, beq_self_eq_true,
    Multiset.singleton_bind, Multiset.map_singleton]
  simp

/-- **The functional precondition is necessary.** Read as SWI-PeTTa's `get-type`
reads repeated rows, `Cons` declared twice types `(Cons 5 Nil)` twice at
`(List Number)`, so the protocol answers `5` twice where the version answers it
once. -/
theorem repeated_rows_break_version (grounded : String → Bool) :
    protocolRun (decls.addRow "Cons" consRow) grounded (equationsBody lsumEqs)
        (arrow ([listNumber].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 2
        [app "Cons" [num 5, sym "Nil"]] = {num 5, num 5} ∧
      versionRun (equationsBody lsumEqs) 2 [app "Cons" [num 5, sym "Nil"]] = {num 5} := by
  refine ⟨?_, lsum_five_version⟩
  have nilInfo : info (decls.addRow "Cons" consRow) (sym "Nil") = info decls (sym "Nil") := by
    rw [info_symbol, info_symbol]
    simp [Decls.addRow]
  have countNil : count (info (decls.addRow "Cons" consRow) (sym "Nil")) listNumber = 1 := by
    rw [nilInfo]
    exact TypedCalls.Controls.count_nil _
  have countFive :
      count (info (decls.addRow "Cons" consRow) (app "Cons" [num 5, sym "Nil"])) listNumber = 2 :=
    TypedCalls.Controls.repeated_rows_twice.1
  have notMetaList : ¬ MetaName listNumber := by simp [MetaName, listNumber, listOf]
  have guardedList : demand ((listNumber : Ty Empty).lift) = .guarded := by
    simp [demand, listNumber, listOf, Ty.lift, Unchecked]
  have notMetaNumber : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  -- the call to itself at `Nil`
  have inner : protocolRun (decls.addRow "Cons" consRow) grounded (equationsBody lsumEqs)
      (arrow ([listNumber].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 1 [sym "Nil"] =
      {num 0} := by
    simp only [protocolRun]
    rw [chainCall_closed]
    simp only [if_pos number_guarded]
    have argNil : argCount (decls.addRow "Cons" consRow) (metatype grounded) [listNumber]
        [sym "Nil"] = 1 := by
      simp only [argCount, guardedList, if_true, mul_one]
      rw [guardCount_of_not_meta notMetaList, countNil]
    rw [argNil, one_nsmul, lsum_body_nil, Multiset.singleton_bind,
      guardCount_of_not_meta notMetaNumber, count_int, one_nsmul]
  simp only [protocolRun]
  rw [chainCall_closed]
  simp only [if_pos number_guarded]
  have argFive : argCount (decls.addRow "Cons" consRow) (metatype grounded) [listNumber]
      [app "Cons" [num 5, sym "Nil"]] = 2 := by
    simp only [argCount, guardedList, if_true, mul_one]
    rw [guardCount_of_not_meta notMetaList, countFive]
  rw [argFive, lsum_body_cons]
  simp only [protocolRun] at inner
  rw [inner, Multiset.singleton_bind]
  simp only [plus, Multiset.singleton_bind]
  rw [guardCount_of_not_meta notMetaNumber, count_int, one_nsmul]
  rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
