import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenRangeInstances

/-!
# Tail calls whose meet with the instance is implied

An HE activation of a head with an open range owes the range at the instance its
arguments give, met with what its caller owed when it was entered by a tail
call. A tail call the body makes is checked against what the activation owes
(the callee's range must meet it). CeTTa now computes an activation's instance
wherever a return position is a tail call whose meet is not implied
(`prepared_pure_tail_meet_implied`, `range_meets_tail`). It takes the meet as
implied only for the head's own tail call whose argument at each formal the
range reads (instance formal) is
* (a) the activation's parameter there,
* (b) a checked build `(C … p …)` of that parameter at a field whose declared type
  in `C`'s only declaration is `C`'s range, or
* (c) such a field of the parameter matched by the equation's pattern.

**What the clauses give** (`range_field_static`): an application of a constructor
typable at a type `U` has its field declared at the constructor's range at `U`,
or untyped. So for (b) the build allows only what the parameter allows
(`build_within`), and for (c) the field allows at least what the matched
parameter allows (`field_contains`). At a tail call by (a) or (b) (`Implied`) the
meet of the callee's instances with the activation's own is the callee's own
(`tail_owes_own`).

**HE's owed instances along a run of tail calls** (`owed`): the first activation
owes the instances its arguments give (`instSet`) within an expectation `E`, and
each next one the meet of its own with its caller's.
* With (a) and (b) only, each activation owes exactly its own instances within
  `E` (`owed_eq`). Entered with no expectation, every meet succeeds wherever the
  arguments meet their formals jointly, and the instance an activation would
  compute is what HE owes (`implied_meets`). So skipping the instance at such
  calls changes no answer (`skip_exact` covers the returns).
* A (c) step keeps the caller's instances (`field_step_keeps`) but loses the
  invariant: a later (b) step may fail where the activation's own instances do
  not (`Controls.field_then_build_fails`, `Controls.field_then_build_steps`).
  CeTTa now computes the instance for a head whose implied steps include both.
* With (a) and (c) only, each activation owes the first one's instances
  (`owed_eq_first`), every later callee's instances include them
  (`first_within_later`), and every meet succeeds wherever the first one's does
  (`field_meets`).
* **The complete rule** (`unmixed_meets`): a run whose steps are all (a)/(b) or
  all (a)/(c) makes every meet succeed wherever each activation's arguments meet
  their formals jointly, so skipping the instance is exact for such heads.
* The field clause never takes part in a run that returns a value: under CeTTa's
  shown rule at an open range (a slot only in an equation whose patterns are all
  variables, a symbol never since its type is read with fresh variables, a tail
  call always) a determinate head with a constructor pattern returns only through
  calls (`field_head_only_calls`).

**Controls of the weaker rules**, on allowed sets: a constructor whose field is
not declared at its range (`(: Wrap (-> (List $b) (List Number)))`,
`Controls.wrap_not_within`), another parameter at the formal
(`Controls.swap_fails`), and a field typed otherwise
(`(: Wrap2 (-> (List String) (List Number)))`, `Controls.wrap2_not_contained`).

**Expression type rows** (`Controls.expr_row_he`). An expression subject's own
row is a typing HE lists first. With `(: (Cons 1 Nil) (List (Pair Number Number)))`
and `(: g (-> (List $t) Number))`, HE's check of `(g (Cons 1 Nil))` binds `$t` at
the row's instance, evaluates the argument there and answers an error, where a
check accepting any typing that unifies with the formal accepts. Clauses (b) and
(c) and the fold read the constructor's type through
`space_type_rows_only_declare`, which an expression row headed by the
constructor fails, so they are not affected; the open-formal check is.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ImpliedMeets

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ShapeTyping StaticEvidence InferredTypeSets OpenFormals OpenRangeInstances

/-! ## Fields declared at the constructor's range -/

/-- **A constructor application typable at `U` has its field declared at the
constructor's range at `U`**, or untyped. -/
theorem range_field_static {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)}
    {R : Ty String} (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) {k : ℕ} {a : Atom}
    (hk : Ts[k]? = some R) (ha : args[k]? = some a) (checked : CheckedTy R) {U : Ty Empty}
    (typed : Typable (stamp Γ (.expression (.symbol c :: args))) U) : StaticAt (stamp Γ a) U := by
  have h := field_static_of_open (F := U.lift) row args hk ha checked (fun _ _ h => h)
    (φ := fun _ => default) (by rwa [Ty.lift_bind_ground])
  rwa [Ty.lift_bind_ground] at h

/-- One stamp allows only what another allows. -/
def AllowsWithin (st st' : Stamp) : Prop := ∀ U, StaticAt st U → StaticAt st' U

theorem AllowsWithin.refl (st : Stamp) : AllowsWithin st st := fun _ h => h

/-- **(b) A checked build allows only what its field at the range allows.** -/
theorem build_within {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) {k : ℕ} {p : Atom}
    (hk : Ts[k]? = some R) (hp : args[k]? = some p) (checked : CheckedTy R) :
    AllowsWithin (stamp Γ (.expression (.symbol c :: args))) (stamp Γ p) := by
  intro U h
  rcases h with h | h
  · exact absurd h (ctor_typs_ne_nil row args)
  · exact range_field_static row args hk hp checked h

/-- **(c) A field at the range allows at least what the matched value allows.** -/
theorem field_contains {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) {k : ℕ} {x : Atom}
    (hk : Ts[k]? = some R) (hx : args[k]? = some x) (checked : CheckedTy R) :
    AllowsWithin (stamp Γ (.expression (.symbol c :: args))) (stamp Γ x) :=
  build_within row args hk hx checked

/-! ## HE's owed instances along a run of tail calls -/

/-- The instances of the range the arguments give: under one assignment of the
formals' variables, each argument allows its formal there. -/
def instSet (R : Ty String) (Fs : List (Ty String)) (allows : List (Ty Empty → Prop)) : Set (Ty Empty) :=
  {T | ∃ ψ : String → Ty Empty, R.bind ψ = T ∧ List.Forall₂ (fun F A => A (F.bind ψ)) Fs allows}

/-- The allowed types of a stamp. -/
def allowsOf (st : Stamp) : Ty Empty → Prop := StaticAt st

/-- Arguments allowing only what others allow give only their instances. -/
theorem instSet_mono {R : Ty String} {Fs : List (Ty String)} {as as' : List (Ty Empty → Prop)}
    (h : List.Forall₂ (fun A A' => ∀ U, A U → A' U) as as') : instSet R Fs as ⊆ instSet R Fs as' := by
  rintro T ⟨ψ, rfl, each⟩
  refine ⟨ψ, rfl, ?_⟩
  induction each generalizing as' with
  | nil => cases h; exact .nil
  | cons hA _ ih =>
      cases h with
      | cons hAA' rest => exact .cons (hAA' _ hA) (ih rest)

/-- **The argument a tail call passes at an instance formal, against the
activation's parameter there**: the parameter itself (a), or a checked build over
it at a field its constructor declares at its range (b). -/
inductive Implied (Γ : Decls) : Atom → Atom → Prop
  | param (p : Atom) : Implied Γ p p
  | build {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
      (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) {k : ℕ} {p : Atom}
      (hk : Ts[k]? = some R) (hp : args[k]? = some p) (checked : CheckedTy R) :
      Implied Γ (.expression (.symbol c :: args)) p

theorem Implied.within {Γ : Decls} {a p : Atom} (h : Implied Γ a p) :
    AllowsWithin (stamp Γ a) (stamp Γ p) := by
  cases h with
  | param => exact AllowsWithin.refl _
  | build row args hk hp checked => exact build_within row args hk hp checked

/-- **The meet at such a tail call is implied**: the instances its arguments give
lie within the activation's own, so their meet is the callee's own instances. -/
theorem tail_owes_own {Γ : Decls} {R : Ty String} {Fs : List (Ty String)} {ws vs : List Atom}
    (h : List.Forall₂ (Implied Γ) ws vs) :
    instSet R Fs (ws.map fun w => allowsOf (stamp Γ w)) ∩ instSet R Fs (vs.map fun v => allowsOf (stamp Γ v)) =
      instSet R Fs (ws.map fun w => allowsOf (stamp Γ w)) := by
  refine Set.inter_eq_left.mpr (instSet_mono ?_)
  exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (h.imp fun _ _ hi => hi.within))

/-- **HE's owed instances**: the first activation owes its own within the
expectation `E`, each next one entered by a tail call the meet of its own with
its caller's. -/
def owed (R : Ty String) (Fs : List (Ty String)) (E : Set (Ty Empty)) (as : ℕ → List (Ty Empty → Prop)) :
    ℕ → Set (Ty Empty)
  | 0 => instSet R Fs (as 0) ∩ E
  | k + 1 => instSet R Fs (as (k + 1)) ∩ owed R Fs E as k

/-- **With clauses (a) and (b) each activation owes its own instances within the
expectation.** -/
theorem owed_eq {R : Ty String} {Fs : List (Ty String)} {E : Set (Ty Empty)} {as : ℕ → List (Ty Empty → Prop)}
    (within : ∀ k, List.Forall₂ (fun A A' => ∀ U, A U → A' U) (as (k + 1)) (as k)) :
    ∀ k, owed R Fs E as k = instSet R Fs (as k) ∩ E
  | 0 => rfl
  | k + 1 => by
      rw [owed, owed_eq within k, ← Set.inter_assoc,
        Set.inter_eq_left.mpr (instSet_mono (within k))]

/-- **Implied meets**: entered with no expectation, a run of tail calls by
clauses (a) and (b) owes at each activation exactly the instances its arguments
give, which are there wherever the arguments meet their formals jointly; every
meet succeeds, and the instance an activation would compute is HE's. -/
theorem implied_meets {R : Ty String} {Fs : List (Ty String)} {as : ℕ → List (Ty Empty → Prop)}
    (within : ∀ k, List.Forall₂ (fun A A' => ∀ U, A U → A' U) (as (k + 1)) (as k))
    (joint : ∀ k, ∃ ψ : String → Ty Empty, List.Forall₂ (fun F A => A (F.bind ψ)) Fs (as k)) :
    ∀ k, owed R Fs Set.univ as k = instSet R Fs (as k) ∧ (owed R Fs Set.univ as k).Nonempty := by
  intro k
  rw [owed_eq within k, Set.inter_univ]
  obtain ⟨ψ, hψ⟩ := joint k
  exact ⟨rfl, R.bind ψ, ψ, rfl, hψ⟩

/-- Discharged arguments at formals sharing no variable meet them jointly, read
on their stamps (`OpenRangeInstances.joint_instance`). -/
theorem joint_of_meets {Γ : Decls} {Fs : List (Ty String)} {vs : List Atom}
    (apart : Fs.Pairwise (fun A B => ∀ x ∈ A.vars, x ∉ B.vars))
    (each : List.Forall₂ (fun F v => CheckedTy F ∧ MeetsOpen F (stamp Γ v)) Fs vs) :
    ∃ ψ : String → Ty Empty, List.Forall₂ (fun F A => A (F.bind ψ)) Fs (vs.map fun v => allowsOf (stamp Γ v)) := by
  obtain ⟨ψ, hψ⟩ := joint_instance Fs vs apart each
  exact ⟨ψ, List.forall₂_map_right_iff.mpr hψ⟩

/-- **A field step keeps its caller's instances**: an argument allowing at least
what the caller's allows meets them all. -/
theorem field_step_keeps {R : Ty String} {Fs : List (Ty String)} {E : Set (Ty Empty)}
    {as : ℕ → List (Ty Empty → Prop)} (k : ℕ)
    (contains : List.Forall₂ (fun A A' => ∀ U, A U → A' U) (as k) (as (k + 1)))
    (own : owed R Fs E as k ⊆ instSet R Fs (as k)) : owed R Fs E as (k + 1) = owed R Fs E as k := by
  rw [owed]
  exact Set.inter_eq_right.mpr (own.trans (instSet_mono contains))

theorem owed_subset_own (R : Ty String) (Fs : List (Ty String)) (E : Set (Ty Empty))
    (as : ℕ → List (Ty Empty → Prop)) : ∀ k, owed R Fs E as k ⊆ instSet R Fs (as k)
  | 0 => Set.inter_subset_left
  | _ + 1 => Set.inter_subset_left


/-- Each activation owes at most what its caller owed. -/
theorem owed_antitone (R : Ty String) (Fs : List (Ty String)) (E : Set (Ty Empty))
    (as : ℕ → List (Ty Empty → Prop)) (k : ℕ) : owed R Fs E as (k + 1) ⊆ owed R Fs E as k :=
  Set.inter_subset_right

/-- **Every meet up to an activation succeeds exactly when its own does.** -/
theorem meets_all_iff_last (R : Ty String) (Fs : List (Ty String)) (E : Set (Ty Empty))
    (as : ℕ → List (Ty Empty → Prop)) (K : ℕ) :
    (∀ k ≤ K, (owed R Fs E as k).Nonempty) ↔ (owed R Fs E as K).Nonempty := by
  refine ⟨fun h => h K le_rfl, fun h k hk => ?_⟩
  induction K with
  | zero => rwa [Nat.le_zero.mp hk]
  | succ K ih =>
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · exact ih (h.mono (owed_antitone R Fs E as K)) (Nat.lt_succ_iff.mp hlt)
      · rwa [heq]

/-- **A context's check of the returned parameter gives the last meet**: where
the run ends by returning its parameter at the range's own formal, an
expectation made of the range's instances that the returned value's typing
allows somewhere meets the instances that value gives. -/
theorem context_check_gives_meets {R : Ty String} {A : Ty Empty → Prop} {E : Set (Ty Empty)}
    (inst : ∀ U ∈ E, ∃ ψ : String → Ty Empty, R.bind ψ = U) (checked : ∃ U ∈ E, A U) :
    (instSet R [R] [A] ∩ E).Nonempty := by
  obtain ⟨U, hU, hA⟩ := checked
  obtain ⟨ψ, hψ⟩ := inst U hU
  exact ⟨U, ⟨ψ, hψ, .cons (by rw [hψ]; exact hA) .nil⟩, hU⟩

/-! ## Runs whose steps are of one kind -/

/-- **With clauses (a) and (c) each activation owes the first one's instances**:
a field allows at least what its parameter allows, so each meet keeps what the
caller owed. -/
theorem owed_eq_first {R : Ty String} {Fs : List (Ty String)} {E : Set (Ty Empty)}
    {as : ℕ → List (Ty Empty → Prop)}
    (contains : ∀ k, List.Forall₂ (fun A A' => ∀ U, A U → A' U) (as k) (as (k + 1))) :
    ∀ k, owed R Fs E as k = owed R Fs E as 0
  | 0 => rfl
  | k + 1 => by
      rw [field_step_keeps k (contains k) (owed_subset_own R Fs E as k), owed_eq_first contains k]

/-- **Each later callee's instances include the first activation's.** -/
theorem first_within_later {R : Ty String} {Fs : List (Ty String)} {as : ℕ → List (Ty Empty → Prop)}
    (contains : ∀ k, List.Forall₂ (fun A A' => ∀ U, A U → A' U) (as k) (as (k + 1))) :
    ∀ k, instSet R Fs (as 0) ⊆ instSet R Fs (as k)
  | 0 => subset_rfl
  | k + 1 => (first_within_later contains k).trans (instSet_mono (contains k))

/-- **Field meets**: a run of tail calls by clauses (a) and (c) owes at every
activation the first one's instances within the expectation, and every meet
succeeds wherever the first one's does. -/
theorem field_meets {R : Ty String} {Fs : List (Ty String)} {E : Set (Ty Empty)}
    {as : ℕ → List (Ty Empty → Prop)}
    (contains : ∀ k, List.Forall₂ (fun A A' => ∀ U, A U → A' U) (as k) (as (k + 1)))
    (first : (owed R Fs E as 0).Nonempty) :
    ∀ k, owed R Fs E as k = instSet R Fs (as 0) ∩ E ∧ (owed R Fs E as k).Nonempty := fun k => by
  rw [owed_eq_first contains k]
  exact ⟨rfl, first⟩

/-- The clause an implied tail call's argument follows at one instance formal. -/
inductive Clause where
  /-- (a): the activation's parameter. -/
  | param
  /-- (b): a checked build over it, at a field declared at the constructor's range. -/
  | build
  /-- (c): such a field of it, matched by the equation's pattern. -/
  | field
  deriving DecidableEq

/-- What a clause gives the allowed types at one instance formal, from an
activation to the next: the same (a), within (b, `build_within`), containing (c,
`field_contains`). -/
def Clause.Rel : Clause → (Ty Empty → Prop) → (Ty Empty → Prop) → Prop
  | .param, A, A' => ∀ U, A U ↔ A' U
  | .build, A, A' => ∀ U, A' U → A U
  | .field, A, A' => ∀ U, A U → A' U

/-- A step of a run whose clauses are drawn from `K`, one per instance formal. -/
def StepIn (K : Clause → Prop) (as as' : List (Ty Empty → Prop)) : Prop :=
  List.Forall₂ (fun A A' => ∃ c, K c ∧ c.Rel A A') as as'

/-- Clauses (a) and (b) only. -/
def Builds (c : Clause) : Prop := c ≠ .field

/-- Clauses (a) and (c) only. -/
def Fields (c : Clause) : Prop := c ≠ .build

theorem StepIn.mono {K K' : Clause → Prop} (hK : ∀ c, K c → K' c) {as as' : List (Ty Empty → Prop)}
    (h : StepIn K as as') : StepIn K' as as' :=
  h.imp fun _ _ ⟨c, hc, hr⟩ => ⟨c, hK c hc, hr⟩

theorem StepIn.within : ∀ {as as' : List (Ty Empty → Prop)}, StepIn Builds as as' →
    List.Forall₂ (fun A A' => ∀ U, A U → A' U) as' as
  | _, _, .nil => .nil
  | _, _, .cons ⟨c, hc, hr⟩ rest => by
      refine .cons ?_ (StepIn.within rest)
      cases c with
      | param => exact fun U h => (hr U).mpr h
      | build => exact hr
      | field => exact absurd rfl hc

theorem StepIn.contains : ∀ {as as' : List (Ty Empty → Prop)}, StepIn Fields as as' →
    List.Forall₂ (fun A A' => ∀ U, A U → A' U) as as'
  | _, _, .nil => .nil
  | _, _, .cons ⟨c, hc, hr⟩ rest => by
      refine .cons ?_ (StepIn.contains rest)
      cases c with
      | param => exact fun U h => (hr U).mp h
      | build => exact absurd rfl hc
      | field => exact hr

/-- **The complete rule**: entered with no expectation, a run whose implied steps
are all by clauses (a) and (b), or all by (a) and (c), makes every meet succeed
wherever each activation's arguments meet their formals jointly. With builds each
activation owes its own instances (`implied_meets`), with fields the first one's
(`field_meets`). A run mixing the two can fail (`Controls.field_then_build_steps`). -/
theorem unmixed_meets {R : Ty String} {Fs : List (Ty String)} {as : ℕ → List (Ty Empty → Prop)}
    {K : Clause → Prop} (unmixed : (∀ c, K c → Builds c) ∨ (∀ c, K c → Fields c))
    (steps : ∀ k, StepIn K (as k) (as (k + 1)))
    (joint : ∀ k, ∃ ψ : String → Ty Empty, List.Forall₂ (fun F A => A (F.bind ψ)) Fs (as k)) :
    ∀ k, (owed R Fs Set.univ as k).Nonempty := by
  rcases unmixed with hb | hf
  · exact fun k => (implied_meets (fun k => ((steps k).mono hb).within) joint k).2
  · have first : (owed R Fs Set.univ as 0).Nonempty := by
      obtain ⟨ψ, hψ⟩ := joint 0
      exact ⟨R.bind ψ, ⟨ψ, rfl, hψ⟩, trivial⟩
    exact fun k => (field_meets (fun k => ((steps k).mono hf).contains) first k).2

/-! ## The field clause and CeTTa's shown rule -/

/-- An argument pattern's head: a variable, or a symbol (a constructor or a
literal). -/
inductive PatHead where
  | var
  | head (s : String)

/-- A return position's kind, as the shown rule reads it. -/
inductive RetKind where
  | slot
  | sym
  | call
  | other

/-- An equation as the shown rule and the determinacy check read it. -/
structure EqShape where
  pats : List PatHead
  rets : List RetKind

/-- Every argument pattern is a variable (`variable_arguments`). -/
def AllVar (e : EqShape) : Prop := ∀ p ∈ e.pats, p = .var

/-- Two equations a weak-head check tells apart: at some argument both patterns
have heads, and the heads differ. -/
def Distinguished (e e' : EqShape) : Prop :=
  ∃ (i : ℕ) (a b : String), e.pats[i]? = some (.head a) ∧ e'.pats[i]? = some (.head b) ∧ a ≠ b

/-- **A determinate head**: every two of its equations are told apart. -/
def Determinate (eqs : List EqShape) : Prop := eqs.Pairwise Distinguished

/-- **CeTTa's shown rule at an open range**, per return position
(`prepared_pure_he_range_shown`): a slot only in an equation whose patterns are
all variables, a symbol never (its type is read with fresh variables, never
syntactically the range), a tail call always. -/
def ShownOpen (e : EqShape) : RetKind → Prop
  | .slot => AllVar e
  | .sym => False
  | .call => True
  | .other => False

theorem not_distinguished_left {e : EqShape} (h : AllVar e) (e' : EqShape) : ¬ Distinguished e e' := by
  rintro ⟨i, a, b, ha, -, -⟩
  have := h _ (List.mem_of_getElem? ha)
  cases this

theorem not_distinguished_right {e : EqShape} (h : AllVar e) (e' : EqShape) : ¬ Distinguished e' e := by
  rintro ⟨i, a, b, -, hb, -⟩
  have := h _ (List.mem_of_getElem? hb)
  cases this

/-- **An equation whose patterns are all variables is its determinate head's
only one.** -/
theorem allVar_only : ∀ {eqs : List EqShape}, Determinate eqs → ∀ e ∈ eqs, AllVar e → ∀ e' ∈ eqs, e' = e ∨ e' ∈ [e]
  | [], _, _, he, _, _, _ => by cases he
  | x :: xs, det, e, he, hv, e', he' => by
      rw [Determinate, List.pairwise_cons] at det
      rcases List.mem_cons.mp he with rfl | hxs
      · rcases List.mem_cons.mp he' with rfl | hxs'
        · exact .inl rfl
        · exact absurd (det.1 e' hxs') (not_distinguished_left hv e')
      · rcases List.mem_cons.mp he' with rfl | hxs'
        · exact absurd (det.1 e hxs) (not_distinguished_right hv e')
        · exact allVar_only det.2 e hxs hv e' hxs'

/-- **The field clause never licenses a skip in a run that returns a value**: in a
determinate head whose open range CeTTa shows, if some equation has a constructor
pattern (which the field clause reads), every return position of every equation
is a call. -/
theorem field_head_only_calls {eqs : List EqShape} (det : Determinate eqs)
    (shown : ∀ e ∈ eqs, ∀ r ∈ e.rets, ShownOpen e r) {ec : EqShape} (hec : ec ∈ eqs) (pattern : ¬ AllVar ec) :
    ∀ e ∈ eqs, ∀ r ∈ e.rets, r = .call := by
  intro e he r hr
  have hnv : ¬ AllVar e := by
    intro hv
    rcases allVar_only det e he hv ec hec with h | h
    · exact pattern (h ▸ hv)
    · rw [List.mem_singleton] at h
      exact pattern (h ▸ hv)
  have hs := shown e he r hr
  cases r with
  | slot => exact absurd hs hnv
  | sym => exact hs.elim
  | call => rfl
  | other => exact hs.elim

/-! ## Controls -/

namespace Controls

/-- `(List x)` as a ground type. -/
abbrev glist (x : Ty Empty) : Ty Empty := .app [.sym "List", x]

/-- `(List $t)`. -/
abbrev listT : Ty String := .app [.sym "List", .var "t"]

theorem listT_bind (ψ : String → Ty Empty) : listT.bind ψ = glist (ψ "t") := by
  simp [listT, glist, Ty.bind_app]

/-- A caller allowing `(List Number)`, a field allowing every list, then a build
allowing `(List String)`. -/
def fieldBuildArgs (k : ℕ) : List (Ty Empty → Prop) :=
  if k = 0 then [fun U => U = glist (.sym "Number")]
  else if k = 1 then [fun U => ∃ X, U = glist X]
  else [fun U => U = glist (.sym "String")]

/-- **A field step then a build step can fail**: the first two meets succeed and
the third fails, where the build's own instances are there. -/
theorem field_then_build_fails :
    (owed listT [listT] Set.univ fieldBuildArgs 1).Nonempty ∧
      owed listT [listT] Set.univ fieldBuildArgs 2 = ∅ ∧
      (instSet listT [listT] (fieldBuildArgs 2)).Nonempty := by
  have h0 : fieldBuildArgs 0 = [fun U => U = glist (.sym "Number")] := rfl
  have h1 : fieldBuildArgs 1 = [fun U => ∃ X, U = glist X] := rfl
  have h2 : fieldBuildArgs 2 = [fun U => U = glist (.sym "String")] := rfl
  refine ⟨⟨glist (.sym "Number"), ?_, ?_, trivial⟩, ?_, ?_⟩
  · rw [h1]
    exact ⟨fun _ => .sym "Number", listT_bind _, .cons ⟨.sym "Number", listT_bind _⟩ .nil⟩
  · rw [h0]
    exact ⟨fun _ => .sym "Number", listT_bind _, .cons (listT_bind _) .nil⟩
  · ext T
    simp only [owed, Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨ψ2, hT2, e2⟩, -, ⟨ψ0, hT0, e0⟩⟩
    rw [h2] at e2
    rw [h0] at e0
    cases e2 with
    | cons a2 _ =>
      cases e0 with
      | cons a0 _ =>
        rw [listT_bind] at hT2 hT0 a2 a0
        rw [← hT2, a2] at hT0
        rw [a0] at hT0
        simp at hT0
  · rw [h2]
    exact ⟨glist (.sym "String"), fun _ => .sym "String", listT_bind _, .cons (listT_bind _) .nil⟩

/-- **The run of `field_then_build_fails` mixes the clauses**: a field step, then
a build step. -/
theorem field_then_build_steps :
    StepIn (· = Clause.field) (fieldBuildArgs 0) (fieldBuildArgs 1) ∧
      StepIn (· = Clause.build) (fieldBuildArgs 1) (fieldBuildArgs 2) := by
  refine ⟨.cons ⟨.field, rfl, fun U h => ⟨.sym "Number", h⟩⟩ .nil,
    .cons ⟨.build, rfl, fun U h => ⟨.sym "String", h⟩⟩ .nil⟩

/-- **A constructor whose field is not declared at its range**
(`(: Wrap (-> (List $b) (List Number)))`): `(Wrap p)` with `p` allowing
`(List String)` allows `(List Number)`, which `p` does not; the meet with what the
caller owes fails. -/
theorem wrap_not_within :
    ¬ (∀ U : Ty Empty, U = glist (.sym "Number") → U = glist (.sym "String")) ∧
      instSet listT [listT] [fun U => U = glist (.sym "Number")] ∩
        instSet listT [listT] [fun U => U = glist (.sym "String")] = ∅ := by
  refine ⟨fun h => by simpa using h _ rfl, ?_⟩
  ext T
  simp only [instSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨ψ, h, e⟩, ⟨ψ', h', e'⟩⟩
  cases e with
  | cons hA _ =>
    cases e' with
    | cons hA' _ =>
      rw [listT_bind] at h h' hA hA'
      rw [← h, hA] at h'
      rw [hA'] at h'
      simp at h'

/-- **Another parameter at the formal** (`(sw $x $y)` calling `(sw $y $x)`): the
argument at the instance formal allows `(List String)` where the caller's allows
`(List Number)`, and the meet fails. -/
theorem swap_fails :
    instSet listT [listT] [fun U => U = glist (.sym "String")] ∩
      instSet listT [listT] [fun U => U = glist (.sym "Number")] = ∅ := by
  ext T
  simp only [instSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨ψ, h, e⟩, ⟨ψ', h', e'⟩⟩
  cases e with
  | cons hA _ =>
    cases e' with
    | cons hA' _ =>
      rw [listT_bind] at h h' hA hA'
      rw [← h, hA] at h'
      rw [hA'] at h'
      simp at h'

/-- **A field typed otherwise** (`(: Wrap2 (-> (List String) (List Number)))`):
the matched `(Wrap2 xs)` allows `(List Number)` and its field `(List String)`,
which does not contain it, and the meet fails. -/
theorem wrap2_not_contained :
    ¬ (∀ U : Ty Empty, U = glist (.sym "Number") → U = glist (.sym "String")) ∧
      instSet listT [listT] [fun U => U = glist (.sym "String")] ∩
        instSet listT [listT] [fun U => U = glist (.sym "Number")] = ∅ :=
  ⟨fun h => by simpa using h _ rfl, swap_fails⟩

/-! ### An expression's own type row in HE's interpreter -/

section HE

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter (symbol apply equation typed)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls (arrowAtom answersWith)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns.Controls (num)

/-- `(List x)` as an atom. -/
def listA (x : Atom) : Atom := apply "List" [x]

/-- `(Pair Number Number)`. -/
def pairNN : Atom := apply "Pair" [symbol "Number", symbol "Number"]

/-- `(Cons 1 Nil)`. -/
def cell : Atom := apply "Cons" [num 1, symbol "Nil"]

/-- `(: (Cons 1 Nil) (List (Pair Number Number)))` beside the list rows, and
`(: g (-> (List $t) Number))`, `(= (g $l) 7)`. -/
def rowSpace : Space := Space.ofList [
  typed "Nil" (listA (.var "a")),
  typed "Cons" (arrowAtom [.var "a", listA (.var "a"), listA (.var "a")]),
  .expression [symbol ":", cell, listA pairNN],
  typed "g" (arrowAtom [listA (.var "t"), symbol "Number"]),
  equation (apply "g" [.var "l"]) (num 7)]

/-- The error HE's interpreter answers: the argument evaluated at the row's
instance fails. -/
def rowError : Atom := .expression [symbol "Error", cell,
  .expression [symbol "BadType", listA pairNN, listA (.var "a")]]

/-- **HE binds the formal at the expression's own row and answers an error**:
`(g (Cons 1 Nil))` is an error at budgets sixteen and forty (Rust's error names
`(List Number)` where the interpreter model, which reads no application typing,
names Cons's range). -/
theorem expr_row_he :
    getAtomTypes rowSpace cell = [listA pairNN] ∧
      answersWith rowSpace (apply "g" [cell]) 16 = [rowError] ∧
      answersWith rowSpace (apply "g" [cell]) 40 = [rowError] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end HE

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ImpliedMeets
