import Mathlib.Data.List.Sections
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StaticEvidence

/-!
# Inferred typing sets of untyped heads

In a closed HE program of typed constructors and untyped functions, CeTTa
gives every node a small set of typings (`prepared_pure_infer_untyped`,
`prepared_pure_static_types`): an untyped head's parameter has the typings its
call sites pass, its answer those its equations' bodies give, from no typing up
to a fixpoint; a head the program names as a value may be called with
anything. A checked build is then left unchecked where every combination of its
children's typings passes the constructor's check, and an argument where every
typing it may have meets the callee's formal, with or without type variables.

**Members are lower bounds.** A member is read by its ground instances, as
`ShapeTyping` reads typings. What it says of a value (`LowerAt`): the value has
no typing, or a valid typing allowing every instance of the member. A formal
gives such a bound, not the value's typing: `Nil` passes the formal
`(List Number)` with its typing `(List $a)`.

**The checks on lower bounds.**
* A build over children typed at least as generally as some members passes
  HE's check wherever the members' joint assignments are nonempty, and is typed
  at least as generally as the range under them (`semCheck_lower`,
  `build_lower`): the combination is read with fresh variables, jointly over the
  children.
* A failing combination of lower bounds says nothing: the children's actual
  typings may be more general and pass (`Controls.failing_lower_combination_builds`).
  So a build whose combinations do not all pass is unknown (`buildSet`).
* A field of a constructor application covered by a member has the field's
  declared type under the member (`field_lower`), when every variable of the
  field's declared type is one of the range's: a variable only the field names is
  not fixed by the range, and the field may be typed at any one instance
  (`Controls.free_field_not_lower`). A member the range does not meet reaches no
  field.
* An argument whose every member allows a closed formal meets it
  (`meets_of_lower`); at a formal with type variables, HE's check unifies a
  typing with a fresh copy of the formal (`MeetsOpen`), and an argument whose
  every member allows some instance of the formal meets it
  (`meetsOpen_of_lower`).

**The analysis** (`absNode`) is the C's: a literal's one typing, a register's
class, a call's answer set or typed range, both branches of an `if`, a `let`'s
body under its bound value's set, a build's combinations, a slot's parameter or
field set; a typed head's slot at a formal without type variables reads the
formal, and at one with type variables the inferred set its call sites join
(`paramSet`, `prepared_pure_inferred_site`); `Walk` collects the call-site and
discharge conditions of a body, and `PostFix` asks them of every body and every
answer, with the inferred parameters of every head the program names as a value
unknown.

**Soundness** (`sound`): on HE's semantics of the program (`Reach` at
`prep = false`: checks at every typed call, return and build), every value
reaching a node is covered by the node's set. **Discharge** (`prepared_iff`):
the prepared semantics, which skips the discharged builds, arguments and
returns, reaches exactly HE's values.

**Controls**: a failing combination keeps its check, and HE's check fails there
(`Controls.failing_combination_checked`); a head the program names as a value and
calls with another argument has a parameter outside its call sites' join
(`Controls.escape_needs_any`); a field read without the range fixing it, and a
failing combination of lower bounds read as no value, each make a set that does
not cover a reaching value (`Controls.free_field_not_lower`,
`Controls.failing_lower_combination_builds`).

**Widened sets** (`postFix_of_widened`): CeTTa decides its flags on sets wider
than its fixpoint's (a set no value reached, a fifth member, a sixty-fifth
combination: unknown); the analysis is monotone and the discharge conditions are
antitone, so such flags are discharges at the fixpoint.

The model's values are reached by one-way matching (ground runs); untyped heads
have no declarations; typed heads have formals with or without type variables,
or unchecked ones, and a closed or no range (an open range's instance is
`OpenRangeInstances`'s subject); formals with type variables are checked one by
one, as CeTTa admits them only where no two share a variable; a `let`'s slot takes its bound value's set when bound, where CeTTa
reads the bound node again at each use. A member is the set of ground instances
of CeTTa's member type, which is what CeTTa's unifier computes for its fresh
copies when no `%Undefined%` occurs inside them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSets

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ShapeTyping StaticEvidence

/-! ## Lower bounds and HE's check -/

/-- Two assignments that agree on a term's substitution agree on its
variables. -/
theorem bind_eq_on_vars {V W : Type} {f g : V → Ty W} :
    ∀ (t : Ty V), t.bind f = t.bind g → ∀ v ∈ t.vars, f v = g v
  | .var v, h, w, hw => by
      simp only [Ty.vars_var, List.mem_singleton] at hw
      subst hw
      simpa using h
  | .sym _, _, w, hw => by simp at hw
  | .app ts, h, w, hw => by
      rw [Ty.bind_app, Ty.bind_app] at h
      have h' := List.map_inj_left.mp (Ty.app.inj h)
      simp only [Ty.vars_app, List.mem_flatMap] at hw
      obtain ⟨t, ht, hw⟩ := hw
      exact bind_eq_on_vars t (h' t ht) w hw

/-- A static typing `S`, a set of ground types, is below a stamp: the value has no
typing, or a valid typing allowing all of `S`. -/
def Below (S : Set (Ty Empty)) (st : Stamp) : Prop :=
  st.typs = [] ∨ ∃ X, Sem.ok X ∈ st.typs ∧ S ⊆ X

/-- **A lower bound**: a nonempty static typing below the stamp. -/
def LowerAt (S : Set (Ty Empty)) (st : Stamp) : Prop := S.Nonempty ∧ Below S st

/-- The assignments of a row's variables sending each parameter into its static
typing. -/
def joint (Ts : List (Ty String)) (Ss : List (Set (Ty Empty))) : Set (String → Ty Empty) :=
  {θ | List.Forall₂ (fun T S => T.bind θ ∈ S) Ts Ss}

/-- The range of a combination: the range under every joint assignment. -/
def combo (Ts : List (Ty String)) (R : Ty String) (Ss : List (Set (Ty Empty))) : Set (Ty Empty) :=
  {T | ∃ θ ∈ joint Ts Ss, R.bind θ = T}

/-- **HE's check passes on lower bounds** wherever their joint assignments are
nonempty, with a valid typing allowing the range under them. -/
theorem semCheck_lower (ρ R : Ty String) :
    ∀ (Ts : List (Ty String)) (Ss : List (Set (Ty Empty))) (ss : List Stamp)
      (Θ : Set (String → Ty Empty)), List.Forall₂ Below Ss ss →
      {θ | θ ∈ Θ ∧ θ ∈ joint Ts Ss}.Nonempty →
      ∃ X, Sem.ok X ∈ semCheck ρ R Ts ss Θ ∧ {T | ∃ θ, (θ ∈ Θ ∧ θ ∈ joint Ts Ss) ∧ R.bind θ = T} ⊆ X
  | [], Ss, ss, Θ, below, ne => by
      obtain ⟨θ0, -, hj⟩ := ne
      have hSs : Ss = [] := by
        simp only [joint, Set.mem_ofPred_eq] at hj
        cases hj
        rfl
      subst hSs
      cases below
      refine ⟨{T | ∃ θ ∈ Θ, R.bind θ = T}, by simp [semCheck], ?_⟩
      rintro T ⟨θ, ⟨hθ, -⟩, rfl⟩
      exact ⟨θ, hθ, rfl⟩
  | P :: Ps, Ss, ss, Θ, below, ne => by
      obtain ⟨θ0, hθ0, hj0⟩ := ne
      obtain ⟨S, Ss', rfl⟩ : ∃ S Ss', Ss = S :: Ss' := by
        simp only [joint, Set.mem_ofPred_eq] at hj0
        cases hj0 with
        | cons _ _ => exact ⟨_, _, rfl⟩
      cases below with
      | cons hst rest =>
      rename_i st ss'
      have hjc : ∀ θ, θ ∈ joint (P :: Ps) (S :: Ss') ↔ P.bind θ ∈ S ∧ θ ∈ joint Ps Ss' := by
        intro θ
        simp only [joint, Set.mem_ofPred_eq, List.forall₂_cons]
      have hP0 := ((hjc θ0).mp hj0).1
      have hrest0 := ((hjc θ0).mp hj0).2
      simp only [semCheck]
      split_ifs with hskip hall hms
      · obtain ⟨X, hX, hsub⟩ := semCheck_lower ρ R Ps Ss' ss' Θ rest ⟨θ0, hθ0, hrest0⟩
        refine ⟨X, hX, fun T hT => hsub ?_⟩
        obtain ⟨θ, ⟨hθ, hj⟩, hT⟩ := hT
        exact ⟨θ, ⟨hθ, ((hjc θ).mp hj).2⟩, hT⟩
      · exfalso
        rcases hst with h1 | ⟨Y, hY, -⟩
        · simp [h1] at hskip
        · rw [List.all_eq_true] at hall
          simpa [Sem.isOk] using hall _ hY
      · exfalso
        rcases hst with h1 | ⟨Y, hY, hSY⟩
        · simp [h1] at hskip
        · have hmem : narrow Θ P Y ∈ st.typs.filterMap (semStep Θ P) := by
            rw [List.mem_filterMap]
            refine ⟨_, hY, ?_⟩
            have hne : (narrow Θ P Y).Nonempty := ⟨θ0, hθ0, hSY hP0⟩
            simp [semStep, hne]
          rw [List.isEmpty_iff] at hms
          rw [hms] at hmem
          cases hmem
      · rcases hst with h1 | ⟨Y, hY, hSY⟩
        · exact absurd (by simp [h1]) hskip
        · have hne : (narrow Θ P Y).Nonempty := ⟨θ0, hθ0, hSY hP0⟩
          have hmem : narrow Θ P Y ∈ st.typs.filterMap (semStep Θ P) := by
            rw [List.mem_filterMap]
            exact ⟨_, hY, by simp [semStep, hne]⟩
          obtain ⟨X, hX, hsub⟩ := semCheck_lower ρ R Ps Ss' ss' (narrow Θ P Y) rest
            ⟨θ0, ⟨hθ0, hSY hP0⟩, hrest0⟩
          refine ⟨X, List.mem_flatMap.mpr ⟨_, hmem, hX⟩, fun T hT => hsub ?_⟩
          obtain ⟨θ, ⟨hθ, hj⟩, hT⟩ := hT
          exact ⟨θ, ⟨⟨hθ, hSY ((hjc θ).mp hj).1⟩, ((hjc θ).mp hj).2⟩, hT⟩

/-- **Inversion of HE's check**: a valid typing of the check's result is the
range under a nonempty set of assignments the path allows, and every argument
is untyped, at a parameter HE does not check, or has a valid typing allowing the
parameter under all of them. -/
theorem semCheck_ok_inv (ρ R : Ty String) :
    ∀ (Ts : List (Ty String)) (ss : List Stamp) (Θ : Set (String → Ty Empty)) (X : Set (Ty Empty)),
      Θ.Nonempty → Sem.ok X ∈ semCheck ρ R Ts ss Θ →
      ∃ Θ' ⊆ Θ, Θ'.Nonempty ∧ X = {T | ∃ θ ∈ Θ', R.bind θ = T} ∧
        List.Forall₂ (fun T st => st.typs = [] ∨ heUnchecked T st.kind = true ∨
          ∃ Y, Sem.ok Y ∈ st.typs ∧ ∀ θ ∈ Θ', T.bind θ ∈ Y) Ts ss
  | [], [], Θ, X, hΘ, h => by
      simp only [semCheck, List.mem_singleton, Sem.ok.injEq] at h
      exact ⟨Θ, le_refl _, hΘ, h, .nil⟩
  | [], _ :: _, _, _, _, h => by simp [semCheck] at h
  | _ :: _, [], _, _, _, h => by simp [semCheck] at h
  | P :: Ps, st :: ss, Θ, X, hΘ, h => by
      simp only [semCheck] at h
      split_ifs at h with hskip hall hms
      · obtain ⟨Θ', hsub, hne, hX, rest⟩ := semCheck_ok_inv ρ R Ps ss Θ X hΘ h
        refine ⟨Θ', hsub, hne, hX, .cons ?_ rest⟩
        simp only [Bool.or_eq_true, List.isEmpty_iff] at hskip
        rcases hskip with h1 | h1
        · exact .inl h1
        · exact .inr (.inl h1)
      · rw [List.all_eq_true] at hall
        have := hall _ h
        simp [Sem.isOk] at this
      · simp only [List.mem_map, List.mem_filter] at h
        obtain ⟨_, _, h⟩ := h
        cases h
      · simp only [List.mem_flatMap, List.mem_filterMap] at h
        obtain ⟨Θ1, ⟨t, ht, hstep⟩, hX⟩ := h
        cases t with
        | err _ => simp [semStep] at hstep
        | ok Y =>
            simp only [semStep] at hstep
            split_ifs at hstep with hne
            cases hstep
            obtain ⟨Θ', hsub, hne', hXe, rest⟩ := semCheck_ok_inv ρ R Ps ss _ X hne hX
            refine ⟨Θ', fun θ hθ => (hsub hθ).1, hne', hXe, .cons (.inr (.inr ⟨Y, ht, ?_⟩)) rest⟩
            intro θ hθ
            exact (hsub hθ).2

/-- A row with a split arrow is a function row HE reads. -/
theorem split_fun {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (split : arrowSplit ρ = some (Ts, R)) : IsFun ρ = true ∧ readRows [ρ] = [ρ] := by
  match ρ, split with
  | .app (.sym s :: t :: ts), split =>
      simp only [arrowSplit] at split
      split_ifs at split with hs
      subst hs
      refine ⟨rfl, ?_⟩
      simp [readRows, undefinedTy]
  | .app [.sym s], split => simp [arrowSplit] at split

/-- **The stamp of an application of a constructor with one function row**:
HE's check of the row, or an arity error. -/
theorem stamp_ctor (Γ : Decls) (c : String) (ρ : Ty String) (Ts : List (Ty String)) (R : Ty String)
    (rows : Γ c = [ρ]) (split : arrowSplit ρ = some (Ts, R)) (args : List Atom) :
    stamp Γ (.expression (.symbol c :: args)) =
      ⟨"Expression", if Ts.length = args.length then semCheck ρ R Ts (args.map (stamp Γ)) Set.univ
        else [Sem.err (inst ρ)]⟩ := by
  obtain ⟨fn, read⟩ := split_fun split
  rw [stamp_node, rows]
  simp [semNode, read, fn, prodSets, semApp, split]

/-- The one function row of a constructor whose only declaration is a function
type: its parameters and range. -/
def ctorRow (Γ : Decls) (c : String) : Option (Ty String × List (Ty String) × Ty String) :=
  match Γ c with
  | [ρ] => (arrowSplit ρ).map fun p => (ρ, p.1, p.2)
  | _ => none

theorem ctorRow_spec {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (h : ctorRow Γ c = some (ρ, Ts, R)) : Γ c = [ρ] ∧ arrowSplit ρ = some (Ts, R) := by
  unfold ctorRow at h
  split at h
  · rename_i ρ' hc
    cases hs : arrowSplit ρ' with
    | none => simp [hs] at h
    | some p =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hc, by rw [hs]⟩
  · cases h

/-- **A build over lower bounds**: children below members whose joint
assignments are nonempty pass HE's check, and the built value is typed at least
as generally as the combination's range. -/
theorem build_lower {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) (Ss : List (Set (Ty Empty)))
    (below : List.Forall₂ Below Ss (args.map (stamp Γ))) (ne : (combo Ts R Ss).Nonempty) :
    LowerAt (combo Ts R Ss) (stamp Γ (.expression (.symbol c :: args))) := by
  obtain ⟨rows, split⟩ := ctorRow_spec row
  obtain ⟨T0, θ0, hj0, hT0⟩ := ne
  have len : Ts.length = args.length := by
    have h1 : Ts.length = Ss.length := List.Forall₂.length_eq hj0
    have h2 : Ss.length = (args.map (stamp Γ)).length := List.Forall₂.length_eq below
    simpa using h1.trans h2
  rw [stamp_ctor Γ c ρ Ts R rows split, if_pos len]
  obtain ⟨X, hX, hsub⟩ := semCheck_lower ρ R Ts Ss _ Set.univ below ⟨θ0, trivial, hj0⟩
  refine ⟨⟨T0, θ0, hj0, hT0⟩, .inr ⟨X, hX, fun T hT => hsub ?_⟩⟩
  obtain ⟨θ, hj, hT⟩ := hT
  exact ⟨θ, ⟨trivial, hj⟩, hT⟩

/-- HE's check at a lower bound has some valid typing: the joint assignments
being nonempty, the build's stamp holds a valid typing allowing the range under
them. -/
theorem build_typed {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) (Ss : List (Set (Ty Empty)))
    (below : List.Forall₂ Below Ss (args.map (stamp Γ))) (ne : (combo Ts R Ss).Nonempty) :
    ∃ X, Sem.ok X ∈ (stamp Γ (.expression (.symbol c :: args))).typs ∧ combo Ts R Ss ⊆ X := by
  obtain ⟨-, hb⟩ := build_lower row args Ss below ne
  rcases hb with h | h
  · exfalso
    obtain ⟨rows, split⟩ := ctorRow_spec row
    obtain ⟨T0, θ0, hj0, -⟩ := ne
    have len : Ts.length = args.length := by
      have h1 : Ts.length = Ss.length := List.Forall₂.length_eq hj0
      have h2 : Ss.length = (args.map (stamp Γ)).length := List.Forall₂.length_eq below
      simpa using h1.trans h2
    obtain ⟨X, hX, -⟩ := semCheck_lower ρ R Ts Ss _ Set.univ below ⟨θ0, trivial, hj0⟩
    rw [stamp_ctor Γ c ρ Ts R rows split, if_pos len] at h
    simp only at h
    rw [h] at hX
    cases hX
  · exact h

/-- A type HE checks at every kind of value: not `%Undefined%`, `Atom`, or a
metatype name. -/
def CheckedTy (T : Ty String) : Prop := ∀ v : Atom, heUnchecked T (metaName v) = false

theorem checked_stamp {T : Ty String} (h : CheckedTy T) (Γ : Decls) (v : Atom) :
    heUnchecked T (stamp Γ v).kind = false := by
  rw [stamp_kind]
  exact h v

/-- The typings a member gives a field: the field's declared type under every
assignment sending the range into the member. -/
def fieldOf (R T : Ty String) (M : Set (Ty Empty)) : Set (Ty Empty) :=
  {U | ∃ τ, R.bind τ ∈ M ∧ T.bind τ = U}

/-- The range fixes a field when every variable of the field's declared type is
one of the range's. -/
def Fixes (R T : Ty String) : Prop := ∀ x ∈ T.vars, x ∈ R.vars

theorem forall₂_getElem? {α β : Type} {Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Q l₁ l₂ →
      ∀ {k : ℕ} {a : α} {b : β}, l₁[k]? = some a → l₂[k]? = some b → Q a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons hab rest, 0, _, _, h1, h2 => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1
      subst h2
      exact hab
  | _, _, .cons _ rest, k + 1, _, _, h1, h2 => by
      simp only [List.getElem?_cons_succ] at h1 h2
      exact forall₂_getElem? rest h1 h2

theorem semCheck_ne_nil (ρ R : Ty String) :
    ∀ (Ts : List (Ty String)) (ss : List Stamp) (Θ : Set (String → Ty Empty)),
      Ts.length = ss.length → semCheck ρ R Ts ss Θ ≠ []
  | [], [], _, _ => by simp [semCheck]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | P :: Ps, st :: ss, Θ, h => by
      have len : Ps.length = ss.length := by simpa using h
      simp only [semCheck]
      split_ifs with hskip hall hms
      · exact semCheck_ne_nil ρ R Ps ss Θ len
      · intro hnil
        simp [hnil] at hskip
      · intro hnil
        have hok : ∃ t ∈ st.typs, t.isOk = true := by
          by_contra hno
          apply hall
          rw [List.all_eq_true]
          intro t ht
          cases hk : t.isOk
          · rfl
          · exact absurd ⟨t, ht, hk⟩ hno
        obtain ⟨t, ht, hokt⟩ := hok
        have : t ∈ st.typs.filter Sem.isOk := List.mem_filter.mpr ⟨ht, hokt⟩
        rw [List.map_eq_nil_iff] at hnil
        rw [hnil] at this
        cases this
      · intro hnil
        rw [List.isEmpty_iff] at hms
        obtain ⟨Θ1, hΘ1⟩ := List.exists_mem_of_ne_nil _ hms
        have := List.flatMap_eq_nil_iff.mp hnil Θ1 hΘ1
        exact semCheck_ne_nil ρ R Ps ss Θ1 len this

/-- **Field inversion on lower bounds**: a field of a constructor application
typed at least as generally as a member is typed at least as generally as the
field's declared type under the member, when the range fixes the field and HE
checks it. -/
theorem field_lower {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) {k : ℕ} {T : Ty String} {a : Atom}
    (hT : Ts[k]? = some T) (ha : args[k]? = some a) (fixes : Fixes R T) (checked : CheckedTy T)
    {M : Set (Ty Empty)} (lower : LowerAt M (stamp Γ (.expression (.symbol c :: args)))) :
    LowerAt (fieldOf R T M) (stamp Γ a) := by
  obtain ⟨rows, split⟩ := ctorRow_spec row
  obtain ⟨⟨m0, hm0⟩, below⟩ := lower
  rw [stamp_ctor Γ c ρ Ts R rows split] at below
  by_cases len : Ts.length = args.length
  swap
  · exfalso
    simp only [if_neg len] at below
    rcases below with h | ⟨X, hX, -⟩
    · cases h
    · simp at hX
  simp only [if_pos len] at below
  rcases below with h | ⟨X, hX, hMX⟩
  · exact absurd h (semCheck_ne_nil ρ R Ts _ Set.univ (by simpa using len))
  obtain ⟨Θ', -, -, hXe, each⟩ := semCheck_ok_inv ρ R Ts _ Set.univ X ⟨fun _ => default, trivial⟩ hX
  subst hXe
  have hsa : (args.map (stamp Γ))[k]? = some (stamp Γ a) := by simp [ha]
  have hfield := forall₂_getElem? each hT hsa
  have hne : (fieldOf R T M).Nonempty := by
    obtain ⟨θ, hθ, hRθ⟩ := hMX hm0
    exact ⟨T.bind θ, θ, by rw [hRθ]; exact hm0, rfl⟩
  refine ⟨hne, ?_⟩
  rcases hfield with h | h | ⟨Y, hY, hTY⟩
  · exact .inl h
  · rw [checked_stamp checked Γ a] at h
    cases h
  · refine .inr ⟨Y, hY, ?_⟩
    rintro U ⟨τ, hτ, rfl⟩
    obtain ⟨θ, hθ, hRθ⟩ := hMX hτ
    have agree := bind_eq_on_vars R hRθ
    rw [Ty.bind_congr T fun x hx => (agree x (fixes x hx)).symm]
    exact hTY θ hθ

/-- **An argument whose lower bound allows a closed formal meets it.** -/
theorem meets_of_lower {F : Ty Empty} {S : Set (Ty Empty)} {st : Stamp} (hF : F ∈ S)
    (h : LowerAt S st) : Meets F st := by
  rcases h.2 with h0 | ⟨X, hX, hSX⟩
  · exact .inl h0
  · exact .inr (.inr ⟨X, hX, hSX hF⟩)

/-- **A checked closed formal is a lower bound of what passes it.** -/
theorem lower_of_meets {Γ : Decls} {F : Ty Empty} (checked : CheckedTy F.lift) {v : Atom}
    (h : Meets F (stamp Γ v)) : LowerAt {F} (stamp Γ v) := by
  refine ⟨⟨F, rfl⟩, ?_⟩
  rcases h with h0 | h0 | ⟨X, hX, hFX⟩
  · exact .inl h0
  · rw [checked_stamp checked Γ v] at h0
    cases h0
  · exact .inr ⟨X, hX, by simpa using hFX⟩

/-- **HE's check at a formal that may have type variables**: the argument has no
typing, the formal is one HE does not check, or a valid typing allows some
instance of the formal (HE unifies a typing with a fresh copy of the formal). -/
def MeetsOpen (F : Ty String) (st : Stamp) : Prop :=
  st.typs = [] ∨ heUnchecked F st.kind = true ∨ ∃ φ : String → Ty Empty, Typable st (F.bind φ)

/-- At a closed formal it is the closed check. -/
theorem meetsOpen_lift (F : Ty Empty) (st : Stamp) : MeetsOpen F.lift st ↔ Meets F st := by
  simp only [MeetsOpen, Meets, Ty.lift_bind_ground]
  constructor
  · rintro (h | h | ⟨_, h⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (h | h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨fun _ => default, h⟩)

/-- A member allows an instance of a formal. -/
def AllowsInstance (F : Ty String) (S : Set (Ty Empty)) : Prop := ∃ φ : String → Ty Empty, F.bind φ ∈ S

/-- **A lower bound allowing an instance of the formal meets it.** -/
theorem meetsOpen_of_lower {F : Ty String} {S : Set (Ty Empty)} {st : Stamp} (hF : AllowsInstance F S)
    (h : LowerAt S st) : MeetsOpen F st := by
  obtain ⟨φ, hφ⟩ := hF
  rcases h.2 with h0 | ⟨X, hX, hSX⟩
  · exact .inl h0
  · exact .inr (.inr ⟨φ, X, hX, hSX hφ⟩)

/-- A formal without type variables has one instance. -/
theorem bind_closed {F : Ty String} (hF : F.vars = []) (φ ψ : String → Ty Empty) : F.bind φ = F.bind ψ :=
  Ty.bind_congr F fun x hx => by simp [hF] at hx

/-- **A checked formal without type variables is a lower bound of what passes
it**: its instances, all one type. -/
theorem lower_of_meetsOpen {Γ : Decls} {F : Ty String} (hF : F.vars = []) (checked : CheckedTy F)
    {v : Atom} (h : MeetsOpen F (stamp Γ v)) : LowerAt (inst F) (stamp Γ v) := by
  refine ⟨⟨F.bind fun _ => default, fun _ => default, rfl⟩, ?_⟩
  rcases h with h0 | h0 | ⟨φ, X, hX, hFX⟩
  · exact .inl h0
  · rw [checked_stamp checked Γ v] at h0
    cases h0
  · refine .inr ⟨X, hX, ?_⟩
    rintro T ⟨ψ, rfl⟩
    rw [bind_closed hF ψ φ]
    exact hFX

/-- The stamp of a symbol: its rows HE reads, each by its instances. -/
theorem stamp_symbol (Γ : Decls) (s : String) :
    stamp Γ (.symbol s) = ⟨"Symbol", (readRows (Γ s)).map fun τ => .ok (inst τ)⟩ := by
  simp only [stamp, heInfo_symbol, heLeaf, HeInfo.stamp, List.map_map]
  congr 1
  apply List.map_congr_left
  intro τ _
  simp only [Function.comp, rowTyping, Typing.solve]
  rw [show (⟨τ.map DVar.own, []⟩ : Deriv) = (rowTyping τ).deriv from rfl, sols_rowTyping]

theorem inst_nonempty (τ : Ty String) : (inst τ).Nonempty := ⟨τ.bind fun _ => default, fun _ => default, rfl⟩

/-! ## Typing sets -/

/-- A typing set: `none`, any typing; `some Ms`, the members, each read by its
ground instances. -/
abbrev TySet := Option (List (Set (Ty Empty)))

/-- **What a typing set says of a value**: nothing when unknown, and otherwise
that some member is a lower bound of the value's typing. -/
def Covers (Γ : Decls) : TySet → Atom → Prop
  | none, _ => True
  | some Ms, v => ∃ S ∈ Ms, LowerAt S (stamp Γ v)

/-- Inclusion of typing sets: unknown is the largest. -/
def Le : TySet → TySet → Prop
  | _, none => True
  | none, some _ => False
  | some Ms, some Ns => ∀ S ∈ Ms, S ∈ Ns

theorem Covers.mono {Γ : Decls} : ∀ {s t : TySet}, Le s t → ∀ {v : Atom}, Covers Γ s v → Covers Γ t v
  | _, none, _, _, _ => trivial
  | none, some _, h, _, _ => h.elim
  | some _, some _, h, _, ⟨S, hS, hl⟩ => ⟨S, h S hS, hl⟩

/-- The join of two typing sets. -/
def join : TySet → TySet → TySet
  | some Ms, some Ns => some (Ms ++ Ns)
  | _, _ => none

theorem covers_join_left {Γ : Decls} {s : TySet} (t : TySet) {v : Atom} (h : Covers Γ s v) :
    Covers Γ (join s t) v := by
  cases s with
  | none => cases t <;> trivial
  | some Ms =>
      cases t with
      | none => trivial
      | some Ns =>
          obtain ⟨S, hS, hl⟩ := h
          exact ⟨S, List.mem_append_left _ hS, hl⟩

theorem covers_join_right {Γ : Decls} (s : TySet) {t : TySet} {v : Atom} (h : Covers Γ t v) :
    Covers Γ (join s t) v := by
  cases t with
  | none => cases s <;> trivial
  | some Ns =>
      cases s with
      | none => trivial
      | some Ms =>
          obtain ⟨S, hS, hl⟩ := h
          exact ⟨S, List.mem_append_right _ hS, hl⟩

/-! ## The transfer functions -/

/-- A literal's typing set: a value's class, or a symbol's one row HE reads; any
other literal is unknown. -/
def litSet (Γ : Decls) : Atom → TySet
  | .grounded g => (valueClass g).map fun c => [{.sym c}]
  | .symbol s =>
      match readRows (Γ s) with
      | [τ] => some [inst τ]
      | _ => none
  | _ => none

theorem covers_lit (Γ : Decls) (a : Atom) : Covers Γ (litSet Γ a) a := by
  cases a with
  | grounded g =>
      cases hc : valueClass g with
      | none => simp [litSet, hc, Covers]
      | some c =>
          simp only [litSet, hc, Option.map_some]
          refine ⟨{.sym c}, List.mem_singleton_self _, ⟨.sym c, rfl⟩, .inr ⟨{.sym c}, ?_, le_refl _⟩⟩
          rw [literal_exact Γ g c hc]
          simp
  | symbol s =>
      simp only [litSet]
      split
      · rename_i τ hτ
        refine ⟨inst τ, List.mem_singleton_self _, inst_nonempty τ, .inr ⟨inst τ, ?_, le_refl _⟩⟩
        rw [stamp_symbol, hτ]
        simp
      · trivial
  | var x => trivial
  | expression xs => trivial

open Classical in
/-- **A field's typing set** (`prepared_pure_static_types`, a slot bound to a
field): each member's field typings, a member the range does not meet giving
none; unknown unless the range fixes the field and HE checks it. -/
noncomputable def fieldSet (Γ : Decls) (c : String) (k : ℕ) : TySet → TySet
  | none => none
  | some Ms =>
      match ctorRow Γ c with
      | some (_, Ts, R) =>
          match Ts[k]? with
          | some T =>
              if Fixes R T ∧ CheckedTy T then
                some ((Ms.map (fieldOf R T)).filter fun F => decide F.Nonempty)
              else none
          | none => none
      | none => none

theorem covers_field {Γ : Decls} {c : String} {k : ℕ} {S : TySet} {xs : List Atom} {a : Atom}
    (ha : xs[k]? = some a) (h : Covers Γ S (.expression (.symbol c :: xs))) :
    Covers Γ (fieldSet Γ c k S) a := by
  classical
  cases S with
  | none => trivial
  | some Ms =>
      simp only [fieldSet]
      split
      · rename_i ρ Ts R hrow
        split
        · rename_i T hT
          split_ifs with hfc
          · obtain ⟨M, hM, hl⟩ := h
            have hF := field_lower hrow xs hT ha hfc.1 hfc.2 hl
            refine ⟨fieldOf R T M, ?_, hF⟩
            exact List.mem_filter.mpr ⟨List.mem_map_of_mem hM, by simpa using hF.1⟩
          · trivial
        · trivial
      · trivial

/-- How a build's children's sets stand, read left to right as CeTTa reads
them: an unknown child, a child no value reaches, or every child's members. -/
inductive Scan where
  | any
  | empty
  | members (Mss : List (List (Set (Ty Empty))))

/-- A child's members in front of the rest's reading. -/
def Scan.cons (Ms : List (Set (Ty Empty))) : Scan → Scan
  | .members Mss => .members (Ms :: Mss)
  | s => s

theorem Scan.cons_empty {Ms : List (Set (Ty Empty))} {s : Scan} (h : s.cons Ms = .empty) : s = .empty := by
  cases s <;> simp_all [Scan.cons]

theorem Scan.cons_members {Ms : List (Set (Ty Empty))} {s : Scan} {Mss : List (List (Set (Ty Empty)))}
    (h : s.cons Ms = .members Mss) : ∃ Mss', s = .members Mss' ∧ Mss = Ms :: Mss' := by
  cases s with
  | members Mss' =>
      simp only [Scan.cons, Scan.members.injEq] at h
      exact ⟨Mss', rfl, h.symm⟩
  | any => cases h
  | empty => cases h

/-- Read the children's sets. -/
def scan : List TySet → Scan
  | [] => .members []
  | none :: _ => .any
  | some [] :: _ => .empty
  | some (M :: Ms) :: rest => (scan rest).cons (M :: Ms)

open Classical in
/-- **A checked build's typing set** (`prepared_pure_static_build_types`):
the range of every combination of its children's members, read jointly with
fresh variables, when every combination passes; no value when a child has none;
unknown otherwise. -/
noncomputable def buildSet (Γ : Decls) (c : String) (kids : List TySet) : TySet :=
  match ctorRow Γ c with
  | none => none
  | some (_, Ts, R) =>
      if Ts.length = kids.length then
        match scan kids with
        | .any => none
        | .empty => some []
        | .members Mss =>
            if ∀ Ss ∈ Mss.sections, (combo Ts R Ss).Nonempty then some (Mss.sections.map (combo Ts R))
            else none
      else none

/-- **A build discharged**: every combination of its children's members passes
the constructor's check, or a child has no value. -/
def BuildPasses (Γ : Decls) (c : String) (kids : List TySet) : Prop :=
  ∃ ρ Ts R, ctorRow Γ c = some (ρ, Ts, R) ∧ Ts.length = kids.length ∧
    (scan kids = .empty ∨ ∃ Mss, scan kids = .members Mss ∧ ∀ Ss ∈ Mss.sections, (combo Ts R Ss).Nonempty)

theorem scan_empty_false {Γ : Decls} :
    ∀ {kids : List TySet} {ws : List Atom}, List.Forall₂ (Covers Γ) kids ws → scan kids = .empty → False
  | [], [], .nil, h => by simp [scan] at h
  | none :: _, _ :: _, .cons _ _, h => by simp [scan] at h
  | some [] :: _, _ :: _, .cons hc _, _ => by
      obtain ⟨S, hS, _⟩ := hc
      cases hS
  | some (M :: Ms) :: rest, _ :: ws, .cons _ hrest, h => by
      simp only [scan] at h
      exact scan_empty_false hrest (Scan.cons_empty h)

theorem scan_members_cover {Γ : Decls} :
    ∀ {kids : List TySet} {ws : List Atom} {Mss : List (List (Set (Ty Empty)))},
      List.Forall₂ (Covers Γ) kids ws → scan kids = .members Mss →
      ∃ Ss ∈ Mss.sections, List.Forall₂ (fun S w => LowerAt S (stamp Γ w)) Ss ws
  | [], [], Mss, .nil, h => by
      simp only [scan, Scan.members.injEq] at h
      subst h
      exact ⟨[], by simp, .nil⟩
  | none :: _, _ :: _, _, .cons _ _, h => by simp [scan] at h
  | some [] :: _, _ :: _, _, .cons _ _, h => by simp [scan] at h
  | some (M :: Ms) :: rest, w :: ws, Mss, .cons hc hrest, h => by
      simp only [scan] at h
      obtain ⟨Mss', hs, rfl⟩ := Scan.cons_members h
      obtain ⟨Ss, hSs, each⟩ := scan_members_cover hrest hs
      obtain ⟨S, hS, hl⟩ := hc
      refine ⟨S :: Ss, ?_, .cons hl each⟩
      rw [List.mem_sections] at hSs ⊢
      exact .cons hS hSs

theorem below_of_lower {Γ : Decls} :
    ∀ {Ss : List (Set (Ty Empty))} {ws : List Atom},
      List.Forall₂ (fun S w => LowerAt S (stamp Γ w)) Ss ws → List.Forall₂ Below Ss (ws.map (stamp Γ))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h rest => .cons h.2 (below_of_lower rest)

/-- **A build's set covers its value.** -/
theorem covers_build {Γ : Decls} {c : String} {kids : List TySet} {ws : List Atom}
    (cov : List.Forall₂ (Covers Γ) kids ws) : Covers Γ (buildSet Γ c kids) (.expression (.symbol c :: ws)) := by
  unfold buildSet
  split
  · trivial
  · rename_i ρ Ts R hrow
    split_ifs with len
    · split
      · trivial
      · rename_i hs
        exact (scan_empty_false cov hs).elim
      · rename_i Mss hs
        split_ifs with hall
        · obtain ⟨Ss, hSs, each⟩ := scan_members_cover cov hs
          have ne := hall Ss hSs
          exact ⟨combo Ts R Ss, List.mem_map_of_mem hSs, build_lower hrow ws Ss (below_of_lower each) ne⟩
        · trivial
    · trivial

/-- What HE's check of a build reads: the built value has a valid typing. -/
def HEPasses (Γ : Decls) (c : String) (ws : List Atom) : Prop :=
  ∃ X, Sem.ok X ∈ (stamp Γ (.expression (.symbol c :: ws))).typs

/-- **A discharged build passes HE's check** on every covered children. -/
theorem passes_of_buildPasses {Γ : Decls} {c : String} {kids : List TySet} {ws : List Atom}
    (cov : List.Forall₂ (Covers Γ) kids ws) (h : BuildPasses Γ c kids) : HEPasses Γ c ws := by
  obtain ⟨ρ, Ts, R, hrow, -, hs⟩ := h
  rcases hs with hs | ⟨Mss, hs, hall⟩
  · exact (scan_empty_false cov hs).elim
  · obtain ⟨Ss, hSs, each⟩ := scan_members_cover cov hs
    obtain ⟨X, hX, -⟩ := build_typed hrow ws Ss (below_of_lower each) (hall Ss hSs)
    exact ⟨X, hX⟩

/-! ## Programs -/

/-- The nodes of a body, as the prepared program has them. A `call`'s flags
mark the arguments whose formal check is discharged, a `build`'s flag a
discharged check. -/
inductive Node where
  | slot (s : ℕ)
  | lit (a : Atom)
  | reg (cls : String) (args : List Node)
  | data (c : String) (args : List Node)
  | call (h : String) (args : List Node) (skip : List Bool)
  | dyncall (f : Node) (args : List Node)
  | build (c : String) (args : List Node) (skip : Bool)
  | ite (c t e : Node)
  | bind (s : ℕ) (v b : Node)

/-- Where an equation binds a slot: argument `i`, field `k` of argument `i`
matched by the constructor `c`, or elsewhere (deeper in a pattern, or a local). -/
inductive Origin where
  | whole (i : ℕ)
  | field (i : ℕ) (c : String) (k : ℕ)
  | other

/-- An equation: its arity, where its pattern binds each slot, and its body. -/
structure Eqn where
  arity : ℕ
  origin : ℕ → Origin
  body : Node

/-- A closed program: each head's equations; a typed head's formals (a type,
with or without type variables, or unchecked) and closed range; the typed heads
whose returns are discharged; the symbols the program names as values; the run's
body. Formals with type variables are checked one by one, as CeTTa admits them
only where no two share a variable. -/
structure Program where
  eqs : String → List Eqn
  formals : String → Option (List (Option (Ty String)))
  range : String → Option (Ty Empty)
  shown : String → Bool
  named : Set String
  main : Node

/-- The inferred sets: each untyped head's parameters and answer. -/
structure Stored where
  param : String → ℕ → TySet
  answer : String → TySet

/-! ### HE's semantics -/

/-- What a pattern binds at a slot, from the arguments. -/
def MatchSlot : Origin → List Atom → Atom → Prop
  | .whole i, ws, x => ws[i]? = some x
  | .field i c k, ws, x => ∃ xs, ws[i]? = some (.expression (.symbol c :: xs)) ∧ xs[k]? = some x
  | .other, _, _ => True

/-- An equation matches the arguments with an environment of its slots. -/
def Matches (e : Eqn) (ws : List Atom) (env : ℕ → Atom) : Prop :=
  ws.length = e.arity ∧ ∀ s, MatchSlot (e.origin s) ws (env s)

/-- A typed call's argument checks; in the prepared run (`prep`) a discharged
argument is not checked. -/
def ArgsChecked (Γ : Decls) (P : Program) (prep : Bool) (h : String) (skip : List Bool)
    (ws : List Atom) : Prop :=
  match P.formals h with
  | none => True
  | some Fs => Fs.length = ws.length ∧ ∀ (j : ℕ) (F : Ty String) (w : Atom), Fs[j]? = some (some F) →
      ws[j]? = some w → (prep = true ∧ skip[j]? = some true) ∨ MeetsOpen F (stamp Γ w)

/-- A typed call's return check; in the prepared run a shown return is not
checked. -/
def RangeChecked (Γ : Decls) (P : Program) (prep : Bool) (h : String) (r : Atom) : Prop :=
  ∀ R, P.range h = some R → (prep = true ∧ P.shown h = true) ∨ Meets R (stamp Γ r)

/-- **The values a node reaches** in an environment of its slots: HE's
semantics of the program at `prep = false`, every check made; the prepared
semantics at `prep = true`, the discharged checks skipped. A call runs an
equation that matches its arguments; a dynamic call reaches a head the program
names as a value. -/
inductive Reach (Γ : Decls) (P : Program) (prep : Bool) : (ℕ → Atom) → Node → Atom → Prop
  | slot (env : ℕ → Atom) (s : ℕ) : Reach Γ P prep env (.slot s) (env s)
  | lit (env : ℕ → Atom) (a : Atom) : Reach Γ P prep env (.lit a) a
  | reg (env : ℕ → Atom) (cls : String) (args : List Node) (ws : List Atom) (g : GroundedValue)
      (len : args.length = ws.length) (each : ∀ p ∈ args.zip ws, Reach Γ P prep env p.1 p.2)
      (hg : valueClass g = some cls) : Reach Γ P prep env (.reg cls args) (.grounded g)
  | data (env : ℕ → Atom) (c : String) (args : List Node) (ws : List Atom)
      (len : args.length = ws.length) (each : ∀ p ∈ args.zip ws, Reach Γ P prep env p.1 p.2) :
      Reach Γ P prep env (.data c args) (.expression (.symbol c :: ws))
  | call (env : ℕ → Atom) (h : String) (args : List Node) (skip : List Bool) (ws : List Atom)
      (e : Eqn) (env' : ℕ → Atom) (r : Atom)
      (len : args.length = ws.length) (each : ∀ p ∈ args.zip ws, Reach Γ P prep env p.1 p.2)
      (he : e ∈ P.eqs h) (hm : Matches e ws env') (hc : ArgsChecked Γ P prep h skip ws)
      (hr : Reach Γ P prep env' e.body r) (hrange : RangeChecked Γ P prep h r) :
      Reach Γ P prep env (.call h args skip) r
  | dyncall (env : ℕ → Atom) (f : Node) (h : String) (args : List Node) (ws : List Atom)
      (e : Eqn) (env' : ℕ → Atom) (r : Atom) (hf : Reach Γ P prep env f (.symbol h))
      (named : h ∈ P.named)
      (len : args.length = ws.length) (each : ∀ p ∈ args.zip ws, Reach Γ P prep env p.1 p.2)
      (he : e ∈ P.eqs h) (hm : Matches e ws env') (hc : ArgsChecked Γ P prep h [] ws)
      (hr : Reach Γ P prep env' e.body r) (hrange : RangeChecked Γ P prep h r) :
      Reach Γ P prep env (.dyncall f args) r
  | build (env : ℕ → Atom) (c : String) (args : List Node) (skip : Bool) (ws : List Atom)
      (len : args.length = ws.length) (each : ∀ p ∈ args.zip ws, Reach Γ P prep env p.1 p.2)
      (hc : (prep = true ∧ skip = true) ∨ HEPasses Γ c ws) :
      Reach Γ P prep env (.build c args skip) (.expression (.symbol c :: ws))
  | iteT (env : ℕ → Atom) (c t e : Node) (w r : Atom) (hc : Reach Γ P prep env c w)
      (ht : Reach Γ P prep env t r) : Reach Γ P prep env (.ite c t e) r
  | iteE (env : ℕ → Atom) (c t e : Node) (w r : Atom) (hc : Reach Γ P prep env c w)
      (he : Reach Γ P prep env e r) : Reach Γ P prep env (.ite c t e) r
  | bind (env : ℕ → Atom) (s : ℕ) (v b : Node) (w r : Atom) (hv : Reach Γ P prep env v w)
      (hb : Reach Γ P prep (Function.update env s w) b r) : Reach Γ P prep env (.bind s v b) r

theorem Reach.lit_inv {Γ : Decls} {P : Program} {prep : Bool} {env : ℕ → Atom} {a v : Atom}
    (h : Reach Γ P prep env (.lit a) v) : v = a := by
  cases h
  rfl

theorem Reach.slot_inv {Γ : Decls} {P : Program} {prep : Bool} {env : ℕ → Atom} {s : ℕ} {v : Atom}
    (h : Reach Γ P prep env (.slot s) v) : v = env s := by
  cases h
  rfl

theorem Reach.build_inv {Γ : Decls} {P : Program} {prep : Bool} {env : ℕ → Atom} {c : String}
    {args : List Node} {skip : Bool} {v : Atom} (h : Reach Γ P prep env (.build c args skip) v) :
    ∃ ws, v = .expression (.symbol c :: ws) ∧ args.length = ws.length ∧
      (∀ p ∈ args.zip ws, Reach Γ P prep env p.1 p.2) ∧ ((prep = true ∧ skip = true) ∨ HEPasses Γ c ws) := by
  cases h with
  | build _ _ _ _ ws len each hc => exact ⟨ws, rfl, len, each, hc⟩

/-! ### The analysis -/

/-- A head's parameter set: an untyped head's inferred one, a typed head's
formal where it has no type variable, the inferred one at a formal with type
variables (`prepared_pure_inferred_site`), unknown at an unchecked formal. -/
def paramSet (P : Program) (St : Stored) (h : String) (i : ℕ) : TySet :=
  match P.formals h with
  | none => St.param h i
  | some Fs =>
      match Fs[i]? with
      | some (some F) => if F.vars = [] then some [inst F] else St.param h i
      | _ => none

/-- A call's set: an untyped head's inferred answer, a typed head's closed
range. -/
def callSet (P : Program) (St : Stored) (h : String) : TySet :=
  match P.formals h with
  | none => St.answer h
  | some _ => (P.range h).map fun R => [{R}]

/-- The sets of an equation's slots on entry. -/
noncomputable def entryEnv (Γ : Decls) (P : Program) (St : Stored) (h : String) (e : Eqn) :
    ℕ → TySet := fun s =>
  match e.origin s with
  | .whole i => paramSet P St h i
  | .field i c k => fieldSet Γ c k (paramSet P St h i)
  | .other => none

mutual
/-- **The typing set of a node** under the sets of its slots. -/
noncomputable def absNode (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → Node → TySet
  | aenv, .slot s => aenv s
  | _, .lit a => litSet Γ a
  | _, .reg cls _ => some [{.sym cls}]
  | _, .data _ _ => none
  | _, .call h _ _ => callSet P St h
  | _, .dyncall _ _ => none
  | aenv, .build c args _ => buildSet Γ c (absNodes Γ P St aenv args)
  | aenv, .ite _ t e => join (absNode Γ P St aenv t) (absNode Γ P St aenv e)
  | aenv, .bind s v b => absNode Γ P St (Function.update aenv s (absNode Γ P St aenv v)) b
/-- The typing sets of a list of nodes. -/
noncomputable def absNodes (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → List Node → List TySet
  | _, [] => []
  | aenv, n :: ns => absNode Γ P St aenv n :: absNodes Γ P St aenv ns
end

theorem absNodes_eq_map (Γ : Decls) (P : Program) (St : Stored) (aenv : ℕ → TySet) :
    ∀ ns : List Node, absNodes Γ P St aenv ns = ns.map (absNode Γ P St aenv)
  | [] => by simp [absNodes]
  | n :: ns => by simp [absNodes, absNodes_eq_map Γ P St aenv ns]

/-- A call site's conditions: an untyped callee's parameters, and a typed
callee's parameters at formals with type variables, hold its arguments' sets; a
typed callee's discharged argument has only members allowing an instance of its
formal (`prepared_pure_discharged_arguments`). -/
def CallOK (P : Program) (St : Stored) (h : String) (kids : List TySet) (skip : List Bool) : Prop :=
  match P.formals h with
  | none => ∀ (j : ℕ) (k : TySet), kids[j]? = some k → Le k (St.param h j)
  | some Fs => (∀ j : ℕ, skip[j]? = some true →
      ∃ F : Ty String, Fs[j]? = some (some F) ∧ ∃ Ms, kids[j]? = some (some Ms) ∧
        ∀ S ∈ Ms, AllowsInstance F S) ∧
    ∀ (j : ℕ) (F : Ty String) (k : TySet), Fs[j]? = some (some F) → F.vars ≠ [] → kids[j]? = some k →
      Le k (St.param h j)

mutual
/-- **The conditions a body asks of the sets**, with its lets in scope: every
call site's (`CallOK`), and every discharged build's (`BuildPasses`). -/
def Walk (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → Node → Prop
  | _, .slot _ => True
  | _, .lit _ => True
  | aenv, .reg _ args => WalkAll Γ P St aenv args
  | aenv, .data _ args => WalkAll Γ P St aenv args
  | aenv, .call h args skip => WalkAll Γ P St aenv args ∧ CallOK P St h (absNodes Γ P St aenv args) skip
  | aenv, .dyncall f args => Walk Γ P St aenv f ∧ WalkAll Γ P St aenv args
  | aenv, .build c args skip =>
      WalkAll Γ P St aenv args ∧ (skip = true → BuildPasses Γ c (absNodes Γ P St aenv args))
  | aenv, .ite c t e => Walk Γ P St aenv c ∧ Walk Γ P St aenv t ∧ Walk Γ P St aenv e
  | aenv, .bind s v b =>
      Walk Γ P St aenv v ∧ Walk Γ P St (Function.update aenv s (absNode Γ P St aenv v)) b
/-- The conditions of a list of nodes. -/
def WalkAll (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → List Node → Prop
  | _, [] => True
  | aenv, n :: ns => Walk Γ P St aenv n ∧ WalkAll Γ P St aenv ns
end

theorem walkAll_iff (Γ : Decls) (P : Program) (St : Stored) (aenv : ℕ → TySet) :
    ∀ ns : List Node, WalkAll Γ P St aenv ns ↔ ∀ n ∈ ns, Walk Γ P St aenv n
  | [] => by simp [WalkAll]
  | n :: ns => by simp [WalkAll, walkAll_iff Γ P St aenv ns]

/-- **A fixpoint of the analysis** (a post-fixpoint suffices): every body's
conditions hold under its entry sets; every untyped head's answer holds its
equations' bodies' sets; every head the program names as a value has unknown
parameters; a shown return's every member allows the range. -/
structure PostFix (Γ : Decls) (P : Program) (St : Stored) : Prop where
  main : Walk Γ P St (fun _ => none) P.main
  eqs : ∀ h, ∀ e ∈ P.eqs h, Walk Γ P St (entryEnv Γ P St h e) e.body
  answers : ∀ h, P.formals h = none → ∀ e ∈ P.eqs h,
    Le (absNode Γ P St (entryEnv Γ P St h e) e.body) (St.answer h)
  escaped : ∀ h, h ∈ P.named → ∀ j, St.param h j = none
  shown : ∀ h R, P.range h = some R → P.shown h = true → ∀ e ∈ P.eqs h,
    ∃ Ms, absNode Γ P St (entryEnv Γ P St h e) e.body = some Ms ∧ ∀ S ∈ Ms, R ∈ S

/-- Typed heads check their formals and range at every kind of value. -/
structure WF (Γ : Decls) (P : Program) : Prop where
  formals : ∀ h Fs, P.formals h = some Fs → ∀ F, some F ∈ Fs → CheckedTy F
  range : ∀ h R, P.range h = some R → CheckedTy R.lift

/-- The slots' values are covered by their sets. -/
def EnvCovers (Γ : Decls) (aenv : ℕ → TySet) (env : ℕ → Atom) : Prop := ∀ s, Covers Γ (aenv s) (env s)

theorem envCovers_update {Γ : Decls} {aenv : ℕ → TySet} {env : ℕ → Atom} (h : EnvCovers Γ aenv env)
    (s : ℕ) {S : TySet} {w : Atom} (hw : Covers Γ S w) :
    EnvCovers Γ (Function.update aenv s S) (Function.update env s w) := by
  intro t
  by_cases hts : t = s
  · subst hts
    simpa using hw
  · simpa [Function.update, hts] using h t

theorem forall₂_of_zip {α β : Type} {Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → (∀ p ∈ l₁.zip l₂, Q p.1 p.2) →
      List.Forall₂ Q l₁ l₂
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l₁, b :: l₂, h, each =>
      .cons (each (a, b) (by simp)) (forall₂_of_zip (by simpa using h)
        fun p hp => each p (by simp [hp]))

/-- **Arguments entering an equation cover its entry sets**: a whole argument
its parameter's set, a field its field set. -/
theorem entry_covers {Γ : Decls} {P : Program} {St : Stored} {h : String} {e : Eqn} {ws : List Atom}
    {env' : ℕ → Atom} (hm : Matches e ws env')
    (hargs : ∀ (i : ℕ) (w : Atom), ws[i]? = some w → Covers Γ (paramSet P St h i) w) :
    EnvCovers Γ (entryEnv Γ P St h e) env' := by
  intro s
  have hs := hm.2 s
  simp only [entryEnv]
  split
  · rename_i i hi
    rw [hi] at hs
    exact hargs i _ hs
  · rename_i i c k hi
    rw [hi] at hs
    obtain ⟨xs, hxs, hk⟩ := hs
    exact covers_field hk (hargs i _ hxs)
  · trivial

/-- **A typed call's arguments cover its formals' sets**: at a formal without
type variables by HE's check, at one with type variables by the inferred set
holding the argument (`opens`). -/
theorem typed_args_cover {Γ : Decls} {P : Program} (wf : WF Γ P) (St : Stored) {h : String}
    {Fs : List (Option (Ty String))} (hF : P.formals h = some Fs) {ws : List Atom}
    {skip : List Bool} (hc : ArgsChecked Γ P false h skip ws)
    (opens : ∀ (i : ℕ) (F : Ty String) (w : Atom), Fs[i]? = some (some F) → F.vars ≠ [] →
      ws[i]? = some w → Covers Γ (St.param h i) w) :
    ∀ (i : ℕ) (w : Atom), ws[i]? = some w → Covers Γ (paramSet P St h i) w := by
  intro i w hw
  simp only [ArgsChecked, hF] at hc
  simp only [paramSet, hF]
  split
  · rename_i F hFi
    split_ifs with hclosed
    · have hmeets : MeetsOpen F (stamp Γ w) := by
        rcases hc.2 i F w hFi hw with hs | hm
        · cases hs.1
        · exact hm
      exact ⟨inst F, List.mem_singleton_self _, lower_of_meetsOpen hclosed (wf.formals h Fs hF F
        (List.mem_of_getElem? hFi)) hmeets⟩
    · exact opens i F w hFi hclosed hw
  · trivial

/-- **Soundness of the analysis**: on HE's semantics, every value a node reaches
in an environment covered by the slots' sets, under a fixpoint, is covered by the
node's set. -/
theorem sound {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {env : ℕ → Atom} {n : Node} {v : Atom} (hr : Reach Γ P false env n v) :
    ∀ aenv, EnvCovers Γ aenv env → Walk Γ P St aenv n → Covers Γ (absNode Γ P St aenv n) v := by
  induction hr with
  | slot env s => intro aenv hcov _; exact hcov s
  | lit env a => intro _ _ _; exact covers_lit Γ a
  | reg env cls args ws g len each hg each_ih =>
      intro _ _ _
      simp only [absNode]
      refine ⟨{.sym cls}, List.mem_singleton_self _, ⟨.sym cls, rfl⟩, .inr ⟨{.sym cls}, ?_, le_refl _⟩⟩
      rw [literal_exact Γ g cls hg]
      simp
  | data env c args ws len each each_ih => intro _ _ _; trivial
  | call env h args skip ws e env' r len each he hm hc hr hrange each_ih hr_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      obtain ⟨hwa, hok⟩ := hwalk
      have kids : List.Forall₂ (Covers Γ) (absNodes Γ P St aenv args) ws := by
        rw [absNodes_eq_map]
        refine List.forall₂_map_left_iff.mpr (forall₂_of_zip len fun p hp => ?_)
        exact each_ih p hp aenv hcov ((walkAll_iff Γ P St aenv args).mp hwa p.1 (List.of_mem_zip hp).1)
      simp only [absNode, callSet]
      cases hF : P.formals h with
      | none =>
          simp only [CallOK, hF] at hok
          have hargs : ∀ (i : ℕ) (w : Atom), ws[i]? = some w → Covers Γ (paramSet P St h i) w := by
            intro i w hw
            simp only [paramSet, hF]
            have hlen : (absNodes Γ P St aenv args).length = ws.length := kids.length_eq
            obtain ⟨k, hk⟩ : ∃ k, (absNodes Γ P St aenv args)[i]? = some k := by
              have hi : i < ws.length := (List.getElem?_eq_some_iff.mp hw).1
              exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
            exact Covers.mono (hok i k hk) (forall₂_getElem? kids hk hw)
          have hbody := hr_ih (entryEnv Γ P St h e) (entry_covers hm hargs) (fix.eqs h e he)
          exact Covers.mono (fix.answers h hF e he) hbody
      | some Fs =>
          cases hR : P.range h with
          | none => trivial
          | some R =>
              have hmeets : Meets R (stamp Γ r) := by
                rcases hrange R hR with h1 | h1
                · cases h1.1
                · exact h1
              exact ⟨{R}, List.mem_singleton_self _, lower_of_meets (wf.range h R hR) hmeets⟩
  | dyncall => intro _ _ _; trivial
  | build env c args skip ws len each hc each_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      simp only [absNode]
      apply covers_build
      rw [absNodes_eq_map]
      refine List.forall₂_map_left_iff.mpr (forall₂_of_zip len fun p hp => ?_)
      exact each_ih p hp aenv hcov ((walkAll_iff Γ P St aenv args).mp hwalk.1 p.1 (List.of_mem_zip hp).1)
  | iteT env c t e w r hc ht hc_ih ht_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      simp only [absNode]
      exact covers_join_left _ (ht_ih aenv hcov hwalk.2.1)
  | iteE env c t e w r hc he hc_ih he_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      simp only [absNode]
      exact covers_join_right _ (he_ih aenv hcov hwalk.2.2)
  | bind env s v b w r hv hb hv_ih hb_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      simp only [absNode]
      exact hb_ih _ (envCovers_update hcov s (hv_ih aenv hcov hwalk.1)) hwalk.2

/-- The children of a node, covered: what `sound` gives at every child. -/
theorem kids_cover {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {env : ℕ → Atom} {args : List Node} {ws : List Atom} (len : args.length = ws.length)
    (each : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2) {aenv : ℕ → TySet}
    (hcov : EnvCovers Γ aenv env) (hwa : WalkAll Γ P St aenv args) :
    List.Forall₂ (Covers Γ) (absNodes Γ P St aenv args) ws := by
  rw [absNodes_eq_map]
  refine List.forall₂_map_left_iff.mpr (forall₂_of_zip len fun p hp => ?_)
  exact sound fix wf (each p hp) aenv hcov ((walkAll_iff Γ P St aenv args).mp hwa p.1 (List.of_mem_zip hp).1)

/-- **A discharged build passes HE's check** wherever HE's run reaches its
children. -/
theorem discharged_build_passes {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St)
    (wf : WF Γ P) {env : ℕ → Atom} {aenv : ℕ → TySet} (hcov : EnvCovers Γ aenv env) {c : String}
    {args : List Node} (hwalk : Walk Γ P St aenv (.build c args true)) {ws : List Atom}
    (len : args.length = ws.length) (each : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2) :
    HEPasses Γ c ws := by
  simp only [Walk] at hwalk
  exact passes_of_buildPasses (kids_cover fix wf len each hcov hwalk.1) (by simpa using hwalk.2)

/-- **A discharged argument meets its formal** wherever HE's run reaches it, at a
formal with or without type variables. -/
theorem discharged_arg_meets {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St)
    (wf : WF Γ P) {env : ℕ → Atom} {aenv : ℕ → TySet} (hcov : EnvCovers Γ aenv env) {h : String}
    {args : List Node} {skip : List Bool} (hwalk : Walk Γ P St aenv (.call h args skip))
    {Fs : List (Option (Ty String))} (hF : P.formals h = some Fs) {ws : List Atom}
    (len : args.length = ws.length) (each : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2)
    {j : ℕ} (hj : skip[j]? = some true) {F : Ty String} (hFj : Fs[j]? = some (some F)) {w : Atom}
    (hw : ws[j]? = some w) : MeetsOpen F (stamp Γ w) := by
  simp only [Walk] at hwalk
  obtain ⟨hwa, hok⟩ := hwalk
  simp only [CallOK, hF] at hok
  obtain ⟨F', hF', Ms, hMs, hall⟩ := hok.1 j hj
  rw [hFj] at hF'
  cases hF'
  obtain ⟨S, hS, hl⟩ := forall₂_getElem? (kids_cover fix wf len each hcov hwa) hMs hw
  exact meetsOpen_of_lower (hall S hS) hl

/-- HE's run is a prepared run. -/
theorem prepared_of_he {Γ : Decls} {P : Program} {env : ℕ → Atom} {n : Node} {v : Atom}
    (h : Reach Γ P false env n v) : Reach Γ P true env n v := by
  induction h with
  | slot env s => exact .slot env s
  | lit env a => exact .lit env a
  | reg env cls args ws g len each hg each_ih => exact .reg env cls args ws g len each_ih hg
  | data env c args ws len each each_ih => exact .data env c args ws len each_ih
  | call env h args skip ws e env' r len each he hm hc hr hrange each_ih hr_ih =>
      refine .call env h args skip ws e env' r len each_ih he hm ?_ hr_ih ?_
      · simp only [ArgsChecked] at hc ⊢
        split
        · trivial
        · rename_i Fs hF
          rw [hF] at hc
          exact ⟨hc.1, fun j F w h1 h2 => .inr ((hc.2 j F w h1 h2).resolve_left fun h => by cases h.1)⟩
      · intro R hR
        exact .inr ((hrange R hR).resolve_left fun h => by cases h.1)
  | dyncall env f h args ws e env' r hf named len each he hm hc hr hrange hf_ih each_ih hr_ih =>
      refine .dyncall env f h args ws e env' r hf_ih named len each_ih he hm ?_ hr_ih ?_
      · simp only [ArgsChecked] at hc ⊢
        split
        · trivial
        · rename_i Fs hF
          rw [hF] at hc
          exact ⟨hc.1, fun j F w h1 h2 => .inr ((hc.2 j F w h1 h2).resolve_left fun h => by cases h.1)⟩
      · intro R hR
        exact .inr ((hrange R hR).resolve_left fun h => by cases h.1)
  | build env c args skip ws len each hc each_ih =>
      exact .build env c args skip ws len each_ih (.inr (hc.resolve_left fun h => by cases h.1))
  | iteT env c t e w r hc ht hc_ih ht_ih => exact .iteT env c t e w r hc_ih ht_ih
  | iteE env c t e w r hc he hc_ih he_ih => exact .iteE env c t e w r hc_ih he_ih
  | bind env s v b w r hv hb hv_ih hb_ih => exact .bind env s v b w r hv_ih hb_ih

/-- The checks a typed call makes in HE's run, from the prepared run's: a
discharged argument meets its formal. -/
theorem args_checked_he {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {env : ℕ → Atom} {aenv : ℕ → TySet} (hcov : EnvCovers Γ aenv env) {h : String} {args : List Node}
    {skip : List Bool} {ws : List Atom} (len : args.length = ws.length)
    (each : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2) (hwalk : Walk Γ P St aenv (.call h args skip))
    (hc : ArgsChecked Γ P true h skip ws) : ArgsChecked Γ P false h skip ws := by
  simp only [ArgsChecked] at hc ⊢
  split
  · trivial
  · rename_i Fs hF
    rw [hF] at hc
    refine ⟨hc.1, fun j F w h1 h2 => .inr ?_⟩
    rcases hc.2 j F w h1 h2 with hs | hm
    · exact discharged_arg_meets fix wf hcov hwalk hF len each hs.2 h1 h2
    · exact hm

/-- An equation entered by a call of HE's run: its slots are covered. -/
theorem entry_covers_he {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {env : ℕ → Atom} {aenv : ℕ → TySet} (hcov : EnvCovers Γ aenv env) {h : String} {args : List Node}
    {skip : List Bool} {ws : List Atom} (len : args.length = ws.length)
    (each : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2) (hwalk : Walk Γ P St aenv (.call h args skip))
    (hc : ArgsChecked Γ P false h skip ws) {e : Eqn} {env' : ℕ → Atom} (hm : Matches e ws env') :
    EnvCovers Γ (entryEnv Γ P St h e) env' := by
  apply entry_covers hm
  cases hF : P.formals h with
  | none =>
      intro i w hw
      simp only [paramSet, hF]
      simp only [Walk] at hwalk
      obtain ⟨hwa, hok⟩ := hwalk
      simp only [CallOK, hF] at hok
      have kids := kids_cover fix wf len each hcov hwa
      obtain ⟨k, hk⟩ : ∃ k, (absNodes Γ P St aenv args)[i]? = some k := by
        have hi : i < ws.length := (List.getElem?_eq_some_iff.mp hw).1
        have hlen : (absNodes Γ P St aenv args).length = ws.length := kids.length_eq
        exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact Covers.mono (hok i k hk) (forall₂_getElem? kids hk hw)
  | some Fs =>
      refine typed_args_cover wf St hF hc fun i F w hFi hopen hw => ?_
      simp only [Walk] at hwalk
      obtain ⟨hwa, hok⟩ := hwalk
      simp only [CallOK, hF] at hok
      have kids := kids_cover fix wf len each hcov hwa
      obtain ⟨k, hk⟩ : ∃ k, (absNodes Γ P St aenv args)[i]? = some k := by
        have hi : i < ws.length := (List.getElem?_eq_some_iff.mp hw).1
        have hlen : (absNodes Γ P St aenv args).length = ws.length := kids.length_eq
        exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact Covers.mono (hok.2 i F k hFi hopen hk) (forall₂_getElem? kids hk hw)

/-- A dynamically called head's entered equation: its slots are covered, a head
named as a value having unknown inferred parameters. -/
theorem entry_covers_dyn {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {h : String} (named : h ∈ P.named) {ws : List Atom} (hc : ArgsChecked Γ P false h [] ws) {e : Eqn}
    {env' : ℕ → Atom} (hm : Matches e ws env') : EnvCovers Γ (entryEnv Γ P St h e) env' := by
  apply entry_covers hm
  cases hF : P.formals h with
  | none =>
      intro i w _
      simp only [paramSet, hF, fix.escaped h named i]
      trivial
  | some Fs =>
      exact typed_args_cover wf St hF hc fun i _ _ _ _ _ => by rw [fix.escaped h named i]; trivial

/-- A typed head's return check in HE's run, from the prepared run's: a shown
return meets the range. -/
theorem range_checked_he {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {h : String} {e : Eqn} (he : e ∈ P.eqs h) {env' : ℕ → Atom}
    (hcov : EnvCovers Γ (entryEnv Γ P St h e) env') {r : Atom} (hr : Reach Γ P false env' e.body r)
    (hrange : RangeChecked Γ P true h r) : RangeChecked Γ P false h r := by
  intro R hR
  refine .inr ?_
  rcases hrange R hR with hs | hm
  · obtain ⟨Ms, hMs, hall⟩ := fix.shown h R hR hs.2 e he
    have hcovr := sound fix wf hr _ hcov (fix.eqs h e he)
    rw [hMs] at hcovr
    obtain ⟨S, hS, hl⟩ := hcovr
    exact meets_of_lower (hall S hS) hl
  · exact hm

/-- **The prepared run reaches HE's values**: under a fixpoint, a run that skips
the discharged builds, arguments and returns reaches only what HE's run, making
every check, reaches. -/
theorem he_of_prepared {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    {env : ℕ → Atom} {n : Node} {v : Atom} (h : Reach Γ P true env n v) :
    ∀ aenv, EnvCovers Γ aenv env → Walk Γ P St aenv n → Reach Γ P false env n v := by
  induction h with
  | slot env s => intro _ _ _; exact .slot env s
  | lit env a => intro _ _ _; exact .lit env a
  | reg env cls args ws g len each hg each_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      exact .reg env cls args ws g len (fun p hp => each_ih p hp aenv hcov
        ((walkAll_iff Γ P St aenv args).mp hwalk p.1 (List.of_mem_zip hp).1)) hg
  | data env c args ws len each each_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      exact .data env c args ws len (fun p hp => each_ih p hp aenv hcov
        ((walkAll_iff Γ P St aenv args).mp hwalk p.1 (List.of_mem_zip hp).1))
  | call env h args skip ws e env' r len each he hm hc hr hrange each_ih hr_ih =>
      intro aenv hcov hwalk
      have hwa : WalkAll Γ P St aenv args := by
        simp only [Walk] at hwalk
        exact hwalk.1
      have each' : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2 := fun p hp =>
        each_ih p hp aenv hcov ((walkAll_iff Γ P St aenv args).mp hwa p.1 (List.of_mem_zip hp).1)
      have hc' := args_checked_he fix wf hcov len each' hwalk hc
      have hcov' := entry_covers_he fix wf hcov len each' hwalk hc' hm
      have hr' := hr_ih _ hcov' (fix.eqs h e he)
      exact .call env h args skip ws e env' r len each' he hm hc' hr'
        (range_checked_he fix wf he hcov' hr' hrange)
  | dyncall env f h args ws e env' r hf named len each he hm hc hr hrange hf_ih each_ih hr_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      have each' : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2 := fun p hp =>
        each_ih p hp aenv hcov ((walkAll_iff Γ P St aenv args).mp hwalk.2 p.1 (List.of_mem_zip hp).1)
      have hc' : ArgsChecked Γ P false h [] ws := by
        simp only [ArgsChecked] at hc ⊢
        split
        · trivial
        · rename_i Fs hF
          rw [hF] at hc
          exact ⟨hc.1, fun j F w h1 h2 => .inr ((hc.2 j F w h1 h2).resolve_left fun h => by
            simp at h)⟩
      have hcov' := entry_covers_dyn fix wf named hc' hm
      have hr' := hr_ih _ hcov' (fix.eqs h e he)
      exact .dyncall env f h args ws e env' r (hf_ih aenv hcov hwalk.1) named len each' he hm hc' hr'
        (range_checked_he fix wf he hcov' hr' hrange)
  | build env c args skip ws len each hc each_ih =>
      intro aenv hcov hwalk
      have hwalk' := hwalk
      simp only [Walk] at hwalk
      have each' : ∀ p ∈ args.zip ws, Reach Γ P false env p.1 p.2 := fun p hp =>
        each_ih p hp aenv hcov ((walkAll_iff Γ P St aenv args).mp hwalk.1 p.1 (List.of_mem_zip hp).1)
      refine .build env c args skip ws len each' (.inr ?_)
      rcases hc with hs | hp
      · obtain ⟨-, rfl⟩ := hs
        exact discharged_build_passes fix wf hcov hwalk' len each'
      · exact hp
  | iteT env c t e w r hc ht hc_ih ht_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      exact .iteT env c t e w r (hc_ih aenv hcov hwalk.1) (ht_ih aenv hcov hwalk.2.1)
  | iteE env c t e w r hc he hc_ih he_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      exact .iteE env c t e w r (hc_ih aenv hcov hwalk.1) (he_ih aenv hcov hwalk.2.2)
  | bind env s v b w r hv hb hv_ih hb_ih =>
      intro aenv hcov hwalk
      simp only [Walk] at hwalk
      have hv' := hv_ih aenv hcov hwalk.1
      exact .bind env s v b w r hv' (hb_ih _ (envCovers_update hcov s (sound fix wf hv' aenv hcov hwalk.1))
        hwalk.2)

/-- **Discharge is exact**: under a fixpoint of the analysis, the run's body
reaches the same values when the discharged checks are skipped as when every
check is made. -/
theorem prepared_iff {Γ : Decls} {P : Program} {St : Stored} (fix : PostFix Γ P St) (wf : WF Γ P)
    (env : ℕ → Atom) (v : Atom) : Reach Γ P true env P.main v ↔ Reach Γ P false env P.main v :=
  ⟨fun h => he_of_prepared fix wf h (fun _ => none) (fun _ => trivial) fix.main, prepared_of_he⟩

/-! ## Widened sets decide the same discharges

CeTTa decides its discharges with its final sets, which widen the fixpoint's: a
set no value reached, a fifth member and a sixty-fifth combination are unknown.
The analysis is monotone (`absNode_mono`) and the discharge conditions antitone
(`buildPasses_anti`, `callFlags_anti`), so flags decided on any sets at least as
wide as a fixpoint's are discharges at that fixpoint (`postFix_of_widened`), and
`prepared_iff` applies. -/

theorem Le.refl : ∀ s : TySet, Le s s
  | none => trivial
  | some _ => fun _ h => h

theorem Le.trans : ∀ {s t u : TySet}, Le s t → Le t u → Le s u
  | _, _, none, _, _ => trivial
  | none, none, some _, _, h => h.elim
  | none, some _, some _, h, _ => h.elim
  | some _, none, some _, _, h => h.elim
  | some _, some _, some _, h1, h2 => fun S hS => h2 S (h1 S hS)

theorem join_mono {s s' t t' : TySet} (hs : Le s s') (ht : Le t t') : Le (join s t) (join s' t') := by
  cases s' with
  | none => cases t' <;> trivial
  | some Ms' =>
      cases t' with
      | none => cases s <;> cases t <;> trivial
      | some Ns' =>
          cases s with
          | none => exact hs.elim
          | some Ms =>
              cases t with
              | none => exact ht.elim
              | some Ns =>
                  intro S hS
                  rcases List.mem_append.mp hS with h | h
                  · exact List.mem_append_left _ (hs S h)
                  · exact List.mem_append_right _ (ht S h)

theorem fieldSet_mono (Γ : Decls) (c : String) (k : ℕ) {s s' : TySet} (h : Le s s') :
    Le (fieldSet Γ c k s) (fieldSet Γ c k s') := by
  classical
  cases s' with
  | none => cases s <;> simp [fieldSet, Le]
  | some Ns =>
      cases s with
      | none => exact h.elim
      | some Ms =>
          simp only [fieldSet]
          split
          · split
            · split_ifs
              · intro F hF
                rw [List.mem_filter, List.mem_map] at hF ⊢
                obtain ⟨⟨M, hM, rfl⟩, hne⟩ := hF
                exact ⟨⟨M, h M hM, rfl⟩, hne⟩
              · trivial
            · trivial
          · trivial

/-- Children's sets read against wider ones. -/
theorem scan_mono :
    ∀ {kids kids' : List TySet}, List.Forall₂ Le kids kids' →
      (scan kids' = .empty → scan kids = .empty) ∧
        ∀ Mss', scan kids' = .members Mss' →
          scan kids = .empty ∨ ∃ Mss, scan kids = .members Mss ∧
            List.Forall₂ (fun l l' => ∀ S ∈ l, S ∈ l') Mss Mss'
  | [], [], .nil => ⟨fun h => h, fun Mss' h => .inr ⟨[], rfl, by
      simp only [scan, Scan.members.injEq] at h
      subst h
      exact .nil⟩⟩
  | k :: ks, none :: ks', .cons _ _ => ⟨fun h => by simp [scan] at h, fun _ h => by simp [scan] at h⟩
  | k :: ks, some [] :: ks', .cons hk _ => by
      have hk' : k = some [] := by
        cases k with
        | none => exact hk.elim
        | some Ms =>
            cases Ms with
            | nil => rfl
            | cons M Ms => exact absurd (hk M (by simp)) (by simp)
      subst hk'
      exact ⟨fun _ => rfl, fun _ h => by simp [scan] at h⟩
  | k :: ks, some (M' :: Ms') :: ks', .cons hk hrest => by
      obtain ⟨hempty, hmem⟩ := scan_mono hrest
      cases k with
      | none => exact hk.elim
      | some Ms =>
          cases Ms with
          | nil => exact ⟨fun _ => rfl, fun _ _ => .inl rfl⟩
          | cons M Ms =>
              refine ⟨fun h => ?_, fun Mss' h => ?_⟩
              · simp only [scan] at h ⊢
                rw [hempty (Scan.cons_empty h)]
                rfl
              · simp only [scan] at h ⊢
                obtain ⟨Mss'', hs, rfl⟩ := Scan.cons_members h
                rcases hmem Mss'' hs with he | ⟨Mss, hs', each⟩
                · exact .inl (by rw [he]; rfl)
                · exact .inr ⟨(M :: Ms) :: Mss, by rw [hs']; rfl, .cons hk each⟩

theorem sections_mono {Mss Mss' : List (List (Set (Ty Empty)))}
    (h : List.Forall₂ (fun l l' => ∀ S ∈ l, S ∈ l') Mss Mss') {Ss : List (Set (Ty Empty))}
    (hSs : Ss ∈ Mss.sections) : Ss ∈ Mss'.sections := by
  rw [List.mem_sections] at hSs ⊢
  have key : ∀ {Ss : List (Set (Ty Empty))} {Mss Mss' : List (List (Set (Ty Empty)))},
      List.Forall₂ (· ∈ ·) Ss Mss → List.Forall₂ (fun l l' => ∀ S ∈ l, S ∈ l') Mss Mss' →
        List.Forall₂ (· ∈ ·) Ss Mss' := by
    intro Ss Mss Mss' h1 h2
    induction h1 generalizing Mss' with
    | nil => cases h2; exact .nil
    | cons hS _ ih =>
        cases h2 with
        | cons hl rest => exact .cons (hl _ hS) (ih rest)
  exact key hSs h

theorem le_none (s : TySet) : Le s none := by cases s <;> trivial

/-- **A build's set is monotone in its children's.** -/
theorem buildSet_mono (Γ : Decls) (c : String) {kids kids' : List TySet}
    (h : List.Forall₂ Le kids kids') : Le (buildSet Γ c kids) (buildSet Γ c kids') := by
  classical
  have len : kids.length = kids'.length := h.length_eq
  obtain ⟨hempty, hmem⟩ := scan_mono h
  cases hrow : ctorRow Γ c with
  | none => simp only [buildSet, hrow]; trivial
  | some r =>
      obtain ⟨ρ, Ts, R⟩ := r
      simp only [buildSet, hrow, len]
      by_cases hlen : Ts.length = kids'.length
      · rw [if_pos hlen, if_pos hlen]
        cases hs' : scan kids' with
        | any => exact le_none _
        | empty =>
            rw [hempty hs']
            exact Le.refl _
        | members Mss' =>
            dsimp only
            by_cases hall' : ∀ Ss ∈ Mss'.sections, (combo Ts R Ss).Nonempty
            · rw [if_pos hall']
              rcases hmem Mss' hs' with he | ⟨Mss, hs, each⟩
              · rw [he]
                intro S hS
                cases hS
              · have hall : ∀ Ss ∈ Mss.sections, (combo Ts R Ss).Nonempty :=
                  fun Ss hSs => hall' Ss (sections_mono each hSs)
                rw [hs]
                dsimp only
                rw [if_pos hall]
                intro S hS
                obtain ⟨Ss, hSs, rfl⟩ := List.mem_map.mp hS
                exact List.mem_map_of_mem (sections_mono each hSs)
            · rw [if_neg hall']
              exact le_none _
      · rw [if_neg hlen, if_neg hlen]
        trivial

/-- **A discharge decided on wider sets holds on narrower ones.** -/
theorem buildPasses_anti {Γ : Decls} {c : String} {kids kids' : List TySet}
    (h : List.Forall₂ Le kids kids') (hp : BuildPasses Γ c kids') : BuildPasses Γ c kids := by
  obtain ⟨ρ, Ts, R, hrow, hlen, hs⟩ := hp
  obtain ⟨hempty, hmem⟩ := scan_mono h
  refine ⟨ρ, Ts, R, hrow, hlen.trans h.length_eq.symm, ?_⟩
  rcases hs with hs | ⟨Mss', hs, hall⟩
  · exact .inl (hempty hs)
  · rcases hmem Mss' hs with he | ⟨Mss, hs', each⟩
    · exact .inl he
    · exact .inr ⟨Mss, hs', fun Ss hSs => hall Ss (sections_mono each hSs)⟩

/-- Stored sets at most as wide as others. -/
structure StoredLe (St St' : Stored) : Prop where
  param : ∀ h j, Le (St.param h j) (St'.param h j)
  answer : ∀ h, Le (St.answer h) (St'.answer h)

theorem paramSet_mono (P : Program) {St St' : Stored} (hle : StoredLe St St') (h : String) (i : ℕ) :
    Le (paramSet P St h i) (paramSet P St' h i) := by
  unfold paramSet
  split
  · exact hle.param h i
  · split
    · split_ifs
      · exact Le.refl _
      · exact hle.param h i
    · exact Le.refl _

theorem entryEnv_mono (Γ : Decls) (P : Program) {St St' : Stored} (hle : StoredLe St St') (h : String)
    (e : Eqn) (s : ℕ) : Le (entryEnv Γ P St h e s) (entryEnv Γ P St' h e s) := by
  unfold entryEnv
  split
  · exact paramSet_mono P hle h _
  · exact fieldSet_mono Γ _ _ (paramSet_mono P hle h _)
  · trivial

theorem update_le {aenv aenv' : ℕ → TySet} (h : ∀ s, Le (aenv s) (aenv' s)) (x : ℕ) {S S' : TySet}
    (hS : Le S S') (s : ℕ) : Le (Function.update aenv x S s) (Function.update aenv' x S' s) := by
  by_cases hs : s = x
  · subst hs
    simpa using hS
  · simpa [Function.update, hs] using h s

mutual
/-- **The analysis is monotone** in the stored sets and the slots' sets. -/
theorem absNode_mono (Γ : Decls) (P : Program) {St St' : Stored} (hle : StoredLe St St') :
    ∀ (n : Node) {aenv aenv' : ℕ → TySet}, (∀ s, Le (aenv s) (aenv' s)) →
      Le (absNode Γ P St aenv n) (absNode Γ P St' aenv' n)
  | .slot s, _, _, h => h s
  | .lit a, _, _, _ => Le.refl _
  | .reg cls _, _, _, _ => Le.refl _
  | .data _ _, _, _, _ => trivial
  | .call f _ _, _, _, _ => by
      simp only [absNode, callSet]
      split
      · exact hle.answer f
      · exact Le.refl _
  | .dyncall _ _, _, _, _ => trivial
  | .build c args _, _, _, h => by
      simp only [absNode]
      exact buildSet_mono Γ c (absNodes_mono Γ P hle args h)
  | .ite _ t e, _, _, h => by
      simp only [absNode]
      exact join_mono (absNode_mono Γ P hle t h) (absNode_mono Γ P hle e h)
  | .bind x v b, _, _, h => by
      simp only [absNode]
      exact absNode_mono Γ P hle b (update_le h x (absNode_mono Γ P hle v h))
theorem absNodes_mono (Γ : Decls) (P : Program) {St St' : Stored} (hle : StoredLe St St') :
    ∀ (ns : List Node) {aenv aenv' : ℕ → TySet}, (∀ s, Le (aenv s) (aenv' s)) →
      List.Forall₂ Le (absNodes Γ P St aenv ns) (absNodes Γ P St' aenv' ns)
  | [], _, _, _ => by simp [absNodes]
  | n :: ns, _, _, h => by
      simp only [absNodes]
      exact .cons (absNode_mono Γ P hle n h) (absNodes_mono Γ P hle ns h)
end

/-- A call site's constraints on its callee's inferred parameters. -/
def CallSites (P : Program) (St : Stored) (h : String) (kids : List TySet) : Prop :=
  match P.formals h with
  | none => ∀ (j : ℕ) (k : TySet), kids[j]? = some k → Le k (St.param h j)
  | some Fs => ∀ (j : ℕ) (F : Ty String) (k : TySet), Fs[j]? = some (some F) → F.vars ≠ [] →
      kids[j]? = some k → Le k (St.param h j)

/-- A call site's discharged arguments of a typed callee. -/
def CallFlags (P : Program) (h : String) (kids : List TySet) (skip : List Bool) : Prop :=
  match P.formals h with
  | none => True
  | some Fs => ∀ j : ℕ, skip[j]? = some true →
      ∃ F : Ty String, Fs[j]? = some (some F) ∧ ∃ Ms, kids[j]? = some (some Ms) ∧
        ∀ S ∈ Ms, AllowsInstance F S

theorem callFlags_anti {P : Program} {h : String} {kids kids' : List TySet} {skip : List Bool}
    (hk : List.Forall₂ Le kids kids') (hf : CallFlags P h kids' skip) : CallFlags P h kids skip := by
  unfold CallFlags at hf ⊢
  split
  · trivial
  · rename_i Fs hF
    rw [hF] at hf
    intro j hj
    obtain ⟨F, hFj, Ms', hMs', hall⟩ := hf j hj
    refine ⟨F, hFj, ?_⟩
    have hlen : kids.length = kids'.length := hk.length_eq
    obtain ⟨k, hk'⟩ : ∃ k, kids[j]? = some k := by
      have hj' : j < kids'.length := (List.getElem?_eq_some_iff.mp hMs').1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hle := forall₂_getElem? hk hk' hMs'
    cases k with
    | none => exact hle.elim
    | some Ms => exact ⟨Ms, hk', fun S hS => hall S (hle S hS)⟩

theorem callOK_of {P : Program} {St : Stored} {h : String} {kids : List TySet} {skip : List Bool}
    (hs : CallSites P St h kids) (hf : CallFlags P h kids skip) : CallOK P St h kids skip := by
  unfold CallSites at hs
  unfold CallFlags at hf
  unfold CallOK
  split
  · rename_i hF
    rw [hF] at hs
    exact hs
  · rename_i Fs hF
    rw [hF] at hf hs
    exact ⟨hf, hs⟩

mutual
/-- The call-site constraints of a body, with its lets in scope. -/
def Sites (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → Node → Prop
  | _, .slot _ => True
  | _, .lit _ => True
  | aenv, .reg _ args => SitesAll Γ P St aenv args
  | aenv, .data _ args => SitesAll Γ P St aenv args
  | aenv, .call h args _ => SitesAll Γ P St aenv args ∧ CallSites P St h (absNodes Γ P St aenv args)
  | aenv, .dyncall f args => Sites Γ P St aenv f ∧ SitesAll Γ P St aenv args
  | aenv, .build _ args _ => SitesAll Γ P St aenv args
  | aenv, .ite c t e => Sites Γ P St aenv c ∧ Sites Γ P St aenv t ∧ Sites Γ P St aenv e
  | aenv, .bind s v b =>
      Sites Γ P St aenv v ∧ Sites Γ P St (Function.update aenv s (absNode Γ P St aenv v)) b
/-- The call-site constraints of a list of nodes. -/
def SitesAll (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → List Node → Prop
  | _, [] => True
  | aenv, n :: ns => Sites Γ P St aenv n ∧ SitesAll Γ P St aenv ns
end

mutual
/-- The discharge flags of a body, decided on the sets `St`. -/
def Flags (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → Node → Prop
  | _, .slot _ => True
  | _, .lit _ => True
  | aenv, .reg _ args => FlagsAll Γ P St aenv args
  | aenv, .data _ args => FlagsAll Γ P St aenv args
  | aenv, .call h args skip => FlagsAll Γ P St aenv args ∧ CallFlags P h (absNodes Γ P St aenv args) skip
  | aenv, .dyncall f args => Flags Γ P St aenv f ∧ FlagsAll Γ P St aenv args
  | aenv, .build c args skip =>
      FlagsAll Γ P St aenv args ∧ (skip = true → BuildPasses Γ c (absNodes Γ P St aenv args))
  | aenv, .ite c t e => Flags Γ P St aenv c ∧ Flags Γ P St aenv t ∧ Flags Γ P St aenv e
  | aenv, .bind s v b =>
      Flags Γ P St aenv v ∧ Flags Γ P St (Function.update aenv s (absNode Γ P St aenv v)) b
/-- The discharge flags of a list of nodes. -/
def FlagsAll (Γ : Decls) (P : Program) (St : Stored) : (ℕ → TySet) → List Node → Prop
  | _, [] => True
  | aenv, n :: ns => Flags Γ P St aenv n ∧ FlagsAll Γ P St aenv ns
end

mutual
/-- **A fixpoint's call sites with flags decided on wider sets are its
conditions.** -/
theorem walk_of_split (Γ : Decls) (P : Program) {St St' : Stored} (hle : StoredLe St St') :
    ∀ (n : Node) {aenv aenv' : ℕ → TySet}, (∀ s, Le (aenv s) (aenv' s)) →
      Sites Γ P St aenv n → Flags Γ P St' aenv' n → Walk Γ P St aenv n
  | .slot _, _, _, _, _, _ => trivial
  | .lit _, _, _, _, _, _ => trivial
  | .reg _ args, _, _, h, hs, hf => by
      simp only [Sites, Flags, Walk] at hs hf ⊢
      exact walkAll_of_split Γ P hle args h hs hf
  | .data _ args, _, _, h, hs, hf => by
      simp only [Sites, Flags, Walk] at hs hf ⊢
      exact walkAll_of_split Γ P hle args h hs hf
  | .call f args skip, _, _, h, hs, hf => by
      simp only [Sites, Flags, Walk] at hs hf ⊢
      exact ⟨walkAll_of_split Γ P hle args h hs.1 hf.1,
        callOK_of hs.2 (callFlags_anti (absNodes_mono Γ P hle args h) hf.2)⟩
  | .dyncall g args, _, _, h, hs, hf => by
      simp only [Sites, Flags, Walk] at hs hf ⊢
      exact ⟨walk_of_split Γ P hle g h hs.1 hf.1, walkAll_of_split Γ P hle args h hs.2 hf.2⟩
  | .build c args skip, _, _, h, hs, hf => by
      simp only [Sites, Flags, Walk] at hs hf ⊢
      exact ⟨walkAll_of_split Γ P hle args h hs hf.1,
        fun hk => buildPasses_anti (absNodes_mono Γ P hle args h) (hf.2 hk)⟩
  | .ite c t e, _, _, h, hs, hf => by
      simp only [Sites, Flags, Walk] at hs hf ⊢
      exact ⟨walk_of_split Γ P hle c h hs.1 hf.1, walk_of_split Γ P hle t h hs.2.1 hf.2.1,
        walk_of_split Γ P hle e h hs.2.2 hf.2.2⟩
  | .bind x v b, _, _, h, hs, hf => by
      simp only [Sites, Flags, Walk] at hs hf ⊢
      exact ⟨walk_of_split Γ P hle v h hs.1 hf.1,
        walk_of_split Γ P hle b (update_le h x (absNode_mono Γ P hle v h)) hs.2 hf.2⟩
theorem walkAll_of_split (Γ : Decls) (P : Program) {St St' : Stored} (hle : StoredLe St St') :
    ∀ (ns : List Node) {aenv aenv' : ℕ → TySet}, (∀ s, Le (aenv s) (aenv' s)) →
      SitesAll Γ P St aenv ns → FlagsAll Γ P St' aenv' ns → WalkAll Γ P St aenv ns
  | [], _, _, _, _, _ => trivial
  | n :: ns, _, _, h, hs, hf => by
      simp only [SitesAll, FlagsAll, WalkAll] at hs hf ⊢
      exact ⟨walk_of_split Γ P hle n h hs.1 hf.1, walkAll_of_split Γ P hle ns h hs.2 hf.2⟩
end

/-- **Flags decided on widened sets are a fixpoint's discharges**: with `St` a
fixpoint of the call sites and answers, and the flags and shown returns decided
on any `St'` at least as wide, every condition of `PostFix` holds at `St`, so the
prepared run reaches exactly HE's values (`prepared_iff`). -/
theorem postFix_of_widened {Γ : Decls} {P : Program} {St St' : Stored} (hle : StoredLe St St')
    (main_sites : Sites Γ P St (fun _ => none) P.main) (main_flags : Flags Γ P St' (fun _ => none) P.main)
    (eqs_sites : ∀ h, ∀ e ∈ P.eqs h, Sites Γ P St (entryEnv Γ P St h e) e.body)
    (eqs_flags : ∀ h, ∀ e ∈ P.eqs h, Flags Γ P St' (entryEnv Γ P St' h e) e.body)
    (answers : ∀ h, P.formals h = none → ∀ e ∈ P.eqs h,
      Le (absNode Γ P St (entryEnv Γ P St h e) e.body) (St.answer h))
    (escaped : ∀ h, h ∈ P.named → ∀ j, St.param h j = none)
    (shown : ∀ h R, P.range h = some R → P.shown h = true → ∀ e ∈ P.eqs h,
      ∃ Ms, absNode Γ P St' (entryEnv Γ P St' h e) e.body = some Ms ∧ ∀ S ∈ Ms, R ∈ S) :
    PostFix Γ P St where
  main := walk_of_split Γ P hle P.main (aenv := fun _ => none) (aenv' := fun _ => none) (fun _ => trivial)
    main_sites main_flags
  eqs h e he := walk_of_split Γ P hle e.body (entryEnv_mono Γ P hle h e) (eqs_sites h e he) (eqs_flags h e he)
  answers := answers
  escaped := escaped
  shown h R hR hs e he := by
    obtain ⟨Ms', hMs', hall⟩ := shown h R hR hs e he
    have hmono := absNode_mono Γ P hle e.body (entryEnv_mono Γ P hle h e)
    rw [hMs'] at hmono
    cases hA : absNode Γ P St (entryEnv Γ P St h e) e.body with
    | none => rw [hA] at hmono; exact hmono.elim
    | some Ms =>
        rw [hA] at hmono
        exact ⟨Ms, rfl, fun S hS => hall S (hmono S hS)⟩

/-! ## CeTTa's two rules the controls refute -/

open Classical in
/-- CeTTa's field rule as the 11/06 binary has it: the range need not fix the
field. -/
noncomputable def fieldSetC (Γ : Decls) (c : String) (k : ℕ) : TySet → TySet
  | none => none
  | some Ms =>
      match ctorRow Γ c with
      | some (_, Ts, R) =>
          match Ts[k]? with
          | some T =>
              if CheckedTy T then some ((Ms.map (fieldOf R T)).filter fun F => decide F.Nonempty)
              else none
          | none => none
      | none => none

open Classical in
/-- CeTTa's build rule as the 11/06 binary has it: a failing combination is
dropped, and a build none of whose combinations passes has no value. -/
noncomputable def buildSetC (Γ : Decls) (c : String) (kids : List TySet) : TySet :=
  match ctorRow Γ c with
  | none => none
  | some (_, Ts, R) =>
      if Ts.length = kids.length then
        match scan kids with
        | .any => none
        | .empty => some []
        | .members Mss => some ((Mss.sections.map (combo Ts R)).filter fun S => decide S.Nonempty)
      else none

/-! ## Controls -/

namespace Controls

open ShapeTyping.Controls (tv tc listT consRow succRow gc glist num str app numList stringFirst decls
  decls_cons decls_succ decls_zero decls_nil consRow_split succRow_split stamp_num stamp_str stamp_nil
  list_stamp wrong_class inst_const)

theorem bind_listT (θ : String → Ty Empty) (x : String) : (listT (tv x)).bind θ = glist (θ x) := by
  simp [listT, tv, glist, Ty.bind_app]

theorem ctorRow_cons :
    ctorRow decls "Cons" = some (consRow, [tv "x", listT (tv "x")], listT (tv "x")) := by
  unfold ctorRow
  rw [decls_cons]
  simp [consRow_split]

theorem ctorRow_succ : ctorRow decls "S" = some (succRow, [tc "Nat"], tc "Nat") := by
  unfold ctorRow
  rw [decls_succ]
  simp [succRow_split]

theorem joint_cons (θ : String → Ty Empty) (A B : Set (Ty Empty)) :
    θ ∈ joint [tv "x", listT (tv "x")] [A, B] ↔ θ "x" ∈ A ∧ glist (θ "x") ∈ B := by
  simp only [joint, Set.mem_ofPred_eq, List.forall₂_cons, List.forall₂_nil_left_iff, and_true,
    bind_listT]
  rfl

/-- **Positive control**: a number before a list of numbers passes, and the
build has the one typing `(List Number)`. -/
theorem numbers_pass :
    BuildPasses decls "Cons" [some [{gc "Number"}], some [{glist (gc "Number")}]] := by
  refine ⟨consRow, _, _, ctorRow_cons, rfl, .inr ⟨[[{gc "Number"}], [{glist (gc "Number")}]], rfl, ?_⟩⟩
  intro Ss hSs
  simp only [List.sections, List.flatMap_cons, List.map_cons, List.map_nil, List.flatMap_nil,
    List.append_nil, List.mem_singleton] at hSs
  subst hSs
  exact ⟨_, fun _ => gc "Number", (joint_cons _ _ _).mpr ⟨rfl, rfl⟩, rfl⟩

/-- **A failing combination is checked, and HE's check fails there**: a string
before a list of numbers. -/
theorem failing_combination_checked :
    ¬ BuildPasses decls "Cons" [some [{gc "String"}], some [{glist (gc "Number")}]] ∧
      ¬ HEPasses decls "Cons" [str "x", numList [1]] := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ρ, Ts, R, hrow, -, hs⟩
    rw [ctorRow_cons] at hrow
    simp only [Option.some.injEq, Prod.mk.injEq] at hrow
    obtain ⟨rfl, rfl, rfl⟩ := hrow
    rcases hs with hs | ⟨Mss, hs, hall⟩
    · simp [scan, Scan.cons] at hs
    · simp only [scan, Scan.cons, Scan.members.injEq] at hs
      subst hs
      obtain ⟨T, θ, hj, -⟩ := hall [{gc "String"}, {glist (gc "Number")}] (by simp [List.sections])
      rw [joint_cons] at hj
      obtain ⟨h1, h2⟩ := hj
      rw [Set.mem_singleton_iff] at h1 h2
      rw [h1] at h2
      simp [glist, gc] at h2
  · rintro ⟨X, hX⟩
    have h : (stamp decls (.expression (.symbol "Cons" :: [str "x", numList [1]]))).typs =
        [.err (inst consRow)] := wrong_class
    rw [h] at hX
    simp at hX

/-! ### A head named as a value -/

/-- `(= (u $x) (S $x))`, its build discharged. -/
def uEqn : Eqn := ⟨1, fun _ => .whole 0, .build "S" [.slot 0] true⟩

/-- `u` named as a value and called with `Z` statically and with `1`
dynamically: `(if Z (u Z) ($u 1))`. -/
def escMain : Node :=
  .ite (.lit (.symbol "Z")) (.call "u" [.lit (.symbol "Z")] [])
    (.dyncall (.lit (.symbol "u")) [.lit (num 1)])

/-- The program. -/
def escProg : Program where
  eqs := fun h => if h = "u" then [uEqn] else []
  formals := fun _ => none
  range := fun _ => none
  shown := fun _ => false
  named := {"u"}
  main := escMain

/-- `u`'s parameter as the join of its static call sites, `Nat`, and its answer. -/
def escSt : Stored where
  param := fun _ _ => some [{gc "Nat"}]
  answer := fun _ => some [combo [tc "Nat"] (tc "Nat") [{gc "Nat"}]]

theorem inst_nat : inst (tc "Nat") = {gc "Nat"} := inst_const "Nat"

theorem esc_passes : BuildPasses decls "S" [some [{gc "Nat"}]] := by
  refine ⟨succRow, _, _, ctorRow_succ, rfl, .inr ⟨[[{gc "Nat"}]], rfl, ?_⟩⟩
  intro Ss hSs
  simp only [List.sections, List.flatMap_cons, List.map_cons, List.map_nil, List.flatMap_nil,
    List.append_nil, List.mem_singleton] at hSs
  subst hSs
  exact ⟨gc "Nat", fun _ => gc "Nat", by simp [joint, tc, gc], rfl⟩

theorem esc_eqs (h : String) (e : Eqn) (he : e ∈ escProg.eqs h) : h = "u" ∧ e = uEqn := by
  simp only [escProg] at he
  split_ifs at he with hh
  · simpa [hh] using he
  · simp at he

/-- **Every condition of a fixpoint holds but the escape rule**: the call sites,
the body's discharged build, and the answer. -/
theorem esc_conditions :
    Walk decls escProg escSt (fun _ => none) escProg.main ∧
      (∀ h, ∀ e ∈ escProg.eqs h, Walk decls escProg escSt (entryEnv decls escProg escSt h e) e.body) ∧
      (∀ h, escProg.formals h = none → ∀ e ∈ escProg.eqs h,
        Le (absNode decls escProg escSt (entryEnv decls escProg escSt h e) e.body) (escSt.answer h)) ∧
      "u" ∈ escProg.named ∧ escSt.param "u" 0 ≠ none := by
  have hlit : litSet decls (.symbol "Z") = some [{gc "Nat"}] := by
    have hr : readRows (decls "Z") = [tc "Nat"] := by
      rw [decls_zero]
      simp [readRows, tc, undefinedTy]
    simp only [litSet, hr]
    rw [inst_nat]
  have hentry : entryEnv decls escProg escSt "u" uEqn 0 = some [{gc "Nat"}] := by
    simp [entryEnv, uEqn, paramSet, escProg, escSt]
  refine ⟨?_, ?_, ?_, rfl, by simp [escSt]⟩
  · simp only [escProg, escMain, Walk, WalkAll, absNodes, absNode, hlit, CallOK]
    refine ⟨trivial, ⟨⟨trivial, trivial⟩, ?_⟩, trivial, trivial, trivial⟩
    intro j k hk
    cases j with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        intro S hS
        simpa [escSt] using hS
    | succ j => simp at hk
  · intro h e he
    obtain ⟨rfl, rfl⟩ := esc_eqs h e he
    rw [show uEqn.body = .build "S" [.slot 0] true from rfl]
    simp only [Walk, WalkAll, absNodes, absNode]
    refine ⟨⟨trivial, trivial⟩, fun _ => ?_⟩
    rw [hentry]
    exact esc_passes
  · intro h _ e he
    obtain ⟨rfl, rfl⟩ := esc_eqs h e he
    rw [show uEqn.body = .build "S" [.slot 0] true from rfl]
    simp only [absNodes, absNode]
    rw [hentry]
    unfold buildSet
    rw [ctorRow_succ]
    simp only [List.length_cons, List.length_nil, if_true, scan, Scan.cons]
    split_ifs with hall
    · intro S hS
      simpa [escSt, List.sections] using hS
    · exfalso
      apply hall
      intro Ss hSs
      simp only [List.sections, List.flatMap_cons, List.map_cons, List.map_nil, List.flatMap_nil,
        List.append_nil, List.mem_singleton] at hSs
      subst hSs
      exact ⟨gc "Nat", fun _ => gc "Nat", by simp [joint, tc, gc], rfl⟩

/-- The prepared run builds `(S 1)` through the dynamic call. -/
theorem esc_prepared : Reach decls escProg true (fun _ => default) escProg.main (app "S" [num 1]) := by
  refine .iteE _ _ _ _ (.symbol "Z") _ (.lit _ _) ?_
  refine .dyncall _ _ "u" _ [num 1] uEqn (fun _ => num 1) _ (.lit _ _) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hp
    subst hp
    exact .lit _ _
  · simp [escProg]
  · exact ⟨rfl, fun s => by simp [uEqn, MatchSlot]⟩
  · simp [ArgsChecked, escProg]
  · refine .build _ "S" [.slot 0] true [num 1] rfl (fun p hp => ?_) (.inl ⟨rfl, rfl⟩)
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hp
    subst hp
    exact .slot _ 0
  · intro R hR
    simp [escProg] at hR

/-- `(S 1)` fails HE's check. -/
theorem succ_one_fails : ¬ HEPasses decls "S" [num 1] := by
  rintro ⟨X, hX⟩
  obtain ⟨rows, split⟩ := ctorRow_spec ctorRow_succ
  rw [stamp_ctor decls "S" succRow [tc "Nat"] (tc "Nat") rows split] at hX
  simp only [List.length_cons, List.length_nil, if_true, List.map_cons, List.map_nil, stamp_num] at hX
  rw [ShapeTyping.Controls.semCheck_one _ _ (tc "Nat") [] "Grounded" {gc "Number"} [] Set.univ rfl] at hX
  have hne : ¬ (narrow Set.univ (tc "Nat") {gc "Number"}).Nonempty := by
    rintro ⟨θ, -, h⟩
    simp [tc, gc] at h
  rw [if_neg hne] at hX
  simp at hX

/-- HE's run does not reach `(S 1)`: the static call builds `(S Z)`, and the
dynamic call's build fails its check. -/
theorem esc_he : ¬ Reach decls escProg false (fun _ => default) escProg.main (app "S" [num 1]) := by
  intro h
  change Reach decls escProg false _ escMain _ at h
  cases h with
  | iteT _ _ _ _ _ _ hc ht =>
      cases ht with
      | call _ _ _ _ ws e env' _ len each he hm _ hr _ =>
          obtain ⟨-, rfl⟩ := esc_eqs _ e he
          match ws, len with
          | [w], _ =>
              have hw := Reach.lit_inv (each (.lit (.symbol "Z"), w) (by simp))
              have h0 := hm.2 0
              simp only [uEqn, MatchSlot, List.getElem?_cons_zero, Option.some.injEq] at h0
              obtain ⟨ws', hv, -, each', -⟩ := Reach.build_inv (c := "S") (args := [.slot 0]) (skip := true) hr
              simp only [app, Atom.expression.injEq, List.cons.injEq, true_and] at hv
              subst hv
              have h1 := Reach.slot_inv (each' (.slot 0, num 1) (by simp))
              simp only at hw h1
              rw [← h0, hw] at h1
              simp [num] at h1
  | iteE _ _ _ _ _ _ hc he =>
      cases he with
      | dyncall _ _ h' _ ws e env' _ hf named len each he' hm _ hr _ =>
          have hh := Reach.lit_inv hf
          simp only [Atom.symbol.injEq] at hh
          subst hh
          obtain ⟨-, rfl⟩ := esc_eqs _ e he'
          match ws, len with
          | [w], _ =>
              have hw := Reach.lit_inv (each (.lit (num 1), w) (by simp))
              have h0 := hm.2 0
              simp only [uEqn, MatchSlot, List.getElem?_cons_zero, Option.some.injEq] at h0
              obtain ⟨ws', hv, -, -, hc'⟩ := Reach.build_inv (c := "S") (args := [.slot 0]) (skip := true) hr
              simp only [app, Atom.expression.injEq, List.cons.injEq, true_and] at hv
              subst hv
              rcases hc' with hc' | hc'
              · cases hc'.1
              · exact succ_one_fails hc'

/-- **A head named as a value needs unknown parameters**: with every other
condition of a fixpoint met, `u`'s parameter read as its static call sites'
join, `Nat`, discharges a check the dynamic call fails, and the prepared run
reaches `(S 1)`, which HE's run does not. -/
theorem escape_needs_any :
    Reach decls escProg true (fun _ => default) escProg.main (app "S" [num 1]) ∧
      ¬ Reach decls escProg false (fun _ => default) escProg.main (app "S" [num 1]) :=
  ⟨esc_prepared, esc_he⟩

/-! ### A field the range does not fix -/

/-- `(: MkBox (-> (List $a) Box))`: the range does not name the field's
variable. -/
def boxRow : Ty String := .app [.sym "->", listT (tv "a"), tc "Box"]

/-- The list rows with `MkBox`. -/
def bdecls : Decls := fun s => if s = "MkBox" then [boxRow] else decls s

theorem ctorRow_mkbox : ctorRow bdecls "MkBox" = some (boxRow, [listT (tv "a")], tc "Box") := by
  simp [ctorRow, bdecls, boxRow, arrowSplit]

theorem stamp_one_b : stamp bdecls (numList [1]) = ⟨"Expression", [.ok {glist (gc "Number")}]⟩ := by
  rw [stamp_congr (Γ' := decls) (numList [1])]
  · exact list_stamp 1 []
  · intro s hs
    simp [numList, app, num, TypedCertificates.Judgment.leaves, TypedCertificates.Judgment.leavesAll] at hs
    rcases hs with rfl | rfl <;> simp [bdecls]

theorem combo_box : combo [listT (tv "a")] (tc "Box") [{glist (gc "Number")}] = {gc "Box"} := by
  ext T
  simp only [combo, joint, Set.mem_ofPred_eq, List.forall₂_cons, List.forall₂_nil_left_iff, and_true,
    Set.mem_singleton_iff, tc, Ty.bind_sym]
  constructor
  · rintro ⟨_, _, rfl⟩
    rfl
  · rintro rfl
    exact ⟨fun _ => gc "Number", by rw [bind_listT], rfl⟩

/-- The field typings `Box` gives the field: every `(List t)`. -/
theorem string_list_field : glist (gc "String") ∈ fieldOf (tc "Box") (listT (tv "a")) {gc "Box"} :=
  ⟨fun _ => gc "String", rfl, by rw [bind_listT]⟩

theorem fieldC_box :
    fieldSetC bdecls "MkBox" 0 (some [{gc "Box"}]) = some [fieldOf (tc "Box") (listT (tv "a")) {gc "Box"}] := by
  classical
  have hchk : CheckedTy (listT (tv "a")) := fun _ => rfl
  have hne : (fieldOf (tc "Box") (listT (tv "a")) {gc "Box"}).Nonempty := ⟨_, string_list_field⟩
  simp only [fieldSetC, ctorRow_mkbox, List.getElem?_cons_zero, if_pos hchk, List.map_cons, List.map_nil]
  simp [hne]

/-- **A field the range does not fix is not bounded by the member**
(the 11/06 binary's field rule; probe `field_private_var2`): under
`(: MkBox (-> (List $a) Box))`, `(MkBox (Cons 1 Nil))` is covered by `Box`, the
rule gives its field every `(List t)`, which the field `(Cons 1 Nil)`, typed
`(List Number)`, is not typed at least as generally as; every member allows
`(List String)`, so a call at that formal is discharged, while HE's check of the
field there fails. The fixed rule leaves the field unknown. -/
theorem free_field_not_lower :
    Covers bdecls (some [{gc "Box"}]) (app "MkBox" [numList [1]]) ∧
      ¬ Covers bdecls (fieldSetC bdecls "MkBox" 0 (some [{gc "Box"}])) (numList [1]) ∧
      (∀ Ms, fieldSetC bdecls "MkBox" 0 (some [{gc "Box"}]) = some Ms → ∀ S ∈ Ms, glist (gc "String") ∈ S) ∧
      ¬ Meets (glist (gc "String")) (stamp bdecls (numList [1])) ∧
      fieldSet bdecls "MkBox" 0 (some [{gc "Box"}]) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hlow := build_lower ctorRow_mkbox [numList [1]] [{glist (gc "Number")}]
      (.cons (.inr ⟨{glist (gc "Number")}, by rw [stamp_one_b]; simp, le_refl _⟩) .nil)
      (by rw [combo_box]; exact ⟨gc "Box", rfl⟩)
    rw [combo_box] at hlow
    exact ⟨{gc "Box"}, List.mem_singleton_self _, hlow⟩
  · rw [fieldC_box]
    rintro ⟨S, hS, -, hb⟩
    rw [List.mem_singleton] at hS
    subst hS
    rw [stamp_one_b] at hb
    rcases hb with hb | ⟨X, hX, hsub⟩
    · cases hb
    · simp only [List.mem_singleton, Sem.ok.injEq] at hX
      subst hX
      have := hsub string_list_field
      simp [glist, gc] at this
  · intro Ms hMs S hS
    rw [fieldC_box, Option.some.injEq] at hMs
    subst hMs
    rw [List.mem_singleton] at hS
    subst hS
    exact string_list_field
  · rw [stamp_one_b]
    rintro (h | h | ⟨X, hX, hx⟩)
    · cases h
    · simp [heUnchecked, glist, Ty.lift, Ty.map, Ty.bind] at h
    · simp only [List.mem_singleton, Sem.ok.injEq] at hX
      subst hX
      simp [glist, gc] at hx
  · have hfix : ¬ Fixes (tc "Box") (listT (tv "a")) := by
      intro h
      have := h "a" (by simp [listT, tv])
      simp [tc] at this
    simp [fieldSet, ctorRow_mkbox, hfix]

/-! ### A failing combination of lower bounds -/

/-- A number, and a list typed at least as generally as `(List String)`: a
formal's static type. -/
def kids7 : List TySet := [some [{gc "Number"}], some [{glist (gc "String")}]]

theorem combo7 : combo [tv "x", listT (tv "x")] (listT (tv "x")) [{gc "Number"}, {glist (gc "String")}] = ∅ := by
  ext T
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨θ, hj, -⟩
  rw [joint_cons] at hj
  obtain ⟨h1, h2⟩ := hj
  rw [Set.mem_singleton_iff] at h1 h2
  rw [h1] at h2
  simp [glist, gc] at h2

theorem scan7 : scan kids7 = .members [[{gc "Number"}], [{glist (gc "String")}]] := rfl

theorem sections7 :
    ([[{gc "Number"}], [{glist (gc "String")}]] : List (List (Set (Ty Empty)))).sections =
      [[{gc "Number"}, {glist (gc "String")}]] := by
  simp [List.sections]

/-- **A failing combination of lower bounds is no evidence of no value**
(the 11/06 binary's build rule; probe `lower_bound_empty`): with `1` and `Nil`,
the latter at the formal `(List String)`, the one combination fails, and the
rule reads the build `(Cons 1 Nil)` as having no value; HE's check passes it.
A build over it is then discharged as unreachable, while HE's check of
`(Cons "x" (Cons 1 Nil))` fails. The model's build is unknown. -/
theorem failing_lower_combination_builds :
    List.Forall₂ (Covers decls) kids7 [num 1, .symbol "Nil"] ∧
      HEPasses decls "Cons" [num 1, .symbol "Nil"] ∧
      buildSetC decls "Cons" kids7 = some [] ∧
      ¬ Covers decls (buildSetC decls "Cons" kids7) (app "Cons" [num 1, .symbol "Nil"]) ∧
      BuildPasses decls "Cons" [some [{gc "String"}], buildSetC decls "Cons" kids7] ∧
      ¬ HEPasses decls "Cons" [str "x", numList [1]] ∧
      buildSet decls "Cons" kids7 = none := by
  classical
  have hC : buildSetC decls "Cons" kids7 = some [] := by
    unfold buildSetC
    rw [ctorRow_cons]
    simp only [kids7, List.length_cons, List.length_nil, if_true]
    rw [show scan [some [{gc "Number"}], some [{glist (gc "String")}]] =
        .members [[{gc "Number"}], [{glist (gc "String")}]] from rfl]
    dsimp only
    rw [sections7]
    simp [combo7]
  refine ⟨?_, ?_, hC, ?_, ?_, ?_, ?_⟩
  · refine .cons ⟨{gc "Number"}, List.mem_singleton_self _, ⟨gc "Number", rfl⟩,
      .inr ⟨{gc "Number"}, by rw [stamp_num]; simp, le_refl _⟩⟩ (.cons ?_ .nil)
    refine ⟨{glist (gc "String")}, List.mem_singleton_self _, ⟨_, rfl⟩,
      .inr ⟨inst (listT (tv "x")), by rw [stamp_nil]; simp, ?_⟩⟩
    rintro T rfl
    exact ⟨fun _ => gc "String", by rw [bind_listT]⟩
  · have h : stamp decls (.expression (.symbol "Cons" :: [num 1, .symbol "Nil"])) =
        ⟨"Expression", [.ok {glist (gc "Number")}]⟩ := list_stamp 1 []
    exact ⟨{glist (gc "Number")}, by rw [h]; simp⟩
  · rw [hC]
    rintro ⟨S, hS, -⟩
    cases hS
  · rw [hC]
    exact ⟨consRow, _, _, ctorRow_cons, rfl, .inl rfl⟩
  · rintro ⟨X, hX⟩
    have h : (stamp decls (.expression (.symbol "Cons" :: [str "x", numList [1]]))).typs =
        [.err (inst consRow)] := wrong_class
    rw [h] at hX
    simp at hX
  · unfold buildSet
    rw [ctorRow_cons]
    simp only [kids7, List.length_cons, List.length_nil, if_true]
    rw [show scan [some [{gc "Number"}], some [{glist (gc "String")}]] =
        .members [[{gc "Number"}], [{glist (gc "String")}]] from rfl]
    dsimp only
    rw [sections7, if_neg]
    intro hall
    have := hall _ (List.mem_singleton_self _)
    rw [combo7] at this
    exact Set.not_nonempty_empty this

/-! ### `%Undefined%` inside an argument's typing -/

/-- `(: x (List %Undefined%))`. -/
def xdecls : Decls := fun s => if s = "x" then [listT (tc "%Undefined%")] else decls s

theorem inst_list_const (c : String) : inst (listT (tc c)) = {glist (gc c)} := by
  ext T
  simp only [inst, listT, tc, glist, gc, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym,
    Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨fun _ => default, h.symm⟩⟩

/-- **`%Undefined%` inside an argument's typing is a type** (probe
`nested_undefined_literal`): the literal `x` has the one typing
`(List %Undefined%)`, which does not allow `(List String)`, and HE's check of `x`
at `(List String)` fails. A matcher reading the inner `%Undefined%` as matching
every type discharges that check. -/
theorem undefined_member_checked :
    litSet xdecls (.symbol "x") = some [{glist (gc "%Undefined%")}] ∧
      glist (gc "String") ∉ ({glist (gc "%Undefined%")} : Set (Ty Empty)) ∧
      ¬ Meets (glist (gc "String")) (stamp xdecls (.symbol "x")) := by
  have hr : readRows (xdecls "x") = [listT (tc "%Undefined%")] := by
    simp [xdecls, readRows, listT, tc, undefinedTy]
  refine ⟨?_, by simp [glist, gc], ?_⟩
  · simp only [litSet, hr]
    rw [inst_list_const]
  · rw [stamp_symbol, hr]
    simp only [List.map_cons, List.map_nil, inst_list_const]
    rintro (h | h | ⟨X, hX, hx⟩)
    · cases h
    · simp [heUnchecked, glist, Ty.lift, Ty.map, Ty.bind] at h
    · simp only [List.mem_singleton, Sem.ok.injEq] at hX
      subst hX
      simp [glist, gc] at hx

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSets
