import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.DeclaredBuiltins
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ShapeTyping

/-!
# Static types that discharge checks

A check may be skipped where the value it would check is known to pass it.

**PeTTa: the same check of the same value** (`prepared_pure_petta_slot_at_formal`).
An activation of a head with a trusted version holds each argument at its
closed formal's fact: a call from outside passed the guard there, and a call
to itself keeps the fact by the version. A callee's version proves its range
of every answer on arguments meeting its entry facts. Passing such a value
on at an identical closed formal, directly or through `let`, meets the
callee's guard exactly once, so dropping that guard changes no answer and no
multiplicity (`identical_formal_discharged`, `proven_range_discharged`);
under functional declarations a guard that passed once meets the fact
(`passed_guard_holds`).

**HE: static types on HE's typing rule**, read by solutions (`ShapeTyping`'s
stamps). A static type `T` of a node says of every value reaching it that the
value has no typing or has a valid typing allowing `T` (`StaticAt`).
* *A check passed at a closed formal* gives that formal (`StaticAt` by
  definition of the check, `static_check_continues` for its use).
* *Field inversion* (`field_inversion`): an application of a constructor with
  one closed arrow `(-> T₁ … Tₘ R)` that is typable at `F` has `F = R`, and each
  field is untyped, at a parameter HE does not check, or typable at its `Tᵢ`.
  A parameter HE does not check gives its field nothing: under
  `(-> %Undefined% R)` the cell's typings are the same for every field
  (`unchecked_field_invisible`), so `%Undefined%` read off the declaration is
  not a static type of the field (the interpreter's counterexample is
  `HETypedRuleControls.undefined_field_not_static`). At a checked parameter a
  field whose typings are all errors passes them up (`checked_field_reads`).
* *A checked build* over fields meeting their parameters is typable at its
  range (`build_typable`); over fields whose typing is exactly their parameter
  its typing is exactly the range (`build_exact`), the typing a run may record
  for the value it built.
* *A symbol with one closed declaration* has exactly that typing
  (`symbol_exact`), and *a literal* its class (`literal_exact`).
* *The discharge* (`static_check_continues`): an argument statically at a
  closed parameter continues the check there as skipping it does. The check
  compares types exactly: `%Undefined%` inside a parameter is a type, so
  `(List String)` fails at `(List %Undefined%)` (`nested_undefined_checked`),
  as hyperon-experimental rejects it; a matcher reading the inner `%Undefined%`
  as a wildcard accepts it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StaticEvidence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## PeTTa: the same check of the same value -/

section PeTTa

variable {Γ : Decls} {grounded : String → Bool}

/-- Under functional declarations a value that passed the guard at a closed
formal meets the formal's fact. -/
theorem passed_guard_holds (hΓ : Functional Γ) {v : Atom} {F : Ty Empty}
    (passed : guardCount (info Γ v) F (metatype grounded v) ≠ 0) : Holds Γ grounded v F :=
  Holds.of_guardCount hΓ passed

/-- **Passing a held value on at the identical formal skips the callee's check
exactly**: the call with the formal checked and the call with it unchecked
have the same answers, multiplicity included. -/
theorem identical_formal_discharged (hΓ : Functional Γ) (body : List Atom → Multiset Atom)
    (pre post : List (Ty Empty)) (F R : Ty Empty) (us vs : List Atom) (len : pre.length = us.length)
    {v : Atom} (held : Holds Γ grounded v F) :
    chainCall Γ (metatype grounded) body (arrow ((pre ++ F :: post).map Ty.lift) R.lift)
        (us ++ v :: vs) =
      chainCall Γ (metatype grounded) body (arrow ((pre ++ uncheckedTy :: post).map Ty.lift) R.lift)
        (us ++ v :: vs) := by
  have h := argument_typed_by_callee (kind := metatype grounded) hΓ body pre post F R us vs len
    (ws := {v}) (fun w hw => by
      rw [Multiset.mem_singleton] at hw
      subst hw
      rw [held.guardCount]
      exact one_ne_zero)
  simpa only [Multiset.singleton_bind] using h

/-- **A callee's version proves its range of every answer** on arguments
meeting its entry facts: the answer is held at the range, so passing it on
at a formal equal to the range is discharged by `identical_formal_discharged`. -/
theorem proven_range_holds {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (hV : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) (n : ℕ) (ws : List Atom)
    (hws : EntryFacts Γ grounded As ws) {r : Atom} (hr : r ∈ versionRun bodyV n ws) :
    Holds Γ grounded r R :=
  version_results hV n ws hws r hr

/-- **The callee's answer passed on at its range**: the call's answers, each
passed to a callee at the identical formal `R`, are those of the callee with
`R` unchecked. -/
theorem proven_range_discharged (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (hV : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) (n : ℕ) (ws : List Atom)
    (hws : EntryFacts Γ grounded As ws) (body : List Atom → Multiset Atom)
    (pre post : List (Ty Empty)) (S : Ty Empty) (us vs : List Atom) (len : pre.length = us.length) :
    ((versionRun bodyV n ws).bind fun r =>
        chainCall Γ (metatype grounded) body (arrow ((pre ++ R :: post).map Ty.lift) S.lift)
          (us ++ r :: vs)) =
      (versionRun bodyV n ws).bind fun r =>
        chainCall Γ (metatype grounded) body (arrow ((pre ++ uncheckedTy :: post).map Ty.lift) S.lift)
          (us ++ r :: vs) :=
  Multiset.bind_congr fun _ hr =>
    identical_formal_discharged hΓ body pre post R S us vs len (proven_range_holds hV n ws hws hr)

end PeTTa

/-! ## HE: a parameter HE does not check carries no type -/

section HE

open ShapeTyping

/-- The arrow `(-> P R)` of one parameter. -/
def arrow1 (P R : Ty String) : Ty String := .app [.sym "->", P, R]

theorem readRows_arrow1 (P R : Ty String) : readRows [arrow1 P R] = [arrow1 P R] := by
  simp [readRows, arrow1, undefinedTy]

theorem isFun_arrow1 (P R : Ty String) : IsFun (rowTyping (arrow1 P R)).deriv.ty = true := by
  simp only [rowTyping, Typing.deriv]
  rw [IsFun_map]
  rfl

/-- The application typings of one declared arrow `(-> P R)`: HE's argument
check at `P`, from position one. -/
theorem appTypings_arrow1 (P R : Ty String) (j : HeInfo) :
    appTypings [j] (rowTyping (arrow1 P R)) =
      checkArgs ⟨(arrow1 P R).map own0, []⟩ (R.map own0) 1 [P.map own0] [j] [] := by
  unfold appTypings
  rw [rowTyping_push, arrowSplit_map']
  simp [arrow1, arrowSplit]

/-- The typings of `(c a)` under one declared arrow: the application typings of
that arrow. -/
theorem typs_one_arrow (Γ : Decls) (c : String) (P R : Ty String) (rows : Γ c = [arrow1 P R]) (a : Atom) :
    (heInfo Γ (.expression [.symbol c, a])).typs = appTypings [heInfo Γ a] (rowTyping (arrow1 P R)) := by
  rw [heInfo_expression]
  have hleaf : heInfo Γ (.symbol c) = ⟨"Symbol", [rowTyping (arrow1 P R)]⟩ := by
    rw [heInfo_symbol]
    simp only [heLeaf, rows, readRows_arrow1, List.map_cons, List.map_nil]
  simp [heNode, hleaf, isFun_arrow1, heTupleParts]

/-- **A parameter HE does not check makes its argument invisible**: under one
declared arrow `(-> %Undefined% R)`, `(c a)` has the same typings for every
argument `a`. -/
theorem unchecked_field_invisible (Γ : Decls) (c : String) (R : Ty String)
    (rows : Γ c = [arrow1 undefinedTy R]) (a b : Atom) :
    (heInfo Γ (.expression [.symbol c, a])).typs = (heInfo Γ (.expression [.symbol c, b])).typs := by
  rw [typs_one_arrow Γ c _ R rows a, typs_one_arrow Γ c _ R rows b, appTypings_arrow1,
    appTypings_arrow1]
  have hu : ∀ kind, heUnchecked ((undefinedTy : Ty String).map own0) kind = true := by
    intro kind
    rw [heUnchecked_map]
    simp [heUnchecked, undefinedTy]
  simp only [checkArgs, hu, Bool.or_true, if_true]

/-- **At a checked parameter the cell's typing reads the field**: a field with
typings that are all errors passes its errors up as the cell's typings. -/
theorem checked_field_reads (Γ : Decls) (c : String) (P R : Ty String) (rows : Γ c = [arrow1 P R])
    (a : Atom) (nonempty : (heInfo Γ a).typs ≠ [])
    (checked : heUnchecked P (heInfo Γ a).kind = false)
    (errors : (heInfo Γ a).typs.all (fun t => !t.isOk) = true) :
    (heInfo Γ (.expression [.symbol c, a])).typs = (heInfo Γ a).typs.map (Typing.push 1) := by
  rw [typs_one_arrow Γ c P R rows a, appTypings_arrow1]
  have hne : (heInfo Γ a).typs.isEmpty = false := by
    cases h : (heInfo Γ a).typs with
    | nil => exact absurd h nonempty
    | cons _ _ => rfl
  have hc : heUnchecked (P.map own0) (heInfo Γ a).kind = false := by rw [heUnchecked_map]; exact checked
  simp only [checkArgs, hne, hc, Bool.or_false, Bool.false_eq_true, if_false, errors, if_true]

/-! ### Static types on HE's stamps -/

/-- A stamp is typable at a ground type when one of its valid typings allows
it. -/
def Typable (st : Stamp) (T : Ty Empty) : Prop := ∃ X, Sem.ok X ∈ st.typs ∧ T ∈ X

/-- **What a static type `T` says of a value**: the value has no typing, which
passes every check, or it is typable at `T`. -/
def StaticAt (st : Stamp) (T : Ty Empty) : Prop := st.typs = [] ∨ Typable st T

/-- What HE's argument check reads of an argument at a parameter: nothing for
an argument without typings or at a parameter it does not check, and
otherwise a valid typing allowing the parameter. -/
def Meets (P : Ty Empty) (st : Stamp) : Prop :=
  st.typs = [] ∨ heUnchecked (P.lift : Ty String) st.kind = true ∨ Typable st P

theorem narrow_closed (Θ : Set (String → Ty Empty)) (P : Ty Empty) (S : Set (Ty Empty)) :
    narrow Θ P.lift S = {θ | θ ∈ Θ ∧ P ∈ S} := by
  ext θ
  simp [narrow, Ty.lift_bind_ground]

theorem range_closed (Θ : Set (String → Ty Empty)) (R : Ty Empty) :
    {T | ∃ θ ∈ Θ, (R.lift : Ty String).bind θ = T} ⊆ {R} := by
  rintro T ⟨θ, -, rfl⟩
  simp [Ty.lift_bind_ground]

/-- **Inversion of HE's argument check on a closed row**: a valid typing of
the check's result allows only the range, and every argument meets its
parameter. -/
theorem semCheck_inversion (ρ : Ty String) (R : Ty Empty) :
    ∀ (Ps : List (Ty Empty)) (ss : List Stamp) (Θ : Set (String → Ty Empty)) (X : Set (Ty Empty)),
      Sem.ok X ∈ semCheck ρ R.lift (Ps.map Ty.lift) ss Θ →
        X ⊆ {R} ∧ List.Forall₂ Meets Ps ss
  | [], [], Θ, X, h => by
      simp only [List.map_nil, semCheck, List.mem_singleton, Sem.ok.injEq] at h
      subst h
      exact ⟨range_closed Θ R, .nil⟩
  | [], _ :: _, _, _, h => by simp [semCheck] at h
  | _ :: _, [], _, _, h => by simp [semCheck] at h
  | P :: Ps, st :: ss, Θ, X, h => by
      simp only [List.map_cons, semCheck] at h
      split_ifs at h with hskip hall hms
      · obtain ⟨sub, rest⟩ := semCheck_inversion ρ R Ps ss Θ X h
        refine ⟨sub, .cons ?_ rest⟩
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
        obtain ⟨Θ', ⟨t, ht, hstep⟩, hX⟩ := h
        obtain ⟨sub, rest⟩ := semCheck_inversion ρ R Ps ss Θ' X hX
        refine ⟨sub, .cons (.inr (.inr ?_)) rest⟩
        cases t with
        | err _ => simp [semStep] at hstep
        | ok S =>
            simp only [semStep] at hstep
            split_ifs at hstep with hne
            obtain ⟨θ, hθ⟩ := hne
            rw [narrow_closed] at hθ
            exact ⟨S, ht, hθ.2⟩

/-- **A checked build types at its range**: on a closed row, arguments meeting
their parameters give a valid typing allowing the range. -/
theorem semCheck_typable (ρ : Ty String) (R : Ty Empty) :
    ∀ (Ps : List (Ty Empty)) (ss : List Stamp) (Θ : Set (String → Ty Empty)), Θ.Nonempty →
      List.Forall₂ Meets Ps ss → ∃ X, Sem.ok X ∈ semCheck ρ R.lift (Ps.map Ty.lift) ss Θ ∧ R ∈ X
  | [], [], Θ, hΘ, _ => by
      obtain ⟨θ, hθ⟩ := hΘ
      exact ⟨{T | ∃ θ ∈ Θ, (R.lift : Ty String).bind θ = T}, by simp [semCheck], θ, hθ,
        Ty.lift_bind_ground θ R⟩
  | P :: Ps, st :: ss, Θ, hΘ, .cons hP rest => by
      simp only [List.map_cons, semCheck]
      split_ifs with hskip hall hms
      · exact semCheck_typable ρ R Ps ss Θ hΘ rest
      · exfalso
        rcases hP with h1 | h1 | ⟨X, hX, _⟩
        · simp [h1] at hskip
        · simp [h1] at hskip
        · rw [List.all_eq_true] at hall
          simpa [Sem.isOk] using hall _ hX
      · exfalso
        rcases hP with h1 | h1 | ⟨X, hX, hPX⟩
        · simp [h1] at hskip
        · simp [h1] at hskip
        · have hmem : narrow Θ P.lift X ∈ st.typs.filterMap (semStep Θ P.lift) := by
            rw [List.mem_filterMap]
            refine ⟨_, hX, ?_⟩
            have hne : (narrow Θ P.lift X).Nonempty := by
              obtain ⟨θ, hθ⟩ := hΘ
              exact ⟨θ, by rw [narrow_closed]; exact ⟨hθ, hPX⟩⟩
            simp [semStep, hne]
          rw [List.isEmpty_iff] at hms
          rw [hms] at hmem
          cases hmem
      · rcases hP with h1 | h1 | ⟨X, hX, hPX⟩
        · exact absurd (by simp [h1]) hskip
        · exact absurd (by simp [h1]) hskip
        · have heq : narrow Θ P.lift X = Θ := by
            rw [narrow_closed]
            ext θ
            simp [hPX]
          have hmem : Θ ∈ st.typs.filterMap (semStep Θ P.lift) := by
            rw [List.mem_filterMap]
            refine ⟨_, hX, ?_⟩
            simp [semStep, heq, hΘ]
          obtain ⟨Y, hY, hRY⟩ := semCheck_typable ρ R Ps ss Θ hΘ rest
          exact ⟨Y, List.mem_flatMap.mpr ⟨Θ, hmem, hY⟩, hRY⟩

/-- An argument whose only typing is exactly its parameter. -/
def Exact (P : Ty Empty) (st : Stamp) : Prop :=
  st.typs = [] ∨ heUnchecked (P.lift : Ty String) st.kind = true ∨ st.typs = [Sem.ok {P}]

/-- **A checked build over exact arguments types exactly at its range**: one
valid typing, the range alone. -/
theorem semCheck_exact (ρ : Ty String) (R : Ty Empty) :
    ∀ (Ps : List (Ty Empty)) (ss : List Stamp) (Θ : Set (String → Ty Empty)), Θ.Nonempty →
      List.Forall₂ Exact Ps ss →
        semCheck ρ R.lift (Ps.map Ty.lift) ss Θ = [Sem.ok {T | ∃ θ ∈ Θ, (R.lift : Ty String).bind θ = T}]
  | [], [], Θ, _, _ => by simp [semCheck]
  | P :: Ps, st :: ss, Θ, hΘ, .cons hP rest => by
      simp only [List.map_cons, semCheck]
      split_ifs with hskip hall hms
      · exact semCheck_exact ρ R Ps ss Θ hΘ rest
      · exfalso
        rcases hP with h1 | h1 | h1
        · simp [h1] at hskip
        · simp [h1] at hskip
        · simp [h1, Sem.isOk] at hall
      · exfalso
        rcases hP with h1 | h1 | h1
        · simp [h1] at hskip
        · simp [h1] at hskip
        · have hne : (narrow Θ P.lift {P}).Nonempty := by
            obtain ⟨θ, hθ⟩ := hΘ
            exact ⟨θ, by rw [narrow_closed]; exact ⟨hθ, rfl⟩⟩
          simp [h1, semStep, hne] at hms
      · rcases hP with h1 | h1 | h1
        · exact absurd (by simp [h1]) hskip
        · exact absurd (by simp [h1]) hskip
        · have heq : narrow Θ P.lift {P} = Θ := by
            rw [narrow_closed]
            ext θ
            simp
          have hstep : semStep Θ P.lift (Sem.ok {P}) = some Θ := by
            simp [semStep, heq, hΘ]
          simp only [h1, List.filterMap_cons, List.filterMap_nil, hstep, List.flatMap_cons,
            List.flatMap_nil, List.append_nil]
          exact semCheck_exact ρ R Ps ss Θ hΘ rest

/-- The rows of a constructor with one closed arrow. -/
theorem closed_row_rows (Ts : List (Ty Empty)) (R : Ty Empty) :
    readRows [arrow (Ts.map Ty.lift) (R.lift : Ty String)] = [arrow (Ts.map Ty.lift) R.lift] ∧
      IsFun (arrow (Ts.map Ty.lift) (R.lift : Ty String)) = true := by
  constructor
  · simp [readRows, arrow, undefinedTy]
  · simp only [arrow, IsFun]
    cases Ts <;> simp

/-- The stamp of a constructor application under one closed arrow: the
argument check's typings. -/
theorem stamp_closed_row (Γ : Decls) (c : String) (Ts : List (Ty Empty)) (R : Ty Empty)
    (rows : Γ c = [arrow (Ts.map Ty.lift) R.lift]) (args : List Atom) (len : Ts.length = args.length) :
    stamp Γ (.expression (.symbol c :: args)) =
      ⟨"Expression", semCheck (arrow (Ts.map Ty.lift) R.lift) R.lift (Ts.map Ty.lift)
        (args.map (stamp Γ)) Set.univ⟩ := by
  rw [stamp_node, rows]
  obtain ⟨hr, hf⟩ := closed_row_rows Ts R
  simp [semNode, hr, hf, prodSets, semApp, len]

/-- **Field inversion**: an application of a constructor with one closed arrow
`(-> T₁ … Tₘ R)` typable at `F` has `F = R`, and every field meets its
parameter: untyped, at a parameter HE does not check, or typable at it. -/
theorem field_inversion (Γ : Decls) (c : String) (Ts : List (Ty Empty)) (R : Ty Empty)
    (rows : Γ c = [arrow (Ts.map Ty.lift) R.lift]) (args : List Atom) {F : Ty Empty}
    (typed : Typable (stamp Γ (.expression (.symbol c :: args))) F) :
    F = R ∧ List.Forall₂ Meets Ts (args.map (stamp Γ)) := by
  by_cases len : Ts.length = args.length
  · rw [stamp_closed_row Γ c Ts R rows args len] at typed
    obtain ⟨X, hX, hF⟩ := typed
    obtain ⟨sub, rest⟩ := semCheck_inversion _ R Ts _ Set.univ X hX
    exact ⟨sub hF, rest⟩
  · exfalso
    obtain ⟨X, hX, _⟩ := typed
    rw [stamp_node, rows] at hX
    obtain ⟨hr, hf⟩ := closed_row_rows Ts R
    simp [semNode, hr, hf, prodSets, semApp, len] at hX

/-- **A checked build is typable at its range**: fields meeting their
parameters give the application a valid typing allowing the range. -/
theorem build_typable (Γ : Decls) (c : String) (Ts : List (Ty Empty)) (R : Ty Empty)
    (rows : Γ c = [arrow (Ts.map Ty.lift) R.lift]) (args : List Atom)
    (meets : List.Forall₂ Meets Ts (args.map (stamp Γ))) :
    Typable (stamp Γ (.expression (.symbol c :: args))) R := by
  have len : Ts.length = args.length := by simpa using meets.length_eq
  rw [stamp_closed_row Γ c Ts R rows args len]
  exact semCheck_typable _ R Ts _ Set.univ ⟨fun _ => .sym "", trivial⟩ meets

/-- **A checked build over exact fields has exactly its range as typing**: the
typing a run may record for the value it built is HE's typing of it. -/
theorem build_exact (Γ : Decls) (c : String) (Ts : List (Ty Empty)) (R : Ty Empty)
    (rows : Γ c = [arrow (Ts.map Ty.lift) R.lift]) (args : List Atom)
    (exact : List.Forall₂ Exact Ts (args.map (stamp Γ))) :
    stamp Γ (.expression (.symbol c :: args)) = ⟨"Expression", [Sem.ok {R}]⟩ := by
  have len : Ts.length = args.length := by simpa using exact.length_eq
  rw [stamp_closed_row Γ c Ts R rows args len,
    semCheck_exact _ R Ts _ Set.univ ⟨fun _ => .sym "", trivial⟩ exact]
  congr
  ext T
  simp only [Set.mem_univ, true_and]
  constructor
  · rintro ⟨θ, rfl⟩
    exact Ty.lift_bind_ground θ R
  · rintro rfl
    exact ⟨fun _ => .sym "", Ty.lift_bind_ground _ T⟩

/-- A path's assignments continue through a valid typing allowing a closed
parameter. -/
theorem continue_mem {Θ : Set (String → Ty Empty)} (hΘ : Θ.Nonempty) {P : Ty Empty} {st : Stamp}
    {X : Set (Ty Empty)} (hX : Sem.ok X ∈ st.typs) (hPX : P ∈ X) :
    Θ ∈ st.typs.filterMap (semStep Θ P.lift) := by
  have heq : narrow Θ P.lift X = Θ := by
    rw [narrow_closed]
    ext θ
    simp [hPX]
  rw [List.mem_filterMap]
  refine ⟨_, hX, ?_⟩
  simp [semStep, heq, hΘ]

/-- **A static type that is the formal discharges HE's check**: wherever the
rest of a path continues, an argument statically at the closed parameter `P`
continues the check at `P` the same way, as skipping the check does. -/
theorem static_check_continues (ρ : Ty String) (R : Ty Empty) (P : Ty Empty) (Ps : List (Ty Empty))
    (st : Stamp) (ss : List Stamp) (Θ : Set (String → Ty Empty)) (hΘ : Θ.Nonempty)
    (hst : StaticAt st P) (x : Sem) (hx : x ∈ semCheck ρ R.lift (Ps.map Ty.lift) ss Θ) :
    x ∈ semCheck ρ R.lift ((P :: Ps).map Ty.lift) (st :: ss) Θ := by
  simp only [List.map_cons, semCheck]
  split_ifs with hskip hall hms
  · exact hx
  · exfalso
    rcases hst with h1 | ⟨X, hX, _⟩
    · simp [h1] at hskip
    · rw [List.all_eq_true] at hall
      simpa [Sem.isOk] using hall _ hX
  · exfalso
    rcases hst with h1 | ⟨X, hX, hPX⟩
    · simp [h1] at hskip
    · have hmem := continue_mem hΘ hX hPX
      rw [List.isEmpty_iff] at hms
      rw [hms] at hmem
      cases hmem
  · rcases hst with h1 | ⟨X, hX, hPX⟩
    · exact absurd (by simp [h1]) hskip
    · exact List.mem_flatMap.mpr ⟨Θ, continue_mem hΘ hX hPX, hx⟩

theorem inst_lift (τ : Ty Empty) : inst (τ.lift : Ty String) = {τ} := by
  ext T
  constructor
  · rintro ⟨θ, rfl⟩
    exact Ty.lift_bind_ground θ τ
  · rintro rfl
    exact ⟨fun _ => .sym "", Ty.lift_bind_ground _ T⟩

/-- **A symbol with one closed declaration has exactly that typing.** -/
theorem symbol_exact (Γ : Decls) (s : String) (τ : Ty Empty) (rows : Γ s = [τ.lift])
    (defined : (τ.lift : Ty String) ≠ undefinedTy) :
    stamp Γ (.symbol s) = ⟨"Symbol", [Sem.ok {τ}]⟩ := by
  simp only [stamp, heInfo_symbol, heLeaf, HeInfo.stamp, rows, readRows, List.filter_cons,
    List.filter_nil, defined, ne_eq, not_false_eq_true, decide_true, if_true, List.map_cons,
    List.map_nil, Typing.solve, rowTyping]
  rw [show sols ⟨(τ.lift : Ty String).map DVar.own, []⟩ = sols (rowTyping τ.lift).deriv from rfl,
    sols_rowTyping, inst_lift]

/-- **A literal's typing is its class**, whatever the declarations: the
models have symbol subjects only, as the C requires where it reads a
literal's typing per grounded kind. -/
theorem literal_exact (Γ : Decls) (g : GroundedValue) (c : String) (hc : valueClass g = some c) :
    stamp Γ (.grounded g) = ⟨"Grounded", [Sem.ok {.sym c}]⟩ := by
  simp only [stamp, heInfo_grounded, heLeaf, hc, HeInfo.stamp, List.map_cons, List.map_nil,
    Typing.solve, sols_classDeriv]

/-- `(List T)`. -/
def listTy (T : Ty Empty) : Ty Empty := .app [.sym "List", T]

/-- **`%Undefined%` inside a parameter is a type, not a wildcard**: at
`(List %Undefined%)` an argument typed exactly `(List String)` fails HE's
check, as hyperon-experimental rejects `(f (Cons "x" Nil))` under
`(: f (-> (List %Undefined%) Number))`. A matcher reading the inner
`%Undefined%` as matching every type accepts it. -/
theorem nested_undefined_checked (ρ : Ty String) (R : Ty Empty) (Ps : List (Ty Empty))
    (ss : List Stamp) (Θ : Set (String → Ty Empty)) :
    semCheck ρ R.lift ((listTy (.sym "%Undefined%") :: Ps).map Ty.lift)
        (⟨"Expression", [Sem.ok {listTy (.sym "String")}]⟩ :: ss) Θ = [Sem.err (inst ρ)] := by
  have hempty : ¬ (narrow Θ (listTy (.sym "%Undefined%")).lift {listTy (.sym "String")}).Nonempty := by
    rintro ⟨θ, hθ⟩
    rw [narrow_closed] at hθ
    simp [listTy] at hθ
  have hu : heUnchecked ((listTy (.sym "%Undefined%")).lift : Ty String) "Expression" = false := by
    simp [listTy, Ty.lift, Ty.map, Ty.bind, heUnchecked]
  simp [semCheck, hu, Sem.isOk, semStep, hempty, List.filter]

end HE

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StaticEvidence
