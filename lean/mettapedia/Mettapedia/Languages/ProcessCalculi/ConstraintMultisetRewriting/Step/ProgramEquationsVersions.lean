import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquationsControls

/-!
# Changing definitions given by pattern equations: versions, citations and rechecks

A definition has versions: `defs u` is the list of its equations at version `u`. The row `ver u`
says which version is installed. A call reads the installed version, matches the call against that
version's equations, and leaves a citation `cite u` of the version it read. A redefinition thread
`(redefTo u')` takes the installed version and installs `u'`. Adding or removing equations is
moving to a version whose equation list has one more or one fewer equation.

* **Reference semantics** (`VStep`), and the **compiled schemas** (`vschema`): one schema per
  equation of each version, reading that version's row, plus one redefinition schema per pair of
  versions. They present the reference semantics exactly on well-formed rows (`vstep_iff`), so
  adequacy on the ordinary step follows (`vexecution`).
* **What each computation records** (`citation_reads_version`, `citations_persist`): every new
  citation is made by a call that read the installed version it cites, and no rule removes one.
* **What stays valid** (`answers_append`, `answers_remove`, `call_transports`): adding equations at
  the end keeps every old answer, in order, and appends exactly the new equations' answers; removing
  an equation removes exactly its answers; a call step under one version is a call step under every
  version containing the equation it used, citing the new version.
* **Controls**: the exact answer multiset does not transport when an equation is added
  (`added_changes_answers`), an answer is lost when its equation is removed
  (`removed_loses_answer`), and the recheck of a citation passes against a version containing the
  equation and fails against one without it (`recheck_control`). In one run, the same call cites
  the version it read before or after a redefinition (`call_before_redefinition`,
  `call_after_redefinition`).

The compiled account fixes the versions ahead: each installed version has its schemas. Installing
arbitrary new equations while running needs equations as data, which is the interpreter's form
(`ProgramCompiledObstruction`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Controls

/-! ## Rows -/

/-- The installed version. -/
def ver (u : ℕ) : Tm := tagged 41 (.const u)
/-- A citation of the version a call read. -/
def cite (u : ℕ) : Tm := tagged 42 (.const u)
/-- The expression asking to install version `u`. -/
def redefTo (u : ℕ) : Tm := tagged 43 (.const u)
/-- The value of a finished redefinition. -/
def done : Tm := .const 44

/-- **Well-formed rows**: tagged, and version and citation rows are ground. -/
def Good (r : Tm) : Prop :=
  Tagged r ∧ ∀ k s, r = tagged k s → (k = 41 ∨ k = 42) → ∃ u : ℕ, s = .const u

theorem good_tagged {k : ℕ} {s : Tm} (other : k ≠ 41 ∧ k ≠ 42) : Good (tagged k s) := by
  refine ⟨tagged_tagged k s, fun k' s' same ground => ?_⟩
  obtain ⟨rfl, -⟩ := tagged_inj.mp same
  omega

theorem good_ground {k u : ℕ} : Good (tagged k (.const u)) := by
  refine ⟨tagged_tagged k _, fun k' s' same _ => ?_⟩
  obtain ⟨-, rfl⟩ := tagged_inj.mp same
  exact ⟨u, rfl⟩

theorem Good.apply {r : Tm} (good : Good r) (σ : Subst rows) : Good (σ.applyTerm r) := by
  obtain ⟨⟨k, s, rfl⟩, ground⟩ := good
  rw [apply_tagged]
  by_cases special : k = 41 ∨ k = 42
  · obtain ⟨u, rfl⟩ := ground k s rfl special
    exact good_ground
  · exact good_tagged ⟨fun h => special (.inl h), fun h => special (.inr h)⟩

/-! ## The reference semantics -/

/-- **The reference semantics of versioned definitions.** A call reads the installed version `u`,
matches one of its equations by two-way unification, and leaves a citation of `u`; a redefinition
takes the installed version and installs `u'`. -/
inductive VStep (defs : ℕ → Program) : Multiset Tm × ℕ → Multiset Tm × ℕ → Prop
  | call (u : ℕ) (j : Fin (defs u).length) (t : Tm) (F : Multiset Tm) (n : ℕ) (θ : Subst rows)
      (mgu : IsMGU [(((defs u).get j).lhs.at n, t)] θ) :
      VStep defs (thread t ::ₘ ver u ::ₘ F, n)
        (thread (θ.applyTerm (((defs u).get j).rhs.at n)) ::ₘ cite u ::ₘ ver u ::ₘ F.map θ.applyTerm,
          n + 1)
  | redefine (u u' : ℕ) (t : Tm) (F : Multiset Tm) (n : ℕ) (θ : Subst rows)
      (mgu : IsMGU [(redefTo u', t)] θ) :
      VStep defs (thread t ::ₘ ver u ::ₘ F, n) (thread done ::ₘ ver u' ::ₘ F.map θ.applyTerm, n + 1)

/-! ## The compiled schemas -/

/-- The schemas of the versioned program: one per equation of each version, and one redefinition
per pair of versions. -/
inductive VRule (defs : ℕ → Program) where
  | call (u : ℕ) (j : Fin (defs u).length)
  | redefine (u u' : ℕ)

/-- **The compiled versioned program.** A call schema takes the call occurrence, reads its
version's row, and makes the instantiated right-hand side and the citation. -/
def vschema (defs : ℕ → Program) : VRule defs → Schema
  | .call u j => ⟨[ptag 40 ((defs u).get j).lhs], [ptag 41 (.sym u)],
      [ptag 40 ((defs u).get j).rhs, ptag 42 (.sym u)]⟩
  | .redefine u u' => ⟨[ptag 40 (ptag 43 (.sym u')), ptag 41 (.sym u)], [],
      [ptag 40 (.sym 44), ptag 41 (.sym u')]⟩

theorem vschema_single (defs : ℕ → Program) (i : VRule defs) : (vschema defs i).read.length ≤ 1 := by
  cases i <;> simp [vschema]

theorem ground_fixed (σ : Subst rows) (k u : ℕ) : σ.applyTerm (tagged k (.const u)) = tagged k (.const u) := by
  rw [apply_tagged]
  rfl

/-- A problem with a ground equation beside a tagged one has the tagged one's most general
unifiers. -/
theorem isMGU_ground_iff {k k' c : ℕ} {a b : Tm} {θ : Subst rows} :
    IsMGU [(tagged k a, tagged k b), (tagged k' (.const c), tagged k' (.const c))] θ ↔
      IsMGU [(a, b)] θ := by
  have unifiers : ∀ δ : Subst rows,
      Unifies δ [(tagged k a, tagged k b), (tagged k' (.const c), tagged k' (.const c))] ↔
        Unifies δ [(a, b)] := by
    intro δ
    rw [← unifies_tagged_iff δ k]
    simp [Unifies]
  have vars : eqVars [(tagged k a, tagged k b), (tagged k' (.const c), tagged k' (.const c))] =
      eqVars [(a, b)] := by
    simp [eqVars, freeVars_tagged, Term.freeVars]
  exact ⟨fun mgu => mgu.congr unifiers vars, fun mgu => mgu.congr (fun δ => (unifiers δ).symm) vars.symm⟩

theorem version_forced {u : ℕ} {r : Tm} (good : Good r) {θ : Subst rows}
    (same : θ.applyTerm (tagged 41 (.const u)) = θ.applyTerm r) : r = ver u := by
  obtain ⟨⟨k, s, rfl⟩, ground⟩ := good
  rw [apply_tagged, apply_tagged, tagged_inj] at same
  obtain ⟨rfl, same⟩ := same
  obtain ⟨u', rfl⟩ := ground 41 s rfl (.inl rfl)
  change (.const u : Tm) = (.const u' : Tm) at same
  rw [ver, same]

theorem thread_forced {k : ℕ} {a : Tm} {r : Tm} (good : Good r) {θ : Subst rows}
    (same : θ.applyTerm (tagged k a) = θ.applyTerm r) : ∃ s, r = tagged k s := by
  obtain ⟨⟨k', s, rfl⟩, -⟩ := good
  rw [apply_tagged, apply_tagged, tagged_inj] at same
  exact ⟨s, by rw [same.1]⟩

theorem ground_rows (u : ℕ) (θ : Subst rows) (F : Multiset Tm) (a b : Tm) :
    (([a, b] : List Tm) : Multiset Tm) + ((([θ.applyTerm (ver u)] : List Tm) : Multiset Tm) + F) =
      a ::ₘ b ::ₘ ver u ::ₘ F := by
  rw [ver, ground_fixed]
  show (a ::ₘ b ::ₘ 0) + ((tagged 41 (.const u) ::ₘ 0) + F) = _
  rw [Multiset.cons_add, Multiset.cons_add, zero_add, Multiset.cons_add, zero_add]

theorem one_one_rows (F : Multiset Tm) (a b : Tm) :
    (([a] : List Tm) : Multiset Tm) + ((([b] : List Tm) : Multiset Tm) + F) = a ::ₘ b ::ₘ F := by
  show (a ::ₘ 0) + ((b ::ₘ 0) + F) = _
  rw [Multiset.cons_add, zero_add, Multiset.cons_add, zero_add]

theorem pair_rows (F : Multiset Tm) (a b : Tm) :
    (([a, b] : List Tm) : Multiset Tm) + ((([] : List Tm) : Multiset Tm) + F) = a ::ₘ b ::ₘ F := by
  show (a ::ₘ b ::ₘ 0) + (0 + F) = _
  rw [Multiset.cons_add, Multiset.cons_add, zero_add, zero_add]

/-- **The compiled schemas present the reference semantics exactly**, on well-formed rows. -/
theorem vstep_iff {defs : ℕ → Program} {W : Multiset Tm} {n : ℕ} (good : ∀ r ∈ W, Good r)
    (s' : Multiset Tm × ℕ) : VStep defs (W, n) s' ↔ ORewrites (vschema defs) (W, n) s' := by
  constructor
  · intro step
    cases step with
    | call u j t F n θ mgu =>
        refine .fire (.call u j) ⟨[thread t], [ver u], F, θ, rfl, rfl, (one_one_rows F _ _).symm, ?_, ?_⟩
        · exact (isMGU_ground_iff (k := 40) (k' := 41) (c := u)).mpr mgu
        · show _ = (([θ.applyTerm (tagged 40 (((defs u).get j).rhs.at n)),
              θ.applyTerm (tagged 42 (.const u))] : List Tm) : Multiset Tm) +
            ((([θ.applyTerm (ver u)] : List Tm) : Multiset Tm) + F.map θ.applyTerm)
          rw [ground_rows, apply_tagged, ground_fixed]
          rfl
    | redefine u u' t F n θ mgu =>
        refine .fire (.redefine u u') ⟨[thread t, ver u], [], F, θ, rfl, rfl, (pair_rows F _ _).symm,
          ?_, ?_⟩
        · exact (isMGU_ground_iff (k := 40) (k' := 41) (c := u)).mpr mgu
        · show _ = (([θ.applyTerm (tagged 40 (.const 44)), θ.applyTerm (tagged 41 (.const u'))] :
              List Tm) : Multiset Tm) + ((([] : List Tm) : Multiset Tm) + F.map θ.applyTerm)
          rw [ground_fixed, ground_fixed, pair_rows]
          rfl
  · intro step
    cases step with
    | fire i fires =>
        obtain ⟨taken, read, F, θ, takeLength, readLength, hW, mgu, rfl⟩ := fires
        cases i with
        | call u j =>
            obtain ⟨r, rfl⟩ : ∃ r, taken = [r] := List.length_eq_one_iff.mp (by
              rw [← takeLength]; rfl)
            obtain ⟨r', rfl⟩ : ∃ r', read = [r'] := List.length_eq_one_iff.mp (by
              rw [← readLength]; rfl)
            have rIn : r ∈ W := by rw [hW]; simp
            have r'In : r' ∈ W := by rw [hW]; simp
            obtain ⟨s, rfl⟩ := thread_forced (good r rIn)
              (mgu.unifies ((ptag 40 ((defs u).get j).lhs).at n, r)
                (List.mem_append_left _ (List.mem_singleton_self _)))
            have isVer := version_forced (good r' r'In)
              (mgu.unifies ((ptag 41 (.sym u)).at n, r')
                (List.mem_append_right _ (List.mem_singleton_self _)))
            subst isVer
            have mgu' : IsMGU [(((defs u).get j).lhs.at n, s)] θ := by
              have tag : IsMGU [(tagged 40 (((defs u).get j).lhs.at n), tagged 40 s),
                  (tagged 41 (.const u), tagged 41 (.const u))] θ := mgu
              exact isMGU_ground_iff.mp tag
            subst hW
            have start : (([tagged 40 s] : List Tm) : Multiset Tm) +
                ((([ver u] : List Tm) : Multiset Tm) + F) = thread s ::ₘ ver u ::ₘ F := one_one_rows F _ _
            have finish : ((((vschema defs (.call u j)).make.map fun q => θ.applyTerm (q.at n)) :
                List Tm) : Multiset Tm) +
                (((([ver u] : List Tm).map θ.applyTerm : List Tm) : Multiset Tm) + F.map θ.applyTerm) =
                thread (θ.applyTerm (((defs u).get j).rhs.at n)) ::ₘ cite u ::ₘ ver u ::ₘ
                  F.map θ.applyTerm := by
              show (([θ.applyTerm (tagged 40 (((defs u).get j).rhs.at n)),
                θ.applyTerm (tagged 42 (.const u))] : List Tm) : Multiset Tm) +
                ((([θ.applyTerm (ver u)] : List Tm) : Multiset Tm) + F.map θ.applyTerm) = _
              rw [ground_rows, apply_tagged, ground_fixed]
              rfl
            rw [start, finish]
            exact .call u j s F n θ mgu'
        | redefine u u' =>
            obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, taken = [r₁, r₂] := List.length_eq_two.mp (by
              rw [← takeLength]; rfl)
            have readNil : read = [] := List.length_eq_zero_iff.mp (by
              rw [← readLength]; rfl)
            subst readNil
            have r₁In : r₁ ∈ W := by rw [hW]; simp
            have r₂In : r₂ ∈ W := by rw [hW]; simp
            obtain ⟨s, rfl⟩ := thread_forced (good r₁ r₁In)
              (mgu.unifies ((ptag 40 (ptag 43 (.sym u'))).at n, r₁)
                (List.mem_append_left _ List.mem_cons_self))
            have isVer := version_forced (good r₂ r₂In)
              (mgu.unifies ((ptag 41 (.sym u)).at n, r₂)
                (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
            subst isVer
            have mgu' : IsMGU [(redefTo u', s)] θ := by
              have tag : IsMGU [(tagged 40 (redefTo u'), tagged 40 s),
                  (tagged 41 (.const u), tagged 41 (.const u))] θ := mgu
              exact isMGU_ground_iff.mp tag
            subst hW
            have start : (([tagged 40 s, ver u] : List Tm) : Multiset Tm) +
                ((([] : List Tm) : Multiset Tm) + F) = thread s ::ₘ ver u ::ₘ F := pair_rows F _ _
            have finish : ((((vschema defs (.redefine u u')).make.map fun q => θ.applyTerm (q.at n)) :
                List Tm) : Multiset Tm) +
                (((([] : List Tm).map θ.applyTerm : List Tm) : Multiset Tm) + F.map θ.applyTerm) =
                thread done ::ₘ ver u' ::ₘ F.map θ.applyTerm := by
              show (([θ.applyTerm (tagged 40 (.const 44)), θ.applyTerm (tagged 41 (.const u'))] :
                List Tm) : Multiset Tm) + ((([] : List Tm) : Multiset Tm) + F.map θ.applyTerm) = _
              rw [ground_fixed, ground_fixed, pair_rows]
              rfl
            rw [start, finish]
            exact .redefine u u' s F n θ mgu'

theorem vstep_good {defs : ℕ → Program} {s s' : Multiset Tm × ℕ} (step : VStep defs s s')
    (good : ∀ r ∈ s.1, Good r) : ∀ r ∈ s'.1, Good r := by
  cases step with
  | call u j t F n θ mgu =>
      intro r member
      simp only [Multiset.mem_cons] at member
      rcases member with rfl | rfl | rfl | member
      · exact good_tagged ⟨by decide, by decide⟩
      · exact good_ground
      · exact good_ground
      · obtain ⟨r₀, r₀In, rfl⟩ := Multiset.mem_map.mp member
        exact (good r₀ (by simp [r₀In])).apply θ
  | redefine u u' t F n θ mgu =>
      intro r member
      simp only [Multiset.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact good_tagged ⟨by decide, by decide⟩
      · exact good_ground
      · obtain ⟨r₀, r₀In, rfl⟩ := Multiset.mem_map.mp member
        exact (good r₀ (by simp [r₀In])).apply θ

theorem vruns_iff {defs : ℕ → Program} {s : Multiset Tm × ℕ} (good : ∀ r ∈ s.1, Good r)
    (s' : Multiset Tm × ℕ) :
    Relation.ReflTransGen (VStep defs) s s' ↔ Relation.ReflTransGen (ORewrites (vschema defs)) s s' := by
  constructor
  · intro path
    suffices Relation.ReflTransGen (ORewrites (vschema defs)) s s' ∧ ∀ r ∈ s'.1, Good r from this.1
    induction path with
    | refl => exact ⟨.refl, good⟩
    | @tail b c _ step ih =>
        obtain ⟨run, good'⟩ := ih
        obtain ⟨W, n⟩ := b
        exact ⟨run.tail ((vstep_iff good' c).mp step), vstep_good step good'⟩
  · intro path
    suffices Relation.ReflTransGen (VStep defs) s s' ∧ ∀ r ∈ s'.1, Good r from this.1
    induction path with
    | refl => exact ⟨.refl, good⟩
    | @tail b c _ step ih =>
        obtain ⟨run, good'⟩ := ih
        obtain ⟨W, n⟩ := b
        have source := (vstep_iff good' c).mpr step
        exact ⟨run.tail source, vstep_good source good'⟩

/-- **Adequacy of versioned definitions on the ordinary step.** -/
theorem vexecution (defs : ℕ → Program) (l : List Tm) (good : ∀ r ∈ l, Good r)
    (bounded : ∀ t ∈ l, Bounded 1 t) (W : Multiset Tm) (m : ℕ) :
    (Relation.ReflTransGen (VStep defs) ((l : Multiset Tm), 1) (W, m) →
      ∃ D, Relation.ReflTransGen (Translated (vschema defs)) (openInitial l, 1) (D, m) ∧
        ORepresents D W m) ∧
    (∀ D, Relation.ReflTransGen (Translated (vschema defs)) (openInitial l, 1) (D, m) →
      ∃ W', Relation.ReflTransGen (VStep defs) ((l : Multiset Tm), 1) (W', m) ∧
        ORepresents D W' m) := by
  have good' : ∀ r ∈ ((l : Multiset Tm), 1).1, Good r := fun r member =>
    good r (Multiset.mem_coe.mp member)
  obtain ⟨sound, complete⟩ := oexecution (vschema_single defs) l bounded W m
  refine ⟨fun path => sound ((vruns_iff good' _).mp path), fun D run => ?_⟩
  obtain ⟨W', path, rep⟩ := complete D run
  exact ⟨W', (vruns_iff good' _).mpr path, rep⟩

/-! ## What each computation records -/

theorem cite_ne_thread (u : ℕ) (t : Tm) : cite u ≠ thread t := fun h => by
  have := (tagged_inj.mp h).1
  omega

theorem cite_ne_ver (u u' : ℕ) : cite u ≠ ver u' := fun h => by
  have := (tagged_inj.mp h).1
  omega

theorem cite_inj {u u' : ℕ} (h : cite u = cite u') : u = u' := by
  have := (tagged_inj.mp h).2
  injection this

theorem cite_of_apply {r : Tm} (good : Good r) {θ : Subst rows} {u : ℕ} (h : θ.applyTerm r = cite u) :
    r = cite u := by
  obtain ⟨⟨k, s, rfl⟩, ground⟩ := good
  rw [apply_tagged] at h
  obtain ⟨rfl, -⟩ := tagged_inj.mp h
  obtain ⟨u', rfl⟩ := ground 42 s rfl (.inr rfl)
  rw [Subst.applyTerm_const] at h
  exact h

/-- **Every new citation is made by a call that read the installed version it cites.** -/
theorem citation_reads_version {defs : ℕ → Program} {s s' : Multiset Tm × ℕ} (step : VStep defs s s')
    (good : ∀ r ∈ s.1, Good r) {u : ℕ} (made : cite u ∈ s'.1) (fresh : cite u ∉ s.1) :
    ver u ∈ s.1 ∧ ∃ t F n θ j, s.1 = thread t ::ₘ ver u ::ₘ F ∧
      IsMGU [(((defs u).get j).lhs.at n, t)] θ := by
  cases step with
  | call u' j t F n θ mgu =>
      simp only [Multiset.mem_cons] at made
      rcases made with h | h | h | h
      · exact absurd h (cite_ne_thread u _)
      · obtain rfl := cite_inj h
        exact ⟨by simp, t, F, n, θ, j, rfl, mgu⟩
      · exact absurd h (cite_ne_ver u u')
      · obtain ⟨r₀, r₀In, hr₀⟩ := Multiset.mem_map.mp h
        have := cite_of_apply (good r₀ (by simp [r₀In])) hr₀
        subst this
        exact (fresh (by simp [r₀In])).elim
  | redefine u₀ u' t F n θ mgu =>
      simp only [Multiset.mem_cons] at made
      rcases made with h | h | h
      · exact absurd h (cite_ne_thread u _)
      · exact absurd h (cite_ne_ver u u')
      · obtain ⟨r₀, r₀In, hr₀⟩ := Multiset.mem_map.mp h
        have := cite_of_apply (good r₀ (by simp [r₀In])) hr₀
        subst this
        exact (fresh (by simp [r₀In])).elim

/-- **No rule removes a citation.** -/
theorem citations_persist {defs : ℕ → Program} {s s' : Multiset Tm × ℕ} (step : VStep defs s s')
    {u : ℕ} (inW : cite u ∈ s.1) : cite u ∈ s'.1 := by
  cases step with
  | call u' j t F n θ mgu =>
      simp only [Multiset.mem_cons] at inW ⊢
      rcases inW with h | h | h
      · exact absurd h (cite_ne_thread u _)
      · exact absurd h (cite_ne_ver u u')
      · exact .inr (.inr (.inr (Multiset.mem_map.mpr ⟨cite u, h, ground_fixed θ 42 u⟩)))
  | redefine u₀ u' t F n θ mgu =>
      simp only [Multiset.mem_cons] at inW ⊢
      rcases inW with h | h | h
      · exact absurd h (cite_ne_thread u _)
      · exact absurd h (cite_ne_ver u u₀)
      · exact .inr (.inr (Multiset.mem_map.mpr ⟨cite u, h, ground_fixed θ 42 u⟩))

/-! ## What stays valid -/

/-- **Adding equations at the end keeps every old answer, in order, and appends exactly the new
equations' answers.** -/
theorem answers_append (prog extra : Program) (n : ℕ) (t : Tm) (F : Multiset Tm) :
    answers (prog ++ extra) n t F = answers prog n t F ++ answers extra n t F := by
  unfold answers
  exact List.filterMap_append

/-- **Removing an equation removes exactly its answers.** -/
theorem answers_remove (before after : Program) (e : Equation) (n : ℕ) (t : Tm) (F : Multiset Tm) :
    answers (before ++ e :: after) n t F = answers before n t F ++ answers [e] n t F ++ answers after n t F := by
  rw [answers_append, show e :: after = [e] ++ after from rfl, answers_append, List.append_assoc]

/-- **A call step transports to every version containing its equation**, citing the new version. -/
theorem call_transports {defs : ℕ → Program} {u u' : ℕ} {j : Fin (defs u).length}
    {j' : Fin (defs u').length} (same : (defs u').get j' = (defs u).get j) {t : Tm} {F : Multiset Tm}
    {n : ℕ} {θ : Subst rows} (mgu : IsMGU [(((defs u).get j).lhs.at n, t)] θ) :
    VStep defs (thread t ::ₘ ver u' ::ₘ F, n)
      (thread (θ.applyTerm (((defs u).get j).rhs.at n)) ::ₘ cite u' ::ₘ ver u' ::ₘ F.map θ.applyTerm,
        n + 1) := by
  have step := VStep.call (defs := defs) u' j' t F n θ (by rw [same]; exact mgu)
  rwa [same] at step

/-! ## Controls -/

/-- Version `1`: `(= (f $x) (one $x))`. Version `2` adds `(= (f $x) (two $x))`. Version `3` removes
the first equation. -/
def versions : ℕ → Program
  | 1 => [xEq 50 63]
  | 2 => [xEq 50 63, xEq 50 64]
  | 3 => [xEq 50 64]
  | _ => []

/-- **Control: the exact answer multiset does not transport when an equation is added.** -/
theorem added_changes_answers :
    answers (versions 1) 1 (tagged 50 ka) 0 = [{thread (tagged 63 ka)}] ∧
      answers (versions 2) 1 (tagged 50 ka) 0 = [{thread (tagged 63 ka)}, {thread (tagged 64 ka)}] ∧
      answers (versions 2) 1 (tagged 50 ka) 0 =
        answers (versions 1) 1 (tagged 50 ka) 0 ++ [{thread (tagged 64 ka)}] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show versions 1 = [xEq 50 63] from rfl, ka, answers_xEq (ground_const 60), answers_nil]
  · rw [show versions 2 = [xEq 50 63, xEq 50 64] from rfl, ka, answers_xEq (ground_const 60),
      answers_xEq (ground_const 60), answers_nil]
  · rw [show versions 2 = [xEq 50 63, xEq 50 64] from rfl, show versions 1 = [xEq 50 63] from rfl, ka,
      answers_xEq (ground_const 60), answers_xEq (ground_const 60), answers_xEq (ground_const 60),
      answers_nil]
    rfl

/-- **Control: an answer is lost when its equation is removed.** -/
theorem removed_loses_answer :
    {thread (tagged 63 ka)} ∈ answers (versions 2) 1 (tagged 50 ka) 0 ∧
      answers (versions 3) 1 (tagged 50 ka) 0 = [{thread (tagged 64 ka)}] ∧
      ({thread (tagged 63 ka)} : Multiset Tm) ≠ {thread (tagged 64 ka)} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show versions 2 = [xEq 50 63, xEq 50 64] from rfl, ka, answers_xEq (ground_const 60)]
    exact List.mem_cons_self
  · rw [show versions 3 = [xEq 50 64] from rfl, ka, answers_xEq (ground_const 60), answers_nil]
  · intro h
    have := Multiset.singleton_inj.mp h
    simp [thread, tagged_inj] at this

/-- **The recheck of a call's citation**: the equation the call used belongs to the cited
version. -/
def Recheck (defs : ℕ → Program) (e : Equation) (u : ℕ) : Prop := e ∈ defs u

/-- **Control: the recheck passes against a version containing the equation, and fails against a
version without it.** -/
theorem recheck_control :
    Recheck versions (xEq 50 63) 1 ∧ Recheck versions (xEq 50 63) 2 ∧ ¬ Recheck versions (xEq 50 63) 3 := by
  refine ⟨List.mem_singleton_self _, List.mem_cons_self, ?_⟩
  intro h
  rw [Recheck, show versions 3 = [xEq 50 64] from rfl, List.mem_singleton] at h
  have := congrArg Equation.rhs h
  simp [xEq, ptag] at this

theorem apply_thread (σ : Subst rows) (t : Tm) : σ.applyTerm (thread t) = thread (σ.applyTerm t) :=
  apply_tagged σ 40 t

/-- The call `(f a)` and a redefinition to version `2`, under version `1`. -/
def startRows : Multiset Tm := (([thread (tagged 50 ka), ver 1, thread (redefTo 2)] : List Tm) : Multiset Tm)

/-- **The call before the redefinition** reads version `1`, answers `one` and cites version `1`. -/
theorem call_before_redefinition :
    VStep versions (startRows, 1)
      ((([thread (tagged 63 ka), cite 1, ver 1, thread (redefTo 2)] : List Tm) : Multiset Tm), 2) := by
  obtain ⟨θ, mgu⟩ := exists_isMGU ⟨_, xEq_unifies 50 1 ka (ground_const 60)⟩
  have bound : θ (1, 0) = ka := xEq_forced (f := 50) (ground_const 60) mgu.unifies
  have step := VStep.call (defs := versions) 1 ⟨0, by decide⟩ (tagged 50 ka)
    (([thread (redefTo 2)] : List Tm) : Multiset Tm) 1 θ mgu
  have target : thread (θ.applyTerm (((versions 1).get ⟨0, by decide⟩).rhs.at 1)) ::ₘ cite 1 ::ₘ ver 1 ::ₘ
      ((([thread (redefTo 2)] : List Tm) : Multiset Tm)).map θ.applyTerm =
      (([thread (tagged 63 ka), cite 1, ver 1, thread (redefTo 2)] : List Tm) : Multiset Tm) := by
    show thread (θ.applyTerm ((ptag 63 (.var 0)).at 1)) ::ₘ cite 1 ::ₘ ver 1 ::ₘ
      ((([thread (redefTo 2)] : List Tm) : Multiset Tm)).map θ.applyTerm = _
    rw [ptag_at, apply_tagged, Multiset.map_coe, List.map_singleton, apply_thread, redefTo, ground_fixed]
    change thread (tagged 63 (θ (1, 0))) ::ₘ cite 1 ::ₘ ver 1 ::ₘ
      (([thread (tagged 43 (.const 2))] : List Tm) : Multiset Tm) = _
    rw [bound]
    rfl
  rw [target] at step
  exact step

/-- **The call after the redefinition** reads version `2` and cites it; it may answer `two`, which
version `1` never gives. -/
theorem call_after_redefinition :
    Relation.ReflTransGen (VStep versions) (startRows, 1)
      ((([thread (tagged 64 ka), cite 2, ver 2, thread done] : List Tm) : Multiset Tm), 3) := by
  obtain ⟨θ₁, mgu₁⟩ := exists_isMGU (P := [(redefTo 2, redefTo 2)]) ⟨Subst.id rows, fun e h => by
    rw [List.mem_singleton] at h
    rw [h]⟩
  have first := VStep.redefine (defs := versions) 1 2 (redefTo 2)
    (([thread (tagged 50 ka)] : List Tm) : Multiset Tm) 1 θ₁ mgu₁
  have reorder : thread (redefTo 2) ::ₘ ver 1 ::ₘ (([thread (tagged 50 ka)] : List Tm) : Multiset Tm) =
      startRows := Multiset.coe_reverse [thread (tagged 50 ka), ver 1, thread (redefTo 2)]
  have middle : thread done ::ₘ ver 2 ::ₘ
      ((([thread (tagged 50 ka)] : List Tm) : Multiset Tm)).map θ₁.applyTerm =
      thread (tagged 50 ka) ::ₘ ver 2 ::ₘ (([thread done] : List Tm) : Multiset Tm) := by
    rw [Multiset.map_coe, List.map_singleton, apply_thread, ka, ground_fixed]
    exact Multiset.coe_reverse [thread (tagged 50 (.const 60)), ver 2, thread done]
  rw [reorder, middle] at first
  obtain ⟨θ₂, mgu₂⟩ := exists_isMGU ⟨_, xEq_unifies 50 2 ka (ground_const 60)⟩
  have bound : θ₂ (2, 0) = ka := xEq_forced (f := 50) (ground_const 60) mgu₂.unifies
  have second := VStep.call (defs := versions) 2 ⟨1, by decide⟩ (tagged 50 ka)
    (([thread done] : List Tm) : Multiset Tm) 2 θ₂ mgu₂
  have target : thread (θ₂.applyTerm (((versions 2).get ⟨1, by decide⟩).rhs.at 2)) ::ₘ cite 2 ::ₘ
      ver 2 ::ₘ ((([thread done] : List Tm) : Multiset Tm)).map θ₂.applyTerm =
      (([thread (tagged 64 ka), cite 2, ver 2, thread done] : List Tm) : Multiset Tm) := by
    show thread (θ₂.applyTerm ((ptag 64 (.var 0)).at 2)) ::ₘ cite 2 ::ₘ ver 2 ::ₘ
      ((([thread done] : List Tm) : Multiset Tm)).map θ₂.applyTerm = _
    rw [ptag_at, apply_tagged, Multiset.map_coe, List.map_singleton, apply_thread]
    change thread (tagged 64 (θ₂ (2, 0))) ::ₘ cite 2 ::ₘ ver 2 ::ₘ
      (([thread done] : List Tm) : Multiset Tm) = _
    rw [bound]
    rfl
  rw [target] at second
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single first) second

#print axioms vstep_iff
#print axioms vstep_good
#print axioms vruns_iff
#print axioms vexecution
#print axioms citation_reads_version
#print axioms citations_persist
#print axioms answers_append
#print axioms answers_remove
#print axioms call_transports
#print axioms added_changes_answers
#print axioms removed_loses_answer
#print axioms recheck_control
#print axioms call_before_redefinition
#print axioms call_after_redefinition

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions
