import Mettapedia.GSLT.Equations.Atomic

/-! # Open atomic matching with raw witnesses

The first visit to a variable binds the stored subterm, not its printed
representative. Subsequent visits compare at the quotient and do not replace
that binding. The mathematical procedure accepts every atomic match and
does not enumerate alternative spellings or backtrack over witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.Atomic

open Contracts.ScopedAliasSections (GTerm)

variable {S C V : Type*}

def same [DecidableEq C] (f : S → C) : GTerm S → GTerm S → Bool
  | .sym a, .sym b => decide (f a = f b)
  | .app l r, .app l' r' => same f l l' && same f r r'
  | _, _ => false

theorem same_iff [DecidableEq C] (f : S → C) (s t : GTerm S) :
    same f s t = true ↔ rename f s = rename f t := by
  induction s generalizing t with
  | sym s => cases t <;> simp [same, rename]
  | app l r il ir => cases t <;> simp [same, rename, il, ir]

abbrev Bindings (V S : Type*) := V → Option (GTerm S)

section

variable [DecidableEq C] [DecidableEq V] (f : S → C)

def set (env : Bindings V S) (v : V) (row : GTerm S) : Bindings V S :=
  fun x => if x = v then some row else env x

def bind (env : Bindings V S) (v : V) (row : GTerm S) : Option (Bindings V S) :=
  match env v with
  | none => some (set env v row)
  | some old => if same f old row then some env else none

def matchFrom : Pattern S V → GTerm S → Bindings V S → Option (Bindings V S)
  | .sym (.inr v), row, env => bind f env v row
  | .sym (.inl a), .sym b, env => if f a = f b then some env else none
  | .app l r, .app l' r', env =>
      (matchFrom l l' env).bind (matchFrom r r')
  | _, _, _ => none

/-- A total quotient valuation consistent with the retained raw witnesses. -/
def Extends (env : Bindings V S) (σ : V → GTerm C) : Prop :=
  ∀ v raw, env v = some raw → σ v = rename f raw

theorem bind_iff (env : Bindings V S) (v : V) (row : GTerm S) (σ : V → GTerm C) :
    (∃ result, bind f env v row = some result ∧ Extends f result σ) ↔
      Extends f env σ ∧ σ v = rename f row := by
  cases h : env v with
  | none =>
    simp only [bind, h, Option.some.injEq, exists_eq_left']
    constructor
    · intro newer
      refine ⟨?_, newer v row (by simp [set])⟩
      intro w t old
      have ne : w ≠ v := by rintro rfl; simp [h] at old
      exact newer w t (by simpa [set, ne] using old)
    · rintro ⟨older, current⟩ w t entry
      by_cases eq : w = v
      · subst w
        have : row = t := by simpa [set] using entry
        simpa only [this] using current
      · exact older w t (by simpa [set, eq] using entry)
  | some old =>
    by_cases equal : same f old row = true
    · simp only [bind, h, equal, if_true, Option.some.injEq, exists_eq_left']
      exact ⟨fun ok => ⟨ok, (ok v old h).trans ((same_iff ..).1 equal)⟩, And.left⟩
    · have fail : bind f env v row = none := by simp [bind, h, equal]
      constructor
      · rintro ⟨result, computed, _⟩
        simp [fail] at computed
      · rintro ⟨ok, eq⟩
        exact False.elim (equal ((same_iff ..).2 ((ok v old h).symm.trans eq)))

/-- A computed match extends exactly the pre-existing compatible valuations
that make the keyed pattern equal to the keyed row. -/
theorem matchFrom_iff (p : Pattern S V) (row : GTerm S) (env : Bindings V S)
    (σ : V → GTerm C) :
    (∃ result, matchFrom f p row env = some result ∧ Extends f result σ) ↔
      Extends f env σ ∧ fill f σ p = rename f row := by
  induction p generalizing row env with
  | sym s =>
    cases s with
    | inl a =>
      cases row with
      | sym b => by_cases h : f a = f b <;> simp [matchFrom, fill, rename, h]
      | app _ _ => simp [matchFrom, fill, rename]
    | inr v => exact bind_iff f env v row σ
  | app l r il ir =>
    cases row with
    | sym t => simp [matchFrom, fill, rename]
    | app a b =>
      simp only [matchFrom, Option.bind_eq_some_iff, fill, rename, GTerm.app.injEq]
      constructor
      · rintro ⟨res, ⟨middle, hl, hr⟩, ok⟩
        obtain ⟨extendsMiddle, right⟩ := (ir b middle).1 ⟨res, hr, ok⟩
        obtain ⟨extendsEnv, left⟩ := (il a env).1 ⟨middle, hl, extendsMiddle⟩
        exact ⟨extendsEnv, left, right⟩
      · rintro ⟨extendsEnv, left, right⟩
        obtain ⟨middle, hl, ex⟩ := (il a env).2 ⟨extendsEnv, left⟩
        obtain ⟨res, hr, ok⟩ := (ir b middle).2 ⟨ex, right⟩
        exact ⟨res, ⟨middle, hl, hr⟩, ok⟩

theorem bind_keeps (env result : Bindings V S) (v : V) (row : GTerm S)
    (computed : bind f env v row = some result) :
    ∀ x t, env x = some t → result x = some t := by
  intro x t old
  cases h : env v with
  | none =>
    have ne : x ≠ v := by rintro rfl; simp [h] at old
    simp only [bind, h, Option.some.injEq] at computed
    rw [← computed]
    simp [set, ne, old]
  | some prior =>
    by_cases eq : same f prior row = true
    · simp only [bind, h, eq, if_true, Option.some.injEq] at computed
      subst result
      exact old
    · simp [bind, h, eq] at computed

theorem matchFrom_keeps (p : Pattern S V) (row : GTerm S) (env result : Bindings V S)
    (computed : matchFrom f p row env = some result) :
    ∀ x t, env x = some t → result x = some t := by
  induction p generalizing row env result with
  | sym s =>
    cases s with
    | inl a =>
      cases row with
      | sym b =>
        by_cases h : f a = f b
        · simp only [matchFrom, h, if_true, Option.some.injEq] at computed
          subst result
          exact fun _ _ old => old
        · simp [matchFrom, h] at computed
      | app _ _ => simp [matchFrom] at computed
    | inr v => exact bind_keeps f env result v row computed
  | app l r il ir =>
    cases row with
    | sym _ => simp [matchFrom] at computed
    | app a b =>
      obtain ⟨middle, hl, hr⟩ := Option.bind_eq_some_iff.mp computed
      exact fun x t old => ir b middle result hr x t (il a env middle hl x t old)

theorem accepts_iff (p : Pattern S V) (row : GTerm S) :
    (matchFrom f p row (fun _ => none)).isSome ↔
      ∃ σ : V → GTerm C, fill f σ p = rename f row := by
  constructor
  · intro h
    obtain ⟨result, resultEq⟩ := Option.isSome_iff_exists.mp h
    let σ : V → GTerm C := fun v => rename f ((result v).getD row)
    have valid : Extends f result σ := fun v raw entry => by simp [σ, entry]
    exact ⟨σ, ((matchFrom_iff f p row _ σ).1 ⟨result, resultEq, valid⟩).2⟩
  · rintro ⟨σ, exactMatch⟩
    obtain ⟨result, eq, _⟩ := (matchFrom_iff f p row (fun _ => none) σ).2
      ⟨by simp [Extends], exactMatch⟩
    exact Option.isSome_iff_exists.mpr ⟨result, eq⟩

/-- An executable match is exact for raw valuations modulo the specified
leaf relation. No surjectivity on machine class identifiers is required. -/
theorem accepts_raw_iff (rel : S → S → Prop) (key : ∀ a b, f a = f b ↔ rel a b)
    (p : Pattern S V) (row : GTerm S) :
    (matchFrom f p row (fun _ => none)).isSome ↔
      ∃ σ : V → GTerm S, (fill id σ p).EqMod rel row := by
  constructor
  · intro yes
    obtain ⟨res, computed⟩ := Option.isSome_iff_exists.mp yes
    let σ : V → GTerm S := fun v => (res v).getD row
    have agrees : Extends f res (rename f ∘ σ) := fun v t h => by simp [σ, h]
    have exactMatch := ((matchFrom_iff f p row _ (rename f ∘ σ)).1 ⟨res, computed, agrees⟩).2
    exact ⟨σ, (match_iff_keyed rel f key p σ row).mp exactMatch⟩
  · rintro ⟨σ, exactMatch⟩
    exact (accepts_iff f p row).mpr
      ⟨rename f ∘ σ, (match_iff_keyed rel f key p σ row).mpr exactMatch⟩

end

/-! ## The rigid-head access path -/

def head : GTerm S → S
  | .sym s => s
  | .app l _ => head l

def rigidHead : Pattern S V → Option S
  | .sym (.inl s) => some s
  | .sym (.inr _) => none
  | .app l _ => rigidHead l

theorem head_rename (f : S → C) (t : GTerm S) :
    head (rename f t) = f (head t) := by
  induction t with
  | sym s => rfl
  | app l r ih _ => exact ih

theorem head_fill (f : S → C) (σ : V → GTerm C) (p : Pattern S V) {s : S}
    (bound : rigidHead p = some s) : head (fill f σ p) = f s := by
  induction p with
  | sym sym =>
    cases sym with
    | inl x => simp [rigidHead] at bound; subst s; rfl
    | inr v => simp [rigidHead] at bound
  | app l r ih _ => exact ih bound

def headCandidate [DecidableEq C] (f : S → C) (p : Pattern S V) (t : GTerm S) : Bool :=
  match rigidHead p with
  | none => true
  | some s => decide (f s = f (head t))

theorem head_candidate_of_match [DecidableEq C] [DecidableEq V] (f : S → C)
    (p : Pattern S V) (t : GTerm S) (env : Bindings V S)
    (matched : matchFrom f p t (fun _ => none) = some env) :
    headCandidate f p t = true := by
  have yes : (matchFrom f p t (fun _ => none)).isSome := by rw [matched]; rfl
  obtain ⟨σ, sameKey⟩ := (accepts_iff f p t).1 yes
  cases h : rigidHead p with
  | none => simp [headCandidate, h]
  | some s =>
    have eq := congrArg head sameKey
    rw [head_fill f σ p h, head_rename] at eq
    simp [headCandidate, h, eq]

/-- Filtering by the rigid head's class is exact, including order, repeated
occurrences, and the raw bindings. A variable-head pattern imposes no such
filter. This is the combination of candidate selection and exact matching,
not a proof about a concrete index layout. -/
theorem restrict_head_exact {Row : Type*} [DecidableEq C] [DecidableEq V]
    (f : S → C) (p : Pattern S V) (value : Row → GTerm S) (rows : List Row) :
    ((rows.filter fun r => headCandidate f p (value r)).filterMap fun r =>
      (matchFrom f p (value r) (fun _ => none)).map (r, ·)) =
    rows.filterMap (fun r => (matchFrom f p (value r) (fun _ => none)).map (r, ·)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    cases h : matchFrom f p (value r) (fun _ => none) with
    | none => by_cases ok : headCandidate f p (value r) = true <;> simp [ok, h, ih]
    | some env =>
      have ok := head_candidate_of_match f p (value r) env h
      simp [ok, h, ih]

end Mettapedia.GSLT.Equations.Atomic
