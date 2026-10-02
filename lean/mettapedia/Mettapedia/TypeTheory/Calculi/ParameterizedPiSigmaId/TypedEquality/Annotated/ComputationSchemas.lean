import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Schemas
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DecoderComputation

/-!
# The declared computations as rewrite schemas

Each kind of declared computation is presented by a family of rewrite schemas
(`Presents`): its steps are exactly the instances of the schemas.

* A definition by one equation, `definitionComputation f Θ rhs`: the one schema
  `f x₁ ⋯ x_k ⟶ rhs` over the telescope's variables.
* The identity eliminator's linear rule, `eliminatorComputation J`: the one schema
  `J a₀ a₁ a₂ a₃ a₄ (refl a₅) ⟶ a₃`.
* A recursor, `iotaComputation rec ctors`: one schema per constructor,
  `rec P m₁ ⋯ m_c (kᵢ a₁ ⋯ aₐ) ⟶ mᵢ a₁ ⋯ aₐ (rec P m₁ ⋯ m_c aⱼ) ⋯`, over the motive,
  the methods and the fields.
* A definition by structural recursion, `recursionComputation f ctors e s d body`:
  one schema per constructor, its left side the application of `f` to the
  pattern of the constructor (`patternSub`), its right side the constructor's
  right-hand side with the recursive calls substituted (`hypSub`).
* The decoder of proposition codes, `decoderComputation D`: one schema for
  implication, and one per quantifier and equation instance.

Every left side of these schemas is first-order; for a given package they are
checked left-linear by evaluation. The schemas are read off the computations'
own data: nothing is restated per constant.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open AlgebraicSchema (SchemaFamily SchemaStep LeftLinear variableMultiplicity)
open Normalization
open TelescopeAbstraction (applyClosed applyClosed_subst)

variable {Head : Type}

/-- A schema as a dependent pair: its number of metavariables, its left and its
right side. -/
abbrev Schema (Head : Type) := Σ arity : Nat, Tm Head arity × Tm Head arity

/-! ## Definitions by one equation -/

/-- The schema of a definition by one equation. -/
def definitionSchema (f : DeclName) {k : Nat} (Θ : Ctx Head k) (rhs : Tm Head k) :
    SchemaFamily Head :=
  fun {arity} L R => (⟨arity, (L, R)⟩ : Schema Head) = ⟨k, (applyClosed Θ ids (.const f), rhs)⟩

theorem subst_applyClosed_ids {k n : Nat} (Θ : Ctx Head k) (σ : Sub Head k n) (f : DeclName) :
    Presentation.subst σ (applyClosed Θ ids (.const f)) = applyClosed Θ σ (.const f) := by
  rw [applyClosed_subst]
  rfl

theorem definition_presents (f : DeclName) {k : Nat} (Θ : Ctx Head k) (rhs : Tm Head k) :
    Presents (definitionComputation f Θ rhs) (definitionSchema f Θ rhs) := by
  intro n l r
  constructor
  · rintro ⟨σ, rfl, rfl⟩
    have step := SchemaStep.instantiate (schema := definitionSchema f Θ rhs)
      (left := applyClosed Θ ids (.const f)) (right := rhs) rfl σ
    rwa [subst_applyClosed_ids] at step
  · intro step
    cases step with
    | instantiate rule τ =>
        cases rule
        exact ⟨τ, subst_applyClosed_ids Θ τ f, rfl⟩

/-! ## The identity eliminator -/

/-- The left side of the eliminator's rule, over six metavariables. -/
def eliminatorLeft (J : DeclName) : Tm Head 6 :=
  appSpine (.const J) [.var 5, .var 4, .var 3, .var 2, .var 1, .refl (.var 0)]

/-- The schema of the identity eliminator's linear rule. -/
def eliminatorSchema (J : DeclName) : SchemaFamily Head :=
  fun {arity} L R => (⟨arity, (L, R)⟩ : Schema Head) = ⟨6, (eliminatorLeft J, .var 2)⟩

theorem eliminator_presents (J : DeclName) :
    Presents (eliminatorComputation (Head := Head) J) (eliminatorSchema J) := by
  intro n l r
  constructor
  · rintro ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩
    have step := SchemaStep.instantiate (schema := eliminatorSchema J)
      (left := eliminatorLeft J) (right := .var 2) rfl ![a₅, a₄, r, a₂, a₁, a₀]
    simpa [eliminatorLeft, subst_appSpine, Presentation.subst] using step
  · intro step
    cases step with
    | instantiate rule τ =>
        cases rule
        exact ⟨τ 5, τ 4, τ 3, τ 2, τ 1, τ 0, by simp [eliminatorLeft, Presentation.subst], rfl⟩

/-! ## The decoder of proposition codes -/

/-- The schemas of the decoder: implication, and every quantifier and equation
instance. -/
def decoderSchema (D : Decoders Head) : SchemaFamily Head :=
  fun {arity} L R =>
    (⟨arity, (L, R)⟩ : Schema Head) =
        ⟨2, (.app (.const D.holds) (.app (.app (.const D.imp) (.var 1)) (.var 0)),
          .pi (.app (.const D.holds) (.var 1))
            (.app (.const D.holds) (Presentation.rename wk (.var 0))))⟩ ∨
    (∃ a A, D.allCarrier a = some A ∧
      (⟨arity, (L, R)⟩ : Schema Head) =
        ⟨1, (.app (.const D.holds) (.app (.const a) (.var 0)),
          .pi (liftClosed A)
            (.app (.const D.holds) (.app (Presentation.rename wk (.var 0)) (.var 0))))⟩) ∨
    (∃ e A, D.eqCarrier e = some A ∧
      (⟨arity, (L, R)⟩ : Schema Head) =
        ⟨2, (.app (.const D.holds) (.app (.app (.const e) (.var 1)) (.var 0)),
          .id (liftClosed A) (.var 1) (.var 0))⟩)

theorem decoder_presents (D : Decoders Head) :
    Presents (decoderComputation D) (decoderSchema D) := by
  intro n l r
  constructor
  · intro step
    cases step with
    | imp p q =>
        exact SchemaStep.instantiate (schema := decoderSchema D) (.inl rfl) ![q, p]
    | all carrier f =>
        have step := SchemaStep.instantiate (schema := decoderSchema D)
          (.inr (.inl ⟨_, _, carrier, rfl⟩)) ![f]
        simp only [Presentation.subst, subst_liftSub_wk, subst_liftClosed, liftSub_zero,
          Matrix.cons_val_zero] at step
        exact step
    | eq carrier x y =>
        have step := SchemaStep.instantiate (schema := decoderSchema D)
          (.inr (.inr ⟨_, _, carrier, rfl⟩)) ![y, x]
        simp only [Presentation.subst, subst_liftClosed] at step
        exact step
  · intro step
    cases step with
    | instantiate rule τ =>
        rcases rule with rule | ⟨a, A, carrier, rule⟩ | ⟨e, A, carrier, rule⟩
        · cases rule
          exact DecoderStep.imp (τ 1) (τ 0)
        · cases rule
          have decoded := DecoderStep.all carrier (τ 0)
          show DecoderStep D _ _
          simp only [Presentation.subst, subst_liftSub_wk, subst_liftClosed, liftSub_zero]
          exact decoded
        · cases rule
          have decoded := DecoderStep.eq carrier (τ 1) (τ 0)
          show DecoderStep D _ _
          simp only [Presentation.subst, subst_liftClosed]
          exact decoded

theorem decoder_firstOrder (D : Decoders Head) : FirstOrderFamily (decoderSchema D) := by
  intro k L R rule
  rcases rule with rule | ⟨a, A, _, rule⟩ | ⟨e, A, _, rule⟩ <;> cases rule
  · refine ⟨rfl, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [variableMultiplicity]
    · refine Fin.cases ?_ (fun j' => j'.elim0) j
      simp [variableMultiplicity]
  · refine ⟨rfl, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => j.elim0) i
    simp [variableMultiplicity]
  · refine ⟨rfl, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [variableMultiplicity]
    · refine Fin.cases ?_ (fun j' => j'.elim0) j
      simp [variableMultiplicity]

/-! ## Definitions by structural recursion -/

/-- The pattern's scrutinee is its constructor applied to its fields. -/
theorem replaceScrut_pattern (s a : Nat) (k : DeclName) (d : Nat) :
    replaceScrut s (appSpine (.const k) (patternFields (Head := Head) s a d)) d
      (patternSub s a d k) = patternSub s a d k := by
  funext ι
  have h := subst_matchSub_patternSub (Head := Head) (m := s + a + d) (s := s) (a := a) k
    (patternFields s a d) (length_patternFields s a d) d (patternSub s a d k) ι
  rw [matchSub_pattern s a k d, subst_ids] at h
  exact h.symm

/-- The schemas of a definition by structural recursion: for each constructor,
`f` applied to its pattern rewrites to its right-hand side with the recursive
calls substituted. -/
def recursionSchema (f : DeclName) (ctors : List (DeclName × List (Field Head)))
    (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) :
    SchemaFamily Head :=
  fun {arity} L R => ∃ k fields, (k, fields) ∈ ctors ∧
    (⟨arity, (L, R)⟩ : Schema Head) =
      ⟨s + fields.length + d,
        (applyClosed (ofEntries e (s + 1 + d)) (patternSub s fields.length d k) (.const f),
          Presentation.subst (hypSub f e s d fields) (body k fields))⟩

theorem recursion_presents (f : DeclName) (ctors : List (DeclName × List (Field Head)))
    (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) :
    Presents (recursionComputation f ctors e s d body) (recursionSchema f ctors e s d body) := by
  intro n l r
  constructor
  · rintro ⟨k, fields, σ, as, mem, has, rfl, rfl⟩
    have step := SchemaStep.instantiate (schema := recursionSchema f ctors e s d body)
      ⟨k, fields, mem, rfl⟩ (matchSub s fields.length as d σ)
    have hl : Presentation.subst (matchSub s fields.length as d σ)
        (applyClosed (ofEntries e (s + 1 + d)) (patternSub s fields.length d k) (.const f)) =
        applyClosed (ofEntries e (s + 1 + d)) (replaceScrut s (appSpine (.const k) as) d σ)
          (.const f) := by
      rw [applyClosed_subst]
      congr 1
      funext ι
      exact subst_matchSub_patternSub k as has d σ ι
    rw [hl] at step
    exact step
  · intro step
    cases step with
    | instantiate rule τ =>
        obtain ⟨k, fields, mem, rule⟩ := rule
        cases rule
        have base : RecursionStep f ctors e s d body
            (applyClosed (ofEntries e (s + 1 + d)) (patternSub s fields.length d k) (.const f))
            (Presentation.subst (hypSub f e s d fields) (body k fields)) :=
          ⟨k, fields, patternSub s fields.length d k, patternFields s fields.length d, mem,
            length_patternFields s fields.length d,
            by rw [replaceScrut_pattern], by rw [matchSub_pattern, subst_ids]⟩
        exact base.substitute τ

/-! ## Recursors -/

/-- The metavariables of a schema over `N` of them, the oldest first. -/
def metaVars (N : Nat) : List (Tm Head N) := (List.finRange N).reverse.map Tm.var

theorem length_metaVars (N : Nat) : (metaVars (Head := Head) N).length = N := by
  simp [metaVars]

/-- The substitution sending the metavariables, oldest first, to the listed terms. -/
def listSub {n : Nat} (N : Nat) (ts : List (Tm Head n)) : Sub Head N n :=
  fun i => ts.getD (N - 1 - i.val) defaultTm

theorem map_listSub_metaVars {n N : Nat} (ts : List (Tm Head n)) (h : ts.length = N) :
    (metaVars N).map (Presentation.subst (listSub N ts)) = ts := by
  apply List.ext_getElem
  · simp [length_metaVars, h]
  · intro j h₁ h₂
    simp only [metaVars, List.map_map, List.getElem_map, Function.comp_apply, Presentation.subst,
      List.getElem_reverse, List.getElem_finRange, listSub, List.length_finRange]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [Fin.cast_mk]; omega)]
    simp only [Option.getD_some, Fin.cast_mk]
    congr 1
    omega

/-- The left side of a computation rule of a recursor, over the motive, the `c`
methods and the `a` fields of constructor `k`. -/
def iotaLeft (rec k : DeclName) (c a : Nat) : Tm Head (1 + c + a) :=
  recApp rec ((metaVars (1 + c + a)).take (1 + c))
    (appSpine (.const k) ((metaVars (1 + c + a)).drop (1 + c)))

/-- The right side of the computation rule for the constructor at index `i`. -/
def iotaRight (rec : DeclName) (c i : Nat) (fields : List (Field Head)) :
    Tm Head (1 + c + fields.length) :=
  appSpine (((metaVars (1 + c + fields.length)).take (1 + c)).getD (1 + i) defaultTm)
    ((metaVars (1 + c + fields.length)).drop (1 + c) ++
      (recArgs fields ((metaVars (1 + c + fields.length)).drop (1 + c))).map
        (recApp rec ((metaVars (1 + c + fields.length)).take (1 + c))))

/-- The schemas of a recursor: one computation rule per constructor. -/
def iotaSchema (rec : DeclName) (ctors : List (DeclName × List (Field Head))) :
    SchemaFamily Head :=
  fun {arity} L R => ∃ i k fields, ctors[i]? = some (k, fields) ∧
    (⟨arity, (L, R)⟩ : Schema Head) =
      ⟨1 + ctors.length + fields.length,
        (iotaLeft rec k ctors.length fields.length, iotaRight rec ctors.length i fields)⟩

theorem getD_map_subst {n m : Nat} (σ : Sub Head n m) (ts : List (Tm Head n)) (j : Nat) :
    (ts.map (Presentation.subst σ)).getD j defaultTm =
      Presentation.subst σ (ts.getD j defaultTm) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ts[j]? <;> rfl

theorem subst_iotaLeft {n : Nat} (rec k : DeclName) (c a : Nat) (τ : Sub Head (1 + c + a) n) :
    Presentation.subst τ (iotaLeft rec k c a) =
      recApp rec (((metaVars (1 + c + a)).map (Presentation.subst τ)).take (1 + c))
        (appSpine (.const k) (((metaVars (1 + c + a)).map (Presentation.subst τ)).drop (1 + c))) := by
  simp only [iotaLeft, subst_recApp, subst_appSpine, List.map_take, List.map_drop]
  rfl

theorem subst_iotaRight {n : Nat} (rec : DeclName) (c i : Nat) (fields : List (Field Head))
    (τ : Sub Head (1 + c + fields.length) n) :
    Presentation.subst τ (iotaRight rec c i fields) =
      appSpine ((((metaVars (1 + c + fields.length)).map (Presentation.subst τ)).take (1 + c)).getD
          (1 + i) defaultTm)
        (((metaVars (1 + c + fields.length)).map (Presentation.subst τ)).drop (1 + c) ++
          (recArgs fields (((metaVars (1 + c + fields.length)).map
              (Presentation.subst τ)).drop (1 + c))).map
            (recApp rec (((metaVars (1 + c + fields.length)).map
              (Presentation.subst τ)).take (1 + c)))) := by
  simp only [iotaRight, subst_appSpine, List.map_append, List.map_map, List.map_take,
    List.map_drop, ← getD_map_subst]
  congr 2
  rw [← List.map_drop, ← map_recArgs, List.map_map]
  congr 1
  funext t
  simp only [Function.comp_apply, subst_recApp, List.map_take]

theorem iota_presents (rec : DeclName) (ctors : List (DeclName × List (Field Head))) :
    Presents (iotaComputation rec ctors) (iotaSchema rec ctors) := by
  intro n l r
  constructor
  · rintro ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩
    have hts : (p :: ms ++ args).length = 1 + ctors.length + fields.length := by
      simp [hms, has]
      omega
    have key := map_listSub_metaVars (p :: ms ++ args) hts
    have step := SchemaStep.instantiate (schema := iotaSchema rec ctors) ⟨i, k, fields, hi, rfl⟩
      (listSub (1 + ctors.length + fields.length) (p :: ms ++ args))
    have htake : (p :: ms ++ args).take (1 + ctors.length) = p :: ms := by
      rw [List.cons_append, Nat.add_comm, List.take_succ_cons, List.take_left' hms]
    have hdrop : (p :: ms ++ args).drop (1 + ctors.length) = args := by
      rw [List.cons_append, Nat.add_comm, List.drop_succ_cons, List.drop_left' hms]
    rw [subst_iotaLeft, subst_iotaRight, key, htake, hdrop] at step
    have hget : (p :: ms).getD (1 + i) defaultTm = m := by
      rw [Nat.add_comm, List.getD_cons_succ, List.getD_eq_getElem?_getD, hm]
      rfl
    rwa [hget] at step
  · intro step
    cases step with
    | instantiate rule τ =>
        obtain ⟨i, k, fields, hi, rule⟩ := rule
        cases rule
        rw [subst_iotaLeft, subst_iotaRight]
        generalize hts : (metaVars (1 + ctors.length + fields.length)).map
          (Presentation.subst τ) = ts
        have hlen : ts.length = 1 + ctors.length + fields.length := by
          rw [← hts, List.length_map, length_metaVars]
        obtain ⟨p, rest, rfl⟩ : ∃ p rest, ts = p :: rest := by
          cases ts with
          | nil => exact absurd hlen (by simp; omega)
          | cons p rest => exact ⟨p, rest, rfl⟩
        have hrest : rest.length = ctors.length + fields.length := by
          simp at hlen
          omega
        have hic : i < ctors.length := (List.getElem?_eq_some_iff.mp hi).1
        refine ⟨p, rest.take ctors.length, i, k, fields, rest.drop ctors.length,
          (rest.take ctors.length).getD i defaultTm, by simp [hrest], hi, by simp [hrest],
          ?_, ?_, ?_⟩
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hrest]; omega)]
          rfl
        · rw [Nat.add_comm, List.take_succ_cons, List.drop_succ_cons]
        · rw [Nat.add_comm 1 ctors.length, List.take_succ_cons, List.drop_succ_cons,
            show 1 + i = i + 1 from Nat.add_comm 1 i, List.getD_cons_succ]

/-! ## Declared computations -/

/-- A declared computation, by kind, with the data that determines it. -/
inductive DeclaredComputation (Head : Type) where
  | definition (f : DeclName) {k : Nat} (Θ : Ctx Head k) (rhs : Tm Head k)
  | eliminator (J : DeclName)
  | iota (rec : DeclName) (ctors : List (DeclName × List (Field Head)))
  | recursion (f : DeclName) (ctors : List (DeclName × List (Field Head)))
      (e : (i : Nat) → Tm Head i) (s d : Nat)
      (body : (k : DeclName) → (fields : List (Field Head)) →
        Tm Head (s + fields.length + d + (recPositions fields).length))

namespace DeclaredComputation

/-- The root computation of a declared computation. -/
def computation : DeclaredComputation Head → RootComputation Head
  | definition f Θ rhs => definitionComputation f Θ rhs
  | eliminator J => eliminatorComputation J
  | iota rec ctors => iotaComputation rec ctors
  | recursion f ctors e s d body => recursionComputation f ctors e s d body

/-- The rewrite schemas of a declared computation. -/
def schemas : DeclaredComputation Head → SchemaFamily Head
  | definition f Θ rhs => definitionSchema f Θ rhs
  | eliminator J => eliminatorSchema J
  | iota rec ctors => iotaSchema rec ctors
  | recursion f ctors e s d body => recursionSchema f ctors e s d body

/-- **A declared computation is presented by its schemas.** -/
theorem presents : ∀ c : DeclaredComputation Head, Presents c.computation c.schemas
  | definition f Θ rhs => definition_presents f Θ rhs
  | eliminator J => eliminator_presents J
  | iota rec ctors => iota_presents rec ctors
  | recursion f ctors e s d body => recursion_presents f ctors e s d body

/-- The left sides of the schemas of a declared computation. -/
def leftSides : DeclaredComputation Head → List (Σ k : Nat, Tm Head k)
  | definition f (k := k) Θ _ => [⟨k, applyClosed Θ ids (.const f)⟩]
  | eliminator J => [⟨6, eliminatorLeft J⟩]
  | iota rec ctors => ctors.map fun kf =>
      ⟨1 + ctors.length + kf.2.length, iotaLeft rec kf.1 ctors.length kf.2.length⟩
  | recursion f ctors e s d _ => ctors.map fun kf =>
      ⟨s + kf.2.length + d,
        applyClosed (ofEntries e (s + 1 + d)) (patternSub s kf.2.length d kf.1) (.const f)⟩

/-- Whether the left sides of a declared computation are first-order and
left-linear, by evaluation. -/
def check (c : DeclaredComputation Head) : Bool :=
  c.leftSides.all fun L => firstOrderLinear L.2

theorem mem_leftSides_firstOrder {c : DeclaredComputation Head} (h : c.check = true) {k : Nat}
    {L : Tm Head k} (mem : (⟨k, L⟩ : Σ k : Nat, Tm Head k) ∈ c.leftSides) :
    firstOrder L = true ∧ LeftLinear L := by
  simp only [check, List.all_eq_true] at h
  exact firstOrderLinear_spec (h _ mem)

/-- **The left sides of a declared computation are first-order and left-linear**
when its check evaluates to `true`. -/
theorem firstOrder_of_check (c : DeclaredComputation Head) (h : c.check = true) :
    FirstOrderFamily c.schemas := by
  intro k L R rule
  cases c with
  | definition f Θ rhs =>
      cases rule
      exact mem_leftSides_firstOrder h (List.mem_singleton_self _)
  | eliminator J =>
      cases rule
      exact mem_leftSides_firstOrder h (List.mem_singleton_self _)
  | iota rec ctors =>
      obtain ⟨i, k', fields, hi, rule⟩ := rule
      cases rule
      exact mem_leftSides_firstOrder h
        (List.mem_map.mpr ⟨(k', fields), List.mem_of_getElem? hi, rfl⟩)
  | recursion f ctors e s d body =>
      obtain ⟨k', fields, mem, rule⟩ := rule
      cases rule
      exact mem_leftSides_firstOrder h (List.mem_map.mpr ⟨(k', fields), mem, rfl⟩)

/-- The union of listed declared computations is presented by the union of their
schemas. -/
theorem presents_unionAll :
    ∀ specs : List (DeclName × DeclaredComputation Head),
      Presents (RootComputation.unionAll (specs.map fun p => (p.1, p.2.computation)))
        (schemaUnionAll (specs.map fun p => (p.1, p.2.schemas)))
  | [] => Presents.empty
  | p :: rest => Presents.union p.2.presents (presents_unionAll rest)

/-- A schema of a listed declared computation is a schema of their union. -/
theorem schemaUnionAll_of_mem {p : DeclName × DeclaredComputation Head} {k : Nat}
    {L R : Tm Head k} (rule : p.2.schemas L R) :
    ∀ {specs : List (DeclName × DeclaredComputation Head)}, p ∈ specs →
      schemaUnionAll (specs.map fun p => (p.1, p.2.schemas)) L R
  | [], mem => absurd mem List.not_mem_nil
  | q :: rest, mem => by
      rcases List.mem_cons.mp mem with rfl | mem'
      · exact Or.inl rule
      · exact Or.inr (schemaUnionAll_of_mem rule mem')

/-- A schema of the union of listed declared computations is a schema of one of
them. -/
theorem mem_of_schemaUnionAll {k : Nat} {L R : Tm Head k} :
    ∀ {specs : List (DeclName × DeclaredComputation Head)},
      schemaUnionAll (specs.map fun p => (p.1, p.2.schemas)) L R →
        ∃ p ∈ specs, p.2.schemas L R
  | [], rule => rule.elim
  | q :: _, rule => by
      rcases rule with rule | rule
      · exact ⟨q, List.mem_cons_self .., rule⟩
      · obtain ⟨p, mem, rule⟩ := mem_of_schemaUnionAll rule
        exact ⟨p, List.mem_cons_of_mem _ mem, rule⟩

theorem firstOrder_unionAll (specs : List (DeclName × DeclaredComputation Head))
    (h : (specs.all fun p => p.2.check) = true) :
    FirstOrderFamily (schemaUnionAll (specs.map fun p => (p.1, p.2.schemas))) := by
  apply FirstOrderFamily.unionAll
  intro s mem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp mem
  simp only [List.all_eq_true] at h
  exact p.2.firstOrder_of_check (h p hp)

end DeclaredComputation

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
