import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTree

/-!
# Compiling equations to case trees

A definition by several equations is read with first-match priority: the
first equation that matches, after all earlier ones mismatch, gives the
result, and an earlier equation that can neither match nor mismatch yet
blocks every later one. Matching is three-valued, as in Norell's covering
algorithm. A pattern matches a value; it mismatches when two distinct
constructors of one family meet; and it is blocked when the value at a
constructor pattern is not yet a canonical value of the constructor's family.
Patterns are matched left to right, and the first outcome other than a match
decides.

`compile` runs the covering algorithm on a neighbourhood, one pattern per
argument, starting with a variable each. It matches the first remaining
equation against the neighbourhood filled with its own variables. A match
gives a leaf; a mismatch drops the equation; a block at a variable splits
that variable over the constructors of its family, and every branch continues
with the refined neighbourhood and the same equations. A block at anything but
a variable, a split over a type that is not inductive, a missing case, an
equation of the wrong arity, and running out of fuel give no tree.

The compiled tree evaluates exactly by first-match selection
(`compile_eval`). So it fires the first equation that matches after
mismatches (`compile_firstMatch`) and takes no step when an equation is
blocked after mismatches (`compile_blocked`). Every split lists the
constructors of an inductive type (`compile_covers`), and the tree is scoped
at the arity (`compile_scoped`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

/-! ## Constant spines and canonical values -/

/-- The constant heading a spine, with its arguments. -/
def constSpine? {n : Nat} : Tm Head n → Option (DeclName × List (Tm Head n))
  | .const c => some (c, [])
  | .app f a => (constSpine? f).map fun spine => (spine.1, spine.2 ++ [a])
  | _ => none

theorem constSpine?_appSpine {n : Nat} (c : DeclName) (args : List (Tm Head n)) :
    constSpine? (appSpine (.const c) args) = some (c, args) := by
  induction args using List.reverseRecOn with
  | nil => rfl
  | append_singleton args a ih =>
      rw [appSpine_concat]
      show (constSpine? (appSpine (.const c) args)).map _ = _
      rw [ih]
      rfl

theorem appSpine_of_constSpine? {n : Nat} :
    ∀ (t : Tm Head n) {c : DeclName} {args : List (Tm Head n)},
      constSpine? t = some (c, args) → t = appSpine (.const c) args
  | .const _, _, _, h => by
      cases h
      rfl
  | .app f a, _, _, h => by
      cases hf : constSpine? f with
      | none =>
          rw [constSpine?, hf] at h
          cases h
      | some spine =>
          obtain ⟨c', args'⟩ := spine
          rw [constSpine?, hf] at h
          cases h
          rw [appSpine_of_constSpine? f hf, appSpine_concat]
  | .var _, _, _, h => nomatch h
  | .head _, _, _, h => nomatch h
  | .pi _ _, _, _, h => nomatch h
  | .sigma _ _, _, _, h => nomatch h
  | .id _ _ _, _, _, h => nomatch h
  | .lam _, _, _, h => nomatch h
  | .pair _ _, _, _, h => nomatch h
  | .fst _, _, _, h => nomatch h
  | .snd _, _, _, h => nomatch h
  | .refl _, _, _, h => nomatch h

/-- The number of fields of the first constructor named `name` in a list of
constructors. -/
def ctorFields : List (DeclName × List (Field Head)) → DeclName → Option Nat
  | [], _ => none
  | (c, fields) :: cs, name => if name = c then some fields.length else ctorFields cs name

/-- A value is canonical for a family with constructors `cs` when it is a
listed constructor applied to its number of fields; the result is the
constructor and the fields. -/
def canonicalIn {n : Nat} (cs : List (DeclName × List (Field Head))) (v : Tm Head n) :
    Option (DeclName × List (Tm Head n)) :=
  match constSpine? v with
  | some (c, args) => if ctorFields cs c = some args.length then some (c, args) else none
  | none => none

theorem canonicalIn_eq_some {n : Nat} {cs : List (DeclName × List (Field Head))}
    {v : Tm Head n} {c : DeclName} {args : List (Tm Head n)} :
    canonicalIn cs v = some (c, args) ↔
      v = appSpine (.const c) args ∧ ctorFields cs c = some args.length := by
  constructor
  · intro h
    unfold canonicalIn at h
    cases hv : constSpine? v with
    | none =>
        rw [hv] at h
        cases h
    | some spine =>
        obtain ⟨c', args'⟩ := spine
        rw [hv] at h
        dsimp only at h
        by_cases fields : ctorFields cs c' = some args'.length
        · rw [if_pos fields] at h
          cases h
          exact ⟨appSpine_of_constSpine? v hv, fields⟩
        · rw [if_neg fields] at h
          cases h
  · rintro ⟨rfl, fields⟩
    unfold canonicalIn
    rw [constSpine?_appSpine]
    dsimp only
    exact if_pos fields

theorem ctorFields_mem : ∀ {cs : List (DeclName × List (Field Head))} {c : DeclName} {k : Nat},
    ctorFields cs c = some k → ∃ fields, (c, fields) ∈ cs ∧ fields.length = k
  | [], _, _, h => by cases h
  | (c', fs) :: cs, c, k, h => by
      simp only [ctorFields] at h
      by_cases same : c = c'
      · rw [if_pos same] at h
        cases h
        subst same
        exact ⟨fs, List.mem_cons_self .., rfl⟩
      · rw [if_neg same] at h
        obtain ⟨fields, mem, length⟩ := ctorFields_mem h
        exact ⟨fields, List.mem_cons_of_mem _ mem, length⟩

/-- A neutral value is canonical for no family. -/
theorem canonicalIn_neutral {roles : Roles Head} (declared : ConstructorsDeclared roles)
    {T : DeclName} {cs : List (DeclName × List (Field Head))} (role : roles T = .inductive cs)
    {n : Nat} {x : Tm Head n} (neutral : Neutral roles x) : canonicalIn cs x = none := by
  cases h : canonicalIn cs x with
  | none => rfl
  | some spine =>
      obtain ⟨c, args⟩ := spine
      obtain ⟨rfl, fields⟩ := canonicalIn_eq_some.mp h
      obtain ⟨fs, mem, _⟩ := ctorFields_mem fields
      exact absurd (.inr ⟨c, _, args, declared.arity role mem, rfl⟩) neutral.not_canonical

theorem canonicalIn_subst {n m : Nat} {cs : List (DeclName × List (Field Head))}
    {v : Tm Head n} {c : DeclName} {args : List (Tm Head n)}
    (h : canonicalIn cs v = some (c, args)) (σ : Sub Head n m) :
    canonicalIn cs (Presentation.subst σ v) = some (c, args.map (Presentation.subst σ)) := by
  obtain ⟨rfl, fields⟩ := canonicalIn_eq_some.mp h
  rw [subst_appSpine]
  exact canonicalIn_eq_some.mpr ⟨rfl, by rw [List.length_map]; exact fields⟩

/-! ## Three-valued matching -/

/-- The outcome of matching patterns against values. -/
inductive MatchResult (Head : Type) (n : Nat) where
  /-- A match, with the values of the pattern variables, left to right. -/
  | yes (values : List (Tm Head n))
  /-- A mismatch: distinct constructors of one family meet. -/
  | no
  /-- Matching waits for `value` to become a canonical value of `family`. -/
  | blocked (family : DeclName) (value : Tm Head n)

/-- Matching left to right: the first outcome other than a match decides. -/
def MatchResult.seq {n : Nat} : MatchResult Head n → MatchResult Head n → MatchResult Head n
  | .yes values, .yes values' => .yes (values ++ values')
  | .yes _, .no => .no
  | .yes _, .blocked family value => .blocked family value
  | .no, _ => .no
  | .blocked family value, _ => .blocked family value

/-- Substitute into the values of a result. -/
def MatchResult.subst {n m : Nat} (σ : Sub Head n m) : MatchResult Head n → MatchResult Head m
  | .yes values => .yes (values.map (Presentation.subst σ))
  | .no => .no
  | .blocked family value => .blocked family (Presentation.subst σ value)

theorem MatchResult.seq_subst {n m : Nat} (σ : Sub Head n m) (r r' : MatchResult Head n) :
    (r.seq r').subst σ = (r.subst σ).seq (r'.subst σ) := by
  cases r <;> cases r' <;> simp only [MatchResult.seq, MatchResult.subst, List.map_append]

section Matching

variable (roles : Roles Head) (familyOf : DeclName → DeclName)

mutual
/-- Match a pattern against a value. A constructor pattern inspects the value
as a canonical value of the family `familyOf` assigns to the constructor. -/
def Pat.matchValue {n : Nat} : Pat → Tm Head n → MatchResult Head n
  | .var, v => .yes [v]
  | .con c ps, v =>
      match roles (familyOf c) with
      | .inductive cs =>
          match canonicalIn cs v with
          | some (c', args) => if c' = c then Pat.matchValues ps args else .no
          | none => .blocked (familyOf c) v
      | _ => .blocked (familyOf c) v
/-- Match patterns against values, left to right. Lists of different lengths
mismatch. -/
def Pat.matchValues {n : Nat} : List Pat → List (Tm Head n) → MatchResult Head n
  | [], [] => .yes []
  | p :: ps, v :: vs => (Pat.matchValue p v).seq (Pat.matchValues ps vs)
  | [], _ :: _ => .no
  | _ :: _, [] => .no
end

mutual
/-- Every constructor pattern names a constructor listed by the family
`familyOf` assigns to it, with its number of fields. -/
def Pat.wellFormed : Pat → Bool
  | .var => true
  | .con c ps =>
      (match roles (familyOf c) with
        | .inductive cs => decide (ctorFields cs c = some ps.length)
        | _ => false) && Pat.wellFormedAll ps
/-- Every pattern of the list is well formed. -/
def Pat.wellFormedAll : List Pat → Bool
  | [] => true
  | p :: ps => p.wellFormed && Pat.wellFormedAll ps
end

end Matching

/-- A constructor pattern is blocked on a neutral value. -/
theorem Pat.matchValue_neutral {roles : Roles Head} {familyOf : DeclName → DeclName}
    (declared : ConstructorsDeclared roles) {c : DeclName} (ps : List Pat)
    {cs : List (DeclName × List (Field Head))} (role : roles (familyOf c) = .inductive cs)
    {n : Nat} {x : Tm Head n} (neutral : Neutral roles x) :
    Pat.matchValue roles familyOf (.con c ps) x = .blocked (familyOf c) x := by
  simp only [Pat.matchValue]
  rw [role]
  dsimp only
  rw [canonicalIn_neutral declared role neutral]

/-! ## Equations and first-match selection -/

/-- An equation of a definition by patterns: its argument patterns and its
right side over the pattern variables, listed left to right (the last is
`var 0`). -/
structure Equation (Head : Type) where
  patterns : List Pat
  rhs : Tm Head (Pat.varsAll patterns)

namespace Equation

/-- The right side at values of the pattern variables. -/
def result {n : Nat} (e : Equation Head) (values : List (Tm Head n)) : Tm Head n :=
  Presentation.subst (valueSub (Pat.varsAll e.patterns) values) e.rhs

theorem result_subst {n m : Nat} (e : Equation Head) (values : List (Tm Head n))
    (σ : Sub Head n m) :
    Presentation.subst σ (e.result values) = e.result (values.map (Presentation.subst σ)) := by
  unfold result
  rw [subst_comp]
  exact subst_ext (fun i => valueSub_map _ rfl values i) e.rhs

variable (roles : Roles Head) (familyOf : DeclName → DeclName)

/-- The equation matches the arguments, with these values of its pattern
variables. -/
abbrev Matches (e : Equation Head) {n : Nat} (args values : List (Tm Head n)) : Prop :=
  Pat.matchValues roles familyOf e.patterns args = .yes values

/-- The equation mismatches the arguments. -/
abbrev Mismatches (e : Equation Head) {n : Nat} (args : List (Tm Head n)) : Prop :=
  Pat.matchValues roles familyOf e.patterns args = .no

/-- The equation is blocked on the arguments. -/
abbrev Blocked (e : Equation Head) {n : Nat} (args : List (Tm Head n)) : Prop :=
  ∃ family value, Pat.matchValues roles familyOf e.patterns args = .blocked family value

end Equation

/-- What first-match selection finds among equations. -/
inductive Selection (Head : Type) (n : Nat) where
  /-- The first equation not mismatching matches, with this result. -/
  | found (result : Tm Head n)
  /-- The first equation not mismatching is blocked. -/
  | blocked
  /-- Every equation mismatches. -/
  | missed

section Select

variable (roles : Roles Head) (familyOf : DeclName → DeclName)

/-- First-match selection: the first equation that does not mismatch decides. -/
def select {n : Nat} : List (Equation Head) → List (Tm Head n) → Selection Head n
  | [], _ => .missed
  | e :: es, args =>
      match Pat.matchValues roles familyOf e.patterns args with
      | .yes values => .found (e.result values)
      | .no => select es args
      | .blocked _ _ => .blocked

end Select

/-! ## The covering algorithm -/

/-- The branches of a split over the constructors `cs`, each with the tree
`sub` gives for its constructor and number of fields. -/
def CaseBranches.build (sub : DeclName → Nat → Option (CaseTree Head)) :
    List (DeclName × List (Field Head)) → Option (CaseBranches Head)
  | [] => some .nil
  | (c, fields) :: cs =>
      match sub c fields.length, CaseBranches.build sub cs with
      | some tree, some rest => some (.cons c fields.length tree rest)
      | _, _ => none

section Compile

variable (roles : Roles Head) (familyOf : DeclName → DeclName)

/-- The covering algorithm with `fuel`, on a neighbourhood `N` of `vars`
pattern variables and the equations `es` that have not mismatched it. -/
def compileAt :
    Nat → (vars : Nat) → List Pat → List (Equation Head) → Option (CaseTree Head)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, vars, N, e :: es =>
      match Pat.matchValues roles familyOf e.patterns
          (Pat.terms N (varTerms (Head := Head) vars)) with
      | .yes values => some (.leaf vars (e.result values))
      | .no => compileAt fuel vars N es
      | .blocked family (.var x) =>
          match roles family with
          | .inductive cs =>
              (CaseBranches.build (fun c fields => compileAt fuel (vars - 1 + fields)
                  (Pat.splitAllAt c fields N (vars - 1 - x.val)) (e :: es)) cs).map
                (CaseTree.split (vars - 1 - x.val) family)
          | _ => none
      | .blocked _ _ => none

mutual
/-- The number of constructor patterns in a pattern. -/
def Pat.size : Pat → Nat
  | .var => 0
  | .con _ ps => Pat.sizeAll ps + 1
/-- The number of constructor patterns in a list of patterns. -/
def Pat.sizeAll : List Pat → Nat
  | [] => 0
  | p :: ps => p.size + Pat.sizeAll ps
end

/-- The fuel `compile` gives the covering algorithm: twice the number of
equations and constructor patterns, and two more. -/
def compileFuel (eqs : List (Equation Head)) : Nat :=
  2 * (eqs.length + (eqs.map fun e => Pat.sizeAll e.patterns).sum) + 2

/-- Compile the equations of a constant of the given arity to a case tree.
Equations of another arity are refused. -/
def compile (arity : Nat) (eqs : List (Equation Head)) : Option (CaseTree Head) :=
  if eqs.all (fun e => e.patterns.length == arity) then
    compileAt roles familyOf (compileFuel eqs) arity (List.replicate arity .var) eqs
  else none

end Compile

/-! ## Matching under substitution

A match and a mismatch survive substitution. A block survives substitution
unless the value it waits for becomes canonical. -/

/-- Substitution by `σ` leaves a blocked result's value non-canonical. -/
def MatchResult.Stays (roles : Roles Head) {n m : Nat} (σ : Sub Head n m)
    (r : MatchResult Head n) : Prop :=
  ∀ family value, r = .blocked family value → ∀ cs, roles family = .inductive cs →
    canonicalIn cs (Presentation.subst σ value) = none

theorem MatchResult.stays_yes (roles : Roles Head) {n m : Nat} (σ : Sub Head n m)
    (values : List (Tm Head n)) : (MatchResult.yes values).Stays roles σ := by
  intro _ _ h
  cases h

theorem MatchResult.stays_no (roles : Roles Head) {n m : Nat} (σ : Sub Head n m) :
    (MatchResult.no : MatchResult Head n).Stays roles σ := by
  intro _ _ h
  cases h

theorem MatchResult.Stays.of_seq_yes {roles : Roles Head} {n m : Nat} {σ : Sub Head n m}
    {values : List (Tm Head n)} {r : MatchResult Head n}
    (stays : ((MatchResult.yes values).seq r).Stays roles σ) : r.Stays roles σ := by
  intro family value h
  subst h
  exact stays family value rfl

section Stability

variable {roles : Roles Head} {familyOf : DeclName → DeclName}

mutual
theorem Pat.matchValue_subst {n m : Nat} (σ : Sub Head n m) :
    ∀ (p : Pat) (v : Tm Head n), (Pat.matchValue roles familyOf p v).Stays roles σ →
      Pat.matchValue roles familyOf p (Presentation.subst σ v) =
        (Pat.matchValue roles familyOf p v).subst σ
  | .var, _ => fun _ => rfl
  | .con c ps, v => by
      simp only [Pat.matchValue]
      cases hr : roles (familyOf c) with
      | «inductive» cs =>
          dsimp only
          cases hc : canonicalIn cs v with
          | none =>
              dsimp only
              intro stays
              rw [stays (familyOf c) v rfl cs hr]
              rfl
          | some spine =>
              obtain ⟨c', args⟩ := spine
              dsimp only
              intro stays
              rw [canonicalIn_subst hc σ]
              dsimp only
              by_cases same : c' = c
              · rw [if_pos same] at stays
                rw [if_pos same, if_pos same]
                exact Pat.matchValues_subst σ ps args stays
              · rw [if_neg same, if_neg same]
                rfl
      | rigid => intro _; rfl
      | constructor _ => intro _; rfl
      | computes _ _ => intro _; rfl
theorem Pat.matchValues_subst {n m : Nat} (σ : Sub Head n m) :
    ∀ (ps : List Pat) (vs : List (Tm Head n)),
      (Pat.matchValues roles familyOf ps vs).Stays roles σ →
      Pat.matchValues roles familyOf ps (vs.map (Presentation.subst σ)) =
        (Pat.matchValues roles familyOf ps vs).subst σ
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: ps, v :: vs, stays => by
      simp only [Pat.matchValues, List.map_cons] at stays ⊢
      rw [MatchResult.seq_subst]
      cases h : Pat.matchValue roles familyOf p v with
      | yes values =>
          rw [h] at stays
          rw [Pat.matchValue_subst σ p v (h ▸ MatchResult.stays_yes roles σ values),
            Pat.matchValues_subst σ ps vs stays.of_seq_yes, h]
      | no =>
          rw [Pat.matchValue_subst σ p v (h ▸ MatchResult.stays_no roles σ), h]
          rfl
      | blocked family value =>
          rw [h] at stays
          rw [Pat.matchValue_subst σ p v (h ▸ stays), h]
          rfl
end

theorem Pat.matchValues_subst_yes {n m : Nat} (σ : Sub Head n m) {ps : List Pat}
    {vs values : List (Tm Head n)} (h : Pat.matchValues roles familyOf ps vs = .yes values) :
    Pat.matchValues roles familyOf ps (vs.map (Presentation.subst σ)) =
      .yes (values.map (Presentation.subst σ)) := by
  rw [Pat.matchValues_subst σ ps vs (h ▸ MatchResult.stays_yes roles σ values), h]
  rfl

theorem Pat.matchValues_subst_no {n m : Nat} (σ : Sub Head n m) {ps : List Pat}
    {vs : List (Tm Head n)} (h : Pat.matchValues roles familyOf ps vs = .no) :
    Pat.matchValues roles familyOf ps (vs.map (Presentation.subst σ)) = .no := by
  rw [Pat.matchValues_subst σ ps vs (h ▸ MatchResult.stays_no roles σ), h]
  rfl

theorem Pat.matchValues_subst_blocked {n m : Nat} (σ : Sub Head n m) {ps : List Pat}
    {vs : List (Tm Head n)} {family : DeclName} {value : Tm Head n}
    (h : Pat.matchValues roles familyOf ps vs = .blocked family value)
    (stays : ∀ cs, roles family = .inductive cs →
      canonicalIn cs (Presentation.subst σ value) = none) :
    Pat.matchValues roles familyOf ps (vs.map (Presentation.subst σ)) =
      .blocked family (Presentation.subst σ value) := by
  rw [Pat.matchValues_subst σ ps vs (by rw [h]; intro f v e; cases e; exact stays), h]
  rfl

/-- A match gives one value per argument. -/
theorem Pat.matchValues_length {n : Nat} :
    ∀ {ps : List Pat} {vs values : List (Tm Head n)},
      Pat.matchValues roles familyOf ps vs = .yes values → vs.length = ps.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | p :: ps, v :: vs, values, h => by
      simp only [Pat.matchValues] at h
      cases h₁ : Pat.matchValue roles familyOf p v with
      | yes values₁ =>
          rw [h₁] at h
          cases h₂ : Pat.matchValues roles familyOf ps vs with
          | yes values₂ =>
              simp only [List.length_cons, Pat.matchValues_length h₂]
          | no => rw [h₂] at h; cases h
          | blocked _ _ => rw [h₂] at h; cases h
      | no => rw [h₁] at h; cases h
      | blocked _ _ => rw [h₁] at h; cases h

mutual
/-- A well-formed pattern matches each of its instances, with the values
filling it. -/
theorem Pat.matchValue_term {n : Nat} :
    ∀ (p : Pat), Pat.wellFormed roles familyOf p = true →
      ∀ {vs : List (Tm Head n)}, vs.length = p.vars →
        Pat.matchValue roles familyOf p (Pat.term p vs) = .yes vs
  | .var, _, vs, h => by
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp h
      rfl
  | .con c ps, wf, vs, h => by
      simp only [Pat.wellFormed, Bool.and_eq_true] at wf
      obtain ⟨wfc, wfs⟩ := wf
      have hc : ∀ cs : List (DeclName × List (Field Head)), ctorFields cs c = some ps.length →
          canonicalIn cs (Pat.term (.con c ps) vs) = some (c, Pat.terms ps vs) := fun cs fields =>
        canonicalIn_eq_some.mpr ⟨rfl, by rw [Pat.fillAll_length]; exact fields⟩
      show (match roles (familyOf c) with
        | .inductive cs =>
            match canonicalIn cs (Pat.term (.con c ps) vs) with
            | some (c', args) => if c' = c then Pat.matchValues roles familyOf ps args else .no
            | none => .blocked (familyOf c) (Pat.term (.con c ps) vs)
        | _ => .blocked (familyOf c) (Pat.term (.con c ps) vs)) = _
      cases hr : roles (familyOf c) with
      | «inductive» cs =>
          rw [hr] at wfc
          dsimp only
          rw [hc cs (of_decide_eq_true wfc)]
          dsimp only
          rw [if_pos rfl]
          exact Pat.matchValues_terms ps wfs h
      | rigid => rw [hr] at wfc; cases wfc
      | constructor _ => rw [hr] at wfc; cases wfc
      | computes _ _ => rw [hr] at wfc; cases wfc
/-- Well-formed patterns match each of their instances, with the values
filling them. -/
theorem Pat.matchValues_terms {n : Nat} :
    ∀ (ps : List Pat), Pat.wellFormedAll roles familyOf ps = true →
      ∀ {vs : List (Tm Head n)}, vs.length = Pat.varsAll ps →
        Pat.matchValues roles familyOf ps (Pat.terms ps vs) = .yes vs
  | [], _, vs, h => by
      rw [List.eq_nil_of_length_eq_zero h]
      rfl
  | p :: ps, wf, vs, h => by
      simp only [Pat.wellFormedAll, Bool.and_eq_true] at wf
      simp only [Pat.varsAll_cons] at h
      show (Pat.matchValue roles familyOf p (Pat.term p (vs.take p.vars))).seq
        (Pat.matchValues roles familyOf ps (Pat.terms ps (vs.drop p.vars))) = _
      rw [Pat.matchValue_term p wf.1 (List.length_take_of_le (by omega)),
        Pat.matchValues_terms ps wf.2 (by rw [List.length_drop]; omega)]
      show MatchResult.yes (vs.take p.vars ++ vs.drop p.vars) = _
      rw [List.take_append_drop]
end

end Stability

/-! ## First-match selection by positions -/

section Selection

variable {roles : Roles Head} {familyOf : DeclName → DeclName}

/-- The first equation that matches after mismatches is selected. -/
theorem select_found {n : Nat} {args : List (Tm Head n)} :
    ∀ {es : List (Equation Head)} {i : Nat} (hi : i < es.length) {values : List (Tm Head n)},
      es[i].Matches roles familyOf args values →
      (∀ j (hj : j < i), (es[j]'(Nat.lt_trans hj hi)).Mismatches roles familyOf args) →
        select roles familyOf es args = .found (es[i].result values)
  | [], _, hi, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | e :: es, 0, _, values, hmatch, _ => by
      simp only [select]
      rw [show Pat.matchValues roles familyOf e.patterns args = .yes values from hmatch]
      rfl
  | e :: es, i + 1, hi, values, hmatch, earlier => by
      simp only [select]
      rw [show Pat.matchValues roles familyOf e.patterns args = .no from
        earlier 0 (Nat.succ_pos i)]
      exact select_found (Nat.lt_of_succ_lt_succ hi) hmatch
        (fun j hj => earlier (j + 1) (Nat.succ_lt_succ hj))

/-- An equation blocked after mismatches blocks the selection. -/
theorem select_blocked {n : Nat} {args : List (Tm Head n)} :
    ∀ {es : List (Equation Head)} {j : Nat} (hj : j < es.length),
      es[j].Blocked roles familyOf args →
      (∀ i (hi : i < j), (es[i]'(Nat.lt_trans hi hj)).Mismatches roles familyOf args) →
        select roles familyOf es args = .blocked
  | [], _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | e :: es, 0, _, ⟨family, value, blocked⟩, _ => by
      simp only [select]
      rw [show Pat.matchValues roles familyOf e.patterns args = .blocked family value from
        blocked]
  | e :: es, j + 1, hj, blocked, earlier => by
      simp only [select]
      rw [show Pat.matchValues roles familyOf e.patterns args = .no from
        earlier 0 (Nat.succ_pos j)]
      exact select_blocked (Nat.lt_of_succ_lt_succ hj) blocked
        (fun i hi => earlier (i + 1) (Nat.succ_lt_succ hi))

end Selection

/-! ## Branches built from constructors -/

theorem CaseBranches.build_find {sub : DeclName → Nat → Option (CaseTree Head)} :
    ∀ {cs : List (DeclName × List (Field Head))} {branches : CaseBranches Head},
      CaseBranches.build sub cs = some branches →
      ∀ {c : DeclName} {fields : Nat} {tree : CaseTree Head},
        branches.find c = some (fields, tree) →
          ctorFields cs c = some fields ∧ sub c fields = some tree
  | [], branches, h, c, fields, tree, found => by
      cases h
      cases found
  | (c', fs) :: cs, branches, h, c, fields, tree, found => by
      simp only [CaseBranches.build] at h
      cases ht : sub c' fs.length with
      | none => rw [ht] at h; cases h
      | some t =>
          cases hrest : CaseBranches.build sub cs with
          | none => rw [ht, hrest] at h; cases h
          | some rest =>
              rw [ht, hrest] at h
              cases h
              simp only [CaseBranches.find] at found
              simp only [ctorFields]
              by_cases same : c = c'
              · rw [if_pos same] at found ⊢
                cases found
                subst same
                exact ⟨rfl, ht⟩
              · rw [if_neg same] at found ⊢
                exact CaseBranches.build_find hrest found

theorem CaseBranches.build_find_of_ctorFields {sub : DeclName → Nat → Option (CaseTree Head)} :
    ∀ {cs : List (DeclName × List (Field Head))} {branches : CaseBranches Head},
      CaseBranches.build sub cs = some branches →
      ∀ {c : DeclName} {fields : Nat}, ctorFields cs c = some fields →
        ∃ tree, sub c fields = some tree ∧ branches.find c = some (fields, tree)
  | [], _, _, _, _, hc => by cases hc
  | (c', fs) :: cs, branches, h, c, fields, hc => by
      simp only [CaseBranches.build] at h
      cases ht : sub c' fs.length with
      | none => rw [ht] at h; cases h
      | some t =>
          cases hrest : CaseBranches.build sub cs with
          | none => rw [ht, hrest] at h; cases h
          | some rest =>
              rw [ht, hrest] at h
              cases h
              simp only [ctorFields] at hc
              simp only [CaseBranches.find]
              by_cases same : c = c'
              · rw [if_pos same] at hc ⊢
                cases hc
                subst same
                exact ⟨t, ht, rfl⟩
              · rw [if_neg same] at hc ⊢
                exact CaseBranches.build_find_of_ctorFields hrest hc

theorem CaseBranches.build_cover {roles : Roles Head}
    {sub : DeclName → Nat → Option (CaseTree Head)}
    (covers : ∀ c fields tree, sub c fields = some tree → tree.Covers roles) :
    ∀ {cs : List (DeclName × List (Field Head))} {branches : CaseBranches Head},
      CaseBranches.build sub cs = some branches → CaseBranches.Cover roles cs branches
  | [], _, h => by
      cases h
      exact .nil
  | (c, fs) :: cs, branches, h => by
      simp only [CaseBranches.build] at h
      cases ht : sub c fs.length with
      | none => rw [ht] at h; cases h
      | some t =>
          cases hrest : CaseBranches.build sub cs with
          | none => rw [ht, hrest] at h; cases h
          | some rest =>
              rw [ht, hrest] at h
              cases h
              exact .cons (covers _ _ _ ht) (CaseBranches.build_cover covers hrest)

theorem CaseBranches.build_scoped {vars : Nat}
    {sub : DeclName → Nat → Option (CaseTree Head)}
    (inScope : ∀ c fields tree, sub c fields = some tree → tree.Scoped (vars - 1 + fields)) :
    ∀ {cs : List (DeclName × List (Field Head))} {branches : CaseBranches Head},
      CaseBranches.build sub cs = some branches → CaseBranches.Scoped vars branches
  | [], _, h => by
      cases h
      exact .nil
  | (c, fs) :: cs, branches, h => by
      simp only [CaseBranches.build] at h
      cases ht : sub c fs.length with
      | none => rw [ht] at h; cases h
      | some t =>
          cases hrest : CaseBranches.build sub cs with
          | none => rw [ht, hrest] at h; cases h
          | some rest =>
              rw [ht, hrest] at h
              cases h
              exact .cons (inScope _ _ _ ht) (CaseBranches.build_scoped inScope hrest)

/-! ## Soundness of the covering algorithm -/

/-- The values split at a position. -/
theorem eq_take_getD_drop {α : Type} {xs : List α} {p : Nat} (h : p < xs.length) (d : α) :
    xs = xs.take p ++ xs.getD p d :: xs.drop (p + 1) := by
  rw [← List.getElem_eq_getD (h := h) d, ← List.drop_eq_getElem_cons h, List.take_append_drop]

section Soundness

variable {roles : Roles Head} {familyOf : DeclName → DeclName}

theorem compileAt_covers :
    ∀ (fuel : Nat) {vars : Nat} {N : List Pat} {es : List (Equation Head)}
      {tree : CaseTree Head}, compileAt roles familyOf fuel vars N es = some tree →
        tree.Covers roles
  | 0, _, _, _, _, h => by cases h
  | _ + 1, _, _, [], _, h => by cases h
  | fuel + 1, vars, N, e :: es, tree, h => by
      simp only [compileAt] at h
      split at h
      · cases h
        exact .leaf _ _
      · exact compileAt_covers fuel h
      · split at h
        · rename_i cs hcs
          obtain ⟨branches, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .split hcs (CaseBranches.build_cover
            (fun _ _ _ ht => compileAt_covers fuel ht) hb)
        · cases h
      · cases h

theorem compileAt_scoped :
    ∀ (fuel : Nat) {vars : Nat} {N : List Pat} {es : List (Equation Head)}
      {tree : CaseTree Head}, compileAt roles familyOf fuel vars N es = some tree →
        tree.Scoped vars
  | 0, _, _, _, _, h => by cases h
  | _ + 1, _, _, [], _, h => by cases h
  | fuel + 1, vars, N, e :: es, tree, h => by
      simp only [compileAt] at h
      split at h
      · cases h
        exact .leaf _
      · exact compileAt_scoped fuel h
      · rename_i family x _
        split at h
        · obtain ⟨branches, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .split (by have := x.isLt; omega) (CaseBranches.build_scoped
            (fun _ _ _ ht => compileAt_scoped fuel ht) hb)
        · cases h
      · cases h

/-- The covering algorithm is sound and complete for first-match selection:
the tree evaluates on the values of the neighbourhood's variables exactly as
first-match selection chooses among the remaining equations at the filled
neighbourhood. -/
theorem compileAt_eval :
    ∀ (fuel : Nat) {vars : Nat} {N : List Pat} {es : List (Equation Head)}
      {tree : CaseTree Head}, compileAt roles familyOf fuel vars N es = some tree →
        Pat.varsAll N = vars → ∀ {n : Nat} {vs : List (Tm Head n)}, vs.length = vars →
          ∀ {u : Tm Head n},
            tree.Eval vs u ↔ select roles familyOf es (Pat.terms N vs) = .found u
  | 0, _, _, _, _, h => by cases h
  | _ + 1, _, _, [], _, h => by cases h
  | fuel + 1, vars, N, e :: es, tree, h => by
      intro hN n vs hvs u
      have hargs := Pat.terms_varTerms_subst (Head := Head) N hvs
      simp only [compileAt] at h
      split at h
      · rename_i values hm
        cases h
        have hm' := Pat.matchValues_subst_yes (valueSub vars vs) hm
        rw [hargs] at hm'
        simp only [select, hm']
        rw [← e.result_subst]
        constructor
        · intro eval
          cases eval
          rfl
        · intro found
          cases found
          exact .leaf _ hvs
      · rename_i hm
        have hm' := Pat.matchValues_subst_no (valueSub vars vs) hm
        rw [hargs] at hm'
        rw [compileAt_eval fuel h hN hvs]
        simp only [select, hm']
      · rename_i family x hm
        split at h
        · rename_i cs hcs
          have hx := x.isLt
          obtain ⟨branches, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          constructor
          · intro eval
            cases eval with
            | @split _ _ _ before after args c t _ lengthBefore found evalT =>
                obtain ⟨_, ht⟩ := CaseBranches.build_find hb found
                have hv := Pat.varsAll_splitAllAt c args.length N (vars - 1 - x.val)
                  (by omega)
                simp only [List.length_append, List.length_cons] at hvs
                have ih := (compileAt_eval fuel ht (by omega)
                  (vs := before ++ args ++ after) (by simp only [List.length_append]; omega)
                  (u := u)).mp evalT
                rw [← lengthBefore, Pat.terms_splitAllAt_fields c N before args after
                  (by omega)] at ih
                exact ih
          · intro found
            have hp : vars - 1 - x.val < vs.length := by omega
            cases hcan : canonicalIn cs (vs.getD (vars - 1 - x.val) defaultTm) with
            | none =>
                exfalso
                have blocked := Pat.matchValues_subst_blocked (valueSub vars vs) hm (by
                  intro cs' hcs'
                  rw [hcs] at hcs'
                  cases hcs'
                  exact hcan)
                rw [hargs] at blocked
                simp only [select, blocked] at found
                cases found
            | some spine =>
                obtain ⟨c, fields⟩ := spine
                obtain ⟨hvalue, hfields⟩ := canonicalIn_eq_some.mp hcan
                obtain ⟨t, ht, hfind⟩ := CaseBranches.build_find_of_ctorFields hb hfields
                have hsplit := eq_take_getD_drop hp defaultTm
                rw [hvalue] at hsplit
                have hv := Pat.varsAll_splitAllAt c fields.length N (vars - 1 - x.val)
                  (by omega)
                have hlen : (vs.take (vars - 1 - x.val)).length = vars - 1 - x.val :=
                  List.length_take_of_le (by omega)
                have hdrop : (vs.drop (vars - 1 - x.val + 1)).length =
                    vars - (vars - 1 - x.val + 1) := by
                  rw [List.length_drop, hvs]
                have key := Pat.terms_splitAllAt_fields c N (vs.take (vars - 1 - x.val)) fields
                  (vs.drop (vars - 1 - x.val + 1)) (by rw [hlen, hdrop]; omega)
                rw [hlen] at key
                rw [hsplit]
                refine .split hlen hfind ((compileAt_eval fuel ht (by omega)
                  (by simp only [List.length_append, hlen, hdrop]; omega)).mpr ?_)
                rw [key, ← hsplit]
                exact found
        · cases h
      · cases h

end Soundness

/-! ## The compiled tree -/

section Compiled

variable {roles : Roles Head} {familyOf : DeclName → DeclName}

theorem compile_arity {arity : Nat} {eqs : List (Equation Head)} {tree : CaseTree Head}
    (h : compile roles familyOf arity eqs = some tree) :
    ∀ e ∈ eqs, e.patterns.length = arity := by
  unfold compile at h
  split at h
  · rename_i hall
    intro e mem
    exact beq_iff_eq.mp (List.all_eq_true.mp hall e mem)
  · cases h

/-- Every split of a compiled tree lists the constructors of an inductive
type. -/
theorem compile_covers {arity : Nat} {eqs : List (Equation Head)} {tree : CaseTree Head}
    (h : compile roles familyOf arity eqs = some tree) : tree.Covers roles := by
  unfold compile at h
  split at h
  · exact compileAt_covers _ h
  · cases h

/-- A compiled tree is scoped at the arity. -/
theorem compile_scoped {arity : Nat} {eqs : List (Equation Head)} {tree : CaseTree Head}
    (h : compile roles familyOf arity eqs = some tree) : tree.Scoped arity := by
  unfold compile at h
  split at h
  · exact compileAt_scoped _ h
  · cases h

/-- A compiled tree evaluates on arguments exactly by first-match selection. -/
theorem compile_eval {arity : Nat} {eqs : List (Equation Head)} {tree : CaseTree Head}
    (h : compile roles familyOf arity eqs = some tree) {n : Nat} {args : List (Tm Head n)}
    (length : args.length = arity) {u : Tm Head n} :
    tree.Eval args u ↔ select roles familyOf eqs args = .found u := by
  unfold compile at h
  split at h
  · have := compileAt_eval _ h (Pat.varsAll_replicate arity) length (u := u)
    rwa [← length, Pat.terms_replicate] at this
  · cases h

/-- A compiled tree steps exactly at spines of the arity, to the result of
first-match selection. -/
theorem compile_step {arity : Nat} {eqs : List (Equation Head)} {tree : CaseTree Head}
    (h : compile roles familyOf arity eqs = some tree) {f : DeclName} {n : Nat}
    {t u : Tm Head n} :
    tree.Step f arity t u ↔ ∃ args, t = appSpine (.const f) args ∧ args.length = arity ∧
      select roles familyOf eqs args = .found u := by
  constructor
  · rintro ⟨args, rfl, length, eval⟩
    exact ⟨args, rfl, length, (compile_eval h length).mp eval⟩
  · rintro ⟨args, rfl, length, found⟩
    exact ⟨args, rfl, length, (compile_eval h length).mpr found⟩

/-- The first equation that matches after mismatches fires. -/
theorem compile_firstMatch {arity : Nat} {eqs : List (Equation Head)} {tree : CaseTree Head}
    (h : compile roles familyOf arity eqs = some tree) (f : DeclName) {n : Nat}
    {args : List (Tm Head n)} {i : Nat} (hi : i < eqs.length) {values : List (Tm Head n)}
    (hmatch : eqs[i].Matches roles familyOf args values)
    (earlier : ∀ j (hj : j < i), (eqs[j]'(Nat.lt_trans hj hi)).Mismatches roles familyOf args) :
    tree.Step f arity (appSpine (.const f) args) (eqs[i].result values) := by
  have length : args.length = arity :=
    (Pat.matchValues_length hmatch).trans (compile_arity h _ (List.getElem_mem hi))
  exact (compile_step h).mpr ⟨args, rfl, length, select_found hi hmatch earlier⟩

/-- An equation blocked after mismatches blocks the definition: no step. -/
theorem compile_blocked {arity : Nat} {eqs : List (Equation Head)} {tree : CaseTree Head}
    (h : compile roles familyOf arity eqs = some tree) (f : DeclName) {n : Nat}
    {args : List (Tm Head n)} {j : Nat} (hj : j < eqs.length)
    (blocked : eqs[j].Blocked roles familyOf args)
    (earlier : ∀ i (hi : i < j), (eqs[i]'(Nat.lt_trans hi hj)).Mismatches roles familyOf args)
    (u : Tm Head n) : ¬ tree.Step f arity (appSpine (.const f) args) u := by
  intro step
  obtain ⟨args', same, _, found⟩ := (compile_step h).mp step
  obtain ⟨-, rfl⟩ := appSpine_const_injective same
  rw [select_blocked hj blocked earlier] at found
  cases found

end Compiled

/-! ## Axiom audit -/

#print axioms constSpine?_appSpine
#print axioms appSpine_of_constSpine?
#print axioms canonicalIn_eq_some
#print axioms ctorFields_mem
#print axioms canonicalIn_neutral
#print axioms canonicalIn_subst
#print axioms Pat.matchValue_neutral
#print axioms MatchResult.seq_subst
#print axioms Equation.result_subst
#print axioms MatchResult.stays_yes
#print axioms MatchResult.stays_no
#print axioms MatchResult.Stays.of_seq_yes
#print axioms Pat.matchValue_subst
#print axioms Pat.matchValues_subst
#print axioms Pat.matchValues_subst_yes
#print axioms Pat.matchValues_subst_no
#print axioms Pat.matchValues_subst_blocked
#print axioms Pat.matchValues_length
#print axioms Pat.matchValue_term
#print axioms Pat.matchValues_terms
#print axioms select_found
#print axioms select_blocked
#print axioms CaseBranches.build_find
#print axioms CaseBranches.build_find_of_ctorFields
#print axioms CaseBranches.build_cover
#print axioms CaseBranches.build_scoped
#print axioms eq_take_getD_drop
#print axioms compileAt_covers
#print axioms compileAt_scoped
#print axioms compileAt_eval
#print axioms compile_arity
#print axioms compile_covers
#print axioms compile_scoped
#print axioms compile_eval
#print axioms compile_step
#print axioms compile_firstMatch
#print axioms compile_blocked

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
