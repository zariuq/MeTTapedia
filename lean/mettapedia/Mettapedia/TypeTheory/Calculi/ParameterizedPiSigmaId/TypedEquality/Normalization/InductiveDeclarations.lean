import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Eliminator

/-!
# Declarations of simple inductive types

A simple inductive type `T` in a universe `u` has constructors whose fields are
`T` itself or closed types. Its declaration consists of

- the type constant `T : u`;
- a constructor `k : F₁ → ⋯ → Fₐ → T` for each entry of the constructor list;
- the recursor `rec : Π (P : T → v). case₁ → ⋯ → case_c → Π (t : T). P t`, where
  the case of a constructor takes its fields, then an induction hypothesis
  `P x` for each recursive field `x`, and returns `P (k x₁ ⋯ xₐ)`;
- one computation rule per constructor,
  `rec P m₁ ⋯ m_c (kᵢ a₁ ⋯ aₐ) ⟶ mᵢ a₁ ⋯ aₐ (rec P m₁ ⋯ m_c aⱼ) ⋯`, with a
  recursive call for each recursive field `aⱼ`.

Telescopes are given entry by entry. Case types are built binder by binder:
under each binder the motive and the fields bound so far are weakened, so the
bound variables are always `var 0` at the moment they are introduced.

The declaration record lists the obligations under which the constants are
semantic: roles, the stages of the rule package at which the field types, the
constructor types and the recursor type are typed, and the computation rules.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Telescopes given by their entries -/

/-- The telescope whose entry at position `j` is `entry j`. -/
def ofEntries (entry : (j : Nat) → Tm Head j) : (n : Nat) → Ctx Head n
  | 0 => .nil
  | n + 1 => .snoc (ofEntries entry n) (entry n)

theorem closeType_ofEntries_succ (entry : (j : Nat) → Tm Head j) (n : Nat) (C : Tm Head (n + 1)) :
    closeType (ofEntries entry (n + 1)) C = closeType (ofEntries entry n) (.pi (entry n) C) :=
  rfl

theorem telescopeArgs_ofEntries_succ (entry : (j : Nat) → Tm Head j) (n : Nat) {m : Nat}
    (σ : Sub Head (n + 1) m) :
    telescopeArgs (ofEntries entry (n + 1)) σ =
      telescopeArgs (ofEntries entry n) (tailSub σ) ++ [σ 0] :=
  rfl

/-- The first argument of a substitution of a telescope is its outermost
variable. -/
theorem telescopeArgs_ofEntries_head (entry : (j : Nat) → Tm Head j) :
    ∀ (n : Nat) {m : Nat} (σ : Sub Head (n + 1) m),
      ∃ rest, telescopeArgs (ofEntries entry (n + 1)) σ = σ (Fin.last n) :: rest
  | 0, _, σ => ⟨[], rfl⟩
  | n + 1, _, σ => by
      obtain ⟨rest, h⟩ := telescopeArgs_ofEntries_head entry n (tailSub σ)
      refine ⟨rest ++ [σ 0], ?_⟩
      rw [telescopeArgs_ofEntries_succ, h]
      rfl

/-! ## Fields and constructors -/

/-- The type of a field of a constructor of `T`. -/
def Field.type (T : DeclName) : Field Head → Tm Head 0
  | .recursive => .const T
  | .closed F => F

/-- The entries of a constructor's telescope: the types of its fields. -/
def ctorEntry (T : DeclName) (fields : List (Field Head)) (j : Nat) : Tm Head j :=
  liftClosed ((fields.getD j .recursive).type T)

/-- The telescope of a constructor. -/
def ctorTele (T : DeclName) (fields : List (Field Head)) : Ctx Head fields.length :=
  ofEntries (ctorEntry T fields) fields.length

/-- The declared type `F₁ → ⋯ → Fₐ → T` of a constructor. -/
def ctorType (T : DeclName) (fields : List (Field Head)) : Tm Head 0 :=
  closeType (ctorTele T fields) (.const T)

/-! ## Cases of the recursor -/

/-- The induction hypotheses `P r → ⋯` ending in `P target`, substituted by `σ`;
under each binder `σ` is weakened. -/
def caseHypsSub {n : Nat} (p target : Tm Head n) :
    {m : Nat} → Sub Head n m → List (Tm Head n) → Tm Head m
  | _, σ, [] => .app (Presentation.subst σ p) (Presentation.subst σ target)
  | _, σ, r :: rs =>
      .pi (.app (Presentation.subst σ p) (Presentation.subst σ r))
        (caseHypsSub p target (fun i => Presentation.rename wk (σ i)) rs)

/-- The induction hypotheses `P r → ⋯`, ending in `P target`. -/
def caseHyps {n : Nat} (p : Tm Head n) (rs : List (Tm Head n)) (target : Tm Head n) :
    Tm Head n :=
  caseHypsSub p target ids rs

/-- The type of a method for constructor `k`: the remaining fields, over the
motive `p`, the fields `xs` bound so far and the recursive ones `recs` among
them. -/
def caseFields (T k : DeclName) :
    List (Field Head) → {n : Nat} → Tm Head n → List (Tm Head n) → List (Tm Head n) → Tm Head n
  | [], _, p, xs, recs => caseHyps p recs (appSpine (.const k) xs)
  | .recursive :: fs, _, p, xs, recs =>
      .pi (.const T) (caseFields T k fs (Presentation.rename wk p)
        (xs.map (Presentation.rename wk) ++ [.var 0]) (recs.map (Presentation.rename wk) ++ [.var 0]))
  | .closed F :: fs, _, p, xs, recs =>
      .pi (liftClosed F) (caseFields T k fs (Presentation.rename wk p)
        (xs.map (Presentation.rename wk) ++ [.var 0]) (recs.map (Presentation.rename wk)))

/-- The type of the method for constructor `k` with the given fields, over the
motive `p`. -/
def caseType (T k : DeclName) (fields : List (Field Head)) {n : Nat} (p : Tm Head n) :
    Tm Head n :=
  caseFields T k fields p [] []

/-- The recursive fields among the arguments of a constructor. -/
def recArgs {n : Nat} : List (Field Head) → List (Tm Head n) → List (Tm Head n)
  | .recursive :: fs, a :: as => a :: recArgs fs as
  | .closed _ :: fs, _ :: as => recArgs fs as
  | _, _ => []

/-! ## The recursor -/

/-- The type `T → v` of motives. -/
def motiveTy (T : DeclName) (v : Head) : Tm Head 0 := .pi (.const T) (.head v)

/-- The entries of the recursor's telescope: the motive, a method for each
constructor over it, and the scrutinee. -/
def recEntry (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head))) :
    (j : Nat) → Tm Head j
  | 0 => motiveTy T v
  | j + 1 =>
      match ctors[j]? with
      | some (k, fields) => caseType T k fields (.var (Fin.last j))
      | none => .const T

/-- The telescope of the recursor. -/
def recTele (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head))) :
    Ctx Head (ctors.length + 2) :=
  ofEntries (recEntry T v ctors) (ctors.length + 2)

/-- The result type `P t` of the recursor. -/
def recBody (c : Nat) : Tm Head (c + 2) := .app (.var (Fin.last (c + 1))) (.var 0)

/-- The declared type of the recursor. -/
def recType (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head))) : Tm Head 0 :=
  closeType (recTele T v ctors) (recBody ctors.length)

/-- A full application of the recursor: the motive and the methods, then the
scrutinee. -/
def recApp (rec : DeclName) {n : Nat} (pre : List (Tm Head n)) (t : Tm Head n) : Tm Head n :=
  appSpine (.const rec) (pre ++ [t])

/-! ## Substitution -/

theorem subst_caseHypsSub {n : Nat} (p target : Tm Head n) :
    ∀ {m k : Nat} (σ : Sub Head n m) (τ : Sub Head m k) (rs : List (Tm Head n)),
      Presentation.subst τ (caseHypsSub p target σ rs) =
        caseHypsSub p target (fun i => Presentation.subst τ (σ i)) rs
  | _, _, σ, τ, [] => by simp [caseHypsSub, Presentation.subst]
  | _, _, σ, τ, r :: rs => by
      simp only [caseHypsSub, Presentation.subst, subst_comp]
      rw [subst_caseHypsSub p target _ (liftSub τ) rs]
      simp only [subst_liftSub_wk]

/-- Hypotheses with the same data after substitution are the same. -/
theorem caseHypsSub_congr {n n' : Nat} (p target : Tm Head n) (p' target' : Tm Head n') :
    ∀ {m : Nat} (σ : Sub Head n m) (σ' : Sub Head n' m) (rs : List (Tm Head n))
      (rs' : List (Tm Head n')),
      Presentation.subst σ p = Presentation.subst σ' p' →
      Presentation.subst σ target = Presentation.subst σ' target' →
      rs.map (Presentation.subst σ) = rs'.map (Presentation.subst σ') →
      caseHypsSub p target σ rs = caseHypsSub p' target' σ' rs'
  | _, σ, σ', [], [], hp, ht, _ => by simp [caseHypsSub, hp, ht]
  | _, σ, σ', r :: rs, r' :: rs', hp, ht, hrs => by
      simp only [List.map_cons, List.cons.injEq] at hrs
      simp only [caseHypsSub, hp, hrs.1]
      have weak : ∀ {k j : Nat} (τ : Sub Head k j) (x : Tm Head k),
          Presentation.subst (fun i => Presentation.rename wk (τ i)) x =
            Presentation.rename wk (Presentation.subst τ x) :=
        fun τ x => (rename_subst wk τ x).symm
      congr 1
      apply caseHypsSub_congr
      · rw [weak, weak, hp]
      · rw [weak, weak, ht]
      · have h := congrArg (List.map (Presentation.rename wk)) hrs.2
        have f : (Presentation.subst fun i => Presentation.rename wk (σ i)) =
            fun x => Presentation.rename wk (Presentation.subst σ x) := funext (weak σ)
        have f' : (Presentation.subst fun i => Presentation.rename wk (σ' i)) =
            fun x => Presentation.rename wk (Presentation.subst σ' x) := funext (weak σ')
        rw [f, f']
        simpa [List.map_map, Function.comp_def] using h
  | _, _, _, [], _ :: _, _, _, h => by simp at h
  | _, _, _, _ :: _, [], _, _, h => by simp at h

/-- Substituting the data of the hypotheses instead of the result. -/
theorem caseHypsSub_eq {n m : Nat} (p target : Tm Head n) (σ : Sub Head n m)
    (rs : List (Tm Head n)) :
    caseHypsSub p target σ rs =
      caseHyps (Presentation.subst σ p) (rs.map (Presentation.subst σ))
        (Presentation.subst σ target) :=
  caseHypsSub_congr _ _ _ _ σ ids rs _ (by rw [subst_ids]) (by rw [subst_ids])
    (by simp [List.map_map, Function.comp_def])

theorem caseHyps_nil {n : Nat} (p target : Tm Head n) : caseHyps p [] target = .app p target := by
  simp [caseHyps, caseHypsSub]

theorem caseHyps_cons {n : Nat} (p r : Tm Head n) (rs : List (Tm Head n)) (target : Tm Head n) :
    caseHyps p (r :: rs) target =
      .pi (.app p r) (caseHyps (Presentation.rename wk p) (rs.map (Presentation.rename wk))
        (Presentation.rename wk target)) := by
  have e : (Presentation.subst fun i => Presentation.rename wk (ids i : Tm Head n)) =
      Presentation.rename wk := funext fun t => subst_renSub wk t
  show caseHypsSub p target ids (r :: rs) = _
  rw [caseHypsSub, caseHypsSub_eq, subst_ids, subst_ids, e]

theorem subst_caseHyps {n m : Nat} (σ : Sub Head n m) (p : Tm Head n) (rs : List (Tm Head n))
    (target : Tm Head n) :
    Presentation.subst σ (caseHyps p rs target) =
      caseHyps (Presentation.subst σ p) (rs.map (Presentation.subst σ))
        (Presentation.subst σ target) := by
  rw [caseHyps, subst_caseHypsSub, ← caseHypsSub_eq]
  rfl

theorem subst_caseFields (T k : DeclName) : ∀ (fs : List (Field Head)) {n m : Nat}
    (σ : Sub Head n m) (p : Tm Head n) (xs recs : List (Tm Head n)),
    Presentation.subst σ (caseFields T k fs p xs recs) =
      caseFields T k fs (Presentation.subst σ p) (xs.map (Presentation.subst σ))
        (recs.map (Presentation.subst σ))
  | [], _, _, σ, p, xs, recs => by
      simp only [caseFields]
      rw [subst_caseHyps, subst_appSpine]
      rfl
  | .recursive :: fs, _, _, σ, p, xs, recs => by
      simp only [caseFields, Presentation.subst]
      rw [subst_caseFields T k fs (liftSub σ)]
      simp only [List.map_append, List.map_map, Function.comp_def, subst_liftSub_wk,
        List.map_cons, List.map_nil, Presentation.subst, liftSub_zero]
  | .closed F :: fs, _, _, σ, p, xs, recs => by
      simp only [caseFields, Presentation.subst]
      rw [subst_caseFields T k fs (liftSub σ), subst_liftClosed]
      simp only [List.map_append, List.map_map, Function.comp_def, subst_liftSub_wk,
        List.map_cons, List.map_nil, Presentation.subst, liftSub_zero]

theorem subst_caseType (T k : DeclName) (fields : List (Field Head)) {n m : Nat}
    (σ : Sub Head n m) (p : Tm Head n) :
    Presentation.subst σ (caseType T k fields p) = caseType T k fields (Presentation.subst σ p) :=
  subst_caseFields T k fields σ p [] []

/-- Opening the first induction hypothesis. -/
theorem inst0_caseHyps {n : Nat} (a p : Tm Head n) (rs : List (Tm Head n)) (target : Tm Head n) :
    inst0 a (caseHyps (Presentation.rename wk p) (rs.map (Presentation.rename wk))
      (Presentation.rename wk target)) = caseHyps p rs target := by
  rw [inst0, subst_caseHyps]
  simp only [List.map_map, Function.comp_def]
  have e : ∀ t : Tm Head n, Presentation.subst (subst0 a) (Presentation.rename wk t) = t :=
    fun t => inst0_rename_wk a t
  simp only [e, List.map_id']

/-- Opening the first field of a case. -/
theorem inst0_caseFields (T k : DeclName) (fs : List (Field Head)) {n : Nat} (a p : Tm Head n)
    (xs recs : List (Tm Head n)) (new : List (Tm Head (n + 1))) (newInst : List (Tm Head n))
    (hnew : new.map (inst0 a) = newInst) :
    inst0 a (caseFields T k fs (Presentation.rename wk p)
      (xs.map (Presentation.rename wk) ++ [.var 0]) (recs.map (Presentation.rename wk) ++ new)) =
      caseFields T k fs p (xs ++ [a]) (recs ++ newInst) := by
  rw [inst0, subst_caseFields]
  have e : ∀ t : Tm Head n, Presentation.subst (subst0 a) (Presentation.rename wk t) = t :=
    fun t => inst0_rename_wk a t
  simp only [List.map_append, List.map_map, Function.comp_def, e, List.map_id', List.map_cons,
    List.map_nil]
  rw [← hnew]
  rfl

/-- Substituting the recursor's result type. -/
theorem subst_recBody {c m : Nat} (t : Tm Head m) (τ : Sub Head (c + 1) m) :
    Presentation.subst (consSub t τ) (recBody c) = .app (τ (Fin.last c)) t :=
  rfl

theorem recEntry_scrutinee (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head))) :
    recEntry T v ctors (ctors.length + 1) = .const T := by
  simp [recEntry]

theorem recEntry_method (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head)))
    {j : Nat} {k : DeclName} {fields : List (Field Head)} (entry : ctors[j]? = some (k, fields)) :
    recEntry T v ctors (j + 1) = caseType T k fields (.var (Fin.last j)) := by
  simp [recEntry, entry]

/-! ## Arguments -/

theorem recArgs_length_le : ∀ {n : Nat} (fs : List (Field Head)) (as : List (Tm Head n)),
    (recArgs fs as).length ≤ as.length
  | _, .recursive :: fs, _ :: as => by simp [recArgs]; exact recArgs_length_le fs as
  | _, .closed _ :: fs, _ :: as => by simp [recArgs]; exact Nat.le_succ_of_le (recArgs_length_le fs as)
  | _, [], _ => by simp [recArgs]
  | _, _ :: _, [] => by cases ‹Field Head› <;> simp [recArgs]

theorem rename_recArgs {n m : Nat} (ρ : Ren n m) :
    ∀ (fs : List (Field Head)) (as : List (Tm Head n)),
      (recArgs fs as).map (Presentation.rename ρ) = recArgs fs (as.map (Presentation.rename ρ))
  | .recursive :: fs, a :: as => by simp [recArgs, rename_recArgs ρ fs as]
  | .closed _ :: fs, _ :: as => by simp [recArgs, rename_recArgs ρ fs as]
  | [], _ => by simp [recArgs]
  | .recursive :: _, [] => by simp [recArgs]
  | .closed _ :: _, [] => by simp [recArgs]

/-! ## Declarations -/

/-- Every constant of a rule package is semantic. -/
def AllSemantic (S : Setting Head L) (R : Rules Head) : Prop :=
  ∀ {name : DeclName} {type : Tm Head 0}, R.constantType name = some type →
    SemanticConstant S name type

theorem AllSemantic.semanticConstantsOf {S : Setting Head L} {R : Rules Head}
    (semantic : AllSemantic S R) : SemanticConstantsOf S R :=
  fun declared _ _ => semantic declared

/-- The rule package declares the simple inductive type `T` in the universe `u`
with the constructors `ctors` and the recursor `rec` into the universe `v`. The
declaration is made in three stages: `R₀` has the earlier constants, `R₁` adds
`T`, and `R₂` adds the constructors. Field types are typed at `R₀`, constructor
types at `R₁` and the recursor's type at `R₂`. -/
structure DeclaresInductive (S : Setting Head L) (R₀ R₁ R₂ : Rules Head) (T : DeclName)
    (u : Head) (ctors : List (DeclName × List (Field Head))) (rec : DeclName) (v : Head) :
    Prop where
  role : S.roles T = .inductive ctors
  recRole : S.roles rec = .computes (ctors.length + 2) (.split (ctors.length + 1) .constructor fun _ => .leaf)
  hu : S.R.isUniverse u
  hv : S.R.isUniverse v
  sub₀ : RulesSub R₀ S.R
  sub₁ : RulesSub R₁ S.R
  sub₂ : RulesSub R₂ S.R
  semantic₀ : AllSemantic S R₀
  stage₁ : ∀ {name : DeclName} {type : Tm Head 0}, R₁.constantType name = some type →
    R₀.constantType name = some type ∨ (name = T ∧ type = .head u)
  stage₂ : ∀ {name : DeclName} {type : Tm Head 0}, R₂.constantType name = some type →
    R₁.constantType name = some type ∨
      ∃ fields, (name, fields) ∈ ctors ∧ type = ctorType T fields
  declared : S.R.constantType T = some (.head u)
  ctorDeclared : ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
    S.R.constantType k = some (ctorType T fields)
  recDeclared : S.R.constantType rec = some (recType T v ctors)
  fieldTyped : ∀ {k : DeclName} {fields : List (Field Head)} {F : Tm Head 0},
    (k, fields) ∈ ctors → Field.closed F ∈ fields → Typed R₀ .nil F (.head u)
  ctorTyped : ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
    ∃ w, S.R.isUniverse w ∧ Typed R₁ .nil (ctorType T fields) (.head w)
  recTyped : ∃ w, S.R.isUniverse w ∧ Typed R₂ .nil (recType T v ctors) (.head w)
  iota : ∀ {n : Nat} {p : Tm Head n} {ms : List (Tm Head n)} {i : Nat} {k : DeclName}
    {fields : List (Field Head)} {args : List (Tm Head n)} {m : Tm Head n},
    ms.length = ctors.length → ctors[i]? = some (k, fields) → args.length = fields.length →
    ms[i]? = some m →
    S.R.computation.step (recApp rec (p :: ms) (appSpine (.const k) args))
      (appSpine m (args ++ (recArgs fields args).map (recApp rec (p :: ms))))

/-- **A package declares the recursor `rec` of the simple inductive type `T`** with the
constructors `ctors`, into the universe `v`: its role computes on its last argument, each
constructor and the recursor are declared at their types, and the recursor's type is a type of a
universe. These are the facts about a recursor that its typing and its computation rules need;
a declaration in stages has them (`DeclaresInductive.toRecursor`). -/
structure DeclaresRecursor (S : Setting Head L) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (rec : DeclName) (v : Head) : Prop where
  recRole : S.roles rec =
    .computes (ctors.length + 2) (.split (ctors.length + 1) .constructor fun _ => .leaf)
  ctorDeclared : ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
    S.R.constantType k = some (ctorType T fields)
  recDeclared : S.R.constantType rec = some (recType T v ctors)
  recTyped : ∃ w, S.R.isUniverse w ∧ Typed S.R .nil (recType T v ctors) (.head w)

/-- A declaration in stages declares its recursor. -/
theorem DeclaresInductive.toRecursor {S : Setting Head L} {R₀ R₁ R₂ : Rules Head}
    {T : DeclName} {u : Head} {ctors : List (DeclName × List (Field Head))} {rec : DeclName}
    {v : Head} (decl : DeclaresInductive S R₀ R₁ R₂ T u ctors rec v) :
    DeclaresRecursor S T ctors rec v where
  recRole := decl.recRole
  ctorDeclared := decl.ctorDeclared
  recDeclared := decl.recDeclared
  recTyped := by
    obtain ⟨w, hw, typed⟩ := decl.recTyped
    exact ⟨w, hw, Derivable.mono decl.sub₂ typed⟩

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
