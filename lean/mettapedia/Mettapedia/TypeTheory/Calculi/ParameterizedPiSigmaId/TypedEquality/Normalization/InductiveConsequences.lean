import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Recursor

/-!
# Consequences for simple inductive types

For the typed equality of a rule package:

- when its constants are semantic, constructors are injective and distinct:
  equal constructor applications have the same constructor and equal arguments
  at the field types, and a constructor application is never equal to a neutral
  term;
- given the facts about the weak-head forms of its types, the computation rules
  of a declared recursor preserve typing: in a typed application of the
  recursor to a constructor form, the method applied to the fields and to the
  recursive calls has the application's type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Constructor forms -/

/-- Equal arguments for the fields of a constructor, at the field types. -/
inductive FieldsEqual (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (T : DeclName) :
    List (Field Head) → List (Tm Head n) → List (Tm Head n) → Prop
  | nil : FieldsEqual R Γ T [] [] []
  | cons {f : Field Head} {fs : List (Field Head)} {a b : Tm Head n} {as bs : List (Tm Head n)}
      (head : Equal R Γ a b (liftClosed (f.type T))) (tail : FieldsEqual R Γ T fs as bs) :
      FieldsEqual R Γ T (f :: fs) (a :: as) (b :: bs)

/-- The two shapes of reducibly equal normal forms of an inductive type. -/
theorem IndEqNf.shape {n : Nat} {Γ : Ctx Head n} {T : DeclName}
    {ctors : List (DeclName × List (Field Head))} {fieldPack : Tm Head 0 → Pack Head n}
    {nf nf' : Tm Head n} (normal : IndEqNf S Γ T ctors fieldPack nf nf') :
    (∃ k fields args args', (k, fields) ∈ ctors ∧
        IndEqFields S Γ T ctors fieldPack fields args args' ∧
        nf = appSpine (.const k) args ∧ nf' = appSpine (.const k) args') ∨
      (Neutral S.roles nf ∧ Neutral S.roles nf') := by
  cases normal with
  | ctor mem arguments => exact .inl ⟨_, _, _, _, mem, arguments, rfl, rfl⟩
  | neutral neutral neutral' _ => exact .inr ⟨neutral, neutral'⟩

section Constructors

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
include laws constants

omit constants in
/-- Reducibly equal arguments for fields are equal at the field types. -/
theorem IndEqFields.equal {n : Nat} {Γ : Ctx Head n} {T : DeclName}
    {ctors : List (DeclName × List (Field Head))} {fieldPack : Tm Head 0 → Pack Head n}
    (rT : Reducible S Γ (.const T) (indPack S Γ T ctors fieldPack))
    (fieldsRed : ∀ {k : DeclName} {fields : List (Field Head)} {F : Tm Head 0},
      (k, fields) ∈ ctors → Field.closed F ∈ fields →
      Reducible S Γ (liftClosed F) (fieldPack F))
    {k : DeclName} {fields₀ : List (Field Head)} (mem : (k, fields₀) ∈ ctors) :
    ∀ {as : List (Tm Head n)} {fields : List (Field Head)} {bs : List (Tm Head n)},
      (∀ {F}, Field.closed F ∈ fields → Field.closed F ∈ fields₀) →
      IndEqFields S Γ T ctors fieldPack fields as bs → FieldsEqual S.R Γ T fields as bs
  | [], _, _, _, h => by cases h; exact .nil
  | _ :: _, _, _, sub, h => by
      cases h with
      | recursive head tail =>
          exact .cons (laws.convTm_sound ((rT.escape laws).eqTm head))
            (IndEqFields.equal rT fieldsRed mem (fun c => sub (List.mem_cons_of_mem _ c)) tail)
      | closed head tail =>
          have r := fieldsRed mem (sub (List.mem_cons_self ..))
          exact .cons (laws.convTm_sound ((r.escape laws).eqTm head))
            (IndEqFields.equal rT fieldsRed mem (fun c => sub (List.mem_cons_of_mem _ c)) tail)

/-- Constructors are injective and distinct: equal constructor applications at
an inductive type have the same constructor, the same fields and equal
arguments. -/
theorem Equal.ctor_injective {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    (role : S.roles T = .inductive ctors) {k k' : DeclName} {fields fields' : List (Field Head)}
    (mem : (k, fields) ∈ ctors) (mem' : (k', fields') ∈ ctors) {as bs : List (Tm Head n)}
    (equal : Equal S.R Γ (appSpine (.const k) as) (appSpine (.const k') bs) (.const T)) :
    k = k' ∧ fields = fields' ∧ FieldsEqual S.R Γ T fields as bs := by
  obtain ⟨r, eq⟩ := Equal.reducible laws constants equal formed
  obtain ⟨fieldPack, same, fieldsRed⟩ := Reducible.inductive_view role r
  rw [same] at eq r
  obtain ⟨red, red', _, normal⟩ := eq
  obtain rfl := WhRed.eq_of_whnf (canonical_whnf S.shape (ctorSpine_canonical role mem as)) red.red
  obtain rfl := WhRed.eq_of_whnf (canonical_whnf S.shape (ctorSpine_canonical role mem' bs))
    red'.red
  rcases normal.shape with ⟨k₀, fields₀, args, args', mem₀, arguments, e, e'⟩ |
    ⟨neutral, _⟩
  · obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
    obtain ⟨rfl, rfl⟩ := appSpine_const_injective e'
    obtain rfl := S.constructors.fields_unique role mem mem₀
    obtain rfl := S.constructors.fields_unique role mem' mem₀
    exact ⟨rfl, rfl, IndEqFields.equal laws r fieldsRed mem₀ id arguments⟩
  · exact absurd (ctorSpine_canonical role mem as) neutral.not_canonical

/-- Distinct constructors are never equal. -/
theorem Equal.ctor_discrimination {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    (role : S.roles T = .inductive ctors) {k k' : DeclName} {fields fields' : List (Field Head)}
    (mem : (k, fields) ∈ ctors) (mem' : (k', fields') ∈ ctors) (distinct : k ≠ k')
    {as bs : List (Tm Head n)} :
    ¬ Equal S.R Γ (appSpine (.const k) as) (appSpine (.const k') bs) (.const T) :=
  fun equal => distinct (Equal.ctor_injective laws constants formed role mem mem' equal).1

/-- A constructor application is never equal to a neutral term. -/
theorem Equal.ctor_ne_neutral {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    (role : S.roles T = .inductive ctors) {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) {as : List (Tm Head n)} {b : Tm Head n}
    (neutral : Neutral S.roles b) :
    ¬ Equal S.R Γ (appSpine (.const k) as) b (.const T) := by
  intro equal
  obtain ⟨r, eq⟩ := Equal.reducible laws constants equal formed
  obtain ⟨fieldPack, same, _⟩ := Reducible.inductive_view role r
  rw [same] at eq
  obtain ⟨red, red', _, normal⟩ := eq
  obtain rfl := WhRed.eq_of_whnf (canonical_whnf S.shape (ctorSpine_canonical role mem as)) red.red
  obtain rfl := WhRed.eq_of_whnf (neutral.whnf S.shape) red'.red
  rcases normal.shape with ⟨k₀, fields₀, args, args', mem₀, _, _, e'⟩ | ⟨neutral₀, _⟩
  · rw [e'] at neutral
    exact neutral.not_canonical (ctorSpine_canonical role mem₀ args')
  · exact neutral₀.not_canonical (ctorSpine_canonical role mem as)

end Constructors

/-! ## Substitutions from argument lists -/

/-- The substitution of a telescope of length `N` by the entries of a list, in
telescope order. -/
def argsSub {m : Nat} (N : Nat) (args : List (Tm Head m)) : Sub Head N m :=
  fun i => args.getD (N - 1 - i) (.const .anonymous)

theorem telescopeArgs_argsSub (entry : (j : Nat) → Tm Head j) :
    ∀ (N : Nat) {m : Nat} (args : List (Tm Head m)), args.length = N →
      telescopeArgs (ofEntries entry N) (argsSub N args) = args := by
  intro N
  induction N with
  | zero =>
      intro m args h
      rw [List.length_eq_zero_iff.mp h]
      rfl
  | succ N ih =>
      intro m args h
      have hne : args ≠ [] := by
        rintro rfl
        exact Nat.noConfusion h
      obtain ⟨init, last, rfl⟩ : ∃ init last, args = init ++ [last] :=
        ⟨args.dropLast, args.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      have hi : init.length = N := by
        simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h
        exact h
      rw [telescopeArgs_ofEntries_succ]
      have tail : tailSub (argsSub (N + 1) (init ++ [last])) = argsSub N init := by
        funext i
        show (init ++ [last]).getD (N + 1 - 1 - (i.val + 1)) _ = init.getD (N - 1 - i.val) _
        have e : N + 1 - 1 - (i.val + 1) = N - 1 - i.val := by omega
        rw [e, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
      have head : argsSub (N + 1) (init ++ [last]) 0 = last := by
        simp [argsSub, hi]
      rw [tail, head, ih init hi]

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a : α},
      l₁[i]? = some a → ∃ b, l₂[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hab⟩
  | _, _, .cons _ rest, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact forall₂_getElem? rest h

/-! ## Typing of methods -/

/-- Applying a term of a method type to typed arguments for the fields. -/
theorem Typed.caseFields_app {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {T k : DeclName} :
    ∀ {fs : List (Field Head)} {as : List (Tm Head n)},
      List.Forall₂ (fun f a => Typed R Γ a (Presentation.liftClosed (Field.type T f))) fs as →
      ∀ {p : Tm Head n} {xs recs : List (Tm Head n)} {g : Tm Head n},
      Typed R Γ g (caseFields T k fs p xs recs) →
      Typed R Γ (appSpine g as) (caseHyps p (recs ++ recArgs fs as) (appSpine (.const k) (xs ++ as)))
  | [], [], .nil, p, xs, recs, g, h => by simpa [caseFields, recArgs] using h
  | .recursive :: fs, a :: as, .cons ha rest, p, xs, recs, g, h => by
      simp only [caseFields] at h
      have h₁ := Derivable.appElim h ha
      rw [inst0_caseFields T k fs a p xs recs [.var 0] [a] rfl] at h₁
      have result := Typed.caseFields_app rest h₁
      simpa [recArgs, List.append_assoc] using result
  | .closed F :: fs, a :: as, .cons ha rest, p, xs, recs, g, h => by
      simp only [caseFields] at h
      have h₁ := Derivable.appElim h ha
      have inst := inst0_caseFields T k fs a p xs recs [] [] rfl
      rw [List.append_nil, List.append_nil] at inst
      rw [inst] at h₁
      have result := Typed.caseFields_app rest h₁
      simpa [recArgs, List.append_assoc] using result

/-- Applying a function of the induction hypotheses to typed hypotheses. -/
theorem Typed.caseHyps_app {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {p target : Tm Head n} :
    ∀ {rs ihs : List (Tm Head n)}, List.Forall₂ (fun r ih => Typed R Γ ih (.app p r)) rs ihs →
      ∀ {g : Tm Head n}, Typed R Γ g (caseHyps p rs target) →
      Typed R Γ (appSpine g ihs) (.app p target)
  | [], [], .nil, g, h => by rwa [caseHyps_nil] at h
  | _ :: _, _ :: _, .cons hih rest, g, h => by
      rw [caseHyps_cons] at h
      have h₁ := Derivable.appElim h hih
      rw [inst0_caseHyps] at h₁
      exact Typed.caseHyps_app rest h₁

/-- Typed recursive calls at the recursive fields. -/
theorem recCalls_typed {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {T : DeclName}
    {p : Tm Head n} {call : Tm Head n → Tm Head n}
    (typed : ∀ {a}, Typed R Γ a (.const T) → Typed R Γ (call a) (.app p a)) :
    ∀ {fs : List (Field Head)} {as : List (Tm Head n)},
      List.Forall₂ (fun f a => Typed R Γ a (liftClosed (Field.type T f))) fs as →
      List.Forall₂ (fun r ih => Typed R Γ ih (.app p r)) (recArgs fs as) ((recArgs fs as).map call)
  | [], [], .nil => .nil
  | .recursive :: _, _ :: _, .cons ha rest => .cons (typed ha) (recCalls_typed typed rest)
  | .closed _ :: _, _ :: _, .cons _ rest => by
      simp only [recArgs]
      exact recCalls_typed typed rest

/-! ## Typings from substitutions of telescopes -/

theorem SubstMor.head {R : Rules Head} {n m : Nat} {Θ : Ctx Head n} {A : Tm Head n}
    {Δ : Ctx Head m} {σ : Sub Head (n + 1) m} (typed : SubstMor R (.snoc Θ A) Δ σ) :
    Typed R Δ (σ 0) (Presentation.subst (tailSub σ) A) := by
  have h := typed 0
  rwa [Ctx.lookup_snoc_zero, subst_rename_wk] at h

/-- The fields of a typed substitution of a constructor's telescope are typed
at the field types. -/
theorem fields_of_substMor {R : Rules Head} {m : Nat} {Δ : Ctx Head m} {T : DeclName}
    {fields : List (Field Head)} :
    ∀ (j : Nat), j ≤ fields.length → ∀ {σ : Sub Head j m},
      SubstMor R (ofEntries (ctorEntry T fields) j) Δ σ →
      List.Forall₂ (fun f a => Typed R Δ a (liftClosed (Field.type T f))) (fields.take j)
        (telescopeArgs (ofEntries (ctorEntry T fields) j) σ) := by
  intro j
  induction j with
  | zero => intro _ _ _; exact .nil
  | succ j ih =>
      intro hj σ typed
      have rest := ih (by omega) (SubstMor.tail typed)
      have head := SubstMor.head typed
      rw [ctorEntry_eq (by omega), subst_liftClosed] at head
      rw [telescopeArgs_ofEntries_succ, List.take_succ_eq_append_getElem (by omega)]
      exact List.rel_append rest (.cons head .nil)

/-- The motive and the methods of a typed substitution of the recursor's prefix. -/
theorem methods_of_substMor {R : Rules Head} {m : Nat} {Δ : Ctx Head m} {T : DeclName}
    {v : Head} {ctors : List (DeclName × List (Field Head))} :
    ∀ (j : Nat), j ≤ ctors.length → ∀ {τ : Sub Head (j + 1) m},
      SubstMor R (ofEntries (recEntry T v ctors) (j + 1)) Δ τ →
      Typed R Δ (τ (Fin.last j)) (.pi (.const T) (.head v)) ∧
      ∃ ms, telescopeArgs (ofEntries (recEntry T v ctors) (j + 1)) τ = τ (Fin.last j) :: ms ∧
        List.Forall₂ (fun c mt => Typed R Δ mt (caseType T c.1 c.2 (τ (Fin.last j))))
          (ctors.take j) ms := by
  intro j
  induction j with
  | zero =>
      intro _ τ typed
      exact ⟨SubstMor.head typed, [], rfl, .nil⟩
  | succ j ih =>
      intro hj τ typed
      obtain ⟨motive, ms, hms, methods⟩ := ih (by omega) (SubstMor.tail typed)
      have head := SubstMor.head typed
      have hget : ctors[j]? = some ctors[j] := List.getElem?_eq_getElem (by omega)
      rcases hc : ctors[j] with ⟨k, fields⟩
      rw [hc] at hget
      rw [recEntry_method T v ctors hget, subst_caseType] at head
      refine ⟨motive, ms ++ [τ 0], ?_, ?_⟩
      · rw [telescopeArgs_ofEntries_succ, hms]
        rfl
      · rw [List.take_succ_eq_append_getElem (by omega), hc]
        exact List.rel_append methods (.cons head .nil)

/-! ## The computation rules preserve typing -/

section Preservation

variable {S₀ : Setting Head L} (facts : FormFacts S.R S.roles) {T : DeclName}
  {v : Head} {ctors : List (DeclName × List (Field Head))} {rec : DeclName}
  {R₀ R₁ R₂ : Rules Head} {u : Head} (decl : DeclaresInductive S₀ R₀ R₁ R₂ T u ctors rec v)
  (sub : RulesSub S₀.R S.R)
include facts decl sub

/-- A computation rule of the recursor preserves typing, in every package
containing the declaring one: in a typed application of the recursor to a
constructor form, the method applied to the fields and to the recursive calls
has the application's type. -/
theorem DeclaresInductive.iota_preserves {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {p : Tm Head n} {ms : List (Tm Head n)} {i : Nat} {k : DeclName}
    {fields : List (Field Head)} {as : List (Tm Head n)} {mt A : Tm Head n}
    (hms : ms.length = ctors.length) (hi : ctors[i]? = some (k, fields))
    (has : as.length = fields.length) (hm : ms[i]? = some mt)
    (typing : Typed S.R Γ (recApp rec (p :: ms) (appSpine (.const k) as)) A) :
    Typed S.R Γ (appSpine mt (as ++ (recArgs fields as).map (recApp rec (p :: ms)))) A := by
  have mem : (k, fields) ∈ ctors := List.mem_of_getElem? hi
  /- Invert the recursor's application. -/
  have args : telescopeArgs (recTele T v ctors)
      (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as])) =
        p :: ms ++ [appSpine (.const k) as] :=
    telescopeArgs_argsSub _ _ _ (by simp [hms])
  have typing' : Typed S.R Γ (applyClosed (recTele T v ctors)
      (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as])) (.const rec)) A := by
    rw [applyClosed_eq_appSpine, args]
    exact typing
  obtain ⟨mor, _, le⟩ := Typed.telescope_inv facts formed (recTele T v ctors)
    (recBody ctors.length) (sub.constantType decl.recDeclared) typing'
  have prefixMor := SubstMor.tail mor
  obtain ⟨_, ms₀, hms₀, methods⟩ :=
    methods_of_substMor (R := S.R) ctors.length (Nat.le_refl _) prefixMor
  rw [List.take_length] at methods
  have split : telescopeArgs (recPrefix T v ctors)
      (tailSub (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as]))) ++
      [argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as]) 0] =
        p :: ms ++ [appSpine (.const k) as] := args
  rw [hms₀] at split
  obtain ⟨hpre, hlast⟩ := List.append_inj' split rfl
  obtain ⟨hp, hms'⟩ := List.cons.inj hpre
  have hscrut := (List.cons.inj hlast).1
  have hms'' := hms'.symm
  subst hms''
  /- The method and the scrutinee. -/
  obtain ⟨mt₀, hmt₀, tmt⟩ := forall₂_getElem? methods hi
  rw [hm] at hmt₀
  obtain rfl := Option.some.inj hmt₀.symm
  rw [hp] at tmt
  have tScrut := SubstMor.head mor
  rw [recEntry_scrutinee, hscrut] at tScrut
  /- Invert the constructor's application. -/
  have argsK : telescopeArgs (ofEntries (ctorEntry T fields) fields.length)
      (argsSub fields.length as) = as :=
    telescopeArgs_argsSub _ _ _ has
  have typingK : Typed S.R Γ (applyClosed (ctorTele T fields) (argsSub fields.length as)
      (.const k)) (.const T) := by
    rw [applyClosed_eq_appSpine]
    show Typed S.R Γ (appSpine (.const k) (telescopeArgs (ofEntries (ctorEntry T fields)
      fields.length) (argsSub fields.length as))) (.const T)
    rw [argsK]
    exact tScrut
  obtain ⟨morK, _, _⟩ := Typed.telescope_inv facts formed (ctorTele T fields)
    (.const T) (sub.constantType (decl.ctorDeclared mem)) typingK
  have fieldsTyped := fields_of_substMor (R := S.R) fields.length (Nat.le_refl _) morK
  rw [List.take_length, argsK] at fieldsTyped
  /- The recursive calls. -/
  have headsRA : recApp rec (p :: ms) =
      Tm.app (recHead rec T v ctors
        (tailSub (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as])))) := by
    funext x
    rw [app_recHead, hms₀, hp]
  have headTyped : Typed S.R Γ (recHead rec T v ctors
      (tailSub (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as]))))
      (.pi (.const T) (.app (Presentation.rename wk
        (tailSub (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as]))
          (Fin.last ctors.length))) (.var 0))) := by
    have h := Typed.telescope_apply (Θ := recPrefix T v ctors)
      (X := .pi (recEntry T v ctors (ctors.length + 1)) (recBody ctors.length)) prefixMor
      (Derivable.mono sub (decl.rec_typing (Γ := Γ)))
    rw [recEntry_scrutinee] at h
    exact h
  have calls := recCalls_typed (call := recApp rec (p :: ms)) (fun ha => by
    rw [headsRA]
    have h := Derivable.appElim headTyped ha
    rw [inst0_motiveApp] at h
    rwa [hp] at h) fieldsTyped
  /- The method applied to both. -/
  have applied := Typed.caseFields_app fieldsTyped (xs := []) (recs := []) tmt
  simp only [List.nil_append] at applied
  have result := Typed.caseHyps_app calls applied
  rw [appSpine_append]
  refine Typed.subsume result ?_
  have body : Presentation.subst (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as]))
      (recBody ctors.length) = .app p (appSpine (.const k) as) := by
    have hp' : argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as])
        (Fin.last (ctors.length + 1)) = p := hp
    show Tm.app (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as])
      (Fin.last (ctors.length + 1)))
      (argsSub (ctors.length + 2) (p :: ms ++ [appSpine (.const k) as]) 0) = _
    rw [hp', hscrut]
  rwa [body] at le

end Preservation

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
