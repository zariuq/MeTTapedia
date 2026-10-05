import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ParameterizedDatatypes

/-!
# The package that declares a parameterized datatype

`parameterDecls` gives the declared types of a datatype that may have parameters:
the type constant, the constructors and the recursor, each closed over the parameter
telescope. This module gives those constants a rule package (`parameterRules`) and
its annotation (`parameterChurch`).

The computation rules are the recursor's. A parameter stands on the recursor and on
the constructor, as a pattern variable. A method is applied to the constructor's
fields and to the recursor at each uniform field; the parameters are not applied
again, because the methods are bound under the parameters.

The empty parameterization is the simple inductive. `parameterRules` agrees with
`inductiveRules` there (`parameterRules_of_none`), by the same computation as
`parameterDecls_of_none`. It is not an abbreviation of `inductiveRules`, and
`withDeclarations` is unchanged: a declaration whose parameterization is not yet
known still builds the simple package from `Datatype.ctors`.

The type constant does not mention the datatype. Closing a formed parameter
telescope over its universe is a type of the base package (`typeConstant_isType`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open AlgebraicSchema (SchemaFamily SchemaStep)
open Impredicative.Domain (pisCtx)
open Normalization
open TelescopeAbstraction (closeType)
open UniverseLevel (LevelOrder)

variable {Head : Type}

/-! ## Recursive arguments of an open constructor -/

/-- The arguments at the uniform fields. A plain field is not a recursive argument. -/
def openRecArgs {p n : Nat} : List (OpenField Head p) → List (Tm Head n) → List (Tm Head n)
  | .uniform :: fs, a :: as => a :: openRecArgs fs as
  | .plain _ :: fs, _ :: as => openRecArgs fs as
  | _, _ => []

theorem map_openRecArgs {p n m : Nat} (f : Tm Head n → Tm Head m) :
    ∀ (fs : List (OpenField Head p)) (as : List (Tm Head n)),
      (openRecArgs fs as).map f = openRecArgs fs (as.map f)
  | .uniform :: fs, a :: as => by simp [openRecArgs, map_openRecArgs f fs as]
  | .plain _ :: fs, _ :: as => by simp [openRecArgs, map_openRecArgs f fs as]
  | [], _ => by simp [openRecArgs]
  | .uniform :: _, [] => by simp [openRecArgs]
  | .plain _ :: _, [] => by simp [openRecArgs]

/-! ## The computation rules -/

/-- A computation rule of the recursor `rec` of the open constructors `ctors`,
with `p` parameters. The parameters are pattern variables of the recursor and of
the constructor. -/
def OpenIotaStep (rec : DeclName) (p : Nat)
    (ctors : List (DeclName × List (OpenField Head p))) {n : Nat}
    (l r : Tm Head n) : Prop :=
  ∃ (params : List (Tm Head n)) (motive : Tm Head n) (ms : List (Tm Head n))
    (i : Nat) (k : DeclName) (fields : List (OpenField Head p))
    (args : List (Tm Head n)) (m : Tm Head n),
    params.length = p ∧ ms.length = ctors.length ∧ ctors[i]? = some (k, fields) ∧
    args.length = fields.length ∧ ms[i]? = some m ∧
    l = recApp rec (params ++ motive :: ms)
      (appSpine (.const k) (params ++ args)) ∧
    r = appSpine m (args ++
      (openRecArgs fields args).map (recApp rec (params ++ motive :: ms)))

/-- `(l₁ ++ l₂).getD (l₁.length + j) = l₂.getD j`. -/
theorem getD_length_add {α : Type} (l₁ l₂ : List α) (j : Nat) (d : α) :
    (l₁ ++ l₂).getD (l₁.length + j) d = l₂.getD j d := by
  induction l₁ with
  | nil => simp [List.length_nil, Nat.zero_add]
  | cons _ l ih =>
      simp only [List.cons_append, List.length_cons, Nat.succ_add, List.getD_cons_succ]
      exact ih

/-- The computation rules of a parameterized recursor, as a root computation. -/
def openIotaComputation (rec : DeclName) (p : Nat)
    (ctors : List (DeclName × List (OpenField Head p))) : RootComputation Head where
  step := OpenIotaStep rec p ctors
  rename := by
    rintro n m ρ l r ⟨params, motive, ms, i, k, fields, args, mt, hp, hms, hi, has, hm, rfl, rfl⟩
    refine ⟨params.map (Presentation.rename ρ), Presentation.rename ρ motive,
      ms.map (Presentation.rename ρ), i, k, fields, args.map (Presentation.rename ρ),
      Presentation.rename ρ mt, by simp [hp], by simp [hms], hi, by simp [has], by simp [hm], ?_, ?_⟩
    · rw [rename_recApp, rename_appSpine]
      simp only [List.map_append, List.map_cons, Presentation.rename]
    · rw [rename_appSpine, List.map_append, List.map_map, ← map_openRecArgs]
      simp only [List.map_map, Function.comp_def, rename_recApp, List.map_append, List.map_cons]
  substitute := by
    rintro n m σ l r ⟨params, motive, ms, i, k, fields, args, mt, hp, hms, hi, has, hm, rfl, rfl⟩
    refine ⟨params.map (Presentation.subst σ), Presentation.subst σ motive,
      ms.map (Presentation.subst σ), i, k, fields, args.map (Presentation.subst σ),
      Presentation.subst σ mt, by simp [hp], by simp [hms], hi, by simp [has], by simp [hm], ?_, ?_⟩
    · rw [subst_recApp, subst_appSpine]
      simp only [List.map_append, List.map_cons, Presentation.subst]
    · rw [subst_appSpine, List.map_append, List.map_map, ← map_openRecArgs]
      simp only [List.map_map, Function.comp_def, subst_recApp, List.map_append, List.map_cons]

/-! ## Schemas -/

/-- The left side of a computation rule, over `p` parameters, the motive, `c`
methods and `a` fields of constructor `k`. The constructor is applied to the
parameters and the fields. -/
def openIotaLeft (rec k : DeclName) (p c a : Nat) : Tm Head (p + 1 + c + a) :=
  recApp rec ((metaVars (p + 1 + c + a)).take (p + 1 + c))
    (appSpine (.const k)
      ((metaVars (p + 1 + c + a)).take p ++ (metaVars (p + 1 + c + a)).drop (p + 1 + c)))

/-- The right side of the computation rule for the constructor at index `i`.
The method is the variable at position `p + 1 + i`, applied to the fields and to
the recursive calls. -/
def openIotaRight (rec : DeclName) (p c i : Nat) (fields : List (OpenField Head p)) :
    Tm Head (p + 1 + c + fields.length) :=
  appSpine (((metaVars (p + 1 + c + fields.length)).take (p + 1 + c)).getD (p + 1 + i) defaultTm)
    ((metaVars (p + 1 + c + fields.length)).drop (p + 1 + c) ++
      (openRecArgs fields ((metaVars (p + 1 + c + fields.length)).drop (p + 1 + c))).map
        (recApp rec ((metaVars (p + 1 + c + fields.length)).take (p + 1 + c))))

/-- The schemas of a parameterized recursor: one computation rule per open constructor. -/
def openIotaSchema (rec : DeclName) (p : Nat)
    (ctors : List (DeclName × List (OpenField Head p))) : SchemaFamily Head :=
  fun {arity} L R => ∃ i k fields, ctors[i]? = some (k, fields) ∧
    (⟨arity, (L, R)⟩ : Schema Head) =
      ⟨p + 1 + ctors.length + fields.length,
        (openIotaLeft rec k p ctors.length fields.length,
          openIotaRight rec p ctors.length i fields)⟩

theorem subst_openIotaLeft {n : Nat} (rec k : DeclName) (p c a : Nat)
    (τ : Sub Head (p + 1 + c + a) n) :
    Presentation.subst τ (openIotaLeft rec k p c a) =
      recApp rec (((metaVars (p + 1 + c + a)).map (Presentation.subst τ)).take (p + 1 + c))
        (appSpine (.const k)
          (((metaVars (p + 1 + c + a)).map (Presentation.subst τ)).take p ++
            ((metaVars (p + 1 + c + a)).map (Presentation.subst τ)).drop (p + 1 + c))) := by
  simp only [openIotaLeft, subst_recApp, subst_appSpine, List.map_take, List.map_drop,
    List.map_append]
  rfl

theorem subst_openIotaRight {n : Nat} (rec : DeclName) (p c i : Nat)
    (fields : List (OpenField Head p)) (τ : Sub Head (p + 1 + c + fields.length) n) :
    Presentation.subst τ (openIotaRight rec p c i fields) =
      appSpine ((((metaVars (p + 1 + c + fields.length)).map (Presentation.subst τ)).take
          (p + 1 + c)).getD (p + 1 + i) defaultTm)
        (((metaVars (p + 1 + c + fields.length)).map (Presentation.subst τ)).drop (p + 1 + c) ++
          (openRecArgs fields (((metaVars (p + 1 + c + fields.length)).map
              (Presentation.subst τ)).drop (p + 1 + c))).map
            (recApp rec (((metaVars (p + 1 + c + fields.length)).map
              (Presentation.subst τ)).take (p + 1 + c)))) := by
  simp only [openIotaRight, subst_appSpine, List.map_append, List.map_map, List.map_take,
    List.map_drop, ← getD_map_subst]
  congr 2
  rw [← List.map_drop, ← map_openRecArgs, List.map_map]
  congr 1
  funext t
  simp only [Function.comp_apply, subst_recApp, List.map_take]

/-- **The computation rules of a parameterized recursor are presented by their schemas.** -/
theorem openIota_presents (rec : DeclName) (p : Nat)
    (ctors : List (DeclName × List (OpenField Head p))) :
    Presents (openIotaComputation rec p ctors) (openIotaSchema rec p ctors) := by
  intro n l r
  constructor
  · rintro ⟨params, motive, ms, i, k, fields, args, m, hp, hms, hi, has, hm, rfl, rfl⟩
    have hprefix : (params ++ motive :: ms).length = p + 1 + ctors.length := by
      simp only [List.length_append, List.length_cons, hp, hms]
      omega
    have hts : ((params ++ motive :: ms) ++ args).length =
        p + 1 + ctors.length + fields.length := by
      simp only [List.length_append, hprefix, has]
    have key := map_listSub_metaVars ((params ++ motive :: ms) ++ args) hts
    have step := SchemaStep.instantiate (schema := openIotaSchema rec p ctors)
      ⟨i, k, fields, hi, rfl⟩
      (listSub (p + 1 + ctors.length + fields.length) ((params ++ motive :: ms) ++ args))
    have htake : ((params ++ motive :: ms) ++ args).take (p + 1 + ctors.length) =
        params ++ motive :: ms := List.take_left' hprefix
    have hdrop : ((params ++ motive :: ms) ++ args).drop (p + 1 + ctors.length) = args :=
      List.drop_left' hprefix
    have htakeP : ((params ++ motive :: ms) ++ args).take p = params := by
      rw [List.take_append_of_le_length (by rw [hprefix]; omega)]
      exact List.take_left' hp
    have hget : (params ++ motive :: ms).getD (p + 1 + i) defaultTm = m := by
      have hidx : p + 1 + i = params.length + (i + 1) := by rw [hp]; omega
      rw [hidx, getD_length_add, List.getD_cons_succ, List.getD_eq_getElem?_getD, hm]
      rfl
    rw [subst_openIotaLeft, subst_openIotaRight, key, htake, hdrop, htakeP, hget] at step
    exact step
  · intro step
    cases step with
    | instantiate rule τ =>
      obtain ⟨i, k, fields, hi, rule⟩ := rule
      cases rule
      rw [subst_openIotaLeft, subst_openIotaRight]
      generalize hts : (metaVars (p + 1 + ctors.length + fields.length)).map
        (Presentation.subst τ) = ts
      have hlen : ts.length = p + 1 + ctors.length + fields.length := by
        rw [← hts, List.length_map, length_metaVars]
      have hpLen : (ts.take p).length = p := List.length_take_of_le (by omega)
      have hAfter : (ts.drop p).length = 1 + ctors.length + fields.length := by
        simp only [List.length_drop, hlen]
        omega
      cases hdropP : ts.drop p with
      | nil =>
        rw [hdropP, List.length_nil] at hAfter
        omega
      | cons motive rest =>
        have hrest : rest.length = ctors.length + fields.length := by
          rw [hdropP, List.length_cons] at hAfter
          omega
        have hmsLen : (rest.take ctors.length).length = ctors.length :=
          List.length_take_of_le (by omega)
        have hidx : p + 1 + ctors.length = (ts.take p).length + (1 + ctors.length) := by
          rw [hpLen]; omega
        have hTakePref : ts.take (p + 1 + ctors.length) =
            ts.take p ++ motive :: rest.take ctors.length := by
          rw [← List.take_append_drop p ts, hdropP, hidx, List.take_length_add_append,
            Nat.add_comm 1 ctors.length, List.take_succ_cons, List.take_left' hpLen]
        have hDropArgs : ts.drop (p + 1 + ctors.length) = rest.drop ctors.length := by
          rw [← List.take_append_drop p ts, hdropP, hidx, List.drop_length_add_append,
            Nat.add_comm 1 ctors.length, List.drop_succ_cons]
        have hget : (ts.take p ++ motive :: rest.take ctors.length).getD (p + 1 + i)
            defaultTm = (rest.take ctors.length).getD i defaultTm := by
          have hpos : p + 1 + i = (ts.take p).length + (i + 1) := by rw [hpLen]; omega
          rw [hpos, getD_length_add, List.getD_cons_succ]
        have hic : i < ctors.length := (List.getElem?_eq_some_iff.mp hi).1
        refine ⟨ts.take p, motive, rest.take ctors.length, i, k, fields,
          rest.drop ctors.length, (rest.take ctors.length).getD i defaultTm,
          hpLen, hmsLen, hi, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_drop, hrest]
          omega
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          rfl
        · rw [hTakePref, hDropArgs]
        · rw [hTakePref, hDropArgs, hget]

/-! ## The package -/

/-- The parameterization is the empty one: no parameters, and no open constructors.
This is the branch `parameterDecls` takes. -/
def parameterSimple (d : Datatype Head) : Bool :=
  d.parameters.telescope.count == 0 && d.parameters.constructors.isEmpty

theorem parameterSimple_of_none (d : Datatype Head) (h : d.parameters = .none) :
    parameterSimple d = true := by
  cases d
  cases h
  rfl

theorem none_of_parameterSimple (d : Datatype Head) (h : parameterSimple d = true) :
    d.parameters = .none := by
  cases d with
  | mk _ _ _ _ _ params =>
    cases params with
    | mk tele opens =>
      cases tele with
      | mk count ctx =>
        have parts := Bool.and_eq_true_iff.mp h
        have hz : count = 0 := eq_of_beq parts.1
        have hempty : opens.isEmpty = true := parts.2
        cases hz
        cases ctx
        cases opens with
        | nil => rfl
        | cons _ _ =>
          simp only [List.isEmpty_cons] at hempty
          cases hempty

/-- The computation rules of a datatype. The empty parameterization uses the simple
recursor rules. -/
def parameterComputation (d : Datatype Head) : RootComputation Head :=
  match parameterSimple d with
  | true => iotaComputation d.recursor d.ctors
  | false => openIotaComputation d.recursor d.parameters.telescope.count
      d.parameters.constructors

/-- The schemas of those rules. -/
def parameterSchema (d : Datatype Head) : SchemaFamily Head :=
  match parameterSimple d with
  | true => iotaSchema d.recursor d.ctors
  | false => openIotaSchema d.recursor d.parameters.telescope.count
      d.parameters.constructors

/-- **The rule package of a datatype that may have parameters**, over the rules of a
package: the declared types `parameterDecls`, and the recursor's computation rules. -/
def parameterRules (target : Rules Head) (d : Datatype Head) : Rules Head :=
  { target with
    constantType := parameterDecls d
    computation := parameterComputation d }

/-- The computation rules are presented by the schemas, on either branch. -/
theorem parameter_presents (d : Datatype Head) :
    Presents (parameterComputation d) (parameterSchema d) := by
  cases h : parameterSimple d <;>
    simp only [parameterComputation, parameterSchema, h]
  · exact openIota_presents d.recursor d.parameters.telescope.count d.parameters.constructors
  · exact iota_presents d.recursor d.ctors

/-- **The annotated package of a datatype that may have parameters.** Each computation
step requires the typings of its parameters, its motive, its methods and its fields. -/
def parameterChurch (target : Rules Head) (d : Datatype Head) :
    ChurchRules (parameterRules target d) :=
  ChurchRules.ofSchemas (parameterRules target d) (parameterSchema d) (parameter_presents d)

/-- **No parameters: the rule package is the simple one.** -/
theorem parameterComputation_of_none (d : Datatype Head) (h : d.parameters = .none) :
    parameterComputation d = iotaComputation d.recursor d.ctors := by
  simp only [parameterComputation, parameterSimple_of_none d h]

/-- **No parameters: the declaring package is the simple package.** -/
theorem parameterRules_of_none (target : Rules Head) (d : Datatype Head)
    (h : d.parameters = .none) :
    parameterRules target d =
      inductiveRules target d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse := by
  cases d
  cases h
  rfl

/-- No parameters: the schemas are the simple recursor's schemas. -/
theorem parameterSchema_of_none (d : Datatype Head) (h : d.parameters = .none) :
    @Eq (SchemaFamily Head) (parameterSchema d) (iotaSchema d.recursor d.ctors) := by
  cases d
  cases h
  rfl

/-- No parameters: the annotated packages declare the same constants. -/
theorem parameterChurch_constantType_of_none (target : Rules Head) (d : Datatype Head)
    (h : d.parameters = .none) :
    (parameterChurch target d).constantType =
      (inductiveChurch target d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).constantType := by
  cases d
  cases h
  unfold parameterChurch inductiveChurch ChurchRules.ofSchemas
  rfl

/-- No parameters: the annotated packages have the same root steps. -/
theorem parameterChurch_computation_of_none (target : Rules Head) (d : Datatype Head)
    (h : d.parameters = .none) :
    (parameterChurch target d).computation =
      (inductiveChurch target d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).computation := by
  cases d
  cases h
  unfold parameterChurch inductiveChurch ChurchRules.ofSchemas
  rfl

/-! ## What the package declares -/

/-- The type constant is declared at the type closed over the parameter telescope. -/
theorem parameterDecls_type (d : Datatype Head) :
    parameterDecls d d.type = some (typeConstant d) := by
  cases d with
  | mk T u ctors rec v params =>
    cases params with
    | mk tele opens =>
      cases tele with
      | mk count ctx =>
        simp only [parameterDecls, typeConstant]
        by_cases h : (count == 0 && opens.isEmpty) = true
        · rw [if_pos h]
          simp only [inductiveDecls]
          have parts := Bool.and_eq_true_iff.mp h
          have hz : count = 0 := eq_of_beq parts.1
          have hempty : opens.isEmpty = true := parts.2
          cases hz
          cases ctx
          cases opens with
          | nil => rfl
          | cons _ _ =>
            simp only [List.isEmpty_cons] at hempty
            cases hempty
        · rw [if_neg h, if_pos rfl]

/-- An open constructor, in a parameterization that is not the empty one, is declared
at its type closed over the parameter telescope. -/
theorem parameterDecls_open_ctor {d : Datatype Head} {k : DeclName}
    {fs : List (OpenField Head d.parameters.telescope.count)}
    (openCase : parameterSimple d = false) (notType : k ≠ d.type)
    (found : d.parameters.constructors.find? (fun entry => entry.1 = k) = some (k, fs)) :
    parameterDecls d k =
      some (closeType d.parameters.telescope.context
        (ctorOpen d.type d.parameters.telescope.count fs 0)) := by
  cases d with
  | mk T u _ _ _ params =>
    cases params with
    | mk tele opens =>
      cases tele with
      | mk count ctx =>
        have hcond : (count == 0 && opens.isEmpty) = false := by
          simpa [parameterSimple] using openCase
        have hnot : ¬ ((count == 0 && opens.isEmpty) = true) := by
          intro ht
          rw [hcond] at ht
          cases ht
        simp only [parameterDecls]
        rw [if_neg hnot, if_neg notType, found]

/-- The recursor, in a parameterization that is not the empty one and whose open
constructors do not use the recursor's name, is declared at its type closed over the
parameter telescope. -/
theorem parameterDecls_recursor {d : Datatype Head}
    (openCase : parameterSimple d = false) (notType : d.recursor ≠ d.type)
    (notCtor : d.parameters.constructors.find?
      (fun entry => entry.1 = d.recursor) = none) :
    parameterDecls d d.recursor =
      some (closeType d.parameters.telescope.context
        (recOpen d.type d.motiveUniverse d.parameters.telescope.count
          d.parameters.constructors)) := by
  cases d with
  | mk T u _ rec v params =>
    cases params with
    | mk tele opens =>
      cases tele with
      | mk count ctx =>
        have hcond : (count == 0 && opens.isEmpty) = false := by
          simpa [parameterSimple] using openCase
        have hnot : ¬ ((count == 0 && opens.isEmpty) = true) := by
          intro ht
          rw [hcond] at ht
          cases ht
        simp only [parameterDecls]
        rw [if_neg hnot, if_neg notType]
        simp only [notCtor]
        rw [if_pos trivial]

/-! ## The type constant is a type -/

/-- Closing a type over a telescope is the annotated function type over the annotated
telescope. -/
theorem liftTm_closeType : ∀ {n : Nat} (Γ : Ctx Head n) (C : Tm Head n),
    liftTm (closeType Γ C) = pisCtx (liftCtx Γ) (liftTm C)
  | _, .nil, _ => rfl
  | _, .snoc Γ A, C => liftTm_closeType Γ (.pi A C)

/-- A formed parameter telescope is a formed annotated context. -/
theorem telescopeFormed_ctx {R : Rules Head} {B : ChurchRules R} :
    ∀ {n : Nat} {Γ : Ctx Head n}, TelescopeFormed B Γ → CCtxFormed B (liftCtx Γ)
  | _, .nil, _ => .nil
  | _, .snoc _ _, formed => .snoc (telescopeFormed_ctx formed.1) formed.2

/-- **A formed telescope closes to a type**: a type over the telescope, closed over
it, is a type. -/
theorem telescope_close_isType {L : Type} [LevelOrder L] {R : Rules Head}
    (levels : LevelModel R L) {B : ChurchRules R} {n : Nat} {Γ : Ctx Head n}
    {C : Tm Head n} (tele : TelescopeFormed B Γ)
    (target : CIsType B (liftCtx Γ) (liftTm C)) :
    CIsType B .nil (liftTm (closeType Γ C)) := by
  rw [liftTm_closeType]
  exact pisCtx_formed levels (telescopeFormed_ctx tele) target

/-- **The declared type of the type constant is a type** of the base package. The
constant does not mention the datatype being declared. -/
theorem typeConstant_isType {L : Type} [LevelOrder L] {R : Rules Head}
    (levels : LevelModel R L) {B : ChurchRules R} {d : Datatype Head}
    (hu : R.isUniverse d.typeUniverse)
    (tele : TelescopeFormed B d.parameters.telescope.context) :
    CIsType B .nil (liftTm (typeConstant d)) :=
  telescope_close_isType levels tele
    (CIsType.head_of_universe (P := B) (Γ := liftCtx d.parameters.telescope.context)
      levels hu)

/-! ## The declaring package keeps the names -/

/-- The domains of a context have no abstraction. -/
def domainsLamFree : {n : Nat} → Ctx Head n → Bool
  | _, .nil => true
  | _, .snoc Γ A => domainsLamFree Γ && lamFree A

/-- Closing a type over domains without abstractions keeps it free of abstractions. -/
theorem lamFree_closeType : ∀ {n : Nat} (Γ : Ctx Head n) (C : Tm Head n),
    domainsLamFree Γ = true → lamFree C = true → lamFree (closeType Γ C) = true
  | _, .nil, _, _, body => body
  | _, .snoc Γ A, C, doms, body => by
    have parts := Bool.and_eq_true_iff.mp doms
    exact lamFree_closeType Γ (.pi A C) parts.1 (by
      simp only [lamFree, parts.2, body]
      rfl)

/-- The declared type of the type constant has no abstraction when the parameter
domains have none. -/
theorem typeConstant_lamFree {d : Datatype Head}
    (doms : domainsLamFree d.parameters.telescope.context = true) :
    lamFree (typeConstant d) = true :=
  lamFree_closeType _ _ doms rfl

/-- **A name `parameterDecls` declares is declared by the package.** The
declaring package keeps the user's names: its constant table at such a name is
not empty, so those names are not new in the declaring package. -/
theorem declaring_name_taken (target : Rules Head) (d : Datatype Head) (c : DeclName)
    {T : Tm Head 0} (declared : parameterDecls d c = some T) :
    (parameterChurch target d).constantType c ≠ none := by
  rw [show (parameterChurch target d).constantType c =
      elabDeclarations (parameterDecls d) c from rfl]
  simp only [elabDeclarations, declared, Option.map_some]
  exact Option.some_ne_none _

/-- A declared type without abstractions is elaborated to its annotation. -/
theorem declaring_name_elaborated (target : Rules Head) (d : Datatype Head) (c : DeclName)
    {T : Tm Head 0} (declared : parameterDecls d c = some T) (free : lamFree T = true) :
    (parameterChurch target d).constantType c = some (liftTm T) := by
  rw [show (parameterChurch target d).constantType c =
      elabDeclarations (parameterDecls d) c from rfl]
  exact elabDeclarations_lamFree (parameterDecls d) declared free

/-- **The type constant is declared** at its type closed over the parameter
telescope, elaborated to the annotation of that type when the parameter domains
have no abstraction. -/
theorem declaring_type_elaborated (target : Rules Head) (d : Datatype Head)
    (doms : domainsLamFree d.parameters.telescope.context = true) :
    (parameterChurch target d).constantType d.type = some (liftTm (typeConstant d)) :=
  declaring_name_elaborated target d d.type (parameterDecls_type d) (typeConstant_lamFree doms)

/-- **Fresh names for an instance.** Renaming the type, the constructors and the
recursor meets `NewNames` in a package where each renamed name is undeclared.
The fields are the instance's fields. -/
theorem newNames_renamed {R : Rules Head} {B : ChurchRules R} {T rec : DeclName}
    {ctors : List (DeclName × List (Field Head))} (f : DeclName → DeclName)
    (typeNew : B.constantType (f T) = none) (recNew : B.constantType (f rec) = none)
    (ctorsNew : ∀ entry ∈ ctors, B.constantType (f entry.1) = none) :
    NewNames B (f T) (ctors.map (fun entry => (f entry.1, entry.2))) (f rec) where
  typeNew := typeNew
  recNew := recNew
  ctorsNew := by
    intro entry member
    obtain ⟨orig, mem, rfl⟩ := List.mem_map.mp member
    exact ctorsNew orig mem

/-! ## Dropping a parameter spine -/

/-- The name of a constant, and nothing otherwise. -/
def spineConst? : {n : Nat} → Tm Head n → Option DeclName
  | _, .const k => some k
  | _, _ => none

/-- The constant spine with its first `p` arguments removed. A constructor of the
declaring package applied to its parameters and then its fields becomes the
constructor of the instance applied to the fields. -/
def dropParamSpine (p : Nat) {n : Nat} (t : Tm Head n) : Option (Tm Head n) :=
  match spineConst? (headArgs t).1 with
  | some k =>
    if p ≤ (headArgs t).2.length then
      some (appSpine (.const k) ((headArgs t).2.drop p))
    else none
  | none => none

/-- **Dropping the parameter prefix of a constructor spine** leaves the constructor
applied to the remaining arguments. -/
theorem dropParamSpine_ctor {n : Nat} (p : Nat) (k : DeclName)
    (params args : List (Tm Head n)) (hp : params.length = p) :
    dropParamSpine p (appSpine (.const k) (params ++ args)) =
      some (appSpine (.const k) args) := by
  have hargs :=
    headArgs_appSpine (f := .const k) (by unfold NotApp; split <;> trivial) (params ++ args)
  have hle : p ≤ params.length + args.length := by
    rw [hp]
    exact Nat.le_add_right _ _
  simp [dropParamSpine, hargs, spineConst?, List.drop_left' hp, if_pos hle]

/-- The scrutinee of a substituted parameterized computation rule is a constructor
applied to the parameter instances and the field instances. Dropping the
parameters leaves the constructor applied to the fields. -/
theorem dropParamSpine_openIota {n : Nat} (k : DeclName) (p c a : Nat)
    (τ : Sub Head (p + 1 + c + a) n) (params fieldArgs : List (Tm Head n))
    (hp : params.length = p)
    (hparams : ((metaVars (p + 1 + c + a)).map (Presentation.subst τ)).take p = params)
    (hfields : ((metaVars (p + 1 + c + a)).map (Presentation.subst τ)).drop (p + 1 + c) =
      fieldArgs) :
    dropParamSpine p (appSpine (.const k)
        (((metaVars (p + 1 + c + a)).map (Presentation.subst τ)).take p ++
          ((metaVars (p + 1 + c + a)).map (Presentation.subst τ)).drop (p + 1 + c))) =
      some (appSpine (.const k) fieldArgs) := by
  rw [hparams, hfields]
  exact dropParamSpine_ctor p k params fieldArgs hp

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
