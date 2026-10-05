import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RecursionEquations

/-!
# A definition by structural recursion has a set model

A function `f : Π (t : T). M` on a declared datatype, defined by one equation for each
constructor whose right side calls `f` at the constructor's recursive fields
(`recursionEquations`), has a value in the set tower: the function that the recursion of the
datatype's set gives, with the right sides as its methods. No term is written for it, and no
check of termination is made beyond the form of the equations: recursive calls at the
recursive fields only.

**The value** (`recursionValue`). A right side is given as a body over the fields of its
constructor and a hypothesis for each recursive field (`methodCtx`). Read in the model, the
body is a function of the field values and of the results at the recursive fields
(`bodyMethod`, a `methodValue`). The recursion of the carrier with these methods
(`recursionFun`) is a function on the set of `T`, and `recursionValue` is its traced graph.

**Typing and computation**, at an assignment that reads the datatype (`InductiveReading`) and
is a set model of the package in which the bodies are typed, for a datatype whose constructor
names are distinct (the recursion tells the constructors apart by the codes of their names):

* an environment of a method's context is a list of field values that fit and of results in
  the result family at the recursive fields (`sat_methodCtx`);
* so each body gives a method of the recursion (`bodyMethod_mem`), the recursion's values lie
  in the result family (`recursionFun_mem`), and the value lies in the set of
  `Π (t : T). M` (`recursionValue_mem`);
* at a constructor value the recursion gives the body at the field values and the results at
  the recursive fields (`recursionFun_constructor`);
* **each equation holds** (`recursionEquation_valid`): at an environment of the constructor's
  fields, the defined constant at the constructor form and the body with the recursive calls
  in place of the hypotheses have one value.

The value reads only the names of the package in which the motive, the field types and the
bodies are typed (`recursionValue_congr`).

**The theorem** (`recursion_setModel`): let a package have a set model at every assignment
that agrees with a given one on the names it declares, and a reading of a declared datatype
with distinct constructor names at each of them. A new constant defined by structural
recursion on that datatype, with result family and bodies typed in the package, gives a
package with a set model at every assignment that agrees, on the names it declares, with the
base assignment extended by the recursion's value. So definitions and declarations can follow
one another, and the package is consistent (`recursion_no_closed_inhabitant`).

Positive examples: the doubling of a number and the append of two lists as definitions by
recursion over declared datatypes (`ObjectRecursiveDefinitions.lean`, in the executable model
of the MeTTa candidate). Negative example: an equation that calls the function at the same
argument is not of this form, and `bad ⟶ suc bad` has no set model
(`ObjectAppendByEquations.lean`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (ctorTele appSpine recPositions wkN
  recPositions_spec getD_of_lt)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)
open ZFSetInductive (Fits constructorValue carrier recFun mapRec nameCode)

universe u

local notation "DeclField" => TypedEquality.Normalization.Field

variable {Head : Type} (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-! ## Lists and environments -/

/-- The environment of one variable is the empty environment extended by its value. -/
theorem env_one (x : ZFSet.{u}) : (fun _ : Fin 1 => x) = extend (Fin.elim0 : Env.{u} 0) x := by
  funext i
  refine Fin.cases rfl (fun j => j.elim0) i

/-- Mapping commutes with reading a list at a position inside it. -/
theorem getD_map_of_lt {α β : Type*} (g : α → β) {l : List α} {j : Nat} (below : j < l.length)
    (d : α) (d' : β) : (l.map g).getD j d' = g (l.getD j d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem below]
  rfl

/-- The values of a function at the recursive arguments are its values at the recursive
positions. -/
theorem mapRec_positions (g : ZFSet.{u} → ZFSet.{u}) :
    ∀ (fields : List (DeclField Head)) (args : List ZFSet.{u}), args.length = fields.length →
      mapRec g (fields.map (fieldSig heads consts)) args =
        (recPositions fields).map fun p => g (args.getD p ∅)
  | [], [], _ => rfl
  | [], _ :: _, length => nomatch length
  | _ :: _, [], length => nomatch length
  | .recursive :: fs, a :: as, length => by
    show g a :: mapRec g (fs.map (fieldSig heads consts)) as = _
    rw [mapRec_positions g fs as (Nat.succ.inj length)]
    show _ = (0 :: (recPositions fs).map (· + 1)).map fun p => g ((a :: as).getD p ∅)
    rw [List.map_cons, List.map_map]
    rfl
  | .closed F :: fs, a :: as, length => by
    show mapRec g (fs.map (fieldSig heads consts)) as = _
    rw [mapRec_positions g fs as (Nat.succ.inj length)]
    show _ = ((recPositions fs).map (· + 1)).map fun p => g ((a :: as).getD p ∅)
    rw [List.map_map]
    rfl

/-- A recursive position is the position of a recursive field. -/
theorem recPosition_mem {fields : List (DeclField Head)} {p : Nat}
    (member : p ∈ recPositions fields) :
    p < fields.length ∧ fields.getD p .recursive = .recursive := by
  obtain ⟨q, below, rfl⟩ := List.getElem_of_mem member
  exact recPositions_spec fields q below

/-! ## The context of a method in the model -/

/-- The value of the result type at a field, in the context of a method: the result family
at the field's value. -/
theorem ev_resultAt (M : CTm Head 1) {a r p : Nat} (below : p < a) (args recs : List ZFSet.{u})
    (length : args.length = a) :
    ev heads consts (resultAt M a r p) (envOf (args ++ recs) (a + r)) =
      ev heads consts M fun _ => args.getD p ∅ := by
  rw [resultAt, ev_subst]
  congr 1
  funext i
  rw [dif_pos below]
  show (args ++ recs).getD (a + r - 1 - (r + (a - 1 - p))) ∅ = args.getD p ∅
  rw [show a + r - 1 - (r + (a - 1 - p)) = p by omega, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]

/-- **An environment satisfies the context of a method** exactly when its field values fit
the constructor's fields and each result lies in the result family at the value of its
recursive field. -/
theorem sat_methodCtx (T : DeclName) (M : CTm Head 1) (fields : List (DeclField Head))
    (args recs : List ZFSet.{u}) (length : args.length = fields.length) :
    ∀ r, r ≤ (recPositions fields).length →
      (Sat heads consts (methodCtx T M fields r) (envOf (args ++ recs) (fields.length + r)) ↔
        Fits (consts T) (fields.map (fieldSig heads consts)) args ∧
          ∀ q, q < r → recs.getD q ∅ ∈
            ev heads consts M fun _ => args.getD ((recPositions fields).getD q 0) ∅)
  | 0, _ => by
    show Sat heads consts (liftCtx (ctorTele T fields)) (envOf (args ++ recs) fields.length) ↔ _
    rw [envOf_append args recs fields.length (le_of_eq length.symm),
      sat_ctorTele heads consts T fields args length]
    exact ⟨fun fits => ⟨fits, fun q below => absurd below (Nat.not_lt_zero q)⟩,
      fun both => both.1⟩
  | r + 1, bound => by
    have smaller : r ≤ (recPositions fields).length := Nat.le_of_succ_le bound
    have inside : r < (recPositions fields).length := Nat.lt_of_succ_le bound
    have position : (recPositions fields).getD r 0 < fields.length := by
      rw [getD_of_lt 0 inside]
      exact (recPositions_spec fields r inside).1
    have newest : (args ++ recs).getD (fields.length + r) ∅ = recs.getD r ∅ := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), length, Nat.add_sub_cancel_left]
    have result := ev_resultAt heads consts M (r := r) position args recs length
    show Sat heads consts ((methodCtx T M fields r).snoc
        (resultAt M fields.length r ((recPositions fields).getD r 0)))
      (envOf (args ++ recs) (fields.length + r + 1)) ↔ _
    rw [envOf_succ, sat_snoc, sat_methodCtx T M fields args recs length r smaller, newest, result]
    constructor
    · rintro ⟨⟨fits, earlier⟩, last⟩
      refine ⟨fits, fun q below => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp below with before | rfl
      · exact earlier q before
      · exact last
    · rintro ⟨fits, all⟩
      exact ⟨⟨fits, fun q below => all q (Nat.lt_succ_of_lt below)⟩, all r (Nat.lt_succ_self r)⟩

variable {heads consts}

/-- **The constructor form in the context of a method** has the constructor's value at the
field values. -/
theorem ev_ctorAt {T k : DeclName} {fields : List (DeclField Head)}
    (value : consts k = telescopeGraph heads consts (liftCtx (ctorTele T fields)) fun η =>
      constructorValue (nameCode k) (envList η))
    {args : List ZFSet.{u}} (fits : Fits (consts T) (fields.map (fieldSig heads consts)) args)
    (recs : List ZFSet.{u}) (r : Nat) :
    ev heads consts (ctorAt k fields.length r) (envOf (args ++ recs) (fields.length + r)) =
      constructorValue (nameCode k) args := by
  have length : args.length = fields.length := ((fits_iff heads consts fields args).mp fits).1
  have restricted : envOf (args ++ recs) (fields.length + r) ∘ wkN r =
      envOf args fields.length := by
    funext j
    have := j.isLt
    show (args ++ recs).getD (fields.length + r - 1 - (j.val + r)) ∅ =
      args.getD (fields.length - 1 - j.val) ∅
    rw [show fields.length + r - 1 - (j.val + r) = fields.length - 1 - j.val by omega,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  rw [ctorAt, liftTm_rename, ev_rename, restricted, ev_appSpine, ev_metaVars,
    envList_envOf args fields.length (le_of_eq length.symm), ← length, List.take_length]
  exact ctor_apply value fits

/-! ## The recursion -/

variable (heads consts) (T : DeclName) (M : CTm Head 1)
  (ctors : List (DeclName × List (DeclField Head)))
  (body : (k : DeclName) → (fields : List (DeclField Head)) →
    CTm Head (fields.length + (recPositions fields).length))

/-- The set of the result family at a value. -/
noncomputable def resultSet (x : ZFSet.{u}) : ZFSet.{u} := ev heads consts M fun _ => x

/-- **The method of a constructor read from its body**: the function of the field values and
of the results at the recursive fields that the body's value gives. -/
noncomputable def bodyMethod (fields : List (DeclField Head))
    (b : CTm Head (fields.length + (recPositions fields).length)) : ZFSet.{u} :=
  methodValue (consts T) (resultSet heads consts M) (fields.map (fieldSig heads consts))
    fun args results =>
      ev heads consts b (envOf (args ++ results) (fields.length + (recPositions fields).length))

/-- The methods of the constructors, in order. -/
noncomputable def bodyMethods : List ZFSet.{u} :=
  ctors.map fun entry => bodyMethod heads consts T M entry.2 (body entry.1 entry.2)

/-- **The function the recursion defines** on the set of the datatype. -/
noncomputable def recursionFun : ZFSet.{u} → ZFSet.{u} :=
  recFun (sig := signature heads consts ctors)
    (methodStep (bodyMethods heads consts T M ctors body))

/-- **The value of a definition by structural recursion**: the traced graph of the recursion
over the set of the datatype. -/
noncomputable def recursionValue : ZFSet.{u} :=
  traceLam (graph (consts T) (recursionFun heads consts T M ctors body))

variable {heads consts T M ctors body}

theorem bodyMethods_getD {i : Nat} {k : DeclName} {fields : List (DeclField Head)}
    (entry : ctors[i]? = some (k, fields)) :
    (bodyMethods heads consts T M ctors body).getD i ∅ =
      bodyMethod heads consts T M fields (body k fields) := by
  rw [bodyMethods, List.getD_eq_getElem?_getD, List.getElem?_map, entry]
  rfl

section Model

variable {R : Rules Head} {B : ChurchRules R} {v : Head} {rec : DeclName}

/-- **A typed body gives a method of the recursion.** -/
theorem bodyMethod_mem (model : SetModel heads consts B) {k : DeclName}
    {fields : List (DeclField Head)}
    (ctorValue : consts k = telescopeGraph heads consts (liftCtx (ctorTele T fields)) fun η =>
      constructorValue (nameCode k) (envList η))
    {b : CTm Head (fields.length + (recPositions fields).length)}
    (typed : CTyped B (methodCtx T M fields (recPositions fields).length) b
      (M.subst fun _ => ctorAt k fields.length (recPositions fields).length)) :
    bodyMethod heads consts T M fields b ∈
      caseSet (consts T) (resultSet heads consts M) (nameCode k)
        (fields.map (fieldSig heads consts)) := by
  refine methodValue_mem fun args fits results members => ?_
  have length : args.length = fields.length := ((fits_iff heads consts fields args).mp fits).1
  rw [mapRec_positions heads consts (resultSet heads consts M) fields args length] at members
  obtain ⟨sameLength, pointwise⟩ := List.forall₂_iff_get.mp members
  rw [List.length_map] at sameLength
  have sat : Sat heads consts (methodCtx T M fields (recPositions fields).length)
      (envOf (args ++ results) (fields.length + (recPositions fields).length)) := by
    refine (sat_methodCtx heads consts T M fields args results length _ (Nat.le_refl _)).mpr
      ⟨fits, fun q below => ?_⟩
    have inResults : q < results.length := sameLength ▸ below
    have inMapped : q < ((recPositions fields).map fun p =>
        resultSet heads consts M (args.getD p ∅)).length := by
      rw [List.length_map]
      exact below
    have member := pointwise q inResults inMapped
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map] at member
    have resultHere : results.getD q ∅ = results[q] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inResults]
      rfl
    rw [resultHere, getD_of_lt 0 below]
    exact member
  have member := CDerivable.sound model typed _ sat
  rw [ev_subst] at member
  have atConstructor : (fun _ : Fin 1 => ev heads consts
      (ctorAt k fields.length (recPositions fields).length)
      (envOf (args ++ results) (fields.length + (recPositions fields).length))) =
      fun _ => constructorValue (nameCode k) args :=
    funext fun _ => ev_ctorAt ctorValue fits results _
  rw [atConstructor] at member
  exact member

/-- **The recursion's values lie in the result family.** -/
theorem recursionFun_mem (model : SetModel heads consts B) (names : (ctors.map (·.1)).Nodup)
    (reading : InductiveReading heads consts T v ctors rec)
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T M fields (recPositions fields).length) (body k fields)
          (M.subst fun _ => ctorAt k fields.length (recPositions fields).length))
    {x : ZFSet.{u}} (member : x ∈ consts T) :
    recursionFun heads consts T M ctors body x ∈ resultSet heads consts M x := by
  rw [reading.type] at member
  refine recursion_mem (signature_distinct heads consts names) (fun i c atIndex => ?_) member
  obtain ⟨k, fields, entry, rfl⟩ := exists_of_signature_getElem? heads consts atIndex
  rw [bodyMethods_getD entry, ← reading.type]
  exact bodyMethod_mem model (reading.ctor entry) (bodies entry)

/-- **The value of the definition lies in the set of its declared type.** -/
theorem recursionValue_mem (model : SetModel heads consts B) (names : (ctors.map (·.1)).Nodup)
    (reading : InductiveReading heads consts T v ctors rec)
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T M fields (recPositions fields).length) (body k fields)
          (M.subst fun _ => ctorAt k fields.length (recPositions fields).length)) :
    recursionValue heads consts T M ctors body ∈
      ev heads consts (.pi (.const T) M) Fin.elim0 := by
  show traceLam (graph (consts T) (recursionFun heads consts T M ctors body)) ∈
    tracePiSet (consts T) fun x => ev heads consts M (extend Fin.elim0 x)
  refine traceLam_graph_mem fun x member => ?_
  rw [← env_one]
  exact recursionFun_mem model names reading bodies member

/-- **The recursion at a constructor value**: the body at the field values and the results at
the recursive fields. -/
theorem recursionFun_constructor (model : SetModel heads consts B)
    (names : (ctors.map (·.1)).Nodup) (reading : InductiveReading heads consts T v ctors rec)
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T M fields (recPositions fields).length) (body k fields)
          (M.subst fun _ => ctorAt k fields.length (recPositions fields).length))
    {i : Nat} {k : DeclName} {fields : List (DeclField Head)}
    (entry : ctors[i]? = some (k, fields)) {args : List ZFSet.{u}}
    (fits : Fits (consts T) (fields.map (fieldSig heads consts)) args) :
    recursionFun heads consts T M ctors body (constructorValue (nameCode k) args) =
      ev heads consts (body k fields)
        (envOf (args ++ (recPositions fields).map fun p =>
            recursionFun heads consts T M ctors body (args.getD p ∅))
          (fields.length + (recPositions fields).length)) := by
  have length : args.length = fields.length := ((fits_iff heads consts fields args).mp fits).1
  have atIndex := signature_getElem? heads consts entry
  have fitsCarrier : Fits (carrier (signature heads consts ctors))
      (fields.map (fieldSig heads consts)) args := reading.type ▸ fits
  have results : List.Forall₂ (fun y D => y ∈ D)
      (mapRec (recursionFun heads consts T M ctors body) (fields.map (fieldSig heads consts)) args)
      (mapRec (resultSet heads consts M) (fields.map (fieldSig heads consts)) args) :=
    mapRec_mem fits fun x member => recursionFun_mem model names reading bodies member
  have unfolded : recursionFun heads consts T M ctors body (constructorValue (nameCode k) args) =
      applyList ((bodyMethods heads consts T M ctors body).getD i ∅)
        (args ++ mapRec (recursionFun heads consts T M ctors body)
          (fields.map (fieldSig heads consts)) args) :=
    ZFSetInductive.recFun_constructor (signature_distinct heads consts names)
      (methodStep (bodyMethods heads consts T M ctors body)) atIndex fitsCarrier
  rw [unfolded, bodyMethods_getD entry, bodyMethod, applyList_methodValue _ fits results,
    mapRec_positions heads consts _ fields args length]

/-- **An equation of the definition holds in the model**: at an environment of the
constructor's fields, the defined constant at the constructor form and the body with the
recursive calls in place of the hypotheses have one value. -/
theorem recursionEquation_valid (model : SetModel heads consts B)
    (names : (ctors.map (·.1)).Nodup) (reading : InductiveReading heads consts T v ctors rec)
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T M fields (recPositions fields).length) (body k fields)
          (M.subst fun _ => ctorAt k fields.length (recPositions fields).length))
    {f : DeclName} (value : consts f = recursionValue heads consts T M ctors body)
    {i : Nat} {k : DeclName} {fields : List (DeclField Head)}
    (entry : ctors[i]? = some (k, fields)) (η : Env.{u} fields.length)
    (sat : Sat heads consts (liftCtx (ctorTele T fields)) η) :
    ev heads consts
        (.app (.const f) (liftTm (appSpine (.const k) (metaVars fields.length)))) η =
      ev heads consts ((body k fields).subst (callSub f fields)) η := by
  have length : (envList η).length = fields.length := envList_length η
  have fits : Fits (consts T) (fields.map (fieldSig heads consts)) (envList η) := by
    have listed := sat
    rw [← envOf_envList η] at listed
    exact (sat_ctorTele heads consts T fields (envList η) length).mp listed
  have members := (fits_iff heads consts fields (envList η)).mp fits
  -- The value of the defined constant at a member of the datatype's set.
  have applied : ∀ x ∈ consts T,
      traceApp (consts f) x = recursionFun heads consts T M ctors body x := by
    intro x member
    rw [value, recursionValue, traceApp_graph_beta _ member]
  -- The left side.
  have ctorHere : ev heads consts (liftTm (appSpine (.const k) (metaVars fields.length))) η =
      constructorValue (nameCode k) (envList η) := by
    rw [ev_appSpine, ev_metaVars]
    exact ctor_apply (reading.ctor entry) fits
  have inCarrier : constructorValue (nameCode k) (envList η) ∈ consts T := by
    rw [reading.type]
    exact ZFSetInductive.constructor_mem_carrier (signature_getElem? heads consts entry)
      (reading.type ▸ fits)
  have left : ev heads consts
      (.app (.const f) (liftTm (appSpine (.const k) (metaVars fields.length)))) η =
      recursionFun heads consts T M ctors body (constructorValue (nameCode k) (envList η)) := by
    show traceApp (consts f) (ev heads consts
      (liftTm (appSpine (.const k) (metaVars fields.length))) η) = _
    rw [ctorHere]
    exact applied _ inCarrier
  -- The right side: the values of the field variables and of the recursive calls.
  have fieldValues : ((metaVars fields.length).map liftTm).map
      (fun t : CTm Head fields.length => ev heads consts t η) = envList η := by
    rw [List.map_map]
    exact ev_metaVars heads consts η
  have fieldAt : ∀ p, p < fields.length →
      ev heads consts (liftTm ((metaVars fields.length).getD p
        Presentation.TypedEquality.Normalization.defaultTm)) η = (envList η).getD p ∅ := by
    intro p below
    have inVars : p < (metaVars (Head := Head) fields.length).length := by
      rw [length_metaVars]
      exact below
    have mapped := getD_map_of_lt (fun t : Tm Head fields.length => ev heads consts (liftTm t) η)
      inVars Presentation.TypedEquality.Normalization.defaultTm (∅ : ZFSet.{u})
    rw [ev_metaVars heads consts η] at mapped
    exact mapped.symm
  have callValues : ((recPositions fields).map fun p => (CTm.app (.const f)
        (liftTm ((metaVars fields.length).getD p
          Presentation.TypedEquality.Normalization.defaultTm)) : CTm Head fields.length)).map
      (fun t : CTm Head fields.length => ev heads consts t η) =
      (recPositions fields).map fun p =>
        recursionFun heads consts T M ctors body ((envList η).getD p ∅) := by
    rw [List.map_map]
    refine List.map_congr_left fun p member => ?_
    obtain ⟨below, recursive⟩ := recPosition_mem member
    show traceApp (consts f) (ev heads consts (liftTm ((metaVars fields.length).getD p
      Presentation.TypedEquality.Normalization.defaultTm)) η) = _
    rw [fieldAt p below]
    refine applied _ ?_
    have inField := members.2 p below
    rw [recursive] at inField
    exact inField
  have allValues : (callTerms f fields).map (fun t : CTm Head fields.length =>
      ev heads consts t η) =
      envList η ++ (recPositions fields).map fun p =>
        recursionFun heads consts T M ctors body ((envList η).getD p ∅) := by
    rw [callTerms, List.map_append, fieldValues, callValues]
  have right : (fun j => ev heads consts (callSub f fields j) η) =
      envOf (envList η ++ (recPositions fields).map fun p =>
          recursionFun heads consts T M ctors body ((envList η).getD p ∅))
        (fields.length + (recPositions fields).length) := by
    funext j
    have inTerms : fields.length + (recPositions fields).length - 1 - j.val <
        (callTerms f fields).length := by
      have := j.isLt
      rw [length_callTerms]
      omega
    show ev heads consts ((callTerms f fields).getD
      (fields.length + (recPositions fields).length - 1 - j.val) (.const .anonymous)) η = _
    rw [← getD_map_of_lt (fun t : CTm Head fields.length => ev heads consts t η) inTerms
      (.const .anonymous) (∅ : ZFSet.{u}), allValues]
    rfl
  rw [left, ev_subst, right]
  exact recursionFun_constructor model names reading bodies entry fits

end Model

/-! ## The value reads only the names of the package before the definition -/

section Congruence

variable {R : Rules Head} {B : ChurchRules R} {consts' : DeclName → ZFSet.{u}}

/-- **The value of a definition by structural recursion is the same at two assignments that
agree on the names of the package** in which the datatype is declared and the result family,
the field types and the bodies are typed. -/
theorem recursionValue_congr (same : ∀ c, B.constantType c ≠ none → consts c = consts' c)
    (typeDeclared : B.constantType T ≠ none) {w : Head}
    (motive : CTyped B (.snoc .nil (.const T)) M (.head w))
    (fieldsFormed : FieldsFormed B ctors)
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T M fields (recPositions fields).length) (body k fields)
          (M.subst fun _ => ctorAt k fields.length (recPositions fields).length)) :
    recursionValue heads consts T M ctors body = recursionValue heads consts' T M ctors body := by
  have typeSame : consts T = consts' T := same T typeDeclared
  have fieldSigs : ∀ entry ∈ ctors,
      entry.2.map (fieldSig heads consts) = entry.2.map (fieldSig heads consts') := by
    intro entry member
    refine List.map_congr_left fun field memberField => ?_
    cases field with
    | recursive => rfl
    | closed F =>
      obtain ⟨u, -, typed⟩ := fieldsFormed entry member F memberField
      show ZFSetInductive.Field.ofSet _ = ZFSetInductive.Field.ofSet _
      rw [CDerivable.ev_congr_declared heads same typed Fin.elim0]
  have signatures : signature heads consts ctors = signature heads consts' ctors :=
    List.map_congr_left fun entry member =>
      congrArg (ZFSetInductive.Constructor.mk _) (fieldSigs entry member)
  have results : resultSet heads consts M = resultSet heads consts' M :=
    funext fun x => CDerivable.ev_congr_declared heads same motive _
  have methods : bodyMethods heads consts T M ctors body =
      bodyMethods heads consts' T M ctors body := by
    refine List.map_congr_left fun entry member => ?_
    obtain ⟨i, found⟩ := List.getElem?_of_mem member
    have typed := bodies (i := i) (k := entry.1) (fields := entry.2) found
    show methodValue (consts T) (resultSet heads consts M) (entry.2.map (fieldSig heads consts))
        (fun args results => ev heads consts (body entry.1 entry.2)
          (envOf (args ++ results) (entry.2.length + (recPositions entry.2).length))) =
      methodValue (consts' T) (resultSet heads consts' M)
        (entry.2.map (fieldSig heads consts'))
        (fun args results => ev heads consts' (body entry.1 entry.2)
          (envOf (args ++ results) (entry.2.length + (recPositions entry.2).length)))
    rw [typeSame, results, fieldSigs entry member]
    congr 1
    funext args recs
    exact CDerivable.ev_congr_declared heads same typed _
  show traceLam (graph (consts T) (recFun (sig := signature heads consts ctors)
      (methodStep (bodyMethods heads consts T M ctors body)))) =
    traceLam (graph (consts' T) (recFun (sig := signature heads consts' ctors)
      (methodStep (bodyMethods heads consts' T M ctors body))))
  rw [typeSame, signatures, methods]

end Congruence

/-! ## The set model of a definition by structural recursion -/

section Theorem

variable {R : Rules Head} {base : DeclName → ZFSet.{u}} {v : Head} {rec f : DeclName}

/-- **A definition by structural recursion on a declared datatype has a set model.** The
package before the definition has a set model, and a reading of the datatype, at every
assignment that agrees with the base assignment on the names it declares; the constructor
names of the datatype are distinct; the defined name is new to the package; and the result
family, the closed field types and the bodies are typed in it. The
model is at every assignment that agrees, on the names the package with the definition
declares, with the base assignment extended by the value of the recursion. -/
theorem recursion_setModel (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (names : (ctors.map (·.1)).Nodup)
    (readings : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        InductiveReading heads consts T v ctors rec)
    (new : B.constantType f = none) (typeDeclared : B.constantType T ≠ none) {w : Head}
    (motive : CTyped B (.snoc .nil (.const T)) M (.head w))
    (fieldsFormed : FieldsFormed B ctors)
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T M fields (recPositions fields).length) (body k fields)
          (M.subst fun _ => ctorAt k fields.length (recPositions fields).length))
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withDefinition B f (.pi (.const T) M)
        (recursionEquations f T ctors body)).constantType c ≠ none →
      consts c = Function.update base f (recursionValue heads base T M ctors body) c) :
    SetModel heads consts
      (withDefinition B f (.pi (.const T) M) (recursionEquations f T ctors body)) := by
  have valueAt : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        recursionValue heads base T M ctors body = recursionValue heads consts T M ctors body :=
    fun consts agreesBase => recursionValue_congr
      (fun c declared => (agreesBase c declared).symm) typeDeclared motive fieldsFormed bodies
  refine definition_setModel_of_value B baseModel new (recursionValue heads base T M ctors body)
    (fun consts agreesBase _ => ?_) (fun consts agreesBase atDefined e member η sat => ?_)
    consts agrees
  · rw [valueAt consts agreesBase]
    exact recursionValue_mem (baseModel consts agreesBase) names (readings consts agreesBase)
      bodies
  · obtain ⟨i, k, fields, entry, rfl⟩ := mem_recursionEquations member
    exact recursionEquation_valid (baseModel consts agreesBase) names
      (readings consts agreesBase) bodies (atDefined.trans (valueAt consts agreesBase)) entry η
      sat

/-- **Consistency**: a closed type whose set is empty has no closed term in a package with a
definition by structural recursion. -/
theorem recursion_no_closed_inhabitant (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (names : (ctors.map (·.1)).Nodup)
    (readings : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
        InductiveReading heads consts T v ctors rec)
    (new : B.constantType f = none) (typeDeclared : B.constantType T ≠ none) {w : Head}
    (motive : CTyped B (.snoc .nil (.const T)) M (.head w))
    (fieldsFormed : FieldsFormed B ctors)
    (bodies : ∀ {i : Nat} {k : DeclName} {fields : List (DeclField Head)},
      ctors[i]? = some (k, fields) →
        CTyped B (methodCtx T M fields (recPositions fields).length) (body k fields)
          (M.subst fun _ => ctorAt k fields.length (recPositions fields).length))
    {A : CTm Head 0}
    (empty : ∀ z, z ∉ ev heads
      (Function.update base f (recursionValue heads base T M ctors body)) A Fin.elim0)
    (t : CTm Head 0) :
    ¬ CTyped (withDefinition B f (.pi (.const T) M) (recursionEquations f T ctors body)) .nil
      t A :=
  CDerivable.no_closed_inhabitant
    (recursion_setModel B baseModel names readings new typeDeclared motive fieldsFormed bodies
      _ fun _ _ => rfl)
    empty t

end Theorem

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
