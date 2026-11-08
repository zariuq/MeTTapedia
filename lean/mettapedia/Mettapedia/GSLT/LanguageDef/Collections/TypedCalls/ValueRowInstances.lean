import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRows

/-!
# First-path instances of hereditary row-free values

Selection precedes argument evaluation. `heCheck_exact` proves that a value
with no expression-subject row anywhere preserves exactly the intersection
chosen by its first matching typing. No uniqueness premise is needed: the
first complete Cartesian path already chooses each argument's first viable
typing, so evaluating that argument cannot narrow the path again.

`unique_typing_instance` derives the native unique-typing case. The private
projection theorem derives rectangularity from separated source formal scopes
before discarding an instance's private coordinates. Correlated incoming
constraints invalidate a spelling-only disjointness argument.

These are results over the existing set-of-ground-solutions `ValueRows`
semantics. They do not identify two concrete binding records, encode the
native type store, or prove a source-to-C value interpretation by themselves.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRowInstances

open ValueRows Classical

private theorem find_refine {α : Type} (xs : List α) (p q : α → Bool) (a : α)
    (selected : xs.find? p = some a) (narrow : ∀ x, q x = true → p x = true)
    (accepts : q a = true) : xs.find? q = some a := by
  induction xs with
  | nil => simp at selected
  | cons x xs ih =>
      cases hp : p x with
      | true =>
          have same : x = a := by simpa [hp] using selected
          subst a
          simp [accepts]
      | false =>
          have hq : q x = false := by
            cases h : q x with
            | false => rfl
            | true => have := narrow x h; simp [hp] at this
          simp only [List.find?_cons, hp] at selected
          simpa [hq] using ih selected

private theorem findSome_consMap {α β : Type} (xs : List α) (p : α → Bool)
    (rest : Option (List β)) (f : α → β) :
    xs.findSome? (fun x => if p x then rest.map (f x :: ·) else none) =
      (xs.find? p).bind (fun x => rest.map (f x :: ·)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hx : p x <;> cases rest <;> simp_all

open Classical in
noncomputable def pointOK : List (Ty Empty) → List TySet → Bool
  | [], [] => true
  | value :: values, type_ :: types => decide (value ∈ type_) && pointOK values types
  | _, _ => false

open Classical in
noncomputable def pointFind : List (Ty Empty) → List (List TySet) → Option (List TySet)
  | [], [] => some []
  | value :: values, types :: lists =>
      (types.find? fun type_ => decide (value ∈ type_)).bind fun type_ =>
        (pointFind values lists).map (type_ :: ·)
  | _, _ => none

theorem find_choices_point (values : List (Ty Empty)) (lists : List (List TySet)) :
    (choices lists).find? (pointOK values) = pointFind values lists := by
  classical
  induction values generalizing lists with
  | nil =>
      cases lists with
      | nil => rfl
      | cons types lists =>
          simp [choices, List.find?_flatMap, List.find?_map, pointOK, pointFind,
            Function.comp_def]
  | cons value values ih =>
      cases lists with
      | nil => rfl
      | cons types lists =>
          rw [choices, List.find?_flatMap]
          have each (type_ : TySet) :
              ((choices lists).map (type_ :: ·)).find? (pointOK (value :: values)) =
                if value ∈ type_ then (pointFind values lists).map (type_ :: ·) else none := by
            rw [List.find?_map]
            by_cases member : value ∈ type_
            · simpa [Function.comp_def, pointOK, member] using
                congrArg (fun result => result.map (type_ :: ·)) (ih lists)
            · simp [Function.comp_def, pointOK, member]
          simp_rw [each]
          simpa [pointFind] using
            findSome_consMap types (fun type_ => decide (value ∈ type_)) (pointFind values lists) id

def PointFirst : List (Ty Empty) → List TySet → List (List TySet) → Prop
  | [], [], [] => True
  | value :: values, chosen :: rest, types :: lists =>
      types.find? (fun type_ => decide (value ∈ type_)) = some chosen ∧
        PointFirst values rest lists
  | _, _, _ => False

theorem pointFind_coordinates (values : List (Ty Empty)) (lists : List (List TySet))
    (chosen : List TySet) (selected : pointFind values lists = some chosen) :
    PointFirst values chosen lists := by
  classical
  induction values generalizing lists chosen with
  | nil =>
      cases lists <;> simp [pointFind] at selected
      cases selected
      simp [PointFirst]
  | cons value values ih =>
      cases lists with
      | nil => simp [pointFind] at selected
      | cons types lists =>
          simp only [pointFind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at selected
          obtain ⟨type_, first, rest, later, rfl⟩ := selected
          exact ⟨first, ih lists rest later⟩

theorem pointOK_iff (values : List (Ty Empty)) (chosen : List TySet) :
    pointOK values chosen = true ↔ List.Forall₂ (fun value type_ => value ∈ type_) values chosen := by
  classical
  induction values generalizing chosen with
  | nil => cases chosen <;> simp [pointOK]
  | cons value values ih => cases chosen <;> simp [pointOK, ih]

/-- Pointwise first membership at every admissible ground observation
determines the first type meeting the entire observation set. -/
theorem firstMeet_of_points (types : List TySet) (E S : TySet) (nonempty : E.Nonempty)
    (first : ∀ value ∈ E, types.find? (fun type_ => decide (value ∈ type_)) = some S) :
    firstMeet types E = some S ∧ E ⊆ S := by
  classical
  have subset : E ⊆ S := by
    intro value member
    have membership : decide (value ∈ S) = true :=
      List.find?_some (p := fun type_ : TySet => decide (value ∈ type_)) (first value member)
    exact of_decide_eq_true membership
  refine ⟨?_, subset⟩
  induction types with
  | nil => obtain ⟨value, member⟩ := nonempty; simpa using first value member
  | cons head tail ih =>
      by_cases meets : (head ∩ E).Nonempty
      · obtain ⟨value, hHead, hE⟩ := meets
        have same : head = S := by simpa [hHead] using first value hE
        subst S
        unfold firstMeet
        simp [show (head ∩ E).Nonempty from ⟨value, hHead, hE⟩]
      · have notMember : ∀ value ∈ E, value ∉ head := fun value hE hHead =>
          meets ⟨value, hHead, hE⟩
        have later : ∀ value ∈ E, tail.find? (fun type_ => decide (value ∈ type_)) = some S := by
          intro value hE
          simpa [notMember value hE] using first value hE
        simpa [firstMeet, meets] using ih later

theorem path_nonempty_iff (Fs : List (Ty String)) (R : Ty String) (chosen : List TySet) (E : TySet) :
    (pathSols Fs R chosen E).Nonempty ↔
      (readAt R (pathSols Fs R chosen Set.univ) ∩ E).Nonempty := by
  constructor
  · rintro ⟨assignment, constraints, expected⟩
    exact ⟨R.bind assignment, ⟨assignment, ⟨constraints, Set.mem_univ _⟩, rfl⟩, expected⟩
  · rintro ⟨value, ⟨assignment, ⟨constraints, _⟩, rfl⟩, expected⟩
    exact ⟨assignment, constraints, expected⟩

/-- First selection over the mapped range typings is the same path
selection, not a fresh choice after the argument is delivered. -/
theorem firstMeet_path (fns : List FnTy) (lists : List (List TySet)) (E S : TySet)
    (chosen : firstMeet (appTyps fns lists) E = some S) :
    ∃ path, firstPath fns lists E = some path ∧
      readAt path.1.2 (pathSols path.1.1 path.1.2 path.2 Set.univ) = S := by
  unfold firstMeet appTyps at chosen
  rw [List.find?_map] at chosen
  have predicates :
      ((fun type_ : TySet => decide (type_ ∩ E).Nonempty) ∘
        (fun path : FnTy × List TySet => readAt path.1.2 (pathSols path.1.1 path.1.2 path.2 Set.univ))) =
      (fun path => decide (pathSols path.1.1 path.1.2 path.2 E).Nonempty) := by
    funext path
    simp only [Function.comp_apply, ← path_nonempty_iff]
  rw [predicates, Option.map_eq_some_iff] at chosen
  exact chosen

theorem firstPath_choices (fns : List FnTy) (lists : List (List TySet)) (E : TySet)
    (path : FnTy × List TySet) (selected : firstPath fns lists E = some path) :
    (choices lists).find? (fun chosen => decide (pathSols path.1.1 path.1.2 chosen E).Nonempty) =
      some path.2 := by
  induction fns with
  | nil => simp [firstPath, paths] at selected
  | cons fn fns ih =>
      unfold firstPath at selected
      simp only [paths, List.flatMap_cons, List.find?_append, List.find?_map] at selected
      cases first : (choices lists).find?
        (fun chosen => decide (pathSols fn.1 fn.2 chosen E).Nonempty) with
      | none =>
          apply ih
          simpa [firstPath, paths, Function.comp_def, first] using selected
      | some chosen =>
          have same : (fn, chosen) = path := by
            simpa [Function.comp_def, first] using selected
          cases same
          exact first

theorem forall₂_bind_point (Fs : List (Ty String)) (chosen : List TySet) (assignment : Asg) :
    List.Forall₂ (fun F S => F.bind assignment ∈ S) Fs chosen ↔
      pointOK (Fs.map (fun F => F.bind assignment)) chosen = true := by
  rw [pointOK_iff, List.forall₂_map_left_iff]

/-- Each ground solution of the first complete path sees the same first
typing at every argument position. Earlier private choices would otherwise
have yielded an earlier complete path. -/
theorem firstPath_pointwise (fns : List FnTy) (lists : List (List TySet)) (E : TySet)
    (path : FnTy × List TySet) (selected : firstPath fns lists E = some path) :
    ∀ assignment ∈ pathSols path.1.1 path.1.2 path.2 E,
      PointFirst (path.1.1.map (fun F => F.bind assignment)) path.2 lists := by
  intro assignment satisfying
  have complete := firstPath_choices fns lists E path selected
  have narrower : ∀ chosen,
      pointOK (path.1.1.map (fun F => F.bind assignment)) chosen = true →
        decide (pathSols path.1.1 path.1.2 chosen E).Nonempty = true := by
    intro chosen matching
    apply decide_eq_true
    exact ⟨assignment, (forall₂_bind_point _ _ _).mpr matching, satisfying.2⟩
  have atChosen : pointOK (path.1.1.map (fun F => F.bind assignment)) path.2 = true :=
    (forall₂_bind_point _ _ _).mp satisfying.1
  have selectedPoint := find_refine (choices lists) _ _ path.2 complete narrower atChosen
  rw [find_choices_point] at selectedPoint
  exact pointFind_coordinates _ _ _ selectedPoint

theorem readAt_path (Fs : List (Ty String)) (R : Ty String) (chosen : List TySet) (E : TySet) :
    readAt R (pathSols Fs R chosen E) = readAt R (pathSols Fs R chosen Set.univ) ∩ E := by
  ext value
  constructor
  · rintro ⟨assignment, ⟨constraints, expected⟩, rfl⟩
    exact ⟨⟨assignment, ⟨constraints, Set.mem_univ _⟩, rfl⟩, expected⟩
  · rintro ⟨⟨assignment, ⟨constraints, _⟩, rfl⟩, expected⟩
    exact ⟨assignment, ⟨constraints, expected⟩, rfl⟩

mutual
/-- A row-free value whose first applicable typing already contains every
expected possibility is evaluation-stable at that whole instance set. -/
theorem eval_first_cover : ∀ (value : Val), Plain value → ∀ (E S : TySet),
    E.Nonempty → firstMeet (orUndef (typs value)) E = some S → E ⊆ S →
      eval value E = some E
  | .leaf types, _, E, S, _, chosen, covered => by
      rw [eval]
      simp only [typs] at chosen
      rw [chosen, Option.map_some]
      congr 1
      exact Set.inter_eq_right.mpr covered
  | .node rows fn fns args, plain, E, S, nonempty, chosen, covered => by
      obtain ⟨noRows, plainArgs⟩ := plain
      subst noRows
      have typings : orUndef (typs (.node [] fn fns args)) = appTyps (fn :: fns) (argTyps args) := by
        simp only [typs, List.nil_append]
        exact orUndef_of_ne_nil (appTyps_ne_nil fn fns args)
      rw [typings] at chosen
      obtain ⟨path, selected, selectedType⟩ := firstMeet_path (fn :: fns) (argTyps args) E S chosen
      have pathExists : (pathSols path.1.1 path.1.2 path.2 E).Nonempty := by
        have valid := List.find?_some selected
        exact of_decide_eq_true valid
      have stableArgs := evalArgs_first args plainArgs path.1.1 path.2
        (pathSols path.1.1 path.1.2 path.2 E) pathExists
        (firstPath_pointwise (fn :: fns) (argTyps args) E path selected)
      rcases path with ⟨functionType, chosenTypes⟩
      rw [eval_node, selected]
      dsimp only
      rw [stableArgs, Option.map_some, readAt_path, selectedType,
        Set.inter_eq_right.mpr covered]
/-- The first complete Cartesian path has already selected each argument's
first compatible typing. Re-evaluating its row-free values cannot further
narrow the shared assignment set. -/
theorem evalArgs_first : ∀ (args : List Val), PlainArgs args →
    ∀ (Fs : List (Ty String)) (chosen : List TySet) (assignments : Set Asg),
      assignments.Nonempty →
      (∀ assignment ∈ assignments,
        PointFirst (Fs.map (fun F => F.bind assignment)) chosen (argTyps args)) →
        evalArgs args Fs assignments = some assignments
  | [], _, Fs, chosen, assignments, nonempty, first => by
      obtain ⟨assignment, member⟩ := nonempty
      have shape := first assignment member
      cases Fs <;> cases chosen <;> simp [PointFirst, argTyps] at shape
      rfl
  | arg :: args, plain, Fs, chosen, assignments, nonempty, first => by
      obtain ⟨plainArg, plainArgs⟩ := plain
      obtain ⟨assignment, member⟩ := nonempty
      have shape := first assignment member
      cases Fs with
      | nil => cases chosen <;> simp [PointFirst, argTyps] at shape
      | cons F Fs =>
          cases chosen with
          | nil => simp [PointFirst, argTyps] at shape
          | cons S chosen =>
              have expectedExists : (readAt F assignments).Nonempty := ⟨F.bind assignment, assignment, member, rfl⟩
              have points : ∀ value ∈ readAt F assignments,
                  (orUndef (typs arg)).find? (fun type_ => decide (value ∈ type_)) = some S := by
                rintro value ⟨current, occurs, rfl⟩
                exact (first current occurs).1
              obtain ⟨selected, covered⟩ := firstMeet_of_points _ _ _ expectedExists points
              have stableArg := eval_first_cover arg plainArg _ _ expectedExists selected covered
              have noChange : {current | current ∈ assignments ∧ F.bind current ∈ readAt F assignments} =
                  assignments := by
                ext current
                exact ⟨And.left, fun occurs => ⟨occurs, current, occurs, rfl⟩⟩
              rw [evalArgs_cons, stableArg]
              dsimp only
              rw [noChange]
              apply evalArgs_first args plainArgs Fs chosen assignments ⟨assignment, member⟩
              intro current occurs
              exact (first current occurs).2
end

theorem firstMeet_refine (types : List TySet) (E S : TySet)
    (chosen : firstMeet types E = some S) : firstMeet types (S ∩ E) = some S := by
  have meets := (firstMeet_some chosen).2
  apply find_refine types (fun type_ => decide (type_ ∩ E).Nonempty) _ S chosen
  · intro type_ accepted
    obtain ⟨value, inType, _, inExpected⟩ := of_decide_eq_true accepted
    exact decide_eq_true ⟨value, inType, inExpected⟩
  · obtain ⟨value, inType, inExpected⟩ := meets
    exact decide_eq_true ⟨value, inType, inType, inExpected⟩

/-- Hereditary absence of expression rows gives the exact instance, not
only acceptance: argument evaluation leaves the first typing's meet intact.
No uniqueness of matching typings is required for this statement. -/
theorem heCheck_exact (value : Val) (plain : Plain value) (E : TySet) :
    heCheck value E = (firstMeet (orUndef (typs value)) E).map (· ∩ E) := by
  unfold heCheck
  cases chosen : firstMeet (orUndef (typs value)) E with
  | none => rfl
  | some S =>
      simp only [Option.bind_some, Option.map_some]
      exact eval_first_cover value plain (S ∩ E) S (firstMeet_some chosen).2
        (firstMeet_refine _ _ _ chosen) Set.inter_subset_left

/-- A single matching typing occurrence determines exactly the instance
left after evaluation, not just a type which was initially possible. -/
theorem unique_typing_instance (value : Val) (plain : Plain value) (E S : TySet)
    (unique : (orUndef (typs value)).filter (fun type_ => decide (type_ ∩ E).Nonempty) = [S]) :
    heCheck value E = some (S ∩ E) := by
  have selected := congrArg List.head? unique
  simp only [List.head?_filter, List.head?_singleton] at selected
  rw [heCheck_exact value plain E]
  change (List.find? (fun type_ => decide (type_ ∩ E).Nonempty) (orUndef (typs value))).map
    (· ∩ E) = _
  rw [selected]
  rfl

/-- Instantiating private variables does not change an observation which
does not read them. Correlation in the incoming solution set is handled
separately by `pathSols_paste`; syntax disjointness alone is not enough. -/
def paste (names : List String) (inside outside : Asg) : Asg :=
  fun name => if name ∈ names then inside name else outside name

def Supported (type_ : Ty String) (names : List String) : Prop :=
  ∀ name ∈ type_.vars, name ∈ names

def Apart (type_ : Ty String) (names : List String) : Prop :=
  ∀ name ∈ type_.vars, name ∉ names

theorem bind_paste_inside {type_ : Ty String} {names : List String}
    (supported : Supported type_ names) (inside outside : Asg) :
    type_.bind (paste names inside outside) = type_.bind inside :=
  Ty.bind_congr type_ fun name occurs => if_pos (supported name occurs)

theorem bind_paste_outside {type_ : Ty String} {names : List String}
    (apart : Apart type_ names) (inside outside : Asg) :
    type_.bind (paste names inside outside) = type_.bind outside :=
  Ty.bind_congr type_ fun name occurs => if_neg (apart name occurs)

theorem constraints_paste (names : List String) (inside outside : Asg) :
    ∀ (Fs : List (Ty String)) (chosen : List TySet),
      (∀ F ∈ Fs, Supported F names ∨ Apart F names) →
      List.Forall₂ (fun F S => F.bind inside ∈ S) Fs chosen →
      List.Forall₂ (fun F S => F.bind outside ∈ S) Fs chosen →
      List.Forall₂ (fun F S => F.bind (paste names inside outside) ∈ S) Fs chosen
  | [], [], _, .nil, .nil => .nil
  | F :: Fs, S :: chosen, separated, .cons first rest, .cons first' rest' => by
      refine .cons ?_ (constraints_paste names inside outside Fs chosen
        (fun formal member => separated formal (List.mem_cons_of_mem _ member)) rest rest')
      rcases separated F (by simp) with supported | apart
      · rwa [bind_paste_inside supported]
      · rwa [bind_paste_outside apart]

/-- Fresh, independently scoped formals earn the rectangular solution-set
property: private coordinates of one valid instance can be combined with
the retained coordinates of another. -/
theorem pathSols_paste (Fs : List (Ty String)) (R : Ty String) (chosen : List TySet)
    (E : TySet) (names : List String)
    (separated : ∀ F ∈ Fs, Supported F names ∨ Apart F names)
    (rangeApart : Apart R names) (inside outside : Asg)
    (insideValid : inside ∈ pathSols Fs R chosen E)
    (outsideValid : outside ∈ pathSols Fs R chosen E) :
    paste names inside outside ∈ pathSols Fs R chosen E := by
  refine ⟨constraints_paste names inside outside Fs chosen separated insideValid.1 outsideValid.1, ?_⟩
  rw [bind_paste_outside rangeApart]
  exact outsideValid.2

/-- A nonempty refinement of one private formal changes neither the range
nor any other disjoint type observation. The solution-set closure used here
is derived above from the source path's separate formal scopes. -/
theorem private_refinement_observation (Fs : List (Ty String)) (R F O : Ty String)
    (chosen : List TySet) (E J : TySet)
    (separated : ∀ formal ∈ Fs, Supported formal F.vars ∨ Apart formal F.vars)
    (rangeApart : Apart R F.vars) (observationApart : Apart O F.vars)
    (nonempty : ∃ assignment ∈ pathSols Fs R chosen E, F.bind assignment ∈ J) :
    readAt O {assignment | assignment ∈ pathSols Fs R chosen E ∧ F.bind assignment ∈ J} =
      readAt O (pathSols Fs R chosen E) := by
  ext observed
  constructor
  · rintro ⟨assignment, ⟨valid, _⟩, same⟩
    exact ⟨assignment, valid, same⟩
  · rintro ⟨outside, outsideValid, same⟩
    obtain ⟨inside, insideValid, refinement⟩ := nonempty
    refine ⟨paste F.vars inside outside, ⟨pathSols_paste Fs R chosen E F.vars separated rangeApart
      inside outside insideValid outsideValid, ?_⟩, ?_⟩
    · rwa [bind_paste_inside (fun _ occurs => occurs)]
    · rw [bind_paste_outside observationApart]
      exact same

namespace Controls

def number : Ty Empty := .sym "Number"
def string : Ty Empty := .sym "String"
def alternativeLeaf : Val := .leaf [{number}, {string}]

theorem first_of_many_is_not_an_arbitrary_instance :
    heCheck alternativeLeaf Set.univ = some {number} := by
  rw [heCheck_exact alternativeLeaf (by trivial)]
  have first : firstMeet [{number}, {string}] Set.univ = some {number} := by
    apply firstMeet_of_head rfl
    exact ⟨number, rfl, Set.mem_univ _⟩
  simp only [alternativeLeaf, typs, orUndef, first, Option.map_some, Set.inter_univ]

theorem row_on_a_descendant_invalidates_exactness :
    heCheck ValueRows.Controls.value ValueRows.Controls.lists ≠
      (firstMeet (orUndef (typs ValueRows.Controls.value)) ValueRows.Controls.lists).map
        (· ∩ ValueRows.Controls.lists) := by
  rw [ValueRows.Controls.value_check]
  obtain ⟨S, first, _, _⟩ := firstMeet_spec ValueRows.Controls.value_accepts
  rw [first]
  simp

def a : Ty String := .var "a"
def b : Ty String := .var "b"
def numberAssignment : Asg := fun _ => number

theorem private_refinement_keeps_other_instances :
    readAt b {assignment | assignment ∈ pathSols [a, b] b [Set.univ, Set.univ] Set.univ ∧
      a.bind assignment ∈ ({number} : TySet)} =
    readAt b (pathSols [a, b] b [Set.univ, Set.univ] Set.univ) := by
  apply private_refinement_observation
  · intro formal occurs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at occurs
    rcases occurs with rfl | rfl
    · exact Or.inl (fun _ member => member)
    · right; simp [Apart, a, b]
  · simp [Apart, a, b]
  · simp [Apart, a, b]
  · exact ⟨numberAssignment, ⟨by simp [a, b], Set.mem_univ _⟩, rfl⟩

def correlated : Set Asg := {assignment | assignment "a" = assignment "b"}

/-- Disjoint names do not remove a correlation already present in the
incoming constraints. Native record projection must preserve that history. -/
theorem disjoint_names_alone_are_insufficient :
    readAt b {assignment | assignment ∈ correlated ∧ a.bind assignment ∈ ({number} : TySet)} ≠
      readAt b correlated := by
  intro same
  have before : string ∈ readAt b correlated := ⟨fun _ => string, rfl, rfl⟩
  rw [← same] at before
  obtain ⟨assignment, ⟨correlation, privateNumber⟩, observedString⟩ := before
  have both : number = string := by
    change assignment "a" = assignment "b" at correlation
    change assignment "a" = number at privateNumber
    change assignment "b" = string at observedString
    exact privateNumber.symm.trans (correlation.trans observedString)
  exact (by decide : number ≠ string) both

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRowInstances
