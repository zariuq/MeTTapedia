import Mettapedia.Machines.ContextualSequenceObservation

/-!
# Nested argument observations through caller bindings

A compiled body may select fields without materializing its whole argument.
Each selection follows aliases and retains the frame entered at that point.
The independent specification first obtains a full contextual image and then
selects the requested path. Successful finite image derivations give both
soundness and completeness of the field-by-field interpretation.

The equality observer below compares fully read fields. It is not an
implementation of bidirectional unification on open terms. Native callers
must establish the argument's syntax, frame, current store and lifetime;
sharing a C pointer alone does not establish this representation relation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.ContextualArgumentPaths

open Mettapedia.Machines.ContextualSequenceObservation

variable {Frame Variable Literal : Type}

theorem image_unique {store : Store Frame Variable Literal}
      {source : Value Frame Variable Literal} {first second : Term (Frame × Variable) Literal}
      (left : Image store source first) (right : Image store source second) : first = second := by
    refine Image.rec
      (motive_1 := fun source first _ => ∀ second,
        Image store source second → first = second)
      (motive_2 := fun frame source first _ => ∀ second,
        Images store frame source second → first = second)
      ?_ ?_ ?_ ?_ ?_ ?_ left second right
    · intro frame cell absent second right
      cases right with
        | free => rfl
        | binding present _ => simp [absent] at present
    · intro frame cell entered result present child ih second right
      cases right with
        | free absent => simp [present] at absent
        | @binding _ _ other _ found otherChild =>
            have same : other = entered := by simpa [present] using found.symm
            subst other
            exact ih second otherChild
    · intro frame literal second right
      cases right
      rfl
    · intro frame fields results images ih second right
      cases right with
      | expression otherFields =>
          exact congrArg Mettapedia.Machines.SubstitutionFold.Term.expr (ih _ otherFields)
    · intro frame second right
      cases right
      rfl
    · intro frame field fields result results head tail headIH tailIH second right
      cases right with
        | cons otherHead otherTail =>
            exact congrArg₂ List.cons (headIH _ otherHead) (tailIH _ otherTail)

theorem image_has_root {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {result : Term (Frame × Variable) Literal}
    (image : Image store source result) :
    ∃ target, RootRead store source target ∧ Image store target result := by
  refine Image.rec
    (motive_1 := fun source result _ =>
      ∃ target, RootRead store source target ∧ Image store target result)
    (motive_2 := fun _ fields results _ => fields.length = results.length)
    ?_ ?_ ?_ ?_ ?_ ?_ image
  · intro frame cell absent
    exact ⟨_, .free absent, .free absent⟩
  · intro frame cell entered result found child ih
    obtain ⟨target, root, selected⟩ := ih
    exact ⟨target, .binding found root, selected⟩
  · intro frame literal
    exact ⟨_, .leaf, .leaf⟩
  · intro frame fields results images _
    exact ⟨_, .expression, .expression images⟩
  · intro frame
    rfl
  · intro frame field fields result results _ _ _ ih
    simpa using congrArg Nat.succ ih

theorem root_variable_unbound {store : Store Frame Variable Literal}
    {source target : Value Frame Variable Literal} (read : RootRead store source target) :
    ∀ frame cell, target = ⟨.var cell, frame⟩ → store frame cell = none := by
  induction read with
  | free absent =>
      intro frame cell same
      cases same
      exact absent
  | binding _ _ ih => exact ih
  | leaf => intro frame cell same; cases same
  | expression => intro frame cell same; cases same

theorem expression_has_root {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {results : List (Term (Frame × Variable) Literal)}
    (image : Image store source (.expr results)) :
    ∃ frame fields, RootRead store source ⟨.expr fields, frame⟩ ∧
      Images store frame fields results := by
  obtain ⟨target, root, selected⟩ := image_has_root image
  cases selected with
  | @binding frame cell entered result found _ =>
      have absent := root_variable_unbound root frame cell rfl
      simp [found] at absent
  | expression fields => exact ⟨_, _, root, fields⟩

def atPath {Cell : Type} : Term Cell Literal → List Nat → Option (Term Cell Literal)
  | term, [] => some term
  | .expr fields, index :: later => fields[index]?.bind (fun field => atPath field later)
  | _, _ :: _ => none

inductive Projection (store : Store Frame Variable Literal) :
    Value Frame Variable Literal → List Nat → Value Frame Variable Literal → Prop where
  | root {source target} : RootRead store source target → Projection store source [] target
  | field {source frame fields index selected later target} :
      RootRead store source ⟨.expr fields, frame⟩ → fields[index]? = some selected →
      Projection store ⟨selected, frame⟩ later target →
      Projection store source (index :: later) target

theorem fields_selected {store : Store Frame Variable Literal} {frame : Frame}
    {fields : List (Term Variable Literal)} {results : List (Term (Frame × Variable) Literal)}
    (images : Images store frame fields results) (index : Nat) {field : Term Variable Literal}
    (selected : fields[index]? = some field) :
    ∃ result, results[index]? = some result ∧ Image store ⟨field, frame⟩ result := by
  induction fields generalizing results index with
  | nil => simp at selected
  | cons first later ih =>
      cases images with
      | cons firstImage laterImages =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
              subst field
              exact ⟨_, rfl, firstImage⟩
          | succ index => exact ih laterImages index selected

theorem results_selected {store : Store Frame Variable Literal} {frame : Frame}
    {fields : List (Term Variable Literal)} {results : List (Term (Frame × Variable) Literal)}
    (images : Images store frame fields results) (index : Nat)
    {result : Term (Frame × Variable) Literal} (selected : results[index]? = some result) :
    ∃ field, fields[index]? = some field ∧ Image store ⟨field, frame⟩ result := by
  induction fields generalizing results index with
  | nil => cases images; simp at selected
  | cons first later ih =>
      cases images with
      | cons firstImage laterImages =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
              subst result
              exact ⟨_, rfl, firstImage⟩
          | succ index => exact ih laterImages index selected

theorem projection_sound {store : Store Frame Variable Literal}
    {source target : Value Frame Variable Literal} {path : List Nat}
    (projection : Projection store source path target)
    {whole : Term (Frame × Variable) Literal} (image : Image store source whole) :
    ∃ selected, atPath whole path = some selected ∧ Image store target selected := by
  induction projection generalizing whole with
  | root root => exact ⟨whole, rfl, (root_image_iff root _).mp image⟩
  | @field source frame fields index field later target root selected next ih =>
      have readImage := (root_image_iff root _).mp image
      cases readImage with
      | expression images =>
          obtain ⟨result, atResult, fieldImage⟩ := fields_selected images index selected
          obtain ⟨answer, atAnswer, targetImage⟩ := ih fieldImage
          exact ⟨answer, by simp [atPath, atResult, atAnswer], targetImage⟩

theorem projection_complete {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {whole selected : Term (Frame × Variable) Literal}
    (image : Image store source whole) (path : List Nat)
    (found : atPath whole path = some selected) :
    ∃ target, Projection store source path target ∧ Image store target selected := by
  induction path generalizing source whole with
  | nil =>
      simp only [atPath, Option.some.injEq] at found
      subst selected
      obtain ⟨target, root, selectedImage⟩ := image_has_root image
      exact ⟨target, .root root, selectedImage⟩
  | cons index later ih =>
      cases whole with
      | var cell => simp [atPath] at found
      | leaf literal => simp [atPath] at found
      | expr results =>
          obtain ⟨frame, fields, root, images⟩ := expression_has_root image
          simp only [atPath, Option.bind_eq_some_iff] at found
          obtain ⟨result, atResult, atAnswer⟩ := found
          obtain ⟨field, atField, fieldImage⟩ := results_selected images index atResult
          obtain ⟨target, projected, targetImage⟩ := ih fieldImage atAnswer
          exact ⟨target, .field root atField projected, targetImage⟩

/-- Selecting through contextual arguments is equivalent to selecting after
full substitution, at every finite successful image and every nested path. -/
theorem projection_image_iff {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {whole selected : Term (Frame × Variable) Literal}
    (image : Image store source whole) (path : List Nat) :
    atPath whole path = some selected ↔
      ∃ target, Projection store source path target ∧ Image store target selected := by
  constructor
  · exact projection_complete image path
  · rintro ⟨target, projected, targetImage⟩
    obtain ⟨result, found, resultImage⟩ := projection_sound projected image
    exact found.trans (congrArg some (image_unique resultImage targetImage))

def EqualFields (store : Store Frame Variable Literal) (source : Value Frame Variable Literal)
    (left right : List Nat) : Prop :=
  ∃ result, (∃ target, Projection store source left target ∧ Image store target result) ∧
    (∃ target, Projection store source right target ∧ Image store target result)

/-- In particular, a pure body comparing two ground argument fields has the
same admission on the path-reading tier and the full-image machine route. -/
theorem equal_fields_iff {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {whole : Term (Frame × Variable) Literal}
    (image : Image store source whole) (left right : List Nat) :
    EqualFields store source left right ↔
      ∃ result, atPath whole left = some result ∧ atPath whole right = some result := by
  simp only [EqualFields, ← projection_image_iff image]

/-- A missing path is absent from the current full image, not a fuel,
residency or allocation failure. It does not refute future instantiation or
a unifier's list-view tell. A native provider must retain these distinctions. -/
inductive Report (store : Store Frame Variable Literal) (source : Value Frame Variable Literal)
    (path : List Nat) : Option (Term (Frame × Variable) Literal) → Prop where
  | found {target result} : Projection store source path target →
      Image store target result → Report store source path (some result)
  | missing : (∀ target, ¬ Projection store source path target) → Report store source path none

theorem report_matches_image {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {whole : Term (Frame × Variable) Literal}
    (image : Image store source whole) (path : List Nat)
    {result : Option (Term (Frame × Variable) Literal)} (reported : Report store source path result) :
    atPath whole path = result := by
  cases reported with
  | found projection selected =>
      exact (projection_image_iff image path).mpr ⟨_, projection, selected⟩
  | missing absent =>
      cases found : atPath whole path with
      | none => rfl
      | some result =>
          obtain ⟨target, projected, _⟩ := projection_complete image path found
          exact False.elim (absent target projected)

/-- Finite adaptive pure bodies can choose their next field after observing
an earlier one. Certificates concern the fields actually read, including
missing paths; they need not demand full eager argument substitution. -/
theorem body_read_coherence {Answer : Type} {store : Store Frame Variable Literal}
    {source : Value Frame Variable Literal} {whole : Term (Frame × Variable) Literal}
    (image : Image store source whole)
    (tier : List Nat → Option (Term (Frame × Variable) Literal))
    (body : Mettapedia.Machines.ReadOnlyQuery.Program (List Nat)
      (Option (Term (Frame × Variable) Literal)) Answer)
    (valid : ∀ observed ∈ (Mettapedia.Machines.ReadOnlyQuery.run tier body).reads,
      Report store source observed.1 observed.2) :
    Mettapedia.Machines.ReadOnlyQuery.run (atPath whole) body =
      Mettapedia.Machines.ReadOnlyQuery.run tier body := by
  apply Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees
  intro observed member
  exact report_matches_image image observed.1 (valid observed member)

end Mettapedia.Machines.RuntimePlumbing.ContextualArgumentPaths
