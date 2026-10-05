import Mettapedia.Languages.MM0.Presentation.SupportData
import Mettapedia.Languages.MM0.Kernel.FreeVariables

/-!
# Computational lists for MM0's binder-sensitive free variables

Intermediate lists retain occurrences. Their finite-set interpretation agrees
with the independent free-variable rules, including dependency images and
per-argument binding. This representation does not sort every computed union.
The authored execution connection is a separate theorem over these data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables

open Kernel

def boundImage? (target formal : Context) (arguments : List Preterm) (position : Nat) : Option Nat :=
  if FreeVariables.checkImage target formal arguments position then
    FreeVariables.argumentIndex? arguments position
  else none

theorem boundImage_eq_some_iff (target formal : Context) (arguments : List Preterm)
    (position image : Nat) :
    boundImage? target formal arguments position = some image ↔
      FreeVariables.BoundImage target formal arguments position image := by
  constructor
  · intro accepted
    unfold boundImage? at accepted
    split at accepted
    next checked =>
      obtain ⟨actual, known⟩ := (FreeVariables.checkImage_iff _ _ _ _).mp checked
      have found := (FreeVariables.argumentIndex_eq_some_iff _ _ _).mpr known.argument
      rw [found] at accepted
      have same := Option.some.inj accepted
      subst actual
      exact known
    next => simp at accepted
  · intro known
    have checked := (FreeVariables.checkImage_iff _ _ _ _).mpr ⟨image, known⟩
    simp only [boundImage?, checked, ↓reduceIte]
    exact (FreeVariables.argumentIndex_eq_some_iff _ _ _).mpr known.argument

def images? (target formal : Context) (arguments : List Preterm) : List Nat → Option (List Nat)
  | [] => some []
  | position :: positions => do
      let image ← boundImage? target formal arguments position
      let images ← images? target formal arguments positions
      pure (image :: images)

theorem images_sound {target formal : Context} {arguments : List Preterm}
    {positions images : List Nat} (computed : images? target formal arguments positions = some images) :
    FreeVariables.Images target formal arguments positions.toFinset images.toFinset := by
  induction positions generalizing images with
  | nil =>
      have same : [] = images := Option.some.inj computed
      subst images
      exact ⟨by simp, by simp⟩
  | cons position positions ih =>
      cases first : boundImage? target formal arguments position with
      | none => simp [images?, first] at computed
      | some image =>
          cases tail : images? target formal arguments positions with
          | none => simp [images?, first, tail] at computed
          | some remaining =>
              have same : image :: remaining = images := by simpa [images?, first, tail] using computed
              subst images
              have headKnown := (boundImage_eq_some_iff _ _ _ _ _).mp first
              have tailKnown := ih tail
              constructor
              · intro selected member
                simp only [List.mem_toFinset, List.mem_cons] at member
                rcases member with rfl | member
                · exact ⟨image, headKnown⟩
                · exact tailKnown.defined selected (by simpa using member)
              · intro value
                constructor
                · intro member
                  simp only [List.mem_toFinset, List.mem_cons] at member
                  rcases member with rfl | member
                  · exact ⟨position, by simp, headKnown⟩
                  · obtain ⟨selected, member, known⟩ := (tailKnown.members value).mp (by simpa using member)
                    exact ⟨selected, by simpa using Or.inr member, known⟩
                · rintro ⟨selected, member, known⟩
                  simp only [List.mem_toFinset, List.mem_cons] at member
                  rcases member with rfl | member
                  · have same := Preterm.var.inj (Option.some.inj (headKnown.argument.symm.trans known.argument))
                    simp [same]
                  · have inTail := (tailKnown.members value).mpr ⟨selected, by simpa using member, known⟩
                    simp only [List.mem_toFinset, List.mem_cons]
                    exact Or.inr (by simpa using inTail)

theorem images_complete {target formal : Context} {arguments : List Preterm}
    {positions : List Nat} {result : Finset Nat}
    (known : FreeVariables.Images target formal arguments positions.toFinset result) :
    ∃ images, images? target formal arguments positions = some images ∧ images.toFinset = result := by
  induction positions generalizing result with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      exact (images_sound (target := target) (formal := formal) (arguments := arguments) rfl).selected_eq.symm.trans
        known.selected_eq
  | cons position positions ih =>
      obtain ⟨image, headKnown⟩ := known.defined position (by simp)
      have first := (boundImage_eq_some_iff _ _ _ _ _).mpr headKnown
      have defined : ∀ selected ∈ positions.toFinset,
          ∃ image, FreeVariables.BoundImage target formal arguments selected image := by
        intro selected member
        exact known.defined selected (by simp [member])
      obtain ⟨tailSet, checked⟩ := (FreeVariables.images_defined_iff _ _ _ _).mpr defined
      have tailKnown := (FreeVariables.images_eq_some_iff _ _ _ _ _).mp checked
      obtain ⟨remaining, tail, _⟩ := ih tailKnown
      have computed : images? target formal arguments (position :: positions) = some (image :: remaining) := by
        simp [images?, first, tail]
      exact ⟨image :: remaining, computed, (images_sound computed).selected_eq.symm.trans known.selected_eq⟩

theorem images_meaning (target formal : Context) (arguments : List Preterm) (positions : List Nat) :
    (images? target formal arguments positions).map List.toFinset =
      FreeVariables.images? target formal arguments positions.toFinset := by
  cases computed : images? target formal arguments positions with
  | some images => exact (images_sound computed).eval.symm
  | none =>
      cases checked : FreeVariables.images? target formal arguments positions.toFinset with
      | none => rfl
      | some result =>
          obtain ⟨images, accepted, _⟩ := images_complete ((FreeVariables.images_eq_some_iff _ _ _ _ _).mp checked)
          rw [computed] at accepted
          contradiction

def subtract (source bound : List Nat) : List Nat := source.filter fun index => !bound.contains index

theorem subtract_meaning (source bound : List Nat) :
    (subtract source bound).toFinset = source.toFinset \ bound.toFinset := by
  ext index
  simp [subtract]

def contributions? (target fullFormal : Context) (arguments : List Preterm) :
    Context → List (List Nat) → Option (List Nat)
  | [], [] => some []
  | .bound _ :: rest, _ :: freeLists => contributions? target fullFormal arguments rest freeLists
  | .regular _ dependencies :: rest, free :: freeLists => do
      let bound ← images? target fullFormal arguments (dependencies.sort (· ≤ ·))
      let remaining ← contributions? target fullFormal arguments rest freeLists
      pure (subtract free bound ++ remaining)
  | _, _ => none

theorem contributions_meaning (target fullFormal : Context) (arguments : List Preterm)
    (formal : Context) (freeLists : List (List Nat)) :
    (contributions? target fullFormal arguments formal freeLists).map List.toFinset =
      FreeVariables.contributions? target fullFormal arguments formal (freeLists.map List.toFinset) := by
  induction formal generalizing freeLists with
  | nil => cases freeLists <;> rfl
  | cons binder formal ih =>
      cases freeLists with
      | nil => cases binder <;> rfl
      | cons free freeLists =>
          cases binder with
          | bound sort => exact ih freeLists
          | regular sort dependencies =>
              have mapped := images_meaning target fullFormal arguments (dependencies.sort (· ≤ ·))
              simp only [Finset.sort_toFinset] at mapped
              cases image : images? target fullFormal arguments (dependencies.sort (· ≤ ·)) <;>
                cases tail : contributions? target fullFormal arguments formal freeLists <;>
                simp [contributions?, FreeVariables.contributions?, ← mapped, ← ih freeLists,
                  image, tail, subtract_meaning]

def indicesSpine? (signature : TermSignature) (context : Context) :
    Preterm → List Preterm → List (List Nat) → Option (List Nat)
  | .var index, [], [] => ComputationalSupport.indices? context (.var index)
  | .var _, _, _ => none
  | .term symbol, arguments, freeLists => do
      let declaration ← signature symbol
      if Substitution.checkArguments signature context arguments declaration.arguments then
        let contributed ← contributions? context declaration.arguments arguments declaration.arguments freeLists
        let returned ← images? context declaration.arguments arguments (declaration.dependencies.sort (· ≤ ·))
        pure (contributed ++ returned)
      else none
  | .app function argument, arguments, freeLists => do
      let free ← indicesSpine? signature context argument [] []
      indicesSpine? signature context function (argument :: arguments) (free :: freeLists)

theorem spine_meaning (signature : TermSignature) (context : Context) (source : Preterm)
    (arguments : List Preterm) (freeLists : List (List Nat)) :
    (indicesSpine? signature context source arguments freeLists).map List.toFinset =
      Preterm.freeSpine? signature context source arguments (freeLists.map List.toFinset) := by
  induction source generalizing arguments freeLists with
  | var index =>
      cases arguments with
      | nil =>
          cases freeLists with
          | nil => exact ComputationalSupport.indices_meaning context (.var index)
          | cons => rfl
      | cons => rfl
  | term symbol =>
      cases known : signature symbol with
      | none => simp [indicesSpine?, Preterm.freeSpine?, known]
      | some declaration =>
          cases typed : Substitution.checkArguments signature context arguments declaration.arguments with
          | false => simp [indicesSpine?, Preterm.freeSpine?, known, typed]
          | true =>
              have contributed := contributions_meaning context declaration.arguments arguments
                declaration.arguments freeLists
              have returned := images_meaning context declaration.arguments arguments
                (declaration.dependencies.sort (· ≤ ·))
              simp only [Finset.sort_toFinset] at returned
              cases contribution : contributions? context declaration.arguments arguments declaration.arguments freeLists <;>
                cases image : images? context declaration.arguments arguments (declaration.dependencies.sort (· ≤ ·)) <;>
                simp [indicesSpine?, Preterm.freeSpine?, known, typed, ← contributed, ← returned,
                  contribution, image]
  | app function argument ihFunction ihArgument =>
      have childMeaning : (indicesSpine? signature context argument [] []).map List.toFinset =
          Preterm.freeSpine? signature context argument [] [] := ihArgument [] []
      cases child : indicesSpine? signature context argument [] [] with
      | none =>
          simp [indicesSpine?, Preterm.freeSpine?, ← childMeaning, child]
      | some free =>
          simpa [indicesSpine?, Preterm.freeSpine?, ← childMeaning, child] using
            ihFunction (argument :: arguments) (free :: freeLists)

def indices? (signature : TermSignature) (context : Context) (source : Preterm) : Option (List Nat) :=
  indicesSpine? signature context source [] []

theorem indices_meaning (signature : TermSignature) (context : Context) (source : Preterm) :
    (indices? signature context source).map List.toFinset = Preterm.freeVariables? signature context source :=
  spine_meaning signature context source [] []

theorem indices_sound {signature : TermSignature} {context : Context} {source : Preterm} {indices : List Nat}
    (computed : indices? signature context source = some indices) :
    Preterm.FreeVars signature context source indices.toFinset := by
  apply Preterm.freeSpine_sound
  change Preterm.freeVariables? signature context source = some indices.toFinset
  rw [← indices_meaning, computed]
  rfl

theorem indices_complete {signature : TermSignature} {context : Context} {source : Preterm} {free : Finset Nat}
    (derived : Preterm.FreeVars signature context source free) :
    ∃ indices, indices? signature context source = some indices ∧ indices.toFinset = free := by
  have meaning := indices_meaning signature context source
  rw [(Preterm.freeVariables_eq_some_iff _ _ _ _).mpr derived] at meaning
  cases computed : indices? signature context source with
  | none => simp [computed] at meaning
  | some indices => exact ⟨indices, rfl, by simpa [computed] using meaning⟩

theorem indices_refusal_iff (signature : TermSignature) (context : Context) (source : Preterm) :
    indices? signature context source = none ↔ ¬ ∃ free, Preterm.FreeVars signature context source free := by
  constructor
  · intro refused ⟨free, known⟩
    obtain ⟨indices, computed, _⟩ := indices_complete known
    rw [refused] at computed
    contradiction
  · intro noFree
    cases computed : indices? signature context source with
    | none => rfl
    | some indices => exact False.elim (noFree ⟨indices.toFinset, indices_sound computed⟩)

namespace Controls

theorem bound_images_keep_order_and_duplicates :
    images? [.bound 0, .bound 0] [.bound 0, .bound 0] [.var 1, .var 0] [1, 0, 1] = some [0, 1, 0] := by
  decide

theorem regular_formal_is_not_a_binder :
    images? [.bound 0] [.regular 0 ∅] [.var 0] [0] = none := by decide

theorem same_sort_regular_target_is_not_a_bound_image :
    images? [.regular 0 ∅] [.bound 0] [.var 0] [0] = none := by decide

theorem wrong_sort_bound_image_refuses :
    images? [.bound 1] [.bound 0] [.var 0] [0] = none := by decide

theorem missing_image_refuses : images? [.bound 0] [.bound 0] [] [0] = none := by decide

theorem all_bound_occurrences_are_removed : subtract [0, 1, 0, 2, 1] [0] = [1, 2, 1] := by decide

theorem a_bound_argument_does_not_contribute_itself :
    contributions? [.bound 0] [.bound 0] [.var 0] [.bound 0] [[0]] = some [] := by decide

theorem an_undeclared_binding_keeps_occurrences_free :
    contributions? [.bound 0] [.bound 0, .regular 0 ∅] [.var 0, .var 0]
      [.bound 0, .regular 0 ∅] [[0], [0]] = some [0] := by
  simp only [contributions?, Finset.sort_empty]
  decide

theorem a_declared_binding_removes_its_argument_occurrences :
    contributions? [.bound 0] [.bound 0, .regular 0 {0}] [.var 0, .var 0]
      [.bound 0, .regular 0 {0}] [[0], [0]] = some [] := by
  simp only [contributions?, Finset.sort_singleton]
  decide

theorem binding_does_not_remove_other_variables :
    contributions? [.bound 0, .bound 0] [.bound 0, .regular 0 {0}] [.var 0, .var 1]
      [.bound 0, .regular 0 {0}] [[0], [0, 1, 1]] = some [1, 1] := by
  simp only [contributions?, Finset.sort_singleton]
  decide

private def context : Context := [.bound 0, .bound 0, .regular 1 {0, 1}]

private def signature : TermSignature
  | 0 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 1 => some ⟨[.bound 0, .regular 1 ∅], 1, ∅⟩
  | 2 => some ⟨[.bound 0], 1, {0}⟩
  | _ => none

theorem complete_expression_removes_only_declared_binding :
    (indices? signature context (.applyArgs (.term 0) [.var 0, .var 2])).map List.toFinset = some {1} := by
  rw [indices_meaning]
  decide

theorem removing_the_binding_declaration_changes_free_variables :
    (indices? signature context (.applyArgs (.term 1) [.var 0, .var 2])).map List.toFinset = some {0, 1} := by
  rw [indices_meaning]
  decide

theorem returned_bound_dependency_contributes :
    (indices? signature context (.app (.term 2) (.var 1))).map List.toFinset = some {1} := by
  rw [indices_meaning]
  decide

theorem nested_binders_compose :
    (indices? signature context (.applyArgs (.term 0)
      [.var 1, .applyArgs (.term 0) [.var 0, .var 2]])).map List.toFinset = some ∅ := by
  rw [indices_meaning]
  decide

theorem complete_expression_does_not_ignore_an_invalid_child :
    indices? signature context (.applyArgs (.term 0) [.var 0, .var 9]) = none := by
  apply (indices_refusal_iff _ _ _).mpr
  exact (Preterm.freeVariables_none_iff _ _ _).mp (by decide)

theorem partial_application_does_not_have_a_free_variable_result :
    indices? signature context (.app (.term 0) (.var 0)) = none := by
  apply (indices_refusal_iff _ _ _).mpr
  exact (Preterm.freeVariables_none_iff _ _ _).mp (by decide)

end Controls

end Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables
