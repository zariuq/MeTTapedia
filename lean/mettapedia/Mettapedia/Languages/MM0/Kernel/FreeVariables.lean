import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Union

/-!
# MM0 binder-sensitive free variables

A regular argument contributes its free variables after removing the images
of the bound formal variables on which that argument is declared to depend.
Return dependencies contribute those bound images independently. The two
contributions are joined by union.

The evaluator follows the binary application spine, checking exact saturation
and argument types at its term head. Dependency images must name bound formal
slots and bound target variables of the matching sort. The independent rules
retain these conditions; no fixed traversal depth is imposed.

This computation differs from complete occurrence support. A bound argument
does not contribute merely because it occurs, and a bound formal does not bind
an occurrence in a regular argument unless that argument declares the dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

namespace FreeVariables

/-- One declared bound slot is replaced by a target bound variable of its sort. -/
inductive BoundImage (target formal : Context) (arguments : List Preterm)
    (position image : Nat) : Prop where
  | intro {sort : Nat} : formal[position]? = some (.bound sort) →
      arguments[position]? = some (.var image) →
      target[image]? = some (.bound sort) → BoundImage target formal arguments position image

def checkImage (target formal : Context) (arguments : List Preterm) (position : Nat) : Bool :=
  match formal[position]?, arguments[position]? with
  | some (.bound sort), some (.var image) => decide (target[image]? = some (.bound sort))
  | _, _ => false

theorem checkImage_iff (target formal : Context) (arguments : List Preterm) (position : Nat) :
    checkImage target formal arguments position = true ↔
      ∃ image, BoundImage target formal arguments position image := by
  cases formalLookup : formal[position]? with
  | none =>
      constructor
      · simp [checkImage, formalLookup]
      · rintro ⟨image, proof⟩; cases proof with
        | intro lookup _ _ => simp [formalLookup] at lookup
  | some binder =>
      cases binder with
      | regular sort dependencies =>
          constructor
          · simp [checkImage, formalLookup]
          · rintro ⟨image, proof⟩; cases proof with
            | intro lookup _ _ => simp [formalLookup] at lookup
      | bound sort =>
          cases argumentLookup : arguments[position]? with
          | none =>
              constructor
              · simp [checkImage, formalLookup, argumentLookup]
              · rintro ⟨image, proof⟩; cases proof with
                | intro _ lookup _ => simp [argumentLookup] at lookup
          | some argument =>
              cases argument with
              | term symbol =>
                  constructor
                  · simp [checkImage, formalLookup, argumentLookup]
                  · rintro ⟨image, proof⟩; cases proof with
                    | intro _ lookup _ => simp [argumentLookup] at lookup
              | app function argument =>
                  constructor
                  · simp [checkImage, formalLookup, argumentLookup]
                  · rintro ⟨image, proof⟩; cases proof with
                    | intro _ lookup _ => simp [argumentLookup] at lookup
              | var image =>
                  constructor
                  · intro checked
                    exact ⟨image, .intro formalLookup argumentLookup
                      (by simpa [checkImage, formalLookup, argumentLookup] using checked)⟩
                  · rintro ⟨other, proof⟩
                    cases proof with
                    | intro knownFormal knownArgument knownTarget =>
                        have sameSort := Binder.bound.inj (Option.some.inj
                          (formalLookup.symm.trans knownFormal))
                        have sameImage := Preterm.var.inj (Option.some.inj
                          (argumentLookup.symm.trans knownArgument))
                        subst other
                        subst sameSort
                        simpa [checkImage, formalLookup, argumentLookup] using knownTarget

def argumentIndex? (arguments : List Preterm) (position : Nat) : Option Nat :=
  match arguments[position]? with
  | some (.var image) => some image
  | _ => none

theorem argumentIndex_eq_some_iff (arguments : List Preterm) (position image : Nat) :
    argumentIndex? arguments position = some image ↔ arguments[position]? = some (.var image) := by
  cases lookup : arguments[position]? with
  | none => simp [argumentIndex?, lookup]
  | some argument => cases argument <;> simp [argumentIndex?, lookup]

def selectedImages (arguments : List Preterm) (dependencies : Finset Nat) : Finset Nat :=
  dependencies.biUnion fun position => (argumentIndex? arguments position).toFinset

theorem mem_selectedImages (arguments : List Preterm) (dependencies : Finset Nat) (image : Nat) :
    image ∈ selectedImages arguments dependencies ↔
      ∃ position ∈ dependencies, arguments[position]? = some (.var image) := by
  simp [selectedImages, Finset.mem_biUnion, argumentIndex_eq_some_iff]

/-- The exact image set, with every requested dependency resolved successfully. -/
structure Images (target formal : Context) (arguments : List Preterm)
    (dependencies images : Finset Nat) : Prop where
  defined : ∀ position ∈ dependencies, ∃ image, BoundImage target formal arguments position image
  members : ∀ image, image ∈ images ↔
    ∃ position ∈ dependencies, BoundImage target formal arguments position image

theorem BoundImage.argument {target formal : Context} {arguments : List Preterm}
    {position image : Nat} (proof : BoundImage target formal arguments position image) :
    arguments[position]? = some (.var image) := by
  cases proof with
  | intro _ lookup _ => exact lookup

theorem Images.selected_eq {target formal : Context} {arguments : List Preterm}
    {dependencies images : Finset Nat} (proof : Images target formal arguments dependencies images) :
    selectedImages arguments dependencies = images := by
  apply Finset.ext
  intro image
  rw [mem_selectedImages, proof.members]
  constructor
  · rintro ⟨position, member, lookup⟩
    obtain ⟨other, known⟩ := proof.defined position member
    have same := Preterm.var.inj (Option.some.inj (lookup.symm.trans known.argument))
    subst other
    exact ⟨position, member, known⟩
  · rintro ⟨position, member, known⟩
    exact ⟨position, member, known.argument⟩

def images? (target formal : Context) (arguments : List Preterm)
    (dependencies : Finset Nat) : Option (Finset Nat) :=
  if ∀ position ∈ dependencies, checkImage target formal arguments position = true then
    some (selectedImages arguments dependencies)
  else none

theorem images_eq_some_iff (target formal : Context) (arguments : List Preterm)
    (dependencies images : Finset Nat) :
    images? target formal arguments dependencies = some images ↔
      Images target formal arguments dependencies images := by
  have check : (∀ position ∈ dependencies, checkImage target formal arguments position = true) ↔
      ∀ position ∈ dependencies, ∃ image, BoundImage target formal arguments position image := by
    simp [checkImage_iff]
  constructor
  · intro accepted
    unfold images? at accepted
    split at accepted
    next checked =>
      have defined := check.mp checked
      have same := Option.some.inj accepted
      subst images
      refine ⟨defined, ?_⟩
      intro image
      rw [mem_selectedImages]
      constructor
      · rintro ⟨position, member, lookup⟩
        obtain ⟨other, known⟩ := defined position member
        have equal := Preterm.var.inj (Option.some.inj (lookup.symm.trans known.argument))
        subst other
        exact ⟨position, member, known⟩
      · rintro ⟨position, member, known⟩
        exact ⟨position, member, known.argument⟩
    next => simp at accepted
  · intro proof
    rw [images?, if_pos (check.mpr proof.defined), proof.selected_eq]

theorem Images.eval {target formal : Context} {arguments : List Preterm}
    {dependencies images : Finset Nat} (proof : Images target formal arguments dependencies images) :
    images? target formal arguments dependencies = some images :=
  (images_eq_some_iff _ _ _ _ _).mpr proof

/-- Per-regular-argument subtraction; the bound argument's own free set is ignored. -/
def contributions? (target fullFormal : Context) (arguments : List Preterm) :
    Context → List (Finset Nat) → Option (Finset Nat)
  | [], [] => some ∅
  | .bound _ :: rest, _ :: freeSets => contributions? target fullFormal arguments rest freeSets
  | .regular _ dependencies :: rest, free :: freeSets => do
      let bound ← images? target fullFormal arguments dependencies
      let remaining ← contributions? target fullFormal arguments rest freeSets
      pure ((free \ bound) ∪ remaining)
  | _, _ => none

inductive Contributions (target fullFormal : Context) (arguments : List Preterm) :
    Context → List (Finset Nat) → Finset Nat → Prop where
  | nil : Contributions target fullFormal arguments [] [] ∅
  | bound {sort : Nat} {rest : Context} {free : Finset Nat}
      {freeSets : List (Finset Nat)} {result : Finset Nat} :
      Contributions target fullFormal arguments rest freeSets result →
      Contributions target fullFormal arguments (.bound sort :: rest) (free :: freeSets) result
  | regular {sort : Nat} {dependencies free bound result : Finset Nat}
      {rest : Context} {freeSets : List (Finset Nat)} :
      Images target fullFormal arguments dependencies bound →
      Contributions target fullFormal arguments rest freeSets result →
      Contributions target fullFormal arguments (.regular sort dependencies :: rest)
        (free :: freeSets) ((free \ bound) ∪ result)

theorem Contributions.eval {target fullFormal : Context} {arguments : List Preterm}
    {formal : Context} {freeSets : List (Finset Nat)} {result : Finset Nat}
    (proof : Contributions target fullFormal arguments formal freeSets result) :
    contributions? target fullFormal arguments formal freeSets = some result := by
  induction proof with
  | nil => rfl
  | bound _ ih => exact ih
  | regular images _ ih => simp [contributions?, images.eval, ih]

theorem contributions_sound {target fullFormal : Context} {arguments : List Preterm}
    {formal : Context} {freeSets : List (Finset Nat)} {result : Finset Nat}
    (accepted : contributions? target fullFormal arguments formal freeSets = some result) :
    Contributions target fullFormal arguments formal freeSets result := by
  induction formal generalizing freeSets result with
  | nil =>
      cases freeSets with
      | nil =>
          have same := Option.some.inj accepted
          subst result
          exact .nil
      | cons => simp [contributions?] at accepted
  | cons binder rest ih =>
      cases freeSets with
      | nil => simp [contributions?] at accepted
      | cons free freeSets =>
          cases binder with
          | bound sort => exact .bound (ih accepted)
          | regular sort dependencies =>
              cases image : images? target fullFormal arguments dependencies with
              | none => simp [contributions?, image] at accepted
              | some bound =>
                  cases tail : contributions? target fullFormal arguments rest freeSets with
                  | none => simp [contributions?, image, tail] at accepted
                  | some remaining =>
                      have same : (free \ bound) ∪ remaining = result := by
                        simpa [contributions?, image, tail] using accepted
                      subst result
                      exact .regular ((images_eq_some_iff _ _ _ _ _).mp image) (ih tail)

theorem contributions_eq_some_iff (target fullFormal : Context) (arguments : List Preterm)
    (formal : Context) (freeSets : List (Finset Nat)) (result : Finset Nat) :
    contributions? target fullFormal arguments formal freeSets = some result ↔
      Contributions target fullFormal arguments formal freeSets result :=
  ⟨contributions_sound, Contributions.eval⟩

theorem images_defined_iff (target formal : Context) (arguments : List Preterm)
    (dependencies : Finset Nat) :
    (∃ images, images? target formal arguments dependencies = some images) ↔
      ∀ position ∈ dependencies, ∃ image, BoundImage target formal arguments position image := by
  constructor
  · rintro ⟨images, accepted⟩
    exact ((images_eq_some_iff _ _ _ _ _).mp accepted).defined
  · intro defined
    refine ⟨selectedImages arguments dependencies, ?_⟩
    have checked : ∀ position ∈ dependencies, checkImage target formal arguments position = true :=
      fun position member => (checkImage_iff _ _ _ _).mpr (defined position member)
    rw [images?, if_pos checked]

/-- Argument typing supplies an actual bound image for any declared bound slot. -/
theorem boundImage_of_fits {signature : TermSignature} {target formal : Context}
    {arguments : List Preterm}
    (fits : List.Forall₂ (Preterm.FitsBinder signature target) arguments formal)
    {position sort : Nat} (lookup : formal[position]? = some (.bound sort)) :
    ∃ image, BoundImage target formal arguments position image := by
  induction fits generalizing position with
  | nil => simp at lookup
  | @cons argument binder arguments formal fits tail ih =>
      cases position with
      | zero =>
          have same : binder = .bound sort := by simpa using lookup
          subst binder
          cases fits with
          | bound known => exact ⟨_, .intro (by rfl) (by rfl) known⟩
      | succ position =>
          have tailLookup : formal[position]? = some (.bound sort) := by simpa using lookup
          obtain ⟨image, known⟩ := ih tailLookup
          cases known with
          | intro knownFormal knownArgument knownTarget =>
              exact ⟨image, .intro (by simpa using knownFormal)
                (by simpa using knownArgument) knownTarget⟩

theorem images_exists_of_fits {signature : TermSignature} {target formal : Context}
    {arguments : List Preterm} {dependencies : Finset Nat}
    (fits : List.Forall₂ (Preterm.FitsBinder signature target) arguments formal)
    (bound : ∀ position ∈ dependencies, ∃ sort, formal[position]? = some (.bound sort)) :
    ∃ images, Images target formal arguments dependencies images := by
  have defined : ∀ position ∈ dependencies,
      ∃ image, BoundImage target formal arguments position image := by
    intro position member
    obtain ⟨sort, lookup⟩ := bound position member
    exact boundImage_of_fits fits lookup
  obtain ⟨images, accepted⟩ := (images_defined_iff _ _ _ _).mpr defined
  exact ⟨images, (images_eq_some_iff _ _ _ _ _).mp accepted⟩

theorem Contributions.length_eq {target fullFormal : Context} {arguments : List Preterm}
    {formal : Context} {freeSets : List (Finset Nat)} {result : Finset Nat}
    (proof : Contributions target fullFormal arguments formal freeSets result) :
    freeSets.length = formal.length := by
  induction proof with
  | nil => rfl
  | bound _ ih => exact congrArg Nat.succ ih
  | regular _ _ ih => exact congrArg Nat.succ ih

theorem contributions_exists_of_fits {signature : TermSignature} {target fullFormal formal : Context}
    {arguments : List Preterm} {freeSets : List (Finset Nat)}
    (fits : List.Forall₂ (Preterm.FitsBinder signature target) arguments fullFormal)
    (length : freeSets.length = formal.length)
    (bound : ∀ sort dependencies, Binder.regular sort dependencies ∈ formal →
      ∀ position ∈ dependencies, ∃ boundSort, fullFormal[position]? = some (.bound boundSort)) :
    ∃ result, Contributions target fullFormal arguments formal freeSets result := by
  induction formal generalizing freeSets with
  | nil =>
      cases freeSets with
      | nil => exact ⟨∅, .nil⟩
      | cons => simp at length
  | cons binder formal ih =>
      cases freeSets with
      | nil => simp at length
      | cons free freeSets =>
          have tailLength : freeSets.length = formal.length := Nat.succ.inj length
          obtain ⟨result, tail⟩ := ih tailLength
            (fun sort dependencies member => bound sort dependencies (by simp [member]))
          cases binder with
          | bound sort => exact ⟨result, .bound tail⟩
          | regular sort dependencies =>
              obtain ⟨images, mapped⟩ := images_exists_of_fits fits
                (bound sort dependencies (by simp))
              exact ⟨(free \ images) ∪ result, .regular mapped tail⟩

end FreeVariables

namespace TermDecl

/-- The dependency portion of declaration admission used by free-variable analysis.
Ordering, sort declarations and conservative definition admission are separate. -/
structure DependenciesBound (declaration : TermDecl) : Prop where
  returned : ∀ position ∈ declaration.dependencies,
    ∃ sort, declaration.arguments[position]? = some (.bound sort)
  arguments : ∀ sort dependencies, Binder.regular sort dependencies ∈ declaration.arguments →
    ∀ position ∈ dependencies, ∃ boundSort, declaration.arguments[position]? = some (.bound boundSort)

end TermDecl

namespace Preterm

open FreeVariables

/-- Walk the source spine; collected arguments and their free sets are in declaration order. -/
def freeSpine? (signature : TermSignature) (context : Context) :
    Preterm → List Preterm → List (Finset Nat) → Option (Finset Nat)
  | .var index, [], [] => support? context (.var index)
  | .var _, _, _ => none
  | .term symbol, arguments, freeSets => do
      let declaration ← signature symbol
      if Substitution.checkArguments signature context arguments declaration.arguments then
        let contributed ← contributions? context declaration.arguments arguments
          declaration.arguments freeSets
        let returned ← images? context declaration.arguments arguments declaration.dependencies
        pure (contributed ∪ returned)
      else none
  | .app function argument, arguments, freeSets => do
      let free ← freeSpine? signature context argument [] []
      freeSpine? signature context function (argument :: arguments) (free :: freeSets)

/-- Independent free-variable rules, including exact typing and dependency resolution. -/
inductive FreeSpine (signature : TermSignature) (context : Context) :
    Preterm → List Preterm → List (Finset Nat) → Finset Nat → Prop where
  | var {index : Nat} {free : Finset Nat} : Supports context (.var index) free →
      FreeSpine signature context (.var index) [] [] free
  | term {symbol : Nat} {declaration : TermDecl} {arguments : List Preterm}
      {freeSets : List (Finset Nat)} {contributed returned : Finset Nat} :
      signature symbol = some declaration →
      List.Forall₂ (FitsBinder signature context) arguments declaration.arguments →
      Contributions context declaration.arguments arguments declaration.arguments freeSets contributed →
      Images context declaration.arguments arguments declaration.dependencies returned →
      FreeSpine signature context (.term symbol) arguments freeSets (contributed ∪ returned)
  | app {function argument : Preterm} {arguments : List Preterm}
      {freeSets : List (Finset Nat)} {free result : Finset Nat} :
      FreeSpine signature context argument [] [] free →
      FreeSpine signature context function (argument :: arguments) (free :: freeSets) result →
      FreeSpine signature context (.app function argument) arguments freeSets result

abbrev FreeVars (signature : TermSignature) (context : Context) (source : Preterm)
    (free : Finset Nat) : Prop := FreeSpine signature context source [] [] free

def freeVariables? (signature : TermSignature) (context : Context) (source : Preterm) :
    Option (Finset Nat) := freeSpine? signature context source [] []

theorem FreeSpine.eval {signature : TermSignature} {context : Context} {source : Preterm}
    {arguments : List Preterm} {freeSets : List (Finset Nat)} {result : Finset Nat}
    (proof : FreeSpine signature context source arguments freeSets result) :
    freeSpine? signature context source arguments freeSets = some result := by
  induction proof with
  | var supported => exact supported.eval
  | term lookup typed contributed returned =>
      simp [freeSpine?, lookup, (Substitution.checkArguments_iff _ _ _ _).mpr typed,
        contributed.eval, returned.eval]
  | app _ _ ihArgument ihFunction => simp [freeSpine?, ihArgument, ihFunction]

theorem freeSpine_sound {signature : TermSignature} {context : Context} {source : Preterm}
    {arguments : List Preterm} {freeSets : List (Finset Nat)} {result : Finset Nat}
    (accepted : freeSpine? signature context source arguments freeSets = some result) :
    FreeSpine signature context source arguments freeSets result := by
  induction source generalizing arguments freeSets result with
  | var index =>
      cases arguments with
      | nil =>
          cases freeSets with
          | nil => exact .var (support_sound accepted)
          | cons => simp [freeSpine?] at accepted
      | cons => simp [freeSpine?] at accepted
  | term symbol =>
      cases lookup : signature symbol with
      | none => simp [freeSpine?, lookup] at accepted
      | some declaration =>
          cases typed : Substitution.checkArguments signature context arguments declaration.arguments with
          | false => simp [freeSpine?, lookup, typed] at accepted
          | true =>
              cases contribution : contributions? context declaration.arguments arguments
                  declaration.arguments freeSets with
              | none => simp [freeSpine?, lookup, typed, contribution] at accepted
              | some contributed =>
                  cases image : images? context declaration.arguments arguments declaration.dependencies with
                  | none => simp [freeSpine?, lookup, typed, contribution, image] at accepted
                  | some returned =>
                      have same : contributed ∪ returned = result := by
                        simpa [freeSpine?, lookup, typed, contribution, image] using accepted
                      subst result
                      exact .term lookup ((Substitution.checkArguments_iff _ _ _ _).mp typed)
                        (contributions_sound contribution) ((images_eq_some_iff _ _ _ _ _).mp image)
  | app function argument ihFunction ihArgument =>
      cases child : freeSpine? signature context argument [] [] with
      | none => simp [freeSpine?, child] at accepted
      | some free =>
          have head : freeSpine? signature context function (argument :: arguments)
              (free :: freeSets) = some result := by simpa [freeSpine?, child] using accepted
          exact .app (ihArgument child) (ihFunction head)

theorem freeSpine_eq_some_iff (signature : TermSignature) (context : Context) (source : Preterm)
    (arguments : List Preterm) (freeSets : List (Finset Nat)) (result : Finset Nat) :
    freeSpine? signature context source arguments freeSets = some result ↔
      FreeSpine signature context source arguments freeSets result :=
  ⟨freeSpine_sound, FreeSpine.eval⟩

theorem freeVariables_eq_some_iff (signature : TermSignature) (context : Context)
    (source : Preterm) (result : Finset Nat) :
    freeVariables? signature context source = some result ↔ FreeVars signature context source result :=
  freeSpine_eq_some_iff signature context source [] [] result

theorem FreeSpine.deterministic {signature : TermSignature} {context : Context} {source : Preterm}
    {arguments : List Preterm} {freeSets : List (Finset Nat)} {first second : Finset Nat}
    (left : FreeSpine signature context source arguments freeSets first)
    (right : FreeSpine signature context source arguments freeSets second) : first = second :=
  Option.some.inj (left.eval.symm.trans right.eval)

theorem freeVariables_none_iff (signature : TermSignature) (context : Context) (source : Preterm) :
    freeVariables? signature context source = none ↔ ¬ ∃ free, FreeVars signature context source free := by
  constructor
  · intro refused ⟨free, proof⟩
    have accepted := proof.eval
    change freeVariables? signature context source = some free at accepted
    rw [refused] at accepted
    contradiction
  · intro noFree
    cases result : freeVariables? signature context source with
    | none => rfl
    | some free => exact False.elim (noFree ⟨free, freeSpine_sound result⟩)

/-- Free-variable evidence includes its whole saturated expression, not just one live child. -/
def IsFree (signature : TermSignature) (context : Context) (source : Preterm) (index : Nat) : Prop :=
  ∃ free, FreeVars signature context source free ∧ index ∈ free

theorem freeVariables_membership_iff (signature : TermSignature) (context : Context)
    (source : Preterm) (index : Nat) :
    (∃ free, freeVariables? signature context source = some free ∧ index ∈ free) ↔
      IsFree signature context source index := by
  simp only [IsFree, freeVariables_eq_some_iff]

/-- A typed head applied to a fitting argument vector keeps its result sort. -/
theorem HasType.applyArgs {signature : TermSignature} {context remaining : Context}
    {source : Preterm} {sort : Nat} (typing : HasType signature context source remaining sort)
    {arguments : List Preterm}
    (fits : List.Forall₂ (FitsBinder signature context) arguments remaining) :
    HasType signature context (applyArgs source arguments) [] sort := by
  induction fits generalizing source with
  | nil => exact typing
  | cons fits tail ih =>
      cases fits with
      | bound lookup => exact ih (.bound typing lookup)
      | regular argumentTyping => exact ih (.regular typing argumentTyping)

theorem FreeSpine.typed {signature : TermSignature} {context : Context} {source : Preterm}
    {arguments : List Preterm} {freeSets : List (Finset Nat)} {result : Finset Nat}
    (proof : FreeSpine signature context source arguments freeSets result) :
    ∃ sort, HasType signature context (applyArgs source arguments) [] sort := by
  induction proof with
  | var supported =>
      cases supported with
      | bound lookup => exact ⟨_, .var lookup⟩
      | regular lookup => exact ⟨_, .var lookup⟩
  | term lookup typed _ _ => exact ⟨_, (HasType.term lookup).applyArgs typed⟩
  | app _ _ _ ihFunction => exact ihFunction

/-- The free-variable computation rejects every undefined, ill-typed or unsaturated preterm. -/
theorem freeVariables_refuses_of_untyped (signature : TermSignature) (context : Context)
    (source : Preterm) (untyped : ¬ ∃ sort, HasType signature context source [] sort) :
    freeVariables? signature context source = none := by
  apply (freeVariables_none_iff _ _ _).mpr
  rintro ⟨free, proof⟩
  exact untyped proof.typed

/-- Completeness on typed applications requires valid declaration dependency positions.
No result, free set or target execution is assumed. -/
theorem HasType.freeSpine_exists {signature : TermSignature} {context remaining : Context}
    {source : Preterm} {sort : Nat} (typing : HasType signature context source remaining sort)
    (declarations : ∀ symbol declaration, signature symbol = some declaration →
      declaration.DependenciesBound) {arguments : List Preterm} {freeSets : List (Finset Nat)}
    (fits : List.Forall₂ (FitsBinder signature context) arguments remaining)
    (frees : List.Forall₂ (FreeVars signature context) arguments freeSets) :
    ∃ result, FreeSpine signature context source arguments freeSets result := by
  induction typing generalizing arguments freeSets with
  | var lookup =>
      cases fits
      cases frees
      rename_i binder
      cases binder with
      | bound sort => exact ⟨_, .var (.bound lookup)⟩
      | regular sort dependencies => exact ⟨_, .var (.regular lookup)⟩
  | @term symbol declaration lookup =>
      have valid := declarations symbol declaration lookup
      obtain ⟨contributed, contributions⟩ := contributions_exists_of_fits fits
        (frees.length_eq.symm.trans fits.length_eq) valid.arguments
      obtain ⟨returned, images⟩ := images_exists_of_fits fits valid.returned
      exact ⟨contributed ∪ returned, .term lookup fits contributions images⟩
  | bound _ lookup ih =>
      have child : FreeVars signature context (.var _) {_} := .var (.bound lookup)
      obtain ⟨result, head⟩ := ih (.cons (.bound lookup) fits) (.cons child frees)
      exact ⟨result, .app child head⟩
  | regular _ argumentTyping ihFunction ihArgument =>
      obtain ⟨free, child⟩ := ihArgument .nil .nil
      obtain ⟨result, head⟩ := ihFunction (.cons (.regular argumentTyping) fits) (.cons child frees)
      exact ⟨result, .app child head⟩

theorem HasType.freeVariables_exists {signature : TermSignature} {context : Context}
    {source : Preterm} {sort : Nat} (typing : HasType signature context source [] sort)
    (declarations : ∀ symbol declaration, signature symbol = some declaration →
      declaration.DependenciesBound) :
    ∃ free, freeVariables? signature context source = some free := by
  obtain ⟨free, proof⟩ := typing.freeSpine_exists declarations .nil .nil
  exact ⟨free, proof.eval⟩

theorem freeVariables_defined_iff (signature : TermSignature) (context : Context) (source : Preterm)
    (declarations : ∀ symbol declaration, signature symbol = some declaration →
      declaration.DependenciesBound) :
    (∃ free, freeVariables? signature context source = some free) ↔
      ∃ sort, HasType signature context source [] sort := by
  constructor
  · rintro ⟨free, accepted⟩
    exact (freeSpine_sound accepted).typed
  · rintro ⟨sort, typing⟩
    exact typing.freeVariables_exists declarations

end Preterm

end Mettapedia.Languages.MM0.Kernel
