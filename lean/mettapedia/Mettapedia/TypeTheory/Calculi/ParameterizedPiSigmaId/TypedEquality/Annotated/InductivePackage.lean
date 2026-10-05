import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ComputationSchemas
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PackageSum
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirst
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.SpineKnowledge

/-!
# The package of a simple inductive declaration

A simple inductive declaration gives a type `T` in a universe `u`, constructors whose fields
are `T` or closed types, and a recursor into a universe `v`
(`Normalization.ctorType`, `recType`). This module makes the declaration a rule package of
its own, over the universe rules of a given package:

* `inductiveDecls`: the declared types of the type, its constructors and its recursor;
* `inductiveRules`: these constants with the computation rules of the recursor
  (`Normalization.iotaComputation`);
* `inductiveChurch`: its annotation from the schemas of the recursor (`iotaSchema`), so that
  each computation step carries the typings of its motive, its methods and its fields as
  premises.

When the closed field types have no abstraction (`FieldsLamFree`), neither have the declared
types (`lamFree_ctorType`, `lamFree_recType`), and the annotated declared types are the
declared types themselves (`inductiveChurch_constantType`).

The metavariables of the computation rule of a constructor are the motive, a method for each
constructor, and the constructor's fields. `iotaTele` is their telescope: the type of motives,
the method types over the motive, and the field types.

**The computation rules in the judgment** (`iota_equal`, `iota_equal_sum`): in a package that
contains the declaration's steps with their premises, an instance of a computation rule at a
substitution typed along the telescope of its metavariables is an equality at every type both
sides have, when the knowledge of the left side is that telescope. The premises of a step are
then the typings of the motive, of the methods and of the fields, and nothing else: the left
side has no reflexivity position (`patternEquations_applicative`).

**The constants in the judgment.** Let a package have a level model, and let a declaration
have distinct names (`DistinctNames`) that are new to the package (`NewNames`) and closed
field types without abstraction that are types of the package (`FieldsFormed`). In the
package with the declaration (`withInductive`):

* the declared type is a type of its universe (`type_typed`);
* the declared type of each constructor is a type (`ctorType_formed`), the constructor has it
  (`ctor_typed`), and applied to terms of the types of its fields it is a term of the declared
  type (`ctor_applied` along a typed substitution, `ctor_spine_typed` for listed terms);
* the type of each method over a motive is a type (`caseFields_formed`), so the declared type
  of the recursor is a type (`recType_formed`) and the recursor has it (`rec_typed`);
* **the typing rule of the recursor** (`rec_applied`): applied to a motive, a method for each
  constructor and a term of the declared type, all typed along the recursor's telescope, it
  has the motive's type at that term.

None of these but the recursor's typing needs the declaration's own package. Every package
that declares the type in its universe with types for the closed fields (`DeclaresDataType`)
has the type, the field types and the constructors' declared types as types; every package
that declares the constructors at their declared types as well (`DeclaresDataCtors`) has the
constructors' typings and the recursor's declared type as a type
(`DeclaresDataCtors.recType_formed`), with or without the recursor. The package with the
declaration is one (`withInductive_declaresDataCtors`), and the lemmas above are these at it;
a package with the type and its constructors and without the recursor is another, where the
recursor's declared type is formed before the recursor is declared.

These rest on two facts about telescopes given by their entries: a telescope of types closes
to a type (`closeType_formed`), and a term of a closed telescope type applied along a
substitution typed along the telescope has the target at that substitution
(`applyAlong_typed`).

**Both sides of a computation rule are typed from the typings of its arguments**
(`iota_typed`, `iota_typed_metaVars`): at a substitution typed along the telescope of the
rule's metavariables, both sides of the rule of a constructor have the motive's type at the
constructor applied to its fields (`iotaTarget`): the left side by the typing rule of the
recursor, the right side because a method applied to the fields and to the recursor's values
at the recursive fields has it (`caseFields_applied`). This uses that annotating commutes with
substitution (`liftTm_subst`), the entry of a telescope seen from a later position
(`ofEntries_lookup`), and the typing of a term of a closed telescope type applied to listed
terms (`spine_typed`). The rule itself, with the typings of its arguments as its only
premises, is `iota_holds` in `DeclarationLists.lean`: it uses the knowledge of the rule's left
side, proved in `IotaKnowledge.lean`.

Positive example: the natural numbers as a declaration (`exampleNat`): its constructors have
no closed field types, so its declared types have no abstraction. Negative example: a name
that the declaration does not declare has no type in its package (`inductiveDecls_other`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization
open TelescopeAbstraction (closeType)
open UniverseLevel (LevelOrder)

variable {Head : Type}

/-! ## Terms without abstractions -/

theorem lamFree_rename : ∀ {n m : Nat} (ρ : Ren n m) (t : Tm Head n),
    lamFree (Presentation.rename ρ t) = lamFree t
  | _, _, _, .var _ => rfl
  | _, _, _, .const _ => rfl
  | _, _, _, .head _ => rfl
  | _, _, ρ, .pi A B => by
    simp only [Presentation.rename, lamFree, lamFree_rename ρ A, lamFree_rename (liftRen ρ) B]
  | _, _, ρ, .sigma A B => by
    simp only [Presentation.rename, lamFree, lamFree_rename ρ A, lamFree_rename (liftRen ρ) B]
  | _, _, ρ, .id A a b => by
    simp only [Presentation.rename, lamFree, lamFree_rename ρ A, lamFree_rename ρ a,
      lamFree_rename ρ b]
  | _, _, _, .lam _ => rfl
  | _, _, ρ, .app f a => by
    simp only [Presentation.rename, lamFree, lamFree_rename ρ f, lamFree_rename ρ a]
  | _, _, ρ, .pair a b => by
    simp only [Presentation.rename, lamFree, lamFree_rename ρ a, lamFree_rename ρ b]
  | _, _, ρ, .fst p => by simp only [Presentation.rename, lamFree, lamFree_rename ρ p]
  | _, _, ρ, .snd p => by simp only [Presentation.rename, lamFree, lamFree_rename ρ p]
  | _, _, ρ, .refl a => by simp only [Presentation.rename, lamFree, lamFree_rename ρ a]

theorem lamFree_liftClosed {n : Nat} (t : Tm Head 0) :
    lamFree (Presentation.liftClosed t : Tm Head n) = lamFree t :=
  lamFree_rename _ t

/-- A term without abstractions applied to such terms has none. -/
theorem lamFree_appSpine {n : Nat} : ∀ (xs : List (Tm Head n)) (f : Tm Head n),
    lamFree f = true → (∀ x ∈ xs, lamFree x = true) → lamFree (appSpine f xs) = true
  | [], _, free, _ => free
  | x :: xs, f, free, all => by
    rw [appSpine_cons]
    refine lamFree_appSpine xs (.app f x) ?_ fun y member => all y (List.mem_cons_of_mem _ member)
    show (lamFree f && lamFree x) = true
    rw [free, all x List.mem_cons_self]
    rfl

/-- The induction hypotheses of a case have no abstraction when their data have none. -/
theorem lamFree_caseHyps : ∀ (count : Nat) {n : Nat} (p : Tm Head n) (rs : List (Tm Head n))
    (target : Tm Head n), rs.length = count → lamFree p = true →
      (∀ r ∈ rs, lamFree r = true) → lamFree target = true →
      lamFree (caseHyps p rs target) = true
  | 0, _, p, rs, target, length, freeP, _, freeT => by
    obtain rfl := List.length_eq_zero_iff.mp length
    rw [caseHyps_nil]
    show (lamFree p && lamFree target) = true
    rw [freeP, freeT]
    rfl
  | count + 1, _, p, rs, target, length, freeP, freeR, freeT => by
    cases rs with
    | nil => exact nomatch length
    | cons r rs =>
      rw [caseHyps_cons]
      show ((lamFree p && lamFree r) && lamFree (caseHyps (Presentation.rename wk p)
        (rs.map (Presentation.rename wk)) (Presentation.rename wk target))) = true
      rw [freeP, freeR r List.mem_cons_self,
        lamFree_caseHyps count _ _ _ (by rw [List.length_map]; exact Nat.succ.inj length)
          (by rw [lamFree_rename]; exact freeP)
          (fun x member => by
            obtain ⟨y, memberY, rfl⟩ := List.mem_map.mp member
            rw [lamFree_rename]
            exact freeR y (List.mem_cons_of_mem _ memberY))
          (by rw [lamFree_rename]; exact freeT)]
      rfl

/-- The closed types among the fields of a constructor list have no abstraction. -/
def FieldsLamFree (ctors : List (DeclName × List (Field Head))) : Prop :=
  ∀ entry ∈ ctors, ∀ F, Field.closed F ∈ entry.2 → lamFree F = true

/-- The type of a method has no abstraction when the closed types of its fields have none. -/
theorem lamFree_caseFields (T k : DeclName) : ∀ (fs : List (Field Head)) {n : Nat}
    (p : Tm Head n) (xs recs : List (Tm Head n)),
    (∀ F, Field.closed F ∈ fs → lamFree F = true) → lamFree p = true →
      (∀ x ∈ xs, lamFree x = true) → (∀ r ∈ recs, lamFree r = true) →
      lamFree (caseFields T k fs p xs recs) = true
  | [], _, p, xs, recs, _, freeP, freeX, freeR =>
    lamFree_caseHyps recs.length p recs _ rfl freeP freeR
      (lamFree_appSpine xs (.const k) rfl freeX)
  | .recursive :: fs, _, p, xs, recs, freeF, freeP, freeX, freeR => by
    show (lamFree (Tm.const T : Tm Head _) && lamFree (caseFields T k fs (Presentation.rename wk p)
      (xs.map (Presentation.rename wk) ++ [.var 0])
      (recs.map (Presentation.rename wk) ++ [.var 0]))) = true
    rw [lamFree_caseFields T k fs _ _ _ (fun F member => freeF F (List.mem_cons_of_mem _ member))
      (by rw [lamFree_rename]; exact freeP)
      (fun x member => by
        rcases List.mem_append.mp member with old | new
        · obtain ⟨y, memberY, rfl⟩ := List.mem_map.mp old
          rw [lamFree_rename]
          exact freeX y memberY
        · obtain rfl := List.mem_singleton.mp new
          rfl)
      (fun x member => by
        rcases List.mem_append.mp member with old | new
        · obtain ⟨y, memberY, rfl⟩ := List.mem_map.mp old
          rw [lamFree_rename]
          exact freeR y memberY
        · obtain rfl := List.mem_singleton.mp new
          rfl)]
    rfl
  | .closed F :: fs, _, p, xs, recs, freeF, freeP, freeX, freeR => by
    show (lamFree (Presentation.liftClosed F : Tm Head _) &&
      lamFree (caseFields T k fs (Presentation.rename wk p)
        (xs.map (Presentation.rename wk) ++ [.var 0]) (recs.map (Presentation.rename wk)))) = true
    rw [lamFree_liftClosed, freeF F List.mem_cons_self,
      lamFree_caseFields T k fs _ _ _ (fun G member => freeF G (List.mem_cons_of_mem _ member))
        (by rw [lamFree_rename]; exact freeP)
        (fun x member => by
          rcases List.mem_append.mp member with old | new
          · obtain ⟨y, memberY, rfl⟩ := List.mem_map.mp old
            rw [lamFree_rename]
            exact freeX y memberY
          · obtain rfl := List.mem_singleton.mp new
            rfl)
        (fun x member => by
          obtain ⟨y, memberY, rfl⟩ := List.mem_map.mp member
          rw [lamFree_rename]
          exact freeR y memberY)]
    rfl

/-- A dependent function type over a telescope given by its entries has no abstraction when
its entries and its body have none. -/
theorem lamFree_closeType_ofEntries (entry : (j : Nat) → Tm Head j) :
    ∀ (n : Nat) (C : Tm Head n), (∀ j, j < n → lamFree (entry j) = true) → lamFree C = true →
      lamFree (closeType (ofEntries entry n) C) = true
  | 0, _, _, free => free
  | n + 1, C, entries, free => by
    rw [closeType_ofEntries_succ]
    refine lamFree_closeType_ofEntries entry n _
      (fun j below => entries j (Nat.lt_succ_of_lt below)) ?_
    show (lamFree (entry n) && lamFree C) = true
    rw [entries n (Nat.lt_succ_self n), free]
    rfl

/-- A field a list gives at an index is one of its fields or the default. -/
theorem closed_mem_of_getD {fields : List (Field Head)} {j : Nat} {F : Tm Head 0}
    (found : fields.getD j .recursive = .closed F) : Field.closed F ∈ fields := by
  rw [List.getD_eq_getElem?_getD] at found
  cases entry : fields[j]? with
  | none =>
    rw [entry] at found
    exact nomatch found
  | some field =>
    rw [entry] at found
    obtain rfl : field = .closed F := found
    exact List.mem_of_getElem? entry

theorem lamFree_ctorType (T : DeclName) {fields : List (Field Head)}
    (free : ∀ F, Field.closed F ∈ fields → lamFree F = true) :
    lamFree (ctorType T fields) = true := by
  refine lamFree_closeType_ofEntries _ _ _ (fun j _ => ?_) rfl
  show lamFree (Presentation.liftClosed ((fields.getD j .recursive).type T) : Tm Head j) = true
  rw [lamFree_liftClosed]
  cases found : fields.getD j .recursive with
  | recursive => rfl
  | closed F => exact free F (closed_mem_of_getD found)

theorem lamFree_recType (T : DeclName) (v : Head) {ctors : List (DeclName × List (Field Head))}
    (free : FieldsLamFree ctors) : lamFree (recType T v ctors) = true := by
  refine lamFree_closeType_ofEntries _ _ _ (fun j _ => ?_) rfl
  cases j with
  | zero => rfl
  | succ j =>
    cases entry : ctors[j]? with
    | none =>
      have unfolded : recEntry T v ctors (j + 1) = .const T := by simp [recEntry, entry]
      rw [unfolded]
      rfl
    | some pair =>
      obtain ⟨k, fields⟩ := pair
      rw [recEntry_method T v ctors entry]
      exact lamFree_caseFields T k fields _ [] []
        (fun F member => free _ (List.mem_of_getElem? entry) F member) rfl
        (fun _ member => nomatch member) (fun _ member => nomatch member)

/-! ## The package -/

/-- **The declared types of a simple inductive declaration**: the type in its universe, each
constructor with the type of its fields, and the recursor. -/
def inductiveDecls (T : DeclName) (u : Head) (ctors : List (DeclName × List (Field Head)))
    (rec : DeclName) (v : Head) : DeclName → Option (Tm Head 0) := fun name =>
  if name = T then some (.head u)
  else match ctors.find? fun entry => entry.1 = name with
    | some entry => some (ctorType T entry.2)
    | none => if name = rec then some (recType T v ctors) else none

/-- **The rule package of a declaration**, over the universe rules of a package: its constants
and the computation rules of its recursor. -/
def inductiveRules (target : Rules Head) (T : DeclName) (u : Head)
    (ctors : List (DeclName × List (Field Head))) (rec : DeclName) (v : Head) : Rules Head :=
  { target with
    constantType := inductiveDecls T u ctors rec v
    computation := iotaComputation rec ctors }

/-- **Its annotated package**, from the schemas of the recursor: each computation step
requires the typings of its motive, its methods and its fields. -/
def inductiveChurch (target : Rules Head) (T : DeclName) (u : Head)
    (ctors : List (DeclName × List (Field Head))) (rec : DeclName) (v : Head) :
    ChurchRules (inductiveRules target T u ctors rec v) :=
  ChurchRules.ofSchemas (inductiveRules target T u ctors rec v) (iotaSchema rec ctors)
    (iota_presents rec ctors)

variable {T : DeclName} {u : Head} {ctors : List (DeclName × List (Field Head))}
  {rec : DeclName} {v : Head}

/-- What a declared constant of the declaration is, with its declared type. -/
theorem inductiveDecls_cases {name : DeclName} {type : Tm Head 0}
    (declared : inductiveDecls T u ctors rec v name = some type) :
    (name = T ∧ type = .head u) ∨
      (∃ (i : Nat) (fields : List (Field Head)),
        ctors[i]? = some (name, fields) ∧ type = ctorType T fields) ∨
      (name = rec ∧ type = recType T v ctors) := by
  unfold inductiveDecls at declared
  split at declared
  · next same => exact .inl ⟨same, (Option.some.inj declared).symm⟩
  · split at declared
    · next entry found =>
      have named : entry.1 = name := by simpa using List.find?_some found
      obtain ⟨i, _, atIndex⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some found)
      refine .inr (.inl ⟨i, entry.2, ?_, (Option.some.inj declared).symm⟩)
      rw [List.getElem?_eq_getElem ‹_›, atIndex, ← named]
    · split at declared
      · next same => exact .inr (.inr ⟨same, (Option.some.inj declared).symm⟩)
      · exact nomatch declared

/-- **The annotated declared types are the declared types**, when the closed field types have
no abstraction. -/
theorem inductiveChurch_constantType (target : Rules Head) (free : FieldsLamFree ctors)
    {name : DeclName} {type : CTm Head 0}
    (declared : (inductiveChurch target T u ctors rec v).constantType name = some type) :
    (name = T ∧ type = .head u) ∨
      (∃ (i : Nat) (fields : List (Field Head)),
        ctors[i]? = some (name, fields) ∧ type = liftTm (ctorType T fields)) ∨
      (name = rec ∧ type = liftTm (recType T v ctors)) := by
  have unfolded : elabDeclarations (inductiveDecls T u ctors rec v) name = some type := declared
  cases found : inductiveDecls T u ctors rec v name with
  | none =>
    rw [elabDeclarations, found] at unfolded
    exact nomatch unfolded
  | some written =>
    rcases inductiveDecls_cases found with ⟨rfl, rfl⟩ | ⟨i, fields, entry, rfl⟩ | ⟨rfl, rfl⟩
    · rw [elabDeclarations_lamFree _ found rfl] at unfolded
      exact .inl ⟨rfl, (Option.some.inj unfolded).symm⟩
    · rw [elabDeclarations_lamFree _ found (lamFree_ctorType T fun F member =>
        free _ (List.mem_of_getElem? entry) F member)] at unfolded
      exact .inr (.inl ⟨i, fields, entry, (Option.some.inj unfolded).symm⟩)
    · rw [elabDeclarations_lamFree _ found (lamFree_recType _ v free)] at unfolded
      exact .inr (.inr ⟨rfl, (Option.some.inj unfolded).symm⟩)

/-! ## The telescope of the metavariables of a computation rule -/

/-- The entries of the telescope of the metavariables of the computation rule of a
constructor: the motive, a method for each constructor over it, and the constructor's
fields. -/
def iotaEntry (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head)))
    (fields : List (Field Head)) (j : Nat) : Tm Head j :=
  if j ≤ ctors.length then recEntry T v ctors j
  else Presentation.liftClosed ((fields.getD (j - (ctors.length + 1)) .recursive).type T)

/-- The telescope of the metavariables of the computation rule of a constructor. -/
def iotaTele (T : DeclName) (v : Head) (ctors : List (DeclName × List (Field Head)))
    (fields : List (Field Head)) : Ctx Head (1 + ctors.length + fields.length) :=
  ofEntries (iotaEntry T v ctors fields) (1 + ctors.length + fields.length)

/-! ## Templates -/

theorem firstOrder_metaVars {N : Nat} {x : Tm Head N} (member : x ∈ metaVars N) :
    firstOrder x = true := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp member
  rfl

theorem lamFree_metaVars {N : Nat} {x : Tm Head N} (member : x ∈ metaVars N) :
    lamFree x = true := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp member
  rfl

/-- A recursive argument is one of the arguments. -/
theorem mem_of_mem_recArgs {n : Nat} {x : Tm Head n} :
    ∀ (fs : List (Field Head)) (as : List (Tm Head n)), x ∈ recArgs fs as → x ∈ as
  | .recursive :: fs, a :: as, member => by
    rcases List.mem_cons.mp member with rfl | rest
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_recArgs fs as rest)
  | .closed _ :: fs, _ :: as, member => List.mem_cons_of_mem _ (mem_of_mem_recArgs fs as member)
  | [], _, member => nomatch member
  | .recursive :: _, [], member => nomatch member
  | .closed _ :: _, [], member => nomatch member

/-- The left side of a computation rule of a recursor is first-order. -/
theorem firstOrder_iotaLeft (rec k : DeclName) (c a : Nat) :
    firstOrder (iotaLeft (Head := Head) rec k c a) = true := by
  refine firstOrder_appSpine _ _ rfl fun x member => ?_
  rcases List.mem_append.mp member with pre | last
  · exact firstOrder_metaVars (List.mem_of_mem_take pre)
  · obtain rfl := List.mem_singleton.mp last
    exact firstOrder_appSpine _ _ rfl fun y memberY =>
      firstOrder_metaVars (List.mem_of_mem_drop memberY)

/-- The right side of a computation rule of a recursor has no abstraction. -/
theorem lamFree_iotaRight (rec : DeclName) (c i : Nat) (fields : List (Field Head)) :
    lamFree (iotaRight rec c i fields) = true := by
  refine lamFree_appSpine _ _ ?_ fun x member => ?_
  · rw [List.getD_eq_getElem?_getD]
    cases found : ((metaVars (Head := Head) (1 + c + fields.length)).take (1 + c))[1 + i]? with
    | none => rfl
    | some t => exact lamFree_metaVars (List.mem_of_mem_take (List.mem_of_getElem? found))
  · rcases List.mem_append.mp member with field | call
    · exact lamFree_metaVars (List.mem_of_mem_drop field)
    · obtain ⟨a, memberA, rfl⟩ := List.mem_map.mp call
      refine lamFree_appSpine _ _ rfl fun y memberY => ?_
      rcases List.mem_append.mp memberY with pre | last
      · exact lamFree_metaVars (List.mem_of_mem_take pre)
      · rw [List.mem_singleton.mp last]
        exact lamFree_metaVars (List.mem_of_mem_drop (mem_of_mem_recArgs fields _ memberA))

/-! ## The computation rules in the judgment -/

/-- Terms built from variables, constants, heads and applications. -/
def applicative : {n : Nat} → Tm Head n → Bool
  | _, .var _ => true
  | _, .const _ => true
  | _, .head _ => true
  | _, .app f a => applicative f && applicative a
  | _, _ => false

/-- A term built from variables, constants, heads and applications has no reflexivity
position, so its instances carry no equation among their premises. -/
theorem patternEquations_applicative (decls : DeclName → Option (CTm Head 0)) :
    ∀ {k : Nat} (t : Tm Head k) (expected : Option (CTm Head k)), applicative t = true →
      patternEquations decls expected t = []
  | _, .var _, _, _ => rfl
  | _, .const _, _, _ => rfl
  | _, .head _, _, _ => rfl
  | _, .app f a, _, built => by
    have parts : applicative f = true ∧ applicative a = true := by
      simpa [applicative] using built
    show patternEquations decls none f ++ patternEquations decls _ a = []
    rw [patternEquations_applicative decls f none parts.1,
      patternEquations_applicative decls a _ parts.2]
    rfl
  | _, .pi _ _, _, built => nomatch built
  | _, .sigma _ _, _, built => nomatch built
  | _, .id _ _ _, _, built => nomatch built
  | _, .lam _, _, built => nomatch built
  | _, .pair _ _, _, built => nomatch built
  | _, .fst _, _, built => nomatch built
  | _, .snd _, _, built => nomatch built
  | _, .refl _, _, built => nomatch built

theorem applicative_appSpine {n : Nat} : ∀ (xs : List (Tm Head n)) (f : Tm Head n),
    applicative f = true → (∀ x ∈ xs, applicative x = true) → applicative (appSpine f xs) = true
  | [], _, built, _ => built
  | x :: xs, f, built, all => by
    rw [appSpine_cons]
    refine applicative_appSpine xs (.app f x) ?_ fun y member =>
      all y (List.mem_cons_of_mem _ member)
    show (applicative f && applicative x) = true
    rw [built, all x List.mem_cons_self]
    rfl

theorem applicative_metaVars {N : Nat} {x : Tm Head N} (member : x ∈ metaVars N) :
    applicative x = true := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp member
  rfl

theorem applicative_iotaLeft (rec k : DeclName) (c a : Nat) :
    applicative (iotaLeft (Head := Head) rec k c a) = true := by
  refine applicative_appSpine _ _ rfl fun x member => ?_
  rcases List.mem_append.mp member with pre | last
  · exact applicative_metaVars (List.mem_of_mem_take pre)
  · obtain rfl := List.mem_singleton.mp last
    exact applicative_appSpine _ _ rfl fun y memberY =>
      applicative_metaVars (List.mem_of_mem_drop memberY)

/-- **The computation rules of the recursor in the judgment.** In a package that contains the
declaration's steps with their premises, an instance of the computation rule of a constructor
at a substitution typed along the telescope of its metavariables is an equality at every type
both sides have, when the knowledge of the left side is that telescope. -/
theorem iota_equal (target : Rules Head) {R' : Rules Head} {Q : ChurchRules R'}
    (steps : ∀ {n : Nat} {l r : CTm Head n},
      (inductiveChurch target T u ctors rec v).computation.step l r → Q.computation.step l r)
    (requires : ∀ {n : Nat} {l r : CTm Head n} {premises : List (CPremise Head n)},
      (inductiveChurch target T u ctors rec v).computation.step l r →
        (inductiveChurch target T u ctors rec v).computation.requires l r premises →
          Q.computation.requires l r premises)
    {i : Nat} {k : DeclName} {fields : List (Field Head)} (entry : ctors[i]? = some (k, fields))
    (known : ∀ j, patternKnowledge (elabDeclarations (inductiveDecls T u ctors rec v)) none
        (iotaLeft rec k ctors.length fields.length) j =
      some ((liftCtx (iotaTele T v ctors fields)).lookup j))
    {n : Nat} {Γ : CCtx Head n} (σ : CSub Head (1 + ctors.length + fields.length) n)
    (typed : CSubstMor Q (liftCtx (iotaTele T v ctors fields)) Γ σ) {A : CTm Head n}
    (left : CTyped Q Γ ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ) A)
    (right : CTyped Q Γ ((liftTm (iotaRight rec ctors.length i fields)).subst σ) A) :
    CEqual Q Γ ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
      ((liftTm (iotaRight rec ctors.length i fields)).subst σ) A := by
  have rule : iotaSchema rec ctors (iotaLeft rec k ctors.length fields.length)
      (iotaRight rec ctors.length i fields) := ⟨i, k, fields, entry, rfl⟩
  have eL : elabLeft (elabDeclarations (inductiveDecls T u ctors rec v))
      (iotaLeft rec k ctors.length fields.length) =
      liftTm (iotaLeft rec k ctors.length fields.length) :=
    elabLeft_firstOrder _ (firstOrder_iotaLeft rec k _ _)
  have eR : elabRight (elabDeclarations (inductiveDecls T u ctors rec v))
      (iotaLeft rec k ctors.length fields.length) (iotaRight rec ctors.length i fields) =
      liftTm (iotaRight rec ctors.length i fields) :=
    elab_lamFree _ (lamFree_iotaRight rec _ i fields) _ _ _
  have step : (inductiveChurch target T u ctors rec v).computation.step
      ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
      ((liftTm (iotaRight rec ctors.length i fields)).subst σ) := by
    rw [← eL, ← eR]
    exact CSchemaStep.instantiate ⟨_, _, rule, rfl, rfl⟩ σ
  have required : (inductiveChurch target T u ctors rec v).computation.requires
      ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
      ((liftTm (iotaRight rec ctors.length i fields)).subst σ)
      (patternPremises (elabDeclarations (inductiveDecls T u ctors rec v))
        (iotaLeft rec k ctors.length fields.length) σ) := by
    rw [← eL, ← eR]
    exact CSchemaRequires.instantiate rule σ
  refine .root (steps step) (requires step required) (fun premise member => ?_) left right
  rcases mem_patternPremises.1 member with ⟨j, type, found, rfl⟩ | ⟨e, memberE, rfl⟩
  · rw [known j] at found
    cases found
    exact typed j
  · rw [patternEquations_applicative _ _ _ (applicative_iotaLeft rec k _ _)] at memberE
    exact nomatch memberE

/-- The same in the sum of a package with the package of the declaration. -/
theorem iota_equal_sum {R : Rules Head} (B : ChurchRules R)
    {i : Nat} {k : DeclName} {fields : List (Field Head)} (entry : ctors[i]? = some (k, fields))
    (known : ∀ j, patternKnowledge (elabDeclarations (inductiveDecls T u ctors rec v)) none
        (iotaLeft rec k ctors.length fields.length) j =
      some ((liftCtx (iotaTele T v ctors fields)).lookup j))
    {n : Nat} {Γ : CCtx Head n} (σ : CSub Head (1 + ctors.length + fields.length) n)
    (typed : CSubstMor (B.sum (inductiveChurch R T u ctors rec v))
      (liftCtx (iotaTele T v ctors fields)) Γ σ) {A : CTm Head n}
    (left : CTyped (B.sum (inductiveChurch R T u ctors rec v)) Γ
      ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ) A)
    (right : CTyped (B.sum (inductiveChurch R T u ctors rec v)) Γ
      ((liftTm (iotaRight rec ctors.length i fields)).subst σ) A) :
    CEqual (B.sum (inductiveChurch R T u ctors rec v)) Γ
      ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
      ((liftTm (iotaRight rec ctors.length i fields)).subst σ) A :=
  iota_equal (Q := B.sum (inductiveChurch R T u ctors rec v)) R (fun step => Or.inr step)
    (fun step required => Or.inr ⟨step, required⟩) entry known σ typed left right

/-! ## Telescopes in the judgment -/

section Telescopes

variable {L : Type} [LevelOrder L] {R : Rules Head} {Q : ChurchRules R}

/-- A closed type is a type in every context. -/
theorem CIsType.liftClosed {A : CTm Head 0} (formed : CIsType Q .nil A) {n : Nat}
    {Γ : CCtx Head n} : CIsType Q Γ A.liftClosed := by
  obtain ⟨w, hw, typed⟩ := formed
  exact ⟨w, hw, CTyped.rename (ρ := Fin.elim0) typed fun i => i.elim0⟩

/-- **A telescope of types closes to a type**: when each entry is a type over the entries
before it and the target is a type over all of them, the dependent function type from the
entries to the target is a type. -/
theorem closeType_formed (levels : LevelModel R L) (entry : (j : Nat) → Tm Head j) :
    ∀ (n : Nat) (C : Tm Head n),
      (∀ j, j < n → CIsType Q (liftCtx (ofEntries entry j)) (liftTm (entry j))) →
      CIsType Q (liftCtx (ofEntries entry n)) (liftTm C) →
      CIsType Q .nil (liftTm (closeType (ofEntries entry n) C))
  | 0, _, _, formed => formed
  | n + 1, C, entries, ⟨w, hw, typed⟩ => by
    obtain ⟨a, ha, domain⟩ := entries n (Nat.lt_succ_self n)
    obtain ⟨c, join⟩ := levels.join_exists ha hw
    exact closeType_formed levels entry n (.pi (entry n) C)
      (fun j below => entries j (Nat.lt_succ_of_lt below))
      ⟨c, (levels.join_level join).1, .piForm domain ha typed hw join⟩

/-- A term applied to the components of a substitution, the oldest first. -/
def applyAlong {m : Nat} : {n : Nat} → CSub Head n m → CTm Head m → CTm Head m
  | 0, _, g => g
  | _ + 1, σ, g => .app (applyAlong (fun i => σ i.succ) g) (σ 0)

/-- **A term of a closed telescope type applied along a typed substitution** has the target
of the telescope at the substitution. -/
theorem applyAlong_typed {m : Nat} {Δ : CCtx Head m} (entry : (j : Nat) → Tm Head j) :
    ∀ (n : Nat) (C : Tm Head n) (σ : CSub Head n m),
      CSubstMor Q (liftCtx (ofEntries entry n)) Δ σ → ∀ {g : CTm Head m},
      CTyped Q Δ g (liftTm (closeType (ofEntries entry n) C)).liftClosed →
      CTyped Q Δ (applyAlong σ g) ((liftTm C).subst σ)
  | 0, C, σ, _, g, typed => by
    rw [CTm.subst_closed]
    exact typed
  | n + 1, C, σ, mor, g, typed => by
    have tailMor : CSubstMor Q (liftCtx (ofEntries entry n)) Δ fun i => σ i.succ := fun i => by
      have at_ := mor i.succ
      change CTyped Q Δ (σ i.succ)
        ((((liftCtx (ofEntries entry n)).lookup i).rename wk).subst σ) at at_
      rwa [CTm.subst_rename] at at_
    have function := applyAlong_typed entry n (.pi (entry n) C) (fun i => σ i.succ) tailMor typed
    have argument : CTyped Q Δ (σ 0) ((liftTm (entry n)).subst fun i => σ i.succ) := by
      have at_ := mor 0
      change CTyped Q Δ (σ 0) (((liftTm (entry n)).rename wk).subst σ) at at_
      rwa [CTm.subst_rename] at at_
    have type : (liftTm C).subst σ =
        CTm.inst0 (σ 0) ((liftTm C).subst (CTm.liftSub fun i => σ i.succ)) := by
      rw [CTm.inst0_subst_liftSub]
      exact congrArg (fun τ => (liftTm C).subst τ) (CTm.eq_consSub_tail σ)
    show CTyped Q Δ (.app (applyAlong (fun i => σ i.succ) g) (σ 0)) ((liftTm C).subst σ)
    rw [type]
    exact .appElim function argument

/-- The oldest entry of a telescope, seen from its end. -/
theorem lookup_last (entry : (j : Nat) → Tm Head j) :
    ∀ n, (liftCtx (ofEntries entry (n + 1))).lookup (Fin.last n) = (liftTm (entry 0)).liftClosed
  | 0 => CTm.rename_closed _ _
  | n + 1 => by
    show ((liftCtx (ofEntries entry (n + 1))).lookup (Fin.last n)).rename wk = _
    rw [lookup_last entry n, CTm.rename_liftClosed]

theorem forall₂_concat {α β : Type} {S : α → β → Prop} :
    ∀ {as : List α} {bs : List β} {a : α} {b : β},
      List.Forall₂ S as bs → S a b → List.Forall₂ S (as ++ [a]) (bs ++ [b])
  | _, _, _, _, .nil, last => .cons last .nil
  | _, _, _, _, .cons head tail, last => .cons head (forall₂_concat tail last)

/-- **The induction hypotheses of a case are a type**: over a motive from a declared type into
a universe, at terms of that type. -/
theorem caseHyps_formed (levels : LevelModel R L) {T : DeclName} {v : Head}
    (hv : R.isUniverse v) : ∀ {n : Nat} {Γ : CCtx Head n} (rs : List (Tm Head n))
      (p target : Tm Head n),
      CTyped Q Γ (liftTm p) (.pi (.const T) (.head v)) →
      (∀ r ∈ rs, CTyped Q Γ (liftTm r) (.const T)) →
      CTyped Q Γ (liftTm target) (.const T) →
      CIsType Q Γ (liftTm (caseHyps p rs target))
  | _, Γ, [], p, target, hp, _, ht => by
    rw [caseHyps_nil]
    exact ⟨v, hv, .appElim hp ht⟩
  | _, Γ, r :: rs, p, target, hp, hrs, ht => by
    rw [caseHyps_cons]
    have domain : CTyped Q Γ (liftTm (.app p r)) (.head v) :=
      .appElim hp (hrs r List.mem_cons_self)
    obtain ⟨w, hw, codomain⟩ := caseHyps_formed levels hv (Γ := .snoc Γ (liftTm (.app p r)))
      (rs.map (Presentation.rename wk)) (Presentation.rename wk p)
      (Presentation.rename wk target)
      (by rw [liftTm_rename]; exact CTyped.weaken hp)
      (fun r' member => by
        obtain ⟨r₀, member₀, rfl⟩ := List.mem_map.mp member
        rw [liftTm_rename]
        exact CTyped.weaken (hrs r₀ (List.mem_cons_of_mem _ member₀)))
      (by rw [liftTm_rename]; exact CTyped.weaken ht)
    obtain ⟨c, join⟩ := levels.join_exists hv hw
    exact ⟨c, (levels.join_level join).1, .piForm domain hv codomain hw join⟩
termination_by _ _ rs => rs.length
decreasing_by
  rw [List.length_map]
  exact Nat.lt_succ_self _

end Telescopes

/-! ## The names of a declaration -/

/-- The names of a declaration are distinct from one another. -/
structure DistinctNames (T : DeclName) (ctors : List (DeclName × List (Field Head)))
    (rec : DeclName) : Prop where
  ctorsNodup : (ctors.map (·.1)).Nodup
  typeNotCtor : T ∉ ctors.map (·.1)
  recNotType : rec ≠ T
  recNotCtor : rec ∉ ctors.map (·.1)

section Lookups

theorem inductiveDecls_type : inductiveDecls T u ctors rec v T = some (.head u) :=
  if_pos rfl

theorem inductiveDecls_ctor (distinct : DistinctNames T ctors rec) {i : Nat} {k : DeclName}
    {fields : List (Field Head)} (entry : ctors[i]? = some (k, fields)) :
    inductiveDecls T u ctors rec v k = some (ctorType T fields) := by
  have member : (k, fields) ∈ ctors := List.mem_of_getElem? entry
  have notType : k ≠ T := fun same =>
    distinct.typeNotCtor (same ▸ List.mem_map.mpr ⟨(k, fields), member, rfl⟩)
  unfold inductiveDecls
  rw [if_neg notType]
  cases found : ctors.find? fun e => e.1 = k with
  | none =>
    have none := List.find?_eq_none.mp found (k, fields) member
    exact absurd (decide_eq_true (rfl : (k, fields).1 = k)) none
  | some e =>
    have named : e.1 = k := by simpa using List.find?_some found
    have same : e = (k, fields) :=
      List.inj_on_of_nodup_map distinct.ctorsNodup (List.mem_of_find?_eq_some found) member named
    rw [same]

theorem inductiveDecls_rec (distinct : DistinctNames T ctors rec) :
    inductiveDecls T u ctors rec v rec = some (recType T v ctors) := by
  unfold inductiveDecls
  rw [if_neg distinct.recNotType]
  have none : (ctors.find? fun e => e.1 = rec) = none :=
    List.find?_eq_none.mpr fun e member => by
      have different : e.1 ≠ rec := fun same =>
        distinct.recNotCtor (same ▸ List.mem_map.mpr ⟨e, member, rfl⟩)
      simpa using different
  rw [none]
  exact if_pos rfl

end Lookups

/-! ## Spines of listed terms -/

theorem liftTm_liftClosed {n : Nat} (t : Tm Head 0) :
    liftTm (Presentation.liftClosed t : Tm Head n) = CTm.liftClosed (liftTm t) :=
  liftTm_rename _ t

/-- A term applied to listed terms is the term applied along the substitution that sends the
metavariables, oldest first, to them. -/
theorem applyAlong_listSub {n : Nat} : ∀ (N : Nat) (xs : List (Tm Head n)), xs.length = N →
    ∀ g : Tm Head n,
      applyAlong (fun i : Fin N => liftTm (listSub N xs i)) (liftTm g) = liftTm (appSpine g xs)
  | 0, xs, len, g => by
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero len
    rfl
  | N + 1, xs, len, g => by
    have nonempty : xs ≠ [] := fun empty => by
      rw [empty] at len
      exact Nat.succ_ne_zero N len.symm
    obtain ⟨init, last, rfl⟩ : ∃ init last, xs = init ++ [last] :=
      ⟨xs.dropLast, xs.getLast nonempty, (List.dropLast_append_getLast nonempty).symm⟩
    have initLen : init.length = N := by
      rw [List.length_append, List.length_singleton] at len
      exact Nat.succ.inj len
    have tail : (fun i : Fin N => liftTm (listSub (N + 1) (init ++ [last]) i.succ)) =
        fun i : Fin N => liftTm (listSub N init i) := funext fun i => by
      show liftTm ((init ++ [last]).getD (N + 1 - 1 - (i.val + 1)) defaultTm) =
        liftTm (init.getD (N - 1 - i.val) defaultTm)
      have index : N + 1 - 1 - (i.val + 1) = N - 1 - i.val := by omega
      have below : N - 1 - i.val < init.length := by
        have := i.isLt
        omega
      rw [index, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left below]
    have head : listSub (N + 1) (init ++ [last]) 0 = last := by
      show (init ++ [last]).getD (N + 1 - 1 - 0) defaultTm = last
      rw [show N + 1 - 1 - 0 = init.length by omega, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [appSpine_concat]
    show CTm.app
        (applyAlong (fun i : Fin N => liftTm (listSub (N + 1) (init ++ [last]) i.succ)) (liftTm g))
        (liftTm (listSub (N + 1) (init ++ [last]) 0)) =
      CTm.app (liftTm (appSpine g init)) (liftTm last)
    rw [tail, head, applyAlong_listSub N init initLen g]

/-! ## The constants of a declaration in a package -/

section Constants

variable {L : Type} [LevelOrder L] {R : Rules Head}

/-- **A package with a simple inductive declaration**: the sum of the package and the package
of the declaration. -/
abbrev withInductive (B : ChurchRules R) (T : DeclName) (u : Head)
    (ctors : List (DeclName × List (Field Head))) (rec : DeclName) (v : Head) :
    ChurchRules (Rules.sum R (inductiveRules R T u ctors rec v)) :=
  B.sum (inductiveChurch R T u ctors rec v)

/-- The names of a declaration are new to a package. -/
structure NewNames (B : ChurchRules R) (T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (rec : DeclName) : Prop where
  typeNew : B.constantType T = none
  ctorsNew : ∀ entry ∈ ctors, B.constantType entry.1 = none
  recNew : B.constantType rec = none

/-- The closed field types of the constructors are types of a package. -/
def FieldsFormed (B : ChurchRules R) (ctors : List (DeclName × List (Field Head))) : Prop :=
  ∀ entry ∈ ctors, ∀ F, (.closed F : Field Head) ∈ entry.2 → CIsType B .nil (liftTm F)

variable (levels : LevelModel R L) (B : ChurchRules R)

theorem sum_type_declared (new : NewNames B T ctors rec) :
    (withInductive B T u ctors rec v).constantType T = some (.head u) :=
  (sumDecls_right new.typeNew).trans (elabDeclarations_lamFree _ inductiveDecls_type rfl)

theorem sum_ctor_declared (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) :
    (withInductive B T u ctors rec v).constantType k = some (liftTm (ctorType T fields)) :=
  (sumDecls_right (new.ctorsNew _ (List.mem_of_getElem? entry))).trans
    (elabDeclarations_lamFree _ (inductiveDecls_ctor distinct entry)
      (lamFree_ctorType T fun F member => free _ (List.mem_of_getElem? entry) F member))

theorem sum_rec_declared (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) :
    (withInductive B T u ctors rec v).constantType rec = some (liftTm (recType T v ctors)) :=
  (sumDecls_right new.recNew).trans
    (elabDeclarations_lamFree _ (inductiveDecls_rec distinct) (lamFree_recType _ v free))

end Constants

/-! ## The constants of a declaration in every package that declares them -/

section Declared

variable {L : Type} [LevelOrder L] {R : Rules Head} (levels : LevelModel R L)
  {Q : ChurchRules R}

/-- **A package declares the type of a simple inductive declaration**: the type is declared in
its universe, and every closed field type is a type of the package. The package with the
declaration is one (`withInductive_declaresDataType`); a package with the type and without the
recursor is another. -/
structure DeclaresDataType (Q : ChurchRules R) (T : DeclName) (u : Head)
    (ctors : List (DeclName × List (Field Head))) : Prop where
  typeUniverse : R.isUniverse u
  typeDeclared : Q.constantType T = some (.head u)
  fieldsFormed : FieldsFormed Q ctors

/-- **A package declares the constructors** of a simple inductive declaration as well, each at
its declared type. -/
structure DeclaresDataCtors (Q : ChurchRules R) (T : DeclName) (u : Head)
    (ctors : List (DeclName × List (Field Head))) : Prop extends DeclaresDataType Q T u ctors where
  ctor : ∀ {i : Nat} {k : DeclName} {fields : List (Field Head)}, ctors[i]? = some (k, fields) →
    Q.constantType k = some (liftTm (ctorType T fields))

include levels in
/-- **A type declared in a universe is a type of it**, in every context. -/
theorem typeConst_typed (hu : R.isUniverse u) (declared : Q.constantType T = some (.head u))
    {n : Nat} {Γ : CCtx Head n} : CTyped Q Γ (.const T) (.head u) := by
  obtain ⟨u', hu', typing, -⟩ := levels.successor hu
  exact CDerivable.const (type := .head u) (u := u') declared (.headType typing) hu'

namespace DeclaresDataType

variable (decl : DeclaresDataType Q T u ctors)
include levels decl

/-- The type of a field is a type, in every context. -/
theorem fieldType_formed {entry : DeclName × List (Field Head)} (member : entry ∈ ctors)
    {field : Field Head} (among : field = .recursive ∨ field ∈ entry.2) {n : Nat}
    {Γ : CCtx Head n} : CIsType Q Γ (liftTm (field.type T)).liftClosed := by
  cases field with
  | recursive =>
    exact ⟨u, decl.typeUniverse, typeConst_typed levels decl.typeUniverse decl.typeDeclared⟩
  | closed F =>
    have listed : (.closed F : Field Head) ∈ entry.2 := among.resolve_left (fun h => nomatch h)
    exact (decl.fieldsFormed entry member F listed).liftClosed

/-- **The declared type of a constructor is a type.** -/
theorem ctorType_formed {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) : CIsType Q .nil (liftTm (ctorType T fields)) := by
  refine closeType_formed levels (ctorEntry T fields) fields.length (.const T)
    (fun j _ => ?_)
    ⟨u, decl.typeUniverse, typeConst_typed levels decl.typeUniverse decl.typeDeclared⟩
  rw [ctorEntry, liftTm_liftClosed]
  refine decl.fieldType_formed levels (List.mem_of_getElem? entry) ?_
  cases found : fields.getD j .recursive with
  | recursive => exact .inl rfl
  | closed F => exact .inr (closed_mem_of_getD found)

end DeclaresDataType

namespace DeclaresDataCtors

variable (decl : DeclaresDataCtors Q T u ctors)
include levels decl

/-- **A constructor has its declared type**, in every context. -/
theorem ctor_typed {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n} :
    CTyped Q Γ (.const k) (liftTm (ctorType T fields)).liftClosed := by
  obtain ⟨w, hw, formed⟩ := decl.toDeclaresDataType.ctorType_formed levels entry
  exact CDerivable.const (decl.ctor entry) formed hw

/-- **A constructor applied along a substitution typed along its fields** is a term of the
declared type. -/
theorem ctor_applied {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n}
    {σ : CSub Head fields.length n} (typed : CSubstMor Q (liftCtx (ctorTele T fields)) Γ σ) :
    CTyped Q Γ (applyAlong σ (.const k)) (.const T) :=
  applyAlong_typed (ctorEntry T fields) fields.length (.const T) σ typed
    (decl.ctor_typed levels entry)

/-- **A constructor applied to listed terms of the types of its fields** is a term of the
declared type. -/
theorem ctor_spine_typed {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n} {xs : List (Tm Head n)}
    (typed : List.Forall₂ (fun x (field : Field Head) =>
      CTyped Q Γ (liftTm x) (liftTm (field.type T)).liftClosed) xs fields) :
    CTyped Q Γ (liftTm (appSpine (.const k) xs)) (.const T) := by
  obtain ⟨length, pointwise⟩ := List.forall₂_iff_get.mp typed
  rw [← applyAlong_listSub fields.length xs length (.const k)]
  refine decl.ctor_applied levels entry fun j => ?_
  have below : fields.length - 1 - j.val < fields.length := by
    have := j.isLt
    omega
  rw [liftCtx_lookup, ctorTele,
    show ofEntries (ctorEntry T fields) fields.length =
      ofEntries (fun j => Presentation.liftClosed ((fields.getD j .recursive).type T))
        fields.length from rfl,
    ofEntries_lookup_closed, liftTm_liftClosed, CTm.subst_liftClosed]
  have belowLeft : fields.length - 1 - j.val < xs.length := by
    rw [length]
    exact below
  have left : xs.getD (fields.length - 1 - j.val) defaultTm =
      xs.get ⟨fields.length - 1 - j.val, belowLeft⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem belowLeft]
    rfl
  have right : fields.getD (fields.length - 1 - j.val) .recursive =
      fields.get ⟨fields.length - 1 - j.val, below⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem below]
    rfl
  show CTyped _ Γ (liftTm (xs.getD (fields.length - 1 - j.val) defaultTm))
    (liftTm ((fields.getD (fields.length - 1 - j.val) .recursive).type T)).liftClosed
  rw [left, right]
  exact pointwise _ _ _

/-- **The type of a method with some of its fields bound is a type**: over a motive, the
fields bound so far at the types of the constructor's first fields, and the recursive ones
among them. -/
theorem caseFields_formed (hv : R.isUniverse v) {i : Nat} {k : DeclName}
    {allFields : List (Field Head)} (entry : ctors[i]? = some (k, allFields)) :
    ∀ (fs done : List (Field Head)) {n : Nat} {Γ : CCtx Head n} (p : Tm Head n)
      (xs recs : List (Tm Head n)), done ++ fs = allFields →
      CTyped Q Γ (liftTm p) (.pi (.const T) (.head v)) →
      List.Forall₂ (fun x (field : Field Head) =>
        CTyped Q Γ (liftTm x) (liftTm (field.type T)).liftClosed) xs done →
      (∀ r ∈ recs, CTyped Q Γ (liftTm r) (.const T)) →
      CIsType Q Γ (liftTm (caseFields T k fs p xs recs))
  | [], done, _, Γ, p, xs, recs, split, hp, hxs, hrecs => by
    obtain rfl : done = allFields := by rw [← split, List.append_nil]
    exact caseHyps_formed levels hv recs p _ hp hrecs (decl.ctor_spine_typed levels entry hxs)
  | .recursive :: fs, done, n, Γ, p, xs, recs, split, hp, hxs, hrecs => by
    have domain : CTyped Q Γ (.const T) (.head u) :=
      typeConst_typed levels decl.typeUniverse decl.typeDeclared
    have weakened : List.Forall₂ (fun x (field : Field Head) =>
        CTyped Q (.snoc Γ (.const T)) (liftTm x)
          (liftTm (field.type T)).liftClosed) (xs.map (Presentation.rename wk)) done :=
      List.forall₂_map_left_iff.mpr (hxs.imp fun x field typed => by
        rw [liftTm_rename]
        simpa only [CTm.rename_liftClosed] using CTyped.weaken (E := .const T) typed)
    obtain ⟨w, hw, codomain⟩ := caseFields_formed hv entry fs
      (done ++ [.recursive]) (Γ := .snoc Γ (.const T)) (Presentation.rename wk p)
      (xs.map (Presentation.rename wk) ++ [.var 0])
      (recs.map (Presentation.rename wk) ++ [.var 0])
      (by rw [List.append_assoc]; exact split)
      (by rw [liftTm_rename]; exact CTyped.weaken hp)
      (forall₂_concat weakened (CDerivable.var (Γ := .snoc Γ (.const T)) 0))
      (fun r member => by
        rcases List.mem_append.mp member with older | newest
        · obtain ⟨r₀, member₀, rfl⟩ := List.mem_map.mp older
          rw [liftTm_rename]
          exact CTyped.weaken (hrecs r₀ member₀)
        · obtain rfl := List.mem_singleton.mp newest
          exact CDerivable.var (Γ := .snoc Γ (.const T)) 0)
    obtain ⟨c, join⟩ := levels.join_exists decl.typeUniverse hw
    exact ⟨c, (levels.join_level join).1, .piForm domain decl.typeUniverse codomain hw join⟩
  | .closed F :: fs, done, n, Γ, p, xs, recs, split, hp, hxs, hrecs => by
    have listed : (.closed F : Field Head) ∈ allFields := by
      rw [← split]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨a, ha, domain⟩ : CIsType Q Γ
        (liftTm (Presentation.liftClosed F : Tm Head n)) := by
      rw [liftTm_liftClosed]
      exact decl.toDeclaresDataType.fieldType_formed levels (List.mem_of_getElem? entry)
        (field := .closed F) (.inr listed)
    have weakened : List.Forall₂ (fun x (field : Field Head) =>
        CTyped Q (.snoc Γ (liftTm (Presentation.liftClosed F : Tm Head n))) (liftTm x)
          (liftTm (field.type T)).liftClosed) (xs.map (Presentation.rename wk)) done :=
      List.forall₂_map_left_iff.mpr (hxs.imp fun x field typed => by
        rw [liftTm_rename]
        simpa only [CTm.rename_liftClosed] using
          CTyped.weaken (E := liftTm (Presentation.liftClosed F : Tm Head n)) typed)
    have newest : CTyped Q
        (.snoc Γ (liftTm (Presentation.liftClosed F : Tm Head n))) (liftTm (.var 0))
        (liftTm ((Field.closed F).type T)).liftClosed := by
      have type : (liftTm (Presentation.liftClosed F : Tm Head n)).rename wk =
          (liftTm F).liftClosed := by
        rw [liftTm_liftClosed, CTm.rename_liftClosed]
      have bound := CDerivable.var (P := Q)
        (Γ := .snoc Γ (liftTm (Presentation.liftClosed F : Tm Head n))) 0
      rw [CCtx.lookup_snoc_zero, type] at bound
      exact bound
    obtain ⟨w, hw, codomain⟩ := caseFields_formed hv entry fs
      (done ++ [.closed F]) (Γ := .snoc Γ (liftTm (Presentation.liftClosed F : Tm Head n)))
      (Presentation.rename wk p) (xs.map (Presentation.rename wk) ++ [.var 0])
      (recs.map (Presentation.rename wk))
      (by rw [List.append_assoc]; exact split)
      (by rw [liftTm_rename]; exact CTyped.weaken hp)
      (forall₂_concat weakened newest)
      (fun r member => by
        obtain ⟨r₀, member₀, rfl⟩ := List.mem_map.mp member
        rw [liftTm_rename]
        exact CTyped.weaken (hrecs r₀ member₀))
    obtain ⟨c, join⟩ := levels.join_exists ha hw
    exact ⟨c, (levels.join_level join).1, .piForm domain ha codomain hw join⟩

/-- **Each entry of the recursor's telescope is a type** over the entries before it: the type
of motives, the types of the methods over the motive, and the declared type. -/
theorem recEntry_formed (hv : R.isUniverse v) :
    ∀ j, CIsType Q (liftCtx (ofEntries (recEntry T v ctors) j)) (liftTm (recEntry T v ctors j))
  | 0 => by
    obtain ⟨v', hv', typing, -⟩ := levels.successor hv
    obtain ⟨c, join⟩ := levels.join_exists decl.typeUniverse hv'
    exact ⟨c, (levels.join_level join).1,
      .piForm (typeConst_typed levels decl.typeUniverse decl.typeDeclared) decl.typeUniverse
        (.headType typing) hv' join⟩
  | j + 1 => by
    cases entry : ctors[j]? with
    | none =>
      have unfolded : recEntry T v ctors (j + 1) = .const T := by simp [recEntry, entry]
      rw [unfolded]
      exact ⟨u, decl.typeUniverse, typeConst_typed levels decl.typeUniverse decl.typeDeclared⟩
    | some pair =>
      obtain ⟨k, fields⟩ := pair
      rw [recEntry_method T v ctors entry]
      refine decl.caseFields_formed levels hv entry fields []
        (.var (Fin.last j)) [] [] rfl ?_ .nil (fun _ member => nomatch member)
      have motive := CDerivable.var (P := Q)
        (Γ := liftCtx (ofEntries (recEntry T v ctors) (j + 1))) (Fin.last j)
      rw [lookup_last] at motive
      exact motive

/-- **The declared type of the recursor is a type.** -/
theorem recType_formed (hv : R.isUniverse v) : CIsType Q .nil (liftTm (recType T v ctors)) := by
  refine closeType_formed levels (recEntry T v ctors) (ctors.length + 2)
    (recBody ctors.length)
    (fun j _ => decl.recEntry_formed levels hv j) ⟨v, hv, ?_⟩
  have motive := CDerivable.var (P := Q)
    (Γ := liftCtx (ofEntries (recEntry T v ctors) (ctors.length + 2)))
    (Fin.last (ctors.length + 1))
  rw [lookup_last] at motive
  have scrutinee := CDerivable.var (P := Q)
    (Γ := liftCtx (ofEntries (recEntry T v ctors) (ctors.length + 2))) 0
  change CTyped _ _ (.var 0) ((liftTm (recEntry T v ctors (ctors.length + 1))).rename wk)
    at scrutinee
  rw [recEntry_scrutinee] at scrutinee
  exact .appElim motive scrutinee

end DeclaresDataCtors

end Declared

/-! ## The constants of a declaration in the package with it -/

section Constants

variable {L : Type} [LevelOrder L] {R : Rules Head}
variable (levels : LevelModel R L) (B : ChurchRules R)

/-- **The package with a simple inductive declaration declares its type**, when the type's
universe is a universe, its names are new and its closed field types are types. -/
theorem withInductive_declaresDataType (hu : R.isUniverse u) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) :
    DeclaresDataType (withInductive B T u ctors rec v) T u ctors where
  typeUniverse := hu
  typeDeclared := sum_type_declared B new
  fieldsFormed := fun entry member F field =>
    let ⟨w, hw, typed⟩ := fieldsFormed entry member F field
    ⟨w, hw, CDerivable.sum_left _ typed⟩

/-- **The package with a simple inductive declaration declares its constructors.** -/
theorem withInductive_declaresDataCtors (hu : R.isUniverse u)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) :
    DeclaresDataCtors (withInductive B T u ctors rec v) T u ctors :=
  { withInductive_declaresDataType B hu new fieldsFormed with
    ctor := fun entry => sum_ctor_declared B distinct free new entry }

include levels in
/-- **The declared type is a type of its universe**, in every context. -/
theorem type_typed (hu : R.isUniverse u) (new : NewNames B T ctors rec) {n : Nat}
    {Γ : CCtx Head n} : CTyped (withInductive B T u ctors rec v) Γ (.const T) (.head u) :=
  typeConst_typed (LevelModel.sum levels _) hu (sum_type_declared B new)

include levels in
/-- The type of a field is a type, in every context. -/
theorem fieldType_formed (hu : R.isUniverse u) (new : NewNames B T ctors rec)
    {entry : DeclName × List (Field Head)} (member : entry ∈ ctors)
    (fieldsFormed : FieldsFormed B ctors) {field : Field Head} (among : field = .recursive ∨
      field ∈ entry.2) {n : Nat} {Γ : CCtx Head n} :
    CIsType (withInductive B T u ctors rec v) Γ (liftTm (field.type T)).liftClosed :=
  (withInductive_declaresDataType (v := v) B hu new fieldsFormed).fieldType_formed
    (LevelModel.sum levels _) member among

include levels in
/-- **The declared type of a constructor is a type.** -/
theorem ctorType_formed (hu : R.isUniverse u) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) :
    CIsType (withInductive B T u ctors rec v) .nil (liftTm (ctorType T fields)) :=
  (withInductive_declaresDataType (v := v) B hu new fieldsFormed).ctorType_formed
    (LevelModel.sum levels _) entry

include levels in
/-- **A constructor has its declared type**, in every context. -/
theorem ctor_typed (hu : R.isUniverse u) (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n} :
    CTyped (withInductive B T u ctors rec v) Γ (.const k)
      (liftTm (ctorType T fields)).liftClosed :=
  (withInductive_declaresDataCtors (v := v) B hu distinct free new fieldsFormed).ctor_typed
    (LevelModel.sum levels _) entry

include levels in
/-- **A constructor applied along a substitution typed along its fields** is a term of the
declared type. -/
theorem ctor_applied (hu : R.isUniverse u) (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n}
    {σ : CSub Head fields.length n}
    (typed : CSubstMor (withInductive B T u ctors rec v) (liftCtx (ctorTele T fields)) Γ σ) :
    CTyped (withInductive B T u ctors rec v) Γ (applyAlong σ (.const k)) (.const T) :=
  (withInductive_declaresDataCtors (v := v) B hu distinct free new fieldsFormed).ctor_applied
    (LevelModel.sum levels _) entry typed

include levels in
/-- **A constructor applied to listed terms of the types of its fields** is a term of the
declared type. -/
theorem ctor_spine_typed (hu : R.isUniverse u) (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n} {xs : List (Tm Head n)}
    (typed : List.Forall₂ (fun x (field : Field Head) =>
      CTyped (withInductive B T u ctors rec v) Γ (liftTm x) (liftTm (field.type T)).liftClosed)
      xs fields) :
    CTyped (withInductive B T u ctors rec v) Γ (liftTm (appSpine (.const k) xs)) (.const T) :=
  (withInductive_declaresDataCtors (v := v) B hu distinct free new fieldsFormed).ctor_spine_typed
    (LevelModel.sum levels _) entry typed

include levels in
/-- **The type of a method with some of its fields bound is a type**: over a motive, the
fields bound so far at the types of the constructor's first fields, and the recursive ones
among them. -/
theorem caseFields_formed (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName}
    {allFields : List (Field Head)} (entry : ctors[i]? = some (k, allFields)) :
    ∀ (fs done : List (Field Head)) {n : Nat} {Γ : CCtx Head n} (p : Tm Head n)
      (xs recs : List (Tm Head n)), done ++ fs = allFields →
      CTyped (withInductive B T u ctors rec v) Γ (liftTm p) (.pi (.const T) (.head v)) →
      List.Forall₂ (fun x (field : Field Head) =>
        CTyped (withInductive B T u ctors rec v) Γ (liftTm x)
          (liftTm (field.type T)).liftClosed) xs done →
      (∀ r ∈ recs, CTyped (withInductive B T u ctors rec v) Γ (liftTm r) (.const T)) →
      CIsType (withInductive B T u ctors rec v) Γ (liftTm (caseFields T k fs p xs recs)) :=
  (withInductive_declaresDataCtors (v := v) B hu distinct free new fieldsFormed).caseFields_formed
    (LevelModel.sum levels _) hv entry

include levels in
/-- **Each entry of the recursor's telescope is a type** over the entries before it: the type
of motives, the types of the methods over the motive, and the declared type. -/
theorem recEntry_formed (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) :
    ∀ j, CIsType (withInductive B T u ctors rec v) (liftCtx (ofEntries (recEntry T v ctors) j))
      (liftTm (recEntry T v ctors j)) :=
  (withInductive_declaresDataCtors (v := v) B hu distinct free new fieldsFormed).recEntry_formed
    (LevelModel.sum levels _) hv

include levels in
/-- **The declared type of the recursor is a type.** -/
theorem recType_formed (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) :
    CIsType (withInductive B T u ctors rec v) .nil (liftTm (recType T v ctors)) :=
  (withInductive_declaresDataCtors (v := v) B hu distinct free new fieldsFormed).recType_formed
    (LevelModel.sum levels _) hv

include levels in
/-- **The recursor has its declared type**, in every context. -/
theorem rec_typed (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) {n : Nat}
    {Γ : CCtx Head n} :
    CTyped (withInductive B T u ctors rec v) Γ (.const rec)
      (liftTm (recType T v ctors)).liftClosed := by
  obtain ⟨w, hw, formed⟩ := recType_formed levels B hu hv distinct free new fieldsFormed
  exact CDerivable.const (sum_rec_declared B distinct free new) formed hw

include levels in
/-- **The typing of the recursor**: applied along a substitution typed along its telescope,
that is to a motive, a method for each constructor and a term of the declared type, the
recursor has the motive's type at that term. -/
theorem rec_applied (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) {n : Nat}
    {Γ : CCtx Head n} {σ : CSub Head (ctors.length + 2) n}
    (typed : CSubstMor (withInductive B T u ctors rec v) (liftCtx (recTele T v ctors)) Γ σ) :
    CTyped (withInductive B T u ctors rec v) Γ (applyAlong σ (.const rec))
      (.app (σ (Fin.last (ctors.length + 1))) (σ 0)) :=
  applyAlong_typed (recEntry T v ctors) (ctors.length + 2) (recBody ctors.length) σ typed
    (rec_typed levels B hu hv distinct free new fieldsFormed)

end Constants

/-! ## Annotation and substitution -/

theorem liftSub_lift {n m : Nat} (τ : Sub Head n m) :
    (fun i => liftTm (Presentation.liftSub τ i)) = CTm.liftSub fun i => liftTm (τ i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact liftTm_rename wk (τ j)

/-- The annotation of a substituted term is the annotation substituted by the annotations. -/
theorem liftTm_subst {n m : Nat} (τ : Sub Head n m) (t : Tm Head n) :
    liftTm (Presentation.subst τ t) = (liftTm t).subst fun i => liftTm (τ i) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB =>
    show CTm.pi (liftTm (Presentation.subst τ A))
        (liftTm (Presentation.subst (Presentation.liftSub τ) B)) =
      CTm.pi ((liftTm A).subst fun i => liftTm (τ i))
        ((liftTm B).subst (CTm.liftSub fun i => liftTm (τ i)))
    rw [ihA, ihB, liftSub_lift]
  | sigma A B ihA ihB =>
    show CTm.sigma (liftTm (Presentation.subst τ A))
        (liftTm (Presentation.subst (Presentation.liftSub τ) B)) =
      CTm.sigma ((liftTm A).subst fun i => liftTm (τ i))
        ((liftTm B).subst (CTm.liftSub fun i => liftTm (τ i)))
    rw [ihA, ihB, liftSub_lift]
  | id A a b ihA iha ihb =>
    show CTm.id (liftTm (Presentation.subst τ A)) (liftTm (Presentation.subst τ a))
        (liftTm (Presentation.subst τ b)) = _
    rw [ihA, iha, ihb]
    rfl
  | lam b ih =>
    show CTm.lam CTm.unknown.liftClosed
        (liftTm (Presentation.subst (Presentation.liftSub τ) b)) =
      CTm.lam (CTm.unknown.liftClosed.subst fun i => liftTm (τ i))
        ((liftTm b).subst (CTm.liftSub fun i => liftTm (τ i)))
    rw [ih, liftSub_lift, CTm.subst_liftClosed]
  | app f a ihf iha =>
    show CTm.app (liftTm (Presentation.subst τ f)) (liftTm (Presentation.subst τ a)) = _
    rw [ihf, iha]
    rfl
  | pair a b iha ihb =>
    show CTm.pair (liftTm (Presentation.subst τ a)) (liftTm (Presentation.subst τ b)) = _
    rw [iha, ihb]
    rfl
  | fst p ih =>
    show CTm.fst (liftTm (Presentation.subst τ p)) = _
    rw [ih]
    rfl
  | snd p ih =>
    show CTm.snd (liftTm (Presentation.subst τ p)) = _
    rw [ih]
    rfl
  | refl a ih =>
    show CTm.refl (liftTm (Presentation.subst τ a)) = _
    rw [ih]
    rfl

/-- The annotation of an opened binder is the annotation opened at the annotation. -/
theorem liftTm_inst0 {n : Nat} (a : Tm Head n) (B : Tm Head (n + 1)) :
    liftTm (Presentation.inst0 a B) = CTm.inst0 (liftTm a) (liftTm B) := by
  show liftTm (Presentation.subst (Presentation.subst0 a) B) = (liftTm B).subst (CTm.subst0 (liftTm a))
  rw [liftTm_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-! ## Positions of a telescope -/

/-- The shift of the variables of a position of a telescope over the later entries. -/
def shiftRen (q N d : Nat) (h : q + d = N) : Ren q N := fun j => ⟨j.val + d, by
  have := j.isLt
  omega⟩

/-- **The entry of a telescope seen from a later position** is the entry renamed by the shift
over the entries after it. -/
theorem ofEntries_lookup (entry : (j : Nat) → Tm Head j) :
    ∀ (N i : Nat) (hi : i < N) (q : Nat) (h : q + (i + 1) = N),
      Ctx.lookup (ofEntries entry N) ⟨i, hi⟩ =
        Presentation.rename (shiftRen q N (i + 1) h) (entry q)
  | N + 1, 0, _, q, h => by
    obtain rfl : q = N := by omega
    show Presentation.rename wk (entry q) = _
    exact rename_ext (fun j => Fin.ext rfl) (entry q)
  | N + 1, i + 1, hi, q, h => by
    show Presentation.rename wk
        (Ctx.lookup (ofEntries entry N) ⟨i, Nat.lt_of_succ_lt_succ hi⟩) = _
    rw [ofEntries_lookup entry N i (Nat.lt_of_succ_lt_succ hi) q (by omega), rename_comp]
    exact rename_ext (fun j => Fin.ext rfl) (entry q)

/-- The metavariable at a position, the oldest first. -/
theorem metaVars_getElem? (N q i : Nat) (hi : i < N) (h : q + (i + 1) = N) :
    (metaVars (Head := Head) N)[q]? = some (.var ⟨i, hi⟩) := by
  have hq : q < (List.finRange N).reverse.length := by
    rw [List.length_reverse, List.length_finRange]
    omega
  rw [metaVars, List.getElem?_map, List.getElem?_eq_getElem hq, List.getElem_reverse]
  simp only [List.length_finRange, List.getElem_finRange, Option.map_some]
  congr 2
  apply Fin.ext
  show N - 1 - q = i
  omega

section Judgment

variable {R : Rules Head} {Q : ChurchRules R}

/-- **A metavariable of a telescope has the type of its entry**, shifted over the later
entries. -/
theorem metaVar_typed (entry : (j : Nat) → Tm Head j) (N q i : Nat) (hi : i < N)
    (h : q + (i + 1) = N) :
    CTyped Q (liftCtx (ofEntries entry N)) (.var ⟨i, hi⟩)
      (liftTm (Presentation.rename (shiftRen q N (i + 1) h) (entry q))) := by
  have typed := CDerivable.var (P := Q) (Γ := liftCtx (ofEntries entry N)) ⟨i, hi⟩
  rw [liftCtx_lookup, ofEntries_lookup entry N i hi q h] at typed
  exact typed

/-- **A term of a closed telescope type applied to listed terms**, each of the type of its
entry at the terms before it, has the target at the listed terms. -/
theorem spine_typed (entry : (j : Nat) → Tm Head j) (m : Nat) (C : Tm Head m) {n : Nat}
    {Γ : CCtx Head n} (xs : List (Tm Head n)) (len : xs.length = m) {g : Tm Head n}
    (function : CTyped Q Γ (liftTm g) (liftTm (closeType (ofEntries entry m) C)).liftClosed)
    (arguments : ∀ (q : Nat) (x : Tm Head n), xs[q]? = some x →
      CTyped Q Γ (liftTm x) (argType entry xs q)) :
    CTyped Q Γ (liftTm (appSpine g xs)) ((liftTm C).subst (argSub xs m)) := by
  rw [← applyAlong_listSub m xs len g]
  refine applyAlong_typed entry m C (argSub xs m) (fun i => ?_) function
  obtain ⟨i, hi⟩ := i
  have position : (m - 1 - i) + (i + 1) = m := by omega
  have below : m - 1 - i < xs.length := by omega
  rw [liftCtx_lookup, ofEntries_lookup entry m i hi (m - 1 - i) position, liftTm_rename,
    CTm.subst_rename]
  have same : (fun j => argSub xs m (shiftRen (m - 1 - i) m (i + 1) position j)) =
      argSub xs (m - 1 - i) := funext fun j => by
    show liftTm (xs.getD (m - 1 - (j.val + (i + 1))) defaultTm) =
      liftTm (xs.getD (m - 1 - i - 1 - j.val) defaultTm)
    rw [show m - 1 - (j.val + (i + 1)) = m - 1 - i - 1 - j.val by omega]
  rw [same]
  have element := arguments (m - 1 - i) xs[m - 1 - i] (List.getElem?_eq_getElem below)
  show CTyped Q Γ (liftTm (xs.getD (m - 1 - i) defaultTm)) (argType entry xs (m - 1 - i))
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem below]
  exact element

/-- **A term of the type of induction hypotheses applied to them** has the motive's type at
the target. -/
theorem caseHyps_applied : ∀ {n : Nat} {Γ : CCtx Head n} (rs : List (Tm Head n))
    (p target g : Tm Head n) (hs : List (Tm Head n)),
    CTyped Q Γ (liftTm g) (liftTm (caseHyps p rs target)) →
    List.Forall₂ (fun h r => CTyped Q Γ (liftTm h) (liftTm (.app p r))) hs rs →
    CTyped Q Γ (liftTm (appSpine g hs)) (liftTm (.app p target))
  | _, _, [], p, target, g, _, typed, .nil => by
    rw [caseHyps_nil] at typed
    exact typed
  | _, Γ, r :: rs, p, target, g, _, typed, .cons (a := h) (l₁ := hs) head tail => by
    rw [caseHyps_cons] at typed
    have applied : CTyped Q Γ (liftTm (.app g h))
        (CTm.inst0 (liftTm h) (liftTm (caseHyps (Presentation.rename wk p)
          (rs.map (Presentation.rename wk)) (Presentation.rename wk target)))) :=
      CDerivable.appElim typed head
    rw [← liftTm_inst0, inst0_caseHyps] at applied
    rw [appSpine_cons]
    exact caseHyps_applied rs p target (.app g h) hs applied tail

/-- **A method applied to its fields and to the induction hypotheses** has the motive's type
at the constructor applied to the fields: for a term of the type of a method with some fields
bound, the remaining fields at their types, and a term of the motive's type at each recursive
field. -/
theorem caseFields_applied (T k : DeclName) : ∀ (fs : List (Field Head)) {n : Nat}
    {Γ : CCtx Head n} (p : Tm Head n) (xs recs args hs : List (Tm Head n)) (g : Tm Head n),
    CTyped Q Γ (liftTm g) (liftTm (caseFields T k fs p xs recs)) →
    List.Forall₂ (fun x (field : Field Head) =>
      CTyped Q Γ (liftTm x) (liftTm (field.type T)).liftClosed) args fs →
    List.Forall₂ (fun h r => CTyped Q Γ (liftTm h) (liftTm (.app p r))) hs
      (recs ++ recArgs fs args) →
    CTyped Q Γ (liftTm (appSpine g (args ++ hs)))
      (liftTm (.app p (appSpine (.const k) (xs ++ args))))
  | [], n, Γ, p, xs, recs, _, hs, g, typed, .nil, results => by
    have hypotheses : List.Forall₂ (fun h r => CTyped Q Γ (liftTm h) (liftTm (.app p r)))
        hs recs := by
      have same : recs ++ recArgs ([] : List (Field Head)) ([] : List (Tm Head n)) = recs :=
        List.append_nil recs
      rw [same] at results
      exact results
    have applied := caseHyps_applied recs p (appSpine (.const k) xs) g hs typed hypotheses
    rw [List.nil_append, List.append_nil]
    exact applied
  | .recursive :: fs, n, Γ, p, xs, recs, _, hs, g, typed,
      .cons (a := a) (l₁ := args) head tail, results => by
    have function : CTyped Q Γ (liftTm g)
        (.pi (.const T) (liftTm (caseFields T k fs (Presentation.rename wk p)
          (xs.map (Presentation.rename wk) ++ [.var 0])
          (recs.map (Presentation.rename wk) ++ [.var 0])))) := typed
    have argument : CTyped Q Γ (liftTm a) (.const T) := head
    have applied : CTyped Q Γ (liftTm (.app g a))
        (CTm.inst0 (liftTm a) (liftTm (caseFields T k fs (Presentation.rename wk p)
          (xs.map (Presentation.rename wk) ++ [.var 0])
          (recs.map (Presentation.rename wk) ++ [.var 0])))) :=
      CDerivable.appElim function argument
    rw [← liftTm_inst0, inst0_caseFields T k fs a p xs recs [.var 0] [a] rfl] at applied
    have rest := caseFields_applied T k fs p (xs ++ [a]) (recs ++ [a]) args hs (.app g a)
      applied tail (by
        rw [List.append_assoc]
        exact results)
    rw [List.append_assoc] at rest
    exact rest
  | .closed F :: fs, n, Γ, p, xs, recs, _, hs, g, typed,
      .cons (a := a) (l₁ := args) head tail, results => by
    have function : CTyped Q Γ (liftTm g)
        (.pi (liftTm (Presentation.liftClosed F : Tm Head n))
          (liftTm (caseFields T k fs (Presentation.rename wk p)
            (xs.map (Presentation.rename wk) ++ [.var 0])
            (recs.map (Presentation.rename wk))))) := typed
    have argument : CTyped Q Γ (liftTm a) (liftTm (Presentation.liftClosed F : Tm Head n)) := by
      rw [liftTm_liftClosed]
      exact head
    have applied : CTyped Q Γ (liftTm (.app g a))
        (CTm.inst0 (liftTm a) (liftTm (caseFields T k fs (Presentation.rename wk p)
          (xs.map (Presentation.rename wk) ++ [.var 0])
          (recs.map (Presentation.rename wk) ++ [])))) := by
      rw [List.append_nil]
      exact CDerivable.appElim function argument
    rw [← liftTm_inst0, inst0_caseFields T k fs a p xs recs [] [] rfl, List.append_nil]
      at applied
    have rest := caseFields_applied T k fs p (xs ++ [a]) recs args hs (.app g a) applied tail
      results
    rw [List.append_assoc] at rest
    exact rest

/-- The recursive arguments among terms of the types of the fields are terms of the declared
type. -/
theorem recArgs_typed (T : DeclName) {n : Nat} {Γ : CCtx Head n} :
    ∀ (fs : List (Field Head)) (args : List (Tm Head n)),
    List.Forall₂ (fun x (field : Field Head) =>
      CTyped Q Γ (liftTm x) (liftTm (field.type T)).liftClosed) args fs →
    ∀ r ∈ recArgs fs args, CTyped Q Γ (liftTm r) (.const T)
  | .recursive :: fs, _, .cons (a := a) (l₁ := args) head tail, r, member => by
    rcases List.mem_cons.mp member with rfl | later
    · exact head
    · exact recArgs_typed T fs args tail r later
  | .closed _ :: fs, _, .cons (l₁ := args) _ tail, r, member =>
    recArgs_typed T fs args tail r member
  | [], _, .nil, _, member => nomatch member

end Judgment

/-! ## The two sides of a computation rule -/

/-- The value of a list at a position where it has one. -/
theorem getD_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (found : l[i]? = some x)
    (d : α) : l.getD i d = x := by
  rw [List.getD_eq_getElem?_getD, found]
  rfl

/-- The motive metavariable of a computation rule: the oldest one. -/
def iotaMotive (c a : Nat) : Tm Head (1 + c + a) := .var ⟨c + a, by omega⟩

/-- **The type of both sides of the computation rule of a constructor**: the motive at the
constructor applied to its fields. -/
def iotaTarget (k : DeclName) (c a : Nat) : Tm Head (1 + c + a) :=
  .app (iotaMotive c a) (appSpine (.const k) ((metaVars (1 + c + a)).drop (1 + c)))

section Rule

variable {L : Type} [LevelOrder L] {R : Rules Head} (levels : LevelModel R L)
  (B : ChurchRules R)

/-- The motive and the methods among the metavariables of a rule. -/
theorem take_metaVars_getElem? (c a q i : Nat) (hi : i < 1 + c + a) (below : q < 1 + c)
    (h : q + (i + 1) = 1 + c + a) :
    ((metaVars (Head := Head) (1 + c + a)).take (1 + c))[q]? = some (.var ⟨i, hi⟩) := by
  rw [List.getElem?_take, if_pos below]
  exact metaVars_getElem? (1 + c + a) q i hi h

/-- **The field metavariables of a rule have the types of the fields.** -/
theorem fieldVars_typed {Q : ChurchRules R} (fields : List (Field Head)) :
    List.Forall₂ (fun x (field : Field Head) =>
      CTyped Q (liftCtx (iotaTele T v ctors fields)) (liftTm x)
        (liftTm (field.type T)).liftClosed)
      ((metaVars (1 + ctors.length + fields.length)).drop (1 + ctors.length)) fields := by
  have length : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).drop
      (1 + ctors.length)).length = fields.length := by
    rw [List.length_drop, length_metaVars]
    omega
  refine List.forall₂_iff_get.mpr ⟨length, fun p h₁ h₂ => ?_⟩
  have hi : fields.length - 1 - p < 1 + ctors.length + fields.length := by omega
  have position : (1 + ctors.length + p) + (fields.length - 1 - p + 1) =
      1 + ctors.length + fields.length := by omega
  have found : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).drop
      (1 + ctors.length))[p]? = some (.var ⟨fields.length - 1 - p, hi⟩) := by
    rw [List.getElem?_drop]
    exact metaVars_getElem? _ _ _ hi position
  have element : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).drop
      (1 + ctors.length)).get ⟨p, h₁⟩ = .var ⟨fields.length - 1 - p, hi⟩ :=
    Option.some.inj ((List.getElem?_eq_getElem h₁).symm.trans found)
  rw [element]
  have typed := metaVar_typed (Q := Q) (iotaEntry T v ctors fields)
    (1 + ctors.length + fields.length) (1 + ctors.length + p) (fields.length - 1 - p) hi position
  have closedEntry : iotaEntry T v ctors fields (1 + ctors.length + p) =
      Presentation.liftClosed ((fields.get ⟨p, h₂⟩).type T) := by
    unfold iotaEntry
    rw [if_neg (by omega)]
    have index : 1 + ctors.length + p - (ctors.length + 1) = p := by omega
    rw [index, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
    rfl
  rw [closedEntry, rename_liftClosed, liftTm_liftClosed] at typed
  exact typed

include levels in
/-- **The recursor applied to the motive and method metavariables of a rule and to a term of
the declared type** has the motive's type at that term. -/
theorem recApp_typed (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors)
    (fields : List (Field Head)) {t : Tm Head (1 + ctors.length + fields.length)}
    (scrutinee : CTyped (withInductive B T u ctors rec v)
      (liftCtx (iotaTele T v ctors fields)) (liftTm t) (.const T)) :
    CTyped (withInductive B T u ctors rec v) (liftCtx (iotaTele T v ctors fields))
      (liftTm (recApp rec
        ((metaVars (1 + ctors.length + fields.length)).take (1 + ctors.length)) t))
      (liftTm (.app (iotaMotive ctors.length fields.length) t)) := by
  have preLength : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).take
      (1 + ctors.length)).length = 1 + ctors.length := by
    rw [List.length_take, length_metaVars]
    omega
  have length : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).take
      (1 + ctors.length) ++ [t]).length = ctors.length + 2 := by
    rw [List.length_append, preLength, List.length_singleton]
    omega
  have last : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).take
      (1 + ctors.length) ++ [t])[ctors.length + 1]? = some t := by
    rw [List.getElem?_append_right (by omega), preLength,
      show ctors.length + 1 - (1 + ctors.length) = 0 by omega]
    rfl
  have earlier : ∀ (q i : Nat) (hi : i < 1 + ctors.length + fields.length), q < 1 + ctors.length →
      q + (i + 1) = 1 + ctors.length + fields.length →
      ((metaVars (Head := Head) (1 + ctors.length + fields.length)).take
        (1 + ctors.length) ++ [t])[q]? = some (.var ⟨i, hi⟩) := fun q i hi below h => by
    rw [List.getElem?_append_left (by omega)]
    exact take_metaVars_getElem? ctors.length fields.length q i hi below h
  have typed := spine_typed (Q := withInductive B T u ctors rec v) (recEntry T v ctors)
    (ctors.length + 2) (recBody ctors.length)
    ((metaVars (1 + ctors.length + fields.length)).take (1 + ctors.length) ++ [t]) length
    (g := .const rec) (rec_typed levels B hu hv distinct free new fieldsFormed)
    (fun q x found => by
      rcases Nat.lt_or_ge q (1 + ctors.length) with below | above
      · -- A motive or method metavariable.
        have hi : 1 + ctors.length + fields.length - 1 - q < 1 + ctors.length + fields.length := by
          omega
        have position : q + (1 + ctors.length + fields.length - 1 - q + 1) =
            1 + ctors.length + fields.length := by omega
        obtain rfl : x = .var ⟨1 + ctors.length + fields.length - 1 - q, hi⟩ :=
          Option.some.inj (found.symm.trans (earlier q _ hi below position))
        have variable_ := metaVar_typed (Q := withInductive B T u ctors rec v)
          (iotaEntry T v ctors fields) (1 + ctors.length + fields.length) q _ hi position
        have entry : iotaEntry T v ctors fields q = recEntry T v ctors q := by
          unfold iotaEntry
          exact if_pos (by omega)
        rw [entry, liftTm_rename, ← CTm.subst_var_comp] at variable_
        have same : argSub ((metaVars (1 + ctors.length + fields.length)).take
            (1 + ctors.length) ++ [t]) q =
            fun j => CTm.var (shiftRen q (1 + ctors.length + fields.length)
              (1 + ctors.length + fields.length - 1 - q + 1) position j) := funext fun j => by
          have hj : j.val + (1 + ctors.length + fields.length - 1 - q + 1) <
              1 + ctors.length + fields.length := by
            have := j.isLt
            omega
          show liftTm (((metaVars (1 + ctors.length + fields.length)).take
            (1 + ctors.length) ++ [t]).getD (q - 1 - j.val) defaultTm) = _
          rw [getD_of_getElem? (earlier (q - 1 - j.val) _ hj (by omega) (by
            have := j.isLt
            omega))]
          rfl
        show CTyped _ _ _ ((liftTm (recEntry T v ctors q)).subst (argSub _ q))
        rw [same]
        exact variable_
      · -- The term of the declared type.
        have atEnd : q = ctors.length + 1 := by
          have bound : q < ctors.length + 2 := by
            rw [← length]
            exact (List.getElem?_eq_some_iff.mp found).1
          omega
        subst atEnd
        obtain rfl : x = t := Option.some.inj (found.symm.trans last)
        show CTyped _ _ _ ((liftTm (recEntry T v ctors (ctors.length + 1))).subst _)
        rw [recEntry_scrutinee]
        exact scrutinee)
  have motive : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).take
      (1 + ctors.length) ++ [t]).getD 0 defaultTm = iotaMotive ctors.length fields.length :=
    getD_of_getElem? (earlier 0 (ctors.length + fields.length) (by omega) (by omega) (by omega)) _
  have result : (liftTm (recBody ctors.length)).subst
      (argSub ((metaVars (1 + ctors.length + fields.length)).take (1 + ctors.length) ++ [t])
        (ctors.length + 2)) = liftTm (.app (iotaMotive ctors.length fields.length) t) := by
    show CTm.app
        (liftTm (((metaVars (1 + ctors.length + fields.length)).take (1 + ctors.length) ++
          [t]).getD (ctors.length + 2 - 1 - (ctors.length + 1)) defaultTm))
        (liftTm (((metaVars (1 + ctors.length + fields.length)).take (1 + ctors.length) ++
          [t]).getD (ctors.length + 2 - 1 - 0) defaultTm)) = _
    rw [show ctors.length + 2 - 1 - (ctors.length + 1) = 0 by omega,
      show ctors.length + 2 - 1 - 0 = ctors.length + 1 by omega, motive,
      getD_of_getElem? last]
    rfl
  rw [result] at typed
  exact typed

include levels in
/-- **Both sides of the computation rule of a constructor are typed over the telescope of the
rule's metavariables**, at the motive at the constructor applied to its fields. -/
theorem iota_typed_metaVars (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) {i : Nat}
    {k : DeclName} {fields : List (Field Head)} (entry : ctors[i]? = some (k, fields)) :
    CTyped (withInductive B T u ctors rec v) (liftCtx (iotaTele T v ctors fields))
        (liftTm (iotaLeft rec k ctors.length fields.length))
        (liftTm (iotaTarget k ctors.length fields.length)) ∧
      CTyped (withInductive B T u ctors rec v) (liftCtx (iotaTele T v ctors fields))
        (liftTm (iotaRight rec ctors.length i fields))
        (liftTm (iotaTarget k ctors.length fields.length)) := by
  have fieldVars := fieldVars_typed (Q := withInductive B T u ctors rec v) (T := T) (v := v)
    (ctors := ctors) fields
  have applied := ctor_spine_typed levels B hu distinct free new fieldsFormed entry fieldVars
  refine ⟨recApp_typed levels B hu hv distinct free new fieldsFormed fields applied, ?_⟩
  have below : i < ctors.length := (List.getElem?_eq_some_iff.mp entry).1
  have hj : ctors.length + fields.length - (i + 1) < 1 + ctors.length + fields.length := by
    omega
  have position : (i + 1) + (ctors.length + fields.length - (i + 1) + 1) =
      1 + ctors.length + fields.length := by omega
  have method : ((metaVars (Head := Head) (1 + ctors.length + fields.length)).take
      (1 + ctors.length)).getD (1 + i) defaultTm =
      .var ⟨ctors.length + fields.length - (i + 1), hj⟩ := by
    rw [Nat.add_comm 1 i]
    exact getD_of_getElem?
      (take_metaVars_getElem? ctors.length fields.length (i + 1) _ hj (by omega) position) _
  have typed := metaVar_typed (Q := withInductive B T u ctors rec v)
    (iotaEntry T v ctors fields) (1 + ctors.length + fields.length) (i + 1) _ hj position
  have entryEq : iotaEntry T v ctors fields (i + 1) =
      caseType T k fields (.var (Fin.last i)) := by
    unfold iotaEntry
    rw [if_pos (by omega)]
    exact recEntry_method T v ctors entry
  have motive : Presentation.subst
      (renSub (shiftRen (i + 1) (1 + ctors.length + fields.length)
        (ctors.length + fields.length - (i + 1) + 1) position))
      (Tm.var (Fin.last i) : Tm Head (i + 1)) =
      iotaMotive ctors.length fields.length := by
    show Tm.var _ = Tm.var _
    congr 1
    apply Fin.ext
    show i + (ctors.length + fields.length - (i + 1) + 1) = ctors.length + fields.length
    omega
  rw [entryEq, ← subst_renSub, subst_caseType, motive] at typed
  have results : List.Forall₂
      (fun h r => CTyped (withInductive B T u ctors rec v) (liftCtx (iotaTele T v ctors fields))
        (liftTm h) (liftTm (.app (iotaMotive ctors.length fields.length) r)))
      ((recArgs fields ((metaVars (1 + ctors.length + fields.length)).drop
        (1 + ctors.length))).map
        (recApp rec ((metaVars (1 + ctors.length + fields.length)).take (1 + ctors.length))))
      ([] ++ recArgs fields ((metaVars (1 + ctors.length + fields.length)).drop
        (1 + ctors.length))) := by
    rw [List.nil_append, List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun r member =>
      recApp_typed levels B hu hv distinct free new fieldsFormed fields
        (recArgs_typed T fields _ fieldVars r member)
  have whole := caseFields_applied T k fields (iotaMotive ctors.length fields.length) [] []
    ((metaVars (1 + ctors.length + fields.length)).drop (1 + ctors.length)) _
    (.var ⟨ctors.length + fields.length - (i + 1), hj⟩) typed fieldVars results
  show CTyped _ _ (liftTm (appSpine
    (((metaVars (1 + ctors.length + fields.length)).take (1 + ctors.length)).getD (1 + i)
      defaultTm) _)) _
  rw [method]
  exact whole

include levels in
/-- **Both sides of an instance of the computation rule are typed**, at the motive at the
constructor applied to its fields, when the instance is typed along the telescope of the
rule's metavariables. -/
theorem iota_typed (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) {i : Nat}
    {k : DeclName} {fields : List (Field Head)} (entry : ctors[i]? = some (k, fields))
    {n : Nat} {Γ : CCtx Head n} (σ : CSub Head (1 + ctors.length + fields.length) n)
    (typed : CSubstMor (withInductive B T u ctors rec v) (liftCtx (iotaTele T v ctors fields))
      Γ σ) :
    CTyped (withInductive B T u ctors rec v) Γ
        ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
        ((liftTm (iotaTarget k ctors.length fields.length)).subst σ) ∧
      CTyped (withInductive B T u ctors rec v) Γ
        ((liftTm (iotaRight rec ctors.length i fields)).subst σ)
        ((liftTm (iotaTarget k ctors.length fields.length)).subst σ) :=
  ⟨(iota_typed_metaVars levels B hu hv distinct free new fieldsFormed entry).1.substitute typed,
    (iota_typed_metaVars levels B hu hv distinct free new fieldsFormed entry).2.substitute typed⟩

end Rule

/-! ## Examples -/

/-- The natural numbers as a declaration: zero, and the successor of a number. -/
def exampleNat : List (DeclName × List (Field Head)) :=
  [(.str .anonymous "zero", []), (.str .anonymous "suc", [.recursive])]

/-- Positive: the fields of the natural numbers have no closed types, so its declared types
have no abstraction. -/
example : FieldsLamFree (exampleNat (Head := Head)) := by
  intro entry member F field
  simp only [exampleNat, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact nomatch field
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
    exact nomatch field

/-- Negative: a name the declaration does not declare has no type in its package. -/
theorem inductiveDecls_other {name : DeclName} (notType : name ≠ T)
    (notCtor : ∀ entry ∈ ctors, entry.1 ≠ name) (notRec : name ≠ rec) :
    inductiveDecls T u ctors rec v name = none := by
  unfold inductiveDecls
  rw [if_neg notType]
  have none : (ctors.find? fun entry => entry.1 = name) = none :=
    List.find?_eq_none.mpr fun entry member => by simpa using notCtor entry member
  rw [none]
  exact if_neg notRec

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
