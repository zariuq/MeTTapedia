import Mathlib.Data.Finset.Basic
import Mettapedia.Data.FreshString

/-!
# π-Calculus Syntax

Asynchronous, choice-free π-calculus with input-guarded replication.
This is the guarded fragment of the syntax in Lybech (2022), whose replication
operator permits arbitrary processes.

Key difference from ρ-calculus: Names are ATOMIC (countably infinite set),
not structured/quoted processes.

## References
- Lybech (2022): "Encodability and Separation for a Reflective Higher-Order Calculus", Section 3, page 98
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

/-- Atomic names (countably infinite) -/
abbrev Name : Type := String

instance : DecidableEq Name := inferInstanceAs (DecidableEq String)
instance : Repr Name := inferInstanceAs (Repr String)

/-- Process syntax for π-calculus -/
inductive Process : Type where
  | nil : Process                              -- 0
  | par : Process → Process → Process          -- P | Q
  | input : Name → Name → Process → Process    -- x(y).P
  | output : Name → Name → Process             -- x<z> (asynchronous)
  | nu : Name → Process → Process              -- (νx)P (restriction)
  | replicate : Name → Name → Process → Process -- !x(y).P (input-guarded)
  deriving DecidableEq, Repr

namespace Process

universe u

/-- Parallel composition notation -/
infixl:50 " ||| " => Process.par

/-- Free names in a process -/
def freeNames : Process → Finset Name
  | nil => ∅
  | par P Q => freeNames P ∪ freeNames Q
  | input x y P => insert x (freeNames P \ {y})
  | output x z => {x, z}
  | nu x P => freeNames P \ {x}
  | replicate x y P => insert x (freeNames P \ {y})

/-- Bound names in a process -/
def boundNames : Process → Finset Name
  | nil => ∅
  | par P Q => boundNames P ∪ boundNames Q
  | input _ y P => insert y (boundNames P)
  | output _ _ => ∅
  | nu x P => insert x (boundNames P)
  | replicate _ y P => insert y (boundNames P)

/-- All names in a process -/
def names (P : Process) : Finset Name :=
  P.freeNames ∪ P.boundNames

/-- Replace free occurrences without freshening. The binder-renaming use in
`substitute` always supplies a target absent from the entire body support. -/
def renameFree : Process → Name → Name → Process
  | .nil, _, _ => .nil
  | .par P Q, y, z => .par (renameFree P y z) (renameFree Q y z)
  | .input x w P, y, z =>
      .input (if x = y then z else x) w (if w = y then P else renameFree P y z)
  | .output x w, y, z =>
      .output (if x = y then z else x) (if w = y then z else w)
  | .nu x P, y, z => .nu x (if x = y then P else renameFree P y z)
  | .replicate x w P, y, z =>
      .replicate (if x = y then z else x) w (if w = y then P else renameFree P y z)

/-- Constructor count, independent of the spelling of names. -/
def nodeCount : Process → Nat
  | .nil => 1
  | .par P Q => nodeCount P + nodeCount Q + 1
  | .input _ _ P => nodeCount P + 1
  | .output _ _ => 1
  | .nu _ P => nodeCount P + 1
  | .replicate _ _ P => nodeCount P + 1

@[simp] theorem nodeCount_renameFree (P : Process) (y z : Name) :
    nodeCount (renameFree P y z) = nodeCount P := by
  induction P with
  | nil | output => rfl
  | par P Q ihP ihQ => simp only [renameFree, nodeCount, ihP, ihQ]
  | input x w P ih | replicate x w P ih =>
      simp only [renameFree, nodeCount]
      split_ifs <;> simp_all only
  | nu x P ih =>
      simp only [renameFree, nodeCount]
      split_ifs <;> simp_all only

/-- A binder name fresh for the body and both substitution names. -/
def freshFor (P : Process) (y z : Name) : Name :=
  Mettapedia.FreshString.fresh (P.names ∪ {y, z})

theorem freshFor_not_names (P : Process) (y z : Name) : freshFor P y z ∉ P.names := by
  intro member
  exact Mettapedia.FreshString.fresh_not_mem _ (Finset.mem_union.mpr (Or.inl member))

/-- Capture-avoiding name substitution. A shadowing binder stops substitution
in its body; a binder colliding with the replacement is freshened first. -/
def substitute : Process → Name → Name → Process
  | .nil, _, _ => .nil
  | .par P Q, y, z => .par (substitute P y z) (substitute Q y z)
  | .input x w P, y, z =>
      if w = y then .input (if x = y then z else x) w P
      else if w = z ∧ y ∈ P.freeNames then
        let fresh := freshFor P y z
        .input (if x = y then z else x) fresh
          (substitute (renameFree P w fresh) y z)
      else .input (if x = y then z else x) w (substitute P y z)
  | .output x w, y, z =>
      .output (if x = y then z else x) (if w = y then z else w)
  | .nu x P, y, z =>
      if x = y then .nu x P
      else if x = z ∧ y ∈ P.freeNames then
        let fresh := freshFor P y z
        .nu fresh (substitute (renameFree P x fresh) y z)
      else .nu x (substitute P y z)
  | .replicate x w P, y, z =>
      if w = y then .replicate (if x = y then z else x) w P
      else if w = z ∧ y ∈ P.freeNames then
        let fresh := freshFor P y z
        .replicate (if x = y then z else x) fresh
          (substitute (renameFree P w fresh) y z)
      else .replicate (if x = y then z else x) w (substitute P y z)
termination_by P _ _ => nodeCount P
decreasing_by all_goals simp only [nodeCount, nodeCount_renameFree]; all_goals omega

@[simp] theorem substitute_nil (y z : Name) : (Process.nil).substitute y z = .nil := by
  rw [substitute]

@[simp] theorem substitute_par (P Q : Process) (y z : Name) :
    (Process.par P Q).substitute y z = .par (P.substitute y z) (Q.substitute y z) := by
  rw [substitute]

@[simp] theorem substitute_output (x w y z : Name) :
    (Process.output x w).substitute y z =
      .output (if x = y then z else x) (if w = y then z else w) := by
  rw [substitute]

def replaceName (y z name : Name) : Name := if name = y then z else name

/-- With both substitution names distinct from the binder, no freshening occurs. -/
theorem substitute_input_of_disjoint (x w : Name) (P : Process) (y z : Name)
    (hwy : w ≠ y) (hwz : w ≠ z) :
    (Process.input x w P).substitute y z =
      .input (replaceName y z x) w (P.substitute y z) := by
  rw [substitute]
  simp only [if_neg hwy, if_neg (fun (capture : w = z ∧ y ∈ P.freeNames) => hwz capture.1),
    replaceName]

/-- Restriction also needs no freshening when its binder is disjoint. -/
theorem substitute_nu_of_disjoint (w : Name) (P : Process) (y z : Name)
    (hwy : w ≠ y) (hwz : w ≠ z) :
    (Process.nu w P).substitute y z = .nu w (P.substitute y z) := by
  rw [substitute]
  simp only [if_neg hwy, if_neg (fun (capture : w = z ∧ y ∈ P.freeNames) => hwz capture.1)]

/-- The input-guarded replication has the same binder substitution law. -/
theorem substitute_replicate_of_disjoint (x w : Name) (P : Process) (y z : Name)
    (hwy : w ≠ y) (hwz : w ≠ z) :
    (Process.replicate x w P).substitute y z =
      .replicate (replaceName y z x) w (P.substitute y z) := by
  rw [substitute]
  simp only [if_neg hwy, if_neg (fun (capture : w = z ∧ y ∈ P.freeNames) => hwz capture.1),
    replaceName]

theorem image_replace_of_absent (names : Finset Name) (y z : Name) (absent : y ∉ names) :
    names.image (replaceName y z) = names := by
  calc
    names.image (replaceName y z) = names.image id := by
      apply Finset.image_congr
      intro name member
      exact if_neg (fun (same : name = y) => absent (same ▸ member))
    _ = names := Finset.image_id

theorem image_replace_erase (names : Finset Name) (y z w : Name)
    (hwy : w ≠ y) (hwz : w ≠ z) :
    (names \ {w}).image (replaceName y z) = (names.image (replaceName y z)) \ {w} := by
  ext name
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨origin, ⟨member, different⟩, rfl⟩
    refine ⟨⟨origin, member, rfl⟩, ?_⟩
    by_cases hy : origin = y
    · simp only [replaceName, if_pos hy]
      exact hwz.symm
    · simpa only [replaceName, if_neg hy] using different
  · rintro ⟨⟨origin, member, rfl⟩, different⟩
    refine ⟨origin, ⟨member, ?_⟩, rfl⟩
    intro same
    subst origin
    exact different (by simp only [replaceName, if_neg hwy])

theorem image_replace_erase_source (names : Finset Name) (y z : Name) :
    (names \ {y}).image (replaceName y z) = names \ {y} := by
  ext name
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨origin, ⟨member, different⟩, same⟩
    simp only [replaceName, if_neg different] at same
    subst name
    exact ⟨member, different⟩
  · rintro ⟨member, different⟩
    exact ⟨name, ⟨member, different⟩, by simp only [replaceName, if_neg different]⟩

theorem image_replace_erase_target (names : Finset Name) (y z : Name)
    (fresh : z ∉ names) :
    names.image (replaceName y z) \ {z} = names \ {y} := by
  ext name
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨origin, member, rfl⟩, different⟩
    by_cases hy : origin = y
    · exact False.elim (different (by simp only [replaceName, if_pos hy]))
    · simpa only [replaceName, if_neg hy] using (And.intro member hy)
  · rintro ⟨member, different⟩
    refine ⟨⟨name, member, by simp only [replaceName, if_neg different]⟩, ?_⟩
    intro same
    exact fresh (same ▸ member)

theorem renameFree_freeNames (P : Process) (y z : Name) (fresh : z ∉ P.boundNames) :
    (renameFree P y z).freeNames = P.freeNames.image (replaceName y z) := by
  induction P with
  | nil => simp only [renameFree, Process.freeNames, Finset.image_empty]
  | par P Q ihP ihQ =>
      simp only [Process.boundNames, Finset.mem_union, not_or] at fresh
      simp only [renameFree, Process.freeNames, ihP fresh.1, ihQ fresh.2, Finset.image_union]
  | input x w P ih | replicate x w P ih =>
      simp only [Process.boundNames, Finset.mem_insert, not_or] at fresh
      have hwz : w ≠ z := Ne.symm fresh.1
      by_cases hwy : w = y
      · subst w
        simp only [renameFree, ite_true, Process.freeNames, Finset.image_insert,
          image_replace_erase_source, replaceName]
      · simp only [renameFree, if_neg hwy, Process.freeNames, ih fresh.2,
          Finset.image_insert]
        rw [image_replace_erase _ y z w hwy hwz]
        rfl
  | output x w =>
      simp only [renameFree, Process.freeNames, Finset.image_insert, Finset.image_singleton,
        replaceName]
  | nu w P ih =>
      simp only [Process.boundNames, Finset.mem_insert, not_or] at fresh
      have hwz : w ≠ z := Ne.symm fresh.1
      by_cases hwy : w = y
      · subst w
        simp only [renameFree, ite_true, Process.freeNames, image_replace_erase_source]
      · simp only [renameFree, if_neg hwy, Process.freeNames, ih fresh.2]
        rw [image_replace_erase _ y z w hwy hwz]

theorem freshFor_ne_source (P : Process) (y z : Name) : freshFor P y z ≠ y := by
  intro same
  apply Mettapedia.FreshString.fresh_not_mem (P.names ∪ {y, z})
  change freshFor P y z ∈ P.names ∪ {y, z}
  rw [same]
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self y {z}))

theorem freshFor_ne_target (P : Process) (y z : Name) : freshFor P y z ≠ z := by
  intro same
  apply Mettapedia.FreshString.fresh_not_mem (P.names ∪ {y, z})
  change freshFor P y z ∈ P.names ∪ {y, z}
  rw [same]
  exact Finset.mem_union.mpr (Or.inr
    (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self z))))

theorem freshFor_not_freeNames (P : Process) (y z : Name) :
    freshFor P y z ∉ P.freeNames := by
  intro member
  exact freshFor_not_names P y z (Finset.mem_union.mpr (Or.inl member))

theorem freshFor_not_boundNames (P : Process) (y z : Name) :
    freshFor P y z ∉ P.boundNames := by
  intro member
  exact freshFor_not_names P y z (Finset.mem_union.mpr (Or.inr member))

theorem capture_body_support (P : Process) (y z w : Name)
    (ih : (substitute (renameFree P w (freshFor P y z)) y z).freeNames =
      (renameFree P w (freshFor P y z)).freeNames.image (replaceName y z)) :
    (substitute (renameFree P w (freshFor P y z)) y z).freeNames \ {freshFor P y z} =
      (P.freeNames \ {w}).image (replaceName y z) := by
  rw [ih, ← image_replace_erase _ y z _ (freshFor_ne_source P y z)
    (freshFor_ne_target P y z), renameFree_freeNames P w _ (freshFor_not_boundNames P y z),
    image_replace_erase_target _ w _ (freshFor_not_freeNames P y z)]

/-- The free names are exactly the image of the source free names. -/
theorem substitute_freeNames_eq (P : Process) (y z : Name) :
    (substitute P y z).freeNames = P.freeNames.image (replaceName y z) := by
  fun_induction substitute P y z with
  | case1 y z => simp only [Process.freeNames, Finset.image_empty]
  | case2 P Q y z ihP ihQ =>
      simp only [Process.freeNames, ihP, ihQ, Finset.image_union]
  | case3 x P y z | case10 x P y z =>
      simp only [Process.freeNames, Finset.image_insert,
        image_replace_erase_source, replaceName]
  | case4 x w P y z different capture fresh ih | case11 x w P y z different capture fresh ih =>
      simp only [Process.freeNames, Finset.image_insert]
      rw [capture_body_support P y z w ih]
      rfl
  | case5 x w P y z different noCapture ih | case12 x w P y z different noCapture ih =>
      simp only [Process.freeNames, ih,
        Finset.image_insert]
      by_cases same : w = z
      · have absent : y ∉ P.freeNames := fun member => noCapture ⟨same, member⟩
        have unchanged := image_replace_of_absent P.freeNames y z absent
        rw [unchanged]
        have unchangedBody : (P.freeNames \ {w}).image (replaceName y z) =
            P.freeNames \ {w} := by
          exact image_replace_of_absent _ y z (fun member => absent (Finset.mem_sdiff.mp member).1)
        rw [unchangedBody]
        rfl
      · rw [image_replace_erase _ y z w different same]
        rfl
  | case6 x w y z =>
      simp only [Process.freeNames, Finset.image_insert, Finset.image_singleton,
        replaceName]
  | case7 P y z =>
      simp only [Process.freeNames, image_replace_erase_source]
  | case8 w P y z different capture fresh ih =>
      simp only [Process.freeNames]
      exact capture_body_support P y z w ih
  | case9 w P y z different noCapture ih =>
      simp only [Process.freeNames, ih]
      by_cases same : w = z
      · have absent : y ∉ P.freeNames := fun member => noCapture ⟨same, member⟩
        have unchanged := image_replace_of_absent P.freeNames y z absent
        rw [unchanged]
        have unchangedBody : (P.freeNames \ {w}).image (replaceName y z) =
            P.freeNames \ {w} := by
          exact image_replace_of_absent _ y z (fun member => absent (Finset.mem_sdiff.mp member).1)
        rw [unchangedBody]
      · exact (image_replace_erase _ y z w different same).symm

/-- Fold a process through an algebra that does not inspect names. -/
def fold {A : Type u} (nil : A) (par : A → A → A) (input : A → A)
    (output : A) (nu : A → A) (replicate : A → A) : Process → A
  | .nil => nil
  | .par P Q => par (fold nil par input output nu replicate P)
      (fold nil par input output nu replicate Q)
  | .input _ _ P => input (fold nil par input output nu replicate P)
  | .output _ _ => output
  | .nu _ P => nu (fold nil par input output nu replicate P)
  | .replicate _ _ P => replicate (fold nil par input output nu replicate P)

theorem fold_renameFree {A : Type u} (nil : A) (par : A → A → A) (input : A → A)
    (output : A) (nu : A → A) (replicate : A → A) (P : Process) (y z : Name) :
    fold nil par input output nu replicate (renameFree P y z) =
      fold nil par input output nu replicate P := by
  induction P with
  | nil | output => rfl
  | par P Q ihP ihQ => simp only [renameFree, fold, ihP, ihQ]
  | input x w P ih | replicate x w P ih =>
      simp only [renameFree, fold]
      split_ifs <;> simp_all only
  | nu x P ih =>
      simp only [renameFree, fold]
      split_ifs <;> simp_all only

/-- Substitution preserves every name-insensitive structural observation. -/
theorem fold_substitute {A : Type u} (nil : A) (par : A → A → A) (input : A → A)
    (output : A) (nu : A → A) (replicate : A → A) (P : Process) (y z : Name) :
    fold nil par input output nu replicate (substitute P y z) =
      fold nil par input output nu replicate P := by
  fun_induction substitute P y z with
  | case1 | case6 => rfl
  | case2 P Q y z ihP ihQ => simp only [fold, ihP, ihQ]
  | case3 | case7 | case10 => rfl
  | case4 x w P y z _ _ fresh ih | case11 x w P y z _ _ fresh ih =>
      simp only [fold, ih, fold_renameFree]
  | case5 x w P y z _ _ ih | case12 x w P y z _ _ ih => simp only [fold, ih]
  | case8 w P y z _ _ fresh ih => simp only [fold, ih, fold_renameFree]
  | case9 w P y z _ _ ih => simp only [fold, ih]

/-- Check if a name is fresh for a process -/
def isFresh (x : Name) (P : Process) : Prop :=
  x ∉ P.names

end Process

end Mettapedia.Languages.ProcessCalculi.PiCalculus
