import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis

/-!
# Dependency analysis: a package catalogue

A small package catalogue and a variant with a dependency cycle. Every value
below is computed by the kernel from the measure-based services; the
accessibility-route versions agree by `affectedAcc_eq`, `scheduleAcc_eq` and
`depFoldAcc_eq`.

Positive controls: affected sets, rebuild waves, derivation keys, critical-path
lengths, and incremental rebuild soundness for a concrete change.
Negative controls: an item outside the affected set, a dependency-violating
order that is not accepted, the cyclic catalogue (blocked schedule, explicit
cycle, no acyclicity certificate), and a self-dependent item.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices.DependencyExamples

open Relation Catalogue

inductive Pkg where
  | core | text | json | http | db | cli | app
  deriving DecidableEq, Repr

open Pkg

def deps : Pkg → List Pkg
  | core => []
  | text => [core]
  | json => [text, core]
  | http => [json, text]
  | db => [core]
  | cli => [text]
  | app => [http, db, cli]

/-- The catalogue. -/
def packages : Catalogue Pkg := ⟨[core, text, json, http, db, cli, app], deps⟩

/-! ## Affected items -/

example : packages.affected [text] = [text, json, http, cli, app] := by decide
example : packages.affected [db] = [db, app] := by decide
example : packages.affected [app] = [app] := by decide

/-- A change to `text` reaches `app`, through `http` and through `cli`. -/
example : ReflTransGen packages.Uses app text :=
  ((packages.mem_affected [text] app).1 (by decide)).elim fun y ⟨hy, r⟩ =>
    (List.mem_singleton.1 hy) ▸ r

/-- Negative control: `db` does not depend on `text`. -/
theorem db_not_uses_text : ¬ ReflTransGen packages.Uses db text := fun r =>
  absurd ((packages.mem_affected [text] db).2 ⟨text, List.mem_singleton_self _, r⟩) (by decide)

/-! ## Rebuild waves -/

example : packages.schedule packages.items =
    .waves [[core], [text, db], [json, cli], [http], [app]] := by decide

/-- The rebuild after a change to `text`. -/
example : packages.schedule (packages.affected [text]) = .waves [[text], [json, cli], [http], [app]] := by
  decide

/-- Negative control: an order that builds `app` first does not respect the
dependencies. -/
example : ¬ packages.Respects [app, core, text, json, http, db, cli] := fun h =>
  absurd h.pairwise (by decide)

example : packages.cycle? = none := by decide

/-! ## Recursion over dependencies -/

/-- The acyclicity certificate. -/
def certificate : packages.Acyclic :=
  match h : packages.acyclic? with
  | some A => A
  | none => absurd (congrArg Option.isSome h)
      (by rw [packages.acyclic?_isSome_iff.2 (packages.cycle?_none (by decide))]; decide)

def base : Pkg → ℕ
  | core => 11 | text => 23 | json => 37 | http => 41 | db => 53 | cli => 67 | app => 79

/-- A derivation key combines an item's own content with its dependencies'
keys. -/
def combine (content : Pkg → ℕ) (x : Pkg) (ks : List ℕ) : ℕ :=
  ks.foldl (fun acc k => (acc * 131 + k) % 1000003) (content x)

def key (content : Pkg → ℕ) : Pkg → ℕ := packages.depFold certificate (combine content)

example : key base core = 11 := by decide
example : key base text = 3024 := by decide
example : key base app = 529788 := by decide

/-- The critical-path length: the number of rebuild waves an item needs. -/
def height : Pkg → ℕ := packages.depFold certificate fun _ hs => hs.foldr max 0 + 1

example : height core = 1 := by decide
example : height app = 5 := by decide

/-! ## Occurrence work and independently derived values -/

theorem packages_dependencyClosed : packages.DependencyClosed := by
  intro owner ownerMember child childMember
  cases owner <;> cases child <;> simp_all [packages, deps]

/-- Recursive occurrence work is not the number of distinct cached nodes. -/
theorem occurrence_work_exceeds_distinct_nodes :
    packages.unfoldingWork certificate (fun _ => 1) app = 13 ∧
      packages.items.length = 7 := by decide

theorem work_has_independent_derivation :
    packages.FoldDerivation (fun (_ : Pkg) (childWork : List Nat) => 1 + childWork.sum) app 13 := by
  have derived := packages.depFold_has_derivation certificate
    (fun (_ : Pkg) (childWork : List Nat) => 1 + childWork.sum)
    packages_dependencyClosed app (by decide)
  have computed : packages.unfoldingWork certificate (fun _ => 1) app = 13 := by decide
  rw [← computed]
  exact derived

def repeated : Catalogue Pkg where
  items := [core, text, app]
  deps
    | text => [core]
    | app => [text, text]
    | _ => []

def repeatedCertificate : repeated.Acyclic := repeated.acyclic?.get (by decide)

/-- Two references to one shared child retain two logical contributions. -/
theorem repeated_child_contributes_twice :
    repeated.unfoldingWork repeatedCertificate (fun _ => 1) app = 5 ∧
      repeated.items.length = 3 := by decide

def missingDependency : Catalogue Pkg := ⟨[app], fun _ => [text]⟩

/-- A missing referenced item cannot receive the closed-catalogue theorem. -/
theorem missing_dependency_not_closed : ¬ missingDependency.DependencyClosed := by
  intro closed
  have admitted := closed app (by decide) text (by decide)
  simp [missingDependency] at admitted

/-- New content for `text`. -/
def edited : Pkg → ℕ := Function.update base text 24

/-- **Incremental rebuild, concretely**: editing `text` leaves the keys of the
items outside its affected set unchanged. -/
theorem key_db_unchanged : key edited db = key base db :=
  packages.depFold_eq_of_not_affected certificate _ _ [text]
    (fun x hx => by
      funext ks
      simp only [combine, edited]
      rw [Function.update_of_ne (fun h => hx (List.mem_singleton.2 h))])
    (by decide)

/-- The keys of affected items do change. -/
example : key edited app ≠ key base app := by decide
example : key edited app = 151915 := by decide

/-! ## A cyclic catalogue -/

def cyclicDeps : Pkg → List Pkg
  | cli => [text, app]
  | x => deps x

def cyclic : Catalogue Pkg := ⟨packages.items, cyclicDeps⟩

example : cyclic.schedule cyclic.items =
    .blocked [cli, app] := by decide

example : cyclic.cycle? = some [cli, app] := by decide

/-- The reported cycle is a cycle. -/
example : cyclic.IsCycle [cli, app] :=
  (cyclic.cycle?_sound (by decide : cyclic.cycle? = some [cli, app])).1

/-- The cyclic catalogue has no acyclicity certificate. -/
example : cyclic.acyclic? = none := by
  cases h : cyclic.acyclic? with
  | none => rfl
  | some A =>
      obtain ⟨a, t⟩ := (cyclic.cycle?_sound (by decide : cyclic.cycle? = some [cli, app])).1.transGen
      exact absurd t (A.respects.acyclic A.covers a)

/-- A self-dependent item is a cycle of length one. -/
def selfLoop : Catalogue Pkg := ⟨[core], fun _ => [core]⟩

example : selfLoop.cycle? = some [core] := by decide

end Mettapedia.Algorithms.WellFoundedServices.DependencyExamples
