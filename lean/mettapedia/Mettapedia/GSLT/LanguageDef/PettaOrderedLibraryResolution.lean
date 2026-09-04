import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Ordered library-reference resolution for PeTTa

PeTTa exposes two different reference constructors.  A standard reference has
one language-owned candidate.  A rooted reference ranges over an ordered
family of authored root occurrences, retaining duplicates.  Resolution only
constructs candidate paths; importing is a later partial observation.

The rooted resolver is a homomorphism from the free monoid of root
occurrences to the free monoid of candidate paths.  Consequently, prepending
or appending roots composes with resolution, a missing candidate contributes
the additive zero during import, and duplicate root occurrences remain
duplicate import opportunities.

`Refused` is deliberately distinct from an empty candidate family.  The
former records a policy or syntax rejection; the latter is ordinary
exhaustion of an admitted nondeterministic relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PettaOrderedLibraryResolution

universe uRoot uMember uPath uRefusal uResult

/-- The two authored library-reference constructors. -/
inductive Reference (Root : Type uRoot) (Member : Type uMember) where
  | standard (member : Member)
  | rooted (root : Root) (member : Member)
deriving DecidableEq, Repr

/-- The language-owned presentation of library resolution.  Admission is
separate from path construction so policy refusal cannot be confused with an
admitted reference whose candidate family is empty. -/
structure Presentation
    (Root : Type uRoot) (Member : Type uMember)
    (Path : Type uPath) (Refusal : Type uRefusal) where
  standardPath : Member → Path
  rootMatches : Root → Path → Bool
  join : Path → Member → Path
  admission : Reference Root Member → Except Refusal Unit

/-- Candidate paths contributed by the matching root occurrences, in authored
order and with duplicate occurrences retained. -/
def rootedCandidates
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (root : Root) (member : Member) (roots : List Path) : List Path :=
  roots.filterMap fun path =>
    if presentation.rootMatches root path then
      some (presentation.join path member)
    else
      none

/-- Independent candidate semantics for an admitted reference. -/
def resolveCandidates
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (roots : List Path) : Reference Root Member → List Path
  | .standard member => [presentation.standardPath member]
  | .rooted root member =>
      rootedCandidates presentation root member roots

/-- Complete resolution: a rejected reference is proof-relevant refusal;
otherwise resolution returns its ordered candidate family, possibly empty. -/
def resolve
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (roots : List Path) (reference : Reference Root Member) :
    Except Refusal (List Path) :=
  match presentation.admission reference with
  | .error reason => .error reason
  | .ok () => .ok (resolveCandidates presentation roots reference)

theorem resolve_admitted
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (roots : List Path) (reference : Reference Root Member)
    (admitted : presentation.admission reference = .ok ()) :
    resolve presentation roots reference =
      .ok (resolveCandidates presentation roots reference) := by
  simp [resolve, admitted]

theorem resolve_refused
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (roots : List Path) (reference : Reference Root Member)
    (reason : Refusal)
    (refused : presentation.admission reference = .error reason) :
    resolve presentation roots reference = .error reason := by
  simp [resolve, refused]

/-- Rooted resolution preserves concatenation of ordered root families. -/
theorem rootedCandidates_append
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (root : Root) (member : Member) (left right : List Path) :
    rootedCandidates presentation root member (left ++ right) =
      rootedCandidates presentation root member left ++
        rootedCandidates presentation root member right := by
  simp [rootedCandidates]

/-- A homomorphism between free monoids, written without relying on a global
algebra instance for `List`. -/
structure FreeMonoidHom (Source : Type uPath) (Target : Type uResult) where
  toFun : List Source → List Target
  mapNil : toFun [] = []
  mapAppend : ∀ left right,
    toFun (left ++ right) = toFun left ++ toFun right

/-- For a fixed rooted reference, resolution is a homomorphism from the free
monoid of root occurrences to the free monoid of path candidates. -/
def rootedResolutionHom
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (root : Root) (member : Member) : FreeMonoidHom Path Path where
  toFun := rootedCandidates presentation root member
  mapNil := by simp [rootedCandidates]
  mapAppend := rootedCandidates_append presentation root member

/-- Dynamic edits of the authored root-occurrence family.  Retraction removes
the first equal occurrence, matching the ordered relational observation. -/
inductive RootEdit (Path : Type uPath) where
  | prepend (path : Path)
  | append (path : Path)
  | retractFirst (path : Path)
deriving DecidableEq, Repr

def removeFirst {Path : Type uPath} [DecidableEq Path]
    (needle : Path) : List Path → List Path
  | [] => []
  | path :: paths =>
      if path = needle then paths else path :: removeFirst needle paths

def applyRootEdit {Path : Type uPath} [DecidableEq Path]
    (edit : RootEdit Path) (roots : List Path) : List Path :=
  match edit with
  | .prepend path => path :: roots
  | .append path => roots ++ [path]
  | .retractFirst path => removeFirst path roots

theorem removeFirst_head {Path : Type uPath} [DecidableEq Path]
    (path : Path) (paths : List Path) :
    removeFirst path (path :: paths) = paths := by
  simp [removeFirst]

theorem removeFirst_skips_unequal
    {Path : Type uPath} [DecidableEq Path]
    (needle path : Path) (paths : List Path) (unequal : path ≠ needle) :
    removeFirst needle (path :: paths) =
      path :: removeFirst needle paths := by
  simp [removeFirst, unequal]

theorem rootedCandidates_after_prepend
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    [DecidableEq Path]
    (presentation : Presentation Root Member Path Refusal)
    (root : Root) (member : Member) (path : Path) (roots : List Path) :
    rootedCandidates presentation root member
        (applyRootEdit (.prepend path) roots) =
      (if presentation.rootMatches root path then
        [presentation.join path member]
       else []) ++ rootedCandidates presentation root member roots := by
  cases matched : presentation.rootMatches root path <;>
    simp [applyRootEdit, rootedCandidates, matched]

theorem rootedCandidates_after_append
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} {Refusal : Type uRefusal}
    [DecidableEq Path]
    (presentation : Presentation Root Member Path Refusal)
    (root : Root) (member : Member) (path : Path) (roots : List Path) :
    rootedCandidates presentation root member
        (applyRootEdit (.append path) roots) =
      rootedCandidates presentation root member roots ++
        if presentation.rootMatches root path then
          [presentation.join path member]
        else [] := by
  cases matched : presentation.rootMatches root path <;>
    simp [applyRootEdit, rootedCandidates, matched]

/-- The three observable states of the streaming C realization. -/
inductive Observation (Path : Type uPath) (Refusal : Type uRefusal) where
  | yield (path : Path)
  | exhausted
  | refused (reason : Refusal)
deriving DecidableEq, Repr

def observe
    {Path : Type uPath} {Refusal : Type uRefusal}
    (resolution : Except Refusal (List Path)) (occurrence : Nat) :
    Observation Path Refusal :=
  match resolution with
  | .error reason => .refused reason
  | .ok paths =>
      match paths[occurrence]? with
      | some path => .yield path
      | none => .exhausted

@[simp] theorem observe_refused
    {Path : Type uPath} {Refusal : Type uRefusal}
    (reason : Refusal) (occurrence : Nat) :
    observe (Path := Path) (.error reason) occurrence = .refused reason := rfl

@[simp] theorem observe_empty
    {Path : Type uPath} {Refusal : Type uRefusal} (occurrence : Nat) :
    observe (Refusal := Refusal) (.ok ([] : List Path)) occurrence =
      .exhausted := by
  simp [observe]

@[simp] theorem observe_head
    {Path : Type uPath} {Refusal : Type uRefusal}
    (path : Path) (paths : List Path) :
    observe (Refusal := Refusal) (.ok (path :: paths)) 0 = .yield path := by
  simp [observe]

/-- Import each candidate and concatenate the successful result families.
Candidate failure is represented by the empty list, the additive identity. -/
def collectImports
    {Path : Type uPath} {Result : Type uResult}
    (load : Path → List Result) (paths : List Path) : List Result :=
  paths.flatMap load

theorem collectImports_append
    {Path : Type uPath} {Result : Type uResult}
    (load : Path → List Result) (left right : List Path) :
    collectImports load (left ++ right) =
      collectImports load left ++ collectImports load right := by
  simp [collectImports]

theorem missingCandidate_is_additiveZero
    {Path : Type uPath} {Result : Type uResult}
    (load : Path → List Result) (missing : Path) (rest : List Path)
    (isMissing : load missing = []) :
    collectImports load (missing :: rest) = collectImports load rest := by
  simp [collectImports, isMissing]

theorem duplicateCandidate_retainsMultiplicity
    {Path : Type uPath} {Result : Type uResult}
    (load : Path → List Result) (path : Path) :
    collectImports load [path, path] = load path ++ load path := by
  simp [collectImports]

def importResolved
    {Path : Type uPath} {Refusal : Type uRefusal}
    {Result : Type uResult}
    (load : Path → List Result) :
    Except Refusal (List Path) → Except Refusal (List Result)
  | .error reason => .error reason
  | .ok paths => .ok (collectImports load paths)

@[simp] theorem importResolved_refused
    {Path : Type uPath} {Refusal : Type uRefusal}
    {Result : Type uResult}
    (load : Path → List Result) (reason : Refusal) :
    importResolved load (.error reason) = .error reason := rfl

/-! ## Executable positive and negative canaries -/

private def examplePresentation :
    Presentation Nat Nat (Nat × List Nat) String where
  standardPath member := (0, [member])
  rootMatches root path := decide (root = path.1)
  join path member := (path.1, path.2 ++ [member])
  admission _ := .ok ()

example :
    resolveCandidates examplePresentation
        [(7, [1]), (8, [4]), (7, [2])] (.rooted 7 3) =
      [(7, [1, 3]), (7, [2, 3])] := by
  decide

/-- Reversing two distinct matching root occurrences is observably different;
the resolver is ordered rather than set-valued. -/
example :
    resolveCandidates examplePresentation
        [(7, [1]), (7, [2])] (.rooted 7 3) ≠
      [(7, [2, 3]), (7, [1, 3])] := by
  decide

/-- Equal root occurrences are not deduplicated. -/
example :
    resolveCandidates examplePresentation
        [(7, [1]), (7, [1])] (.rooted 7 3) =
      [(7, [1, 3]), (7, [1, 3])] := by
  decide

private def refusingPresentation :
    Presentation Nat Nat (Nat × List Nat) String :=
  { examplePresentation with
    admission := fun
      | .rooted 9 _ => .error "root refused"
      | _ => .ok () }

/-- Refusal and admitted exhaustion are different observations. -/
example :
    resolve refusingPresentation [] (.rooted 9 3) =
      .error "root refused" := by
  decide

example :
    resolve examplePresentation [] (.rooted 9 3) = .ok [] := by
  decide

example : removeFirst 4 [3, 4, 4, 5] = [3, 4, 5] := by
  decide

#print axioms rootedCandidates_append
#print axioms rootedResolutionHom
#print axioms missingCandidate_is_additiveZero
#print axioms duplicateCandidate_retainsMultiplicity

end Mettapedia.GSLT.LanguageDef.PettaOrderedLibraryResolution
