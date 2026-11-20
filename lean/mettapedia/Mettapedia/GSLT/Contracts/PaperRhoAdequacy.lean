import Mettapedia.GSLT.Contracts.PaperRhoStructuralCongruence
import Mettapedia.GSLT.Contracts.PaperRhoPatternBoundary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep


/-!
# Step adequacy of our rho calculus against the paper's rho calculus

The reference is the paper's rho calculus as written (Meredith and Radestock
2005): `Congruence` and `NameEquivalence`, where structural congruence compares
names in subject and drop positions by name equivalence, and `Reduction`, with
COMM under a name-equivalence premise, PAR and EQUIV. Our side is the step
relation compiled from the authored rho language (`RhoStep`). Its COMM matcher
compares channels by canonical equality under `rhoReflectivePresentation`, the
presentation selected for the rule, and its contractum is reflective
substitution under the same presentation. Equality in our calculus is equality
of canonical forms. The translation is the plain readback `encodeProcess`.

* **Bridge**, for all processes and names, with no scope condition:
  `canonicalize_encodeProcess_eq_iff`, `canonicalize_encodeName_eq_iff`.
  Completeness reads a canonical form back (`decodeProcess_canonicalize`).
* **Substitution**: `canonicalize_substituteReflective` (up to the equations, for
  every body, payload and depth) and `substituteReflective_encode_exact` (spelling
  for spelling, when body and payload have no quotation exposing a drop).
* **Steps**: `rhoStep_of_reduction`, `rhoStep_canonicalForm_reduction`,
  `rhoStep_encodeProcess_reduction`, and `reduction_iff_rhoStep`.
* **Many steps**: each step is read at the canonical form of its target
  (`CanonicalStep`), so the next step starts from the next canonical form.
  `reflTransGen_canonicalStep_iff`: from the canonical form of a closed process,
  the reachable canonical forms are exactly those of its paper reducts;
  `transGen_reduction_iff_canonicalStep`: with at least one step the
  correspondence is exact between canonical forms.

A paper reduction is matched by a step from the canonical form of its source.
From the plain encoding it need not be: our step relation reads a parallel bag
as written, while the paper reaches a redex split across parallel levels through
EQUIV and the unit law (`AdequacyControls.plain_encoding_not_complete`). Within
our calculus this is `CanonicalRepresentativeStep`: the raw step relation is not
closed under the equations, and stepping the canonical representative loses no
step. The converse direction needs a closed source, because the paper's COMM
admits only closed communication (`AdequacyControls.open_step_not_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.Adequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.Contracts.PaperRho.PatternBoundary
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns sortPatterns_eq_of_perm)

/-! ## Canonical forms of encoded syntax -/

theorem canonicalize_zero :
    canonicalize rhoReflectivePresentation (encodeProcess .zero) = .apply "PZero" [] := by
  simp [encodeProcess, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

theorem canonicalize_send (x : Name) (p : Process) :
    canonicalize rhoReflectivePresentation (encodeProcess (.send x p)) =
      .apply "POutput" [canonicalize rhoReflectivePresentation (encodeName x),
        canonicalize rhoReflectivePresentation (encodeProcess p)] := by
  simp [encodeProcess, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

theorem canonicalize_receive (x : Name) (p : Process) :
    canonicalize rhoReflectivePresentation (encodeProcess (.receive x p)) =
      .apply "PInput" [canonicalize rhoReflectivePresentation (encodeName x),
        .lambda none (canonicalize rhoReflectivePresentation (encodeProcess p))] := by
  simp [encodeProcess, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

theorem canonicalize_drop (x : Name) :
    canonicalize rhoReflectivePresentation (encodeProcess (.drop x)) =
      .apply "PDrop" [canonicalize rhoReflectivePresentation (encodeName x)] := by
  simp [encodeProcess, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

theorem canonicalize_par (p q : Process) :
    canonicalize rhoReflectivePresentation (encodeProcess (.par p q)) =
      collapseParallel rhoReflectivePresentation
        (normalizeParallelElements rhoReflectivePresentation
          [canonicalize rhoReflectivePresentation (encodeProcess p),
            canonicalize rhoReflectivePresentation (encodeProcess q)]) := by
  simp [encodeProcess, canonicalize, canonicalizeList, rhoReflectivePresentation]

theorem canonicalize_bound (index : Nat) :
    canonicalize rhoReflectivePresentation (encodeName (.bound index)) = .bvar index := by
  simp [encodeName, canonicalize]

theorem canonicalize_quote (p : Process) :
    canonicalize rhoReflectivePresentation (encodeName (.quote p)) =
      finishNormalizeReflectiveApply rhoReflectivePresentation "NQuote"
        [canonicalize rhoReflectivePresentation (encodeProcess p)] := by
  simp [encodeName, canonicalize, canonicalizeList]

private theorem rho_unit_cons (patterns : List Pattern) :
    normalizeParallelElements rhoReflectivePresentation (.apply "PZero" [] :: patterns) =
      normalizeParallelElements rhoReflectivePresentation patterns :=
  normalizeParallelElements_unit_cons rhoReflectivePresentation patterns

/-! ## The paper's congruence is respected by our canonical equality -/

mutual
  theorem Congruence.canonicalize_eq {p q : Process} :
      Congruence p q →
        canonicalize rhoReflectivePresentation (encodeProcess p) =
          canonicalize rhoReflectivePresentation (encodeProcess q)
    | .refl _ => rfl
    | .symm same => (Congruence.canonicalize_eq same).symm
    | .trans first second =>
        (Congruence.canonicalize_eq first).trans (Congruence.canonicalize_eq second)
    | .unit p => by
        rw [canonicalize_par, canonicalize_zero,
          normalizeParallelElements_eq_of_perm rhoReflectivePresentation
            (List.Perm.swap _ _ []), rho_unit_cons]
        exact collapse_normalize_singleton_of_isCanonical _ (canonicalize_isCanonical _ _)
    | .swap p q => by
        rw [canonicalize_par, canonicalize_par,
          normalizeParallelElements_eq_of_perm rhoReflectivePresentation (List.Perm.swap _ _ [])]
    | .assoc p q r => by
        have left := canonicalize_parallel_flatten rhoReflectivePresentation
          [encodeProcess r] [encodeProcess p, encodeProcess q]
        have right := canonicalize_parallel_flatten rhoReflectivePresentation
          [encodeProcess p] [encodeProcess q, encodeProcess r]
        have reorder := canonicalize_parallel_permutation rhoReflectivePresentation
          (left := [encodeProcess r, encodeProcess p, encodeProcess q])
          (right := [encodeProcess p, encodeProcess q, encodeProcess r])
          (by simpa using (List.perm_append_comm (l₁ := [encodeProcess r])
            (l₂ := [encodeProcess p, encodeProcess q])))
        have outer := canonicalize_parallel_permutation rhoReflectivePresentation
          (left := [encodeProcess (.par p q), encodeProcess r])
          (right := [encodeProcess r, encodeProcess (.par p q)]) (List.Perm.swap _ _ [])
        simp only [encodeProcess] at left right outer ⊢
        simp only [List.cons_append, List.nil_append] at left right
        exact outer.trans (left.trans (reorder.trans right.symm))
    | .par first second => by
        rw [canonicalize_par, canonicalize_par, Congruence.canonicalize_eq first,
          Congruence.canonicalize_eq second]
    | .send names code => by
        rw [canonicalize_send, canonicalize_send, NameEquivalence.canonicalize_eq names,
          Congruence.canonicalize_eq code]
    | .receive names code => by
        rw [canonicalize_receive, canonicalize_receive, NameEquivalence.canonicalize_eq names,
          Congruence.canonicalize_eq code]
    | .drop names => by
        rw [canonicalize_drop, canonicalize_drop, NameEquivalence.canonicalize_eq names]

  theorem NameEquivalence.canonicalize_eq {x y : Name} :
      NameEquivalence x y →
        canonicalize rhoReflectivePresentation (encodeName x) =
          canonicalize rhoReflectivePresentation (encodeName y)
    | .refl _ => rfl
    | .symm same => (NameEquivalence.canonicalize_eq same).symm
    | .trans first second =>
        (NameEquivalence.canonicalize_eq first).trans (NameEquivalence.canonicalize_eq second)
    | .quote_drop x => by
        rw [canonicalize_quote, canonicalize_drop]
        exact Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.finish_quote_drop
          (declaration := rhoReflectivePresentation) _
    | .quote code => by
        rw [canonicalize_quote, canonicalize_quote, Congruence.canonicalize_eq code]
end

/-! ## Reading canonical patterns back -/

/-- Right-nested parallel composition of a list, closed by the unit. -/
def parallelOf : List Process → Process
  | [] => .zero
  | p :: ps => .par p (parallelOf ps)

mutual
  /-- Read a pattern back as a paper name, if it has the shape of one. -/
  def decodeName : Pattern → Option Name
    | .bvar index => some (.bound index)
    | .apply constructor [code] =>
        if constructor = "NQuote" then (decodeProcess code).map .quote else none
    | _ => none

  /-- Read a pattern back as a paper process, if it has the shape of one.
  A parallel bag is read as the right-nested composition of its members. -/
  def decodeProcess : Pattern → Option Process
    | .apply constructor [] => if constructor = "PZero" then some .zero else none
    | .apply constructor [name] =>
        if constructor = "PDrop" then (decodeName name).map .drop else none
    | .apply constructor [name, second] =>
        if constructor = "POutput" then
          (decodeName name).bind fun x => (decodeProcess second).map (.send x)
        else if constructor = "PInput" then
          (decodeName name).bind fun x => (decodeAbstraction second).map (.receive x)
        else none
    | .collection .hashBag members none => decodeMembers members
    | _ => none

  /-- Read the continuation slot of an input. -/
  def decodeAbstraction : Pattern → Option Process
    | .lambda none body => decodeProcess body
    | _ => none

  /-- Read the members of a parallel bag. -/
  def decodeMembers : List Pattern → Option Process
    | [] => some .zero
    | member :: members =>
        (decodeProcess member).bind fun p => (decodeMembers members).map (.par p)
end

@[simp] theorem decodeName_bvar (index : Nat) : decodeName (.bvar index) = some (.bound index) := by
  simp [decodeName]

@[simp] theorem decodeName_quote (code : Pattern) :
    decodeName (.apply "NQuote" [code]) = (decodeProcess code).map .quote := by
  simp [decodeName]

@[simp] theorem decodeProcess_zero : decodeProcess (.apply "PZero" []) = some .zero := by
  simp [decodeProcess]

@[simp] theorem decodeProcess_drop (name : Pattern) :
    decodeProcess (.apply "PDrop" [name]) = (decodeName name).map .drop := by
  simp [decodeProcess]

@[simp] theorem decodeProcess_send (name payload : Pattern) :
    decodeProcess (.apply "POutput" [name, payload]) =
      (decodeName name).bind fun x => (decodeProcess payload).map (.send x) := by
  conv_lhs => rw [decodeProcess]
  simp

@[simp] theorem decodeProcess_receive (name body : Pattern) :
    decodeProcess (.apply "PInput" [name, .lambda none body]) =
      (decodeName name).bind fun x => (decodeProcess body).map (.receive x) := by
  conv_lhs => rw [decodeProcess]
  simp [decodeAbstraction]

@[simp] theorem decodeProcess_parallel (members : List Pattern) :
    decodeProcess (.collection .hashBag members none) = decodeMembers members := by
  rw [decodeProcess]

/-- Decoded patterns have only the two name shapes. -/
theorem decodeName_shape {pattern : Pattern} {x : Name} (decoded : decodeName pattern = some x) :
    (∃ index, pattern = .bvar index) ∨ ∃ code, pattern = .apply "NQuote" [code] := by
  cases pattern with
  | bvar index => exact .inl ⟨index, rfl⟩
  | apply constructor arguments =>
      match arguments, decoded with
      | [code], decoded =>
          by_cases quoted : constructor = "NQuote"
          · exact .inr ⟨code, by rw [quoted]⟩
          · simp [decodeName, quoted] at decoded
      | [], decoded => simp [decodeName] at decoded
      | _ :: _ :: _, decoded => simp [decodeName] at decoded
  | fvar _ | lambda _ _ | multiLambda _ _ _ | subst _ _ | collection _ _ _ =>
      simp [decodeName] at decoded

theorem decodeMembers_eq_some {members : List Pattern} {p : Process} :
    decodeMembers members = some p ↔
      ∃ ps, List.Forall₂ (fun member q => decodeProcess member = some q) members ps ∧
        p = parallelOf ps := by
  induction members generalizing p with
  | nil => simp [decodeMembers, parallelOf, eq_comm]
  | cons member members ih =>
      simp only [decodeMembers, Option.bind_eq_some_iff, Option.map_eq_some_iff, ih]
      constructor
      · rintro ⟨head, decoded, _, ⟨ps, each, rfl⟩, rfl⟩
        exact ⟨head :: ps, .cons decoded each, rfl⟩
      · rintro ⟨_ | ⟨head, ps⟩, each, rfl⟩
        · cases each
        · cases each with
          | cons decoded each => exact ⟨head, decoded, _, ⟨ps, each, rfl⟩, rfl⟩

/-! ## Parallel composition of lists, up to the paper's congruence -/

theorem parallelOf_append (ps qs : List Process) :
    Congruence (parallelOf (ps ++ qs)) (.par (parallelOf ps) (parallelOf qs)) := by
  induction ps with
  | nil => exact .symm (.trans (.swap _ _) (.unit _))
  | cons p ps ih => exact .trans (.par (.refl p) ih) (.symm (.assoc _ _ _))

theorem parallelOf_perm {ps qs : List Process} (permutation : ps.Perm qs) :
    Congruence (parallelOf ps) (parallelOf qs) := by
  induction permutation with
  | nil => exact .refl _
  | cons p _ ih => exact .par (.refl p) ih
  | swap p q rest =>
      exact .trans (.symm (.assoc _ _ _)) (.trans (.par (.swap _ _) (.refl _)) (.assoc _ _ _))
  | trans _ _ first second => exact .trans first second

theorem parallelOf_singleton (p : Process) : Congruence (parallelOf [p]) p := .unit p

private theorem forall₂_perm {R : Pattern → Process → Prop} {members members' : List Pattern}
    {ps : List Process} (each : List.Forall₂ R members ps) (permutation : members.Perm members') :
    ∃ ps', List.Forall₂ R members' ps' ∧ ps.Perm ps' := by
  obtain ⟨ps', each', permuted⟩ := List.perm_comp_forall₂ permutation.symm each
  exact ⟨ps', each', permuted.symm⟩

private theorem unitName :
    rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor = "PZero" := rfl

/-- Dropping unit members from a decoded list keeps its composition. -/
private theorem decode_filter_unit {members : List Pattern} {ps : List Process}
    (each : List.Forall₂ (fun member q => decodeProcess member = some q) members ps) :
    ∃ kept, List.Forall₂ (fun member q => decodeProcess member = some q)
        (members.filter fun pattern => decide (¬ pattern = .apply "PZero" [])) kept ∧
      Congruence (parallelOf ps) (parallelOf kept) := by
  induction each with
  | nil => exact ⟨[], .nil, .refl _⟩
  | @cons member q members qs head _ ih =>
      obtain ⟨kept, keptEach, keptCongruent⟩ := ih
      by_cases unit : member = .apply "PZero" []
      · subst unit
        simp only [decodeProcess_zero, Option.some.injEq] at head
        subst head
        rw [List.filter_cons_of_neg (by simp)]
        exact ⟨kept, keptEach, .trans (.trans (.swap _ _) (.unit _)) keptCongruent⟩
      · rw [List.filter_cons_of_pos (by simp [unit])]
        exact ⟨q :: kept, .cons head keptEach, .par (.refl q) keptCongruent⟩

/-- The decoded members of the unguarded parallel layer of a pattern. -/
private theorem decode_parallelContents {pattern : Pattern} {p : Process}
    (decoded : decodeProcess pattern = some p) :
    ∃ ps, List.Forall₂ (fun member q => decodeProcess member = some q)
        (parallelContents rhoReflectivePresentation [pattern]) ps ∧
      Congruence p (parallelOf ps) := by
  by_cases isUnit : pattern = .apply "PZero" []
  · subst isUnit
    simp only [decodeProcess_zero, Option.some.injEq] at decoded
    subst decoded
    refine ⟨[], ?_, .refl _⟩
    simp [parallelContents, parallelSplice, rhoReflectivePresentation]
  by_cases isParallel : ∃ members, pattern = .collection .hashBag members none
  · obtain ⟨members, rfl⟩ := isParallel
    rw [decodeProcess_parallel, decodeMembers_eq_some] at decoded
    obtain ⟨ps, each, rfl⟩ := decoded
    have contents : parallelContents rhoReflectivePresentation [.collection .hashBag members none] =
        members.filter fun pattern => decide (¬ pattern = .apply "PZero" []) := by
      simp only [parallelContents, List.flatMap_singleton, parallelSplice,
        rhoReflectivePresentation]
      apply List.filter_congr
      intro pattern _
      by_cases same : pattern = .apply "PZero" [] <;> simp [same]
    rw [contents]
    obtain ⟨kept, keptEach, keptCongruent⟩ := decode_filter_unit each
    exact ⟨kept, keptEach, keptCongruent⟩
  · have splice : parallelSplice rhoReflectivePresentation pattern = [pattern] :=
      parallelSplice_eq_singleton_of_not_parallel _ pattern (by
        intro members same
        exact isParallel ⟨members, same⟩)
    refine ⟨[p], ?_, .symm (parallelOf_singleton p)⟩
    have contents : parallelContents rhoReflectivePresentation [pattern] = [pattern] := by
      unfold parallelContents
      rw [List.flatMap_singleton, splice, List.filter_cons, unitName]
      simp [isUnit]
    rw [contents]
    exact .cons decoded .nil

/-- Decoding a collapsed parallel list gives the composition of its members. -/
private theorem decode_collapseParallel {members : List Pattern} {ps : List Process}
    (each : List.Forall₂ (fun member q => decodeProcess member = some q) members ps) :
    ∃ p, decodeProcess (collapseParallel rhoReflectivePresentation members) = some p ∧
      Congruence p (parallelOf ps) := by
  match members, ps, each with
  | [], [], .nil => exact ⟨.zero, by rfl, .refl _⟩
  | [member], [q], .cons head .nil => exact ⟨q, head, .symm (parallelOf_singleton q)⟩
  | first :: second :: rest, ps, each =>
      refine ⟨parallelOf ps, ?_, .refl _⟩
      change decodeProcess (.collection .hashBag (first :: second :: rest) none) = _
      rw [decodeProcess_parallel, decodeMembers_eq_some]
      exact ⟨ps, each, rfl⟩

/-! ## Every encoded process is read back from its canonical form -/

mutual
  theorem decodeProcess_canonicalize : ∀ p : Process,
      ∃ p', decodeProcess (canonicalize rhoReflectivePresentation (encodeProcess p)) = some p' ∧
        Congruence p p'
    | .zero => ⟨.zero, by rw [canonicalize_zero]; rfl, .refl _⟩
    | .send x q => by
        obtain ⟨x', nameDecoded, nameSame⟩ := decodeName_canonicalize x
        obtain ⟨q', decoded, same⟩ := decodeProcess_canonicalize q
        exact ⟨.send x' q', by simp [canonicalize_send, nameDecoded, decoded],
          .send nameSame same⟩
    | .receive x q => by
        obtain ⟨x', nameDecoded, nameSame⟩ := decodeName_canonicalize x
        obtain ⟨q', decoded, same⟩ := decodeProcess_canonicalize q
        exact ⟨.receive x' q', by simp [canonicalize_receive, nameDecoded, decoded],
          .receive nameSame same⟩
    | .drop x => by
        obtain ⟨x', nameDecoded, nameSame⟩ := decodeName_canonicalize x
        exact ⟨.drop x', by simp [canonicalize_drop, nameDecoded], .drop nameSame⟩
    | .par a b => by
        obtain ⟨a', aDecoded, aSame⟩ := decodeProcess_canonicalize a
        obtain ⟨b', bDecoded, bSame⟩ := decodeProcess_canonicalize b
        obtain ⟨as, aEach, aParallel⟩ := decode_parallelContents aDecoded
        obtain ⟨bs, bEach, bParallel⟩ := decode_parallelContents bDecoded
        have joined : List.Forall₂ (fun member q => decodeProcess member = some q)
            (parallelContents rhoReflectivePresentation
                [canonicalize rhoReflectivePresentation (encodeProcess a)] ++
              parallelContents rhoReflectivePresentation
                [canonicalize rhoReflectivePresentation (encodeProcess b)]) (as ++ bs) :=
          List.rel_append aEach bEach
        rw [← parallelContents_append] at joined
        obtain ⟨sorted, sortedEach, sortedPerm⟩ := forall₂_perm joined
          (sortPatterns_perm (parallelContents rhoReflectivePresentation
            ([canonicalize rhoReflectivePresentation (encodeProcess a)] ++
              [canonicalize rhoReflectivePresentation (encodeProcess b)]))).symm
        obtain ⟨p', decoded, same⟩ := decode_collapseParallel sortedEach
        refine ⟨p', ?_, ?_⟩
        · rw [canonicalize_par]
          exact decoded
        · exact .trans (.par (aSame.trans aParallel) (bSame.trans bParallel))
            (.trans (.symm (parallelOf_append as bs))
              (.trans (parallelOf_perm sortedPerm) (.symm same)))

  theorem decodeName_canonicalize : ∀ x : Name,
      ∃ x', decodeName (canonicalize rhoReflectivePresentation (encodeName x)) = some x' ∧
        NameEquivalence x x'
    | .bound index => ⟨.bound index, by rw [canonicalize_bound]; rfl, .refl _⟩
    | .quote code => by
        obtain ⟨code', decoded, same⟩ := decodeProcess_canonicalize code
        rw [canonicalize_quote]
        rcases Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.finish_cases
            (declaration := rhoReflectivePresentation) "NQuote"
            [canonicalize rhoReflectivePresentation (encodeProcess code)] with
          plain | ⟨name, _, single, finished⟩
        · rw [plain]
          exact ⟨.quote code', by simp [decoded], .quote same⟩
        · rw [finished]
          simp only [List.cons.injEq, and_true] at single
          rw [single] at decoded
          change decodeProcess (.apply "PDrop" [name]) = some code' at decoded
          rw [decodeProcess_drop, Option.map_eq_some_iff] at decoded
          obtain ⟨x', nameDecoded, rfl⟩ := decoded
          exact ⟨x', nameDecoded, .trans (.quote same) (.quote_drop x')⟩
end

/-! ## The bridge -/

/-- **Bridge for processes.** Two encoded processes have the same canonical form
in our calculus exactly when they are structurally congruent in the paper. -/
theorem canonicalize_encodeProcess_eq_iff (p q : Process) :
    canonicalize rhoReflectivePresentation (encodeProcess p) =
        canonicalize rhoReflectivePresentation (encodeProcess q) ↔ Congruence p q := by
  refine ⟨fun same => ?_, Congruence.canonicalize_eq⟩
  obtain ⟨p', pDecoded, pSame⟩ := decodeProcess_canonicalize p
  obtain ⟨q', qDecoded, qSame⟩ := decodeProcess_canonicalize q
  rw [same, qDecoded, Option.some.injEq] at pDecoded
  subst pDecoded
  exact pSame.trans qSame.symm

/-- **Bridge for names.** Two encoded names have the same canonical form in our
calculus exactly when they are name-equivalent in the paper. -/
theorem canonicalize_encodeName_eq_iff (x y : Name) :
    canonicalize rhoReflectivePresentation (encodeName x) =
        canonicalize rhoReflectivePresentation (encodeName y) ↔ NameEquivalence x y := by
  refine ⟨fun same => ?_, NameEquivalence.canonicalize_eq⟩
  obtain ⟨x', xDecoded, xSame⟩ := decodeName_canonicalize x
  obtain ⟨y', yDecoded, ySame⟩ := decodeName_canonicalize y
  rw [same, yDecoded, Option.some.injEq] at xDecoded
  subst xDecoded
  exact xSame.trans ySame.symm

/-- The bridge in the form the matcher uses. -/
theorem canonicalEquivalent_encodeName_iff (x y : Name) :
    canonicalEquivalent rhoReflectivePresentation (encodeName x) (encodeName y) = true ↔
      NameEquivalence x y := by
  rw [canonicalEquivalent_eq_true_iff, canonicalize_encodeName_eq_iff]

/-- The canonical form of a name denotes a binder slot exactly when the paper's
whole-name test selects that slot. -/
theorem canonicalize_encodeName_eq_bvar_iff (x : Name) (index : Nat) :
    canonicalize rhoReflectivePresentation (encodeName x) = .bvar index ↔
      binderIndex x = some index := by
  rw [← canonicalize_bound index, canonicalize_encodeName_eq_iff, nameEquivalence_bound_iff]

/-- A canonical name is a binder slot or a quotation. -/
theorem canonicalize_encodeName_shape (x : Name) :
    (∃ index, canonicalize rhoReflectivePresentation (encodeName x) = .bvar index) ∨
      ∃ code, canonicalize rhoReflectivePresentation (encodeName x) = .apply "NQuote" [code] := by
  obtain ⟨_, decoded, _⟩ := decodeName_canonicalize x
  exact decodeName_shape decoded

/-! ## Unguarded parallel members -/

/-- The unguarded parallel members of a process: its outputs, inputs and drops. -/
def parallelMembers : Process → List Process
  | .zero => []
  | .par p q => parallelMembers p ++ parallelMembers q
  | .send x p => [.send x p]
  | .receive x p => [.receive x p]
  | .drop x => [.drop x]

/-- A process that is an output, an input or a drop. -/
def IsPrefixed : Process → Prop
  | .send .. | .receive .. | .drop .. => True
  | .zero | .par .. => False

theorem parallelMembers_congruence : ∀ p : Process, Congruence p (parallelOf (parallelMembers p))
  | .zero => .refl _
  | .par a b =>
      .trans (.par (parallelMembers_congruence a) (parallelMembers_congruence b))
        (.symm (parallelOf_append _ _))
  | .send .. | .receive .. | .drop .. => .symm (parallelOf_singleton _)

theorem isPrefixed_of_mem_parallelMembers :
    ∀ {p c : Process}, c ∈ parallelMembers p → IsPrefixed c
  | .zero, _, membership => by simp [parallelMembers] at membership
  | .par a b, _, membership => by
      rcases List.mem_append.mp membership with inA | inB
      · exact isPrefixed_of_mem_parallelMembers inA
      · exact isPrefixed_of_mem_parallelMembers inB
  | .send .., _, membership | .receive .., _, membership | .drop .., _, membership => by
      simp only [parallelMembers, List.mem_singleton] at membership
      subst membership
      trivial

theorem parallelMembers_parallelOf : ∀ {ps : List Process}, (∀ c ∈ ps, IsPrefixed c) →
    parallelMembers (parallelOf ps) = ps
  | [], _ => rfl
  | c :: cs, prefixed => by
      have rest : parallelMembers (parallelOf cs) = cs :=
        parallelMembers_parallelOf (fun d member => prefixed d (List.mem_cons_of_mem c member))
      have head := prefixed c (by simp)
      cases c with
      | zero | par _ _ => exact head.elim
      | send _ _ | receive _ _ | drop _ =>
          simp [parallelOf, parallelMembers, rest]

/-- The canonical form, in our calculus, of an encoded paper process. -/
abbrev canonicalForm (p : Process) : Pattern :=
  canonicalize rhoReflectivePresentation (encodeProcess p)

/-- The canonical form of a prefixed process is a single parallel member. -/
private theorem parallelContents_prefixed {c : Process} (prefixed : IsPrefixed c) :
    parallelContents rhoReflectivePresentation [canonicalForm c] = [canonicalForm c] := by
  have notUnit : canonicalForm c ≠ .apply "PZero" [] := by
    cases c with
    | zero | par _ _ => exact prefixed.elim
    | send _ _ => simp [canonicalForm, canonicalize_send]
    | receive _ _ => simp [canonicalForm, canonicalize_receive]
    | drop _ => simp [canonicalForm, canonicalize_drop]
  have splice : parallelSplice rhoReflectivePresentation (canonicalForm c) = [canonicalForm c] := by
    apply parallelSplice_eq_singleton_of_not_parallel
    intro elements same
    cases c with
    | zero | par _ _ => exact prefixed.elim
    | send _ _ => simp [canonicalForm, canonicalize_send] at same
    | receive _ _ => simp [canonicalForm, canonicalize_receive] at same
    | drop _ => simp [canonicalForm, canonicalize_drop] at same
  unfold parallelContents
  rw [List.flatMap_singleton, splice]
  exact List.filter_cons_of_pos (decide_eq_true notUnit)

private theorem parallelContents_map_prefixed :
    ∀ {cs : List Process}, (∀ c ∈ cs, IsPrefixed c) →
    parallelContents rhoReflectivePresentation (cs.map canonicalForm) = cs.map canonicalForm
  | [], _ => rfl
  | c :: cs, prefixed => by
      rw [List.map_cons, show canonicalForm c :: cs.map canonicalForm =
          [canonicalForm c] ++ cs.map canonicalForm from rfl, parallelContents_append,
        parallelContents_prefixed (prefixed c (by simp)),
        parallelContents_map_prefixed (fun d member => prefixed d (by simp [member]))]

/-- The parallel members of a canonical form are the canonical forms of the
parallel members, up to order. -/
theorem parallelContents_canonicalForm : ∀ p : Process,
    (parallelContents rhoReflectivePresentation [canonicalForm p]).Perm
      ((parallelMembers p).map canonicalForm)
  | .zero => by
      rw [show canonicalForm .zero = .apply "PZero" [] from canonicalize_zero]
      unfold parallelContents
      rw [List.flatMap_singleton]
      simp [parallelSplice, parallelMembers, unitName]
  | .par a b => by
      have canonical :
          IsCanonicalList rhoReflectivePresentation [canonicalForm a, canonicalForm b] :=
        canonicalizeList_isCanonical _ [encodeProcess a, encodeProcess b]
      rw [show canonicalForm (.par a b) = _ from canonicalize_par a b,
        parallelContents_collapse_normalized _ canonical,
        normalizeParallelElements_eq_sort_parallelContents]
      refine (sortPatterns_perm _).trans ?_
      rw [show [canonicalForm a, canonicalForm b] = [canonicalForm a] ++ [canonicalForm b] from rfl,
        parallelContents_append, parallelMembers, List.map_append]
      exact (parallelContents_canonicalForm a).append (parallelContents_canonicalForm b)
  | .send x q => by rw [parallelContents_prefixed (by trivial)]; rfl
  | .receive x q => by rw [parallelContents_prefixed (by trivial)]; rfl
  | .drop x => by rw [parallelContents_prefixed (by trivial)]; rfl

/-- A canonical form is the collapsed, sorted list of the canonical forms of the
parallel members. -/
theorem canonicalForm_eq_collapse (p : Process) :
    canonicalForm p = collapseParallel rhoReflectivePresentation
      (sortPatterns ((parallelMembers p).map canonicalForm)) := by
  show canonicalize rhoReflectivePresentation (encodeProcess p) = _
  conv_lhs => rw [← collapse_normalize_singleton_of_isCanonical rhoReflectivePresentation
    (canonicalize_isCanonical rhoReflectivePresentation (encodeProcess p))]
  rw [normalizeParallelElements_eq_sort_parallelContents,
    sortPatterns_eq_of_perm (parallelContents_canonicalForm p)]

/-- Replacing one parallel member of a canonical bag. The remaining members are
the canonical forms of the members of `rest`, in any order. -/
theorem canonicalize_bag_eq {head : Pattern} {residue : List Pattern} {replacement rest : Process}
    (headSame : canonicalize rhoReflectivePresentation head = canonicalForm replacement)
    (residuePerm : residue.Perm ((parallelMembers rest).map canonicalForm)) :
    canonicalize rhoReflectivePresentation (.collection .hashBag (head :: residue) none) =
      canonicalForm (.par replacement rest) := by
  have residueFixed : residue.map (canonicalize rhoReflectivePresentation) = residue := by
    refine List.map_congr_left (fun pattern member => ?_) |>.trans (List.map_id _)
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp (residuePerm.subset member)
    exact canonicalize_idempotent _ _
  have prefixed : ∀ c ∈ parallelMembers rest, IsPrefixed c :=
    fun _ member => isPrefixed_of_mem_parallelMembers member
  rw [show canonicalForm (.par replacement rest) = _ from canonicalize_par replacement rest]
  change canonicalize rhoReflectivePresentation
      (.collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        (head :: residue) none) = _
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.canonicalize_parallel_eq, List.map_cons,
    residueFixed, headSame]
  congr 1
  rw [normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents]
  apply sortPatterns_eq_of_perm
  rw [show canonicalForm replacement :: residue = [canonicalForm replacement] ++ residue from rfl,
    show [canonicalForm replacement, canonicalForm rest] =
      [canonicalForm replacement] ++ [canonicalForm rest] from rfl,
    parallelContents_append, parallelContents_append]
  refine List.Perm.append_left _ ?_
  refine (parallelContents_perm _ residuePerm).trans ?_
  rw [parallelContents_map_prefixed prefixed]
  exact (parallelContents_canonicalForm rest).symm

/-! ## Substitution -/

open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent
  (QuotesResolved QuotesResolvedList canonicalize_substituteResolved_resolveQuotes
    canonicalize_substituteResolved_canonical_parallel canonicalize_normalizeReflective
    normalizeReflective_of_resolved resolveQuotes_of_resolved canonicalize_unary_of_resolved
    substituteResolved_drop substituteResolved_apply_long finish_long finish_not_quote)

/-- The action of reflective substitution on bound indices. -/
private abbrev replacing (replacement : Pattern) : Nat → Nat → Pattern :=
  fun level index => if index = level then replacement else .bvar index

private theorem rho_distinct :
    rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor ≠
      rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor := by
  decide

private theorem substituteResolved_quote (atIndex : Nat → Nat → Pattern) (depth : Nat)
    (code : Pattern) :
    substituteResolved rhoReflectivePresentation atIndex depth (.apply "NQuote" [code]) =
      .apply "NQuote" [code] := by
  simp [substituteResolved, rhoReflectivePresentation]

private theorem receive_quote (code : Pattern) :
    receive rhoReflectivePresentation "PDrop" (.apply "NQuote" [code]) = code := by
  simp [receive, rhoReflectivePresentation]

private theorem canonicalize_apply_two (constructor : String) (first second : Pattern) :
    canonicalize rhoReflectivePresentation (.apply constructor [first, second]) =
      .apply constructor [canonicalize rhoReflectivePresentation first,
        canonicalize rhoReflectivePresentation second] := by
  simp only [canonicalize, canonicalizeList, finish_long]

private theorem canonicalize_dropPattern (name : Pattern) :
    canonicalize rhoReflectivePresentation (.apply "PDrop" [name]) =
      .apply "PDrop" [canonicalize rhoReflectivePresentation name] := by
  simp only [canonicalize, canonicalizeList]
  exact finish_not_quote (by decide) _

private theorem canonicalize_quotePattern (code : Pattern) :
    canonicalize rhoReflectivePresentation (.apply "NQuote" [code]) =
      finishNormalizeReflectiveApply rhoReflectivePresentation "NQuote"
        [canonicalize rhoReflectivePresentation code] := by
  simp only [canonicalize, canonicalizeList]

/-- The binder test of reflective substitution, read on a canonical name, is the
paper's whole-name test. -/
theorem matchesBinder_canonicalize_encodeName (depth : Nat) (x : Name) :
    matchesBinder rhoReflectivePresentation depth
        (canonicalize rhoReflectivePresentation (encodeName x)) = true ↔
      binderIndex x = some depth := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.matchesBinder_canonicalize, matchesBinder,
    decide_eq_true_iff, BinderHead.ofPattern_index_iff, canonicalize_encodeName_eq_bvar_iff]

private theorem substituteResolved_name {payload : Process} {received : Pattern}
    (receivedSame : canonicalize rhoReflectivePresentation received = canonicalForm payload)
    (depth : Nat) (x : Name) :
    canonicalize rhoReflectivePresentation
        (substituteResolved rhoReflectivePresentation (replacing (.apply "NQuote" [received])) depth
          (canonicalize rhoReflectivePresentation (encodeName x))) =
      canonicalize rhoReflectivePresentation (encodeName (bindName payload depth x)) := by
  rcases canonicalize_encodeName_shape x with ⟨index, shape⟩ | ⟨code, shape⟩
  · have binder := (canonicalize_encodeName_eq_bvar_iff x index).mp shape
    rw [shape]
    change canonicalize rhoReflectivePresentation
      (if index = depth then .apply "NQuote" [received] else .bvar index) = _
    unfold bindName
    by_cases hit : index = depth
    · subst hit
      rw [if_pos rfl, if_pos binder, canonicalize_quote, canonicalize_quotePattern, receivedSame]
    · rw [if_neg hit, if_neg (by rw [binder]; simpa using hit), shape]
      rfl
  · have miss : binderIndex x ≠ some depth := fun hit => by
      have selected := (canonicalize_encodeName_eq_bvar_iff x depth).mpr hit
      rw [shape] at selected
      cases selected
    rw [shape, substituteResolved_quote]
    unfold bindName
    rw [if_neg miss, ← shape, canonicalize_idempotent]

private theorem substituteResolved_process {payload : Process} {received : Pattern}
    (receivedSame : canonicalize rhoReflectivePresentation received = canonicalForm payload) :
    ∀ (body : Process) (depth : Nat),
      canonicalize rhoReflectivePresentation
          (substituteResolved rhoReflectivePresentation (replacing (.apply "NQuote" [received]))
            depth (canonicalForm body)) =
        canonicalForm (substitute payload depth body)
  | .zero, depth => by
      rw [show canonicalForm .zero = .apply "PZero" [] from canonicalize_zero]
      simp only [substitute]
      rw [show canonicalForm .zero = .apply "PZero" [] from canonicalize_zero]
      simp [substituteResolved, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
        rhoReflectivePresentation]
  | .par a b, depth => by
      have parallel := canonicalize_substituteResolved_canonical_parallel
        (declaration := rhoReflectivePresentation) (replacing (.apply "NQuote" [received])) depth
        [encodeProcess a, encodeProcess b]
      simp only [List.map_cons, List.map_nil] at parallel
      rw [substituteResolved_process receivedSame a depth,
        substituteResolved_process receivedSame b depth] at parallel
      simp only [substitute]
      rw [show canonicalForm (.par (substitute payload depth a) (substitute payload depth b)) = _
        from canonicalize_par _ _]
      exact parallel
  | .send x q, depth => by
      rw [show canonicalForm (.send x q) = _ from canonicalize_send x q,
        substituteResolved_apply_long, List.map_cons, List.map_singleton, canonicalize_apply_two,
        substituteResolved_name receivedSame, substituteResolved_process receivedSame q depth]
      simp only [substitute]
      rw [show canonicalForm (.send _ _) = _ from canonicalize_send _ _]
  | .receive x q, depth => by
      rw [show canonicalForm (.receive x q) = _ from canonicalize_receive x q,
        substituteResolved_apply_long, List.map_cons, List.map_singleton, canonicalize_apply_two,
        substituteResolved_name receivedSame]
      simp only [substituteResolved, canonicalize]
      rw [substituteResolved_process receivedSame q (depth + 1)]
      simp only [substitute]
      rw [show canonicalForm (.receive _ _) = _ from canonicalize_receive _ _]
  | .drop x, depth => by
      rw [show canonicalForm (.drop x) = _ from canonicalize_drop x]
      change canonicalize rhoReflectivePresentation
        (substituteResolved rhoReflectivePresentation _ depth
        (.apply rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
          [canonicalize rhoReflectivePresentation (encodeName x)])) = _
      rw [substituteResolved_drop rho_distinct]
      simp only [substitute]
      by_cases hit : binderIndex x = some depth
      · rw [if_pos ((matchesBinder_canonicalize_encodeName depth x).mpr hit), if_pos hit]
        rw [show replacing (.apply "NQuote" [received]) depth depth = .apply "NQuote" [received]
          from if_pos rfl]
        exact (congrArg _ (receive_quote received)).trans receivedSame
      · rw [if_neg (fun matched =>
            hit ((matchesBinder_canonicalize_encodeName depth x).mp matched)),
          if_neg hit]
        change canonicalize rhoReflectivePresentation (.apply "PDrop" [_]) = _
        rw [canonicalize_dropPattern, substituteResolved_name receivedSame]
        unfold bindName
        rw [if_neg hit, show canonicalForm (.drop x) = _ from canonicalize_drop x]

/-- **Substitution, up to the equations.** Reflective substitution of the quoted
payload, as the compiled COMM step performs it, has the canonical form of the
paper's substitution. Body and payload may be any patterns with the canonical
forms of the paper's body and payload; no scope or fiber condition is needed. -/
theorem canonicalize_substituteReflective {body received : Pattern} {B P : Process}
    (bodySame : canonicalize rhoReflectivePresentation body = canonicalForm B)
    (payloadSame : canonicalize rhoReflectivePresentation received = canonicalForm P)
    (depth : Nat) :
    canonicalize rhoReflectivePresentation
        (substituteReflective rhoReflectivePresentation depth
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation received]) body) =
      canonicalize rhoReflectivePresentation (encodeProcess (substitute P depth B)) := by
  unfold substituteReflective
  rw [canonicalize_substituteResolved_resolveQuotes, bodySame]
  exact substituteResolved_process
    ((canonicalize_normalizeReflective rho_distinct received).trans payloadSame) B depth

/-- **Substitution on encodings.** -/
theorem canonicalize_substituteReflective_encode (body payload : Process) (depth : Nat) :
    canonicalize rhoReflectivePresentation
        (substituteReflective rhoReflectivePresentation depth
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation (encodeProcess payload)])
          (encodeProcess body)) =
      canonicalize rhoReflectivePresentation (encodeProcess (substitute payload depth body)) :=
  canonicalize_substituteReflective rfl rfl depth

/-! ### The exact fiber -/

private theorem substituteResolved_name_exact {payload : Process} (depth : Nat) :
    ∀ x : Name, QuotesResolved rhoReflectivePresentation (encodeName x) →
      substituteResolved rhoReflectivePresentation
          (replacing (.apply "NQuote" [encodeProcess payload])) depth (encodeName x) =
        encodeName (bindName payload depth x)
  | .bound index, _ => by
      change (if index = depth then _ else _) = _
      unfold bindName
      by_cases hit : index = depth
      · subst hit
        simp [binderIndex, encodeName]
      · rw [if_neg hit, if_neg (by simpa [binderIndex] using hit)]
        rfl
  | .quote code, resolved => by
      change substituteResolved rhoReflectivePresentation _ depth
        (.apply "NQuote" [encodeProcess code]) = _
      rw [substituteResolved_quote]
      have miss : binderIndex (.quote code) ≠ some depth := fun hit => by
        have selected := (canonicalize_encodeName_eq_bvar_iff (.quote code) depth).mpr hit
        change canonicalize rhoReflectivePresentation (.apply "NQuote" [encodeProcess code]) = _
          at selected
        rw [canonicalize_unary_of_resolved resolved] at selected
        cases selected
      unfold bindName
      rw [if_neg miss]
      rfl

private theorem substituteResolved_process_exact {payload : Process} :
    ∀ (body : Process) (depth : Nat),
      QuotesResolved rhoReflectivePresentation (encodeProcess body) →
      substituteResolved rhoReflectivePresentation
          (replacing (.apply "NQuote" [encodeProcess payload])) depth (encodeProcess body) =
        encodeProcess (substitute payload depth body)
  | .zero, depth, _ => by
      simp [substitute, substituteResolved, encodeProcess]
  | .par a b, depth, resolved => by
      obtain ⟨aResolved, bResolved, _⟩ := resolved
      simp only [substitute, encodeProcess, substituteResolved, substituteResolvedList]
      rw [substituteResolved_process_exact a depth aResolved,
        substituteResolved_process_exact b depth bResolved]
  | .send x q, depth, resolved => by
      obtain ⟨⟨xResolved, qResolved, _⟩, _⟩ := resolved
      simp only [substitute, encodeProcess]
      rw [substituteResolved_apply_long, List.map_cons, List.map_singleton,
        substituteResolved_name_exact depth x xResolved,
        substituteResolved_process_exact q depth qResolved]
  | .receive x q, depth, resolved => by
      obtain ⟨⟨xResolved, qResolved, _⟩, _⟩ := resolved
      simp only [substitute, encodeProcess]
      rw [substituteResolved_apply_long, List.map_cons, List.map_singleton,
        substituteResolved_name_exact depth x xResolved]
      simp only [substituteResolved]
      rw [substituteResolved_process_exact q (depth + 1) qResolved]
  | .drop x, depth, resolved => by
      obtain ⟨⟨xResolved, _⟩, _⟩ := resolved
      simp only [substitute]
      change substituteResolved rhoReflectivePresentation _ depth
        (.apply rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
          [encodeName x]) = _
      rw [substituteResolved_drop rho_distinct]
      have test : matchesBinder rhoReflectivePresentation depth (encodeName x) = true ↔
          binderIndex x = some depth := by
        rw [← Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.matchesBinder_canonicalize,
          matchesBinder_canonicalize_encodeName]
      by_cases hit : binderIndex x = some depth
      · rw [if_pos (test.mpr hit), if_pos hit,
          show replacing (.apply "NQuote" [encodeProcess payload]) depth depth =
            .apply "NQuote" [encodeProcess payload] from if_pos rfl]
        exact receive_quote _
      · rw [if_neg (fun matched => hit (test.mp matched)), if_neg hit,
          substituteResolved_name_exact depth x xResolved]
        unfold bindName
        rw [if_neg hit]
        rfl

/-- **Substitution, exactly, on the resolved fiber.** When neither body nor payload
has a quotation exposing a drop, the compiled substitution is the paper's
substitution, spelling for spelling. -/
theorem substituteReflective_encode_exact (body payload : Process) (depth : Nat)
    (bodyResolved : QuotesResolved rhoReflectivePresentation (encodeProcess body))
    (payloadResolved : QuotesResolved rhoReflectivePresentation (encodeProcess payload)) :
    substituteReflective rhoReflectivePresentation depth
        (.apply "NQuote" [normalizeReflective rhoReflectivePresentation (encodeProcess payload)])
        (encodeProcess body) =
      encodeProcess (substitute payload depth body) := by
  unfold substituteReflective
  rw [normalizeReflective_of_resolved payloadResolved, resolveQuotes_of_resolved bodyResolved]
  exact substituteResolved_process_exact body depth bodyResolved

/-! ## Our step relation -/

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStepAt RhoStep)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep
  (rhoStepAt_cases rhoStepAt_comm_at CanonicalStep)

/-! ## Steps both ways -/

/-- Every reduction of the paper is one communication in a parallel context, up
to structural congruence on both sides. -/
theorem redex_of_reduction {p q : Process} (step : Reduction p q) :
    ∃ (offered waiting : Name) (payload body rest : Process),
      ScopedName 0 offered ∧ ScopedName 0 waiting ∧ ScopedProcess 0 payload ∧
      ScopedProcess 1 body ∧ NameEquivalence offered waiting ∧
      Congruence p (.par (.par (.send offered payload) (.receive waiting body)) rest) ∧
      Congruence q (.par (substitute payload 0 body) rest) := by
  induction step with
  | comm offered waiting payload body agree substitution =>
      refine ⟨_, _, _, _, .zero, offered, waiting, payload, body, agree, .symm (.unit _), ?_⟩
      rw [← substitution.substitute_eq]
      exact .symm (.unit _)
  | par frame _ ih =>
      obtain ⟨offered, waiting, payload, body, rest, o, w, pl, b, agree, before, after⟩ := ih
      exact ⟨offered, waiting, payload, body, .par rest frame, o, w, pl, b, agree,
        .trans (.par before (.refl frame)) (.assoc _ _ _),
        .trans (.par after (.refl frame)) (.assoc _ _ _)⟩
  | equiv before _ after ih =>
      obtain ⟨offered, waiting, payload, body, rest, o, w, pl, b, agree, start, finish⟩ := ih
      exact ⟨offered, waiting, payload, body, rest, o, w, pl, b, agree, before.trans start,
        after.symm.trans finish⟩

private theorem perm_map_cons_inv {f : Process → Pattern} {l : List Process} {a : Pattern}
    {t : List Pattern} (permutation : (l.map f).Perm (a :: t)) :
    ∃ x l', l.Perm (x :: l') ∧ f x = a ∧ (l'.map f).Perm t := by
  obtain ⟨x, member, rfl⟩ := List.mem_map.mp (permutation.symm.subset (List.mem_cons_self))
  obtain ⟨front, back, rfl⟩ := List.append_of_mem member
  have split : (front ++ x :: back).Perm (x :: (front ++ back)) := List.perm_middle
  refine ⟨x, front ++ back, split, rfl, ?_⟩
  have mapped := (split.map f).symm.trans permutation
  exact mapped.cons_inv

private theorem perm_extract_two (elements : List Pattern) (first second : Nat)
    (firstBound : first < elements.length)
    (secondBound : second < (elements.eraseIdx first).length) :
    elements.Perm
      (elements[first] :: (elements.eraseIdx first)[second] ::
        (elements.eraseIdx first).eraseIdx second) :=
  (List.getElem_cons_eraseIdx_perm firstBound).symm.trans
    ((List.getElem_cons_eraseIdx_perm secondBound).symm.cons _)

private theorem canonicalForm_prefixed_ne_collection {c : Process} (prefixed : IsPrefixed c)
    (kind : CollType) (elements : List Pattern) (rest : Option String) :
    canonicalForm c ≠ .collection kind elements rest := by
  cases c with
  | zero | par _ _ => exact prefixed.elim
  | send _ _ => simp [canonicalForm, canonicalize_send]
  | receive _ _ => simp [canonicalForm, canonicalize_receive]
  | drop _ => simp [canonicalForm, canonicalize_drop]

/-- A canonical form that is a parallel bag lists the canonical forms of the
parallel members. -/
theorem canonicalForm_collection {p : Process} {kind : CollType} {elements : List Pattern}
    {termRest : Option String}
    (shape : canonicalForm p = .collection kind elements termRest) :
    termRest = none ∧ elements.Perm ((parallelMembers p).map canonicalForm) := by
  rw [canonicalForm_eq_collapse] at shape
  have sorted := sortPatterns_perm ((parallelMembers p).map canonicalForm)
  generalize sortPatterns ((parallelMembers p).map canonicalForm) = listed at shape sorted
  match listed, shape, sorted with
  | [], shape, _ => cases shape
  | [single], shape, sorted =>
      obtain ⟨c, member, rfl⟩ := List.mem_map.mp (sorted.subset (List.mem_singleton_self _))
      exact absurd shape (canonicalForm_prefixed_ne_collection
        (isPrefixed_of_mem_parallelMembers member) _ _ _)
  | first :: second :: more, shape, sorted =>
      change Pattern.collection .hashBag (first :: second :: more) none = _ at shape
      cases shape
      exact ⟨rfl, sorted⟩

private theorem congruence_of_members_perm {p : Process} {cs : List Process}
    (permutation : (parallelMembers p).Perm cs) : Congruence p (parallelOf cs) :=
  (parallelMembers_congruence p).trans (parallelOf_perm permutation)

private theorem prefixed_of_members_perm {p c : Process} {cs : List Process}
    (permutation : (parallelMembers p).Perm (c :: cs)) :
    IsPrefixed c ∧ ∀ d ∈ cs, IsPrefixed d :=
  ⟨isPrefixed_of_mem_parallelMembers (permutation.symm.subset List.mem_cons_self),
    fun _ member => isPrefixed_of_mem_parallelMembers
      (permutation.symm.subset (List.mem_cons_of_mem _ member))⟩

private theorem scopedProcess_par {depth : Nat} {p q : Process}
    (admitted : ScopedProcess depth (.par p q)) :
    ScopedProcess depth p ∧ ScopedProcess depth q := by
  cases admitted with
  | par left right => exact ⟨left, right⟩

/-- **Steps, from the paper to our calculus.** Every reduction of the paper is
matched by a step of our calculus from the canonical form of the source, landing
on the canonical form of the target. -/
theorem rhoStep_of_reduction {p q : Process} (step : Reduction p q) :
    ∃ r, RhoStep (canonicalize rhoReflectivePresentation (encodeProcess p)) r ∧
      canonicalize rhoReflectivePresentation r =
        canonicalize rhoReflectivePresentation (encodeProcess q) := by
  obtain ⟨offered, waiting, payload, body, rest, _, _, _, _, agree, before, after⟩ :=
    redex_of_reduction step
  let output : Process := .send offered payload
  let input : Process := .receive waiting body
  let residueForms := (parallelMembers rest).map canonicalForm
  have outputForm : canonicalForm output = .apply "POutput"
      [canonicalize rhoReflectivePresentation (encodeName offered), canonicalForm payload] :=
    canonicalize_send offered payload
  have inputForm : canonicalForm input = .apply "PInput"
      [canonicalize rhoReflectivePresentation (encodeName waiting),
        .lambda none (canonicalForm body)] :=
    canonicalize_receive waiting body
  let listed := sortPatterns (canonicalForm output :: canonicalForm input :: residueForms)
  have listedPerm : listed.Perm (canonicalForm output :: canonicalForm input :: residueForms) :=
    sortPatterns_perm _
  have sourceForm : canonicalForm p = .collection .hashBag listed none := by
    rw [show canonicalForm p = canonicalForm (.par (.par output input) rest) from
        (canonicalize_encodeProcess_eq_iff _ _).mpr before, canonicalForm_eq_collapse]
    have lengthBound : 2 ≤ listed.length := by simp [listed, listedPerm.length_eq]
    have members : (parallelMembers (.par (.par output input) rest)).map canonicalForm =
        canonicalForm output :: canonicalForm input :: residueForms := by
      simp [parallelMembers, output, input, residueForms]
    rw [members]
    exact collapseParallel_eq_collection_of_length_ge_two _ lengthBound
  obtain ⟨inputIndex, inputBound, inputAt⟩ := List.getElem_of_mem
    (listedPerm.symm.subset (List.mem_cons_of_mem _ List.mem_cons_self))
  have afterInput : (listed.eraseIdx inputIndex).Perm (canonicalForm output :: residueForms) := by
    have whole := (List.getElem_cons_eraseIdx_perm inputBound).trans listedPerm
    rw [inputAt] at whole
    exact (whole.trans (List.Perm.swap _ _ _)).cons_inv
  obtain ⟨outputIndex, outputBound, outputAt⟩ := List.getElem_of_mem
    (afterInput.symm.subset List.mem_cons_self)
  have residuePerm : ((listed.eraseIdx inputIndex).eraseIdx outputIndex).Perm residueForms := by
    have whole := (List.getElem_cons_eraseIdx_perm outputBound).trans afterInput
    rw [outputAt] at whole
    exact whole.cons_inv
  have channels : canonicalize rhoReflectivePresentation
        (canonicalize rhoReflectivePresentation (encodeName waiting)) =
      canonicalize rhoReflectivePresentation
        (canonicalize rhoReflectivePresentation (encodeName offered)) := by
    rw [canonicalize_idempotent, canonicalize_idempotent]
    exact ((canonicalize_encodeName_eq_iff _ _).mpr agree).symm
  refine ⟨_, sourceForm ▸ (⟨1, rhoStepAt_comm_at (termRest := none) inputBound outputBound
    (inputAt.trans inputForm) (outputAt.trans outputForm) channels⟩ : RhoStep _ _), ?_⟩
  rw [show canonicalize rhoReflectivePresentation (encodeProcess q) =
      canonicalForm (.par (substitute payload 0 body) rest) from
    (canonicalize_encodeProcess_eq_iff _ _).mpr after]
  exact canonicalize_bag_eq
    (canonicalize_substituteReflective (canonicalize_idempotent _ _)
      (canonicalize_idempotent _ _) 0)
    residuePerm

/-- **Steps, from our calculus to the paper, on canonical forms.** Every step of
our calculus from the canonical form of a closed process is matched by a
reduction of the paper, landing on the canonical form of its target. -/
theorem rhoStepAt_canonicalForm_reduction :
    ∀ {fuel : Nat} {p : Process} {r : Pattern}, ScopedProcess 0 p →
      RhoStepAt fuel (canonicalize rhoReflectivePresentation (encodeProcess p)) r →
      ∃ q, Reduction p q ∧
        canonicalize rhoReflectivePresentation r =
          canonicalize rhoReflectivePresentation (encodeProcess q) := by
  intro fuel
  induction fuel with
  | zero => intro p r _ step; cases step
  | succ fuel ih =>
  intro p r closed step
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
      binder, outputChannel, payload, sourceEq, inputEq, outputEq, channels, targetEq⟩ |
    ⟨smaller, elements, termRest, index, indexBound, candidate, fuelEq, sourceEq, innerStep,
      targetEq⟩
  · obtain ⟨_, elementsPerm⟩ := canonicalForm_collection sourceEq
    have extracted := (perm_extract_two elements inputIndex outputIndex inputBound
      outputBound).symm.trans elementsPerm
    rw [inputEq, outputEq] at extracted
    obtain ⟨inputMember, others, inputSplit, inputShape, othersPerm⟩ :=
      perm_map_cons_inv extracted.symm
    obtain ⟨outputMember, rest, outputSplit, outputShape, restPerm⟩ :=
      perm_map_cons_inv othersPerm
    have arrangement : (parallelMembers p).Perm (inputMember :: outputMember :: rest) :=
      inputSplit.trans (outputSplit.cons _)
    obtain ⟨inputPrefixed, othersPrefixed⟩ := prefixed_of_members_perm arrangement
    have outputPrefixed := othersPrefixed outputMember List.mem_cons_self
    have restPrefixed : ∀ d ∈ rest, IsPrefixed d :=
      fun d member => othersPrefixed d (List.mem_cons_of_mem _ member)
    cases inputMember with
    | zero | par _ _ => exact inputPrefixed.elim
    | send _ _ => simp [canonicalForm, canonicalize_send] at inputShape
    | drop _ => simp [canonicalForm, canonicalize_drop] at inputShape
    | receive waiting received =>
    cases outputMember with
    | zero | par _ _ => exact outputPrefixed.elim
    | receive _ _ => simp [canonicalForm, canonicalize_receive] at outputShape
    | drop _ => simp [canonicalForm, canonicalize_drop] at outputShape
    | send offered sent =>
    rw [show canonicalForm (.receive waiting received) = _ from canonicalize_receive _ _]
      at inputShape
    rw [show canonicalForm (.send offered sent) = _ from canonicalize_send _ _] at outputShape
    simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
      true_and] at inputShape outputShape
    obtain ⟨waitingEq, binderEq, bodyEq⟩ := inputShape
    obtain ⟨offeredEq, payloadEq⟩ := outputShape
    have arranged := congruence_of_members_perm arrangement
    have closedArranged := (arranged.scoped_iff 0).mp closed
    simp only [parallelOf] at arranged closedArranged
    obtain ⟨inputScoped, outputAndRest⟩ := scopedProcess_par closedArranged
    obtain ⟨outputScoped, _⟩ := scopedProcess_par outputAndRest
    cases inputScoped with
    | receive waitingScoped bodyScoped =>
    cases outputScoped with
    | send offeredScoped payloadScoped =>
    have agree : NameEquivalence offered waiting := by
      apply NameEquivalence.symm
      rw [← canonicalize_encodeName_eq_iff, ← canonicalize_idempotent rhoReflectivePresentation
        (encodeName waiting), ← canonicalize_idempotent rhoReflectivePresentation
        (encodeName offered), waitingEq, offeredEq]
      exact channels
    refine ⟨.par (substitute sent 0 received) (parallelOf rest), ?_, ?_⟩
    · exact .equiv
        (arranged.trans (.trans (.symm (.assoc _ _ _)) (.par (.swap _ _) (.refl _))))
        (.par _ (.comm offeredScoped waitingScoped payloadScoped bodyScoped agree
          (substitute_fits sent 0 received)))
        (.refl _)
    · rw [targetEq]
      refine canonicalize_bag_eq
        (canonicalize_substituteReflective (by rw [← bodyEq]; exact canonicalize_idempotent _ _)
          (by rw [← payloadEq]; exact canonicalize_idempotent _ _) 0) ?_
      rw [parallelMembers_parallelOf restPrefixed]
      exact restPerm.symm
  · cases fuelEq
    obtain ⟨_, elementsPerm⟩ := canonicalForm_collection sourceEq
    have extracted := (List.getElem_cons_eraseIdx_perm indexBound).trans elementsPerm
    obtain ⟨member, rest, split, memberShape, restPerm⟩ := perm_map_cons_inv extracted.symm
    obtain ⟨_, restPrefixed⟩ := prefixed_of_members_perm split
    have arranged := congruence_of_members_perm split
    have closedArranged := (arranged.scoped_iff 0).mp closed
    simp only [parallelOf] at arranged closedArranged
    obtain ⟨memberScoped, _⟩ := scopedProcess_par closedArranged
    rw [← memberShape] at innerStep
    obtain ⟨reduced, memberReduces, reducedForm⟩ := ih memberScoped innerStep
    refine ⟨.par reduced (parallelOf rest),
      .equiv arranged (.par _ memberReduces) (.refl _), ?_⟩
    rw [targetEq]
    refine canonicalize_bag_eq reducedForm ?_
    rw [parallelMembers_parallelOf restPrefixed]
    exact restPerm.symm

/-- Unbounded form of `rhoStepAt_canonicalForm_reduction`. -/
theorem rhoStep_canonicalForm_reduction {p : Process} {r : Pattern} (closed : ScopedProcess 0 p)
    (step : RhoStep (canonicalize rhoReflectivePresentation (encodeProcess p)) r) :
    ∃ q, Reduction p q ∧
      canonicalize rhoReflectivePresentation r =
        canonicalize rhoReflectivePresentation (encodeProcess q) := by
  obtain ⟨_, bounded⟩ := step
  exact rhoStepAt_canonicalForm_reduction closed bounded

/-- **Two-way step adequacy.** For a closed process, the paper's reduction is
exactly a step of our calculus from the canonical form, read up to canonical
equality of the target. -/
theorem reduction_iff_rhoStep {p q : Process} (closed : ScopedProcess 0 p) :
    Reduction p q ↔
      ∃ r, RhoStep (canonicalize rhoReflectivePresentation (encodeProcess p)) r ∧
        canonicalize rhoReflectivePresentation r =
          canonicalize rhoReflectivePresentation (encodeProcess q) := by
  refine ⟨rhoStep_of_reduction, ?_⟩
  rintro ⟨r, step, same⟩
  obtain ⟨q', reduces, form⟩ := rhoStep_canonicalForm_reduction closed step
  exact .equiv (.refl _) reduces
    ((canonicalize_encodeProcess_eq_iff q' q).mp (form.symm.trans same))

/-! ## Many steps

Each step of our calculus is read at the canonical form of its target
(`CanonicalStep`), so the next step starts from the next canonical form. -/

/-- Closed scope is preserved along paper reductions. -/
theorem closed_of_reflTransGen {p q : Process}
    (steps : Relation.ReflTransGen Reduction p q) (closed : ScopedProcess 0 p) :
    ScopedProcess 0 q := by
  induction steps with
  | refl => exact closed
  | tail _ step ih => exact step.preserves_closed_scope ih

/-- One paper reduction is one step between canonical forms. -/
theorem canonicalStep_of_reduction {p q : Process} (step : Reduction p q) :
    CanonicalStep (canonicalForm p) (canonicalForm q) :=
  rhoStep_of_reduction step

/-- The next canonical form reached from the canonical form of a closed process
is the canonical form of a paper reduct. -/
theorem reduction_of_canonicalStep {p : Process} {u : Pattern} (closed : ScopedProcess 0 p)
    (step : CanonicalStep (canonicalForm p) u) : ∃ q, Reduction p q ∧ canonicalForm q = u := by
  obtain ⟨r, rStep, rfl⟩ := step
  obtain ⟨q, reduces, form⟩ := rhoStep_canonicalForm_reduction closed rStep
  exact ⟨q, reduces, form.symm⟩

/-- **Many steps, from the paper to our calculus.** -/
theorem reflTransGen_canonicalStep_of_reduction {p q : Process}
    (steps : Relation.ReflTransGen Reduction p q) :
    Relation.ReflTransGen CanonicalStep (canonicalForm p) (canonicalForm q) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (canonicalStep_of_reduction step)

/-- **Many steps, from our calculus to the paper.** -/
theorem reduction_of_reflTransGen_canonicalStep {p : Process} {u : Pattern}
    (closed : ScopedProcess 0 p) (steps : Relation.ReflTransGen CanonicalStep (canonicalForm p) u) :
    ∃ q, Relation.ReflTransGen Reduction p q ∧ canonicalForm q = u := by
  induction steps with
  | refl => exact ⟨p, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨q, reductions, rfl⟩ := ih
      obtain ⟨q', reduces, form⟩ :=
        reduction_of_canonicalStep (closed_of_reflTransGen reductions closed) step
      exact ⟨q', reductions.tail reduces, form⟩

/-- **Many-step adequacy.** For a closed process, the canonical forms reachable
by our calculus from its canonical form are exactly the canonical forms of its
paper reducts. -/
theorem reflTransGen_canonicalStep_iff {p : Process} {u : Pattern} (closed : ScopedProcess 0 p) :
    Relation.ReflTransGen CanonicalStep (canonicalForm p) u ↔
      ∃ q, Relation.ReflTransGen Reduction p q ∧ canonicalForm q = u :=
  ⟨reduction_of_reflTransGen_canonicalStep closed,
    fun ⟨_, steps, form⟩ => form ▸ reflTransGen_canonicalStep_of_reduction steps⟩

/-- Between the canonical forms of two processes, many-step adequacy holds up to
the paper's congruence at the end. -/
theorem reflTransGen_canonicalStep_iff_congruent {p q : Process} (closed : ScopedProcess 0 p) :
    Relation.ReflTransGen CanonicalStep (canonicalForm p) (canonicalForm q) ↔
      ∃ q', Relation.ReflTransGen Reduction p q' ∧ Congruence q' q := by
  rw [reflTransGen_canonicalStep_iff closed]
  exact exists_congr fun q' => and_congr_right fun _ => canonicalize_encodeProcess_eq_iff q' q

/-- **At least one step.** The last reduction absorbs the congruence, so the
transitive closures correspond exactly. -/
theorem transGen_reduction_iff_canonicalStep {p q : Process} (closed : ScopedProcess 0 p) :
    Relation.TransGen Reduction p q ↔
      Relation.TransGen CanonicalStep (canonicalForm p) (canonicalForm q) := by
  constructor
  · intro steps
    induction steps with
    | single step => exact .single (canonicalStep_of_reduction step)
    | tail _ step ih => exact ih.tail (canonicalStep_of_reduction step)
  · intro steps
    have reached : ∀ {u : Pattern}, Relation.TransGen CanonicalStep (canonicalForm p) u →
        ∃ q', Relation.TransGen Reduction p q' ∧ canonicalForm q' = u := by
      intro u steps
      induction steps with
      | single step =>
          obtain ⟨q', reduces, form⟩ := reduction_of_canonicalStep closed step
          exact ⟨q', .single reduces, form⟩
      | tail _ step ih =>
          obtain ⟨q, reductions, rfl⟩ := ih
          obtain ⟨q', reduces, form⟩ := reduction_of_canonicalStep
            (closed_of_reflTransGen reductions.to_reflTransGen closed) step
          exact ⟨q', reductions.tail reduces, form⟩
    obtain ⟨q', reductions, form⟩ := reached steps
    have same : Congruence q' q := (canonicalize_encodeProcess_eq_iff q' q).mp form
    cases reductions with
    | single step => exact .single (.equiv (.refl _) step same)
    | tail first step => exact first.tail (.equiv (.refl _) step same)

/-! ### Steps from the plain encoding -/

private theorem encodeProcess_eq_collection {p : Process} {kind : CollType}
    {elements : List Pattern} {termRest : Option String}
    (shape : encodeProcess p = .collection kind elements termRest) :
    ∃ a b, p = .par a b ∧ elements = [encodeProcess a, encodeProcess b] ∧
      termRest = none := by
  cases p <;> simp [encodeProcess] at shape
  obtain ⟨_, rfl, rfl⟩ := shape
  exact ⟨_, _, rfl, rfl, rfl⟩

private theorem encodeProcess_eq_input {p : Process} {channel body : Pattern}
    {binder : Option String}
    (shape : encodeProcess p = .apply "PInput" [channel, .lambda binder body]) :
    ∃ y B, p = .receive y B ∧ channel = encodeName y ∧ body = encodeProcess B := by
  cases p <;> simp [encodeProcess] at shape
  obtain ⟨rfl, _, rfl⟩ := shape
  exact ⟨_, _, rfl, rfl, rfl⟩

private theorem encodeProcess_eq_output {p : Process} {channel payload : Pattern}
    (shape : encodeProcess p = .apply "POutput" [channel, payload]) :
    ∃ x P, p = .send x P ∧ channel = encodeName x ∧ payload = encodeProcess P := by
  cases p <;> simp [encodeProcess] at shape
  obtain ⟨rfl, rfl⟩ := shape
  exact ⟨_, _, rfl, rfl, rfl⟩

private theorem canonicalize_pair {first second : Pattern} {X Y : Process}
    (firstSame : canonicalize rhoReflectivePresentation first = canonicalForm X)
    (secondSame : canonicalize rhoReflectivePresentation second = canonicalForm Y) :
    canonicalize rhoReflectivePresentation (.collection .hashBag [first, second] none) =
      canonicalForm (.par X Y) := by
  change canonicalize rhoReflectivePresentation
      (.collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        [first, second] none) = _
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.canonicalize_parallel_eq, List.map_cons,
    List.map_singleton, firstSame, secondSame]
  exact (canonicalize_par X Y).symm

private theorem canonicalize_single {only : Pattern} :
    canonicalize rhoReflectivePresentation (.collection .hashBag [only] none) =
      canonicalize rhoReflectivePresentation only :=
  canonicalize_parallel_singleton rhoReflectivePresentation only

/-- **Steps, from our calculus to the paper, on plain encodings.** Every step of
our calculus from the encoding of a closed process is matched by a reduction of
the paper. -/
theorem rhoStepAt_encodeProcess_reduction :
    ∀ {fuel : Nat} {p : Process} {r : Pattern}, ScopedProcess 0 p →
      RhoStepAt fuel (encodeProcess p) r →
      ∃ q, Reduction p q ∧
        canonicalize rhoReflectivePresentation r =
          canonicalize rhoReflectivePresentation (encodeProcess q) := by
  intro fuel
  induction fuel with
  | zero => intro p r _ step; cases step
  | succ fuel ih =>
  intro p r closed step
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
      binder, outputChannel, payload, sourceEq, inputEq, outputEq, channels, targetEq⟩ |
    ⟨smaller, elements, termRest, index, indexBound, candidate, fuelEq, sourceEq, innerStep,
      targetEq⟩
  · obtain ⟨a, b, rfl, rfl, rfl⟩ := encodeProcess_eq_collection sourceEq
    obtain ⟨aClosed, bClosed⟩ := scopedProcess_par closed
    have commutes : ∀ {x y : Name} {P B : Process}, ScopedProcess 0 (.send x P) →
        ScopedProcess 0 (.receive y B) →
        canonicalize rhoReflectivePresentation (encodeName y) =
          canonicalize rhoReflectivePresentation (encodeName x) →
        Reduction (.par (.send x P) (.receive y B)) (substitute P 0 B) := by
      intro x y P B sendClosed receiveClosed same
      cases sendClosed with
      | send xScoped PScoped =>
      cases receiveClosed with
      | receive yScoped BScoped =>
      exact .comm xScoped yScoped PScoped BScoped
        ((canonicalize_encodeName_eq_iff y x).mp same).symm (substitute_fits P 0 B)
    match inputIndex, inputBound, outputIndex, outputBound, inputEq, outputEq, targetEq with
    | 0, _, 0, _, inputEq, outputEq, targetEq =>
        obtain ⟨y, B, rfl, rfl, rfl⟩ := encodeProcess_eq_input inputEq
        obtain ⟨x, P, rfl, rfl, rfl⟩ := encodeProcess_eq_output outputEq
        refine ⟨substitute P 0 B,
          .equiv (.swap _ _) (commutes bClosed aClosed channels) (.refl _), ?_⟩
        rw [targetEq]
        exact canonicalize_single.trans (canonicalize_substituteReflective_encode B P 0)
    | 1, _, 0, _, inputEq, outputEq, targetEq =>
        obtain ⟨y, B, rfl, rfl, rfl⟩ := encodeProcess_eq_input inputEq
        obtain ⟨x, P, rfl, rfl, rfl⟩ := encodeProcess_eq_output outputEq
        refine ⟨substitute P 0 B, commutes aClosed bClosed channels, ?_⟩
        rw [targetEq]
        exact canonicalize_single.trans (canonicalize_substituteReflective_encode B P 0)
    | 0, _, _ + 1, outputBound, _, _, _ => simp at outputBound
    | 1, _, _ + 1, outputBound, _, _, _ => simp at outputBound
    | _ + 2, inputBound, _, _, _, _, _ => simp at inputBound
  · cases fuelEq
    obtain ⟨a, b, rfl, rfl, rfl⟩ := encodeProcess_eq_collection sourceEq
    obtain ⟨aClosed, bClosed⟩ := scopedProcess_par closed
    match index, indexBound, innerStep, targetEq with
    | 0, _, innerStep, targetEq =>
        obtain ⟨reduced, reduces, form⟩ := ih aClosed innerStep
        refine ⟨.par reduced b, .par b reduces, ?_⟩
        rw [targetEq]
        exact canonicalize_pair form rfl
    | 1, _, innerStep, targetEq =>
        obtain ⟨reduced, reduces, form⟩ := ih bClosed innerStep
        refine ⟨.par a reduced, .equiv (.swap _ _) (.par a reduces) (.swap _ _), ?_⟩
        rw [targetEq]
        exact (canonicalize_pair form rfl).trans (Congruence.canonicalize_eq (.swap _ _))
    | _ + 2, indexBound, _, _ => simp at indexBound

/-- Unbounded form of `rhoStepAt_encodeProcess_reduction`. -/
theorem rhoStep_encodeProcess_reduction {p : Process} {r : Pattern} (closed : ScopedProcess 0 p)
    (step : RhoStep (encodeProcess p) r) :
    ∃ q, Reduction p q ∧
      canonicalize rhoReflectivePresentation r =
        canonicalize rhoReflectivePresentation (encodeProcess q) := by
  obtain ⟨_, bounded⟩ := step
  exact rhoStepAt_encodeProcess_reduction closed bounded

/-- On the resolved fiber, the COMM step of our calculus from a plain encoded
redex lands on the encoding of the paper's contractum, spelling for spelling. -/
theorem rhoStep_encode_comm_exact {x y : Name} {B P : Process}
    (channels : NameEquivalence x y)
    (bodyResolved : QuotesResolved rhoReflectivePresentation (encodeProcess B))
    (payloadResolved : QuotesResolved rhoReflectivePresentation (encodeProcess P)) :
    RhoStep (encodeProcess (.par (.receive y B) (.send x P)))
      (.collection .hashBag [encodeProcess (substitute P 0 B)] none) := by
  have step : RhoStep _ _ := ⟨1, rhoStepAt_comm_at
    (elements := [encodeProcess (.receive y B), encodeProcess (.send x P)]) (termRest := none)
    (inputIndex := 0) (outputIndex := 0) (by simp) (by simp) rfl rfl
    ((canonicalize_encodeName_eq_iff y x).mpr channels.symm)⟩
  rw [substituteReflective_encode_exact B P 0 bodyResolved payloadResolved] at step
  exact step

/-- Equal canonical forms with at least two parallel members have the same
parallel members up to order and the equations. -/
theorem parallelMembers_perm_of_canonicalForm_eq {p q : Process}
    (many : 2 ≤ (parallelMembers p).length) (same : canonicalForm p = canonicalForm q) :
    ((parallelMembers p).map canonicalForm).Perm ((parallelMembers q).map canonicalForm) := by
  have sorted := sortPatterns_perm ((parallelMembers p).map canonicalForm)
  have shape : canonicalForm p = .collection .hashBag
      (sortPatterns ((parallelMembers p).map canonicalForm)) none := by
    rw [canonicalForm_eq_collapse]
    exact collapseParallel_eq_collection_of_length_ge_two _ (by simpa [sorted.length_eq] using many)
  obtain ⟨_, other⟩ := canonicalForm_collection (same ▸ shape)
  exact sorted.symm.trans other

#print axioms canonicalize_encodeProcess_eq_iff
#print axioms canonicalize_encodeName_eq_iff
#print axioms canonicalEquivalent_encodeName_iff
#print axioms canonicalize_substituteReflective
#print axioms canonicalize_substituteReflective_encode
#print axioms substituteReflective_encode_exact
#print axioms rhoStep_of_reduction
#print axioms rhoStep_canonicalForm_reduction
#print axioms rhoStep_encodeProcess_reduction
#print axioms reduction_iff_rhoStep
#print axioms rhoStep_encode_comm_exact
#print axioms reflTransGen_canonicalStep_of_reduction
#print axioms reduction_of_reflTransGen_canonicalStep
#print axioms reflTransGen_canonicalStep_iff
#print axioms reflTransGen_canonicalStep_iff_congruent
#print axioms transGen_reduction_iff_canonicalStep

end Mettapedia.GSLT.Contracts.PaperRho.Adequacy
