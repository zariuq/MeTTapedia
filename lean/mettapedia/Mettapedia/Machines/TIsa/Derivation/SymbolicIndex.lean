import Mettapedia.Machines.TIsa.Derivation.FirstOrderIndex
import Mettapedia.Machines.TIsa.Derivation.SymbolicFiring

/-!
# Indexing unresolved first-order terms

A constructor at a fixed position survives every substitution. An
unknown at that position does not. The index keeps a separate
posting list for these unknowns, common to every compatible lookup.
Equal answers never share an occurrence merely because they share
a posting key. Key collisions can retain a candidate, not reject it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicIndex

open Mettapedia.Logic.LP
open FirstOrderTerms (Head)
open OccurrencePostings (bucket group bucket_group)

variable {σ : LPSignature}

def head : Term σ → Option (Head σ)
  | .var _ => none
  | .const c => some (.inl c)
  | .app f _ => some (.inr f)

def argument (position : ℕ) : Term σ → Option (Head σ)
  | .app f args =>
    if inside : position < σ.functionArity f then head (args ⟨position, inside⟩) else none
  | _ => none

theorem head_fixed (solution : Subst σ) {term : Term σ} {key : Head σ}
    (known : head term = some key) : head (solution.applyTerm term) = some key := by
  cases term <;> first | exact known | cases known

theorem argument_fixed (solution : Subst σ) (position : ℕ) {term : Term σ} {key : Head σ}
    (known : argument position term = some key) : argument position (solution.applyTerm term) = some key := by
  cases term with
  | var _ => cases known
  | const _ => cases known
  | app f args =>
    by_cases inside : position < σ.functionArity f
    · simp only [argument, dif_pos inside] at known
      simp only [Subst.applyTerm, argument, dif_pos inside]
      exact head_fixed solution known
    · simp [argument, inside] at known

structure Search (K : Type*) where
  headKey : K
  argumentKey : Option (ℕ × K)

variable {K : Type*} [BEq K] [Hashable K]

def termKey (encode : Head σ → K) (t : Term σ) : Option K := (head t).map encode
def argKey (encode : Head σ → K) (position : ℕ) (t : Term σ) : Option K :=
  (argument position t).map encode

def request (encode : Head σ → K) (width : ℕ) (t : Term σ) : Option (Search K) :=
  (termKey encode t).map fun h =>
    ⟨h, (List.range width).findSome? fun i => (argKey encode i t).map fun a => (i, a)⟩

def Search.matches (query : Search K) (encode : Head σ → K) (width : ℕ) (value : Term σ) : Bool :=
  match termKey encode value with
  | none => true
  | some h =>
    (h == query.headKey) &&
      match query.argumentKey with
      | none => true
      | some (i, a) => if i < width then
          match argKey encode i value with
          | none => true
          | some b => (b == a)
        else true

def compatible (encode : Head σ → K) (width : ℕ) (pattern value : Term σ) : Bool :=
  ((request encode width pattern).map fun q => q.matches encode width value).getD true

omit [BEq K] [Hashable K] in
private theorem keys_agree {project : Term σ → Option (Head σ)}
    (fixed : ∀ (s : Subst σ) {t k}, project t = some k → project (s.applyTerm t) = some k)
    (encode : Head σ → K) {p v : Term σ} {a b : K} (solution : Subst σ)
    (equal : solution.applyTerm p = solution.applyTerm v)
    (left : (project p).map encode = some a) (right : (project v).map encode = some b) : b = a := by
  obtain ⟨ka, knownA, rfl⟩ := Option.map_eq_some_iff.mp left
  obtain ⟨kb, knownB, rfl⟩ := Option.map_eq_some_iff.mp right
  exact congrArg encode (Option.some.inj ((fixed solution knownB).symm.trans ((congrArg project equal).symm.trans
    (fixed solution knownA))))

omit [Hashable K] in
theorem compatible_of_unified [LawfulBEq K] (encode : Head σ → K) (width : ℕ) (pattern value : Term σ)
    (solution : Subst σ) (equal : solution.applyTerm pattern = solution.applyTerm value) :
    compatible encode width pattern value = true := by
  cases ep : termKey encode pattern with
  | none => simp [compatible, request, ep]
  | some p =>
    cases ev : termKey encode value with
    | none => simp [compatible, request, Search.matches, ep, ev]
    | some v =>
      have same := keys_agree head_fixed encode solution equal ep ev
      simp only [compatible, request, ep, Option.map_some, Option.getD_some, Search.matches, ev,
        same, beq_self_eq_true, Bool.true_and]
      split
      · rfl
      · rename_i i a requested
        by_cases bounded : i < width
        · have inPattern : argKey encode i pattern = some a := by
            obtain ⟨j, _, result⟩ := List.exists_of_findSome?_eq_some requested
            obtain ⟨tag, read, found⟩ := Option.map_eq_some_iff.mp result
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj found
            exact read
          cases read : argKey encode i value with
          | none => simp [bounded]
          | some b =>
            have inside := keys_agree (fun s {t k} h => argument_fixed s i (term := t) (key := k) h)
              encode solution equal inPattern read
            simp [bounded, inside]
        · simp [bounded]

structure Index (σ : LPSignature) (K : Type*) [BEq K] [Hashable K] where
  source : List (ℕ × Term σ)
  heads : Std.HashMap (Option K) (List (ℕ × Term σ))
  args : List (Std.HashMap (Option K × Option K) (List (ℕ × Term σ)))

def build (encode : Head σ → K) (width : ℕ) (source : List (ℕ × Term σ)) : Index σ K where
  source
  heads := group (termKey encode ∘ Prod.snd) source
  args := (List.range width).map fun i => group (fun (_, t) => (termKey encode t, argKey encode i t)) source

def lookup (pattern : Term σ) (encode : Head σ → K) (width : ℕ) (index : Index σ K) :
    List (ℕ × Term σ) :=
  match request encode width pattern with
  | none => index.source
  | some request =>
    let wild := bucket index.heads none
    let full := bucket index.heads (some request.headKey)
    match request.argumentKey with
    | none => wild ++ full
    | some (i, a) =>
      match index.args[i]? with
      | none => wild ++ full
      | some table => wild ++ bucket table (some request.headKey, none) ++ bucket table (some request.headKey, some a)

omit [BEq K] [Hashable K] in
private theorem disjoint_filters {A : Type*} (source : List A) (first second : A → Bool)
    (apart : ∀ a, first a = true → second a = false) :
    (source.filter first ++ source.filter second).Perm (source.filter fun a => first a || second a) := by
  induction source with
  | nil => exact .nil
  | cons a rest ih =>
    cases f : first a with
    | true => simpa only [List.filter_cons, f, apart a f, Bool.true_or, if_true, Bool.false_eq_true,
        if_false, List.cons_append] using ih.cons a
    | false =>
      cases s : second a
      · simpa only [List.filter_cons, f, s, Bool.false_or, Bool.false_eq_true, if_false] using ih
      · simp only [List.filter_cons, f, s, Bool.false_or, Bool.false_eq_true, if_false, if_true]
        exact List.perm_middle.trans (ih.cons a)

variable [LawfulBEq K]

private theorem pair_beq {A B : Type*} [BEq A] [BEq B] (a c : A) (b d : B) :
    ((a, b) == (c, d)) = ((a == c) && (b == d)) := rfl

theorem lookup_perm_filter (pattern : Term σ) (encode : Head σ → K) (width : ℕ)
    (source : List (ℕ × Term σ)) :
    (lookup pattern encode width (build encode width source)).Perm
      (source.filter fun entry => compatible encode width pattern entry.2) := by
  cases h : request encode width pattern with
  | none => simp [lookup, h, build, compatible]
  | some q =>
    simp only [lookup, h, compatible, Option.map_some, Option.getD_some, build, bucket_group, Function.comp_def]
    cases requestArg : q.argumentKey with
    | none =>
      refine (disjoint_filters source _ _ ?_).trans ?_
      · intro entry wild
        simp [eq_of_beq wild]
      · apply List.Perm.of_eq
        apply List.filter_congr
        intro entry _
        cases e : termKey encode entry.2 <;> simp [Search.matches, e, requestArg]
    | some ask =>
      obtain ⟨position, value⟩ := ask
      by_cases indexed : position < width
      · simp only [List.getElem?_map, List.getElem?_range indexed, Option.map_some, bucket_group]
        rw [List.append_assoc]
        have arg := disjoint_filters source
          (fun entry => (termKey encode entry.2, argKey encode position entry.2) == (some q.headKey, none))
          (fun entry => (termKey encode entry.2, argKey encode position entry.2) == (some q.headKey, some value))
          (fun entry yes => by
            have key : argKey encode position entry.2 = none := congrArg Prod.snd (eq_of_beq yes)
            simp [pair_beq, key])
        refine (arg.append_left _).trans ((disjoint_filters source _ _ ?_).trans ?_)
        · intro entry wild
          have key := eq_of_beq wild
          simp [pair_beq, key]
        · apply List.Perm.of_eq
          apply List.filter_congr
          intro entry _
          cases e : termKey encode entry.2 <;> cases a : argKey encode position entry.2 <;>
            simp [Search.matches, e, a, requestArg, indexed, pair_beq]
      · have unavailable : (List.range width)[position]? = none := List.getElem?_eq_none (by simpa using indexed)
        simp only [List.getElem?_map, unavailable, Option.map_none]
        refine (disjoint_filters source _ _ ?_).trans ?_
        · intro entry wild
          simp [eq_of_beq wild]
        · apply List.Perm.of_eq
          apply List.filter_congr
          intro entry _
          cases e : termKey encode entry.2 <;> simp [Search.matches, e, requestArg, indexed]

theorem lookup_keeps_solution (encode : Head σ → K) (width : ℕ) (pattern : Term σ)
    (source : List (ℕ × Term σ)) {id : ℕ} {term : Term σ} (inside : (id, term) ∈ source)
    (solution : Subst σ) (equal : solution.applyTerm pattern = solution.applyTerm term) :
    (id, term) ∈ lookup pattern encode width (build encode width source) :=
  (lookup_perm_filter pattern encode width source).mem_iff.mpr
    (List.mem_filter.mpr ⟨inside, compatible_of_unified encode width pattern term solution equal⟩)

section Source

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.OneFrame (Terms ext)
open SymbolicFiring (World act)

variable {O : Type} [DecidableEq O] {program : RuleSyntax.Program (Terms (Term σ))}
  {before : World σ O}

omit [Hashable K] in
/-- The necessary key test applies to the symbolic firing itself, even
when its solution also uses stored knowledge and tells. -/
theorem matching_compatible (encode : Head σ → K) (width : ℕ)
    (f : RuleSyntax.Firing O (ext (FirstOrder.action σ)) program before.frame)
    (admitted : f.Admits (act σ) before) (equation : Term σ × Term σ)
    (inside : equation ∈ f.matching (act σ) before (f.opened (act σ)).take f.selection.taken ++
        f.matching (act σ) before (f.opened (act σ)).read f.selection.read) :
    compatible encode width equation.1 equation.2 = true := by
  obtain ⟨_, solution, solved⟩ := admitted.2.2.1
  have carries : equation ∈ f.information (act σ) before := by
    unfold RuleSyntax.Firing.information
    simp only [List.mem_append] at inside ⊢
    tauto
  exact compatible_of_unified encode width _ _ solution (solved equation carries)

end Source

namespace Examples

private abbrev signature : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Bool
  functionArity := fun _ => 1

private def wrap (f : Bool) (argument : Term signature) : Term signature := .app f (fun _ => argument)

private def encode : Head signature → ℕ
  | .inl c => c + 2
  | .inr f => if f then 0 else 1

private def store : List (ℕ × Term signature) :=
  [(0, .var 9), (1, wrap true (.var 0)), (2, wrap true (.const 7)),
   (3, wrap true (.const 7)), (4, wrap true (.const 8)), (5, wrap false (.const 7))]

/-- Both unknown positions and both equal occurrences survive; the
different constructor and different fixed argument are rejected. -/
theorem unknowns_are_not_missing_and_duplicates_are_not_merged :
    ((lookup (wrap true (.const 7)) encode 1 (build encode 1 store)).map Prod.fst).Perm [0, 1, 2, 3] := by
  have exactIndex := (lookup_perm_filter (wrap true (.const 7)) encode 1 store).map Prod.fst
  have expected : (store.filter fun e => compatible encode 1 (wrap true (.const 7)) e.2).map Prod.fst =
      [0, 1, 2, 3] := by decide +kernel
  rw [expected] at exactIndex
  exact exactIndex

theorem the_unknown_head_can_become_a_match :
    ∃ θ : Subst signature, θ.applyTerm (.var 9) = θ.applyTerm (wrap true (.const 7)) :=
  ⟨fun _ => wrap true (.const 7), rfl⟩

end Examples

end Mettapedia.Machines.TIsa.Derivation.SymbolicIndex
