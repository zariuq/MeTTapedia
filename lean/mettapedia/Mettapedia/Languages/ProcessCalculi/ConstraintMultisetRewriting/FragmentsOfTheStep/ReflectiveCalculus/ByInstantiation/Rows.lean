import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Bisimulation

/-!
# Rows: the representation of closed processes, and what similarity keeps

* `represent_closed`: every closed process of the source is the read-back of a ground twin term,
  exactly (`read t = P`): the translation's inverse on its image is the read-back. The translation
  writes the received name's drop as the twin variable, and a drop of quoted code as `dropq`.
* Similarity is kept by renaming (`similar_rename`) and by the instantiation of a continuation at
  similar received processes (`similar_made`).
* Inversion of similarity at each former (`similar_input_inv`, ...), and the spine weight of a
  row (`spine`), which similarity keeps (`similar_spine`).
* Primes of bags read back (`primes_cons_bag`, `primes_empty_bag`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-! ## The representation of closed processes -/

/-- The name variable of the `i`-th pair. -/
def nameAt : (m i : Nat) → i < m → Var (pairs m) .nm
  | _ + 1, 0, _ => .zero
  | m + 1, i + 1, small => .succ (.succ (nameAt m i (by omega)))

theorem half_nameAt : ∀ (m i : Nat) (small : i < m), half (position (nameAt m i small)) = i
  | _ + 1, 0, _ => rfl
  | m + 1, i + 1, small => by
      show half (position (nameAt m i _)) + 1 = i + 1
      rw [half_nameAt m i]

/-- The twin of a name variable. -/
def twinOf : (m : Nat) → Var (pairs m) .nm → Var (pairs m) .pr
  | _ + 1, .zero => .succ .zero
  | m + 1, .succ (.succ w) => .succ (.succ (twinOf m w))

theorem half_twinOf : ∀ (m : Nat) (v : Var (pairs m) .nm), half (position (twinOf m v)) = half (position v)
  | _ + 1, .zero => rfl
  | m + 1, .succ (.succ w) => by
      show half (position (twinOf m w)) + 1 = half (position w) + 1
      rw [half_twinOf m w]

mutual
  theorem represent_name : ∀ {bound : List String} {n : Pattern},
      NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound n →
      (∀ x ∈ bound, x = rhoReflectivePresentation.nameSort) →
      ∃ t : G (pairs bound.length) .nm, read t = n
    | bound, _, .bvar (index := index) lookup, _ => by
        have small : index < bound.length := (List.getElem?_eq_some_iff.mp lookup).1
        refine ⟨.var (nameAt bound.length index small), ?_⟩
        show Pattern.bvar (half (position (nameAt bound.length index small))) = _
        rw [half_nameAt]
    | _, _, .fvar lookup, _ => by simp [FreeSortContext.empty] at lookup
    | _, _, .quote typed _, names => by
        obtain ⟨t, same⟩ := represent_proc typed names
        exact ⟨quoteT t, by rw [read_quote, same]; rfl⟩

  theorem represent_proc : ∀ {bound : List String} {p : Pattern},
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound p →
      (∀ x ∈ bound, x = rhoReflectivePresentation.nameSort) →
      ∃ t : G (pairs bound.length) .pr, read t = p
    | bound, _, .bvar (index := index) lookup, names => by
        obtain ⟨small, value⟩ := List.getElem?_eq_some_iff.mp lookup
        have same := names _ (List.getElem_mem small)
        rw [value] at same
        simp [rhoReflectivePresentation] at same
    | _, _, .fvar lookup, _ => by simp [FreeSortContext.empty] at lookup
    | _, _, .unit, _ => ⟨zeroT, rfl⟩
    | bound, _, .drop typed, names => by
        obtain ⟨t, same⟩ := represent_name typed names
        match t, same with
        | .var v, same =>
            refine ⟨.var (twinOf bound.length v), ?_⟩
            show Pattern.apply "PDrop" [.bvar (half (position (twinOf bound.length v)))] = _
            rw [half_twinOf, ← same]
            rfl
        | .op (.inl .quote) (.cons p .nil), same =>
            refine ⟨dropqT p, ?_⟩
            rw [read_dropq, ← same]
            rfl
        | .op (.inr o) _, _ => exact o.key.elim
    | _, _, .output channelTyped payloadTyped, names => by
        obtain ⟨c, sameC⟩ := represent_name channelTyped names
        obtain ⟨p, sameP⟩ := represent_proc payloadTyped names
        exact ⟨outputT c p, by rw [read_output, sameC, sameP]; rfl⟩
    | bound, _, .input channelTyped bodyTyped, names => by
        obtain ⟨c, sameC⟩ := represent_name channelTyped names
        obtain ⟨b, sameB⟩ := represent_proc bodyTyped (by
          intro x member
          rcases List.mem_cons.mp member with rfl | member
          · rfl
          · exact names x member)
        refine ⟨inputT c b, ?_⟩
        show Pattern.apply "PInput" [read c, .lambda none (read b)] = _
        rw [sameC, sameB]
        rfl
    | _, _, .parallel listTyped, names => by
        obtain ⟨l, same⟩ := represent_list listTyped names
        exact ⟨bagT l, by rw [read_bag, same]; rfl⟩

  theorem represent_list : ∀ {bound : List String} {ps : List Pattern},
      ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty bound ps →
      (∀ x ∈ bound, x = rhoReflectivePresentation.nameSort) →
      ∃ l : G (pairs bound.length) .ps, read l = .collection .hashBag ps none
    | _, _, .nil, _ => ⟨pnilT, rfl⟩
    | _, _, .cons headTyped tailTyped, names => by
        obtain ⟨p, sameP⟩ := represent_proc headTyped names
        obtain ⟨l, sameL⟩ := represent_list tailTyped names
        exact ⟨pconsT p l, by rw [read_pcons, sameP, sameL]; rfl⟩
end

/-- **Every closed process is the read-back of a ground twin term**, exactly. -/
theorem represent_closed (P : RhoProcess) : ∃ t : G [] .pr, read t = P.1 :=
  represent_proc ((rhoClosedTermWellSorted_process_iff _).mp P.2).1 (fun _ member => by
    simp at member)

/-- A representation of a closed process is closed. -/
theorem represent_closed_safe {P : RhoProcess} {t : G [] .pr} (same : read t = P.1) : Closed t := by
  show binderSafeAt "NQuote" 0 (read t) = true
  rw [same]
  exact ((rhoClosedTermWellSorted_process_iff _).mp P.2).2

/-! ## Inversion of similarity -/

section Inversion

variable {Γ : Ctx sig}

theorem similar_zero_inv {u : G Γ .pr} (similar : Similar zeroT u) : u = zeroT := by
  cases similar
  rfl

theorem similar_bag_inv {l : G Γ .ps} {u : G Γ .pr} (similar : Similar (bagT l) u) :
    ∃ l', u = bagT l' ∧ Similar l l' := by
  cases similar with
  | bag inner => exact ⟨_, rfl, inner⟩

theorem similar_pnil_inv {u : G Γ .ps} (similar : Similar pnilT u) : u = pnilT := by
  cases similar
  rfl

theorem similar_pcons_inv {p : G Γ .pr} {l : G Γ .ps} {u : G Γ .ps}
    (similar : Similar (pconsT p l) u) : ∃ p' l', u = pconsT p' l' ∧ Similar p p' ∧ Similar l l' := by
  cases similar with
  | pcons head tail => exact ⟨_, _, rfl, head, tail⟩

theorem similar_input_inv {c : G Γ .nm} {b : G (.nm :: .pr :: Γ) .pr} {u : G Γ .pr}
    (similar : Similar (inputT c b) u) : ∃ c' b', u = inputT c' b' ∧ Similar c c' ∧ Similar b b' := by
  cases similar with
  | input channel body => exact ⟨_, _, rfl, channel, body⟩

theorem similar_output_inv {c : G Γ .nm} {p : G Γ .pr} {u : G Γ .pr}
    (similar : Similar (outputT c p) u) : ∃ c' p', u = outputT c' p' ∧ Similar c c' ∧ Similar p p' := by
  cases similar with
  | output channel payload => exact ⟨_, _, rfl, channel, payload⟩

end Inversion

/-! ## The spine weight -/

/-- **The spine weight** of a term: one for the null process, one for each bag and each component
of a bag along the parallel structure; nothing for a prime. -/
def spine : {Γ : Ctx sig} → {s : Srt} → G Γ s → Nat
  | _, _, .op (.inl .zero) .nil => 1
  | _, _, .op (.inl .bag) (.cons l .nil) => spine l + 1
  | _, _, .op (.inl .pcons) (.cons p (.cons l .nil)) => spine p + spine l + 1
  | _, _, _ => 0

theorem spine_name : ∀ {Γ : Ctx sig} (n : G Γ .nm), spine n = 0
  | _, .var _ => rfl
  | _, .op (.inl .quote) (.cons _ .nil) => rfl
  | _, .op (.inr o) _ => o.key.elim

/-- **Similar terms have the same spine.** -/
theorem similar_spine {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} (similar : Similar t t') :
    spine t = spine t' := by
  induction similar with
  | var => rfl
  | name => rw [spine_name, spine_name]
  | zero => rfl
  | bag _ inner => exact congrArg (· + 1) inner
  | pnil => rfl
  | pcons _ _ head tail => exact congrArg (· + 1) (congrArg₂ (· + ·) head tail)
  | input => rfl
  | output => rfl
  | dropq => rfl
  | quote => rfl

/-! ## Similarity under renaming and instantiation -/

section Rename

variable {Γ Δ : Ctx sig} (ρ : Ren (signature sig noUnknowns) Γ Δ)

theorem rename_zero : rename ρ (zeroT (D := noUnknowns) (Γ := Γ)) = zeroT := rfl
theorem rename_bag (l : G Γ .ps) : rename ρ (bagT l) = bagT (rename ρ l) := rfl
theorem rename_pnil : rename ρ (pnilT (D := noUnknowns) (Γ := Γ)) = pnilT := rfl
theorem rename_pcons (p : G Γ .pr) (l : G Γ .ps) :
    rename ρ (pconsT p l) = pconsT (rename ρ p) (rename ρ l) := rfl
theorem rename_input (c : G Γ .nm) (b : G (.nm :: .pr :: Γ) .pr) :
    rename ρ (inputT c b) = inputT (rename ρ c) (rename (liftRen ρ [.nm, .pr]) b) := rfl
theorem rename_output (c : G Γ .nm) (p : G Γ .pr) :
    rename ρ (outputT c p) = outputT (rename ρ c) (rename ρ p) := rfl
theorem rename_dropq (p : G Γ .pr) : rename ρ (dropqT p) = dropqT (rename ρ p) := rfl
theorem rename_quote (p : G Γ .pr) : rename ρ (quoteT p) = quoteT (rename ρ p) := rfl

end Rename

/-- **Similarity is kept by renamings that keep positions.** -/
theorem similar_rename {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} (similar : Similar t t') :
    ∀ {Δ : Ctx sig} (ρ : Ren (signature sig noUnknowns) Γ Δ), KeepsPositions ρ →
      Similar (rename ρ t) (rename ρ t') := by
  induction similar with
  | var v => exact fun ρ _ => .var (ρ _ v)
  | @name Γ n m closedN closedM same =>
      intro Δ ρ keeps
      refine .name ?_ ?_ ?_
      · show binderSafeAt "NQuote" 0 (read (rename ρ n)) = true
        rw [read_rename n ρ keeps]
        exact closedN
      · show binderSafeAt "NQuote" 0 (read (rename ρ m)) = true
        rw [read_rename m ρ keeps]
        exact closedM
      · rw [read_rename n ρ keeps, read_rename m ρ keeps]
        exact same
  | zero => exact fun _ _ => .zero
  | bag _ inner => exact fun ρ keeps => .bag (inner ρ keeps)
  | pnil => exact fun _ _ => .pnil
  | pcons _ _ head tail => exact fun ρ keeps => .pcons (head ρ keeps) (tail ρ keeps)
  | input _ _ channel body =>
      exact fun ρ keeps => .input (channel ρ keeps)
        (body (liftRen ρ [.nm, .pr]) (keepsPositions_liftRen keeps _))
  | output _ _ channel payload =>
      exact fun ρ keeps => .output (channel ρ keeps) (payload ρ keeps)
  | dropq _ inner => exact fun ρ keeps => .dropq (inner ρ keeps)
  | quote _ inner => exact fun ρ keeps => .quote (inner ρ keeps)

/-- Two substitutions of the `k`-th pair by similar received values. -/
structure SimilarShifts (k : Nat) {Γ Δ : Ctx sig} (σ σ' : Sub (signature sig noUnknowns) Γ Δ) :
    Prop where
  inner : ∀ (s : Srt) (v : Var Γ s), half (position v) < k →
    ∃ w : Var Δ s, σ s v = .var w ∧ σ' s v = .var w ∧ position w = position v
  received : ∀ (s : Srt) (v : Var Γ s), half (position v) = k →
    ∃ (c c' : G [] s) (ρ ρ' : Ren (signature sig noUnknowns) [] Δ),
      σ s v = rename ρ c ∧ σ' s v = rename ρ' c' ∧ Similar c c'

theorem similarShifts_fixes {k : Nat} {Γ Δ : Ctx sig} {σ σ' : Sub (signature sig noUnknowns) Γ Δ}
    (shifts : SimilarShifts k σ σ') : Fixes k σ ∧ Fixes k σ' := by
  refine ⟨fun s v small => ?_, fun s v small => ?_⟩
  · obtain ⟨w, one, _, at'⟩ := shifts.inner s v small
    exact ⟨w, one, at'⟩
  · obtain ⟨w, _, two, at'⟩ := shifts.inner s v small
    exact ⟨w, two, at'⟩

theorem similarShifts_liftSub {k : Nat} {Γ Δ : Ctx sig} {σ σ' : Sub (signature sig noUnknowns) Γ Δ}
    (shifts : SimilarShifts k σ σ') :
    SimilarShifts (k + 1) (liftSub σ [.nm, .pr]) (liftSub σ' [.nm, .pr]) := by
  refine ⟨?_, ?_⟩
  · intro s v small
    match v with
    | .zero => exact ⟨.zero, rfl, rfl, rfl⟩
    | .succ .zero => exact ⟨.succ .zero, rfl, rfl, rfl⟩
    | .succ (.succ w) =>
        have inner : half (position w) < k := by
          have : half (position w) + 1 < k + 1 := small
          omega
        obtain ⟨w', one, two, at'⟩ := shifts.inner s w inner
        refine ⟨.succ (.succ w'), ?_, ?_, ?_⟩
        · show weaken (weaken (σ s w)) = _
          rw [one]
          rfl
        · show weaken (weaken (σ' s w)) = _
          rw [two]
          rfl
        · show position w' + 1 + 1 = position w + 1 + 1
          rw [at']
  · intro s v at'
    match v with
    | .zero => exact absurd at' (by simp [position, half])
    | .succ .zero => exact absurd at' (by simp [position, half])
    | .succ (.succ w) =>
        have outer : half (position w) = k := by
          have : half (position w) + 1 = k + 1 := at'
          omega
        obtain ⟨c, c', ρ, ρ', one, two, similar⟩ := shifts.received s w outer
        refine ⟨c, c', fun s' u => .succ (.succ (ρ s' u)), fun s' u => .succ (.succ (ρ' s' u)),
          ?_, ?_, similar⟩
        · show weaken (weaken (σ s w)) = _
          rw [one]
          simp only [weaken, rename_comp]
        · show weaken (weaken (σ' s w)) = _
          rw [two]
          simp only [weaken, rename_comp]

/-- Renamings of the empty context are all equal. -/
theorem ren_empty_eq {Δ : Ctx sig} (ρ ρ' : Ren (signature sig noUnknowns) [] Δ) : ρ = ρ' :=
  funext fun _ => funext fun v => nomatch v

/-- **Similar terms instantiated at similar received values are similar.** -/
theorem similar_bind {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} (similar : Similar t t') :
    ∀ (k : Nat) {Δ : Ctx sig} (σ σ' : Sub (signature sig noUnknowns) Γ Δ), Γ = pairs (k + 1) →
      SimilarShifts k σ σ' → Similar (bind σ t) (bind σ' t') := by
  induction similar with
  | @var Γ s v =>
      intro k Δ σ σ' shape shifts
      have small : half (position v) < k + 1 := by
        subst shape
        exact (var_pairs (k + 1) v).1
      rcases Nat.lt_or_ge (half (position v)) k with inner | outer
      · obtain ⟨w, one, two, _⟩ := shifts.inner s v inner
        show Similar (σ s v) (σ' s v)
        rw [one, two]
        exact .var w
      · obtain ⟨c, c', ρ, ρ', one, two, related⟩ := shifts.received s v (by omega)
        show Similar (σ s v) (σ' s v)
        rw [one, two, ren_empty_eq ρ' ρ]
        exact similar_rename related ρ (keepsPositions_empty ρ)
  | @name Γ n m closedN closedM same =>
      intro k Δ σ σ' shape shifts
      have fixedN : read (bind σ n) = read n :=
        read_bind_fixed n (k + 1) 0 σ shape (fixes_zero σ) closedN
      have fixedM : read (bind σ' m) = read m :=
        read_bind_fixed m (k + 1) 0 σ' shape (fixes_zero σ') closedM
      refine .name ?_ ?_ ?_
      · show binderSafeAt "NQuote" 0 (read (bind σ n)) = true
        rw [fixedN]
        exact closedN
      · show binderSafeAt "NQuote" 0 (read (bind σ' m)) = true
        rw [fixedM]
        exact closedM
      · rw [fixedN, fixedM]
        exact same
  | zero => exact fun _ _ _ _ _ _ => .zero
  | bag _ inner =>
      exact fun k Δ σ σ' shape shifts => .bag (inner k σ σ' shape shifts)
  | pnil => exact fun _ _ _ _ _ _ => .pnil
  | pcons _ _ head tail =>
      exact fun k Δ σ σ' shape shifts =>
        .pcons (head k σ σ' shape shifts) (tail k σ σ' shape shifts)
  | input _ _ channel body =>
      intro k Δ σ σ' shape shifts
      exact .input (channel k σ σ' shape shifts)
        (body (k + 1) (liftSub σ [.nm, .pr]) (liftSub σ' [.nm, .pr]) (by rw [shape]; rfl)
          (similarShifts_liftSub shifts))
  | output _ _ channel payload =>
      exact fun k Δ σ σ' shape shifts =>
        .output (channel k σ σ' shape shifts) (payload k σ σ' shape shifts)
  | dropq _ inner =>
      exact fun k Δ σ σ' shape shifts => .dropq (inner k σ σ' shape shifts)
  | quote _ inner =>
      exact fun k Δ σ σ' shape shifts => .quote (inner k σ σ' shape shifts)

/-- **The made row is determined up to similarity**: a similar continuation instantiated at a
similar received process is similar. -/
theorem similar_made {b b' : G [.nm, .pr] .pr} {q q' : G [] .pr} (bodies : Similar b b')
    (payloads : Similar q q') : Similar (bind (received q) b) (bind (received q') b') := by
  refine similar_bind bodies 0 (received q) (received q') rfl ⟨?_, ?_⟩
  · intro s v small
    exact absurd small (Nat.not_lt_zero _)
  · intro s v _
    match v with
    | .zero =>
        exact ⟨quoteT q, quoteT q', fun _ v => v, fun _ v => v, (rename_id _).symm,
          (rename_id _).symm, .quote payloads⟩
    | .succ .zero =>
        exact ⟨q, q', fun _ v => v, fun _ v => v, (rename_id _).symm, (rename_id _).symm,
          payloads⟩

/-! ## Primes of read-back bags -/

theorem primes_bag (elements : List Pattern) :
    primes (.collection .hashBag elements none) =
      (Canonical.bagContents (elements.map canonicalize) : Multiset Pattern) := by
  unfold primes
  rw [CanonicalStepperCompleteness.canonicalize_bag, CanonicalBag.normalize_multiset,
    Canonical.bagContents_collapse_normalized (CanonicalBag.canonical_list_map elements),
    CanonicalBag.normalize_multiset]

theorem primes_singleton (pattern : Pattern) :
    primes pattern = (Canonical.bagContents [canonicalize pattern] : Multiset Pattern) := by
  unfold primes
  rw [CanonicalBag.normalize_multiset]

/-- **The primes of a bag are those of its first component and of the rest.** -/
theorem primes_cons_bag (first : Pattern) (elements : List Pattern) :
    primes (.collection .hashBag (first :: elements) none) =
      primes first + primes (.collection .hashBag elements none) := by
  rw [primes_bag, primes_bag, primes_singleton, List.map_cons, ← List.singleton_append,
    Canonical.bagContents_append, ← Multiset.coe_add]

theorem primes_empty_bag : primes (.collection .hashBag [] none) = 0 := by
  rw [primes_bag]
  rfl

#print axioms represent_closed
#print axioms similar_spine
#print axioms similar_bind
#print axioms similar_made
#print axioms primes_cons_bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
