import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Knowledge

/-!
# The contractum by instantiation

A continuation is a ground term `b` open in one pair (the received name and its twin). The made
row of communication is `b` instantiated at the received name `@q` and the received process `q`:
`bind (received q) b`, the term algebra's own capture-avoiding substitution.

* `contract`: for every sealed continuation (no bound position inside a quote), the read-back of
  the instantiation is structurally congruent to the calculus's semantic substitution of the
  read-backs, at every binder depth.
* `contractum_by_instantiation`: hence the instantiated continuation, read back, has the canonical
  form of the calculus's communication contractum `semanticCommSubst`, for every continuation and
  payload in the image of the representation, canonical or not.
* `instantiation_sealed`: the instantiation is sealed again, so the next communication applies.
* Read-back facts used by the step: read-backs are well sorted (`read_sorted`), hash-set free
  (`read_hashSetFree`), and invariant under renamings that keep positions (`read_rename`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize HashSetFree HashSetFreeList)

/-! ## Contexts of pairs -/

/-- The context of a continuation under `n` inputs: each input binds a name and its twin. -/
def pairs : Nat → Ctx sig
  | 0 => []
  | n + 1 => .nm :: .pr :: pairs n

/-- In a context of pairs, a variable belongs to one of the pairs and is a name or a twin. -/
theorem var_pairs : ∀ (m : Nat) {s : Srt} (v : Var (pairs m) s), half (position v) < m ∧ s ≠ .ps
  | 0, _, v => nomatch v
  | _ + 1, _, .zero => ⟨Nat.succ_pos _, by decide⟩
  | _ + 1, _, .succ .zero => ⟨Nat.succ_pos _, by decide⟩
  | m + 1, _, .succ (.succ w) => by
      obtain ⟨small, sorted⟩ := var_pairs m w
      refine ⟨?_, sorted⟩
      show half (position w + 1 + 1) < m + 1
      show half (position w) + 1 < m + 1
      omega

/-! ## Read-back under renaming -/

/-- A renaming that keeps every variable at its position. -/
def KeepsPositions {Γ Δ : Ctx sig} (ρ : Ren (signature sig noUnknowns) Γ Δ) : Prop :=
  ∀ (s : Srt) (v : Var Γ s), position (ρ s v) = position v

theorem keepsPositions_liftRen {Γ Δ : Ctx sig} {ρ : Ren (signature sig noUnknowns) Γ Δ}
    (keeps : KeepsPositions ρ) : ∀ bs : List Srt, KeepsPositions (liftRen ρ bs)
  | [], s, v => keeps s v
  | _ :: _, _, .zero => rfl
  | _ :: bs, s, .succ w => by
      show position (liftRen ρ bs s w) + 1 = position w + 1
      rw [keepsPositions_liftRen keeps bs s w]

/-- Every renaming of the empty context keeps positions. -/
theorem keepsPositions_empty {Δ : Ctx sig} (ρ : Ren (signature sig noUnknowns) [] Δ) :
    KeepsPositions ρ := fun _ v => nomatch v

mutual
  /-- **Read-back is invariant under renamings that keep positions.** -/
  theorem read_rename : ∀ {Γ Δ : Ctx sig} {s : Srt} (t : G Γ s)
      (ρ : Ren (signature sig noUnknowns) Γ Δ), KeepsPositions ρ → read (rename ρ t) = read t
    | _, _, s, .var v, ρ, keeps => by
        show readVar s (position (ρ s v)) = readVar s (position v)
        rw [keeps s v]
    | _, _, _, .op o args, ρ, keeps => by
        show build o (readArgs (renameArgs ρ args)) = build o (readArgs args)
        rw [readArgs_rename args ρ keeps]

  theorem readArgs_rename : ∀ {as : List (List Srt × Srt)} {Γ Δ : Ctx sig}
      (args : Args (signature sig noUnknowns) as Γ) (ρ : Ren (signature sig noUnknowns) Γ Δ),
      KeepsPositions ρ → readArgs (renameArgs ρ args) = readArgs args
    | _, _, _, .nil, _, _ => rfl
    | _, _, _, .cons (bs := bs) head tail, ρ, keeps => by
        show read (rename (liftRen ρ bs) head) :: readArgs (renameArgs ρ tail) =
          read head :: readArgs tail
        rw [read_rename head (liftRen ρ bs) (keepsPositions_liftRen keeps bs),
          readArgs_rename tail ρ keeps]
end

/-- A closed term reads back the same after any renaming. -/
theorem read_rename_closed {Δ : Ctx sig} {s : Srt} (t : G [] s)
    (ρ : Ren (signature sig noUnknowns) [] Δ) : read (rename ρ t) = read t :=
  read_rename t ρ (keepsPositions_empty ρ)

/-! ## Substitution, former by former -/

section Unfold

variable {Γ Δ : Ctx sig} (σ : Sub (signature sig noUnknowns) Γ Δ)

theorem bind_zero : bind σ (zeroT (D := noUnknowns) (Γ := Γ)) = zeroT := rfl
theorem bind_bag (l : G Γ .ps) : bind σ (bagT l) = bagT (bind σ l) := rfl
theorem bind_pnil : bind σ (pnilT (D := noUnknowns) (Γ := Γ)) = pnilT := rfl
theorem bind_pcons (p : G Γ .pr) (l : G Γ .ps) :
    bind σ (pconsT p l) = pconsT (bind σ p) (bind σ l) := rfl
theorem bind_input (c : G Γ .nm) (b : G (.nm :: .pr :: Γ) .pr) :
    bind σ (inputT c b) = inputT (bind σ c) (bind (liftSub σ [.nm, .pr]) b) := rfl
theorem bind_output (c : G Γ .nm) (p : G Γ .pr) :
    bind σ (outputT c p) = outputT (bind σ c) (bind σ p) := rfl
theorem bind_dropq (p : G Γ .pr) : bind σ (dropqT p) = dropqT (bind σ p) := rfl
theorem bind_quote (p : G Γ .pr) : bind σ (quoteT p) = quoteT (bind σ p) := rfl

end Unfold

/-! ## Substitutions that keep the inner pairs -/

/-- `σ` keeps every variable of the first `j` pairs at its position. -/
def Fixes (j : Nat) {Γ Δ : Ctx sig} (σ : Sub (signature sig noUnknowns) Γ Δ) : Prop :=
  ∀ (s : Srt) (v : Var Γ s), half (position v) < j →
    ∃ w : Var Δ s, σ s v = .var w ∧ position w = position v

theorem fixes_zero {Γ Δ : Ctx sig} (σ : Sub (signature sig noUnknowns) Γ Δ) : Fixes 0 σ :=
  fun _ _ small => absurd small (Nat.not_lt_zero _)

theorem fixes_liftSub {j : Nat} {Γ Δ : Ctx sig} {σ : Sub (signature sig noUnknowns) Γ Δ}
    (fixes : Fixes j σ) : Fixes (j + 1) (liftSub σ [.nm, .pr]) := by
  intro s v small
  match v with
  | .zero => exact ⟨.zero, rfl, rfl⟩
  | .succ .zero => exact ⟨.succ .zero, rfl, rfl⟩
  | .succ (.succ w) =>
      have inner : half (position w) < j := by
        have : half (position w) + 1 < j + 1 := small
        omega
      obtain ⟨w', same, at'⟩ := fixes s w inner
      refine ⟨.succ (.succ w'), ?_, ?_⟩
      · show weaken (weaken (σ s w)) = _
        rw [same]
        rfl
      · show position w' + 1 + 1 = position w + 1 + 1
        rw [at']

/-! ## Read-back facts -/

/-- What a read-back is at a sort: a well-sorted name, process, or bag of processes. -/
def SortedAt (m : Nat) : Srt → Pattern → Prop
  | .nm, n => NameWellSorted rhoReflectivePresentation FreeSortContext.empty
      (List.replicate m rhoReflectivePresentation.nameSort) n
  | .pr, p => ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (List.replicate m rhoReflectivePresentation.nameSort) p
  | .ps, p => ∃ elements, p = .collection .hashBag elements none ∧
      ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty
        (List.replicate m rhoReflectivePresentation.nameSort) elements

theorem lookup_name {m i : Nat} (small : i < m) :
    (List.replicate m rhoReflectivePresentation.nameSort)[i]? =
      some rhoReflectivePresentation.nameSort := by
  simp [small]

/-- **Read-backs are well sorted**, in a context of pairs. -/
theorem read_sorted : ∀ {Γ : Ctx sig} {s : Srt} (t : G Γ s) (m : Nat), Γ = pairs m →
    SortedAt m s (read t)
  | _, s, .var v, m, shape => by
      subst shape
      obtain ⟨small, notList⟩ := var_pairs m v
      cases s with
      | nm => exact .bvar (lookup_name small)
      | pr => exact .drop (.bvar (lookup_name small))
      | ps => exact absurd rfl notList
  | _, _, .op (.inl .zero) .nil, _, _ => .unit
  | _, _, .op (.inl .bag) (.cons l .nil), m, shape => by
      obtain ⟨elements, same, typed⟩ := (read_sorted l m shape : SortedAt m .ps (read l))
      show ProcWellSorted _ _ _ (read l)
      rw [same]
      exact .parallel typed
  | _, _, .op (.inl .pnil) .nil, _, _ => ⟨[], rfl, .nil⟩
  | _, _, .op (.inl .pcons) (.cons p (.cons l .nil)), m, shape => by
      have head : SortedAt m .pr (read p) := read_sorted p m shape
      obtain ⟨elements, same, typed⟩ := (read_sorted l m shape : SortedAt m .ps (read l))
      refine ⟨read p :: elements, ?_, .cons head typed⟩
      show consBag (read p) (read l) = _
      rw [same]
      rfl
  | _, _, .op (.inl .input) (.cons c (.cons b .nil)), m, shape => by
      have channel : SortedAt m .nm (read c) := read_sorted c m shape
      have body : SortedAt (m + 1) .pr (read b) := read_sorted b (m + 1) (by rw [shape]; rfl)
      exact .input channel body
  | _, _, .op (.inl .output) (.cons c (.cons p .nil)), m, shape => by
      have channel : SortedAt m .nm (read c) := read_sorted c m shape
      have payload : SortedAt m .pr (read p) := read_sorted p m shape
      exact .output channel payload
  | _, _, .op (.inl .dropq) (.cons p .nil), m, shape => by
      have inner : SortedAt m .pr (read p) := read_sorted p m shape
      exact .drop (.quote inner)
  | _, _, .op (.inl .quote) (.cons p .nil), m, shape => by
      have inner : SortedAt m .pr (read p) := read_sorted p m shape
      exact .quote inner
  | _, _, .op (.inr o) _, _, _ => o.key.elim

/-- **Read-backs contain no hash set.** -/
theorem read_hashSetFree : ∀ {Γ : Ctx sig} {s : Srt} (t : G Γ s), HashSetFree (read t)
  | _, .nm, .var _ => trivial
  | _, .pr, .var _ => ⟨trivial, trivial⟩
  | _, .ps, .var _ => trivial
  | _, _, .op (.inl .zero) .nil => trivial
  | _, _, .op (.inl .bag) (.cons l .nil) => read_hashSetFree l
  | _, _, .op (.inl .pnil) .nil => trivial
  | _, _, .op (.inl .pcons) (.cons p (.cons l .nil)) => by
      obtain ⟨elements, same⟩ := read_ps_ground l
      have tail := read_hashSetFree l
      rw [same] at tail
      show HashSetFree (consBag (read p) (read l))
      rw [same]
      exact ⟨read_hashSetFree p, tail⟩
  | _, _, .op (.inl .input) (.cons c (.cons b .nil)) =>
      ⟨read_hashSetFree c, read_hashSetFree b, trivial⟩
  | _, _, .op (.inl .output) (.cons c (.cons p .nil)) =>
      ⟨read_hashSetFree c, read_hashSetFree p, trivial⟩
  | _, _, .op (.inl .dropq) (.cons p .nil) => ⟨⟨read_hashSetFree p, trivial⟩, trivial⟩
  | _, _, .op (.inl .quote) (.cons p .nil) => ⟨read_hashSetFree p, trivial⟩
  | _, _, .op (.inr o) _ => o.key.elim

/-! ## Closed code is fixed -/

/-- **A substitution that keeps the free pairs of a term does not change its read-back.** -/
theorem read_bind_fixed : ∀ {Γ Δ : Ctx sig} {s : Srt} (t : G Γ s) (m j : Nat)
    (σ : Sub (signature sig noUnknowns) Γ Δ), Γ = pairs m → Fixes j σ →
    binderSafeAt "NQuote" j (read t) = true → read (bind σ t) = read t
  | _, _, s, .var v, m, j, σ, shape, fixes, safe => by
      subst shape
      obtain ⟨_, notList⟩ := var_pairs m v
      have small : half (position v) < j := by
        cases s with
        | nm => simpa [read, readVar, binderSafeAt] using safe
        | pr => simpa [read, readVar, binderSafeAt, binderSafeListAt] using safe
        | ps => exact absurd rfl notList
      obtain ⟨w, same, at'⟩ := fixes s v small
      show read (σ s v) = readVar s (position v)
      rw [same]
      show readVar s (position w) = _
      rw [at']
  | _, _, _, .op (.inl .zero) .nil, _, _, _, _, _, _ => rfl
  | _, _, _, .op (.inl .bag) (.cons l .nil), m, j, σ, shape, fixes, safe => by
      show read (bind σ l) = read l
      exact read_bind_fixed l m j σ shape fixes safe
  | _, _, _, .op (.inl .pnil) .nil, _, _, _, _, _, _ => rfl
  | _, _, _, .op (.inl .pcons) (.cons p (.cons l .nil)), m, j, σ, shape, fixes, safe => by
      obtain ⟨elements, same⟩ := read_ps_ground l
      have both : binderSafeAt "NQuote" j (read p) = true ∧
          binderSafeListAt "NQuote" j elements = true := by
        have unfolded : binderSafeAt "NQuote" j (consBag (read p) (read l)) = true := safe
        rw [same] at unfolded
        simpa [consBag, bagElements, binderSafeAt, binderSafeListAt] using unfolded
      have tailSafe : binderSafeAt "NQuote" j (read l) = true := by
        rw [same]
        simpa [binderSafeAt] using both.2
      show consBag (read (bind σ p)) (read (bind σ l)) = consBag (read p) (read l)
      rw [read_bind_fixed p m j σ shape fixes both.1, read_bind_fixed l m j σ shape fixes tailSafe]
  | _, _, _, .op (.inl .input) (.cons c (.cons b .nil)), m, j, σ, shape, fixes, safe => by
      have both : binderSafeAt "NQuote" j (read c) = true ∧
          binderSafeAt "NQuote" (j + 1) (read b) = true := by
        have unfolded : binderSafeAt "NQuote" j
            (.apply "PInput" [read c, .lambda none (read b)]) = true := safe
        simpa [binderSafeAt, binderSafeListAt] using unfolded
      show Pattern.apply "PInput" [read (bind σ c),
          .lambda none (read (bind (liftSub σ [.nm, .pr]) b))] =
        .apply "PInput" [read c, .lambda none (read b)]
      rw [read_bind_fixed c m j σ shape fixes both.1,
        read_bind_fixed b (m + 1) (j + 1) (liftSub σ [.nm, .pr]) (by rw [shape]; rfl)
          (fixes_liftSub fixes) both.2]
  | _, _, _, .op (.inl .output) (.cons c (.cons p .nil)), m, j, σ, shape, fixes, safe => by
      have both : binderSafeAt "NQuote" j (read c) = true ∧
          binderSafeAt "NQuote" j (read p) = true := by
        have unfolded : binderSafeAt "NQuote" j (.apply "POutput" [read c, read p]) = true := safe
        simpa [binderSafeAt, binderSafeListAt] using unfolded
      show Pattern.apply "POutput" [read (bind σ c), read (bind σ p)] =
        .apply "POutput" [read c, read p]
      rw [read_bind_fixed c m j σ shape fixes both.1, read_bind_fixed p m j σ shape fixes both.2]
  | _, _, _, .op (.inl .dropq) (.cons p .nil), m, j, σ, shape, _, safe => by
      have inner : binderSafeAt "NQuote" 0 (read p) = true := by
        have unfolded : binderSafeAt "NQuote" j
            (.apply "PDrop" [.apply "NQuote" [read p]]) = true := safe
        simpa [binderSafeAt, binderSafeListAt] using unfolded
      show Pattern.apply "PDrop" [.apply "NQuote" [read (bind σ p)]] =
        .apply "PDrop" [.apply "NQuote" [read p]]
      rw [read_bind_fixed p m 0 σ shape (fixes_zero σ) inner]
  | _, _, _, .op (.inl .quote) (.cons p .nil), m, j, σ, shape, _, safe => by
      have inner : binderSafeAt "NQuote" 0 (read p) = true := by
        have unfolded : binderSafeAt "NQuote" j (.apply "NQuote" [read p]) = true := safe
        simpa [binderSafeAt] using unfolded
      show Pattern.apply "NQuote" [read (bind σ p)] = .apply "NQuote" [read p]
      rw [read_bind_fixed p m 0 σ shape (fixes_zero σ) inner]
  | _, _, _, .op (.inr o) _, _, _, _, _, _, _ => o.key.elim

/-! ## The substitution of the received pair -/

/-- What the substitution puts at the received pair: the received name and the received
process. -/
def value (q : G [] .pr) : (s : Srt) → G [] s
  | .nm => quoteT q
  | .pr => q
  | .ps => pnilT

/-- **`σ` substitutes the `k`-th pair**: it keeps the inner pairs at their positions and puts the
received name and process, weakened, at the `k`-th pair. -/
structure Shifts (q : G [] .pr) (k : Nat) {Γ Δ : Ctx sig}
    (σ : Sub (signature sig noUnknowns) Γ Δ) : Prop where
  inner : Fixes k σ
  received : ∀ (s : Srt) (v : Var Γ s), half (position v) = k →
    ∃ ρ : Ren (signature sig noUnknowns) [] Δ, σ s v = rename ρ (value q s)

theorem shifts_liftSub {q : G [] .pr} {k : Nat} {Γ Δ : Ctx sig}
    {σ : Sub (signature sig noUnknowns) Γ Δ} (shifts : Shifts q k σ) :
    Shifts q (k + 1) (liftSub σ [.nm, .pr]) := by
  refine ⟨fixes_liftSub shifts.inner, ?_⟩
  intro s v at'
  match v with
  | .zero => exact absurd at' (by simp [position, half])
  | .succ .zero => exact absurd at' (by simp [position, half])
  | .succ (.succ w) =>
      have outer : half (position w) = k := by
        have : half (position w) + 1 = k + 1 := at'
        omega
      obtain ⟨ρ, same⟩ := shifts.received s w outer
      refine ⟨fun s' u => .succ (.succ (ρ s' u)), ?_⟩
      show weaken (weaken (σ s w)) = _
      rw [same]
      simp only [weaken, rename_comp]

/-- The semantic substitution of the received name `@Q` at the `k`-th bound name, by sort. -/
def substAt (Q : Pattern) : Srt → Nat → Pattern → Pattern
  | .nm, k, n => semanticSubstName k (.apply "NQuote" [Q]) n
  | .pr, k, p => semanticSubstProc k (.apply "NQuote" [Q]) p
  | .ps, k, p => semanticSubstProc k (.apply "NQuote" [Q]) p

/-- A quoted read-back of a sealed process is a name whose semantic normal form is no bound
variable. -/
theorem quote_not_bvar {m : Nat} {p : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (List.replicate m rhoReflectivePresentation.nameSort) p)
    (safe : binderSafeAt "NQuote" 0 p = true) (index : Nat) :
    semanticNormalizeName (.apply "NQuote" [p]) ≠ .bvar index :=
  SubstitutionCanonicalCommutation.semanticNormalizeName_ne_bvar_of_nameWellSorted (.quote typed)
    (depth := 0) (by simpa [binderSafeAt, rhoReflectivePresentation] using safe)
    (fun _ same => by cases same) index

/-- A drop whose name the substitution does not match stays a drop of the normalized name. -/
theorem substProc_drop_unmatched {k : Nat} {r name normal : Pattern}
    (mark : semanticSubstNameMark k r name = (normal, false)) :
    semanticSubstProc k r (.apply "PDrop" [name]) = .apply "PDrop" [normal] := by
  simp only [semanticSubstProc, mark]

theorem substName_quote {m k : Nat} {p : Pattern} (Q : Pattern)
    (typed : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (List.replicate m rhoReflectivePresentation.nameSort) p)
    (safe : binderSafeAt "NQuote" 0 p = true) :
    semanticSubstNameMark k (.apply "NQuote" [Q]) (.apply "NQuote" [p]) =
      (semanticNormalizeName (.apply "NQuote" [p]), false) := by
  have miss : canonicalize (.apply "NQuote" [p]) ≠ .bvar k :=
    SubstitutionCanonicalCommutation.canonicalize_ne_bvar_of_nameWellSorted (.quote typed)
      (depth := 0) (by simpa [binderSafeAt, rhoReflectivePresentation] using safe)
      (fun _ same => by cases same) k
  rw [semanticSubstNameMark, if_neg miss]

/-- **Instantiation is the calculus's substitution, up to its equations.** For every sealed term
in a context of pairs and every substitution of the `k`-th pair, the read-back of the
instantiation is structurally congruent to the semantic substitution of the read-back, and it is
sealed one binder less deep. -/
theorem contract (q : G [] .pr) (closedQ : binderSafeAt "NQuote" 0 (read q) = true) :
    ∀ {Γ Δ : Ctx sig} {s : Srt} (t : G Γ s) (k : Nat) (σ : Sub (signature sig noUnknowns) Γ Δ),
      Γ = pairs (k + 1) → Shifts q k σ → binderSafeAt "NQuote" (k + 1) (read t) = true →
      StructuralCongruence (read (bind σ t)) (substAt (read q) s k (read t)) ∧
        binderSafeAt "NQuote" k (read (bind σ t)) = true
  | _, _, s, .var v, k, σ, shape, shifts, safe => by
      subst shape
      obtain ⟨_, notList⟩ := var_pairs (k + 1) v
      have small : half (position v) < k + 1 := by
        cases s with
        | nm => simpa [read, readVar, binderSafeAt] using safe
        | pr => simpa [read, readVar, binderSafeAt, binderSafeListAt] using safe
        | ps => exact absurd rfl notList
      rcases Nat.lt_or_ge (half (position v)) k with inner | outer
      · obtain ⟨w, same, at'⟩ := shifts.inner s v inner
        have readSame : read (bind σ (.var v)) = readVar s (position v) := by
          show read (σ s v) = _
          rw [same]
          show readVar s (position w) = _
          rw [at']
        have different : half (position v) ≠ k := Nat.ne_of_lt inner
        rw [readSame]
        cases s with
        | nm =>
            refine ⟨?_, by simpa [readVar, binderSafeAt] using inner⟩
            have fixed : substAt (read q) .nm k (readVar .nm (position v)) =
                readVar .nm (position v) := by
              simp [substAt, readVar, semanticSubstName, semanticSubstNameMark,
                semanticNormalizeName, canonicalize, different]
            show StructuralCongruence _ (substAt (read q) .nm k (readVar .nm (position v)))
            rw [fixed]
            exact StructuralCongruence.refl _
        | pr =>
            refine ⟨?_, by simpa [readVar, binderSafeAt, binderSafeListAt] using inner⟩
            have fixed : substAt (read q) .pr k (readVar .pr (position v)) =
                readVar .pr (position v) := by
              simp [substAt, readVar, semanticSubstProc, semanticSubstNameMark,
                semanticNormalizeName, canonicalize, different]
            show StructuralCongruence _ (substAt (read q) .pr k (readVar .pr (position v)))
            rw [fixed]
            exact StructuralCongruence.refl _
        | ps => exact absurd rfl notList
      · have at' : half (position v) = k := by omega
        obtain ⟨ρ, same⟩ := shifts.received s v at'
        have readSame : read (bind σ (.var v)) = read (value q s) := by
          show read (σ s v) = _
          rw [same, read_rename_closed]
        rw [readSame]
        cases s with
        | nm =>
            refine ⟨?_, ?_⟩
            · have substituted : substAt (read q) .nm k (read (Term.var v)) =
                  .apply "NQuote" [read q] := by
                show semanticSubstName k (.apply "NQuote" [read q]) (readVar .nm (position v)) = _
                simp [readVar, at', semanticSubstName, semanticSubstNameMark, canonicalize]
              rw [substituted]
              exact StructuralCongruence.refl _
            · show binderSafeAt "NQuote" k (.apply "NQuote" [read q]) = true
              simpa [binderSafeAt] using closedQ
        | pr =>
            refine ⟨?_, ?_⟩
            · have substituted : substAt (read q) .pr k (read (Term.var v)) = read q := by
                show semanticSubstProc k (.apply "NQuote" [read q]) (readVar .pr (position v)) = _
                simp [readVar, at', semanticSubstProc, semanticSubstNameMark, canonicalize]
              rw [substituted]
              exact StructuralCongruence.refl _
            · exact binderSafeAt_mono "NQuote" closedQ (Nat.zero_le k)
        | ps => exact absurd rfl notList
  | _, _, _, .op (.inl .zero) .nil, k, σ, _, _, _ => by
      refine ⟨?_, rfl⟩
      show StructuralCongruence (.apply "PZero" [])
        (semanticSubstProc k (.apply "NQuote" [read q]) (.apply "PZero" []))
      exact StructuralCongruence.alpha _ _ (by simp [semanticSubstProc])
  | _, _, _, .op (.inl .bag) (.cons l .nil), k, σ, shape, shifts, safe => by
      have inner := contract q closedQ l k σ shape shifts safe
      exact inner
  | _, _, _, .op (.inl .pnil) .nil, k, σ, _, _, _ => by
      refine ⟨?_, rfl⟩
      show StructuralCongruence (.collection .hashBag [] none)
        (semanticSubstProc k (.apply "NQuote" [read q]) (.collection .hashBag [] none))
      simp only [semanticSubstProc, semanticSubstProcList]
      exact StructuralCongruence.refl _
  | _, _, _, .op (.inl .pcons) (.cons p (.cons l .nil)), k, σ, shape, shifts, safe => by
      obtain ⟨elements, same⟩ := read_ps_ground l
      obtain ⟨elements', same'⟩ := read_ps_ground (bind σ l)
      have both : binderSafeAt "NQuote" (k + 1) (read p) = true ∧
          binderSafeListAt "NQuote" (k + 1) elements = true := by
        have unfolded : binderSafeAt "NQuote" (k + 1) (consBag (read p) (read l)) = true := safe
        rw [same] at unfolded
        simpa [consBag, bagElements, binderSafeAt, binderSafeListAt] using unfolded
      have tailSafe : binderSafeAt "NQuote" (k + 1) (read l) = true := by
        rw [same]
        simpa [binderSafeAt] using both.2
      obtain ⟨headSC, headSafe⟩ := contract q closedQ p k σ shape shifts both.1
      obtain ⟨tailSC, tailSafe'⟩ := contract q closedQ l k σ shape shifts tailSafe
      rw [same, same'] at tailSC
      rw [same'] at tailSafe'
      have tailSC' : StructuralCongruence (.collection .hashBag elements' none)
          (.collection .hashBag (semanticSubstProcList k (.apply "NQuote" [read q]) elements) none) := by
        simpa [substAt, semanticSubstProc] using tailSC
      refine ⟨?_, ?_⟩
      · show StructuralCongruence (consBag (read (bind σ p)) (read (bind σ l)))
          (semanticSubstProc k (.apply "NQuote" [read q]) (consBag (read p) (read l)))
        rw [same, same']
        show StructuralCongruence (.collection .hashBag (read (bind σ p) :: elements') none)
          (semanticSubstProc k (.apply "NQuote" [read q]) (.collection .hashBag (read p :: elements) none))
        simp only [semanticSubstProc, semanticSubstProcList]
        exact sc_cons headSC tailSC'
      · show binderSafeAt "NQuote" k (consBag (read (bind σ p)) (read (bind σ l))) = true
        rw [same']
        have tailList : binderSafeListAt "NQuote" k elements' = true := by
          simpa [binderSafeAt] using tailSafe'
        simp [consBag, bagElements, binderSafeAt, binderSafeListAt, headSafe, tailList]
  | _, _, _, .op (.inl .input) (.cons c (.cons b .nil)), k, σ, shape, shifts, safe => by
      have both : binderSafeAt "NQuote" (k + 1) (read c) = true ∧
          binderSafeAt "NQuote" (k + 1 + 1) (read b) = true := by
        have unfolded : binderSafeAt "NQuote" (k + 1)
            (.apply "PInput" [read c, .lambda none (read b)]) = true := safe
        simpa [binderSafeAt, binderSafeListAt] using unfolded
      obtain ⟨channelSC, channelSafe⟩ := contract q closedQ c k σ shape shifts both.1
      obtain ⟨bodySC, bodySafe⟩ := contract q closedQ b (k + 1) (liftSub σ [.nm, .pr])
        (by rw [shape]; rfl) (shifts_liftSub shifts) both.2
      refine ⟨?_, ?_⟩
      · show StructuralCongruence
          (.apply "PInput" [read (bind σ c), .lambda none (read (bind (liftSub σ [.nm, .pr]) b))])
          (semanticSubstProc k (.apply "NQuote" [read q]) (.apply "PInput" [read c, .lambda none (read b)]))
        simp only [semanticSubstProc]
        exact sc_apply_two _ channelSC (StructuralCongruence.lambda_cong _ _ _ bodySC)
      · show binderSafeAt "NQuote" k
          (.apply "PInput" [read (bind σ c), .lambda none (read (bind (liftSub σ [.nm, .pr]) b))]) =
            true
        simp [binderSafeAt, binderSafeListAt, channelSafe, bodySafe]
  | _, _, _, .op (.inl .output) (.cons c (.cons p .nil)), k, σ, shape, shifts, safe => by
      have both : binderSafeAt "NQuote" (k + 1) (read c) = true ∧
          binderSafeAt "NQuote" (k + 1) (read p) = true := by
        have unfolded : binderSafeAt "NQuote" (k + 1) (.apply "POutput" [read c, read p]) = true :=
          safe
        simpa [binderSafeAt, binderSafeListAt] using unfolded
      obtain ⟨channelSC, channelSafe⟩ := contract q closedQ c k σ shape shifts both.1
      obtain ⟨payloadSC, payloadSafe⟩ := contract q closedQ p k σ shape shifts both.2
      refine ⟨?_, ?_⟩
      · show StructuralCongruence (.apply "POutput" [read (bind σ c), read (bind σ p)])
          (semanticSubstProc k (.apply "NQuote" [read q]) (.apply "POutput" [read c, read p]))
        simp only [semanticSubstProc]
        exact sc_apply_two _ channelSC payloadSC
      · show binderSafeAt "NQuote" k (.apply "POutput" [read (bind σ c), read (bind σ p)]) = true
        simp [binderSafeAt, binderSafeListAt, channelSafe, payloadSafe]
  | _, _, _, .op (.inl .dropq) (.cons p .nil), k, σ, shape, shifts, safe => by
      have inner : binderSafeAt "NQuote" 0 (read p) = true := by
        have unfolded : binderSafeAt "NQuote" (k + 1)
            (.apply "PDrop" [.apply "NQuote" [read p]]) = true := safe
        simpa [binderSafeAt, binderSafeListAt] using unfolded
      have fixed : read (bind σ p) = read p :=
        read_bind_fixed p (k + 1) 0 σ shape (fixes_zero σ) inner
      have typed : SortedAt (k + 1) .pr (read p) := read_sorted p (k + 1) shape
      refine ⟨?_, ?_⟩
      · show StructuralCongruence (.apply "PDrop" [.apply "NQuote" [read (bind σ p)]])
          (semanticSubstProc k (.apply "NQuote" [read q]) (.apply "PDrop" [.apply "NQuote" [read p]]))
        rw [fixed, substProc_drop_unmatched (substName_quote (read q) typed inner)]
        exact sc_apply_one _ (StructuralCongruence.symm _ _ semanticNormalizeName_sound_struct)
      · show binderSafeAt "NQuote" k (.apply "PDrop" [.apply "NQuote" [read (bind σ p)]]) = true
        rw [fixed]
        simpa [binderSafeAt, binderSafeListAt] using inner
  | _, _, _, .op (.inl .quote) (.cons p .nil), k, σ, shape, shifts, safe => by
      have inner : binderSafeAt "NQuote" 0 (read p) = true := by
        have unfolded : binderSafeAt "NQuote" (k + 1) (.apply "NQuote" [read p]) = true := safe
        simpa [binderSafeAt] using unfolded
      have fixed : read (bind σ p) = read p :=
        read_bind_fixed p (k + 1) 0 σ shape (fixes_zero σ) inner
      have typed : SortedAt (k + 1) .pr (read p) := read_sorted p (k + 1) shape
      refine ⟨?_, ?_⟩
      · show StructuralCongruence (.apply "NQuote" [read (bind σ p)])
          (semanticSubstName k (.apply "NQuote" [read q]) (.apply "NQuote" [read p]))
        rw [fixed]
        unfold semanticSubstName
        rw [substName_quote (read q) typed inner]
        exact StructuralCongruence.symm _ _ semanticNormalizeName_sound_struct
      · show binderSafeAt "NQuote" k (.apply "NQuote" [read (bind σ p)]) = true
        rw [fixed]
        simpa [binderSafeAt] using inner
  | _, _, _, .op (.inr o) _, _, _, _, _, _ => o.key.elim

/-! ## The made row of communication -/

/-- **The substitution the made row is instantiated with**: the received name `@q` for the bound
name, the received process `q` for its twin. -/
abbrev received (q : G [] .pr) : Sub (signature sig noUnknowns) [.nm, .pr] [] :=
  argsToSub (.cons (quoteT q) (.cons q .nil))

theorem shifts_received (q : G [] .pr) : Shifts q 0 (received q) := by
  refine ⟨fixes_zero _, ?_⟩
  intro s v _
  match v with
  | .zero => exact ⟨fun _ v => v, (rename_id _).symm⟩
  | .succ .zero => exact ⟨fun _ v => v, (rename_id _).symm⟩

/-- **The instantiated continuation is the semantic substitution, up to the equations, and it is
sealed.** -/
theorem instantiation_sealed (b : G [.nm, .pr] .pr) (q : G [] .pr)
    (safeB : binderSafeAt "NQuote" 1 (read b) = true)
    (safeQ : binderSafeAt "NQuote" 0 (read q) = true) :
    StructuralCongruence (read (bind (received q) b))
        (semanticSubstProc 0 (.apply "NQuote" [read q]) (read b)) ∧
      binderSafeAt "NQuote" 0 (read (bind (received q) b)) = true :=
  contract q safeQ b 0 (received q) rfl (shifts_received q) safeB

/-- **The contractum by instantiation.** For every sealed continuation and sealed payload, the
continuation instantiated at the received name and process, read back, has the canonical form of
the calculus's communication contractum. -/
theorem contractum_by_instantiation (b : G [.nm, .pr] .pr) (q : G [] .pr)
    (safeB : binderSafeAt "NQuote" 1 (read b) = true)
    (safeQ : binderSafeAt "NQuote" 0 (read q) = true) :
    canonicalize (read (bind (received q) b)) =
      canonicalize (semanticCommSubst (read b) (read q)) := by
  obtain ⟨congruent, _⟩ := instantiation_sealed b q safeB safeQ
  have freeMade := read_hashSetFree (bind (received q) b)
  have freeSubst := (Canonical.hashSetFree_iff_of_structuralCongruence congruent).mp freeMade
  have bodyTyped : SortedAt 1 .pr (read b) := read_sorted b 1 rfl
  have payloadEq : canonicalize (read q) = canonicalize (semanticNormalizeProc (read q)) :=
    (SubstitutionCanonicalCommutation.canonicalize_semanticNormalizeProc (read_hashSetFree q)).symm
  rw [Canonical.canonicalize_eq_of_structuralCongruence congruent freeMade freeSubst,
    SubstitutionCanonicalCommutation.canonicalize_semanticSubstProc_payload bodyTyped payloadEq 0]
  rfl

/-- **Canonical forms of the parts suffice**: the contractum by instantiation is the canonical
contractum of the canonical forms of continuation and payload. -/
theorem contractum_by_instantiation_canonical (b : G [.nm, .pr] .pr) (q : G [] .pr)
    (safeB : binderSafeAt "NQuote" 1 (read b) = true)
    (safeQ : binderSafeAt "NQuote" 0 (read q) = true) :
    canonicalize (read (bind (received q) b)) =
      canonicalize (semanticCommSubst (canonicalize (read b)) (canonicalize (read q))) := by
  rw [contractum_by_instantiation b q safeB safeQ]
  exact (SubstitutionCanonicalCommutation.canonicalize_semanticCommSubst_canonicalize
    (read_sorted b 1 rfl) (read_hashSetFree q)).symm

#print axioms read_rename
#print axioms read_sorted
#print axioms read_bind_fixed
#print axioms contract
#print axioms contractum_by_instantiation
#print axioms contractum_by_instantiation_canonical

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
