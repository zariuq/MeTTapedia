import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFolds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Constructors
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedVersions

/-!
# One certificate, three uses: skip, select and shape

A value's certificate at a closed sort is a derivation in the declared
constructor signature. Its inversion (a derivation of a term at the sort is a
constructor of the sort applied to derived children, Lambek's lemma for the
signature's initial algebra) has three readings:

* **Skip.** The children are certified, so the checks of the calls a
  structural recursion makes on them hold already. Exactness in multiplicity
  needs more than existence: a typed recursion's answers on a spine are its
  native fold's answers scaled by the product of the guard counts of the
  suffixes (`guarded_build`), so dropping the guards is exact exactly when
  every suffix's count is one (`skip_iff`). A certificate that gives one
  derivation (`walk_count`) discharges them all (`certified_fold`); two
  derivations per cell double the answers at every cell
  (`Controls.two_rows_double`).
* **Select.** The head of a certified term is one of the sort's constructors,
  so equation search on it is the search over the equations keyed by that
  head (`keyed_dispatch`, which holds for any term) and, when the keyed
  equations cover every constructor with linear patterns, some equation
  matches (`exhaustive_matched`): the "no equation matched" path is
  unreachable on certified arguments. Without a certificate the path is live
  (`Controls.uncertified_unmatched`); without a covering equation it is live
  on a certified term (`Controls.missing_case_unmatched`); a non-linear
  pattern does not cover its constructor (`Controls.nonlinear_does_not_cover`).
* **Shape.** Iterating the inversion along a recursive position gives the
  maximal spine: it ends in the sort's stop and carries certified elements
  (`TypedCertificates.spine_of_sort`). A typed fold over a certified list is
  the native fold of its elements over the stop's known answers, with no
  shape test per cell, no guard per call and no call at the end
  (`certified_fold`).

**The closed list sort** (`listDecls`: `(: Nil (List $a))` and
`(: Cons (-> $a (List $a) (List $a)))`, numbers typed by their class): a term
walks at `(List τ)` exactly when it is `Nil` or a `Cons` of a term walked at
`τ` and a term walked at `(List τ)` (`walk_list_inversion`), and a term walked
at `Number` is an integer (`walk_number_inversion`). With `walk_count`, a typed
recursion over any certified list answers the native fold of its elements
over the answers at `Nil` (`list_certified_fold`), the elements are integers
at `(List Number)` (`list_number_elements`), and the equations `(f Nil)` and
`(f (Cons $x $xs))` are matched at every certified list (`list_exhaustive`,
`Controls.lsum_matched`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ClosedSortEvidence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Presentations (Family Spine)
open StructureByProof
open TypedCertificates

universe u v w x

/-! ## Skip: guards along a spine -/

section Skip

variable {T : Type u} {F : Type v} (P : Family T F) {β : Type w} {ε : Type x}

/-- The product of the guard counts of the cells of a spine. -/
def guardProduct (g : T → ℕ) : List F → T → ℕ
  | [], _ => 1
  | f :: fs, e => g (P.build ⟨f :: fs, e⟩) * guardProduct g fs e

theorem guardProduct_eq_one_iff (g : T → ℕ) (fs : List F) (e : T) :
    guardProduct P g fs e = 1 ↔ ∀ i < fs.length, g (P.build ⟨fs.drop i, e⟩) = 1 := by
  induction fs with
  | nil => simp [guardProduct]
  | cons f fs ih =>
      rw [guardProduct, mul_eq_one, ih]
      constructor
      · rintro ⟨head, tail⟩ i lt
        cases i with
        | zero => simpa using head
        | succ i => simpa using tail i (by simp at lt; omega)
      · intro all
        exact ⟨by simpa using all 0 (by simp), fun i lt => by simpa using all (i + 1) (by simp; omega)⟩

/-- A typed structural recursion: on a cell, the answers on the rest, stepped by
the cell's field, once for each derivation of the guard on the cell. -/
structure GuardedRecursion (g : T → ℕ) (answers : T → Multiset (β × ε)) where
  step : F → ε → β → β
  cell_answers : ∀ f r, answers (P.cell f r) =
    g (P.cell f r) • (answers r).map fun p => (step f p.2 p.1, p.2)

namespace GuardedRecursion

variable {P} {g : T → ℕ} {answers : T → Multiset (β × ε)} (G : GuardedRecursion P g answers)

/-- The fold of a list of fields, for one answer's bindings. -/
def foldFields (fs : List F) (p : β × ε) : β × ε :=
  (fs.foldr (fun f b => G.step f p.2 b) p.1, p.2)

/-- **The typed recursion is the native fold scaled by the guards.** -/
theorem guarded_build (fs : List F) (e : T) :
    answers (P.build ⟨fs, e⟩) = guardProduct P g fs e • (answers e).map (G.foldFields fs) := by
  induction fs with
  | nil =>
      simp only [Family.build_nil, guardProduct, one_nsmul]
      conv_lhs => rw [← Multiset.map_id (answers e)]
      rfl
  | cons f fs ih =>
      rw [Family.build_cons, G.cell_answers, ih, Multiset.map_nsmul, Multiset.map_map,
        ← mul_nsmul', guardProduct, Family.build_cons]
      rfl

/-- Guards that count one on every cell drop out. -/
theorem skip_of_guards (fs : List F) (e : T)
    (one : ∀ i < fs.length, g (P.build ⟨fs.drop i, e⟩) = 1) :
    answers (P.build ⟨fs, e⟩) = (answers e).map (G.foldFields fs) := by
  rw [G.guarded_build, (guardProduct_eq_one_iff P g fs e).mpr one, one_nsmul]

/-- **Dropping the guards is exact exactly when every cell's guard counts one.**
The end's answers are assumed to exist; otherwise every count fits. -/
theorem skip_iff (fs : List F) (e : T) (some : answers e ≠ 0) :
    answers (P.build ⟨fs, e⟩) = (answers e).map (G.foldFields fs) ↔
      ∀ i < fs.length, g (P.build ⟨fs.drop i, e⟩) = 1 := by
  rw [G.guarded_build, ← guardProduct_eq_one_iff]
  constructor
  · intro same
    have cards := congrArg Multiset.card same
    rw [Multiset.card_nsmul, Multiset.card_map] at cards
    have pos : 0 < Multiset.card (answers e) := Multiset.card_pos.mpr some
    exact (Nat.mul_eq_right (Nat.pos_iff_ne_zero.mp pos)).mp cards
  · intro one
    rw [one, one_nsmul]

end GuardedRecursion

end Skip

/-! ## Shape: the certified fold -/

section Shape

variable {T : Type u} {F : Type v} (P : Family T F) {β : Type w} {ε : Type x}

/-- **The certified fold.** For a sort whose certificate inverts into a cell
of a certified element and a certified rest, or a stop, and whose guard
counts one on certified terms: a typed recursion's answers on a certified
term are its answers on the spine's stop, folded over the spine's elements;
the stop is a stop of the sort and the elements are certified. -/
theorem certified_fold (HasSort : T → Prop) (HasElem : F → Prop) (Stop : T → Prop)
    (inversion : ∀ t, HasSort t →
      (∃ f r, P.uncell t = some (f, r) ∧ HasElem f ∧ HasSort r) ∨ (P.uncell t = none ∧ Stop t))
    {g : T → ℕ} (unique : ∀ t, HasSort t → g t = 1)
    {answers : T → Multiset (β × ε)} (G : GuardedRecursion P g answers)
    (t : T) (sorted : HasSort t) :
    answers t = (answers (P.spine t).stop).map (G.foldFields (P.spine t).elems) ∧
      Stop (P.spine t).stop ∧ (∀ f ∈ (P.spine t).elems, HasElem f) := by
  obtain ⟨stop, elems⟩ := spine_of_sort P HasSort HasElem Stop inversion t sorted
  refine ⟨?_, stop, elems⟩
  have built : HasSort (P.build ⟨(P.spine t).elems, (P.spine t).stop⟩) := by
    rw [show (⟨(P.spine t).elems, (P.spine t).stop⟩ : Spine T F) = P.spine t from rfl,
      P.build_spine]
    exact sorted
  have guards : ∀ i < (P.spine t).elems.length,
      g (P.build ⟨(P.spine t).elems.drop i, (P.spine t).stop⟩) = 1 := fun i _ =>
    unique _ (sort_suffix P HasSort HasElem Stop inversion _ _ built i)
  have := (G.skip_of_guards (P.spine t).elems (P.spine t).stop guards)
  conv_lhs => rw [← P.build_spine t]
  exact this

end Shape

/-! ## Select: dispatch on a certified head -/

section Select

/-- A constructor application: the symbol itself when it has no fields. -/
def ctorTerm : String → List Atom → Atom
  | c, [] => .symbol c
  | c, a :: args => .expression (.symbol c :: a :: args)

/-- The linear pattern of a constructor: distinct variables for its fields. -/
def ctorPat : String → List String → Pat
  | c, [] => .const (.symbol c)
  | c, x :: xs => .ctor c ((x :: xs).map .var)

theorem matchAll_vars : ∀ (xs : List String) (vs : List Atom), xs.length = vs.length →
    Pat.matchAll (xs.map .var) vs = some (xs.zip vs)
  | [], [], _ => by simp [Pat.matchAll]
  | x :: xs, v :: vs, h => by
      rw [List.map_cons, Pat.matchAll, matchAll_vars xs vs (by simpa using h)]
      simp [Pat.match]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **A linear constructor pattern matches every application of its constructor
of its arity.** -/
theorem match_ctor (c : String) (xs : List String) (args : List Atom)
    (lengths : xs.length = args.length) :
    Pat.match (ctorPat c xs) (ctorTerm c args) = some (xs.zip args) := by
  cases xs with
  | nil =>
      cases args with
      | nil => simp [ctorPat, ctorTerm, Pat.match]
      | cons _ _ => simp at lengths
  | cons x xs =>
      cases args with
      | nil => simp at lengths
      | cons a args =>
          simp only [ctorPat, ctorTerm, Pat.match, if_true]
          exact matchAll_vars (x :: xs) (a :: args) lengths

/-- Whether a pattern can match an application of `c`: a constructor pattern of
another symbol cannot; any other pattern may. -/
def fits (c : String) : Pat → Bool
  | .ctor c' _ => c' == c
  | _ => true

theorem match_none_of_not_fits {c : String} {p : Pat} (no : fits c p = false) (args : List Atom) :
    Pat.match p (ctorTerm c args) = none := by
  cases p with
  | var _ => simp [fits] at no
  | const _ => simp [fits] at no
  | ctor c' ps =>
      have different : c' ≠ c := by simpa [fits] using no
      cases args with
      | nil => simp [ctorTerm, Pat.match]
      | cons a args => simp [ctorTerm, Pat.match, different]

theorem matchAll_none_at : ∀ (ps : List Pat) (vs : List Atom) (i : ℕ) (q : Pat) (v : Atom),
    ps[i]? = some q → vs[i]? = some v → Pat.match q v = none → Pat.matchAll ps vs = none
  | [], _, _, _, _, hq, _, _ => by simp at hq
  | _ :: _, [], _, _, _, _, hv, _ => by simp at hv
  | p :: ps, w :: ws, 0, q, v, hq, hv, none_ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq hv
      subst hq; subst hv
      simp [Pat.matchAll, none_]
  | p :: ps, w :: ws, i + 1, q, v, hq, hv, none_ => by
      simp only [List.getElem?_cons_succ] at hq hv
      have rest := matchAll_none_at ps ws i q v hq hv none_
      simp only [Pat.matchAll, rest]
      cases Pat.match p w <;> rfl

/-- Whether an equation can match a call whose argument at position `i` is an
application of `c`. -/
def fitsAt (i : ℕ) (c : String) (eq : Equation) : Bool :=
  match eq.pats[i]? with
  | some p => fits c p
  | none => true

theorem bind_filter_of_zero {α γ : Type} (keep : α → Bool) (xs : List α) (F : α → Multiset γ)
    (zero : ∀ a, keep a = false → F a = 0) :
    (xs : Multiset α).bind F = ((xs.filter keep : List α) : Multiset α).bind F := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases kept : keep a = true
      · rw [List.filter_cons_of_pos kept, ← Multiset.cons_coe, ← Multiset.cons_coe,
          Multiset.cons_bind, Multiset.cons_bind, ih]
      · have : F a = 0 := zero a (by simpa using kept)
        rw [List.filter_cons_of_neg kept, ← Multiset.cons_coe, Multiset.cons_bind, this, zero_add, ih]

/-- **Keyed dispatch is equation search**, for any arguments: the equations
whose pattern at position `i` is a constructor pattern of another symbol
contribute nothing, multiplicity included. -/
theorem keyed_dispatch (E : Env) (O : Oracle) (eqs : List Equation) (vs : List Atom) (i : ℕ)
    (c : String) (args : List Atom) (at_ : vs[i]? = some (ctorTerm c args)) :
    equationsBody E eqs O vs = equationsBody E (eqs.filter (fitsAt i c)) O vs := by
  unfold equationsBody
  apply bind_filter_of_zero
  intro eq no
  cases hp : eq.pats[i]? with
  | none => simp [fitsAt, hp] at no
  | some p =>
      have pNo : fits c p = false := by simpa [fitsAt, hp] using no
      rw [matchAll_none_at eq.pats vs i p _ hp at_ (match_none_of_not_fits pNo args)]

/-- At least one equation matches. -/
def Matched (eqs : List Equation) (vs : List Atom) : Prop :=
  ∃ eq ∈ eqs, (Pat.matchAll eq.pats vs).isSome

/-- **Exhaustive dispatch**: if every certified value is an application of one
of the sort's constructors at its arity, and for each of them an equation has
its linear pattern, every certified argument is matched. -/
theorem exhaustive_matched (K : List (String × ℕ)) (Certified : Atom → Prop)
    (closed : ∀ v, Certified v → ∃ k ∈ K, ∃ args : List Atom, v = ctorTerm k.1 args ∧ args.length = k.2)
    (eqs : List Equation)
    (covers : ∀ k ∈ K, ∃ eq ∈ eqs, ∃ xs : List String, eq.pats = [ctorPat k.1 xs] ∧ xs.length = k.2)
    (v : Atom) (certified : Certified v) : Matched eqs [v] := by
  obtain ⟨k, member, args, rfl, arity⟩ := closed v certified
  obtain ⟨eq, inEqs, xs, pats, xsArity⟩ := covers k member
  refine ⟨eq, inEqs, ?_⟩
  rw [pats, Pat.matchAll, match_ctor k.1 xs args (by omega)]
  simp [Pat.matchAll]

end Select

/-! ## The closed list sort -/

section ListSort

open Controls

/-- The declarations of a closed list sort: `(: Nil (List $a))` and
`(: Cons (-> $a (List $a) (List $a)))`; numbers are typed by their class. -/
def listDecls : Decls := fun s =>
  if s = "Nil" then [listOf (.var "a")] else if s = "Cons" then [consRow] else []

theorem listDecls_nil : listDecls "Nil" = [listOf (.var "a")] := by simp [listDecls]

theorem listDecls_cons : listDecls "Cons" = [consRow] := by simp [listDecls]

theorem listDecls_other {s : String} (notNil : s ≠ "Nil") (notCons : s ≠ "Cons") :
    listDecls s = [] := by
  simp [listDecls, notNil, notCons]

theorem walk_nil_list (τ : Ty Empty) : Walk listDecls (sym "Nil") (listOf τ) :=
  ⟨listOf (.var "a"), listDecls_nil, by simp [IsArrowTy, listOf], fun _ => τ, by simp [listOf]⟩

/-- A cell walks at `(List τ)` exactly when its element walks at `τ` and its rest
at `(List τ)`. -/
theorem walk_cons_list (x rest : Atom) (τ : Ty Empty) :
    Walk listDecls (app "Cons" [x, rest]) (listOf τ) ↔
      Walk listDecls x τ ∧ Walk listDecls rest (listOf τ) := by
  constructor
  · rintro ⟨Ps, R, hrow, σ, hσ, hargs⟩
    have hrow' : consRow = arrow Ps R := by simpa [listDecls_cons] using hrow
    obtain ⟨rfl, rfl⟩ := arrow_inj hrow'
    have ha : σ "a" = τ := by simpa [listOf] using hσ
    obtain ⟨-, hx, -, hrest, -⟩ := hargs
    refine ⟨by simpa [ha] using hx, ?_⟩
    simpa [listOf, ha] using hrest
  · rintro ⟨hx, hrest⟩
    refine ⟨[.var "a", listOf (.var "a")], listOf (.var "a"), by simp [listDecls_cons, consRow],
      fun _ => τ, by simp [listOf], .inl ⟨"a", rfl, by simp [listOf]⟩, by simpa using hx,
      .inr (.inr rfl), ?_, trivial⟩
    simpa [listOf] using hrest

/-- **The list sort is closed** (Lambek's lemma for its declarations): a term
walks at `(List τ)` exactly when it is `Nil`, or a `Cons` of a term walked at
`τ` and a term walked at `(List τ)`. -/
theorem walk_list_inversion (τ : Ty Empty) (t : Atom) :
    Walk listDecls t (listOf τ) ↔ t = sym "Nil" ∨
      ∃ x r, t = app "Cons" [x, r] ∧ Walk listDecls x τ ∧ Walk listDecls r (listOf τ) := by
  constructor
  · intro walked
    rcases t with s | _ | g | items
    · obtain ⟨D, hD, notArrow, σ, hσ⟩ := walked
      left
      by_cases notNil : s = "Nil"
      · subst notNil; rfl
      exfalso
      by_cases isCons : s = "Cons"
      · subst isCons
        rw [listDecls_cons] at hD
        simp only [List.cons.injEq, and_true] at hD
        subst hD
        exact notArrow (by simp [IsArrowTy, consRow, arrow])
      · rw [listDecls_other notNil isCons] at hD
        simp at hD
    · exact absurd walked (by simp [Walk])
    · obtain ⟨c, -, hc⟩ := walked
      simp [listOf] at hc
    · rcases items with _ | ⟨head, rest⟩
      · exact absurd walked (by simp [Walk])
      · rcases head with H | _ | _ | _
        · rcases rest with _ | ⟨c, cs⟩
          · exact absurd walked (by simp [Walk])
          · obtain ⟨Ps, R, hrow, σ, hR, args⟩ := walked
            right
            by_cases isCons : H = "Cons"
            · subst isCons
              rw [listDecls_cons] at hrow
              simp only [List.cons.injEq, and_true] at hrow
              obtain ⟨rfl, rfl⟩ := arrow_inj hrow.symm
              rcases cs with _ | ⟨r, _ | ⟨_, _⟩⟩
              · simp [WalkArgs] at args
              · exact ⟨c, r, rfl, (walk_cons_list c r τ).mp
                  ⟨_, _, by simp [listDecls_cons], σ, hR, args⟩⟩
              · simp [WalkArgs] at args
            · exfalso
              by_cases isNil : H = "Nil"
              · subst isNil
                rw [listDecls_nil] at hrow
                simp [arrow, listOf] at hrow
              · rw [listDecls_other isNil isCons] at hrow
                simp at hrow
        all_goals exact absurd walked (by simp [Walk])
  · rintro (rfl | ⟨x, r, rfl, hx, hr⟩)
    · exact walk_nil_list τ
    · exact (walk_cons_list x r τ).mpr ⟨hx, hr⟩

/-- **A term walked at `Number` is an integer**: the elements unbox. -/
theorem walk_number_inversion (t : Atom) (walked : Walk listDecls t (.sym "Number")) :
    ∃ n : ℤ, t = .grounded (.int n) := by
  rcases t with s | _ | g | items
  · obtain ⟨D, hD, notArrow, σ, hσ⟩ := walked
    exfalso
    by_cases isNil : s = "Nil"
    · subst isNil
      rw [listDecls_nil] at hD
      simp only [List.cons.injEq, and_true] at hD
      subst hD
      simp [Ty.bind, listOf] at hσ
    by_cases isCons : s = "Cons"
    · subst isCons
      rw [listDecls_cons] at hD
      simp only [List.cons.injEq, and_true] at hD
      subst hD
      exact notArrow (by simp [IsArrowTy, consRow, arrow])
    · rw [listDecls_other isNil isCons] at hD
      simp at hD
  · exact absurd walked (by simp [Walk])
  · obtain ⟨c, hc, he⟩ := walked
    cases g with
    | int n => exact ⟨n, rfl⟩
    | string _ =>
        simp [valueClass] at hc
        subst hc
        simp at he
    | bool _ =>
        simp [valueClass] at hc
        subst hc
        simp at he
    | custom _ _ => simp [valueClass] at hc
  · rcases items with _ | ⟨head, rest⟩
    · exact absurd walked (by simp [Walk])
    · rcases head with H | _ | _ | _
      · rcases rest with _ | ⟨c, cs⟩
        · exact absurd walked (by simp [Walk])
        · obtain ⟨Ps, R, hrow, σ, hR, -⟩ := walked
          exfalso
          by_cases isCons : H = "Cons"
          · subst isCons
            rw [listDecls_cons] at hrow
            simp only [List.cons.injEq, and_true] at hrow
            obtain ⟨-, rfl⟩ := arrow_inj hrow.symm
            simp [Ty.bind, listOf] at hR
          by_cases isNil : H = "Nil"
          · subst isNil
            rw [listDecls_nil] at hrow
            simp [arrow, listOf] at hrow
          · rw [listDecls_other isNil isCons] at hrow
            simp at hrow
      all_goals exact absurd walked (by simp [Walk])

/-- The list family's inversion in the form `spine_of_sort` reads. -/
theorem list_inversion_family (τ : Ty Empty) :
    ∀ t, Walk listDecls t (listOf τ) →
      (∃ f r, (Presentations.binary "Cons").uncell t = some (f, r) ∧ Walk listDecls f τ ∧
          Walk listDecls r (listOf τ)) ∨
        ((Presentations.binary "Cons").uncell t = none ∧ t = sym "Nil") := by
  intro t walked
  rcases (walk_list_inversion τ t).mp walked with rfl | ⟨x, r, rfl, hx, hr⟩
  · right
    exact ⟨rfl, rfl⟩
  · left
    refine ⟨x, r, ?_, hx, hr⟩
    have := (Presentations.binary "Cons").uncell_cell x r
    simpa using this

/-- **The typed fold over a certified list.** A typed structural recursion over
`Cons` whose guard is the type relation's count at `(List τ)` answers, on any
term walked at `(List τ)`, its answers at `Nil` folded over the term's
elements, each walked at `τ`: no guard, no shape test and no call at the
end. -/
theorem list_certified_fold (τ : Ty Empty) {β ε : Type}
    {answers : Atom → Multiset (β × ε)}
    (G : GuardedRecursion (Presentations.binary "Cons")
      (fun t => count (info listDecls t) (listOf τ)) answers)
    (t : Atom) (walked : Walk listDecls t (listOf τ)) :
    answers t = (answers (sym "Nil")).map
        (G.foldFields ((Presentations.binary "Cons").spine t).elems) ∧
      ∀ x ∈ ((Presentations.binary "Cons").spine t).elems, Walk listDecls x τ := by
  obtain ⟨same, stop, elems⟩ := certified_fold (Presentations.binary "Cons")
    (fun t => Walk listDecls t (listOf τ)) (fun x => Walk listDecls x τ) (· = sym "Nil")
    (list_inversion_family τ) (fun _ h => walk_count h) G t walked
  rw [stop] at same
  exact ⟨same, elems⟩

/-- At `(List Number)` the elements are integers. -/
theorem list_number_elements (t : Atom) (walked : Walk listDecls t (listOf (.sym "Number"))) :
    ∀ x ∈ ((Presentations.binary "Cons").spine t).elems, ∃ n : ℤ, x = .grounded (.int n) := by
  obtain ⟨-, elems⟩ := spine_of_sort (Presentations.binary "Cons")
    (fun t => Walk listDecls t (listOf (.sym "Number"))) (fun x => Walk listDecls x (.sym "Number"))
    (· = sym "Nil") (list_inversion_family _) t walked
  exact fun x member => walk_number_inversion x (elems x member)

/-- **Exhaustive dispatch on the list sort.** Equations `(f Nil)` and
`(f (Cons $x $xs))` match every list walked at `(List τ)`. -/
theorem list_exhaustive (τ : Ty Empty) (eqs : List Equation)
    (nilCase : ∃ eq ∈ eqs, eq.pats = [ctorPat "Nil" []])
    (consCase : ∃ eq ∈ eqs, ∃ x xs : String, eq.pats = [ctorPat "Cons" [x, xs]])
    (t : Atom) (walked : Walk listDecls t (listOf τ)) : Matched eqs [t] := by
  apply exhaustive_matched [("Nil", 0), ("Cons", 2)] (fun t => Walk listDecls t (listOf τ)) _ eqs
    _ t walked
  · intro v certified
    rcases (walk_list_inversion τ v).mp certified with rfl | ⟨x, r, rfl, -, -⟩
    · exact ⟨("Nil", 0), by simp, [], rfl, rfl⟩
    · exact ⟨("Cons", 2), by simp, [x, r], rfl, rfl⟩
  · intro k member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · obtain ⟨eq, inEqs, pats⟩ := nilCase
      exact ⟨eq, inEqs, [], pats, rfl⟩
    · obtain ⟨eq, inEqs, x, xs, pats⟩ := consCase
      exact ⟨eq, inEqs, [x, xs], pats, rfl⟩

end ListSort

namespace Controls

open TypedCalls.Controls

/-- Constant guard counts multiply along the spine. -/
theorem guardProduct_const {T F : Type} (P : Family T F) (k : ℕ) (fs : List F) (e : T) :
    guardProduct P (fun _ => k) fs e = k ^ fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [guardProduct, ih, pow_succ, mul_comm]

/-- **Two derivations per cell double the answers at every cell**: with every
guard counting two, the typed recursion answers `2ⁿ` times what the native fold
answers on a spine of `n` cells, so a fold that skips the guards is wrong on
every nonempty spine. -/
theorem two_rows_double {T F β ε : Type} {P : Family T F} {answers : T → Multiset (β × ε)}
    (G : GuardedRecursion P (fun _ => 2) answers) (fs : List F) (e : T) :
    answers (P.build ⟨fs, e⟩) = 2 ^ fs.length • (answers e).map (G.foldFields fs) ∧
      (fs ≠ [] → answers e ≠ 0 →
        answers (P.build ⟨fs, e⟩) ≠ (answers e).map (G.foldFields fs)) := by
  refine ⟨by rw [G.guarded_build, guardProduct_const], fun nonempty some same => ?_⟩
  have := (G.skip_iff fs e some).mp same 0 (List.length_pos_of_ne_nil nonempty)
  simp at this

def zeroE : Expr := .const (num 0)

def lsumEqs : List Equation :=
  [⟨[ctorPat "Nil" []], zeroE⟩, ⟨[ctorPat "Cons" ["x", "xs"]], zeroE⟩]

/-- Both cases of `lsum` cover the sort. -/
theorem lsum_matched (t : Atom) (walked : Walk listDecls t (listOf (.sym "Number"))) :
    Matched lsumEqs [t] :=
  list_exhaustive _ lsumEqs ⟨⟨[ctorPat "Nil" []], zeroE⟩, by simp [lsumEqs], rfl⟩
    ⟨⟨[ctorPat "Cons" ["x", "xs"]], zeroE⟩, by simp [lsumEqs], "x", "xs", rfl⟩ t walked

/-- **Without a certificate the unmatched path is live**: `foo` matches no
equation of `lsum`, and does not walk at a list type. -/
theorem uncertified_unmatched :
    ¬ Matched lsumEqs [sym "foo"] ∧ ¬ Walk listDecls (sym "foo") (listOf (.sym "Number")) := by
  constructor
  · rintro ⟨eq, member, matched⟩
    simp only [lsumEqs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [ctorPat, Pat.matchAll, Pat.match] at matched
  · intro walked
    rcases (walk_list_inversion _ _).mp walked with same | ⟨_, _, same, -⟩ <;> simp at same

/-- **Without a covering equation the unmatched path is live on a certified
term**: with only the `Cons` case, `Nil` is certified and unmatched. -/
theorem missing_case_unmatched :
    Walk listDecls (sym "Nil") (listOf (.sym "Number")) ∧
      ¬ Matched [⟨[ctorPat "Cons" ["x", "xs"]], zeroE⟩] [sym "Nil"] := by
  refine ⟨walk_nil_list _, ?_⟩
  rintro ⟨eq, member, matched⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  simp [ctorPat, Pat.matchAll, Pat.match] at matched

/-- **A pattern with a constant field does not cover its constructor**:
`(Cons $x Nil)` leaves the certified `(Cons 1 (Cons 2 Nil))` unmatched. -/
theorem nonlinear_does_not_cover :
    Walk listDecls (app "Cons" [num 1, app "Cons" [num 2, sym "Nil"]]) (listOf (.sym "Number")) ∧
      ¬ Matched [⟨[.ctor "Cons" [.var "x", .const (sym "Nil")]], zeroE⟩]
        [app "Cons" [num 1, app "Cons" [num 2, sym "Nil"]]] := by
  refine ⟨?_, ?_⟩
  · refine (walk_cons_list _ _ _).mpr ⟨⟨"Number", rfl, rfl⟩, (walk_cons_list _ _ _).mpr
      ⟨⟨"Number", rfl, rfl⟩, walk_nil_list _⟩⟩
  · rintro ⟨eq, member, matched⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    simp [Pat.matchAll, Pat.match] at matched

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ClosedSortEvidence
