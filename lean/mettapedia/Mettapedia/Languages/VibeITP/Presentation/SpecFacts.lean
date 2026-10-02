import Mettapedia.Languages.VibeITP.Presentation.Instances
import Mettapedia.Languages.VibeITP.Spec.Derivation

/-!
# Vibe-ITP presentation: facts about the specification and the encoding

* the encoding of a symbol in normal form, and injectivity of the encodings;
* inversion of term encodings constructor by constructor;
* the kernel's argument traversals restated over an explicit binder list,
  which is how the presented rules walk a head symbol's binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-! ## Symbols -/

def bindersOf (sig : Sig) (s : SymId) : List Nat :=
  match sig s with
  | some info => info.binders
  | none => []

def kindOf (sig : Sig) (s : SymId) : SymKind :=
  match sig s with
  | some info => info.kind
  | none => .constant

theorem encSym_eq (sig : Sig) (s : SymId) :
    encSym sig s =
      cSym (encNat (symNumber s)) (encKind (kindOf sig s)) (encNatList (bindersOf sig s)) := by
  cases hs : sig s with
  | none => simp only [encSym, kindOf, bindersOf, hs]; rfl
  | some info => simp only [encSym, kindOf, bindersOf, hs]

theorem binderAt_eq (sig : Sig) (s : SymId) (i : Nat) :
    binderAt sig s i = (bindersOf sig s).getD i 0 := by
  cases hs : sig s <;> simp [binderAt, bindersOf, hs]

theorem isFvarSym_eq (sig : Sig) (s : SymId) :
    isFvarSym sig s = (kindOf sig s == .fvar) := by
  cases hs : sig s with
  | none => simp only [isFvarSym, kindOf, hs]; rfl
  | some info => simp only [isFvarSym, kindOf, hs]

theorem symArity_eq (sig : Sig) (s : SymId) : symArity sig s = (bindersOf sig s).length := by
  cases hs : sig s <;> simp only [symArity, bindersOf, hs] <;> rfl

theorem Builtin.slot_inj : ∀ {a b : Builtin}, a.slot = b.slot → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [Builtin.slot] at h)

theorem Builtin.slot_le (b : Builtin) : b.slot ≤ 12 := by
  cases b <;> simp [Builtin.slot]

theorem symNumber_inj : ∀ {s₁ s₂ : SymId}, symNumber s₁ = symNumber s₂ → s₁ = s₂
  | .builtin a, .builtin b, h => by
      simp only [symNumber] at h; rw [Builtin.slot_inj h]
  | .builtin a, .fresh n, h => by
      simp only [symNumber, protectedSymbolSlots] at h
      have := Builtin.slot_le a; omega
  | .fresh n, .builtin b, h => by
      simp only [symNumber, protectedSymbolSlots] at h
      have := Builtin.slot_le b; omega
  | .fresh n, .fresh m, h => by
      simp only [symNumber, protectedSymbolSlots] at h
      have : n = m := by omega
      rw [this]

theorem encKind_inj : ∀ {a b : SymKind}, encKind a = encKind b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [encKind, cKConst, cKFvar] at h)

theorem encSym_inj (sig : Sig) {s₁ s₂ : SymId} (h : encSym sig s₁ = encSym sig s₂) : s₁ = s₂ := by
  rw [encSym_eq, encSym_eq] at h
  simp only [cSym, Pattern.apply.injEq, List.cons.injEq, true_and] at h
  exact symNumber_inj (encNat_inj h.1)

/-! ## Term encodings -/

theorem encTerm_bvar (sig : Sig) (i : Nat) : encTerm sig (.bvar i) = cBVar (encNat i) := rfl

theorem encTerm_lit (sig : Sig) (bytes : List UInt8) :
    encTerm sig (.lit bytes) = cLit (encBytes bytes) := rfl

theorem encTerm_app (sig : Sig) (s : SymId) (args : List Term) :
    encTerm sig (.app s args) =
      cApp (encSym sig s) (encTermList sig args)
        (cAnn (encNat (depthArgs sig s 0 args))
          (encBool (isFvarSym sig s || hasFvarList sig args))) := by
  rw [encTerm]

theorem encTermList_nil (sig : Sig) : encTermList sig [] = cNil := by rw [encTermList]

theorem encTermList_cons (sig : Sig) (t : Term) (ts : List Term) :
    encTermList sig (t :: ts) = cCons (encTerm sig t) (encTermList sig ts) := by
  rw [encTermList]

theorem encTerm_eq_bvar (sig : Sig) (t : Term) (n : Pattern) :
    encTerm sig t = cBVar n → ∃ i, t = .bvar i ∧ n = encNat i := by
  intro h
  cases t with
  | bvar i =>
      rw [encTerm_bvar] at h
      simp only [cBVar, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
      exact ⟨i, rfl, h.symm⟩
  | lit bytes => rw [encTerm_lit] at h; simp [cLit, cBVar] at h
  | app s args => rw [encTerm_app] at h; simp [cApp, cBVar] at h

theorem encTerm_eq_lit (sig : Sig) (t : Term) (bs : Pattern) :
    encTerm sig t = cLit bs → ∃ bytes, t = .lit bytes ∧ bs = encBytes bytes := by
  intro h
  cases t with
  | bvar i => rw [encTerm_bvar] at h; simp [cLit, cBVar] at h
  | lit bytes =>
      rw [encTerm_lit] at h
      simp only [cLit, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
      exact ⟨bytes, rfl, h.symm⟩
  | app s args => rw [encTerm_app] at h; simp [cApp, cLit] at h

theorem encTerm_eq_app (sig : Sig) (t : Term) (s ts ann : Pattern) :
    encTerm sig t = cApp s ts ann →
      ∃ h args, t = .app h args ∧ s = encSym sig h ∧ ts = encTermList sig args ∧
        ann = cAnn (encNat (depthArgs sig h 0 args))
          (encBool (isFvarSym sig h || hasFvarList sig args)) := by
  intro heq
  cases t with
  | bvar i => rw [encTerm_bvar] at heq; simp [cApp, cBVar] at heq
  | lit bytes => rw [encTerm_lit] at heq; simp [cApp, cLit] at heq
  | app h args =>
      rw [encTerm_app] at heq
      simp only [cApp, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at heq
      exact ⟨h, args, rfl, heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩

theorem encTermList_eq_nil (sig : Sig) (ts : List Term) :
    encTermList sig ts = cNil → ts = [] := by
  intro h
  cases ts with
  | nil => rfl
  | cons t ts => rw [encTermList_cons] at h; simp [cCons, cNil] at h

theorem encTermList_eq_cons (sig : Sig) (ts : List Term) (x xs : Pattern) :
    encTermList sig ts = cCons x xs →
      ∃ t ts', ts = t :: ts' ∧ x = encTerm sig t ∧ xs = encTermList sig ts' := by
  intro h
  cases ts with
  | nil => rw [encTermList_nil] at h; simp [cCons, cNil] at h
  | cons t ts =>
      rw [encTermList_cons] at h
      simp only [cCons, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
      exact ⟨t, ts, rfl, h.1.symm, h.2.symm⟩

mutual
theorem encTerm_inj (sig : Sig) : ∀ {t₁ t₂ : Term}, encTerm sig t₁ = encTerm sig t₂ → t₁ = t₂
  | .bvar i, t₂, h => by
      rw [encTerm_bvar] at h
      obtain ⟨j, rfl, hj⟩ := encTerm_eq_bvar sig t₂ _ h.symm
      rw [encNat_inj hj]
  | .lit b, t₂, h => by
      rw [encTerm_lit] at h
      obtain ⟨b', rfl, hb⟩ := encTerm_eq_lit sig t₂ _ h.symm
      rw [encBytes_inj hb]
  | .app s args, t₂, h => by
      rw [encTerm_app] at h
      obtain ⟨s', args', rfl, hs, hts, _⟩ := encTerm_eq_app sig t₂ _ _ _ h.symm
      rw [encSym_inj sig hs, encTermList_inj sig hts]
theorem encTermList_inj (sig : Sig) :
    ∀ {l₁ l₂ : List Term}, encTermList sig l₁ = encTermList sig l₂ → l₁ = l₂
  | [], l₂, h => by
      rw [encTermList_nil] at h
      rw [encTermList_eq_nil sig l₂ h.symm]
  | t :: ts, l₂, h => by
      rw [encTermList_cons] at h
      obtain ⟨t', ts', rfl, ht, hts⟩ := encTermList_eq_cons sig l₂ _ _ h.symm
      rw [encTerm_inj sig ht, encTermList_inj sig hts]
end

theorem encNatList_eq_nil (l : List Nat) : encNatList l = cNil → l = [] := by
  intro h
  cases l with
  | nil => rfl
  | cons a as => simp [encNatList, encList, cCons, cNil] at h

theorem encNatList_eq_cons (l : List Nat) (x xs : Pattern) :
    encNatList l = cCons x xs → ∃ a as, l = a :: as ∧ x = encNat a ∧ xs = encNatList as := by
  intro h
  cases l with
  | nil => simp [encNatList, encList, cCons, cNil] at h
  | cons a as =>
      simp only [encNatList, List.map_cons, encList, cCons, Pattern.apply.injEq,
        List.cons.injEq, and_true, true_and] at h
      exact ⟨a, as, rfl, h.1.symm, h.2.symm⟩

theorem encNatList_nil : encNatList [] = cNil := rfl

theorem encNatList_cons (a : Nat) (as : List Nat) :
    encNatList (a :: as) = cCons (encNat a) (encNatList as) := rfl

theorem encBytes_nil : encBytes [] = cNil := rfl

theorem encBytes_cons (b : UInt8) (bs : List UInt8) :
    encBytes (b :: bs) = cCons (encNat b.toNat) (encBytes bs) := rfl

theorem decList_encTermList (sig : Sig) :
    ∀ ts : List Term, decList (encTermList sig ts) = some (ts.map (encTerm sig))
  | [] => by rw [encTermList_nil]; rfl
  | t :: ts => by
      rw [encTermList_cons, decList_cons, decList_encTermList sig ts]
      rfl

theorem decList_encNatList : ∀ l : List Nat, decList (encNatList l) = some (l.map encNat)
  | [] => rfl
  | a :: as => by
      rw [encNatList_cons, decList_cons, decList_encNatList as]
      rfl

theorem decList_encBytes :
    ∀ bytes : List UInt8, decList (encBytes bytes) = some (bytes.map fun b => encNat b.toNat)
  | [] => rfl
  | b :: bs => by
      rw [encBytes_cons, decList_cons, decList_encBytes bs]
      rfl

/-! ## Argument traversals over an explicit binder list -/

def depthBinders (sig : Sig) : List Nat → List Term → Nat
  | _, [] => 0
  | bs, a :: as => max (depth sig a - bs.headD 0) (depthBinders sig bs.tail as)

theorem drop_headD (l : List Nat) (i : Nat) : (l.drop i).headD 0 = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a as _ =>
      cases i <;> simp

theorem drop_tail (l : List Nat) (i : Nat) : (l.drop i).tail = l.drop (i + 1) := by
  simp [List.tail_drop]

theorem depthArgs_eq (sig : Sig) (s : SymId) :
    ∀ (idx : Nat) (args : List Term),
      depthArgs sig s idx args = depthBinders sig ((bindersOf sig s).drop idx) args
  | _, [] => by simp [depthArgs, depthBinders]
  | idx, a :: as => by
      rw [depthArgs, depthBinders, depthArgs_eq sig s (idx + 1) as, binderAt_eq,
        drop_headD, drop_tail]

theorem depth_app (sig : Sig) (s : SymId) (args : List Term) :
    depth sig (.app s args) = depthBinders sig (bindersOf sig s) args := by
  rw [depth, depthArgs_eq]; rfl

theorem hasFvar_app (sig : Sig) (s : SymId) (args : List Term) :
    hasFvar sig (.app s args) = (isFvarSym sig s || hasFvarList sig args) := by
  rw [hasFvar]

theorem hasFvarList_nil (sig : Sig) : hasFvarList sig [] = false := by rw [hasFvarList]

theorem hasFvarList_cons (sig : Sig) (t : Term) (ts : List Term) :
    hasFvarList sig (t :: ts) = (hasFvar sig t || hasFvarList sig ts) := by
  rw [hasFvarList]

theorem encTerm_app' (sig : Sig) (s : SymId) (args : List Term) :
    encTerm sig (.app s args) =
      cApp (encSym sig s) (encTermList sig args)
        (cAnn (encNat (depthBinders sig (bindersOf sig s) args))
          (encBool (isFvarSym sig s || hasFvarList sig args))) := by
  rw [encTerm_app, depthArgs_eq]; rfl

def shiftList (sig : Sig) (amount cutoff : Nat) : List Nat → List Term → Option (List Term)
  | _, [] => some []
  | bs, a :: as =>
      if cutoff + bs.headD 0 < wordBound then
        match shift sig amount (cutoff + bs.headD 0) a, shiftList sig amount cutoff bs.tail as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
      else none

theorem shiftArgs_eq (sig : Sig) (amount : Nat) (s : SymId) (cutoff : Nat) :
    ∀ (idx : Nat) (args : List Term),
      shiftArgs sig amount s cutoff idx args =
        shiftList sig amount cutoff ((bindersOf sig s).drop idx) args
  | _, [] => by simp [shiftArgs, shiftList]
  | idx, a :: as => by
      rw [shiftArgs, shiftList, shiftArgs_eq sig amount s cutoff (idx + 1) as, binderAt_eq,
        drop_headD, drop_tail]
      split <;> rfl

def substList (sig : Sig) (numArgs : Nat) (args : List Term) (offset : Nat) :
    List Nat → List Term → Option (List Term)
  | _, [] => some []
  | bs, a :: as =>
      if offset + bs.headD 0 < wordBound then
        match substGo sig numArgs args (offset + bs.headD 0) a,
            substList sig numArgs args offset bs.tail as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
      else none

theorem substGoArgs_eq (sig : Sig) (numArgs : Nat) (args : List Term) (s : SymId)
    (offset : Nat) : ∀ (idx : Nat) (as : List Term),
      substGoArgs sig numArgs args s offset idx as =
        substList sig numArgs args offset ((bindersOf sig s).drop idx) as
  | _, [] => by simp [substGoArgs, substList]
  | idx, a :: as => by
      rw [substGoArgs, substList, substGoArgs_eq sig numArgs args s offset (idx + 1) as,
        binderAt_eq, drop_headD, drop_tail]
      split <;> rfl

def instList (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (offset : Nat) :
    List Nat → List Term → Option (List Term)
  | _, [] => some []
  | bs, a :: as =>
      if offset + bs.headD 0 < wordBound then
        match instGo sig F arity value (offset + bs.headD 0) a,
            instList sig F arity value offset bs.tail as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
      else none

theorem instArgs_eq (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (s : SymId)
    (offset : Nat) : ∀ (idx : Nat) (as : List Term),
      instArgs sig F arity value s offset idx as =
        instList sig F arity value offset ((bindersOf sig s).drop idx) as
  | _, [] => by simp [instArgs, instList]
  | idx, a :: as => by
      rw [instArgs, instList, instArgs_eq sig F arity value s offset (idx + 1) as,
        binderAt_eq, drop_headD, drop_tail]
      split <;> rfl

theorem instList_length (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (offset : Nat) :
    ∀ (bs : List Nat) (as as' : List Term),
      instList sig F arity value offset bs as = some as' → as'.length = as.length
  | _, [], as', h => by simp [instList] at h; subst h; rfl
  | bs, a :: as, as', h => by
      simp only [instList] at h
      split at h
      · split at h
        · rename_i a' as'' _ htail
          simp only [Option.some.injEq] at h
          subst h
          simp [instList_length sig F arity value offset bs.tail as as'' htail]
        · simp at h
      · simp at h

/-! ## Hints of definitions -/

/-- Consume one hint per free-variable occurrence; each hint must name the
occurring parameter.  Returns the unused hints. -/
def consumeHints (fids : List SymId) : List SymId → List Nat → Option (List Nat)
  | [], hs => some hs
  | _ :: _, [] => none
  | s :: occ, h :: hs => if fids[h]? = some s then consumeHints fids occ hs else none

theorem consumeHints_append (fids : List SymId) :
    ∀ (occ₁ occ₂ : List SymId) (hs : List Nat),
      consumeHints fids (occ₁ ++ occ₂) hs = (consumeHints fids occ₁ hs).bind (consumeHints fids occ₂)
  | [], occ₂, hs => by simp [consumeHints]
  | s :: occ, occ₂, [] => by simp [consumeHints]
  | s :: occ, occ₂, h :: hs => by
      simp only [List.cons_append, consumeHints]
      split
      · exact consumeHints_append fids occ occ₂ hs
      · simp

theorem hintsAdmit_iff (fids : List SymId) (hints : List Nat) (occ : List SymId) :
    hintsAdmit fids hints occ = true ↔
      (∀ h ∈ hints, h < fids.length) ∧ (consumeHints fids occ hints).isSome := by
  unfold hintsAdmit
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨hall, hlen⟩, hzip⟩
    refine ⟨hall, ?_⟩
    clear hall
    induction occ generalizing hints with
    | nil => simp [consumeHints]
    | cons s occ ih =>
        cases hints with
        | nil => simp at hlen
        | cons h hs =>
            simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hzip
            simp only [consumeHints, hzip.1, if_true]
            exact ih hs hzip.2 (by simpa using hlen)
  · rintro ⟨hall, hsome⟩
    refine ⟨⟨hall, ?_⟩, ?_⟩ <;> clear hall
    · induction occ generalizing hints with
      | nil => simp
      | cons s occ ih =>
          cases hints with
          | nil => simp [consumeHints] at hsome
          | cons h hs =>
              simp only [consumeHints] at hsome
              split at hsome
              · simpa using ih hs hsome
              · simp at hsome
    · induction occ generalizing hints with
      | nil => simp
      | cons s occ ih =>
          cases hints with
          | nil => simp [consumeHints] at hsome
          | cons h hs =>
              simp only [consumeHints] at hsome
              split at hsome
              · rename_i heq
                simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
                exact ⟨heq, ih hs hsome⟩
              · simp at hsome

theorem fvarOccurrences_app (sig : Sig) (s : SymId) (args : List Term) :
    fvarOccurrences sig (.app s args) =
      (if isFvarSym sig s then [s] else []) ++ fvarOccurrencesList sig args := by
  rw [fvarOccurrences]

theorem fvarOccurrencesList_cons (sig : Sig) (t : Term) (ts : List Term) :
    fvarOccurrencesList sig (t :: ts) = fvarOccurrences sig t ++ fvarOccurrencesList sig ts := by
  rw [fvarOccurrencesList]

end Mettapedia.Languages.VibeITP.Presentation
