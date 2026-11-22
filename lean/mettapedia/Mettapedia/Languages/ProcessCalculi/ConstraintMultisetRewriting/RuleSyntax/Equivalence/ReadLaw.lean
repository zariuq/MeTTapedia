import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Strong
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.TellLaw

/-!
# Reading a row is taking it and making it again

`withRead r p` has the takes, tells, checks, made rows and collect query of `r`, and one read, of `p`.
`withTakeMake r p` takes `p` after the takes of `r` and makes `p` after its made rows, and reads
nothing. With infinitely many identities they are interchangeable beside every program, at every
state (`readTakeMake_congruent`).

* A firing of the read is answered by the take-and-make firing that takes the read row `o` and makes
  a fresh identity `m`, and conversely (`readTakeMake_core`). Their informations are equal
  (`information_takeMake`): the take equates `p` with the row exactly as the read did.
* The results differ by the identity of the row (the read keeps `o`, the take-and-make makes `m`), and
  by its label: the read keeps the old label, the take-and-make labels it by the opened `p`; the
  information equates the two. So the results are congruent: rename `o` to `m` (Law 1), then replace
  the label by one the knowledge equates with it (Law 2).

Where the hypotheses come from:

* **Infinitely many identities.** The made row needs an identity absent from the store; with every
  identity present the read fires and the take-and-make cannot. With one identity the two rules are
  not congruent (`AtOneFrame.read_needs_infinite`); an instance with identities `ℕ` is
  `AtOneFrame.read_example`.
* **One read.** Two reads may read one row in one firing, a take and a read may not
  (`Enabled.apart`), so the law is stated for a rule with one read; rules with two reads are not
  covered here.
* **One firing.** The law relates a read to a take and a make in the same firing. A take in one
  firing and a make in a later one pass through a state without the row, which a count or an absence
  of another firing can read; that comparison is not made here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uE uOcc uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- The rule reading `p`. -/
abbrev withRead (r : Rule Tm) (p : Tm r.locals) : Rule Tm :=
  ⟨r.locals, ⟨r.body.take, [p], r.body.tell, r.body.checks, r.body.produce⟩, r.collect⟩

/-- The rule taking `p` and making it again. -/
abbrev withTakeMake (r : Rule Tm) (p : Tm r.locals) : Rule Tm :=
  ⟨r.locals, ⟨r.body.take ++ [p], [], r.body.tell, r.body.checks, r.body.produce ++ [p]⟩, r.collect⟩

section Relabel

variable {O : Type uOcc} [DecidableEq O]

theorem relabel_append_of_mem {a : Obj} (old : O → Tm a) (m : O) (t : Tm a) :
    ∀ (made : List O) (rows : List (Tm a)) (o : O), made.length = rows.length → o ∈ made →
      relabel old (made ++ [m]) (rows ++ [t]) o = relabel old made rows o
  | [], _, _, _, inside => by cases inside
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | n :: rest, u :: us, o, lengths, inside => by
      simp only [List.cons_append, relabel]
      split_ifs with same
      · rfl
      · have later : o ∈ rest := by
          rcases List.mem_cons.mp inside with rfl | later
          · exact absurd rfl same
          · exact later
        exact relabel_append_of_mem old m t rest us o (Nat.succ.inj lengths) later

theorem relabel_append_last {a : Obj} (old : O → Tm a) (m : O) (t : Tm a) :
    ∀ (made : List O) (rows : List (Tm a)), made.length = rows.length → m ∉ made →
      relabel old (made ++ [m]) (rows ++ [t]) m = t
  | [], [], _, _ => by simp [relabel]
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | n :: rest, u :: us, lengths, absent => by
      have other : m ≠ n := fun same => absent (same ▸ List.mem_cons_self)
      have later : m ∉ rest := fun inside => absent (List.mem_cons_of_mem _ inside)
      simp only [List.cons_append, relabel, if_neg other]
      exact relabel_append_last old m t rest us (Nat.succ.inj lengths) later

theorem relabel_append_other {a : Obj} (old : O → Tm a) (m : O) (t : Tm a) (made : List O)
    (rows : List (Tm a)) (o : O) (notMade : o ∉ made) (other : o ≠ m) :
    relabel old (made ++ [m]) (rows ++ [t]) o = relabel old made rows o := by
  rw [Firing.relabel_of_not_mem old (made ++ [m]) (rows ++ [t]) (by simp [notMade, other]),
    Firing.relabel_of_not_mem old made rows notMade]

end Relabel

section Law

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

omit [DecidableEq O] in
/-- Support depends on the present rows only through which they are. -/
theorem supports_present_eq {F : Obj} {K : EquationStore (Tm F)} {W W' : Finset O}
    {ℓ : O → Tm F} (same : W = W') {b : Obj} (φ ψ : Hom F b) :
    Supports X (⟨F, K, W, ℓ⟩ : State Tm O) φ ψ ↔ Supports X (⟨F, K, W', ℓ⟩ : State Tm O) φ ψ := by
  subst same
  exact Iff.rfl

variable (r : Rule Tm) (p : Tm r.locals)

/-- The read firing: takes `tl`, reads `o`, makes `ml`. -/
def readFiring {a : Obj} (ext : E.Ext a) (ι : Hom r.locals (E.target ext)) (tl ml : List O) (o : O)
    (seen : List (Finset O)) : Firing O E ({withRead r p} : Program Tm) a :=
  ⟨withRead r p, Set.mem_singleton _, ext, ι, ⟨tl, [o], ml⟩, seen⟩

/-- The take-and-make firing: takes `tl` and then `o`, makes `ml` and then `m`. -/
def takeMakeFiring {a : Obj} (ext : E.Ext a) (ι : Hom r.locals (E.target ext)) (tl ml : List O)
    (o m : O) (seen : List (Finset O)) : Firing O E ({withTakeMake r p} : Program Tm) a :=
  ⟨withTakeMake r p, Set.mem_singleton _, ext, ι, ⟨tl ++ [o], [], ml ++ [m]⟩, seen⟩

theorem terms_takeMake (u : Tm r.locals) :
    u ∈ (withTakeMake r p).terms ↔ u ∈ (withRead r p).terms := by
  simp only [Rule.terms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem kept_takeMake (u : Tm r.locals) :
    u ∈ keptTerms (withTakeMake r p) ↔ u ∈ keptTerms (withRead r p) := by
  simp only [keptTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

variable {r p}

omit [DecidableEq O] in
theorem fresh_takeMake {s : State Tm O} (ext : E.Ext s.frame) (ι : Hom r.locals (E.target ext))
    (tl ml : List O) (o m : O) (seen : List (Finset O)) :
    (takeMakeFiring r p ext ι tl ml o m seen).Fresh X s ↔ (readFiring r p ext ι tl ml o seen).Fresh X s := by
  constructor
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    exact ⟨u, state, fun v inside => rule v ((terms_takeMake r p v).mpr inside)⟩
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    exact ⟨u, state, fun v inside => rule v ((terms_takeMake r p v).mp inside)⟩

omit [DecidableEq O] in
/-- **The take equates `p` with the row exactly as the read did.** -/
theorem information_takeMake {s : State Tm O} (ext : E.Ext s.frame) (ι : Hom r.locals (E.target ext))
    (tl ml : List O) (o m : O) (seen : List (Finset O)) (lengths : r.body.take.length = tl.length) :
    (takeMakeFiring r p ext ι tl ml o m seen).information X s =
      (readFiring r p ext ι tl ml o seen).information X s := by
  show X.applyStore (E.weaken ext) s.knowledge ++
      ((r.body.take ++ [p]).map (X.act ι)).zipWith
        (fun q o' => (q, X.act (E.weaken ext) (s.label o'))) (tl ++ [o]) ++
      (([] : List (Tm r.locals)).map (X.act ι)).zipWith
        (fun q o' => (q, X.act (E.weaken ext) (s.label o'))) [] ++
      (r.body.tell.map fun pair => (X.act ι pair.1, X.act ι pair.2)) =
    X.applyStore (E.weaken ext) s.knowledge ++
      (r.body.take.map (X.act ι)).zipWith (fun q o' => (q, X.act (E.weaken ext) (s.label o'))) tl ++
      ([p].map (X.act ι)).zipWith (fun q o' => (q, X.act (E.weaken ext) (s.label o'))) [o] ++
      (r.body.tell.map fun pair => (X.act ι pair.1, X.act ι pair.2))
  rw [List.map_append, List.zipWith_append (by rw [List.length_map]; exact lengths)]
  simp

/-- **The two firings, at one state**: admitted together, with congruent results. -/
theorem readTakeMake_core
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (invariantModulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {s : State Tm O} (ext : E.Ext s.frame) (ι : Hom r.locals (E.target ext)) (tl ml : List O)
    (o m : O) (seen : List (Finset O)) (mFresh : m ∉ s.present) (mNew : m ∉ ml) :
    ((readFiring r p ext ι tl ml o seen).Admits X s ↔
        (takeMakeFiring r p ext ι tl ml o m seen).Admits X s) ∧
      ((readFiring r p ext ι tl ml o seen).Admits X s → ∀ Q : Program Tm,
        Congruent X O E obs ⟨Q, (readFiring r p ext ι tl ml o seen).result X s⟩
          ⟨Q, (takeMakeFiring r p ext ι tl ml o m seen).result X s⟩) := by
  let f := readFiring r p ext ι tl ml o seen
  let g := takeMakeFiring r p ext ι tl ml o m seen
  have admitsIff : f.Admits X s ↔ g.Admits X s := by
    constructor
    · rintro ⟨⟨fresh, tlNodup, mlNodup, takeLength, -, produceLength, collect⟩, enabled, solvable, asks⟩
      have info : g.information X s = f.information X s :=
        information_takeMake ext ι tl ml o m seen takeLength
      have oPresent : o ∈ s.present := enabled.kept_subset (by simp [f, readFiring, Selection.commit])
      have oNotTaken : o ∉ tl := fun inside => Finset.disjoint_left.mp enabled.apart
        (by simpa [f, readFiring, Selection.commit] using inside)
        (by simp [f, readFiring, Selection.commit])
      refine ⟨⟨(fresh_takeMake ext ι tl ml o m seen).mpr fresh, ?_, ?_, ?_, rfl, ?_, collect⟩, ?_, ?_, ?_⟩
      · exact List.nodup_append.mpr ⟨tlNodup, List.nodup_singleton o, fun a inside b same => by
          rw [List.mem_singleton] at same
          subst same
          exact fun equal => oNotTaken (equal ▸ inside)⟩
      · exact List.nodup_append.mpr ⟨mlNodup, List.nodup_singleton m, fun a inside b same => by
          rw [List.mem_singleton] at same
          subst same
          exact fun equal => mNew (equal ▸ inside)⟩
      · show (r.body.take ++ [p]).length = (tl ++ [o]).length
        simp only [List.length_append, List.length_singleton]
        exact congrArg (· + 1) takeLength
      · show (r.body.produce ++ [p]).length = (ml ++ [m]).length
        simp only [List.length_append, List.length_singleton]
        exact congrArg (· + 1) produceLength
      · refine ⟨fun x inside => ?_, fun x inside => ?_, ?_, ?_, fun q inside => ?_⟩
        · simp only [g, takeMakeFiring, Selection.commit, List.toFinset_append, Finset.mem_union,
            List.mem_toFinset, List.mem_singleton] at inside
          rcases inside with taken | rfl
          · exact enabled.taken_subset (by simpa [f, readFiring, Selection.commit] using taken)
          · exact oPresent
        · simp [g, takeMakeFiring, Selection.commit] at inside
        · simp [g, takeMakeFiring, Selection.commit]
        · rw [Finset.disjoint_left]
          intro x inside present
          simp only [g, takeMakeFiring, Selection.commit, List.toFinset_append, Finset.mem_union,
            List.mem_toFinset, List.mem_singleton] at inside
          rcases inside with made | rfl
          · exact Finset.disjoint_left.mp enabled.fresh
              (by simpa [f, readFiring, Selection.commit] using made) present
          · exact mFresh present
        · exact absurd inside List.not_mem_nil
      · rw [info]
        exact solvable
      · rw [info]
        exact asks
    · rintro ⟨⟨fresh, tlNodup, mlNodup, takeLength, -, produceLength, collect⟩, enabled, solvable, asks⟩
      have takeLength' : r.body.take.length = tl.length := by
        have lengths : (r.body.take ++ [p]).length = (tl ++ [o]).length := takeLength
        simp only [List.length_append, List.length_singleton] at lengths
        omega
      have info : g.information X s = f.information X s :=
        information_takeMake ext ι tl ml o m seen takeLength'
      have tlNodup' : tl.Nodup := (List.nodup_append.mp tlNodup).1
      have oNotTaken : o ∉ tl := fun inside =>
        (List.nodup_append.mp tlNodup).2.2 o inside o (List.mem_singleton_self o) rfl
      refine ⟨⟨(fresh_takeMake ext ι tl ml o m seen).mp fresh, tlNodup', (List.nodup_append.mp mlNodup).1,
        takeLength', rfl, ?_, collect⟩, ?_, ?_, ?_⟩
      · have lengths : (r.body.produce ++ [p]).length = (ml ++ [m]).length := produceLength
        simp only [List.length_append, List.length_singleton] at lengths
        show r.body.produce.length = ml.length
        omega
      · refine ⟨fun x inside => ?_, fun x inside => ?_, ?_, ?_, fun q inside => ?_⟩
        · have taken : x ∈ tl := by simpa [f, readFiring, Selection.commit] using inside
          exact enabled.taken_subset (by simp [g, takeMakeFiring, Selection.commit, taken])
        · have same : x = o := by simpa [f, readFiring, Selection.commit] using inside
          subst same
          exact enabled.taken_subset (by simp [g, takeMakeFiring, Selection.commit])
        · rw [Finset.disjoint_left]
          intro x inside inside'
          have same : x = o := by simpa [f, readFiring, Selection.commit] using inside'
          subst same
          exact oNotTaken (by simpa [f, readFiring, Selection.commit] using inside)
        · rw [Finset.disjoint_left]
          intro x inside present
          have made : x ∈ ml := by simpa [f, readFiring, Selection.commit] using inside
          exact Finset.disjoint_left.mp enabled.fresh
            (by simp [g, takeMakeFiring, Selection.commit, made]) present
        · exact absurd inside List.not_mem_nil
      · rw [← info]
        exact solvable
      · rw [← info]
        exact asks
  refine ⟨admitsIff, fun admitted Q => ?_⟩
  obtain ⟨⟨-, -, -, takeLength, -, produceLength, -⟩, enabled, -, -⟩ := id admitted
  have admittedG : g.Admits X s := admitsIff.mp admitted
  have info : g.information X s = f.information X s :=
    information_takeMake ext ι tl ml o m seen takeLength
  have oPresent : o ∈ s.present := enabled.kept_subset (by simp [readFiring, Selection.commit])
  have oNotTaken : o ∉ tl := fun inside => Finset.disjoint_left.mp enabled.apart
    (by simpa [f, readFiring, Selection.commit] using inside)
    (by simp [readFiring, Selection.commit])
  have oNotMade : o ∉ ml := fun inside => Finset.disjoint_left.mp enabled.fresh
    (by simpa [f, readFiring, Selection.commit] using inside) oPresent
  have mNotO : m ≠ o := fun same => mFresh (same ▸ oPresent)
  have produceLength' : ml.length = (f.opened X).produce.length := by
    show ml.length = (r.body.produce.map (X.act ι)).length
    rw [List.length_map]
    exact produceLength.symm
  let π : Equiv.Perm O := Equiv.swap o m
  let renamed := renameState π (f.result X s)
  -- The renamed result has the take-and-make result's rows.
  have present : renamed.present = (g.result X s).present := by
    show (fire s.present (f.selection.commit (T := Unit))).map π.toEmbedding =
      fire s.present (g.selection.commit (T := Unit))
    ext x
    rw [Finset.mem_map_equiv, mem_fire, mem_fire]
    simp only [f, g, readFiring, takeMakeFiring, Selection.commit, List.toFinset_append,
      Finset.mem_union, List.mem_toFinset, List.mem_singleton, π, Equiv.symm_swap]
    by_cases isO : x = o
    · subst isO
      rw [Equiv.swap_apply_left]
      constructor
      · rintro (⟨present, -⟩ | made)
        · exact absurd present mFresh
        · exact absurd made mNew
      · rintro (⟨-, notTaken⟩ | made)
        · exact absurd (Or.inr rfl) notTaken
        · rcases made with made | same
          · exact absurd made oNotMade
          · exact absurd same (Ne.symm mNotO)
    · by_cases isM : x = m
      · subst isM
        rw [Equiv.swap_apply_right]
        constructor
        · intro _
          exact Or.inr (Or.inr rfl)
        · intro _
          exact Or.inl ⟨oPresent, oNotTaken⟩
      · rw [Equiv.swap_apply_of_ne_of_ne isO isM]
        constructor
        · rintro (⟨present, notTaken⟩ | made)
          · exact Or.inl ⟨present, fun taken => by
              rcases taken with taken | same
              · exact notTaken taken
              · exact isO same⟩
          · exact Or.inr (Or.inl made)
        · rintro (⟨present, notTaken⟩ | made)
          · exact Or.inl ⟨present, fun taken => notTaken (Or.inl taken)⟩
          · rcases made with made | same
            · exact Or.inr made
            · exact absurd same isM
  have shape : g.result X s =
      ⟨renamed.frame, g.information X s, renamed.present, (g.result X s).label⟩ := by
    rw [present]
    rfl
  have modulo : Modulo X renamed (g.result X s) := by
    refine ⟨g.information X s, (g.result X s).label, ⟨?_, ?_, ?_⟩, shape⟩
    · rw [info]
      exact fun _ _ => Iff.rfl
    · intro x inside b σ solved
      have solvedF : X.Models σ (f.information X s) := solved
      by_cases isM : x = m
      · subst isM
        have left : renamed.label x = f.row X s o := by
          show relabel (f.row X s) ml (f.opened X).produce (π.symm x) = f.row X s o
          rw [Equiv.symm_swap, Equiv.swap_apply_right]
          exact Firing.relabel_of_not_mem _ _ _ oNotMade
        have right : (g.result X s).label x = X.act ι p := by
          show relabel (g.row X s) (ml ++ [x]) ((r.body.produce ++ [p]).map (X.act ι)) x = X.act ι p
          rw [List.map_append, List.map_singleton]
          exact relabel_append_last _ x _ ml _ produceLength' mNew
        rw [left, right]
        have equated := Firing.read_solved f solvedF (p := X.act ι p) (o := o) List.mem_cons_self
        exact (X.equivalence b).symm equated
      · have isNotO : x ≠ o := by
          intro same
          subst same
          have back : π.symm x ∈ fire s.present (f.selection.commit (T := Unit)) :=
            Finset.mem_map_equiv.mp inside
          rw [Equiv.symm_swap, Equiv.swap_apply_left] at back
          rcases mem_fire.mp back with ⟨present, -⟩ | made
          · exact mFresh present
          · exact mNew (by simpa [f, readFiring, Selection.commit] using made)
        have same : renamed.label x = (g.result X s).label x := by
          show relabel (f.row X s) ml (f.opened X).produce (π.symm x) =
            relabel (g.row X s) (ml ++ [m]) ((r.body.produce ++ [p]).map (X.act ι)) x
          rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne isNotO isM, List.map_append,
            List.map_singleton]
          by_cases made : x ∈ ml
          · exact (relabel_append_of_mem _ m _ ml _ x produceLength' made).symm
          · exact (relabel_append_other _ m _ ml _ x made isM).symm
        rw [same]
        exact (X.equivalence b).refl _
    · intro b φ ψ
      have renamedSupport : Supports X renamed φ ψ ↔ Supports X (f.result X s) φ ψ := by
        constructor
        · exact fun agree t mentioned =>
            agree t ((mentions_renameState π (f.result X s) t).mpr mentioned)
        · exact fun agree t mentioned =>
            agree t ((mentions_renameState π (f.result X s) t).mp mentioned)
      have sameTerms : (∀ u ∈ resultTerms X f, X.E (X.act φ u) (X.act ψ u)) ↔
          ∀ u ∈ resultTerms X g, X.E (X.act φ u) (X.act ψ u) := by
        rw [resultTerms_eq f, resultTerms_eq g]
        constructor
        · intro agree u inside
          obtain ⟨v, member, rfl⟩ := List.mem_map.mp inside
          exact agree _ (List.mem_map.mpr ⟨v, (kept_takeMake r p v).mp member, rfl⟩)
        · intro agree u inside
          obtain ⟨v, member, rfl⟩ := List.mem_map.mp inside
          exact agree _ (List.mem_map.mpr ⟨v, (kept_takeMake r p v).mpr member, rfl⟩)
      exact (renamedSupport.trans ((supports_result admitted.1 enabled φ ψ).trans
        ((and_congr Iff.rfl sameTerms).trans (supports_result admittedG.1 admittedG.2.1 φ ψ).symm))).trans
        (supports_present_eq present.symm φ ψ)
  exact (rename_congruent invariantRename π ⟨Q, f.result X s⟩).trans
    (modulo_congruent invariantModulo Q modulo)

variable (r p)

/-- **Reading a row is taking it and making it again**, with infinitely many identities, beside
every program and at every state. -/
theorem readTakeMake_congruent [Infinite O]
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (invariantModulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    (Q : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨Q ∪ {withRead r p}, s⟩ ⟨Q ∪ {withTakeMake r p}, s⟩ := by
  have forward : Answers X O E obs ({withRead r p} : Program Tm) {withTakeMake r p} := by
    rintro s ⟨rule, member, ext, ι, ⟨tl, rd, ml⟩, seen⟩ admitted
    have isRule : rule = withRead r p := member
    subst rule
    have readLength : 1 = rd.length := admitted.1.2.2.2.2.1
    obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp readLength.symm
    obtain ⟨m, fresh⟩ := Infinite.exists_notMem_finset (s.present ∪ ml.toFinset)
    have mFresh : m ∉ s.present := fun inside => fresh (Finset.mem_union_left _ inside)
    have mNew : m ∉ ml := fun inside => fresh (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))
    obtain ⟨admitsIff, results⟩ := readTakeMake_core (r := r) (p := p) (s := s) invariantRename
      invariantModulo ext ι tl ml o m seen mFresh mNew
    exact ⟨takeMakeFiring r p ext ι tl ml o m seen, admitsIff.mp admitted, results admitted⟩
  have backward : Answers X O E obs ({withTakeMake r p} : Program Tm) {withRead r p} := by
    rintro s ⟨rule, member, ext, ι, ⟨tl', rd, ml'⟩, seen⟩ admitted
    have isRule : rule = withTakeMake r p := member
    subst rule
    obtain ⟨⟨-, -, mlNodup, takeLength, readLength, produceLength, -⟩, enabled, -, -⟩ := id admitted
    have takeLength' : r.body.take.length + 1 = tl'.length := by simpa using takeLength
    have produceLength' : r.body.produce.length + 1 = ml'.length := by simpa using produceLength
    have rdEmpty : rd = [] := List.length_eq_zero_iff.mp (by simpa using readLength.symm)
    subst rdEmpty
    have tlNonempty : tl' ≠ [] := fun empty => by rw [empty] at takeLength'; simp at takeLength'
    have mlNonempty : ml' ≠ [] := fun empty => by rw [empty] at produceLength'; simp at produceLength'
    obtain ⟨tl, o, rfl⟩ : ∃ tl o, tl' = tl ++ [o] :=
      ⟨tl'.dropLast, tl'.getLast tlNonempty, (List.dropLast_append_getLast tlNonempty).symm⟩
    obtain ⟨ml, m, rfl⟩ : ∃ ml m, ml' = ml ++ [m] :=
      ⟨ml'.dropLast, ml'.getLast mlNonempty, (List.dropLast_append_getLast mlNonempty).symm⟩
    have mFresh : m ∉ s.present := fun inside =>
      Finset.disjoint_left.mp enabled.fresh (by simp [Selection.commit]) inside
    have mNew : m ∉ ml := fun inside =>
      (List.nodup_append.mp mlNodup).2.2 m inside m (List.mem_singleton_self m) rfl
    obtain ⟨admitsIff, results⟩ := readTakeMake_core (r := r) (p := p) (s := s) invariantRename
      invariantModulo ext ι tl ml o m seen mFresh mNew
    have admittedF := admitsIff.mpr admitted
    exact ⟨readFiring r p ext ι tl ml o seen, admittedF, fun P => (results admittedF P).symm⟩
  have replaced := replace_congruent forward backward Q s
  rw [Set.union_comm, Set.union_comm ({withTakeMake r p} : Program Tm)] at replaced
  exact replaced

/-- **For the chosen barbs.** -/
theorem readTakeMake_congruent_mayBarb [Infinite O] (Q : Program Tm) (s : State Tm O) :
    Congruent X O E (MayBarb X) ⟨Q ∪ {withRead r p}, s⟩ ⟨Q ∪ {withTakeMake r p}, s⟩ :=
  readTakeMake_congruent r p (fun π q s => mayBarb_renameState X π q s)
    (fun related q => mayBarb_modulo related q) Q s

end Law

#print axioms relabel_append_of_mem
#print axioms relabel_append_last
#print axioms information_takeMake
#print axioms readTakeMake_core
#print axioms readTakeMake_congruent
#print axioms readTakeMake_congruent_mayBarb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
