import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceCommit

/-!
# The REFL correspondence at the name frame: reflection of the child's segment

`refl_reflects`: in a state where the child `l = Child(Root, x, p)` holds its token `Pending(l, Root)` and its rows
are the cells (identity, source part), each row reading as the represented part at `l` and no other row reading
at `l`: for EVERY admitted COMM at the child on two of the cells, EVERY run of coolings after it (in whatever order)
and EVERY admitted close of the reflection at its end,

* the COMM is the source's COMM on the child's bag of parts (`FiniteProgram.BagComm`), and
* the close's made row reads, at every solution, as `for(@(pPar (represented reduct)) <- x) 0 @ Root`, the
  represented reduct being the other cells' parts and the two dotted continuations.

So, from the child's heated state on, the hosting quotes exactly a one-step COMM reduct of the reflected bag, the
one its commit chose. Not covered here: the heating before the commit (any order of splits), firings at other
locations interleaved with the segment, and a commit by an inner close.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar tProc pReflect applyDot)
open MeTTaOperationsComm (psubst PSubst pvars GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (Apart)
open FiniteProgram (predot)
open OneFrame (embed)
open ReflQuotient (bagCanon groundBags)
open ReflNames (NameLaws nameAction QN QNE nameCanon)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok located)
open ReflPacking (CoolRun)
open ReflLocatedStep (res resConf commChildAt)

variable {O : Type*}

/-- **Reflection of the child's segment: commit, packing, close.** -/
theorem refl_reflects [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern)
    (reflection tk first second made₁ made₂ madeTok listener : O) (pre mid post : List (O × Pattern))
    (t u ch ch' A B : Pattern)
    (nodupCells : ((pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)).map Prod.fst).Nodup)
    (readsCells : ∀ q ∈ pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post),
      q.1 ∈ C.present ∧ q.1 ≠ tk ∧ ∀ σ : PSubst, nameAction.Models σ C.equations →
        NameLaws (psubst σ (label q.1)) (psubst σ (atLoc (predot q.2) (childLoc rootLoc x p))))
    (others : ∀ o ∈ C.present, o ≠ tk →
      o ∉ (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)).map Prod.fst →
      ∀ σ : PSubst, nameAction.Models σ C.equations →
        ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc rootLoc x p))))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label tk)) (psubst σ (pendingTok (childLoc rootLoc x p) rootLoc)))
    (inReflection : reflection ∈ C.present) (reflectionTk : reflection ≠ tk)
    (reflectionCells : reflection ∉ (pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)).map Prod.fst)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x p) rootLoc)))
    (groundCh : pvars ch = []) (groundCh' : pvars ch' = []) (canonicalCh : nameCanon ch = ch)
    (canonicalCh' : nameCanon ch' = ch')
    (unifiable : (∃ σ : PSubst, psubst σ t = psubst σ u) →
      ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true)
    (convention : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (ρ : PSubst) (committed : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (commChildAt ρ first second tk made₁ made₂ madeTok))
    {label₄ : O → Pattern} {C₄ : Configuration Pattern O} {d' : O} {rows : List Pattern}
    (run : CoolRun (childLoc rootLoc x p) rootLoc (res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label
      (resConf label C (commChildAt ρ first second tk made₁ made₂ madeTok)) madeTok label₄ C₄ d' rows)
    (ρ₅ : PSubst)
    (closed : (RuleSyntax.step QN O QNE located).Admits (s := embed label₄ C₄) (closeRootAt ρ₅ reflection d' listener)) :
    ch = ch' ∧ ∃ bs : Bindings,
      FiniteProgram.BagComm (pFor t ch A ::ₘ pFor u ch B ::ₘ ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern))
        ((FiniteProgram.parts (applyDot bs A) : Multiset Pattern) +
          (FiniteProgram.parts (applyDot bs B) : Multiset Pattern) + ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern)) ∧
      ∀ σ : PSubst, nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ reflection d' listener)).knowledge →
        NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ reflection d' listener)).label listener))
          (psubst σ (atLoc (pFor (tProc (pPar ((pre ++ mid ++ post).map (fun q => predot q.2) ++
            [predot (applyDot bs A), predot (applyDot bs B)]))) x pZero) rootLoc)) := by
  have firstIn : (first, pFor t ch A) ∈ pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) := by
    simp
  have secondIn : (second, pFor u ch' B) ∈ pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) := by
    simp
  obtain ⟨sameCh, bs, bagComm, reads⟩ := child_commit_sound label C t u ch ch' A B (childLoc rootLoc x p) rootLoc first
    second tk made₁ made₂ madeTok ρ (readsCells _ firstIn).2.2 (readsCells _ secondIn).2.2 readsToken groundCh
    groundCh' canonicalCh canonicalCh' unifiable convention foA foB groundT groundU canonicalT canonicalU committed
    ((pre ++ mid ++ post).map Prod.snd : Multiset Pattern)
  refine ⟨sameCh, bs, bagComm, ?_⟩
  -- The facts of the commit.
  obtain ⟨_, shapes, enabled, _, _, _⟩ := (RuleSyntax.admits_iff _).mp committed
  have madeNodup : [made₁, made₂, madeTok].Nodup := shapes.2.1
  have m₁ := List.nodup_cons.mp madeNodup
  have m₂ := List.nodup_cons.mp m₁.2
  have ne₁₂ : made₁ ≠ made₂ := fun same => m₁.1 (List.mem_cons.mpr (.inl same))
  have ne₁T : made₁ ≠ madeTok := fun same => m₁.1 (List.mem_cons.mpr (.inr (List.mem_singleton.mpr same)))
  have ne₂T : made₂ ≠ madeTok := fun same => m₂.1 (List.mem_singleton.mpr same)
  have freshOf : ∀ o, o = made₁ ∨ o = made₂ ∨ o = madeTok → o ∉ C.present := by
    intro o which inside
    refine Finset.disjoint_left.mp enabled.fresh ?_ inside
    rcases which with same | same | same <;> rw [same] <;> simp [commChildAt, Selection.commit]
  have notMade : ∀ o ∈ C.present, o ≠ made₁ ∧ o ≠ made₂ ∧ o ≠ madeTok := fun o inside =>
    ⟨fun same => freshOf o (.inl same) inside, fun same => freshOf o (.inr (.inl same)) inside,
      fun same => freshOf o (.inr (.inr same)) inside⟩
  -- The cells around the pair.
  have permIds : ((pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post)).map Prod.fst).Perm
      (first :: second :: (pre ++ mid ++ post).map Prod.fst) := by
    simp only [List.map_append, List.map_cons]
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    rw [← List.append_assoc]
    exact List.perm_middle
  obtain ⟨firstOut, nodupFront⟩ := List.nodup_cons.mp (permIds.nodup_iff.mp nodupCells)
  obtain ⟨secondOut, restNodup⟩ := List.nodup_cons.mp nodupFront
  have restIn : ∀ q ∈ pre ++ mid ++ post, q ∈ pre ++ (first, pFor t ch A) :: (mid ++ (second, pFor u ch' B) :: post) := by
    intro q member
    simp only [List.mem_append, List.mem_cons] at member ⊢
    rcases member with (inPre | inMid) | inPost
    · exact .inl inPre
    · exact .inr (.inr (.inl inMid))
    · exact .inr (.inr (.inr (.inr inPost)))
  have restApart : ∀ q ∈ pre ++ mid ++ post, q.1 ≠ first ∧ q.1 ≠ second := by
    intro q member
    have inside : q.1 ∈ (pre ++ mid ++ post).map Prod.fst := List.mem_map.mpr ⟨q, member, rfl⟩
    exact ⟨fun same => firstOut (List.mem_cons.mpr (.inr (same ▸ inside))), fun same => secondOut (same ▸ inside)⟩
  have back₃ : ∀ σ : PSubst,
      nameAction.Models σ (resConf label C (commChildAt ρ first second tk made₁ made₂ madeTok)).equations →
      nameAction.Models σ C.equations :=
    fun σ solved => commit_back label C ρ first second tk made₁ made₂ madeTok solved
  have keep₃ : ∀ o ∈ C.present, o ≠ first → o ≠ second → o ≠ tk →
      o ∈ (resConf label C (commChildAt ρ first second tk made₁ made₂ madeTok)).present ∧
      (res label C (commChildAt ρ first second tk made₁ made₂ madeTok)).label o = label o := by
    intro o inside ne₁ ne₂ neT
    obtain ⟨n₁, n₂, n₃⟩ := notMade o inside
    exact ⟨(commit_present label C ρ first second tk made₁ made₂ madeTok o).mpr (.inl ⟨inside, ne₁, ne₂, neT⟩),
      commit_label_old label C ρ first second tk made₁ made₂ madeTok n₁ n₂ n₃⟩
  -- The cells after the commit.
  let cells' : List (O × Pattern) := (pre ++ mid ++ post).map (fun q => (q.1, predot q.2)) ++
    [(made₁, predot (applyDot bs A)), (made₂, predot (applyDot bs B))]
  have cellsSnd : cells'.map Prod.snd = (pre ++ mid ++ post).map (fun q => predot q.2) ++
      [predot (applyDot bs A), predot (applyDot bs B)] := by
    simp [cells', Function.comp_def]
  have cellsFst : cells'.map Prod.fst = (pre ++ mid ++ post).map Prod.fst ++ [made₁, made₂] := by
    simp [cells', Function.comp_def]
  have restIds : ∀ o ∈ (pre ++ mid ++ post).map Prod.fst, o ∈ C.present ∧ o ≠ first ∧ o ≠ second ∧ o ≠ tk := by
    intro o inside
    obtain ⟨q, inQ, rfl⟩ := List.mem_map.mp inside
    have facts := readsCells q (restIn q inQ)
    exact ⟨facts.1, (restApart q inQ).1, (restApart q inQ).2, facts.2.1⟩
  have nodup' : (cells'.map Prod.fst).Nodup := by
    rw [cellsFst]
    refine List.nodup_append.mpr ⟨restNodup, by simp [ne₁₂], fun a inA b inB same => ?_⟩
    have aIn := (restIds a inA).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inB
    rcases inB with isM₁ | isM₂
    · exact (notMade a aIn).1 (same.trans isM₁)
    · exact (notMade a aIn).2.1 (same.trans isM₂)
  have cellsCases : ∀ q ∈ cells', (∃ q₀ ∈ pre ++ mid ++ post, q = (q₀.1, predot q₀.2)) ∨
      q = (made₁, predot (applyDot bs A)) ∨ q = (made₂, predot (applyDot bs B)) := by
    intro q member
    rcases List.mem_append.mp member with inMap | inMade
    · obtain ⟨q₀, inQ₀, same⟩ := List.mem_map.mp inMap
      exact .inl ⟨q₀, inQ₀, same.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inMade
      rcases inMade with isM₁ | isM₂
      · exact .inr (.inl isM₁)
      · exact .inr (.inr isM₂)
  have madeIn₃ : ∀ o, o = made₁ ∨ o = made₂ ∨ o = madeTok →
      o ∈ (resConf label C (commChildAt ρ first second tk made₁ made₂ madeTok)).present :=
    fun o which => (commit_present label C ρ first second tk made₁ made₂ madeTok o).mpr (.inr which)
  have reflectionApart : reflection ≠ first ∧ reflection ≠ second := by
    refine ⟨fun same => reflectionCells ?_, fun same => reflectionCells ?_⟩
    · rw [same]
      exact List.mem_map.mpr ⟨_, firstIn, rfl⟩
    · rw [same]
      exact List.mem_map.mpr ⟨_, secondIn, rfl⟩
  obtain ⟨reflectionIn₃, reflectionLabel₃⟩ :=
    keep₃ reflection inReflection reflectionApart.1 reflectionApart.2 reflectionTk
  have reads' := refl_close_reads x p reflection listener ρ₅ run closed cells' nodup'
    (fun q member => by
      rcases cellsCases q member with ⟨q₀, inQ₀, rfl⟩ | isM₁ | isM₂
      · dsimp only
        obtain ⟨present₀, notTk, reads₀⟩ := readsCells q₀ (restIn q₀ inQ₀)
        obtain ⟨in₃, label₃⟩ := keep₃ q₀.1 present₀ (restApart q₀ inQ₀).1 (restApart q₀ inQ₀).2 notTk
        refine ⟨in₃, (notMade q₀.1 present₀).2.2, fun σ solved => ?_⟩
        rw [label₃]
        exact reads₀ σ (back₃ σ solved)
      · rw [isM₁]
        exact ⟨madeIn₃ made₁ (.inl rfl), ne₁T, fun σ solved => (reads σ solved).2.1⟩
      · rw [isM₂]
        exact ⟨madeIn₃ made₂ (.inr (.inl rfl)), ne₂T, fun σ solved => (reads σ solved).2.2.1⟩)
    (fun o inside notTok notCell σ solved y same => by
      rcases (commit_present label C ρ first second tk made₁ made₂ madeTok o).mp inside with
        ⟨inC, ne₁, ne₂, neT⟩ | isM₁ | isM₂ | isT
      · rw [(keep₃ o inC ne₁ ne₂ neT).2] at same
        refine others o inC neT ?_ σ (back₃ σ solved) y same
        intro inCells
        obtain ⟨q, inQ, rfl⟩ := List.mem_map.mp inCells
        simp only [List.mem_append, List.mem_cons] at inQ
        rcases inQ with inPre | isFirst | inMid | isSecond | inPost
        · exact notCell (by
            rw [cellsFst]
            exact List.mem_append_left _ (List.mem_map.mpr ⟨q, by simp [inPre], rfl⟩))
        · exact ne₁ (by rw [isFirst])
        · exact notCell (by
            rw [cellsFst]
            exact List.mem_append_left _ (List.mem_map.mpr ⟨q, by simp [inMid], rfl⟩))
        · exact ne₂ (by rw [isSecond])
        · exact notCell (by
            rw [cellsFst]
            exact List.mem_append_left _ (List.mem_map.mpr ⟨q, by simp [inPost], rfl⟩))
      · exact notCell (by rw [cellsFst, isM₁]; simp)
      · exact notCell (by rw [cellsFst, isM₂]; simp)
      · exact notTok isT)
    reflectionIn₃ (fun same => freshOf reflection (.inr (.inr same)) inReflection)
    (by
      rw [cellsFst]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun inside => reflectionCells ?_, fun same => freshOf reflection (.inl same) inReflection,
        fun same => freshOf reflection (.inr (.inl same)) inReflection⟩
      obtain ⟨q, inQ, same⟩ := List.mem_map.mp inside
      exact List.mem_map.mpr ⟨q, restIn q inQ, same⟩)
    (fun σ solved => by
      rw [reflectionLabel₃]
      exact readsReflection σ (back₃ σ solved))
    (fun σ solved => (reads σ solved).2.2.2)
  intro σ solved
  have reading := reads' σ solved
  rw [cellsSnd] at reading
  exact reading

#print axioms refl_reflects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
