import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Pure rho boundary on the shared pattern carrier

The strict rho grammar is derived from `rhoReflectivePresentation`.  Its
parallel constructor is a bag, so a derived rho process cannot contain the
finite-set constructor used by the optional lookahead extension.

The older low-level reduction relation is defined on the larger shared
`Pattern` carrier and therefore has contextual constructors for sets.  The
theorems below show that those constructors are unreachable from derived pure
rho syntax: semantic COMM substitution and low-level reduction preserve the
`hashSet`-free fragment.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-! ## Derived syntax stays in the paper carrier -/

/-- Every name admitted by the authored rho presentation is `hashSet`-free. -/
theorem rhoNameWellSorted_hashSetFree
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name) :
    HashSetFree name := by
  apply NameWellSorted.rec
    (presentation := rhoReflectivePresentation) (free := free) (t := typed)
    (motive_1 := fun _ name _ => HashSetFree name)
    (motive_2 := fun _ process _ => HashSetFree process)
    (motive_3 := fun _ processes _ => HashSetFreeList processes)
  all_goals
    intros
    simp_all [HashSetFree, HashSetFreeList, rhoReflectivePresentation]

/-- Every process admitted by the authored rho presentation is `hashSet`-free. -/
theorem rhoProcWellSorted_hashSetFree
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process) :
    HashSetFree process := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation) (free := free) (t := typed)
    (motive_1 := fun _ name _ => HashSetFree name)
    (motive_2 := fun _ process _ => HashSetFree process)
    (motive_3 := fun _ processes _ => HashSetFreeList processes)
  all_goals
    intros
    simp_all [HashSetFree, HashSetFreeList, rhoReflectivePresentation]

/-- List form of `rhoProcWellSorted_hashSetFree`. -/
theorem rhoProcListWellSorted_hashSetFree
    {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted rhoReflectivePresentation free bound processes) :
    HashSetFreeList processes := by
  apply ProcListWellSorted.rec
    (presentation := rhoReflectivePresentation) (free := free) (t := typed)
    (motive_1 := fun _ name _ => HashSetFree name)
    (motive_2 := fun _ process _ => HashSetFree process)
    (motive_3 := fun _ processes _ => HashSetFreeList processes)
  all_goals
    intros
    simp_all [HashSetFree, HashSetFreeList, rhoReflectivePresentation]

/-! ## Semantic substitution preserves the boundary -/

mutual
  /-- Process normalization cannot introduce a finite-set node. -/
  theorem hashSetFree_semanticNormalizeProc :
    ∀ {process : Pattern}, HashSetFree process →
        HashSetFree (semanticNormalizeProc process)
    | process, free => by
        cases process using
            semanticNormalizeProc.fun_cases_unfolding with
        | case1 index => simpa [semanticNormalizeProc] using free
        | case2 name => simpa [semanticNormalizeProc] using free
        | case3 channel payload =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact ⟨hashSetFree_semanticNormalizeName free.1,
              hashSetFree_semanticNormalizeProc free.2.1, trivial⟩
        | case4 channel body =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact ⟨hashSetFree_semanticNormalizeName free.1,
              hashSetFree_semanticNormalizeProc free.2.1, trivial⟩
        | case5 name =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact ⟨hashSetFree_semanticNormalizeName free.1, trivial⟩
        | case6 quoted =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact ⟨hashSetFree_semanticNormalizeProc free.1, trivial⟩
        | case7 binderName body =>
            have bodyFree : HashSetFree body := by
              simpa only [HashSetFree] using free
            exact hashSetFree_semanticNormalizeProc bodyFree
        | case8 arity binderNames body =>
            have bodyFree : HashSetFree body := by
              simpa only [HashSetFree] using free
            exact hashSetFree_semanticNormalizeProc bodyFree
        | case9 body replacement =>
            simp only [HashSetFree] at free ⊢
            exact ⟨hashSetFree_semanticNormalizeProc free.1,
              hashSetFree_semanticNormalizeProc free.2⟩
        | case10 collectionType elements rest =>
            cases collectionType with
            | hashSet => exact absurd free (by simp [HashSetFree])
            | hashBag =>
                simp only [HashSetFree] at free ⊢
                exact hashSetFree_semanticNormalizeProcList free
            | vec =>
                simp only [HashSetFree] at free ⊢
                exact hashSetFree_semanticNormalizeProcList free
        | case11 constructor _ _ _ _ _ _ _ _ _ =>
            simpa [semanticNormalizeProc] using free

  /-- List form of `hashSetFree_semanticNormalizeProc`. -/
  theorem hashSetFree_semanticNormalizeProcList :
      ∀ {processes : List Pattern}, HashSetFreeList processes →
        HashSetFreeList (semanticNormalizeProcList processes)
    | [], _ => by simp [semanticNormalizeProcList, HashSetFreeList]
    | process :: processes, free => by
        simp only [HashSetFreeList] at free
        rw [semanticNormalizeProcList]
        simp only [HashSetFreeList]
        exact ⟨hashSetFree_semanticNormalizeProc free.1,
          hashSetFree_semanticNormalizeProcList free.2⟩

  /-- Name normalization cannot introduce a finite-set node. -/
  theorem hashSetFree_semanticNormalizeName :
    ∀ {name : Pattern}, HashSetFree name →
        HashSetFree (semanticNormalizeName name)
    | name, free => by
        cases name using
            semanticNormalizeName.fun_cases_unfolding with
        | case1 index => simpa [semanticNormalizeName] using free
        | case2 name => simpa [semanticNormalizeName] using free
        | case3 inner =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact hashSetFree_semanticNormalizeName free.1.1
        | case4 process _ =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact ⟨hashSetFree_semanticNormalizeProc free.1, trivial⟩
        | case5 constructor _ _ _ =>
            simpa [semanticNormalizeName] using free
end

/-- Name substitution returns either the supplied pure name or a normalized
pure source name. -/
theorem hashSetFree_semanticSubstName
    {depth : Nat} {replacementName name : Pattern}
    (replacementFree : HashSetFree replacementName)
    (nameFree : HashSetFree name) :
    HashSetFree (semanticSubstName depth replacementName name) := by
  have normalizedFree := hashSetFree_semanticNormalizeName nameFree
  unfold semanticSubstName semanticSubstNameMark
  dsimp only
  split <;> (try split) <;> simp_all [HashSetFree]

mutual
  /-- Paper-faithful process substitution preserves the pure carrier when its
  replacement name is pure. -/
  theorem hashSetFree_semanticSubstProc
      {replacementName : Pattern} (replacementFree : HashSetFree replacementName) :
      ∀ {depth : Nat} {process : Pattern}, HashSetFree process →
        HashSetFree (semanticSubstProc depth replacementName process)
    | depth, process, free => by
        cases process using
            semanticSubstProc.fun_cases_unfolding depth replacementName with
        | case1 index => exact replacementFree
        | case2 index _ => exact free
        | case3 name => exact free
        | case4 quoted => exact free
        | case5 name process substitution =>
            have sourceNameFree : HashSetFree name := by
              simpa [HashSetFree, HashSetFreeList] using free
            have substitutedNameFree :
                HashSetFree (semanticSubstName depth replacementName name) :=
              hashSetFree_semanticSubstName
                (depth := depth) replacementFree sourceNameFree
            have substitutedName :
                semanticSubstName depth replacementName name =
                  .apply "NQuote" [process] := by
              simp [semanticSubstName, substitution]
            rw [substitutedName] at substitutedNameFree
            simpa [HashSetFree, HashSetFreeList] using substitutedNameFree
        | case6 name substituted matched substitution notQuote =>
            have sourceNameFree : HashSetFree name := by
              simpa [HashSetFree, HashSetFreeList] using free
            have substitutedNameFree :
                HashSetFree (semanticSubstName depth replacementName name) :=
              hashSetFree_semanticSubstName
                (depth := depth) replacementFree sourceNameFree
            have substitutedName :
                substituted = semanticSubstName depth replacementName name := by
              simp [semanticSubstName, substitution]
            subst substitutedName
            simp only [HashSetFree, HashSetFreeList]
            exact ⟨substitutedNameFree, trivial⟩
        | case7 channel payload =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact ⟨hashSetFree_semanticSubstName replacementFree free.1,
              hashSetFree_semanticSubstProc replacementFree free.2.1, trivial⟩
        | case8 channel body =>
            simp only [HashSetFree, HashSetFreeList] at free ⊢
            exact ⟨hashSetFree_semanticSubstName replacementFree free.1,
              hashSetFree_semanticSubstProc replacementFree free.2.1, trivial⟩
        | case9 binderName body =>
            have bodyFree : HashSetFree body := by
              simpa only [HashSetFree] using free
            exact hashSetFree_semanticSubstProc
              (depth := depth + 1) replacementFree bodyFree
        | case10 arity binderNames body =>
            have bodyFree : HashSetFree body := by
              simpa only [HashSetFree] using free
            exact hashSetFree_semanticSubstProc
              (depth := depth + arity) replacementFree bodyFree
        | case11 body replacement =>
            simp only [HashSetFree] at free ⊢
            exact ⟨hashSetFree_semanticSubstProc replacementFree free.1,
              hashSetFree_semanticSubstProc replacementFree free.2⟩
        | case12 collectionType elements rest =>
            cases collectionType with
            | hashSet => exact absurd free (by simp [HashSetFree])
            | hashBag =>
                simp only [HashSetFree] at free ⊢
                exact hashSetFree_semanticSubstProcList replacementFree free
            | vec =>
                simp only [HashSetFree] at free ⊢
                exact hashSetFree_semanticSubstProcList replacementFree free
        | case13 _ _ _ _ _ _ _ _ _ _ => exact free

  /-- List form of `hashSetFree_semanticSubstProc`. -/
  theorem hashSetFree_semanticSubstProcList
      {replacementName : Pattern} (replacementFree : HashSetFree replacementName) :
      ∀ {depth : Nat} {processes : List Pattern}, HashSetFreeList processes →
        HashSetFreeList (semanticSubstProcList depth replacementName processes)
    | _, [], _ => by simp [semanticSubstProcList, HashSetFreeList]
    | depth, process :: processes, free => by
        simp only [HashSetFreeList] at free
        rw [semanticSubstProcList]
        simp only [HashSetFreeList]
        exact ⟨hashSetFree_semanticSubstProc replacementFree free.1,
          hashSetFree_semanticSubstProcList replacementFree free.2⟩
end

/-- Strict COMM substitution preserves the pure carrier. -/
theorem hashSetFree_semanticCommSubst
    {body payload : Pattern} (bodyFree : HashSetFree body)
    (payloadFree : HashSetFree payload) :
    HashSetFree (semanticCommSubst body payload) := by
  unfold semanticCommSubst
  refine hashSetFree_semanticSubstProc ?_ bodyFree
  simp only [HashSetFree, HashSetFreeList]
  exact ⟨hashSetFree_semanticNormalizeProc payloadFree, trivial⟩

/-! ## The ambient low-level relation is conservative on pure syntax -/

/-- Low-level reduction cannot leave the pure carrier.  The set-context cases
are impossible because their sources are not `hashSet`-free. -/
theorem hashSetFree_of_reduces :
    ∀ {source target : Pattern}, Reduces source target →
      HashSetFree source → HashSetFree target
  | _, _, .comm, sourceFree => by
      simp only [HashSetFree, List.cons_append, List.nil_append,
        HashSetFreeList] at sourceFree ⊢
      refine ⟨?_, sourceFree.2.2⟩
      have payloadFree : HashSetFree _ := sourceFree.1.2.1
      have bodyFree : HashSetFree _ := sourceFree.2.1.2.1
      exact hashSetFree_semanticCommSubst bodyFree payloadFree
  | _, _, .equiv sourceCongruence reduction targetCongruence, sourceFree => by
      have representativeFree :=
        (hashSetFree_iff_of_structuralCongruence sourceCongruence).mp sourceFree
      exact (hashSetFree_iff_of_structuralCongruence targetCongruence).mp
        (hashSetFree_of_reduces reduction representativeFree)
  | _, _, .par reduction, sourceFree => by
      simp only [HashSetFree, HashSetFreeList] at sourceFree ⊢
      exact ⟨hashSetFree_of_reduces reduction sourceFree.1, sourceFree.2⟩
  | _, _, .par_any reduction, sourceFree => by
      simp only [HashSetFree] at sourceFree ⊢
      rw [hashSetFreeList_append_iff] at sourceFree ⊢
      refine ⟨?_, sourceFree.2⟩
      rw [hashSetFreeList_append_iff] at sourceFree ⊢
      refine ⟨sourceFree.1.1, ?_⟩
      simp only [HashSetFreeList] at sourceFree ⊢
      exact ⟨hashSetFree_of_reduces reduction sourceFree.1.2.1, trivial⟩
  | _, _, .par_set _, sourceFree => by
      simp only [HashSetFree] at sourceFree
  | _, _, .par_set_any _, sourceFree => by
      simp only [HashSetFree] at sourceFree

/-- A reduction beginning at syntax derived from the authored rho
presentation remains inside the paper carrier. -/
theorem rhoReduces_from_derived_stays_pure
    {free : FreeSortContext} {bound : List String} {source target : Pattern}
    (sourceTyped :
      ProcWellSorted rhoReflectivePresentation free bound source)
    (reduction : Reduces source target) : HashSetFree target :=
  hashSetFree_of_reduces reduction
    (rhoProcWellSorted_hashSetFree sourceTyped)

/-! ## Executable boundary witnesses -/

/-- The optional finite-set context is outside the syntax derived from pure
rho's authored presentation. -/
theorem rhoSetProcess_not_wellSorted
    (free : FreeSortContext) (bound : List String) :
    ¬ ProcWellSorted rhoReflectivePresentation free bound
      (.collection .hashSet [.apply "PZero" []] none) := by
  intro typed
  cases typed

/-- Positive control: the same component in the declared parallel bag is a
pure derived process. -/
example : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
    (.collection .hashBag [.apply "PZero" []] none) :=
  .parallel (.cons .unit .nil)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
