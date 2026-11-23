import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec

/-!
# Ordered pattern witnesses

A match trace records the support atom selected at every pattern position
and threads the substitution. Compatibility matching reads the trace's
finite support. Multiple selections of one atom remain visible in the trace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive PatternMatchTrace (space : Space) :
    Subst → List Atom → List Atom → Subst → Prop where
  | nil (substitution : Subst) : PatternMatchTrace space substitution [] [] substitution
  | cons {first next result : Subst} {pattern atom : Atom} {patterns atoms : List Atom}
      (present : atom ∈ space) (matched : matchAtom first pattern atom = some next)
      (rest : PatternMatchTrace space next patterns atoms result) :
      PatternMatchTrace space first (pattern :: patterns) (atom :: atoms) result

private theorem support_cons (seen : Finset Atom) (atom : Atom) (rest : List Atom) :
    (seen ∪ {atom}) ∪ rest.toFinset = seen ∪ (atom :: rest).toFinset := by
  ext candidate
  simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]

private theorem matchPattern_go_mem_iff
    (space : Space) (patterns : List Atom) (first result : Subst)
    (seen support : Finset Atom) :
    (result, support) ∈ matchPattern.go space patterns first seen ↔
      ∃ atoms, PatternMatchTrace space first patterns atoms result ∧
        support = seen ∪ atoms.toFinset := by
  induction patterns generalizing first seen with
  | nil =>
      constructor
      · intro member
        simp only [matchPattern.go, List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact ⟨[], .nil _, by simp⟩
      · rintro ⟨atoms, trace, rfl⟩
        cases trace
        simp [matchPattern.go]
  | cons pattern patterns induction =>
      simp only [matchPattern.go, List.mem_flatMap]
      constructor
      · rintro ⟨⟨middle, atom⟩, step, tail⟩
        obtain ⟨present, matched⟩ := matchOneInSpace_spec first pattern space middle atom step
        obtain ⟨atoms, trace, exactSupport⟩ := (induction middle (seen ∪ {atom})).mp tail
        exact ⟨atom :: atoms, .cons present matched trace,
          exactSupport.trans (support_cons seen atom atoms)⟩
      · rintro ⟨atoms, trace, rfl⟩
        cases trace with
        | cons present matched trace =>
            refine ⟨(_, _), matchOneInSpace_mem first pattern space _ present _ matched, ?_⟩
            exact (induction _ _).mpr ⟨_, trace, (support_cons _ _ _).symm⟩

theorem mem_matchPattern_iff
    (space : Space) (pattern : Pattern) (first result : Subst) (support : Finset Atom) :
    (result, support) ∈ matchPattern first space pattern ↔
      ∃ atoms, PatternMatchTrace space first pattern.atoms atoms result ∧
        support = atoms.toFinset := by
  simp only [matchPattern, matchPattern_go_mem_iff, Finset.empty_union]

theorem mem_matchInputSpec_compat_of_trace
    {space : Space} {pattern : Pattern} {first result : Subst} {atoms : List Atom}
    (matched : PatternMatchTrace space first pattern.atoms atoms result) :
    result ∈ (matchInputSpec first space (.compat pattern)).map Prod.fst :=
  List.mem_map.mpr ⟨(result, atoms.toFinset),
    (mem_matchPattern_iff _ _ _ _ _).mpr ⟨atoms, matched, rfl⟩, rfl⟩

theorem mem_readCopyAtom_iff (space : Space) (directive candidate : Atom) :
    candidate ∈ readCopyAtom space directive ↔ candidate ∈ space ∨ candidate = directive := by
  by_cases same : candidate = directive
  · simp [readCopyAtom, same]
  · simp [readCopyAtom, consumeAtom, Finset.mem_erase, same]

theorem mem_readCopyAtom_of_mem {space : Space} {directive candidate : Atom}
    (member : candidate ∈ space) : candidate ∈ readCopyAtom space directive :=
  (mem_readCopyAtom_iff _ _ _).mpr (Or.inl member)

section Controls

private def firstFact : Atom := .symbol "first"
private def otherFact : Atom := .symbol "other"
private def repeatedVariable : Atom := .var "x"
private def bound : Subst := [("x", firstFact)]

example : PatternMatchTrace {firstFact} [] [repeatedVariable, repeatedVariable]
    [firstFact, firstFact] bound :=
  .cons (by simp) rfl (.cons (by simp) rfl (.nil _))

example : ¬ PatternMatchTrace {firstFact, otherFact} [] [repeatedVariable, repeatedVariable]
    [firstFact, otherFact] bound := by
  intro trace
  cases trace with
  | cons _ first tail =>
      change some bound = _ at first
      obtain rfl := Option.some.inj first
      cases tail with
      | cons _ conflicting _ =>
          simp [matchAtom, repeatedVariable, bound, Subst.lookup, firstFact, otherFact] at conflicting

end Controls

end Mettapedia.Languages.ProcessCalculi.MORK
