import Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec

namespace Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec

mutual
  theorem testMatch {p : Parameters} {l r b} (d : MatchRel p l r b) : True := by
    cases d with
    | symSym => trivial
    | varVar => trivial
    | varNonVar => trivial
    | nonVarVar => trivial
    | expression d _ => exact testList d
    | groundedLeftCustom => trivial
    | groundedRightCustom => trivial
    | groundedFallback => trivial

  theorem testList {p : Parameters} {ls rs seed out}
      (d : MatchListAccRel p ls rs seed out) : True := by
    cases d with
    | nil => trivial
    | cons hm hg ht =>
        have := testMatch hm
        have := testMerge hg
        exact testList ht

  theorem testAddBinding {p : Parameters} {b v a out}
      (d : AddVarBindingRel p b v a out) : True := by
    cases d with
    | fresh => trivial
    | same => trivial
    | conflict _ _ _ hm hg =>
        have := testMatch hm
        exact testMerge hg
    | reconcile _ _ hl hg =>
        have := testList hl
        exact testMerge hg

  theorem testAddEquality {p : Parameters} {b l r out}
      (d : AddVarEqualityRel p b l r out) : True := by
    cases d with
    | consistent => trivial
    | reconcile _ _ hl hg =>
        have := testList hl
        exact testMerge hg

  theorem testConstraints {p : Parameters} {b cs out}
      (d : MergeConstraintsRel p b cs out) : True := by
    cases d with
    | nil => trivial
    | value ha ht =>
        have := testAddBinding ha
        exact testConstraints ht
    | equality ha ht =>
        have := testAddEquality ha
        exact testConstraints ht

  theorem testMerge {p : Parameters} {l r out}
      (d : MergeRel p l r out) : True := by
    cases d with
    | mk _ hf => exact testConstraints hf
end

end Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec
