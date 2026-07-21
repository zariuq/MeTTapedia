import Mettapedia.GSLT.Parsing.GuardCorrespondence

/-!
# Packed scannerless parse forests

This module gives the GLL/GLR shared-forest boundary an explicit semantics.
Symbol nodes are keyed by category and exact input span.  Each packed family
records one admitted source rule and references terminal leaves or shared
symbol nodes.  A forest represents a certificate precisely when every family
chosen by that certificate occurs in the shared store.

The results below separate two obligations cleanly: forest representation and
engine scheduling.  Packed replay is source-sound, every compiled derivation
has a finite packable witness, and any forest satisfying the explicit
completeness predicate has exactly the source result may-set.  Establishing
that a concrete GLL or GLR worklist always satisfies that predicate is a
subsequent algorithm theorem.
-/

namespace Mettapedia.GSLT.Parsing.PackedForest

open CompilerCorrespondence GuardCorrespondence

structure NodeKey where
  category : Category
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

inductive ChildRef where
  | terminal (codepoint : Codepoint) (start stop : Nat)
  | node (key : NodeKey)
  deriving DecidableEq, Repr

structure Family where
  parent : NodeKey
  sourceRule : RuleId
  children : List ChildRef
  deriving DecidableEq, Repr

structure Forest where
  roots : List NodeKey
  families : List Family
  deriving DecidableEq, Repr

def certificateKey : Certificate → Option NodeKey
  | .terminal _ _ _ => none
  | .node _ category start stop _ =>
      some { category := category, start := start, stop := stop }

def certificateRef : Certificate → ChildRef
  | .terminal codepoint start stop => .terminal codepoint start stop
  | .node _ category start stop _ =>
      .node { category := category, start := start, stop := stop }

def certificateFamily : Certificate → Option Family
  | .terminal _ _ _ => none
  | .node sourceRule category start stop children =>
      some {
        parent := { category := category, start := start, stop := stop }
        sourceRule := sourceRule
        children := children.map certificateRef }

mutual
  def certificateFamilies : Certificate → List Family
    | .terminal _ _ _ => []
    | certificate@(.node _ _ _ _ children) =>
        (certificateFamily certificate).toList ++
          certificatesFamilies children

  def certificatesFamilies : List Certificate → List Family
    | [] => []
    | certificate :: certificates =>
        certificateFamilies certificate ++ certificatesFamilies certificates
end

/-- Canonical finite packing of a certificate collection.  Equal roots and
families are shared by `eraseDups`; distinct alternatives at one node remain
distinct families. -/
def packCertificates (certificates : List Certificate) : Forest :=
  { roots := (certificates.filterMap certificateKey).eraseDups
    families := (certificatesFamilies certificates).eraseDups }

/-- Every family selected by one certificate occurs in the packed store. -/
def Unfolds (forest : Forest) (certificate : Certificate) : Prop :=
  ∀ family, family ∈ certificateFamilies certificate →
    family ∈ forest.families

/-- The certificate also begins at an exact root of the forest. -/
def RootUnfolds (forest : Forest) (certificate : Certificate) : Prop :=
  ∃ key, certificateKey certificate = some key ∧
    key ∈ forest.roots ∧ Unfolds forest certificate

theorem member_packCertificates_unfolds
    {certificates : List Certificate} {certificate : Certificate}
    (member : certificate ∈ certificates)
    (isNode : ∃ key, certificateKey certificate = some key) :
    RootUnfolds (packCertificates certificates) certificate := by
  obtain ⟨key, keyEquation⟩ := isNode
  refine ⟨key, keyEquation, ?_, ?_⟩
  · simp only [packCertificates, List.mem_eraseDups,
      List.mem_filterMap]
    exact ⟨certificate, member, keyEquation⟩
  · intro family familyMember
    simp only [packCertificates, List.mem_eraseDups]
    induction certificates with
    | nil => contradiction
    | cons head tail inductionHypothesis =>
        simp only [List.mem_cons] at member
        simp only [certificatesFamilies, List.mem_append]
        rcases member with rfl | tailMember
        · exact Or.inl familyMember
        · exact Or.inr (inductionHypothesis tailMember)

/-- A packed witness is accepted only together with exact-span certificate
replay against the compiled grammar. -/
def PackedReplays (forest : Forest)
    (presentation : GuardCorrespondence.SourcePresentation)
    (input : List Codepoint) (certificate : Certificate)
    (tree : ParseTree) : Prop :=
  RootUnfolds forest certificate ∧
    RootCertificateReplays presentation input certificate tree

/-- Exact root replay for an arbitrary admitted compiled grammar.  This is the
trust boundary used by compacted backends, whose finite terminal sets need not
be expressible as one source rule. -/
def GrammarRootCertificateReplays
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (certificate : Certificate)
    (tree : ParseTree) : Prop :=
  CertificateReplays grammar input certificate grammar.start
      0 input.length tree ∧
    certificate.start = 0 ∧ certificate.stop = input.length

/-- A packed certificate is checked both against the forest and directly
against the arbitrary admitted compiled grammar. -/
def GrammarPackedReplays (forest : Forest)
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (certificate : Certificate)
    (tree : ParseTree) : Prop :=
  RootUnfolds forest certificate ∧
    GrammarRootCertificateReplays grammar input certificate tree

theorem grammar_packed_replay_sound
    {forest : Forest} {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {certificate : Certificate} {tree : ParseTree}
    (replay : GrammarPackedReplays forest grammar input certificate tree) :
    CompiledDerivesAt grammar input grammar.start 0 input.length tree :=
  certificate_replay_compiled_sound replay.2.1

/-- Packed replay cannot invent a source parse. -/
theorem packed_replay_sound
    {forest : Forest}
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {certificate : Certificate} {tree : ParseTree}
    (replay : PackedReplays forest presentation input certificate tree) :
    SourceDerivesAt presentation input presentation.start
      0 input.length tree :=
  certificate_replay_sound replay.2

theorem compiled_derivation_has_certificate
    {grammar : GuardCorrespondence.CompiledGrammar}
    {fullInput category start stop tree}
    (derivation : CompiledDerivesAt grammar fullInput category start stop tree) :
    ∃ certificate, CertificateReplays grammar fullInput certificate
      category start stop tree := by
  exact CompiledDerivesAt.rec
    (motive_1 := fun category start stop tree _ =>
      ∃ certificate, CertificateReplays grammar fullInput certificate
        category start stop tree)
    (motive_2 := fun symbols start stop trees _ =>
      ∃ certificates, CertificateBodyReplays grammar fullInput symbols
        start stop certificates trees)
    (motive_3 := fun guards cursor _ =>
      CompiledGuardsHold grammar fullInput guards cursor)
    (fun {start} {stop} {children} production member _ _ bodyIH guardsIH => by
      obtain ⟨certificates, bodyReplay⟩ := bodyIH
      exact ⟨Certificate.node production.sourceRule production.category
        start stop certificates,
        CertificateReplays.node production member bodyReplay guardsIH⟩)
    (by exact ⟨[], CertificateBodyReplays.nil⟩)
    (fun {start} {codepoint} {symbols} {stop} {children}
        lookup _ restIH => by
      obtain ⟨certificates, restReplay⟩ := restIH
      exact ⟨Certificate.terminal codepoint start (start + 1) :: certificates,
        CertificateBodyReplays.terminal lookup restReplay⟩)
    (fun {start} {codepoint} {symbols} {stop} {children}
        lookup _ restIH => by
      obtain ⟨certificates, restReplay⟩ := restIH
      exact ⟨Certificate.terminal codepoint start (start + 1) :: certificates,
        CertificateBodyReplays.anyTerminal lookup restReplay⟩)
    (fun {start} {codepoint} {_} {symbols} {stop} {children}
        lookup member _ restIH => by
      obtain ⟨certificates, restReplay⟩ := restIH
      exact ⟨Certificate.terminal codepoint start (start + 1) :: certificates,
        CertificateBodyReplays.oneOfTerminal lookup member restReplay⟩)
    (fun {category} {start} {middle} {tree} {symbols} {stop} {children}
        _ _ headIH restIH => by
      obtain ⟨headCertificate, headReplay⟩ := headIH
      obtain ⟨certificates, restReplay⟩ := restIH
      cases headReplay with
      | node production member body guards =>
          exact ⟨_ :: certificates, CertificateBodyReplays.nonterminal
              (CertificateReplays.node production member body guards)
              restReplay⟩)
    (by exact CompiledGuardsHold.nil)
    (fun endEq _ restIH => CompiledGuardsHold.atEnd endEq restIH)
    (fun lookup member _ restIH =>
      CompiledGuardsHold.nextIn lookup member restIH)
    (fun allowed endEq _ restIH =>
      CompiledGuardsHold.nextInEof allowed endEq restIH)
    (fun witness _ _ restIH =>
      CompiledGuardsHold.lookahead witness restIH)
    derivation

private theorem certificateReplay_spans
    {grammar : GuardCorrespondence.CompiledGrammar}
    {fullInput certificate category start stop tree}
    (replay : CertificateReplays grammar fullInput certificate
      category start stop tree) :
    certificate.start = start ∧ certificate.stop = stop := by
  cases replay
  exact ⟨rfl, rfl⟩

private theorem certificateReplay_hasKey
    {grammar : GuardCorrespondence.CompiledGrammar}
    {fullInput certificate category start stop tree}
    (replay : CertificateReplays grammar fullInput certificate
      category start stop tree) :
    ∃ key, certificateKey certificate = some key := by
  cases replay with
  | node production member body guards =>
      exact ⟨{ category := production.category, start := start, stop := stop },
        rfl⟩

/-- Every source result has a finite tree-shaped SPPF witness.  Sharing several
such witnesses with `packCertificates` preserves every alternative. -/
theorem source_derivation_has_packed_witness
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint}
    {tree : ParseTree}
    (derivation : SourceDerivesAt presentation input presentation.start
      0 input.length tree) :
    ∃ forest certificate,
      PackedReplays forest presentation input certificate tree := by
  have compiled := compile_preserves derivation
  obtain ⟨certificate, certificateReplay⟩ :=
    compiled_derivation_has_certificate compiled
  let forest := packCertificates [certificate]
  have rootKey := certificateReplay_hasKey certificateReplay
  have spans := certificateReplay_spans certificateReplay
  refine ⟨forest, certificate, ?_, ?_⟩
  · exact member_packCertificates_unfolds (by simp) rootKey
  · exact ⟨certificateReplay, spans.1, spans.2⟩

def grammarPackedResults (forest : Forest)
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : Set ParseTree :=
  { tree | ∃ certificate,
      GrammarPackedReplays forest grammar input certificate tree }

/-- The scheduler obligation for an arbitrary admitted compiled grammar. -/
def GrammarComplete (forest : Forest)
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : Prop :=
  ∀ tree, CompiledDerivesAt grammar input grammar.start 0 input.length tree →
    ∃ certificate,
      GrammarPackedReplays forest grammar input certificate tree

theorem grammarPackedResults_subset_grammarResults
    (forest : Forest) (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) :
    grammarPackedResults forest grammar input ⊆
      GuardCorrespondence.grammarResults grammar input := by
  intro tree replay
  obtain ⟨certificate, accepted⟩ := replay
  exact grammar_packed_replay_sound accepted

theorem grammar_complete_result_set_agreement
    {forest : Forest} {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint}
    (complete : GrammarComplete forest grammar input) :
    grammarPackedResults forest grammar input =
      GuardCorrespondence.grammarResults grammar input := by
  ext tree
  constructor
  · intro replay
    exact grammarPackedResults_subset_grammarResults forest grammar input replay
  · exact complete tree

def packedResults (forest : Forest)
    (presentation : GuardCorrespondence.SourcePresentation)
    (input : List Codepoint) : Set ParseTree :=
  { tree | ∃ certificate,
      PackedReplays forest presentation input certificate tree }

/-- The explicit scheduler obligation: every source result is present in one
shared forest. -/
def Complete (forest : Forest)
    (presentation : GuardCorrespondence.SourcePresentation)
    (input : List Codepoint) : Prop :=
  ∀ tree, SourceDerivesAt presentation input presentation.start
      0 input.length tree →
    ∃ certificate, PackedReplays forest presentation input certificate tree

theorem packedResults_subset_sourceResults
    (forest : Forest)
    (presentation : GuardCorrespondence.SourcePresentation)
    (input : List Codepoint) :
    packedResults forest presentation input ⊆
      GuardCorrespondence.sourceResults presentation input := by
  intro tree replay
  obtain ⟨certificate, accepted⟩ := replay
  exact packed_replay_sound accepted

theorem complete_result_set_agreement
    {forest : Forest}
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint}
    (complete : Complete forest presentation input) :
    packedResults forest presentation input =
      GuardCorrespondence.sourceResults presentation input := by
  ext tree
  constructor
  · intro replay
    exact packedResults_subset_sourceResults forest presentation input replay
  · intro derivation
    exact complete tree derivation

def Ambiguous (results : Set ParseTree) : Prop :=
  ∃ first ∈ results, ∃ second ∈ results, first ≠ second

theorem grammar_complete_ambiguity_agreement
    {forest : Forest} {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint}
    (complete : GrammarComplete forest grammar input) :
    Ambiguous (grammarPackedResults forest grammar input) ↔
      Ambiguous (GuardCorrespondence.grammarResults grammar input) := by
  rw [grammar_complete_result_set_agreement complete]

theorem complete_ambiguity_agreement
    {forest : Forest}
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint}
    (complete : Complete forest presentation input) :
    Ambiguous (packedResults forest presentation input) ↔
      Ambiguous (GuardCorrespondence.sourceResults presentation input) := by
  rw [complete_result_set_agreement complete]

/-- GLL and GLR forests agree extensionally whenever both discharge the same
explicit completeness obligation. -/
theorem complete_forests_result_set_agreement
    {left right : Forest}
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint}
    (leftComplete : Complete left presentation input)
    (rightComplete : Complete right presentation input) :
    packedResults left presentation input =
      packedResults right presentation input := by
  rw [complete_result_set_agreement leftComplete,
    complete_result_set_agreement rightComplete]

/-! ## Executable packed-ambiguity controls -/

def toyPresentation : GuardCorrespondence.SourcePresentation :=
  { start := "start"
    rules := [
      { sourceRule := "left", category := "start",
        symbols := [.exact 97], guards := [] },
      { sourceRule := "right", category := "start",
        symbols := [.exact 97], guards := [] }] }

def leftTree : ParseTree := .node "left" "start" [.terminal 97]
def rightTree : ParseTree := .node "right" "start" [.terminal 97]

def leftCertificate : Certificate :=
  .node "left" "start" 0 1 [.terminal 97 0 1]

def rightCertificate : Certificate :=
  .node "right" "start" 0 1 [.terminal 97 0 1]

def ambiguousForest : Forest :=
  packCertificates [leftCertificate, rightCertificate]

theorem ambiguousForest_shares_root : ambiguousForest.roots.length = 1 := by
  decide

theorem ambiguousForest_retains_two_families :
    ambiguousForest.families.length = 2 := by
  decide

theorem leftCertificate_replays :
    RootCertificateReplays toyPresentation [97] leftCertificate leftTree := by
  constructor
  · apply CertificateReplays.node
      (GuardCorrespondence.compile toyPresentation).productions[0]
    · simp [GuardCorrespondence.compile, toyPresentation]
    · apply GuardCorrespondence.CertificateBodyReplays.terminal
      · rfl
      · exact .nil
    · exact .nil
  · exact ⟨rfl, rfl⟩

theorem rightCertificate_replays :
    RootCertificateReplays toyPresentation [97] rightCertificate rightTree := by
  constructor
  · apply CertificateReplays.node
      (GuardCorrespondence.compile toyPresentation).productions[1]
    · simp [GuardCorrespondence.compile, toyPresentation]
    · apply GuardCorrespondence.CertificateBodyReplays.terminal
      · rfl
      · exact .nil
    · exact .nil
  · exact ⟨rfl, rfl⟩

theorem leftPackedReplay :
    PackedReplays ambiguousForest toyPresentation [97]
      leftCertificate leftTree := by
  constructor
  · exact member_packCertificates_unfolds (by simp)
      ⟨{ category := "start", start := 0, stop := 1 }, rfl⟩
  · exact leftCertificate_replays

theorem rightPackedReplay :
    PackedReplays ambiguousForest toyPresentation [97]
      rightCertificate rightTree := by
  constructor
  · exact member_packCertificates_unfolds (by simp)
      ⟨{ category := "start", start := 0, stop := 1 }, rfl⟩
  · exact rightCertificate_replays

theorem ambiguousForest_is_ambiguous :
    Ambiguous (packedResults ambiguousForest toyPresentation [97]) :=
  ⟨leftTree, ⟨leftCertificate, leftPackedReplay⟩,
    rightTree, ⟨rightCertificate, rightPackedReplay⟩, by
      intro equality
      simp [leftTree, rightTree] at equality⟩

def leftOnlyForest : Forest := packCertificates [leftCertificate]

theorem missingAlternative_rejects :
    ¬ RootUnfolds leftOnlyForest rightCertificate := by
  intro unfolds
  obtain ⟨key, keyEquation, rootMember, families⟩ := unfolds
  have rightFamilyMember :
      { parent := { category := "start", start := 0, stop := 1 }
        sourceRule := "right"
        children := [.terminal 97 0 1] } ∈
        certificateFamilies rightCertificate := by
    simp [rightCertificate, certificateFamilies, certificateFamily,
      certificateRef]
  have stored := families _ rightFamilyMember
  simp [leftOnlyForest, packCertificates, certificatesFamilies,
    leftCertificate, certificateFamilies, certificateFamily,
    certificateRef] at stored

end Mettapedia.GSLT.Parsing.PackedForest
