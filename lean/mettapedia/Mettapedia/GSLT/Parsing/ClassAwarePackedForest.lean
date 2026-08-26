import Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate

/-!
# Occurrence-preserving class-aware packed forests

This module packs finite ParserPack certificates without quotienting physical
production occurrences.  Symbol nodes share a result sort and exact scalar
span; packed families retain whether the selected row was lexical or
structural and retain its physical table position.  Equal rule payloads at
different rows therefore remain distinct alternatives.

Forest membership and semantic replay are separate.  A forest supplies finite
data; `Replays` checks each selected certificate against the supplied parser
profile, compiled plan, and input.  `Complete` is an exact proof-fibre
criterion rather than equality of result sets.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwarePackedForest

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-- Shared symbol-node identity.  Equal values at different source spans are
different nodes. -/
structure NodeKey where
  resultSort : String
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- Physical identity of the selected ordered plan row. -/
inductive ProductionRef where
  | lexical (position : Nat)
  | structural (position : Nat)
  deriving DecidableEq, Repr

/-- One ordered child of a packed family.  Terminal leaves retain the exact
matcher and scalar span; nonterminals reference a shared symbol node. -/
inductive ChildRef where
  | terminal (matcher : TerminalMatcher) (start stop : Nat)
  | node (key : NodeKey)
  deriving DecidableEq, Repr

/-- One packed alternative at a shared symbol node. -/
structure Family where
  parent : NodeKey
  production : ProductionRef
  children : List ChildRef
  deriving DecidableEq, Repr

/-- A finite shared forest.  Root order is retained, while identical node
keys and identical families may be shared canonically. -/
structure Forest where
  roots : List NodeKey
  families : List Family
  deriving DecidableEq, Repr

def certificateKey (resultSort : String) : Certificate → NodeKey
  | .lexical _ _ start stop => ⟨resultSort, start, stop⟩
  | .structural _ start stop _ => ⟨resultSort, start, stop⟩

mutual
  /-- Ordered family children selected by one certificate body. -/
  def itemsChildRefs : ItemsCertificate → List ChildRef
    | .nil _ => []
    | .terminal matcher start stop rest =>
        .terminal matcher start stop :: itemsChildRefs rest
    | .nonterminal resultSort start stop _ rest =>
        .node ⟨resultSort, start, stop⟩ :: itemsChildRefs rest

  /-- The family selected by one complete certificate. -/
  def certificateFamily (resultSort : String) : Certificate → Family
    | .lexical position matcher start stop => {
        parent := ⟨resultSort, start, stop⟩
        production := .lexical position
        children := [.terminal matcher start stop]
      }
    | .structural position start stop body => {
        parent := ⟨resultSort, start, stop⟩
        production := .structural position
        children := itemsChildRefs body
      }

  /-- Every family recursively selected by one complete certificate. -/
  def certificateFamilies (resultSort : String) :
      Certificate → List Family
    | certificate@(.lexical _ _ _ _) =>
        [certificateFamily resultSort certificate]
    | certificate@(.structural _ _ _ body) =>
        certificateFamily resultSort certificate :: itemsFamilies body

  /-- Families selected by recursive nonterminal children in an item
  certificate. -/
  def itemsFamilies : ItemsCertificate → List Family
    | .nil _ => []
    | .terminal _ _ _ rest => itemsFamilies rest
    | .nonterminal resultSort _ _ head rest =>
        certificateFamilies resultSort head ++ itemsFamilies rest
end

/-- Canonically pack a list of root-sort/certificate pairs.  `eraseDups`
shares only literally equal identities; distinct physical production rows
remain distinct families even when their payloads are equal. -/
def pack (certificates : List (String × Certificate)) : Forest := {
  roots := (certificates.map fun entry =>
    certificateKey entry.1 entry.2).eraseDups
  families := (certificates.flatMap fun entry =>
    certificateFamilies entry.1 entry.2).eraseDups
}

/-- Every family recursively selected by a certificate occurs in the shared
store. -/
def Unfolds (forest : Forest) (resultSort : String)
    (certificate : Certificate) : Prop :=
  ∀ family, family ∈ certificateFamilies resultSort certificate →
    family ∈ forest.families

/-- A certificate begins at an exported root and all of its selected families
occur in the shared store. -/
def RootUnfolds (forest : Forest) (resultSort : String)
    (certificate : Certificate) : Prop :=
  certificateKey resultSort certificate ∈ forest.roots ∧
    Unfolds forest resultSort certificate

theorem member_pack_rootUnfolds
    {certificates : List (String × Certificate)}
    {resultSort : String} {certificate : Certificate}
    (member : (resultSort, certificate) ∈ certificates) :
    RootUnfolds (pack certificates) resultSort certificate := by
  constructor
  · simp only [pack, List.mem_eraseDups, List.mem_map]
    exact ⟨(resultSort, certificate), member, rfl⟩
  · intro family familyMember
    simp only [pack, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨(resultSort, certificate), member, familyMember⟩

/-- Exact packed replay combines finite forest membership with semantic
certificate replay. -/
def PackedReplays (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat)
    (certificate : Certificate) (resultSort : String)
    (start stop : Nat) (tree : CST) : Type :=
  PLift (RootUnfolds forest resultSort certificate) ×
    Replays profile plan input certificate resultSort start stop tree

instance PackedReplays.instSubsingleton
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    {certificate : Certificate} {resultSort : String}
    {start stop : Nat} {tree : CST} :
    Subsingleton (PackedReplays forest profile plan input certificate
      resultSort start stop tree) := by
  unfold PackedReplays
  infer_instance

/-- Packed replay cannot invent a ParserPack derivation. -/
def PackedReplays.derivation
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    {certificate : Certificate} {resultSort : String}
    {start stop : Nat} {tree : CST}
    (replay : PackedReplays forest profile plan input certificate
      resultSort start stop tree) :
    ParserPackDerivesAt profile plan input resultSort start stop tree :=
  replay.2.derivation

/-- The exact fibre presented by one forest at a fixed semantic observation. -/
abbrev PackedFibre (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat)
    (resultSort : String) (start stop : Nat) (tree : CST) : Type :=
  Sigma fun certificate =>
    PackedReplays forest profile plan input certificate
      resultSort start stop tree

/-- Proof-fibre completeness: every operational derivation's exact finite
certificate is present in the forest. -/
def Complete (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat)
    (resultSort : String) (start stop : Nat) (tree : CST) : Prop :=
  ∀ derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree,
    RootUnfolds forest resultSort (Certificate.ofDerivation derivation)

/-- Every member of a finite derivation list has a canonical packed replay. -/
def member_has_packed_replay
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String} {start stop : Nat} {tree : CST}
    {derivations : List (ParserPackDerivesAt profile plan input
      resultSort start stop tree)}
    {derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree}
    (member : derivation ∈ derivations) :
    PackedReplays
      (pack (derivations.map fun candidate =>
        (resultSort, Certificate.ofDerivation candidate)))
      profile plan input (Certificate.ofDerivation derivation)
      resultSort start stop tree := by
  refine ⟨⟨member_pack_rootUnfolds ?_⟩,
    Replays.ofDerivation derivation⟩
  exact List.mem_map.mpr ⟨derivation, member, rfl⟩

/-- A complete packed forest has exactly the operational ParserPack proof
fibre, not merely the same set of CST endpoints. -/
noncomputable def completeDerivationEquiv
    {forest : Forest} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    {resultSort : String} {start stop : Nat} {tree : CST}
    (complete : Complete forest profile plan input
      resultSort start stop tree) :
    ParserPackDerivesAt profile plan input resultSort start stop tree ≃
      PackedFibre forest profile plan input resultSort start stop tree where
  toFun derivation :=
    ⟨Certificate.ofDerivation derivation,
      ⟨⟨complete derivation⟩, Replays.ofDerivation derivation⟩⟩
  invFun packed := packed.2.derivation
  left_inv derivation :=
    Replays.derivation_ofDerivation derivation
  right_inv packed := by
    rcases packed with ⟨certificate, packedReplay⟩
    have certificateEqual :=
      Replays.certificate_derivation packedReplay.2
    apply Sigma.eq certificateEqual
    apply Subsingleton.elim

/-! ## Occurrence and corruption controls -/

/-- Distinct structural plan positions yield distinct packed families even
when parent and children are identical. -/
theorem structural_family_positions_remain_distinct
    {resultSort : String} {start stop leftPosition rightPosition : Nat}
    {body : ItemsCertificate} (different : leftPosition ≠ rightPosition) :
    certificateFamily resultSort
        (Certificate.structural leftPosition start stop body) ≠
      certificateFamily resultSort
        (Certificate.structural rightPosition start stop body) := by
  intro equal
  exact different (by
    have productionEqual := congrArg Family.production equal
    cases productionEqual
    rfl)

/-- Negative control: changing one terminal seam changes the packed family,
so the forest boundary cannot erase a cursor mutation. -/
theorem terminal_seam_mutation_changes_family
    {resultSort : String} {position start stop : Nat}
    {matcher : TerminalMatcher} {leftMiddle rightMiddle : Nat}
    {rest : ItemsCertificate} (different : leftMiddle ≠ rightMiddle) :
    certificateFamily resultSort
        (Certificate.structural position start stop
          (.terminal matcher start leftMiddle rest)) ≠
      certificateFamily resultSort
        (Certificate.structural position start stop
          (.terminal matcher start rightMiddle rest)) := by
  intro equal
  exact different (by
    have childrenEqual := congrArg Family.children equal
    cases childrenEqual
    rfl)

end Mettapedia.GSLT.Parsing.ClassAwarePackedForest
