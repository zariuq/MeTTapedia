import Algorithms.GF.Generated.PaperAmbiguityIR

namespace Algorithms.GF.Examples.PaperFragment

open Algorithms.GF.CompiledIR
open Algorithms.GF.CYK
open Algorithms.GF.Generated.PaperAmbiguityIR

abbrev telescopeTokens : Array Tok := englishTelescopeTokens
abbrev annaTokens : Array Tok := englishAnnaTokens
abbrev czechTelescopeTokens' : Array Tok := czechTelescopeTokens
abbrev czechAnnaTokens' : Array Tok := czechAnnaTokens

abbrev telescopeParses : Array Parsed := englishTelescopeParsed
abbrev annaParses : Array Parsed := englishAnnaParsed
abbrev czechTelescopeParses' : Array Parsed := czechTelescopeParsed
abbrev czechAnnaParses' : Array Parsed := czechAnnaParsed

abbrev telescopeRecovered : Array ExportedTree := englishTelescopeRecovered
abbrev annaRecovered : Array ExportedTree := englishAnnaRecovered
abbrev czechTelescopeRecovered' : Array ExportedTree := czechTelescopeRecovered
abbrev czechAnnaRecovered' : Array ExportedTree := czechAnnaRecovered

abbrev telescopeParseCount : Nat := telescopeParses.size
abbrev annaParseCount : Nat := annaParses.size
abbrev czechTelescopeParseCount : Nat := czechTelescopeParses'.size
abbrev czechAnnaParseCount : Nat := czechAnnaParses'.size

def telescopeRootCats : Array CatId :=
  telescopeParses.map (fun p => p.derivation.rootCat)

def annaRootCats : Array CatId :=
  annaParses.map (fun p => p.derivation.rootCat)

def czechTelescopeRootCats : Array CatId :=
  czechTelescopeParses'.map (fun p => p.derivation.rootCat)

def czechAnnaRootCats : Array CatId :=
  czechAnnaParses'.map (fun p => p.derivation.rootCat)

private def containsTree (xs : Array ExportedTree) (target : ExportedTree) : Bool :=
  xs.any (fun x => x == target)

private def sameTreeSet (xs ys : Array ExportedTree) : Bool :=
  xs.size == ys.size &&
    xs.toList.all (containsTree ys) &&
    ys.toList.all (containsTree xs)

def telescopeParseCountOk : Bool := telescopeParseCount == 2
def annaParseCountOk : Bool := annaParseCount == 2
def czechTelescopeParseCountOk : Bool := czechTelescopeParseCount == 2
def czechAnnaParseCountOk : Bool := czechAnnaParseCount == 2

def telescopeRootCatsOk : Bool := telescopeRootCats == #["S", "S"]
def annaRootCatsOk : Bool := annaRootCats == #["S", "S"]
def czechTelescopeRootCatsOk : Bool := czechTelescopeRootCats == #["S", "S"]
def czechAnnaRootCatsOk : Bool := czechAnnaRootCats == #["S", "S"]

def telescopeRecoveredOk : Bool := sameTreeSet telescopeRecovered englishTelescopeExpected
def annaRecoveredOk : Bool := sameTreeSet annaRecovered englishAnnaExpected
def czechTelescopeRecoveredOk : Bool := sameTreeSet czechTelescopeRecovered' czechTelescopeExpected
def czechAnnaRecoveredOk : Bool := sameTreeSet czechAnnaRecovered' czechAnnaExpected

def englishChecksOk : Bool :=
  telescopeParseCountOk && annaParseCountOk &&
  telescopeRootCatsOk && annaRootCatsOk &&
  telescopeRecoveredOk && annaRecoveredOk

def czechChecksOk : Bool :=
  czechTelescopeParseCountOk && czechAnnaParseCountOk &&
  czechTelescopeRootCatsOk && czechAnnaRootCatsOk &&
  czechTelescopeRecoveredOk && czechAnnaRecoveredOk

def allChecksOk : Bool :=
  englishChecksOk && czechChecksOk

end Algorithms.GF.Examples.PaperFragment
