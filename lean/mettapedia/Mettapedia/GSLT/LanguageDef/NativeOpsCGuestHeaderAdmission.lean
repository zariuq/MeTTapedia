import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderLayout
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment000
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment001
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment002
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment003
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment004
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment005
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment006
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment007
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment008
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment009
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment010
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment011
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment012
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment013
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment014
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment015
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment016
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment017
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment018
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment019
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment020
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment021
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment022
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment023
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment024
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment025
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment026
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment027
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment028
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment029
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment030
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment031
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment032
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment033
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment034
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment035
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment036
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment037
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment038
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment039
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment040
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment041
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment042
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment043
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment044
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment045
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment046
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment047
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment048
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment049
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment050
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment051
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment052
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment053
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment054
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment055
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment056
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment057
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment058
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment059
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment060
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment061
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment062
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment063
import Mettapedia.GSLT.LanguageDef.NativeOpsCGuestHeaderSegment064
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexAccumulator

/-! Original header characters, complete lexing/parsing and declaration admission. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsCGuest

open NativeOps NativeOps.NativeC

attribute [local irreducible] LexSegmentAgreement

def headerJoin_000_chars : List Char := headerPiece_000_chars ++ headerPiece_001_chars
def headerJoin_000_tokens : List Token := headerPiece_000_tokens ++ headerPiece_001_tokens
def headerJoin_000_before : LexPoint := headerPiece_000_before
def headerJoin_000_after : LexPoint := headerPiece_001_after

theorem headerJoin_000_checked : LexSegmentAgreement headerJoin_000_before headerJoin_000_after
    headerJoin_000_chars headerJoin_000_tokens :=
  lex_segment_compose headerPiece_000_checked headerPiece_001_checked

def headerJoin_001_chars : List Char := headerPiece_002_chars ++ headerPiece_003_chars
def headerJoin_001_tokens : List Token := headerPiece_002_tokens ++ headerPiece_003_tokens
def headerJoin_001_before : LexPoint := headerPiece_002_before
def headerJoin_001_after : LexPoint := headerPiece_003_after

theorem headerJoin_001_checked : LexSegmentAgreement headerJoin_001_before headerJoin_001_after
    headerJoin_001_chars headerJoin_001_tokens :=
  lex_segment_compose headerPiece_002_checked headerPiece_003_checked

def headerJoin_002_chars : List Char := headerJoin_000_chars ++ headerJoin_001_chars
def headerJoin_002_tokens : List Token := headerJoin_000_tokens ++ headerJoin_001_tokens
def headerJoin_002_before : LexPoint := headerJoin_000_before
def headerJoin_002_after : LexPoint := headerJoin_001_after

theorem headerJoin_002_checked : LexSegmentAgreement headerJoin_002_before headerJoin_002_after
    headerJoin_002_chars headerJoin_002_tokens :=
  lex_segment_compose headerJoin_000_checked headerJoin_001_checked

def headerJoin_003_chars : List Char := headerPiece_004_chars ++ headerPiece_005_chars
def headerJoin_003_tokens : List Token := headerPiece_004_tokens ++ headerPiece_005_tokens
def headerJoin_003_before : LexPoint := headerPiece_004_before
def headerJoin_003_after : LexPoint := headerPiece_005_after

theorem headerJoin_003_checked : LexSegmentAgreement headerJoin_003_before headerJoin_003_after
    headerJoin_003_chars headerJoin_003_tokens :=
  lex_segment_compose headerPiece_004_checked headerPiece_005_checked

def headerJoin_004_chars : List Char := headerPiece_006_chars ++ headerPiece_007_chars
def headerJoin_004_tokens : List Token := headerPiece_006_tokens ++ headerPiece_007_tokens
def headerJoin_004_before : LexPoint := headerPiece_006_before
def headerJoin_004_after : LexPoint := headerPiece_007_after

theorem headerJoin_004_checked : LexSegmentAgreement headerJoin_004_before headerJoin_004_after
    headerJoin_004_chars headerJoin_004_tokens :=
  lex_segment_compose headerPiece_006_checked headerPiece_007_checked

def headerJoin_005_chars : List Char := headerJoin_003_chars ++ headerJoin_004_chars
def headerJoin_005_tokens : List Token := headerJoin_003_tokens ++ headerJoin_004_tokens
def headerJoin_005_before : LexPoint := headerJoin_003_before
def headerJoin_005_after : LexPoint := headerJoin_004_after

theorem headerJoin_005_checked : LexSegmentAgreement headerJoin_005_before headerJoin_005_after
    headerJoin_005_chars headerJoin_005_tokens :=
  lex_segment_compose headerJoin_003_checked headerJoin_004_checked

def headerJoin_006_chars : List Char := headerJoin_002_chars ++ headerJoin_005_chars
def headerJoin_006_tokens : List Token := headerJoin_002_tokens ++ headerJoin_005_tokens
def headerJoin_006_before : LexPoint := headerJoin_002_before
def headerJoin_006_after : LexPoint := headerJoin_005_after

theorem headerJoin_006_checked : LexSegmentAgreement headerJoin_006_before headerJoin_006_after
    headerJoin_006_chars headerJoin_006_tokens :=
  lex_segment_compose headerJoin_002_checked headerJoin_005_checked

def headerJoin_007_chars : List Char := headerPiece_008_chars ++ headerPiece_009_chars
def headerJoin_007_tokens : List Token := headerPiece_008_tokens ++ headerPiece_009_tokens
def headerJoin_007_before : LexPoint := headerPiece_008_before
def headerJoin_007_after : LexPoint := headerPiece_009_after

theorem headerJoin_007_checked : LexSegmentAgreement headerJoin_007_before headerJoin_007_after
    headerJoin_007_chars headerJoin_007_tokens :=
  lex_segment_compose headerPiece_008_checked headerPiece_009_checked

def headerJoin_008_chars : List Char := headerPiece_010_chars ++ headerPiece_011_chars
def headerJoin_008_tokens : List Token := headerPiece_010_tokens ++ headerPiece_011_tokens
def headerJoin_008_before : LexPoint := headerPiece_010_before
def headerJoin_008_after : LexPoint := headerPiece_011_after

theorem headerJoin_008_checked : LexSegmentAgreement headerJoin_008_before headerJoin_008_after
    headerJoin_008_chars headerJoin_008_tokens :=
  lex_segment_compose headerPiece_010_checked headerPiece_011_checked

def headerJoin_009_chars : List Char := headerJoin_007_chars ++ headerJoin_008_chars
def headerJoin_009_tokens : List Token := headerJoin_007_tokens ++ headerJoin_008_tokens
def headerJoin_009_before : LexPoint := headerJoin_007_before
def headerJoin_009_after : LexPoint := headerJoin_008_after

theorem headerJoin_009_checked : LexSegmentAgreement headerJoin_009_before headerJoin_009_after
    headerJoin_009_chars headerJoin_009_tokens :=
  lex_segment_compose headerJoin_007_checked headerJoin_008_checked

def headerJoin_010_chars : List Char := headerPiece_012_chars ++ headerPiece_013_chars
def headerJoin_010_tokens : List Token := headerPiece_012_tokens ++ headerPiece_013_tokens
def headerJoin_010_before : LexPoint := headerPiece_012_before
def headerJoin_010_after : LexPoint := headerPiece_013_after

theorem headerJoin_010_checked : LexSegmentAgreement headerJoin_010_before headerJoin_010_after
    headerJoin_010_chars headerJoin_010_tokens :=
  lex_segment_compose headerPiece_012_checked headerPiece_013_checked

def headerJoin_011_chars : List Char := headerPiece_014_chars ++ headerPiece_015_chars
def headerJoin_011_tokens : List Token := headerPiece_014_tokens ++ headerPiece_015_tokens
def headerJoin_011_before : LexPoint := headerPiece_014_before
def headerJoin_011_after : LexPoint := headerPiece_015_after

theorem headerJoin_011_checked : LexSegmentAgreement headerJoin_011_before headerJoin_011_after
    headerJoin_011_chars headerJoin_011_tokens :=
  lex_segment_compose headerPiece_014_checked headerPiece_015_checked

def headerJoin_012_chars : List Char := headerJoin_010_chars ++ headerJoin_011_chars
def headerJoin_012_tokens : List Token := headerJoin_010_tokens ++ headerJoin_011_tokens
def headerJoin_012_before : LexPoint := headerJoin_010_before
def headerJoin_012_after : LexPoint := headerJoin_011_after

theorem headerJoin_012_checked : LexSegmentAgreement headerJoin_012_before headerJoin_012_after
    headerJoin_012_chars headerJoin_012_tokens :=
  lex_segment_compose headerJoin_010_checked headerJoin_011_checked

def headerJoin_013_chars : List Char := headerJoin_009_chars ++ headerJoin_012_chars
def headerJoin_013_tokens : List Token := headerJoin_009_tokens ++ headerJoin_012_tokens
def headerJoin_013_before : LexPoint := headerJoin_009_before
def headerJoin_013_after : LexPoint := headerJoin_012_after

theorem headerJoin_013_checked : LexSegmentAgreement headerJoin_013_before headerJoin_013_after
    headerJoin_013_chars headerJoin_013_tokens :=
  lex_segment_compose headerJoin_009_checked headerJoin_012_checked

def headerJoin_014_chars : List Char := headerJoin_006_chars ++ headerJoin_013_chars
def headerJoin_014_tokens : List Token := headerJoin_006_tokens ++ headerJoin_013_tokens
def headerJoin_014_before : LexPoint := headerJoin_006_before
def headerJoin_014_after : LexPoint := headerJoin_013_after

theorem headerJoin_014_checked : LexSegmentAgreement headerJoin_014_before headerJoin_014_after
    headerJoin_014_chars headerJoin_014_tokens :=
  lex_segment_compose headerJoin_006_checked headerJoin_013_checked

def headerJoin_015_chars : List Char := headerPiece_016_chars ++ headerPiece_017_chars
def headerJoin_015_tokens : List Token := headerPiece_016_tokens ++ headerPiece_017_tokens
def headerJoin_015_before : LexPoint := headerPiece_016_before
def headerJoin_015_after : LexPoint := headerPiece_017_after

theorem headerJoin_015_checked : LexSegmentAgreement headerJoin_015_before headerJoin_015_after
    headerJoin_015_chars headerJoin_015_tokens :=
  lex_segment_compose headerPiece_016_checked headerPiece_017_checked

def headerJoin_016_chars : List Char := headerPiece_018_chars ++ headerPiece_019_chars
def headerJoin_016_tokens : List Token := headerPiece_018_tokens ++ headerPiece_019_tokens
def headerJoin_016_before : LexPoint := headerPiece_018_before
def headerJoin_016_after : LexPoint := headerPiece_019_after

theorem headerJoin_016_checked : LexSegmentAgreement headerJoin_016_before headerJoin_016_after
    headerJoin_016_chars headerJoin_016_tokens :=
  lex_segment_compose headerPiece_018_checked headerPiece_019_checked

def headerJoin_017_chars : List Char := headerJoin_015_chars ++ headerJoin_016_chars
def headerJoin_017_tokens : List Token := headerJoin_015_tokens ++ headerJoin_016_tokens
def headerJoin_017_before : LexPoint := headerJoin_015_before
def headerJoin_017_after : LexPoint := headerJoin_016_after

theorem headerJoin_017_checked : LexSegmentAgreement headerJoin_017_before headerJoin_017_after
    headerJoin_017_chars headerJoin_017_tokens :=
  lex_segment_compose headerJoin_015_checked headerJoin_016_checked

def headerJoin_018_chars : List Char := headerPiece_020_chars ++ headerPiece_021_chars
def headerJoin_018_tokens : List Token := headerPiece_020_tokens ++ headerPiece_021_tokens
def headerJoin_018_before : LexPoint := headerPiece_020_before
def headerJoin_018_after : LexPoint := headerPiece_021_after

theorem headerJoin_018_checked : LexSegmentAgreement headerJoin_018_before headerJoin_018_after
    headerJoin_018_chars headerJoin_018_tokens :=
  lex_segment_compose headerPiece_020_checked headerPiece_021_checked

def headerJoin_019_chars : List Char := headerPiece_022_chars ++ headerPiece_023_chars
def headerJoin_019_tokens : List Token := headerPiece_022_tokens ++ headerPiece_023_tokens
def headerJoin_019_before : LexPoint := headerPiece_022_before
def headerJoin_019_after : LexPoint := headerPiece_023_after

theorem headerJoin_019_checked : LexSegmentAgreement headerJoin_019_before headerJoin_019_after
    headerJoin_019_chars headerJoin_019_tokens :=
  lex_segment_compose headerPiece_022_checked headerPiece_023_checked

def headerJoin_020_chars : List Char := headerJoin_018_chars ++ headerJoin_019_chars
def headerJoin_020_tokens : List Token := headerJoin_018_tokens ++ headerJoin_019_tokens
def headerJoin_020_before : LexPoint := headerJoin_018_before
def headerJoin_020_after : LexPoint := headerJoin_019_after

theorem headerJoin_020_checked : LexSegmentAgreement headerJoin_020_before headerJoin_020_after
    headerJoin_020_chars headerJoin_020_tokens :=
  lex_segment_compose headerJoin_018_checked headerJoin_019_checked

def headerJoin_021_chars : List Char := headerJoin_017_chars ++ headerJoin_020_chars
def headerJoin_021_tokens : List Token := headerJoin_017_tokens ++ headerJoin_020_tokens
def headerJoin_021_before : LexPoint := headerJoin_017_before
def headerJoin_021_after : LexPoint := headerJoin_020_after

theorem headerJoin_021_checked : LexSegmentAgreement headerJoin_021_before headerJoin_021_after
    headerJoin_021_chars headerJoin_021_tokens :=
  lex_segment_compose headerJoin_017_checked headerJoin_020_checked

def headerJoin_022_chars : List Char := headerPiece_024_chars ++ headerPiece_025_chars
def headerJoin_022_tokens : List Token := headerPiece_024_tokens ++ headerPiece_025_tokens
def headerJoin_022_before : LexPoint := headerPiece_024_before
def headerJoin_022_after : LexPoint := headerPiece_025_after

theorem headerJoin_022_checked : LexSegmentAgreement headerJoin_022_before headerJoin_022_after
    headerJoin_022_chars headerJoin_022_tokens :=
  lex_segment_compose headerPiece_024_checked headerPiece_025_checked

def headerJoin_023_chars : List Char := headerPiece_026_chars ++ headerPiece_027_chars
def headerJoin_023_tokens : List Token := headerPiece_026_tokens ++ headerPiece_027_tokens
def headerJoin_023_before : LexPoint := headerPiece_026_before
def headerJoin_023_after : LexPoint := headerPiece_027_after

theorem headerJoin_023_checked : LexSegmentAgreement headerJoin_023_before headerJoin_023_after
    headerJoin_023_chars headerJoin_023_tokens :=
  lex_segment_compose headerPiece_026_checked headerPiece_027_checked

def headerJoin_024_chars : List Char := headerJoin_022_chars ++ headerJoin_023_chars
def headerJoin_024_tokens : List Token := headerJoin_022_tokens ++ headerJoin_023_tokens
def headerJoin_024_before : LexPoint := headerJoin_022_before
def headerJoin_024_after : LexPoint := headerJoin_023_after

theorem headerJoin_024_checked : LexSegmentAgreement headerJoin_024_before headerJoin_024_after
    headerJoin_024_chars headerJoin_024_tokens :=
  lex_segment_compose headerJoin_022_checked headerJoin_023_checked

def headerJoin_025_chars : List Char := headerPiece_028_chars ++ headerPiece_029_chars
def headerJoin_025_tokens : List Token := headerPiece_028_tokens ++ headerPiece_029_tokens
def headerJoin_025_before : LexPoint := headerPiece_028_before
def headerJoin_025_after : LexPoint := headerPiece_029_after

theorem headerJoin_025_checked : LexSegmentAgreement headerJoin_025_before headerJoin_025_after
    headerJoin_025_chars headerJoin_025_tokens :=
  lex_segment_compose headerPiece_028_checked headerPiece_029_checked

def headerJoin_026_chars : List Char := headerPiece_030_chars ++ headerPiece_031_chars
def headerJoin_026_tokens : List Token := headerPiece_030_tokens ++ headerPiece_031_tokens
def headerJoin_026_before : LexPoint := headerPiece_030_before
def headerJoin_026_after : LexPoint := headerPiece_031_after

theorem headerJoin_026_checked : LexSegmentAgreement headerJoin_026_before headerJoin_026_after
    headerJoin_026_chars headerJoin_026_tokens :=
  lex_segment_compose headerPiece_030_checked headerPiece_031_checked

def headerJoin_027_chars : List Char := headerJoin_025_chars ++ headerJoin_026_chars
def headerJoin_027_tokens : List Token := headerJoin_025_tokens ++ headerJoin_026_tokens
def headerJoin_027_before : LexPoint := headerJoin_025_before
def headerJoin_027_after : LexPoint := headerJoin_026_after

theorem headerJoin_027_checked : LexSegmentAgreement headerJoin_027_before headerJoin_027_after
    headerJoin_027_chars headerJoin_027_tokens :=
  lex_segment_compose headerJoin_025_checked headerJoin_026_checked

def headerJoin_028_chars : List Char := headerJoin_024_chars ++ headerJoin_027_chars
def headerJoin_028_tokens : List Token := headerJoin_024_tokens ++ headerJoin_027_tokens
def headerJoin_028_before : LexPoint := headerJoin_024_before
def headerJoin_028_after : LexPoint := headerJoin_027_after

theorem headerJoin_028_checked : LexSegmentAgreement headerJoin_028_before headerJoin_028_after
    headerJoin_028_chars headerJoin_028_tokens :=
  lex_segment_compose headerJoin_024_checked headerJoin_027_checked

def headerJoin_029_chars : List Char := headerJoin_021_chars ++ headerJoin_028_chars
def headerJoin_029_tokens : List Token := headerJoin_021_tokens ++ headerJoin_028_tokens
def headerJoin_029_before : LexPoint := headerJoin_021_before
def headerJoin_029_after : LexPoint := headerJoin_028_after

theorem headerJoin_029_checked : LexSegmentAgreement headerJoin_029_before headerJoin_029_after
    headerJoin_029_chars headerJoin_029_tokens :=
  lex_segment_compose headerJoin_021_checked headerJoin_028_checked

def headerJoin_030_chars : List Char := headerJoin_014_chars ++ headerJoin_029_chars
def headerJoin_030_tokens : List Token := headerJoin_014_tokens ++ headerJoin_029_tokens
def headerJoin_030_before : LexPoint := headerJoin_014_before
def headerJoin_030_after : LexPoint := headerJoin_029_after

theorem headerJoin_030_checked : LexSegmentAgreement headerJoin_030_before headerJoin_030_after
    headerJoin_030_chars headerJoin_030_tokens :=
  lex_segment_compose headerJoin_014_checked headerJoin_029_checked

def headerJoin_031_chars : List Char := headerPiece_032_chars ++ headerPiece_033_chars
def headerJoin_031_tokens : List Token := headerPiece_032_tokens ++ headerPiece_033_tokens
def headerJoin_031_before : LexPoint := headerPiece_032_before
def headerJoin_031_after : LexPoint := headerPiece_033_after

theorem headerJoin_031_checked : LexSegmentAgreement headerJoin_031_before headerJoin_031_after
    headerJoin_031_chars headerJoin_031_tokens :=
  lex_segment_compose headerPiece_032_checked headerPiece_033_checked

def headerJoin_032_chars : List Char := headerPiece_034_chars ++ headerPiece_035_chars
def headerJoin_032_tokens : List Token := headerPiece_034_tokens ++ headerPiece_035_tokens
def headerJoin_032_before : LexPoint := headerPiece_034_before
def headerJoin_032_after : LexPoint := headerPiece_035_after

theorem headerJoin_032_checked : LexSegmentAgreement headerJoin_032_before headerJoin_032_after
    headerJoin_032_chars headerJoin_032_tokens :=
  lex_segment_compose headerPiece_034_checked headerPiece_035_checked

def headerJoin_033_chars : List Char := headerJoin_031_chars ++ headerJoin_032_chars
def headerJoin_033_tokens : List Token := headerJoin_031_tokens ++ headerJoin_032_tokens
def headerJoin_033_before : LexPoint := headerJoin_031_before
def headerJoin_033_after : LexPoint := headerJoin_032_after

theorem headerJoin_033_checked : LexSegmentAgreement headerJoin_033_before headerJoin_033_after
    headerJoin_033_chars headerJoin_033_tokens :=
  lex_segment_compose headerJoin_031_checked headerJoin_032_checked

def headerJoin_034_chars : List Char := headerPiece_036_chars ++ headerPiece_037_chars
def headerJoin_034_tokens : List Token := headerPiece_036_tokens ++ headerPiece_037_tokens
def headerJoin_034_before : LexPoint := headerPiece_036_before
def headerJoin_034_after : LexPoint := headerPiece_037_after

theorem headerJoin_034_checked : LexSegmentAgreement headerJoin_034_before headerJoin_034_after
    headerJoin_034_chars headerJoin_034_tokens :=
  lex_segment_compose headerPiece_036_checked headerPiece_037_checked

def headerJoin_035_chars : List Char := headerPiece_038_chars ++ headerPiece_039_chars
def headerJoin_035_tokens : List Token := headerPiece_038_tokens ++ headerPiece_039_tokens
def headerJoin_035_before : LexPoint := headerPiece_038_before
def headerJoin_035_after : LexPoint := headerPiece_039_after

theorem headerJoin_035_checked : LexSegmentAgreement headerJoin_035_before headerJoin_035_after
    headerJoin_035_chars headerJoin_035_tokens :=
  lex_segment_compose headerPiece_038_checked headerPiece_039_checked

def headerJoin_036_chars : List Char := headerJoin_034_chars ++ headerJoin_035_chars
def headerJoin_036_tokens : List Token := headerJoin_034_tokens ++ headerJoin_035_tokens
def headerJoin_036_before : LexPoint := headerJoin_034_before
def headerJoin_036_after : LexPoint := headerJoin_035_after

theorem headerJoin_036_checked : LexSegmentAgreement headerJoin_036_before headerJoin_036_after
    headerJoin_036_chars headerJoin_036_tokens :=
  lex_segment_compose headerJoin_034_checked headerJoin_035_checked

def headerJoin_037_chars : List Char := headerJoin_033_chars ++ headerJoin_036_chars
def headerJoin_037_tokens : List Token := headerJoin_033_tokens ++ headerJoin_036_tokens
def headerJoin_037_before : LexPoint := headerJoin_033_before
def headerJoin_037_after : LexPoint := headerJoin_036_after

theorem headerJoin_037_checked : LexSegmentAgreement headerJoin_037_before headerJoin_037_after
    headerJoin_037_chars headerJoin_037_tokens :=
  lex_segment_compose headerJoin_033_checked headerJoin_036_checked

def headerJoin_038_chars : List Char := headerPiece_040_chars ++ headerPiece_041_chars
def headerJoin_038_tokens : List Token := headerPiece_040_tokens ++ headerPiece_041_tokens
def headerJoin_038_before : LexPoint := headerPiece_040_before
def headerJoin_038_after : LexPoint := headerPiece_041_after

theorem headerJoin_038_checked : LexSegmentAgreement headerJoin_038_before headerJoin_038_after
    headerJoin_038_chars headerJoin_038_tokens :=
  lex_segment_compose headerPiece_040_checked headerPiece_041_checked

def headerJoin_039_chars : List Char := headerPiece_042_chars ++ headerPiece_043_chars
def headerJoin_039_tokens : List Token := headerPiece_042_tokens ++ headerPiece_043_tokens
def headerJoin_039_before : LexPoint := headerPiece_042_before
def headerJoin_039_after : LexPoint := headerPiece_043_after

theorem headerJoin_039_checked : LexSegmentAgreement headerJoin_039_before headerJoin_039_after
    headerJoin_039_chars headerJoin_039_tokens :=
  lex_segment_compose headerPiece_042_checked headerPiece_043_checked

def headerJoin_040_chars : List Char := headerJoin_038_chars ++ headerJoin_039_chars
def headerJoin_040_tokens : List Token := headerJoin_038_tokens ++ headerJoin_039_tokens
def headerJoin_040_before : LexPoint := headerJoin_038_before
def headerJoin_040_after : LexPoint := headerJoin_039_after

theorem headerJoin_040_checked : LexSegmentAgreement headerJoin_040_before headerJoin_040_after
    headerJoin_040_chars headerJoin_040_tokens :=
  lex_segment_compose headerJoin_038_checked headerJoin_039_checked

def headerJoin_041_chars : List Char := headerPiece_044_chars ++ headerPiece_045_chars
def headerJoin_041_tokens : List Token := headerPiece_044_tokens ++ headerPiece_045_tokens
def headerJoin_041_before : LexPoint := headerPiece_044_before
def headerJoin_041_after : LexPoint := headerPiece_045_after

theorem headerJoin_041_checked : LexSegmentAgreement headerJoin_041_before headerJoin_041_after
    headerJoin_041_chars headerJoin_041_tokens :=
  lex_segment_compose headerPiece_044_checked headerPiece_045_checked

def headerJoin_042_chars : List Char := headerPiece_046_chars ++ headerPiece_047_chars
def headerJoin_042_tokens : List Token := headerPiece_046_tokens ++ headerPiece_047_tokens
def headerJoin_042_before : LexPoint := headerPiece_046_before
def headerJoin_042_after : LexPoint := headerPiece_047_after

theorem headerJoin_042_checked : LexSegmentAgreement headerJoin_042_before headerJoin_042_after
    headerJoin_042_chars headerJoin_042_tokens :=
  lex_segment_compose headerPiece_046_checked headerPiece_047_checked

def headerJoin_043_chars : List Char := headerJoin_041_chars ++ headerJoin_042_chars
def headerJoin_043_tokens : List Token := headerJoin_041_tokens ++ headerJoin_042_tokens
def headerJoin_043_before : LexPoint := headerJoin_041_before
def headerJoin_043_after : LexPoint := headerJoin_042_after

theorem headerJoin_043_checked : LexSegmentAgreement headerJoin_043_before headerJoin_043_after
    headerJoin_043_chars headerJoin_043_tokens :=
  lex_segment_compose headerJoin_041_checked headerJoin_042_checked

def headerJoin_044_chars : List Char := headerJoin_040_chars ++ headerJoin_043_chars
def headerJoin_044_tokens : List Token := headerJoin_040_tokens ++ headerJoin_043_tokens
def headerJoin_044_before : LexPoint := headerJoin_040_before
def headerJoin_044_after : LexPoint := headerJoin_043_after

theorem headerJoin_044_checked : LexSegmentAgreement headerJoin_044_before headerJoin_044_after
    headerJoin_044_chars headerJoin_044_tokens :=
  lex_segment_compose headerJoin_040_checked headerJoin_043_checked

def headerJoin_045_chars : List Char := headerJoin_037_chars ++ headerJoin_044_chars
def headerJoin_045_tokens : List Token := headerJoin_037_tokens ++ headerJoin_044_tokens
def headerJoin_045_before : LexPoint := headerJoin_037_before
def headerJoin_045_after : LexPoint := headerJoin_044_after

theorem headerJoin_045_checked : LexSegmentAgreement headerJoin_045_before headerJoin_045_after
    headerJoin_045_chars headerJoin_045_tokens :=
  lex_segment_compose headerJoin_037_checked headerJoin_044_checked

def headerJoin_046_chars : List Char := headerPiece_048_chars ++ headerPiece_049_chars
def headerJoin_046_tokens : List Token := headerPiece_048_tokens ++ headerPiece_049_tokens
def headerJoin_046_before : LexPoint := headerPiece_048_before
def headerJoin_046_after : LexPoint := headerPiece_049_after

theorem headerJoin_046_checked : LexSegmentAgreement headerJoin_046_before headerJoin_046_after
    headerJoin_046_chars headerJoin_046_tokens :=
  lex_segment_compose headerPiece_048_checked headerPiece_049_checked

def headerJoin_047_chars : List Char := headerPiece_050_chars ++ headerPiece_051_chars
def headerJoin_047_tokens : List Token := headerPiece_050_tokens ++ headerPiece_051_tokens
def headerJoin_047_before : LexPoint := headerPiece_050_before
def headerJoin_047_after : LexPoint := headerPiece_051_after

theorem headerJoin_047_checked : LexSegmentAgreement headerJoin_047_before headerJoin_047_after
    headerJoin_047_chars headerJoin_047_tokens :=
  lex_segment_compose headerPiece_050_checked headerPiece_051_checked

def headerJoin_048_chars : List Char := headerJoin_046_chars ++ headerJoin_047_chars
def headerJoin_048_tokens : List Token := headerJoin_046_tokens ++ headerJoin_047_tokens
def headerJoin_048_before : LexPoint := headerJoin_046_before
def headerJoin_048_after : LexPoint := headerJoin_047_after

theorem headerJoin_048_checked : LexSegmentAgreement headerJoin_048_before headerJoin_048_after
    headerJoin_048_chars headerJoin_048_tokens :=
  lex_segment_compose headerJoin_046_checked headerJoin_047_checked

def headerJoin_049_chars : List Char := headerPiece_052_chars ++ headerPiece_053_chars
def headerJoin_049_tokens : List Token := headerPiece_052_tokens ++ headerPiece_053_tokens
def headerJoin_049_before : LexPoint := headerPiece_052_before
def headerJoin_049_after : LexPoint := headerPiece_053_after

theorem headerJoin_049_checked : LexSegmentAgreement headerJoin_049_before headerJoin_049_after
    headerJoin_049_chars headerJoin_049_tokens :=
  lex_segment_compose headerPiece_052_checked headerPiece_053_checked

def headerJoin_050_chars : List Char := headerPiece_054_chars ++ headerPiece_055_chars
def headerJoin_050_tokens : List Token := headerPiece_054_tokens ++ headerPiece_055_tokens
def headerJoin_050_before : LexPoint := headerPiece_054_before
def headerJoin_050_after : LexPoint := headerPiece_055_after

theorem headerJoin_050_checked : LexSegmentAgreement headerJoin_050_before headerJoin_050_after
    headerJoin_050_chars headerJoin_050_tokens :=
  lex_segment_compose headerPiece_054_checked headerPiece_055_checked

def headerJoin_051_chars : List Char := headerJoin_049_chars ++ headerJoin_050_chars
def headerJoin_051_tokens : List Token := headerJoin_049_tokens ++ headerJoin_050_tokens
def headerJoin_051_before : LexPoint := headerJoin_049_before
def headerJoin_051_after : LexPoint := headerJoin_050_after

theorem headerJoin_051_checked : LexSegmentAgreement headerJoin_051_before headerJoin_051_after
    headerJoin_051_chars headerJoin_051_tokens :=
  lex_segment_compose headerJoin_049_checked headerJoin_050_checked

def headerJoin_052_chars : List Char := headerJoin_048_chars ++ headerJoin_051_chars
def headerJoin_052_tokens : List Token := headerJoin_048_tokens ++ headerJoin_051_tokens
def headerJoin_052_before : LexPoint := headerJoin_048_before
def headerJoin_052_after : LexPoint := headerJoin_051_after

theorem headerJoin_052_checked : LexSegmentAgreement headerJoin_052_before headerJoin_052_after
    headerJoin_052_chars headerJoin_052_tokens :=
  lex_segment_compose headerJoin_048_checked headerJoin_051_checked

def headerJoin_053_chars : List Char := headerPiece_056_chars ++ headerPiece_057_chars
def headerJoin_053_tokens : List Token := headerPiece_056_tokens ++ headerPiece_057_tokens
def headerJoin_053_before : LexPoint := headerPiece_056_before
def headerJoin_053_after : LexPoint := headerPiece_057_after

theorem headerJoin_053_checked : LexSegmentAgreement headerJoin_053_before headerJoin_053_after
    headerJoin_053_chars headerJoin_053_tokens :=
  lex_segment_compose headerPiece_056_checked headerPiece_057_checked

def headerJoin_054_chars : List Char := headerPiece_058_chars ++ headerPiece_059_chars
def headerJoin_054_tokens : List Token := headerPiece_058_tokens ++ headerPiece_059_tokens
def headerJoin_054_before : LexPoint := headerPiece_058_before
def headerJoin_054_after : LexPoint := headerPiece_059_after

theorem headerJoin_054_checked : LexSegmentAgreement headerJoin_054_before headerJoin_054_after
    headerJoin_054_chars headerJoin_054_tokens :=
  lex_segment_compose headerPiece_058_checked headerPiece_059_checked

def headerJoin_055_chars : List Char := headerJoin_053_chars ++ headerJoin_054_chars
def headerJoin_055_tokens : List Token := headerJoin_053_tokens ++ headerJoin_054_tokens
def headerJoin_055_before : LexPoint := headerJoin_053_before
def headerJoin_055_after : LexPoint := headerJoin_054_after

theorem headerJoin_055_checked : LexSegmentAgreement headerJoin_055_before headerJoin_055_after
    headerJoin_055_chars headerJoin_055_tokens :=
  lex_segment_compose headerJoin_053_checked headerJoin_054_checked

def headerJoin_056_chars : List Char := headerPiece_060_chars ++ headerPiece_061_chars
def headerJoin_056_tokens : List Token := headerPiece_060_tokens ++ headerPiece_061_tokens
def headerJoin_056_before : LexPoint := headerPiece_060_before
def headerJoin_056_after : LexPoint := headerPiece_061_after

theorem headerJoin_056_checked : LexSegmentAgreement headerJoin_056_before headerJoin_056_after
    headerJoin_056_chars headerJoin_056_tokens :=
  lex_segment_compose headerPiece_060_checked headerPiece_061_checked

def headerJoin_057_chars : List Char := headerPiece_063_chars ++ headerPiece_064_chars
def headerJoin_057_tokens : List Token := headerPiece_063_tokens ++ headerPiece_064_tokens
def headerJoin_057_before : LexPoint := headerPiece_063_before
def headerJoin_057_after : LexPoint := headerPiece_064_after

theorem headerJoin_057_checked : LexSegmentAgreement headerJoin_057_before headerJoin_057_after
    headerJoin_057_chars headerJoin_057_tokens :=
  lex_segment_compose headerPiece_063_checked headerPiece_064_checked

def headerJoin_058_chars : List Char := headerPiece_062_chars ++ headerJoin_057_chars
def headerJoin_058_tokens : List Token := headerPiece_062_tokens ++ headerJoin_057_tokens
def headerJoin_058_before : LexPoint := headerPiece_062_before
def headerJoin_058_after : LexPoint := headerJoin_057_after

theorem headerJoin_058_checked : LexSegmentAgreement headerJoin_058_before headerJoin_058_after
    headerJoin_058_chars headerJoin_058_tokens :=
  lex_segment_compose headerPiece_062_checked headerJoin_057_checked

def headerJoin_059_chars : List Char := headerJoin_056_chars ++ headerJoin_058_chars
def headerJoin_059_tokens : List Token := headerJoin_056_tokens ++ headerJoin_058_tokens
def headerJoin_059_before : LexPoint := headerJoin_056_before
def headerJoin_059_after : LexPoint := headerJoin_058_after

theorem headerJoin_059_checked : LexSegmentAgreement headerJoin_059_before headerJoin_059_after
    headerJoin_059_chars headerJoin_059_tokens :=
  lex_segment_compose headerJoin_056_checked headerJoin_058_checked

def headerJoin_060_chars : List Char := headerJoin_055_chars ++ headerJoin_059_chars
def headerJoin_060_tokens : List Token := headerJoin_055_tokens ++ headerJoin_059_tokens
def headerJoin_060_before : LexPoint := headerJoin_055_before
def headerJoin_060_after : LexPoint := headerJoin_059_after

theorem headerJoin_060_checked : LexSegmentAgreement headerJoin_060_before headerJoin_060_after
    headerJoin_060_chars headerJoin_060_tokens :=
  lex_segment_compose headerJoin_055_checked headerJoin_059_checked

def headerJoin_061_chars : List Char := headerJoin_052_chars ++ headerJoin_060_chars
def headerJoin_061_tokens : List Token := headerJoin_052_tokens ++ headerJoin_060_tokens
def headerJoin_061_before : LexPoint := headerJoin_052_before
def headerJoin_061_after : LexPoint := headerJoin_060_after

theorem headerJoin_061_checked : LexSegmentAgreement headerJoin_061_before headerJoin_061_after
    headerJoin_061_chars headerJoin_061_tokens :=
  lex_segment_compose headerJoin_052_checked headerJoin_060_checked

def headerJoin_062_chars : List Char := headerJoin_045_chars ++ headerJoin_061_chars
def headerJoin_062_tokens : List Token := headerJoin_045_tokens ++ headerJoin_061_tokens
def headerJoin_062_before : LexPoint := headerJoin_045_before
def headerJoin_062_after : LexPoint := headerJoin_061_after

theorem headerJoin_062_checked : LexSegmentAgreement headerJoin_062_before headerJoin_062_after
    headerJoin_062_chars headerJoin_062_tokens :=
  lex_segment_compose headerJoin_045_checked headerJoin_061_checked

def headerJoin_063_chars : List Char := headerJoin_030_chars ++ headerJoin_062_chars
def headerJoin_063_tokens : List Token := headerJoin_030_tokens ++ headerJoin_062_tokens
def headerJoin_063_before : LexPoint := headerJoin_030_before
def headerJoin_063_after : LexPoint := headerJoin_062_after

theorem headerJoin_063_checked : LexSegmentAgreement headerJoin_063_before headerJoin_063_after
    headerJoin_063_chars headerJoin_063_tokens :=
  lex_segment_compose headerJoin_030_checked headerJoin_062_checked

def headerCharacters : List Char := headerJoin_063_chars

theorem header_tokens_exact : headerJoin_063_tokens = headerTokens := by rfl

theorem original_header_lexed : lex headerCharacters = .ok headerTokens := by
  exact header_tokens_exact ▸ lex_checked_complete headerJoin_063_checked

theorem original_header_tokens_parsed : completeHeader? headerTokens = some candidateHeader := by cbv

theorem original_header_parsed : headerText? headerCharacters = some candidateHeader := by
  simp only [headerText?, original_header_lexed, Except.toOption]
  exact original_header_tokens_parsed

theorem original_header_admitted :
    headerText? headerCharacters = some candidateHeader ∧
    headerAgrees representation candidateHeader = true :=
  ⟨original_header_parsed, declaration_layout_checked⟩

end Mettapedia.GSLT.LanguageDef.NativeOpsCGuest
