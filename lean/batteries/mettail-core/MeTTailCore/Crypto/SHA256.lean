/-!
# Pure-Lean SHA-256

NIST FIPS 180-4 compliant SHA-256 implementation.
Operates on UTF-8 bytes (`String.toUTF8`), matching Rust's `text.as_bytes()`.

This is a build-time utility for artifact integrity — not used in proofs.
-/

namespace MeTTailCore.Crypto.SHA256

-- § Initial hash values (first 32 bits of fractional parts of square roots of first 8 primes)
private def h0Init : UInt32 := 0x6a09e667
private def h1Init : UInt32 := 0xbb67ae85
private def h2Init : UInt32 := 0x3c6ef372
private def h3Init : UInt32 := 0xa54ff53a
private def h4Init : UInt32 := 0x510e527f
private def h5Init : UInt32 := 0x9b05688c
private def h6Init : UInt32 := 0x1f83d9ab
private def h7Init : UInt32 := 0x5be0cd19

-- § Round constants (first 32 bits of fractional parts of cube roots of first 64 primes)
private def kConsts : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

-- § Bitwise helpers
private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x.complement &&& z)

private def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def bigSigma0 (x : UInt32) : UInt32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

private def bigSigma1 (x : UInt32) : UInt32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

private def smallSigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

private def smallSigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

-- § Hash state
private structure HashState where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32

private def initState : HashState :=
  { h0 := h0Init, h1 := h1Init, h2 := h2Init, h3 := h3Init,
    h4 := h4Init, h5 := h5Init, h6 := h6Init, h7 := h7Init }

-- § Message schedule + compression for one 64-byte block
private def processBlock (state : HashState) (block : ByteArray) : HashState :=
  -- Build 16-word message schedule from block bytes (big-endian)
  let w0 : Array UInt32 := Id.run do
    let mut arr := Array.mkEmpty 16
    for i in [:16] do
      let b0 := (block.get! (i * 4)).toUInt32
      let b1 := (block.get! (i * 4 + 1)).toUInt32
      let b2 := (block.get! (i * 4 + 2)).toUInt32
      let b3 := (block.get! (i * 4 + 3)).toUInt32
      arr := arr.push ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
    return arr
  -- Extend to 64 words
  let w : Array UInt32 := Id.run do
    let mut arr := w0
    for _ in [:48] do
      let sz := arr.size
      let s0 := smallSigma0 arr[sz - 15]!
      let s1 := smallSigma1 arr[sz - 2]!
      arr := arr.push (arr[sz - 16]! + s0 + arr[sz - 7]! + s1)
    return arr
  -- Compression rounds
  let (a, b, c, d, e, f, g, h) := Id.run do
    let mut a := state.h0
    let mut b := state.h1
    let mut c := state.h2
    let mut d := state.h3
    let mut e := state.h4
    let mut f := state.h5
    let mut g := state.h6
    let mut h := state.h7
    for i in [:64] do
      let t1 := h + bigSigma1 e + ch e f g + kConsts[i]! + w[i]!
      let t2 := bigSigma0 a + maj a b c
      h := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    return (a, b, c, d, e, f, g, h)
  { h0 := state.h0 + a, h1 := state.h1 + b, h2 := state.h2 + c, h3 := state.h3 + d,
    h4 := state.h4 + e, h5 := state.h5 + f, h6 := state.h6 + g, h7 := state.h7 + h }

-- § Padding: append 1-bit, zeros, then 64-bit big-endian length
private def pad (data : ByteArray) : ByteArray := Id.run do
  let len := data.size
  let bitLen : UInt64 := (len.toUInt64) * 8
  -- Append 0x80
  let mut padded := data.push 0x80
  -- Pad with zeros until length ≡ 56 (mod 64)
  let rem := padded.size % 64
  let zerosNeeded := if rem <= 56 then 56 - rem else 64 - rem + 56
  for _ in [:zerosNeeded] do
    padded := padded.push 0x00
  -- Append 64-bit big-endian length
  padded := padded.push (bitLen >>> 56).toUInt8
  padded := padded.push (bitLen >>> 48).toUInt8
  padded := padded.push (bitLen >>> 40).toUInt8
  padded := padded.push (bitLen >>> 32).toUInt8
  padded := padded.push (bitLen >>> 24).toUInt8
  padded := padded.push (bitLen >>> 16).toUInt8
  padded := padded.push (bitLen >>> 8).toUInt8
  padded := padded.push bitLen.toUInt8
  return padded

-- § Core hash function
def sha256Bytes (data : ByteArray) : ByteArray :=
  let padded := pad data
  let numBlocks := padded.size / 64
  let state := Id.run do
    let mut s := initState
    for i in [:numBlocks] do
      let block := padded.extract (i * 64) (i * 64 + 64)
      s := processBlock s block
    return s
  -- Serialize state to 32 bytes (big-endian)
  Id.run do
    let mut result := ByteArray.empty
    for w in [state.h0, state.h1, state.h2, state.h3,
              state.h4, state.h5, state.h6, state.h7] do
      result := result.push (w >>> 24).toUInt8
      result := result.push (w >>> 16).toUInt8
      result := result.push (w >>> 8).toUInt8
      result := result.push w.toUInt8
    return result

-- § Hex encoding
private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat)  -- '0' + n
  else Char.ofNat (87 + n.toNat)             -- 'a' + (n - 10)

private def byteToHex (b : UInt8) : String :=
  String.ofList [hexDigit (b >>> 4), hexDigit (b &&& 0x0f)]

def toHexString (data : ByteArray) : String :=
  Id.run do
    let mut s := ""
    for b in data do
      s := s ++ byteToHex b
    return s

-- § Convenience: hash a string (UTF-8 encoded) and return 64-char hex
def sha256Hex (text : String) : String :=
  toHexString (sha256Bytes text.toUTF8)

-- § NIST test vectors
#guard sha256Hex "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard sha256Hex "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

end MeTTailCore.Crypto.SHA256
