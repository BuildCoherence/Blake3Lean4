import Blake3
import Lean.Data.Json
import Lean.Data.Json.FromToJson

/-! # BLAKE3 hash correctness proofs
These theorems prove that specific inputs hash to specific outputs under BLAKE3.
All proofs are verified by the Lean 4 kernel without `native_decide`.
-/

namespace Blake3.Proofs

/-- The BLAKE3 hash of the empty input matches the official test vector. -/
theorem hash_empty :
    Blake3.hash ⟨#[]⟩ =
    ⟨#[0xAF, 0x13, 0x49, 0xB9, 0xF5, 0xF9, 0xA1, 0xA6,
       0xA0, 0x40, 0x4D, 0xEA, 0x36, 0xDC, 0xC9, 0x49,
       0x9B, 0xCB, 0x25, 0xC9, 0xAD, 0xC1, 0x12, 0xB7,
       0xCC, 0x9A, 0x93, 0xCA, 0xE4, 0x1F, 0x32, 0x62]⟩ := by
  blake3_decide

/-- The BLAKE3 hash of a single zero byte matches the official test vector. -/
theorem hash_one_byte :
    Blake3.hash ⟨#[0x00]⟩ =
    ⟨#[0x2D, 0x3A, 0xDE, 0xDF, 0xF1, 0x1B, 0x61, 0xF1,
       0x4C, 0x88, 0x6E, 0x35, 0xAF, 0xA0, 0x36, 0x73,
       0x6D, 0xCD, 0x87, 0xA7, 0x4D, 0x27, 0xB5, 0xC1,
       0x51, 0x02, 0x25, 0xD0, 0xF5, 0x92, 0xE2, 0x13]⟩ := by
  blake3_decide

/-- The BLAKE3 hash of [0x00, 0x01] matches the official test vector. -/
theorem hash_two_bytes :
    Blake3.hash ⟨#[0x00, 0x01]⟩ =
    ⟨#[0x7B, 0x70, 0x15, 0xBB, 0x92, 0xCF, 0x0B, 0x31,
       0x80, 0x37, 0x70, 0x2A, 0x6C, 0xDD, 0x81, 0xDE,
       0xE4, 0x12, 0x24, 0xF7, 0x34, 0x68, 0x4C, 0x2C,
       0x12, 0x2C, 0xD6, 0x35, 0x9C, 0xB1, 0xEE, 0x63]⟩ := by
  blake3_decide

/-- The hex-encoded BLAKE3 hash of empty input. -/
theorem hex_hash_empty :
    Blake3.cidToHex (Blake3.hash ⟨#[]⟩) =
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" := by
  have h := hash_empty
  rw [h]
  rfl

/-- The BLAKE3 hash of "Cryptography in the kernel!" matches the expected value. -/
theorem hash_crypto_kernel :
    Blake3.hash "Cryptography in the kernel!".toUTF8 =
    ⟨#[0xFC, 0xB1, 0x0C, 0xED, 0x13, 0xC6, 0xDA, 0x48,
       0xCC, 0xD2, 0x23, 0x4F, 0xC6, 0x56, 0xF1, 0x60,
       0x2D, 0x48, 0x46, 0xD4, 0xBA, 0x99, 0x5F, 0xC1,
       0x17, 0xA8, 0xE9, 0x34, 0xFA, 0x2A, 0x7D, 0x98]⟩ := by
  blake3_decide

#print axioms hash_crypto_kernel

example : Blake3.cidToHex (Blake3.hash "Cryptography in the kernel!".toUTF8)
    = "fcb10ced13c6da48ccd2234fc656f1602d4846d4ba995fc117a8e934fa2a7d98" := by
  have h := hash_crypto_kernel
  rw [h]
  rfl

end Blake3.Proofs

open Lean

structure TestCase where
  input_len : Nat
  hash : String
  keyed_hash : String
  derive_key : String
deriving FromJson, Inhabited

structure TestVectors where
  key : String
  context_string : String
  cases : Array TestCase
deriving FromJson, Inhabited

def makeTestInput (len : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.emptyWithCapacity len
  for i in [:len] do
    arr := arr.push (UInt8.ofNat (i % 251))
  return arr

def main : IO UInt32 := do
  IO.println "BLAKE3 Official Test Vectors Suite"
  IO.println "=================================="

  let env_var ← IO.getEnv "BLAKE3_TEST_VECTORS"
  let path := env_var.getD "test_vectors.json"

  let content ← try
    IO.FS.readFile path
  catch _ =>
    IO.println s!"Test vectors file not found at {path}."
    IO.println "Please set BLAKE3_TEST_VECTORS to point to test_vectors.json."
    return (1 : UInt32)

  let json ← match Json.parse content with
    | .ok j => pure j
    | .error e =>
      IO.println s!"Error parsing JSON: {e}"
      return (1 : UInt32)

  let res : Except String TestVectors := fromJson? json
  let vectors : TestVectors ← match res with
    | .error e =>
      IO.println s!"Error deserializing JSON: {e}"
      return (1 : UInt32)
    | .ok v => pure v

  let keyData := vectors.key.toUTF8
  let contextStr := vectors.context_string

  let mut passed := 0
  let mut failed := 0

  for c in vectors.cases do
    let input := makeTestInput c.input_len

    let h := Blake3.hash input
    let hexH := Blake3.cidToHex h

    let kh := Blake3.keyedHash input keyData
    let hexKh := Blake3.cidToHex kh

    let dk := Blake3.deriveKey contextStr input
    let hexDk := Blake3.cidToHex dk

    let check : String → String → String → IO Bool := fun name actual expectedFull => do
      let expected := expectedFull.take 64
      if actual == expected then
        return true
      else
        IO.println s!"  FAIL [{c.input_len}]: {name}"
        IO.println s!"    Expected: {expected}"
        IO.println s!"    Got:      {actual}"
        return false

    let mut casePassed := true
    casePassed := casePassed && (← check "hash" hexH c.hash)
    casePassed := casePassed && (← check "keyed_hash" hexKh c.keyed_hash)
    casePassed := casePassed && (← check "derive_key" hexDk c.derive_key)

    if casePassed then
      passed := passed + 1
    else
      failed := failed + 1

  IO.println s!"\nTests Run:  {passed + failed}"
  IO.println s!"Passed:     {passed}"
  IO.println s!"Failed:     {failed}"

  if failed > 0 then
    return (1 : UInt32)
  else
    return (0 : UInt32)
