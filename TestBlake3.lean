import Blake3
import Lean.Data.Json
import Lean.Data.Json.FromToJson

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
