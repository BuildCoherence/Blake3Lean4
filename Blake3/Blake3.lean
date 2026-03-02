namespace Blake3

-- BLAKE3 constants
def IV : Vector UInt32 8 := Vector.mk #[
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
  0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
] (by rfl)

def MSG_PERMUTATION : Vector (Fin 16) 16 := Vector.mk #[
  2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8
] (by rfl)

-- Domain separation flags
def CHUNK_START : UInt32 := 1
def CHUNK_END   : UInt32 := 2
def PARENT      : UInt32 := 4
def ROOT        : UInt32 := 8

abbrev State := Vector UInt32 16

@[inline] def rotateRight (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- BLAKE3 G mixing function (quarter-round). -/
def g (state : State) (a b c d : Fin 16) (mx my : UInt32) : State :=
  let va := state.get a
  let vb := state.get b
  let vc := state.get c
  let vd := state.get d
  let va := va + vb + mx
  let vd := rotateRight (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotateRight (vb ^^^ vc) 12
  let va := va + vb + my
  let vd := rotateRight (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotateRight (vb ^^^ vc) 7
  state
    |>.set a va
    |>.set b vb
    |>.set c vc
    |>.set d vd

/-- One round of BLAKE3: 4 column G calls + 4 diagonal G calls. -/
def round (state : State) (m : Vector UInt32 16) : State :=
  -- Column rounds
  let state := g state 0 4 8 12 (m.get 0) (m.get 1)
  let state := g state 1 5 9 13 (m.get 2) (m.get 3)
  let state := g state 2 6 10 14 (m.get 4) (m.get 5)
  let state := g state 3 7 11 15 (m.get 6) (m.get 7)
  -- Diagonal rounds
  let state := g state 0 5 10 15 (m.get 8) (m.get 9)
  let state := g state 1 6 11 12 (m.get 10) (m.get 11)
  let state := g state 2 7 8 13 (m.get 12) (m.get 13)
  let state := g state 3 4 9 14 (m.get 14) (m.get 15)
  state

/-- Permute message words for next round. -/
def permute (m : Vector UInt32 16) : Vector UInt32 16 :=
  Vector.ofFn fun i => m.get (MSG_PERMUTATION.get i)

/-- BLAKE3 compress function.
    Takes chaining value (8 words), block words (16 words),
    counter, block length, and flags. Returns 16-word state. -/
def compress (cv : Vector UInt32 8) (block : Vector UInt32 16)
    (counter : UInt64) (blockLen : UInt32) (flags : UInt32) : Vector UInt32 16 :=
  let counterLo := counter.toUInt32
  let counterHi := (counter >>> 32).toUInt32
  let state : State := Vector.mk #[
    cv.get 0, cv.get 1, cv.get 2, cv.get 3,
    cv.get 4, cv.get 5, cv.get 6, cv.get 7,
    IV.get 0, IV.get 1, IV.get 2, IV.get 3,
    counterLo, counterHi, blockLen, flags
  ] (by rfl)
  -- 7 rounds with message permutation between rounds
  let (state, _) := (List.range 7).foldl (fun (state, m) _ =>
    let state := round state m
    let m := permute m
    (state, m)
  ) (state, block)
  -- Finalize: XOR upper half with lower half, and lower half with CV
  Vector.ofFn fun i =>
    if h : i.val < 8 then
      state.get i ^^^ state.get ⟨i.val + 8, by omega⟩
    else
      state.get i ^^^ cv.get ⟨i.val - 8, by omega⟩

/-- Read a little-endian UInt32 from a ByteArray at the given offset. -/
def readLE32 (data : ByteArray) (offset : Nat) : UInt32 :=
  let get (i : Nat) : UInt8 :=
    if h : i < data.size then GetElem.getElem data.data i h else 0
  let b0 := (get offset).toUInt32
  let b1 := (get (offset + 1)).toUInt32
  let b2 := (get (offset + 2)).toUInt32
  let b3 := (get (offset + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Write a little-endian UInt32 to a ByteArray. -/
def writeLE32 (val : UInt32) : ByteArray :=
  let b := ByteArray.emptyWithCapacity 4
  let b := b.push (val &&& 0xFF).toUInt8
  let b := b.push ((val >>> 8) &&& 0xFF).toUInt8
  let b := b.push ((val >>> 16) &&& 0xFF).toUInt8
  let b := b.push ((val >>> 24) &&& 0xFF).toUInt8
  b

/-- Parse a 64-byte block into 16 UInt32 words (little-endian). -/
def bytesToWords (data : ByteArray) : Vector UInt32 16 :=
  Vector.ofFn fun i => readLE32 data (i.val * 4)

/-- Convert first N words of an array to bytes. -/
def wordsToBytes (words : Array UInt32) (count : Nat := 8) : ByteArray := Id.run do
  let mut result := ByteArray.emptyWithCapacity (count * 4)
  for i in [:count] do
    result := result ++ writeLE32 (words.getD i 0)
  return result

/-- Pad a block to 64 bytes with zeros. -/
def padBlock (data : ByteArray) : ByteArray := Id.run do
  if data.size >= 64 then return data
  let mut result := data
  for _ in [:64 - data.size] do
    result := result.push 0
  return result

/-- Extract a slice from a ByteArray. -/
def slice (data : ByteArray) (start len : Nat) : ByteArray :=
  data.extract start (start + len)

/-- Process a single chunk (up to 1024 bytes) and return its 8-word chaining value.
    If isRoot is true, applies ROOT flag and returns the 32-byte hash directly. -/
def processChunk (data : ByteArray) (chunkCounter : UInt64)
    (key : Vector UInt32 8) (baseFlags : UInt32) (isRoot : Bool := false) : ByteArray := Id.run do
  let dataLen := data.size
  let numBlocks := if dataLen == 0 then 1 else (dataLen + 63) / 64
  let mut cv := key
  for blockIdx in [:numBlocks] do
    let blockStart := blockIdx * 64
    let remaining := if dataLen >= blockStart then dataLen - blockStart else 0
    let blockData := if remaining >= 64
      then slice data blockStart 64
      else padBlock (slice data blockStart remaining)
    let blockWords := bytesToWords blockData
    let blockLen := UInt32.ofNat (min remaining 64)
    let mut flags : UInt32 := baseFlags
    if blockIdx == 0 then flags := flags ||| CHUNK_START
    if blockIdx == numBlocks - 1 then flags := flags ||| CHUNK_END
    if isRoot && blockIdx == numBlocks - 1 then flags := flags ||| ROOT
    let output := compress cv blockWords chunkCounter blockLen flags
    if isRoot && blockIdx == numBlocks - 1 then
      return wordsToBytes output.toArray 8
    cv := Vector.ofFn fun i => output.get ⟨i.val, by omega⟩
  return wordsToBytes cv.toArray 8

/-- Merge two 32-byte chaining values using the parent node compression.
    Returns 8-word chaining value. -/
def parentNode (left right : ByteArray) (key : Vector UInt32 8) (baseFlags : UInt32) : Vector UInt32 8 :=
  let combined := left ++ right
  let blockWords := bytesToWords combined
  let output := compress key blockWords 0 64 (PARENT ||| baseFlags)
  Vector.ofFn fun i => output.get ⟨i.val, by omega⟩

/-- Generic BLAKE3 hash computation. -/
def hashWithKey (data : ByteArray) (key : Vector UInt32 8) (flags : UInt32 := 0) : ByteArray := Id.run do
  let dataLen := data.size
  if dataLen <= 1024 then
    return processChunk data 0 key flags true
  -- Multi-chunk: split into 1024-byte chunks, build tree
  let numChunks := (dataLen + 1023) / 1024
  let mut cvs : Array ByteArray := #[]
  for i in [:numChunks] do
    let chunkStart := i * 1024
    let remaining := if dataLen >= chunkStart then dataLen - chunkStart else 0
    let chunkLen := min remaining 1024
    let chunkData := slice data chunkStart chunkLen
    let cv := processChunk chunkData (UInt64.ofNat i) key flags false
    cvs := cvs.push cv
  -- Tree merge: repeatedly merge pairs bottom-up
  while cvs.size > 2 do
    let pairs := cvs.size / 2
    let nextLevel := Array.ofFn (n := pairs) fun i =>
      let i := i.val
      have h1 : 2*i < cvs.size := by omega
      have h2 : 2*i + 1 < cvs.size := by omega
      let parent := parentNode (GetElem.getElem cvs (2*i) h1) (GetElem.getElem cvs (2*i+1) h2) key flags
      wordsToBytes parent.toArray 8
    let mut cvs' := nextLevel
    if h : cvs.size % 2 = 1 then
      have h_last : cvs.size - 1 < cvs.size := by omega
      cvs' := cvs'.push (GetElem.getElem cvs (cvs.size - 1) h_last)
    cvs := cvs'
  -- Final merge with ROOT flag
  if h : cvs.size = 1 then
    have h0 : 0 < cvs.size := by omega
    return GetElem.getElem cvs 0 h0
  if h : cvs.size >= 2 then
    have h0 : 0 < cvs.size := by omega
    have h1 : 1 < cvs.size := by omega
    let combined := GetElem.getElem cvs 0 h0 ++ GetElem.getElem cvs 1 h1
    let blockWords := bytesToWords combined
    let mut parentFlags := PARENT ||| ROOT
    if flags != 0 then parentFlags := parentFlags ||| flags
    let output := compress key blockWords 0 64 parentFlags
    return wordsToBytes output.toArray 8
  return .empty

/-- Compute the standard BLAKE3 hash. -/
def hash (data : ByteArray) : ByteArray :=
  hashWithKey data IV 0

/-- Compute the BLAKE3 keyed hash. Key must be exactly 32 bytes. -/
def keyedHash (data : ByteArray) (keyData : ByteArray) : ByteArray :=
  if keyData.size != 32 then .empty
  else
    let keyWords := bytesToWords keyData
    let keyVec := Vector.ofFn fun i => keyWords.get ⟨i.val, by omega⟩
    -- Domain separation for keyed hash is KEYED_HASH flag = 16
    hashWithKey data keyVec 16

/-- Domain separation flag for derive_key. -/
def DERIVE_KEY_CONTEXT : UInt32 := 32

/-- Compute the BLAKE3 derive_key hash. -/
def deriveKey (context : String) (material : ByteArray) : ByteArray :=
  let contextBytes := context.toUTF8
  let contextHash := hashWithKey contextBytes IV DERIVE_KEY_CONTEXT
  let contextKeyWords := bytesToWords contextHash
  let contextKey := Vector.ofFn fun i => contextKeyWords.get ⟨i.val, by omega⟩
  -- Key generation uses DERIVE_KEY_MATERIAL flag = 64
  hashWithKey material contextKey 64

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat)
  else Char.ofNat (87 + n.toNat)

/-- Convert a ByteArray to a lowercase hex string. -/
def cidToHex (cid : ByteArray) : String :=
  let chars := cid.foldl (fun acc b =>
    acc ++ [hexDigit (b >>> 4), hexDigit (b &&& 0x0F)]
  ) []
  String.ofList chars

end Blake3
