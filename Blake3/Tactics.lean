import Blake3.Blake3
import Lean

namespace Blake3

open Lean Elab Tactic in
/-- Tactic that proves BLAKE3 hash equalities by kernel-verified computation.
    All proofs are fully checked by the Lean 4 kernel (no `native_decide`).

    Strategy: use `simp` to rewrite `Range.forIn` (not kernel-reducible)
    into `List.forIn` (kernel-reducible via structural recursion), then `rfl`. -/
elab "blake3_decide" : tactic => do
  withMainContext do
    let goal ← getMainGoal
    goal.withContext do
      withOptions (fun opts =>
        opts |>.set `maxRecDepth 131072
             |>.set `maxHeartbeats 800000) do
        evalTactic (← `(tactic|
          simp only [Blake3.hash, Blake3.hashWithKey, Blake3.processChunk,
            Blake3.padBlock, Blake3.wordsToBytes,
            Std.Legacy.Range.forIn_eq_forIn_range']
        ))
        evalTactic (← `(tactic| rfl))

/-- DecidableEq instance for ByteArray, enabling kernel-verified equality proofs via `decide`. -/
instance instDecidableEqByteArrayBlake3 : DecidableEq ByteArray
  | ⟨a⟩, ⟨b⟩ =>
    if h : a = b then .isTrue (congrArg ByteArray.mk h)
    else .isFalse (fun h' => absurd (congrArg ByteArray.data h') h)

end Blake3
