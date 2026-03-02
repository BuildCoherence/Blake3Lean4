import Lake
open Lake DSL

package blake3 where
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "test_blake3"

@[default_target]
lean_lib Blake3 where
  srcDir := "."

lean_exe test_blake3 where
  root := `TestBlake3
