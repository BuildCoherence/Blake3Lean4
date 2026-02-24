import Lake
open Lake DSL

package blake3 where
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "blake3_test_vectors"

@[default_target]
lean_lib Blake3 where
  srcDir := "."

lean_exe blake3_test_vectors where
  root := `TestBlake3
