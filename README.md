# Blake3Lean4

A pure Lean 4 standalone implementation of the [BLAKE3 cryptographic hash function](https://github.com/BLAKE3-team/BLAKE3).

> [!IMPORTANT]
> This implementation has not been audited and is recommended for research and experimental use only.

This implementation supports:
- Standard BLAKE3 Hashing
- Keyed Hashing
- Key Derivation Function (KDF)
- Merkle Tree structure (for multi-chunk hashing)
- Full compatibility with the official BLAKE3 test vectors

## Setup

This project uses `lake` for Lean dependency management and optional Nix for environment consistency and fetching official test vectors.

### Using Nix (Recommended)
This requires [Nix](https://nixos.org/download) with `nix-command` and `flakes` enabled.

Enter the development shell, which provides `elan` and automatically fetches the official test vectors:
```bash
nix develop
```

### Manual Setup
Ensure you have [elan](https://github.com/leanprover/elan) installed for managing Lean versions. This project uses Lean version `v4.28.0` (specified in `lean-toolchain`).

## Usage

You can use the `Blake3` namespace functions located in `Blake3.lean`:

### Standard Hashing
```lean
import Blake3

def exampleHash : ByteArray := 
  Blake3.hash "hello world".toUTF8

-- Convert to hex string
def hexOutput : String := 
  Blake3.cidToHex exampleHash
```

### Keyed Hashing
Requires a 32-byte key:
```lean
import Blake3

def exampleKeyedHash : ByteArray :=
  let keyData := "How do you like your thoughts?".toUTF8
  Blake3.keyedHash "Formally verified.".toUTF8 keyData
```

### Key Derivation
Requires a context string:
```lean
import Blake3

def derivedKey : ByteArray :=
  let context := "my context"
  Blake3.deriveKey context "my secret key material".toUTF8
```

## Testing

The test suite parses and verifies against the [official BLAKE3 Test Vectors JSON](https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/test_vectors.json).

If you are inside the `nix develop` environment, simply run:
```bash
# Builds the project and runs the test executable
lake test
```

If you are not using Nix, you must manually download `test_vectors.json` and set the `BLAKE3_TEST_VECTORS` environment variable to its path:
```bash
wget https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/master/test_vectors/test_vectors.json
export BLAKE3_TEST_VECTORS="$(pwd)/test_vectors.json"
lake test
```
