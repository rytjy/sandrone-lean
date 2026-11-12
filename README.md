# sandrone-lean

A minimal Lean 4 + Mathlib project whose only purpose is to prove that the pipeline works end to end: toolchain, Mathlib cache, and CI.

Sandrone.lean contains three lemmas proved by hand. The CI badge turns green only if the file actually compiles against Mathlib.

## Run it yourself

    lake exe cache get
    lake build

No credentials, no account, no local setup beyond elan.
