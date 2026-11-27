# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local project on Linux ARM64. Lean 4.33.1 built all 328 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 328 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separately located, version-locked external dependency cache.

The lexical source scan passed. The 486 source reports and 6 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the original polynomial and the final theorem to the original rows.

- Source ZIP SHA-256 `f898574a9597625368d12a2f80e16e9d7647c7b3671ebd72e5e1bc6e4c14107b`
- Entry source SHA-256 `d7224a202c779ca593140c3bf8339d3a47ccae0193ecdb22e0fc4a4f2716422f`
- Cold log SHA-256 `d812e635b9aa9be6dc51d47aaece6bee223436a36e259a4b11f79c1f3d55ecca`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
