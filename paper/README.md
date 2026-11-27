# Five interlacing rows of ordered set partitions at threshold four

The sole author is Bowen Zuo, East China University of Science and Technology.
The manuscript describes the full mathematical proof for the original
ordered set partitions, with all old ranks and all four shifts. The analytic
argument starts at old rank 288, and the finite certificate covers old ranks
0 through 287 and upper ranks through 291.

## Build the PDF and source archive

Use Python 3 and TeX Live with `pdflatex`, Latin Modern, AMS, Microtype and
Hyperref. From this directory run:

```sh
python3 -B reproduce.py
```

The script builds the loose source twice and the independently unpacked
source archive twice. It checks for unresolved references, missing glyphs,
and overfull boxes. The final PDF bytes must agree between the two builds. The script also
replays the arithmetic and finite certificates from the unpacked archive.
The only TeX entry point is `main.tex`. Set `PDFLATEX` to the executable
path if it is absent from `PATH`. The frozen PDF uses pdfTeX 1.40.29
(TeX Live 2026). The same-source build test compares builds made with
the same version of the compiler.

## Replay the mathematical certificates

The following commands use only the Python standard library. All sign and
norm tests use exact arithmetic.

```sh
(
  cd anc/analytic
  python3 -IB boxes.py
  python3 -IB arithmetic.py
  python3 -IB certificate.py
)
(
  cd anc/finite
  python3 -IB verify.py intervals-287.json --max-old 287 | cmp result-287.json -
)
```

`boxes.py` checks the 17 rational disk bins with shared endpoints in
`dominance.json`. `arithmetic.py` checks the scalar estimates at the real
critical point and the circle, along with an exact reciprocal-edge
identity. `certificate.py` verifies the uniform residue sign margins for
256 small cells and 16 compact bins and the endpoint phase margin.
`effective-analytic-note.md` describes the explicit rank-288 calculation.
The [earlier existence note](anc/analytic/earlier-existence-note.md)
is the historical precursor for the four-pole geometry and a separate
asymptotic argument. It is the file called `proof.md` in the effective note. Status statements in both notes are dated; the current mathematical statement is Theorem 1.

The finite verifier computes the original ordered-partition rows via the
marked-block generating function. It checks 10,512 isolating intervals
and 1,152 interlacings, including constant cases. The finite generator
uses the integer first-block recurrence and can independently regenerate
the intervals; run `python3 -IB generate.py --help` within `anc/finite`.

## Formal verification

The companion source archive is ordered-partitions-five-row-window-source.zip,
SHA-256 f898574a9597625368d12a2f80e16e9d7647c7b3671ebd72e5e1bc6e4c14107b.
It contains the 328 local Lean modules used by the all-sizes theorem.
OrderedPartitions.FourPoleAllSizes imports the exact finite comparisons
and the effective analytic result. The final declarations cover all old
ranks, the five-row window and failure of six-row windows.
From an extraction, use Python 3 to run verify.py against the pinned
external Lake packages. The verifier checks the transitive axiom reports
and replays each project module with the Lean kernel.
