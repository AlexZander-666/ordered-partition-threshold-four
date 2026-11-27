# Five interlacing rows of ordered set partitions at threshold four

Bowen Zuo, East China University of Science and Technology.

For every rank, the original fully ordered threshold-four rows have
simple negative roots and interlace strictly across gaps one through
four. The five-row window is sharp. The analytic proof starts at old
rank 288 and uses two conjugate pole pairs. Exact sign brackets verify
the 1,152 remaining comparisons.

- [Paper](paper/main.pdf) and [TeX and certificate instructions](paper/README.md)
- [Locked Lean build](formal/README.md) and [formal theorem map](verification/STATEMENT-MAP.md)
- [Input fingerprints](verification/SOURCE-PINS.md)

Run the independent certificate checks with Python 3:

    cd paper
    python3 -IB anc/analytic/boxes.py
    python3 -IB anc/analytic/arithmetic.py
    python3 -IB anc/analytic/certificate.py
    python3 -IB anc/finite/verify.py anc/finite/intervals-287.json --max-old 287 | cmp anc/finite/result-287.json -

The paper reproducer checks and builds twice from loose source and
twice from its source ZIP, then replays the finite and analytic
arithmetic. The 328-module formal project has the all-ranks entry
OrderedPartitions.FourPoleAllSizes. The hosted workflow checks exactly
these inputs and starts from empty local Lean build state.

Apache-2.0 covers the original Lean proof and verification code.
The author retains copyright in the manuscript.
