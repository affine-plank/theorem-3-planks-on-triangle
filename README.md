# The affine plank conjecture for three planks on a triangle

[![Proof checks](https://github.com/affine-plank/theorem-3-planks-on-triangle/actions/workflows/proof.yml/badge.svg)](https://github.com/affine-plank/theorem-3-planks-on-triangle/actions/workflows/proof.yml)

Three planks covering a triangle have total relative width at least one.

Start with [Triangle.lean](Triangle.lean). It defines the triangle, planks
and relative width, and states the theorem using ordinary sets and a finite sum.
All supporting project proofs are in [Triangle/Proof.lean](Triangle/Proof.lean).

The [paper](https://zazbrown.com/research/paper/affine-plank/three-planks-on-a-triangle/)
gives an elementary geometric proof.
The Lean proof uses a different organization.

With [Lean installed](https://lean-lang.org/install/), run:

```sh
lake exe cache get
lake build
```

To replay the proof and its dependencies through Lean's kernel:

```sh
lake env leanchecker --fresh Triangle
```

For a [Comparator check](verification/README.md), including the permitted
axioms, see `verification/`.
