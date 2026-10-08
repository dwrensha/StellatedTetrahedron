# The 11/20 stellated tetrahedron is not Rupert

<p align="center">
  <img src="assets/stellated-tetrahedron.webp" alt="The 11/20 stellated tetrahedron, rotating" width="400">
</p>

This project proves, in Lean 4, that the stellated tetrahedron `P_{11/20}`
(the convex hull of a regular tetrahedron and its reflection scaled by `11/20`)
does not have [Rupert's property](https://en.wikipedia.org/wiki/Prince_Rupert%27s_cube):
no copy of it fits through a hole in itself.

The definitions and the reduction to finitely many certificate checks live in
[`Noperts/Stellated/`](Noperts/Stellated); the final statement is
`not_rupert_of_valid_table` in [IsNotRupert.lean](Noperts/Stellated/IsNotRupert.lean).
(This project grew out of the
[Noperthedron formalization](https://github.com/jcreedcmu/Noperthedron), and
shares some of its infrastructure.)

## The case analysis

The pose space is covered by three kinds of certificate tables:

* a chart table (`chart0.pack`): projective edge-cycle and balanced-triple
  certificates over a Cayley atlas of rotations;
* local tables (`local-NN.pack`): neighbourhoods of the symmetric poses;
* corner tables (`corner-*.pack`): blow-up coordinates around the corner views
  where the shadows touch at vertices.

### Native proof

[`constructStellated`](constructStellated.lean) reads the certificate data,
checks it with compiled code (trusting the Lean compiler, like `native_decide`)
and constructs the proof:

```
lake build constructStellated
.lake/build/bin/constructStellated DIR
```

On a 16-core machine this takes about 35 minutes.

### Kernel-only proof (in progress)

Integer and packed-`Nat` checkers that the kernel can evaluate quickly
(`LocalKernel*`, `CornerKernel*`, `ChartKernel*`), each proved sound with only
the standard axioms, plus a generator (`kernelCorner ktreegen`) that emits
kernel-checked proof modules into `StellatedKernel/`.

## Getting started

[Install Lean](https://lean-lang.org/install/manual/), clone this project, then:

```
lake exe cache get
lake build
```
