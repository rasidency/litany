# litany

An MLIR dialect for Timbda-0, the calculus in [Figure 19 of the OPLSS 2026 Verse notes](https://www.cs.uoregon.edu/research/summerschool/summer26/_lectures/SPJ_Verse-figures.pdf#page=15) with continuation passing SSA construction proved in Rocq and extracted to OCaml

Build with Rocq 9.2 and its standard library, OCaml 5.5, and LLVM/MLIR 19 with TableGen, headers and shared libraries:

```sh
make MLIR=/usr/lib/llvm-19
make check MLIR=/usr/lib/llvm-19
```

### Example

The compiler gives each lambda an MLIR region and represents its parameter as a block argument of type `!timbda.set`. In this example, the outer argument feeds the inner domain through `timbda.choice` and appears again as a capture in the inner body. The negative literal comes through as `si66`:

<div align="center">

https://github.com/user-attachments/assets/9d0e0eb4-6bce-4ba6-b1bd-cc285bbaec32

</div>

```sh
cat examples/Showcase.tim
_build/litany examples/Showcase.tim | _build/litany-opt
make -B _build/Target.vo
```

`int` is the identity graph on ℤ, so `:int` gives the integers. More generally `:e` takes the range of a graph expression, `f x` applies a graph, `e | e` takes the union, and `fail` gives the empty set. Write `lambda (x := domain). body` with `λ` and `\` as alternate spellings. Range binds tightest then left associative application and then choice

The block argument denotes a singleton while the lambda result contains every total function graph over the domain whose outputs are allowed by the body

### Verification

`translate_verified` starts at a closed named syntax tree and ends at the MLIR operation tree. It proves that the target decodes to well scoped SSA and that for any interpretation of integers and graphs, a value belongs to the target denotation exactly when it belongs to the source denotation. The same development proves that translation accepts exactly the lexically resolvable trees  that decimal literals round trip and fit their signed attribute widths and that [the identity example](examples/Example.tim) denotes `{7}` under the integer identity interpretation. Rocq checks these results without axioms, and `make check` fails unless the kernel checker reports no axioms or unsafe fixpoints across the whole dependency closure, before it exercises the OCaml text parser and printer and the native MLIR verifier
