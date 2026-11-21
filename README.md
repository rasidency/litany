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

### Translation validation

`litany-opt` registers MLIR's canonicaliser and CSE, marks every Timbda-0 operation pure and folds `fail` through range, application and choice, but none of that C++ is trusted. `litany --validate` checks each optimised module against its source by translation validation, after George Necula's Translation Validation for an Optimizing Compiler (PLDI 2000). It rebuilds every SSA value as a term whose lambda arguments are levels, applies the same folds as it goes and compares the two results structurally. Here CSE merges `int x | int x`, the canonicaliser removes `:fail` and the second `7`, and 17 operations become 6:

```sh
_build/litany examples/Redundant.tim | _build/litany-opt --canonicalize --cse --canonicalize > /tmp/redundant.mlir
_build/litany --validate examples/Redundant.tim /tmp/redundant.mlir
```

Swapping the operands of the remaining `timbda.apply` still passes the MLIR verifier, but validation rejects it:

```sh
sed 's/"timbda.apply"(%0, %arg0)/"timbda.apply"(%arg0, %0)/' /tmp/redundant.mlir > /tmp/swapped.mlir
_build/litany --validate examples/Redundant.tim /tmp/swapped.mlir
```

### Verification

`translate_verified` starts at a closed named syntax tree and ends at the MLIR operation tree. It proves that the target decodes to well scoped SSA and that for any interpretation of integers and graphs, a value belongs to the target denotation exactly when it belongs to the source denotation. The same development proves that translation accepts exactly the lexically resolvable trees  that decimal literals round trip and receive the least signed attribute width that holds them and that [the identity example](examples/Example.tim) denotes `{7}` under the integer identity interpretation. Rocq checks these results without axioms, and `make check` fails unless the kernel checker reports no axioms or unsafe fixpoints across the whole dependency closure, before it exercises the OCaml text parser and printer and the native MLIR verifier

`optimisation_verified` extends that result past the optimiser. When translation succeeds and `validate` accepts an optimised module, the module decodes to well scoped SSA, and under every interpretation it denotes exactly the set the named source denotes. `validate_sound` is the step behind it, and it goes through `lift_correct`, which relates the SSA environment to the rebuilt terms. The definitions it rebuilds live in a binary trie keyed by native integer arithmetic, so 200,000 operations validate in about 4 seconds. `validate_complete` proves the converse for the optimiser. Validation accepts every module reachable from the source by redirecting uses between values of the same rebuilt term and deleting unused operations, anywhere in the tree, including inside lambda bodies. CSE and each folder perform the first of these rewrites, as `folds_agree` shows for the folds, and DCE performs the second. `src/Reader.ml`, which turns MLIR text into the operation tree that `decode` checks, is trusted

Extraction maps `nat` onto native OCaml `int` so that printing an SSA index costs constant time rather than a walk over unary numerals, which means the compiler also trusts that indices and literal widths, both linear in the input, stay below `max_int`
