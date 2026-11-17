set -eu

dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
emit=_build/litany
opt=_build/litany-opt

"$emit" examples/Example.tim > "$dir/example.mlir"
"$opt" "$dir/example.mlir" > "$dir/normal.mlir"
"$opt" "$dir/normal.mlir" > "$dir/roundtrip.mlir"
cmp "$dir/normal.mlir" "$dir/roundtrip.mlir"
grep -Fq '"timbda.yield"(%arg0)' "$dir/normal.mlir"

printf '%s\n' '(λ (x := :int). lambda (x := x | fail). x) -18446744073709551617' |
  "$emit" > "$dir/nested.mlir"
"$opt" "$dir/nested.mlir" > "$dir/normal.mlir"
grep -Fq '"timbda.choice"(%arg0,' "$dir/normal.mlir"
grep -Fq '"timbda.yield"(%arg1)' "$dir/normal.mlir"
grep -Fq 'value = -18446744073709551617 : si66' "$dir/normal.mlir"

printf '%s\n' 'lambda (x := 1). lambda (y := 2). x' | "$emit" > "$dir/capture.mlir"
"$opt" "$dir/capture.mlir" > "$dir/normal.mlir"
grep -Fq '"timbda.yield"(%arg0)' "$dir/normal.mlir"

if printf '%s\n' 'lambda (x := x). x' | "$emit" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
test ! -s "$dir/out"
grep -Fq 'unbound variable x' "$dir/error"

sed 's/si4/i4/g' "$dir/example.mlir" > "$dir/invalid.mlir"
if "$opt" "$dir/invalid.mlir" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fq 'requires a signed integer attribute' "$dir/error"

sed 's/\^bb0(%v2: !timbda.set):/^bb0(%v2: !timbda.set, %extra: !timbda.set):/' \
  "$dir/example.mlir" > "$dir/invalid.mlir"
if "$opt" "$dir/invalid.mlir" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fq 'requires one !timbda.set block argument' "$dir/error"

sed '/"timbda.yield"/i\        %foreign = "builtin.unrealized_conversion_cast"(%v2) : (!timbda.set) -> !timbda.set' \
  "$dir/example.mlir" > "$dir/invalid.mlir"
if "$opt" "$dir/invalid.mlir" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fq 'is outside the Timbda-0 lambda body grammar' "$dir/error"

"$emit" examples/Showcase.tim > "$dir/showcase.mlir"
"$opt" "$dir/showcase.mlir" > "$dir/normal.mlir"
grep -Fq '"timbda.choice"(%arg0,' "$dir/normal.mlir"
grep -Fq '^bb0(%arg1: !timbda.set):' "$dir/normal.mlir"
grep -Eq '"timbda.choice"\(%[0-9]+, %arg0\)' "$dir/normal.mlir"
grep -Fq 'value = -18446744073709551617 : si66' "$dir/normal.mlir"
