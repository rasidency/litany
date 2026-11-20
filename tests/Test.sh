set -eu

cd "$(dirname "$0")/.."
build=$(cd "${1:-_build}" && pwd)
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
emit=$build/litany
opt=$build/litany-opt

"$emit" examples/Example.tim > "$dir/example.mlir"
"$opt" "$dir/example.mlir" > "$dir/normal.mlir"
"$opt" "$dir/normal.mlir" > "$dir/roundtrip.mlir"
cmp "$dir/normal.mlir" "$dir/roundtrip.mlir"
grep -Fq '"timbda.yield"(%arg0)' "$dir/normal.mlir"

cp examples/Example.tim "$dir/-h"
(cd "$dir" && "$emit" -- -h) > "$dir/dashfile.mlir"
cmp "$dir/example.mlir" "$dir/dashfile.mlir"

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

if printf '%s\n' 'λ (x := :int). y' | "$emit" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fxq -- '-:1:16: unbound variable y' "$dir/error"

sed 's/si4/i4/g' "$dir/example.mlir" > "$dir/invalid.mlir"
if "$opt" "$dir/invalid.mlir" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fq 'requires a signed integer attribute' "$dir/error"

cat > "$dir/zerowidth.mlir" <<'EOF'
module {
  %0 = "timbda.constant"() <{value = 0 : si0}> : () -> !timbda.set
}
EOF
if "$opt" "$dir/zerowidth.mlir" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fq 'requires a positive integer bit width' "$dir/error"

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

cat > "$dir/escape.mlir" <<'MLIR'
module {
  func.func @main() -> !timbda.set {
    %domain = "timbda.fail"() : () -> !timbda.set
    %closure = "timbda.lambda"(%domain) ({
    ^bb0(%bound: !timbda.set):
      "timbda.yield"(%bound) : (!timbda.set) -> ()
    }) : (!timbda.set) -> !timbda.set
    return %bound : !timbda.set
  }
}
MLIR
if "$opt" "$dir/escape.mlir" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fq 'use of undeclared SSA value name' "$dir/error"

sed 's/"timbda.yield"(%bound)/"timbda.yield"(%closure)/; s/return %bound/return %closure/' \
  "$dir/escape.mlir" > "$dir/self.mlir"
if "$opt" "$dir/self.mlir" > "$dir/out" 2> "$dir/error"; then
  exit 1
fi
grep -Fq 'does not dominate this use' "$dir/error"
