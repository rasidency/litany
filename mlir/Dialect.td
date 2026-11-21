include "mlir/IR/OpBase.td"
include "mlir/IR/AttrTypeBase.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"

def Timbda_Dialect : Dialect {
  let name = "timbda";
  let cppNamespace = "::timbda";
  let useDefaultTypePrinterParser = 1;
}

def Timbda_Set : TypeDef<Timbda_Dialect, "Set"> {
  let mnemonic = "set";
}

class Timbda_Op<string name, list<Trait> traits = []>
    : Op<Timbda_Dialect, name, traits>;

def Timbda_Constant : Timbda_Op<"constant", [Pure]> {
  let arguments = (ins APIntAttr:$value);
  let results = (outs Timbda_Set:$result);
  let hasVerifier = 1;
}

def Timbda_Int : Timbda_Op<"int", [Pure]> {
  let results = (outs Timbda_Set:$result);
}

def Timbda_Fail : Timbda_Op<"fail", [Pure]> {
  let results = (outs Timbda_Set:$result);
}

def Timbda_Range : Timbda_Op<"range", [Pure]> {
  let arguments = (ins Timbda_Set:$graph);
  let results = (outs Timbda_Set:$result);
  let hasFolder = 1;
}

def Timbda_Apply : Timbda_Op<"apply", [Pure]> {
  let arguments = (ins Timbda_Set:$graph, Timbda_Set:$arg);
  let results = (outs Timbda_Set:$result);
  let hasFolder = 1;
}

def Timbda_Choice : Timbda_Op<"choice", [Pure]> {
  let arguments = (ins Timbda_Set:$left, Timbda_Set:$right);
  let results = (outs Timbda_Set:$result);
  let hasFolder = 1;
}

def Timbda_Lambda : Timbda_Op<"lambda", [SingleBlock, Pure]> {
  let arguments = (ins Timbda_Set:$domain);
  let results = (outs Timbda_Set:$result);
  let regions = (region SizedRegion<1>:$body);
  let hasRegionVerifier = 1;
}

def Timbda_Yield : Timbda_Op<"yield", [Pure, Terminator, ReturnLike, HasParent<"Lambda">]> {
  let arguments = (ins Timbda_Set:$value);
}
