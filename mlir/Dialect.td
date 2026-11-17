include "mlir/IR/OpBase.td"
include "mlir/IR/AttrTypeBase.td"

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

def Timbda_Constant : Timbda_Op<"constant"> {
  let arguments = (ins APIntAttr:$value);
  let results = (outs Timbda_Set:$result);
  let hasVerifier = 1;
}

def Timbda_Int : Timbda_Op<"int"> {
  let results = (outs Timbda_Set:$result);
}

def Timbda_Fail : Timbda_Op<"fail"> {
  let results = (outs Timbda_Set:$result);
}

def Timbda_Range : Timbda_Op<"range"> {
  let arguments = (ins Timbda_Set:$graph);
  let results = (outs Timbda_Set:$result);
}

def Timbda_Apply : Timbda_Op<"apply"> {
  let arguments = (ins Timbda_Set:$graph, Timbda_Set:$arg);
  let results = (outs Timbda_Set:$result);
}

def Timbda_Choice : Timbda_Op<"choice"> {
  let arguments = (ins Timbda_Set:$left, Timbda_Set:$right);
  let results = (outs Timbda_Set:$result);
}

def Timbda_Lambda : Timbda_Op<"lambda", [SingleBlock]> {
  let arguments = (ins Timbda_Set:$domain);
  let results = (outs Timbda_Set:$result);
  let regions = (region SizedRegion<1>:$body);
  let hasRegionVerifier = 1;
}

def Timbda_Yield : Timbda_Op<"yield", [Terminator, HasParent<"Lambda">]> {
  let arguments = (ins Timbda_Set:$value);
}
