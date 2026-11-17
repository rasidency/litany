#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/DialectImplementation.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "llvm/ADT/TypeSwitch.h"

#include "Dialect.h.inc"
#define GET_TYPEDEF_CLASSES
#include "Types.h.inc"
#define GET_OP_CLASSES
#include "Ops.h.inc"

#include "Dialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "Types.cpp.inc"
#define GET_OP_CLASSES
#include "Ops.cpp.inc"

void timbda::TimbdaDialect::initialize() {
  addTypes<SetType>();
  addOperations<
#define GET_OP_LIST
#include "Ops.cpp.inc"
      >();
}

mlir::LogicalResult timbda::Constant::verify() {
  if (!getValueAttr().getType().isSignedInteger())
    return emitOpError("requires a signed integer attribute");
  return mlir::success();
}

mlir::LogicalResult timbda::Lambda::verifyRegions() {
  auto &entry = getBody().front();
  if (entry.getNumArguments() != 1 ||
      !mlir::isa<SetType>(entry.getArgument(0).getType()))
    return emitOpError("requires one !timbda.set block argument");
  if (!mlir::isa<Yield>(entry.getTerminator()))
    return emitOpError("requires a timbda.yield terminator");
  for (auto &op : entry)
    if (op.getDialect() != getOperation()->getDialect())
      return op.emitOpError("is outside the Timbda-0 lambda body grammar");
  return mlir::success();
}

int main(int argc, char **argv) {
  mlir::DialectRegistry registry;
  registry.insert<timbda::TimbdaDialect, mlir::func::FuncDialect>();
  return mlir::asMainReturnCode(
      mlir::MlirOptMain(argc, argv, "litany Timbda-0 MLIR verifier\n", registry));
}
