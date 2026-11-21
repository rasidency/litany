#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/DialectImplementation.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Support/FileUtilities.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/ToolOutputFile.h"

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
  auto type = mlir::dyn_cast<mlir::IntegerType>(getValueAttr().getType());
  if (!type || !type.isSigned())
    return emitOpError("requires a signed integer attribute");
  if (type.getWidth() == 0)
    return emitOpError("requires a positive integer bit width");
  return mlir::success();
}

static bool failing(mlir::Value value) { return value.getDefiningOp<timbda::Fail>() != nullptr; }

mlir::OpFoldResult timbda::Range::fold(FoldAdaptor) {
  return failing(getGraph()) ? getGraph() : nullptr;
}

mlir::OpFoldResult timbda::Apply::fold(FoldAdaptor) {
  if (failing(getGraph()))
    return getGraph();
  return failing(getArg()) ? getArg() : nullptr;
}

mlir::OpFoldResult timbda::Choice::fold(FoldAdaptor) {
  if (failing(getLeft()))
    return getRight();
  if (failing(getRight()) || getLeft() == getRight())
    return getLeft();
  return nullptr;
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

static mlir::LogicalResult verifyProgram(mlir::ModuleOp module) {
  mlir::func::FuncOp main;
  for (auto &op : *module.getBody()) {
    auto func = mlir::dyn_cast<mlir::func::FuncOp>(op);
    if (main || !func || func.getSymName() != "main")
      return op.emitOpError("is outside the Timbda-0 program grammar");
    main = func;
  }
  if (!main)
    return module.emitError("requires a func.func @main");
  auto *context = module.getContext();
  auto type = mlir::FunctionType::get(context, {}, {timbda::SetType::get(context)});
  if (main.getFunctionType() != type || !main.getBody().hasOneBlock())
    return main.emitOpError("requires one block of type () -> !timbda.set");
  auto *dialect = context->getLoadedDialect<timbda::TimbdaDialect>();
  for (auto &op : main.getBody().front())
    if (!mlir::isa<mlir::func::ReturnOp>(op) && op.getDialect() != dialect)
      return op.emitOpError("is outside the Timbda-0 program grammar");
  auto attributes = main.walk([](mlir::Operation *op) {
    if (op->getDiscardableAttrDictionary().empty())
      return mlir::WalkResult::advance();
    op->emitOpError("carries attributes outside the Timbda-0 program grammar");
    return mlir::WalkResult::interrupt();
  });
  return mlir::failure(attributes.wasInterrupted());
}

namespace {
struct Program
    : mlir::PassWrapper<Program, mlir::OperationPass<mlir::ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(Program)
  void runOnOperation() final {
    if (mlir::failed(verifyProgram(getOperation())))
      signalPassFailure();
  }
};
} // namespace

int main(int argc, char **argv) {
  llvm::InitLLVM init(argc, argv);
  mlir::registerCanonicalizerPass();
  mlir::registerCSEPass();
  mlir::DialectRegistry registry;
  registry.insert<timbda::TimbdaDialect, mlir::func::FuncDialect>();
  auto [input, output] = mlir::registerAndParseCLIOptions(
      argc, argv, "litany Timbda-0 MLIR verifier\n", registry);
  auto config = mlir::MlirOptMainConfig::createFromCLOptions();
  if (config.shouldShowDialects()) {
    llvm::outs() << "Available Dialects: ";
    llvm::interleave(registry.getDialectNames(), llvm::outs(), ",");
    llvm::outs() << "\n";
    return 0;
  }
  auto requested = config;
  config.setPassPipelineSetupFn([requested](mlir::PassManager &pm) {
    pm.addPass(std::make_unique<Program>());
    return requested.setupPassPipeline(pm);
  });
  std::string error;
  auto file = mlir::openInputFile(input, &error);
  if (!file) {
    llvm::errs() << error << "\n";
    return 1;
  }
  auto out = mlir::openOutputFile(output, &error);
  if (!out) {
    llvm::errs() << error << "\n";
    return 1;
  }
  if (mlir::failed(mlir::MlirOptMain(out->os(), std::move(file), registry, config)))
    return 1;
  out->keep();
  return 0;
}
