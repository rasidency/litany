MLIR ?= /usr/lib/llvm-19
LLVM_LIB ?= LLVM
ROCQ ?= rocq
OCAMLOPT ?= ocamlopt
CXX ?= c++
BUILD ?= _build
TABLEGEN := $(MLIR)/bin/mlir-tblgen
GENERATED := $(foreach part,Dialect Types Ops,$(foreach ext,h cpp,$(BUILD)/$(part).$(ext).inc))

.PHONY: all proof check clean
all: $(BUILD)/litany $(BUILD)/litany-opt

$(BUILD):
	mkdir -p $@

$(BUILD)/Core.vo: proof/Core.v | $(BUILD)
	cp $< $(BUILD)/Core.v
	cd $(BUILD) && $(ROCQ) compile Core.v

$(BUILD)/Names.vo: proof/Names.v $(BUILD)/Core.vo
	cp $< $(BUILD)/Names.v
	cd $(BUILD) && $(ROCQ) compile Names.v

$(BUILD)/Target.vo $(BUILD)/core.ml $(BUILD)/core.mli &: proof/Target.v $(BUILD)/Names.vo
	cp $< $(BUILD)/Target.v
	cd $(BUILD) && $(ROCQ) compile Target.v

$(BUILD)/litany: $(BUILD)/core.ml $(BUILD)/core.mli src/Syntax.ml src/Main.ml
	cp src/Syntax.ml src/Main.ml $(BUILD)/
	cd $(BUILD) && $(OCAMLOPT) -o litany core.mli core.ml Syntax.ml Main.ml

define generate
$(BUILD)/$(1).$(2).inc: mlir/Dialect.td | $(BUILD)
	"$(TABLEGEN)" -I "$(MLIR)/include" -gen-$(3)-$(4) $$< -o $$@
endef

$(eval $(call generate,Dialect,h,dialect,decls))
$(eval $(call generate,Dialect,cpp,dialect,defs))
$(eval $(call generate,Types,h,typedef,decls))
$(eval $(call generate,Types,cpp,typedef,defs))
$(eval $(call generate,Ops,h,op,decls))
$(eval $(call generate,Ops,cpp,op,defs))

$(BUILD)/litany-opt: mlir/Dialect.cpp $(GENERATED) Makefile
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -std=c++17 -O2 -I "$(MLIR)/include" -I $(BUILD) $< -L "$(MLIR)/lib" -Wl,-rpath,"$(MLIR)/lib" $(LDFLAGS) -lMLIR -l$(LLVM_LIB) -o $@

proof: $(BUILD)/Target.vo
	cd $(BUILD) && $(ROCQ) check -silent -o Target > context.txt 2>&1
	@for fact in 'Theory: Set is predicative' 'Theory: Rewrite rules are not allowed' \
	  'Axioms: <none>' 'Constants/Inductives relying on type-in-type: <none>' \
	  'Constants/Inductives relying on unsafe (co)fixpoints: <none>' \
	  'Inductives whose positivity is assumed: <none>'; do \
	  grep -Fxq "* $$fact" $(BUILD)/context.txt || { echo "proof: missing '$$fact'" >&2; exit 1; }; \
	done

check: all proof
	sh tests/Test.sh "$(BUILD)"

clean:
	rm -rf $(BUILD)
