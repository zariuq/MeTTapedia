FRONTEND := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
include $(FRONTEND)/source.lock

BUILD_DIR ?= $(FRONTEND)/build
CETTA_DIR := $(abspath $(BUILD_DIR)/cetta-$(CETTA_REVISION))
TRANSLATOR := $(abspath $(BUILD_DIR)/mm2-translate)
# An optional object source accelerates checkout without building in it.
CETTA_SOURCE ?=

.PHONY: all test native-reader-objects dependency check-dependency
all: dependency
	$(MAKE) -C "$(CETTA_DIR)" -f "$(FRONTEND)/native.mk" \
		MM2_FRONTEND_ROOT="$(FRONTEND)" MM2_OUTPUT="$(TRANSLATOR)" \
		BUILD=core ENABLE_LIB_PROLOG=0 ENABLE_GMP=0 mm2-native

test: all
	python3 "$(FRONTEND)/../tests/test_reader.py" --translator "$(TRANSLATOR)"

native-reader-objects: dependency
	$(MAKE) -C "$(CETTA_DIR)" -f "$(FRONTEND)/native.mk" \
		MM2_FRONTEND_ROOT="$(FRONTEND)" MM2_OUTPUT="$(TRANSLATOR)" \
		BUILD=core ENABLE_LIB_PROLOG=0 ENABLE_GMP=0 mm2-reader-objects

dependency: $(CETTA_DIR)/.git check-dependency

$(CETTA_DIR)/.git:
	@mkdir -p "$(dir $(CETTA_DIR))"
	@set -eu; \
	if test -e "$(CETTA_DIR)"; then \
		echo 'dependency destination already exists without a checkout' >&2; exit 2; \
	fi; \
	if test -n "$(CETTA_SOURCE)"; then \
		git -C "$(CETTA_SOURCE)" cat-file -e '$(CETTA_REVISION)^{commit}'; \
		git clone --shared --no-checkout "$(CETTA_SOURCE)" "$(CETTA_DIR)"; \
	else \
		git clone --filter=blob:none --no-checkout "$(CETTA_URL)" "$(CETTA_DIR)"; \
	fi; \
	git -C "$(CETTA_DIR)" checkout --detach "$(CETTA_REVISION)"

check-dependency: $(CETTA_DIR)/.git
	@test "$$(git -C "$(CETTA_DIR)" rev-parse HEAD)" = "$(CETTA_REVISION)" || \
		{ echo 'native reader dependency revision does not match source.lock' >&2; exit 2; }
	@git -C "$(CETTA_DIR)" diff --quiet && \
		git -C "$(CETTA_DIR)" diff --cached --quiet || \
		{ echo 'native reader dependency has modified tracked source' >&2; exit 2; }
