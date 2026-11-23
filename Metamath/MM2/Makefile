MM2_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
CC ?= cc
CHECK_CFLAGS ?= -std=c11 -Wall -Wextra -Wpedantic -Werror
CHECK_DIR := $(MM2_ROOT)/.build/tests

.PHONY: all frontend test
all: frontend

frontend:
	$(MAKE) -C "$(MM2_ROOT)/frontend"

$(CHECK_DIR):
	mkdir -p "$@"

$(CHECK_DIR)/test_model: $(MM2_ROOT)/tests/test_model.c \
		$(MM2_ROOT)/frontend/model.c $(MM2_ROOT)/frontend/model.h \
		$(MM2_ROOT)/frontend/reader.h | $(CHECK_DIR)
	$(CC) $(CHECK_CFLAGS) -I"$(MM2_ROOT)/frontend" \
		"$(MM2_ROOT)/tests/test_model.c" "$(MM2_ROOT)/frontend/model.c" -o "$@"

$(CHECK_DIR)/test_wire: $(MM2_ROOT)/tests/test_wire.c \
		$(MM2_ROOT)/frontend/wire.c $(MM2_ROOT)/frontend/wire.h \
		$(MM2_ROOT)/frontend/reader.h | $(CHECK_DIR)
	$(CC) $(CHECK_CFLAGS) -I"$(MM2_ROOT)/frontend" \
		"$(MM2_ROOT)/tests/test_wire.c" "$(MM2_ROOT)/frontend/wire.c" -o "$@"

test: frontend $(CHECK_DIR)/test_model $(CHECK_DIR)/test_wire
	"$(CHECK_DIR)/test_model"
	"$(CHECK_DIR)/test_wire"
	python3 -m unittest discover -s "$(MM2_ROOT)/tests" -p 'test_*.py' -v
