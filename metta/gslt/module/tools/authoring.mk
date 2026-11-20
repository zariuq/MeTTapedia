# Optional clients of an existing CeTTa build. Include after CeTTa's Makefile.
# Set MODULE_TOOLS_SOURCE_DIR and MODULE_TOOLS_OUTPUT_DIR explicitly.
.PHONY: module-authoring-client holr-scan-oracle mmb-header-oracle

module-authoring-client:
	@test -n "$(MODULE_TOOLS_SOURCE_DIR)" -a -n "$(MODULE_TOOLS_OUTPUT_DIR)"
	@mkdir -p "$(MODULE_TOOLS_OUTPUT_DIR)"
	$(CC) $(CPPFLAGS) $(CFLAGS) "$(MODULE_TOOLS_SOURCE_DIR)/module_authoring.c" $(FALLBACK_EVAL_TEST_LINK_OBJ) $(BRIDGE_DEPS) $(LDFLAGS) -o "$(MODULE_TOOLS_OUTPUT_DIR)/module-authoring"

holr-scan-oracle:
	@test -n "$(MODULE_TOOLS_SOURCE_DIR)" -a -n "$(MODULE_TOOLS_OUTPUT_DIR)"
	@mkdir -p "$(MODULE_TOOLS_OUTPUT_DIR)"
	$(CC) $(CPPFLAGS) $(CFLAGS) "$(MODULE_TOOLS_SOURCE_DIR)/holr_scan_oracle.c" native/hol_light/hol_stream.c $(filter-out native/hol_light/hol_stream.$(BUILD_OBJ_TAG).o,$(FALLBACK_EVAL_TEST_LINK_OBJ)) $(BRIDGE_DEPS) $(LDFLAGS) -o "$(MODULE_TOOLS_OUTPUT_DIR)/holr-scan-oracle"

mmb-header-oracle:
	@test -n "$(MODULE_TOOLS_SOURCE_DIR)" -a -n "$(MODULE_TOOLS_OUTPUT_DIR)"
	@mkdir -p "$(MODULE_TOOLS_OUTPUT_DIR)"
	$(CC) $(CPPFLAGS) $(CFLAGS) "$(MODULE_TOOLS_SOURCE_DIR)/mmb_header_oracle.c" $(filter-out native/mm0/mm0_mmb.$(BUILD_OBJ_TAG).o,$(FALLBACK_EVAL_TEST_LINK_OBJ)) $(BRIDGE_DEPS) $(LDFLAGS) -o "$(MODULE_TOOLS_OUTPUT_DIR)/mmb-header-oracle"
