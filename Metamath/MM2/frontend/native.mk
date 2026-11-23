ifndef MM2_FRONTEND_ROOT
$(error MM2_FRONTEND_ROOT must name the frontend source directory)
endif
include Makefile
include $(MM2_FRONTEND_ROOT)/source.lock
.DEFAULT_GOAL := mm2-native

MM2_BUILD := $(dir $(MM2_OUTPUT))
MM2_SOURCES := reader model wire emit_source emit native_main
MM2_OBJECTS := $(addprefix $(MM2_BUILD),$(addsuffix .o,$(MM2_SOURCES)))
MM2_CURSOR_OBJECT := $(MM2_BUILD)native_cursor.o

.PHONY: mm2-native mm2-reader-objects
mm2-native: $(MM2_OUTPUT)
mm2-reader-objects: $(PARSER_PACK_CURSOR_GENERATED_V1_LINK_OBJ) \
		$(MM2_CURSOR_OBJECT) $(MM2_BUILD)reader.o

$(MM2_BUILD)%.o: $(MM2_FRONTEND_ROOT)/%.c \
		$(MM2_FRONTEND_ROOT)/reader.h $(MM2_FRONTEND_ROOT)/source.lock \
		$(MM2_FRONTEND_ROOT)/native.mk $(BUILD_CONFIG_HEADER)
	@mkdir -p "$(dir $@)"
	$(CC) $(CPPFLAGS) -I"$(MM2_FRONTEND_ROOT)" \
		-DMM2_CETTA_REVISION='"$(CETTA_REVISION)"' $(CFLAGS) $(DEPFLAGS) \
		-MF "$(@:.o=.d)" -c -o "$@" "$<"

$(MM2_CURSOR_OBJECT): $(BUILD_CONFIG_HEADER) $(MM2_FRONTEND_ROOT)/source.lock \
		$(MM2_FRONTEND_ROOT)/native.mk
	@mkdir -p "$(dir $@)"
	@git cat-file -e "$(CETTA_REVISION):$(CETTA_CURSOR_SOURCE)"
	git show "$(CETTA_REVISION):$(CETTA_CURSOR_SOURCE)" | \
	$(CC) $(CPPFLAGS) $(CFLAGS) $(DEPFLAGS) -MF "$(@:.o=.d)" \
		-x c -c -o "$@" -

$(MM2_OUTPUT): $(MM2_OBJECTS) $(MM2_CURSOR_OBJECT) \
		$(PARSER_PACK_CURSOR_GENERATED_V1_LINK_OBJ)
	$(CC) $(CFLAGS) -Wl,--gc-sections -o "$@" $^ $(LDFLAGS)

-include $(MM2_OBJECTS:.o=.d)
