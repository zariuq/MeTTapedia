#ifndef METTAPEDIA_MM2_EMIT_H
#define METTAPEDIA_MM2_EMIT_H

#include "reader.h"
#include <stdio.h>

void mm2_emit_statement(FILE *out, const mm2_source *source,
                        const mm2_statement *statement);
void mm2_emit_event_rows(FILE *out, const mm2_source *source,
                         const char *owner);
mm2_status mm2_emit_data(FILE *out, const mm2_source *source,
                         const char *owner, mm2_error *error);

#endif
