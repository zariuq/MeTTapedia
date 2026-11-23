#define _POSIX_C_SOURCE 200809L

#include "emit.h"
#include "wire.h"

#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef MM2_CETTA_REVISION
#error MM2_CETTA_REVISION must come from source.lock
#endif

static void usage(FILE *out) {
    fputs("usage: mm2-translate INPUT.mm --output DATA.mm2 "
          "[--profile zar] [--owner NAME] [--root-name unit.mm]\n"
          "       mm2-translate INPUT.mm --source-identities [--root-name unit.mm]\n"
          "       mm2-translate --identity\n", out);
}

static void diagnostic(const mm2_source *source, const mm2_error *error) {
    const char *kind = error->status == MM2_REJECTED ? "source rejected" : "failure";
    fprintf(stderr, "mm2-translate: %s", kind);
    if (error->source_id < source->file_count)
        fprintf(stderr, " in %s", source->files[error->source_id].name);
    else if (error->source_id != UINT32_MAX)
        fprintf(stderr, " in source %u", error->source_id);
    if (error->end > error->start)
        fprintf(stderr, " at bytes %zu..%zu", error->start, error->end);
    fprintf(stderr, ": %s\n", error->message);
}

static bool valid_name(const char *name) {
    return name[0] && mm2_wire_valid_utf8((const uint8_t *)name, strlen(name));
}

static bool same_file(const char *input, const char *output) {
    struct stat in, out;
    return stat(input, &in) == 0 && stat(output, &out) == 0 &&
           in.st_dev == out.st_dev && in.st_ino == out.st_ino;
}

static bool aliases_source(const mm2_source *source, const char *output) {
    struct stat metadata;
    if (stat(output, &metadata) != 0) return false;
    for (size_t i = 0; i < source->file_count; ++i)
        if (source->files[i].physical_device == (uintmax_t)metadata.st_dev &&
            source->files[i].physical_inode == (uintmax_t)metadata.st_ino)
            return true;
    return false;
}

int main(int argc, char **argv) {
    const char *input = NULL, *output = NULL;
    const char *profile = MM2_READER_PROFILE;
    const char *owner = "metamath-test-unit", *root_name = "unit.mm";
    bool output_seen = false, profile_seen = false, owner_seen = false, root_seen = false;
    bool identities = false;
    mm2_reader_options options;
    mm2_source source = {0};
    mm2_error error;
    mm2_status status;
    char *staging = NULL;
    FILE *stream = NULL;
    int descriptor, result = MM2_ERROR;

    if (argc == 2 && strcmp(argv[1], "--identity") == 0) {
        printf("{\"schema\":\"%s\",\"profile\":\"%s\",\"version\":\"%s\","
               "\"reader_dependency\":\"CeTTa\",\"reader_revision\":\"%s\"}\n",
               MM2_SOURCE_DATA_SCHEMA, MM2_READER_PROFILE, MM2_READER_VERSION,
               MM2_CETTA_REVISION);
        return ferror(stdout) ? MM2_ERROR : MM2_OK;
    }
    for (int i = 1; i < argc; ++i) {
        const char *argument = argv[i];
        const char **target = NULL;
        bool *seen = NULL;
        if (strcmp(argument, "--source-identities") == 0 && !identities) {
            identities = true;
            continue;
        }
        if (strcmp(argument, "--output") == 0) { target = &output; seen = &output_seen; }
        else if (strcmp(argument, "--profile") == 0) { target = &profile; seen = &profile_seen; }
        else if (strcmp(argument, "--owner") == 0) { target = &owner; seen = &owner_seen; }
        else if (strcmp(argument, "--root-name") == 0) { target = &root_name; seen = &root_seen; }
        else if (argument[0] != '-' && !input) { input = argument; continue; }
        else { usage(stderr); return MM2_ERROR; }
        if (*seen || i + 1 == argc) { usage(stderr); return MM2_ERROR; }
        *target = argv[++i];
        *seen = true;
    }
    if (!input || (identities ? output != NULL : (!output || !output[0])) ||
        strcmp(profile, MM2_READER_PROFILE) != 0) {
        usage(stderr);
        return MM2_ERROR;
    }
    if (!valid_name(owner) || !valid_name(root_name)) {
        fputs("mm2-translate: owner and root name must be nonempty UTF-8 strings\n", stderr);
        return MM2_ERROR;
    }
    if (output && same_file(input, output)) {
        fputs("mm2-translate: output must not replace the source input\n", stderr);
        return MM2_ERROR;
    }
    options = (mm2_reader_options){root_name, MM2_INCLUDE_BOOK};
    status = mm2_read_source(input, &options, &source, &error);
    if (status != MM2_OK) {
        diagnostic(&source, &error);
        result = status;
        goto done;
    }
    if (identities) {
        fputs("{\"schema\":\"mm2-source-identities-v1\",\"files\":[", stdout);
        for (size_t i = 0; i < source.file_count; ++i) {
            printf("%s{\"device\":%" PRIuMAX ",\"inode\":%" PRIuMAX "}",
                   i ? "," : "", source.files[i].physical_device,
                   source.files[i].physical_inode);
        }
        fputs("]}\n", stdout);
        result = fflush(stdout) != 0 || ferror(stdout) ? MM2_ERROR : MM2_OK;
        goto done;
    }
    if (aliases_source(&source, output)) {
        fputs("mm2-translate: output must not replace an expanded source file\n", stderr);
        goto done;
    }
    if (strlen(output) > SIZE_MAX - sizeof(".stage.XXXXXX")) {
        fputs("mm2-translate: output name is too long\n", stderr);
        goto done;
    }
    staging = malloc(strlen(output) + sizeof(".stage.XXXXXX"));
    if (!staging) {
        fputs("mm2-translate: cannot allocate output staging name\n", stderr);
        goto done;
    }
    sprintf(staging, "%s.stage.XXXXXX", output);
    descriptor = mkstemp(staging);
    if (descriptor < 0) {
        fprintf(stderr, "mm2-translate: cannot create output staging file: %s\n", strerror(errno));
        goto done;
    }
    stream = fdopen(descriptor, "wb");
    if (!stream) {
        int saved_errno = errno;
        close(descriptor);
        fprintf(stderr, "mm2-translate: cannot open output staging stream: %s\n", strerror(saved_errno));
        goto retained;
    }
    status = mm2_emit_data(stream, &source, owner, &error);
    if (status != MM2_OK) {
        diagnostic(&source, &error);
        result = status;
        goto retained;
    }
    if (fflush(stream) != 0 || ferror(stream)) {
        fputs("mm2-translate: cannot flush output staging stream\n", stderr);
        goto retained;
    }
    if (fclose(stream) != 0) {
        stream = NULL;
        fputs("mm2-translate: cannot close output staging stream\n", stderr);
        goto retained;
    }
    stream = NULL;
    if (rename(staging, output) != 0) {
        fprintf(stderr, "mm2-translate: cannot publish output: %s\n", strerror(errno));
        goto retained;
    }
    result = MM2_OK;
    goto done;
retained:
    if (stream) { fclose(stream); stream = NULL; }
    fprintf(stderr, "mm2-translate: retained staging file %s\n", staging);
done:
    free(staging);
    mm2_source_free(&source);
    return result;
}
