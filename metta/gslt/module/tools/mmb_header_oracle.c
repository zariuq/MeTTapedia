#include "native/mm0/mm0_mmb.c"
#include <inttypes.h>
#include <string.h>

/* Observe the existing reader's header check and command primitive. */
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    FILE *f = fopen(argv[2], "rb");
    if (!f || fseek(f, 0, SEEK_END)) return 2;
    long size = ftell(f);
    if (size < 0 || fseek(f, 0, SEEK_SET)) return 2;
    uint8_t *input = malloc(size ? (size_t)size : 1);
    if (!input || fread(input, 1, (size_t)size, f) != (size_t)size) return 2;
    fclose(f);
    Mm0Error error = {0};
    Mmb v = {.file=input, .end=input+size, .len=(size_t)size, .error=&error};
    if (!strcmp(argv[1], "header")) {
        if (!check_header(&v)) {
            printf("(MMBOracleRefused \"%s\")\n", error.reason);
        } else {
            printf("(MMBHeaderValue %u %u %u %u %u %u %u %u %u %u %" PRIu64 ")\n",
                mm0_le32(input), input[4], input[5], mm0_le16(input+6),
                v.num_terms, v.num_thms, mm0_le32(input+16), mm0_le32(input+20),
                mm0_le32(input+24), mm0_le32(input+28), mm0_le64(input+32));
        }
    } else if (!strcmp(argv[1], "command")) {
        MmbCmd cmd;
        if (!cmd_at(&v, input, &cmd)) return 1;
        printf("(MMBCommandValue %u %u %u)\n", cmd.op, cmd.data, cmd.size);
    } else return 2;
    free(input); return 0;
}
