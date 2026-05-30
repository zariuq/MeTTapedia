#include <stddef.h>

static int conf_eq(const unsigned char *conf, long conf_len, const char *s) {
  long i = 0;
  while (s[i] != '\0') {
    if (i >= conf_len || conf[i] != (unsigned char)s[i]) {
      return 0;
    }
    i++;
  }
  return i == conf_len;
}

void fficall_ml(unsigned char *conf, long conf_len,
                unsigned char *bytes, long bytes_len) {
  if (bytes_len < 4) {
    return;
  }

  if (!conf_eq(conf, conf_len, "call-ml") &&
      !conf_eq(conf, conf_len, "call-native:call-ml")) {
    bytes[0] = 2;
    bytes[3] = 254;
    return;
  }

  if (bytes[0] != 1) {
    bytes[0] = 3;
    bytes[3] = 255;
    return;
  }

  bytes[0] = 0;
  bytes[1] = (unsigned char)(bytes[1] + 1);
  bytes[2] = (unsigned char)(bytes[2] + conf_len);
  bytes[3] = 7;
}
