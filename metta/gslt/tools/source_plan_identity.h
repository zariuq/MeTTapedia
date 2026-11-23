#ifndef GSLT_SOURCE_PLAN_IDENTITY_H
#define GSLT_SOURCE_PLAN_IDENTITY_H
/* Source-plan identity encoding is shared with the in-process reader. */
#include "native/source_plan_identity_v1.h"

static bool write_plan_identity(const char *forest_path, const PPABIV1Pack *pack,
    char *error, size_t error_size) {
    uint8_t *bytes=NULL;size_t size=0u;
    if(!source_plan_identity_bytes(pack,&bytes,&size,error,error_size))return false;
    size_t length=strlen(forest_path);
    if(length>SIZE_MAX-5u){free(bytes);return false;}
    char *path=malloc(length+5u);
    if(!path){free(bytes);return false;}
    memcpy(path,forest_path,length);memcpy(path+length,".pni",5u);
    FILE *stream=fopen(path,"wb");free(path);
    bool ok=stream&&fwrite(bytes,1u,size,stream)==size;
    if(stream&&fclose(stream)!=0)ok=false;
    free(bytes);return ok;
}
#endif
