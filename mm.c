#include <stddef.h>

int mm_init(void) { return 0; }
void *malloc(size_t size) { return NULL; }
void free(void *ptr) {}
void *realloc(void *ptr, size_t size) { return NULL; }
void *calloc (size_t nmemb, size_t size) { return NULL; }
void mm_checkheap(void) {}
