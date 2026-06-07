#include "glibc_slist_raw.h"

struct glibc_slist *glibc_slist_copy(const struct glibc_slist *src)
{
    struct glibc_slist *dst;
    struct glibc_slist_node *pos;
    struct glibc_slist_node *copy;

    dst = malloc(sizeof(*dst));
    if (dst == NULL) {
        return NULL;
    }

    SLIST_INIT(dst);
    SLIST_FOREACH(pos, src, link) {
        copy = glibc_slist_new_node(pos->data);
        if (copy == NULL) {
            struct glibc_slist_node *tmp;
            while (!SLIST_EMPTY(dst)) {
                tmp = SLIST_FIRST(dst);
                SLIST_REMOVE_HEAD(dst, link);
                free(tmp);
            }
            free(dst);
            return NULL;
        }
        glibc_slist_insert_tail(dst, copy);
    }
    return dst;
}
