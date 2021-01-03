# map_T_insert_or_assign (T key) - CTL - C Container Template library

Defined in header [**<ctl/map.h>**](../map.md)

# SYNOPSIS

      map_charint_it *iter = map_charint_insert_or_assign (&a,
                               charint_copy(&(charint){ "test", 0 }));

      int found;
      map_charint_it *iter = map_charint_insert_or_assign_found (&a,
                               charint_copy(&(charint){ "test", 0 }, &found));

# DESCRIPTION

If the key exists in the container, replaces the old value with the new one.
Returns an iterator at the position in the container.

If the key does not exists in the container, adds the new key.
Returns an iterator at the position in the container.

The _found variant replaces the pair variants from C++, and sets int *found 
to 0 or 1, if found.

# SEEALSO

[map_T_insert](insert.md)

