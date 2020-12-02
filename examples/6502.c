//
// -- SIMPLE 6502 COMPILER --
//

#include <stdarg.h>
#include <stdio.h>
#include <str.h>

#define P
#define T char
#include <deq.h>

size_t line = 0;

void
quit(char* message, ...)
{
    va_list args;
    va_start(args, message);
    printf("error: line %lu: ", line);
    vprintf(message, args);
    putchar('\n');
    va_end(args);
    exit(1);
}

#define BINDS X(TYPE) X(STRUCTURE) X(VARIABLE) X(INTERNAL)

typedef enum
{
#define X(name) name,
BINDS
#undef X
}
bind_t;

char*
printable(bind_t bind)
{
    return (char* [])
    {
#define X(name) #name,
BINDS
#undef X
    }
    [bind];
}

typedef struct
{
    bind_t bind;
    str type;
    str name; // KEY.
    size_t size;
    size_t offset;
}
var_t;

void
tab(size_t n)
{
    while(n--)
        printf("\t");
}

void
var_t_print(var_t* var, size_t tabs)
{
    tab(tabs); printf("name : %s\n", var->name.value);
    tab(tabs); printf("\tbind : %s\n", printable(var->bind));
    tab(tabs); printf("\ttype : %s\n", var->type.value);
    tab(tabs); printf("\tsize : %lu\n", var->size);
    tab(tabs); printf("\toffs : %lu\n", var->offset);
}

var_t
var_t_init(str type, str name, bind_t bind, size_t size, size_t offset)
{
    return (var_t)
    {
        .type = type,
        .name = name,
        .bind = bind,
        .size = size,
        .offset = offset,
    };
}

var_t
var_t_copy(var_t* self)
{
    return (var_t)
    {
        .type = str_copy(&self->name),
        .bind = self->bind,
        .name = str_copy(&self->type),
        .size = self->size,
        .offset = self->offset,
    };
}

void
var_t_free(var_t* self)
{
    str_free(&self->type);
    str_free(&self->name);
    *self = (var_t) { 0 };
}

int
var_t_key_compare(var_t* a, var_t* b)
{
    return str_key_compare(&a->name, &b->name);
}

#define T var_t
#include <set.h>

void
set_var_t_put(set_var_t* self, var_t var)
{
    if(set_var_t_contains(self, var))
        quit("'%s' already defined", var.name.value);
    set_var_t_insert(self, var);
}

var_t*
set_var_t_get(set_var_t* self, str name)
{
    set_var_t_node* node = set_var_t_find(self, (var_t) {.name = name});
    if(!node)
        quit("'%s' not defined", name.value);
    return &node->key;
}

typedef struct
{
    var_t var;
    set_var_t member; // FOR STRUCTURE.
}
tok_t;

void
tok_t_print(tok_t* tok)
{
    var_t_print(&tok->var, 0);
    foreach(set_var_t, &tok->member, it,
        var_t_print(it.ref, 2);
    )
}

tok_t
tok_t_init(var_t var)
{
    return (tok_t)
    {
        .var = var,
        .member = set_var_t_init(var_t_key_compare)
    };
}

tok_t
tok_t_copy(tok_t* self)
{
    return (tok_t)
    {
        .var = var_t_copy(&self->var),
        .member = set_var_t_copy(&self->member)
    };
}

void
tok_t_free(tok_t* self)
{
    var_t_free(&self->var);
    set_var_t_free(&self->member);
    *self = (tok_t) { 0 };
}

int
tok_t_key_compare(tok_t* a, tok_t* b)
{
    return var_t_key_compare(&a->var, &b->var);
}

tok_t
tok_t_keyword(str name, bind_t bind)
{
    var_t var = var_t_init(str_init(""), name, bind, 0, 0);
    return tok_t_init(var);
}

tok_t
tok_t_keyword_type(str name, bind_t bind, size_t size)
{
    tok_t tok = tok_t_keyword(name, bind);
    tok.var.size = size;
    return tok;
}

#define T tok_t
#include <set.h>

void
set_tok_t_put(set_tok_t* self, tok_t tok)
{
    if(set_tok_t_contains(self, tok))
        quit("'%s' already defined", tok.var.name.value);
    set_tok_t_insert(self, tok);
}

tok_t*
set_tok_t_get(set_tok_t* self, str name)
{
    set_tok_t_node* node = set_tok_t_find(self, (tok_t) {.var = {.name = name}});
    if(!node)
        quit("'%s' not defined", name.value);
    return &node->key;
}

deq_char
extract(str* code)
{
    deq_char feed = deq_char_init();
    foreach(str, code, it,
        deq_char_push_back(&feed, *it.ref);
    )
    return feed;
}

int
is_space(char c)
{
    return c == ' ' || c == '\n';
}

int
is_digit(char c)
{
    return c >= '0' && c <= '9';
}

int
is_alpha(char c)
{
    return (c >= 'a' && c <= 'z')
        || (c >= 'A' && c <= 'Z');
}

int
is_alnum(char c)
{
    return is_alpha(c) || is_digit(c);
}

int
is_ident(char c)
{
    return is_alnum(c) || c == '_';
}

char
peek(deq_char* feed)
{
    return *deq_char_front(feed);
}

void
pop(deq_char* feed)
{
    if(peek(feed) == '\n')
        line += 1;
    deq_char_pop_front(feed);
}

char
next(deq_char* feed)
{
    while(is_space(peek(feed)))
        pop(feed);
    return peek(feed);
}

void
match(deq_char* feed, char c)
{
    if(next(feed) != c)
        quit("expected %c", c);
    pop(feed);
}

str
identifier(deq_char* feed)
{
    if(!is_ident(next(feed)))
        quit("identfier must start with letter or underscore");
    str s = str_init("");
    while(is_ident(peek(feed)))
    {
        str_push_back(&s, peek(feed));
        pop(feed);
    }
    return s;
}

set_tok_t
setup_keywords(void)
{
    set_tok_t toks = set_tok_t_init(tok_t_key_compare);
    char* internals[] = {
        "if",
        "else",
        "while",
        "def",
        "struct"
    };
    for(size_t i = 0; i < len(internals); i++)
        set_tok_t_put(&toks, tok_t_keyword(str_init(internals[i]), INTERNAL));
    struct
    {
        char* a;
        size_t b;
    }
    types[] = {
        { "u8",   1 },
        { "void", 0 },
    };
    for(size_t i = 0; i < len(types); i++)
        set_tok_t_put(&toks, tok_t_keyword_type(str_init(types[i].a), TYPE, types[i].b));
    return toks;
}

void
structure(deq_char* feed, set_tok_t* toks)
{
    tok_t tok = tok_t_keyword(identifier(feed), STRUCTURE);
    match(feed, '{');
    size_t offset = 0;
    while(next(feed) != '}')
    {
        str type = identifier(feed);
        str name = identifier(feed);
        size_t size = set_tok_t_get(toks, type)->var.size;
        var_t var = var_t_init(type, name, VARIABLE, size, offset);
        set_var_t_put(&tok.member, var);
        offset += size;
        match(feed, ';');
    }
    tok.var.size = offset;
    set_tok_t_put(toks, tok);
    match(feed, '}');
}

void
program(deq_char* feed)
{
    set_tok_t toks = setup_keywords();
    str s = identifier(feed);
    if(str_match(&s, "struct"))
        structure(feed, &toks);
    else
    if(str_match(&s, "proc"))
        procedure(feed, &toks);
    str_free(&s);
    foreach(set_tok_t, &toks, it, tok_t_print(it.ref);)
    set_tok_t_free(&toks);
}

int
main(void)
{
    str code = str_init(
        "                 \n"
        "   struct person \n"
        "   {             \n"
        "       u8 a;     \n"
        "       u8 b;     \n"
        "       u8 c;     \n"
        "       u8 d;     \n"
        "       u8 e;     \n"
        "       u8 f;     \n"
        "       u8 g;     \n"
        "   }             \n"
        "   proc main()   \n"
        "   {             \n"
        "   }             \n"
    );
    deq_char feed = extract(&code);
    program(&feed);
    deq_char_free(&feed);
    str_free(&code);
}
