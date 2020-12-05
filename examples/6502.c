//
// -- SIMPLE 6502 COMPILER --
//

#include <stdio.h>
#include <str.h>

typedef char* charp;

#define P
#define T char
#include <deq.h>

#define T str
#include <vec.h>

deq_char feed;

struct
{
    int line;
    int addr;
    str function;
}
global;

#define quit(message, ...) { printf("error: line %d: "message"\n", global.line, __VA_ARGS__); exit(1); }

typedef struct
{
    str type;
    str name;
    size_t size;
    size_t addr;
    vec_str args; // For functions.
}
token;

token
token_copy(token* self)
{
    return (token) {
        str_copy(&self->type),
        str_copy(&self->name),
        self->size,
        self->addr,
        vec_str_copy(&self->args),
    };
}

void
token_free(token* self)
{
    str_free(&self->type);
    str_free(&self->name);
    vec_str_free(&self->args);
}

int
token_key_compare(token* a, token* b)
{
    return strcmp(a->name.value, b->name.value);
}

token
identifier(char* type, char* name, size_t size, size_t addr)
{
    return (token) {
        str_init(type),
        str_init(name),
        size,
        addr,
        vec_str_init(),
    };
}

token
keyword(char* name, size_t size)
{
    return identifier(name, name, size, 0);
}

#define W "12" // Table column width.

void
token_print(token* self)
{
    printf("%"W"s %"W"s %"W"lu %"W"lu %"W"lu\n",
        self->name.value,
        self->type.value,
        self->size,
        self->addr,
        self->args.size);
}

#define T token
#include <set.h>

set_token tokens;

void
dump(void)
{
    printf("%"W"s %"W"s %"W"s %"W"s %"W"s\n", "NAME", "VALUE", "SIZE", "ADDR", "FN ARGS");
    foreach(set_token, &tokens, it, token_print(it.ref);)
}

token*
find(str* name)
{
    token key;
    key.name = *name;
    set_token_node* node = set_token_find(&tokens, key);
    if(node)
        return &node->key;
    return NULL;
}

void
insert(token t)
{
    set_token_insert(&tokens, t);
}

void
queue(str* code)
{
    for(size_t i = 0; i < code->size; i++)
        deq_char_push_back(&feed, code->value[i]);
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
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

int
is_operator(char c)
{
    return !is_space(c) && !is_digit(c) && !is_alpha(c) && c != '(';
}

int
valid_operator(str* s)
{
    return str_compare(s, "+") == 0
        || str_compare(s, "-") == 0;
}

int
is_ident(char c)
{
    return is_digit(c) || is_alpha(c) || c == '_';
}

void
pop(void)
{
    deq_char_pop_front(&feed);
}

int
end(void)
{
    return deq_char_empty(&feed);
}

char
front(void)
{
    return *deq_char_front(&feed);
}

void
space(void)
{
    for(char c; !end() && is_space(c = front());)
    {
        if(c == '\n')
            global.line += 1;
        pop();
    }
}

char
next(void)
{
    space();
    return front();
}

void
match(char c)
{
    if(next() != c)
        quit("expected '%c' but got '%c'\n", c, next());
    pop();
}

str
read(int pred(char))
{
    space();
    str s = str_init("");
    for(char c; pred(c = front());)
    {
        str_push_back(&s, c);
        pop();
    }
    return s;
}

int
is_ref(str* t)
{
    return *str_back(t) == '&';
}

charp
infer(str* t)
{
    charp type;
    if(is_digit(t->value[0]))
        type = "u8";
    else
    {
        int ref = is_ref(t);
        if(ref)
            str_pop_back(t);
        token* tok = find(t);
        if(tok)
        {
            if(ref)
            {
                str temp = str_copy(&tok->type);
                str_append(&temp, "&");
                token* ref_tok = find(&temp);
                if(ref_tok)
                    type = ref_tok->type.value;
                else
                    quit("type '%s' not defined; type inference failed", temp.value);
                str_free(&temp);
            }
            else
                type = tok->type.value;
        }
        else
            quit("type '%s' not defined; type inference failed", t->value);
    }
    return type;
}

str
expression(void);

str
term(void)
{
    if(next() == '(')
    {
        match('(');
        str out = expression();
        match(')');
        return out;
    }
    else
    if(is_digit(next()))
        return read(is_digit);
    else
    if(is_ident(next()))
        return read(is_ident);
    else
    {
        char unary = next();
        if(unary == '&')
        {
            match('&');
            str name = read(is_ident);
            str_append(&name, "&");
            return name;
        }
        else
            quit("unary operator '%c' not supported; term generation failed", unary);
        return str_init("");
    }
}

str
expression(void)
{
    str t = term();
    charp a = infer(&t);
    while(1)
    {
        if(next() == ')')
            break;
        if(next() == ';')
            break;
        str o = read(is_operator);
        if(str_empty(&o))
            quit("missing operator - expression generation failed - previous term was %s", t.value);
        if(!valid_operator(&o))
            quit("invalid operator '%s'; expression generation failed", o.value);
        str_free(&o);
        str u = term();
        charp b = infer(&u);
        if(strcmp(a, b) != 0)
            quit("type mismatch - expression generation failed - types are '%s' and '%s'", a, b);
        str_free(&u);
    }
    str_free(&t);
    return str_init(a);
}

void
evaluate(str* ident)
{
    if(next() == ';')
        quit("expression may not be empty - assignment evaluation failed - see identifier '%s'", ident->value);
    str type = expression();
    token* defined = find(&type);
    if(!defined)
        quit("type '%s' not defined; evaluation failed", type.value);
    token* exists = find(ident);
    if(exists)
    {
        if(str_key_compare(&type, &exists->type) != 0)
            quit("assignment type mismatch - evaluation failed - '%s' and '%s'", type.value, exists->type.value);
    }
    else
    {
        insert(identifier(type.value, ident->value, defined->size, global.addr));
        global.addr += defined->size;
    }
    str_free(&type);
}

void
fallback(str* ident)
{
    for(size_t i = 0; i < ident->size; i++)
        deq_char_push_front(&feed, ident->value[i]);
    if(next() == ';')
        quit("expressions may not be empty - fallback expression failed - see identifier '%s'", ident->value);
    str type = expression();
    str_free(&type);
}

void
ret(void)
{
    token* tok = find(&global.function);
    if(str_compare(&tok->type, "void") != 0)
    {
        if(next() == ';')
            quit("empty return statement in function '%s' requires type '%s'; return statement failed", global.function.value, tok->type.value);
        str type = expression();
        if(str_compare(&tok->type, type.value) != 0)
            quit("computed return statement in function '%s' is '%s' but expected '%s'; return statement failed", global.function.value, type.value, tok->type.value);
        str_free(&type);
    }
    else
    if(next() != ';')
        quit("void function '%s' may not compute a return expression; return statement failed", global.function.value);
    match(';');
}

void
statement(void)
{
    while(1)
    {
        if(next() == ';')
            match(';');
        if(next() == '}')
            break;
        str ident = read(is_ident);
        if(next() == '=')
        {
            match('=');
            if(next() == ';')
                quit("assignments may not be empty - statement failed - see '%s'", ident.value);
            evaluate(&ident);
        }
        else
        if(str_compare(&ident, "return") == 0)
            ret();
        else
            fallback(&ident);
        str_free(&ident);
    }
}

void
block(void)
{
    match('{');
    statement();
    match('}');
}

str
type(void)
{
    str ident = read(is_ident);
    if(next() == '&')
    {
        str_push_back(&ident, '&');
        pop();
    }
    return ident;
}

vec_str
function_params(void)
{
    match('(');
    vec_str args = vec_str_init();
    while(1)
    {
        if(next() == ')')
            break;
        str t = type();
        str n = read(is_ident);
        if(find(&n))
            quit("function arguments must be unique - failed function definition - see type '%s'", t.value);
        token* tok = find(&t);
        if(!tok)
            quit("unknown type in function paramater list - failed function definition - see type '%s'", t.value);
        insert(identifier(t.value, n.value, tok->size, global.addr));
        global.addr += tok->size;
        vec_str_push_back(&args, str_copy(&t));
        str_free(&t);
        str_free(&n);
        if(next() == ',')
            match(',');
    }
    match(')');
    return args;
}

token
function_sign(void)
{
    token sig;
    if(next() == '-')
    {
        match('-');
        match('>');
        str t = type();
        token* tok = find(&t);
        if(!tok)
            quit("unknown function return type; failed function definition - see '%s'", t.value);
        sig = identifier(t.value, global.function.value, tok->size, 0);
        str_free(&t);
    }
    else
        sig = identifier("void", global.function.value, 0, 0);
    return sig;
}

void
function(void)
{
    str name = read(is_ident);
    str_swap(&name, &global.function);
    str_free(&name);
    if(find(&global.function))
        quit("function '%s' already defined; failed function definition", global.function.value);
    vec_str args = function_params();
    token sig = function_sign();
    sig.args = args;
    insert(sig);
    block();
}

void
program(void)
{
    while(1)
    {
        function();
        space();
        if(end())
            break;
    }
}

void
setup(void)
{
    feed = deq_char_init();
    tokens = set_token_init(token_key_compare);
    insert(keyword("u8", 1));
    insert(keyword("u8&", 2));
    insert(keyword("void", 0));
    insert(keyword("return", 0));
    global.line = 0;
    global.addr = 0;
    str_free(&global.function);
}

void
compile(char* text)
{
    setup();
    str code = str_init(text);
    queue(&code);
    program();
    dump();
    str_free(&code);
    deq_char_free(&feed);
    set_token_free(&tokens);
}

void
test_spacing(void)
{
    compile(
        "main()                    \n"
        "{                         \n"
        "    a = 0;                \n"
        "    a  = 1+0+1;           \n"
        "    a   = 1+(0)+1;        \n"
        "    a    = 1+(0+0)+1;     \n"
        "    b =  1 + ( 0+0 ) + 1; \n"
        "    b =  1 + (  0  ) + 1; \n"
        "    b =  1 + (0 + 0) + 1; \n"
        "    0;                    \n"
        "    1+0+1;                \n"
        "    1+(0)+1;              \n"
        "    1+(0+0)+1;            \n"
        "    1 + ( 0+0 ) + 1;      \n"
        "    1 + (  0  ) + 1;      \n"
        "    1 + (0 + 0) + 1;      \n"
        "}                         \n");
}

void
test_pointer_init(void)
{
    compile(
        "fun() -> u8              \n"
        "{                        \n"
        "    a = 1;               \n"
        "    return 1;            \n"
        "}                        \n"
        "nuf(u8& test, u8 z)      \n"
        "{                        \n"
        "    a = 1;               \n"
        "    b = &a;              \n"
        "    a + fun;             \n"
        "    return;              \n"
        "}                        \n"
        "main()                   \n"
        "{                        \n"
        "    a = 1;               \n"
        "}                        \n");
}

int
main(void)
{
    test_spacing();
    test_pointer_init();
}