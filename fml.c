#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdalign.h>
#include <string.h>
#include <assert.h>
#include <inttypes.h>
#include <setjmp.h>

#define PROJECT_NAME "fml"

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

#define UNREACHABLE() unreachable(__FILE__, __LINE__)
_Noreturn void
unreachable(char *file, size_t line)
{
	fprintf(stderr, "ERROR: unreachable code reached at %s:%zu\n", file, line);
	exit(EXIT_FAILURE);
}

typedef struct ArenaChunk ArenaChunk;

struct ArenaChunk {
	size_t size;
	size_t pos;
	ArenaChunk *prev;
	alignas(u64) u8 mem[];
};

typedef struct {
	ArenaChunk *current;
	size_t prev_size_sum;
} Arena;

void
arena_init(Arena *arena)
{
	size_t size = 1024;
	ArenaChunk *chunk = malloc(sizeof(ArenaChunk) + size);
	chunk->prev = NULL;
	chunk->size = size;
	chunk->pos = 0;
	arena->current = chunk;
	arena->prev_size_sum = 0;
}

void
arena_destroy(Arena *arena)
{
	ArenaChunk *chunk = arena->current;
	while (chunk) {
		ArenaChunk *prev = chunk->prev;
		free(chunk);
		chunk = prev;
	}
}

void *
arena_alloc(Arena *arena, size_t size)
{
	if (arena->current->pos + size > arena->current->size) {
		arena->prev_size_sum += arena->current->size;
		size_t new_size = size + arena->current->size * 2;
		ArenaChunk *new = malloc(sizeof(ArenaChunk) + new_size);
		new->size = new_size;
		new->pos = 0;
		new->prev = arena->current;
		arena->current = new;
	}
	size_t pos = (arena->current->pos + 7) & ~7;
	arena->current->pos = pos + size;
	return &arena->current->mem[pos];
}

size_t
arena_save(Arena *arena)
{
	return arena->prev_size_sum + arena->current->pos;
}

void
arena_restore(Arena *arena, size_t pos)
{
	ArenaChunk *chunk = arena->current;
	while (chunk && pos < arena->prev_size_sum) {
		ArenaChunk *prev = chunk->prev;
		free(chunk);
		chunk = prev;
		arena->prev_size_sum -= chunk->size;
	}
	chunk->pos = pos - arena->prev_size_sum;
	arena->current = chunk;
}

u8 *
arena_vaprintf(Arena *arena, const char *fmt, va_list ap)
{
	va_list ap_orig;
	// save original va_list (vprintf changes it)
	va_copy(ap_orig, ap);

	size_t available = arena->current->size - arena->current->pos;
	void *mem = &arena->current->mem[arena->current->pos];
	int len = vsnprintf(mem, available, fmt, ap);
	assert(len >= 0);
	len += 1;
	if ((size_t) len <= available) {
		arena->current->pos += (size_t) len;
		va_copy(ap, ap_orig);
		mem = arena_alloc(arena, (size_t) len);
		len = vsnprintf(mem, (size_t) len, fmt, ap);
	}
	va_end(ap_orig);
	return mem;
}

typedef struct {
	u8 *mem;
	size_t pos;
	size_t capacity;
} GArena;

void
garena_init(GArena *arena)
{
	arena->mem = NULL;
	arena->pos = 0;
	arena->capacity = 0;
}

void
garena_destroy(GArena *arena)
{
	free(arena->mem);
}

void *
garena_alloc(GArena *arena, size_t size, size_t alignment)
{
	if (arena->pos + size > arena->capacity) {
		arena->capacity = arena->capacity ? arena->capacity * 2 : size * 8;
		arena->mem = realloc(arena->mem, arena->capacity);
	}
	size_t pos = (arena->pos + (alignment - 1)) & ~(alignment - 1);
	arena->pos = pos + size;
	return &arena->mem[pos];
}

size_t
garena_save(GArena *arena)
{
	return arena->pos;
}

void *
garena_restore(GArena *arena, size_t pos)
{
	arena->pos = pos;
	return &arena->mem[pos];
}

void *
garena_mem(GArena *arena)
{
	return arena->mem;
}

#define garena_cnt(arena, type) (((arena)->pos) / sizeof(type))
#define garena_cnt_from(arena, type, start) ((((arena)->pos) - (start)) / sizeof(type))
#define garena_push(arena, type) ((type *)garena_alloc((arena), sizeof(type), alignof(type)))
#define garena_push_value(arena, type, value) do { type tmp_pushed_ = (value); *garena_push((arena), type) = tmp_pushed_; } while (0)

#define move_to_arena(arena, garena, start, type) move_to_arena_((arena), (garena), (start), alignof(type))
void *
move_to_arena_(Arena *arena, GArena *garena, size_t start, size_t align)
{
	size_t size = garena->pos - start;
	if (size == 0) {
		return NULL;
	}
	garena_restore(garena, start);
	// "alloc 0 bytes" to get the alignment right
	void *old = garena_alloc(garena, 0, align);
	return memcpy(arena_alloc(arena, size), old, size);
}


typedef struct Error Error;
struct Error {
	Error *next;
	char *kind;
	const u8 *pos;
	u8 *msg;
};

typedef struct {
	Arena *arena;
	const u8 *source;
	size_t source_len;
	Error *error_head;
	Error *error_tail;
	jmp_buf loc;
} ErrorContext;

static void
verror(ErrorContext *ec, const u8 *pos, char *kind, bool fatal, const char *fmt, va_list ap)
{
	Error *error = arena_alloc(ec->arena, sizeof(*error));
	error->msg = arena_vaprintf(ec->arena, fmt, ap);
	error->pos = pos;
	error->kind = kind;
	error->next = NULL;
	if (ec->error_tail) {
		ec->error_tail->next = error;
	}
	ec->error_tail = error;
	if (!ec->error_head) {
		ec->error_head = error;
	}
	if (fatal) {
		longjmp(ec->loc, 1);
	}
}

static void __attribute__((format(printf, 5, 6)))
error(ErrorContext *ec, const u8 *pos, char *kind, bool fatal, const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	verror(ec, pos, kind, fatal, fmt, ap);
	va_end(ap);
}

typedef struct {
	const u8 *pos;
	const u8 *end;
} Lexer;

typedef enum {
	LS_START,
	LS_IDENTIFIER,
	LS_NUMBER,
	LS_STRING,
	LS_STRING_ESC,
	LS_SLASH,
	LS_LINE_COMMENT,
	LS_BLOCK_COMMENT,
	LS_BLOCK_COMMENT_STAR,
	LS_MINUS,
	LS_EQUAL,
	LS_GREATER,
	LS_LESS,
	LS_EXCLAM,
} LexState;

#define TOKENS(KW, PU, OT) \
	OT(NUMBER,        "a number",      primary,  NULL,      0,  0) \
	OT(IDENTIFIER,    "an identifier", ident,    NULL,      0,  0) \
	OT(STRING,        "a string",      NULL,     NULL,      0,  0) \
                                                                       \
	PU(BAR,           "|",             NULL,     binop,     3,  4) \
	PU(AMPERSANT,     "&",             NULL,     binop,     5,  6) \
	PU(EQUAL_EQUAL,   "==",            NULL,     binop,     7,  8) \
	PU(BANG_EQUAL,    "!=",            NULL,     binop,     7,  8) \
	PU(GREATER,       ">",             NULL,     binop,     7,  8) \
	PU(LESS,          "<",             NULL,     binop,     7,  8) \
	PU(GREATER_EQUAL, ">=",            NULL,     binop,     7,  8) \
	PU(LESS_EQUAL,    "<=",            NULL,     binop,     7,  8) \
	PU(PLUS,          "+",             NULL,     binop,     9, 10) \
	PU(MINUS,         "-",             NULL,     binop,     9, 10) \
	PU(ASTERISK,      "*",             NULL,     binop,    11, 12) \
	PU(SLASH,         "/",             NULL,     binop,    11, 12) \
	PU(PERCENT,       "%",             NULL,     binop,    11, 12) \
	                                                               \
	PU(SEMICOLON,     ";",             NULL,     stop,     -1,  0) \
	PU(LPAREN,        "(",             paren,    call,     13, 14) \
	PU(RPAREN,        ")",             NULL,     stop,     -1,  0) \
	PU(EQUAL,         "=",             NULL,     NULL,      0,  0) \
	PU(LARROW,        "<-",            NULL,     assign,    2,  1) \
	PU(RARROW,        "->",            NULL,     NULL,      0,  0) \
	PU(DOT,           ".",             NULL,     field,    13, 14) \
	PU(LBRACKET,      "[",             NULL,     indexing, 13, 14) \
	PU(RBRACKET,      "]",             NULL,     stop,     -1,  0) \
	PU(COMMA,         ",",             NULL,     stop,     -1,  0) \
	                                                               \
	KW(BEGIN,         "begin",         block,    stop,     -1,  0) \
	KW(END,           "end",           NULL,     stop,     -1,  0) \
	KW(IF,            "if",            cond,     NULL,      0,  0) \
	KW(THEN,          "then",          NULL,     stop,     -1,  0) \
	KW(ELSE,          "else",          NULL,     stop,     -1,  0) \
	KW(LET,           "let",           let,      NULL,      0,  0) \
	KW(NULL,          "null",          primary,  NULL,      0,  0) \
	KW(PRINT,         "print",         print,    NULL,      0,  0) \
	KW(OBJECT,        "object",        object,   NULL,      0,  0) \
	KW(EXTENDS,       "extends",       NULL,     NULL,      0,  0) \
	KW(WHILE,         "while",         loop,     NULL,      0,  0) \
	KW(DO,            "do",            NULL,     stop,     -1,  0) \
	KW(FUNCTION,      "function",      function, NULL,      0,  0) \
	KW(ARRAY,         "array",         array,    NULL,      0,  0) \
	KW(TRUE,          "true",          primary,  NULL,      0,  0) \
	KW(FALSE,         "false",         primary,  NULL,      0,  0) \
	                                                               \
	OT(EOF,           "end of input",  NULL,     stop,     -1,  0) \
	OT(ERROR,         "lex error",     NULL,     NULL,      0,  0)


typedef enum {
	#define TOK_ENUM(tok, ...) TK_##tok,
	TOKENS(TOK_ENUM, TOK_ENUM, TOK_ENUM)
	#undef TOK_ENUM
} TokenKind;

static const char *tok_repr[] = {
	#define TOK_STR(tok, str, ...) "'"str"'",
	#define TOK_STR_OTHER(tok, str, ...) str,
	TOKENS(TOK_STR, TOK_STR, TOK_STR_OTHER)
	#undef TOK_STR
	#undef TOK_STR_OTHER
};

static struct {
	const char *str;
	TokenKind tok;
} keywords[] = {
	#define TOK_KW(tok, str, ...) { str, TK_##tok },
	#define TOK_OTHER(tok, str, ...)
	TOKENS(TOK_KW, TOK_OTHER, TOK_OTHER)
	#undef TOK_KW
#undef TOK_OTHER
};

static bool
tok_is_identifier(TokenKind kind)
{
	return kind == TK_IDENTIFIER || (kind >= TK_BAR && kind <= TK_PERCENT);
}

typedef struct {
	TokenKind kind;
	const u8 *pos;
	const u8 *end;
} Token;

Lexer
lex_init(const u8 *buf, size_t size)
{
	return (Lexer) {
		.pos = buf,
		.end = buf + size,
	};
}

#define ALPHA '_': case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm': case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'v': case 'u': case 'w': case 'x': case 'y': case 'z': case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M': case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'V': case 'U': case 'W': case 'X': case 'Y': case 'Z'

#define DIGIT '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9'

void
lex_next(Lexer *lexer, Token *token)
{
	LexState state = LS_START;
	TokenKind tok = TK_ERROR;
	int end_offset = 0;
	const u8 *start = lexer->pos;
	size_t length;
	while (lexer->pos != lexer->end) {
		u8 c = *lexer->pos;
		switch (state) {
		case LS_START: switch (c) {
			case ' ': case '\t': case '\n': start += 1; break;
			case ALPHA: state = LS_IDENTIFIER; break;
			case DIGIT: state = LS_NUMBER; break;
			case '"': state = LS_STRING; start += 1; break;
			case '/': state = LS_SLASH; break;
			case '-': state = LS_MINUS; break;
			case '=': state = LS_EQUAL; break;
			case '>': state = LS_GREATER; break;
			case '<': state = LS_LESS; break;
			case '!': state = LS_EXCLAM; break;
			case ';': tok = TK_SEMICOLON; goto done;
			case '|': tok = TK_BAR; goto done;
			case '&': tok = TK_AMPERSANT; goto done;
			case '+': tok = TK_PLUS; goto done;
			case '*': tok = TK_ASTERISK; goto done;
			case '%': tok = TK_PERCENT; goto done;
			case '(': tok = TK_LPAREN; goto done;
			case ')': tok = TK_RPAREN; goto done;
			case '.': tok = TK_DOT; goto done;
			case '[': tok = TK_LBRACKET; goto done;
			case ']': tok = TK_RBRACKET; goto done;
			case ',': tok = TK_COMMA; goto done;
			default:  tok = TK_ERROR; goto done;
		}; break;
		case LS_IDENTIFIER: switch (c) {
			case ALPHA: case DIGIT: break;
			default: tok = TK_IDENTIFIER; goto prev_done;
		}; break;
		case LS_NUMBER: switch (c) {
			case DIGIT: break;
			default: tok = TK_NUMBER; goto prev_done;
		}; break;
		case LS_STRING: switch (c) {
			case '"': tok = TK_STRING; end_offset = -1; goto done;
			case '\\': state = LS_STRING_ESC; break;
		}; break;
		case LS_STRING_ESC: switch (c) {
			case 'n': case 't': case 'r': case '~': case '"': case '\\': state = LS_STRING; break;
			default: goto err;
		}; break;
		case LS_SLASH: switch (c) {
			case '/': state = LS_LINE_COMMENT; start += 2; break;
			case '*': state = LS_BLOCK_COMMENT; start += 2; break;
			default: tok = TK_SLASH; goto prev_done;
		}; break;
		case LS_LINE_COMMENT: switch (c) {
			case '\n': state = LS_START; start = lexer->pos + 1; break;
		}; break;
		case LS_BLOCK_COMMENT: switch (c) {
			case '*': state = LS_BLOCK_COMMENT_STAR; break;
		}; break;
		case LS_BLOCK_COMMENT_STAR: switch (c) {
			case '*': break;
			case '/': state = LS_START; start = lexer->pos + 1; break;
			default: state = LS_BLOCK_COMMENT; break;
		}; break;
		case LS_MINUS: switch (c) {
			case '>': tok = TK_RARROW; goto done;
			case DIGIT: state = LS_NUMBER; break;
			default: tok = TK_MINUS; goto prev_done;
		}; break;
		case LS_EQUAL: switch (c) {
			case '=': tok = TK_EQUAL_EQUAL; goto done;
			default: tok = TK_EQUAL; goto prev_done;
		}; break;
		case LS_GREATER: switch (c) {
			case '=': tok = TK_GREATER_EQUAL; goto done;
			default: tok = TK_GREATER; goto prev_done;
		}; break;
		case LS_LESS: switch (c) {
			case '=': tok = TK_LESS_EQUAL; goto done;
			case '-': tok = TK_LARROW; goto done;
			default: tok = TK_LESS; goto prev_done;
		}; break;
		case LS_EXCLAM: switch (c) {
			case '=': tok = TK_BANG_EQUAL; goto done;
			default: goto err;
		}; break;
		}

		lexer->pos += 1;
	}

	switch (state) {
	case LS_START: case LS_LINE_COMMENT: tok = TK_EOF; goto prev_done;
	case LS_IDENTIFIER: tok = TK_IDENTIFIER; goto prev_done;
	case LS_NUMBER: tok = TK_NUMBER; goto prev_done;
	case LS_STRING: case LS_STRING_ESC: case LS_BLOCK_COMMENT: case LS_BLOCK_COMMENT_STAR: goto err;
	case LS_SLASH: case LS_MINUS: case LS_EQUAL: case LS_GREATER: case LS_LESS: tok = TK_SLASH; goto prev_done;
	case LS_EXCLAM: goto err;
	}

done:
	lexer->pos += 1;
prev_done:
err:
	length = lexer->pos - start + end_offset;
	if (tok == TK_IDENTIFIER) {
		for (size_t i = 0; i < sizeof(keywords) / sizeof(keywords[0]); i++) {
			if (strlen(keywords[i].str) == length && memcmp((const char*) start, keywords[i].str, length) == 0) {
				tok = keywords[i].tok;
				break;
			}
		}
	}
	token->kind = tok;
	token->pos = start;
	token->end = lexer->pos + end_offset;
}

typedef struct {
	const u8 *name;
	size_t len;
} Identifier;

bool
ident_eq(Identifier a, Identifier b)
{
	return a.len == b.len && memcmp(a.name, b.name, a.len) == 0;
}


// FNV-1a hash
// http://www.isthe.com/chongo/tech/comp/fnv/
u64
ident_hash(Identifier id)
{
    u64 h = UINT64_C(14695981039346656037);
    for (size_t i = 0; i < id.len; i++) {
	// beware of unwanted sign extension!
        h ^= id.name[i];
        h *= UINT64_C(1099511628211);
    }
    return h;
}

static Identifier THIS  = { .name = (const u8*) "this", .len = 4 };
static Identifier SET   = { .name = (const u8*)  "set", .len = 3 };
static Identifier GET   = { .name = (const u8*)  "get", .len = 3 };
static Identifier LESS  = { .name = (const u8*)   "<",  .len = 1 };
static Identifier PLUS  = { .name = (const u8*)   "+",  .len = 1 };
static Identifier EMPTY = { .name = (const u8*)    "",  .len = 0 };

typedef enum {
	AST_NULL,
	AST_BOOLEAN,
	AST_INTEGER,
	AST_ARRAY,
	AST_OBJECT,
	AST_FUNCTION,
	AST_DECLARATION,
	AST_VARIABLE_ACCESS,
	AST_VARIABLE_ASSIGNMENT,
	AST_INDEX_ACCESS,
	AST_INDEX_ASSIGNMENT,
	AST_FIELD_ACCESS,
	AST_FIELD_ASSIGNMENT,
	AST_FUNCTION_CALL,
	AST_METHOD_CALL,
	AST_IF,
	AST_WHILE,
	AST_PRINT,
	AST_BLOCK,
	AST_TOP,
} AstKind;

#define AST_COMMON_FIELDS \
		AstKind kind;
		//Ast *next;

typedef union Ast Ast;

typedef struct {
	AST_COMMON_FIELDS
	bool value;
} AstBoolean;

typedef struct {
	AST_COMMON_FIELDS
	i32 value;
} AstInteger;

typedef struct {
	AST_COMMON_FIELDS
	Ast *size;
	Ast *initializer;
} AstArray;

typedef struct {
	AST_COMMON_FIELDS
	Ast *extends;
	Ast **members;
	size_t member_cnt;
} AstObject;

typedef struct {
	AST_COMMON_FIELDS
	Identifier *parameters;
	size_t parameter_cnt;
	Ast *body;
} AstFunction;

typedef struct {
	AST_COMMON_FIELDS
	Identifier name;
	Ast *value;
} AstDeclaration;

typedef struct {
	AST_COMMON_FIELDS
	Identifier name;
} AstVariableAccess;

typedef struct {
	AST_COMMON_FIELDS
	Identifier name;
	Ast *value;
} AstVariableAssignment;

typedef struct {
	AST_COMMON_FIELDS
	Ast *object;
	Ast *index;
} AstIndexAccess;

typedef struct {
	AST_COMMON_FIELDS
	Ast *object;
	Ast *index;
	Ast *value;
} AstIndexAssignment;

typedef struct {
	AST_COMMON_FIELDS
	Ast *object;
	Identifier field;
} AstFieldAccess;

typedef struct {
	AST_COMMON_FIELDS
	Ast *object;
	Identifier field;
	Ast *value;
} AstFieldAssignment;

typedef struct {
	AST_COMMON_FIELDS
	Ast *function;
	Ast **arguments;
	size_t argument_cnt;
} AstFunctionCall;

typedef struct {
	AST_COMMON_FIELDS
	Ast* object;
	Identifier name;
	Ast **arguments;
	size_t argument_cnt;
} AstMethodCall;

typedef struct {
	AST_COMMON_FIELDS
	Ast *condition;
	Ast *consequent;
	Ast *alternative;
} AstConditional;

typedef struct {
	AST_COMMON_FIELDS
	Ast *condition;
	Ast *body;
} AstLoop;

typedef struct {
	AST_COMMON_FIELDS
	Identifier format;
	Ast **arguments;
	size_t argument_cnt;
} AstPrint;

typedef struct {
	AST_COMMON_FIELDS
	Ast **expressions;
	size_t expression_cnt;
} AstBlock;

typedef struct {
	AST_COMMON_FIELDS
	Ast **expressions;
	size_t expression_cnt;
} AstTop;

union Ast {
	struct {
		AST_COMMON_FIELDS
	};
	AstBoolean boolean;
	AstInteger integer;
	AstArray array;
	AstObject object;
	AstFunction function;
	AstDeclaration declaration;
	AstVariableAccess variable_access;
	AstVariableAssignment variable_assignment;
	AstIndexAccess index_access;
	AstIndexAssignment index_assignment;
	AstFieldAccess field_access;
	AstFieldAssignment field_assignment;
	AstFunctionCall function_call;
	AstMethodCall method_call;
	AstConditional conditional;
	AstLoop loop;
	AstPrint print;
	AstBlock block;
	AstTop top;
};

typedef struct {
	Lexer lexer;
	Token lookahead;
	Token prev;
	Arena *arena;
	GArena *scratch;
	ErrorContext *ec;
} Parser;

void
parser_init(Parser *parser, ErrorContext *ec, Arena *arena, GArena *scratch, const u8 *buf, size_t buf_len)
{
	ec->source = buf;
	ec->source_len = buf_len;
	parser->ec = ec;
	parser->arena = arena;
	parser->scratch = scratch;
	parser->lexer = lex_init(buf, buf_len);
	lex_next(&parser->lexer, &parser->lookahead);
}

static void
parser_error(Parser *parser, Token errtok, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(parser->ec, errtok.pos, "parse", true, msg, ap);
	va_end(ap);
}

static TokenKind
peek(const Parser *parser)
{
	return parser->lookahead.kind;
}

static Token
prev_tok(Parser *parser)
{
	return parser->lookahead;
}

static Token
discard(Parser *parser)
{
	parser->prev = parser->lookahead;
	lex_next(&parser->lexer, &parser->lookahead);
	return parser->prev;
}

static void
eat(Parser *parser, TokenKind kind)
{
	Token tok = discard(parser);
	if (tok.kind != kind) {
		parser_error(parser, tok, "expected %s, found %s", tok_repr[kind], tok_repr[tok.kind]);
	}
}

static void
eat_identifier(Parser *parser, Identifier *identifier)
{
	Token tok = discard(parser);
	if (!tok_is_identifier(tok.kind)) {
		parser_error(parser, tok, "expected %s, found %s", tok_repr[TK_IDENTIFIER], tok_repr[tok.kind]);
	}
	identifier->name = tok.pos;
	identifier->len = tok.end - tok.pos;
}

static void
eat_string(Parser *parser, Identifier *identifier)
{
	Token tok = discard(parser);
	if (tok.kind != TK_STRING) {
		printf("expected %s, found %s\n", tok_repr[TK_STRING], tok_repr[tok.kind]);
	}
	identifier->name = tok.pos;
	identifier->len = tok.end - tok.pos;
}

static bool
try_eat(Parser *parser, TokenKind kind)
{
	if (peek(parser) == kind) {
		discard(parser);
		return true;
	}
	return false;
}

static void *
ast_create(Arena *arena, AstKind kind)
{
	Ast *ast = arena_alloc(arena, sizeof(Ast));
	memset(ast, 0, sizeof(*ast));
	ast->kind = kind;
	return ast;
}

static Ast *
create_null(Parser *parser)
{
	Ast *ast = ast_create(parser->arena, AST_NULL);
	return ast;
}

static Ast *expression_bp(Parser *parser, int bp);

static Ast *
expression(Parser *parser)
{
	return expression_bp(parser, 0);
}

static void
expression_list(Parser *parser, Ast ***list, size_t *n, TokenKind separator, TokenKind terminator)
{
	size_t start = garena_save(parser->scratch);
	while (!try_eat(parser, terminator)) {
		garena_push_value(parser->scratch, Ast *, expression(parser));
		if (!try_eat(parser, separator)) {
			eat(parser, terminator);
			break;
		}
	}
	*n = garena_cnt_from(parser->scratch, Ast *, start);
	*list = move_to_arena(parser->arena, parser->scratch, start, Ast *);
}

static void
identifier_list(Parser *parser, Identifier **list, size_t *n, TokenKind separator, TokenKind terminator)
{
	size_t start = garena_save(parser->scratch);
	while (!try_eat(parser, terminator)) {
		eat_identifier(parser, garena_push(parser->scratch, Identifier));
		if (!try_eat(parser, separator)) {
			eat(parser, terminator);
			break;
		}
	}
	*n = garena_cnt_from(parser->scratch, Identifier, start);
	*list = move_to_arena(parser->arena, parser->scratch, start, Identifier);
}


static Ast *
primary(Parser *parser)
{
	Ast *ast = ast_create(parser->arena, AST_NULL);
	Token token = discard(parser);
	switch (token.kind) {
	case TK_NUMBER:
		ast->kind = AST_INTEGER;
		const u8 *pos = token.pos;
		bool negative = 0;
		while (*pos == '-') {
			negative = !negative;
			pos += 1;
		}
		i64 value = 0;
		for (; pos < token.end; pos++) {
			value = value * 10 + (*pos - '0');
		}
		ast->integer.value = negative ? -value : value;
		break;
	case TK_NULL:
		ast->kind = AST_NULL;
		break;
	case TK_TRUE:
		ast->kind = AST_BOOLEAN;
		ast->boolean.value = true;
		break;
	case TK_FALSE:
		ast->kind = AST_BOOLEAN;
		ast->boolean.value = false;
		break;
	default:
		UNREACHABLE();
	}
	return ast;
}

static Ast *
ident(Parser *parser)
{
	AstVariableAccess *variable_access = ast_create(parser->arena, AST_VARIABLE_ACCESS);
	eat_identifier(parser, &variable_access->name);
	return (Ast *) variable_access;
}

static Ast *
block(Parser *parser)
{
	AstBlock *block = ast_create(parser->arena, AST_BLOCK);
	eat(parser, TK_BEGIN);
	expression_list(parser, &block->expressions, &block->expression_cnt, TK_SEMICOLON, TK_END);
	// begin end => null
	if (block->expression_cnt == 0) {
		block->kind = AST_NULL;
	}
	return (Ast *) block;
}

static Ast *
let(Parser *parser)
{
	AstDeclaration *declaration = ast_create(parser->arena, AST_DECLARATION);
	eat(parser, TK_LET);
	eat_identifier(parser, &declaration->name);
	eat(parser, TK_EQUAL);
	declaration->value = expression(parser);
	return (Ast *) declaration;
}

static Ast *
array(Parser *parser)
{
	AstArray *array = ast_create(parser->arena, AST_ARRAY);
	eat(parser, TK_ARRAY);
	eat(parser, TK_LPAREN);
	array->size = expression(parser);
	eat(parser, TK_COMMA);
	array->initializer = expression(parser);
	eat(parser, TK_RPAREN);
	return (Ast *) array;
}

static Ast *
object(Parser *parser)
{
	AstObject *object = ast_create(parser->arena, AST_OBJECT);
	eat(parser, TK_OBJECT);
	Token object_tok = prev_tok(parser);
	if (try_eat(parser, TK_EXTENDS)) {
		object->extends = expression(parser);
	} else {
		object->extends = create_null(parser);
	}
	eat(parser, TK_BEGIN);
	expression_list(parser, &object->members, &object->member_cnt, TK_SEMICOLON, TK_END);
	for (size_t i = 0; i < object->member_cnt; i++) {
		if (object->members[i]->kind != AST_DECLARATION) {
			parser_error(parser, object_tok, "Found object member that is not a declaration");
		}
	}
	return (Ast *) object;
}

static Ast *
cond(Parser *parser)
{
	AstConditional *conditional = ast_create(parser->arena, AST_IF);
	eat(parser, TK_IF);
	conditional->condition = expression(parser);
	eat(parser, TK_THEN);
	conditional->consequent = expression(parser);
	if (try_eat(parser, TK_ELSE)) {
		conditional->alternative = expression(parser);
	} else {
		conditional->alternative = create_null(parser);
	}
	return (Ast *) conditional;
}

static Ast *
loop(Parser *parser)
{
	AstLoop *loop = ast_create(parser->arena, AST_WHILE);
	eat(parser, TK_WHILE);
	loop->condition = expression(parser);
	eat(parser, TK_DO);
	loop->body = expression(parser);
	return (Ast *) loop;
}

static Ast *
print(Parser *parser)
{
	AstPrint *print = ast_create(parser->arena, AST_PRINT);
	eat(parser, TK_PRINT);
	eat(parser, TK_LPAREN);
	eat_string(parser, &print->format);
	Token fmt_tok = prev_tok(parser);
	size_t formats = 0;
	for (size_t i = 0; i < print->format.len; i++) {
		switch (print->format.name[i]) {
		case '\\': continue;
		case '~': formats += 1;
		}
	}
	if (try_eat(parser, TK_COMMA)) {
		expression_list(parser, &print->arguments, &print->argument_cnt, TK_COMMA, TK_RPAREN);
	} else {
		eat(parser, TK_RPAREN);
	}
	if (formats != print->argument_cnt) {
		parser_error(parser, fmt_tok, "Invalid number of print arguments: %zu expected, got %zu", formats, print->argument_cnt);
	}
	return (Ast *) print;
}

static Ast *
paren(Parser *parser)
{
	Ast *ast;
	eat(parser, TK_LPAREN);
	ast = expression(parser);
	eat(parser, TK_RPAREN);
	return ast;
}


static Ast *
function(Parser *parser)
{
	AstFunction *function = ast_create(parser->arena, AST_FUNCTION);
	Ast *ast = (Ast *) function;
	eat(parser, TK_FUNCTION);
	if (tok_is_identifier(peek(parser))) {
		AstDeclaration *declaration = ast_create(parser->arena, AST_DECLARATION);
		eat_identifier(parser, &declaration->name);
		declaration->value = (Ast *) function;
		ast = (Ast *) declaration;
	}
	eat(parser, TK_LPAREN);
	identifier_list(parser, &function->parameters, &function->parameter_cnt, TK_COMMA, TK_RPAREN);
	eat(parser, TK_RARROW);
	function->body = expression(parser);
	return ast;
}

static Ast *
stop(Parser *parser, Ast *left, int rbp)
{
	(void) parser;
	(void) left;
	(void) rbp;
	UNREACHABLE();
}

static Ast *
binop(Parser *parser, Ast *left, int rbp)
{
	AstMethodCall *method_call = ast_create(parser->arena, AST_METHOD_CALL);
	Token token = discard(parser);
	method_call->object = left;
	method_call->name.name = token.pos;
	method_call->name.len = token.end - token.pos;
	method_call->arguments = arena_alloc(parser->arena, sizeof(*method_call->arguments));
	method_call->arguments[0] = expression_bp(parser, rbp);
	//method_call->arguments = expression_bp(parser, rbp);
	method_call->argument_cnt = 1;
	return (Ast *) method_call;
}

static Ast *
call(Parser *parser, Ast *left, int rbp)
{
	(void) rbp;
	// NOTE: In this function we change Ast's from one kind to other, so we
	// copy the old structs to avoid problems with aliasing union fields
	eat(parser, TK_LPAREN);
	switch (left->kind) {
	case AST_FIELD_ACCESS: {
		left->kind = AST_METHOD_CALL;
		AstFieldAccess field_access = left->field_access;
		AstMethodCall *method_call = &left->method_call;
		method_call->object = field_access.object;
		method_call->name = field_access.field;
		expression_list(parser, &method_call->arguments, &method_call->argument_cnt, TK_COMMA, TK_RPAREN);
		return left;
	}
	default: {
		AstFunctionCall *function_call = ast_create(parser->arena, AST_FUNCTION_CALL);
		function_call->function = left;
		expression_list(parser, &function_call->arguments, &function_call->argument_cnt, TK_COMMA, TK_RPAREN);
		return (Ast *) function_call;
	}
	}
}

static Ast *
indexing(Parser *parser, Ast *left, int rbp)
{
	// rbp not used - delimited by TK_RBRACKET, not by precedence
	(void) rbp;
	AstIndexAccess *index_access = ast_create(parser->arena, AST_INDEX_ACCESS);
	eat(parser, TK_LBRACKET);
	index_access->object = left;
	index_access->index = expression(parser);
	eat(parser, TK_RBRACKET);
	return (Ast *) index_access;
}

static Ast *
field(Parser *parser, Ast *left, int rbp)
{
	(void) rbp;
	AstFieldAccess *field_access = ast_create(parser->arena, AST_FIELD_ACCESS);
	eat(parser, TK_DOT);
	field_access->object = left;
	eat_identifier(parser, &field_access->field);
	return (Ast *) field_access;
}

static Ast *
assign(Parser *parser, Ast *left, int rbp)
{
	// NOTE: In this function we change Ast's from one kind to other, so we
	// copy the old structs to avoid problems with aliasing union fields
	eat(parser, TK_LARROW);
	switch (left->kind) {
	case AST_VARIABLE_ACCESS: {
		left->kind = AST_VARIABLE_ASSIGNMENT;
		AstVariableAccess variable_access = left->variable_access;
		AstVariableAssignment *variable_assignment = &left->variable_assignment;
		variable_assignment->name = variable_access.name;
		variable_assignment->value = expression_bp(parser, rbp);
		return left;
	}
	case AST_FIELD_ACCESS: {
		left->kind = AST_FIELD_ASSIGNMENT;
		AstFieldAccess field_access = left->field_access;
		AstFieldAssignment *field_assignment = &left->field_assignment;
		field_assignment->object = field_access.object;
		field_assignment->field = field_access.field;
		field_assignment->value = expression_bp(parser, rbp);
		return left;
	}
	case AST_INDEX_ACCESS: {
		left->kind = AST_INDEX_ASSIGNMENT;
		AstIndexAccess index_access = left->index_access;
		AstIndexAssignment *index_assignment = &left->index_assignment;
		index_assignment->object = index_access.object;
		index_assignment->index = index_access.index;
		index_assignment->value = expression_bp(parser, rbp);
		return left;
	}
	default:
		parser_error(parser, parser->prev, "Invalid assignment left hand side, expected variable, index or field access");
		return left;
	}
}

typedef struct {
	Ast *(*nud)(Parser *);
} NullInfo;

NullInfo null_info[] = {
	#define TOK_NULL(tok, str, nud, led, lbp, rbp) { nud },
	TOKENS(TOK_NULL, TOK_NULL, TOK_NULL)
	#undef TOK_STR
};

typedef struct {
	Ast *(*led)(Parser *, Ast *left, int rbp);
	int lbp;
	int rbp;
} LeftInfo;

LeftInfo left_info[] = {
	#define TOK_LEFT(tok, str, nud, led, lbp, rbp) { led, lbp, rbp },
	TOKENS(TOK_LEFT, TOK_LEFT, TOK_LEFT)
	#undef TOK_STR
};

static Ast *
expression_bp(Parser *parser, int bp)
{
	TokenKind token = peek(parser);
	NullInfo ni = null_info[token];
	Ast *left;

	if (!ni.nud) {
		parser_error(parser, parser->lookahead, "Invalid start of expression %s", tok_repr[token]);
	}
	left = ni.nud(parser);

	for (;;) {
		token = peek(parser);
		LeftInfo li = left_info[token];
		if (!li.led) {
			if (token == TK_EQUAL) {
				parser_error(parser, parser->lookahead, "Unexpected %s, did you mean to use %s for assignment?", tok_repr[TK_EQUAL], tok_repr[TK_LARROW]);
			} else {
				parser_error(parser, parser->lookahead, "Invalid expression continuing/ending token %s", tok_repr[token]);
			}
		}
		if (li.lbp < bp) {
			break;
		}
		left = li.led(parser, left, li.rbp);
	}

	return left;
}

Ast *
parse(ErrorContext *ec, Arena *arena, u8 *buf, size_t buf_len)
{
	Parser parser;
	GArena scratch;
	garena_init(&scratch);
	parser_init(&parser, ec, arena, &scratch, buf, buf_len);
	// TODO: setjmp for GArena destruction
	AstTop *top = ast_create(parser.arena, AST_TOP);
	expression_list(&parser, &top->expressions, &top->expression_cnt, TK_SEMICOLON, TK_EOF);
	// empty program => null
	if (top->expression_cnt == 0) {
		top->kind = AST_NULL;
	}
	garena_destroy(&scratch);
	return (Ast *) top;
}

typedef enum {
	VK_NULL,
	VK_BOOLEAN,
	VK_INTEGER,
	VK_GCVALUE,

	VK_FUNCTION,
} ValueKind;

typedef enum {
	GK_ARRAY,
	GK_OBJECT,
} GcValueKind;

typedef struct GcValue GcValue;

typedef struct {
	ValueKind kind;
	union {
		bool boolean;
		i32 integer;
		GcValue *gcvalue;

		// For AST interpreter.
		AstFunction *function;
		// For BC interpreter.
		u16 function_index;

		// For BC compiler.
		u16 local_index;
	};
} Value;

struct GcValue {
	GcValueKind kind;
};

typedef struct {
	GcValue gcvalue;
	size_t length;
	Value values[];
} Array;

typedef struct {
	Identifier name;
	Value value;
} Field;


typedef struct {
	GcValue gcvalue;
	Value parent;
	size_t field_cnt;
	Field fields[];
} Object;

typedef struct {
	GcValue gcvalue;
	Ast *ast;
} Function;

static void
exec_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "execution", true, msg, ap);
	va_end(ap);
}

Value
make_null(void)
{
	return (Value) { .kind = VK_NULL };
}

Value
make_boolean(bool value)
{
	return (Value) { .kind = VK_BOOLEAN, .boolean = value };
}

Value
make_integer(i32 value)
{
	return (Value) { .kind = VK_INTEGER, .integer = value };
}

Value
make_array(size_t length)
{
	Array *array = malloc(sizeof(*array) + length * sizeof(array->values[0]));
	array->gcvalue = (GcValue) { .kind = GK_ARRAY };
	array->length = length;

	return (Value) { .kind = VK_GCVALUE, .gcvalue = &array->gcvalue };
}

Value
make_object(size_t field_cnt)
{
	Object *object = malloc(sizeof(*object) + field_cnt * sizeof(object->fields[0]));
	object->gcvalue = (GcValue) { .kind = GK_OBJECT };
	// NOTE: Caller has to set parent!
	//object->parent = make_null();
	object->field_cnt = field_cnt;

	return (Value) { .kind = VK_GCVALUE, .gcvalue = &object->gcvalue };
}

Value
make_function_ast(AstFunction *function)
{
	return (Value) { .kind = VK_FUNCTION, .function = function };
}

Value
make_function_bc(u16 function_index)
{
	return (Value) { .kind = VK_FUNCTION, .function_index = function_index };
}

bool
value_is_null(Value value)
{
	return value.kind == VK_NULL;
}

bool
value_is_bool(Value value)
{
	return value.kind == VK_BOOLEAN;
}

bool
value_as_bool(Value value)
{
	assert(value.kind == VK_BOOLEAN);
	return value.boolean;
}

bool
value_is_integer(Value value)
{
	return value.kind == VK_INTEGER;
}

i32
value_as_integer(Value value)
{
	assert(value.kind == VK_INTEGER);
	return value.integer;
}

bool
value_is_array(Value value)
{
	return value.kind == VK_GCVALUE && value.gcvalue->kind == GK_ARRAY;
}

Array *
value_as_array(Value value)
{
	assert(value.kind == VK_GCVALUE);
	assert(value.gcvalue->kind == GK_ARRAY);
	return (Array *) value.gcvalue;
}

bool
value_is_object(Value value)
{
	return value.kind == VK_GCVALUE && value.gcvalue->kind == GK_OBJECT;
}

Object *
value_as_object(Value value)
{
	assert(value.kind == VK_GCVALUE);
	assert(value.gcvalue->kind == GK_OBJECT);
	return (Object *) value.gcvalue;
}

bool
value_is_function(Value value)
{
	return value.kind == VK_FUNCTION;
}

AstFunction *
value_as_function_ast(Value value)
{
	assert(value.kind == VK_FUNCTION);
	return value.function;
}

u16
value_as_function_bc(Value value)
{
	assert(value.kind == VK_FUNCTION);
	return (u16) value.function_index;
}

static int
ident_cmp(Identifier a, Identifier b)
{
	int cmp = memcmp(a.name, b.name, a.len < b.len ? a.len : b.len);
	return cmp == 0 ? (a.len > b.len) - (b.len > a.len) : cmp;
}

void
value_print(Value value)
{
	switch (value.kind) {
	case VK_NULL:
		printf("%s", "null");
		break;
	case VK_BOOLEAN:
		printf("%s", value.boolean ? "true" : "false");
		break;
	case VK_INTEGER:
		printf("%"PRIi32, value.integer);
		break;
	case VK_GCVALUE:
		switch (value.gcvalue->kind) {
		case GK_ARRAY: {
			printf("[");
			Array *array = value_as_array(value);
			for (size_t i = 0; i < array->length; i++) {
				if (i != 0) {
					printf(", ");
				}
				value_print(array->values[i]);
			}
			printf("]");
			break;
		}
		case GK_OBJECT:
			printf("object(");
			Object *object = value_as_object(value);
			Value parent = object->parent;
			bool prev = false;
			if (!value_is_null(parent)) {
				printf("..=");
				value_print(parent);
				prev = true;
			}
			Field *fields = calloc(object->field_cnt, sizeof(*fields));
			size_t field_cnt = 0;
			for (size_t i = 0; i < object->field_cnt; i++) {
				if (value_is_function(object->fields[i].value)) {
					continue;
				}
				fields[field_cnt] = object->fields[i];
				field_cnt += 1;
			}

			for (size_t i = 0; i < field_cnt; i++) {
				for (size_t j = i; j > 0 && ident_cmp(fields[j - 1].name, fields[j].name) > 0; j--) {
					Field tmp = fields[j - 1];
					fields[j - 1] = fields[j];
					fields[j] = tmp;
				}
			}

			for (size_t i = 0; i < field_cnt; i++) {
				if (prev) {
					printf(", ");
				}
				Identifier name = fields[i].name;
				printf("%.*s=", (int)name.len, name.name);
				value_print(fields[i].value);
				prev = true;
			}
			printf(")");
			free(fields);
			break;
		}
		break;

	case VK_FUNCTION:
		printf("function '%p'", (void *) value.function);
		break;
	}
}

static void
builtin_print(ErrorContext *ec, Identifier format, Value *arguments, size_t argument_cnt)
{
	bool in_escape = false;
	size_t arg_index = 0;
	for (size_t i = 0; i < format.len; i++) {
		u8 c = format.name[i];
		if (in_escape) {
			in_escape = false;
			switch (c) {
			case  'n': c = '\n'; break;
			case  't': c = '\t'; break;
			case  'r': c = '\r'; break;
			case  '~': c =  '~'; break;
			case  '"': c =  '"'; break;
			case '\\': c = '\\'; break;
			default:
				exec_error(ec, "Invalid escape sequence: '\\%c'", c);
			}
			putchar(c);
		} else {
			switch (c) {
			case '\\': in_escape = true; break;
			case '~':
				if (arg_index >= argument_cnt) {
					exec_error(ec, "More format string placeholders (%zu+) than arguments (%zu)", arg_index + 1, argument_cnt);
				}
				value_print(arguments[arg_index]);
				arg_index += 1;
				break;
			default:
				putchar(c);
			}
		}
	}
	fflush(stdout);
}

bool
value_to_bool(Value value)
{
	if (value.kind == VK_NULL || (value.kind == VK_BOOLEAN && value.boolean == false)) {
		return false;
	}
	return true;
}

size_t
value_as_size(ErrorContext *ec, Value value)
{
	if (!value_is_integer(value)) {
		exec_error(ec, "Value is not an integer");
	}
	i32 int_index = value_as_integer(value);
	if (int_index < 0) {
		exec_error(ec, "Value is negataive");
	}
	return (size_t) int_index;
}

Value *
array_index(ErrorContext *ec, Value array_value, Value index_value)
{
	Array *array = value_as_array(array_value);
	size_t index = value_as_size(ec, index_value);
	if (index >= array->length) {
		exec_error(ec, "Array indexed out of bounds");
	}
	return &array->values[index];
}

Value *
value_field_try(Value value, Value *receiver, Identifier name)
{
	if (!value_is_object(value)) {
		// We did not find the field, but we have the eldest parent
		// object on which we can call a primitive method (hopefully)
		*receiver = value;
		return NULL;
	}
	Object *object = value_as_object(value);
	for (size_t i = 0; i < object->field_cnt; i++) {
		if (ident_eq(object->fields[i].name, name)) {
			// We found the field, set the receiver Object to the
			// field's owner
			receiver->gcvalue = &object->gcvalue;
			return &object->fields[i].value;
		}
	}
	return value_field_try(object->parent, receiver, name);
}

Value *
value_field(ErrorContext *ec, Value value, Value *receiver, Identifier name)
{
	Value *field = value_field_try(value, receiver, name);
	if (!field) {
		exec_error(ec, "failed to find field %.*s in object", (int)name.len, name.name);
	}
	return field;
}

Value
value_call_primitive_method(ErrorContext *ec, Value target, Identifier method, Value *arguments, size_t argument_cnt)
{
	const u8 *method_name = method.name;
	size_t method_name_len = method.len;
	#define METHOD(name) \
			if (sizeof(name) - 1 == method_name_len && memcmp(name, method_name, method_name_len) == 0) /* body*/

	METHOD("==") {
		if (argument_cnt != 1) goto err;
		if (target.kind != arguments[0].kind) return make_boolean(false);
		switch (target.kind) {
		case VK_NULL: return make_boolean(true);
		case VK_BOOLEAN: return make_boolean(value_as_bool(target) == value_as_bool(arguments[0]));
		case VK_INTEGER: return make_boolean(value_as_integer(target) == value_as_integer(arguments[0]));
		default: goto err;
		}
	}
	METHOD("!=") {
		if (argument_cnt != 1) goto err;
		if (target.kind != arguments[0].kind) return make_boolean(true);
		switch (target.kind) {
		case VK_NULL: return make_boolean(false);
		case VK_BOOLEAN: return make_boolean(value_as_bool(target) != value_as_bool(arguments[0]));
		case VK_INTEGER: return make_boolean(value_as_integer(target) != value_as_integer(arguments[0]));
		default: goto err;
		}
	}

	switch (target.kind) {
	case VK_NULL:
	case VK_BOOLEAN:
		if (argument_cnt != 1) goto err;
		if (arguments[0].kind != VK_BOOLEAN) goto err;
		#define LOG_OP(op) return make_boolean(value_as_bool(target) op value_as_bool(arguments[0]))
		METHOD("&") LOG_OP(&&);
		METHOD("|") LOG_OP(||);
		#undef LOG_OP
		break;
	case VK_INTEGER:
		if (argument_cnt != 1) goto err;
		if (arguments[0].kind != VK_INTEGER) goto err;
		#define OP(op) METHOD(#op) return make_integer(value_as_integer(target) op value_as_integer(arguments[0]))
		#define REL_OP(op) METHOD(#op) return make_boolean(value_as_integer(target) op value_as_integer(arguments[0]))
		OP(+); OP(-); OP(*); OP(/); OP(%);
		REL_OP(<=); REL_OP(<); REL_OP(>=); REL_OP(>);
		#undef OP
		#undef REL_OP
		break;
	case VK_GCVALUE:
		switch (target.gcvalue->kind) {
		case GK_ARRAY:
			METHOD("get") {
				if (argument_cnt != 1) goto err;
				Value *lvalue = array_index(ec, target, arguments[0]);
				return *lvalue;
			}
			METHOD("set") {
				if (argument_cnt != 2) goto err;
				Value *lvalue = array_index(ec, target, arguments[0]);
				return *lvalue = arguments[1];
			}
		case GK_OBJECT:
			break;
		}
	case VK_FUNCTION:
		break;
	}
err:
	exec_error(ec, "Invalid method '%.*s' called on value (invalid types or number of arguments)", method_name_len, method_name);
	return make_null();
}

// A simple hash table.
// Inspired by: http://www.craftinginterpreters.com/hash-tables.html

typedef struct {
	Identifier key;
	Value value;
} Entry;

typedef struct {
	Entry *entries;
	size_t entry_cnt;
	size_t capacity;
} Table;

void
table_init(Table *table, size_t capacity)
{
	table->entry_cnt = 0;
	if (capacity == 0) {
		table->capacity = 0;
		table->entries = NULL;
	} else {
		table->capacity = 1;
		while (table->capacity < capacity) {
			table->capacity *= 2;
		}
		table->entries = calloc(table->capacity, sizeof(*table->entries));
	}
}

void
table_destroy(Table *table)
{
	free(table->entries);
}

Entry *
table_find_entry(Entry *entries, size_t capacity, Identifier key)
{
	u64 hash = ident_hash(key);
	// NOTE: We guarantee that the capacity is a power of two. The modulo
	// operation thus simplifies to simple binary AND.
	size_t mask = capacity - 1;
	for (size_t index = hash & mask;; index = (index + 1) & mask) {
		Entry *entry = &entries[index];
		if (entry->key.name == NULL || ident_eq(entry->key, key)) {
			return entry;
		}
	}
}

void
table_grow(Table *table)
{
	size_t capacity = table->capacity ? table->capacity * 2 : 8;
	// TODO: intialize memory if not zero allocated
	Entry *entries = calloc(capacity, sizeof(*entries));
	for (size_t i = 0; i < table->capacity; i++) {
		Entry *old = &table->entries[i];
		if (old->key.name == NULL) {
			continue;
		}
		Entry *new = table_find_entry(entries, capacity, old->key);
		*new = *old;
	}
	free(table->entries);
	table->entries = entries;
	table->capacity = capacity;
}

Value *
table_get(Table *table, Identifier key)
{
	if (table->entry_cnt == 0) {
		return NULL;
	}
	Entry *entry = table_find_entry(table->entries, table->capacity, key);
	if (entry->key.name == NULL) {
		return NULL;
	}
	return &entry->value;
}

bool
table_insert(Table *table, Identifier key, Value value)
{
	if (table->entry_cnt + 1 >= table->capacity / 2) {
		table_grow(table);
	}
	Entry *entry = table_find_entry(table->entries, table->capacity, key);
	bool new = entry->key.name == NULL;
	if (new) {
		table->entry_cnt += 1;
		entry->key = key;
	}
	entry->value = value;
	return new;
}

typedef struct Environment Environment;
struct Environment {
	Environment *prev;
	Table env;
};

typedef struct {
	ErrorContext *ec;
	Environment *env;
	Environment *global_env;
} InterpreterState;

Environment *
env_create(Environment *prev)
{
	Environment *env = calloc(sizeof(*env), 1);
	env->prev = prev;
	table_init(&env->env, 0);
	return env;
}

void
env_destroy(Environment *env)
{
	table_destroy(&env->env);
	free(env);
}

void
env_define(Environment *env, Identifier name, Value value)
{
	table_insert(&env->env, name, value);
}

Value *
env_lookup_raw(Environment *env, Identifier name)
{
	if (!env) {
		return NULL;
	}
	Value *lvalue = table_get(&env->env, name);
	if (lvalue) {
		return lvalue;
	}
	return env_lookup_raw(env->prev, name);
}

Value *
env_lookup(InterpreterState *is, Identifier name)
{
	Value *lvalue = env_lookup_raw(is->env, name);
	if (!lvalue) {
		// Name not found, should be a global whose
		// definition we will yet see.
		Value null = make_null();
		// TODO: could be improved by having env_define return an lvalue
		env_define(is->global_env, name, null);
		return env_lookup_raw(is->global_env, name);
	}
	return lvalue;
}

static Value interpreter_call_method(InterpreterState *is, Value object, bool function_call, Identifier method, Ast **ast_arguments, size_t argument_cnt);

static Value
interpret(InterpreterState *is, Ast *ast)
{
	switch (ast->kind) {
	case AST_NULL: {
		return make_null();
	}
	case AST_BOOLEAN: {
		return make_boolean(ast->boolean.value);
	}
	case AST_INTEGER: {
		return make_integer(ast->integer.value);
	}
	case AST_ARRAY: {
		Value size_value = interpret(is, ast->array.size);
		size_t size = value_as_size(is->ec, size_value);
		Value array_value = make_array(size);
		Array *array = value_as_array(array_value);
		Environment *saved_env = is->env;
		for (size_t i = 0; i < size; i++) {
			array->values[i] = interpret(is, ast->array.initializer);
			is->env = saved_env;
		}
		return array_value;
	}
	case AST_OBJECT: {
		Value parent = interpret(is, ast->object.extends);
		Value object_value = make_object(ast->object.member_cnt);
		Object *object = value_as_object(object_value);
		object->parent = parent;
		for (size_t i = 0; i < ast->object.member_cnt; i++) {
			Ast *ast_member = ast->object.members[i];
			switch (ast_member->kind) {
			case AST_DECLARATION:
				object->fields[i].name = ast_member->declaration.name;
				object->fields[i].value = interpret(is, ast_member->declaration.value);
				break;
			default:
				UNREACHABLE();
			}
		}
		return object_value;
	}
	case AST_FUNCTION: {
		return make_function_ast(&ast->function);
	}

	case AST_DECLARATION: {
		Value value = interpret(is, ast->declaration.value);
		env_define(is->env, ast->declaration.name, value);
		return value;
	}

	case AST_VARIABLE_ACCESS: {
		Value *lvalue = env_lookup(is, ast->variable_access.name);
		return *lvalue;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		Value value = interpret(is, ast->variable_assignment.value);
		Value *lvalue = env_lookup(is, ast->variable_assignment.name);
		return *lvalue = value;
	}

	case AST_INDEX_ACCESS: {
		Value object = interpret(is, ast->index_access.object);
		return interpreter_call_method(is, object, false, GET, &ast->index_access.index, 1);
	}
	case AST_INDEX_ASSIGNMENT: {
		Value object = interpret(is, ast->index_assignment.object);
		Ast *arguments[2] = {ast->index_assignment.index, ast->index_assignment.value};
		return interpreter_call_method(is, object, false, SET, &arguments[0], 2);
	}

	case AST_FIELD_ACCESS: {
		Value object = interpret(is, ast->field_access.object);
		Value *lvalue = value_field(is->ec, object, &object, ast->field_access.field);
		return *lvalue;
	}
	case AST_FIELD_ASSIGNMENT: {
		Value object = interpret(is, ast->field_assignment.object);
		Value value = interpret(is, ast->field_assignment.value);
		Value *lvalue = value_field(is->ec, object, &object, ast->field_access.field);
		return *lvalue = value;
	}

	case AST_FUNCTION_CALL: {
		Value function = interpret(is, ast->function_call.function);
		return interpreter_call_method(is, function, true, EMPTY, ast->function_call.arguments, ast->function_call.argument_cnt);
	}
	case AST_METHOD_CALL: {
		Value object = interpret(is, ast->method_call.object);
		return interpreter_call_method(is, object, false, ast->method_call.name, ast->method_call.arguments, ast->method_call.argument_cnt);
	}

	case AST_IF: {
		Value condition = interpret(is, ast->conditional.condition);
		if (value_to_bool(condition)) {
			return interpret(is, ast->conditional.consequent);
		} else {
			return interpret(is, ast->conditional.alternative);
		}
	}
	case AST_WHILE: {
		while (value_to_bool(interpret(is, ast->loop.condition))) {
			interpret(is, ast->loop.body);
		}
		return make_null();
	}
	case AST_PRINT: {
		Value *arguments = calloc(ast->print.argument_cnt, sizeof(*arguments));
		for (size_t i = 0; i < ast->print.argument_cnt; i++) {
			arguments[i] = interpret(is, ast->print.arguments[i]);
		}
		builtin_print(is->ec, ast->print.format, arguments, ast->print.argument_cnt);
		free(arguments);
		return make_null();
	}
	case AST_BLOCK: {
		AstBlock *block = &ast->block;
		Environment *saved_env = is->env;
		is->env = env_create(is->env);
		Value value = interpret(is, block->expressions[0]);
		for (size_t i = 1; i < block->expression_cnt; i++) {
			value = interpret(is, block->expressions[i]);
		}
		env_destroy(is->env);
		is->env = saved_env;
		return value;
	}
	case AST_TOP: {
		AstTop *top = &ast->top;
		Value value = interpret(is, top->expressions[0]);
		for (size_t i = 1; i < top->expression_cnt; i++) {
			value = interpret(is, top->expressions[i]);
		}
		return value;
	}
	}
	UNREACHABLE();
}

static Value
interpreter_call_method(InterpreterState *is, Value object, bool function_call, Identifier method, Ast **ast_arguments, size_t argument_cnt)
{
	Value return_value;
	Value *arguments = calloc(argument_cnt, sizeof(*arguments));

	for (size_t i = 0; i < argument_cnt; i++) {
		arguments[i] = interpret(is, ast_arguments[i]);
	}

	AstFunction *function = NULL;
	if (function_call) {
		if (!value_is_function(object)) {
			exec_error(is->ec, "Function call target is not a function");
		}
		function = value_as_function_ast(object);
	} else {
		Value *function_value = value_field_try(object, &object, method);
		function = function_value ? value_as_function_ast(*function_value) : NULL;
	}
	if (function) {
		if (argument_cnt != function->parameter_cnt) {
			exec_error(is->ec, "Wrong number of arguments: %zu expected, got %zu", function->parameter_cnt, argument_cnt);
		}

		// Starting with _only_ the global environment, add the function
		// arguments to the scope
		Environment *saved_env = is->env;
		is->env = env_create(is->global_env);
		for (size_t i = 0; i < argument_cnt; i++) {
			env_define(is->env, function->parameters[i], arguments[i]);
		}
		if (!function_call) {
			env_define(is->env, THIS, object);
		}
		return_value = interpret(is, function->body);
		env_destroy(is->env);
		is->env = saved_env;
	} else {
		return_value = value_call_primitive_method(is->ec, object, method, &arguments[0], argument_cnt);
	}
	free(arguments);
	return return_value;
}

void
interpret_ast(ErrorContext *ec, Ast *ast)
{
	Environment *env = env_create(NULL);
	InterpreterState is = {
		.ec = ec,
		.env = env,
		.global_env = env,
	};
	interpret(&is, ast);
	env_destroy(env);
}

// Parse little endian numbers from byte array.Beware of implicit promotion from uint8_t to signed int.
// https://commandcenter.blogspot.com/2012/04/byte-order-fallacy.html
// https://www.reddit.com/r/C_Programming/comments/bjuk3v/the_byte_order_fallacy/embbwq2/

static u32
read_u32(u8 **src)
{
	u8 *pos = *src;
	u32 res = (((u32) pos[3]) << 24) | (pos[2] << 16) | (pos[1] << 8) | (pos[0] << 0);
	*src += 4;
	return res;
}

static uint16_t
read_u16(u8 **src)
{
	u8 *pos = *src;
	u16 res = ((uint16_t) (pos[1] << 8) | (pos[0] << 0));
	*src += 2;
	return res;
}

static uint8_t
read_u8(u8 **src)
{
	return *(*src)++;
}


typedef enum {
	CK_NULL = 0x01,
	CK_BOOLEAN = 0x06,
	CK_INTEGER = 0x00,
	CK_STRING = 0x02,
	CK_METHOD = 0x03,
	CK_CLASS = 0x05,
} ConstantKind;

typedef enum {
	OP_LITERAL = 0x01,
	OP_ARRAY = 0x03,
	OP_OBJECT = 0x04,
	OP_FUNCTION = 0x11,
	OP_GET_LOCAL = 0x0A,
	OP_SET_LOCAL = 0x09,
	OP_GET_GLOBAL = 0x0C,
	OP_SET_GLOBAL = 0x0B,
	OP_GET_FIELD = 0x05,
	OP_SET_FIELD = 0x06,
	OP_JUMP = 0x0E,
	OP_BRANCH = 0x0D,
	OP_CALL_FUNCTION = 0x08,
	OP_CALL_METHOD = 0x07,
	OP_PRINT = 0x02,
	OP_DROP = 0x10,
	OP_RETURN = 0x0F,
} OpCode;

typedef struct {
	u16 local_cnt;
	u8 parameter_cnt;
	u8 *instruction_start;
	size_t instruction_len;
} CMethod;

typedef struct {
	// Can't be u16 * due to alignment problems
	u8 *members;
	u16 member_cnt;
} Class;

typedef struct {
	ConstantKind kind;
	union {
		bool boolean;
		i32 integer;
		Identifier string;
		u16 slot;
		CMethod method;
		Class class;
	};
} Constant;

typedef struct {
	Constant *constants;
	size_t constant_cnt;
	Class global_class;
	u16 entry_point;
} Program;

static void
read_class(u8 **input, Class *class)
{
	class->member_cnt = read_u16(input);
	class->members = *input;
	for (size_t i = 0; i < class->member_cnt; i++) {
		read_u16(input);
	}
}

static void
read_constant(ErrorContext *ec, u8 **input, Constant *constant)
{
	ConstantKind kind = read_u8(input);
	constant->kind = kind;
	switch (kind) {
	case CK_NULL:
		break;
	case CK_BOOLEAN: {
		u8 b = read_u8(input);
		if (b > 1) {
			error(ec, NULL, "bytecode", true, "Boolean is %d not 0 or 1", (int) b);
		}
		constant->boolean = b == 1;
		break;
	}
	case CK_INTEGER:
		constant->integer = (i32) read_u32(input);
		break;
	case CK_STRING:
		constant->string.len = read_u32(input);
		constant->string.name = *input;
		*input += constant->string.len;
		break;
	case CK_METHOD:
		constant->method.parameter_cnt = read_u8(input);
		constant->method.local_cnt = read_u16(input);
		constant->method.instruction_len = read_u32(input);
		constant->method.instruction_start = *input;
		*input += constant->method.instruction_len;
		break;
	case CK_CLASS: {
		read_class(input, &constant->class);
		break;
	}
	default:
		error(ec, NULL, "bytecode", true, "Invalid constant tag '%d'", (int) kind);
	}
}

static bool
read_program(ErrorContext *ec, Program *program, u8 *input, size_t input_len)
{
	assert(input_len >= 2);
	program->constant_cnt = read_u16(&input);
	program->constants = calloc(program->constant_cnt, sizeof(*program->constants));
	for (size_t i = 0; i < program->constant_cnt; i++) {
		read_constant(ec, &input, &program->constants[i]);
	}
	read_class(&input, &program->global_class);
	program->entry_point = read_u16(&input);
	return true;
}

typedef struct {
	ErrorContext *ec;
	Program *program;
	Value global;
	Value *stack;
	size_t stack_pos;
	size_t stack_len;
	Value *frame_stack;
	size_t frame_stack_pos;
	size_t frame_stack_len;
	size_t bp;
} VM;


static Value
make_null_vm(VM *vm)
{
	(void) vm;
	return make_null();
}

static Value
vm_pop_value(VM *vm)
{
	return vm->stack[vm->stack_pos--];
}

static Identifier
constant_string(VM *vm, u8 **ip)
{
	u16 constant_index = read_u16(ip);
	Constant *constant = &vm->program->constants[constant_index];
	assert(constant->kind == CK_STRING);
	return constant->string;
}

static Value
vm_instantiate_class(VM *vm, Class *class, Value (*make_value)(VM *vm))
{
	Value object_value = make_object(class->member_cnt);
	Object *object = value_as_object(object_value);
	Constant *constants = vm->program->constants;

	u16 *members = (u16 *) class->members;
	for (size_t i = class->member_cnt; i--;) {
		u8 *member_name_pos = (u8 *) &members[i];
		u16 member_name = read_u16(&member_name_pos);
		Constant *name = &constants[member_name];
		assert(name->kind == CK_STRING);
		object->fields[i].name = name->string;
		object->fields[i].value = make_value(vm);
	}
	object->parent = make_value(vm);
	return object_value;
}

static void
vm_call_method(VM *vm, u16 method_index, u8 argument_cnt)
{
	Constant *method_constant = &vm->program->constants[method_index];
	assert(method_constant->kind == CK_METHOD);
	CMethod *method = &method_constant->method;
	assert(argument_cnt == method->parameter_cnt);

	size_t local_cnt = argument_cnt + method->local_cnt;
	size_t saved_bp = vm->bp;
	vm->bp = vm->frame_stack_pos;
	vm->frame_stack_pos += local_cnt;

	Value *arguments = &vm->stack[vm->stack_pos - (argument_cnt - 1)];
	vm->stack_pos -= argument_cnt;
	Value *locals = &vm->frame_stack[vm->bp];
	for (size_t i = 0; i < argument_cnt; i++) {
		locals[i] = arguments[i];
	}
	for (size_t i = argument_cnt; i < local_cnt; i++) {
		locals[i] = make_null();
	}

	for (u8 *ip = method->instruction_start;;) {
		switch (read_u8(&ip)) {
		case OP_LITERAL: {
			u16 constant_index = read_u16(&ip);
			Constant *constant = &vm->program->constants[constant_index];
			Value value;
			switch (constant->kind) {
			case CK_NULL:
				value = make_null();
				break;
			case CK_BOOLEAN:
				value = make_boolean(constant->boolean);
				break;
			case CK_INTEGER:
				value = make_integer(constant->integer);
				break;
			default:
				assert(false);
			}
			vm->stack[++vm->stack_pos] = value;
			break;
		}
		case OP_ARRAY: {
			Value initializer = vm->stack[vm->stack_pos--];
			Value size_value = vm->stack[vm->stack_pos--];
			size_t size = value_as_size(vm->ec, size_value);
			Value array_value = make_array(size);
			Array *array = value_as_array(array_value);
			for (size_t i = 0; i < size; i++) {
				array->values[i] = initializer;
			}
			vm->stack[++vm->stack_pos] = array_value;
			break;
		}
		case OP_OBJECT: {
			u16 constant_index = read_u16(&ip);
			Constant *constant = &vm->program->constants[constant_index];
			assert(constant->kind == CK_CLASS);
			Value object = vm_instantiate_class(vm, &constant->class, vm_pop_value);
			vm->stack[++vm->stack_pos] = object;
			break;
		}
		case OP_FUNCTION: {
			u16 constant_index = read_u16(&ip);
			Constant *constant = &vm->program->constants[constant_index];
			assert(constant->kind == CK_METHOD);
			Value function = make_function_bc(constant_index);
			vm->stack[++vm->stack_pos] = function;
			break;
		}
		case OP_GET_LOCAL: {
			u16 local_index = read_u16(&ip);
			vm->stack[++vm->stack_pos] = locals[local_index];
			break;
		}
		case OP_SET_LOCAL: {
			u16 local_index = read_u16(&ip);
			locals[local_index] = vm->stack[vm->stack_pos];
			break;
		}
		case OP_GET_GLOBAL: {
			Identifier name = constant_string(vm, &ip);
			Value *lvalue = value_field(vm->ec, vm->global, &vm->global, name);
			vm->stack[++vm->stack_pos] = *lvalue;
			break;
		}
		case OP_SET_GLOBAL: {
			Identifier name = constant_string(vm, &ip);
			Value *lvalue = value_field(vm->ec, vm->global, &vm->global, name);
			*lvalue = vm->stack[vm->stack_pos];
			break;
		}
		case OP_GET_FIELD: {
			Identifier name = constant_string(vm, &ip);
			Value object = vm->stack[vm->stack_pos--];
			Value *lvalue = value_field(vm->ec, object, &object, name);
			vm->stack[++vm->stack_pos] = *lvalue;
			break;
		}
		case OP_SET_FIELD: {
			Identifier name = constant_string(vm, &ip);
			Value value = vm->stack[vm->stack_pos--];
			Value object = vm->stack[vm->stack_pos--];
			Value *lvalue = value_field(vm->ec, object, &object, name);
			*lvalue = value;
			vm->stack[++vm->stack_pos] = value;
			break;
		}
		case OP_JUMP: {
			i16 offset = read_u16(&ip);
			ip += offset;
			break;
		}
		case OP_BRANCH: {
			i16 offset = read_u16(&ip);
			Value condition = vm->stack[vm->stack_pos--];
			if (value_to_bool(condition)) {
				ip += offset;
			}
			break;
		}
		case OP_CALL_FUNCTION: {
			u8 argument_cnt = read_u8(&ip);
			Value *function = &vm->stack[vm->stack_pos - argument_cnt];
			if (!value_is_function(*function)) {
				exec_error(vm->ec, "Function call target is not a function");
			}
			u16 method_index = value_as_function_bc(*function);
			// Receiver (this) is null for functions
			*function = make_null();
			vm_call_method(vm, method_index, argument_cnt + 1);
			break;
		}
		case OP_CALL_METHOD: {
			Identifier name = constant_string(vm, &ip);
			u8 argument_cnt = read_u8(&ip);
			Value *lobject = &vm->stack[vm->stack_pos - (argument_cnt - 1)];
			Value *method_value = value_field_try(*lobject, lobject, name);
			if (method_value) {
				u16 method_index = value_as_function_bc(*method_value);
				vm_call_method(vm, method_index, argument_cnt);
			} else {
				Value *arguments = &vm->stack[vm->stack_pos - (argument_cnt - 2)];
				Value return_value = value_call_primitive_method(vm->ec, *lobject, name, arguments, argument_cnt - 1);
				vm->stack_pos -= argument_cnt;
				vm->stack[++vm->stack_pos] = return_value;
			}
			break;
		}
		case OP_PRINT: {
			Identifier format_string = constant_string(vm, &ip);
			u8 argument_cnt = read_u8(&ip);
			Value *arguments = &vm->stack[vm->stack_pos - (argument_cnt - 1)];
			builtin_print(vm->ec, format_string, arguments, argument_cnt);
			vm->stack_pos -= argument_cnt;
			vm->stack[++vm->stack_pos] = make_null();
			break;
		}
		case OP_DROP: {
			vm->stack_pos--;
			break;
		}
		case OP_RETURN: {
			vm->frame_stack_pos = vm->bp;
			vm->bp = saved_bp;
			return;
		}
		}
	}
}

static void
vm_run(ErrorContext *ec, Program *program)
{
	VM vm = {
		.ec = ec,
		.program = program,
		.global = make_null(),
		.stack = calloc(1024, sizeof(Value)),
		.stack_pos = -1,
		.stack_len = 1024,
		.frame_stack = calloc(1024, sizeof(Value)),
		.frame_stack_pos = 0,
		.frame_stack_len = 1024,
		.bp = 0,
	};
	vm.global = vm_instantiate_class(&vm, &program->global_class, make_null_vm);
	vm_call_method(&vm, program->entry_point, 0);
	// Check that the program left exactly one value on the stack
	assert(vm.stack_pos == 0);
}

typedef struct {
	ErrorContext *ec;
	Arena *arena;
	GArena constants; // Constant array
	GArena instructions; // u8 array
	GArena members; // u16 array (but unaligned when serialized)
	bool in_object;
	bool in_block;
	Environment *env;
	u16 local_cnt;
} CompilerState;

static size_t
inst_pos(CompilerState *cs)
{
	return garena_save(&cs->instructions);
}

static void
inst_write_u8(CompilerState *cs, u8 b)
{
	u8 *pos = garena_alloc(&cs->instructions, 1, 1);
	pos[0] = b;
}

static void
inst_write_u16(CompilerState *cs, u16 b)
{
	u8 *pos = garena_alloc(&cs->instructions, 2, 1);
	pos[0] = b >> 0;
	pos[1] = b >> 8;
}

static u16
add_constant(CompilerState *cs, Constant constant)
{
	size_t index = garena_cnt(&cs->constants, Constant);
	garena_push_value(&cs->constants, Constant, constant);
	if (index > 0xFFFF) {
		error(cs->ec, NULL, "compile", true, "Too many constants (only 65536 allowed)");
	}
	return index;
}

static u16
add_string(CompilerState *cs, Identifier name)
{
	return add_constant(cs, (Constant) {
	       .kind = CK_STRING,
	       .string = name,
	});
}

static void
inst_constant(CompilerState *cs, Constant constant)
{
	inst_write_u16(cs, add_constant(cs, constant));
}

static void
inst_string(CompilerState *cs, Identifier name)
{
	inst_write_u16(cs, add_string(cs, name));
}

static void
literal(CompilerState *cs, Constant constant)
{
	inst_write_u8(cs, OP_LITERAL);
	inst_constant(cs, constant);
}

static void
op(CompilerState *cs, OpCode op)
{
	inst_write_u8(cs, op);
}

static void
op_index(CompilerState *cs, OpCode op, u16 index)
{
	inst_write_u8(cs, op);
	inst_write_u16(cs, index);
}

static void
op_string(CompilerState *cs, OpCode op, Identifier string)
{
	inst_write_u8(cs, op);
	inst_string(cs, string);
}

static void
op_string_cnt(CompilerState *cs, OpCode op, Identifier string, u8 count)
{
	inst_write_u8(cs, op);
	inst_string(cs, string);
	inst_write_u8(cs, count);
}

static void
jump(CompilerState *cs, OpCode op, size_t *pos)
{
	inst_write_u8(cs, op);
	*pos = inst_pos(cs);
	inst_write_u16(cs, 0x0000);
}

static void
jump_fixup(CompilerState *cs, size_t pos, size_t target)
{
	int diff = target - (pos + 2);
	assert(diff <= INT16_MAX && diff >= INT16_MIN);
	if (diff > INT16_MAX || diff < INT16_MIN) {
		error(cs->ec, NULL, "compile", true, "Jump offset too large (%d, allowed %d to %d)", diff, INT16_MIN, INT16_MAX);
	}
	u16 offset = (i16) diff;
	u8 *dest = garena_mem(&cs->instructions);
	dest[pos + 0] = offset >> 0;
	dest[pos + 1] = offset >> 8;
}

static void
jump_to(CompilerState *cs, OpCode op, size_t target)
{
	size_t pos;
	jump(cs, op, &pos);
	jump_fixup(cs, pos, target);
}

static void
compile(CompilerState *cs, Ast *ast)
{
	switch (ast->kind) {
	case AST_NULL: {
		literal(cs, (Constant) { .kind = CK_NULL });
		return;
	}
	case AST_BOOLEAN: {
		literal(cs, (Constant) {
		       .kind = CK_BOOLEAN,
		       .boolean = ast->boolean.value,
		});
		return;
	}
	case AST_INTEGER: {
		literal(cs, (Constant) {
		       .kind = CK_INTEGER,
		       .integer = ast->integer.value,
		});
		return;
	}
	case AST_ARRAY: {
		AstArray *array = &ast->array;

		// Try low hanging fruit "simple initializers" that can't change
		switch (array->initializer->kind) {
		case AST_NULL:
		case AST_BOOLEAN:
		case AST_INTEGER:
		case AST_VARIABLE_ACCESS:
			compile(cs, array->size);
			compile(cs, array->initializer);
			op(cs, OP_ARRAY);
			return;
		default:;
		}

		u16 size_var = cs->local_cnt++;
		u16 i_var = cs->local_cnt++;
		u16 array_var = cs->local_cnt++;

		literal(cs, (Constant) { .kind = CK_INTEGER, .integer = 0 });
		op_index(cs, OP_SET_LOCAL, i_var);
		op(cs, OP_DROP);

		compile(cs, array->size);
		op_index(cs, OP_SET_LOCAL, size_var);
		// Dummy initializer
		literal(cs, (Constant) { .kind = CK_NULL });
		op(cs, OP_ARRAY);
		op_index(cs, OP_SET_LOCAL, array_var);

		size_t condition_to_init;
		size_t condition_to_after;

		size_t condition = inst_pos(cs);
		op_index(cs, OP_GET_LOCAL, i_var);
		op_index(cs, OP_GET_LOCAL, size_var);
		op_string_cnt(cs, OP_CALL_METHOD, LESS, 2);
		jump(cs, OP_BRANCH, &condition_to_init);
		jump(cs, OP_JUMP, &condition_to_after);
		size_t init = inst_pos(cs);
		op_index(cs, OP_GET_LOCAL, i_var);
		compile(cs, array->initializer);
		op_string_cnt(cs, OP_CALL_METHOD, SET, 3);
		op(cs, OP_DROP);
		op_index(cs, OP_GET_LOCAL, i_var);
		literal(cs, (Constant) { .kind = CK_INTEGER, .integer = 1 });
		op_string_cnt(cs, OP_CALL_METHOD, PLUS, 2);
		op_index(cs, OP_SET_LOCAL, i_var);
		op(cs, OP_DROP);
		op_index(cs, OP_GET_LOCAL, array_var);
		jump_to(cs, OP_JUMP, condition);

		jump_fixup(cs, condition_to_init, init);
		jump_fixup(cs, condition_to_after, inst_pos(cs));
		return;
	}
	case AST_OBJECT: {
		AstObject *object = &ast->object;
		compile(cs, object->extends);
		bool saved_in_object = cs->in_object;
		size_t start = garena_save(&cs->members);

		cs->in_object = true;
		for (size_t i = 0; i < object->member_cnt; i++) {
			Ast *ast_member = object->members[i];
			switch (ast_member->kind) {
			case AST_DECLARATION:
				compile(cs, ast_member);
				break;
			default: UNREACHABLE();
			}
		}
		op(cs, OP_OBJECT);

		// NOTE: due to losing alignment when serializing, we refer to
		// members with `u8` pointers while compiling them as if they
		// were u16
		size_t member_cnt = garena_cnt_from(&cs->members, u16, start);
		u16 *members = move_to_arena(cs->arena, &cs->members, start, u16);
		inst_constant(cs, (Constant) {
		       .kind = CK_CLASS,
		       .class = (Class) {
				.member_cnt = member_cnt,
				.members = (u8 *) members,
			},
		});
		cs->in_object = saved_in_object;
		return;
	}
	case AST_FUNCTION: {
		AstFunction *function = &ast->function;
		Environment *saved_environment = cs->env;
		u16 saved_local_cnt = cs->local_cnt;
		size_t start = garena_save(&cs->instructions);
		bool saved_in_block = cs->in_block;
		bool saved_in_object = cs->in_object;

		cs->local_cnt = 0;
		cs->in_block = false;
		cs->in_object = false;

		cs->env = env_create(cs->env);
		env_define(cs->env, THIS, make_integer(cs->local_cnt));
		cs->local_cnt += 1;
		for (size_t i = 0; i < function->parameter_cnt; i++) {
			env_define(cs->env, function->parameters[i], make_integer(cs->local_cnt));
			cs->local_cnt += 1;
		}
		compile(cs, function->body);
		op(cs, OP_RETURN);
		env_destroy(cs->env);

		size_t instruction_len = garena_cnt_from(&cs->instructions, u8, start);
		u8 *instruction_start = move_to_arena(cs->arena, &cs->instructions, start, u8);
		u16 method = add_constant(cs, (Constant) {
		       .kind = CK_METHOD,
		       .method = (CMethod) {
				.local_cnt = cs->local_cnt - (function->parameter_cnt + 1),
				.parameter_cnt = function->parameter_cnt + 1,
				.instruction_start = instruction_start,
				.instruction_len = instruction_len,
			},
		});
		cs->env = saved_environment;
		cs->local_cnt = saved_local_cnt;
		cs->in_block = saved_in_block;
		cs->in_object = saved_in_object;
		op_index(cs, OP_FUNCTION, method);
		return;
	}

	case AST_DECLARATION: {
		AstDeclaration *declaration = &ast->declaration;
		compile(cs, declaration->value);
		if (cs->in_object || !cs->in_block) {
			u16 name = add_string(cs, declaration->name);
			garena_push_value(&cs->members, u16, name);
			if (!cs->in_object) {
				op_string(cs, OP_SET_GLOBAL, declaration->name);
			}
		} else {
			env_define(cs->env, declaration->name, make_integer(cs->local_cnt));
			op_index(cs, OP_SET_LOCAL, cs->local_cnt);
			cs->local_cnt += 1;
		}
		return;
	}

	case AST_VARIABLE_ACCESS: {
		AstVariableAccess *variable_access = &ast->variable_access;
		Value *local_index = env_lookup_raw(cs->env, variable_access->name);
		if (local_index) {
			op_index(cs, OP_GET_LOCAL, value_as_integer(*local_index));
		} else {
			op_string(cs, OP_GET_GLOBAL, variable_access->name);
		}
		return;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		AstVariableAssignment *variable_assignment = &ast->variable_assignment;
		compile(cs, variable_assignment->value);
		Value *local_index = env_lookup_raw(cs->env, variable_assignment->name);
		if (local_index) {
			op_index(cs, OP_SET_LOCAL, value_as_integer(*local_index));
		} else {
			op_string(cs, OP_SET_GLOBAL, variable_assignment->name);
		}
		return;
	}

	case AST_INDEX_ACCESS: {
		AstIndexAccess *index_access = &ast->index_access;
		compile(cs, index_access->object);
		compile(cs, index_access->index);
		op_string_cnt(cs, OP_CALL_METHOD, GET, 2);
		return;
	}
	case AST_INDEX_ASSIGNMENT: {
		AstIndexAssignment *index_assignment = &ast->index_assignment;
		compile(cs, index_assignment->object);
		compile(cs, index_assignment->index);
		compile(cs, index_assignment->value);
		op_string_cnt(cs, OP_CALL_METHOD, SET, 3);
		return;
	}

	case AST_FIELD_ACCESS: {
		AstFieldAccess *field_access = &ast->field_access;
		compile(cs, field_access->object);
		op_string(cs, OP_GET_FIELD, field_access->field);
		return;
	}
	case AST_FIELD_ASSIGNMENT: {
		AstFieldAssignment *field_assignment = &ast->field_assignment;
		compile(cs, field_assignment->object);
		compile(cs, field_assignment->value);
		op_string(cs, OP_SET_FIELD, field_assignment->field);
		return;
	}

	case AST_FUNCTION_CALL: {
		AstFunctionCall *function_call = &ast->function_call;
		compile(cs, function_call->function);
		for (size_t i = 0; i < function_call->argument_cnt; i++) {
			compile(cs, function_call->arguments[i]);
		}
		op(cs, OP_CALL_FUNCTION);
		inst_write_u8(cs, function_call->argument_cnt);
		return;
	}
	case AST_METHOD_CALL: {
		AstMethodCall *method_call = &ast->method_call;
		compile(cs, method_call->object);
		for (size_t i = 0; i < method_call->argument_cnt; i++) {
			compile(cs, method_call->arguments[i]);
		}
		op_string_cnt(cs, OP_CALL_METHOD, method_call->name, method_call->argument_cnt + 1);
		return;
	}

	case AST_IF: {
		AstConditional *conditional = &ast->conditional;
		size_t cond_to_consequent;
		size_t cond_to_alternative;
		size_t consequent_to_after;

		compile(cs, conditional->condition);
		jump(cs, OP_BRANCH, &cond_to_consequent);
		jump(cs, OP_JUMP, &cond_to_alternative);
		size_t consequent = inst_pos(cs);
		compile(cs, conditional->consequent);
		jump(cs, OP_JUMP, &consequent_to_after);
		size_t alternative = inst_pos(cs);
		compile(cs, conditional->alternative);

		jump_fixup(cs, cond_to_consequent, consequent);
		jump_fixup(cs, cond_to_alternative, alternative);
		jump_fixup(cs, consequent_to_after, inst_pos(cs));
		return;
	}
	case AST_WHILE: {
		AstLoop *loop = &ast->loop;
		size_t condition_to_body;
		size_t condition_to_after;

		literal(cs, (Constant) { .kind = CK_NULL });
		size_t condition = inst_pos(cs);
		compile(cs, loop->condition);
		jump(cs, OP_BRANCH, &condition_to_body);
		jump(cs, OP_JUMP, &condition_to_after);
		size_t body = inst_pos(cs);
		// Drop value from previous iteration (or the initial null)
		op(cs, OP_DROP);
		compile(cs, loop->body);
		jump_to(cs, OP_JUMP, condition);

		jump_fixup(cs, condition_to_body, body);
		jump_fixup(cs, condition_to_after, inst_pos(cs));
		return;
	}
	case AST_PRINT: {
		AstPrint *print = &ast->print;
		for (size_t i = 0; i < print->argument_cnt; i++) {
			compile(cs, print->arguments[i]);
		}
		op_string_cnt(cs, OP_PRINT, print->format, print->argument_cnt);
		return;
	}
	case AST_BLOCK: {
		AstBlock *block = &ast->block;
		Environment *saved_environment = cs->env;
		bool saved_in_block = cs->in_block;
		cs->in_block = true;
		cs->env = env_create(cs->env);
		compile(cs, block->expressions[0]);
		for (size_t i = 1; i < block->expression_cnt; i++) {
			op(cs, OP_DROP);
			compile(cs, block->expressions[i]);
		}
		env_destroy(cs->env);
		cs->env = saved_environment;
		cs->in_block = saved_in_block;
		return;
	}
	case AST_TOP: {
		AstTop *top = &ast->top;
		compile(cs, top->expressions[0]);
		for (size_t i = 1; i < top->expression_cnt; i++) {
			op(cs, OP_DROP);
			compile(cs, top->expressions[i]);
		}
		// emit OP_RETURN in outer level (in case there is a AST_NULL
		// instead of AST_TOP as the top level).
		return;
	}
	}
	UNREACHABLE();
}

void
compile_ast(ErrorContext *ec, Arena *arena, Program *program, Ast *ast)
{
	CompilerState cs = {
		.ec = ec,
		.arena = arena,
		.constants = {0},
		.instructions = {0},
		.members = {0},
		.in_object = false,
		.in_block = false,
		.env = NULL,
		.local_cnt = 0,
	};
	garena_init(&cs.constants);
	garena_init(&cs.instructions);
	garena_init(&cs.members);

	size_t start = garena_save(&cs.instructions);
	compile(&cs, ast);
	op(&cs, OP_RETURN);

	size_t instruction_len = garena_cnt_from(&cs.instructions, u8, start);
	u8 *instruction_start = move_to_arena(cs.arena, &cs.instructions, start, u8);
	u16 entry_point = add_constant(&cs, (Constant) {
	       .kind = CK_METHOD,
	       .method = (CMethod) {
			.local_cnt = cs.local_cnt,
			.parameter_cnt = 0,
			.instruction_start = instruction_start,
			.instruction_len = instruction_len,
		},
	});

	program->constant_cnt = garena_cnt(&cs.constants, Constant);
	program->constants = move_to_arena(cs.arena, &cs.constants, 0, Constant);

	size_t member_cnt = garena_cnt_from(&cs.members, u16, start);
	u16 *members = move_to_arena(cs.arena, &cs.members, start, u16);
	program->global_class = (Class) {
		.members = (u8 *) members,
		.member_cnt = member_cnt,
	};

	program->entry_point = entry_point;

	garena_destroy(&cs.constants);
	garena_destroy(&cs.instructions);
	garena_destroy(&cs.members);
}

static void
write_u32(FILE *f, u32 num)
{
	fputc(num >> 0, f);
	fputc(num >> 8, f);
	fputc(num >> 16, f);
	fputc(num >> 24, f);
}

static void
write_u16(FILE *f, u16 num)
{
	fputc(num >> 0, f);
	fputc(num >> 8, f);
}

static void
write_u8(FILE *f, u8 num)
{
	fputc(num, f);
}

static void
write_class(FILE *f, Class *class)
{
	write_u16(f, class->member_cnt);
	u8 *members = class->members;
	for (size_t i = 0; i < class->member_cnt; i++) {
		u16 member = read_u16(&members);
		write_u16(f, member);
	}
}

static void
write_constant(FILE *f, Constant *constant)
{
	write_u8(f, constant->kind);
	switch (constant->kind) {
	case CK_NULL:
		break;
	case CK_BOOLEAN: {
		write_u8(f, (u8) constant->boolean);
		break;
	}
	case CK_INTEGER:
		write_u32(f, constant->integer);
		break;
	case CK_STRING:
		write_u32(f, constant->string.len);
		fwrite(constant->string.name, constant->string.len, 1, f);
		break;
	case CK_METHOD:
		write_u8(f, constant->method.parameter_cnt);
		write_u16(f, constant->method.local_cnt);
		write_u32(f, constant->method.instruction_len);
		fwrite(constant->method.instruction_start, constant->method.instruction_len, 1, f);
		break;
	case CK_CLASS: {
		write_class(f, &constant->class);
		break;
	}
	default:
		UNREACHABLE();
	}
}

void
write_program(Program *program, FILE *f)
{
	write_u16(f, program->constant_cnt);
	for (size_t i = 0; i < program->constant_cnt; i++) {
		write_constant(f, &program->constants[i]);
	}
	write_class(f, &program->global_class);
	write_u16(f, program->entry_point);
}

int
main(int argc, char **argv) {

	Arena arena_;
	Arena *arena = &arena_;
	arena_init(arena);
	if(argc != 3) {
		return 1;
	}
	FILE *f = fopen(argv[2], "rb");
	fseek(f, 0, SEEK_END);
	long fsize = ftell(f);
	fseek(f, 0, SEEK_SET);
	u8 *buf = arena_alloc(arena, fsize);
	fread(buf, fsize, 1, f);
	fclose(f);

	ErrorContext ec = {
		.arena = arena,
	};

	if (setjmp(ec.loc) != 0) {
		goto end;
	}

	if (strcmp(argv[1], "run_ast") == 0) {
		Ast *ast = parse(&ec, arena, buf, fsize);
		assert(ast);
		interpret_ast(&ec, ast);
	} else if (strcmp(argv[1], "run") == 0) {
		Ast *ast = parse(&ec, arena, buf, fsize);
		assert(ast);
		Program program;
		compile_ast(&ec, arena, &program, ast);
		vm_run(&ec, &program);
	} else if (strcmp(argv[1], "execute") == 0) {
		Program program;
		read_program(&ec, &program, buf, fsize);
		vm_run(&ec, &program);
	} else if (strcmp(argv[1], "compile") == 0) {
		Ast *ast = parse(&ec, arena, buf, fsize);
		assert(ast);
		Program program;
		compile_ast(&ec, arena, &program, ast);
		write_program(&program, stdout);
		fflush(stdout);
	} else if (strcmp(argv[1], "serde") == 0) {
		Ast *ast = parse(&ec, arena, buf, fsize);
		assert(ast);
		Program program;
		compile_ast(&ec, arena, &program, ast);
		FILE *f = fopen("out.bc", "wb");
		write_program(&program, f);
		fclose(f);
		f = fopen("out.bc", "rb");
		fseek(f, 0, SEEK_END);
		long fsize = ftell(f);
		fseek(f, 0, SEEK_SET);
		u8 *buf = arena_alloc(arena, fsize);
		fread(buf, fsize, 1, f);
		fclose(f);
		Program program2;
		read_program(&ec, &program2, buf, fsize);
		vm_run(&ec, &program2);
	}

end:
	for (Error *err = ec.error_head; err; err = err->next) {
		if (!err->pos) {
			fprintf(stderr, "%s error: %s\n", err->kind, err->msg);
			continue;
		}
		const u8 *line_start = ec.source;
		size_t line = 0;
		const u8 *pos = ec.source;
		for (; pos < err->pos; pos++) {
			if (*pos == '\n') {
				line_start = pos + 1;
				line++;
			}
		}
		size_t col = pos - line_start;
		const u8 *source_end = ec.source + ec.source_len;
		const u8 *line_end = pos;
		for (; line_end < source_end && *line_end != '\n'; line_end++);
		fprintf(stderr, "[%zu:%zu]: %s error: %s\n", line + 1, col + 1, err->kind, err->msg);
		fprintf(stderr, "  %.*s\n", (int) (line_end - line_start), line_start);
		fprintf(stderr, "  %*s\n", (int) (pos - line_start + 1), "^");
	}

	arena_destroy(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
