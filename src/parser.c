#include <stdio.h>

#include "parser.h"

#define UNREACHABLE() unreachable(__FILE__, __LINE__)
_Noreturn void
unreachable(char *file, size_t line)
{
	fprintf(stderr, "ERROR: unreachable code reached at %s:%zu\n", file,
			line);
	exit(EXIT_FAILURE);
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

typedef enum {
	ASSOC_LEFT,
	ASSOC_RIGHT,
} Associativity;

typedef enum {
	PREC_NONE,
	PREC_EXPR,
	PREC_ASGN,
	PREC_DISJ,
	PREC_CONJ,
	PREC_CMP,
	PREC_ADD,
	PREC_MUL,
	PREC_POST,
	PREC_TOP,
} Precedence;

#define TOKENS(KW, PU, OT) \
	/* token          repr             nud       led       prec  assoc*/\
	OT(NUMBER,        "a number",      primary,  lefterr,  TOP,  LEFT)  \
	OT(IDENTIFIER,    "an identifier", ident,    lefterr,  TOP,  LEFT)  \
	OT(STRING,        "a string",      nullerr,  lefterr,  TOP,  LEFT)  \
                                                                            \
	PU(BAR,           "|",             nullerr,  binop,    DISJ, LEFT)  \
	PU(AMPERSANT,     "&",             nullerr,  binop,    CONJ, LEFT)  \
	PU(EQUAL_EQUAL,   "==",            nullerr,  binop,    CMP,  LEFT)  \
	PU(BANG_EQUAL,    "!=",            nullerr,  binop,    CMP,  LEFT)  \
	PU(GREATER,       ">",             nullerr,  binop,    CMP,  LEFT)  \
	PU(LESS,          "<",             nullerr,  binop,    CMP,  LEFT)  \
	PU(GREATER_EQUAL, ">=",            nullerr,  binop,    CMP,  LEFT)  \
	PU(LESS_EQUAL,    "<=",            nullerr,  binop,    CMP,  LEFT)  \
	PU(PLUS,          "+",             nullerr,  binop,    ADD,  LEFT)  \
	PU(MINUS,         "-",             nullerr,  binop,    ADD,  LEFT)  \
	PU(ASTERISK,      "*",             nullerr,  binop,    MUL,  LEFT)  \
	PU(SLASH,         "/",             nullerr,  binop,    MUL,  LEFT)  \
	PU(PERCENT,       "%",             nullerr,  binop,    MUL,  LEFT)  \
	                                                                    \
	PU(SEMICOLON,     ";",             nullerr,  stop,     NONE, LEFT)  \
	PU(LPAREN,        "(",             paren,    call,     POST, LEFT)  \
	PU(RPAREN,        ")",             nullerr,  stop,     NONE, LEFT)  \
	PU(EQUAL,         "=",             nullerr,  eqerr,    ASGN, LEFT)  \
	PU(LARROW,        "<-",            nullerr,  assign,   ASGN, RIGHT) \
	PU(RARROW,        "->",            nullerr,  lefterr,  TOP,  LEFT)  \
	PU(DOT,           ".",             nullerr,  field,    POST, LEFT)  \
	PU(LBRACKET,      "[",             nullerr,  indexing, POST, LEFT)  \
	PU(RBRACKET,      "]",             nullerr,  stop,     NONE, LEFT)  \
	PU(COMMA,         ",",             nullerr,  stop,     NONE, LEFT)  \
	                                                                    \
	KW(BEGIN,         "begin",         block,    stop,     NONE, LEFT)  \
	KW(END,           "end",           nullerr,  stop,     NONE, LEFT)  \
	KW(IF,            "if",            cond,     lefterr,  TOP,  LEFT)  \
	KW(THEN,          "then",          nullerr,  stop,     NONE, LEFT)  \
	KW(ELSE,          "else",          nullerr,  stop,     NONE, LEFT)  \
	KW(LET,           "let",           let,      lefterr,  TOP,  LEFT)  \
	KW(NULL,          "null",          primary,  lefterr,  TOP,  LEFT)  \
	KW(PRINT,         "print",         print,    lefterr,  TOP,  LEFT)  \
	KW(OBJECT,        "object",        object,   lefterr,  TOP,  LEFT)  \
	KW(EXTENDS,       "extends",       nullerr,  lefterr,  TOP,  LEFT)  \
	KW(WHILE,         "while",         loop,     lefterr,  TOP,  LEFT)  \
	KW(DO,            "do",            nullerr,  stop,     NONE, LEFT)  \
	KW(FUNCTION,      "function",      function, lefterr,  TOP,  LEFT)  \
	KW(ARRAY,         "array",         array,    lefterr,  TOP,  LEFT)  \
	KW(TRUE,          "true",          primary,  lefterr,  TOP,  LEFT)  \
	KW(FALSE,         "false",         primary,  lefterr,  TOP,  LEFT)  \
	                                                                    \
	OT(EOF,           "end of input",  nullerr,  stop,     NONE, LEFT)  \
	OT(ERROR,         "lex error",     nullerr,  lefterr,  TOP,  LEFT)

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
	Str str;
} Token;

Lexer
lex_create(Str source)
{
	return (Lexer) {
		.pos = source.str,
		.end = source.str + source.len,
	};
}

#define ALPHA '_': case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm': case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'v': case 'u': case 'w': case 'x': case 'y': case 'z': case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M': case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'V': case 'U': case 'W': case 'X': case 'Y': case 'Z'

#define DIGIT '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9'

static void
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
		} break;
		case LS_IDENTIFIER: switch (c) {
			case ALPHA: case DIGIT: break;
			default: tok = TK_IDENTIFIER; goto prev_done;
		} break;
		case LS_NUMBER: switch (c) {
			case DIGIT: break;
			default: tok = TK_NUMBER; goto prev_done;
		} break;
		case LS_STRING: switch (c) {
			case '"': tok = TK_STRING; end_offset = -1; goto done;
			case '\\': state = LS_STRING_ESC; break;
		} break;
		case LS_STRING_ESC: switch (c) {
			case 'n': case 't': case 'r': case '~': case '"': case '\\': state = LS_STRING; break;
			default: goto err;
		} break;
		case LS_SLASH: switch (c) {
			case '/': state = LS_LINE_COMMENT; start += 2; break;
			case '*': state = LS_BLOCK_COMMENT; start += 2; break;
			default: tok = TK_SLASH; goto prev_done;
		} break;
		case LS_LINE_COMMENT: switch (c) {
			case '\n': state = LS_START; start = lexer->pos + 1; break;
		} break;
		case LS_BLOCK_COMMENT: switch (c) {
			case '*': state = LS_BLOCK_COMMENT_STAR; break;
		} break;
		case LS_BLOCK_COMMENT_STAR: switch (c) {
			case '*': break;
			case '/': state = LS_START; start = lexer->pos + 1; break;
			default: state = LS_BLOCK_COMMENT; break;
		} break;
		case LS_MINUS: switch (c) {
			case '>': tok = TK_RARROW; goto done;
			case DIGIT: state = LS_NUMBER; break;
			default: tok = TK_MINUS; goto prev_done;
		} break;
		case LS_EQUAL: switch (c) {
			case '=': tok = TK_EQUAL_EQUAL; goto done;
			default: tok = TK_EQUAL; goto prev_done;
		} break;
		case LS_GREATER: switch (c) {
			case '=': tok = TK_GREATER_EQUAL; goto done;
			default: tok = TK_GREATER; goto prev_done;
		} break;
		case LS_LESS: switch (c) {
			case '=': tok = TK_LESS_EQUAL; goto done;
			case '-': tok = TK_LARROW; goto done;
			default: tok = TK_LESS; goto prev_done;
		} break;
		case LS_EXCLAM: switch (c) {
			case '=': tok = TK_BANG_EQUAL; goto done;
			default: goto err;
		} break;
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
	token->str.str = start;
	token->str.len = length;
}

typedef struct {
	Arena *arena;
	GArena *scratch;
	void *user_data;
	void (*error_callback)(void *user_data, const u8 *err_pos, const char *msg, va_list ap);
	Lexer lexer;
	Token lookahead;
	Token prev;
	bool had_error;
	bool panic_mode;
} Parser;

static void
parser_error(Parser *parser, Token errtok, bool panic, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	if (!parser->panic_mode) {
		parser->error_callback(parser->user_data, errtok.str.str, msg, ap);
		parser->had_error = true;
		parser->panic_mode = panic;
	}
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
	return parser->prev;
}

static Token
discard(Parser *parser)
{
	parser->prev = parser->lookahead;
	lex_next(&parser->lexer, &parser->lookahead);
	if (parser->lookahead.kind == TK_ERROR) {
		parser_error(parser, parser->lookahead, true, "Unexpected character");
	}
	return parser->prev;
}

static void
eat(Parser *parser, TokenKind kind)
{
	TokenKind tok = peek(parser);
	if (tok != kind) {
		parser_error(parser, parser->lookahead, true, "Expected %s, found %s", tok_repr[kind], tok_repr[tok]);
		return;
	}
	discard(parser);
}

static void
eat_identifier(Parser *parser, Str *identifier)
{
	TokenKind tok = peek(parser);
	if (!tok_is_identifier(tok)) {
		parser_error(parser, parser->lookahead, true, "Expected %s, found %s", tok_repr[TK_IDENTIFIER], tok_repr[tok]);
		return;
	}
	discard(parser);
	*identifier = prev_tok(parser).str;
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

#define AST_CREATE(type, var, arena, kind) type *var = ast_create_((arena), (kind), sizeof(type))
static void *
ast_create_(Arena *arena, AstKind kind, size_t size)
{
	Ast *ast = arena_alloc(arena, size);
	memset(ast, 0, size);
	ast->kind = kind;
	return ast;
}

static Ast *
create_null(Parser *parser)
{
	AST_CREATE(AstNull, ast, parser->arena, AST_NULL);
	return &ast->base;
}

static Ast *expression_bp(Parser *parser, int bp);

static Ast *
expression(Parser *parser)
{
	return expression_bp(parser, PREC_EXPR);
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
	*n = garena_cnt_from(parser->scratch, start, Ast *);
	*list = move_to_arena(parser->arena, parser->scratch, start, Ast *);
}

static void
identifier_list(Parser *parser, Str **list, size_t *n, TokenKind separator, TokenKind terminator)
{
	size_t start = garena_save(parser->scratch);
	while (!try_eat(parser, terminator)) {
		eat_identifier(parser, garena_push(parser->scratch, Str));
		if (!try_eat(parser, separator)) {
			eat(parser, terminator);
			break;
		}
	}
	*n = garena_cnt_from(parser->scratch, start, Str);
	*list = move_to_arena(parser->arena, parser->scratch, start, Str);
}

static Ast *
nullerr(Parser *parser)
{
	TokenKind tok = peek(parser);
	parser_error(parser, parser->lookahead, true, "Invalid start of expression %s", tok_repr[tok]);
	return create_null(parser);
}

static Ast *
primary(Parser *parser)
{
	Token token = discard(parser);
	switch (token.kind) {
	case TK_NUMBER: {
		AST_CREATE(AstInteger, integer, parser->arena, AST_INTEGER);
		const u8 *pos = token.str.str;
		const u8 *end = pos + token.str.len;
		bool negative = 0;
		while (*pos == '-') {
			negative = !negative;
			pos += 1;
		}
		i64 value = 0;
		for (; pos < end; pos++) {
			value = value * 10 + (*pos - '0');
		}
		integer->value = (i32) (negative ? -value : value);
		return &integer->base;
	}
	case TK_NULL: {
		AST_CREATE(AstNull, null, parser->arena, AST_NULL);
		return &null->base;
	}
	case TK_TRUE: {
		AST_CREATE(AstBoolean, boolean, parser->arena, AST_BOOLEAN);
		boolean->value = true;
		return &boolean->base;
	}
	case TK_FALSE: {
		AST_CREATE(AstBoolean, boolean, parser->arena, AST_BOOLEAN);
		boolean->value = false;
		return &boolean->base;
	}
	default:
		UNREACHABLE();
	}
}

static Ast *
ident(Parser *parser)
{
	AST_CREATE(AstVariableAccess, variable_access, parser->arena, AST_VARIABLE_ACCESS);
	eat_identifier(parser, &variable_access->name);
	return &variable_access->base;
}

static Ast *
block(Parser *parser)
{
	AST_CREATE(AstBlock, block, parser->arena, AST_BLOCK);
	eat(parser, TK_BEGIN);
	expression_list(parser, &block->expressions, &block->expression_cnt, TK_SEMICOLON, TK_END);
	// begin end => null
	if (block->expression_cnt == 0) {
		block->base.kind = AST_NULL;
	}
	return &block->base;
}

static Ast *
let(Parser *parser)
{
	AST_CREATE(AstDefinition, definition, parser->arena, AST_DEFINITION);
	eat(parser, TK_LET);
	eat_identifier(parser, &definition->name);
	eat(parser, TK_EQUAL);
	definition->value = expression(parser);
	return &definition->base;
}

static Ast *
array(Parser *parser)
{
	AST_CREATE(AstArray, array, parser->arena, AST_ARRAY);
	eat(parser, TK_ARRAY);
	eat(parser, TK_LPAREN);
	array->size = expression(parser);
	eat(parser, TK_COMMA);
	array->initializer = expression(parser);
	eat(parser, TK_RPAREN);
	return &array->base;
}

static Ast *
object(Parser *parser)
{
	AST_CREATE(AstObject, object, parser->arena, AST_OBJECT);
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
		if (object->members[i]->kind != AST_DEFINITION) {
			parser_error(parser, object_tok, false, "Found object member that is not a definition");
		}
	}
	return &object->base;
}

static Ast *
cond(Parser *parser)
{
	AST_CREATE(AstConditional, conditional, parser->arena, AST_CONDITIONAL);
	eat(parser, TK_IF);
	conditional->condition = expression(parser);
	eat(parser, TK_THEN);
	conditional->consequent = expression(parser);
	if (try_eat(parser, TK_ELSE)) {
		conditional->alternative = expression(parser);
	} else {
		conditional->alternative = create_null(parser);
	}
	return &conditional->base;
}

static Ast *
loop(Parser *parser)
{
	AST_CREATE(AstLoop, loop, parser->arena, AST_LOOP);
	eat(parser, TK_WHILE);
	loop->condition = expression(parser);
	eat(parser, TK_DO);
	loop->body = expression(parser);
	return &loop->base;
}

static Ast *
print(Parser *parser)
{
	AST_CREATE(AstPrint, print, parser->arena, AST_PRINT);
	eat(parser, TK_PRINT);
	eat(parser, TK_LPAREN);
	eat(parser, TK_STRING);
	Token fmt_tok = prev_tok(parser);
	print->format = fmt_tok.str;
	size_t formats = 0;
	for (size_t i = 0; i < print->format.len; i++) {
		switch (print->format.str[i]) {
		case '\\': i++; continue;
		case '~': formats += 1;
		}
	}
	if (try_eat(parser, TK_COMMA)) {
		expression_list(parser, &print->arguments, &print->argument_cnt, TK_COMMA, TK_RPAREN);
	} else {
		eat(parser, TK_RPAREN);
	}
	if (formats != print->argument_cnt) {
		parser_error(parser, fmt_tok, false, "Invalid number of print arguments: %zu expected, got %zu", formats, print->argument_cnt);
	}
	return &print->base;
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
	AST_CREATE(AstFunction, function, parser->arena, AST_FUNCTION);
	Ast *ast = &function->base;
	eat(parser, TK_FUNCTION);
	if (tok_is_identifier(peek(parser))) {
		AST_CREATE(AstDefinition, definition, parser->arena, AST_DEFINITION);
		eat_identifier(parser, &definition->name);
		definition->value = &function->base;
		ast = &definition->base;
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
lefterr(Parser *parser, Ast *left, int rbp)
{
	(void) left;
	(void) rbp;
	TokenKind tok = peek(parser);
	parser_error(parser, parser->lookahead, true, "Invalid expression continuing/ending token %s", tok_repr[tok]);
	// Set the current token to something with low binding power to not get
	// into infinite loop of `lefterr`s on the same token.
	parser->lookahead.kind = TK_EOF;
	return create_null(parser);
}

static Ast *
binop(Parser *parser, Ast *left, int rbp)
{
	AST_CREATE(AstMethodCall, method_call, parser->arena, AST_METHOD_CALL);
	method_call->object = left;
	Token token = discard(parser);
	method_call->name = token.str;
	method_call->arguments = arena_alloc(parser->arena, sizeof(*method_call->arguments));
	method_call->arguments[0] = expression_bp(parser, rbp);
	//method_call->arguments = expression_bp(parser, rbp);
	method_call->argument_cnt = 1;
	return &method_call->base;
}

static Ast *
call(Parser *parser, Ast *left, int rbp)
{
	(void) rbp;
	eat(parser, TK_LPAREN);
	switch (left->kind) {
	case AST_FIELD_ACCESS: {
		AstFieldAccess *field_access = (AstFieldAccess *) left;
		AST_CREATE(AstMethodCall, method_call, parser->arena, AST_METHOD_CALL);
		left->kind = AST_METHOD_CALL;
		method_call->object = field_access->object;
		method_call->name = field_access->field;
		expression_list(parser, &method_call->arguments, &method_call->argument_cnt, TK_COMMA, TK_RPAREN);
		return &method_call->base;
	}
	default: {
		AST_CREATE(AstFunctionCall, function_call, parser->arena, AST_FUNCTION_CALL);
		function_call->function = left;
		expression_list(parser, &function_call->arguments, &function_call->argument_cnt, TK_COMMA, TK_RPAREN);
		return &function_call->base;
	}
	}
}

static Ast *
indexing(Parser *parser, Ast *left, int rbp)
{
	// rbp not used - delimited by TK_RBRACKET, not by precedence
	(void) rbp;
	AST_CREATE(AstIndexAccess, index_access, parser->arena, AST_INDEX_ACCESS);
	eat(parser, TK_LBRACKET);
	index_access->object = left;
	index_access->index = expression(parser);
	eat(parser, TK_RBRACKET);
	return &index_access->base;
}

static Ast *
field(Parser *parser, Ast *left, int rbp)
{
	(void) rbp;
	AST_CREATE(AstFieldAccess, field_access, parser->arena, AST_FIELD_ACCESS);
	eat(parser, TK_DOT);
	field_access->object = left;
	eat_identifier(parser, &field_access->field);
	return &field_access->base;
}

static Ast *
assign(Parser *parser, Ast *left, int rbp)
{
	eat(parser, TK_LARROW);
	switch (left->kind) {
	case AST_VARIABLE_ACCESS: {
		AstVariableAccess *variable_access = (AstVariableAccess *) left;
		AST_CREATE(AstVariableAssignment, variable_assignment, parser->arena, AST_VARIABLE_ASSIGNMENT);
		variable_assignment->name = variable_access->name;
		variable_assignment->value = expression_bp(parser, rbp);
		return &variable_assignment->base;
	}
	case AST_FIELD_ACCESS: {
		AstFieldAccess *field_access = (AstFieldAccess *) left;
		AST_CREATE(AstFieldAssignment, field_assignment, parser->arena, AST_FIELD_ASSIGNMENT);
		field_assignment->object = field_access->object;
		field_assignment->field = field_access->field;
		field_assignment->value = expression_bp(parser, rbp);
		return &field_assignment->base;
	}
	case AST_INDEX_ACCESS: {
		AstIndexAccess *index_access = (AstIndexAccess *) left;
		AST_CREATE(AstIndexAssignment, index_assignment, parser->arena, AST_INDEX_ASSIGNMENT);
		index_assignment->object = index_access->object;
		index_assignment->index = index_access->index;
		index_assignment->value = expression_bp(parser, rbp);
		return &index_assignment->base;
	}
	default:
		parser_error(parser, parser->prev, false, "Invalid assignment left hand side, expected variable, index or field access");
		return left;
	}
}

static Ast *
eqerr(Parser *parser, Ast *left, int rbp)
{
	parser_error(parser, parser->lookahead, false, "Unexpected %s, did you mean to use %s for assignment?", tok_repr[TK_EQUAL], tok_repr[TK_LARROW]);
	parser->lookahead.kind = TK_LARROW;
	return assign(parser, left, rbp);
}


typedef struct {
	Ast *(*nud)(Parser *);
} NullInfo;

static NullInfo null_info[] = {
	#define TOK_NULL(tok, str, nud, led, lbp, rbp) { nud },
	TOKENS(TOK_NULL, TOK_NULL, TOK_NULL)
	#undef TOK_STR
};

static bool
at_synchronization_point(Parser *parser)
{
	if (parser->prev.kind == TK_EOF) {
		// nothing to synchronize
		return true;
	}
	if (parser->prev.kind == TK_SEMICOLON && null_info[parser->lookahead.kind].nud != nullerr) {
		// an expression separator and a token that starts an expression
		return true;
	}
	return false;
}

typedef struct {
	Ast *(*led)(Parser *, Ast *left, int rbp);
	int lbp;
	int rbp;
} LeftInfo;

static LeftInfo left_info[] = {
	#define TOK_LEFT(tok, str, nud, led, prec, assoc) { led, PREC_##prec, PREC_##prec + (ASSOC_##assoc == ASSOC_LEFT) },
	TOKENS(TOK_LEFT, TOK_LEFT, TOK_LEFT)
	#undef TOK_STR
};

static Ast *
expression_bp(Parser *parser, int bp)
{
	NullInfo ni = null_info[peek(parser)];
	Ast *left = ni.nud(parser);

	for (;;) {
		LeftInfo li = left_info[peek(parser)];
		if (li.lbp < bp) {
			break;
		}
		left = li.led(parser, left, li.rbp);
	}

	return left;
}

static Ast *
top(Parser *parser)
{
	AST_CREATE(AstTop, top, parser->arena, AST_TOP);
	for (;;) {
		expression_list(parser, &top->expressions, &top->expression_cnt, TK_SEMICOLON, TK_EOF);
		if (!parser->panic_mode) {
			break;
		}
		do {
			discard(parser);
		} while (!at_synchronization_point(parser));
		parser->panic_mode = false;
	}
	// empty program => null
	if (top->expression_cnt == 0) {
		top->base.kind = AST_NULL;
	}
	return &top->base;
}

void
parser_error_cb(void *user_data, const u8 *err_pos, const char *msg, va_list ap)
{
	Str *src = user_data;
	const u8 *line_start = src->str;
	size_t line = 0;
	const u8 *pos = src->str;
	for (; pos < err_pos; pos++) {
		if (*pos == '\n') {
			line_start = pos + 1;
			line++;
		}
	}
	size_t col = pos - line_start;
	const u8 *source_end = src->str + src->len;
	const u8 *line_end = pos;
	for (; line_end < source_end && *line_end != '\n'; line_end++) {}
	fprintf(stderr, "[%zu:%zu]: parser error: ", line + 1, col + 1);
	vfprintf(stderr, msg, ap);
	fprintf(stderr, "\n");
	fprintf(stderr, "  %.*s\n", (int) (line_end - line_start), line_start);
	fprintf(stderr, "  %*s\n", (int) (pos - line_start + 1), "^");
}

Ast *
parse(Arena *arena, GArena *scratch, Str source, void (*error_callback)(void *user_data, const u8 *err_pos, const char *msg, va_list ap), void *user_data)
{
	Parser parser = {
		.arena = arena,
		.scratch = scratch,
		.user_data = user_data,
		.error_callback = error_callback,
		.lexer = lex_create(source),
		.had_error = false,
		.panic_mode = false,
	};
	discard(&parser);

	Ast *ast = top(&parser);
	if (parser.had_error) {
		return NULL;
	}
	return ast;
}

Ast *
parse_src(Arena *arena, Str source)
{
	GArena scratch;
	garena_init(&scratch);
	Ast *ast = parse(arena, &scratch, source, parser_error_cb, &source);
	garena_destroy(&scratch);
	return ast;
}
