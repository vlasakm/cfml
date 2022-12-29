#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <inttypes.h>

#define PROJECT_NAME "fml"

typedef struct {
	const unsigned char *pos;
	const unsigned char *end;
	const unsigned char *line_start;
	size_t line_num; // zero-based
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

#define TOKENS(_) \
	_(NUMBER,        primary,  NULL,      0,  0) \
	_(IDENTIFIER,    ident,    NULL,      0,  0) \
	_(STRING,        NULL,     NULL,      0,  0) \
                                                     \
	_(BAR,           NULL,     binop,     3,  4) \
	_(AMPERSANT,     NULL,     binop,     5,  6) \
	_(EQUAL_EQUAL,   NULL,     binop,     7,  8) \
	_(BANG_EQUAL,    NULL,     binop,     7,  8) \
	_(GREATER,       NULL,     binop,     7,  8) \
	_(LESS,          NULL,     binop,     7,  8) \
	_(GREATER_EQUAL, NULL,     binop,     7,  8) \
	_(LESS_EQUAL,    NULL,     binop,     7,  8) \
	_(PLUS,          NULL,     binop,     9, 10) \
	_(MINUS,         NULL,     binop,     9, 10) \
	_(ASTERISK,      NULL,     binop,    11, 12) \
	_(SLASH,         NULL,     binop,    11, 12) \
	_(PERCENT,       NULL,     binop,    11, 12) \
	                                             \
	_(SEMICOLON,     NULL,     NULL,      0,  0) \
	_(LPAREN,        paren,    call,     13, 14) \
	_(RPAREN,        NULL,     NULL,      0,  0) \
	_(EQUAL,         NULL,     NULL,      0,  0) \
	_(LARROW,        NULL,     assign,    2,  1) \
	_(RARROW,        NULL,     NULL,      0,  0) \
	_(DOT,           NULL,     field,    13, 14) \
	_(LBRACKET,      NULL,     indexing, 13, 14) \
	_(RBRACKET,      NULL,     NULL,      0,  0) \
	_(COMMA,         NULL,     NULL,      0,  0) \
	                                             \
	_(BEGIN,         block,    NULL,      0,  0) \
	_(END,           NULL,     NULL,      0,  0) \
	_(IF,            cond,     NULL,      0,  0) \
	_(THEN,          NULL,     NULL,      0,  0) \
	_(ELSE,          NULL,     NULL,      0,  0) \
	_(LET,           let,      NULL,      0,  0) \
	_(NULL,          primary,  NULL,      0,  0) \
	_(PRINT,         print,    NULL,      0,  0) \
	_(OBJECT,        object,   NULL,      0,  0) \
	_(EXTENDS,       NULL,     NULL,      0,  0) \
	_(WHILE,         loop,     NULL,      0,  0) \
	_(DO,            NULL,     NULL,      0,  0) \
	_(FUNCTION,      function, NULL,      0,  0) \
	_(ARRAY,         array,    NULL,      0,  0) \
	_(TRUE,          primary,  NULL,      0,  0) \
	_(FALSE,         primary,  NULL,      0,  0) \
	                                             \
	_(EOF,           NULL,     NULL,      0,  0) \
	_(ERROR,         NULL,     NULL,      0,  0)


typedef enum {
	#define TOK_ENUM(tok, ...) TK_##tok,
	TOKENS(TOK_ENUM)
	#undef TOK_ENUM
	TK_OP_MIN = TK_BAR,
	TK_OP_MAX = TK_PERCENT,
} TokenKind;

static const char *tok_repr[] = {
	#define TOK_STR(tok, ...) #tok,
	TOKENS(TOK_STR)
	#undef TOK_STR
};

typedef struct {
	TokenKind kind;
	const unsigned char *pos;
	const unsigned char *end;
	size_t line;
	size_t col;
} Token;

Lexer
lex_init(const unsigned char *buf, size_t size)
{
	return (Lexer) {
		.pos = buf,
		.end = buf + size,
		.line_start = buf,
		.line_num = 0,
	};
}

#define ALPHA '_': case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm': case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'v': case 'u': case 'w': case 'x': case 'y': case 'z': case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M': case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'V': case 'U': case 'W': case 'X': case 'Y': case 'Z'

#define DIGIT '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9'

void
lex_next(Lexer *lexer, Token *token)
{
	LexState state = LS_START;
	TokenKind tok = TK_ERROR;
	ssize_t end_offset = 0;
	const unsigned char *start = lexer->pos;
	size_t length;
	while (lexer->pos != lexer->end) {
		unsigned char c = *lexer->pos;
		switch (state) {
		case LS_START: switch (c) {
			case '\n': lexer->line_start = start += 1; lexer->line_num += 1; break;
			case ' ': case '\t': start += 1; break;
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
			case '\n':
				state = LS_START;
				lexer->line_start = start = lexer->pos + 1;
				lexer->line_num += 1;
				break;
		}; break;
		case LS_BLOCK_COMMENT: switch (c) {
			// TODO: handle \n
			case '*': state = LS_BLOCK_COMMENT_STAR; break;
		}; break;
		case LS_BLOCK_COMMENT_STAR: switch (c) {
			// TODO: handle \n
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
	case LS_IDENTIFIER: tok = TK_IDENTIFIER; goto done;
	case LS_NUMBER: tok = TK_NUMBER; goto done;
	case LS_STRING: case LS_STRING_ESC: case LS_BLOCK_COMMENT: case LS_BLOCK_COMMENT_STAR: goto err;
	case LS_SLASH: case LS_MINUS: case LS_EQUAL: case LS_GREATER: case LS_LESS: tok = TK_SLASH; goto done;
	case LS_EXCLAM: goto err;
	}

done:
	lexer->pos += 1;
prev_done:
err:
	length = lexer->pos - start + end_offset;
	size_t line = lexer->line_num + 1;
	size_t col = start - lexer->line_start + 1;
	fprintf(stderr, "TOK[%2zu:%2zu]: %s %.*s\n", line, col, tok_repr[tok], (int) length, start);
	static struct {
		const char *str;
		TokenKind tok;
	} keywords[] = {
		{ "begin", TK_BEGIN },
		{ "end", TK_END },
		{ "if", TK_IF },
		{ "then", TK_THEN },
		{ "else", TK_ELSE },
		{ "let", TK_LET },
		{ "null", TK_NULL },
		{ "print", TK_PRINT },
		{ "object", TK_OBJECT },
		{ "extends", TK_EXTENDS },
		{ "while", TK_WHILE },
		{ "do", TK_DO },
		{ "function", TK_FUNCTION },
		{ "array", TK_ARRAY },
		{ "true", TK_TRUE },
		{ "false", TK_FALSE },
	};
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
	token->line = line;
	token->col = col;
}

typedef enum {
	AST_NULL,
	AST_BOOLEAN,
	AST_INTEGER,

	AST_ARRAY,
	AST_OBJECT,
	AST_FUNCTION,

	AST_VARIABLE,

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
} AstKind;

typedef struct Ast Ast;

typedef struct {
	const unsigned char *name;
	size_t len;
} Identifier;

static Identifier THIS = { .name = (const unsigned char*) "this", .len = 4 };
static Identifier SET  = { .name = (const unsigned char*)  "set", .len = 3 };
static Identifier GET  = { .name = (const unsigned char*)  "get", .len = 3 };


struct Ast {
	AstKind kind;
	union {
		struct { bool value; } boolean;
		struct { int32_t value; } integer;

		struct { Ast *size; Ast *initializer; } array;
		struct { Ast *extends; Ast **members; size_t member_cnt; } object;
		struct { Identifier *name; Identifier **parameters; size_t parameter_cnt; Ast *body; } function;

		struct { Identifier *name; Ast *value; } variable;

		struct { Identifier *name; } variable_access;
		struct { Identifier *name; Ast *value; } variable_assignment;

		struct { Ast *object; Ast *index; } index_access;
		struct { Ast *object; Ast *index; Ast *value; } index_assignment;

		struct { Ast *object; Identifier *field; } field_access;
		struct { Ast *object; Identifier *field; Ast *value; } field_assignment;

		struct { Identifier *name; Ast **arguments; size_t argument_cnt; } function_call;
		struct { Ast* object; Identifier *name; Ast **arguments; size_t argument_cnt; } method_call;

		struct { Ast *condition; Ast *consequent; Ast *alternative; } conditional;
		struct { Ast *condition; Ast *body; } loop;
		struct { Identifier *format; Ast **arguments; size_t argument_cnt; } print;
		struct { Ast **expressions; size_t expression_cnt; } block;
	};
};

typedef struct {
	Lexer lexer;
	Token lookahead;
} Parser;

void
parser_init(Parser *parser, const unsigned char *buf, size_t buf_len)
{
	parser->lexer = lex_init(buf, buf_len);
	lex_next(&parser->lexer, &parser->lookahead);
}

static TokenKind
peek(const Parser *parser)
{
	return parser->lookahead.kind;
}

static Token
discard(Parser *parser)
{
	Token prev = parser->lookahead;
	lex_next(&parser->lexer, &parser->lookahead);
	return prev;
}

static bool
eat(Parser *parser, TokenKind kind)
{
	Token tok = discard(parser);
	if (tok.kind != kind) {
		fprintf(stderr, "expected %s, found %s\n", tok_repr[kind], tok_repr[tok.kind]);
		return false;
	}
	return true;
}

static Identifier *
eat_identifier(Parser *parser)
{
	Token tok = discard(parser);
	if (tok.kind != TK_IDENTIFIER && (tok.kind < TK_OP_MIN || tok.kind > TK_OP_MAX)) {
		fprintf(stderr, "expected an identifier, found %s\n", tok_repr[tok.kind]);
		return NULL;
	}
	Identifier *identifier = calloc(1, sizeof(*identifier));
	identifier->name = tok.pos;
	identifier->len = tok.end - tok.pos;
	return identifier;
}

static Identifier *
eat_string(Parser *parser)
{
	Token tok = discard(parser);
	if (tok.kind != TK_STRING) {
		printf("expected %s, found %s\n", tok_repr[TK_STRING], tok_repr[tok.kind]);
		return NULL;
	}
	Identifier *identifier = calloc(1, sizeof(*identifier));
	identifier->name = tok.pos;
	identifier->len = tok.end - tok.pos;
	return identifier;
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

static Ast *
make_ast(AstKind kind)
{
	Ast *ast = calloc(1, sizeof(*ast));
	ast->kind = kind;
	return ast;
}

static Ast *
create_null(Parser *parser)
{
	(void) parser;
	return make_ast(AST_NULL);
}

#define TRY(arg) do { if (!(arg)) { return NULL; } } while(0)

static Ast *expression_bp(Parser *parser, int bp);

static Ast *
expression(Parser *parser)
{
	return expression_bp(parser, 0);
}


static bool
separated_list(Parser *parser, void*(*one)(Parser *), void ***list, size_t *n, TokenKind separator, TokenKind terminator)
{
	size_t capacity = 0;
	*list = NULL;
	*n = 0;

	while (!try_eat(parser, terminator)) {
		if (capacity == 0 || *n == capacity) {
			capacity = capacity ? capacity * 2 : 4;
			*list = realloc(*list, capacity * sizeof((*list)[0]));
		}

		void *expr;
		TRY(expr = one(parser));
		(*list)[*n] = expr;
		*n += 1;

		if (!try_eat(parser, separator)) {
			eat(parser, terminator);
			return true;
		}
	}

	return true;
}

static Ast *
primary(Parser *parser)
{
	Ast *ast = make_ast(AST_NULL);
	Token token = discard(parser);
	switch (token.kind) {
	case TK_NUMBER:
		ast->kind = AST_INTEGER;
		const unsigned char *pos = token.pos;
		bool negative = 0;
		while (*pos == '-') {
			negative = !negative;
			pos += 1;
		}
		int32_t value = 0;
		for (; pos < token.end; pos++) {
			value = value * 10 + *pos - '0';
		}
		ast->integer.value = negative ? -value : value;
		break;
	case TK_IDENTIFIER:
		ast->kind = AST_VARIABLE_ACCESS;
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
		__builtin_unreachable();
	}
	return ast;
}

static Ast *
ident(Parser *parser)
{
	Ast *ast = make_ast(AST_VARIABLE_ACCESS);
	TRY(ast->variable_access.name = eat_identifier(parser));
	return ast;
}

static Ast *
block(Parser *parser)
{
	Ast *ast = make_ast(AST_BLOCK);
	TRY(eat(parser, TK_BEGIN));
	TRY(separated_list(parser, (void*(*)(Parser*))expression, (void***)&ast->block.expressions, &ast->block.expression_cnt, TK_SEMICOLON, TK_END));
	return ast;
}

static Ast *
let(Parser *parser)
{
	Ast *ast = make_ast(AST_VARIABLE);
	TRY(eat(parser, TK_LET));
	TRY(ast->variable.name = eat_identifier(parser));
	TRY(eat(parser, TK_EQUAL));
	TRY(ast->variable.value = expression(parser));
	return ast;
}

static Ast *
array(Parser *parser)
{
	Ast *ast = make_ast(AST_ARRAY);
	TRY(eat(parser, TK_ARRAY));
	TRY(eat(parser, TK_LPAREN));
	TRY(ast->array.size = expression(parser));
	TRY(eat(parser, TK_COMMA));
	TRY(ast->array.initializer = expression(parser));
	TRY(eat(parser, TK_RPAREN));
	return ast;
}

static Ast *
object(Parser *parser)
{
	Ast *ast = make_ast(AST_OBJECT);
	TRY(eat(parser, TK_OBJECT));
	if (try_eat(parser, TK_EXTENDS)) {
		TRY(ast->object.extends = expression(parser));
	} else {
		ast->object.extends = create_null(parser);
	}
	TRY(eat(parser, TK_BEGIN));
	TRY(separated_list(parser, (void*(*)(Parser*))expression, (void***)&ast->object.members, &ast->object.member_cnt, TK_SEMICOLON, TK_END));
	return ast;
}

static Ast *
cond(Parser *parser)
{
	Ast *ast = make_ast(AST_IF);
	TRY(eat(parser, TK_IF));
	TRY(ast->conditional.condition = expression(parser));
	TRY(eat(parser, TK_THEN));
	TRY(ast->conditional.consequent = expression(parser));
	if (try_eat(parser, TK_ELSE)) {
		TRY(ast->conditional.alternative = expression(parser));
	} else {
		ast->conditional.alternative = create_null(parser);
	}
	return ast;
}

static Ast *
loop(Parser *parser)
{
	Ast *ast = make_ast(AST_WHILE);
	TRY(eat(parser, TK_WHILE));
	TRY(ast->loop.condition = expression(parser));
	TRY(eat(parser, TK_DO));
	TRY(ast->loop.body = expression(parser));
	return ast;
}

static Ast *
print(Parser *parser)
{
	Ast *ast = make_ast(AST_PRINT);
	TRY(eat(parser, TK_PRINT));
	TRY(eat(parser, TK_LPAREN));
	TRY(ast->print.format = eat_string(parser));
	if (try_eat(parser, TK_COMMA)) {
		separated_list(parser, (void*(*)(Parser*))expression, (void***)&ast->print.arguments, &ast->print.argument_cnt, TK_COMMA, TK_RPAREN);
	} else {
		TRY(eat(parser, TK_RPAREN));
	}
	return ast;
}

static Ast *
paren(Parser *parser)
{
	Ast *ast;
	TRY(eat(parser, TK_LPAREN));
	TRY(ast = expression(parser));
	TRY(eat(parser, TK_RPAREN));
	return ast;
}


static Ast *
function(Parser *parser)
{
	Ast *ast = make_ast(AST_FUNCTION);
	TRY(eat(parser, TK_FUNCTION));
	TRY(ast->function.name = eat_identifier(parser));
	TRY(eat(parser, TK_LPAREN));
	TRY(separated_list(parser, (void*(*)(Parser*))eat_identifier, (void***)&ast->function.parameters, &ast->function.parameter_cnt, TK_COMMA, TK_RPAREN));
	TRY(eat(parser, TK_RARROW));
	TRY(ast->function.body = expression(parser));
	return ast;
}

static Ast *
binop(Parser *parser, Ast *left, int rbp)
{
	Ast *ast = make_ast(AST_METHOD_CALL);
	Token token = discard(parser);
	ast->method_call.object = left;
	ast->method_call.name = calloc(1, sizeof(Identifier));
	ast->method_call.name->name = token.pos;
	ast->method_call.name->len = token.end - token.pos;
	ast->method_call.arguments = malloc(sizeof(*ast->method_call.arguments));
	// TODO: leaked malloc
	TRY(ast->method_call.arguments[0] = expression_bp(parser, rbp));
	//TRY(ast->method_call.arguments = expression_bp(parser, rbp));
	ast->method_call.argument_cnt = 1;
	return ast;
}

static Ast *
call(Parser *parser, Ast *left, int rbp)
{
	(void) rbp;
	TRY(eat(parser, TK_LPAREN));
	switch (left->kind) {
	case AST_VARIABLE_ACCESS: {
		Identifier *name = left->variable_access.name;
		Ast *ast = left;
		ast->kind = AST_FUNCTION_CALL;
		ast->function_call.name = name;
		TRY(separated_list(parser, (void*(*)(Parser*))expression, (void***)&ast->function_call.arguments, &ast->function_call.argument_cnt, TK_COMMA, TK_RPAREN));
		return ast;
	}
	case AST_FIELD_ACCESS: {
		Ast *object = left->field_access.object;
		Identifier *name = left->field_access.field;
		Ast *ast = left;
		ast->kind = AST_METHOD_CALL;
		ast->method_call.object = object;
		ast->method_call.name = name;
		TRY(separated_list(parser, (void*(*)(Parser*))expression, (void***)&ast->method_call.arguments, &ast->method_call.argument_cnt, TK_COMMA, TK_RPAREN));
		return ast;
	}
	default:
		fprintf(stderr, "invalid call target, expected variable or field\n");
		return NULL;
	}
}

static Ast *
indexing(Parser *parser, Ast *left, int rbp)
{
	// rbp not used - delimited by TK_RBRACKET, not by precedence
	(void) rbp;
	Ast *ast = make_ast(AST_INDEX_ACCESS);
	TRY(eat(parser, TK_LBRACKET));
	ast->index_access.object = left;
	TRY(ast->index_access.index = expression(parser));
	TRY(eat(parser, TK_RBRACKET));
	return ast;
}

static Ast *
field(Parser *parser, Ast *left, int rbp)
{
	(void) rbp;
	Ast *ast = make_ast(AST_FIELD_ACCESS);
	TRY(eat(parser, TK_DOT));
	ast->field_access.object = left;
	TRY(ast->field_access.field = eat_identifier(parser));
	return ast;
}

static Ast *
assign(Parser *parser, Ast *left, int rbp)
{
	TRY(eat(parser, TK_LARROW));
	switch (left->kind) {
	case AST_VARIABLE_ACCESS: {
		Identifier *name = left->variable_access.name;
		Ast *ast = left;
		ast->kind = AST_VARIABLE_ASSIGNMENT;
		ast->variable_assignment.name = name;
		TRY(ast->variable_assignment.value = expression_bp(parser, rbp));
		return ast;
	}
	case AST_FIELD_ACCESS: {
		Ast *object = left->field_access.object;
		Identifier *field = left->field_access.field;
		Ast *ast = left;
		ast->kind = AST_FIELD_ASSIGNMENT;
		ast->field_assignment.object = object;
		ast->field_assignment.field = field;
		TRY(ast->field_assignment.value = expression_bp(parser, rbp));
		return ast;
	}
	case AST_INDEX_ACCESS: {
		Ast *object = left->index_access.object;
		Ast *index = left->index_access.index;
		Ast *ast = left;
		ast->kind = AST_INDEX_ASSIGNMENT;
		ast->index_assignment.object = object;
		ast->index_assignment.index = index;
		TRY(ast->index_assignment.value = expression_bp(parser, rbp));
		return ast;
	}
	default:
		fprintf(stderr, "invalid call target, expected variable or field\n");
		return NULL;
	}
}

typedef struct {
	Ast *(*nud)(Parser *);
} NullInfo;

NullInfo null_info[] = {
	#define TOK_NULL(tok, nud, led, lbp, rbp) { nud },
	TOKENS(TOK_NULL)
	#undef TOK_STR
};

typedef struct {
	Ast *(*led)(Parser *, Ast *left, int rbp);
	int lbp;
	int rbp;
} LeftInfo;

LeftInfo left_info[] = {
	#define TOK_LEFT(tok, nud, led, lbp, rbp) { led, lbp, rbp },
	TOKENS(TOK_LEFT)
	#undef TOK_STR
};

static Ast *
expression_bp(Parser *parser, int bp)
{
	TokenKind token = peek(parser);
	NullInfo ni = null_info[token];
	Ast *left;

	if (!ni.nud) {
		fprintf(stderr, "invalid start of expression: %s\n", tok_repr[token]);
		return NULL;
	}
	TRY(left = ni.nud(parser));

	for (;;) {
		token = peek(parser);
		LeftInfo li = left_info[token];
		if (!li.led || li.lbp < bp) {
			break;
		}
		TRY(left = li.led(parser, left, li.rbp));
	}

	return left;
}

Ast *
parse(unsigned char *buf, size_t buf_len)
{
	Parser parser;
	parser_init(&parser, buf, buf_len);
	Ast *ast = make_ast(AST_BLOCK);
	// TODO: distinguish at the parser level an empty program (evaluates to null)
	TRY(separated_list(&parser, (void*(*)(Parser*))expression, (void***)&ast->block.expressions, &ast->block.expression_cnt, TK_SEMICOLON, TK_EOF));
	return ast;
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

typedef struct Array Array;
typedef struct Object Object;
typedef struct Function Function;

typedef struct {
	ValueKind kind;
	union {
		bool boolean;
		int32_t integer;
		GcValue *gcvalue;
		Ast *function;
	};
} Value;

struct GcValue {
	GcValueKind kind;
};

struct Array {
	GcValue gcvalue;
	size_t length;
	Value values[];
};

typedef struct {
	Identifier *name;
	Value value;
} Field;


struct Object {
	GcValue gcvalue;
	Value parent;
	size_t field_cnt;
	Field fields[];
};

struct Function {
	GcValue gcvalue;
	Ast *ast;
};

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
make_integer(int32_t value)
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
make_object(Value parent, size_t field_cnt)
{
	Object *object = malloc(sizeof(*object) + field_cnt * sizeof(object->fields[0]));
	object->gcvalue = (GcValue) { .kind = GK_OBJECT };
	object->parent = parent;
	object->field_cnt = field_cnt;

	return (Value) { .kind = VK_GCVALUE, .gcvalue = &object->gcvalue };
}

Value
make_function(Ast *ast)
{
	return (Value) { .kind = VK_FUNCTION, .function = ast };
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

int32_t
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

Ast *
value_as_function(Value value)
{
	return value.function;
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
			for (size_t i = 0; i < object->field_cnt; i++) {
				if (value_is_function(object->fields[i].value)) {
					continue;
				}
				if (prev) {
					prev = false;
					printf(", ");
				}
				Identifier *name = object->fields[i].name;
				printf("%.*s=", (int)name->len, name->name);
				value_print(object->fields[i].value);
				prev = true;
			}
			printf(")");
			break;
		}
		break;

	case VK_FUNCTION:
		printf("function '%s'", value_as_function(value)->function.name->name);
	}
}

bool
value_to_bool(Value value)
{
	if (value.kind == VK_NULL || (value.kind == VK_BOOLEAN && value.boolean == false)) {
		return false;
	}
	return true;
}

typedef struct Environment Environment;

struct Environment {
	Environment *prev;
	Identifier *name;
	Value value;
};

size_t
value_as_index(Value value)
{
	if (!value_is_integer(value)) {
		assert(false);
	}
	int32_t int_index = value_as_integer(value);
	if (int_index < 0) {
		assert(false);
	}
	return (size_t) int_index;
}

Value *
array_index(Value array_value, Value index_value)
{
	assert(value_is_array(array_value));
	Array *array = value_as_array(array_value);
	size_t index = value_as_index(index_value);
	return &array->values[index];
}

Value *
value_field(Value value, Identifier *name)
{
	if (!value_is_object(value)) {
		return NULL;
	}
	Object *object = value_as_object(value);
	for (size_t i = 0; i < object->field_cnt; i++) {
		Identifier *field_name = object->fields[i].name;
		if (value_is_function(object->fields[i].value)) {
			continue;
		}
		if (field_name->len == name->len && memcmp(field_name->name, name->name, name->len) == 0) {
			return &object->fields[i].value;
		}
	}
	return value_field(object->parent, name);
}

Ast *
value_method(Value value, Value *receiver, Identifier *name)
{
	if (!value_is_object(value)) {
		// We did not find the method, but we have the eldest parent
		// object on which we can call a primitive method (hopefully)
		*receiver = value;
		return NULL;
	}
	Object *object = value_as_object(value);
	for (size_t i = 0; i < object->field_cnt; i++) {
		Identifier *field_name = object->fields[i].name;
		if (!value_is_function(object->fields[i].value)) {
			continue;
		}
		if (field_name->len == name->len && memcmp(field_name->name, name->name, name->len) == 0) {
			// We found the method, set the receiver Object to the
			// method's owner
			receiver->gcvalue = &object->gcvalue;
			return value_as_function(object->fields[i].value);
		}
	}
	return value_method(object->parent, receiver, name);
}

Value
value_call_primitive_method(Value target, Identifier *method, Value *arguments, size_t argument_cnt)
{
	const unsigned char *method_name = method->name;
	size_t method_name_len = method->len;
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
				Value *lvalue = array_index(target, arguments[0]);
				return *lvalue;
			}
			METHOD("set") {
				if (argument_cnt != 2) goto err;
				Value *lvalue = array_index(target, arguments[0]);
				return *lvalue = arguments[1];
			}
		case GK_OBJECT:
			break;
		}
	case VK_FUNCTION:
		break;
	}
err:
	// invalid method M called on object X
	assert(false);
}

Environment *
make_env(Environment *prev, Identifier *name, Value value)
{
	Environment *env = malloc(sizeof(*env));
	env->prev = prev;
	env->name = name;
	env->value = value;
	return env;
}

Value *
env_lookup_raw(Environment *env, Identifier *name)
{
	if (!env) {
		return NULL;
	}
	Identifier *env_name = env->name;
	if (env_name->len == name->len && memcmp(env_name->name, name->name, name->len) == 0) {
		return &env->value;
	}
	return env_lookup_raw(env->prev, name);
}

Value *
env_lookup(Environment *env, Identifier *name)
{
	Value *lvalue = env_lookup_raw(env, name);
	if (lvalue && value_is_function(*lvalue)) {
		return NULL;
	}
	return lvalue;
}

Ast *
env_lookup_func(Environment *env, Identifier *name)
{
	Value *lvalue = env_lookup_raw(env, name);
	if (lvalue && value_is_function(*lvalue)) {
		return value_as_function(*lvalue);
	}
	return NULL;
}

typedef struct {
	Environment *env;
} InterpreterState;

Value
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
		size_t size = value_as_index(size_value);
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
		Value object_value = make_object(parent, ast->object.member_cnt);
		Object *object = value_as_object(object_value);
		for (size_t i = 0; i < ast->object.member_cnt; i++) {
			Ast *ast_member = ast->object.members[i];
			switch (ast_member->kind) {
			case AST_VARIABLE:
				object->fields[i].name = ast_member->variable.name;
				object->fields[i].value = interpret(is, ast_member->variable.value);
				break;
			case AST_FUNCTION:
				object->fields[i].name = ast_member->function.name;
				object->fields[i].value = make_function(ast_member);
				break;
			default:
				assert(false);
			}
		}
		return object_value;
	}
	case AST_FUNCTION: {
		Value function = make_function(ast);
		is->env = make_env(is->env, ast->function.name, function);
		return make_null();
	}

	case AST_VARIABLE: {
		Value value = interpret(is, ast->variable.value);
		is->env = make_env(is->env, ast->variable.name, value);
		return value;
	}

	case AST_VARIABLE_ACCESS: {
		Value *lvalue = env_lookup(is->env, ast->variable_access.name);
		assert(lvalue);
		return *lvalue;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		Value value = interpret(is, ast->variable_assignment.value);
		Value *lvalue = env_lookup(is->env, ast->variable_assignment.name);
		assert(lvalue);
		return *lvalue = value;
	}

	case AST_INDEX_ACCESS: {
		Value object = interpret(is, ast->index_access.object);
		Value index = interpret(is, ast->index_access.index);
		return value_call_primitive_method(object, &GET, &index, 1);
	}
	case AST_INDEX_ASSIGNMENT: {
		Value object = interpret(is, ast->index_assignment.object);
		Value arguments[2];
		arguments[0] = interpret(is, ast->index_assignment.index);
		arguments[1] = interpret(is, ast->index_assignment.value);
		return value_call_primitive_method(object, &SET, &arguments[0], 2);
	}

	case AST_FIELD_ACCESS: {
		Value object = interpret(is, ast->field_access.object);
		Value *lvalue = value_field(object, ast->field_access.field);
		return *lvalue;
	}
	case AST_FIELD_ASSIGNMENT: {
		Value object = interpret(is, ast->field_assignment.object);
		Value value = interpret(is, ast->field_assignment.value);
		Value *lvalue = value_field(object, ast->field_access.field);
		return *lvalue = value;
	}

	case AST_FUNCTION_CALL: {
		Ast *function = env_lookup_func(is->env, ast->function_call.name);
		assert(function);
		assert(function->function.parameter_cnt == ast->function_call.argument_cnt);
		Environment *saved_env = is->env;
		for (size_t i = 0; i < ast->function_call.argument_cnt; i++) {
			Value value = interpret(is, ast->function_call.arguments[i]);
			is->env = make_env(is->env, function->function.parameters[i], value);
		}
		Value return_value = interpret(is, function->function.body);
		is->env = saved_env;
		return return_value;
	}
	case AST_METHOD_CALL: {
		Value object = interpret(is, ast->method_call.object);
		Ast *function = value_method(object, &object, ast->method_call.name);
		if (function) {
			Environment *saved_env = is->env;
			Environment *new_env = is->env;
			for (size_t i = 0; i < ast->method_call.argument_cnt; i++) {
				Value value = interpret(is, ast->method_call.arguments[i]);
				new_env = make_env(new_env, function->function.parameters[i], value);
			}
			is->env = make_env(new_env, &THIS, object);
			Value return_value = interpret(is, function->function.body);
			is->env = saved_env;
			return return_value;
		} else {
			// abuse the fact that there may be at most two args
			Value arguments[2];
			assert(ast->method_call.argument_cnt <= 2);
			for (size_t i = 0; i < ast->method_call.argument_cnt; i++) {
				arguments[i] = interpret(is, ast->method_call.arguments[i]);
			}
			return value_call_primitive_method(object, ast->method_call.name, &arguments[0], ast->method_call.argument_cnt);
		}
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
		Value value = make_null();
		while (value_to_bool(interpret(is, ast->loop.condition))) {
			value = interpret(is, ast->loop.body);
		}
		return value;
	}
	case AST_PRINT: {
		const unsigned char *format = ast->print.format->name;
		size_t length = ast->print.format->len;
		bool in_escape = false;
		size_t arg_index = 0;
		Value *arguments = calloc(ast->print.argument_cnt, sizeof(*arguments));
		for (size_t i = 0; i < ast->print.argument_cnt; i++) {
			arguments[i] = interpret(is, ast->print.arguments[i]);
		}
		for (size_t i = 0; i < length; i++) {
			unsigned char c = format[i];
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
					fprintf(stderr, "invalid string escape sequence: %c", c);
					assert(false);
				}
				putchar(c);
			} else {
				switch (c) {
				case '\\': in_escape = true; break;
				case '~':
					assert(arg_index < ast->print.argument_cnt);
					value_print(arguments[arg_index]);
					arg_index += 1;
					break;
				default:
					putchar(c);
				}
			}
		}
		free(arguments);
		fflush(stdout);
		return make_null();
	}
	case AST_BLOCK: {
		Environment *saved_env = is->env;
		Value value = make_null();
		for (size_t i = 0; i < ast->block.expression_cnt; i++) {
			value = interpret(is, ast->block.expressions[i]);
		}
		is->env = saved_env;
		return value;
	}
	}
	__builtin_unreachable();
}

int
main(int argc, char **argv) {
	if(argc != 3 || strcmp(argv[1], "run") != 0) {
		return 1;
	}
	FILE *f = fopen(argv[2], "rb");
	fseek(f, 0, SEEK_END);
	long fsize = ftell(f);
	fseek(f, 0, SEEK_SET);
	unsigned char *buf = malloc(fsize);
	fread(buf, fsize, 1, f);
	fclose(f);

	//Lexer lexer = lex_init(buf, fsize);
	//for (;;) {
	//	Token tok;
	//	lex_next(&lexer, &tok);
	//	if (/*tok.kind == TK_ERROR ||*/ tok.kind == TK_EOF)
	//		break;
	//}

	Ast *ast = parse(buf, fsize);
	assert(ast);

	InterpreterState is = {
		.env = NULL,
	};
	interpret(&is, ast);

	free(buf);
	return 0;
}
