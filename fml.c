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
	#define TOK_ENUM(tok, nud, led, lbp, rbp) TK_##tok,
	TOKENS(TOK_ENUM)
	#undef TOK_ENUM
} TokenKind;

static const char *tok_repr[] = {
	#define TOK_STR(tok, nud, led, lbp, rbp) #tok,
	TOKENS(TOK_STR)
	#undef TOK_STR
};

typedef struct {
	TokenKind kind;
	const unsigned char *pos;
	const unsigned char *end;
} Token;

Lexer
lex_init(const unsigned char *buf, size_t size)
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
	ssize_t end_offset = 0;
	const unsigned char *start = lexer->pos;
	size_t length;
	while (lexer->pos != lexer->end) {
		unsigned char c = *lexer->pos;
		switch (state) {
		case LS_START: switch (c) {
			case '\n': case ' ': case '\t': start += 1; break;
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
			case '\n': state = LS_START; start = lexer->pos; break;
		}; break;
		case LS_BLOCK_COMMENT: switch (c) {
			case '*': state = LS_BLOCK_COMMENT_STAR; break;
		}; break;
		case LS_BLOCK_COMMENT_STAR: switch (c) {
			case '*': break;
			case '/': state = LS_START; start = lexer->pos; break;
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
	printf("TOK: %s %.*s\n", tok_repr[tok], (int) length, start);
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
	if (tok.kind != TK_IDENTIFIER) {
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
	ast->method_call.arguments[0] = expression_bp(parser, rbp);
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
	Ast *ast = make_ast(AST_INDEX_ACCESS);
	TRY(eat(parser, TK_LBRACKET));
	ast->index_access.object = left;
	TRY(ast->index_access.index = expression_bp(parser, rbp));
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
	(void) rbp;
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
} ValueKind;

typedef enum {
	GK_ARRAY,
	GK_OBJECT,
} GcValueKind;

typedef struct GcValue GcValue;

typedef struct Array Array;
typedef struct Object Object;

typedef struct {
	ValueKind kind;
	union {
		bool boolean;
		int32_t integer;
		GcValue *gcvalue;
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
} KeyValue;


struct Object {
	GcValue gcvalue;
	size_t length;
	KeyValue key_values[];
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

void
print_value(Value value)
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
		assert(false);
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

Value *
array_index(Value array_value, Value index)
{
	assert(value_is_array(array_value));
	Array *array = value_as_array(array_value);
	if (!value_is_integer(index)) {
		assert(false);
	}
	int32_t int_index = value_as_integer(index);
	if (int_index < 0) {
		assert(false);
	}
	return &array->values[int_index];
}

Value
value_get_index(Value target, Value index)
{
	switch (target.kind) {
	case VK_GCVALUE: {
		switch (target.gcvalue->kind) {
		case GK_ARRAY: {
			Value *lvalue = array_index(target, index);
			return *lvalue;
		}
		case GK_OBJECT: {
			assert(false);
		}
		}
		break;
	}
	default:
		assert(false);
	}
	assert(false);
}

Value
value_set_index(Value target, Value index, Value value)
{
	switch (target.kind) {
	case VK_GCVALUE: {
		switch (target.gcvalue->kind) {
		case GK_ARRAY: {
			Value *lvalue = array_index(target, index);
			return *lvalue = value;
		}
		case GK_OBJECT: {
			assert(false);
		}
		}
		break;
	}
	default:
		assert(false);
	}
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

Environment *
env_lookup(Environment *env, Identifier *name)
{
	if (!env) {
		return NULL;
	}
	Identifier *env_name = env->name;
	if (env_name->len == name->len && memcmp(env_name->name, name->name, name->len) == 0) {
		return env;
	}
	if (env->prev) {
		return env_lookup(env->prev, name);
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
		Value size = interpret(is, ast->array.size);
		assert(size.kind == VK_INTEGER && size.integer >= 0);
		Value array_value = make_array(size.integer);
		Array *array = value_as_array(array_value);
		for (size_t i = 0; i < (size_t) size.integer; i++) {
			array->values[i] = interpret(is, ast->array.initializer);
		}
		return array_value;
	}
	case AST_OBJECT: {
		break;
	}
	case AST_FUNCTION: {
		break;
	}

	case AST_VARIABLE: {
		Value value = interpret(is, ast->variable.value);
		is->env = make_env(is->env, ast->variable.name, value);
		return value;
	}

	case AST_VARIABLE_ACCESS: {
		Environment *env = env_lookup(is->env, ast->variable_access.name);
		assert(env);
		return env->value;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		Value value = interpret(is, ast->variable_assignment.value);
		Environment *env = env_lookup(is->env, ast->variable_assignment.name);
		assert(env);
		env->value = value;
		return value;
	}

	case AST_INDEX_ACCESS: {
		Value object = interpret(is, ast->index_access.object);
		Value index = interpret(is, ast->index_access.index);
		return value_get_index(object, index);
	}
	case AST_INDEX_ASSIGNMENT: {
		Value object = interpret(is, ast->index_assignment.object);
		Value index = interpret(is, ast->index_assignment.index);
		Value value = interpret(is, ast->index_assignment.value);
		return value_set_index(object, index, value);
	}

	case AST_FIELD_ACCESS: {
		assert(false);
	}
	case AST_FIELD_ASSIGNMENT: {
		assert(false);
	}

	case AST_FUNCTION_CALL: {
		assert(false);
	}
	case AST_METHOD_CALL: {
		assert(false);
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
		for (size_t i = 0; i < length; i++) {
			unsigned char c = format[i];
			if (in_escape) {
				in_escape = false;
				switch (c) {
				case  'n': putchar('\n'); break;
				case  't': putchar('\t'); break;
				case  'r': putchar('\r'); break;
				case  '~': putchar('~');  break;
				case  '"': putchar('"');  break;
				case '\\': putchar('\\'); break;
				default:
					fprintf(stderr, "invalid string escape sequence: %c", c);
					assert(false);
				}
			} else {
				switch (c) {
				case '\\': in_escape = true; break;
				case '~':
					assert(arg_index < ast->print.argument_cnt);
					Value value = interpret(is, ast->print.arguments[arg_index]);
					print_value(value);
					arg_index += 1;
					break;
				default:
					putchar(c);
				}
			}
		}
		fflush(stdout);
		return make_null();
	}
	case AST_BLOCK: {
		Environment *env = is->env;
		Value value = make_null();
		for (size_t i = 0; i < ast->block.expression_cnt; i++) {
			value = interpret(is, ast->block.expressions[i]);
		}
		is->env = env;
		return value;
	}
	}
	__builtin_unreachable();
}

int
main(int argc, char **argv) {
	if(argc != 2) {
		return 1;
	}
	FILE *f = fopen(argv[1], "rb");
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
