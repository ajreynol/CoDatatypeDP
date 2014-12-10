#include <stdio.h>
#include <string.h>

typedef enum {
    Tok_Left_Paren,
    Tok_Right_Paren,
    Tok_Declare_Datatypes,
    Tok_Declare_Codatatypes,
    Tok_Ident,
    Tok_End
} token;

const int BIG_NUM = 65536;

int next_ch;
token tok;
char tok_str[BIG_NUM];

void print_token(FILE *out)
{
    switch (tok) {
    case Tok_Left_Paren:
        fputc('(', out);
        break;
    case Tok_Right_Paren:
        fputc(')', out);
        break;
    case Tok_Declare_Datatypes:
        fprintf(out, "declare-datatypes ");
        break;
    case Tok_Declare_Codatatypes:
        fprintf(out, "declare-codatatypes ");
        break;
    case Tok_Ident:
        fprintf(out, "%s", tok_str);
        fputc(' ', out);
        break;
    case Tok_End:
        ;
    }
}

int get_token(FILE *in)
{
    for (;;) {
        switch (next_ch) {
        case EOF:
            return Tok_End;
        case ';':
            while (next_ch != EOF &&
                    next_ch != '\n') {
                next_ch = fgetc(in);
            }
            break;
        case '(':
            next_ch = fgetc(in);
            return Tok_Left_Paren;
        case ')':
            next_ch = fgetc(in);
            return Tok_Right_Paren;
        case ' ':
        case '\a':
        case '\n':
        case '\r':
        case '\t':
        case '\v':
            next_ch = fgetc(in);
            break;
        default:
            {
                int i = 0;

                while (next_ch != EOF &&
                        next_ch != '(' &&
                        next_ch != ')' &&
                        next_ch != ';' &&
                        next_ch != ' ' &&
                        next_ch != '\a' &&
                        next_ch != '\n' &&
                        next_ch != '\r' &&
                        next_ch != '\t' &&
                        next_ch != '\v') {
                    tok_str[i++] = next_ch;
                    next_ch = fgetc(in);
                }
                tok_str[i] = '\0';
                if (strcmp(tok_str, "declare-datatypes") == 0) {
                    return Tok_Declare_Datatypes;
                } else if (strcmp(tok_str, "declare-codatatypes") == 0) {
                    return Tok_Declare_Codatatypes;
                } else {
                    return Tok_Ident;
                }
            }
        }
    }
}

int eliminate_co_datatype(FILE *in)
{
    char typeName[BIG_NUM];

    strcpy(typeName, tok_str);

    if (tok != Tok_Left_Paren) {
        return 1;
    }

    tok = get_token(in);
    if (tok != Tok_Left_Paren) {
        return 1;
    }

    while (tok != Tok_Right_Paren) {
        tok = get_token(in);
    }
    tok = get_token(in);

    return 0;
}

int eliminate_co_datatypes(FILE *in)
{
    token tok = get_token(in);
    if (tok != Tok_Left_Paren) {
        return 1;
    }

    tok = get_token(in);
    if (tok != Tok_Right_Paren) {
        return 1;
    }

    tok = get_token(in);
    if (tok != Tok_Left_Paren) {
        return 1;
    }

    eliminate_co_datatype(in);

    while (tok != Tok_Right_Paren) {
        tok = get_token(in);
    }
    tok = get_token(in);
    return 0;
}

int generate_one_file(const char *inName, int keep_data, int keep_codata)
{
    FILE *in = fopen(inName, "r");
    if (in == 0) {
        fprintf(stderr, "Cannot open \"%s\"\n", inName);
        return 1;
    }

    char outName[BIG_NUM];

    strcpy(outName, inName);

    if (keep_data) {
        if (keep_codata) {
            strcat(outName, ".all");
        } else {
            strcat(outName, ".data");
        }
    } else {
        if (keep_codata) {
            strcat(outName, ".codata");
        } else {
            strcat(outName, ".nix");
        }
    }

    FILE *out = fopen(outName, "w");

    if (out == 0) {
        fprintf(stderr, "Cannot open output file \"%s\"\n", outName);
        return 1;
    }

    next_ch = fgetc(in);
    tok = get_token(in);

    while (tok != Tok_End) {
        if (tok == Tok_Left_Paren) {
            tok = get_token(in);

            if (tok == Tok_Declare_Datatypes && !keep_data) {
                eliminate_co_datatypes(in);
            } else if (tok == Tok_Declare_Codatatypes && !keep_codata) {
                eliminate_co_datatypes(in);
            } else {
                int depth = 1;

                fputc('(', out);

                while (depth != 0 && tok != Tok_End) {
                    print_token(out);

                    if (tok == Tok_Left_Paren) {
                        ++depth;
                    } else if (tok == Tok_Right_Paren) {
                        --depth;
                    }
                    tok = get_token(in);
                }

                fputc('\n', out);
            }
        } else {
            print_token(out);

            tok = get_token(in);
        }
    }

    return 0;
}

int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "Usage: undata FILE\n");
        return 1;
    }

    return generate_one_file(argv[1], 0, 0)
            && generate_one_file(argv[1], 0, 1)
            && generate_one_file(argv[1], 1, 0);
}
