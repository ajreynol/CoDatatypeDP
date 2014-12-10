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

char tok_str[BIG_NUM];

void print_token(FILE *out, token tok)
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

int get_token(FILE *in, int *next_ch)
{
    for (;;) {
        switch (*next_ch) {
        case EOF:
            return Tok_End;
        case ';':
            while (*next_ch != EOF &&
                    *next_ch != '\n') {
                *next_ch = fgetc(in);
            }
            break;
        case '(':
            *next_ch = fgetc(in);
            return Tok_Left_Paren;
        case ')':
            *next_ch = fgetc(in);
            return Tok_Right_Paren;
        case ' ':
        case '\a':
        case '\n':
        case '\r':
        case '\t':
        case '\v':
            *next_ch = fgetc(in);
            break;
        default:
            {
                int i = 0;

                while (*next_ch != EOF &&
                        *next_ch != '(' &&
                        *next_ch != ')' &&
                        *next_ch != ';' &&
                        *next_ch != ' ' &&
                        *next_ch != '\a' &&
                        *next_ch != '\n' &&
                        *next_ch != '\r' &&
                        *next_ch != '\t' &&
                        *next_ch != '\v') {
                    tok_str[i++] = *next_ch;
                    *next_ch = fgetc(in);
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

void parse_co_datatypes(FILE *in, int *next_ch)
{
}

int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "Usage: undata FILE\n");
        return 1;
    }

    FILE *in = fopen(argv[1], "r");
    if (in == 0) {
        fprintf(stderr, "Cannot open \"%s\"\n", argv[1]);
        return 1;
    }

    char outNixName[BIG_NUM];
    char outDataName[BIG_NUM];
    char outCodataName[BIG_NUM];

    strcpy(outNixName, argv[1]);
    strcpy(outDataName, argv[1]);
    strcpy(outCodataName, argv[1]);

    strcat(outNixName, ".nix");
    strcat(outDataName, ".data");
    strcat(outCodataName, ".codata");

    FILE *outNix = fopen(outNixName, "w");
    FILE *outData = fopen(outDataName, "w");
    FILE *outCodata = fopen(outCodataName, "w");

    if (outNix == 0 || outData == 0 || outCodata == 0) {
        fprintf(stderr, "Cannot open output files");
        return 1;
    }

    int next_ch = fgetc(in);
    token tok = get_token(in, &next_ch);

    while (tok != Tok_End) {
        if (tok == Tok_Left_Paren) {
            tok = get_token(in, &next_ch);

            if (tok == Tok_Declare_Datatypes) {
                tok = get_token(in, &next_ch);
                parse_co_datatypes(in, &next_ch);
            } else if (tok == Tok_Declare_Codatatypes) {
                tok = get_token(in, &next_ch);
                parse_co_datatypes(in, &next_ch);
            } else {
                int depth = 1;

                print_token(outNix, Tok_Left_Paren);
                print_token(outData, Tok_Left_Paren);
                print_token(outCodata, Tok_Left_Paren);

                while (depth != 0 && tok != Tok_End) {
                    print_token(outNix, tok);
                    print_token(outData, tok);
                    print_token(outCodata, tok);

                    if (tok == Tok_Left_Paren) {
                        ++depth;
                    } else if (tok == Tok_Right_Paren) {
                        --depth;
                    }
                    tok = get_token(in, &next_ch);
                }

                fputc('\n', outNix);
                fputc('\n', outData);
                fputc('\n', outCodata);
            }
        } else {
            print_token(outNix, tok);
            print_token(outData, tok);
            print_token(outCodata, tok);

            tok = get_token(in, &next_ch);
        }
    }

    return 0;
}
