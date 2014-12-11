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

const int Big_Num = 1024;

int next_ch;
token tok;
char tok_str[Big_Num];

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

int eliminate_constructor_argument(const char *sort_name,
        const char *ctor_name, char (*funs)[Big_Num], int *num_funs,
        char (*args)[Big_Num], int *num_args, FILE *in, FILE *out)
{
    char sel_name[Big_Num];
    char arg_sort[Big_Num];

    if (tok != Tok_Left_Paren) {
        return 1;
    }

    tok = get_token(in);
    strcpy(sel_name, tok_str);

    tok = get_token(in);
    strcpy(arg_sort, tok_str);
    fprintf(stderr, "%d %s %s %s %s\n", (int)tok, sort_name, ctor_name,
            sel_name, arg_sort);

    strcpy(*args++, arg_sort);

    char sel_sig[Big_Num];
    sprintf(sel_sig, "%s (%s)%s", sel_name, sort_name, arg_sort);
    strcpy(funs[(*num_funs)++], sel_sig);

    tok = get_token(in);
    if (tok != Tok_Right_Paren) {
        return 1;
    }

    tok = get_token(in);
    return 0;
}

int eliminate_constructor(const char *sort_name, char (*funs)[Big_Num],
        int *num_funs, FILE *in, FILE *out)
{
    char ctor_name[Big_Num];
    char args[Big_Num][Big_Num];
    int num_args = 0;

    if (tok != Tok_Left_Paren) {
        return 1;
    }

    tok = get_token(in);
    strcpy(ctor_name, tok_str);
    fprintf(stderr, "%d %s %s\n", (int)tok, sort_name, tok_str);

    char arg_sorts[Big_Num];
    for (int i = 0; i < num_args; i++) {
        strcat(arg_sorts, args[i]);
        if (i > 0) {
            strcat(arg_sorts, " ");
        }
    }

    char ctor_sig[Big_Num];
    sprintf(ctor_sig, "%s (%s)%s", ctor_name, arg_sorts, sort_name);
    strcpy(funs[(*num_funs)++], ctor_sig);

    tok = get_token(in);

    while (tok == Tok_Left_Paren) {
        eliminate_constructor_argument(sort_name, ctor_name, funs, num_funs,
            args, &num_args, in, out);
    }

    if (tok != Tok_Right_Paren) {
        return 1;
    }

    tok = get_token(in);
    return 0;
}

int eliminate_co_datatype(char (*funs)[Big_Num], FILE *in, FILE *out)
{
    char sort_name[Big_Num];
    int num_funs = 0;

    if (tok != Tok_Left_Paren) {
        return 1;
    }

    tok = get_token(in);

    strcpy(sort_name, tok_str);
    fprintf(stderr, "%d %s\n", (int)tok, sort_name);
    tok = get_token(in);

    fprintf(out, "(declare-sort %s 0)\n", sort_name);

    while (tok == Tok_Left_Paren) {
        eliminate_constructor(sort_name, funs, &num_funs, in, out);
    }

    if (tok != Tok_Right_Paren) {
        return 1;
    }

    tok = get_token(in);
    return 0;
}

int eliminate_co_datatypes(FILE *in, FILE *out)
{
    tok = get_token(in);
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

    tok = get_token(in);

    char funs[Big_Num][Big_Num];

    for (int i = 0; i < Big_Num; i++) {
        funs[i][0] = '\0';
    }

    while (tok != Tok_End && tok != Tok_Right_Paren) {
        eliminate_co_datatype(funs, in, out);
    }

    for (int i = 0; i < Big_Num; i++) {
        if (funs[i][0] != '\0') {
            fprintf(out, "(declare-fun %s)\n", funs[i]);
        }
    }

    tok = get_token(in);
    return 0;
}

int generate_one_file(const char *in_name, int keep_data, int keep_codata)
{
    FILE *in = fopen(in_name, "r");
    if (in == 0) {
        fprintf(stderr, "Cannot open \"%s\"\n", in_name);
        return 1;
    }

    char out_name[Big_Num];

    strcpy(out_name, in_name);

    if (keep_data) {
        if (keep_codata) {
            strcat(out_name, ".all");
        } else {
            strcat(out_name, ".data");
        }
    } else {
        if (keep_codata) {
            strcat(out_name, ".codata");
        } else {
            strcat(out_name, ".nix");
        }
    }

    FILE *out = fopen(out_name, "w");

    if (out == 0) {
        fprintf(stderr, "Cannot open output file \"%s\"\n", out_name);
        return 1;
    }

    next_ch = fgetc(in);
    tok = get_token(in);

    while (tok != Tok_End) {
        if (tok == Tok_Left_Paren) {
            tok = get_token(in);

            if (tok == Tok_Declare_Datatypes && !keep_data) {
                eliminate_co_datatypes(in, out);
                if (tok == Tok_Right_Paren) {
                    tok = get_token(in);
                } else {
                    return 1;
                }
            } else if (tok == Tok_Declare_Codatatypes && !keep_codata) {
                eliminate_co_datatypes(in, out);
                if (tok == Tok_Right_Paren) {
                    tok = get_token(in);
                } else {
                    return 1;
                }
            } else {
                int depth = 1;

                fputc('(', out);

                while (tok != Tok_End && depth != 0) {
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
            + generate_one_file(argv[1], 0, 1)
            + generate_one_file(argv[1], 1, 0);
}
