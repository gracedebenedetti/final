#include "value.h"
#include "linkedlist.h"
#include "talloc.h"
#include "tokenizer.h"
#include "parser.h"
// #include "linkedlist.c"
// #include "talloc.c"
// #include "tokenizer.c"
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <ctype.h>

Value *addToParseTree(Value *tree, int *depth, Value *token){
    if (token->type != CLOSE_TYPE){
        if (token->type == OPEN_TYPE){
            *depth = *depth + 1;
        }
        tree = cons(token, tree);
    } else {
        if (*depth < 1) {
            printf("Syntax error: number of Parentheses \n");
            texit(1);
        }
        Value *subtree = makeNull();
        *depth = *depth - 1;
        while (car(tree)->type != OPEN_TYPE){
            subtree = cons(car(tree), subtree);
            tree = cdr(tree);
        }
        tree->c.car = subtree;
    }
    return tree;
}

// Takes a list of tokens from a Scheme program, and returns a pointer to a
// parse tree representing that program.
Value *parse(Value *tokens){
    Value *tree = makeNull();
    int depth = 0;

    Value *current = tokens;
    assert(current != NULL && "Error (parse): null pointer");
    while (current->type != NULL_TYPE) {
        Value *token = car(current);
        //printf("%s \n", token->s);
        tree = addToParseTree(tree, &depth, token);
        current = cdr(current);
    }
    if (depth != 0) {
        printf("Syntax error: number of Parentheses \n");
        texit(1);    
    }
    return reverse(tree);
}

void printToken(Value *tree){ 
    while (tree->type != NULL_TYPE){
        if (car(tree)->type == CONS_TYPE){
            printf(" (");
            printToken(car(tree));
            printf(") ");
        } else if (car(tree)->type == INT_TYPE){
            printf(" %i", car(tree)->i);
        } else if (car(tree)->type == STR_TYPE){
            printf(" %s", car(tree)->s);
        } else if (car(tree)->type == DOUBLE_TYPE){
            printf(" %lf", car(tree)->d);
        } else if (car(tree)->type == BOOL_TYPE){
            if (car(tree)->i == 1){
                printf(" #t");
            }
            if (car(tree)->i == 0){
                printf(" #f");
            }
        } else if (car(tree)->type == SYMBOL_TYPE) {
            printf(" %s ", car(tree)->s);
        } else if (car(tree)->type == NULL_TYPE) {
            printf("()");
        }
        tree = cdr(tree);
    }
}

void printTree(Value *tree){
    printToken(tree);
}

// Prints the tree to the screen in a readable fashion. It should look just like
// Scheme code; use parentheses to indicate subtrees.
// void printTree(Value *tree){
//     while(tree->type != NULL_TYPE){
//         printf("(");
//         //printsubtree();
//         //while (tree->type == CONS_TYPE){
//         //tree = car(tree);
//         if (car(tree)->type != CONS_TYPE){
//             //printf("going to print");
//             //printf("%u", car(tree)->type);
//             //printf("first if \n");
//             printToken(car(tree));
//         }
//         else{
//             tree = car(tree);
//             printToken(car(tree));
//         }
//         tree = cdr(tree);
//         //}
//     printf(")");
//     printf("\n");
//     }
// }