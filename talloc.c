#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "value.h"
#include "linkedlist.h"

//global variable head

// Basically what this variable does is it keeps track of the head of the list.
// However, you're not allowed to have pointers as global variables,
// so this one is an object literal which *points* to the head of the list.
//
// If the list is empty, then the cdr of the listHead will be NULL. (Which it is by default)
// If the list has items, then the cdr of the listHead will *point* to the head of the list,
// which can then be used as normal.
//
Value* listHead;


// Replacement for malloc that stores the pointers allocated.
void *talloc(size_t size){
    if (listHead == NULL)
    {
        Value* newNullNode = (Value*)malloc(sizeof(Value));
        newNullNode->type = NULL_TYPE;
        listHead = newNullNode;
    }
    Value* newPtrNode = (Value*)malloc(sizeof(Value));
    newPtrNode->type = PTR_TYPE;
    void* newPtr = malloc(size); // This is the new pointer being malloc'd by the user
    newPtrNode->p = newPtr; // assigns the pointer to the new PTR_TYPE node

    Value* newConsNode = (Value*)malloc(sizeof(Value));
    newConsNode->type = CONS_TYPE;

    newConsNode->c.car = newPtrNode;
    newConsNode->c.cdr = listHead;
    listHead = newConsNode;
    return newPtr;
}

// Free all pointers allocated by talloc, as well as whatever memory you
// allocated in lists to hold those pointerse.
void tfree(){
    Value* tempPtr = listHead;
    while (listHead != NULL && listHead->type != NULL_TYPE) // only need to free memory if the list is nonempty
    {
        if (listHead->c.car != NULL && listHead->c.car->type == PTR_TYPE)
        {
            free(listHead->c.car->p);
        }
        free(listHead->c.car);
        tempPtr = listHead;
        listHead = listHead->c.cdr;
        free(tempPtr);
    }
    free(listHead);
    listHead = NULL;
}

// Replacement for the C function "exit", that consists of two lines: it calls
// tfree before calling exit.
void texit(int status){
    tfree();
    exit(status);
}
