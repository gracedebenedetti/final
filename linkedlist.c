#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include <string.h>
#include "linkedlist.h"
#include "value.h"
#include "talloc.h"


// Create a new NULL_TYPE value node.
Value *makeNull(){
    Value *val = (Value *)talloc(sizeof(Value));
    val->type = NULL_TYPE;
    return val;
}

// Create a new CONS_TYPE value node.
Value *cons(Value *newCar, Value *newCdr){
    Value *consVal = (Value *)talloc(sizeof(Value));
    consVal->type = CONS_TYPE;
    consVal->c.car = newCar;
    consVal->c.cdr = newCdr;
    return consVal;
}


// Utility to make it less typing to get car value. Use assertions to make sure
// that this is a legitimate operation.
Value *car(Value *list){
    assert(list->type != NULL_TYPE);
    return list->c.car;
}

// Utility to make it less typing to get cdr value. Use assertions to make sure
// that this is a legitimate operation.
Value *cdr(Value *list){
    assert(list->type != NULL_TYPE);
    return list->c.cdr;
}

// Utility to check if pointing to a NULL_TYPE value. Use assertions to make sure
// that this is a legitimate operation.
bool isNull(Value *value){
    assert(value);
    return (value->type == NULL_TYPE);
}

// Display the contents of the linked list to the screen in some kind of
// readable format
void display(Value *list){
    Value *cur = list;
    while (cur->type != NULL_TYPE) {
        if (car(cur)->type == INT_TYPE){
            printf("value = %d\n", car(cur)->i);
        }
        if (car(cur)->type == DOUBLE_TYPE){
            printf("value = %lf\n", car(cur)->d);
        }
        if (car(cur)->type == STR_TYPE){
            printf("value = %s\n", car(cur)->s);
        }
        cur = cdr(cur);
    }
}

// Return a new list that is the reverse of the one that is passed in. No stored
// data within the linked list should be duplicated; rather, a new linked list
// of CONS_TYPE nodes should be created, that point to items in the original
// list.
Value *reverse(Value *list){
    Value* cur = list;
    Value* tempNull = makeNull(); // [1] This is temporary until we can copy the null from the original list. this will be freed at the end.
    if (cur->type == NULL_TYPE){
        return cur;
    }
    Value* newHead = cons(car(cur), tempNull);
    Value* newTail = newHead; // [2] Eventually this gets assigned to the null node at the end
    cur = cdr(cur);
    while(cur->type != NULL_TYPE && cur != NULL)
    {
        Value* newConsCell = cons(car(cur), newHead);
        newHead = newConsCell;
        cur = cdr(cur);
    }
    newTail->c.cdr = cur; // This is what we described in comment [2]
    //free(tempNull); // This is what we described in comment [1]
    return newHead;
}

// // Frees up all memory directly or indirectly referred to by list. This includes strings.
// void cleanup(Value *list){
//     Value* cur = list;
//     while (!isNull(cur)){
//         Value *next = cdr(cur);
//         if (car(cur)->type == STR_TYPE){
//             free(car(cur)->s);
//         }
//         free(car(cur));
//         free(cur);
//         cur = next;
//     }
//     free(cur);
// }

// Measure length of list. Use assertions to make sure that this is a legitimate
// operation.
int length(Value *value){
    Value *cur = value;
    assert(cur);
    int length = 0;
    if (cur->type == NULL_TYPE){
        return 0;
    }
    //need to use assertions but this line failing
    //assert(!isNull(cur));
    while (cur->type != NULL_TYPE){
        Value *next = cdr(cur);
        length++;
        cur = next;
    }
    return length;
}