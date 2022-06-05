#include "value.h"
#include "linkedlist.h"
#include "talloc.h"
#include "tokenizer.h"
#include "parser.h"
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <ctype.h>
#include "interpreter.h"



void evaluationError(char *errorMessage)
{
  printf("Evaluation error: %s\n", errorMessage);
  texit(1);
}

void printTokenHelp(Value* tree)
{
  assert(tree->type != CONS_TYPE && "Error -- unexpected call to printTokenHelp()");
  switch (tree->type) 
  {
    case INT_TYPE :
      printf("%d", tree->i);
      break;
    case DOUBLE_TYPE :
      printf("%lf",tree->d);
      break;
    case STR_TYPE :
      printf("\"%s\"",tree->s);
      break;
    case SYMBOL_TYPE :
      printf("%s", tree->s);
      break;
    case NULL_TYPE :
      printf ("()");
      break;
    case BOOL_TYPE :
      if (tree->i == 1)
      {
        printf("#t");
      } else
      {
        printf("#f");
      }
      break;
    case CLOSURE_TYPE :
      printf("#<procedure>");
      break;
    case VOID_TYPE :
      break;
    
    default :
      evaluationError("Print error");
  }
}



void printConsHelp(Value *tree)
{
  printf("(");
  while (tree->type != NULL_TYPE)
  {
    if (tree->type == CONS_TYPE && car(tree)->type == CONS_TYPE)
    {
      printConsHelp(car(tree));
    }
    else
    {
      printTokenHelp(car(tree));
      if (cdr(tree)->type != NULL_TYPE && cdr(tree)->type != CONS_TYPE)
      {
        printf(" . ");
        printTokenHelp(cdr(tree));
        break;
      }
    }
    if (cdr(tree)->type != NULL_TYPE)
    {
      printf(" ");
    }
    tree = cdr(tree);
  }
  printf(")");
}

// tree should just be a single cell
void print(Value* tree)
{
  if (tree->type == CONS_TYPE)
  {
    printConsHelp(tree);
  } else
  {
    printTokenHelp(tree);
  }
}


// Returns the length of a given tree. Tree should be a list of CONS_TYPEs followed by a NULL_TYPE
int treeLength(Value *tree)
{
  int len = 0;
  Value *cur = tree;
  while (cur->type != NULL_TYPE)
  {
    if (cur->type != CONS_TYPE)
    {
      printf("Error in treeLength(). CONS_TYPE node expected\n");
      texit(1);
    }
    len++;
    cur = cdr(cur);
  }
  return len;
}

Value* getBottomLeftChild(Value* tree)
{
  assert(tree != NULL && "Error: null tree/child");
  if (tree->type == CONS_TYPE)
  {
    return getBottomLeftChild(car(tree));
  }
  return tree;
}

// This method looks up the given symbol within the bindings to see if it is a bound variable
Value *lookUpSymbol(Value *symbol, Frame *frame)
{
  Value *bindings = frame->bindings; // we have to choose how to implement this. my idea is a list of cons cells, where each cell points to a *pair* of
                                     // cons cells, which are (symbol, value)
                                     // so (let ((x 1) (y "a")) ...) would look like *bindings = CONS-------------->CONS
                                     //                                                            |                   |
                                     //                                                           CONS--->CONS       CONS--->CONS
                                     //                                                            |        |         |        |
                                     //                                                        SYMBOL(x)   INT(1)  SYMBOL(y)  STR("a")
  Value *cur = bindings;
  while (cur->type != NULL_TYPE)
  //while (cur->type == CONS_TYPE)
  {
    //assert(cur->type == CONS_TYPE && "Should be cons type");
    Value *pairList = car(cur);
    //assert(pairList != NULL && pairList->type == CONS_TYPE);
    Value *boundSymbol = car(pairList);
    assert(boundSymbol->type == SYMBOL_TYPE);
    if (!strcmp(boundSymbol->s, symbol->s)) // if boundSymbol is equal to symbol, return the boundValue
    {
      Value *boundValue = car(cdr(pairList));
      if (boundValue->type == SYMBOL_TYPE)
      {
        return lookUpSymbol(boundValue, frame->parent);
      } else if (boundValue->type == CONS_TYPE)
      {
        if (getBottomLeftChild(boundValue)->type == INT_TYPE || getBottomLeftChild(boundValue)->type == STR_TYPE || getBottomLeftChild(boundValue)->type == BOOL_TYPE || getBottomLeftChild(boundValue)->type == DOUBLE_TYPE)
        {
          return boundValue;
        }
        return eval(cdr(pairList), frame);
      }
      return boundValue;
    }
    cur = cdr(cur);
  }
  if (frame->parent == NULL)
  {
    return NULL;
  }
  return lookUpSymbol(symbol, frame->parent);
}


Value *evalQuote(Value *tree){
  
  if (treeLength(tree) != 1){
    evaluationError("Error: too many args in quote");
  }
  if (tree->type == NULL_TYPE){
    evaluationError("Error: Quote args");
  }
  return car(tree);
}

Value *evalIf(Value *args, Frame *frame)
{
  if (treeLength(args) != 3)
  {
    evaluationError("evalution error");
  }
  Value* boolVal = eval(args, frame);
  if (boolVal->type != BOOL_TYPE)
  {
    evaluationError("Error: 1st argument of IF is not BOOL_TYPE");
  }
  else
  {
    if (boolVal->i == 1)
    {
      return eval(cdr(args), frame);
    }
    else
    {
      return eval(cdr(cdr(args)), frame);
    }
  }
  return NULL;
}

Value *evalLet(Value *args, Frame *frame)
{
  Frame *newFrame = talloc(sizeof(Frame));
  newFrame->bindings = frame->bindings;
  newFrame->parent = frame;
  if (treeLength(args) < 1){
    evaluationError("Error: empty arguments to let");
  } else {
    newFrame->bindings = car(args);
    //appendBindingsTree(newFrame->bindings, frame->bindings);
    
    Value* next = cdr(args);
    return eval(next, newFrame);
  }
  return NULL;
}


Value *evalBegin (Value *args, Frame *frame){
  while (args->type != NULL_TYPE){
    Value *begin = eval(car(args), frame);
    if (cdr(args)->type == NULL_TYPE){
      return begin;
    }
    args = cdr(args);
  }
  Value *special = talloc(sizeof(Value));
  special->type = VOID_TYPE;
  return special;
}

Value *evalEach(Value *args, Frame *frame){
  Value *evaledArgs = makeNull();
  Value *cur = args;
  while (cur->type != NULL_TYPE){
    evaledArgs = cons(eval(cur, frame), evaledArgs);
    cur = cdr(cur);
  }
  return reverse(evaledArgs);
}

Value *apply(Value *function, Value *args){
  if (function->type == PRIMITIVE_TYPE) {
    return (function->pf)(args);
  }
  if (args->type == NULL_TYPE)
  {
    eval(function->cl.functionCode, function->cl.frame);
  }
  
  //Construct a new frame whose parent frame is the environment 
  //stored in the closure.
  Frame *newFrame = talloc(sizeof(Frame));
  newFrame->parent = function->cl.frame;
  //Add bindings to the new frame mapping each formal parameter 
    //(found in the closure) to the corresponding actual parameter (found in args).
  Value *bindings = makeNull();
  Value *pnames = function->cl.paramNames;
  Value *body = function->cl.functionCode;
  while (args->type != NULL_TYPE && pnames->type != NULL_TYPE) {
    Value *binding = cons(car(args), makeNull());
    binding = cons(car(pnames), binding);
    bindings = cons(binding, bindings);
    pnames = cdr(pnames);
    args = cdr(args);
  }
  newFrame->bindings = bindings;
  //Evaluate the function body (found in the closure) with the new 
  //frame as its environment, and return the result of the call to eval.
  return eval(body, newFrame);
}

Value *evalAnd(Value *args, Frame *frame){
  if (treeLength(args) < 1) {
    evaluationError("Evaluation Error: less than 1 argument for and");
  }
  Value* boolVal = eval(args, frame);
  while (cdr(args)->type != NULL_TYPE){
    if (boolVal->i == 0){
      return boolVal;
    }
    args = cdr(args);
    boolVal = eval(args, frame);
    }
  return boolVal;
}

Value *evalOr(Value *args, Frame *frame){
  if (treeLength(args) < 1) {
    evaluationError("Evaluation Error: less than 1 argument for or");
  }
  Value* boolVal = eval(args, frame);
  while (cdr(args)->type != NULL_TYPE){
    if (boolVal->i == 1){
      return boolVal;
    }
    args = cdr(args);
    boolVal = eval(args, frame);
    }
  return boolVal;
}

Value *evalDefine(Value *args, Frame *frame){
  if (args->type == NULL_TYPE) {
    evaluationError("Evaluation error: no arguments");
  }
  else if (cdr(args)->type == NULL_TYPE || car(cdr(args))->type == NULL_TYPE) {
    evaluationError("Evaluation error: no body");
  } else if (car(args)->type != SYMBOL_TYPE) {
    evaluationError("Evaluation error: not a symbol");
  }
  //segfault
  Value *binding = cons(eval(cdr(args), frame), makeNull());
  binding = cons(car(args), binding);
  binding = cons(binding, makeNull());
  if (frame->bindings->type == NULL_TYPE)
  {
    frame->bindings = binding;
  } else
  {
    Value* tail = binding;
    tail->c.cdr = frame->bindings;
    frame->bindings = binding;
  }
  
  Value *special = talloc(sizeof(Value));
  special->type = VOID_TYPE;
  return special;
}

Value *evalLambda(Value *args, Frame *frame){
  if (args->type == NULL_TYPE) {
    evaluationError("Evaluation Error: empty lambda");
  } else if (length(args) != 2) {
    evaluationError("Evaluation Error: parameters or body missing");
  } else if (car(args)->type == CONS_TYPE && car(car(args))->type != SYMBOL_TYPE) {
    evaluationError("Evaluation Error: parameters must be symbols");
  }
  Value* closure = (Value*)talloc(sizeof(Value));
  closure->type = CLOSURE_TYPE;
  closure->cl.frame = frame;
  if (car(args)->type == NULL_TYPE)
  {
    closure->cl.paramNames = makeNull();
  } else
  {
    assert(car(args)->type == CONS_TYPE && "Error, lambda parameter tree is wrongly formatted\n");
    closure->cl.paramNames = car(args);
  }
  closure->cl.functionCode = cdr(args);

  return closure;
}

void bind(char *name, Value *(*function)(Value *), Frame *frame) {
    // Add primitive functions to top-level bindings list
  Value* symbol = (Value*)talloc(sizeof(Value));
  symbol->type = SYMBOL_TYPE;
  symbol->s = name;

  Value* value = (Value*)talloc(sizeof(Value));
  value->type = PRIMITIVE_TYPE;
  value->pf = function;

  Value* list_2 = cons(value, makeNull());
  Value* list_1 = cons(symbol, list_2);

  frame->bindings = cons(list_1, frame->bindings);
}

Value *primitiveAdd(Value *args){
  double sum = 0;
  bool isDouble = 0;
  Value* cur = args;
  while (cur->type != NULL_TYPE){
    
    if (car(cur)->type == DOUBLE_TYPE)
    {
      isDouble = 1;
      sum += car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      sum += car(cur)->i;
    } else {
      evaluationError("Evaluation Error: Adding non-numbers");
    }
    cur = cdr(cur);
  }
  
  Value* ret = makeNull();
  if (isDouble)
  {
    ret->type = DOUBLE_TYPE;
    ret->d = sum;
  } else
  {
    ret->type = INT_TYPE;
    ret->i = (int)sum;
  }
  return ret;
}

Value *primitiveSubtract(Value *args){
  double difference = 0;
  bool isDouble = 0;
  Value* cur = args;
  while (cur->type != NULL_TYPE){
    
    if (car(cur)->type == DOUBLE_TYPE)
    {
      isDouble = 1;
      difference -= car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      difference -= car(cur)->i;
    } else {
      evaluationError("Evaluation Error: Subtracting non-numbers");
    }
    cur = cdr(cur);
  }
  
  Value* ret = makeNull();
  if (isDouble)
  {
    ret->type = DOUBLE_TYPE;
    ret->d = difference;
  } else
  {
    ret->type = INT_TYPE;
    ret->i = (int)difference;
  }
  return ret;
}

Value *primitiveGreater (Value *args){
  bool firstisDouble = 0;
  bool secondisDouble = 0;
  double first;
  double second;
  Value *result = makeNull();
  result->type = BOOL_TYPE;
  Value* cur = args;
  if (car(cur)->type == DOUBLE_TYPE)
    {
      firstisDouble = 1;
      double first = car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      int first = car(cur)->i;
    } else {
      evaluationError("Evaluation Error: Comparing non-numbers");
    }
  if (car(cdr(cur))->type == DOUBLE_TYPE)
    {
      secondisDouble = 1;
      double second = car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      int second = car(cur)->i;
    } else {
      evaluationError("Evaluation Error: comparing non-numbers");
    }
  if (first > second){
    result->i = 1;
  } else {
    result->i = 0;
  }
  return result;
}

Value *primitiveLess (Value *args){
  bool firstisDouble = 0;
  bool secondisDouble = 0;
  double first;
  double second;
  Value *result = makeNull();
  result->type = BOOL_TYPE;
  Value* cur = args;
  if (car(cur)->type == DOUBLE_TYPE)
    {
      firstisDouble = 1;
      double first = car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      int first = car(cur)->i;
    } else {
      evaluationError("Evaluation Error: Comparing non-numbers");
    }
  if (car(cdr(cur))->type == DOUBLE_TYPE)
    {
      secondisDouble = 1;
      double second = car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      int second = car(cur)->i;
    } else {
      evaluationError("Evaluation Error: comparing non-numbers");
    }
  if (first < second){
    result->i = 1;
  } else {
    result->i = 0;
  }
  return result;
}

Value *primitiveEqual (Value *args){
  bool firstisDouble = 0;
  bool secondisDouble = 0;
  double first;
  double second;
  Value *result = makeNull();
  result->type = BOOL_TYPE;
  Value* cur = args;
  if (car(cur)->type == DOUBLE_TYPE)
    {
      firstisDouble = 1;
      double first = car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      int first = car(cur)->i;
    } else {
      evaluationError("Evaluation Error: Comparing non-numbers");
    }
  if (car(cdr(cur))->type == DOUBLE_TYPE)
    {
      secondisDouble = 1;
      double second = car(cur)->d;
    } else if (car(cur)->type == INT_TYPE){
      int second = car(cur)->i;
    } else {
      evaluationError("Evaluation Error: comparing non-numbers");
    }
  if (first == second){
    result->i = 1;
  } else {
    result->i = 0;
  }
  return result;
}

Value *primitiveNull(Value *args){
  if (treeLength(args) != 1) {
    evaluationError("Evaluation error: more or less than 1 argument");
  }
  Value* ret = (Value*)talloc(sizeof(Value));
  ret->type = BOOL_TYPE;
  Value* argument = car(args); // if argument is a cons_type, then check to see if it points to an empty list
                                // (if so, return true). otherwise, check to see if it's null (if so, return true).
                                // if neither, return false;
  if (argument->type == CONS_TYPE)
  {
    if (car(argument)->type == NULL_TYPE)
    {
      ret->i = 1;
    } else
    {
      ret->i = 0;
    }
  } else
  {
    if (argument->type == NULL_TYPE)
    {
      ret->i = 1;
    } else
    {
      ret->i = 0;
    }
  }
  return ret;
}

Value *primitiveCar(Value *args){
  if (treeLength(args) != 1) {
    evaluationError("Evaluation error: more or less than 1 argument");
  }
  if (car(args)->type != CONS_TYPE){
    evaluationError("Evaluation error: not a cons type argument");
  }
  return car(car(args));
}

Value *primitiveCdr(Value *args){
  if (treeLength(args) != 1) {
    evaluationError("Evaluation error: more or less than 1 argument");
  }
  if (car(args)->type != CONS_TYPE){
    evaluationError("Evaluation error: not a cons type argument");
  }
  return cdr(car(args));
}

Value *primitiveCons(Value *args){
  if (treeLength(args) != 2) {
    evaluationError("Evaluation error: more or less than 2 arguments");
  }
  return cons(car(args), car(cdr(args)));
}

Value *eval(Value *tree, Frame *frame)
{
  Value* val = car(tree);
  switch (val->type)
  {
    case INT_TYPE: // this means the whole program consists of one single number, so we can just return the number.
      return val;

    case DOUBLE_TYPE:
      return val;
    case BOOL_TYPE:
      return val;
    case NULL_TYPE:
      return val;
    case STR_TYPE: // this means the whole program is just a string, so we can just return it
      return val;
    case SYMBOL_TYPE:
    {               // this means that the whole program is just a variable name, so just return the value of the variable.
      Value* found = lookUpSymbol(val, frame);
      if (found == NULL)
      {
        evaluationError("symbol not found.\n");
      }
      return found;
    }
    case CONS_TYPE:
      if (!strcmp(car(val)->s, "if"))
      {
        Value* nxt = cdr(val);
        return evalIf(nxt, frame);
      }
      if (!strcmp(car(val)->s, "quote"))
      {
        return evalQuote(cdr(val));
      }
      if (!strcmp(car(val)->s, "let"))
      {
        return evalLet(cdr(val), frame);
      }
      // .. other special forms here...
      if (!strcmp(car(val)->s, "define")) 
      {
        //Frame *defineFrame = talloc(sizeof(Frame));
        return evalDefine(cdr(val), frame);
      }
      if (!strcmp(car(val)->s, "lambda")) 
      {
        return evalLambda(cdr(val), frame);
      }
      if (!strcmp(car(val)->s, "and")) 
      {
        return evalAnd(cdr(val), frame);
      }
      if (!strcmp(car(val)->s, "or")) 
      {
        return evalOr(cdr(val), frame);
      } 
      if (!strcmp(first->s, "set!")) 
      {
          return = evalSet(args, frame);
      }
      if (!strcmp(first->s, "let*")) 
      {
          return = evalLetStar(args, frame);
      }
      if (!strcmp(first->s, "letrec")) 
      {
          return = evalLetRec(args, frame);
      }
      // if (!strcmp(car(val)->s, "+"))
      // {
      //   return primitiveAdd(cdr(val), frame);
      // }
      // if (!strcmp(car(val)->s, "car")) 
      // {
      //   return eval(val, frame);
      // }
      else
      {
        // If not a special form, evaluate the first, evaluate the args, then
        // apply the first to the args.
        Value *evaledOperator = eval(val, frame); // this returns a closure
        Value *evaledArgs = evalEach(cdr(val), frame);
        return apply(evaledOperator, evaledArgs);
      }
      break;
    default:
      printf("Evaluation error, type: %u,\n",val->type);
      break;
  }
  return NULL;
}


// calls eval for each top-level S-expression in the program.
// You should print out any necessary results before moving on to the next S-expression.
void interpret(Value *tree)
{
  Frame *frame = talloc(sizeof(Frame));
  frame->parent = NULL;
  frame->bindings = makeNull();
  // for s-expression in program:
  Value *curr = tree;
  while (curr->type != NULL_TYPE)
  {
    bind("+", primitiveAdd, frame);
    bind("null?", primitiveNull, frame);
    bind("car", primitiveCar, frame);
    bind("cdr", primitiveCdr, frame);
    bind("cons", primitiveCons, frame);
    bind(">", primitiveGreater, frame);
    bind("<", primitiveLess, frame);
    bind("=", primitiveEqual, frame);
    Value* result = eval(curr,frame);
    print(result);
    curr = cdr(curr);
    printf("\n");
  }
}



// int main() {

//     Value *list = tokenize();
//     Value *tree = parse(list);
//     interpret(tree);

//     tfree();
//     return 0;
// }