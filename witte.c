#include "interpreter.h"

//clang -g linkedlist.c parser.c tokenizer.c talloc.c interpreter.c -o interpreter



//HELPERS



Frame *newFrame(Frame *curFrame){
  //initializes and creates a new frame
  Frame *frame=talloc(sizeof(Frame));
  frame->parent=curFrame;
  frame->bindings=makeNull();
  return frame;
}
void evaluationError(){
  printf("Evaluation error\n");
  texit(0);
}

void printReturn(Value *car){
     switch (car->type){
       case INT_TYPE:
         printf("%i\n",car -> i);
         break;
       case DOUBLE_TYPE:
         printf("%f\n", car -> d);
         break;
       case STR_TYPE:
         printf("%s\n", car -> s);
         break;
       case NULL_TYPE:
        printf("() ");
         break;
       case CONS_TYPE:
        printf("(");
        printProg(car);
        printf("\n");
         break;
       case PTR_TYPE:
         break;
       case OPEN_TYPE:
         printf("%s\n", car -> s);
         break;
       case CLOSE_TYPE:
         printf("%s\n", car -> s);
         break;
       case BOOL_TYPE:
         if(car->i==1){
          printf("%s\n","#t");
          }
        else{
          printf("%s\n","#f");
        }
        break;
       case SYMBOL_TYPE:
         printf("%s\n", car -> s);
         break;
       case OPENBRACKET_TYPE:
         break;
       case CLOSEBRACKET_TYPE:
         break;
       case DOT_TYPE:
         break;
       case SINGLEQUOTE_TYPE:
         break;
        case VOID_TYPE:
          break;
        case CLOSURE_TYPE:
        printf("#<procedure>\n");
        break;
        case PRIMITIVE_TYPE:
          break;
        case UNSPECIFIED_TYPE:
          printf("#<undifined>\n");
          break;
     }
   }

void doubleVarChecker(Value *compare, Frame *frame){
  while(frame->bindings->type!=NULL_TYPE){
      if(!strcmp(frame->bindings->c.car->c.car->s,compare->s)){
        evaluationError();
      }
      frame->bindings=frame->bindings->c.cdr;
    }
}

void doubleParamchecker(Value *closure){
  Value *holder=closure->cl.paramNames;
  Value *symbol=closure->cl.paramNames;
  int counter=0;
  while(symbol->type!=NULL_TYPE){
    if(symbol->c.car->type!=SYMBOL_TYPE){
      evaluationError();
    }
    while(holder->type!=NULL_TYPE){
      if(!strcmp(holder->c.car->s,symbol->c.car->s)){
          counter++;
        }
        holder=holder->c.cdr;
    }
    if(counter>1){
      evaluationError();
    }
    symbol=symbol->c.cdr;
    holder=symbol;
    counter=0;
  }
}

Value *replaceSymbol(Value *symbol, Value *newVal, Frame *frame){
  //takes a cymbol and looks up what that symbol points to in the frames.
  Value *result=talloc(sizeof(Value));
  result->type=VOID_TYPE;
  Value *bindings;
  while(frame!=NULL){
    bindings=frame->bindings;
    while(frame->bindings->type!=NULL_TYPE){
    //if you find a match for the symbol return the match.
      if(!strcmp(car(car(frame->bindings))->s,symbol->s)){
        frame->bindings->c.car->c.cdr=newVal;
        frame->bindings=bindings;
        return result;//eval(result,frame);
      }
    frame->bindings=frame->bindings->c.cdr;
    }
    frame->bindings=bindings;
    frame=frame->parent;
    }
  evaluationError();
  return result;
}



void setBindings(Value *bindings, Frame *frame){
  //sets the bindings for local variables
  if(bindings->type!=CONS_TYPE && bindings->type!=NULL_TYPE){
    evaluationError();
  }
  
  //char *last;
  while(bindings->type!=NULL_TYPE){
    if(car(bindings)->type!=CONS_TYPE||length(car(bindings))!=2||bindings->c.car->c.car->type!=SYMBOL_TYPE){
      evaluationError();
    }
  
    Value *holder=frame->bindings;
    doubleVarChecker(car(car(bindings)),frame);
    //creates cons cell where car is the symbol and cdr is the value the symbol points to
    /*if (last != car(car(bindings)) -> s) {
      char *last = car(car(bindings)) -> s;
    } else {
      evaluationError();
    }*/
   frame->bindings=holder;
    Value *symbol=cons(car(car(bindings)),eval(car(car(bindings)->c.cdr),frame));
    //then we store this into the Frames bindings
    Value *framePtr=frame->bindings;
    frame->bindings=cons(symbol,framePtr);
    bindings=bindings->c.cdr;
  }
}

void setLetRec(Value *symbols,Frame *frame){
  Value *un=talloc(sizeof(Value));
  un->type=UNSPECIFIED_TYPE;
  while(symbols->type!=NULL_TYPE){
    Value *pair=cons(car(symbols),un);
    frame->bindings=cons(pair,frame->bindings);
    symbols=cdr(symbols);
  }
}

void setLetRecFin(Value *symbols, Value *vals, Frame *frame){
  Value *bindings;
  Value *symbol;
  Value *val;
  while(symbols->type!=NULL_TYPE){
    symbol=car(symbols);
    val=car(vals);
    replaceSymbol(symbol,val,frame);
    symbols=cdr(symbols);
    vals=cdr(vals);
}
}





void setLambdaBindings(Value *formal, Value *actual, Frame *frame){
  if(length(formal)!=length(actual)){
    evaluationError();
  }
  while(formal->type!=NULL_TYPE){
    Value *bindings=frame->bindings;
    Value *symbol=cons(car(formal),car(actual));
    Value *newPair=cons(symbol,bindings);
    frame->bindings=newPair;
    formal=formal->c.cdr;
    actual=actual->c.cdr;
  }

}

void bind(char *name,Value *(*function)(struct Value *), Frame *frame){
  Value *symbol=talloc(sizeof(Value));
  symbol->s=talloc(sizeof(char)*(strlen(name)+1));
  strcpy(symbol->s,name);
  Value *value=talloc(sizeof(Value));
  value->type=PRIMITIVE_TYPE;
  value->pf=function;
  symbol->type=SYMBOL_TYPE;
  Value *binding=cons(symbol,value);
  frame->bindings=cons(binding,frame->bindings);
}

Value *lookupSymbol(Value *symbol, Frame *frame){
  //takes a cymbol and looks up what that symbol points to in the frames.
  Value *result;
  Value *bindings;
  while(frame!=NULL){
    bindings=frame->bindings;
    while(frame->bindings->type!=NULL_TYPE){
    //if you find a match for the symbol return the match.
      if(!strcmp(car(car(frame->bindings))->s,symbol->s)){
        result = cdr(car(frame->bindings));
        frame->bindings=bindings;
        return result;//eval(result,frame);
      }
    frame->bindings=frame->bindings->c.cdr;
    }
    frame->bindings=bindings;
    frame=frame->parent;
    }
  evaluationError();
  return NULL;
}




//PRIMITIVES---------------------------------------------------------------



Value *add(Value *args){
  int doubleFlag=0;
  Value *returnVal=talloc(sizeof(Value));
  returnVal->type=INT_TYPE;
  int val=0;
  double doub=0;
  while(args->type!=NULL_TYPE){
    if(car(args)->type!=DOUBLE_TYPE&&car(args)->type!=INT_TYPE){
      evaluationError();
    }
    if(car(args)->type==DOUBLE_TYPE&&doubleFlag==0){
      doubleFlag=1;
      returnVal->type=DOUBLE_TYPE; 
         }
    if(car(args)->type==DOUBLE_TYPE){
      doub+=car(args)->d;
    }
    else{
      val+=car(args)->i;
    }

    args=cdr(args);
}
if(doubleFlag==0){
  returnVal->i=val;
}
else{
  returnVal->d=val+doub;
}
return returnVal;
}

Value *consC(Value *args){
  if(length(args)!=2){
    evaluationError();
  }
  return cons(car(args),car(cdr(args)));
}

Value *carC(Value *args){
  if(length(args)!=1||car(args)->type!=CONS_TYPE){
    evaluationError();
  }
  return car(car(args));
}

Value *cdrC(Value *args){
  if(length(args)!=1||car(args)->type!=CONS_TYPE){
    evaluationError();
  }
  return cdr(car(args));
}

Value *null(Value *args){
  if(length(args)!=1){
    evaluationError();
  }
  Value *retVal=talloc(sizeof(Value));
  retVal->type=BOOL_TYPE;
  if(car(args)->type==NULL_TYPE){
    retVal->i=1;
  }
  else{
    retVal->i=0;
  }
  return retVal;
}

Value *sub(Value *args){
  int doubleFlag=0;
  Value *returnVal=talloc(sizeof(Value));
  returnVal->type=INT_TYPE;
  int val=0;
  double doub=0;
  if(car(args)->type==INT_TYPE){
    val=car(args)->i;
    args=cdr(args);
  }
  else if(car(args)->type==DOUBLE_TYPE){
    doub=car(args)->d;
    args=cdr(args);
  }
  while(args->type!=NULL_TYPE){
    if(car(args)->type!=DOUBLE_TYPE&&car(args)->type!=INT_TYPE){
      evaluationError();
    }
    if(car(args)->type==DOUBLE_TYPE&&doubleFlag==0){
      doubleFlag=1;
      returnVal->type=DOUBLE_TYPE; 
         }
    if(car(args)->type==DOUBLE_TYPE){
      doub-=car(args)->d;
    }
    else{
      val-=car(args)->i;
    }

    args=cdr(args);
}
if(doubleFlag==0){
  returnVal->i=val;
}
else{
  returnVal->d=val+doub;
}
return returnVal;
}

Value *less(Value *args){
  if(length(args)!=2){
    evaluationError();
  }
  Value *boolRet=talloc(sizeof(Value));
  boolRet->type=BOOL_TYPE;
  boolRet->i=0;
  if(car(args)->type==DOUBLE_TYPE){
    if(car(cdr(args))->type==DOUBLE_TYPE){
      if(car(args)->d<car(cdr(args))->d){
        boolRet->i=1;
      }
    }
    else{
      if(car(args)->d<car(cdr(args))->i){
        boolRet->i=1;
      }
    }
  }
  else{
    if(car(cdr(args))->type==DOUBLE_TYPE){
      if(car(args)->i<car(cdr(args))->d){
        boolRet->i=1;
      }
    }
    else{
      if(car(args)->i<car(cdr(args))->i){
        boolRet->i=1;
      }
    }

  }
  return boolRet;
}


Value *greater(Value *args){
  if(length(args)!=2){
    evaluationError();
  }
  Value *boolRet=talloc(sizeof(Value));
  boolRet->type=BOOL_TYPE;
  boolRet->i=0;
  if(car(args)->type==DOUBLE_TYPE){
    if(car(cdr(args))->type==DOUBLE_TYPE){
      if(car(args)->d>car(cdr(args))->d){
        boolRet->i=1;
      }
    }
    else{
      if(car(args)->d>car(cdr(args))->i){
        boolRet->i=1;
      }
    }
  }
  else{
    if(car(cdr(args))->type==DOUBLE_TYPE){
      if(car(args)->i>car(cdr(args))->d){
        boolRet->i=1;
      }
    }
    else{
      if(car(args)->i>car(cdr(args))->i){
        boolRet->i=1;
      }
    }

  }
  return boolRet;
}

Value *equal(Value *args){
  if(length(args)!=2){
    evaluationError();
  }
  Value *boolRet=talloc(sizeof(Value));
  boolRet->type=BOOL_TYPE;
  boolRet->i=0;
  if(car(args)->i==car(cdr(args))->i){
    boolRet->i=1;
  }
  return boolRet;
}


//SPECIAL EVALS-----------------------------------------------------------




Value *evalEach(Value *args, Frame *frame){
  Value *param;
  Value *returnList=makeNull();
  while(args->type!=NULL_TYPE){
    param=eval(car(args),frame);
    Value *parameter=cons(param,returnList);
    returnList=parameter;
    args=args->c.cdr;
  }
  return reverse(returnList);
}

//eval special cases
Value *evalIf(Value *args, Frame * frame){
  //Evaluates an if expression
  Value *test=eval(car(args),frame);
  //evaluates the test
  if(length(args)!=3){
    //if the length of the expression does not equal three then there is an error
    evaluationError();
  }
  if(test->type!=BOOL_TYPE){
    evaluationError();
  }
  if(test->i==1){
    //true is returned so evaluates true expression
    return eval(car(cdr(args)), frame);
  }
  else{
    //evaluates false expression
    return eval(car(cdr(cdr(args))),frame);
  }
}
 

Value *evalLet(Value *args, Frame *frame){
  //evaluates let
   if(length(args) < 2){
    evaluationError();
  }
  //sets bindings in the curent frame
  setBindings(car(args),frame);
  Value *valToEval=args->c.cdr;
  while(valToEval->c.cdr->type!=NULL_TYPE){
    valToEval=valToEval->c.cdr;

  }
  return eval(car(valToEval),frame);
}

Value *evalLetS(Value *args, Frame *frame){
  if(length(args) < 2){
    evaluationError();
  }
  Value *states=car(args);
  while (states->type!=NULL_TYPE){
    frame=newFrame(frame);
    setBindings(states,frame);
    states=states->c.cdr;
  }
  Value *valToEval=args->c.cdr;
  while(valToEval->c.cdr->type!=NULL_TYPE){
    valToEval=valToEval->c.cdr;

  }
  return eval(car(valToEval),frame);

}

Value *evalLetRec(Value *args, Frame *frame){
  Value *state=car(args);
  Value *symbols=makeNull();
  Value *values=makeNull();
  while(state->type!=NULL_TYPE){
    Value *symbol=cons(car(car(state)),symbols);
    symbols=symbol;
    Value *val=cons(car(cdr(car(state))),values);
    values=val;
    state=state->c.cdr;
  }
  Frame *frame1=newFrame(frame);
  setLetRec(symbols,frame1);
  Value *evaledVals=evalEach(values,frame1);
  setLetRecFin(symbols,evaledVals,frame1);
  Value *valToEval=args->c.cdr;
  while(valToEval->c.cdr->type!=NULL_TYPE){
    valToEval=valToEval->c.cdr;
  }
  return eval(car(valToEval),frame1);
}

Value *evalQuote(Value *args, Frame *frame){
    if (car(args) -> type != CONS_TYPE) {
            if (length(args) > 1) {
              evaluationError();
            }
          }
    return car(args);}

Value *evalDefine(Value *args, Frame *frame){
  if(args->type==NULL_TYPE||car(args)->type!=SYMBOL_TYPE||length(args)<2){
    evaluationError();
  }
  Value *bindings = frame -> bindings;
  Value *cdr=eval(car(args->c.cdr),frame);
  Value *symbol = cons(car(args),cdr);
  frame -> bindings = cons(symbol,bindings);
  Value *returnVal = talloc(sizeof(Value));
  returnVal->type = VOID_TYPE;
  return returnVal;
}

Value *evalLambda(Value *args, Frame *frame){
  if(length(args)<2){
    evaluationError();
  }
  Value *closure=talloc(sizeof(Value));
  closure->type=CLOSURE_TYPE;
  if (car(args)->type!=NULL_TYPE) {
    closure->cl.paramNames=car(args);
  }
  else {
    closure->cl.paramNames=makeNull();
  }
  doubleParamchecker(closure);
  closure->cl.functionCode=car(cdr(args));
  closure->cl.frame=frame;
  return eval(closure,frame);
}

Value *evalSet(Value *args, Frame *frame){
  if(args->type==NULL_TYPE||car(args)->type!=SYMBOL_TYPE||length(args)<2){
    evaluationError();
  }
  Value *ret=replaceSymbol(car(args),eval(car(cdr(args)),frame),frame);
  return eval(ret,frame);
}

Value *evalBegin(Value *args, Frame *frame){
  while(cdr(args)->type!=NULL_TYPE){
    eval(car(args),frame);
    args=cdr(args);
  }
  return eval(car(args),frame);
}

Value *evalAnd(Value *args, Frame *frame){
  Value *test;
  while(args->type!=NULL_TYPE){
    test=eval(car(args),frame);
    if(test->i==0){
      return test;
    }
    args=cdr(args);
  }
  return test;
}

Value *evalOr(Value *args, Frame *frame){
  Value *test;
  while(args->type!=NULL_TYPE){
    test=eval(car(args),frame);
    if(test->i==1){
      return test;
    }
    args=cdr(args);
  }
  return test;
}

Value *apply(Value *function, Value *parameters){
  Frame *deepFrame=newFrame(function->cl.frame);
  setLambdaBindings(function->cl.paramNames,parameters,deepFrame);
  return eval(function->cl.functionCode,deepFrame);
}




//CORE---------------------------------------------------------------------


void interpret(Value *tree){
  Frame *globalFrame=talloc(sizeof(Frame));
  globalFrame->bindings=makeNull();
  globalFrame->parent=NULL;
  bind("+",add,globalFrame);
  bind("cons",consC,globalFrame);
  bind("car",carC,globalFrame);
  bind("cdr",cdrC,globalFrame);
  bind("null?",null,globalFrame);
  bind("<",less,globalFrame);
  bind(">",greater,globalFrame);
  bind("-",sub,globalFrame);
  bind("=",equal,globalFrame);
  while (tree->type!=NULL_TYPE){
    Value *expression=eval(car(tree),globalFrame);
    printReturn(expression);
    tree=tree->c.cdr;
  }
}




Value *eval(Value *tree, Frame *frame){
  switch (tree->type){
    case INT_TYPE: {
        return tree;
        break;
     }
    case DOUBLE_TYPE: {
        return tree;
        break;
     }  
    case SYMBOL_TYPE: {
      return lookupSymbol(tree,frame);
        break;
     }  
    case STR_TYPE:{
       return tree;
     }
    case BOOL_TYPE:{
      return tree;
    }
    case PTR_TYPE:
         break;
    case OPEN_TYPE:
         break;
    case CLOSE_TYPE:
         break;
    case OPENBRACKET_TYPE:
         break;
    case CLOSEBRACKET_TYPE:
         break;
    case DOT_TYPE:
         break;
    case SINGLEQUOTE_TYPE:
         break;
    case NULL_TYPE:
      break;
    case VOID_TYPE:
      return tree;
      break; 
    case CLOSURE_TYPE:
      return tree;
      break;
    case PRIMITIVE_TYPE:
      return tree;
      break;
    case UNSPECIFIED_TYPE:
      return tree;
      break;
    case CONS_TYPE: {
      //this turns the code into something it can eval and evaluates it
        Value *first = car(tree);
        Value *args = cdr(tree);
        
        Value *result;
        if (!strcmp(first->s,"if")) {
          result = evalIf(args,frame);
          return result;
            
        }
        else if(!strcmp(first->s,"let")) {
          Frame *deepFrame=newFrame(frame);
          result=evalLet(args,deepFrame);
          return result;
          
        } 
        else if(!strcmp(first->s,"quote")) {
          result=evalQuote(args,frame);
          return result;

        }
        else if(!strcmp(first->s,"define")) {
          result=evalDefine(args,frame);
          return eval(result,frame);
        }
        else if(!strcmp(first->s,"lambda")){
          result=evalLambda(args, frame);
          return eval(result,frame);
        }
        else if(!strcmp(first->s,"+")||!strcmp(first->s,"-")){
          Value *evaledArgs=evalEach(args,frame);
          Value *function=lookupSymbol(first,frame);
          return eval(function->pf(evaledArgs),frame);
        }
        else if(!strcmp(first->s,"cons")){
           Value *evaledArgs=evalEach(args,frame);
          Value *function=lookupSymbol(first,frame);
          return function->pf(evaledArgs);
        }
        else if(!strcmp(first->s,"null?")||!strcmp(first->s,"cdr")||!strcmp(first->s,"car")||!strcmp(first->s,">")||!strcmp(first->s,"=")||!strcmp(first->s,"<")){
           Value *evaledArgs=evalEach(args,frame);
          Value *function=lookupSymbol(first,frame);
          return function->pf(evaledArgs);
        }
        else if(!strcmp(first->s,"let*")){
          result=evalLetS(args, frame);
          return result;
        }
        else if(!strcmp(first->s,"letrec")){
          result=evalLetRec(args, frame);
          return result;
        }
        else if(!strcmp(first->s,"set!")){
          result=evalSet(args,frame);
          return eval(result,frame);
        }
        else if(!strcmp(first->s,"begin")){
          result=evalBegin(args,frame);
          return eval(result,frame);
        }
        else if(!strcmp(first->s,"and")){
          result=evalAnd(args,frame);
          return eval(result,frame);
        }
        else if(!strcmp(first->s,"or")){
          result=evalOr(args,frame);
          return eval(result,frame);
        }


        else{
          Value *evalOperator=eval(first,frame);
          Value *evaledArgs=evalEach(args,frame);
          return apply(evalOperator,evaledArgs);
        }
        
        break;
     }
     

      

    }
    return makeNull();  
}

/*int main(){
  Value *list = tokenize();
  Value *tree = parse(list);
  interpret(tree);
    tfree();
    return 0;
}*/