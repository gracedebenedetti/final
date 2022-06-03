#include "value.h"
#include "linkedlist.h"
#include "talloc.h"
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <ctype.h>

/**
 * @brief This function tests to see if the given character represents the beginning of a symbol.
 * 
 * @param ch 
 * @return true 
 * @return false 
 */
bool isSymbol(char ch){
    if ((65 <= ch && ch <= 90) || (97 <= ch && ch <= 122))
    {
        return true;
    }
    if (ch == '!' || ch == '$' || ch == '%' || ch == '&' || ch == '*' || ch == '/' || ch == ':' || ch == '<'
        || ch == '=' || ch == '>' || ch == '?' || ch == '~' || ch == '_' || ch == '^')
    {
        return true;
    }
    if (isdigit(ch))
    {
        return true;
    }
    return false;
}

/**
 * @brief This function reads data from stdin (assuming charRead is the start of a symbol)
 * and compiles the symbol into a single string before returning.
 * 
 * @param charRead 
 * @return Value* 
 */
Value* symbolToken(char charRead)
{
    char* symbol = (char*)talloc(301);
    int symSize = 0;
    Value* symToken = (Value*)talloc(sizeof(Value));
    symToken->type = SYMBOL_TYPE;

    while (charRead != EOF && charRead != ' ' && charRead != '\n' && charRead != '(' && charRead != ')')
    {
        symbol[symSize] = charRead;
        symSize++;
        charRead = (char)fgetc(stdin);
    }
    ungetc(charRead, stdin);
    
    symbol[symSize] = '\0';
    symToken->s = symbol;
    return symToken;
}

// This function should be called when an open quote is found. 
// It will read characters from stdin until another quote is found.
// If a \n or EOF is found before another quote, an error is thrown.
//
// BE CAREFUL WITH THIS! ONLY CALL WHEN " IS FOUND
//
// This method will consume stdin characters up to *and including* the closing quote
char *readString()
{
    char charRead = (char)fgetc(stdin); // this should be the first character of the string

    char* newString = talloc(301);
    int size = 0;
    newString[size] = '"';
    size++;
    
    while (charRead != EOF && charRead != '\n')
    {
        if (charRead == '"')
        {
            newString[size] = '"';
            newString[size+1] = '\0';
            return newString;
        } else
        {
            // add charRead to newString
            newString[size] = charRead;
            size++;
        }
        charRead = (char)fgetc(stdin);
    } // if we reach the end of the this while loop before we return, it means we have an error.
    printf("Syntax error: Closing quotation (\") expected.\n");
    texit(1);
    return NULL;
}


/**
 * @brief This function reads through numbers, determining double or int, and returning as a Value node.
 * 
 * @param charRead 
 * @return Value* 
 */
Value *numToken(char charRead) {
    char *fullnumber = talloc(301); //input cannot be longer than 300 chars
    int doubleCheck = 0;
    int numSize = 0;
    if (charRead == '+' || charRead == '-') {
      fullnumber[0] = charRead; //add
      numSize++;
      char symbolsign = charRead;
      charRead = (char)fgetc(stdin);

      if (!isdigit(charRead)) {
        charRead = ungetc(charRead, stdin);
        //charRead = ungetc(symbolsign, stdin); //add back +/- since not number
        charRead = symbolsign;
        return symbolToken(charRead);
      }
    }

    while (isdigit(charRead) || charRead == '.') { //int or double
        if (charRead == '.') {
            doubleCheck = 1; //is a double
        }
        fullnumber[numSize] = charRead;
        numSize++;
        charRead = (char)fgetc(stdin);
    }

    fullnumber[numSize] = '\0'; //end of num
    char *endptr;
    Value *newToken = talloc(sizeof(Value));
    if (doubleCheck) {
        newToken->type = DOUBLE_TYPE;
        newToken->d = strtod(fullnumber, &endptr);
    } else {
        newToken->type = INT_TYPE;
        newToken->i = strtod(fullnumber, &endptr);
    }
    ungetc(charRead, stdin);
    return newToken;

}

/**
 * @brief This function expects readChar == '#'. It compiles the 't' or 'f' into a 
 * new Value node and returns it.
 * 
 * @param readChar 
 * @return Value* 
 */
Value *boolToken(char readChar) {
  Value *newboolToken = talloc(sizeof(Value));
  assert(readChar == '#');
  newboolToken->type = BOOL_TYPE;
  char boolChar = (char)fgetc(stdin);
  if (boolChar == 'f') {
    newboolToken->i = 0;
  } else if (boolChar == 't') {
    newboolToken->i = 1;
  } else {
    printf("Syntax error: found '#', expected 'f' or 't' \n");
    texit(0);
  }
  return newboolToken;
}

/**
 * @brief This function handles tokenizing of open and close parenthesis.
 * 
 * @param paren 
 * @return Value* 
 */
Value *parenthesisToken(char paren){
    Value* token = (Value*)talloc(sizeof(Value));
    if (paren == '(')
    {

        token->type = OPEN_TYPE;
    } else
    {
        token->type = CLOSE_TYPE;
    }
    char* string = (char*)talloc(sizeof(char) * 2);
    string[0] = paren;
    string[1] = '\0';
    token->s = string;
    return token;
}


/**
 * @brief This function skips through Scheme comments until the end of the line.
 * 
 * @param readChar 
 * @return int 
 */
int isComment(char readChar) {
    assert(readChar == ';');
    while (readChar != EOF && readChar != '\n') {
        readChar = (char)fgetc(stdin); //keep searching for end of comment
    }
    if (readChar == EOF) {
        return 1;
    } else {
        return 0;
    }
}

// Read all of the input from stdin, and return a linked list consisting of the
// tokens.
Value *tokenize() {
    char charRead;
    Value *list = makeNull();
    charRead = (char)fgetc(stdin);

    while (charRead != EOF && charRead != '`') {
        //create new constype node
        //Value* newConsNode = cons(charRead, list); // the cdr of this should be the head of the current list
                                                   // (we will create a reverse list first, then reverse it)

        if (charRead == '(' || charRead == ')') {
            list = cons(parenthesisToken(charRead), list);
        } else if (charRead == '#') {
            list = cons(boolToken(charRead), list);
        } else if (charRead == '+' || charRead == '-' || isdigit(charRead) || charRead == '.'){
            list = cons(numToken(charRead), list);
        } else if (charRead == '"') {
            Value* strToken = (Value*)talloc(sizeof(Value));
            strToken->type = STR_TYPE;
            strToken->s = readString();
            list = cons(strToken, list);
        } else if (charRead == ';') {
            isComment(charRead);
        } else if (charRead == ' ' || charRead == '\n')
        { 
            // do nothing
        } else if (isSymbol(charRead)){
            list = cons(symbolToken(charRead), list);
        } else
        {
            printf("Syntax error: Untokenizable input\n");
            texit(1);
        }
        
        charRead = (char)fgetc(stdin);
    }
    Value *revList = reverse(list);
    return revList;
}





// Displays the contents of the linked list as tokens, with type information
void displayTokens(Value *list){
    //token = car(list);
    
    while(!isNull(list) && !isNull(car(list))){
        if (car(list)->type == INT_TYPE){
            printf("%i:integer\n", car(list)->i);
        }
        if (car(list)->type == BOOL_TYPE){
            if (car(list)->i == 1){
                printf("#t:boolean\n");
            }
            else{
                printf("#f:boolean\n");
            }
        }
        if (car(list)->type == STR_TYPE){
            printf("%s:string\n", car(list)->s);
        }
        if (car(list)->type == DOUBLE_TYPE){
            printf("%lf:double\n", car(list)->d);
        }
        if (car(list)->type == SYMBOL_TYPE){
            printf("%s:symbol\n", car(list)->s);
        }
        if (car(list)->type == OPEN_TYPE){
            printf("(:open\n");
        }
        if (car(list)->type == CLOSE_TYPE){
            printf("):close\n");
        } else 
        {
            
        }
        list = cdr(list);
    }
    texit(0);
}