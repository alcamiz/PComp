%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 08 Jul 22   */

/* Copyright (c) 2022 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12;
   30 Jul 13; 25 Jul 19 ; 28 Feb 22 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input

                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D

                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D

           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <ctype.h>
#include <assert.h>
#include <string.h>
#include <stdbool.h>

#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"
#include "codegen.h"
// #include "parsfun.h"

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN makerealc(double num);
TOKEN makestringc(char *num);
TOKEN fixarray(TOKEN stplist, TOKEN type);
TOKEN fixrec(TOKEN rec, TOKEN list);
TOKEN fixpoint(TOKEN pt, TOKEN id);
TOKEN fieldconc (TOKEN lista, TOKEN listb);
TOKEN fixenum(TOKEN tok, TOKEN idlist);
TOKEN fixgoto(TOKEN labeltok);
TOKEN fixlabel(TOKEN labeltok, TOKEN statement);
TOKEN forcearef(TOKEN var, TOKEN off);
TOKEN combine_off(TOKEN aref, TOKEN a);
TOKEN createlabel(int c);

TOKEN parseresult;

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH

%right thenthen ELSE // Same precedence, but "shift" wins.

%%

program    :  PROGRAM IDENTIFIER LPAREN IDENTIFIER RPAREN SEMICOLON lblock DOT    { parseresult = makeprogram($2, $4, $7); }
           ;

  lblock     :  LABEL numlist SEMICOLON cblock              { $$ = $4; }
             |  cblock
             ;
  cblock     :  CONST cdef_list tblock                      { $$ = $3; }
             |  tblock
             ;
  tblock     :  TYPE tdef_list vblock                       { $$ = $3; }
             |  vblock
             ;
  vblock     :  VAR varspecs block                          { $$ = $3; }
             |  block
             ;
  cdef_list  :  cdef SEMICOLON cdef_list
             |  cdef SEMICOLON
             ;
  cdef       :  IDENTIFIER EQ constant                      { instconst($1, $3); }
             ;
  tdef_list  :  tdef SEMICOLON tdef_list
             |  tdef SEMICOLON
             ;
  tdef       :  IDENTIFIER EQ type                          { insttype($1, $3); }
             ;
  varspecs   :  vargroup SEMICOLON varspecs
             |  vargroup SEMICOLON
             ;
  vargroup   :  idlist COLON type                           { instvars($1, $3); }
             ;
  constant   :  NUMBER
             |  IDENTIFIER
             |  STRING
             ;
  numlist    :  NUMBER COMMA numlist                        { instlabel($1); }
             |  NUMBER                                      { instlabel($1); }
             ;
  type       :  simpletype
             |  ARRAY LBRACKET stplist RBRACKET OF type     { $$ = fixarray($3, $6); }
             |  RECORD fdlist END                           { $$ = fixrec($1, $2); }
             |  POINT IDENTIFIER                            { $$ = fixpoint($1, $2); }
             ;
  fields     :  idlist COLON type                           { $$ = instfields($1, $3); }
             ;
  fdlist     :  fields SEMICOLON fdlist                     { $$ = fieldconc($1, $3); }
             |  fields                                      { $$ = $1; }   
             ;
  simpletype :  IDENTIFIER                                  { $$ = findtype($1); }
             |  LPAREN idlist RPAREN                        { $$ = fixenum($1, $2); }
             |  constant DOTDOT constant                    { $$ = makesubrange($2, $1->intval, $3->intval); }
             ;
  stplist    :  simpletype COMMA stplist                    { $$ = cons($1, $3); }
             |  simpletype                                  { $$ = cons($1, NULL); }
             ;
  block      :  BEGINBEGIN statement endpart                { $$ = makeprogn($1,cons($2, $3)); }
             ;
  idlist     :  IDENTIFIER COMMA idlist                     { $$ = cons($1, $3); }
             |  IDENTIFIER                                  { $$ = cons($1, NULL); }
             ;
  statement  :  IF expr THEN statement endif                { $$ = makeif($1, $2, $4, $5); }
             |  FOR assignment TO expr DO statement         { $$ = makefor(1, $1, $2, $3, $4, $5, $6); }
             |  REPEAT stlist UNTIL expr                    { $$ = makerepeat($1, $2, $3, $4); }
             |  WHILE expr DO statement                     { $$ = makewhile($1, $2, $3, $4); }
             |  GOTO NUMBER                                 { $$ = fixgoto($2); }
             |  NUMBER COLON statement                      { $$ = fixlabel($1, $3); }
             |  assignment
             |  funcall
             |  block
             ;
  stlist     :  statement SEMICOLON stlist                  { $$ = cons($1, $3); }
             |  statement                                   { $$ = cons($1, NULL); }
             ;
  endpart    :  SEMICOLON statement endpart                 { $$ = cons($2, $3); }
             |  END                                         { $$ = NULL; }
             ;
  endif      :  ELSE statement                              { $$ = $2; }
             |  /* empty */                                 { $$ = NULL; }  %prec thenthen
             ;
  assignment :  variable ASSIGN expr                        { $$ = binop($2, $1, $3); }
             ;
  expr_list  :  expr_list COMMA expr                        { $$ = cons($1, $3); }
             |  expr                                        { $$ = cons($1, NULL); }
             |  STRING
             ;
  expr       :  expr PLUS term                              { $$ = binop($2, $1, $3); }
             |  expr MINUS term                             { $$ = binop($2, $1, $3); }
             |  expr EQ term                                { $$ = binop($2, $1, $3); }
             |  expr NE term                                { $$ = binop($2, $1, $3); }
             |  expr LT term                                { $$ = binop($2, $1, $3); }
             |  term
             ;
  term       :  term TIMES factor                           { $$ = binop($2, $1, $3); }
             |  term DIVIDE factor                          { $$ = binop($2, $1, $3); }
             |  factor
             ;
  factor     :  LPAREN expr RPAREN                          { $$ = $2; }
             |  MINUS variable                              { $$ = unaryop($1, $2); }
             |  variable
             |  funcall
             |  NUMBER
             |  NIL                                         { $$ = makeintc(0); }
             ;
  funcall    :  IDENTIFIER LPAREN expr_list RPAREN          { $$ = makefuncall($2, $1, $3); }
             ;
  variable   :  IDENTIFIER                                  { $$ = findid($1); }
             |  variable LBRACKET expr_list RBRACKET        { $$ = arrayref($1, $2, $3, $4); }
             |  variable DOT IDENTIFIER                     { $$ = reducedot($1, $2, $3); }
             |  variable POINT                              { $$ = dopoint($1, $2); }
             ;
  
%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG         0             /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */

int labelnumber = 0;  /* sequential counter for internal label numbers */
int labels[50] = {0};

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN cons(TOKEN item, TOKEN list) {

  if (DEBUG) {
    printf("Enter cons\n");
  }

  item->link = list;

  if (DEBUG & DB_CONS) {
    printf("cons\n");
    dbugprinttok(item);
    dbugprinttok(list);
  }

  return item;
}

bool boolop(TOKEN op) {

  bool cond = (14 <= op->whichval) && (op->whichval <= 16);
  if (cond) op->basicdt = BOOLETYPE;

  /* if (DEBUG) {
    printf("boolop\n");
    dbugprinttok(op);
  } */

  return cond;
}

bool numop(TOKEN op) {
  bool a = (1 <= op->whichval) && (op->whichval <= 5);
  bool b = (6 <= op->whichval) && (op->whichval <= 11);

  if (a)
    op->basicdt = INTEGER;
  if (b)
    op->basicdt = BOOLETYPE;

  /* if (DEBUG) {
    printf("numop\n");
    dbugprinttok(op);
  } */

  return (a || b);
}

TOKEN unaryop(TOKEN op, TOKEN lhs) {

  if (DEBUG) {
    printf("Enter unarop\n");
  }

  op->operands = lhs;
  op->basicdt = lhs->basicdt;
  lhs->link = NULL;

  if (DEBUG) {
    printf("unaryop\n");
    dbugprinttok(op);
    dbugprinttok(lhs);
  }

  return op;
}

TOKEN makefix(TOKEN tok) {

  if (DEBUG) {
    printf("Enter makefix\n");
  }

  tok->basicdt = INTEGER;
  if (tok->tokentype == NUMBERTOK)
    tok->intval = (int) tok->realval;
  else
    tok = unaryop(makeop(FIXOP), tok);

  if (DEBUG) {
    printf("makefix\n");
    dbugprinttok(tok);
  }

  return tok;
}

TOKEN makefloat(TOKEN tok) {

  if (DEBUG) {
    printf("Enter makefloat\n");
  }

  TOKEN val = tok;

  if (tok->tokentype == NUMBERTOK)
    tok->realval = (double) tok->intval;
  else
    tok = unaryop(makeop(FLOATOP), tok);

  tok->basicdt = REAL;

  if (DEBUG) {
    printf("makefloat\n");
    dbugprinttok(tok);
  }

  return tok;
}

TOKEN makesubrange(TOKEN tok, int low, int high) {

  if (DEBUG) {
    printf("Enter makesubrange\n");
  }

  SYMBOL sym = symalloc();
  sym->kind = SUBRANGE;
  sym->lowbound = low;
  sym->highbound = high;
  /* sym->size = high - low + 1; */

  tok->symtype = sym;

  if (DEBUG) {
    printf("makesubrange\n");
    dbugprinttok(tok);
  }

  return tok;
}

TOKEN typewr(TOKEN tok, int basicdt) {

  if (DEBUG) {
    printf("Enter typewr\n");
  }

  switch (basicdt) {

    case INTEGER:
      if (tok->basicdt != INTEGER)
        return makefix(tok);
      break;

    case REAL:
      if (tok->basicdt != REAL)
        return makefloat(tok);
      break;

  }

  if (DEBUG) {
    printf("typewr\n");
    dbugprinttok(tok);
  }

  return tok;
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {

  if (DEBUG) {
    printf("Enter binop\n");
  }

  if (!boolop(op) && numop(op) && op->basicdt == INTEGER) {
    op->basicdt = (lhs->basicdt > rhs->basicdt)? lhs->basicdt : rhs->basicdt;
    if (op->basicdt != lhs->basicdt) lhs = typewr(lhs, op->basicdt);
    if (op->basicdt != rhs->basicdt) rhs = typewr(rhs, op->basicdt);
  }

  op->operands = lhs;          /* link operands to operator       */
  lhs->link = rhs;             /* link second operand to first    */
  rhs->link = NULL;            /* terminate operand list          */

  if (DEBUG & DB_BINOP) {
    printf("binop\n");
    dbugprinttok(op);
    /* dbugprinttok(lhs); */
    dbugprinttok(rhs);
  }

  return op;
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart) {

  if (DEBUG) {
    printf("Enter makeif\n");
  }

  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
  tok->whichval = IFOP;

  if (elsepart != NULL)
    elsepart->link = NULL;

  thenpart->link = elsepart;
  exp->link = thenpart;
  tok->operands = exp;

  if (DEBUG & DB_MAKEIF) {
    printf("makeif\n");
    dbugprinttok(tok);
    dbugprinttok(exp);
    dbugprinttok(thenpart);
    dbugprinttok(elsepart);
  }

  return tok;
}

TOKEN makeprogn(TOKEN tok, TOKEN statements) {

  if (DEBUG) {
    printf("Enter makeprogn\n");
  }

  if (statements != NULL && statements->tokentype == OPERATOR && statements->whichval == PROGNOP) {
    TOKEN cur = statements->operands;
    while (cur->link != NULL)
      cur = cur->link;
    cons(cur, statements->link);
    statements = statements->operands;
  }

  tok->tokentype = OPERATOR;
  tok->whichval = PROGNOP;
  tok->operands = statements;

  if (DEBUG & DB_MAKEPROGN) {
    printf("makeprogn\n");
    dbugprinttok(tok);
    dbugprinttok(statements);
  }

  return tok;
}

int wordaddress(int n, int wordsize) {
  return ((n + wordsize - 1) / wordsize) * wordsize;
}
 
void yyerror (char const *s) {
  fprintf (stderr, "%s\n", s);
}

void instconst(TOKEN idtok, TOKEN consttok) {

  if (DEBUG) {
    printf("Enter instconst\n");
  }

  SYMBOL sym = insertsym(idtok->stringval);
  sym->kind = CONSTSYM;

  if (consttok->tokentype == STRINGTOK) {
    sym->basicdt = STRINGTYPE;
    strcpy(sym->constval.stringconst, consttok->stringval);
  }

  if (consttok->tokentype == NUMBERTOK) {
    sym->basicdt = consttok->basicdt;
    if (consttok->basicdt == INTEGER)
      sym->constval.intnum = consttok->intval;
    if (consttok->basicdt == REAL)
      sym->constval.realnum = consttok->realval;
  }

  if (DEBUG) {
    printf("instconst\n");
    dbugprinttok(idtok);
    dbugprinttok(consttok);
  }

}

void instvars(TOKEN idlist, TOKEN typetok) {

  if (DEBUG) {
    printf("Enter instvars\n");
  }

  SYMBOL sym, typesym; int align;
  typesym = typetok->symtype;
  align = alignsize(typesym);
  
  while ( idlist != NULL ) {
    sym = insertsym(idlist->stringval);
    sym->kind = VARSYM;
    sym->offset = wordaddress(blockoffs[blocknumber], align);
    sym->size = typesym->size;
    blockoffs[blocknumber] = sym->offset + sym->size;
    sym->datatype = typesym;
    sym->basicdt = typesym->basicdt;
    idlist = idlist->link;
  }

  if (DEBUG) {
    printf("instvars\n");
    dbugprinttok(idlist);
    dbugprinttok(typetok);
  }

}

void insttype(TOKEN typename, TOKEN typetok) {

  if (DEBUG) {
    printf("Enter insttype\n");
  }

  SYMBOL typesym = typetok->symtype;
  SYMBOL sym = searchst(typename->stringval);
  if (sym == NULL)
    sym = insertsym(typename->stringval);

  sym->kind = TYPESYM;
  sym->datatype = typesym;
  if(typesym != NULL) {
    sym->size = typesym->size;
    sym->basicdt = typesym->basicdt;
  }

  if (DEBUG) {
    printf("insttype\n");
    dbugprinttok(typename);
    dbugprinttok(typetok);
  }

}

void instlabel (TOKEN num) {

  if (DEBUG) {
    printf("Enter instlabel\n");
  }

  TOKEN lbl = makelabel();
  labels[lbl->operands->intval] = num->intval;

  if (DEBUG) {
    printf("instlabel\n");
    dbugprinttok(num);
  }
}

TOKEN fieldconc (TOKEN lista, TOKEN listb) {

  if (DEBUG) {
    printf("Enter fieldconc\n");
  }

  SYMBOL iter;
  int align = alignsize(listb->symtype);
  int off = wordaddress(lista->symentry->size, align);

  iter = listb->symentry->link;
  while (iter != NULL) {
    iter->offset += off;
    iter = iter->link;
  }

  iter = lista->symentry->link;
  while (iter->link != NULL) {
    iter = iter->link;
  }

  iter->link = listb->symentry->link;
  lista->symentry->size = off + listb->symentry->size;

  if (DEBUG) {
    printf("fieldconc\n");
    dbugprinttok(lista);
    dbugprinttok(listb);
  }

  return lista;
}

TOKEN instfields(TOKEN idlist, TOKEN typetok) {

  if (DEBUG) {
    printf("Enter instfields\n");
  }

  SYMBOL sym, typesym;
  typesym = typetok->symtype;

  int size = wordaddress(typesym->size, alignsize(typesym));
  int offset = 0;
  int cnt = 0;

  SYMBOL head = symalloc();
  SYMBOL prev = head;
  
  while ( idlist != NULL ) {
    sym = makesym(idlist->stringval);
    prev->link = sym;

    sym->kind = VARSYM;
    sym->offset = offset;
    sym->size = typesym->size;
    sym->datatype = typesym;
    sym->basicdt = typesym->basicdt;

    offset += size;
    idlist = idlist->link;
    prev = prev->link;
    cnt += 1;
  }

  prev->link = NULL;
  head->size = cnt*size;
  typetok->symentry = head;

  if (DEBUG) {
    printf("instfields\n");
    dbugprinttok(idlist);
    dbugprinttok(typetok);
  }

  return typetok;
}

TOKEN fixrec(TOKEN rec, TOKEN list) {

  if (DEBUG) {
    printf("Enter fixrec\n");
  }

  SYMBOL sym = list->symentry;
  list->symentry = NULL;

  sym->kind = RECORDSYM;
  sym->size = wordaddress(sym->size, alignsize(sym));
  sym->datatype = sym->link;
  sym->link = NULL;

  rec->symtype = sym;

  if (DEBUG) {
    printf("fixrec\n");
    dbugprinttok(rec);
    dbugprinttok(list);
  }

  return rec;
}

TOKEN fixpoint(TOKEN pt, TOKEN id) {

  if (DEBUG) {
    printf("Enter fixpoint\n");
  }

  SYMBOL tgt = searchst(id->stringval);
  if (tgt == NULL)
    tgt = insertsym(id->stringval);

  SYMBOL ptr = symalloc();
  ptr->kind = POINTERSYM;
  ptr->basicdt = POINTER;
  ptr->datatype = tgt;
  ptr->size = 8;

  pt->symtype = ptr;

  if (DEBUG) {
    printf("fixpoint\n");
    dbugprinttok(pt);
    dbugprinttok(id);
  }

  return pt;
}

TOKEN fixenum(TOKEN tok, TOKEN idlist) {

  if (DEBUG) {
    printf("Enter fixenum\n");
  }

  int cnt = 0;
  while ( idlist != NULL ) {
    instconst(idlist, makeintc(cnt));
    cnt += 1;
    idlist = idlist->link;
  }

  if (DEBUG) {
    printf("fixenum\n");
    dbugprinttok(tok);
    dbugprinttok(idlist);
  }

  TOKEN tmp = makesubrange(tok, 0, cnt-1);
  tmp->symtype->size = 4;
  return tmp;
}

TOKEN fixarray(TOKEN stplist, TOKEN type) {

  if (DEBUG) {
    printf("Enter fixarray\n");
  }

  SYMBOL inf, cur, prev, head, typesym;
  TOKEN iter;
  int tot;

  typesym = type->symtype;
  tot = typesym->size;

  head = symalloc();
  
  prev = head;
  iter = stplist;
  while ( iter != NULL ) {
    cur = symalloc();
    inf = iter->symtype;

    if (inf->kind != SUBRANGE) {
      inf = inf->datatype;
    }

    cur->kind = ARRAYSYM;
    cur->lowbound = inf->lowbound;
    cur->highbound = inf->highbound;

    prev->datatype = cur;
    tot *= inf->highbound - inf->lowbound + 1;

    iter = iter->link;
    prev = prev->datatype;
  }
  prev->datatype = typesym;

  prev = head;
  iter = stplist;
  while ( iter != NULL ) {
    cur = prev->datatype;
    cur->size = tot;
    tot /= cur->highbound - cur->lowbound + 1;

    iter = iter->link;
    prev = prev->datatype;
  }

  if (DEBUG) {
    printf("fixarray\n");
    dbugprinttok(stplist);
    dbugprinttok(type);
  }

  stplist->symtype = head->datatype;
  /* stplist->symtype->basicdt = POINTER; */

  return stplist;
}

TOKEN fixgoto(TOKEN labeltok) {

  if (DEBUG) {
    printf("Enter fixgoto\n");
  }

  int tgt = labeltok->intval;

  for (int i = 0; i < 50; i++) {
    /* printf("%d ", labels[i]); */
    if (labels[i] == tgt)
      return makegoto(i);
  }
  printf("\n");

  if (DEBUG) {
    printf("fixgoto\n");
    dbugprinttok(labeltok);
  }

  return NULL;
}

TOKEN fixlabel(TOKEN labeltok, TOKEN statement) {

  if (DEBUG) {
    printf("Enter fixlabel\n");
  }

  int tgt = labeltok->intval;
  TOKEN lbl = NULL;

  for (int i = 0; i < 50; i++) {
    if (labels[i] == tgt) {
      lbl =  createlabel(i);
      break;
    }
  }

  if (lbl == NULL)
    return NULL;


  if (DEBUG) {
    printf("fixlabel\n");
    dbugprinttok(labeltok);
  }

  return makeprogn(labeltok, cons(lbl, statement));
}

TOKEN findid(TOKEN tok) {

  if (DEBUG) {
    printf("Enter findid\n");
  }

  SYMBOL sym = searchst(tok->stringval);

  if (sym == NULL)
    return NULL;

  if (sym->kind == CONSTSYM) {
    if (sym->basicdt == INTEGER)
      return makeintc(sym->constval.intnum);
    if (sym->basicdt == REAL)
      return makerealc(sym->constval.realnum);
    if (sym->basicdt == STRINGTYPE)
      return makestringc(sym->constval.stringconst);
  }

  tok->symentry = sym;
  SYMBOL typ = sym->datatype;
  tok->symtype = typ;
  /* tok->intval = 0; */

  if ( typ->kind == BASICTYPE || typ->kind == POINTERSYM)
    tok->basicdt = typ->basicdt;

  if (DEBUG) {
    printf("findid\n");
    dbugprinttok(tok);
  }

  return tok;
}

TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement) {

  if (DEBUG) {
    printf("Enter makefor\n");
  }

  TOKEN var = asg->operands;
  TOKEN lbl = makelabel();
  int lbl_num = lbl->operands->intval;

  // Start if-statement (stored in tokc)
  TOKEN check = binop(makeop(LEOP), copytok(var), endexpr);
  TOKEN crgo = makegoto(lbl_num);

  TOKEN incr = binop(makeop(PLUSOP), copytok(var), makeintc(1));
  TOKEN iter = binop(makeop(ASSIGNOP), copytok(var), incr);

  tokb = makeprogn(tokb, cons(statement, cons(iter, crgo)));
  tokc = makeif(tokc, check, tokb, NULL);
  // End if-statement

  tok = makeprogn(tok, cons(asg, cons(lbl, tokc)));

  if (DEBUG) {
    printf("makefor\n");
    dbugprinttok(tok);
    dbugprinttok(asg);
    dbugprinttok(tokb);
    dbugprinttok(endexpr);
    dbugprinttok(tokc);
    dbugprinttok(statement);
  }

  return tok;
}

TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {

  if (DEBUG) {
    printf("Enter makewhile\n");
  }

  TOKEN lbl = makelabel();

  int lbl_num = lbl->operands->intval;
  TOKEN crgo = makegoto(lbl_num);

  tokb = makeprogn(tokb, cons(statement, crgo));
  tok = makeif(tok, expr, tokb, NULL);

  if (DEBUG) {
    printf("makewhile\n");
    dbugprinttok(tok);
    dbugprinttok(expr);
    dbugprinttok(tokb);
    dbugprinttok(statement);
  }

  return makeprogn(talloc(), cons(lbl, tok));
}

TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {

  if (DEBUG) {
    printf("Enter makerepeat\n");
  }

  TOKEN lbl = makelabel();
  int lbl_num = lbl->operands->intval;

  tokb = makeif(tokb, expr, makeprogn(talloc(), NULL), makegoto(lbl_num));
  tok = makeprogn(tok, cons(makeprogn(talloc(), cons(lbl, statements)), tokb));

  if (DEBUG) {
    printf("makerepeat\n");
    dbugprinttok(tok);
    dbugprinttok(statements);
    dbugprinttok(tokb);
    dbugprinttok(expr);
  }

  return tok;
}

TOKEN dopoint(TOKEN var, TOKEN tok) {

  if (DEBUG) {
    printf("Enter dopoint\n");
  }

  tok = unaryop(makeop(POINTEROP), var);

  tok->symtype = var->symtype->datatype->datatype;
  tok->basicdt = var->symtype->datatype->basicdt;
  return tok;
}

TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {

  if (DEBUG) {
    printf("Enter reducedot\n");
  }

  // Pointer to first element in record
  SYMBOL fld = var->symtype->datatype->datatype;
  /* int off = 0; */

  while (fld != NULL && strcmp(fld->namestring, field->stringval)) {
    /* printf("%s\n", fld->namestring); */
    /* printf("%s: %d\n", fld->namestring, fld->offset); */
    /* off += fld->size; */
    fld = fld->link;
  }
  /* printf("END: %s: %d\n", fld->namestring, fld->offset); */

  TOKEN res = forcearef(var, makeintc(fld->offset));
  /* assert(fld); */
  res->symtype = fld->datatype;
  res->basicdt = fld->datatype->basicdt;

  if (DEBUG) {
    printf("reducedot\n");
    dbugprinttok(res);
    dbugprinttok(field);
  }

  return res;
}

TOKEN forcearef(TOKEN var, TOKEN off) {

  if (var->tokentype == OPERATOR && var->whichval == AREFOP) {
    var = combine_off(var, off);
  } else {
    var = binop(makeop(AREFOP), var, off);
  }
  return var;
}

TOKEN combine_off(TOKEN aref, TOKEN a) {

  TOKEN off = aref->operands->link;

  bool aint = a->tokentype == NUMBERTOK && a->basicdt == INTEGER;

  if (off->operands == NULL) {
    bool oint = off->tokentype == NUMBERTOK && off->basicdt == INTEGER;
    if (oint) {
      off->intval += a->intval;
    } else {
      aref->operands->link = binop(makeop(PLUSOP), off, a);
    }
    return aref;
  }

  bool refint = off->operands->tokentype == NUMBERTOK && off->operands->basicdt == INTEGER;

  if (aint && refint) {
    off->operands->intval += a->intval;

  } else if (refint) {
    off->operands->link = binop(makeop(PLUSOP), off->operands->link, a);

  } else {
    off->operands = binop(makeop(PLUSOP), off->operands, a);
  }

  return aref;
}

/* TOKEN combine_off(TOKEN a, TOKEN b) {

  bool aint = a->tokentype == NUMBERTOK && a->basicdt = INTEGER;
  bool bint = b->tokentype == NUMBERTOK && b->basicdt = INTEGER

  if (aint && bint) {
    return makeintc(a->intval + b->intval);
  }

  int off = 0
  off += (aint)? a->intval : a->operand->intval;
  off += (bint)? b->intval : b->operand->intval;

  TOKEN offset = makeintc(off);
  TOKEN tmp = NULL

  if (!aint && !bint)
    tmp = binop(makeop(PLUSOP), a->operand->link, a->operand->link);
  else
    tmp = (!aint)? a->operand->link : a->operand->link;
    
  return binop(makeop(PLUSOP), offset, tmp);

} */

TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {

  if (DEBUG) {
    printf("Enter arrayref\n");
  }

  SYMBOL sym = arr->symtype;
  int elem = sym->datatype->size;
  int nsize = (-1) * elem * sym->lowbound;

  TOKEN off = NULL;
  if (subs->tokentype == NUMBERTOK && subs->basicdt == INTEGER) {
    off = makeintc(nsize + subs->intval*elem);
  } else {
    off = binop(makeop(PLUSOP), makeintc(nsize), binop(makeop(TIMESOP), makeintc(elem), copytok(subs)));
  }

  TOKEN tmp = forcearef(arr, off);
  tmp->symtype = sym->datatype;
  tmp->basicdt = sym->basicdt;

  if (subs->link != NULL) {
    tmp = arrayref(tmp, tok, subs->link, tokb);
  }

  return tmp;
}

/* TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {

  int res = 0;

  TOKEN var = NULL;

  TOKEN iter = subs;
  SYMBOL inf = arr->symtype;

  while(iter != NULL) {

    SYMBOL cur = iter->symtype;
    int nsize = inf->datatype->size;
    res -= nsize * inf->lowbound;

    printf("Here\n");
    if (cur != NULL) {

      TOKEN tmp = binop(makeop(TIMESOP), makeintc(nsize), iter);

      if (var == NULL) {
        var = tmp;
      } else {
        var = binop(makeop(PLUSOP), var, tmp);
      }

    } else {
      res += nsize * iter->intval;
    }

    iter = iter->link;
    inf = inf->datatype;
  }

  if (var != NULL) {
    var = binop(makeop(PLUSOP), makeintc(res), var);
  } else {
    var = makeintc(res);
  }

  arr = binop(makeop(AREFOP), arr, makeintc(off));
  arr->symtype = inf;
  arr->basicdt = inf->basicdt;

  if (DEBUG) {
    printf("arrayref\n");
    dbugprinttok(arr);
    dbugprinttok(tok);
    dbugprinttok(subs);
    dbugprinttok(tokb);
  }

  return var;

} */

TOKEN createlabel(int c) {
  TOKEN lbl = talloc();
  lbl->tokentype = OPERATOR;
  lbl->whichval = LABELOP;
  lbl->operands = makeintc(c);
  return lbl;
}

TOKEN makelabel() {
  TOKEN lbl = createlabel(labelnumber);
  labelnumber++;
  return lbl;
}

TOKEN makeintc(int num) {
  TOKEN tok = talloc();
  tok->tokentype = NUMBERTOK;
  tok->basicdt = INTEGER;
  tok->intval = num;
  return tok;
}

TOKEN makerealc(double num) {
  TOKEN tok = talloc();
  tok->tokentype = NUMBERTOK;
  tok->basicdt = REAL;
  tok->realval = num;
  return tok;
}

TOKEN makestringc(char *num) {
  TOKEN tok = talloc();
  tok->tokentype = STRINGTOK;
  tok->basicdt = STRINGTYPE;
  strcpy(num, tok->stringval);
  return tok;
}

TOKEN makeop(int opnum) {
  TOKEN tok = talloc();
  tok->tokentype = OPERATOR;
  tok->whichval = opnum;
  return tok;
}

TOKEN makegoto(int label) {
  TOKEN tok = talloc();
  tok->tokentype = OPERATOR;
  tok->whichval = GOTOOP;
  tok->operands = makeintc(label);
  return tok;
}

TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  SYMBOL tmp = searchst(fn->stringval);

  tok->basicdt = tmp->datatype->basicdt;
  tok->tokentype = OPERATOR;
  tok->whichval = FUNCALLOP;
  tok->operands = fn;

  if (!strcmp(fn->stringval, "new")) {
    fn->link = makeintc(args->symtype->datatype->datatype->size);
    tok = binop(makeop(ASSIGNOP), args, tok);
  } else {
    if (!strcmp(fn->stringval, "writeln")) {
      if (args->basicdt == INTEGER)
        strcpy(fn->stringval, "writelni");
      if (args->basicdt == REAL)
        strcpy(fn->stringval, "writelnf");
    } 
    fn->link = args;
  }

  if (DEBUG) {
    printf("makefuncall\n");
    dbugprinttok(tok);
    dbugprinttok(fn);
    dbugprinttok(args);
  }

  return tok;
}

TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
  TOKEN tok = makeop(PROGRAMOP);
  tok->operands = name;
  name->link = makeprogn(talloc(), args);
  name->link->link = statements;

  if (DEBUG) {
    printf("makeprogram\n");
    dbugprinttok(name);
    dbugprinttok(args);
    dbugprinttok(statements);
  }

  return tok;
}

TOKEN findtype(TOKEN tok) {

  tok->symtype = searchst(tok->stringval);

  if (DEBUG) {
    printf("findtype\n");
    dbugprinttok(tok);
  }

  return tok;
}

TOKEN copytok(TOKEN tok) {
  TOKEN cpy = talloc();
  memcpy(cpy, tok, sizeof(struct tokn));
  cpy->link = NULL;
  cpy->operands = NULL;

  if (DEBUG) {
    printf("findtype\n");
    dbugprinttok(tok);
  }

  return cpy;
}

int main(void) {
  int res;
  initsyms();
  res = yyparse();
  /* printstlevel(1); */

  /* dbugprinttok(parseresult); */
  /* ppexpr(parseresult); */
  gencode(parseresult, blockoffs[blocknumber], labelnumber);
}
