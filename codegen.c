/* codgen.c       Generate Assembly Code for x86         07 May 18   */

/* Copyright (c) 2018 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>

#include "token.h"
#include "symtab.h"
#include "lexan.h"
#include "genasm.h"
#include "codegen.h"
#include "pprint.h"

void genc(TOKEN code);
int genop1(int OP, int reg, int type);
int genop2(int OP, int type);
int genjmp(int op);
int tmove(int basicdt, int storereg, int reg);

bool onearg(TOKEN code);

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */

bool registers[FMAX];
int comparisons[6];

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

   Add this line to the end of your main program:
   gencode(parseresult, blockoffs[blocknumber], labelnumber);
   The generated code is printed out; use a text editor to extract it for
   your .s file.
*/

void gencode(TOKEN pcode, int varsize, int maxlabel) {
   TOKEN name, code;
   name = pcode->operands;
   code = name->link->link;
   nextlabel = maxlabel + 1;
   stkframesize = asmentry(name->stringval,varsize);
   genc(code);
   asmexit(name->stringval);
}

/* Trivial version: always returns RBASE + 0 */
/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */
int getreg(int kind) {

   switch (kind) {

      case WORD: case ADDR:
         for (int i = RBASE; i <= RMAX; i++) {
            if (!registers[i]) {
               used(i);
               return i;
            }
         }
         assert(0);
      break;

      case FLOAT:
         for (int i = FBASE; i <= FMAX; i++) {
            if (!registers[i]) {
               used(i);
               return i;
            }
         }
         assert(0);
      break;

   }
   return -1;
}

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code) {

   int num, reg, label, offs, type, inst, op, lreg, rreg;
   double fnum;
   char *str;

   TOKEN lhs, rhs;
   SYMBOL sym;

   if (DEBUGGEN) {
      printf("genarith\n");
      dbugprinttok(code);
   };

   switch ( code->tokentype ) {

      case NUMBERTOK:
         switch (code->basicdt) {

            case INTEGER:
               num = code->intval;
               reg = getreg(WORD);
               if (num >= MINIMMEDIATE && num <= MAXIMMEDIATE)
                  asmimmed(MOVL, num, reg);
            break;

            case REAL:
               fnum = code->realval;
               reg = getreg(FLOAT);
               label = nextlabel++;
               makeflit(fnum,label);
               asmldflit(MOVSD, label, reg);
            break;

         }
      break;

      case IDENTIFIERTOK:

         sym = code->symentry;
         offs = sym->offset - stkframesize;

         switch (code->basicdt) {

            case INTEGER:
               reg = getreg(WORD);
               asmld(MOVL, offs, reg, code->stringval);
            break;

            case REAL:
               reg = getreg(FLOAT);
               asmld(MOVSD, offs, reg, code->stringval);
            break;

            case POINTER:
               reg = getreg(ADDR);
               asmld(MOVQ, offs, reg, code->stringval);
            break;

         }
      break;

      case OPERATOR:

         op = code->whichval;

         if (op == FUNCALLOP) {
            reg = genfun(code);
            break;
         }

         if (op == AREFOP) {
            reg = genaref(code, -1);
            break;
         }

         lhs = code->operands;
         lreg = genarith(lhs);

         if (!onearg(code)) {
            rhs = lhs->link;

            if (rhs->tokentype == OPERATOR && rhs->whichval == FUNCALLOP) {
               savereg(lreg);
            }

            rreg = genarith(rhs);

            if (rhs->tokentype == OPERATOR && rhs->whichval == FUNCALLOP) {
               lreg = getreg(FLOAT);
               restorereg(lreg);
            }

            // printf("ARITH: %d\n", code->basicdt);
            type = (lhs->basicdt == INTEGER)? WORD : FLOAT;
            inst = genop2(op, type);
            asmrr(inst, rreg, lreg);
            unused(rreg);

         } else {
            type = (lhs->basicdt == INTEGER)? WORD : FLOAT;
            lreg = genop1(op, lreg, type);
         }

         reg = lreg;
         
      break;

      case STRINGTOK:
         str = code->stringval;
         reg = RDI;
         label = nextlabel++;
         makeblit(str, label);
         asmlitarg(label, reg);
      break;

   };

   return reg;
}


/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code) {
   TOKEN tok, lhs, rhs, cmp, thn, els;
   int reg, offs, jmp, l1, l2, tmp;
   SYMBOL sym;

   if (DEBUGGEN) {
      printf("genc\n");
      dbugprinttok(code);
   };

   if (code->tokentype != OPERATOR) {
      printf("Bad code token");
      dbugprinttok(code);
   };
     
   switch ( code->whichval ) {

      case PROGNOP:
         tok = code->operands;
         while ( tok != NULL ) {
            genc(tok);
            tok = tok->link;
         };
      break;

      case ASSIGNOP:
         lhs = code->operands;
         rhs = lhs->link;
         reg = genarith(rhs);                /* generate rhs into a register */
         if (lhs->tokentype == OPERATOR && lhs->whichval == AREFOP) {
            genaref(lhs, reg);
            unused(reg);
            break;
         }
         sym = lhs->symentry;                /* assumes lhs is a simple var  */
         offs = sym->offset - stkframesize;  /* net offset of the var   */
         switch (lhs->symtype->basicdt) {            /* store value into lhs  */
            case INTEGER:
               asmst(MOVL, reg, offs, lhs->stringval);
               unused(reg);
            break;
            case REAL:
               asmst(MOVSD, reg, offs, lhs->stringval);
               unused(reg);
            break;
            case POINTER:
               asmst(MOVQ, reg, offs, lhs->stringval);
               unused(reg);
            break;
         };
         unused(reg);
      break;

      case FUNCALLOP:
         unused(genfun(code));
      break;

      case GOTOOP:
         asmjump(JMP, code->operands->intval);
      break;

      case LABELOP:
         asmlabel(code->operands->intval);
      break;

      case IFOP:

         cmp = code->operands;
         thn = cmp->link;
         els = thn->link;

         tmp = genarith(cmp);
         unused(tmp);
         jmp = genjmp(cmp->whichval);

         l1 = nextlabel++;
         l2 = nextlabel++;

         asmjump(jmp, l1);
         if (els != NULL) genc(els);
         asmjump(JMP, l2);

         asmlabel(l1);
         genc(thn);
         asmlabel(l2);

      break;
    
  };
}

bool onearg(TOKEN code) {
   assert(code->operands);
   return code->operands->link == NULL;
}

int genop2 (int OP, int type) {

   if (type == WORD) {
      switch (OP) {
         case PLUSOP:
            return ADDL;
         case MINUSOP:
            return SUBL;
         case TIMESOP:
            return IMULL;
         case DIVOP:
            return DIVL;
         case EQOP: case NEOP: case LTOP: case LEOP:
         case GTOP: case GEOP:
            return CMPL;
      }
      assert(0);
   }

   if (type == ADDR) {
      switch (OP) {
         case PLUSOP:
            return ADDQ;
         case MINUSOP:
            return SUBQ;
         case TIMESOP:
            return IMULQ;
         case EQOP: case NEOP: case LTOP:
            return CMPQ;
      }
      assert(0);
   }

   if (type == FLOAT) {
      switch (OP) {
         case PLUSOP:
            return ADDSD;
         case MINUSOP:
            return SUBSD;
         case TIMESOP:
            return MULSD;
         case DIVOP:
            return DIVSD;
         case EQOP: case NEOP: case LTOP:
            return CMPSD;
      }
      assert(0);
   }
   return -1;
}

int genop1 (int OP, int reg, int type) {

   int dreg, tmp;

   if (type == WORD) {
      switch (OP) {

         case MINUSOP:
            asmr(NEGL, reg);
         break;

         case FLOATOP:
            dreg = getreg(FLOAT);
            asmfloat(reg, dreg);
            unused(reg);
            return dreg;
         break;

      }
   }

   if (type == ADDR) {
      switch (OP) {
         case MINUSOP:
            asmr(NEGQ, reg);
         break;
      }
   }

   if (type == FLOAT) {
      switch (OP) {
         case MINUSOP:
            tmp = getreg(FLOAT);
            asmfneg(reg, tmp);
            unused(tmp);
         break;
      }
   }

   return reg;
}

int moveop(TOKEN code) {

   switch (code->symtype->basicdt) {

      case INTEGER:
         return MOVL;
      break;

      case REAL:
         return MOVSD;
      break;

      case POINTER:
         return MOVQ;
      break;

   }

   assert(0);
   return -1;
}

int tmove(int basicdt, int storereg, int reg) {
   // assert(sym->kind == BASICTYPE);
   int dreg;

   if (storereg < 0) {

      switch (basicdt) {

         case INTEGER:
            dreg = getreg(WORD);
            asmldrr(MOVL, (-1)*stkframesize, reg, dreg, "\0");
         break;

         case REAL:
            dreg = getreg(FLOAT);
            asmldrr(MOVSD, (-1)*stkframesize, reg, dreg, "\0");
         break;

         case POINTER:
            dreg = getreg(ADDR);
            asmldrr(MOVQ, (-1)*stkframesize, reg, dreg, "\0");
         break;
      }
      return dreg;

   } else {

      switch (basicdt) {

         case INTEGER:
            asmstrr(MOVL, storereg, (-1)*stkframesize, reg, "\0");
         break;

         case REAL:
            asmstrr(MOVSD, storereg, (-1)*stkframesize, reg, "\0");
         break;

         case POINTER:
            asmstrr(MOVQ, storereg, (-1)*stkframesize, reg, "\0");
         break;
      }
      return -1;

   }

}

int genaref(TOKEN code, int storereg) {

   int lreg, rreg, bdt;
   TOKEN lhs, rhs;
   SYMBOL sym;
   
   lhs = code->operands;
   rhs = lhs->link;
   rreg = genarith(rhs);
   asmop(CLTQ);

   if (lhs->tokentype == OPERATOR && lhs->whichval == POINTEROP) {
      lreg = getreg(WORD);
      asmimmed(MOVL, lhs->operands->symtype->offset, lreg);
      // lreg = genarith(lhs->operands);
      // bdt = lhs->basicdt;

   } else {
      lreg = getreg(WORD);
      asmimmed(MOVL, lhs->symtype->offset, lreg);
      // bdt = lhs->symtype->datatype->basicdt;
   }

   asmrr(ADDL, rreg, lreg);
   unused(rreg);

   rreg = tmove(code->basicdt, storereg, lreg);
   unused(lreg);
   return rreg;
}

void clearreg() {
   for (int i = 0; i < FMAX; i++)
      registers[i] = false;
}

void unused(int reg) {
   registers[reg] = false;
}

void used(int reg) {
   registers[reg] = true;
}

int genjmp(int op) {
   switch (op) {
      case EQOP:
         return JE;
      case NEOP:
         return JNE;
      case LTOP:
         return JL;
      case LEOP:
         return JLE;
      case GEOP:
         return JGE;
      case GTOP:
         return JG;
   }
   assert(0);
   return -1;
}

void savereg(int reg) {
   assert (reg >= FBASE);
   asmsttemp(reg);
   unused(reg);
}

void restorereg(int reg) {
   asmldtemp(reg);
   used(reg);
}

int genfun(TOKEN code) {

   TOKEN args;
   int arg, reg;

   args = code->operands->link;
   arg = genarith(args);

   switch (args->basicdt) {

      case INTEGER:
         if (arg != EDI) {
            asmrr(MOVL, arg, EDI);
            unused(arg);
         }
      break;

      case REAL:
         if (arg != XMM0) {
            asmrr(MOVSD, arg, XMM0);
            unused(arg);
         }
      break;
   }

   unused(arg);
   asmcall(code->operands->stringval);

   switch (code->basicdt) {

      case INTEGER:
         reg = EAX;
         // asmrr(MOVL, EAX, reg);
      break;

      case REAL:
         reg = XMM0;
      break;

   }

   used(reg);
   // printf("EXIT\n");
   return reg;
   
}
