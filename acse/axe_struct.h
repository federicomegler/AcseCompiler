/*
 * Andrea Di Biagio
 * Politecnico di Milano, 2007
 *
 * axe_struct.h
 * Formal Languages & Compilers Machine, 2007/2008
 *
 * Fundamental data structures
 */

#ifndef _AXE_STRUCT_H
#define _AXE_STRUCT_H

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "axe_constants.h"
#include "collections.h"

typedef struct t_axe_label
{
   int labelID;      /* label identifier */
   char *name;       /* Name of the label. If NULL, the name will be
                      * automatically generated in the form L<ID>. */
} t_axe_label;

typedef struct t_axe_register
{
   int ID;        /* an identifier of the register */
   int indirect;  /* a boolean value: 1 if the register value is a pointer */
}t_axe_register;

typedef struct t_axe_address
{
   int addr;               /* a Program Counter */
   t_axe_label *labelID;   /* a label identifier */
   int type;               /* one of ADDRESS_TYPE or LABEL_TYPE */
}t_axe_address;

/* A structure that defines the internal data of a `Acse variable' */
typedef struct t_axe_variable
{
   int type;      /* a valid data type @see `axe_constants.h' */
   int isArray;   /* must be TRUE if the current variable is an array */
   int arraySize; /* the size of the array. This information is useful only
                   * if the field `isArray' is TRUE */
   int init_val;  /* initial value of the current variable. Actually it is
                   * implemented as a integer value. `int' is
                   * the only supported type at the moment,
                   * future developments could consist of a modification of
                   * the supported type system. Thus, maybe init_val will be
                   * modified in future. */
   char *ID;               /* variable identifier (should never be a NULL
                            * pointer or an empty string "") */
   t_axe_label *labelID;   /* a label that refers to the location
                            * of the variable inside the data segment */
} t_axe_variable;

/* a symbolic assembly instruction */
typedef struct t_axe_instruction
{
   int opcode;                   /* instruction opcode (for example: ADD) */
   t_axe_register *reg_1;        /* destination register */
   t_axe_register *reg_2;        /* first source register */
   t_axe_register *reg_3;        /* second source register */
   int immediate;                /* immediate value */
   t_axe_address *address;       /* an address operand */
   char *user_comment;           /* if defined it is set to the source code
                                  * instruction that generated the current
                                  * assembly. This string will be written
                                  * into the output code as a comment */
   t_axe_label *labelID;        /* a label associated with the current
                                  * instruction */
}t_axe_instruction;

/* this structure is used in order to define assembler directives.
 * Directives are used in many cases such the definition of variables
 * inside the data segment. Every instance `t_axe_data' contains
 * all the informations about a single directive.
 * An example is the directive .word that is required when the assembler
 * must reserve a word of data inside the data segment. */
typedef struct t_axe_data
{
   int directiveType;      /* the type of the current directive
                            * (for example: DIR_WORD) */
   int value;              /* the value associated with the directive */
   t_axe_label *labelID;   /* label associated with the current data */
}t_axe_data;

typedef struct t_axe_expression
{
   int value;           /* an immediate value or a register identifier */
   int expression_type; /* actually only integer values are supported */
} t_axe_expression;

typedef struct t_axe_declaration
{
   int isArray;           /* must be TRUE if the current variable is an array */
   int arraySize;         /* the size of the array. This information is useful
                           * only if the field `isArray' is TRUE */
   int init_val;          /* initial value of the current variable. */
   char *ID;              /* variable identifier (should never be a NULL pointer
                           * or an empty string "") */
} t_axe_declaration;


typedef struct t_iteration_statement
{

  char* ID;

  int index;

} t_iteration_statement;


typedef struct t_loopdecreasing_statement
{

  t_axe_label* label_loop;

  t_axe_label* label_check;

  t_axe_label* label_end;

} t_loopdecreasing_statement;


typedef struct t_while_statement
{
   t_axe_label *label_condition;   /* this label points to the expression
                                    * that is used as loop condition */
   t_axe_label *label_end;         /* this label points to the instruction
                                    * that follows the while construct */
} t_while_statement;


typedef struct t_try_catch_statement
{

  t_axe_label* label_catch;

  t_axe_label* label_end;

} t_try_catch_statement;


typedef struct t_switch_statement{
  //This is the register that contains the value for the comparison
  int cmp_register;

  //List of all the cases 
  t_list *cases;

  t_axe_label *default_label;
  t_axe_label *switch_end;
  t_axe_label *begin_tests;

}t_switch_statement;

typedef struct t_case_statement{
  //number is the value that will be used for the comparison
  int number;

  t_axe_label *begin_case_label;
} t_case_statement;

typedef struct t_either_or_statement
{
  t_axe_label *label_condition;

  t_axe_label *label_either;

  t_axe_label *label_or;

  t_axe_label *label_end;

}t_either_or_statement;


/* struct per FOR statement */

typedef struct t_for_statement
{
  t_axe_label *label_exit;

  t_axe_label *label_exp;

  t_axe_label *label_code_block;

  t_axe_label *label_epilogue;

} t_for_statement;




/* create a label */
extern t_axe_label *alloc_label(int value);

/* free a label */
extern void free_label(t_axe_label *lab);

/* create an expression */
extern t_axe_expression create_expression(int value, int type);

/* create an instance that will mantain infos about a while statement */
extern t_while_statement create_while_statement();

extern t_either_or_statement create_either_statement();

extern t_try_catch_statement create_try_catch_statement();

/* create an instance that will mantain infor about a for statement */
extern t_for_statement create_for_statement();

extern t_loopdecreasing_statement create_loop_decreasing_statement();

extern t_iteration_statement create_iteration_statement();

/* create an instance of `t_axe_register' */
extern t_axe_register *alloc_register(int ID, int indirect);

/* create an instance of `t_axe_instruction' */
extern t_axe_instruction *alloc_instruction(int opcode);

/* create an instance of `t_axe_address' */
extern t_axe_address *alloc_address(int type, int address, t_axe_label *label);

/* create an instance of `t_axe_data' */
extern t_axe_data *alloc_data(int directiveType, int value, t_axe_label *label);

/* create an instance of `t_axe_variable' */
extern t_axe_variable *alloc_variable(
      char *ID, int type, int isArray, int arraySize, int init_val);

/* finalize an instance of `t_axe_variable' */
extern void free_variable(t_axe_variable *variable);

/* create an instance of `t_axe_variable' */
extern t_axe_declaration *alloc_declaration(
      char *ID, int isArray, int arraySize, int init_val);

/* finalize an instruction info. */
extern void free_Instruction(t_axe_instruction *inst);

/* finalize a data info. */
extern void free_Data(t_axe_data *data);

#endif
