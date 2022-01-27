%{
/*
 * Andrea Di Biagio
 * Politecnico di Milano, 2007
 *
 * Acse.y
 * Formal Languages & Compilers Machine, 2007/2008
 */


/*
 * Extensions by Federico Megler
 * Politecnico di Milano, a.a. 2021/2022
 *
 * Extensions added:
 *        - FOR loop
 *        - shift left statement
 *        - conditional exp
 *        - splice operator
 *        - undo_if statement
 *        - assign array
 *        - either-or statement
 *        - scalar product operator
 *        - reduce array ( red(...) )
 *        - op vector range a = b[ start: end ]
 *        - op. +=
 *        - op [*] (fake multiplication)
 *        - switch case statement
 *        - vec_xor operator
 *        - alias statement
 *        - protect with statement
 *        - merge operator
 *        - cast_array op
 *        - foreach statement (with "every" statement)
 *        - assert statement
 *
*/


/*************************************************************************

                   Compiler for the language LANCE

***************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "axe_struct.h"
#include "axe_engine.h"
#include "symbol_table.h"
#include "axe_target_asm_print.h"
#include "axe_target_transform.h"
#include "axe_errors.h"
#include "collections.h"
#include "axe_expressions.h"
#include "axe_gencode.h"
#include "axe_utils.h"
#include "axe_array.h"
#include "axe_cflow_graph.h"
#include "cflow_constants.h"
#include "axe_transform.h"
#include "axe_reg_alloc.h"
#include "reg_alloc_constants.h"
#include "axe_io_manager.h"

#ifndef NDEBUG
#  include "axe_debug.h"
#endif

/* global variables */
int line_num;        /* this variable will keep track of the
                      * source code line number. Every time that a newline
                      * is encountered while parsing the input file, this
                      * value is increased by 1. This value is then used
                      * for error tracking: if the parser returns an error
                      * or a warning, this value is used in order to notify
                      * in which line of code the error has been found */
int num_error;       /* the number of errors found in the code. This value
                      * is increased by 1 every time a new error is found
                      * in the code. */
int num_warning;     /* As for the `num_error' global variable, this one
                      * keeps track of all the warning messages displayed */

/* errorcode is defined inside "axe_engine.c" */
extern int errorcode;   /* this variable is used to test if an error is found
                         * while parsing the input file. It also is set
                         * to notify if the compiler internal state is invalid.
                         * When the parsing process is started, the value
                         * of `errorcode' is set to the value of the macro
                         * `AXE_OK' defined in "axe_constants.h".
                         * As long as everything (the parsed source code and
                         * the internal state of the compiler) is correct,
                         * the value of `errorcode' is set to `AXE_OK'.
                         * When an error occurs (because the input file contains
                         * one or more syntax errors or because something went
                         * wrong in the machine internal state), the errorcode
                         * is set to a value that is different from `AXE_OK'. */
extern const char *errormsg; /* When errorcode is not equal to AXE_OK,
                         * this variable may be set to an error message to print
                         * if desired. */

extern int cflow_errorcode;   /* As for `errorcode' this value is used to
                        * test if an error occurs during the creation process of
                        * a control flow graph. More informations can be found
                        * analyzing the file `axe_cflow_graph.h'. */

/* program informations */
t_program_infos *program;  /* The singleton instance of `program'.
                            * An instance of `t_program_infos' holds in its
                            * internal structure, all the useful informations
                            * about a program. For example: the assembly
                            * (code and directives); the symbol table;
                            * the label manager (see axe_labels.h) etc. */
t_cflow_Graph *graph;      /* An instance of a control flow graph. This instance
                            * will be generated starting from `program' and will
                            * be used during the register allocation process */

t_reg_allocator *RA;       /* Register allocator. It implements the "Linear
                            * scan" algorithm */

t_io_infos *file_infos;    /* input and output files used by the compiler */


t_list* switchStack = NULL;

t_list* protectStack = NULL;

t_list* iterationStack = NULL;

char* aliased = NULL;
char* alias = NULL;

void vect_copy(char*, char*);
extern int yylex(void);
extern void yyerror(const char*);

%}
%expect 3

/*=========================================================================
                          SEMANTIC RECORDS
=========================================================================*/

%union {
   int intval;
   char *svalue;
   t_axe_expression expr;
   t_axe_declaration *decl;
   t_list *list;
   t_axe_label *label;
   t_while_statement while_stmt;
   t_for_statement for_stmt;
   t_either_or_statement either_stmt;
   t_switch_statement* switch_stmt;
   t_loopdecreasing_statement loopdec_stmt;
}
/*=========================================================================
                               TOKENS
=========================================================================*/
%start program

%token EOF_TOK /* end of file */
%token LBRACE RBRACE LPAR RPAR LSQUARE RSQUARE
%token SEMI PLUS MINUS MUL_OP DIV_OP FAKE_MUL
%token AND_OP OR_OP NOT_OP
%token ASSIGN ASSIGN_PLUS ASSIGNARRAY LT GT SHL_OP SHR_OP EQ NOTEQ LTEQ GTEQ
%token ANDAND OROR
%token COMMA
%token RETURN
%token READ
%token WRITE
%token UNDO
%token DOLLAR
%token AT
%token OR
%token ON
%token RED
%token VEC_XOR
%token CASE DEFAULT BREAK
%token COLON
//%token TRY CATCH
//%token THROW
%token ALIAS
%token MERGE
%token BIT
%token ASSERT

%token <loopdec_stmt> LOOPDEC
%token BY
%token <label> DO
%token <while_stmt> WHILE
%token <for_stmt> FOR
%token <label> IF
%token <label> ELSE
%token <intval> TYPE
%token <svalue> IDENTIFIER
%token <intval> NUMBER
%token <either_stmt> EITHER
%token <switch_stmt> SWITCH
%token <label> PROTECT
%token <label> WITH
%token <while_stmt> FOREACH
%token <while_stmt> EVERY
%token <intval>IN
%token <while_stmt> ITER


%type <expr> exp
%type <decl> declaration
%type <list> declaration_list
%type <label> if_stmt

/*=========================================================================
                          OPERATOR PRECEDENCES
 =========================================================================*/

%left COMMA
%left ASSIGN ASSIGN_PLUS
%left ASSIGNARRAY
%left MERGE
%left ATAT
%left OROR
%left ANDAND
%left OR_OP
%left AND_OP
%left EQ NOTEQ
%left LT GT LTEQ GTEQ
%left SHL_OP SHR_OP
%left MINUS PLUS
%left MUL_OP DIV_OP FAKE_MUL
%right NOT_OP
%right BIT
%left IF ELSE
%left DOLLAR AT
%left EITHER OR ON
%left RED


/*=========================================================================
                         BISON GRAMMAR
=========================================================================*/
%%

/* `program' is the starting non-terminal of the grammar.
 * A program is composed by:
      1. declarations (zero or more);
      2. A list of instructions. (at least one instruction!).
 * When the rule associated with the non-terminal `program' is executed,
 * the parser notifies it to the `program' singleton instance. */
program  : var_declarations statements EOF_TOK
         {
            /* Notify the end of the program. Once called
             * the function `set_end_Program' - if necessary -
             * introduces a `HALT' instruction into the
             * list of instructions. */
            set_end_Program(program);

            /* return from yyparse() */
            YYACCEPT;
         }
;

var_declarations : var_declarations var_declaration   { /* does nothing */ }
                 | /* empty */                        { /* does nothing */ }
;

var_declaration   : TYPE declaration_list SEMI
                  {
                     /* update the program infos by adding new variables */
                     set_new_variables(program, $1, $2);
                  }
;

declaration_list  : declaration_list COMMA declaration
                  {  /* add the new declaration to the list of declarations */
                     $$ = addElement($1, $3, -1);
                     
                     if(!$3->isArray){
                      
                      //alloco una copia
                      char* s = malloc(sizeof(char)*strlen($3->ID)+3);
                      strcpy(s, $3->ID);
                      s = strcat(s, "_i");
                      $$ = addElement($$, alloc_declaration(s, 0, 0, $3->init_val), -1);
                      
                    }
                  }
                  | declaration
                  {
                     /* add the new declaration to the list of declarations */
                     $$ = addElement(NULL, $1, -1);
                     if(!$1->isArray){
                      
                       //alloco una copia
                       char* s = malloc(sizeof(char)*strlen($1->ID)+3);
                       strcpy(s, $1->ID);
                       s = strcat(s, "_i");
                       $$ = addElement($$, alloc_declaration(s, 0, 0, $1->init_val), -1);
                      
                    }
                  }
;

declaration : IDENTIFIER ASSIGN NUMBER
            {
              
               /* create a new instance of declaration */
               $$ = alloc_declaration($1, 0, 0, $3);

               /* test if an `out of memory' occurred */
               if ($$ == NULL)
                  notifyError(AXE_OUT_OF_MEMORY);
            }
            | IDENTIFIER LSQUARE NUMBER RSQUARE
            {
               /* create a new instance of t_axe_declaration */
               $$ = alloc_declaration($1, 1, $3, 0);

                  /* test if an `out of memory' occurred */
               if ($$ == NULL)
                  notifyError(AXE_OUT_OF_MEMORY);
            }
            | IDENTIFIER
            {
               /* create a new instance of t_axe_declaration */
               $$ = alloc_declaration($1, 0, 0, 0);

               /* test if an `out of memory' occurred */
               if ($$ == NULL)
                  notifyError(AXE_OUT_OF_MEMORY);
            }
;

/* A block of code can be either a single statement or
 * a set of statements enclosed between braces */
code_block  : statement                  { /* does nothing */ }
            | LBRACE statements RBRACE   { /* does nothing */ }
;

/* One or more code statements */
statements  : statements statement       { /* does nothing */ }
            | statement                  { /* does nothing */ }
;

/* A statement can be either an assignment statement or a control statement
 * or a read/write statement or a semicolon */
statement   : assign_statement SEMI      { /* does nothing */ }
            | control_statement          { /* does nothing */ }
            | read_write_statement SEMI  { /* does nothing */ }
            | shift_left_array SEMI      { /* does nothing */ }
            | undo_if_statement SEMI     { /* does nothing */ }
            | break_statement SEMI       { /* does nothing */ }
            | vec_xor_statement SEMI     { /* does nothing */ }
            | foreach_every_statement    { /* does nothing */ }
            | alias_statement            { /* does nothing */ }
            | assert_statement SEMI      { /* does nothing */ }
            | protect_with_statement     { /* does nothing */ }
            | SEMI            { gen_nop_instruction(program); }
;

control_statement : if_statement         { /* does nothing */ }
            | while_statement            { /* does nothing */ }
            | for_statement              { /* does nothing */ }
            | either_or_statement SEMI   { /* does nothing */ }
            | do_while_statement SEMI    { /* does nothing */ }
            | return_statement SEMI      { /* does nothing */ }
            | loop_decreasing_statement SEMI { /* does nothing */ }
            | iterate_statement          { /* does nothing */ }
            | switch_statement           { /* does nothing */ }
;

read_write_statement : read_statement  { /* does nothing */ }
                     | write_statement { /* does nothing */ }
;


/* codice aggiunto per il ciclo for */
assignment_list : {}
                | assignment_list COMMA assign_statement { /* does nothing */ }
                | assign_statement                       { /* does nothing */ }
;

assign_statement : IDENTIFIER LSQUARE exp RSQUARE ASSIGN exp
            {
               char* identifier = (alias != NULL && strcmp(alias, $1)==0) ? aliased : $1;

               /* Notify to `program' that the value $6
                * have to be assigned to the location
                * addressed by $1[$3]. Where $1 is obviously
                * the array/pointer identifier, $3 is an expression
                * that holds an integer value. That value will be
                * used as an index for the array $1 */
               storeArrayElement(program, identifier, $3, $6);

               /* free the memory associated with the IDENTIFIER.
                * The use of the free instruction is required
                * because of the value associated with IDENTIFIER.
                * The value of IDENTIFIER is a string created
                * by a call to the function `strdup' (see Acse.lex) */
               free($1);
            }
            | IDENTIFIER ASSIGN exp
            {
               int location;
               int old;

              char* identifier = (alias != NULL && strcmp(alias, $1)==0) ? aliased : $1;
              int index=0;
              int found=0;

               /* in order to assign a value to a variable, we have to
                * know where the variable is located (i.e. in which register).
                * the function `get_symbol_location' is used in order
                * to retrieve the register location assigned to
                * a given identifier.
                * A symbol table keeps track of the location of every
                * declared variable.
                * `get_symbol_location' perform a query on the symbol table
                * in order to discover the correct location of
                * the variable with $1 as identifier */

               /* get the location of the symbol with the given ID. */

               if(getVariable(program, $1)->isArray && iterationStack != NULL){
                      int len = getLength(iterationStack);
                      int i=0;
                      while(i<len){
                        t_iteration_statement* iter = ((t_iteration_statement*)LDATA(getElementAt(iterationStack, i)));
                        if(strcmp($1, iter->ID)==0){
                          location = loadArrayElement(program, iter->ID, create_expression(iter->index, REGISTER));
                          index = iter->index;
                          found =1;
                          break;
                      }
                      i=i+1;
                    }
                }
                else{

                  location = get_symbol_location(program, identifier, 0);
                  old = get_symbol_location(program, strcat(identifier, "_i"),0);
                  gen_add_instruction(program, old, REG_0, location, CG_DIRECT_ALL);
                  if ($3.expression_type == IMMEDIATE)
                    gen_move_immediate(program, location, $3.value);
                  else
                    gen_add_instruction(program,
                                        location,
                                        REG_0,
                                        $3.value,
                                        CG_DIRECT_ALL);

                }

                  if(found == 1){
                    if ($3.expression_type == IMMEDIATE)
                      gen_move_immediate(program, location, $3.value);
                    else
                      gen_add_instruction(program, location, REG_0, $3.value, CG_DIRECT_ALL);
                    //TODO fix this assignment
                    storeArrayElement(program, $1,create_expression(index, IMMEDIATE), create_expression(location, REGISTER));
               }

               
               /* free the memory associated with the IDENTIFIER */
               free($1);
            }
            | IDENTIFIER ASSIGNARRAY IDENTIFIER
            {
              t_axe_variable* var1 =  (alias != NULL && strcmp(alias, $1) == 0) ? getVariable(program, aliased) : getVariable(program, $1);
              t_axe_variable* var2 =  (alias != NULL && strcmp(alias, $3) == 0) ? getVariable(program, aliased) : getVariable(program, $3);

              if(var1 == NULL || var2 == NULL || !var1->isArray || !var2->isArray)
                notifyError(AXE_INVALID_VARIABLE);

              if(var1->arraySize > var2->arraySize){
                //loop
                t_axe_expression min = create_expression(gen_load_immediate(program, var2->arraySize), REGISTER);
                t_axe_expression index = create_expression(gen_load_immediate(program, 0), REGISTER);
                t_axe_expression max = create_expression(gen_load_immediate(program, var1->arraySize), REGISTER);
               
                t_axe_label* label_cond = assignNewLabel(program);
                t_axe_label* label_zeros = newLabel(program);
                t_axe_label* label_end = newLabel(program);

                handle_binary_comparison(program, index, min, _LT_);
                gen_beq_instruction(program, label_zeros, 0);
                
                int elem_array2 = loadArrayElement(program, var2->ID, index);
                storeArrayElement(program, var1->ID, index, create_expression(elem_array2, REGISTER));
                gen_addi_instruction(program, index.value, index.value, 1);
                gen_bt_instruction(program, label_cond, 0);

                assignLabel(program, label_zeros);
                
                handle_binary_comparison(program, index, max, _LT_);
                gen_beq_instruction(program, label_end, 0);

                storeArrayElement(program, var1->ID, index, create_expression(0,IMMEDIATE));
                gen_addi_instruction(program, index.value, index.value, 1);
                gen_bt_instruction(program, label_zeros, 0);

                assignLabel(program, label_end);
              }
              else{
                t_axe_expression min = create_expression(gen_load_immediate(program, var1->arraySize), REGISTER);
                t_axe_expression index = create_expression(gen_load_immediate(program, 0), REGISTER);
                
                t_axe_label* label_cond = assignNewLabel(program);
                t_axe_label* label_end = newLabel(program);

                handle_binary_comparison(program, index, min, _LT_);
                gen_beq_instruction(program, label_end, 0);
                
                int elem_array2 = loadArrayElement(program, var2->ID, index);
                storeArrayElement(program, var1->ID, index, create_expression(elem_array2, REGISTER));
                gen_addi_instruction(program, index.value, index.value, 1);
                gen_bt_instruction(program, label_cond, 0);

                assignLabel(program, label_end);
                
              }

              free($1);
              free($3);
            }
            | IDENTIFIER ASSIGN_PLUS exp
            {
              int destination = (alias != NULL && strcmp(alias, $1) == 0) ? get_symbol_location(program, aliased, 0) : get_symbol_location(program, $1, 0);


              if($3.expression_type == IMMEDIATE){
                gen_addi_instruction(program, destination, destination, $3.value);
              }
              else{
                gen_add_instruction(program, destination, destination, $3.value, CG_DIRECT_ALL);
              }

              free($1);
            }
            | IDENTIFIER ASSIGN IDENTIFIER LSQUARE NUMBER COLON NUMBER RSQUARE
            {
              
              char* id1 = ( alias != NULL && strcmp(alias, $1)==0) ? aliased : $1;
              char* id2 = (alias != NULL && strcmp(alias, $3)==0) ? aliased : $3;
              
              t_axe_variable* target = getVariable(program, id1);
              t_axe_variable* source = getVariable(program, id2);

              if(target == NULL || source == NULL || !source->isArray || !target->isArray)
                notifyError(AXE_INVALID_VARIABLE);
              
              int start = $5;
              int stop = $7;
              
              int max = start >= stop ? start : stop;

              if( max > source->arraySize - 1)
                notifyError(AXE_INVALID_ARRAY_SIZE);
              
              if(start > stop){
                int interval = (source->arraySize - start) + stop + 1;
                if(interval > target->arraySize)
                  notifyError(AXE_INVALID_ARRAY_SIZE);



              if (strcmp(id1, id2) == 0){
                char* copy_var_id = (char*) malloc((strlen(id2)+4)*sizeof(char));
                strcpy(copy_var_id, id1);
                strcat(copy_var_id, "_axe");

                t_axe_variable* copy_var = getVariable(program, copy_var_id);

                if (copy_var == NULL){
                    set_new_variables(program, INTEGER_TYPE, addElement(NULL, alloc_declaration(copy_var_id, 1, source->arraySize, 0), -1));
                }

                vect_copy(copy_var_id, id2);

                source = getVariable(program, copy_var_id);
              }


                
                int index = gen_load_immediate(program, 0);
                int destination = gen_load_immediate(program, interval - stop - 1);
                t_axe_label* step1 = assignNewLabel(program);
                storeArrayElement(program, target->ID, create_expression(destination, REGISTER), create_expression(loadArrayElement(program, source->ID, create_expression(index, REGISTER)), REGISTER));
                gen_addi_instruction(program, index, index, 1);
                gen_addi_instruction(program, destination, destination, 1);
                handle_binary_comparison(program, create_expression(index, REGISTER), create_expression(stop+1, IMMEDIATE), _NOTEQ_);
                gen_bne_instruction(program, step1, 0);

                gen_addi_instruction(program, index, REG_0, start);
                gen_eorl_instruction(program, destination, destination, destination, CG_DIRECT_ALL);
                
                t_axe_label* step2 = assignNewLabel(program);
                
                storeArrayElement(program, target->ID, create_expression(destination, REGISTER), create_expression(loadArrayElement(program, source->ID, create_expression(index, REGISTER)), REGISTER));
                gen_addi_instruction(program, index, index, 1);
                gen_addi_instruction(program, destination, destination, 1);
                handle_binary_comparison(program, create_expression(index, REGISTER), create_expression(source->arraySize, IMMEDIATE), _NOTEQ_);
                gen_bne_instruction(program, step2, 0);
              }
              else if(start < stop){
                int interval = stop - start + 1;
                if( interval > target->arraySize)
                  notifyError(AXE_INVALID_ARRAY_SIZE);

                int index = gen_load_immediate(program, start);
                int destination = gen_load_immediate(program, 0);

                t_axe_label* begin = assignNewLabel(program);
 
                storeArrayElement(program, target->ID, create_expression(destination, REGISTER), create_expression(loadArrayElement(program, source->ID, create_expression(index, REGISTER)), REGISTER));
                gen_addi_instruction(program, index, index, 1);
                gen_addi_instruction(program, destination, destination, 1);
                handle_binary_comparison(program, create_expression(index, REGISTER), create_expression(stop+1, IMMEDIATE), _NOTEQ_);
                gen_bne_instruction(program, begin, 0);
              }
              else{
                storeArrayElement(program, target->ID, create_expression(0, IMMEDIATE), create_expression(loadArrayElement(program, source->ID, create_expression(start, IMMEDIATE)), REGISTER));
              }

              free($1);
              free($3);
            }
;


/* work in progress */
shift_left_array : IDENTIFIER SHL_OP exp
                {
                  char* identifier = (alias != NULL && strcmp(alias, $1)==0) ? aliased : $1;
                  t_axe_variable *variable = (alias != NULL && strcmp(alias, $1)==0) ? getVariable(program, aliased) : getVariable(program, $1);
                  int size = variable->arraySize;
                  if(variable == NULL || !variable->isArray) notifyError(AXE_INVALID_VARIABLE);

                  t_axe_expression src_index = handle_bin_numeric_op(program, create_expression(REG_0, REGISTER), $3, ADD);
                  t_axe_expression dest_index = create_expression(gen_load_immediate(program, 0), REGISTER);

                  t_axe_label* label_end = newLabel(program);
                  /* controllo se l'indice è minore di 0, se è il caso salto le operazioni */
                  /* t_axe_expression cmp = */handle_binary_comparison(program, src_index, create_expression(0, IMMEDIATE), _LTEQ_);
                  gen_bne_instruction(program, label_end, 0);

                  //while a runtime

                  //inizio del while
                  t_axe_label* label_cond = assignNewLabel(program);
                  t_axe_label* label_cond2 = newLabel(program);
                  //condizione del while (finché src_index non è maggiore uguale alla dimensione dell'array)
                  handle_binary_comparison(program, src_index, create_expression(variable->arraySize, IMMEDIATE), _GTEQ_);
                  gen_bne_instruction(program, label_cond2, 0);

                  //effettuo lo spostamento degli elementi quindi carico l'elemento nella posizione src_index e lo salvo della posizione dest_index
                  int reg = loadArrayElement(program, identifier, src_index);
                  storeArrayElement(program, identifier, dest_index, create_expression(reg, REGISTER));

                  gen_addi_instruction(program, src_index.value, src_index.value, 1);
                  gen_addi_instruction(program, dest_index.value, dest_index.value, 1);

                  gen_bt_instruction(program, label_cond, 0);



                  //inserimento degli zeri

                  //inizio del while
                  assignLabel(program, label_cond2);
                  //condizione del while (finché src_index non è maggiore uguale alla dimensione dell'array)
                  handle_binary_comparison(program, dest_index, create_expression(variable->arraySize, IMMEDIATE), _GTEQ_);
                  gen_bne_instruction(program, label_end, 0);

                  storeArrayElement(program, $1, dest_index, create_expression(0, IMMEDIATE));

                  gen_addi_instruction(program, dest_index.value, dest_index.value, 1);

                  gen_bt_instruction(program, label_cond2, 0);

                  assignLabel(program, label_end);
                  
                  free($1);
                }
;

if_statement   : if_stmt
               {
                  /* fix the `label_else' */
                  assignLabel(program, $1);
               }
               | if_stmt ELSE
               {
                  /* reserve a new label that points to the address where to
                   * jump if `exp' is verified */
                  $2 = newLabel(program);

                  /* exit from the if-else */
                  gen_bt_instruction (program, $2, 0);

                  /* fix the `label_else' */
                  assignLabel(program, $1);
               }
               code_block
               {
                  /* fix the `label_else' */
                  assignLabel(program, $2);
               }
;



if_stmt  :  IF
               {
                  /* the label that points to the address where to jump if
                   * `exp' is not verified */
                  $1 = newLabel(program);
               }
               LPAR exp RPAR
               {
                     if ($4.expression_type == IMMEDIATE)
                         gen_load_immediate(program, $4.value);
                     else
                         gen_andb_instruction(program, $4.value,
                             $4.value, $4.value, CG_DIRECT_ALL);

                     /* if `exp' returns FALSE, jump to the label $1 */
                     gen_beq_instruction (program, $1, 0);
               }
               code_block { $$ = $1; }
;

protect_with_statement : protect_statement WITH 
                       {
                          $2 = newLabel(program);
                          gen_bt_instruction(program, $2, 0);
                          assignLabel(program, (t_axe_label*)LDATA(getElementAt(protectStack, 0)));
                          protectStack = removeFirst(protectStack);
                       }
                       code_block
                       {
                          assignLabel(program, $2);
                       }
;


protect_statement : PROTECT 
                       {
                          protectStack = addFirst(protectStack, newLabel(program));
                       }
                       code_block {}
;




iterate_statement : ITER IDENTIFIER
                  {
                    t_axe_variable* array = getVariable(program, $2);
                    if(!array->isArray)
                      notifyError(AXE_INVALID_VARIABLE);
                    
                    t_iteration_statement* iter = (t_iteration_statement*)malloc(sizeof(t_iteration_statement));
                    iter->ID = strdup($2);
                    iter->index = gen_load_immediate(program, 0);
                    iterationStack = addFirst(iterationStack, iter);

                    $1 = create_while_statement();
                    $1.label_condition = assignNewLabel(program);
                    $1.label_end = newLabel(program);

                    handle_binary_comparison(program, create_expression(iter->index, REGISTER), create_expression(array->arraySize, IMMEDIATE), _EQ_);
                    gen_bne_instruction(program, $1.label_end, 0);
                  }
                  code_block
                  {
                    int index_reg = ((t_iteration_statement*)LDATA(getElementAt(iterationStack, 0)))->index;
                    gen_addi_instruction(program, index_reg, index_reg, 1);
                    gen_bt_instruction(program, $1.label_condition, 0);
                    assignLabel(program, $1.label_end);

                    iterationStack = removeFirst(iterationStack);
                    free($2);
                  }
;




alias_statement : ALIAS IDENTIFIER COMMA IDENTIFIER 
                {
                  t_axe_variable* var1 = getVariable(program, $2);
                  t_axe_variable* var2 = getVariable(program, $4);
                  
                  if(alias != NULL || var1->isArray != var2->isArray)
                    notifyError(AXE_SYNTAX_ERROR);

                  alias = $2;
                  aliased = $4;

                }
                code_block
                {
                  alias = NULL;
                  aliased = NULL;
                  free($2);
                  free($4);
                }
;


undo_if_statement: UNDO IDENTIFIER IF exp
                  {
                    
                    char* identifier = (alias != NULL && strcmp(alias, $2)==0) ? aliased : $2;

                    if($4.expression_type == IMMEDIATE){
                      if($4.value != 0){
                        int old = get_symbol_location(program, strcat(identifier, "_i"), 0);
                        int new = get_symbol_location(program, identifier, 0);
                        gen_add_instruction(program, new, REG_0, old, CG_DIRECT_ALL);
                      }
                    }
                    else{
                      t_axe_label* label_end = newLabel(program);
                      gen_andb_instruction(program, $4.value, $4.value, $4.value, CG_DIRECT_ALL);
                      gen_bne_instruction(program, label_end, 0);

                      int old = get_symbol_location(program, strcat(identifier, "_i"), 0);
                      int new = get_symbol_location(program, identifier, 0);
                      gen_add_instruction(program, new, REG_0, old, CG_DIRECT_ALL);

                      assignLabel(program, label_end);
                    }

                    free($2);
                  }
;

loop_decreasing_statement : LOOPDEC IDENTIFIER BY 
                            {
                              
                              $1 = create_loop_decreasing_statement();
                              $1.label_end = newLabel(program);
                              $1.label_check = newLabel(program);
                              gen_bt_instruction(program, $1.label_check, 0);
                              $1.label_loop = assignNewLabel(program);

                              t_axe_variable* v_counter = getVariable(program, $2);
                              
                              if(v_counter == NULL || v_counter->isArray)
                                notifyError(AXE_INVALID_VARIABLE);

                            }
                            exp
                            {
                              int r_counter = get_symbol_location(program, $2, 0);
                              if($5.expression_type == IMMEDIATE)
                                gen_subi_instruction(program, r_counter, r_counter, $5.value);
                              else
                                gen_sub_instruction(program, r_counter, r_counter, $5.value, CG_DIRECT_ALL);

                              assignLabel(program, $1.label_check);
                              handle_binary_comparison(program, create_expression(r_counter, REGISTER), create_expression(REG_0, REGISTER), _LTEQ_);
                              gen_bne_instruction(program, $1.label_end, 0);
                            }
                            code_block WHILE LPAR exp RPAR
                            {
                              handle_binary_comparison(program, $10, create_expression(REG_0, REGISTER), _EQ_);
                              gen_bne_instruction(program, $1.label_loop, 0);
                              assignLabel(program, $1.label_end);

                              free($2);
                            }
;

for_statement : FOR
                {
                  $1 = create_for_statement();
                } LPAR assignment_list SEMI
                {
                  $1.label_exp = assignNewLabel(program);
                }
                exp SEMI
              {

                if($7.expression_type == IMMEDIATE)
                    gen_load_immediate(program, $7.value);
                else
                    gen_andb_instruction(program, $7.value, $7.value,
                        $7.value, CG_DIRECT_ALL);

                /* beq check if Z==1 so if the result of 'exp' is 0 --> (FALSE) */
                $1.label_exit = newLabel(program);
                gen_beq_instruction(program, $1.label_exit, 0);

                /* if beq is not taken exp is TRUE so we jump to code_block*/
                $1.label_code_block = newLabel(program);
                gen_bt_instruction(program, $1.label_code_block, 0);

                $1.label_epilogue = assignNewLabel(program);

              }
              assignment_list RPAR
              {
                gen_bt_instruction(program, $1.label_exp, 0);
                assignLabel(program, $1.label_code_block);
              }
              code_block
              {
                gen_bt_instruction(program, $1.label_epilogue, 0);
                assignLabel(program, $1.label_exit);
              }
;

/*
try_catch_statement : TRY
                    {
                      $1 = create_try_catch_statement();
                      $1.label_end = newLabel(program);
                      $1.label_catch = newLabel(program);
                    }
                    code_block
                    CATCH
                    {
                      
                    }
                    code_block
;*/

while_statement  : WHILE
                  {
                     /* initialize the value of the non-terminal */
                     $1 = create_while_statement();

                     /* reserve and fix a new label */
                     $1.label_condition
                           = assignNewLabel(program);
                  }
                  LPAR exp RPAR
                  {
                     if ($4.expression_type == IMMEDIATE)
                        gen_load_immediate(program, $4.value);
                     else
                         gen_andb_instruction(program, $4.value,
                             $4.value, $4.value, CG_DIRECT_ALL);

                     /* reserve a new label. This new label will point
                      * to the first instruction after the while code
                      * block */
                     $1.label_end = newLabel(program);

                     /* if `exp' returns FALSE, jump to the label
                      * $1.label_end */
                     gen_beq_instruction (program, $1.label_end, 0);
                  }
                  code_block
                  {
                     /* jump to the beginning of the loop */
                     gen_bt_instruction
                           (program, $1.label_condition, 0);

                     /* fix the label `label_end' */
                     assignLabel(program, $1.label_end);
                  }
;

switch_statement: SWITCH LPAR IDENTIFIER RPAR LBRACE
                {
                  char* identifier = (alias != NULL && strcmp(alias, $3)==0) ? aliased : $3;
                  $1 = (t_switch_statement*)malloc(sizeof(t_switch_statement));
                  $1->cmp_register = getNewRegister(program);
                  gen_addi_instruction(program, $1->cmp_register, get_symbol_location(program, identifier, 0), 0);
                  $1->begin_tests = newLabel(program);
                  $1->switch_end = newLabel(program);
                  switchStack = addFirst(switchStack, $1);
                  gen_bt_instruction(program, $1->begin_tests, 0);
                }
                switch_block RBRACE
                {
                  t_list* p;
                  int cmpReg;
                  assignLabel(program, $1->begin_tests);
                  cmpReg = getNewRegister(program);
                  p = $1->cases;

                  while( p != NULL){
                    gen_subi_instruction(program, cmpReg, $1->cmp_register, ((t_case_statement*)p->data)->number);
                    gen_beq_instruction(program,((t_case_statement*)p->data)->begin_case_label, 0);
                    p = p->next;
                  }

                  if($1->default_label != NULL){
                    gen_bt_instruction(program, $1->default_label, 0);
                    assignLabel(program, $1->switch_end);
                    switchStack = removeFirst(switchStack);
                  }

                  free($3);
                }
;

switch_block: case_statements
              {
                gen_bt_instruction(program, ((t_switch_statement*)LDATA( getFirst(switchStack)))->switch_end, 0);
              }
            | case_statements default_statement
              {
                 gen_bt_instruction(program, ((t_switch_statement*)LDATA( getFirst(switchStack)))->switch_end, 0);
              }
;

case_statements: case_statements case_statement
               | case_statement
;

case_statement: CASE NUMBER COLON
              {
                t_case_statement* c = (t_case_statement *) malloc(sizeof(t_case_statement));
                c->number = $2;
                c->begin_case_label = assignNewLabel(program);
                ((t_switch_statement*)LDATA(getFirst(switchStack)))->cases = addLast(((t_switch_statement*)LDATA(getFirst(switchStack)))->cases, c);
              }
              code_block
;

default_statement: DEFAULT COLON
                 {
                  ((t_switch_statement*)LDATA(getFirst(switchStack)))->default_label = assignNewLabel(program);
                 }
                 code_block
;

break_statement: BREAK
               {
                if(switchStack == NULL){
                  notifyError(AXE_SYNTAX_ERROR);
                }
                else{
                  gen_bt_instruction(program, ((t_switch_statement*)LDATA(getFirst(switchStack)))->switch_end, 0);
                }
               }
;


assert_statement : ASSERT LPAR exp RPAR
                  {
                    if($3.expression_type == IMMEDIATE){
                      if($3.value == 0)
                        gen_halt_instruction(program);
                    }
                    else{
                      t_axe_label* bypass = newLabel(program);
                      handle_binary_comparison(program, $3, create_expression(REG_0, REGISTER), _EQ_);
                      gen_beq_instruction(program, bypass, 0);
                      gen_halt_instruction(program);
                      assignLabel(program, bypass);
                    }
                  }
;

foreach_every_statement : FOREACH IDENTIFIER IN IDENTIFIER
                          {
                            t_axe_variable* elem = getVariable(program, $2);
                            t_axe_variable* array = getVariable(program, $4);

                            if(elem == NULL || array == NULL || elem->isArray || ! array->isArray)
                              notifyError(AXE_INVALID_VARIABLE);
                            
                            $3 = gen_load_immediate(program, 0);

                            t_axe_expression index_exp = create_expression($3, REGISTER);
                            int load_reg = loadArrayElement(program, $4, index_exp);
                            /* get register where value of elem variable is stored */
                            int elem_reg = get_symbol_location(program, $2, 0);
                            /* move the value from load_reg into elem_reg */
                            gen_andb_instruction(program, elem_reg, load_reg, load_reg, CG_DIRECT_ALL);

                            $1.label_condition = assignNewLabel(program);
                            $1.label_end = newLabel(program);

                          }
                          code_block EVERY exp DO
                          {
                            if ($8.expression_type != IMMEDIATE) {
                            notifyError(AXE_INVALID_EXPRESSION);
                            }
                            t_axe_variable *array = getVariable(program, $4);
                            if ($8.value <= 1 || $8.value >= array->arraySize) {
                            notifyError(AXE_INVALID_EXPRESSION);
                            }

                            $7.label_end = newLabel(program);
                            gen_bt_instruction(program, $7.label_end, 0);
                            $7.label_condition = assignNewLabel(program);

                          }
                          code_block
                          {
                            assignLabel(program, $7.label_end);
                            /* increment index */
                            gen_addi_instruction(program, $3, $3, 1);

                            /* check exit condition */
                            int tmp_reg = getNewRegister(program);
                            t_axe_variable *array = getVariable(program, $4);
                            gen_subi_instruction(program, tmp_reg, $3, array->arraySize);
                            gen_beq_instruction(program, $1.label_end, 0);

                            /* load element */
                            t_axe_expression index_exp = create_expression($3, REGISTER);
                            int load_reg = loadArrayElement(program, $4, index_exp);
                            int elem_reg = get_symbol_location(program, $2, 0);
                            gen_andb_instruction(program, elem_reg, load_reg, load_reg, CG_DIRECT_ALL);

                            /* check which code block should be executed */
                            /* index % k == 0 ...but % operator is not available */
                            /* (index / k) * k - index == 0 */
                            gen_divi_instruction(program, tmp_reg, $3, $8.value);
                            gen_muli_instruction(program, tmp_reg, tmp_reg, $8.value);
                            gen_sub_instruction(program, tmp_reg, tmp_reg, $3, CG_DIRECT_ALL);

                            gen_beq_instruction(program, $7.label_condition, 0);
                            gen_bt_instruction(program, $1.label_condition, 0);
                            assignLabel(program, $1.label_end);
                          }
;

either_or_statement : EITHER
                      {
                        $1 = create_either_statement();
                        $1.label_condition = newLabel(program);
                        $1.label_end = newLabel(program);
                        gen_bt_instruction(program, $1.label_condition, 0);
                        $1.label_either = assignNewLabel(program);
                      }
                      code_block OR
                      {
                        gen_bt_instruction(program, $1.label_end, 0);
                        $1.label_or = assignNewLabel(program);
                      }
                      code_block 
                      {
                        gen_bt_instruction(program, $1.label_end, 0);
                        assignLabel(program, $1.label_condition);
                      }
                      ON exp
                      {
                        if($9.expression_type == IMMEDIATE){
                          if($9.value == 0)
                            gen_bt_instruction(program, $1.label_or, 0);
                          else
                            gen_bt_instruction(program, $1.label_either, 0);
                        }
                        else{
                          gen_andb_instruction(program, $9.value, $9.value, $9.value, CG_DIRECT_ALL);
                          gen_bne_instruction(program, $1.label_either, 0);
                          gen_bt_instruction(program, $1.label_or, 0);
                        }
                        assignLabel(program, $1.label_end);
                      }

do_while_statement  : DO
                     {
                        /* the label that points to the address where to jump if
                         * `exp' is not verified */
                        $1 = newLabel(program);

                        /* fix the label */
                        assignLabel(program, $1);
                     }
                     code_block WHILE LPAR exp RPAR
                     {
                           if ($6.expression_type == IMMEDIATE)
                               gen_load_immediate(program, $6.value);
                           else
                               gen_andb_instruction(program, $6.value,
                                   $6.value, $6.value, CG_DIRECT_ALL);

                           /* if `exp' returns TRUE, jump to the label $1 */
                           gen_bne_instruction (program, $1, 0);
                     }
;




return_statement : RETURN
            {
               /* insert an HALT instruction */
               gen_halt_instruction(program);
            }
;

vec_xor_statement : VEC_XOR LPAR IDENTIFIER COMMA IDENTIFIER COMMA IDENTIFIER RPAR
                  {
                    t_axe_variable *target =  (alias != NULL && strcmp(alias, $3)==0) ? getVariable(program, aliased) : getVariable(program, $3);
                    t_axe_variable *source1 = (alias != NULL && strcmp(alias, $3)==0) ? getVariable(program, aliased) : getVariable(program, $5);
                    t_axe_variable *source2 = (alias != NULL && strcmp(alias, $3)==0) ? getVariable(program, aliased) : getVariable(program, $7);

                    if(target == NULL || source1 == NULL || source2 == NULL || !target->isArray || !source1->isArray 
                                      || !source2->isArray || source1->arraySize != source2->arraySize 
                                      || source2->arraySize != target->arraySize)
                      notifyError(AXE_INVALID_VARIABLE);

                    int index = gen_load_immediate(program, 0);
                    t_axe_label* begin = assignNewLabel(program);
                    int op1 = loadArrayElement(program, source1->ID, create_expression(index, REGISTER));
                    int op2 = loadArrayElement(program, source2->ID, create_expression(index, REGISTER));
                    t_axe_expression result = handle_bin_numeric_op(program, create_expression(op1, REGISTER), create_expression(op2, REGISTER), EORB);
                    storeArrayElement(program, target->ID, create_expression(index, REGISTER), result);
                    gen_addi_instruction(program, index, index, 1);
                    handle_binary_comparison(program, create_expression(index, REGISTER), create_expression(target->arraySize, IMMEDIATE), _EQ_);
                    gen_beq_instruction(program, begin, 0);

                  }
;

read_statement : READ LPAR IDENTIFIER RPAR
            {
               int location;
               int old;

              char* identifier = (alias != NULL && strcmp(alias, $3)==0) ? aliased : $3;
               /* read from standard input an integer value and assign
                * it to a variable associated with the given identifier */
               /* get the location of the symbol with the given ID */

               /* lookup the symbol table and fetch the register location
                * associated with the IDENTIFIER $3. */
               location = get_symbol_location(program, identifier, 0);
               
               old = get_symbol_location(program, strcat(identifier, "_i"),0);
               
               gen_add_instruction(program, old, REG_0, location, CG_DIRECT_ALL);
               /* insert a read instruction */
               gen_read_instruction (program, location);

               /* free the memory associated with the IDENTIFIER */
               free($3);
            }
;

write_statement : WRITE LPAR exp RPAR
            {
               int location;

               if ($3.expression_type == IMMEDIATE)
               {
                  /* load `immediate' into a new register. Returns the new
                   * register identifier or REG_INVALID if an error occurs */
                  location = gen_load_immediate(program, $3.value);
               }
               else
                  location = $3.value;

               /* write to standard output an integer value */
               gen_write_instruction (program, location);
            }
;

exp: NUMBER      { $$ = create_expression ($1, IMMEDIATE); }
   | IDENTIFIER  {
                     int location = -1;

                    
                    if(alias != NULL && strcmp($1, alias)==0)
                      location = get_symbol_location(program, aliased, 0);
                    else if(getVariable(program, $1)->isArray && iterationStack != NULL){
                      int len = getLength(iterationStack);
                      int i=0;
                      while(i<len){
                        t_iteration_statement* iter = ((t_iteration_statement*)LDATA(getElementAt(iterationStack, i)));
                        if(strcmp($1, iter->ID)==0){
                          location = loadArrayElement(program, iter->ID, create_expression(iter->index, REGISTER));
                          break;
                      }
                      i=i+1;
                    }
                    if(location == -1)
                      notifyError(AXE_INVALID_VARIABLE);
                    }
                    else {

                     /* get the location of the symbol with the given ID */
                     location = get_symbol_location(program, $1, 0);
                      
                      }

                     /* return the register location of IDENTIFIER as
                      * a value for `exp' */
                     $$ = create_expression (location, REGISTER);

                     /* free the memory associated with the IDENTIFIER */
                     free($1);
   }
   | IDENTIFIER LSQUARE exp RSQUARE {
                     int reg;

                    if(alias != NULL && strcmp($1, alias)==0)
                      reg = loadArrayElement(program, aliased, $3);
                    else {
                      /* load the value IDENTIFIER[exp]
                        * into `arrayElement' */
                       reg = loadArrayElement(program, $1, $3);
                    }

                     /* create a new expression */
                     $$ = create_expression (reg, REGISTER);

                     /* free the memory associated with the IDENTIFIER */
                     free($1);
   }
   | NOT_OP exp {
               if ($2.expression_type == IMMEDIATE)
               {
                  /* IMMEDIATE (constant) expression: compute the value at
                   * compile-time and place the result in a new IMMEDIATE
                   * expression */
                  $$ = create_expression(!($2.value), IMMEDIATE);
               }
               else
               {
                  /* REGISTER expression: generate the code that will compute
                   * the result at compile time */

                  /* Reserve a new register for the result */
                  int output_register = getNewRegister(program);

                  /* Generate a NOTL instruction which will store the negated
                   * logic value into the register we reserved */
                  gen_notl_instruction(program, output_register, $2.value);

                  /* Return a REGISTER expression with the result register */
                  $$ = create_expression(output_register, REGISTER);
               }
   }
   | exp AND_OP exp { $$ = handle_bin_numeric_op(program, $1, $3, ANDB); }
   | exp OR_OP exp  { $$ = handle_bin_numeric_op(program, $1, $3, ORB); }
   | exp PLUS exp   { $$ = handle_bin_numeric_op(program, $1, $3, ADD); }
   | exp MINUS exp  { $$ = handle_bin_numeric_op(program, $1, $3, SUB); }
   | exp MUL_OP exp { $$ = handle_bin_numeric_op(program, $1, $3, MUL); }
   | exp FAKE_MUL exp {
                        int result = gen_load_immediate(program, 0);
                        int op1, op2;
                        
                        op1 = ($1.expression_type == IMMEDIATE) ? gen_load_immediate(program, $1.value) : $1.value;
                        op2 = ($1.expression_type == IMMEDIATE) ? gen_load_immediate(program, $3.value) : (handle_bin_numeric_op(program,
                                                                          create_expression(gen_load_immediate(program, 0),REGISTER), $3, ADD).value);
                        
                        t_axe_label* end = newLabel(program);
                        t_axe_label* bypass = newLabel(program);
                        t_axe_label* start = assignNewLabel(program);
                        //check if op2 is zero
                        gen_andb_instruction(program, op2, op2, op2, CG_DIRECT_ALL);
                        gen_beq_instruction(program, end, 0);
                        gen_bgt_instruction(program, bypass, 0);
                        gen_sub_instruction(program, op2, REG_0, op2, CG_DIRECT_ALL);
                        assignLabel(program, bypass);

                        gen_add_instruction(program, result, result, op1, CG_DIRECT_ALL);
                        gen_subi_instruction(program, op2, op2, 1);
                        gen_bne_instruction(program, bypass, 0);
                        
                        gen_andb_instruction(program, $3.value, $3.value, $3.value, CG_DIRECT_ALL);
                        gen_bgt_instruction(program, end, 0);
                        gen_sub_instruction(program, result, REG_0, result, CG_DIRECT_ALL);

                        assignLabel(program, end);
                        
                        $$ = create_expression(result, REGISTER);

                      }
   | exp DIV_OP exp { 
                      
                      if(protectStack != NULL){
                        int r = getNewRegister(program);
                        gen_addi_instruction(program, r, REG_0, 0);
                        handle_binary_comparison(program, $3, create_expression(r, REGISTER), _EQ_);
                        gen_bne_instruction(program, (t_axe_label*)LDATA(getElementAt(protectStack, 0)), 0);
                      }
                        $$ = handle_bin_numeric_op(program, $1, $3, DIV); 
                    }
   | exp LT exp     { $$ = handle_binary_comparison(program, $1, $3, _LT_); }
   | exp GT exp     { $$ = handle_binary_comparison(program, $1, $3, _GT_); }
   | exp EQ exp     { $$ = handle_binary_comparison(program, $1, $3, _EQ_); }
   | exp NOTEQ exp  { $$ = handle_binary_comparison(program, $1, $3, _NOTEQ_); }
   | exp LTEQ exp   { $$ = handle_binary_comparison(program, $1, $3, _LTEQ_); }
   | exp GTEQ exp   { $$ = handle_binary_comparison(program, $1, $3, _GTEQ_); }
   | exp SHL_OP exp { $$ = handle_bin_numeric_op(program, $1, $3, SHL); }
   | exp SHR_OP exp { $$ = handle_bin_numeric_op(program, $1, $3, SHR); }
   | exp ANDAND exp { $$ = handle_bin_numeric_op(program, $1, $3, ANDL); }
   | exp OROR exp   { $$ = handle_bin_numeric_op(program, $1, $3, ORL); }
   | OR_OP exp OR_OP { 
                        if($2.expression_type == IMMEDIATE)
                          $$ = create_expression($2.value > 0 ? $2.value : -$2.value, IMMEDIATE);
                        else{
                          
                          gen_andb_instruction(program, $2.value, $2.value, $2.value, CG_DIRECT_ALL);
                          t_axe_label* positive = newLabel(program);
                          gen_bpl_instruction(program, positive, 0);
                          gen_muli_instruction(program, $2.value, $2.value, -1);
                          assignLabel(program, positive);
                          $$ = $2;
                        }
                     }
   | LPAR exp RPAR  { $$ = $2; }
   | MINUS exp {
                  if ($2.expression_type == IMMEDIATE)
                  {
                     $$ = $2;
                     $$.value = - ($$.value);
                  }
                  else
                  {
                     t_axe_expression exp_r0;

                     /* create an expression for register REG_0 */
                     exp_r0.value = REG_0;
                     exp_r0.expression_type = REGISTER;

                     $$ = handle_bin_numeric_op
                           (program, exp_r0, $2, SUB);
                  }
               }
    | exp IF exp ELSE exp
      {
        if($3.expression_type == IMMEDIATE){
          if($3.value == 0)
            $$ = $5;
          else
            $$ = $1;
        }
        else {
          t_axe_expression cmp = handle_binary_comparison(program, $3, create_expression(0, IMMEDIATE),_EQ_);
          t_axe_expression mask = handle_bin_numeric_op(program, cmp, create_expression(1, IMMEDIATE), SUB);

          int reg = getNewRegister(program);
          gen_notb_instruction(program, reg, mask.value);

          t_axe_expression nmask = create_expression(reg, REGISTER);

          $$ = handle_bin_numeric_op(program,
                            handle_bin_numeric_op(program, $1, mask, ANDB),
                            handle_bin_numeric_op(program, $5, nmask, ANDB), ORB);
        }
      }
      | exp DOLLAR exp AT exp
        {
          /* operatore splice r = a $ b @ 5 = (a31 a30 a29 a28 a27 b26 ... b0) */
          /* formula r = (a ANDB !mask) ORB (b ANDB mask)*/
          
          // se k è un IMMEDIATE posso eseguire a compile time
          if($5.expression_type == IMMEDIATE){
            if($5.value >= 32){
              $$ = $1;
            }
            else if($5.value <= 0){
              $$ = $3;
            }
            else{
              int n_bit_b = 32 - $5.value;
              int mask_a = 0xFFFFFFFF << n_bit_b;
              int mask_b = ~mask_a;

              $$ = handle_bin_numeric_op(program,
                handle_bin_numeric_op(program, $1, create_expression(mask_a, IMMEDIATE), ANDB),
                handle_bin_numeric_op(program, $3, create_expression(mask_b, IMMEDIATE), ANDB),
                ORB);
            }
          }
          else{
            t_axe_label* label_below_zero = newLabel(program);
            t_axe_label* label_between = newLabel(program);
            t_axe_label* label_splice = newLabel(program);
            int maska = gen_load_immediate(program, 0);
            int maskb = gen_load_immediate(program, 0);
            
            //controllo se k >= 32
            handle_binary_comparison(program, $5, create_expression(32, IMMEDIATE), _GTEQ_);
            gen_beq_instruction(program, label_below_zero, 0);
            gen_notb_instruction(program, maska, maska);
            gen_bt_instruction(program, label_splice, 0);
            
            //controllo se k <= 0
            assignLabel(program, label_below_zero);
            handle_binary_comparison(program, $5, create_expression(0, IMMEDIATE), _LTEQ_);
            gen_beq_instruction(program, label_between, 0);
            gen_notb_instruction(program, maskb, maskb);
            gen_bt_instruction(program, label_splice, 0);

            //between
            assignLabel(program, label_between);
            int n_bit_b = gen_load_immediate(program, 32);
            gen_sub_instruction(program, n_bit_b, n_bit_b, $5.value, CG_DIRECT_ALL);
            gen_addi_instruction(program, maska, REG_0, 0xFFFFFFFF);
            gen_shl_instruction(program, maska, maska, n_bit_b, CG_DIRECT_ALL);
            gen_notb_instruction(program, maskb, maska);

            assignLabel(program, label_splice);
            $$ = handle_bin_numeric_op(program,
                handle_bin_numeric_op(program, $1, create_expression(maska, REGISTER), ANDB),
                handle_bin_numeric_op(program, $3, create_expression(maskb, REGISTER), ANDB),
                ORB);
           }
        }
        | IDENTIFIER ATAT IDENTIFIER
          {
            t_axe_variable* var1 = getVariable(program, $1);
            t_axe_variable* var2 = getVariable(program, $3);

            //alias control
            if(alias != NULL && strcmp($3, alias)==0)
              var2 = getVariable(program, aliased);
            else 
              var2 = getVariable(program, $3);

            if(alias != NULL && strcmp($1, alias)==0)
              var1 = getVariable(program, aliased);
            else
              var1 = getVariable(program, $1);


            if(var1 == NULL || var2 == NULL || !var1->isArray || !var2->isArray)
              notifyError(AXE_INVALID_VARIABLE);
            else if(var1->arraySize != var2->arraySize)
              notifyError(AXE_INVALID_ARRAY_SIZE);
            else{
              int i=0;
              int result = gen_load_immediate(program, 0);
              for(i=0; i < var1->arraySize; i = i+1){
                int elem1 = loadArrayElement(program, var1->ID, create_expression(i, IMMEDIATE));
                int elem2 = loadArrayElement(program, var2->ID, create_expression(i, IMMEDIATE));

                gen_add_instruction(program, result, result, handle_bin_numeric_op(program, 
                        create_expression(elem1, REGISTER), create_expression(elem2, REGISTER), MUL).value, CG_DIRECT_ALL);
              }
              $$ = create_expression(result, REGISTER);
            }
          }
          | RED LPAR IDENTIFIER RPAR
          {
            //alias control
            t_axe_variable* variable;

            if(alias != NULL && strcmp($3, alias)==0)
              variable = getVariable(program, aliased);
            else 
              variable = getVariable(program, $3);

            if(variable == NULL || !variable->isArray){
               notifyError(AXE_INVALID_VARIABLE);
            }
            else{

              int result = gen_load_immediate(program, 0);
              int i=0;
              for(i=0; i < variable->arraySize; ++i){
                 int element = loadArrayElement(program, variable->ID, create_expression(i, IMMEDIATE));
                 gen_add_instruction(program, result, result, element, CG_DIRECT_ALL);
              }
              $$ = create_expression(result, REGISTER);
            }
          }
          | MERGE exp COMMA exp COMMA exp
          {
            if($6.expression_type == IMMEDIATE){
              if($6.value == 0){
                $$ = $4;
              }
              else{
                $$ = $2;
              }
            }
            else{
              int reg1 = $2.expression_type == IMMEDIATE ? gen_load_immediate(program, $2.value) : $2.value;
              int reg2 = $4.expression_type == IMMEDIATE ? gen_load_immediate(program, $4.value) : $4.value;
              int res = gen_load_immediate(program, 0);
              t_axe_label* end = newLabel(program);
              t_axe_label* zero = newLabel(program);
              gen_andb_instruction(program, $6.value, $6.value, $6.value, CG_DIRECT_ALL);
              gen_beq_instruction(program, zero, 0);
              gen_add_instruction(program, res, reg1, REG_0, CG_DIRECT_ALL);
              gen_bt_instruction(program, end, 0);
              assignLabel(program, zero);
              gen_add_instruction(program, res, reg2, REG_0, CG_DIRECT_ALL);
              assignLabel(program, end);

              $$ = create_expression(res, REGISTER);

            }
          }
          | BIT IDENTIFIER
          {
              t_axe_variable* var = getVariable(program, $2);

              if(var == NULL){
                notifyError(AXE_INVALID_VARIABLE);
              }
              else if(!var->isArray){
                $$ = create_expression(get_symbol_location(program, $2, 1), REGISTER);
              }
              else {
                int i=0;
                int result = gen_load_immediate(program, 0);
                int dim = var->arraySize < 32 ? var->arraySize : 32;
                while(i < dim){
                  gen_add_instruction(program, result, result,
                              handle_bin_numeric_op(program, 
                                        handle_binary_comparison(program, create_expression(REG_0, REGISTER), create_expression(loadArrayElement(program, $2, create_expression(i, IMMEDIATE)), REGISTER), _NOTEQ_),
                              create_expression(i, IMMEDIATE), SHL).value, CG_DIRECT_ALL);
                  ++i;
                }
                $$ = create_expression(result, REGISTER);
            }
          }
;

%%

void vect_copy(char* dest_var_id, char* src_var_id){
  t_axe_variable* src_var = getVariable(program, src_var_id);

  int i_reg = gen_load_immediate(program, 0);
  t_axe_label* l_condition = assignNewLabel(program);
  t_axe_label* l_end = newLabel(program);
  handle_binary_comparison(program, create_expression(i_reg, REGISTER), create_expression(src_var->arraySize, IMMEDIATE), _EQ_);
  gen_bne_instruction(program, l_end, 0);
  int reg = loadArrayElement(program, src_var_id, create_expression(i_reg, REGISTER));
  storeArrayElement(program, dest_var_id, create_expression(i_reg, REGISTER), create_expression(reg, REGISTER));
  gen_addi_instruction(program, i_reg, i_reg, 1);
  gen_bt_instruction(program, l_condition, 0);
  assignLabel(program, l_end);

  return;
}

/*=========================================================================
                                  MAIN
=========================================================================*/
int main (int argc, char **argv)
{
   /* initialize all the compiler data structures and global variables */
   init_compiler(argc, argv);
   t_list* switchStack;

   /* start the parsing procedure */
   yyparse();

#ifndef NDEBUG
   fprintf(stdout, "Parsing process completed. \n");
   printProgramInfos(program, file_infos->frontend_output);
#endif

   /* test if the parsing process completed succesfully */
   checkConsistency();

   /* do not attach a line number to the instructions generated by the
    * transformations that follow. */
   line_num = -1;

   doTargetSpecificTransformations(program);

#ifndef NDEBUG
   fprintf(stdout, "Creating a control flow graph. \n");
#endif

   /* create the control flow graph */
   graph = createFlowGraph(program->instructions);
   checkConsistency();

#ifndef NDEBUG
   assert(program != NULL);
   assert(program->sy_table != NULL);
   assert(file_infos != NULL);
   assert(file_infos->syTable_output != NULL);
   printSymbolTable(program->sy_table, file_infos->syTable_output);
   printGraphInfos(graph, file_infos->cfg_1, 0);

   fprintf(stdout, "Updating the basic blocks. \n");
#endif

   /* update the control flow graph by inserting load and stores inside
   * every basic block */
   graph = insertLoadAndStoreInstr(program, graph);

#ifndef NDEBUG
   fprintf(stdout, "Executing a liveness analysis on the intermediate code \n");
#endif
   performLivenessAnalysis(graph);
   checkConsistency();

#ifndef NDEBUG
   printGraphInfos(graph, file_infos->cfg_2, 1);
#endif

#ifndef NDEBUG
   fprintf(stdout, "Starting the register allocation process. \n");
#endif
   /* initialize the register allocator by using the control flow
    * informations stored into the control flow graph */
   RA = initializeRegAlloc(graph);

   /* execute the linear scan algorithm */
   execute_linear_scan(RA);

#ifndef NDEBUG
   printRegAllocInfos(RA, file_infos->reg_alloc_output);
#endif

#ifndef NDEBUG
   fprintf(stdout, "Updating the control flow informations. \n");
#endif
   /* apply changes to the program informations by using the informations
   * of the register allocation process */
   materializeRegisterAllocation(program, graph, RA);
   updateProgramInfos(program, graph);

#ifndef NDEBUG
   fprintf(stdout, "Writing the assembly file... \n");
#endif
   writeAssembly(program, file_infos->output_file_name);

#ifndef NDEBUG
   fprintf(stdout, "Assembly written on file \"%s\".\n", file_infos->output_file_name);
#endif

   /* shutdown the compiler */
   shutdownCompiler(0);

   return 0;
}

/*=========================================================================
                                 YYERROR
=========================================================================*/
void yyerror(const char* msg)
{
   errorcode = AXE_SYNTAX_ERROR;
   free((void *)errormsg);
   errormsg = strdup(msg);
}
