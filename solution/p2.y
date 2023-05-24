%{
/*****************/
/*   Include     */
/*****************/
#include <stdio.h>
#include <stdlib.h>
/*****************/
/*    Define     */
/*****************/
#define MAX_N 128
/*****************/
/*  Structures   */
/*****************/
typedef struct tree_node {
  char letter;
  struct tree_node *next;
}tree_node;
typedef struct tree_list {
  tree_node *head;
  int size;
}tree_list;

typedef struct tree_head {
  tree_list *children[MAX_N];
  tree_list *union_set[MAX_N];
  tree_list *first_set;
  tree_list *follow_set;
  char union_first[MAX_N];
  char union_follow[MAX_N];
  int is_change;
  int is_nullable;
  int seen;
  int size;
  int first_set_size;
  int first_size;
  int follow_size;
  char letter;
}tree_head;
/*****************/
/*  Declarations */
/*****************/
int lookahead;
tree_head *grammar[MAX_N];
tree_head *first_set[MAX_N];
int grammar_size = 0;
int g_idx = 0;
int c_idx = 0;
int is_or = 0;
int concat = 0;
int epsilon = 0;
/*****************/
/*   Functions   */
/*****************/
void lhs_productions();
void rhs_productions();
void or_rhs_productions();
void rhs_concat();
void match(int);
void print_error();
void A();
void A_prime();
void B();
void C();
void C_prime();
void D();
%}
%union {
  char *str;
}

%token <str> NT T GOES SEMI OR EOL
%type <str> production

%%
prod_list1       : production prod_list2
                 { printf("production %s\n", $1); }
                 ;
prod_list2       : %empty
                 | production prod_list2
                 ;
production       : NT GOES production_body1 SEMI EOL
                 { printf("yacc %s\n", $1); }
                 ;
production_body1 : rule production_body2
                 ;
production_body2 : %empty
                 | OR rule production_body2
                 ;
rule : NT rule   { printf("yacc %s\n", $1); }
     | T rule
     | EOL
     ;

%%
tree_head *create_lhs() {
  tree_head *node = malloc(sizeof(tree_head));
  node->letter = (char)(*yylval.str);
  for(int i = 0; i < MAX_N; i++) {
    node->children[i] = NULL;
    node->union_set[i] = NULL;
  }
  node->size = 0;
  node->first_set_size = 0;
  node->first_size = 0;
  node->follow_size = 0;
  node->is_change = 0;
  node->is_nullable = 0;
  int seen = 0;
  node->first_set = NULL;
  node->follow_set = NULL;
  return node;
}

tree_list *create_lhs_children() {
  tree_list *list = malloc(sizeof(tree_list));
  list->head = NULL;
  list->size = 0;
  return list;
}

tree_node *create_node() {
  tree_node *node = malloc(sizeof(tree_node));
  node->letter = (char)(*yylval.str);
  node->next = NULL;
  return node;
}

void insert_node(tree_node *node) {
  tree_head *curr = grammar[g_idx-1];
  tree_node *tmp = curr->children[curr->size-1]->head;
  while(tmp->next != NULL) {
    tmp = tmp->next;
  }
  tmp->next = node;
  curr->children[curr->size-1]->size++;
}

int contains(int val, tree_list *list) {
  if(list->head == NULL) return 0;
  tree_node *tmp = list->head;
  while(tmp != NULL) {
    if(tmp->letter == (char)val) {
      return 1;
    }
    tmp = tmp->next;
  }
  return 0;
}

void init_first_set() {
  for(int i = 0; i < MAX_N; i++) {
    first_set[i] = NULL;
  }
}

int first_set_contains(int val) {
  if(first_set[MAX_N - val] != NULL) {
    return 1;
  }
  return 0;
}

void print_grammar() {
  for(int i = 0; i < grammar_size; i++) {
    printf("%c  --> ", grammar[i]->letter);
    for(int j = 0; j < grammar[i]->size; j++) {
      if(grammar[i]->children[j]->head->letter == '@') {
        printf("epsilon");
      }
      else {
        printf("%c ", grammar[i]->children[j]->head->letter);
        tree_node *tmp = grammar[i]->children[j]->head->next;
        while(tmp != NULL) {
          printf("%c ", tmp->letter);
          tmp = tmp->next;
        }
      }
      if(j < grammar[i]->size-1) printf("\n    |  ");
      else printf("\n");
    }
  }
}

void add_to_first_set(int val, tree_head *curr_lhs) {
  // if first set is empty, create head node
  if(curr_lhs->first_set == NULL) {
    curr_lhs->first_set = create_lhs_children();
    tree_node *node = create_node();
    node->letter = (char)val;
    curr_lhs->first_set->head = node;
  }
  // first set already exists
  else {
    // check if non terminal already exists
    if(!contains(val, curr_lhs->first_set)) {
      tree_node *tmp = curr_lhs->first_set->head;
      while(tmp->next != NULL) {
        tmp = tmp->next;
      }
      tree_node *new_node = create_node();
      new_node->letter = (char)val;
      tmp->next = new_node;
    }
  }
}

void add_lhs_productions() {
  for(int i = 0; i < grammar_size; i++) {
    first_set[MAX_N - grammar[i]->letter] = grammar[i];
  }
}

void terminal_and_epsilon() {
  for(int i = 0; i < grammar_size; i++) {
    for(int j = 0; j < grammar[i]->size; j++) {
      int c_val = (int)grammar[i]->children[j]->head->letter;
      if(c_val >= 97 && c_val <= 122) {
        add_to_first_set(c_val, grammar[i]);
      }
      else if(c_val == 64) {
        add_to_first_set(c_val, grammar[i]);
        grammar[i]->is_nullable = 1;
      }
    }
  }
}

tree_list *new_union_head(tree_node *node) {
  tree_list *new_list = malloc(sizeof(tree_list));
  new_list->head = node;
  return new_list;
}

void correct_first_set() {
  for(int i = 0; i < grammar_size; i++) {
    for(int j = 0; j < grammar[i]->first_set_size; j++) {
      //printf("grammar[%c] fset: %c\n", grammar[i]->letter, grammar[i]->union_set[j]->head->letter);
      if(grammar[i]->union_set[j]->head->letter >= 65 && grammar[i]->union_set[j]->head->letter <= 90) {
        if(first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->is_nullable) {
          if(grammar[i]->union_set[j]->head->next == NULL){
            // add epsilon to union set and mark grammar[i] as nullable 
            grammar[i]->is_nullable = 1;
            grammar[i]->is_change = 1;
            //printf("make epsilon for grammar[%c]\n", grammar[i]->letter);
            add_to_first_set(64, grammar[i]);
          }
        }
      }
    }
  }
}

void restart_epsilon() {
  for(int i = 0; i < grammar_size; i++) {
    for(int j = 0; j < grammar[i]->first_set_size; j++) {
      if(grammar[i]->union_set[j]->head->letter >= 65 && grammar[i]->union_set[j]->head->letter <= 90) {
        if(first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->is_nullable && 
            first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->is_change) {
          if(grammar[i]->union_set[j]->head->next != NULL) {
            grammar[i]->union_set[grammar[i]->first_set_size++] = malloc(sizeof(tree_list));
            grammar[i]->union_set[grammar[i]->first_set_size-1]->head = grammar[i]->union_set[j]->head->next;
            //printf("added\n");
          }
          first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->is_change = 0;
        }
      }
    }
  }
}

void first_set_non_terminals() {
  for(int i = 0; i < grammar_size; i++) {
    for(int j = 0; j < grammar[i]->size; j++) {
      int c_val = (int)grammar[i]->children[j]->head->letter;
      if(c_val >= 65 && c_val <= 90) {
        if(first_set[MAX_N-c_val]->is_nullable) {
          grammar[i]->union_set[grammar[i]->first_set_size++] = grammar[i]->children[j];
          //printf("%c is nullable\n", grammar[i]->union_set[grammar[i]->first_set_size-1]->head->letter);
          // loop through child list until non nullable non-terminal or
          // terminal is found
          tree_node *tmp = grammar[i]->children[j]->head->next;
          while(tmp != NULL) {
            if(tmp->letter >= 65 && tmp->letter <= 90 && first_set[MAX_N-tmp->letter]->is_nullable) {
              // another non terminal is found to add to union set
              grammar[i]->union_set[grammar[i]->first_set_size++] = new_union_head(tmp);
              //printf("another null %c\n", tmp->letter);
            } 
            else if(tmp->letter >= 65 && tmp->letter <= 90 && !first_set[MAX_N-tmp->letter]->is_nullable) {
              // printf("not nullable %c\n", tmp->letter);
              grammar[i]->union_set[grammar[i]->first_set_size++] = new_union_head(tmp);
              //printf("not nullable %c\n", grammar[i]->union_set[grammar[i]->first_set_size-1]->head->letter);
              tmp = NULL;
            }
            else {
              //printf("terminal found: %c\n", tmp->letter);
              grammar[i]->union_set[grammar[i]->first_set_size++] = new_union_head(tmp);
              tmp = NULL;
            }
            if(tmp != NULL)
              tmp = tmp->next;
          }
          //if(tmp != NULL) printf("tmp: %c\n", tmp->letter);
        }
        else {
          grammar[i]->union_set[grammar[i]->first_set_size++] = grammar[i]->children[j];
          //printf("%c union set\n", grammar[i]->union_set[grammar[i]->first_set_size-1]->head->letter);
        }
      }
    }
  } 
}


tree_list *create_lhs_first_set(tree_node *first) {
  tree_list *new = create_lhs_children();
  // check if epsilon is the root
  new->head = first;
  //printf("lhs first set created\n");
  return new;
}

void insert(tree_list *list, tree_node *node) {
  tree_node *head = list->head;
  while(head->next != NULL) {
    head = head->next;
  }
  head->next = node;
}

void add_to_follow_set(char c, tree_list *set) {
 // printf("%c added to follow set\n", c);
  if(set->head == NULL) {
    tree_node *node = create_node();
    node->letter = c;
    set->head = node; 
  }
  else {
    tree_node *tmp = set->head;
    while(tmp->next != NULL) {
      tmp = tmp->next;
    }
    tree_node *new_node = create_node();
    new_node->letter = c;
    tmp->next = new_node;
  }
}

void union_sets() {
  // loop until no changes occur. Make sure is_change is set to 0
  for(int i = 0; i < grammar_size; i++) {
    grammar[i]->is_change = 0;
  }
  // add $ to starting follow set
  tree_node *dollar = create_node();
  dollar->letter = '$';
  grammar[0]->follow_set->head = dollar;
  while(1) {
    // union first 
    int start_over = 0;
    for(int i = 0; i < grammar_size; i++) {
      for(int j = 0; j < grammar[i]->first_size; j++) {
        // add to follow set if applicable
        // if its a terminal just add it
        if(grammar[i]->union_first[j] >= 97 && grammar[i]->union_first[j] <= 122) {
          if(!contains((int)grammar[i]->union_first[j], grammar[i]->follow_set)) {
            add_to_follow_set(grammar[i]->union_first[j], grammar[i]->follow_set);
            grammar[i]->is_change = 1;
          }
        }
        else {
          // loop through union_first[i] first set
          tree_node *tmp = first_set[MAX_N-grammar[i]->union_first[j]]->first_set->head;
          while(tmp != NULL) {
            if(tmp->letter == 64) break;
            else if(!contains((int)tmp->letter, grammar[i]->follow_set)) {
              add_to_follow_set(tmp->letter, grammar[i]->follow_set);
              grammar[i]->is_change = 1;
            }
            tmp = tmp->next;
          }
        }
      }
    }
    for(int i = 0; i < grammar_size; i++) {
      for(int j = 0; j < grammar[i]->follow_size; j++) {
        // loop through union follows non terminal follow set
        // check if follow set is null, continue and mark is_change
        if(first_set[MAX_N-grammar[i]->union_follow[j]]->follow_set->head == NULL) {
          grammar[i]->is_change = 1;
        }
        else {
          tree_node *tmp = first_set[MAX_N-grammar[i]->union_follow[j]]->follow_set->head;
          while(tmp != NULL) {
            if(!contains((int)tmp->letter, grammar[i]->follow_set)) {
              add_to_follow_set(tmp->letter, grammar[i]->follow_set);
              grammar[i]->is_change = 1;
            }
            tmp = tmp->next;
          }
        }
      }
    }
    // union follow sets
    for(int i = 0; i < grammar_size; i++) {
      if(grammar[i]->is_change == 1) {
        start_over = 1;
        grammar[i]->is_change = 0;
      }
    }
    if(start_over == 0) return;
  }
}


void build_follow_set() {
  //printf("Wasn't able to complete follow sets\n");
  // initialize all grammars follow set
  for(int i = 0; i < grammar_size; i++) {
    grammar[i]->follow_set = malloc(sizeof(tree_list));
    grammar[i]->follow_set->head = NULL;
  }
  //printf("init follow set\n");
  // loop though grammar union set and store in arrays for sets to union 
  for(int i = 0; i < grammar_size; i++) {
    for(int j = 0; j < grammar[i]->first_set_size; j++) {
      // start from head of union set and follow until the end of list
      tree_node *tmp = grammar[i]->union_set[j]->head;
      while(tmp != NULL) {
        if(tmp->letter >= 65 && tmp->letter <= 90) {
          // now loop through this list until non nullable or terminal found
          //printf("inner letter %c\n", tmp->letter);
          if(tmp->next == NULL) {
            // set follow tmp to follow of grammar[i]
            first_set[MAX_N-tmp->letter]->union_follow[first_set[MAX_N-tmp->letter]->follow_size++] = grammar[i]->letter;
            //printf("stored %c in follow set of %c\n", grammar[i]->letter, tmp->letter);
          }
          // if tmp is not null loop though until
          else {
            // its a union with first set of next 
            // loop through the rest of the list
            tree_node *scnd_tmp = tmp->next;
            while(scnd_tmp != NULL) {
              first_set[MAX_N-tmp->letter]->union_first[first_set[MAX_N-tmp->letter]->first_size++] = scnd_tmp->letter;
              if(scnd_tmp->letter >= 65 && scnd_tmp->letter <= 90 && first_set[MAX_N-scnd_tmp->letter]->is_nullable) {
                //printf("%c is nullable\n", scnd_tmp->letter);
                scnd_tmp = scnd_tmp->next;
                if(scnd_tmp == NULL) {
                  first_set[MAX_N-tmp->letter]->union_follow[first_set[MAX_N-tmp->letter]->follow_size++] = grammar[i]->letter;
                }
              }
              else {
                scnd_tmp = NULL;
              }
            }
          }
        }
        tmp = tmp->next;
      }
    }
  }
  // print union first and union follow
  /*
  for(int i = 0; i < grammar_size; i++) {
    printf("grammar %c union first-----------\n", grammar[i]->letter);
    for(int j = 0; j < grammar[i]->first_size; j++) {
      printf("%c ", grammar[i]->union_first[j]);
    }
    printf("\n");
  }
  for(int i = 0; i < grammar_size; i++) {
    printf("grammar %c union follow------------\n", grammar[i]->letter);
    for(int j = 0; j < grammar[i]->follow_size; j++) {
      printf("%c ", grammar[i]->union_follow[j]);
    }
    printf("\n");
  }
  */
  union_sets();
}

void build_first_set() {
  // create array of all lhs productions
  init_first_set();
  // add all lhs productions to a quick lookup table
  add_lhs_productions();
  // computation of terminal and epsilon symbols
  terminal_and_epsilon();
  // computation of non-terminals
  first_set_non_terminals();
  // print union and first sets if not null
  correct_first_set();
  restart_epsilon();
  for(int i = 0; i < grammar_size; i++) {
    for(int j = 0; j < grammar[i]->first_set_size; j++) {
      //printf("grammar[%c] union_set[%d]: %c ", grammar[i]->letter, j, grammar[i]->union_set[j]->head->letter);
      tree_node *tmp = grammar[i]->union_set[j]->head->next;
      while(tmp != NULL) {
        //printf("%c ", tmp->letter);
        tmp = tmp->next;
      }
      //printf("\n");
    }
  }

  // loop through stored union sets and only break when no more changes occur
  while(1) {
    // loop through grammar array
    for(int i = 0; i < grammar_size; i++) {
      //printf("-----------------------------------------\n");
      //printf("Production %c in effect\n", grammar[i]->letter);
      // loop through first set branches
      for(int j = 0; j < grammar[i]->first_set_size; j++) {
        // if its a non terminal check if union can occur
        //printf("------------------------------------------\n");
        //printf("RHS %c is in effect\n", grammar[i]->union_set[j]->head->letter);
        if(grammar[i]->union_set[j]->head->letter >= 65 && grammar[i]->union_set[j]->head->letter <= 90) {
          // check if first_set exists
          if(first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->first_set == NULL) {
            //printf("grammar %c has a null first set\n", grammar[i]->union_set[j]->head->letter);
            // set change bit on for current rhs
            grammar[i]->is_change = 1;
          }
          else {
            // first_set grammar exists, union with lhs
            //printf("grammar %c exists\n", grammar[i]->union_set[j]->head->letter);
            // check if lhs first set exists
            if(grammar[i]->first_set == NULL) {
              //printf("lhs %c is null first set\n", grammar[i]->letter);
              // join set, dont add epsilon
              //grammar[i]->first_set = create_lhs_first_set(first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->first_set->head);
              // mark change in lhs
              grammar[i]->is_change = 1;
              // loop through the rest of the set
              //printf("rhs root %c\n", first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->first_set->head->letter);
              //printf("first_set head: %c\n", first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->first_set->head->letter);
              tree_node *tmp = first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->first_set->head;
              if(tmp == NULL) printf("oh no\n");
              while(tmp != NULL) {
                if((int)tmp->letter != 64) {
                  // add to first_set
                 // printf("lhs %c added %c\n", grammar[i]->letter, tmp->letter);  
                  add_to_first_set((int)tmp->letter, grammar[i]);
                }
                tmp = tmp->next;
              }
            }
            else {
              //printf("union lhs %c with rhs %c\n", grammar[i]->letter, grammar[i]->union_set[j]->head->letter);
              // rhs exists, union and mark if any change occurs
              tree_node *tmp = first_set[MAX_N-grammar[i]->union_set[j]->head->letter]->first_set->head;
              while(tmp != NULL) {
                if((int)tmp->letter != 64 && !contains((int)tmp->letter, grammar[i]->first_set)) {
                  //printf("lhs does not contain %c\n", tmp->letter);
                  //insert(grammar[i]->first_set, tmp);
                  add_to_first_set((int)tmp->letter, grammar[i]);
                  grammar[i]->is_change = 1;
                }
                tmp = tmp->next;
              }
            }
          }
        }
        else if(grammar[i]->union_set[j]->head->letter >= 97 && grammar[i]->union_set[j]->head->letter <= 122) {
          //printf("terminal %c found on rhs\n", grammar[i]->union_set[j]->head->letter);
          // check if lhs exists
          if(grammar[i]->first_set == NULL) {
            // make a new node for the non terminal
            tree_node *node = malloc(sizeof(tree_node));
            node->next = NULL;
            node->letter = grammar[i]->union_set[j]->head->letter;
            grammar[i]->first_set = create_lhs_first_set(node);
            
            //printf("first set %c lhs created for terminal %c\n", grammar[i]->letter, grammar[i]->union_set[j]->head->letter);
            grammar[i]->is_change = 1;
          }
          else {
            //printf("in before union of terminal\n");
            // add lhs terminal to rhs if it doesn't exist
            if(!contains((int)grammar[i]->union_set[j]->head->letter, grammar[i]->first_set)) {
              add_to_first_set((int)grammar[i]->union_set[j]->head->letter, grammar[i]);
              grammar[i]->is_change = 1;
            }
          }
        }
        // if(j == 3) return;
      }
    }
    int start_over = 0;
    // loop through the lhs productions and see if any changes have occured
    // if changes occured, reset flags to 0
    // else we are done production
    for(int i = 0; i < grammar_size; i++) {
      if(grammar[i]->is_change == 1) {
        start_over = 1;
        grammar[i]->is_change = 0;
      }
    }
    if(start_over == 0) return;
  }
}


void lhs_productions() {
  char c = (char)(*yylval.str);
  // create a new tree head node(lhs)
  tree_head *node = create_lhs();
  // add node to the grammar, which is an
  // array of lhs nonterminals
  grammar[g_idx] = node; 
  // move current grammar index
  g_idx++;
  // increase grammar size
  grammar_size++;
}

void rhs_productions() {
  char c = (char)(*yylval.str);
  // create a tree list for tree heads children(rhs)
  tree_list *new_list = create_lhs_children();
  // create a node to use as the head of rhs production
  // in case concat children exist on rhs of rhs
  tree_node *new_node = create_node();
  // create head node for rhs line 1
  new_list->head = new_node;
  // update size of list
  new_list->size++;
  // insert list into array of lists
  grammar[g_idx-1]->children[grammar[g_idx-1]->size++] = new_list;

  // increment the children index
  c_idx++;
}

void or_rhs_productions() {
  char c = (char)(*yylval.str);
  if(epsilon == 1) {
    epsilon = 0; 
    c = '@';
    
  }
  // create a tree list for tree heads children(rhs)
  tree_list *new_list = create_lhs_children();
  // create a node to use as the head of this or'd rhs production
  tree_node *new_node = create_node();
  // if epsilon is the current production, change to special char
  if(c == '@') new_node->letter = c;
  // create head node for rhs line n
  new_list->head = new_node;
  // update size of list
  new_list->size++;
  // insert into array of lists
  grammar[g_idx-1]->children[grammar[g_idx-1]->size++] = new_list;
  c_idx++;
}

void rhs_concat() {
  char c = (char)(*yylval.str);
  tree_node *new_node = create_node();
  // printf("g_idx: %d c_idx : %d\n", g_idx, c_idx);
  // insert into list of current grammar[idx] and grammars children[idx]
  insert_node(new_node);
}

void A() {
  if(lookahead == NT) {
    B(); A_prime();
  }
  else {
    print_error();
    exit(1);
  }
}

void A_prime() {
  if(lookahead == NT) {
    B(); A_prime();
  }
  else if(lookahead == 0) {
    return;
  }
  else {
    print_error();
    exit(2);
  }
}

void B() {
  if(lookahead == NT) {
    lhs_productions(); match(NT); match(GOES); 
    C(); match(SEMI); c_idx = 0; is_or = 0; match(EOL);
  }
  else {
    print_error();
    exit(3);
  }
}

void C() {
  if(lookahead == NT || lookahead == T || lookahead == EOL) {
    D(); C_prime();
  }
  else {
    print_error();
    exit(4);
  }
}

void C_prime() {
  if(lookahead == OR) {
    match(OR); 
    if(lookahead == EOL) epsilon = 1;
    is_or = 1; D(); is_or = 0; C_prime();
  }
  else if(lookahead == SEMI) {
    return;
  }
  else {
    print_error();
    exit(5);
  }
}

void D() {
  if(lookahead == NT) {
    if(is_or == 0) 
      if(concat == 1) rhs_concat(); 
      else rhs_productions(); 
    else if(is_or == 1) 
      if(concat == 1) rhs_concat();
      else or_rhs_productions();
    match(NT); concat = 1; D();
  }
  else if(lookahead == T) {
    if(is_or == 0)
      if(concat == 1) rhs_concat();
      else rhs_productions();
    else if(is_or == 1)
      if(concat == 1) rhs_concat();
      else or_rhs_productions();
    match(T); concat = 1; D();
  }
  else if(lookahead == EOL) {
    concat = 0; 
    if(epsilon == 1)
      or_rhs_productions();  
    match(EOL);
  }
  else {
    print_error();
    exit(6);
  }
}


void match(int symbol) {
  if(symbol == lookahead) {
    lookahead = yylex();
  }
  else {
    printf("unexpected \'%s\'\n", yylval.str);
    exit(7);
  }
}

void print_error() {
  switch(lookahead) {
    case NT:
      printf("unexpected \'%s\'\n", yylval.str);
      break;
    case T:
      printf("unexpected \'%s\'\n", yylval.str);
      break;
    case OR:
      printf("unexpected \'%s\'\n", yylval.str);
      break;
    case SEMI:
      printf("unexpected \'%s\'\n", yylval.str);
      break;
    case GOES:
      printf("unexpected \'%s\'\n", yylval.str);
      break;
    case EOL:
      printf("unexpected \'EOL\'\n");
      break;
  }
}

int main(int argc, char **argv) {
  lookahead = yylex();

  
  A();

  print_grammar();

  build_first_set();

  printf("First Sets\n");

  for(int i = 0; i < grammar_size; i++) {
    printf("%c: ", grammar[i]->letter);
    tree_node *tmp = grammar[i]->first_set->head;
    while(tmp != NULL) {
      if((int)tmp->letter == 64)
        printf("epsilon ");
      else
        printf("%c ", tmp->letter);
      tmp = tmp->next;
    }
    printf("\n");
  }

  build_follow_set();
  printf("Follow Sets\n");

  for(int i = 0; i < grammar_size; i++) {
    printf("%c: ", grammar[i]->letter);
    tree_node *tmp = grammar[i]->follow_set->head;
    while(tmp != NULL) {
      printf("%c ", tmp->letter);
      tmp = tmp->next;
    }
    printf("\n");
  }
  return 0;
}

int yyerror(char *errmsg) {
  fprintf(stderr, "%s\n", errmsg);
}
