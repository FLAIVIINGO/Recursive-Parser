%{
#include "p2.tab.h"
%}

%s PRODUCTION
%s NEWPROD

ws      [ ]

%%
<INITIAL>[A-Z]         { 
                         BEGIN PRODUCTION; 
                         yylval.str = strdup(yytext); return NT; 
                       }
<INITIAL>[a-z]         {
                         yylval.str = strdup(yytext); return T;
                       }
<INITIAL>[\n]          { ; }
<PRODUCTION>[A-Z]      {
                         yylval.str = strdup(yytext); return NT; 
                       }
<PRODUCTION>[a-z]      {  
                         yylval.str = strdup(yytext); return T;     
                       }
<PRODUCTION>[-][-][>]  { 
                         yylval.str = strdup(yytext); return GOES;     
                       }
<PRODUCTION>[;]        { BEGIN NEWPROD; 
                         yylval.str = strdup(yytext); return SEMI;     
                       }
<PRODUCTION>[|]        { 
                         yylval.str = strdup(yytext); return OR;       
                       }
<PRODUCTION>[\n]       { 
                         yylval.str = strdup(yytext); return EOL;      
                       }
<INITIAL,PRODUCTION>{ws}+      { ; }
<NEWPROD>[\n]          { BEGIN INITIAL; 
                         yylval.str = strdup(yytext); return EOL; 
                       }
%%

