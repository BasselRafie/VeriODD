grammar ODD;

RELATIONALOPERATOR
                : '<='
                | '>='
                | '='
                | '<'
                | '>';

TAB    :'    ';
DTAB   :'        ';
TTAB   :'            ';

MINUS: '-';
INTEGER : MINUS?[0-9]+;
DECIMAL : MINUS?[0-9]+'.'[0-9]+;
MEASURMENT: (('km'|'m'|'cm'|'ft'|'inch')('/h'|'/m'|'/s'|'/ms')?)|'%'|'mph'|'mpm'|'mps'|'mpms';
TRUE  : 'true'|'True'|'TRUE';
FALSE : 'false'|'False'|'FALSE';

INCLUDE_AND  : (TAB)'INCLUDE_AND:\n';
INCLUDE_OR   : (TAB)'INCLUDE_OR:\n';
EXCLUDE_AND  : (TAB)'EXCLUDE_AND:\n';
EXCLUDE_OR   : (TAB)'EXCLUDE_OR:\n';

ALPHANUMERIC: [a-zA-Z]([a-zA-Z0-9_]+)?;

ID   : (DTAB)?(ALPHANUMERIC)WS*(':\n'|':') {setText(getText().replaceAll("\\s|\n",""));};

BOOL : (TAB|TTAB)?'-'?WS*(TRUE|FALSE)WS*('\n' | EOF) {setText(getText().replaceAll("\\s|-|\n", ""));};
INT  : (TAB|TTAB)?'-'?WS*(RELATIONALOPERATOR WS* INTEGER)WS*MEASURMENT?WS*('\n' | EOF) {setText(getText().replaceAll("^\\s+-|\\s+|\n", ""));};
DEC  : (TAB|TTAB)?'-'?WS*(RELATIONALOPERATOR WS* DECIMAL)WS*MEASURMENT?WS*('\n' | EOF) {setText(getText().replaceAll("^\\s+-|\\s+|\n", ""));};
STR  : (TAB|TTAB)?'-'?WS*(ALPHANUMERIC)WS*('\n' | EOF) {setText(getText().replaceAll("\\s+|-|\n", ""));};
MODULE_ID_REF : (DTAB)?'-'WS*(ALPHANUMERIC)WS*('\n' | EOF) {setText(getText().replaceAll("\\s+|-|\n", ""));};

WS:[ \t\n]+ -> skip;


input
    : module+
    | EOF;
module
    : ID logicalexpression+
    | statement;
logicalexpression
    : include_and
    | include_or
    | exclude_and
    | exclude_or;
include_and
    : INCLUDE_AND statement+;
include_or
    : INCLUDE_OR  statement+;
exclude_and
    : EXCLUDE_AND statement+;
exclude_or
    : EXCLUDE_OR  statement+;
statement
    : ID condition+
    | MODULE_ID_REF;
condition
    : BOOL
    | INT
    | DEC
    | STR;