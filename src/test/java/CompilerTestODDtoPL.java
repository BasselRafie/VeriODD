
import static org.junit.jupiter.api.Assertions.*;

import odd.ODDLexer;
import odd.ODDParser;
import odd.ODDVisitorPropositionalLogic;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.jupiter.api.Test;

public class CompilerTestODDtoPL {

    String compiler(String inputString){
        ODDVisitorPropositionalLogic ODDVisitorPropositionalLogic = new ODDVisitorPropositionalLogic();
        CodePointCharStream input = CharStreams.fromString(inputString);
        ODDLexer lexer = new ODDLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        ODDParser parser = new ODDParser(tokens);
        ParseTree tree = parser.input();
        String result = ODDVisitorPropositionalLogic.visit(tree);
        return result;
    }

    @Test
    void testmodule1() {
        String inputString =
                "testmodule1:true";

        String expected =
                "testmodule1:=\n" +
                        "[testmodule1]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testmodule2() {
        String inputString =
                "testmodule2: false";

        String expected =
                "testmodule2:=\n" +
                        "[(!testmodule2)]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testmodule3() {
        String inputString =
                "testmodule3: = 12";

        String expected =
                "testmodule3:=\n" +
                        "[(testmodule3 = 12)]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testmodule4() {
        String inputString =
                "testmodule4: <= 12";

        String expected =
                "testmodule4:=\n" +
                        "[(testmodule4 <= 12)]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testmodule5() {
        String inputString =
                "testmodule5: variable";

        String expected =
                "testmodule5:=\n" +
                        "[(testmodule5 = variable)]";

        assertEquals(expected,compiler(inputString));
    }

    @Test
    void testmodule6() {
        String inputString =
                "testmodule6:\n" +
                        "   - variable1\n" +
                        "   - variable2";

        String expected =
                "testmodule6:=\n" +
                        "[((testmodule6 = variable1) | (testmodule6 = variable2))]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testmodule7() {
        String inputString =
                "testmodule7:\n" +
                        "   - = 15\n" +
                        "   - = 15.5";

        String expected =
                "testmodule7:=\n" +
                        "[((testmodule7 = 15) | (testmodule7 = 15.5))]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testmodule8() {
        String inputString =
                "testmodule8:\n" +
                        "   -  false\n" +
                        "   -  true";

        String expected =
                "testmodule8:=\n" +
                        "[((!testmodule8) | testmodule8)]";

        assertEquals(expected,compiler(inputString));
    }


    @Test
    void testinclude_and1() {
        String inputString =
                "testmodule1:\n" +
                        "    INCLUDE_AND:\n" +
                        "        -statement";

        String expected =
                "testmodule1:=\n" +
                        "[statement]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testinclude_and2() {
        String inputString =
                "testmodule2:\n" +
                        "    INCLUDE_AND:\n" +
                        "        statement: true";

        String expected =
                "testmodule2:=\n" +
                        "[statement]";

        assertEquals(expected,compiler(inputString));
    }


    @Test
    void testinclude_and3() {
        String inputString =
                "testmodule3:\n" +
                        "    INCLUDE_AND:\n" +
                        "        statement: false";

        String expected =
                "testmodule3:=\n" +
                        "[(!statement)]";

        assertEquals(expected,compiler(inputString));
    }

    @Test
    void testinclude_and4() {
        String inputString =
                "testmodule4:\n" +
                        "    INCLUDE_AND:\n" +
                        "        statement: =12";

        String expected =
                "testmodule4:=\n" +
                        "[(statement = 12)]";

        assertEquals(expected,compiler(inputString));
    }

    @Test
    void testinclude_and5() {
        String inputString =
                "testmodule5:\n" +
                        "    INCLUDE_AND:\n" +
                        "        statement: =12.55";

        String expected =
                "testmodule5:=\n" +
                        "[(statement = 12.55)]";

        assertEquals(expected,compiler(inputString));
    }

    @Test
    void testinclude_and6() {
        String inputString =
                "testmodule6:\n" +
                        "    INCLUDE_AND:\n" +
                        "        statement: variable";

        String expected =
                "testmodule6:=\n" +
                        "[(statement = variable)]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testinclude_and7() {
        String inputString =
                "testmodule7:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - statement1\n"+
                        "        - statement2";

        String expected =
                "testmodule7:=\n" +
                        "[(statement1 & statement2)]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testinclude_and8() {
        String inputString =
                "testmodule8:\n" +
                        "    INCLUDE_AND:\n" +
                        "        statement1: true\n"+
                        "        statement2: true";

        String expected =
                "testmodule8:=\n" +
                        "[(statement1 & statement2)]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testinclude_and9() {
        String inputString = "testmodule9:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: false\n" +
                "        statement2: true";

        String expected =
                "testmodule9:=\n" +
                        "[((!statement1) & statement2)]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and10(){
        String inputString = "testmodule10:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: true\n"+
                "        statement2: false";

        String expected =
                "testmodule10:=\n" +
                        "[(statement1 & (!statement2))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and11(){
        String inputString = "testmodule11:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: false\n"+
                "        statement2: false";

        String expected =
                "testmodule11:=\n" +
                        "[((!statement1) & (!statement2))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and12(){
        String inputString = "testmodule12:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13";

        String expected =
                "testmodule12:=\n" +
                        "[((statement1 = 12) & (statement2 = 13))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and13(){
        String inputString = "testmodule13:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13.5";

        String expected =
                "testmodule13:=\n" +
                        "[((statement1 = 12) & (statement2 = 13.5))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and14(){
        String inputString = "testmodule14:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: variable1\n"+
                "        statement2: variable2";

        String expected =
                "testmodule14:=\n" +
                        "[((statement1 = variable1) & (statement2 = variable2))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and15(){
        String inputString = "testmodule15:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1";

        String expected =
                "testmodule15:=\n" +
                        "[(statement1 = variable1)]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and16(){
        String inputString = "testmodule16:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2";

        String expected =
                "testmodule16:=\n" +
                        "[((statement1 = variable1) | (statement1 = variable2))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and199(){
        String inputString = "testmodule199:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2\n"+
                "            - variable3";

        String expected =
                "testmodule199:=\n" +
                        "[((statement1 = variable1) | (statement1 = variable2) | (statement1 = variable3))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and17(){
        String inputString = "testmodule17:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - true\n"+
                "            - false";

        String expected =
                "testmodule17:=\n" +
                        "[(statement1 | (!statement1))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and18(){
        String inputString = "testmodule18:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13";

        String expected =
                "testmodule18:=\n" +
                        "[((statement1 = 12) | (statement1 = 13))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and19(){
        String inputString = "testmodule19:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5";

        String expected =
                "testmodule19:=\n" +
                        "[((statement1 = 12) | (statement1 = 13.5))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and20(){
        String inputString = "testmodule20:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "        - statement2";
        String expected =
                "testmodule20:=\n" +
                        "[((statement1 = 12) & statement2)]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and21(){
        String inputString = "testmodule21:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        - statement2";

        String expected =
                "testmodule21:=\n" +
                        "[(((statement1 = 12) | (statement1 = 13.5)) & statement2)]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and22(){
        String inputString = "testmodule22:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2: >= 12";

        String expected =
                "testmodule22:=\n" +
                        "[(((statement1 = 12) | (statement1 = 13.5)) & (statement2 >= 12))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and23(){
        String inputString = "testmodule23:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2: < 15";

        String expected =
                "testmodule23:=\n" +
                        "[(((statement1 = 12) | (statement1 = 13.5)) & (statement2 < 15))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and24(){
        String inputString = "testmodule24:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2: false";

        String expected =
                "testmodule24:=\n" +
                        "[(((statement1 = 12) | (statement1 = 13.5)) & (!statement2))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and25(){
        String inputString = "testmodule25:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - >= 12\n"+
                "            - <= 13.5\n"+
                "        statement2:\n"+
                "            - = 25";

        String expected =
                "testmodule25:=\n" +
                        "[(((statement1 >= 12) | (statement1 <= 13.5)) & (statement2 = 25))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and26(){
        String inputString = "testmodule26:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - >= 12\n"+
                "            - <= 13.5\n"+
                "        statement2:\n"+
                "            - = 26\n"+
                "            - = 26.5";

        String expected =
                "testmodule26:=\n" +
                        "[(((statement1 >= 12) | (statement1 <= 13.5)) & ((statement2 = 26) | (statement2 = 26.5)))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and27(){
        String inputString = "testmodule27:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2\n"+
                "        statement2:\n"+
                "            - <= 26\n"+
                "            - >= 26.5";
        String expected =
                "testmodule27:=\n" +
                        "[(((statement1 = variable1) | (statement1 = variable2)) & ((statement2 <= 26) | (statement2 >= 26.5)))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and28(){
        String inputString = "testmodule28:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2\n"+
                "        statement2:\n"+
                "            - variable3\n"+
                "            - variable4\n";
        String expected =
                "testmodule28:=\n" +
                        "[(((statement1 = variable1) | (statement1 = variable2)) & ((statement2 = variable3) | (statement2 = variable4)))]";

        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testinclude_and29(){
        String inputString = "testmodule29:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2\n"+
                "        statement2:\n"+
                "            - variable3\n"+
                "            - variable4\n"+
                "        statement3:\n"+
                "            - variable5\n"+
                "            - variable6\n";
        String expected =
                "testmodule29:=\n" +
                        "[(((statement1 = variable1) | (statement1 = variable2)) & ((statement2 = variable3) | (statement2 = variable4)) & ((statement3 = variable5) | (statement3 = variable6)))]";

        assertEquals(expected, compiler(inputString));

    }

    //EXCLUDE_OR
    @Test
    void testexclude_or1() {
        String inputString = "testmodule1:\n" +
                "    EXCLUDE_OR:\n" +
                "        -statement";

        String expected =
                    "testmodule1:=\n" +
                            "[(!statement)]";
        assertEquals(expected, compiler(inputString));
    }

    @Test
    void testexclude_or2(){
        String inputString = "testmodule2:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: true";

        String expected =
                "testmodule2:=\n" +
                        "[(!statement)]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or3(){
        String inputString = "testmodule3:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: false";

        String expected =
                "testmodule3:=\n" +
                        "[(!(!statement))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or4(){
        String inputString = "testmodule4:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: = 12";

        String expected =
                "testmodule4:=\n" +
                        "[(!(statement = 12))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or5(){
        String inputString = "testmodule5:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: = 12.5";

        String expected =
                "testmodule5:=\n" +
                        "[(!(statement = 12.5))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or6(){
        String inputString = "testmodule6:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: variable";

        String expected =
                "testmodule6:=\n" +
                        "[(!(statement = variable))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or7(){
        String inputString = "testmodule7:\n" +
                "    EXCLUDE_OR:\n" +
                "        - statement1\n"+
                "        - statement2";

        String expected =
                "testmodule7:=\n" +
                        "[(!(statement1 | statement2))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or8(){
        String inputString = "testmodule8:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: true\n"+
                "        statement2: true";

        String expected =
                "testmodule8:=\n" +
                        "[(!(statement1 | statement2))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or9(){
        String inputString = "testmodule9:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: false\n"+
                "        statement2: true";

        String expected =
                "testmodule9:=\n" +
                        "[(!((!statement1) | statement2))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or10(){
        String inputString =
                "testmodule10:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1: true\n"+
                        "        statement2: false";

        String expected =
                "testmodule10:=\n" +
                        "[(!(statement1 | (!statement2)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or11(){
        String inputString = "testmodule11:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: false\n"+
                "        statement2: false";

        String expected =
                "testmodule11:=\n" +
                        "[(!((!statement1) | (!statement2)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or12(){
        String inputString = "testmodule12:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13";

        String expected =
                "testmodule12:=\n" +
                        "[(!((statement1 = 12) | (statement2 = 13)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or13(){
        String inputString = "testmodule13:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13.5";

        String expected =
                "testmodule13:=\n" +
                        "[(!((statement1 = 12) | (statement2 = 13.5)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or14(){
        String inputString = "testmodule14:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: variable1\n"+
                "        statement2: variable2";

        String expected =
                "testmodule14:=\n" +
                        "[(!((statement1 = variable1) | (statement2 = variable2)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or15(){
        String inputString = "testmodule15:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - variable1";

        String expected =
                "testmodule15:=\n" +
                        "[(!(statement1 = variable1))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or16(){
        String inputString = "testmodule16:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2";

        String expected =
                "testmodule16:=\n" +
                        "[(!((statement1 = variable1) | (statement1 = variable2)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or17(){
        String inputString = "testmodule17:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - true\n"+
                "            - false";
        String expected =
                "testmodule17:=\n" +
                        "[(!(statement1 | (!statement1)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or18(){
        String inputString =
                "testmodule18:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - = 12\n"+
                        "            - = 13";
        String expected =
                "testmodule18:=\n" +
                        "[(!((statement1 = 12) | (statement1 = 13)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or19(){
        String inputString =
                "testmodule19:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - = 12\n"+
                        "            - = 13.5";
        String expected =
                "testmodule19:=\n" +
                        "[(!((statement1 = 12) | (statement1 = 13.5)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or20(){
        String inputString =
                "testmodule20:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - = 12\n"+
                        "        - statement2";
        String expected =
                "testmodule20:=\n" +
                        "[(!((statement1 = 12) | statement2))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or21(){
        String inputString =
                "testmodule21:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - = 12\n"+
                        "            - = 13.5\n"+
                        "        - statement2";

        String expected =
                "testmodule21:=\n" +
                        "[(!(((statement1 = 12) | (statement1 = 13.5)) | statement2))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or22(){
        String inputString =
                "testmodule22:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - >= 12\n"+
                        "            - <= 13.5\n"+
                        "        - statement2";
        String expected =
                "testmodule22:=\n" +
                        "[(!(((statement1 >= 12) | (statement1 <= 13.5)) | statement2))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or23(){
        String inputString =
                "testmodule23:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - >= 12\n"+
                        "            - <= 13.5\n"+
                        "        statement2: = 12";
        String expected =
                "testmodule23:=\n" +
                        "[(!(((statement1 >= 12) | (statement1 <= 13.5)) | (statement2 = 12)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or24(){
        String inputString =
                "testmodule24:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - > 12\n"+
                        "            - < 13.5\n"+
                        "        statement2: false";

        String expected =
                "testmodule24:=\n" +
                        "[(!(((statement1 > 12) | (statement1 < 13.5)) | (!statement2)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or25(){
        String inputString =
                "testmodule25:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - = 12\n"+
                        "            - = 13.5\n"+
                        "        statement2:\n"+
                        "            - = 25";

        String expected =
                "testmodule25:=\n" +
                        "[(!(((statement1 = 12) | (statement1 = 13.5)) | (statement2 = 25)))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or26(){
        String inputString =
                "testmodule26:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - = 12\n"+
                        "            - = 13.5\n"+
                        "        statement2:\n"+
                        "            - = 26\n"+
                        "            - = 26.5";
        String expected =
                "testmodule26:=\n" +
                        "[(!(((statement1 = 12) | (statement1 = 13.5)) | ((statement2 = 26) | (statement2 = 26.5))))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or27(){
        String inputString =
                "testmodule27:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - variable1\n"+
                        "            - variable2\n"+
                        "        statement2:\n"+
                        "            - <= 26\n"+
                        "            - >= 26.5";
        String expected =
                "testmodule27:=\n" +
                        "[(!(((statement1 = variable1) | (statement1 = variable2)) | ((statement2 <= 26) | (statement2 >= 26.5))))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or28(){
        String inputString =
                "testmodule28:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - variable1\n"+
                        "            - variable2\n"+
                        "        statement2:\n"+
                        "            - variable3\n"+
                        "            - variable4\n";
        String expected =
                "testmodule28:=\n" +
                        "[(!(((statement1 = variable1) | (statement1 = variable2)) | ((statement2 = variable3) | (statement2 = variable4))))]";
        assertEquals(expected, compiler(inputString));
    }
    @Test
    void testexclude_or29(){
        String inputString =
                "testmodule29:\n" +
                        "    EXCLUDE_OR:\n" +
                        "        statement1:\n"+
                        "            - variable1\n"+
                        "            - variable2\n"+
                        "        statement2:\n"+
                        "            - variable3\n"+
                        "            - variable4\n"+
                        "        statement3:\n"+
                        "            - variable5\n"+
                        "            - variable6\n";
        String expected =
                "testmodule29:=\n" +
                        "[(!(((statement1 = variable1) | (statement1 = variable2)) | ((statement2 = variable3) | (statement2 = variable4)) | ((statement3 = variable5) | (statement3 = variable6))))]";
        assertEquals(expected, compiler(inputString));
    }
    // INCLUDE_AND & EXCLUDE_OR Combined
    @Test
    void test_include_and_exclude_or1(){
        String inputString =
                "testmodule1:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - statement1\n"+
                        "    EXCLUDE_OR:\n" +
                        "        - statement2";

        String expected =
                "testmodule1:=\n" +
                        "[statement1 & (!statement2)]";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void test_include_and_exclude_or2(){
        String inputString =
                "testmodule2:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - statement1\n"+
                        "        - statement2\n"+
                        "    EXCLUDE_OR:\n" +
                        "        - statement3\n"+
                        "        - statement4";

        String expected =
                "testmodule2:=\n" +
                        "[(statement1 & statement2) & (!(statement3 | statement4))]";

        assertEquals(expected,compiler(inputString));

    }
    @Test
    void test_multiple_modules1(){
        String inputString =
                "testmodule1:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - statement1\n"+
                        "        - statement2\n"+
                        "    EXCLUDE_OR:\n" +
                        "        - statement3\n"+
                        "        - statement4\n"+
                        "testmodule2:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - statement1\n"+
                        "        - statement2\n"+
                        "    EXCLUDE_OR:\n" +
                        "        - statement3\n"+
                        "        - statement4";
        String expected=
                "testmodule1:=\n" +
                        "[(statement1 & statement2) & (!(statement3 | statement4))]\n" +
                        "\n" +
                        "testmodule2:=\n" +
                        "[(statement1 & statement2) & (!(statement3 | statement4))]";

        assertEquals(expected,compiler(inputString));

    }
    @Test
    void test_multiple_modules2() {
        String inputString =
                "testmodule1:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - testmodule2\n" +
                        "        - statement2\n" +
                        "testmodule2:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - statement1\n" +
                        "        - statement2";
        String expected=
                "testmodule1:=\n" +
                        "[(testmodule2 & statement2)]\n" +
                        "\n" +
                        "testmodule2:=\n" +
                        "[(statement1 & statement2)]";

        assertEquals(expected,compiler(inputString));

    }


}
