
import static org.junit.jupiter.api.Assertions.*;

import odd.ODDLexer;
import odd.ODDParser;
import odd.ODDVistorSMTLIB;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.jupiter.api.Test;

public class CompilerTestODDtoSMTLIB {

    String compiler(String inputString){
        ODDVistorSMTLIB ODDVistorSMTLIB = new ODDVistorSMTLIB();
        CodePointCharStream input = CharStreams.fromString(inputString);
        ODDLexer lexer = new ODDLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        ODDParser parser = new ODDParser(tokens);
        ParseTree tree = parser.input();
        String result = ODDVistorSMTLIB.visit(tree);
        return result;
    }

    @Test
    void testinclude_and1() {
        String inputString = "testmodule1:\n" +
            "    INCLUDE_AND:\n" +
            "        -statement";


        assertEquals(compiler(inputString),"(declare-const statement Bool)\n" +
                "\n" +
                "(define-fun testmodule1 () Bool\n" +
                "statement\n" +
                ")\n");
    }

    @Test
    void testinclude_and2(){
        String inputString = "testmodule2:\n" +
                "    INCLUDE_AND:\n" +
                "        statement: true";

        assertEquals(compiler(inputString),"(declare-const statement Bool)\n" +
                "\n" +
                "(define-fun testmodule2 () Bool\n" +
                "statement\n" +
                ")\n");
    }
    @Test
    void testinclude_and3(){
         String inputString = "testmodule3:\n" +
                "    INCLUDE_AND:\n" +
                "        statement: false";

        assertEquals(compiler(inputString),"(declare-const statement Bool)\n" +
                "\n" +
                "(define-fun testmodule3 () Bool\n" +
                "(not statement)\n" +
                ")\n");
    }
    @Test
    void testinclude_and4(){
        String inputString = "testmodule4:\n" +
                "    INCLUDE_AND:\n" +
                "        statement: = 12";

        assertEquals(compiler(inputString),"(declare-const statement Int)\n" +
                "\n" +
                "(define-fun testmodule4 () Bool\n" +
                "(= statement 12)\n" +
                ")\n");
    }
    @Test
    void testinclude_and5(){
        String inputString = "testmodule5:\n" +
                "    INCLUDE_AND:\n" +
                "        statement: = 12.5";

        assertEquals(compiler(inputString),"(declare-const statement Real)\n" +
                "\n" +
                "(define-fun testmodule5 () Bool\n" +
                "(= statement 12.5)\n" +
                ")\n");
    }
    @Test
    void testinclude_and6(){
        String inputString = "testmodule6:\n" +
                "    INCLUDE_AND:\n" +
                "        statement: variable";

        assertEquals(compiler(inputString),"(declare-const statement String)\n" +
                "\n" +
                "(define-fun testmodule6 () Bool\n" +
                "(= statement \"variable\")\n" +
                ")\n");
    }
    @Test
    void testinclude_and7(){
         String inputString = "testmodule7:\n" +
                "    INCLUDE_AND:\n" +
                "        - statement1\n"+
                "        - statement2";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule7 () Bool\n" +
                "(and statement1 statement2)\n" +
                ")\n");
    }
    @Test
    void testinclude_and8(){
        String inputString = "testmodule8:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: true\n"+
                "        statement2: true";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule8 () Bool\n" +
                "(and statement1 statement2)\n" +
                ")\n");
    }
    @Test
    void testinclude_and9(){
        String inputString = "testmodule9:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: false\n"+
                "        statement2: true";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule9 () Bool\n" +
                "(and (not statement1) statement2)\n" +
                ")\n");
    }
    @Test
    void testinclude_and10(){
        String inputString = "testmodule10:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: true\n"+
                "        statement2: false";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule10 () Bool\n" +
                "(and statement1 (not statement2))\n" +
                ")\n");
    }
    @Test
    void testinclude_and11(){
        String inputString = "testmodule11:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: false\n"+
                "        statement2: false";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule11 () Bool\n" +
                "(and (not statement1) (not statement2))\n" +
                ")\n");
    }
    @Test
    void testinclude_and12(){
        String inputString = "testmodule12:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13";

        assertEquals(compiler(inputString),"(declare-const statement1 Int)\n" +
                "(declare-const statement2 Int)\n" +
                "\n" +
                "(define-fun testmodule12 () Bool\n" +
                "(and (= statement1 12) (= statement2 13))\n" +
                ")\n");
    }
    @Test
    void testinclude_and13(){
        String inputString = "testmodule13:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13.5";

        assertEquals(compiler(inputString),"(declare-const statement1 Int)\n" +
                "(declare-const statement2 Real)\n" +
                "\n" +
                "(define-fun testmodule13 () Bool\n" +
                "(and (= statement1 12) (= statement2 13.5))\n" +
                ")\n");
    }
    @Test
    void testinclude_and14(){
        String inputString = "testmodule14:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1: variable1\n"+
                "        statement2: variable2";

        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +
                "(declare-const statement2 String)\n" +
                "\n" +
                "(define-fun testmodule14 () Bool\n" +
                "(and (= statement1 \"variable1\") (= statement2 \"variable2\"))\n" +
                ")\n");
    }
    @Test
    void testinclude_and15(){
        String inputString = "testmodule15:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1";

        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +

                "\n" +
                "(define-fun testmodule15 () Bool\n" +
                "(= statement1 \"variable1\")\n" +
                ")\n");
    }
    @Test
    void testinclude_and16(){
        String inputString = "testmodule16:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2";

        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +

                "\n" +
                "(define-fun testmodule16 () Bool\n" +
                "(or (= statement1 \"variable1\") (= statement1 \"variable2\"))\n" +
                ")\n");
    }
    @Test
    void testinclude_and199(){
        String inputString = "testmodule199:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2\n"+
                "            - variable3";

        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +


                "\n" +
                "(define-fun testmodule199 () Bool\n" +
                "(or (= statement1 \"variable1\") (= statement1 \"variable2\") (= statement1 \"variable3\"))\n" +
                ")\n");
    }
    @Test
    void testinclude_and17(){
        String inputString = "testmodule17:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - true\n"+
                "            - false";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +

                "\n" +
                "(define-fun testmodule17 () Bool\n" +
                "(or statement1 (not statement1))\n" +
                ")\n");
    }
    @Test
    void testinclude_and18(){
        String inputString = "testmodule18:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13";

        assertEquals(compiler(inputString),"(declare-const statement1 Int)\n" +

                "\n" +
                "(define-fun testmodule18 () Bool\n" +
                "(or (= statement1 12) (= statement1 13))\n" +
                ")\n");
    }
    @Test
    void testinclude_and19(){
        String inputString = "testmodule19:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5";

        assertEquals(compiler(inputString),"(declare-const statement1 Real)\n" +

                "\n" +
                "(define-fun testmodule19 () Bool\n" +
                "(or (= statement1 12) (= statement1 13.5))\n" +
                ")\n");
    }
    @Test
    void testinclude_and20(){
        String inputString = "testmodule20:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "        - statement2";

        assertEquals(compiler(inputString),"(declare-const statement1 Int)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule20 () Bool\n" +
                "(and (= statement1 12) statement2)\n" +
                ")\n");
    }
    @Test
    void testinclude_and21(){
        String inputString = "testmodule21:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        - statement2";

        assertEquals(compiler(inputString),"(declare-const statement1 Real)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule21 () Bool\n" +
                "(and (or (= statement1 12) (= statement1 13.5)) statement2)\n" +
                ")\n");
    }
    @Test
    void testinclude_and22(){
        String inputString = "testmodule22:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        - statement2";

        assertEquals(compiler(inputString),"(declare-const statement1 Real)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule22 () Bool\n" +
                "(and (or (= statement1 12) (= statement1 13.5)) statement2)\n" +
                ")\n");
    }
    @Test
    void testinclude_and23(){
        String inputString = "testmodule23:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2: = 12";

        assertEquals(compiler(inputString),"(declare-const statement1 Real)\n" +
                "(declare-const statement2 Int)\n" +
                "\n" +
                "(define-fun testmodule23 () Bool\n" +
                "(and (or (= statement1 12) (= statement1 13.5)) (= statement2 12))\n" +
                ")\n");
    }
    @Test
    void testinclude_and24(){
        String inputString = "testmodule24:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2: false";

        assertEquals(compiler(inputString),"(declare-const statement1 Real)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule24 () Bool\n" +
                "(and (or (= statement1 12) (= statement1 13.5)) (not statement2))\n" +
                ")\n");
    }
    @Test
    void testinclude_and25(){
        String inputString = "testmodule25:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2:\n"+
                "            - = 25";

        assertEquals(compiler(inputString),"(declare-const statement1 Real)\n" +
                "(declare-const statement2 Int)\n" +
                "\n" +
                "(define-fun testmodule25 () Bool\n" +
                "(and (or (= statement1 12) (= statement1 13.5)) (= statement2 25))\n" +
                ")\n");
    }
    @Test
    void testinclude_and26(){
        String inputString = "testmodule26:\n" +
                "    INCLUDE_AND:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2:\n"+
                "            - = 26\n"+
                "            - = 26.5";

        assertEquals(compiler(inputString),"(declare-const statement1 Real)\n" +
                "(declare-const statement2 Real)\n" +
                "\n" +
                "(define-fun testmodule26 () Bool\n" +
                "(and (or (= statement1 12) (= statement1 13.5)) (or (= statement2 26) (= statement2 26.5)))\n" +
                ")\n");
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
        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +
                "(declare-const statement2 Real)\n" +
                "\n" +
                "(define-fun testmodule27 () Bool\n" +
                "(and (or (= statement1 \"variable1\") (= statement1 \"variable2\")) (or (<= statement2 26) (>= statement2 26.5)))\n" +
                ")\n");
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
        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +
                "(declare-const statement2 String)\n" +
                "\n" +
                "(define-fun testmodule28 () Bool\n" +
                "(and (or (= statement1 \"variable1\") (= statement1 \"variable2\")) (or (= statement2 \"variable3\") (= statement2 \"variable4\")))\n" +
                ")\n");
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
        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +
                "(declare-const statement2 String)\n" +
                "(declare-const statement3 String)\n" +
                "\n" +
                "(define-fun testmodule29 () Bool\n" +
                "(and (or (= statement1 \"variable1\") (= statement1 \"variable2\")) (or (= statement2 \"variable3\") (= statement2 \"variable4\")) (or (= statement3 \"variable5\") (= statement3 \"variable6\")))\n" +
                ")\n");


    }

    //EXCLUDE_OR
    @Test
    void testexclude_or1() {
        String inputString = "testmodule1:\n" +
                "    EXCLUDE_OR:\n" +
                "        -statement";

        assertEquals(compiler(inputString),"(declare-const statement Bool)\n" +
                "\n" +
                "(define-fun testmodule1 () Bool\n" +
                "(not statement)\n" +
                ")\n");
    }

    @Test
    void testexclude_or2(){
        String inputString = "testmodule2:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: true";

        assertEquals(compiler(inputString),"(declare-const statement Bool)\n" +
                "\n" +
                "(define-fun testmodule2 () Bool\n" +
                "(not statement)\n" +
                ")\n");
    }
    @Test
    void testexclude_or3(){
        String inputString = "testmodule3:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: false";

        assertEquals(compiler(inputString),"(declare-const statement Bool)\n" +
                "\n" +
                "(define-fun testmodule3 () Bool\n" +
                "(not (not statement))\n" +
                ")\n");
    }
    @Test
    void testexclude_or4(){
        String inputString = "testmodule4:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: = 12";

        assertEquals(compiler(inputString),"(declare-const statement Int)\n" +
                "\n" +
                "(define-fun testmodule4 () Bool\n" +
                "(not (= statement 12))\n" +
                ")\n");
    }
    @Test
    void testexclude_or5(){
        String inputString = "testmodule5:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: = 12.5";

        assertEquals(compiler(inputString),"(declare-const statement Real)\n" +
                "\n" +
                "(define-fun testmodule5 () Bool\n" +
                "(not (= statement 12.5))\n" +
                ")\n");
    }
    @Test
    void testexclude_or6(){
        String inputString = "testmodule6:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement: variable";

        assertEquals(compiler(inputString),"(declare-const statement String)\n" +
                "\n" +
                "(define-fun testmodule6 () Bool\n" +
                "(not (= statement \"variable\"))\n" +
                ")\n");
    }
    @Test
    void testexclude_or7(){
        String inputString = "testmodule7:\n" +
                "    EXCLUDE_OR:\n" +
                "        - statement1\n"+
                "        - statement2";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule7 () Bool\n" +
                "(not (or statement1 statement2))\n" +
                ")\n");
    }
    @Test
    void testexclude_or8(){
        String inputString = "testmodule8:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: true\n"+
                "        statement2: true";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule8 () Bool\n" +
                "(not (or statement1 statement2))\n" +
                ")\n");
    }
    @Test
    void testexclude_or9(){
        String inputString = "testmodule9:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: false\n"+
                "        statement2: true";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule9 () Bool\n" +
                "(not (or (not statement1) statement2))\n" +
                ")\n");
    }
    @Test
    void testexclude_or10(){
        String inputString =
                "testmodule10:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: true\n"+
                "        statement2: false";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule10 () Bool\n" +
                "(not (or statement1 (not statement2)))\n" +
                ")\n");
    }
    @Test
    void testexclude_or11(){
        String inputString = "testmodule11:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: false\n"+
                "        statement2: false";

        assertEquals(compiler(inputString),"(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule11 () Bool\n" +
                "(not (or (not statement1) (not statement2)))\n" +
                ")\n");
    }
    @Test
    void testexclude_or12(){
        String inputString = "testmodule12:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13";

        assertEquals(compiler(inputString),"(declare-const statement1 Int)\n" +
                "(declare-const statement2 Int)\n" +
                "\n" +
                "(define-fun testmodule12 () Bool\n" +
                "(not (or (= statement1 12) (= statement2 13)))\n" +
                ")\n");
    }
    @Test
    void testexclude_or13(){
        String inputString = "testmodule13:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: = 12\n"+
                "        statement2: = 13.5";

        assertEquals(compiler(inputString),"(declare-const statement1 Int)\n" +
                "(declare-const statement2 Real)\n" +
                "\n" +
                "(define-fun testmodule13 () Bool\n" +
                "(not (or (= statement1 12) (= statement2 13.5)))\n" +
                ")\n");
    }
    @Test
    void testexclude_or14(){
        String inputString = "testmodule14:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1: variable1\n"+
                "        statement2: variable2";

        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +
                "(declare-const statement2 String)\n" +
                "\n" +
                "(define-fun testmodule14 () Bool\n" +
                "(not (or (= statement1 \"variable1\") (= statement2 \"variable2\")))\n" +
                ")\n");
    }
    @Test
    void testexclude_or15(){
        String inputString = "testmodule15:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - variable1";

        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +

                "\n" +
                "(define-fun testmodule15 () Bool\n" +
                "(not (= statement1 \"variable1\"))\n" +
                ")\n");
    }
    @Test
    void testexclude_or16(){
        String inputString = "testmodule16:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - variable1\n"+
                "            - variable2";

        assertEquals(compiler(inputString),"(declare-const statement1 String)\n" +

                "\n" +
                "(define-fun testmodule16 () Bool\n" +
                "(not (or (= statement1 \"variable1\") (= statement1 \"variable2\")))\n" +
                ")\n");
    }
    @Test
    void testexclude_or17(){
        String inputString = "testmodule17:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - true\n"+
                "            - false";
        String expected =
                "(declare-const statement1 Bool)\n" +

                "\n" +
                "(define-fun testmodule17 () Bool\n" +
                "(not (or statement1 (not statement1)))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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
                "(declare-const statement1 Int)\n" +
                "\n" +
                "(define-fun testmodule18 () Bool\n" +
                "(not (or (= statement1 12) (= statement1 13)))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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
                "(declare-const statement1 Real)\n" +
                "\n" +
                "(define-fun testmodule19 () Bool\n" +
                "(not (or (= statement1 12) (= statement1 13.5)))\n" +
                ")\n";

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
                "(declare-const statement1 Int)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule20 () Bool\n" +
                "(not (or (= statement1 12) statement2))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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

        String expected = "(declare-const statement1 Real)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule21 () Bool\n" +
                "(not (or (or (= statement1 12) (= statement1 13.5)) statement2))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testexclude_or22(){
        String inputString =
                "testmodule22:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        - statement2";
        String expected =
                "(declare-const statement1 Real)\n" +
                        "(declare-const statement2 Bool)\n" +
                        "\n" +
                        "(define-fun testmodule22 () Bool\n" +
                        "(not (or (or (= statement1 12) (= statement1 13.5)) statement2))\n" +
                        ")\n";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testexclude_or23(){
        String inputString =
                "testmodule23:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2: = 12";
        String expected =
                "(declare-const statement1 Real)\n" +
                "(declare-const statement2 Int)\n" +
                "\n" +
                "(define-fun testmodule23 () Bool\n" +
                "(not (or (or (= statement1 12) (= statement1 13.5)) (= statement2 12)))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
    }
    @Test
    void testexclude_or24(){
        String inputString =
                "testmodule24:\n" +
                "    EXCLUDE_OR:\n" +
                "        statement1:\n"+
                "            - = 12\n"+
                "            - = 13.5\n"+
                "        statement2: false";

        String expected =
                "(declare-const statement1 Real)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule24 () Bool\n" +
                "(not (or (or (= statement1 12) (= statement1 13.5)) (not statement2)))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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

        String expected = "(declare-const statement1 Real)\n" +
                "(declare-const statement2 Int)\n" +
                "\n" +
                "(define-fun testmodule25 () Bool\n" +
                "(not (or (or (= statement1 12) (= statement1 13.5)) (= statement2 25)))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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
                "(declare-const statement1 Real)\n" +
                "(declare-const statement2 Real)\n" +
                "\n" +
                "(define-fun testmodule26 () Bool\n" +
                "(not (or (or (= statement1 12) (= statement1 13.5)) (or (= statement2 26) (= statement2 26.5))))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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
                "(declare-const statement1 String)\n" +
                "(declare-const statement2 Real)\n" +
                "\n" +
                "(define-fun testmodule27 () Bool\n" +
                "(not (or (or (= statement1 \"variable1\") (= statement1 \"variable2\")) (or (<= statement2 26) (>= statement2 26.5))))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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
                "(declare-const statement1 String)\n" +
                "(declare-const statement2 String)\n" +
                "\n" +
                "(define-fun testmodule28 () Bool\n" +
                "(not (or (or (= statement1 \"variable1\") (= statement1 \"variable2\")) (or (= statement2 \"variable3\") (= statement2 \"variable4\"))))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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
                "(declare-const statement1 String)\n" +
                "(declare-const statement2 String)\n" +
                "(declare-const statement3 String)\n" +
                "\n" +
                "(define-fun testmodule29 () Bool\n" +
                "(not (or (or (= statement1 \"variable1\") (= statement1 \"variable2\")) (or (= statement2 \"variable3\") (= statement2 \"variable4\")) (or (= statement3 \"variable5\") (= statement3 \"variable6\"))))\n" +
                ")\n";

        assertEquals(expected,compiler(inputString));
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
                "(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "\n" +
                "(define-fun testmodule1 () Bool\n" +
                "(and statement1 (not statement2))\n" +
                ")\n";

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

        String expected=
                "(declare-const statement1 Bool)\n" +
                "(declare-const statement2 Bool)\n" +
                "(declare-const statement3 Bool)\n" +
                "(declare-const statement4 Bool)\n" +
                "\n" +
                "(define-fun testmodule2 () Bool\n" +
                "(and (and statement1 statement2) (not (or statement3 statement4)))\n" +
                ")\n";

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
                        "(declare-const statement1 Bool)\n" +
                                "(declare-const statement2 Bool)\n" +
                                "(declare-const statement3 Bool)\n" +
                                "(declare-const statement4 Bool)\n" +
                                "\n" +
                                "(define-fun testmodule1 () Bool\n" +
                                "(and (and statement1 statement2) (not (or statement3 statement4)))\n" +
                                ")\n" +
                                "(define-fun testmodule2 () Bool\n" +
                                "(and (and statement1 statement2) (not (or statement3 statement4)))\n" +
                                ")\n";

        assertEquals(expected,compiler(inputString));

    }
    @Test
    void test_multiple_modules2(){
        String inputString =
                "testmodule1:\n" +
                        "    INCLUDE_AND:\n" +
                        "        - statement1\n"+
                        "        - statement2\n"+
                "testmodule2:\n" +
                "    INCLUDE_AND:\n" +
                "        - testmodule1\n"+
                "        - statement2";
        String expected=
                        "(declare-const statement1 Bool)\n" +
                                "(declare-const statement2 Bool)\n" +
                                "\n" +
                                "(define-fun testmodule1 () Bool\n" +
                                "(and statement1 statement2)\n" +
                                ")\n" +
                                "(define-fun testmodule2 () Bool\n" +
                                "(and testmodule1 statement2)\n" +
                                ")\n";

        assertEquals(expected,compiler(inputString));

    }


}
