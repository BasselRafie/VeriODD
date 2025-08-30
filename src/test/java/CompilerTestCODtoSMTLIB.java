
import static org.junit.jupiter.api.Assertions.*;

import cod.CODLexer;
import cod.CODParser;
import cod.CODVisitorSMTLIB;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.jupiter.api.Test;

public class CompilerTestCODtoSMTLIB {

    String compileCODToSMT(String inputString){
        CODVisitorSMTLIB CODVisitorSMTLIB = new CODVisitorSMTLIB();
        CodePointCharStream input = CharStreams.fromString(inputString);
        CODLexer lexer = new CODLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        CODParser parser = new CODParser(tokens);
        ParseTree tree = parser.input();
        String result = CODVisitorSMTLIB.visit(tree);
        return result;
    }

    @Test
    void basicExample_matchesListing() {
        String cod = ""
                + "parking_lot_length: = 13\n"
                + "is_curve: true\n"
                + "surface: snow_covered\n"
                + "location: on_shoulder\n";

        String expected = ""
                + "(assert (= parking_lot_length 13))\n"
                + "(assert (= is_curve true))\n"
                + "(assert (= surface \"snow_covered\"))\n"
                + "(assert (= location \"on_shoulder\"))";

        assertEquals(expected, compileCODToSMT(cod));
    }

    @Test
    void booleansAndStrings_renderCorrectly() {
        String cod = ""
                + "gps_available: true\n"
                + "hd_map_available: false\n"
                + "surface: dry\n"
                + "light: daylight\n";

        String expected = ""
                + "(assert (= gps_available true))\n"
                + "(assert (= hd_map_available false))\n"
                + "(assert (= surface \"dry\"))\n"
                + "(assert (= light \"daylight\"))";

        assertEquals(expected, compileCODToSMT(cod));
    }

    @Test
    void integersAndDecimals_supported() {
        String cod = ""
                + "temperature_c: = -5\n"
                + "grade_percent: = 3.5\n";

        String expected = ""
                + "(assert (= temperature_c -5))\n"
                + "(assert (= grade_percent 3.5))";

        assertEquals(expected, compileCODToSMT(cod));
    }

    @Test
    void whitespaceRobustness_spacesAroundOperatorsIgnored() {
        String cod = ""
                + "parking_lot_length:    =   13\n"
                + "is_curve:    true\n"
                + "surface:    snow_covered\n"
                + "location:    on_shoulder\n";

        String expected = ""
                + "(assert (= parking_lot_length 13))\n"
                + "(assert (= is_curve true))\n"
                + "(assert (= surface \"snow_covered\"))\n"
                + "(assert (= location \"on_shoulder\"))";

        assertEquals(expected, compileCODToSMT(cod));
    }

    @Test
    void preservesOrderOfStatements() {
        String cod = ""
                + "a: = 1\n"
                + "b: = 2\n"
                + "c: true\n";

        String expected = ""
                + "(assert (= a 1))\n"
                + "(assert (= b 2))\n"
                + "(assert (= c true))";

        assertEquals(expected, compileCODToSMT(cod));
    }

    @Test
    void ignoresEmptyLines() {
        String cod = ""
                + "surface: dry\n"
                + "\n"
                + "location: on_shoulder\n";

        String expected = ""
                + "(assert (= surface \"dry\"))\n"
                + "(assert (= location \"on_shoulder\"))";

        assertEquals(expected, compileCODToSMT(cod));
    }
}

