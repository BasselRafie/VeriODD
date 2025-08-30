
import static org.junit.jupiter.api.Assertions.*;

import cod.CODLexer;
import cod.CODParser;
import cod.CODVisitorPropositionalLogic;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.jupiter.api.Test;

public class CompilerTestCODtoPL {

    String compileCODToPL(String inputString){
        CODVisitorPropositionalLogic CODVisitorPropositionalLogic = new CODVisitorPropositionalLogic();
        CodePointCharStream input = CharStreams.fromString(inputString);
        CODLexer lexer = new CODLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        CODParser parser = new CODParser(tokens);
        ParseTree tree = parser.input();
        String result = CODVisitorPropositionalLogic.visit(tree);
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
                + "parking_lot_length = 13\n"
                + "is_curve = true\n"
                + "surface = snow_covered\n"
                + "location = on_shoulder";

        assertEquals(expected, compileCODToPL(cod));
    }

    @Test
    void booleansAndStrings_renderAsAtoms() {
        String cod = ""
                + "gps_available: true\n"
                + "hd_map_available: false\n"
                + "surface: dry\n"
                + "light: daylight\n";

        String expected = ""
                + "gps_available = true\n"
                + "hd_map_available = false\n"
                + "surface = dry\n"
                + "light = daylight";

        assertEquals(expected, compileCODToPL(cod));
    }

    @Test
    void integersAndDecimals_supported() {
        String cod = ""
                + "temperature_c: = -5\n"
                + "grade_percent: = 3.5\n";

        String expected = ""
                + "temperature_c = -5\n"
                + "grade_percent = 3.5";

        assertEquals(expected, compileCODToPL(cod));
    }

    @Test
    void whitespaceRobustness_spacesAroundOperatorsIgnored() {
        String cod = ""
                + "parking_lot_length:    =   13\n"
                + "is_curve:    true\n"
                + "surface:    snow_covered\n"
                + "location:    on_shoulder\n";

        String expected = ""
                + "parking_lot_length = 13\n"
                + "is_curve = true\n"
                + "surface = snow_covered\n"
                + "location = on_shoulder";

        assertEquals(expected, compileCODToPL(cod));
    }

    @Test
    void preservesOrderOfStatements() {
        String cod = ""
                + "a: = 1\n"
                + "b: = 2\n"
                + "c: true\n";

        String expected = ""
                + "a = 1\n"
                + "b = 2\n"
                + "c = true";

        assertEquals(expected, compileCODToPL(cod));
    }

    @Test
    void ignoresEmptyLines() {
        String cod = ""
                + "surface: dry\n"
                + "\n"
                + "location: on_shoulder\n";

        String expected = ""
                + "surface = dry\n"
                + "location = on_shoulder";

        assertEquals(expected, compileCODToPL(cod));
    }
}

